import BianchiIX.Dynamics.EntranceRadialInverseBounds
import BianchiIX.Dynamics.EntranceCoefficientDerivatives

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

local instance entranceProjectionOperatorGroup : NormedAddCommGroup (ProjectiveState →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance entranceProjectionOperatorSpace : NormedSpace ℝ (ProjectiveState →L[ℝ] ℝ) := inferInstance
local instance entranceStableOperatorGroup : NormedAddCommGroup (StableState →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance entranceStableOperatorSpace : NormedSpace ℝ (StableState →L[ℝ] ℝ) := inferInstance

theorem entranceStablePhase_hessian {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (v w : ProjectiveState) :
    fderiv ℝ (fderiv ℝ entranceStablePhase) y v w =
      fderiv ℝ (fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)))
        (stableRestriction y) (stableRestriction v) (stableRestriction w) := by
  let P := fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)
  have hP : ContDiffAt ℝ 2 P (stableRestriction y) := contDiffAt_stableBoundaryProjection_two hm hu hw
  have heq : (fun z => fderiv ℝ entranceStablePhase z w) =ᶠ[𝓝 y]
      (fun z => fderiv ℝ P (stableRestriction z) (stableRestriction w)) := by
    filter_upwards [stableRestriction.continuous.continuousAt.eventually (hP.eventually (by norm_num))] with z hz
    have H := (hz.differentiableAt (by norm_num)).hasFDerivAt.comp z stableRestriction.hasFDerivAt
    exact congrArg (fun L : ProjectiveState →L[ℝ] ℝ => L w) H.fderiv
  have hL := (((contDiffAt_entranceStablePhase_two hm hu hw).fderiv_right
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)).hasFDerivAt.clm_apply
      (hasFDerivAt_const (𝕜 := ℝ) w y)
  have hR := (((hP.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
    (by norm_num)).hasFDerivAt.comp y stableRestriction.hasFDerivAt).clm_apply
      (hasFDerivAt_const (𝕜 := ℝ) (stableRestriction w) y)
  have H := congrArg (fun L : ProjectiveState →L[ℝ] ℝ => L v) heq.fderiv_eq
  change HasFDerivAt (fun z => fderiv ℝ P (stableRestriction z) (stableRestriction w)) _ y at hR
  rw [hL.fderiv, hR.fderiv] at H
  simpa [P] using H

/-- The ordinary projection columns retain the large entrance parameter powers. -/
theorem exists_entranceProjection_estimates :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y →
      let b := y 1 + y 3
      let Q := fderiv ℝ (fderiv ℝ entranceStablePhase) y
      |entranceStablePhase y - y 0| ≤ C * b ^ 2 / k ∧
      |entranceStablePartial y 0 - 1| ≤ C * b ^ 2 / k ^ 2 ∧
      |entranceStablePartial y 1| ≤ C * b / k ∧
      |entranceStablePartial y 3| ≤ C * b / k ∧
      |Q (Pi.single 0 1) (Pi.single 0 1)| ≤ C * b ^ 2 / k ^ 3 ∧
      |Q (Pi.single 1 1) (Pi.single 0 1)| ≤ C * b / k ^ 2 ∧
      |Q (Pi.single 3 1) (Pi.single 0 1)| ≤ C * b / k ^ 2 := by
  obtain ⟨C, hC, HC⟩ := exists_stableBoundaryProjection_refined_derivatives
  refine ⟨8 * (C + 8), by positivity, ?_⟩
  intro k y hk hy
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  have hk0 : 0 < k := by linarith
  have hL : k / 2 ≤ y 0 + 1 := by linarith [(entranceRegion_phase hk hy).1]
  have hb : 0 ≤ y 1 + y 3 := add_nonneg hy.2.2.1.1 hy.2.2.2.2.1
  have hscale (a q : ℝ) (ha : 0 ≤ a) (hq : 0 ≤ q) (n : ℕ) :
      a / (y 0 + 1) ^ n * q ≤ 2 ^ n * a * q / k ^ n := by
    calc
      _ ≤ a / (k / 2) ^ n * q := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left ha (pow_pos (by positivity) _) (pow_le_pow_left₀ (by positivity) hL n)) hq
      _ = _ := by simp only [div_pow]; field_simp
  have h0 : stableRestriction (Pi.single (0 : Fin 4) (1 : ℝ)) = Pi.single 0 1 := by
    ext i; fin_cases i <;> simp [stableRestriction]
  have h1 : stableRestriction (Pi.single (1 : Fin 4) (1 : ℝ)) = Pi.single 1 1 := by
    ext i; fin_cases i <;> simp [stableRestriction]
  have h3 : stableRestriction (Pi.single (3 : Fin 4) (1 : ℝ)) = Pi.single 2 1 := by
    ext i; fin_cases i <;> simp [stableRestriction]
  obtain ⟨hpM, hpz, hpMM, hpMz, _⟩ := HC (stableRestriction y) hm hu hw
  have H0 := hpM (Pi.single 0 1) (by simp) (by simp)
  have H1 := hpz (Pi.single 1 1) (by simp)
  have H3 := hpz (Pi.single 2 1) (by simp)
  have H00 := hpMM (Pi.single 0 1) (Pi.single 0 1) (by simp) (by simp) (by simp) (by simp)
  have H01 := hpMz (Pi.single 0 1) (Pi.single 1 1) (by simp) (by simp) (by simp)
  have H03 := hpMz (Pi.single 0 1) (Pi.single 2 1) (by simp) (by simp) (by simp)
  have hsym := (contDiffAt_entranceStablePhase_two hm hu hw).isSymmSndFDerivAt (by norm_num)
  dsimp only
  rw [hsym.eq (Pi.single 1 1) (Pi.single 0 1), hsym.eq (Pi.single 3 1) (Pi.single 0 1)]
  simp only [entranceStablePartial, entranceStablePhase_fderiv hm hu hw,
    entranceStablePhase_hessian hm hu hw, h0, h1, h3]
  have Hval : |entranceStablePhase y - y 0| ≤ 8 / (y 0 + 1) * (y 1 + y 3) ^ 2 := by
    have H := (stableBoundaryProjection_exists (m := y 0) hm (by simp) hu.le hw.le).2.2.2.2
    rw [abs_of_nonneg hy.2.2.1.1, abs_of_nonneg hy.2.2.2.2.1] at H
    convert! H using 1
    ring
  simp only [stableRestriction_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Pi.single_eq_same, Pi.norm_single, norm_one, mul_one,
    abs_of_nonneg hy.2.2.1.1, abs_of_nonneg hy.2.2.2.2.1] at H0 H1 H3 H00 H01 H03 ⊢
  have HB (a q : ℝ) (ha : 0 ≤ a) (hq : 0 ≤ q) (n : ℕ) (hconst : 2 ^ n * a ≤ 8 * (C + 8)) :
      a / (y 0 + 1) ^ n * q ≤ 8 * (C + 8) * q / k ^ n :=
    (hscale a q ha hq n).trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hconst hq) (pow_pos hk0 n).le)
  refine ⟨?_, H0.trans (HB C _ hC.le (sq_nonneg _) 2 (by nlinarith)),
    ?_, ?_, H00.trans (HB C _ hC.le (sq_nonneg _) 3 (by nlinarith)),
    H01.trans (HB C _ hC.le hb 2 (by nlinarith)),
    H03.trans (HB C _ hC.le hb 2 (by nlinarith))⟩
  · simpa using Hval.trans (by simpa using HB 8 _ (by norm_num) (sq_nonneg (y 1 + y 3)) 1 (by nlinarith))
  · simpa using H1.trans (by simpa using HB C _ hC.le hb 1 (by nlinarith))
  · simpa using H3.trans (by simpa using HB C _ hC.le hb 1 (by nlinarith))

end BianchiIX
