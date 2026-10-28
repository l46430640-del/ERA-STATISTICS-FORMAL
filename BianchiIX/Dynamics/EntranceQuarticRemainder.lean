import BianchiIX.Dynamics.StableQuadraticRemainderBounds
import BianchiIX.Dynamics.EntranceProjectionEstimates

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

local instance entranceQuarticOperatorGroup : NormedAddCommGroup (ProjectiveState →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance entranceQuarticOperatorSpace : NormedSpace ℝ (ProjectiveState →L[ℝ] ℝ) := inferInstance
local instance entranceQuarticStableOperatorGroup : NormedAddCommGroup (StableState →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance entranceQuarticStableOperatorSpace : NormedSpace ℝ (StableState →L[ℝ] ℝ) := inferInstance

def entranceQuarticRemainder (y : ProjectiveState) : ℝ := stableQuadraticRemainder (stableRestriction y)

theorem contDiffAt_entranceQuarticRemainder_two {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) :
    ContDiffAt ℝ 2 entranceQuarticRemainder y :=
  (stableQuadraticRemainder_derivatives (y := stableRestriction y) hm hu hw).1.comp y stableRestriction.contDiff.contDiffAt

theorem entranceQuarticRemainder_fderiv {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (v : ProjectiveState) :
    fderiv ℝ entranceQuarticRemainder y v =
      fderiv ℝ stableQuadraticRemainder (stableRestriction y) (stableRestriction v) := by
  have H := ((stableQuadraticRemainder_derivatives (y := stableRestriction y) hm hu hw).1.differentiableAt
    (by norm_num)).hasFDerivAt.comp y stableRestriction.hasFDerivAt
  exact congrArg (fun L : ProjectiveState →L[ℝ] ℝ => L v) H.fderiv

theorem entranceQuarticRemainder_hessian {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (v w : ProjectiveState) :
    fderiv ℝ (fderiv ℝ entranceQuarticRemainder) y v w =
      fderiv ℝ (fderiv ℝ stableQuadraticRemainder) (stableRestriction y) (stableRestriction v) (stableRestriction w) := by
  have hR := (stableQuadraticRemainder_derivatives (y := stableRestriction y) hm hu hw).1
  have heq : (fun z => fderiv ℝ entranceQuarticRemainder z w) =ᶠ[𝓝 y]
      (fun z => fderiv ℝ stableQuadraticRemainder (stableRestriction z) (stableRestriction w)) := by
    filter_upwards [stableRestriction.continuous.continuousAt.eventually (hR.eventually (by norm_num))] with z hz
    have H := (hz.differentiableAt (by norm_num)).hasFDerivAt.comp z stableRestriction.hasFDerivAt
    exact congrArg (fun L : ProjectiveState →L[ℝ] ℝ => L w) H.fderiv
  have hleft := (((contDiffAt_entranceQuarticRemainder_two hm hu hw).fderiv_right
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)).hasFDerivAt.clm_apply
      (hasFDerivAt_const (𝕜 := ℝ) w y)
  have hright := (((hR.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
    (by norm_num)).hasFDerivAt.comp y stableRestriction.hasFDerivAt).clm_apply
      (hasFDerivAt_const (𝕜 := ℝ) (stableRestriction w) y)
  have H := congrArg (fun L : ProjectiveState →L[ℝ] ℝ => L v) heq.fderiv_eq
  change HasFDerivAt (fun z => fderiv ℝ stableQuadraticRemainder (stableRestriction z) (stableRestriction w)) _ y at hright
  rw [hleft.fderiv, hright.fderiv] at H
  simpa using H

/-- The quartic remainder retains all phase and mixed second derivative bounds in the entrance chart. -/
theorem exists_entranceQuarticRemainder_bounds :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y →
      let b := y 1 + y 3
      let L := fderiv ℝ entranceQuarticRemainder y
      let Q := fderiv ℝ (fderiv ℝ entranceQuarticRemainder) y
      |entranceQuarticRemainder y| ≤ C * b ^ 4 / k ^ 3 ∧
      |L (Pi.single 0 1)| ≤ C * b ^ 4 / k ^ 3 ∧
      |L (Pi.single 1 1)| ≤ C * b ^ 3 / k ^ 3 ∧
      |L (Pi.single 3 1)| ≤ C * b ^ 3 / k ^ 3 ∧
      |Q (Pi.single 0 1) (Pi.single 0 1)| ≤ C * b ^ 4 / k ^ 3 ∧
      |Q (Pi.single 1 1) (Pi.single 0 1)| ≤ C * b ^ 3 / k ^ 3 ∧
      |Q (Pi.single 3 1) (Pi.single 0 1)| ≤ C * b ^ 3 / k ^ 3 := by
  obtain ⟨C, hC, HC⟩ := exists_stableQuadraticRemainder_bounds
  refine ⟨8 * C, by positivity, ?_⟩
  intro k y hk hy
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  have hk0 : 0 < k := by linarith
  have hL : k / 2 ≤ y 0 + 1 := by linarith [(entranceRegion_phase hk hy).1]
  have hb : 0 ≤ y 1 + y 3 := add_nonneg hy.2.2.1.1 hy.2.2.2.2.1
  have hscale (q : ℝ) (hq : 0 ≤ q) : C / (y 0 + 1) ^ 3 * q ≤ 8 * C * q / k ^ 3 := by
    calc
      _ ≤ C / (k / 2) ^ 3 * q := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left hC.le (by positivity) (pow_le_pow_left₀ (by positivity) hL 3)) hq
      _ = _ := by field_simp; ring
  have h0 : stableRestriction (Pi.single (0 : Fin 4) (1 : ℝ)) = Pi.single 0 1 := by
    ext i; fin_cases i <;> simp [stableRestriction]
  have h1 : stableRestriction (Pi.single (1 : Fin 4) (1 : ℝ)) = Pi.single 1 1 := by
    ext i; fin_cases i <;> simp [stableRestriction]
  have h3 : stableRestriction (Pi.single (3 : Fin 4) (1 : ℝ)) = Pi.single 2 1 := by
    ext i; fin_cases i <;> simp [stableRestriction]
  obtain ⟨_, Hval, hM, hz, hMM, hMz, _⟩ := HC (stableRestriction y) hm hu hw
  have H0 := hM (Pi.single 0 1) (by simp) (by simp)
  have H1 := hz (Pi.single 1 1) (by simp)
  have H3 := hz (Pi.single 2 1) (by simp)
  have H00 := hMM (Pi.single 0 1) (Pi.single 0 1) (by simp) (by simp) (by simp) (by simp)
  have H01 := hMz (Pi.single 0 1) (Pi.single 1 1) (by simp) (by simp) (by simp)
  have H03 := hMz (Pi.single 0 1) (Pi.single 2 1) (by simp) (by simp) (by simp)
  have hsym := (contDiffAt_entranceQuarticRemainder_two hm hu hw).isSymmSndFDerivAt (by norm_num)
  dsimp only
  rw [hsym.eq (Pi.single 1 1) (Pi.single 0 1), hsym.eq (Pi.single 3 1) (Pi.single 0 1)]
  simp only [entranceQuarticRemainder_fderiv hm hu hw, entranceQuarticRemainder_hessian hm hu hw, h0, h1, h3]
  simp only [entranceQuarticRemainder, stableRestriction_apply]
  simp only [stableRestriction_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    Pi.norm_single, norm_one, mul_one, abs_of_nonneg hy.2.2.1.1, abs_of_nonneg hy.2.2.2.2.1] at Hval H0 H1 H3 H00 H01 H03
  exact ⟨Hval.trans (hscale _ (by positivity)), H0.trans (hscale _ (by positivity)),
    H1.trans (hscale _ (by positivity)), H3.trans (hscale _ (by positivity)),
    H00.trans (hscale _ (by positivity)), H01.trans (hscale _ (by positivity)), H03.trans (hscale _ (by positivity))⟩

end BianchiIX
