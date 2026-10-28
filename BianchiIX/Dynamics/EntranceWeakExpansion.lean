import BianchiIX.Dynamics.EntranceQuarticRemainder
import Mathlib.Analysis.Calculus.Deriv.Pi

noncomputable section

namespace BianchiIX

def entranceWeakQuadratic (y : ProjectiveState) : ℝ :=
  (1 - 1 / (y 0 + 1) ^ 2) * y 1 ^ 2 + (-1 + 4 / (y 0 + 1) ^ 2) * y 1 * y 3 - y 3 ^ 2 / (y 0 + 1) ^ 2

def entranceWeakRemainder (y : ProjectiveState) : ℝ :=
  -entranceQuarticRemainder y - (y 0 - 1) * fderiv ℝ entranceQuarticRemainder y (Pi.single 0 1) -
    (entranceStablePhase y - y 0) * (entranceStablePartial y 0 - 1)

theorem hasDerivAt_stableQuadraticPhase_phase {m u w : ℝ} (hm : 1 < m) :
    HasDerivAt (fun a => stableQuadraticPhase a u w)
      (1 + stableCorrectionADeriv m * u ^ 2 + stableCorrectionCDeriv m * u * w - w ^ 2 / (2 * (m + 1) ^ 2)) m := by
  have hden : 2 * (m + 1) ≠ 0 := by positivity
  have H := (((hasDerivAt_id m).add ((hasDerivAt_stableCorrectionA hm).mul_const (u ^ 2))).add
    (((hasDerivAt_stableCorrectionC (by linarith : -1 < m)).mul_const u).mul_const w)).add
    ((hasDerivAt_const m (w ^ 2)).div (((hasDerivAt_id m).add_const 1).const_mul 2) hden)
  apply H.congr_deriv
  dsimp [stableCorrectionADeriv, stableCorrectionCDeriv]
  have hL : m + 1 ≠ 0 := by linarith
  have hsq : m ^ 2 - 1 ≠ 0 := by nlinarith only [hm]
  field_simp
  ring

theorem entranceStablePartial_quadratic_phase {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) :
    entranceStablePartial y 0 = 1 + stableCorrectionADeriv (y 0) * y 1 ^ 2 +
      stableCorrectionCDeriv (y 0) * y 1 * y 3 - y 3 ^ 2 / (2 * (y 0 + 1) ^ 2) +
      fderiv ℝ entranceQuarticRemainder y (Pi.single 0 1) := by
  have hpath := hasDerivAt_update y 0 (y 0)
  have hR : HasFDerivAt entranceQuarticRemainder (fderiv ℝ entranceQuarticRemainder y) (Function.update y 0 (y 0)) := by
    simpa using ((contDiffAt_entranceQuarticRemainder_two hm hu hw).differentiableAt (by norm_num)).hasFDerivAt
  have hP : HasFDerivAt entranceStablePhase (fderiv ℝ entranceStablePhase y) (Function.update y 0 (y 0)) := by
    simpa using ((contDiffAt_entranceStablePhase_two hm hu hw).differentiableAt (by norm_num)).hasFDerivAt
  have hRP := hR.comp_hasDerivAt (y 0) hpath
  have hPQ := (hP.comp_hasDerivAt (y 0) hpath).sub
    (hasDerivAt_stableQuadraticPhase_phase (u := y 1) (w := y 3) (by linarith : 1 < y 0))
  have heq : (fun a => entranceQuarticRemainder (Function.update y 0 a)) =
      (fun a => entranceStablePhase (Function.update y 0 a) - stableQuadraticPhase a (y 1) (y 3)) := by
    funext a
    simp [entranceQuarticRemainder, stableQuadraticRemainder, entranceStablePhase, stableRestriction]
  change HasDerivAt (fun a => entranceQuarticRemainder (Function.update y 0 a)) _ (y 0) at hRP
  rw [heq] at hRP
  have H := hRP.unique hPQ
  dsimp [entranceStablePartial]
  linarith only [H]

/-- Exact quadratic expansion of the weak numerator, retaining the large-parameter cancellation. -/
theorem entranceWeakNumerator_quadratic_expansion {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) :
    entranceWeakNumerator y = entranceWeakQuadratic y + entranceWeakRemainder y := by
  have hRM := entranceStablePartial_quadratic_phase hm hu hw
  have hR : entranceQuarticRemainder y = entranceStablePhase y - stableQuadraticPhase (y 0) (y 1) (y 3) := rfl
  have hd : y 0 + 1 ≠ 0 := by linarith
  have he : y 0 ^ 2 - 1 ≠ 0 := by nlinarith only [hm]
  unfold entranceWeakNumerator entranceWeakQuadratic entranceWeakRemainder
  rw [hR]
  have heq : fderiv ℝ entranceQuarticRemainder y (Pi.single 0 1) = entranceStablePartial y 0 -
      (1 + stableCorrectionADeriv (y 0) * y 1 ^ 2 + stableCorrectionCDeriv (y 0) * y 1 * y 3 - y 3 ^ 2 / (2 * (y 0 + 1) ^ 2)) := by
    linarith only [hRM]
  rw [heq]
  dsimp [stableQuadraticPhase, stableCorrectionA, stableCorrectionC, stableCorrectionADeriv, stableCorrectionCDeriv]
  field_simp
  ring

theorem entranceWeakRemainder_differential {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) :
    DifferentiableAt ℝ entranceWeakRemainder y ∧ ∀ v : ProjectiveState,
      fderiv ℝ entranceWeakRemainder y v =
        -fderiv ℝ entranceQuarticRemainder y v - v 0 * fderiv ℝ entranceQuarticRemainder y (Pi.single 0 1) -
        (y 0 - 1) * fderiv ℝ (fderiv ℝ entranceQuarticRemainder) y v (Pi.single 0 1) -
        (fderiv ℝ entranceStablePhase y v - v 0) * (entranceStablePartial y 0 - 1) -
        (entranceStablePhase y - y 0) * fderiv ℝ (fderiv ℝ entranceStablePhase) y v (Pi.single 0 1) := by
  have hR := contDiffAt_entranceQuarticRemainder_two hm hu hw
  have hRM := (((hR.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
    (by norm_num)).hasFDerivAt).clm_apply (hasFDerivAt_const (𝕜 := ℝ) (Pi.single 0 1) y)
  have hP := contDiffAt_entranceStablePhase_two hm hu hw
  have hPM := (((hP.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt
    (by norm_num)).hasFDerivAt).clm_apply (hasFDerivAt_const (𝕜 := ℝ) (Pi.single 0 1) y)
  have hd := hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 4) y
  have hfirst := ((hR.differentiableAt (by norm_num)).hasFDerivAt.neg).sub ((hd.sub_const 1).mul hRM)
  have H := hfirst.sub
    ((((hP.differentiableAt (by norm_num)).hasFDerivAt).sub hd).mul (hPM.sub_const 1))
  change HasFDerivAt entranceWeakRemainder _ y at H
  refine ⟨H.differentiableAt, fun v => ?_⟩
  rw [H.fderiv]
  simp [entranceStablePartial, sub_apply, add_apply, neg_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, Pi.sub_apply]
  ring

end BianchiIX
