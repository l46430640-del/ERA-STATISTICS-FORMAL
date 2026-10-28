import BianchiIX.Analysis.SecondDerivativeRules
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Data.Fin.VecNotation

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def reciprocalParameter (y : Fin 2 → ℝ) : ℝ := (y 0 + 1)⁻¹

def reciprocalParameterMap (y : Fin 2 → ℝ) : Fin 2 → ℝ := ![reciprocalParameter y, y 1]

theorem contDiffAt_reciprocalParameter (n : WithTop ℕ∞) {y : Fin 2 → ℝ} (hy : y 0 + 1 ≠ 0) :
    ContDiffAt ℝ n reciprocalParameter y := by unfold reciprocalParameter; fun_prop

theorem contDiffAt_reciprocalParameterMap (n : WithTop ℕ∞) {y : Fin 2 → ℝ} (hy : y 0 + 1 ≠ 0) :
    ContDiffAt ℝ n reciprocalParameterMap y := by
  unfold reciprocalParameterMap
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact contDiffAt_reciprocalParameter n hy
  · exact contDiffAt_apply ℝ ℝ 1 y

theorem reciprocalParameter_fderiv {y : Fin 2 → ℝ} (hy : y 0 + 1 ≠ 0) (v : Fin 2 → ℝ) :
    fderiv ℝ reciprocalParameter y v = -(reciprocalParameter y) ^ 2 * v 0 := by
  have H := (hasFDerivAt_inv hy).comp y ((hasFDerivAt_apply (𝕜 := ℝ) 0 y).add_const 1)
  have H' := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L v) H.fderiv
  unfold reciprocalParameter
  simpa [Function.comp_def, reciprocalParameter, inv_pow, mul_comm] using H'

theorem reciprocalParameter_fderiv2 {y : Fin 2 → ℝ} (hy : y 0 + 1 ≠ 0) (v w : Fin 2 → ℝ) :
    fderiv ℝ (fderiv ℝ reciprocalParameter) y v w = 2 * (reciprocalParameter y) ^ 3 * v 0 * w 0 := by
  have hreg := contDiffAt_reciprocalParameter 2 hy
  have hd := (hreg.differentiableAt (by norm_num)).hasFDerivAt
  have hd' := ((hreg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)).hasFDerivAt
  have Hleft := hd'.clm_apply (hasFDerivAt_const w y)
  have Hright := ((hd.pow 2).neg).mul_const (w 0)
  have heq : (fun z => fderiv ℝ reciprocalParameter z w) =ᶠ[𝓝 y]
      (fun z => -(reciprocalParameter z) ^ 2 * w 0) := by
    filter_upwards [((continuous_apply 0).add continuous_const).continuousAt.eventually_ne hy] with z hz
    exact reciprocalParameter_fderiv hz w
  have H := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L v)
    (Hleft.unique (Hright.congr_of_eventuallyEq heq))
  simpa [reciprocalParameter_fderiv hy, mul_assoc, mul_comm, mul_left_comm, pow_succ] using H

theorem reciprocalParameterMap_fderiv {y : Fin 2 → ℝ} (hy : y 0 + 1 ≠ 0) (v : Fin 2 → ℝ) :
    fderiv ℝ reciprocalParameterMap y v = ![-(reciprocalParameter y) ^ 2 * v 0, v 1] := by
  have hd := (contDiffAt_reciprocalParameterMap 1 hy).differentiableAt (by norm_num)
  have H0 := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L v) (fderiv_apply hd (0 : Fin 2))
  have H1 := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L v) (fderiv_apply hd (1 : Fin 2))
  change fderiv ℝ reciprocalParameter y v = fderiv ℝ reciprocalParameterMap y v 0 at H0
  change fderiv ℝ (fun z : Fin 2 → ℝ => z 1) y v = fderiv ℝ reciprocalParameterMap y v 1 at H1
  rw [reciprocalParameter_fderiv hy] at H0
  rw [(hasFDerivAt_apply (𝕜 := ℝ) 1 y).fderiv] at H1
  ext i; fin_cases i
  · exact H0.symm
  · exact H1.symm

theorem reciprocalParameterMap_fderiv2 {y : Fin 2 → ℝ} (hy : y 0 + 1 ≠ 0) (v w : Fin 2 → ℝ) :
    fderiv ℝ (fderiv ℝ reciprocalParameterMap) y v w = ![2 * (reciprocalParameter y) ^ 3 * v 0 * w 0, 0] := by
  have H0 := fderiv2_clm_comp_apply (contDiffAt_reciprocalParameterMap 2 hy)
    (ContinuousLinearMap.proj (0 : Fin 2)) v w
  have H1 := fderiv2_clm_comp_apply (contDiffAt_reciprocalParameterMap 2 hy)
    (ContinuousLinearMap.proj (1 : Fin 2)) v w
  change fderiv ℝ (fderiv ℝ reciprocalParameter) y v w = fderiv ℝ (fderiv ℝ reciprocalParameterMap) y v w 0 at H0
  change fderiv ℝ (fderiv ℝ (fun z : Fin 2 → ℝ => z 1)) y v w = fderiv ℝ (fderiv ℝ reciprocalParameterMap) y v w 1 at H1
  have hproj : fderiv ℝ (fun z : Fin 2 → ℝ => z 1) = fun _ => ContinuousLinearMap.proj 1 :=
    funext (fun z => (hasFDerivAt_apply (𝕜 := ℝ) 1 z).fderiv)
  rw [reciprocalParameter_fderiv2 hy] at H0
  rw [hproj, fderiv_const_apply] at H1
  ext i; fin_cases i
  · exact H0.symm
  · exact H1.symm

theorem reciprocalParameter_range {y : Fin 2 → ℝ} (hy : 3 / 2 ≤ y 0) :
    0 < reciprocalParameter y ∧ reciprocalParameter y ≤ 2 / 5 := by
  have h : 0 < y 0 + 1 := by linarith
  refine ⟨inv_pos.mpr h, ?_⟩
  dsimp [reciprocalParameter]
  rw [← one_div]
  apply (div_le_iff₀ h).mpr
  linarith

theorem reciprocalParameter_derivative_bounds {y : Fin 2 → ℝ} (hy : 3 / 2 ≤ y 0) (v w : Fin 2 → ℝ) :
    |fderiv ℝ reciprocalParameter y v| ≤ reciprocalParameter y * ‖v‖ ∧
      |fderiv ℝ (fderiv ℝ reciprocalParameter) y v w| ≤ 2 * reciprocalParameter y * ‖v‖ * ‖w‖ ∧
      ‖fderiv ℝ reciprocalParameterMap y v‖ ≤ ‖v‖ ∧
      ‖fderiv ℝ (fderiv ℝ reciprocalParameterMap) y v w‖ ≤ 2 * ‖v‖ * ‖w‖ := by
  let a := reciprocalParameter y
  have ha := reciprocalParameter_range hy
  have ha1 : a ≤ 1 := by dsimp [a]; linarith [ha.2]
  have ha0 : 0 ≤ a := ha.1.le
  have ha2 : a ^ 2 ≤ a := by nlinarith
  have ha3 : a ^ 3 ≤ a := by nlinarith [mul_le_mul_of_nonneg_left ha2 ha0]
  have hv (i : Fin 2) : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i
  have hw (i : Fin 2) : |w i| ≤ ‖w‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w i
  have hn : y 0 + 1 ≠ 0 := by linarith
  have H1 : |-(a ^ 2) * v 0| ≤ a * ‖v‖ := by
    rw [abs_mul, abs_neg, abs_of_nonneg (sq_nonneg a)]
    exact mul_le_mul ha2 (hv 0) (abs_nonneg _) ha0
  have H2 : |2 * a ^ 3 * v 0 * w 0| ≤ 2 * a * ‖v‖ * ‖w‖ := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * a ^ 3)]
    exact mul_le_mul (mul_le_mul (by nlinarith : 2 * a ^ 3 ≤ 2 * a) (hv 0) (abs_nonneg _) (by positivity))
      (hw 0) (abs_nonneg _) (by positivity)
  refine ⟨by simpa only [reciprocalParameter_fderiv hn] using H1,
    by simpa only [reciprocalParameter_fderiv2 hn] using H2, ?_, ?_⟩
  · rw [reciprocalParameterMap_fderiv hn]
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
    intro i; fin_cases i
    · exact H1.trans (mul_le_of_le_one_left (norm_nonneg v) ha1)
    · exact hv 1
  · rw [reciprocalParameterMap_fderiv2 hn]
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * ‖v‖ * ‖w‖)).mpr
    intro i; fin_cases i
    · exact H2.trans (by nlinarith only [mul_le_mul_of_nonneg_right ha1 (show 0 ≤ 2 * ‖v‖ * ‖w‖ by positivity)])
    · simpa using (show 0 ≤ 2 * ‖v‖ * ‖w‖ by positivity)

end BianchiIX
