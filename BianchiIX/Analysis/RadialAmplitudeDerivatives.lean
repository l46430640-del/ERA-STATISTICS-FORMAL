import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

namespace BianchiIX

/-- Relative radial bounds survive division by a positive height, including a zero numerator. -/
theorem scaled_quotient_radial_derivative_bound {f g : ℝ → ℝ} {f' g' t r c Kf Kg : ℝ}
    (Hf : HasDerivAt f f' t) (Hg : HasDerivAt g g' t)
    (hr : 0 < r) (hc : 0 ≤ c) (hf : 0 ≤ f t) (hg : 0 < g t)
    (hf' : |f'| ≤ Kf * f t / r) (hg' : |g'| ≤ Kg * g t / r) :
    DifferentiableAt ℝ (fun x => c * f x / g x) t ∧
      |deriv (fun x => c * f x / g x) t| ≤ (Kf + Kg) * (c * f t / g t) / r := by
  have HD := (Hf.const_mul c).div Hg (ne_of_gt hg)
  change HasDerivAt (fun x => c * f x / g x) _ t at HD
  refine ⟨HD.differentiableAt, ?_⟩
  rw [HD.deriv, abs_div, abs_of_nonneg (sq_nonneg (g t))]
  calc
    _ ≤ ((c * |f'|) * g t + (c * f t) * |g'|) / (g t) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      have H := abs_sub_le (c * f' * g t) 0 (c * f t * g')
      simpa only [sub_zero, zero_sub, abs_neg, abs_mul, abs_of_nonneg hc,
        abs_of_nonneg hf, abs_of_pos hg] using H
    _ ≤ ((c * (Kf * f t / r)) * g t + (c * f t) * (Kg * g t / r)) / (g t) ^ 2 := by
      gcongr
    _ = _ := by field_simp

theorem product_radial_derivative_bound {f g : ℝ → ℝ} {t r Kf Kg : ℝ}
    (Hf : DifferentiableAt ℝ f t) (Hg : DifferentiableAt ℝ g t)
    (hf : 0 ≤ f t) (hg : 0 ≤ g t)
    (hf' : |deriv f t| ≤ Kf * f t / r) (hg' : |deriv g t| ≤ Kg * g t / r) :
    DifferentiableAt ℝ (fun x => f x * g x) t ∧
      |deriv (fun x => f x * g x) t| ≤ (Kf + Kg) * (f t * g t) / r := by
  have HD := Hf.hasDerivAt.mul Hg.hasDerivAt
  change HasDerivAt (fun x => f x * g x) _ t at HD
  refine ⟨HD.differentiableAt, ?_⟩
  rw [HD.deriv]
  calc
    _ ≤ |deriv f t * g t| + |f t * deriv g t| := abs_add_le _ _
    _ = |deriv f t| * g t + f t * |deriv g t| := by rw [abs_mul, abs_mul, abs_of_nonneg hf, abs_of_nonneg hg]
    _ ≤ (Kf * f t / r) * g t + f t * (Kg * g t / r) := by gcongr
    _ = _ := by ring

theorem log_radial_derivative_bound {f : ℝ → ℝ} {t r K : ℝ}
    (Hf : DifferentiableAt ℝ f t) (hf : 0 < f t)
    (hf' : |deriv f t| ≤ K * f t / r) :
    DifferentiableAt ℝ (fun x => Real.log (f x)) t ∧
      |deriv (fun x => Real.log (f x)) t| ≤ K / r := by
  have HD := Hf.hasDerivAt.log (ne_of_gt hf)
  refine ⟨HD.differentiableAt, ?_⟩
  rw [HD.deriv, abs_div, abs_of_pos hf]
  calc
    _ ≤ (K * f t / r) / f t := div_le_div_of_nonneg_right hf' hf.le
    _ = _ := by field_simp

end BianchiIX
