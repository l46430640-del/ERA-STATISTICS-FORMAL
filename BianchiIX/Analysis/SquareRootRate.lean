import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

noncomputable section

namespace BianchiIX

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasFDerivAt_sqrt_rate {Q F : E → ℝ} {x : E}
    (HQ : DifferentiableAt ℝ Q x) (HF : DifferentiableAt ℝ F x) (hQ : 0 < Q x) :
    HasFDerivAt (fun y => F y / (2 * Real.sqrt (Q y)))
      ((1 / (2 * Real.sqrt (Q x))) • fderiv ℝ F x -
        (F x / (2 * Q x)) • fderiv ℝ (fun y => Real.sqrt (Q y)) x) x := by
  have HR := HQ.hasFDerivAt.sqrt hQ.ne'
  have hR : 0 < Real.sqrt (Q x) := Real.sqrt_pos.mpr hQ
  have HI := ((hasDerivAt_inv hR.ne').const_mul (1 / 2 : ℝ)).comp_hasFDerivAt x
    HR.differentiableAt.hasFDerivAt
  convert! HF.hasFDerivAt.mul HI using 1
  · ext y
    simp only [Pi.mul_apply, Function.comp_apply, div_eq_mul_inv, mul_inv_rev]
    ring
  · ext v
    simp only [sub_apply, smul_apply, add_apply, smul_eq_mul, Function.comp_apply]
    rw [Real.sq_sqrt hQ.le]
    field_simp
    ring

/-- Differentiating a square-root drift preserves one radial power on a nondegenerate annulus. -/
theorem sqrt_rate_derivative_bounds {Q F : E → ℝ} {x : E} {A c b n : ℝ}
    (HQ : DifferentiableAt ℝ Q x) (HF : DifferentiableAt ℝ F x)
    (hA : 0 ≤ A) (hc : 0 < c) (hb : 0 < b) (hn : 0 ≤ n)
    (hlower : c * b ≤ Real.sqrt (Q x))
    (HDQ : ‖fderiv ℝ Q x‖ ≤ A * b)
    (HFval : |F x| ≤ A * (n * b + b ^ 2) * Q x)
    (HDF : ‖fderiv ℝ F x‖ ≤ A * (n * b ^ 2 + b ^ 3)) :
    DifferentiableAt ℝ (fun y => Real.sqrt (Q y)) x ∧
      ‖fderiv ℝ (fun y => Real.sqrt (Q y)) x‖ ≤ A / c ∧
      DifferentiableAt ℝ (fun y => F y / (2 * Real.sqrt (Q y))) x ∧
      ‖fderiv ℝ (fun y => F y / (2 * Real.sqrt (Q y))) x‖ ≤
        (A + A ^ 2) / c * (n * b + b ^ 2) := by
  have hR : 0 < Real.sqrt (Q x) := (mul_pos hc hb).trans_le hlower
  have hQ : 0 < Q x := Real.sqrt_pos.mp hR
  have HR := HQ.hasFDerivAt.sqrt hQ.ne'
  have HD : ‖fderiv ℝ (fun y => Real.sqrt (Q y)) x‖ ≤ A / c := by
    rw [HR.fderiv, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (2 * Real.sqrt (Q x)))]
    calc
      _ = ‖fderiv ℝ Q x‖ / (2 * Real.sqrt (Q x)) := by ring
      _ ≤ A * b / (2 * Real.sqrt (Q x)) := div_le_div_of_nonneg_right HDQ (by positivity)
      _ ≤ A * b / (c * b) := div_le_div_of_nonneg_left (mul_nonneg hA hb.le)
        (mul_pos hc hb) (by linarith only [hlower, hR])
      _ = A / c := by field_simp
  have HG := hasFDerivAt_sqrt_rate HQ HF hQ
  refine ⟨HR.differentiableAt, HD, HG.differentiableAt, ?_⟩
  have Hfirst : ‖fderiv ℝ F x‖ / (2 * Real.sqrt (Q x)) ≤ A / c * (n * b + b ^ 2) := by
    calc
      _ ≤ A * (n * b ^ 2 + b ^ 3) / (2 * Real.sqrt (Q x)) :=
        div_le_div_of_nonneg_right HDF (by positivity)
      _ ≤ A * (n * b ^ 2 + b ^ 3) / (c * b) := div_le_div_of_nonneg_left (by positivity)
        (mul_pos hc hb) (by linarith only [hlower, hR])
      _ = _ := by field_simp
  have Hfactor : |F x| / (2 * Q x) ≤ A * (n * b + b ^ 2) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * Q x)).mpr
    nlinarith only [HFval, mul_nonneg (mul_nonneg hA (add_nonneg (mul_nonneg hn hb.le) (sq_nonneg b))) hQ.le]
  rw [HG.fderiv]
  calc
    _ ≤ ‖(1 / (2 * Real.sqrt (Q x))) • fderiv ℝ F x‖ +
        ‖(F x / (2 * Q x)) • fderiv ℝ (fun y => Real.sqrt (Q y)) x‖ := norm_sub_le _ _
    _ = ‖fderiv ℝ F x‖ / (2 * Real.sqrt (Q x)) +
        (|F x| / (2 * Q x)) * ‖fderiv ℝ (fun y => Real.sqrt (Q y)) x‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by positivity : 0 < 1 / (2 * Real.sqrt (Q x))), abs_div,
        abs_of_pos (by positivity : 0 < 2 * Q x)]
      ring
    _ ≤ A / c * (n * b + b ^ 2) + (A * (n * b + b ^ 2)) * (A / c) := by
      exact add_le_add Hfirst (mul_le_mul Hfactor HD (norm_nonneg _) (by positivity))
    _ = _ := by ring

end BianchiIX
