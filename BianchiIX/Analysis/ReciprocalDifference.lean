import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

namespace BianchiIX

theorem reciprocal_difference_differential {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f r : E → ℝ} {y : E} (hf : ContDiffAt ℝ 2 f y) (hr : ContDiffAt ℝ 2 r y)
    (hf0 : f y ≠ 0) (hr0 : r y ≠ 0) :
    ContDiffAt ℝ 2 (fun z => 2 / f z - 2 / r z) y ∧
      (2 / f y - 2 / r y = -2 * (f y - r y) / (r y * f y)) ∧
      ∀ d : E, fderiv ℝ (fun z => 2 / f z - 2 / r z) y d =
        -2 * fderiv ℝ (fun z => f z - r z) y d / (f y) ^ 2 +
          2 * (f y - r y) * (f y + r y) * fderiv ℝ r y d / ((r y) ^ 2 * (f y) ^ 2) := by
  refine ⟨(contDiffAt_const.div hf hf0).sub (contDiffAt_const.div hr hr0), ?_, ?_⟩
  · field_simp; ring
  · intro d
    have HD := (((hasDerivAt_inv hf0).comp_hasFDerivAt y (hf.differentiableAt (by norm_num)).hasFDerivAt).const_mul 2).sub
      (((hasDerivAt_inv hr0).comp_hasFDerivAt y (hr.differentiableAt (by norm_num)).hasFDerivAt).const_mul 2)
    change HasFDerivAt (fun z => 2 / f z - 2 / r z) _ y at HD
    rw [HD.fderiv, fderiv_fun_sub (hf.differentiableAt (by norm_num)) (hr.differentiableAt (by norm_num))]
    simp only [sub_apply, smul_apply, smul_eq_mul]
    field_simp
    ring

theorem reciprocal_difference_value_bound {α F R : ℝ} (hα : 0 < α)
    (hF : 1 / α ≤ F) (hR : 1 / α ≤ R) :
    |2 / F - 2 / R| ≤ 2 * α ^ 2 * |F - R| := by
  have hF0 : 0 < F := (one_div_pos.mpr hα).trans_le hF
  have hR0 : 0 < R := (one_div_pos.mpr hα).trans_le hR
  have hFi : 1 / F ≤ α := (div_le_iff₀ hF0).mpr (by
    have H := (div_le_iff₀ hα).mp hF; nlinarith only [H])
  have hRi : 1 / R ≤ α := (div_le_iff₀ hR0).mpr (by
    have H := (div_le_iff₀ hα).mp hR; nlinarith only [H])
  have Heq : 2 / F - 2 / R = -2 * (F - R) / (R * F) := by field_simp; ring
  rw [Heq, abs_div, abs_mul, abs_of_pos (mul_pos hR0 hF0)]
  norm_num only [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ = (2 * |F - R|) * (1 / R * (1 / F)) := by ring
    _ ≤ (2 * |F - R|) * (α * α) := by gcongr
    _ = _ := by ring

theorem reciprocal_difference_derivative_bound {α F R Θ p q D : ℝ} (hα : 0 < α)
    (hF : 1 / α ≤ F) (hR : 1 / α ≤ R) (hq : |q| ≤ D / α ^ 2) :
    |-2 * p / F ^ 2 + 2 * Θ * (F + R) * q / (R ^ 2 * F ^ 2)| ≤
      2 * α ^ 2 * |p| + 4 * D * α * |Θ| := by
  have hF0 : 0 < F := (one_div_pos.mpr hα).trans_le hF
  have hR0 : 0 < R := (one_div_pos.mpr hα).trans_le hR
  have hFi : 1 / F ≤ α := (div_le_iff₀ hF0).mpr (by
    have H := (div_le_iff₀ hα).mp hF; nlinarith only [H])
  have hRi : 1 / R ≤ α := (div_le_iff₀ hR0).mpr (by
    have H := (div_le_iff₀ hα).mp hR; nlinarith only [H])
  have hFi2 : 1 / F ^ 2 ≤ α ^ 2 := by
    simpa only [div_pow, one_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ 1 / F) hFi 2
  have HC : (F + R) / (R ^ 2 * F ^ 2) ≤ 2 * α ^ 3 := by
    calc
      _ = (1 / R) * (1 / R) * (1 / F) + (1 / R) * (1 / F) * (1 / F) := by field_simp
      _ ≤ α * α * α + α * α * α := by gcongr
      _ = _ := by ring
  calc
    _ ≤ |-2 * p / F ^ 2| + |2 * Θ * (F + R) * q / (R ^ 2 * F ^ 2)| := abs_add_le _ _
    _ = (2 * |p|) * (1 / F ^ 2) + (2 * |Θ|) * ((F + R) / (R ^ 2 * F ^ 2)) * |q| := by
      rw [abs_div, abs_div]
      simp only [abs_mul, abs_neg, abs_of_pos hF0, abs_of_pos hR0,
        abs_of_pos (add_pos hF0 hR0), abs_pow]
      norm_num
      ring
    _ ≤ (2 * |p|) * α ^ 2 + (2 * |Θ|) * (2 * α ^ 3) * (D / α ^ 2) := by gcongr
    _ = _ := by field_simp; ring

/-- The reciprocal correction preserves the two amplitude-sensitive columns. -/
theorem reciprocal_difference_amplitude_bounds {α A D u v Θ ψ : ℝ} {p s : Fin 3 → ℝ}
    (hα : 0 < α ∧ α ≤ 1) (hA : 0 ≤ A) (hD : 0 ≤ D) (hu : 0 ≤ u) (hv : 0 ≤ v ∧ v ≤ 1)
    (hΘ : |Θ| ≤ A * α * u * v) (hψ : |ψ| ≤ 2 * α ^ 2 * |Θ|)
    (hp : |p 0| + |p 1| ≤ A * u * v / α ^ 2) (hp2 : |p 2| ≤ A * u / α ^ 2)
    (hs : ∀ i, |s i| ≤ 2 * α ^ 2 * |p i| + 4 * D * α * |Θ|) :
    |ψ| ≤ 10 * A * (D + 1) * α ^ 3 * u * v ∧
      |s 0| + |s 1| ≤ 10 * A * (D + 1) * u * v ∧
      |s 2| ≤ 10 * A * (D + 1) * u := by
  have hα0 := hα.1
  have hv0 := hv.1
  have hαsq : α ^ 2 ≤ 1 := pow_le_one₀ hα.1.le hα.2
  have HΘ : 4 * D * α * |Θ| ≤ 4 * D * A * u * v := by
    calc
      _ ≤ 4 * D * α * (A * α * u * v) := mul_le_mul_of_nonneg_left hΘ (by positivity)
      _ = (4 * D * A * u * v) * α ^ 2 := by ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) hαsq
  have HP : 2 * α ^ 2 * (|p 0| + |p 1|) ≤ 2 * A * u * v := by
    calc
      _ ≤ 2 * α ^ 2 * (A * u * v / α ^ 2) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by field_simp
  have HP2 : 2 * α ^ 2 * |p 2| ≤ 2 * A * u := by
    calc
      _ ≤ 2 * α ^ 2 * (A * u / α ^ 2) := mul_le_mul_of_nonneg_left hp2 (by positivity)
      _ = _ := by field_simp
  refine ⟨?_, ?_, ?_⟩
  · have H := mul_le_mul_of_nonneg_left hΘ (by positivity : 0 ≤ 2 * α ^ 2)
    nlinarith only [hψ, H, mul_nonneg hD (by positivity : 0 ≤ A * α ^ 3 * u * v),
      (by positivity : 0 ≤ A * α ^ 3 * u * v)]
  · nlinarith only [hs 0, hs 1, HΘ, HP, mul_nonneg hD (by positivity : 0 ≤ A * u * v),
      (by positivity : 0 ≤ A * u * v)]
  · have Hv := mul_le_mul_of_nonneg_left hv.2 (by positivity : 0 ≤ 4 * D * A * u)
    nlinarith only [hs 2, HΘ, HP2, Hv, mul_nonneg hD (by positivity : 0 ≤ A * u), mul_nonneg hA hu]

end BianchiIX
