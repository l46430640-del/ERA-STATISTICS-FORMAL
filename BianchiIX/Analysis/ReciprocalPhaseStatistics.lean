import BianchiIX.Analysis.ReciprocalDifference
import Mathlib.LinearAlgebra.Matrix.Notation

noncomputable section

namespace BianchiIX

theorem two_div_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {y : E} (hf : DifferentiableAt ℝ f y) (h0 : f y ≠ 0) (v : E) :
    fderiv ℝ (fun z => 2 / f z) y v = -2 * fderiv ℝ f y v / (f y) ^ 2 := by
  have HD := ((hasDerivAt_inv h0).comp_hasFDerivAt y hf.hasFDerivAt).const_mul 2
  change HasFDerivAt (fun z => 2 / f z) _ y at HD
  rw [HD.fderiv]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- The exact relative radial identity in (D.32). -/
theorem reciprocal_phase_relative_identity {α x p : ℝ} (hα : α ≠ 0) (hx : x ≠ 0) :
    -α ^ 2 * (-2 * p / x ^ 2) = (1 + (2 * p - 1)) / (1 + (x - α) / α) ^ 2 ∧
      (1 + (2 * p - 1)) / (1 + (x - α) / α) ^ 2 - 1 =
        ((2 * p - 1) - 2 * ((x - α) / α) - ((x - α) / α) ^ 2) /
          (1 + (x - α) / α) ^ 2 := by
  have H : 1 + (x - α) / α = x / α := by field_simp; ring
  rw [H]
  constructor <;> field_simp <;> ring

/-- Inverting a small positive phase costs two powers in value and three in its radial error. -/
theorem reciprocal_small_phase_bounds {α x p A b : ℝ}
    (hα : 0 < α ∧ α ≤ 1) (hA : 0 ≤ A) (hb : 0 ≤ b)
    (hsmall : A * b ≤ α / 4) (herr : |x - α| + |p - 1 / 2| ≤ A * b) :
    0 < x ∧ 1 / x ^ 2 ≤ 4 / α ^ 2 ∧
      |2 / x - 2 / α| ≤ 4 * A * b / α ^ 2 ∧
      |-2 * p / x ^ 2 + 1 / α ^ 2| ≤ 20 * A * b / α ^ 3 := by
  have hα0 := hα.1
  have Hx : |x - α| ≤ A * b := (le_add_of_nonneg_right (abs_nonneg _)).trans herr
  have Hp : |p - 1 / 2| ≤ A * b := (le_add_of_nonneg_left (abs_nonneg _)).trans herr
  have Hlo : α / 2 ≤ x := by linarith only [(abs_le.mp Hx).1, hsmall, hα.1]
  have Hhi : x ≤ 2 * α := by linarith only [(abs_le.mp Hx).2, hsmall, hα.1]
  have hx : 0 < x := (by positivity : 0 < α / 2).trans_le Hlo
  have Hinv : 1 / x ≤ 2 / α := by
    apply (div_le_div_iff₀ hx hα.1).mpr
    linarith only [Hlo]
  have Hinv2 : 1 / x ^ 2 ≤ 4 / α ^ 2 := by
    simpa only [div_pow, one_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using
      pow_le_pow_left₀ (by positivity : 0 ≤ 1 / x) Hinv 2
  refine ⟨hx, Hinv2, ?_, ?_⟩
  · have HE : 2 / x - 2 / α = -2 * (x - α) / (x * α) := by field_simp; ring
    rw [HE, abs_div, abs_mul, abs_of_pos (mul_pos hx hα.1)]
    norm_num only [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      _ = (2 * |x - α|) * (1 / x) / α := by ring
      _ ≤ (2 * (A * b)) * (2 / α) / α := by gcongr
      _ = _ := by ring
  · have HE : -2 * p / x ^ 2 + 1 / α ^ 2 =
        -2 * (p - 1 / 2) / x ^ 2 + (x - α) * (x + α) / (α ^ 2 * x ^ 2) := by
      field_simp; ring
    rw [HE]
    calc
      _ ≤ |-2 * (p - 1 / 2) / x ^ 2| + |(x - α) * (x + α) / (α ^ 2 * x ^ 2)| := abs_add_le _ _
      _ = (2 * |p - 1 / 2|) * (1 / x ^ 2) +
          (|x - α| * (x + α)) * (1 / x ^ 2) / α ^ 2 := by
        simp only [abs_div, abs_mul, abs_neg, abs_of_pos (add_pos hx hα.1),
          abs_of_nonneg (sq_nonneg x), abs_of_nonneg (sq_nonneg α)]
        norm_num
        ring
      _ ≤ (2 * (A * b)) * (4 / α ^ 2) +
          ((A * b) * (3 * α)) * (4 / α ^ 2) / α ^ 2 := by
        gcongr
        linarith only [Hhi]
      _ = 8 * A * b / α ^ 2 + 12 * A * b / α ^ 3 := by field_simp; ring
      _ ≤ 20 * A * b / α ^ 3 := by
        have H : 8 * A * b * α ≤ 8 * A * b := mul_le_of_le_one_right (by positivity) hα.2
        apply (le_div_iff₀ (by positivity : 0 < α ^ 3)).mpr
        field_simp
        nlinarith only [H]

theorem reciprocal_phase_statistics {f : (Fin 3 → ℝ) → ℝ} {y : Fin 3 → ℝ}
    {α A b : ℝ} (hf : ContDiffAt ℝ 2 f y) (hα : 0 < α ∧ α ≤ 1)
    (hA : 0 ≤ A) (hb : 0 ≤ b) (hsmall : A * b ≤ α / 4)
    (herr : |f y - α| + |fderiv ℝ f y (Pi.single 0 1) - 1 / 2| ≤ A * b)
    (hwall : |fderiv ℝ f y (Pi.single 1 1)| + |fderiv ℝ f y (Pi.single 2 1)| ≤ A) :
    0 < f y ∧ ContDiffAt ℝ 2 (fun z => 2 / f z) y ∧
      |2 / f y - 2 / α| ≤ 4 * A * b / α ^ 2 ∧
      |fderiv ℝ (fun z => 2 / f z) y (Pi.single 0 1) + 1 / α ^ 2| ≤ 20 * A * b / α ^ 3 ∧
      |fderiv ℝ (fun z => 2 / f z) y (Pi.single 1 1)| +
        |fderiv ℝ (fun z => 2 / f z) y (Pi.single 2 1)| ≤ 8 * A / α ^ 2 := by
  obtain ⟨hx, Hinv, Hv, Hr⟩ := reciprocal_small_phase_bounds hα hA hb hsmall herr
  have HD := two_div_fderiv (hf.differentiableAt (by norm_num)) hx.ne'
  refine ⟨hx, contDiffAt_const.div hf hx.ne', Hv, by rw [HD]; exact Hr, ?_⟩
  rw [HD, HD]
  simp only [abs_div, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg (f y))]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ = 2 * (|fderiv ℝ f y (Pi.single 1 1)| + |fderiv ℝ f y (Pi.single 2 1)|) * (1 / (f y) ^ 2) := by ring
    _ ≤ 2 * A * (4 / α ^ 2) := by gcongr
    _ = _ := by ring

end BianchiIX
