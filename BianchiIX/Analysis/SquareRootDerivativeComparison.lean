import BianchiIX.Analysis.SquareRootRate

noncomputable section

namespace BianchiIX

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_fderiv_sqrt_sub_sqrt_le {Q S : E → ℝ} {x : E}
    (HQ : DifferentiableAt ℝ Q x) (HS : DifferentiableAt ℝ S x)
    (hQ : 0 < Q x) (hS : 0 < S x) :
    ‖fderiv ℝ (fun y => Real.sqrt (Q y) - Real.sqrt (S y)) x‖ ≤
      ‖fderiv ℝ (fun y => Q y - S y) x‖ / (2 * Real.sqrt (S x)) +
        |Real.sqrt (Q x) - Real.sqrt (S x)| * ‖fderiv ℝ Q x‖ /
          (2 * Real.sqrt (Q x) * Real.sqrt (S x)) := by
  have hR := Real.sqrt_pos.mpr hQ
  have hP := Real.sqrt_pos.mpr hS
  have HR := HQ.hasFDerivAt.sqrt hQ.ne'
  have HP := HS.hasFDerivAt.sqrt hS.ne'
  have Hdiff := HR.sub HP
  have HD := HQ.hasFDerivAt.sub HS.hasFDerivAt
  change HasFDerivAt (fun y => Real.sqrt (Q y) - Real.sqrt (S y)) _ x at Hdiff
  change HasFDerivAt (fun y => Q y - S y) _ x at HD
  have Heq : fderiv ℝ (fun y => Real.sqrt (Q y) - Real.sqrt (S y)) x =
      (1 / (2 * Real.sqrt (S x))) • fderiv ℝ (fun y => Q y - S y) x +
        ((Real.sqrt (S x) - Real.sqrt (Q x)) / (2 * Real.sqrt (Q x) * Real.sqrt (S x))) • fderiv ℝ Q x := by
    rw [Hdiff.fderiv, HD.fderiv]
    ext v
    simp only [sub_apply, smul_apply, add_apply, smul_eq_mul]
    field_simp
    ring
  rw [Heq]
  apply (norm_add_le _ _).trans_eq
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.sqrt (S x))), abs_div,
    abs_of_pos (by positivity : 0 < 2 * Real.sqrt (Q x) * Real.sqrt (S x)), abs_sub_comm]
  ring

/-- First-order comparison of square roots retains the small coefficient on a fixed radial annulus. -/
theorem sqrt_sub_sqrt_derivative_bound {Q S : E → ℝ} {x : E} {A c b n : ℝ}
    (HQ : DifferentiableAt ℝ Q x) (HS : DifferentiableAt ℝ S x)
    (hA : 0 ≤ A) (hc : 0 < c) (hb : 0 < b) (hn : 0 ≤ n)
    (hQ : c * b ≤ Real.sqrt (Q x)) (hS : c * b ≤ Real.sqrt (S x))
    (Hval : |Real.sqrt (Q x) - Real.sqrt (S x)| ≤ A * n * b)
    (HDQ : ‖fderiv ℝ Q x‖ ≤ A * b)
    (HDS : ‖fderiv ℝ (fun y => Q y - S y) x‖ ≤ A * n * b) :
    DifferentiableAt ℝ (fun y => Real.sqrt (Q y) - Real.sqrt (S y)) x ∧
      ‖fderiv ℝ (fun y => Real.sqrt (Q y) - Real.sqrt (S y)) x‖ ≤
        (A / c + A ^ 2 / c ^ 2) * n := by
  have hR : 0 < Real.sqrt (Q x) := (mul_pos hc hb).trans_le hQ
  have hP : 0 < Real.sqrt (S x) := (mul_pos hc hb).trans_le hS
  have hQpos := Real.sqrt_pos.mp hR
  have hSpos := Real.sqrt_pos.mp hP
  refine ⟨(HQ.sqrt hQpos.ne').sub (HS.sqrt hSpos.ne'), ?_⟩
  apply (norm_fderiv_sqrt_sub_sqrt_le HQ HS hQpos hSpos).trans
  have Hfirst : ‖fderiv ℝ (fun y => Q y - S y) x‖ / (2 * Real.sqrt (S x)) ≤ A / c * n := by
    calc
      _ ≤ A * n * b / (2 * Real.sqrt (S x)) := div_le_div_of_nonneg_right HDS (by positivity)
      _ ≤ A * n * b / (c * b) := div_le_div_of_nonneg_left (by positivity)
        (mul_pos hc hb) (by linarith only [hS, hP])
      _ = _ := by field_simp
  have Hsecond : |Real.sqrt (Q x) - Real.sqrt (S x)| * ‖fderiv ℝ Q x‖ /
      (2 * Real.sqrt (Q x) * Real.sqrt (S x)) ≤ A ^ 2 / c ^ 2 * n := by
    calc
      _ ≤ (A * n * b) * (A * b) / (2 * Real.sqrt (Q x) * Real.sqrt (S x)) := by
        gcongr
      _ ≤ (A * n * b) * (A * b) / (c * b) ^ 2 := div_le_div_of_nonneg_left (by positivity)
        (sq_pos_of_pos (mul_pos hc hb)) (by
          have HM := mul_le_mul hQ hS (mul_pos hc hb).le hR.le
          nlinarith only [HM, mul_pos hR hP])
      _ = _ := by field_simp
  nlinarith only [Hfirst, Hsecond]

end BianchiIX
