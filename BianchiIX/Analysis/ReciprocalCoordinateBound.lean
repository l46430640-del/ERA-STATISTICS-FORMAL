import BianchiIX.Analysis.ReciprocalDifference

noncomputable section

namespace BianchiIX

theorem reciprocal_coordinate_differential_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {f : E → Fin n → ℝ} {x : E} {α D : ℝ} (i : Fin n)
    (hf : ContDiffAt ℝ 2 f x) (hα : 0 < α) (hD : 0 ≤ D)
    (hval : 1 / α ≤ f x i) (hder : ‖fderiv ℝ f x‖ ≤ D / α ^ 2) :
    ContDiffAt ℝ 2 (fun y => 2 / f y i) x ∧
      ∀ v : E, |fderiv ℝ (fun y => 2 / f y i) x v| ≤ 2 * D * ‖v‖ := by
  have hr : 0 < f x i := (one_div_pos.mpr hα).trans_le hval
  have HR := hasFDerivAt_pi'.mp (hf.differentiableAt (by norm_num)).hasFDerivAt i
  have HD := ((hasDerivAt_inv hr.ne').comp_hasFDerivAt x HR).const_mul 2
  change HasFDerivAt (fun y => 2 / f y i) _ x at HD
  refine ⟨contDiffAt_const.div ((contDiffAt_pi.mp hf) i) hr.ne', ?_⟩
  intro v
  have HE : fderiv ℝ (fun y => 2 / f y i) x v = -2 * fderiv ℝ f x v i / (f x i) ^ 2 := by
    rw [HD.fderiv]
    simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
    ring
  have Hpart : |fderiv ℝ f x v i| ≤ (D / α ^ 2) * ‖v‖ := (norm_le_pi_norm _ i).trans
    (((fderiv ℝ f x).le_opNorm v).trans (mul_le_mul_of_nonneg_right hder (norm_nonneg v)))
  have Hinv : 1 / f x i ≤ α := (div_le_iff₀ hr).mpr (by
    have H := (div_le_iff₀ hα).mp hval; nlinarith only [H])
  have Hinv2 : 1 / (f x i) ^ 2 ≤ α ^ 2 := by
    simpa only [div_pow, one_pow] using pow_le_pow_left₀ (by positivity : 0 ≤ 1 / f x i) Hinv 2
  rw [HE, abs_div, abs_mul, abs_of_nonneg (sq_nonneg (f x i))]
  norm_num only [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ = (2 * |fderiv ℝ f x v i|) * (1 / (f x i) ^ 2) := by ring
    _ ≤ (2 * ((D / α ^ 2) * ‖v‖)) * α ^ 2 := by gcongr
    _ = _ := by field_simp

end BianchiIX
