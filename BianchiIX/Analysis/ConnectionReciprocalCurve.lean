import BianchiIX.Analysis.PartialCoreReciprocalError

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

/-- The combined radial error gives the value and ordinary derivative bounds of E.28. -/
theorem connection_reciprocal_radial_bounds {g k : ℝ → ℝ} {x r K C U P : ℝ}
    (hr : 0 < r ∧ r ≤ 1) (hK : 1 ≤ K) (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hP : 0 ≤ P ∧ P ≤ 1) (hg : DifferentiableAt ℝ g x) (hk : DifferentiableAt ℝ k x)
    (hk6 : 6 ≤ k x) (hklo : 2 / (K * r) ≤ k x) (hglo : k x / 4 ≤ g x)
    (hdk : |deriv k x| ≤ K / r ^ 2)
    (he : |g x - (k x - 2)| ≤ C * (U + r * P ^ 2))
    (hde : |deriv g x - deriv k x| ≤ C * (U + r * P) / r ^ 2) :
    let E := fun a => 2 / g a - (2 / k a) / (1 - 2 / k a)
    DifferentiableAt ℝ E x ∧ |E x| ≤ 8 * C * K ^ 2 * r ^ 2 * (U + r * P ^ 2) ∧
      |deriv E x| ≤ (8 * C * K ^ 2 + 32 * C * K ^ 4) * (U + r * P) := by
  intro E
  have hr0 := hr.1
  have hK0 : 0 < K := by linarith only [hK]
  have hP0 := hP.1
  have hα : 0 < 2 * K * r := by positivity
  have hfloor : 1 / (2 * K * r) ≤ k x / 4 := by
    calc
      _ = (2 / (K * r)) / 4 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hklo (by norm_num)
  have hgf := hfloor.trans hglo
  have hkf : 1 / (2 * K * r) ≤ k x - 2 := hfloor.trans (by linarith only [hk6])
  have hg0 : 0 < g x := (one_div_pos.mpr hα).trans_le hgf
  have hk0 : 0 < k x - 2 := by linarith only [hk6]
  have Hk : HasDerivAt (fun a => k a - 2) (deriv k x) x := hk.hasDerivAt.sub_const 2
  have HD := hasDerivAt_reciprocal_error hg.hasDerivAt Hk hg0.ne' hk0.ne'
  have Hval : |2 / g x - 2 / (k x - 2)| ≤ 8 * C * K ^ 2 * r ^ 2 * (U + r * P ^ 2) :=
    (reciprocal_difference_value_bound hα hgf hkf).trans
    ((mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 * (2 * K * r) ^ 2)).trans_eq (by ring))
  have hq : |deriv k x| ≤ (4 * K ^ 3) / (2 * K * r) ^ 2 := hdk.trans_eq (by field_simp; norm_num)
  have Hb := reciprocal_difference_derivative_bound hα hgf hkf hq
    (Θ := g x - (k x - 2)) (p := deriv g x - deriv k x)
  have H1 : 2 * (2 * K * r) ^ 2 * |deriv g x - deriv k x| ≤
      8 * C * K ^ 2 * (U + r * P) :=
    (mul_le_mul_of_nonneg_left hde (by positivity)).trans_eq (by field_simp; ring)
  have hPr : 0 ≤ r * P ∧ r * P ≤ 1 :=
    ⟨mul_nonneg hr.1.le hP.1, (mul_le_mul hr.2 hP.2 hP.1 (by norm_num)).trans_eq (by ring)⟩
  have hsmall : r * (U + r * P ^ 2) ≤ U + r * P := by
    nlinarith only [mul_le_mul_of_nonneg_right hr.2 hU,
      mul_le_mul_of_nonneg_right hPr.2 hPr.1]
  have H2 : 4 * (4 * K ^ 3) * (2 * K * r) * |g x - (k x - 2)| ≤
      32 * C * K ^ 4 * (U + r * P) := by
    calc
      _ ≤ 4 * (4 * K ^ 3) * (2 * K * r) * (C * (U + r * P ^ 2)) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = (32 * C * K ^ 4) * (r * (U + r * P ^ 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (by positivity)
  have HM : E =ᶠ[𝓝 x] (fun a => 2 / g a - 2 / (k a - 2)) := by
    filter_upwards [hk.continuousAt.eventually (lt_mem_nhds (show 2 < k x by linarith only [hk6]))] with a ha
    have hka : k a ≠ 0 := ne_of_gt (by linarith only [ha])
    have hka2 : k a - 2 ≠ 0 := ne_of_gt (by linarith only [ha])
    dsimp only [E]
    congr 1
    field_simp
  refine ⟨HD.differentiableAt.congr_of_eventuallyEq HM, ?_, ?_⟩
  · rw [HM.self_of_nhds]
    exact Hval
  · rw [HM.deriv_eq, HD.deriv]
    exact Hb.trans ((add_le_add H1 H2).trans_eq (by ring))

end BianchiIX
