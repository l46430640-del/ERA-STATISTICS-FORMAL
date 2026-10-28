import BianchiIX.Dynamics.CoreContraction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem integral_exp_decay {a b c : ℝ} (hc : 0 < c) :
    (∫ z in a..b, Real.exp (-c * (z - a))) = (1 - Real.exp (-c * (b - a))) / c := by
  have hd (z : ℝ) : HasDerivAt (fun u => -Real.exp (-c * (u - a)) / c)
      (Real.exp (-c * (z - a))) z := by
    convert! (((hasDerivAt_id z).sub_const a).const_mul (-c)).exp.neg.div_const c using 1
    simp only [id_eq]
    field_simp
  have hcont : Continuous (fun z => Real.exp (-c * (z - a))) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hd z) (hcont.intervalIntegrable _ _)]
  simp only [sub_self, mul_zero, Real.exp_zero]
  ring

theorem integral_exp_decay_le {a b c : ℝ} (hc : 0 < c) :
    (∫ z in a..b, Real.exp (-c * (z - a))) ≤ 1 / c := by
  rw [integral_exp_decay hc]
  exact (div_le_div_iff_of_pos_right hc).mpr (by linarith [Real.exp_pos (-c * (b - a))])

theorem integral_le_of_exp_decay {f : ℝ → ℝ} {a b c B : ℝ} (hab : a ≤ b) (hc : 0 < c)
    (hB : 0 ≤ B) (hf : ContinuousOn f (Icc a b))
    (hbound : ∀ z ∈ Icc a b, f z ≤ B * Real.exp (-c * (z - a))) :
    (∫ z in a..b, f z) ≤ B / c := by
  have hg : Continuous (fun z => B * Real.exp (-c * (z - a))) := by fun_prop
  have H := intervalIntegral.integral_mono_on (μ := volume) hab
    (hf.intervalIntegrable_of_Icc hab) (hg.intervalIntegrable _ _) hbound
  rw [intervalIntegral.integral_const_mul] at H
  exact H.trans ((mul_le_mul_of_nonneg_left (integral_exp_decay_le hc) hB).trans_eq (by ring))

theorem sech_le_exp {a b : ℝ} (hab : a ≤ b) :
    1 / Real.cosh b ≤ (1 / Real.cosh a) * Real.exp (b - a) := by
  have hd (z : ℝ) : HasDerivAt (fun u => 1 / Real.cosh u)
      (-Real.sinh z / Real.cosh z ^ 2) z := by
    convert! (Real.hasDerivAt_cosh z).inv (ne_of_gt (Real.cosh_pos z)) using 1
    ext u
    simp
  have hbound (z : ℝ) : -Real.sinh z / Real.cosh z ^ 2 ≤ 1 / Real.cosh z := by
    have H : -Real.sinh z ≤ Real.cosh z := by
      simpa only [Real.sinh_neg, Real.cosh_neg] using (Real.sinh_lt_cosh (x := -z)).le
    apply (div_le_iff₀ (sq_pos_of_pos (Real.cosh_pos z))).mpr
    convert! H using 1
    field_simp
  simpa only [one_mul] using le_exp_of_linear_deriv_le (I := univ) convex_univ
    (c := 1) (fun z _ => hd z) (fun z _ => by simpa only [one_mul] using hbound z)
    (mem_univ a) (mem_univ b) hab

/-- Endpoint control replaces an enclosing arcosh interval in the slow-wall integral. -/
theorem integral_cosh_sq_le_endpoints {a b : ℝ} (hab : a ≤ b) :
    (∫ z in a..b, Real.cosh z ^ 2) ≤ Real.cosh a ^ 2 + Real.cosh b ^ 2 := by
  have hd (z : ℝ) : HasDerivAt (fun u => Real.sinh u * Real.cosh u)
      (Real.cosh z ^ 2 + Real.sinh z ^ 2) z := by
    convert! (Real.hasDerivAt_sinh z).mul (Real.hasDerivAt_cosh z) using 1
    ring
  have hc : Continuous (fun z => Real.cosh z ^ 2 + Real.sinh z ^ 2) := by fun_prop
  have hcosh : Continuous (fun z => Real.cosh z ^ 2) := by fun_prop
  have H := intervalIntegral.integral_mono_on (μ := volume) hab (hcosh.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
    (fun z _ => le_add_of_nonneg_right (sq_nonneg (Real.sinh z)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hd z) (hc.intervalIntegrable _ _)] at H
  have hb := mul_le_mul_of_nonneg_right (Real.sinh_lt_cosh (x := b)).le (Real.cosh_pos b).le
  have ha := mul_le_mul_of_nonneg_right
    (show -Real.sinh a ≤ Real.cosh a by
      simpa only [Real.sinh_neg, Real.cosh_neg] using (Real.sinh_lt_cosh (x := -a)).le) (Real.cosh_pos a).le
  nlinarith

theorem integral_le_of_cosh_sq {f : ℝ → ℝ} {a b B K : ℝ} (hab : a ≤ b)
    (hB : 0 ≤ B) (hf : ContinuousOn f (Icc a b))
    (hbound : ∀ z ∈ Icc a b, f z ≤ B * Real.cosh z ^ 2)
    (ha : Real.cosh a ≤ K) (hb : Real.cosh b ≤ K) :
    (∫ z in a..b, f z) ≤ 2 * B * K ^ 2 := by
  have hg : Continuous (fun z => B * Real.cosh z ^ 2) := by fun_prop
  have H := intervalIntegral.integral_mono_on (μ := volume) hab (hf.intervalIntegrable_of_Icc hab) (hg.intervalIntegrable _ _) hbound
  rw [intervalIntegral.integral_const_mul] at H
  have hsq : Real.cosh a ^ 2 + Real.cosh b ^ 2 ≤ 2 * K ^ 2 := by
    have ha' := (sq_le_sq₀ (Real.cosh_pos a).le ((Real.cosh_pos a).le.trans ha)).mpr ha
    have hb' := (sq_le_sq₀ (Real.cosh_pos b).le ((Real.cosh_pos b).le.trans hb)).mpr hb
    linarith
  exact H.trans ((mul_le_mul_of_nonneg_left ((integral_cosh_sq_le_endpoints hab).trans hsq) hB).trans_eq (by ring))

theorem abs_sub_le_integral_bound {f f' B : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ z ∈ Icc a b, HasDerivAt f (f' z) z) (hB : ContinuousOn B (Icc a b))
    (hbound : ∀ z ∈ Icc a b, |f' z| ≤ B z) :
    |f b - f a| ≤ ∫ z in a..b, B z := by
  apply (norm_sub_le_integral_of_norm_deriv_le_of_le hab
    (fun z hz => (hf z hz).continuousAt.continuousWithinAt)
    (fun z hz => (hf z ⟨hz.1.le, hz.2.le⟩).differentiableAt.differentiableWithinAt)
    (ae_of_all _ fun z hz => ?_) (hB.intervalIntegrable_of_Icc hab))
  rw [(hf z ⟨hz.1.le, hz.2.le⟩).deriv, Real.norm_eq_abs]
  exact hbound z ⟨hz.1.le, hz.2.le⟩

end BianchiIX
