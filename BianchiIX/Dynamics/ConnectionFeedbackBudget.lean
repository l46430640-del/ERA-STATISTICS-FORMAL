import BianchiIX.Dynamics.ConnectionMoments
import BianchiIX.Analysis.ConnectionFeedbackBounds

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem integral_connectionPhaseFeedbackRate {U P : ℝ → ℝ} {μ a b : ℝ} (hab : a ≤ b)
    (hU : ContinuousOn U (Icc a b)) (hP : ContinuousOn P (Icc a b)) :
    (∫ z in a..b, connectionPhaseFeedbackRate μ (z - a) (U z) (P z)) =
      (64 / μ ^ 2) * (∫ z in a..b, U z) + (64 / μ ^ 4) * (∫ z in a..b, P z ^ 2) +
      8192 * (∫ z in a..b, (z - a) * U z) + (8192 / μ ^ 5) * ∫ z in a..b, (z - a) * P z ^ 2 := by
  have htime : ContinuousOn (fun z : ℝ => z - a) (Icc a b) := continuousOn_id.sub continuousOn_const
  have h1 := (hU.const_mul (64 / μ ^ 2)).intervalIntegrable_of_Icc (μ := volume) hab
  have h2 := ((hP.pow 2).const_mul (64 / μ ^ 4)).intervalIntegrable_of_Icc (μ := volume) hab
  have h3 := ((htime.mul hU).const_mul 8192).intervalIntegrable_of_Icc (μ := volume) hab
  have h4 := ((htime.mul (hP.pow 2)).const_mul (8192 / μ ^ 5)).intervalIntegrable_of_Icc (μ := volume) hab
  simp only [Pi.pow_apply, Pi.mul_apply] at h2 h3 h4
  have heq (z : ℝ) : connectionPhaseFeedbackRate μ (z - a) (U z) (P z) =
      (64 / μ ^ 2) * U z + (64 / μ ^ 4) * P z ^ 2 + 8192 * ((z - a) * U z) +
        (8192 / μ ^ 5) * ((z - a) * P z ^ 2) := by unfold connectionPhaseFeedbackRate; ring
  simp_rw [heq]
  rw [intervalIntegral.integral_add ((h1.add h2).add h3) h4,
    intervalIntegral.integral_add (h1.add h2) h3, intervalIntegral.integral_add h1 h2]
  simp only [intervalIntegral.integral_const_mul]

theorem connectionLog_feedback_budget {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hsmall : Y a 1 ≤ (1 / 10000) / μ) (hwall : Y a 3 ≤ 1 / 10000) :
    (∫ z in a..b, connectionPhaseFeedbackRate μ (z - a) (Y z 1) (Y z 2 * Y z 3)) ≤
      connectionPhaseFeedbackBudget μ (Y a 1) (Y a 2 * Y a 3) ∧
      connectionPhaseFeedbackBudget μ (Y a 1) (Y a 2 * Y a 3) ≤ 1 / 16 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hc := HasDerivAt.continuousOn hY
  have hU := continuousOn_pi.mp hc 1
  have hP : ContinuousOn (fun z => Y z 2 * Y z 3) (Icc a b) :=
    (continuousOn_pi.mp hc 2).mul (continuousOn_pi.mp hc 3)
  have H := connectionLog_dissipative_moments hab hμ hY hm hu hv hw hentry
  constructor
  · rw [integral_connectionPhaseFeedbackRate (μ := μ) hab hU hP]
    apply (add_le_add (add_le_add
      (add_le_add (mul_le_mul_of_nonneg_left H.1 (by positivity : 0 ≤ 64 / μ ^ 2))
        (mul_le_mul_of_nonneg_left H.2.2.1 (by positivity : 0 ≤ 64 / μ ^ 4)))
      (mul_le_mul_of_nonneg_left H.2.1 (by norm_num : (0 : ℝ) ≤ 8192)))
      (mul_le_mul_of_nonneg_left H.2.2.2 (by positivity : 0 ≤ 8192 / μ ^ 5))).trans_eq
    unfold connectionPhaseFeedbackBudget
    field_simp
    ring
  · have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
    apply connectionPhaseFeedbackBudget_small hμ ⟨(hu a ha).1, hsmall⟩
    refine ⟨mul_nonneg (hv a ha).1.le (hw a ha).1, ?_⟩
    exact (mul_le_mul_of_nonneg_right (hv a ha).2 (hw a ha).1).trans (by simpa using hwall)

end BianchiIX
