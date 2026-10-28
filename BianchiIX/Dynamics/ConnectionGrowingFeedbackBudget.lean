import BianchiIX.Analysis.ConnectionGrowingFeedbackBounds
import BianchiIX.Dynamics.ConnectionGrowingSourceIntegrals

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem integral_connectionGrowingFeedbackSource {Y : ℝ → ProjectiveState} {μ u w a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn Y (Icc a b)) :
    (∫ z in a..b, connectionGrowingFeedbackSource μ u w (Y z)) =
      (1024 + 819200 * u) * (∫ z in a..b, Y z 1) +
      (5120 / (μ * w)) * (∫ z in a..b, Y z 1 * Y z 3 ^ 2) +
      (819200 * u / μ ^ 5) * (∫ z in a..b, (Y z 2 * Y z 3) ^ 2) +
      (4096 / (μ ^ 6 * w)) * (∫ z in a..b, (Y z 2 * Y z 3) ^ 2 * Y z 3 ^ 2) +
      (∫ z in a..b, connectionGrowingPhaseSource μ w (Y z)) := by
  have hcoord (i : Fin 4) := continuousOn_pi.mp hc i
  have hU : ContinuousOn (fun z => Y z 1) (Icc a b) := hcoord 1
  have hW : ContinuousOn (fun z => Y z 3 ^ 2) (Icc a b) := (hcoord 3).pow 2
  have hP : ContinuousOn (fun z => (Y z 2 * Y z 3) ^ 2) (Icc a b) := ((hcoord 2).mul (hcoord 3)).pow 2
  have h1 : IntervalIntegrable (fun z => (1024 + 819200 * u) * Y z 1) volume a b :=
    (hU.const_mul _).intervalIntegrable_of_Icc hab
  have h2 : IntervalIntegrable (fun z => (5120 / (μ * w)) * (Y z 1 * Y z 3 ^ 2)) volume a b :=
    ((hU.mul hW).const_mul _).intervalIntegrable_of_Icc hab
  have h3 : IntervalIntegrable (fun z => (819200 * u / μ ^ 5) * (Y z 2 * Y z 3) ^ 2) volume a b :=
    (hP.const_mul _).intervalIntegrable_of_Icc hab
  have h4 : IntervalIntegrable (fun z => (4096 / (μ ^ 6 * w)) * ((Y z 2 * Y z 3) ^ 2 * Y z 3 ^ 2)) volume a b :=
    ((hP.mul hW).const_mul _).intervalIntegrable_of_Icc hab
  have h5 : IntervalIntegrable (fun z => connectionGrowingPhaseSource μ w (Y z)) volume a b :=
    ((continuous_connectionGrowingSources μ w).2.2.comp_continuousOn hc).intervalIntegrable_of_Icc hab
  have hid (z : ℝ) : connectionGrowingFeedbackSource μ u w (Y z) =
      (1024 + 819200 * u) * Y z 1 + (5120 / (μ * w)) * (Y z 1 * Y z 3 ^ 2) +
      (819200 * u / μ ^ 5) * (Y z 2 * Y z 3) ^ 2 +
      (4096 / (μ ^ 6 * w)) * ((Y z 2 * Y z 3) ^ 2 * Y z 3 ^ 2) + connectionGrowingPhaseSource μ w (Y z) := by
    unfold connectionGrowingFeedbackSource
    ring
  simp_rw [hid]
  rw [intervalIntegral.integral_add (((h1.add h2).add h3).add h4) h5,
    intervalIntegral.integral_add ((h1.add h2).add h3) h4,
    intervalIntegral.integral_add (h1.add h2) h3, intervalIntegral.integral_add h1 h2]
  simp only [intervalIntegral.integral_const_mul]

theorem connectionLog_growing_feedback_source_budget {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hw0 : 0 < Y a 3) :
    (∫ z in a..b, connectionGrowingFeedbackSource μ (Y a 1) (Y a 3) (Y z)) ≤
      connectionGrowingFeedbackBudget μ (Y a 1) (Y a 3) := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hu0 := (hu a ha).1
  have HV : Y a 2 ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ (hv a ha).1.le (hv a ha).2 2
  have HW : Y b 3 ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ (hw b hb).1 (hw b hb).2 2
  have HP : (Y a 2 * Y a 3) ^ 2 ≤ Y a 3 ^ 2 := by
    rw [mul_pow]
    exact (mul_le_mul_of_nonneg_right HV (sq_nonneg _)).trans_eq (one_mul _)
  have HM := connectionLog_growing_moments hab hμ hY hm hu hv hw hentry
  have HD := connectionLog_dissipative_moments hab hμ hY hm hu hv hw hentry
  have Hsource := (connectionLog_growing_source_integrals hab hμ hY hm hu hv hw hentry hw0).2.2
  have HP2 : (∫ z in a..b, (Y z 2 * Y z 3) ^ 2) ≤ μ * Y a 3 ^ 2 / 4 :=
    HD.2.2.1.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left HP hμ0.le) (by norm_num))
  have HPW : (∫ z in a..b, (Y z 2 * Y z 3) ^ 2 * Y z 3 ^ 2) ≤ Y a 3 ^ 2 / 2 := by
    apply HM.2.2.2.2.trans
    exact div_le_div_of_nonneg_right
      ((mul_le_mul HP HW (sq_nonneg _) (sq_nonneg _)).trans_eq (mul_one _)) (by norm_num)
  rw [integral_connectionGrowingFeedbackSource hab (HasDerivAt.continuousOn hY)]
  apply (add_le_add (add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left HD.1 (by positivity : 0 ≤ 1024 + 819200 * Y a 1))
    (mul_le_mul_of_nonneg_left HM.2.2.1 (by positivity : 0 ≤ 5120 / (μ * Y a 3))))
    (mul_le_mul_of_nonneg_left HP2 (by positivity : 0 ≤ 819200 * Y a 1 / μ ^ 5)))
    (mul_le_mul_of_nonneg_left HPW (by positivity : 0 ≤ 4096 / (μ ^ 6 * Y a 3)))) Hsource).trans_eq
  unfold connectionGrowingFeedbackBudget
  field_simp
  ring

end BianchiIX
