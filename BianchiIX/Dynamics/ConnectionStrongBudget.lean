import BianchiIX.Dynamics.ConnectionFeedbackBudget
import BianchiIX.Analysis.ConnectionStrongForcing

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem integral_connectionStrongSource {U P : ℝ → ℝ} {μ u x a b : ℝ} (hab : a ≤ b)
    (hU : ContinuousOn U (Icc a b)) (hP : ContinuousOn P (Icc a b)) :
    (∫ z in a..b, connectionStrongSource μ u (U z) (P z) x) =
      (|x| * (32 + 16384 * u)) * (∫ z in a..b, U z) +
        (|x| * 16384 * u / μ ^ 5) * ∫ z in a..b, P z ^ 2 := by
  have h1 := (hU.const_mul (|x| * (32 + 16384 * u))).intervalIntegrable_of_Icc (μ := volume) hab
  have h2 := ((hP.pow 2).const_mul (|x| * 16384 * u / μ ^ 5)).intervalIntegrable_of_Icc (μ := volume) hab
  simp only [Pi.pow_apply] at h2
  have hid (z : ℝ) : connectionStrongSource μ u (U z) (P z) x =
      (|x| * (32 + 16384 * u)) * U z + (|x| * 16384 * u / μ ^ 5) * P z ^ 2 := by
    unfold connectionStrongSource
    ring
  simp_rw [hid]
  rw [intervalIntegral.integral_add h1 h2]
  simp only [intervalIntegral.integral_const_mul]

theorem connectionLog_strong_source_budget {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1) (hentry : Y a 1 ≤ Y a 2) (x : ℝ) :
    (∫ z in a..b, connectionStrongSource μ (Y a 1) (Y z 1) (Y z 2 * Y z 3) x) ≤
      connectionStrongSourceBudget μ (Y a 1) (Y a 2 * Y a 3) x := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hu0 := (hu a ⟨le_rfl, hab⟩).1
  have hc := HasDerivAt.continuousOn hY
  have hU := continuousOn_pi.mp hc 1
  have hP : ContinuousOn (fun z => Y z 2 * Y z 3) (Icc a b) :=
    (continuousOn_pi.mp hc 2).mul (continuousOn_pi.mp hc 3)
  rw [integral_connectionStrongSource hab hU hP]
  have H := connectionLog_dissipative_moments hab hμ hY hm hu hv hw hentry
  apply (add_le_add (mul_le_mul_of_nonneg_left H.1 (by positivity : 0 ≤ |x| * (32 + 16384 * Y a 1)))
    (mul_le_mul_of_nonneg_left H.2.2.1 (by positivity : 0 ≤ |x| * 16384 * Y a 1 / μ ^ 5))).trans_eq
  unfold connectionStrongSourceBudget
  field_simp
  ring

end BianchiIX
