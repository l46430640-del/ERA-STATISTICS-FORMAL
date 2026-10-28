import BianchiIX.Analysis.ConnectionGrowingSources
import BianchiIX.Dynamics.ConnectionGrowingMoments

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem integral_connectionGrowingSources {Y : ℝ → ProjectiveState} {μ w a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn Y (Icc a b)) :
    (∫ z in a..b, connectionGrowingStrongSource μ w (Y z)) =
      (32 / (μ * w)) * ((∫ z in a..b, Y z 3 ^ 2) + ∫ z in a..b, Y z 2 * Y z 3) +
        (32 / w) * (∫ z in a..b, Y z 1 * Y z 3) ∧
    (∫ z in a..b, connectionGrowingWeakSource μ w (Y z)) =
      (64 / (μ * w)) * (∫ z in a..b, Y z 3 ^ 2) + (64 * μ / w) * (∫ z in a..b, Y z 1 * Y z 3) ∧
    (∫ z in a..b, connectionGrowingPhaseSource μ w (Y z)) =
      (32 / w) * (∫ z in a..b, Y z 1 * Y z 3) +
        (32 / (μ ^ 3 * w)) * (∫ z in a..b, (Y z 2 * Y z 3) ^ 2) := by
  have hW : IntervalIntegrable (fun z => Y z 3 ^ 2) volume a b :=
    ((continuousOn_pi.mp hc 3).pow 2).intervalIntegrable_of_Icc hab
  have hP : IntervalIntegrable (fun z => Y z 2 * Y z 3) volume a b :=
    ((continuousOn_pi.mp hc 2).mul (continuousOn_pi.mp hc 3)).intervalIntegrable_of_Icc hab
  have hUW : IntervalIntegrable (fun z => Y z 1 * Y z 3) volume a b :=
    ((continuousOn_pi.mp hc 1).mul (continuousOn_pi.mp hc 3)).intervalIntegrable_of_Icc hab
  have hP2 : IntervalIntegrable (fun z => (Y z 2 * Y z 3) ^ 2) volume a b :=
    (((continuousOn_pi.mp hc 2).mul (continuousOn_pi.mp hc 3)).pow 2).intervalIntegrable_of_Icc hab
  have hadd (f g : ℝ → ℝ) (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
      (c d : ℝ) : (∫ z in a..b, c * f z + d * g z) = c * (∫ z in a..b, f z) + d * ∫ z in a..b, g z := by
    rw [intervalIntegral.integral_add (hf.const_mul c) (hg.const_mul d)]
    simp only [intervalIntegral.integral_const_mul]
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = ∫ z in a..b, (32 / (μ * w)) * (Y z 3 ^ 2 + Y z 2 * Y z 3) + (32 / w) * (Y z 1 * Y z 3) := by
        apply intervalIntegral.integral_congr
        intro z _
        unfold connectionGrowingStrongSource
        ring
      _ = _ := by rw [hadd _ _ (hW.add hP) hUW, intervalIntegral.integral_add hW hP]
  · calc
      _ = ∫ z in a..b, (64 / (μ * w)) * Y z 3 ^ 2 + (64 * μ / w) * (Y z 1 * Y z 3) := by
        apply intervalIntegral.integral_congr
        intro z _
        unfold connectionGrowingWeakSource
        ring
      _ = _ := hadd _ _ hW hUW _ _
  · calc
      _ = ∫ z in a..b, (32 / w) * (Y z 1 * Y z 3) + (32 / (μ ^ 3 * w)) * (Y z 2 * Y z 3) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro z _
        unfold connectionGrowingPhaseSource
        ring
      _ = _ := hadd _ _ hUW hP2 _ _

theorem connectionLog_growing_source_integrals {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hentry : Y a 1 ≤ Y a 2) (hw0 : 0 < Y a 3) :
    (∫ z in a..b, connectionGrowingStrongSource μ (Y a 3) (Y z)) ≤
      32 * (1 + Y b 3 ^ 2 / (μ * Y a 3)) ∧
    (∫ z in a..b, connectionGrowingWeakSource μ (Y a 3) (Y z)) ≤
      256 * Y a 1 + 32 * Y b 3 ^ 2 / (μ * Y a 3) ∧
    (∫ z in a..b, connectionGrowingPhaseSource μ (Y a 3) (Y z)) ≤
      128 * Y a 1 / μ + 8 * Y a 3 / μ ^ 2 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hc := HasDerivAt.continuousOn hY
  have HI := integral_connectionGrowingSources (μ := μ) (w := Y a 3) hab hc
  have HM := connectionLog_growing_moments hab hμ hY hm hu hv hw hentry
  have HP := (connectionLog_dissipative_moments hab hμ hY hm hu hv hw hentry).2.2.1
  rw [HI.1, HI.2.1, HI.2.2]
  refine ⟨?_, ?_, ?_⟩
  · have H := add_le_add
      (mul_le_mul_of_nonneg_left (add_le_add HM.1 HM.2.2.2.1) (by positivity : 0 ≤ 32 / (μ * Y a 3)))
      (mul_le_mul_of_nonneg_left HM.2.1 (by positivity : 0 ≤ 32 / Y a 3))
    have hid : (32 / (μ * Y a 3)) * (Y b 3 ^ 2 / 2 + μ * (Y a 2 * Y a 3) / 2) +
        (32 / Y a 3) * (4 * Y a 1 * Y a 3 / μ) =
          16 * (Y b 3 ^ 2 / (μ * Y a 3)) + 16 * Y a 2 + 128 * Y a 1 / μ := by field_simp; ring
    rw [hid] at H
    have huμ : 128 * Y a 1 / μ ≤ 1 := (div_le_iff₀ hμ0).mpr (by linarith only [(hu a ha).2, hμ])
    have hq : 0 ≤ Y b 3 ^ 2 / (μ * Y a 3) := by positivity
    linarith only [H, huμ, (hv a ha).2, hq]
  · apply (add_le_add (mul_le_mul_of_nonneg_left HM.1 (by positivity : 0 ≤ 64 / (μ * Y a 3)))
      (mul_le_mul_of_nonneg_left HM.2.1 (by positivity : 0 ≤ 64 * μ / Y a 3))).trans_eq
    field_simp
    ring
  · have H := add_le_add (mul_le_mul_of_nonneg_left HM.2.1 (by positivity : 0 ≤ 32 / Y a 3))
      (mul_le_mul_of_nonneg_left HP (by positivity : 0 ≤ 32 / (μ ^ 3 * Y a 3)))
    have hid : (32 / Y a 3) * (4 * Y a 1 * Y a 3 / μ) +
        (32 / (μ ^ 3 * Y a 3)) * (μ * (Y a 2 * Y a 3) ^ 2 / 4) =
          128 * Y a 1 / μ + (8 * Y a 3 / μ ^ 2) * Y a 2 ^ 2 := by field_simp; ring
    rw [hid] at H
    have hv2 : Y a 2 ^ 2 ≤ 1 := by
      simpa using pow_le_pow_left₀ (hv a ha).1.le (hv a ha).2 2
    exact H.trans (add_le_add (le_refl _)
      ((mul_le_mul_of_nonneg_left hv2 (by positivity : 0 ≤ 8 * Y a 3 / μ ^ 2)).trans_eq (mul_one _)))

end BianchiIX
