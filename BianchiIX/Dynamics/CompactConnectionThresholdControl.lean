import BianchiIX.Dynamics.CompactConnectionPhaseBounds

noncomputable section

namespace BianchiIX

/-- One common wall box gives transversality, endpoint signs, and quantitative threshold estimates. -/
theorem exists_compact_connection_threshold_control :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 10000 ∧ ∀ η : ℝ, (0 < η ∧ η ≤ δ) →
      ∃ ε > (0 : ℝ), ε ≤ 1 / 2 ∧ ∃ A > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → (0 < Y 1 ∧ Y 1 ≤ ε) → (0 < Y 2 ∧ Y 2 ≤ ε) →
      coreTailValid η Y ∧ entranceReturnValid (compactConnectionEntry η Y) ∧
        ContDiffAt ℝ 2 (compactConnectionPhase η) Y ∧
        1 / 2 ≤ fderiv ℝ (compactConnectionPhase η) Y (Pi.single 0 1) ∧
        |compactConnectionPhase η Y - (Y 0 - 2)| ≤ 1 / 16 ∧
        |compactConnectionPhase η Y - (Y 0 - 2) + 2 * Y 1 / Y 0| ≤ A * (Y 1 + Y 2) ^ 2 ∧
        |fderiv ℝ (compactConnectionPhase η) Y (Pi.single 0 1) - 1| ≤ A * (Y 1 + Y 2) ∧
        |fderiv ℝ (compactConnectionPhase η) Y (Pi.single 1 1) + 2 / Y 0| +
          |fderiv ℝ (compactConnectionPhase η) Y (Pi.single 2 1)| ≤ A * (Y 1 + Y 2) := by
  obtain ⟨δ, hδ, hδsmall, HP⟩ := exists_compact_connection_phase_bounds
  refine ⟨δ, hδ, hδsmall, ?_⟩
  intro η hη
  obtain ⟨εp, hεp, A, hA, HP'⟩ := HP η hη
  let ε := min εp (min (1 / 64) (1 / (64 * (A + 1))))
  have hε : 0 < ε := lt_min hεp (lt_min (by norm_num) (by positivity))
  have hεp' : ε ≤ εp := min_le_left _ _
  have hε64 : ε ≤ 1 / 64 := (min_le_right _ _).trans (min_le_left _ _)
  have hεA : A * ε ≤ 1 / 64 := by
    have H := (le_div_iff₀ (by positivity : 0 < 64 * (A + 1))).mp
      (show ε ≤ 1 / (64 * (A + 1)) from (min_le_right _ _).trans (min_le_right _ _))
    nlinarith only [H, hε]
  refine ⟨ε, hε, by linarith only [hε64], A, hA, ?_⟩
  intro Y hk hu hw
  obtain ⟨htail, hreturn, hphase, Hval, Hr, Ht⟩ := HP' Y hk
    ⟨hu.1, hu.2.trans hεp'⟩ ⟨hw.1, hw.2.trans hεp'⟩
  have hb : 0 ≤ Y 1 + Y 2 ∧ Y 1 + Y 2 ≤ 1 :=
    ⟨add_nonneg hu.1.le hw.1.le, by linarith only [hu.2, hw.2, hε64]⟩
  have hb2 : (Y 1 + Y 2) ^ 2 ≤ Y 1 + Y 2 := by nlinarith only [hb.1, hb.2]
  have hbudget : A * (Y 1 + Y 2) ≤ 1 / 32 := by
    nlinarith only [mul_le_mul_of_nonneg_left (add_le_add hu.2 hw.2) hA.le, hεA]
  have hw2 : (Y 2) ^ 2 ≤ Y 2 := by nlinarith only [hw.1, hw.2, hε64]
  have Hrad : |fderiv ℝ (compactConnectionPhase η) Y (Pi.single 0 1) - 1| ≤ A * (Y 1 + Y 2) :=
    Hr.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hw2) hA.le)
  have hcoarse : |compactConnectionPhase η Y - (Y 0 - 2)| ≤ 1 / 16 := by
    have hk0 : 0 < Y 0 := by linarith only [hk.1]
    have hq : 0 ≤ 2 * Y 1 / Y 0 ∧ 2 * Y 1 / Y 0 ≤ Y 1 :=
      ⟨by positivity [hu.1], (div_le_iff₀ hk0).mpr (by nlinarith only [hu.1, mul_le_mul_of_nonneg_left hk.1 hu.1.le])⟩
    have H := abs_sub (compactConnectionPhase η Y - (Y 0 - 2) + 2 * Y 1 / Y 0) (2 * Y 1 / Y 0)
    rw [add_sub_cancel_right, abs_of_nonneg hq.1] at H
    have Hv := Hval.trans ((mul_le_mul_of_nonneg_left hb2 hA.le).trans hbudget)
    linarith only [H, Hv, hq.2, hu.2, hε64]
  refine ⟨htail, hreturn, hphase, ?_, hcoarse, Hval, Hrad, Ht⟩
  have H := Hrad.trans hbudget
  linarith only [(abs_le.mp H).1]

end BianchiIX
