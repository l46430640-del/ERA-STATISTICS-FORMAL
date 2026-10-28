import BianchiIX.Dynamics.CompactConnectionErrorBounds
import BianchiIX.Dynamics.CompactConnectionPhaseExpansion
import BianchiIX.Dynamics.CompactConnectionRadialBound

noncomputable section

namespace BianchiIX

/-- The phase value and all ordinary phase derivatives in B.44. -/
theorem exists_compact_connection_phase_bounds :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 10000 ∧ ∀ η : ℝ, (0 < η ∧ η ≤ δ) →
      ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → (0 < Y 1 ∧ Y 1 ≤ ε) → (0 < Y 2 ∧ Y 2 ≤ ε) →
      coreTailValid η Y ∧ entranceReturnValid (compactConnectionEntry η Y) ∧
        ContDiffAt ℝ 2 (compactConnectionPhase η) Y ∧
        |compactConnectionPhase η Y - (Y 0 - 2) + 2 * Y 1 / Y 0| ≤ C * (Y 1 + Y 2) ^ 2 ∧
        |fderiv ℝ (compactConnectionPhase η) Y (Pi.single 0 1) - 1| ≤ C * (Y 1 + (Y 2) ^ 2) ∧
        |fderiv ℝ (compactConnectionPhase η) Y (Pi.single 1 1) + 2 / Y 0| +
          |fderiv ℝ (compactConnectionPhase η) Y (Pi.single 2 1)| ≤ C * (Y 1 + Y 2) := by
  obtain ⟨δ, hδ, hδsmall, HD⟩ := exists_compact_connection_error_bounds
  refine ⟨δ, hδ, hδsmall, ?_⟩
  intro η hη
  obtain ⟨εD, hεD, D, hD, HD'⟩ := HD η hη
  obtain ⟨εA, hεA, A, hA, HA⟩ := exists_compact_connection_phase_expansion ⟨hη.1, hη.2.trans hδsmall⟩
  obtain ⟨εB, hεB, B, hB, HB⟩ := exists_compact_connection_finite_radial_bound ⟨hη.1, hη.2.trans hδsmall⟩
  let ε := min εD (min εA (min εB 1))
  have hεD' : ε ≤ εD := min_le_left _ _
  have hεA' : ε ≤ εA := (min_le_right _ _).trans (min_le_left _ _)
  have hεB' : ε ≤ εB := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let C := 2 * (A + B + D)
  have hAC : A + D ≤ C := by dsimp only [C]; linarith only [hA, hB, hD]
  have hBC : B + D ≤ C := by dsimp only [C]; linarith only [hA, hB, hD]
  have h2AC : 2 * (A + D) ≤ C := by dsimp only [C]; linarith only [hB]
  refine ⟨ε, lt_min hεD (lt_min hεA (lt_min hεB zero_lt_one)), C, by dsimp only [C]; positivity, ?_⟩
  intro Y hk hu hw
  obtain ⟨htail, hreturn, hE, HE0, HEu, HEw⟩ := HD' Y hk
    ⟨hu.1, hu.2.trans hεD'⟩ ⟨hw.1, hw.2.trans hεD'⟩
  obtain ⟨_, hR, HR0, HRcols⟩ := HA Y hk
    (by rw [abs_of_pos hu.1]; exact hu.2.trans hεA')
    (by rw [abs_of_pos hw.1]; exact hw.2.trans hεA')
  obtain ⟨_, _, HRr⟩ := HB Y hk
    (by rw [abs_of_pos hu.1]; exact hu.2.trans hεB')
    (by rw [abs_of_pos hw.1]; exact hw.2.trans hεB')
  rw [abs_of_pos hu.1, abs_of_pos hw.1] at HR0 HRcols
  rw [abs_of_pos hu.1] at HRr
  have hsumfun : compactConnectionPhase η = compactConnectionError η + compactConnectionFinitePhase η := by
    ext Z
    dsimp only [Pi.add_apply, compactConnectionError]
    ring
  have hphase : ContDiffAt ℝ 2 (compactConnectionPhase η) Y := by
    rw [hsumfun]
    exact hE.add hR
  have hdiff (v : CoreAngleState) : fderiv ℝ (compactConnectionPhase η) Y v =
      fderiv ℝ (compactConnectionError η) Y v + fderiv ℝ (compactConnectionFinitePhase η) Y v := by
    rw [hsumfun, fderiv_add (hE.differentiableAt (by norm_num)) (hR.differentiableAt (by norm_num))]
    rfl
  have hb0 : 0 ≤ Y 1 + Y 2 := add_nonneg hu.1.le hw.1.le
  have hquadratic : Y 2 * (Y 1 + Y 2) ≤ (Y 1 + Y 2) ^ 2 := by
    nlinarith only [mul_nonneg hu.1.le hb0]
  have hradial : Y 2 * (Y 1 + Y 2) ≤ Y 1 + (Y 2) ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left (hw.2.trans hε1) hu.1.le]
  have HE : |compactConnectionError η Y| ≤ D * Y 2 * (Y 1 + Y 2) :=
    (le_add_of_nonneg_right (abs_nonneg _)).trans HE0
  have HEr : |fderiv ℝ (compactConnectionError η) Y (Pi.single 0 1)| ≤ D * Y 2 * (Y 1 + Y 2) :=
    (le_add_of_nonneg_left (abs_nonneg _)).trans HE0
  have HEd : D * Y 2 * (Y 1 + Y 2) ≤ D * (Y 1 + Y 2) ^ 2 := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hquadratic hD.le
  have HEr' : D * Y 2 * (Y 1 + Y 2) ≤ D * (Y 1 + (Y 2) ^ 2) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hradial hD.le
  have HRu : |fderiv ℝ (compactConnectionFinitePhase η) Y (Pi.single 1 1) + 2 / Y 0| ≤ A * (Y 1 + Y 2) := by
    simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, sub_neg_eq_add, neg_div] using HRcols 1
  have HRw : |fderiv ℝ (compactConnectionFinitePhase η) Y (Pi.single 2 1)| ≤ A * (Y 1 + Y 2) := by
    simpa using HRcols 2
  refine ⟨htail, hreturn, hphase, ?_, ?_, ?_⟩
  · have hid : compactConnectionPhase η Y - (Y 0 - 2) + 2 * Y 1 / Y 0 =
        compactConnectionError η Y + (compactConnectionFinitePhase η Y - (Y 0 - 2 - 2 * Y 1 / Y 0)) := by
      dsimp only [compactConnectionError]; ring
    rw [hid]
    calc
      _ ≤ |compactConnectionError η Y| + |compactConnectionFinitePhase η Y - (Y 0 - 2 - 2 * Y 1 / Y 0)| := abs_add_le _ _
      _ ≤ D * (Y 1 + Y 2) ^ 2 + A * (Y 1 + Y 2) ^ 2 := add_le_add (HE.trans HEd) HR0
      _ = (A + D) * (Y 1 + Y 2) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hAC (sq_nonneg _)
  · rw [hdiff, add_sub_assoc]
    calc
      _ ≤ |fderiv ℝ (compactConnectionError η) Y (Pi.single 0 1)| +
          |fderiv ℝ (compactConnectionFinitePhase η) Y (Pi.single 0 1) - 1| := abs_add_le _ _
      _ ≤ D * (Y 1 + (Y 2) ^ 2) + B * (Y 1 + (Y 2) ^ 2) := add_le_add (HEr.trans HEr') HRr
      _ = (B + D) * (Y 1 + (Y 2) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hBC (add_nonneg hu.1.le (sq_nonneg _))
  · rw [hdiff, hdiff, add_assoc]
    calc
      _ ≤ (|fderiv ℝ (compactConnectionError η) Y (Pi.single 1 1)| +
          |fderiv ℝ (compactConnectionFinitePhase η) Y (Pi.single 1 1) + 2 / Y 0|) +
          (|fderiv ℝ (compactConnectionError η) Y (Pi.single 2 1)| +
          |fderiv ℝ (compactConnectionFinitePhase η) Y (Pi.single 2 1)|) := add_le_add (abs_add_le _ _) (abs_add_le _ _)
      _ ≤ (D * Y 2 + A * (Y 1 + Y 2)) + (D * (Y 1 + Y 2) + A * (Y 1 + Y 2)) :=
        add_le_add (add_le_add HEu HRu) (add_le_add HEw HRw)
      _ ≤ 2 * (A + D) * (Y 1 + Y 2) := by nlinarith only [mul_nonneg hD.le hu.1.le]
      _ ≤ _ := mul_le_mul_of_nonneg_right h2AC hb0

end BianchiIX
