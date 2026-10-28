import BianchiIX.Dynamics.EntrancePhysicalBounds

noncomputable section

namespace BianchiIX

/-- The C.25 estimates in the form needed for the finite-tail composition. -/
theorem exists_entrance_compact_phase_bounds :
    ∃ A : ℝ, 1 ≤ A ∧ ∃ δ > (0 : ℝ), δ ≤ 1 / 10000 ∧
      ∀ y : ProjectiveState,
      7 / 4 ≤ coreRadius (y 0) (y 2) → 1 ≤ y 0 →
      (0 < y 1 ∧ y 1 ≤ δ) → (0 < y 2 ∧ y 2 < 1) → (0 < y 3 ∧ y 3 ≤ δ) →
      ∃ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ ∧
      let z := entranceRadialCoordinates y
      let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
      ContDiffAt ℝ 2 F z ∧ |F z - z 0| ≤ A * y 2 * (y 1 + y 2) ∧
        |fderiv ℝ F z (Pi.single 0 1) - 1| ≤ A * y 2 * (y 1 + y 2) ∧
        |fderiv ℝ F z (Pi.single 1 1)| ≤ A * y 2 ∧
        |fderiv ℝ F z (Pi.single 2 1)| ≤ A * (y 1 + y 2) := by
  obtain ⟨C, hC, δ, hδ, hδsmall, HC⟩ := exists_entrance_physical_basic_bounds
  refine ⟨2 * C + 1, by linarith, δ, hδ, hδsmall, ?_⟩
  intro y hk hm hu hv hw
  obtain ⟨Ψ, HΨ, hF, H0, Hr, Hu, Hv, _⟩ := HC y hk hm hu hv hw
  refine ⟨Ψ, HΨ, hF, ?_, ?_, ?_, ?_⟩
  all_goals
    have hk1 : 1 ≤ coreRadius (y 0) (y 2) := by linarith only [hk]
    have huw : 0 ≤ y 1 + y 3 ∧ y 1 + y 3 ≤ 1 := by
      constructor
      · positivity [hu.1, hw.1]
      · linarith [hu.2, hw.2, hδsmall]
    have huw2 : (y 1 + y 3) ^ 2 ≤ 1 := by nlinarith only [huw.1, huw.2]
    have hbudget : y 1 * y 2 + (y 2) ^ 2 * (y 1 + y 3) ^ 2 ≤ y 2 * (y 1 + y 2) := by
      nlinarith only [mul_le_mul_of_nonneg_left huw2 (sq_nonneg (y 2))]
    have hb0 : 0 ≤ y 1 * y 2 + (y 2) ^ 2 * (y 1 + y 3) ^ 2 := by positivity [hu.1, hv.1]
    have hC' : C ≤ 2 * C + 1 := by linarith only [hC]
  · exact H0.trans ((div_le_self (mul_nonneg hC.le hb0) hk1).trans
      ((mul_le_mul_of_nonneg_left hbudget hC.le).trans (by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hC' (mul_nonneg hv.1.le (add_nonneg hu.1.le hv.1.le)))))
  · have hk2 : 1 ≤ coreRadius (y 0) (y 2) ^ 2 := by nlinarith only [hk1]
    exact Hr.trans ((div_le_self (mul_nonneg hC.le hb0) hk2).trans
      ((mul_le_mul_of_nonneg_left hbudget hC.le).trans (by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hC' (mul_nonneg hv.1.le (add_nonneg hu.1.le hv.1.le)))))
  · have hV2 : (y 2) ^ 2 ≤ y 2 := by nlinarith only [hv.1, hv.2]
    have hb : y 2 + (y 2) ^ 2 * (y 1 + y 3) ≤ 2 * y 2 := by
      nlinarith only [mul_le_mul_of_nonneg_left huw.2 (sq_nonneg (y 2)), hV2]
    have H := Hu.trans ((div_le_self (by positivity [hv.1, huw.1] : 0 ≤ C * (y 2 + (y 2) ^ 2 * (y 1 + y 3))) hk1).trans
      (mul_le_mul_of_nonneg_left hb hC.le))
    nlinarith only [H, hv.1]
  · have hb : y 1 + y 2 * (y 1 + y 3) ^ 2 ≤ y 1 + y 2 := by
      nlinarith only [mul_le_mul_of_nonneg_left huw2 hv.1.le]
    exact Hv.trans ((mul_le_mul_of_nonneg_left hb hC.le).trans
      (mul_le_mul_of_nonneg_right hC' (add_nonneg hu.1.le hv.1.le)))

end BianchiIX
