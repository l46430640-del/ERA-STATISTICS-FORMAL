import BianchiIX.Dynamics.EntranceMultiplierDifferential
import BianchiIX.Dynamics.EntranceFullReturnColumns
import BianchiIX.Analysis.TwoWallLimit

noncomputable section

namespace BianchiIX

/-- Removing the entrance-wall logarithms leaves eight uniformly bounded multiplier columns. -/
theorem exists_entrance_logMultiplier_columns_pos :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ y : ProjectiveState,
      let k := coreRadius (y 0) (y 2)
      7 / 4 ≤ k → 1 ≤ y 0 → (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) →
      (0 < y 3 ∧ y 3 ≤ ε) →
      (|entranceLogMultiplierResponse y 0 (Pi.single 0 1)| ≤ C * (-Real.log (y 2)) ∧
       |entranceLogMultiplierResponse y 0 (Pi.single 1 1)| ≤ C ∧
       |entranceLogMultiplierResponse y 0 (Pi.single 2 1)| ≤ C * k / y 2 ∧
       |entranceLogMultiplierResponse y 0 (Pi.single 3 1)| ≤ C) ∧
      (|entranceLogMultiplierResponse y 2 (Pi.single 0 1)| ≤ C * (-Real.log (y 2)) / k ^ 2 ∧
       |entranceLogMultiplierResponse y 2 (Pi.single 1 1)| ≤ C / k ^ 2 ∧
       |entranceLogMultiplierResponse y 2 (Pi.single 2 1)| ≤ C / y 2 ∧
       |entranceLogMultiplierResponse y 2 (Pi.single 3 1)| ≤ C / k ^ 2) := by
  obtain ⟨C, hC, ε, hε, hεsmall, HC⟩ := exists_entrance_return_full_columns
  refine ⟨C, hC, ε, hε, hεsmall, ?_⟩
  intro y k hk hm hu hv hw
  obtain ⟨Ψ, HΨ, _, HU, HW⟩ := HC y 1 hk hm hu hv hw (Or.inl rfl)
  have hu' : 0 < y 1 ∧ y 1 ≤ 1 / 10000 := ⟨hu.1, hu.2.trans hεsmall⟩
  have hw' : 0 < y 3 ∧ y 3 ≤ 1 / 10000 := ⟨hw.1, hw.2.trans hεsmall⟩
  simpa [HΨ.return_logWalls_multiplier hk hm hu' hv hw'] using And.intro HU HW

/-- The same eight ordinary multiplier derivatives extend to both zero stable walls. -/
theorem exists_entrance_logMultiplier_columns_nonneg :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ y : ProjectiveState,
      let k := coreRadius (y 0) (y 2)
      7 / 4 ≤ k → 1 ≤ y 0 → (0 ≤ y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) →
      (0 ≤ y 3 ∧ y 3 ≤ ε) →
      (|entranceLogMultiplierResponse y 0 (Pi.single 0 1)| ≤ C * (-Real.log (y 2)) ∧
       |entranceLogMultiplierResponse y 0 (Pi.single 1 1)| ≤ C ∧
       |entranceLogMultiplierResponse y 0 (Pi.single 2 1)| ≤ C * k / y 2 ∧
       |entranceLogMultiplierResponse y 0 (Pi.single 3 1)| ≤ C) ∧
      (|entranceLogMultiplierResponse y 2 (Pi.single 0 1)| ≤ C * (-Real.log (y 2)) / k ^ 2 ∧
       |entranceLogMultiplierResponse y 2 (Pi.single 1 1)| ≤ C / k ^ 2 ∧
       |entranceLogMultiplierResponse y 2 (Pi.single 2 1)| ≤ C / y 2 ∧
       |entranceLogMultiplierResponse y 2 (Pi.single 3 1)| ≤ C / k ^ 2) := by
  obtain ⟨C, hC, ε, hε, hεsmall, HC⟩ := exists_entrance_logMultiplier_columns_pos
  refine ⟨C, hC, ε, hε, hεsmall, ?_⟩
  intro y k hk hm hu hv hw
  have hu' : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := ⟨hu.1, hu.2.trans hεsmall⟩
  have hw' : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := ⟨hw.1, hw.2.trans hεsmall⟩
  have hlimit (i : Fin 3) (j : Fin 4) (B : ℝ)
      (H : ∀ z : ProjectiveState, z 0 = y 0 → z 2 = y 2 →
        (0 < z 1 ∧ z 1 ≤ ε) → (0 < z 3 ∧ z 3 ≤ ε) →
        |entranceLogMultiplierResponse z i (Pi.single j 1)| ≤ B) :
      |entranceLogMultiplierResponse y i (Pi.single j 1)| ≤ B :=
    le_of_two_nonnegative_walls hε hu hw
      (continuousAt_entranceLogMultiplierResponse hk hm hu' hv hw' i (Pi.single j 1)).abs H
  have H (z : ProjectiveState) (h0 : z 0 = y 0) (h2 : z 2 = y 2)
      (hu : 0 < z 1 ∧ z 1 ≤ ε) (hw : 0 < z 3 ∧ z 3 ≤ ε) :=
    HC z (by simpa only [h0, h2] using hk) (by simpa only [h0] using hm)
      hu (by simpa only [h2] using hv) hw
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · apply hlimit 0 0
    intro z h0 h2 hu hw
    simpa only [h2] using (H z h0 h2 hu hw).1.1
  · apply hlimit 0 1
    intro z h0 h2 hu hw
    exact (H z h0 h2 hu hw).1.2.1
  · apply hlimit 0 2
    intro z h0 h2 hu hw
    simpa only [h0, h2] using (H z h0 h2 hu hw).1.2.2.1
  · apply hlimit 0 3
    intro z h0 h2 hu hw
    exact (H z h0 h2 hu hw).1.2.2.2
  · apply hlimit 2 0
    intro z h0 h2 hu hw
    simpa only [h0, h2] using (H z h0 h2 hu hw).2.1
  · apply hlimit 2 1
    intro z h0 h2 hu hw
    simpa only [h0, h2] using (H z h0 h2 hu hw).2.2.1
  · apply hlimit 2 2
    intro z h0 h2 hu hw
    simpa only [h2] using (H z h0 h2 hu hw).2.2.2.1
  · apply hlimit 2 3
    intro z h0 h2 hu hw
    simpa only [h0, h2] using (H z h0 h2 hu hw).2.2.2.2

end BianchiIX
