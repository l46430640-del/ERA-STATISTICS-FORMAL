import BianchiIX.Dynamics.EraEventTimes
import BianchiIX.Statistics.EraSurvivorOrbit

noncomputable section

namespace BianchiIX

/-- Every block of every retained infinite history follows the actual core and connection event rules. -/
theorem exists_era_survivor_events :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bstar > (0 : ℝ), Bstar < 1 ∧ ∀ Bcap : ℝ, Bcap ≤ Bstar →
          ∀ p : eraSurvivorDomain η J σ Bcap, ∀ n,
            EraEventItinerary η J (EraSurvivor.digits p n).natPred (EraSurvivor.state p n) ∧
              coreRadiusEntry (EraSurvivor.state p (n + 1)) =
                terminalNaturalState η J (eraCoreExit (EraSurvivor.digits p n).natPred (EraSurvivor.state p n)) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_input_event_itinerary
  obtain ⟨δA, hδA, _, HA⟩ := exists_era_input_avoidance
  refine ⟨min δ δA, lt_min hδ hδA, (min_le_left _ _).trans hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bstar, hB, hBone, HB⟩ := Hδ η hη (hηδ.trans (min_le_left _ _)) J hJ σ hσ hσone hσJ
  obtain ⟨BA, hBA, _, Ha⟩ := HA η hη (hηδ.trans (min_le_right _ _)) J hJ σ hσ hσone hσJ
  refine ⟨min Bstar BA, lt_min hB hBA, (min_le_left _ _).trans_lt hBone, ?_⟩
  intro Bcap hcap p n
  have hinput := (EraSurvivor.budgetState_mem_selected p n).1
  refine ⟨HB Bcap (hcap.trans (min_le_left _ _)) (EraSurvivor.digits p n).natPred
    (EraSurvivor.budgetState p n) hinput, ?_⟩
  have hinA : EraSurvivor.budgetState p n ∈ eraInputSelection σ BA (EraSurvivor.digits p n).natPred :=
    ⟨⟨hinput.1.1, hinput.1.2.trans (hcap.trans (min_le_right _ _))⟩, hinput.2⟩
  obtain ⟨_, _, _, _, hrec, _⟩ := Ha (EraSurvivor.digits p n).natPred (EraSurvivor.budgetState p n) hinA
  rw [EraSurvivor.state_succ]
  exact hrec

end BianchiIX
