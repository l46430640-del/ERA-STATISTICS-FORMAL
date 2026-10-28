import BianchiIX.Statistics.CommonEraCoding
import BianchiIX.Statistics.CoreRestartOrbit
import BianchiIX.Statistics.EraSurvivorTimeMeasurability
import BianchiIX.Statistics.EraSurvivorEvents
import BianchiIX.Statistics.EraStatisticsShift

noncomputable section

namespace BianchiIX

open Set MeasureTheory Filter
open scoped Topology

/-- On one invariant null exception's complement, the jointly Borel selected sequence is an exact orbit with unbounded original arrival times. -/
theorem exists_common_borel_era_orbit
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    (hBrehm : Literature.BrehmIXAttractorInput) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧
          ∃ N : Set NormalizedState, MeasurableSet N ∧ N ⊆ physicalPhaseSpace ∧
            geometricException ⊆ N ∧
            (∀ x : NormalizedState, ∀ t ∈ normalizedMaxDomain x 0,
              normalizedMaxCurve x 0 t ∈ N ↔ x ∈ N) ∧
            (∀ (C : SectionCoordinates → NormalizedState) (U : Set SectionCoordinates),
              IsOpen U → (∀ y ∈ U, ContDiffAt ℝ 1 C y) →
              (∀ y ∈ U, positiveWalls (C y)) → (∀ y ∈ U, stateConstraint (C y) = 1) →
              (∀ y ∈ U, normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) →
              volume (U ∩ C ⁻¹' N) = 0) ∧ NullInFourCoordinates N ∧
            ∃ W : NormalizedState → CoreRestartData, Measurable W ∧
              ∃ p : ↥(physicalPhaseSpace \ N) → eraSurvivorDomain η J σ Bcap,
                Measurable p ∧ Measurable (EraSurvivor.digits ∘ p) ∧
                Measurable (EraSurvivor.code ∘ p) ∧ Measurable (EraSurvivor.state ∘ p) ∧
                Measurable (EraSurvivor.phase ∘ p) ∧
                Measurable (fun x => EraSurvivor.physicalTime (W x.val) (p x)) ∧
                Measurable (fun x => EraSurvivor.physicalFrame (W x.val) (p x)) ∧ ∀ x,
                  (p x).val = (W x.val).2 ∧ EraStatistics (EraSurvivor.digits (p x)) (EraSurvivor.phase (p x)) ∧
                  EraStatistics (shiftDigits (EraSurvivor.digits (p x)) 1)
                    (fun n => EraSurvivor.phase (p x) (1 + n)) ∧
                  (∀ n, Nat.floor (EraSurvivor.state (p x) n 0 / 2) = (EraSurvivor.digits (p x) n : ℕ)) ∧
                  StrictMono (EraSurvivor.physicalTime (W x.val) (p x)) ∧
                  Tendsto (EraSurvivor.physicalTime (W x.val) (p x)) atTop atTop ∧ ∀ n,
                    EraEventItinerary η J (EraSurvivor.digits (p x) n).natPred (EraSurvivor.state (p x) n) ∧
                    coreRadiusEntry (EraSurvivor.state (p x) (n + 1)) = terminalNaturalState η J
                      (eraCoreExit (EraSurvivor.digits (p x) n).natPred (EraSurvivor.state (p x) n)) ∧
                    0 < EraSurvivor.physicalTime (W x.val) (p x) n ∧
                    EraSurvivor.physicalTime (W x.val) (p x) n ∈ normalizedMaxDomain x.val 0 ∧
                    fromProjectiveState (coreRadiusEntry (EraSurvivor.state (p x) n)) =
                      (axisFrame (EraSurvivor.physicalFrame (W x.val) (p x) n)).map
                        (normalizedMaxCurve x.val 0 (EraSurvivor.physicalTime (W x.val) (p x) n)) := by
  obtain ⟨δC, hδC, hδmax, HC⟩ := exists_common_borel_era_coding hBirkhoff hBrehm
  obtain ⟨δO, hδO, _, HO⟩ := exists_era_survivor_unbounded_orbit
  obtain ⟨δT, hδT, _, HT⟩ := exists_era_input_time_regular
  obtain ⟨δE, hδE, _, HE⟩ := exists_era_survivor_events
  refine ⟨min δC (min δO (min δT δE)), lt_min hδC (lt_min hδO (lt_min hδT hδE)),
    (min_le_left _ _).trans hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  have hδOT := hηδ.trans (min_le_right _ _)
  have hδTE := hδOT.trans (min_le_right _ _)
  obtain ⟨BO, hBO, _, Hphys⟩ := HO η hη (hδOT.trans (min_le_left _ _)) J hJ σ hσ hσone hσJ
  obtain ⟨BT, hBT, _, Htime⟩ := HT η hη (hδTE.trans (min_le_left _ _)) J hJ σ hσ hσone hσJ
  obtain ⟨BE, hBE, _, Hevents⟩ := HE η hη (hδTE.trans (min_le_right _ _)) J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hcapOT, Hmeas, N, hNm, hNp, hNg, hNi, hNn, hNfour,
    W, hW, HW, p, hpm, had, hac, has, hap, Hp⟩ :=
    HC η hη (hηδ.trans (min_le_left _ _)) J hJ σ hσ hσone hσJ
      (min BO (min BT BE)) (lt_min hBO (lt_min hBT hBE))
  have hcapTE := hcapOT.trans (min_le_right _ _)
  have Hregular (m : ℕ) (q : ℝ × CoreAngleState) (hq : q ∈ eraSelectedInputs η J σ Bcap m) :
      ContDiffAt ℝ 1 (eraReturnTime η J m) q.2 :=
    Htime Bcap (hcapTE.trans (min_le_left _ _)) m q hq.1
  have hpair : Measurable (fun x : ↥(physicalPhaseSpace \ N) => (W x.val, p x)) :=
    (hW.comp measurable_subtype_coe).prodMk hpm
  refine ⟨Bcap, hcap, hcapone, N, hNm, hNp, hNg, hNi, hNn, hNfour,
    W, hW, p, hpm, had, hac, has, hap, ?_, ?_, ?_⟩
  · convert (EraSurvivor.physicalTime_measurable Hmeas Hregular).comp hpair using 1
    rfl
  · convert (EraSurvivor.physicalFrame_measurable Hmeas).comp hpair using 1
    rfl
  · intro x
    obtain ⟨hval, hstat⟩ := Hp x
    obtain ⟨Hstep, Hmono, Htop, Horbit⟩ := Hphys Bcap (hcapOT.trans (min_le_left _ _)) (p x)
    have Hx := (HW x.val x.property.1 x.property.2).physical_orbit x.property.1.2 (p x) hval
      Hmono Htop (fun n => (Horbit n).2)
    have Htail := (eraStatistics_shift_iff (EraSurvivor.digits (p x)) (EraSurvivor.phase (p x)) 1).mpr hstat
    refine ⟨hval, hstat, Htail, fun n => (Hstep n).2.2, Hx.1, Hx.2.1, ?_⟩
    intro n
    obtain ⟨Hblock, Hnext⟩ := Hevents Bcap (hcapTE.trans (min_le_right _ _)) (p x) n
    exact ⟨Hblock, Hnext, Hx.2.2 n⟩

end BianchiIX
