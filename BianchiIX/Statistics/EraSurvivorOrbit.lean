import BianchiIX.Dynamics.EraInputOrbit
import BianchiIX.Statistics.EraSurvivorMeasurability

noncomputable section

namespace BianchiIX

namespace EraSurvivor

variable {η σ Bcap : ℝ} {J : ℕ}

def duration (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) : ℝ :=
  eraReturnTime η J (digits p n).natPred (state p n)

def elapsedTime (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, duration p j

def frame (p : eraSurvivorDomain η J σ Bcap) : ℕ → Fin 6
  | 0 => 0
  | n + 1 => (axisFrame_comp (eraReturnFrame (digits p n).natPred) (frame p n)).choose

theorem elapsedTime_succ (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) :
    elapsedTime p (n + 1) = duration p n + elapsedTime p n := by
  rw [elapsedTime, Finset.sum_range_succ]
  exact add_comm _ _

theorem frame_succ (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) (x : NormalizedState) :
    (axisFrame (frame p (n + 1))).map x =
      (axisFrame (eraReturnFrame (digits p n).natPred)).map ((axisFrame (frame p n)).map x) :=
  ((axisFrame_comp (eraReturnFrame (digits p n).natPred) (frame p n)).choose_spec x).symm

theorem state_zero (p : eraSurvivorDomain η J σ Bcap) : state p 0 = p.val.2 :=
  congrArg Prod.snd (budgetState_zero p)

theorem state_succ (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) :
    state p (n + 1) = eraNextState η J (digits p n).natPred (state p n) :=
  congrArg Prod.snd (budgetState_succ p n)

theorem budgetState_budget (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) :
    (budgetState p n).1 = eraAmplitude p.val.1 n := by
  have hp : 0 < p.val.1 := by
    have H := (budgetState_mem_selected p 0).1.1.1
    rwa [budgetState_zero] at H
  rw [budgetState, eraPrefixState_budget η J (word p n) p.val hp.le, word_length]

/-- Actual one-step endpoints give all finite orbit identities and strictly increasing original arrival times. -/
theorem physical_orbit (p : eraSurvivorDomain η J σ Bcap)
    (H : ∀ n, 0 < duration p n ∧ coreRadiusReturnValid (state p n) ∧
      fromProjectiveState (coreRadiusEntry (state p (n + 1))) =
        (axisFrame (eraReturnFrame (digits p n).natPred)).map
          (normalizedMaxCurve (fromProjectiveState (coreRadiusEntry (state p n))) 0 (duration p n))) :
    StrictMono (elapsedTime p) ∧ ∀ n,
      elapsedTime p n ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry p.val.2)) 0 ∧
      fromProjectiveState (coreRadiusEntry (state p n)) = (axisFrame (frame p n)).map
        (normalizedMaxCurve (fromProjectiveState (coreRadiusEntry p.val.2)) 0 (elapsedTime p n)) := by
  let x := fromProjectiveState (coreRadiusEntry p.val.2)
  have hpos (n : ℕ) : 0 < duration p n := (H n).1
  have hnonneg (n : ℕ) : 0 ≤ elapsedTime p n :=
    Finset.sum_nonneg (fun j _ => (hpos j).le)
  have hc : stateConstraint x = 1 := by
    have HV := (H 0).2.1
    rw [state_zero] at HV
    exact fromProjectiveState_constraint (coreRadiusReturnValid_denom_pos HV).ne'
  have hdom (n : ℕ) : elapsedTime p n ∈ normalizedMaxDomain x 0 :=
    normalizedMaxDomain_contains_Ici_of_constraint hc 0 (hnonneg n)
  refine ⟨strictMono_nat_of_lt_succ (fun n => by rw [elapsedTime_succ]; linarith only [hpos n]), ?_⟩
  intro n
  refine ⟨hdom n, ?_⟩
  induction n with
  | zero =>
    simp only [state_zero, elapsedTime, Finset.range_zero, Finset.sum_empty, normalizedMaxCurve_initial]
    rfl
  | succ n ih =>
    have hcT := (normalizedMaxCurve_forward_of_constraint hc (hnonneg n)).2.1
    have hs := normalizedMaxCurve_shift (t₀ := (0 : ℝ)) (t := duration p n)
      (by simpa only [zero_add] using hdom n)
      (by simpa only [elapsedTime_succ] using hdom (n + 1))
    simp only [zero_add] at hs
    rw [(H n).2.2, ih, (axisFrame (frame p n)).maxCurve
      (normalizedMaxDomain_contains_Ici_of_constraint hcT 0 (hpos n).le),
      hs, elapsedTime_succ, frame_succ]

end EraSurvivor

/-- No additional orbit-realization assumption is needed for survivors at the common small cap. -/
theorem exists_era_survivor_orbit :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bstar > (0 : ℝ), Bstar < 1 ∧ ∀ Bcap : ℝ, Bcap ≤ Bstar →
          ∀ p : eraSurvivorDomain η J σ Bcap,
            (∀ n, 0 < EraSurvivor.duration p n ∧ coreRadiusReturnValid (EraSurvivor.state p n) ∧
              Nat.floor (EraSurvivor.state p n 0 / 2) = (EraSurvivor.digits p n : ℕ)) ∧
            StrictMono (EraSurvivor.elapsedTime p) ∧ ∀ n,
              EraSurvivor.elapsedTime p n ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry p.val.2)) 0 ∧
              fromProjectiveState (coreRadiusEntry (EraSurvivor.state p n)) =
                (axisFrame (EraSurvivor.frame p n)).map (normalizedMaxCurve
                  (fromProjectiveState (coreRadiusEntry p.val.2)) 0 (EraSurvivor.elapsedTime p n)) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_input_orbit
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bstar, hB, hBone, HB⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bstar, hB, hBone, ?_⟩
  intro Bcap hcap p
  have Hinput (n : ℕ) : EraSurvivor.budgetState p n ∈
      eraInputSelection σ Bstar (EraSurvivor.digits p n).natPred := by
    have H := (EraSurvivor.budgetState_mem_selected p n).1
    exact ⟨⟨H.1.1, H.1.2.trans hcap⟩, H.2⟩
  have Hstep (n : ℕ) := HB (EraSurvivor.digits p n).natPred (EraSurvivor.budgetState p n) (Hinput n)
  refine ⟨fun n => ⟨(Hstep n).1, (Hstep n).2.2.2.1, ?_⟩, ?_⟩
  · simpa only [EraSurvivor.state, PNat.natPred_add_one] using (Hstep n).2.2.2.2
  · apply EraSurvivor.physical_orbit p
    intro n
    refine ⟨(Hstep n).1, (Hstep n).2.2.2.1, ?_⟩
    rw [EraSurvivor.state_succ]
    exact (Hstep n).2.2.1

end BianchiIX
