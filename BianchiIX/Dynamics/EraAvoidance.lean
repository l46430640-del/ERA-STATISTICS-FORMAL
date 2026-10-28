import BianchiIX.Dynamics.CoreSectionPhysical
import BianchiIX.Dynamics.EraInputEstimates

noncomputable section

namespace BianchiIX

open Set

/-- Every small selected-input era has a genuine upward physical endpoint and preserves Taub avoidance. -/
theorem exists_era_input_avoidance :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bstar > (0 : ℝ), Bstar < 1 ∧ ∀ m : ℕ, ∀ p ∈ eraInputSelection σ Bstar m,
          let Y := eraNextState η J m p.2
          2 < Y 0 ∧ 0 < Y 1 ∧ 0 < Y 2 ∧ Y 1 + Y 2 ≤ p.1 ^ (4 / 3 : ℝ) ∧
          coreRadiusEntry Y = eraOutputState η J m p.2 ∧
          ∀ ε : ℝ, normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry p.2)) →
            normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry Y)) := by
  obtain ⟨δp, hδp, hδmax, HP⟩ := exists_era_bounded_phase_estimates
  obtain ⟨δa, hδa, _, HA⟩ := exists_era_input_estimates
  refine ⟨min δp δa, lt_min hδp hδa, (min_le_left _ _).trans hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨a, ha, _, C, hC, Hp⟩ := HP η hη (hηδ.trans (min_le_left _ _)) J (by omega)
  obtain ⟨_, _, Ba, hBa, _, Ha⟩ := HA η hη (hηδ.trans (min_le_right _ _)) J hJ σ hσ hσone hσJ
  obtain ⟨Br, hBr, hBrone, Hr⟩ := exists_retained_era_parameter_budget ha
    (le_trans zero_le_one hC) hσ hσone hσJ
  let Bstar := min Br (min Ba (1 / 4))
  have hBstar : 0 < Bstar := lt_min hBr (lt_min hBa (by norm_num))
  have hBBr : Bstar ≤ Br := min_le_left _ _
  have hBBa : Bstar ≤ Ba := (min_le_right _ _).trans (min_le_left _ _)
  have hBquarter : Bstar ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨Bstar, hBstar, hBBr.trans_lt hBrone, ?_⟩
  intro m p hp Y
  obtain ⟨hB, hm, hu, hw, hsum, hr⟩ := hp
  obtain ⟨_, _, hU, hW, hsumOut, _⟩ := Ha m p ⟨⟨hB.1, hB.2.trans hBBa⟩, hm, hu, hw, hsum, hr⟩
  obtain ⟨hβ, hβmax, hsmall, hmargin, hscale⟩ := Hr p.1 ⟨hB.1, hB.2.trans hBBr⟩
  have hcap : (m : ℝ) + 1 ≤ 1 / p.1 ^ σ :=
    (show (m : ℝ) + 1 ≤ (⌊1 / p.1 ^ σ⌋₊ : ℝ) by exact_mod_cast (Nat.succ_le_of_lt hm)).trans
      (Nat.floor_le (by positivity))
  have hrpos : 0 < p.2 0 := by nlinarith only [hr.1, hβ, Nat.cast_nonneg (α := ℝ) m]
  have hBrX : p.1 * p.2 0 ≤ a :=
    (mul_le_mul_of_nonneg_left hr.2 hB.1.le).trans (hscale m hcap)
  have hwall {z : ℝ} (hz : z ≤ p.1) : z ≤ a / p.2 0 :=
    (le_div_iff₀ hrpos).mpr ((mul_le_mul_of_nonneg_right hz hrpos.le).trans hBrX)
  have hphase : (m : ℝ) + 1 + p.1 ^ σ ≤ p.2 0 / 2 ∧ p.2 0 / 2 ≤ (m : ℝ) + 2 - p.1 ^ σ := by
    constructor <;> linarith only [hr.1, hr.2]
  obtain ⟨_, _, _, _, _, _, _, hR, Hvalid, Hconn, _, hchart, Hfirst, Hactual, Hunit, Htrans, _⟩ :=
    Hp m (p.1 ^ σ) p.2 hβ (by linarith only [hβmax])
      ⟨hu, hwall (by linarith only [hsum, hw])⟩ ⟨hw, hwall (by linarith only [hsum, hu])⟩
      (hsum.trans hsmall) hphase
      ((mul_le_mul_of_nonneg_left hsum (le_trans zero_le_one hC)).trans_lt hmargin)
  let Z := eraCoreExit m p.2
  let x := axisCycle (fromProjectiveState (coreTailEntry Z))
  let T := terminalNaturalTime η J Z
  have hlast := Hvalid m le_rfl
  have hlastEndpoint := coreReturn_normalized_endpoint hlast hchart
  have hc : stateConstraint x = 1 := by
    rw [show x = axisCycle (fromProjectiveState (coreTailEntry Z)) from rfl, axisCycle_constraint]
    change stateConstraint (fromProjectiveState (coreTailEntry
      (coreReturnState coreRadiusReturnTime ((coreReflectionState coreRadiusReturnTime)^[m] p.2)))) = 1
    rw [hlastEndpoint]
    exact (normalizedMaxCurve_constraint hlast.1.1.2.1).trans
      (fromProjectiveState_constraint (coreRadiusReturnValid_denom_pos hlast).ne')
  have hsmallOut : Y 1 + Y 2 ≤ 1 / 4 := hsumOut.trans
    ((Real.rpow_le_self_of_le_one hB.1.le (hB.2.trans (hBBr.trans hBrone.le)) (by norm_num)).trans
      (hB.2.trans hBquarter))
  change terminalNaturalState η J Z 1 + terminalNaturalState η J Z 3 ≤ 1 / 4 at hsmallOut
  change 0 < terminalNaturalState η J Z 1 at hU
  change 0 < terminalNaturalState η J Z 3 at hW
  have hrec := upward_core_normalized_reconstruction
    ((normalizedMaxCurve_constraint Hfirst.1.2.1).trans hc)
    (by rw [Hactual]; exact Hunit)
    (by rw [Hactual]; exact ⟨hU.le, by linarith only [hsmallOut, hW]⟩)
    (by rw [Hactual]; exact ⟨hW.le, by linarith only [hsmallOut, hU]⟩) Htrans
  dsimp only at hrec
  rw [Hactual] at hrec
  change coreRadiusEntry Y = eraOutputState η J m p.2 ∧
    fromProjectiveState (coreRadiusEntry Y) = normalizedMaxCurve x 0 T at hrec
  refine ⟨hR, hU, hW, hsumOut, hrec.1, ?_⟩
  intro ε Ha
  have Hprefix : ∀ j ≤ m, normalizedTaubAvoidance ε
      (fromProjectiveState (coreRadiusEntry ((coreReflectionState coreRadiusReturnTime)^[j] p.2))) := by
    intro j
    induction j with
    | zero => intro _; exact Ha
    | succ j ih =>
      intro hj
      obtain ⟨_, hT, horbit⟩ := Hconn j (by omega)
      rw [Function.iterate_succ_apply']
      exact (ih (by omega)).coreReflection (Hvalid j (by omega)) hT horbit
  have Hdown := (Hprefix m le_rfl).coreReturn hlast hchart
  have Hcycle : normalizedTaubAvoidance ε x := Hdown.frame 1
  rw [hrec.2]
  exact Hcycle.forward Hfirst.1.1.le Hfirst.1.2.1

end BianchiIX
