import BianchiIX.Dynamics.EraAvoidance
import BianchiIX.Dynamics.EraReturnOrbit

noncomputable section

namespace BianchiIX

open Set

/-- Every retained input has the explicitly summed positive return time and the exact physical endpoint in its accumulated axis frame. -/
theorem exists_era_input_orbit :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bstar > (0 : ℝ), Bstar < 1 ∧ ∀ m : ℕ, ∀ p ∈ eraInputSelection σ Bstar m,
          0 < eraReturnTime η J m p.2 ∧
          eraReturnTime η J m p.2 ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry p.2)) 0 ∧
          fromProjectiveState (coreRadiusEntry (eraNextState η J m p.2)) =
            (axisFrame (eraReturnFrame m)).map (normalizedMaxCurve
              (fromProjectiveState (coreRadiusEntry p.2)) 0 (eraReturnTime η J m p.2)) ∧
          coreRadiusReturnValid p.2 ∧ Nat.floor (p.2 0 / 2) = m + 1 := by
  obtain ⟨δp, hδp, hδmax, HP⟩ := exists_era_bounded_phase_estimates
  obtain ⟨δa, hδa, _, HA⟩ := exists_era_input_avoidance
  refine ⟨min δp δa, lt_min hδp hδa, (min_le_left _ _).trans hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨a, ha, _, C, hC, Hp⟩ := HP η hη (hηδ.trans (min_le_left _ _)) J (by omega)
  obtain ⟨Ba, hBa, _, Ha⟩ := HA η hη (hηδ.trans (min_le_right _ _)) J hJ σ hσ hσone hσJ
  obtain ⟨Br, hBr, hBrone, Hr⟩ := exists_retained_era_parameter_budget ha
    (le_trans zero_le_one hC) hσ hσone hσJ
  refine ⟨min Br Ba, lt_min hBr hBa, (min_le_left _ _).trans_lt hBrone, ?_⟩
  intro m p hp
  obtain ⟨hB, hm, hu, hw, hsum, hr⟩ := hp
  obtain ⟨_, _, _, _, hrec, _⟩ := Ha m p ⟨⟨hB.1, hB.2.trans (min_le_right _ _)⟩, hm, hu, hw, hsum, hr⟩
  obtain ⟨hβ, hβmax, hsmall, hmargin, hscale⟩ := Hr p.1 ⟨hB.1, hB.2.trans (min_le_left _ _)⟩
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
  obtain ⟨_, _, _, _, _, _, hcount, _, Hvalid, Hconn, _, hchart, Hfirst, Hactual, Hunit, _, _⟩ :=
    Hp m (p.1 ^ σ) p.2 hβ (by linarith only [hβmax])
      ⟨hu, hwall (by linarith only [hsum, hw])⟩ ⟨hw, hwall (by linarith only [hsum, hu])⟩
      (hsum.trans hsmall) hphase
      ((mul_le_mul_of_nonneg_left hsum (le_trans zero_le_one hC)).trans_lt hmargin)
  obtain ⟨hT, hdom, hend⟩ := eraReturn_normalized_endpoint Hvalid
    (fun j hj => (Hconn j hj).2) hchart Hfirst.1.1 Hactual Hunit
  refine ⟨hT, hdom, ?_, Hvalid 0 (Nat.zero_le _), hcount⟩
  rw [hrec]
  exact hend

end BianchiIX
