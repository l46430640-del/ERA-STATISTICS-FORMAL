import BianchiIX.Dynamics.EraSelectedInputs

noncomputable section

namespace BianchiIX

open Set

/-- Selection by the actual output phase agrees exactly with the open inverse-branch image. -/
theorem exists_era_selected_inputs_inverse :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 4 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bstar > (0 : ℝ), Bstar < 1 ∧ ∀ B ∈ Ioc 0 Bstar,
          ∀ Γ : EraCurve, Γ.Admissible B → ∀ m : ℕ, m < ⌊1 / B ^ σ⌋₊ → ∀ x : ℝ,
            (B, Γ.state (2 / x)) ∈ eraSelectedInputs η J σ Bstar m ↔
              x ∈ eraInverseBranch η J m (B ^ σ) Γ.U Γ.W '' Ioo (2 * B ^ σ) (1 - 2 * B ^ σ) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_interval_inverse
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨ε, hε, _, C, hC, Hinv⟩ := Hδ η hη hηδ J hJ
  obtain ⟨Bs, hBs, hBsone, Hbudget⟩ :=
    exists_retained_era_parameter_budget hε (by linarith : 0 ≤ C) hσ hσone hσJ
  refine ⟨Bs, hBs, hBsone, ?_⟩
  intro B hB Γ hΓ m hm x
  obtain ⟨hβ, hβmax, hsmall, hmargin, hscale⟩ := Hbudget B hB
  have hcap : (m : ℝ) + 1 ≤ 1 / B ^ σ :=
    (show (m : ℝ) + 1 ≤ (⌊1 / B ^ σ⌋₊ : ℝ) by exact_mod_cast (Nat.succ_le_of_lt hm)).trans
      (Nat.floor_le (by positivity))
  have Hgraph := fun r (hr : r ∈ Icc (2 * ((m : ℝ) + 1 + B ^ σ))
      (2 * ((m : ℝ) + 2 - B ^ σ))) => hΓ r (by nlinarith [hr.1, Nat.cast_nonneg (α := ℝ) m])
  obtain ⟨_, _, _, _, H⟩ := Hinv m (B ^ σ) B Γ.U Γ.W hβ (by linarith)
    (hscale m hcap) hsmall hmargin Hgraph
  let φ := graphPhase (eraBoundedPhase η J m) Γ.U Γ.W
  let g := intervalRadiusInverse φ (2 * ((m : ℝ) + 1 + B ^ σ)) (2 * ((m : ℝ) + 2 - B ^ σ))
  constructor
  · intro hx
    let y := 2 / eraOutputRadius η J m (Γ.state (2 / x))
    have hy : y ∈ Ioo (2 * B ^ σ) (1 - 2 * B ^ σ) := hx.2
    obtain ⟨_, _, huniq, _⟩ := H y ⟨hy.1.le, hy.2.le⟩
    have hr : 2 / x ∈ Icc (2 * ((m : ℝ) + 1 + B ^ σ)) (2 * ((m : ℝ) + 2 - B ^ σ)) :=
      hx.1.2.2.2.2.2
    have hg : g y = 2 / x := (huniq (2 / x) hr rfl).symm
    refine ⟨y, hy, ?_⟩
    change 2 / g y = x
    rw [hg]
    field_simp
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hg, hfg, _⟩ := H y ⟨hy.1.le, hy.2.le⟩
    have hrec : 2 / eraInverseBranch η J m (B ^ σ) Γ.U Γ.W y = g y := by
      change 2 / (2 / g y) = g y
      field_simp
    rw [hrec]
    have HΓ := Hgraph (g y) ⟨hg.1.le, hg.2.le⟩
    refine ⟨⟨hB, hm, HΓ.1, HΓ.2.1, HΓ.2.2.1, ⟨hg.1.le, hg.2.le⟩⟩, ?_⟩
    change φ (g y) ∈ Ioo (2 * B ^ σ) (1 - 2 * B ^ σ)
    change φ (g y) = y at hfg
    rw [hfg]
    exact hy

/-- The Borel return and its inverse-tree interpretation hold at the same uniform threshold. -/
theorem exists_era_selected_return :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bstar > (0 : ℝ), Bstar < 1 ∧
          (∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bstar m) ∧
            Measurable (fun p : eraSelectedInputs η J σ Bstar m => eraBudgetReturn η J m p.val)) ∧
          ∀ B ∈ Ioc 0 Bstar, ∀ Γ : EraCurve, Γ.Admissible B →
            ∀ m : ℕ, m < ⌊1 / B ^ σ⌋₊ → ∀ x : ℝ,
              (B, Γ.state (2 / x)) ∈ eraSelectedInputs η J σ Bstar m ↔
                x ∈ eraInverseBranch η J m (B ^ σ) Γ.U Γ.W '' Ioo (2 * B ^ σ) (1 - 2 * B ^ σ) := by
  obtain ⟨δm, hδm, hδmax, HM⟩ := exists_era_selected_inputs_measurable
  obtain ⟨δi, hδi, _, HI⟩ := exists_era_selected_inputs_inverse
  refine ⟨min δm δi, lt_min hδm hδi, (min_le_left _ _).trans hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bm, hBm, hBmone, Hm⟩ := HM η hη (hηδ.trans (min_le_left _ _)) J hJ σ hσ hσone hσJ
  obtain ⟨Bi, hBi, _, Hi⟩ := HI η hη (hηδ.trans (min_le_right _ _)) J (by omega) σ hσ hσone hσJ
  refine ⟨min Bm Bi, lt_min hBm hBi, (min_le_left _ _).trans_lt hBmone, ?_, ?_⟩
  · intro m
    apply eraSelectedInputs_measurable_of_contDiff hσ.le
    intro p hp
    exact (Hm m).1 p ⟨⟨hp.1.1, hp.1.2.trans (min_le_left _ _)⟩, hp.2⟩
  · intro B hB Γ hΓ m hm x
    have hBi' : B ∈ Ioc 0 Bi := ⟨hB.1, hB.2.trans (min_le_right _ _)⟩
    have heq : (B, Γ.state (2 / x)) ∈ eraSelectedInputs η J σ (min Bm Bi) m ↔
        (B, Γ.state (2 / x)) ∈ eraSelectedInputs η J σ Bi m := by
      simp only [eraSelectedInputs, eraInputSelection, mem_ofPred_eq, hB, hBi', true_and]
    exact heq.trans (Hi B hBi' Γ hΓ m hm x)

end BianchiIX
