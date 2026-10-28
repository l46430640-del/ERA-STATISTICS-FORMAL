import BianchiIX.Dynamics.EraAvoidance
import BianchiIX.Dynamics.AwayCorePhase
import BianchiIX.Statistics.CompactEraSurvival

noncomputable section

namespace BianchiIX

open Set

/-- A physically Taub-avoiding small core has compact phase along every selected finite history. -/
theorem exists_compactEraHistories_of_taub_avoidance :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ γ > (0 : ℝ), γ < 1 / 4 ∧
          ∃ Bstar > (0 : ℝ), Bstar < 1 ∧ ∀ Bcap : ℝ, ∀ p : ℝ × CoreAngleState,
            p.1 ∈ Ioc 0 Bstar → 2 - γ / 2 ≤ p.2 0 →
            0 < p.2 1 → 0 < p.2 2 → p.2 1 + p.2 2 ≤ p.1 →
            normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry p.2)) →
            compactEraHistories η J σ Bcap N γ p := by
  obtain ⟨δ, hδ, hδmax, H⟩ := exists_era_input_avoidance
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ ε hε
  obtain ⟨Be, hBe, hBeone, He⟩ := H η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨N, γ, hγ, hγmax, Bc, hBc, Hc⟩ := exists_compactEraPhase_of_taub_avoidance hε
  let Bstar := min Be Bc
  have hBstar : 0 < Bstar := lt_min hBe hBc
  have hBBe : Bstar ≤ Be := min_le_left _ _
  have hBBc : Bstar ≤ Bc := min_le_right _ _
  have hBone : Bstar < 1 := hBBe.trans_lt hBeone
  refine ⟨N, γ, hγ, hγmax, Bstar, hBstar, hBone, ?_⟩
  intro Bcap
  have Hhistory : ∀ w : List ℕ+, ∀ p : ℝ × CoreAngleState,
      p.1 ∈ Ioc 0 Bstar → 2 - γ / 2 ≤ p.2 0 →
      0 < p.2 1 → 0 < p.2 2 → p.2 1 + p.2 2 ≤ p.1 →
      normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry p.2)) →
      p ∈ eraPrefixDomain η J σ Bcap w →
      (eraPrefixState η J w p).2 ∈ compactEraPhase N γ := by
    intro w
    induction w with
    | nil =>
      intro p hp hk hu hw hb ha _
      exact Hc p.2 hk hu hw (hb.trans (hp.2.trans hBBc)) ha
    | cons a w ih =>
      intro p hp hk hu hw hb ha hmem
      have hin : p ∈ eraInputSelection σ Be a.natPred :=
        ⟨⟨hp.1, hp.2.trans hBBe⟩, hmem.1.1.2⟩
      obtain ⟨hr, hU, hW, hsum, _, havoid⟩ := He a.natPred p hin
      have hpower : p.1 ^ (4 / 3 : ℝ) ≤ p.1 :=
        Real.rpow_le_self_of_le_one hp.1.le (hp.2.trans hBone.le) (by norm_num)
      exact ih (eraBudgetReturn η J a.natPred p)
        ⟨Real.rpow_pos_of_pos hp.1 _, hpower.trans hp.2⟩
        (by change 2 - γ / 2 ≤ eraNextState η J a.natPred p.2 0; linarith only [hr, hγ])
        hU hW hsum (havoid ε ha) hmem.2
  intro p hp hk hu hw hb ha w hmem
  exact Hhistory w p hp hk hu hw hb ha hmem

end BianchiIX
