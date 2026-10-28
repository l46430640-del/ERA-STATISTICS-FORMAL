import BianchiIX.Dynamics.CompactEraStep
import BianchiIX.Statistics.EraBoundedDigits

noncomputable section

namespace BianchiIX

open Set

/-- Compactness is required only at the end of each finite selected history that already exists. -/
def compactEraHistories (η : ℝ) (J : ℕ) (σ Bcap : ℝ) (N : ℕ) (γ : ℝ)
    (p : ℝ × CoreAngleState) : Prop :=
  ∀ w : List ℕ+, p ∈ eraPrefixDomain η J σ Bcap w →
    (eraPrefixState η J w p).2 ∈ compactEraPhase N γ

/-- A one-step extension and compactness of existing histories produce arbitrarily long finite histories. -/
theorem compactEraHistories_finite_prefix {η σ Bcap Bstar γ : ℝ} {J N : ℕ}
    (hBstar : Bstar ≤ 1)
    (Hstep : ∀ B ∈ Ioc 0 Bstar, ∀ X : CoreAngleState,
      X ∈ compactEraPhase N γ → 0 < X 1 → 0 < X 2 → X 1 + X 2 ≤ B →
        ∃ m : ℕ, (B, X) ∈ eraSelectedInputs η J σ Bcap m ∧
          0 < eraNextState η J m X 1 ∧ 0 < eraNextState η J m X 2 ∧
          eraNextState η J m X 1 + eraNextState η J m X 2 ≤ B ^ (4 / 3 : ℝ))
    {p : ℝ × CoreAngleState} (hp : p.1 ∈ Ioc 0 Bstar)
    (hu : 0 < p.2 1) (hw : 0 < p.2 2) (hsum : p.2 1 + p.2 2 ≤ p.1)
    (Hcompact : compactEraHistories η J σ Bcap N γ p) (n : ℕ) :
    ∃ w : List ℕ+, w.length = n ∧ p ∈ eraPrefixDomain η J σ Bcap w ∧
      let q := eraPrefixState η J w p
      0 < q.2 1 ∧ 0 < q.2 2 ∧ q.2 1 + q.2 2 ≤ q.1 := by
  induction n with
  | zero => exact ⟨[], rfl, mem_univ _, hu, hw, hsum⟩
  | succ n ih =>
    obtain ⟨w, hlen, hmem, hU, hW, Hsum⟩ := ih
    let q := eraPrefixState η J w p
    have hq : q.1 ∈ Ioc 0 Bstar := by
      rw [show q.1 = eraAmplitude p.1 w.length from eraPrefixState_budget η J w p hp.1.le]
      exact ⟨eraAmplitude_pos hp.1 _, (eraAmplitude_le hp.1.le (hp.2.trans hBstar) _).trans hp.2⟩
    obtain ⟨m, hselected, hU', hW', Hsum'⟩ := Hstep q.1 hq q.2 (Hcompact w hmem) hU hW Hsum
    let a : ℕ+ := ⟨m + 1, by omega⟩
    have ha : a.natPred = m := by simp [a, PNat.natPred]
    have hnext : p ∈ eraPrefixDomain η J σ Bcap (w ++ [a]) := by
      apply (mem_eraPrefixDomain_append η J σ Bcap w [a] p).mpr
      refine ⟨hmem, ?_⟩
      simpa only [eraPrefixDomain, ha, mem_inter_iff, mem_preimage, mem_univ, and_true] using hselected
    have hstate : eraPrefixState η J (w ++ [a]) p = eraBudgetReturn η J m q := by
      rw [eraPrefixState_append]
      simp only [eraPrefixState, ha, Function.comp_apply, id_eq, q]
    refine ⟨w ++ [a], by simp only [List.length_append, List.length_singleton, hlen], hnext, ?_⟩
    rw [hstate]
    exact ⟨hU', hW', Hsum'⟩

/-- No infinite survival hypothesis is needed: each finite length has just been constructed. -/
theorem compactEraHistories_survives {η σ Bcap Bstar γ : ℝ} {J N : ℕ}
    (hBstar : Bstar ≤ 1)
    (Hstep : ∀ B ∈ Ioc 0 Bstar, ∀ X : CoreAngleState,
      X ∈ compactEraPhase N γ → 0 < X 1 → 0 < X 2 → X 1 + X 2 ≤ B →
        ∃ m : ℕ, (B, X) ∈ eraSelectedInputs η J σ Bcap m ∧
          0 < eraNextState η J m X 1 ∧ 0 < eraNextState η J m X 2 ∧
          eraNextState η J m X 1 + eraNextState η J m X 2 ≤ B ^ (4 / 3 : ℝ))
    {p : ℝ × CoreAngleState} (hp : p.1 ∈ Ioc 0 Bstar)
    (hu : 0 < p.2 1) (hw : 0 < p.2 2) (hsum : p.2 1 + p.2 2 ≤ p.1)
    (Hcompact : compactEraHistories η J σ Bcap N γ p) : p ∈ eraSurvivorDomain η J σ Bcap := by
  apply mem_iInter.mpr
  intro n
  obtain ⟨w, hlen, hmem, _⟩ := compactEraHistories_finite_prefix hBstar Hstep hp hu hw hsum Hcompact n
  exact mem_iUnion.mpr ⟨⟨w, hlen⟩, hmem⟩

theorem EraSurvivor.digits_le_of_compactHistories {η σ Bcap γ : ℝ} {J N : ℕ}
    (p : eraSurvivorDomain η J σ Bcap)
    (Hcompact : compactEraHistories η J σ Bcap N γ p.val) (n : ℕ) : (digits p n : ℕ) ≤ N := by
  have Hnext := mem_word_domain p (n + 1)
  rw [word_succ] at Hnext
  have hs := ((mem_eraPrefixDomain_append η J σ Bcap (word p n) [digits p n] p.val).mp Hnext).2.1
  have hphase := (Hcompact (word p n) (mem_word_domain p n)).2.1
  have hβ : 0 < (eraPrefixState η J (word p n) p.val).1 ^ σ := Real.rpow_pos_of_pos hs.1.1.1 _
  have hlow := hs.1.2.2.2.2.2.1
  have hcast : ((digits p n).natPred : ℝ) + 1 = (digits p n : ℝ) := by
    exact_mod_cast (digits p n).natPred_add_one
  rw [hcast] at hlow
  exact_mod_cast (show (digits p n : ℝ) ≤ (N : ℝ) by linarith only [hlow, hphase, hβ])

/-- Compact finite histories enter the already constructed bounded-digit Borel domain at a common scale. -/
theorem exists_compactEra_survival :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∀ N : ℕ, ∀ γ : ℝ, 0 < γ → γ < 1 / 4 → ∀ Bcap : ℝ, 0 < Bcap →
          ∃ Bstar > (0 : ℝ), Bstar ≤ Bcap ∧ Bstar < 1 ∧
            ∀ p : ℝ × CoreAngleState, p.1 ∈ Ioc 0 Bstar →
              0 < p.2 1 → 0 < p.2 2 → p.2 1 + p.2 2 ≤ p.1 →
              compactEraHistories η J σ Bcap N γ p → p ∈ EraSurvivor.boundedDigitDomain η J σ Bcap := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_compactEra_step
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ N γ hγ hγmax Bcap hcap
  obtain ⟨Bstar, hBstar, hBcap, hBone, H⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ N γ hγ hγmax Bcap hcap
  refine ⟨Bstar, hBstar, hBcap, hBone, ?_⟩
  intro p hp hu hw hsum Hcompact
  have hs : p ∈ eraSurvivorDomain η J σ Bcap := compactEraHistories_survives hBone.le (by
    intro B hB X hX hU hW Hsum
    obtain ⟨m, _, _, Hsel, hU', hW', Hsum', _⟩ := H B hB X hX hU hW Hsum
    exact ⟨m, Hsel, hU', hW', Hsum'⟩) hp hu hw hsum Hcompact
  let q : eraSurvivorDomain η J σ Bcap := ⟨p, hs⟩
  exact ⟨q, ⟨N, EraSurvivor.digits_le_of_compactHistories q Hcompact⟩, rfl⟩

end BianchiIX
