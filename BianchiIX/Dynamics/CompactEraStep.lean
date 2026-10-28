import BianchiIX.Dynamics.EraInputEstimates

noncomputable section

namespace BianchiIX

open Set

def compactEraPhase (N : ℕ) (γ : ℝ) : Set CoreAngleState :=
  {X | 2 + 2 * γ ≤ X 0 ∧ X 0 ≤ 2 * N ∧
    X 0 / 2 - (⌊X 0 / 2⌋₊ : ℝ) ∈ Icc γ (1 - γ)}

theorem mem_compactEraPhase_of_integer_separation {N : ℕ} {γ : ℝ} {X : CoreAngleState}
    (hγ : 0 ≤ γ) (hlo : 2 + 2 * γ ≤ X 0) (hhi : X 0 ≤ 2 * N)
    (hsep : ∀ k : ℤ, γ ≤ |X 0 / 2 - k|) : X ∈ compactEraPhase N γ := by
  have hx : 0 ≤ X 0 / 2 := by linarith only [hlo, hγ]
  have hf := Nat.floor_le hx
  have hnext := Nat.lt_floor_add_one (X 0 / 2)
  have hleft := hsep (⌊X 0 / 2⌋₊ : ℤ)
  have hright := hsep ((⌊X 0 / 2⌋₊ : ℤ) + 1)
  push_cast at hleft hright
  rw [abs_of_nonneg (sub_nonneg.mpr hf)] at hleft
  rw [abs_of_nonpos (by linarith only [hnext])] at hright
  exact ⟨hlo, hhi, hleft, by linarith only [hright]⟩

/-- A compact phase selects a positive digit below the retained digit cutoff. -/
theorem exists_compactEra_digit {N : ℕ} {γ β : ℝ} {X : CoreAngleState}
    (hγ : 0 < γ) (hβ : 0 < β) (hβγ : β < γ / 4) (hβN : β < 1 / ((N : ℝ) + 2))
    (hX : X ∈ compactEraPhase N γ) :
    ∃ m : ℕ, m + 1 = ⌊X 0 / 2⌋₊ ∧ m + 1 ≤ N ∧ m < ⌊1 / β⌋₊ ∧
      X 0 ∈ Icc (2 * ((m : ℝ) + 1 + β)) (2 * ((m : ℝ) + 2 - β)) ∧
      X 0 / 2 - ((m : ℝ) + 1) ∈ Icc γ (1 - γ) := by
  let n := ⌊X 0 / 2⌋₊
  have hn1 : 1 ≤ n := (Nat.one_le_floor_iff _).mpr (by linarith only [hX.1, hγ])
  have hnN : n ≤ N := Nat.floor_le_of_le (by linarith only [hX.2.1])
  have hnreal : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast Nat.sub_add_cancel hn1
  have hNrec : (N : ℝ) ≤ 1 / β := by
    have H := (lt_div_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 2)).mp hβN
    apply (le_div_iff₀ hβ).mpr
    nlinarith only [H, hβ]
  have hcut : N ≤ ⌊1 / β⌋₊ := Nat.le_floor hNrec
  have hfrac : X 0 / 2 - (((n - 1 : ℕ) : ℝ) + 1) ∈ Icc γ (1 - γ) := by
    rw [hnreal]
    exact hX.2.2
  refine ⟨n - 1, by omega, by omega, by omega, ?_, hfrac⟩
  constructor <;> linarith only [hfrac.1, hfrac.2, hβγ, hγ]

/-- The actual output has a uniform positive margin from both retained endpoints. -/
theorem compactEra_retained_margin {γ β f y : ℝ}
    (hβγ : β < γ / 4) (hf : f ∈ Icc γ (1 - γ))
    (herror : |y - f| < β / 4) :
    7 * γ / 16 < y - 2 * β ∧ 7 * γ / 16 < (1 - 2 * β) - y ∧
      y ∈ Ioo (2 * β) (1 - 2 * β) := by
  obtain ⟨hl, hu⟩ := abs_lt.mp herror
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith only [hl, hu, hf.1, hf.2, hβγ]

/-- Every sufficiently small compact-phase input completes a retained actual era and propagates the amplitude budget. -/
theorem exists_compactEra_step :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∀ N : ℕ, ∀ γ : ℝ, 0 < γ → γ < 1 / 4 → ∀ Bcap : ℝ, 0 < Bcap →
          ∃ Bstar > (0 : ℝ), Bstar ≤ Bcap ∧ Bstar < 1 ∧
            ∀ B ∈ Ioc 0 Bstar, ∀ X : CoreAngleState,
              X ∈ compactEraPhase N γ → 0 < X 1 → 0 < X 2 → X 1 + X 2 ≤ B →
                ∃ m : ℕ, m + 1 = ⌊X 0 / 2⌋₊ ∧ m + 1 ≤ N ∧
                  (B, X) ∈ eraSelectedInputs η J σ Bcap m ∧
                  0 < eraNextState η J m X 1 ∧ 0 < eraNextState η J m X 2 ∧
                  eraNextState η J m X 1 + eraNextState η J m X 2 ≤ B ^ (4 / 3 : ℝ) ∧
                  ∀ j ≤ m, coreRadiusReturnValid ((coreReflectionState coreRadiusReturnTime)^[j] X) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_input_estimates
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ N γ hγ _ Bcap hcap
  obtain ⟨C, _, Bi, hBi, hBione, Hi⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bb, hBb, _, Hb⟩ := exists_common_rpow_budget (ι := Fin 1) Finset.univ
    (C := fun _ => 1) (p := fun _ => σ) (ε := fun _ => min (γ / 4) (1 / ((N : ℝ) + 2)))
    (by intros; norm_num) (by intros; exact hσ)
    (by intros; exact lt_min (by positivity) (by positivity)) (by norm_num : (0 : ℝ) < 1)
  refine ⟨min Bi (min Bcap Bb), lt_min hBi (lt_min hcap hBb),
    (min_le_right _ _).trans (min_le_left _ _), (min_le_left _ _).trans_lt hBione, ?_⟩
  intro B hB X hX hu hw hsum
  have hBi' : B ∈ Ioc 0 Bi := ⟨hB.1, hB.2.trans (min_le_left _ _)⟩
  have hBcap : B ∈ Ioc 0 Bcap := ⟨hB.1, hB.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hβ : 0 < B ^ σ := Real.rpow_pos_of_pos hB.1 _
  have hβsmall : B ^ σ < min (γ / 4) (1 / ((N : ℝ) + 2)) := by
    simpa only [one_mul] using Hb B ⟨hB.1, hB.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
      0 (Finset.mem_univ _)
  obtain ⟨m, hcount, hN, hm, hr, hf⟩ := exists_compactEra_digit hγ hβ
    (hβsmall.trans_le (min_le_left _ _)) (hβsmall.trans_le (min_le_right _ _)) hX
  obtain ⟨Herr, Hmargin, hU, hW, Hsum, Hvalid⟩ := Hi m (B, X) ⟨hBi', hm, hu, hw, hsum, hr⟩
  have Hret := compactEra_retained_margin (hβsmall.trans_le (min_le_left _ _)) hf
    (Herr.trans_lt Hmargin)
  exact ⟨m, hcount, hN, ⟨⟨hBcap, hm, hu, hw, hsum, hr⟩, Hret.2.2⟩, hU, hW, Hsum, Hvalid⟩

end BianchiIX
