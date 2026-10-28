import BianchiIX.Dynamics.CoreEvenSeparation
import BianchiIX.Dynamics.CompactEraStep

noncomputable section

namespace BianchiIX

/-- Physical Taub avoidance forces every sufficiently small core into one common compact phase range. -/
theorem exists_compactEraPhase_of_taub_avoidance {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ γ > (0 : ℝ), γ < 1 / 4 ∧ ∃ B > (0 : ℝ),
      ∀ Y : CoreAngleState, 2 - γ / 2 ≤ Y 0 → 0 < Y 1 → 0 < Y 2 → Y 1 + Y 2 ≤ B →
        normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry Y)) →
        Y ∈ compactEraPhase N γ := by
  obtain ⟨δ, hδ, _, C, hC, H⟩ := exists_core_even_separation
  obtain ⟨ρ, hρ, hρmax, Hsep⟩ := H ε hε
  let K := 8 / ε
  let N := ⌈K / 2⌉₊
  let γ := ρ / 4
  let B := min (1 / 100) (min (δ / (1 + K)) (ρ / (4 * C)))
  have hK : 0 < K := div_pos (by norm_num) hε
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hB : 0 < B := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hγmax : γ < 1 / 4 := by dsimp [γ]; linarith only [hρmax]
  refine ⟨N, γ, hγ, hγmax, B, hB, ?_⟩
  intro Y hk hu hw hb ha
  have hk1 : 1 ≤ Y 0 := by linarith only [hk, hγmax]
  have hb100 : Y 1 + Y 2 ≤ 1 / 100 := hb.trans (min_le_left _ _)
  have hu100 : 0 ≤ Y 1 ∧ Y 1 ≤ 1 / 100 := ⟨hu.le, by linarith only [hb100, hw]⟩
  have hw100 : 0 ≤ Y 2 ∧ Y 2 ≤ 1 / 100 := ⟨hw.le, by linarith only [hb100, hu]⟩
  have hupper : Y 0 < K := coreRadiusEntry_radius_bound_of_away hε hk1 hu100 hw100 (ha.initial 0)
  have hbudget : Y 1 + Y 2 ≤ δ / (1 + Y 0) :=
    (hb.trans ((min_le_right _ _).trans (min_le_left _ _))).trans
      (div_le_div_of_nonneg_left hδ.le (by linarith only [hk1]) (by linarith only [hupper]))
  have hsmall : C * (Y 1 + Y 2) ≤ ρ / 4 := by
    have HH : Y 1 + Y 2 ≤ ρ / (4 * C) := hb.trans ((min_le_right _ _).trans (min_le_right _ _))
    have HH' := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp HH
    nlinarith only [HH']
  have hsep := Hsep Y hu hw hbudget hsmall ha
  have hlo : 2 + 2 * γ ≤ Y 0 := by
    have HH := hsep 1 (by omega)
    norm_num only [Nat.cast_one, mul_one] at HH
    rcases lt_abs.mp HH with hp | hm
    · dsimp [γ]
      linarith only [hp]
    · dsimp [γ] at hk
      linarith only [hm, hk, hρ]
  have hN : K / 2 ≤ (N : ℝ) := Nat.le_ceil _
  apply mem_compactEraPhase_of_integer_separation hγ.le hlo (by linarith only [hupper, hN])
  intro k
  cases k with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, Int.cast_natCast]
    cases n with
    | zero =>
      rw [Nat.cast_zero, sub_zero]
      rw [abs_of_nonneg (by linarith only [hlo, hγ] : 0 ≤ Y 0 / 2)]
      linarith only [hlo]
    | succ n =>
      have HH := hsep (n + 1) (by omega)
      have heq : Y 0 - 2 * (n + 1 : ℕ) = 2 * (Y 0 / 2 - (n + 1 : ℕ)) := by ring
      rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at HH
      change γ ≤ |Y 0 / 2 - (n + 1 : ℕ)|
      dsimp [γ]
      exact (by linarith only [HH] : ρ / 4 ≤ |Y 0 / 2 - (n + 1 : ℕ)|)
  | negSucc n =>
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    simp only [Int.cast_negSucc, Nat.cast_add, Nat.cast_one]
    rw [abs_of_nonneg (by linarith only [hlo, hγ, hn] : 0 ≤ Y 0 / 2 - -((n : ℝ) + 1))]
    linarith only [hlo, hn]

end BianchiIX
