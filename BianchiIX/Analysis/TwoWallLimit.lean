import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

theorem exists_positive_wall_approximation {u ε : ℝ} (hε : 0 < ε)
    (hu : 0 ≤ u ∧ u ≤ ε) :
    ∃ q : ℕ → ℝ, Tendsto q atTop (𝓝 u) ∧ ∀ n, 0 < q n ∧ q n ≤ ε := by
  by_cases h : u = 0
  · subst u
    refine ⟨fun n => ε / ((n : ℝ) + 1), ?_, ?_⟩
    · simpa only [div_eq_mul_inv, one_mul, mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ε
    · intro n
      exact ⟨by positivity, div_le_self hε.le (by have := Nat.cast_nonneg (α := ℝ) n; linarith)⟩
  · exact ⟨fun _ => u, tendsto_const_nhds, fun _ => ⟨lt_of_le_of_ne hu.1 (Ne.symm h), hu.2⟩⟩

/-- A continuous inequality at two nonnegative walls follows from the positive interior,
while the center and active coordinate remain exactly fixed. -/
theorem le_of_two_nonnegative_walls {f : (Fin 4 → ℝ) → ℝ} {y : Fin 4 → ℝ} {ε B : ℝ}
    (hε : 0 < ε) (hu : 0 ≤ y 1 ∧ y 1 ≤ ε) (hw : 0 ≤ y 3 ∧ y 3 ≤ ε)
    (hf : ContinuousAt f y)
    (hbound : ∀ z : Fin 4 → ℝ, z 0 = y 0 → z 2 = y 2 →
      (0 < z 1 ∧ z 1 ≤ ε) → (0 < z 3 ∧ z 3 ≤ ε) → f z ≤ B) : f y ≤ B := by
  obtain ⟨u, hlu, hu⟩ := exists_positive_wall_approximation hε hu
  obtain ⟨w, hlw, hw⟩ := exists_positive_wall_approximation hε hw
  let q : ℕ → (Fin 4 → ℝ) := fun n => ![y 0, u n, y 2, w n]
  have hq : Tendsto q atTop (𝓝 y) := by
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · exact tendsto_const_nhds
    · exact hlu
    · exact tendsto_const_nhds
    · exact hlw
  exact le_of_tendsto_of_tendsto' (hf.tendsto.comp hq) tendsto_const_nhds
    (fun n => hbound (q n) rfl rfl (hu n) (hw n))

end BianchiIX
