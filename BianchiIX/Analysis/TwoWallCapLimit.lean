import BianchiIX.Analysis.TwoWallLimit
import Mathlib.Analysis.Real.Sqrt

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

/-- Positive approximation inside a wall box with a closed bound on the wall sum. -/
theorem exists_positive_walls_sum_approximation {y : Fin 4 → ℝ} {ε b : ℝ}
    (hε : 0 < ε) (hb : 0 < b) (hu : 0 ≤ y 1 ∧ y 1 ≤ ε)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ ε) (hs : y 1 + y 3 ≤ b) :
    ∃ q : ℕ → (Fin 4 → ℝ), Tendsto q atTop (𝓝 y) ∧ ∀ n,
      q n 0 = y 0 ∧ q n 2 = y 2 ∧ (0 < q n 1 ∧ q n 1 ≤ ε) ∧
      (0 < q n 3 ∧ q n 3 ≤ ε) ∧ q n 1 + q n 3 ≤ b := by
  obtain ⟨t, ht, htb⟩ := exists_positive_wall_approximation (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1)
  let a := min ε (b / 2)
  have ha : 0 < a := lt_min hε (by positivity)
  have haε : a ≤ ε := min_le_left _ _
  have hab : 2 * a ≤ b := by linarith [min_le_right ε (b / 2)]
  let p (s : ℝ) (n : ℕ) := (1 - t n) * s + t n * a
  have hp (s : ℝ) : Tendsto (p s) atTop (𝓝 s) := by
    simpa [p] using (((tendsto_const_nhds (x := (1 : ℝ))).sub ht).mul_const s).add (ht.mul_const a)
  have hpb {s : ℝ} (hs : 0 ≤ s ∧ s ≤ ε) (n : ℕ) : 0 < p s n ∧ p s n ≤ ε := by
    have h1 : 0 ≤ 1 - t n := sub_nonneg.mpr (htb n).2
    refine ⟨add_pos_of_nonneg_of_pos (mul_nonneg h1 hs.1) (mul_pos (htb n).1 ha), ?_⟩
    dsimp only [p]
    nlinarith only [mul_le_mul_of_nonneg_left hs.2 h1,
      mul_le_mul_of_nonneg_left haε (htb n).1.le]
  let q : ℕ → (Fin 4 → ℝ) := fun n => ![y 0, p (y 1) n, y 2, p (y 3) n]
  refine ⟨q, ?_, ?_⟩
  · apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · exact tendsto_const_nhds
    · exact hp _
    · exact tendsto_const_nhds
    · exact hp _
  · intro n
    refine ⟨rfl, rfl, hpb hu n, hpb hw n, ?_⟩
    change p (y 1) n + p (y 3) n ≤ b
    dsimp only [p]
    nlinarith only [mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr (htb n).2),
      mul_le_mul_of_nonneg_left hab (htb n).1.le]

theorem le_of_two_nonnegative_walls_sum {f g : (Fin 4 → ℝ) → ℝ} {y : Fin 4 → ℝ} {ε b : ℝ}
    (hε : 0 < ε) (hb : 0 < b) (hu : 0 ≤ y 1 ∧ y 1 ≤ ε)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ ε) (hs : y 1 + y 3 ≤ b)
    (hf : ContinuousAt f y) (hg : ContinuousAt g y)
    (hbound : ∀ z : Fin 4 → ℝ, z 0 = y 0 → z 2 = y 2 →
      (0 < z 1 ∧ z 1 ≤ ε) → (0 < z 3 ∧ z 3 ≤ ε) → z 1 + z 3 ≤ b → f z ≤ g z) :
    f y ≤ g y := by
  obtain ⟨q, hq, hqb⟩ := exists_positive_walls_sum_approximation hε hb hu hw hs
  exact le_of_tendsto_of_tendsto' (hf.tendsto.comp hq) (hg.tendsto.comp hq)
    (fun n => hbound (q n) (hqb n).1 (hqb n).2.1 (hqb n).2.2.1
      (hqb n).2.2.2.1 (hqb n).2.2.2.2)

theorem le_of_two_nonnegative_walls_continuous {f g : (Fin 4 → ℝ) → ℝ}
    {y : Fin 4 → ℝ} {ε : ℝ} (hε : 0 < ε) (hu : 0 ≤ y 1 ∧ y 1 ≤ ε)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ ε) (hf : ContinuousAt f y) (hg : ContinuousAt g y)
    (hbound : ∀ z : Fin 4 → ℝ, z 0 = y 0 → z 2 = y 2 →
      (0 < z 1 ∧ z 1 ≤ ε) → (0 < z 3 ∧ z 3 ≤ ε) → f z ≤ g z) : f y ≤ g y := by
  exact sub_nonpos.mp (le_of_two_nonnegative_walls hε hu hw (hf.sub hg)
    (fun z h0 h2 hu hw => sub_nonpos.mpr (hbound z h0 h2 hu hw)))

/-- The quadratic smallness condition is preserved, including its equality boundary. -/
theorem le_of_two_nonnegative_walls_quadratic {f g : (Fin 4 → ℝ) → ℝ}
    {y : Fin 4 → ℝ} {ε k : ℝ} (hε : 0 < ε) (hk : 0 < k)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ ε) (hw : 0 ≤ y 3 ∧ y 3 ≤ ε)
    (hs : k * (y 1 + y 3) ^ 2 ≤ 1) (hf : ContinuousAt f y) (hg : ContinuousAt g y)
    (hbound : ∀ z : Fin 4 → ℝ, z 0 = y 0 → z 2 = y 2 →
      (0 < z 1 ∧ z 1 ≤ ε) → (0 < z 3 ∧ z 3 ≤ ε) → k * (z 1 + z 3) ^ 2 ≤ 1 →
      f z ≤ g z) : f y ≤ g y := by
  have hcap : y 1 + y 3 ≤ Real.sqrt (1 / k) :=
    Real.le_sqrt_of_sq_le ((le_div_iff₀ hk).mpr (by simpa only [mul_comm] using hs))
  apply le_of_two_nonnegative_walls_sum hε (Real.sqrt_pos.mpr (one_div_pos.mpr hk))
    hu hw hcap hf hg
  intro z h0 h2 hu hw hs
  apply hbound z h0 h2 hu hw
  have H := (Real.le_sqrt (add_nonneg hu.1.le hw.1.le) (one_div_pos.mpr hk).le).mp hs
  exact (mul_comm _ _).trans_le ((le_div_iff₀ hk).mp H)

end BianchiIX
