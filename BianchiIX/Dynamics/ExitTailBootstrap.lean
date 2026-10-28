import BianchiIX.Dynamics.ExitTailPrefix

noncomputable section

namespace BianchiIX

open Set

theorem exists_exitTail_feedback_budget {A D : ℝ} (hA : 1 ≤ A) (hD : 0 ≤ D) :
    ∃ ε > (0 : ℝ), ε ≤ 1 ∧ ∀ T b α K : ℝ,
      0 ≤ T → 0 ≤ b → b * (1 + T) ≤ ε → α * T ≤ K →
      exitTailRateBudget α b A D T ≤ 10 * K + 6 ∧
      20 * (A * b + (A * b) ^ 2 * T) ≤ 40 * A * b := by
  let C := 10 * D + 100 * A + 100 * A ^ 2
  let ε := 1 / (C + 1)
  have hA0 : 0 ≤ A := by linarith only [hA]
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hε1 : ε ≤ 1 := (div_le_iff₀ (by positivity : 0 < C + 1)).mpr (by linarith only [hC])
  have hCε : C * ε ≤ 1 := by
    dsimp only [ε]
    rw [mul_one_div]
    exact (div_le_iff₀ (by positivity : 0 < C + 1)).mpr (by linarith)
  have hAε : A * ε ≤ 1 := by
    have hAC : A ≤ C := by dsimp only [C]; nlinarith only [hA, hD, sq_nonneg A]
    exact (mul_le_mul_of_nonneg_right hAC hε.le).trans hCε
  refine ⟨ε, hε, hε1, ?_⟩
  intro T b α K hT hb hsmall hα
  have hbε : b ≤ ε := by nlinarith only [hsmall, mul_nonneg hb hT]
  have hbT : b * T ≤ ε := by nlinarith only [hsmall, hb]
  have hb1 : b ≤ 1 := hbε.trans hε1
  have hb2T : b ^ 2 * T ≤ ε := by
    have H := mul_le_mul_of_nonneg_left hb1 (mul_nonneg hb hT)
    nlinarith only [H, hbT]
  have hfeedback : 10 * D * b * T + 100 * A * b + 100 * A ^ 2 * b ^ 2 * T ≤ 1 := by
    have H1 := mul_le_mul_of_nonneg_left hbT (by positivity : 0 ≤ 10 * D)
    have H2 := mul_le_mul_of_nonneg_left hbε (by positivity : 0 ≤ 100 * A)
    have H3 := mul_le_mul_of_nonneg_left hb2T (by positivity : 0 ≤ 100 * A ^ 2)
    dsimp only [C] at hCε
    nlinarith only [H1, H2, H3, hCε]
  have hAbT : A * b * T ≤ 1 := by
    nlinarith only [mul_le_mul_of_nonneg_left hbT hA0, hAε]
  constructor
  · dsimp only [exitTailRateBudget]
    nlinarith only [hfeedback, hα]
  · nlinarith only [mul_le_mul_of_nonneg_left hAbT (mul_nonneg hA0 hb)]

/-- A single smallness budget improves both wall and radial bootstrap constants by a factor of two. -/
theorem exists_exitTail_strict_prefix_bounds {K : ℝ} (hK : 0 ≤ K) :
    ∃ A ≥ (2 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 ∧ ∀ T α b : ℝ, ∀ Y : ℝ → ExitTailState,
      0 ≤ T → 0 ≤ α → 0 ≤ b → b * (1 + T) ≤ ε → α * T ≤ K →
      (∀ s ∈ Icc 0 T, HasDerivAt Y (exitTailField (Real.exp (-s)) (Y s)) s) →
      (∀ s ∈ Icc 0 T, exitTailRegion α b A (80 * A) (Y s)) →
      |Y 0 1| + |Y 0 2| ≤ b →
      (∀ i : Fin 2,
        Y T i.succ = Y 0 i.succ * exitTailMultiplier Y i T ∧
        2 / A ≤ exitTailMultiplier Y i T ∧ exitTailMultiplier Y i T ≤ A / 2) ∧
      |Y T 1| + |Y T 2| ≤ A * b / 2 ∧ |Y T 0 - Y 0 0| ≤ 40 * A * b := by
  let L := 10 * K + 6
  let A := 2 * Real.exp L
  have hL : 0 ≤ L := by dsimp only [L]; linarith only [hK]
  have hA : 2 ≤ A := by
    have H : 1 ≤ Real.exp L := Real.one_le_exp_iff.mpr hL
    dsimp only [A]
    linarith only [H]
  have hA0 : 0 ≤ A := by linarith only [hA]
  obtain ⟨ε, hε, hε1, HB⟩ := exists_exitTail_feedback_budget
    (by linarith only [hA] : 1 ≤ A) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 80) hA0)
  refine ⟨A, hA, ε, hε, hε1, ?_⟩
  intro T α b Y hT hα hb hsmall hwait hY hreg hinit
  obtain ⟨hrate, hrad⟩ := HB T b α K hT hb hsmall hwait
  have hmult (i : Fin 2) : Y T i.succ = Y 0 i.succ * exitTailMultiplier Y i T ∧
      2 / A ≤ exitTailMultiplier Y i T ∧ exitTailMultiplier Y i T ≤ A / 2 := by
    obtain ⟨heq, hlo, hhi⟩ := exitTail_prefix_multipliers hT hα hb hA0 hY hreg i
    refine ⟨heq, ?_, ?_⟩
    · have H := (Real.exp_le_exp.mpr (neg_le_neg hrate)).trans hlo
      have he : Real.exp (-L) = 2 / A := by
        rw [Real.exp_neg]
        dsimp only [A]
        field_simp
      exact he ▸ H
    · have H := hhi.trans (Real.exp_le_exp.mpr hrate)
      have he : Real.exp L = A / 2 := by dsimp only [A]; ring
      exact H.trans_eq he
  refine ⟨hmult, ?_, (exitTail_prefix_radial_bound hT hb hA0 hY hreg).trans hrad⟩
  obtain ⟨he0, _, hi0⟩ := hmult 0
  obtain ⟨he1, _, hi1⟩ := hmult 1
  change Y T 1 = Y 0 1 * exitTailMultiplier Y 0 T at he0
  change Y T 2 = Y 0 2 * exitTailMultiplier Y 1 T at he1
  rw [he0, he1, abs_mul, abs_mul,
    abs_of_pos (show 0 < exitTailMultiplier Y 0 T from Real.exp_pos _),
    abs_of_pos (show 0 < exitTailMultiplier Y 1 T from Real.exp_pos _)]
  have H0 := mul_le_mul_of_nonneg_left hi0 (abs_nonneg (Y 0 1))
  have H1 := mul_le_mul_of_nonneg_left hi1 (abs_nonneg (Y 0 2))
  have H := mul_le_mul_of_nonneg_right hinit (by positivity : 0 ≤ A / 2)
  nlinarith only [H0, H1, H]

end BianchiIX
