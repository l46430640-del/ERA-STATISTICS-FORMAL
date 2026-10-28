import BianchiIX.Dynamics.ExitTailSecondBounds
import BianchiIX.Dynamics.ExitTailScale

noncomputable section

namespace BianchiIX

open Set

theorem exists_exitTail_uniform_variation_budget {η : ℝ} (hη : 0 < η ∧ η ≤ 1)
    {J : ℕ} (hJ : 1 ≤ J) :
    ∃ A ≥ (2 : ℝ), ∃ B ≥ (0 : ℝ), ∃ ε > (0 : ℝ),
      ∀ (α b T : ℝ) (Y : ℝ → ExitTailState),
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J →
      (0 ≤ T ∧ T ≤ exitTailLength η α J) → Y 0 0 = 2 + 2 * α →
      |Y 0 1| + |Y 0 2| ≤ b →
      (∀ s ∈ Icc 0 T, HasDerivAt Y (exitTailField (Real.exp (-s)) (Y s)) s) →
      (∀ s ∈ Icc 0 T, exitTailRegion α b A (80 * A) (Y s)) ∧
        exitTailVariationBudget α b A (80 * A) T ≤ B := by
  let K := Real.log (1 / η) + J * Real.exp (-1)
  let Q := 1 + Real.log (1 / η) + Real.exp (-1)
  have he : 0 ≤ Real.log (1 / η) := Real.log_nonneg
    ((le_div_iff₀ hη.1).mpr (by linarith only [hη.2]))
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  obtain ⟨A, hA, ε₀, hε₀, HP⟩ := exists_exitTail_scale_bounds hη hJ
  have hA0 : 0 ≤ A := by linarith only [hA]
  obtain ⟨δ, hδ, hδ1, HB⟩ := exists_exitTail_feedback_budget
    (by linarith only [hA] : 1 ≤ A) (by positivity : 0 ≤ 80 * A)
  let B := 2 * (10 * K + 6) + 2048 * (1 + A)
  let ε := min ε₀ (δ / Q)
  have hε : 0 < ε := lt_min hε₀ (div_pos hδ hQ)
  refine ⟨A, hA, B, by dsimp only [B]; positivity, ε, hε, ?_⟩
  intro α b T Y hα hb hsmall hT hR hw hY
  have hsmall₀ : b ≤ ε₀ * α ^ J := hsmall.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hα.1.le J))
  have Hpath := HP α b T Y hα hb hsmall₀ hT hR hw hY
  have Hscale := (exitTail_smallness_budgets hη hα hε.le hJ hsmall).1
  have Hδ : ε * Q ≤ δ := (le_div_iff₀ hQ).mp (min_le_right _ _)
  have Hsmall : b * (1 + T) ≤ δ :=
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hT.2) hb.le).trans (Hscale.trans Hδ)
  have Hwait := (exitTailLength_weighted_bounds hη hα J).1
  have Hrate := (HB T b α K hT.1 hb.le Hsmall
    ((mul_le_mul_of_nonneg_left hT.2 hα.1.le).trans Hwait)).1
  have HbT : b * T ≤ 1 := by nlinarith only [Hsmall, hδ1, hb]
  have HAbT := mul_le_mul_of_nonneg_left HbT hA0
  refine ⟨fun s hs => (Hpath s hs).1, ?_⟩
  dsimp only [exitTailVariationBudget, B]
  nlinarith only [Hrate, HAbT]

/-- Uniform first variations on every subinterval, with no dependence on alpha or the wall ratio. -/
theorem exists_exitTail_uniform_linear_bound {η : ℝ} (hη : 0 < η ∧ η ≤ 1)
    {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ (α b T : ℝ) (Y : ℝ → ExitTailState),
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J →
      (0 ≤ T ∧ T ≤ exitTailLength η α J) → Y 0 0 = 2 + 2 * α →
      |Y 0 1| + |Y 0 2| ≤ b →
      (∀ s ∈ Icc 0 T, HasDerivAt Y (exitTailField (Real.exp (-s)) (Y s)) s) →
      ∀ (X : ℝ → ExitTailState) (a t : ℝ), 0 ≤ a → a ≤ t → t ≤ T →
      (∀ s ∈ Icc a t, HasDerivAt X
        (fderiv ℝ (exitTailField (Real.exp (-s))) (Y s) (X s)) s) → ‖X t‖ ≤ C * ‖X a‖ := by
  obtain ⟨A, hA, B, hB, ε, hε, H⟩ := exists_exitTail_uniform_variation_budget hη hJ
  refine ⟨Real.exp (3 * B), Real.one_le_exp_iff.mpr (by positivity), ε, hε, ?_⟩
  intro α b T Y hα hb hsmall hT hR hw hY X a t ha hat ht hX
  obtain ⟨hreg, hbudget⟩ := H α b T Y hα hb hsmall hT hR hw hY
  apply (exitTail_variation_bound hT.1 hα.1.le hb.le (by linarith only [hA])
    (HasDerivAt.continuousOn hY) hreg ha hat ht hX).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hbudget (by norm_num))

theorem exists_exitTail_uniform_second_bound {η : ℝ} (hη : 0 < η ∧ η ≤ 1)
    {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ (α b T : ℝ) (Y X Z Q : ℝ → ExitTailState),
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J →
      (0 ≤ T ∧ T ≤ exitTailLength η α J) → Y 0 0 = 2 + 2 * α →
      |Y 0 1| + |Y 0 2| ≤ b →
      (∀ s ∈ Icc 0 T, HasDerivAt Y (exitTailField (Real.exp (-s)) (Y s)) s) →
      (∀ s ∈ Icc 0 T, HasDerivAt X
        (fderiv ℝ (exitTailField (Real.exp (-s))) (Y s) (X s)) s) →
      (∀ s ∈ Icc 0 T, HasDerivAt Z
        (fderiv ℝ (exitTailField (Real.exp (-s))) (Y s) (Z s)) s) →
      (∀ s ∈ Icc 0 T, HasDerivAt Q
        (fderiv ℝ (exitTailField (Real.exp (-s))) (Y s) (Q s) +
          fderiv ℝ (fderiv ℝ (exitTailField (Real.exp (-s)))) (Y s) (X s) (Z s)) s) →
      Q 0 = 0 → ‖Q T‖ ≤ C * T * ‖X 0‖ * ‖Z 0‖ := by
  obtain ⟨A, hA, B, hB, ε, hε, H⟩ := exists_exitTail_uniform_variation_budget hη hJ
  obtain ⟨C, hC, HC⟩ := exists_exitTail_second_variation_bound
  have hC0 : 0 ≤ C := by linarith only [hC]
  have he : 1 ≤ Real.exp (9 * B) := Real.one_le_exp_iff.mpr (by positivity)
  refine ⟨C * Real.exp (9 * B), ?_, ε, hε, ?_⟩
  · nlinarith only [hC, he, mul_le_mul_of_nonneg_left he hC0]
  intro α b T Y X Z Q hα hb hsmall hT hR hw hY hX hZ hQ hQ0
  obtain ⟨hreg, hbudget⟩ := H α b T Y hα hb hsmall hT hR hw hY
  apply (HC Y X Z Q T α b A (80 * A) hT.1 hα.1.le hb.le (by linarith only [hA])
    (HasDerivAt.continuousOn hY) hreg hX hZ hQ hQ0).trans
  have he' := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hbudget (by norm_num : (0 : ℝ) ≤ 9))
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he' hC0) hT.1) (norm_nonneg _))
    (norm_nonneg _)

end BianchiIX
