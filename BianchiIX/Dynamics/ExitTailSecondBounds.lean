import BianchiIX.Dynamics.ExitTailVariationBounds

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- The bounded state Hessian and the integrated Jacobian give linear, rather than exponential, duration loss. -/
theorem exists_exitTail_second_variation_bound :
    ∃ C ≥ (1 : ℝ), ∀ (Y X Z Q : ℝ → ExitTailState) (T α b A D : ℝ),
      0 ≤ T → 0 ≤ α → 0 ≤ b → 0 ≤ A →
      ContinuousOn Y (Icc 0 T) →
      (∀ s ∈ Icc 0 T, exitTailRegion α b A D (Y s)) →
      (∀ s ∈ Icc 0 T, HasDerivAt X
        (fderiv ℝ (exitTailField (Real.exp (-s))) (Y s) (X s)) s) →
      (∀ s ∈ Icc 0 T, HasDerivAt Z
        (fderiv ℝ (exitTailField (Real.exp (-s))) (Y s) (Z s)) s) →
      (∀ s ∈ Icc 0 T, HasDerivAt Q
        (fderiv ℝ (exitTailField (Real.exp (-s))) (Y s) (Q s) +
          fderiv ℝ (fderiv ℝ (exitTailField (Real.exp (-s)))) (Y s) (X s) (Z s)) s) →
      Q 0 = 0 →
      ‖Q T‖ ≤ C * Real.exp (9 * exitTailVariationBudget α b A D T) * T * ‖X 0‖ * ‖Z 0‖ := by
  obtain ⟨C, hC, HC⟩ := exists_exitTail_hessian_forcing_bound
  refine ⟨C, hC, ?_⟩
  intro Y X Z Q T α b A D hT hα hb hA hY hreg hX hZ hQ hQ0
  let B := exitTailVariationBudget α b A D T
  let L := Real.exp (3 * B)
  have hL : 0 ≤ L := (Real.exp_pos _).le
  have HX (s : ℝ) (hs : s ∈ Icc 0 T) : ‖X s‖ ≤ L * ‖X 0‖ :=
    exitTail_variation_bound hT hα hb hA hY hreg le_rfl hs.1 hs.2
      (fun r hr => hX r ⟨hr.1, hr.2.trans hs.2⟩)
  have HZ (s : ℝ) (hs : s ∈ Icc 0 T) : ‖Z s‖ ≤ L * ‖Z 0‖ :=
    exitTail_variation_bound hT hα hb hA hY hreg le_rfl hs.1 hs.2
      (fun r hr => hZ r ⟨hr.1, hr.2.trans hs.2⟩)
  have HP (s : ℝ) (hs : s ∈ Icc 0 T) :
      ‖fderiv ℝ (fderiv ℝ (exitTailField (Real.exp (-s)))) (Y s) (X s) (Z s)‖ ≤
        C * L ^ 2 * ‖X 0‖ * ‖Z 0‖ := by
    have hv : 0 ≤ Real.exp (-s) ∧ Real.exp (-s) ≤ 1 :=
      ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.1)⟩
    have H := HC (Real.exp (-s)) (Y s) (X s) (Z s)
      (hreg s hs).1 (hreg s hs).2.1 hv (hreg s hs).2.2.1
    apply H.trans
    calc
      C * ‖X s‖ * ‖Z s‖ ≤ C * (L * ‖X 0‖) * (L * ‖Z 0‖) := by
        gcongr
        · exact HX s hs
        · exact HZ s hs
      _ = _ := by ring
  have H := exitTail_forced_variation_bound hT hα hb hA hY hreg le_rfl hT le_rfl hQ
    (R := fun _ => C * L ^ 2 * ‖X 0‖ * ‖Z 0‖) continuousOn_const HP
  simp only [hQ0, norm_zero, zero_add, intervalIntegral.integral_const, sub_zero,
    smul_eq_mul] at H
  apply H.trans_eq
  have hpow : L * L ^ 2 = Real.exp (9 * B) := by
    dsimp only [L]
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  change L * (T * (C * L ^ 2 * ‖X 0‖ * ‖Z 0‖)) = _
  calc
    _ = C * (L * L ^ 2) * T * ‖X 0‖ * ‖Z 0‖ := by ring
    _ = _ := by rw [hpow]

end BianchiIX
