import BianchiIX.Analysis.IntegralLinearGrowth
import BianchiIX.Dynamics.ExitTailJacobianBudget

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def exitTailVariationBudget (α b A D T : ℝ) : ℝ :=
  2 * exitTailRateBudget α b A D T + 2048 * (1 + A * b * T)

theorem exitTail_jacobian_subinterval_bound {Y : ℝ → ExitTailState} {T α b A D a t : ℝ}
    (hT : 0 ≤ T) (hα : 0 ≤ α) (hb : 0 ≤ b) (hA : 0 ≤ A)
    (hY : ContinuousOn Y (Icc 0 T))
    (hreg : ∀ s ∈ Icc 0 T, exitTailRegion α b A D (Y s))
    (ha : 0 ≤ a) (hat : a ≤ t) (ht : t ≤ T) :
    (∫ s in a..t, ‖fderiv ℝ (exitTailField (Real.exp (-s))) (Y s)‖) ≤
      exitTailVariationBudget α b A D T := by
  have hc := (continuousOn_exitTail_stateDerivative hY hreg).norm
  apply le_trans (intervalIntegral.integral_mono_interval ha hat ht
    (Filter.Eventually.of_forall (fun s => norm_nonneg _)) (hc.intervalIntegrable_of_Icc hT))
  exact exitTail_jacobian_integral_bound hT hα hb hA hY hreg

/-- Forced variations can start anywhere in the controlled tail, with the same total budget. -/
theorem exitTail_forced_variation_bound {Y X P : ℝ → ExitTailState} {R : ℝ → ℝ}
    {T α b A D a t : ℝ} (hT : 0 ≤ T) (hα : 0 ≤ α) (hb : 0 ≤ b) (hA : 0 ≤ A)
    (hY : ContinuousOn Y (Icc 0 T))
    (hreg : ∀ s ∈ Icc 0 T, exitTailRegion α b A D (Y s))
    (ha : 0 ≤ a) (hat : a ≤ t) (ht : t ≤ T)
    (hX : ∀ s ∈ Icc a t, HasDerivAt X
      (fderiv ℝ (exitTailField (Real.exp (-s))) (Y s) (X s) + P s) s)
    (hR : ContinuousOn R (Icc a t)) (hP : ∀ s ∈ Icc a t, ‖P s‖ ≤ R s) :
    ‖X t‖ ≤ Real.exp (3 * exitTailVariationBudget α b A D T) *
      (‖X a‖ + ∫ s in a..t, R s) := by
  have hsub : Icc a t ⊆ Icc 0 T := fun _ hs => ⟨ha.trans hs.1, hs.2.trans ht⟩
  have H := norm_le_exp_integral_of_forced_linear hat hX
    ((continuousOn_exitTail_stateDerivative hY hreg).mono hsub) hR hP
  have HB := exitTail_jacobian_subinterval_bound hT hα hb hA hY hreg ha hat ht
  have hRn : 0 ≤ ∫ s in a..t, R s := intervalIntegral.integral_nonneg hat
    (fun s hs => (norm_nonneg _).trans (hP s hs))
  apply H.trans
  apply mul_le_mul_of_nonneg_right _ (add_nonneg (norm_nonneg _) hRn)
  apply Real.exp_le_exp.mpr
  simpa using mul_le_mul_of_nonneg_left HB (by norm_num : (0 : ℝ) ≤ 3)

theorem exitTail_variation_bound {Y X : ℝ → ExitTailState}
    {T α b A D a t : ℝ} (hT : 0 ≤ T) (hα : 0 ≤ α) (hb : 0 ≤ b) (hA : 0 ≤ A)
    (hY : ContinuousOn Y (Icc 0 T))
    (hreg : ∀ s ∈ Icc 0 T, exitTailRegion α b A D (Y s))
    (ha : 0 ≤ a) (hat : a ≤ t) (ht : t ≤ T)
    (hX : ∀ s ∈ Icc a t, HasDerivAt X
      (fderiv ℝ (exitTailField (Real.exp (-s))) (Y s) (X s)) s) :
    ‖X t‖ ≤ Real.exp (3 * exitTailVariationBudget α b A D T) * ‖X a‖ := by
  simpa using exitTail_forced_variation_bound hT hα hb hA hY hreg ha hat ht
    (P := fun _ => 0) (R := fun _ => 0) (fun s hs => by simpa using hX s hs)
    continuousOn_const (fun _ _ => by simp)

end BianchiIX
