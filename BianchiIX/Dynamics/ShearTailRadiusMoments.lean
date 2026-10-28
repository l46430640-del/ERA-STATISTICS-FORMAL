import BianchiIX.Dynamics.ShearTailRadius

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- Radius-energy moments follow from the existing energy moments and one dissipative strong wall. -/
theorem shearTail_prefix_radius_moments {a T : ℝ} {α : ℝ → NormalizedState}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hT : 0 ≤ T)
    (hα : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt α (normalizedField (α t)) t)
    (hc : ∀ t ∈ Icc (0 : ℝ) T, stateConstraint (α t) = 1)
    (hn : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ α t 2 ∧ 0 ≤ α t 3 ∧ 0 ≤ α t 4)
    (hr : ∀ t ∈ Icc (0 : ℝ) T, shearTailRegion a (α t)) :
    (∫ t in 0..T, shearTailRadiusEnergy (α t)) ≤
      (∫ t in 0..T, shearTailEnergy (α t)) + α 0 2 / 2 ∧
    (∫ t in 0..T, t * shearTailRadiusEnergy (α t)) ≤
      (∫ t in 0..T, t * shearTailEnergy (α t)) + α 0 2 / 4 := by
  have HD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) := (hasDerivAt_normalized_components (hα t ht)).2.2.1
  have Hdec (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      rateOne (α t 0) (α t 1) * α t 2 ≤ -2 * α t 2 := by
    obtain ⟨hp, hsl, hsu, hN, hX, hY⟩ := hr t ht
    have H := (shearTail_wall_rates ha (by linarith only [hp]) ⟨hsl, hsu⟩
      ⟨(hn t ht).1, hN⟩ ⟨(hn t ht).2.1, hX⟩ ⟨(hn t ht).2.2, hY⟩ (hc t ht)).1
    exact mul_le_mul_of_nonneg_right H (hn t ht).1
  have HN := integral_moments_le_of_linear_dissipation hT (by norm_num : (0 : ℝ) < 2)
    HD Hdec (hn T ⟨hT, le_rfl⟩).1
  norm_num only [sub_zero, show (2 : ℝ) ^ 2 = 4 by norm_num] at HN
  have Hα := HasDerivAt.continuousOn hα
  have HE : ContinuousOn (fun t => shearTailRadiusEnergy (α t)) (Icc (0 : ℝ) T) := by
    unfold shearTailRadiusEnergy
    fun_prop
  have HB : ContinuousOn (fun t => shearTailEnergy (α t)) (Icc (0 : ℝ) T) := by
    unfold shearTailEnergy
    fun_prop
  have Hn : ContinuousOn (fun t => α t 2) (Icc (0 : ℝ) T) := HasDerivAt.continuousOn HD
  have Hpoint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      shearTailRadiusEnergy (α t) ≤ shearTailEnergy (α t) + α t 2 := by
    dsimp only [shearTailRadiusEnergy, shearTailEnergy]
    nlinarith only [sq_nonneg (α t 2), mul_nonneg (hn t ht).1 (add_nonneg (hn t ht).2.1 (hn t ht).2.2)]
  constructor
  · have H := intervalIntegral.integral_mono_on (μ := volume) hT
      (HE.intervalIntegrable_of_Icc hT) ((HB.add Hn).intervalIntegrable_of_Icc hT) Hpoint
    simp only [Pi.add_apply] at H
    rw [intervalIntegral.integral_add (HB.intervalIntegrable_of_Icc hT) (Hn.intervalIntegrable_of_Icc hT)] at H
    linarith only [H, HN.1]
  · have H := intervalIntegral.integral_mono_on (μ := volume) hT
      ((continuousOn_id.mul HE).intervalIntegrable_of_Icc hT)
      (((continuousOn_id.mul HB).add (continuousOn_id.mul Hn)).intervalIntegrable_of_Icc hT)
      (fun t ht => show t * shearTailRadiusEnergy (α t) ≤ t * shearTailEnergy (α t) + t * α t 2 by
        nlinarith only [mul_le_mul_of_nonneg_left (Hpoint t ht) ht.1])
    simp only [Pi.add_apply, Pi.mul_apply, id_eq] at H
    rw [intervalIntegral.integral_add (f := fun t => t * shearTailEnergy (α t)) (g := fun t => t * α t 2)
      ((continuousOn_id.mul HB).intervalIntegrable_of_Icc hT)
      ((continuousOn_id.mul Hn).intervalIntegrable_of_Icc hT)] at H
    linarith only [H, HN.2]

end BianchiIX
