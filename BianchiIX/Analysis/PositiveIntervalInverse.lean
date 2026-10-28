import BianchiIX.Analysis.IntervalRadiusInverse

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- One inverse on the whole image agrees with the ordinary local inverse at every interior point. -/
theorem intervalRadiusInverse_positive_control {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 f x)
    (hd : ∀ x ∈ Icc a b, 0 < deriv f x) :
    let g := intervalRadiusInverse f a b
    StrictMonoOn f (Icc a b) ∧ f '' Icc a b = Icc (f a) (f b) ∧
      LeftInvOn g f (Icc a b) ∧ MapsTo g (Icc (f a) (f b)) (Icc a b) ∧
      RightInvOn g f (Icc (f a) (f b)) ∧
      ∀ y ∈ Ioo (f a) (f b), g y ∈ Ioo a b ∧ ContDiffAt ℝ 1 g y ∧
        HasDerivAt g (deriv f (g y))⁻¹ y := by
  intro g
  have hc : ContinuousOn f (Icc a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hmono := strictMonoOn_of_deriv_pos (convex_Icc a b) hc
    (fun x hx => hd x (interior_subset hx))
  have himage := hc.image_Icc_of_monotoneOn hab.le hmono.monotoneOn
  have hleft : LeftInvOn g f (Icc a b) := hmono.injOn.leftInvOn_invFunOn
  have honto : SurjOn f (Icc a b) (Icc (f a) (f b)) := by
    rw [← himage]
    exact surjOn_image f (Icc a b)
  have hmaps : MapsTo g (Icc (f a) (f b)) (Icc a b) := honto.mapsTo_invFunOn
  have hright : RightInvOn g f (Icc (f a) (f b)) := honto.rightInvOn_invFunOn
  refine ⟨hmono, himage, hleft, hmaps, hright, ?_⟩
  intro y hy
  have hyc : y ∈ Icc (f a) (f b) := ⟨hy.1.le, hy.2.le⟩
  have hx := hmaps hyc
  have hxy := hright hyc
  have hxi : g y ∈ Ioo a b := by
    refine ⟨lt_of_le_of_ne hx.1 ?_, lt_of_le_of_ne hx.2 ?_⟩
    · intro heq
      have : f a = y := by simpa only [← heq] using hxy
      exact (ne_of_lt hy.1) this
    · intro heq
      have : f b = y := by simpa only [heq] using hxy
      exact (ne_of_lt hy.2) this.symm
  obtain ⟨j, hj⟩ := exists_scalarLocalInverseAt (hf (g y) hx) (hd (g y) hx).ne'
  have hjlim : Tendsto j (𝓝 (f (g y))) (𝓝 (g y)) := by
    simpa only [ContinuousAt, hj.apply_base] using hj.contDiffAt.continuousAt
  have hjnear : ∀ᶠ z in 𝓝 y, j z ∈ Ioo a b := by
    simpa only [hxy, mem_Ioo] using hjlim.eventually (Ioo_mem_nhds hxi.1 hxi.2)
  have hjright : ∀ᶠ z in 𝓝 y, f (j z) = z := by
    simpa only [hxy] using hj.right_inverse
  have heq : g =ᶠ[𝓝 y] j := by
    filter_upwards [Ioo_mem_nhds hy.1 hy.2, hjnear, hjright] with z hz hjz hrightz
    have hzc : z ∈ Icc (f a) (f b) := ⟨hz.1.le, hz.2.le⟩
    exact hmono.injOn (hmaps hzc) ⟨hjz.1.le, hjz.2.le⟩
      ((hright hzc).trans hrightz.symm)
  refine ⟨hxi, ?_, ?_⟩
  · exact (hxy ▸ hj.contDiffAt).congr_of_eventuallyEq heq
  · exact (hxy ▸ hj.hasDerivAt).congr_of_eventuallyEq heq

end BianchiIX
