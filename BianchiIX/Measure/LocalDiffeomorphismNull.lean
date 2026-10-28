import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.Compactness.Lindelof

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

/-- A nonsingular smooth map pulls back every outer-null set on one common neighborhood. -/
theorem exists_local_null_preimage {n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)} {x : Fin n → ℝ}
    (hf : ContDiffAt ℝ 1 f x) (hdet : (fderiv ℝ f x).det ≠ 0) :
    ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x ∈ U ∧
      ∀ Z : Set (Fin n → ℝ), volume Z = 0 → volume (U ∩ f ⁻¹' Z) = 0 := by
  let L := (fderiv ℝ f x).toContinuousLinearEquivOfDetNeZero hdet
  have hd : HasFDerivAt f (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) x := by
    rw [show (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) = fderiv ℝ f x from
      ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _]
    exact (hf.differentiableAt (by norm_num)).hasFDerivAt
  let g := hf.localInverse hd (by norm_num)
  have hg : ContDiffAt ℝ 1 g (f x) := hf.to_localInverse hd (by norm_num)
  have hleft : ∀ᶠ y in 𝓝 x, g (f y) = y := (hf.hasStrictFDerivAt' hd (by norm_num)).eventually_left_inverse
  obtain ⟨V, hV, hVo, hxV⟩ := mem_nhds_iff.mp (hg.eventually (by norm_num))
  obtain ⟨U, hU, hUo, hxU⟩ := mem_nhds_iff.mp
    ((hf.continuousAt.eventually (hVo.mem_nhds hxV)).and hleft)
  refine ⟨U, hUo, hxU, fun Z hZ => ?_⟩
  have hnull : volume (g '' (Z ∩ V)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (fun z hz => ((show ContDiffAt ℝ 1 g z from hV hz.2).differentiableAt
        (by norm_num)).differentiableWithinAt)
      (measure_mono_null inter_subset_left hZ)
  apply measure_mono_null _ hnull
  intro y hy
  exact ⟨f y, ⟨hy.2, (hU hy.1).1⟩, (hU hy.1).2⟩

/-- Local null projections cover a relation by countably many patches, allowing all event times. -/
theorem volume_fst_image_eq_zero_of_local_null {n : ℕ} {S : Set ((Fin n → ℝ) × ℝ)}
    (H : ∀ p ∈ S, ∃ V : Set ((Fin n → ℝ) × ℝ), IsOpen V ∧ p ∈ V ∧
      ∃ Z : Set (Fin n → ℝ), volume Z = 0 ∧ ∀ q ∈ S ∩ V, q.1 ∈ Z) :
    volume (Prod.fst '' S) = 0 := by
  classical
  by_cases hS : S.Nonempty
  · let : Nonempty S := hS.to_subtype
    choose V hVo hpV Z hZ hcover using (fun p : S => H p.val p.property)
    obtain ⟨f, hf⟩ := (HereditarilyLindelofSpace.isLindelof S).indexed_countable_subcover V hVo
      (fun p hp => mem_iUnion.mpr ⟨⟨p, hp⟩, hpV ⟨p, hp⟩⟩)
    apply measure_mono_null (t := ⋃ m : ℕ, Z (f m)) _ (measure_iUnion_null fun m => hZ (f m))
    rintro y ⟨p, hp, rfl⟩
    obtain ⟨m, hm⟩ := mem_iUnion.mp (hf hp)
    exact mem_iUnion.mpr ⟨m, hcover (f m) p ⟨hp, hm⟩⟩
  · simp only [Set.not_nonempty_iff_eq_empty.mp hS, image_empty, measure_empty]

end BianchiIX
