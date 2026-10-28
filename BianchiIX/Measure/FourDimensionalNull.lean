import BianchiIX.Measure.RegularLevelNull
import BianchiIX.Dynamics.Normalized
import Mathlib.MeasureTheory.Constructions.Pi

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped Topology ENNReal

abbrev FourCoordinates := Fin 4 → ℝ

/-- Nullity after every differentiable four-dimensional coordinate observation. -/
def NullInFourCoordinates (S : Set NormalizedState) : Prop :=
  ∀ P : NormalizedState → FourCoordinates, Differentiable ℝ P → volume (P '' S) = 0

theorem NullInFourCoordinates.mono {S T : Set NormalizedState}
    (H : NullInFourCoordinates T) (hST : S ⊆ T) : NullInFourCoordinates S :=
  fun P hP => measure_mono_null (image_mono hST) (H P hP)

theorem NullInFourCoordinates.iUnion {ι : Type*} [Countable ι]
    {S : ι → Set NormalizedState} (H : ∀ i, NullInFourCoordinates (S i)) :
    NullInFourCoordinates (⋃ i, S i) := by
  intro P hP
  rw [image_iUnion]
  exact measure_iUnion_null fun i => H i P hP

theorem NullInFourCoordinates.union {S T : Set NormalizedState}
    (HS : NullInFourCoordinates S) (HT : NullInFourCoordinates T) :
    NullInFourCoordinates (S ∪ T) := by
  intro P hP
  rw [image_union]
  exact measure_union_null (HS P hP) (HT P hP)

/-- Every regular four-dimensional chart pulls back a coordinate-null set to a null set. -/
theorem NullInFourCoordinates.preimage {S : Set NormalizedState} (H : NullInFourCoordinates S)
    {C : FourCoordinates → NormalizedState} {U : Set FourCoordinates}
    (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hinj : ∀ y ∈ U, Function.Injective (fderiv ℝ C y)) :
    volume (U ∩ C ⁻¹' S) = 0 := by
  apply volume_eq_zero_of_local_null
  intro y hy
  obtain ⟨A, hA⟩ := (fderiv ℝ C y).toLinearMap.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (hinj y hy.1))
  let P : NormalizedState →L[ℝ] FourCoordinates := A.toContinuousLinearMap
  have hcomp : P.comp (fderiv ℝ C y) = ContinuousLinearMap.id ℝ FourCoordinates := by
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun L : FourCoordinates →ₗ[ℝ] FourCoordinates => L v) hA
  have hderiv : HasFDerivAt (fun z => P (C z)) (ContinuousLinearMap.id ℝ FourCoordinates) y := by
    have hd := P.hasFDerivAt.comp y ((hC y hy.1).differentiableAt (by norm_num)).hasFDerivAt
    rwa [hcomp] at hd
  have hsmooth := P.contDiff.contDiffAt.comp y (hC y hy.1)
  have hdet : (fderiv ℝ (fun z => P (C z)) y).det ≠ 0 := by
    rw [hderiv.fderiv]
    change LinearMap.det (LinearMap.id : FourCoordinates →ₗ[ℝ] FourCoordinates) ≠ 0
    rw [LinearMap.det_id]
    exact one_ne_zero
  obtain ⟨V, hVo, hyV, hV⟩ := exists_local_null_preimage hsmooth hdet
  refine ⟨V, hVo, hyV, measure_mono_null ?_ (hV (P '' S) (H P P.differentiable))⟩
  intro z hz
  exact ⟨hz.2, mem_image_of_mem P hz.1.2⟩

theorem NullInFourCoordinates.ae_not_mem {S : Set NormalizedState} (H : NullInFourCoordinates S)
    {C : FourCoordinates → NormalizedState} {U : Set FourCoordinates}
    (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hinj : ∀ y ∈ U, Function.Injective (fderiv ℝ C y)) (ρ : FourCoordinates → ℝ≥0∞) :
    ∀ᵐ y ∂volume.withDensity ρ, y ∈ U → C y ∉ S := by
  rw [ae_iff]
  have heq : {y | ¬(y ∈ U → C y ∉ S)} = U ∩ C ⁻¹' S := by
    ext y; simp
  rw [heq]
  exact withDensity_absolutelyContinuous volume ρ (H.preimage hC hinj)

theorem volume_tail_preimage_null {Z : Set (Fin 3 → ℝ)} (hZ : volume Z = 0) :
    volume {p : FourCoordinates | Fin.tail p ∈ Z} = 0 := by
  have hn : volume ((univ : Set ℝ) ×ˢ Z) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, hZ, mul_zero]
  have H := (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).quasiMeasurePreserving.preimage_null hn
  have heq : {p : FourCoordinates | Fin.tail p ∈ Z} =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0) ⁻¹' ((univ : Set ℝ) ×ˢ Z) := by
    ext p
    simp [MeasurableEquiv.piFinSuccAbove]
  rw [heq]
  exact H

theorem volume_first_coordinate_zero : volume {p : FourCoordinates | p 0 = 0} = 0 := by
  have hn : volume (({0} : Set ℝ) ×ˢ (univ : Set (Fin 3 → ℝ))) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, zero_mul]
  have H := (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).quasiMeasurePreserving.preimage_null hn
  have heq : {p : FourCoordinates | p 0 = 0} =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0) ⁻¹'
        (({0} : Set ℝ) ×ˢ (univ : Set (Fin 3 → ℝ))) := by
    ext p
    simp [MeasurableEquiv.piFinSuccAbove]
  rw [heq]
  exact H

end BianchiIX
