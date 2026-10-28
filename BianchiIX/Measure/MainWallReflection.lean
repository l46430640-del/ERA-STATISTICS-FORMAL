import BianchiIX.Dynamics.MainWallReflection
import BianchiIX.Measure.MainWallMeasure

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

theorem measurableSet_mainWallReflection_image {A : Set SectionCoordinates} (hA : MeasurableSet A) :
    MeasurableSet (mainWallReflection '' A) :=
  hA.image_of_continuousOn_injOn mainWallReflectionEquiv.continuous.continuousOn
    mainWallReflectionEquiv.injective.injOn

/-- Axis exchange preserves the corrected section measure, including its domain restriction. -/
theorem mainWallMeasure_reflection {h : ℝ} {A : Set SectionCoordinates} (hA : MeasurableSet A) :
    mainWallMeasure h (mainWallReflection '' A) = mainWallMeasure h A := by
  let D := mainWallChartDomain h
  have hD : MeasurableSet D := (isOpen_mainWallChartDomain h).measurableSet
  have hI : mainWallReflection '' (A ∩ D) = mainWallReflection '' A ∩ D := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hd⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, by simpa only [D, mainWallChartDomain, mem_ofPred_eq, mainWallRadicand_reflection] using hd⟩
    · rintro ⟨⟨x, hx, rfl⟩, hd⟩
      exact ⟨x, ⟨hx, by simpa only [D, mainWallChartDomain, mem_ofPred_eq, mainWallRadicand_reflection] using hd⟩, rfl⟩
  have H (B : Set SectionCoordinates) (hB : MeasurableSet B) :
      mainWallMeasure h B = ∫⁻ y in B ∩ D, ENNReal.ofReal (mainWallChartDensity h y) := by
    rw [mainWallMeasure, withDensity_apply _ hB, Measure.restrict_restrict hB]
  rw [H _ (measurableSet_mainWallReflection_image hA), H _ hA, ← hI]
  have hf (y : SectionCoordinates) : HasFDerivAt mainWallReflection
      mainWallReflectionEquiv.toContinuousLinearMap y := mainWallReflectionEquiv.hasFDerivAt
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hA.inter hD)
    (fun y _ => (hf y).hasFDerivWithinAt) mainWallReflectionEquiv.injective.injOn]
  have hdet : mainWallReflectionEquiv.toContinuousLinearMap.det = 1 := mainWallReflection_det
  simp only [hdet, abs_one, ENNReal.ofReal_one,
    mainWallChartDensity_reflection, one_mul]

def mainWallSymmetrization (A : Set SectionCoordinates) : Set SectionCoordinates :=
  A ∪ mainWallReflection '' A

theorem measurableSet_mainWallSymmetrization {A : Set SectionCoordinates} (hA : MeasurableSet A) :
    MeasurableSet (mainWallSymmetrization A) := hA.union (measurableSet_mainWallReflection_image hA)

theorem mainWallMeasure_symmetrization_le {h : ℝ} {A : Set SectionCoordinates} (hA : MeasurableSet A) :
    mainWallMeasure h (mainWallSymmetrization A) ≤ 2 * mainWallMeasure h A := by
  exact (measure_union_le A (mainWallReflection '' A)).trans_eq (by rw [mainWallMeasure_reflection hA, two_mul])

theorem mainWallReflection_mem_symmetrization_iff {A : Set SectionCoordinates} {y : SectionCoordinates} :
    mainWallReflection y ∈ mainWallSymmetrization A ↔ y ∈ mainWallSymmetrization A := by
  change (mainWallReflection y ∈ A ∨ mainWallReflection y ∈ mainWallReflection '' A) ↔
    (y ∈ A ∨ y ∈ mainWallReflection '' A)
  constructor
  · rintro (h | ⟨z, hz, heq⟩)
    · exact Or.inr ⟨mainWallReflection y, h, mainWallReflection_twice y⟩
    · exact Or.inl ((mainWallReflectionEquiv.injective heq) ▸ hz)
  · rintro (h | ⟨z, hz, rfl⟩)
    · exact Or.inr ⟨y, h, rfl⟩
    · exact Or.inl (by simpa only [mainWallReflection_twice] using hz)

end BianchiIX
