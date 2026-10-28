import BianchiIX.Literature
import BianchiIX.Statistics.GaussErgodic
import BianchiIX.Statistics.CommonTypical
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Concrete cylinder statistics, conditional only on the stated pointwise ergodic theorem. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace BianchiIX

noncomputable section

def gaussCylinderObservable (w : List ℕ) : ℝ → ℝ :=
  (gaussCylinder w).indicator (fun _ => 1)

def gaussCylinderTypicalSet : Set ℝ :=
  commonTypicalSet gaussMap gaussCylinderObservable
    (fun w => (gaussMeasure (gaussCylinder w)).toReal)

theorem measurable_gaussCylinderObservable (w : List ℕ) : Measurable (gaussCylinderObservable w) :=
  measurable_const.indicator (measurableSet_gaussCylinder w)

theorem gaussCylinderObservable_bounded (w : List ℕ) :
    Bornology.IsBounded (range (gaussCylinderObservable w)) := by
  apply (isCompact_Icc (a := (0 : ℝ)) (b := 1)).isBounded.subset
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ gaussCylinder w <;> simp [gaussCylinderObservable, hx]

theorem integrable_gaussCylinderObservable (w : List ℕ) :
    Integrable (gaussCylinderObservable w) gaussMeasure :=
  (integrable_const (1 : ℝ)).indicator (measurableSet_gaussCylinder w)

theorem integral_gaussCylinderObservable (w : List ℕ) :
    (∫ x, gaussCylinderObservable w x ∂gaussMeasure) = (gaussMeasure (gaussCylinder w)).toReal :=
  integral_indicator_one (measurableSet_gaussCylinder w)

theorem gaussCylinderTypicalSet_measurable : MeasurableSet gaussCylinderTypicalSet :=
  commonTypicalSet_measurable _ measurable_gaussMap measurable_gaussCylinderObservable

theorem gaussCylinderTypicalSet_preimage : gaussMap ⁻¹' gaussCylinderTypicalSet = gaussCylinderTypicalSet :=
  commonTypicalSet_preimage _ _ _ gaussCylinderObservable_bounded

theorem ae_gaussCylinderTypicalSet (hB : Literature.BirkhoffErgodicInput ℝ) :
    ∀ᵐ x ∂gaussMeasure, x ∈ gaussCylinderTypicalSet := by
  apply ae_mem_commonTypicalSet
  intro w
  have h := hB gaussMeasure inferInstance gaussMap ergodic_gaussMap
    (gaussCylinderObservable w) (integrable_gaussCylinderObservable w)
  simpa only [integral_gaussCylinderObservable] using h

theorem ae_volume_gaussCylinderTypicalSet (hB : Literature.BirkhoffErgodicInput ℝ) :
    ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) 1), x ∈ gaussCylinderTypicalSet :=
  volume_restrict_absolutelyContinuous_gaussMeasure.ae_le (ae_gaussCylinderTypicalSet hB)

theorem gaussCylinder_average_of_typical {x : ℝ} (hx : x ∈ gaussCylinderTypicalSet) (w : List ℕ) :
    Tendsto (fun n => birkhoffAverage ℝ gaussMap (gaussCylinderObservable w) n x)
      atTop (𝓝 (gaussMeasure (gaussCylinder w)).toReal) := hx w

theorem gaussCylinderObservable_code (a : ℕ → ℕ+) (w : List ℕ) (hw : ∀ k ∈ w, 1 ≤ k) :
    gaussCylinderObservable w (gaussCode a) = if digitPrefix a w.length = w then 1 else 0 := by
  by_cases h : digitPrefix a w.length = w
  · have hc := (gaussCode_mem_cylinder_iff a w hw).mpr h
    simp [gaussCylinderObservable, hc, h]
  · have hc : gaussCode a ∉ gaussCylinder w :=
      fun hc => h ((gaussCode_mem_cylinder_iff a w hw).mp hc)
    simp [gaussCylinderObservable, hc, h]

theorem gauss_digit_block_frequency (a : ℕ → ℕ+) (ha : gaussCode a ∈ gaussCylinderTypicalSet)
    (w : List ℕ) (hw : ∀ k ∈ w, 1 ≤ k) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n,
      if digitPrefix (shiftDigits a j) w.length = w then (1 : ℝ) else 0)
      atTop (𝓝 (gaussMeasure (gaussCylinder w)).toReal) := by
  have h := gaussCylinder_average_of_typical ha w
  change Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n,
    gaussCylinderObservable w (gaussMap^[j] (gaussCode a))) atTop _ at h
  simpa only [gaussMap_iterate_code, gaussCylinderObservable_code _ w hw] using h

namespace InverseBranchTree.BranchEstimates

theorem ae_code_gaussCylinderTypical {T : InverseBranchTree} {d e : ℕ → ℝ}
    (E : T.BranchEstimates d e) (hB : Literature.BirkhoffErgodicInput ℝ) {L : ℝ}
    (hbudget : ∀ n, (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤ L) :
    ∀ᵐ x ∂(volume.comap (Subtype.val : T.survivors → ℝ)), T.code x ∈ gaussCylinderTypicalSet :=
  E.ae_code_property_on_unit hbudget (ae_volume_gaussCylinderTypicalSet hB)

theorem ae_digit_block_frequency {T : InverseBranchTree} {d e : ℕ → ℝ}
    (E : T.BranchEstimates d e) (hB : Literature.BirkhoffErgodicInput ℝ) {L : ℝ}
    (hbudget : ∀ n, (∑ j ∈ Finset.range n, (e j + if j = 0 then 0 else 2 * d j)) ≤ L) :
    ∀ᵐ x ∂(volume.comap (Subtype.val : T.survivors → ℝ)), ∀ w : List ℕ,
      (∀ k ∈ w, 1 ≤ k) →
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n,
        if digitPrefix (shiftDigits (T.digits x) j) w.length = w then (1 : ℝ) else 0)
        atTop (𝓝 (gaussMeasure (gaussCylinder w)).toReal) := by
  filter_upwards [E.ae_code_gaussCylinderTypical hB hbudget] with x hx
  exact fun w hw => gauss_digit_block_frequency (T.digits x) hx w hw

end InverseBranchTree.BranchEstimates
end
end BianchiIX
