import BianchiIX.Measure.GlobalSuccess
import BianchiIX.Measure.AxisSaturatedException
import BianchiIX.Measure.GeometricException
import BianchiIX.Measure.GeometricVolumeNull

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology ENNReal

theorem globalAxisWallHittingDomain_of_forward {ι : Type*} (A : ι → NormalizedSymmetry)
    {h : ι → ℝ} {B : ι → Set SectionCoordinates} {x : NormalizedState} {s : ℝ}
    (hs : 0 ≤ s) (hdom : s ∈ normalizedMaxDomain x 0)
    (H : normalizedMaxCurve x 0 s ∈ globalAxisWallHittingDomain A h B (Ici 0)) :
    x ∈ globalAxisWallHittingDomain A h B (Ici 0) := by
  obtain ⟨t, ht, htdom, i, y, hy, heq⟩ := H
  have Hflow := normalizedMaxCurve_restart (t := t + s) hdom (by simpa using htdom)
  simp only [add_sub_cancel_right] at Hflow
  exact ⟨t + s, add_nonneg ht hs, Hflow.1, i, y, hy, heq.trans Hflow.2.symm⟩

theorem ae_primaryAxis_success_of_decay
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) {h d : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 1 / 16) (hd : 0 < d) (hdh : d < h / 8)
    {F : Set (Fin 3 × SectionCoordinates)} (hF : MeasurableSet F)
    (hfinite : axisFamilyMeasure (fun _ : Fin 3 => h) F ≠ ⊤) :
    let E := fun _ : Fin 3 => mainWallSmallSection d ∩ mainWallChartDomain h
    ∀ᵐ z ∂axisFamilyMeasure (fun _ : Fin 3 => h), z ∈ axisFamilySection E →
      WallProductDecay (axisFamilyChart primaryAxisFrame (fun _ => h) z) →
        axisFamilyChart primaryAxisFrame (fun _ => h) z ∈
          globalAxisWallHittingDomain primaryAxisFrame (fun _ => h)
            (axisFamilySuccessTargets E F) (Ici 0) := by
  intro E
  have hh1 : h ≤ 1 / 8 := hhmax.trans (by norm_num)
  have hd1 : d ≤ 1 / 8 := hdh.le.trans (by linarith only [hh1])
  have hE : ∀ i, MeasurableSet (E i) := fun _ =>
    (measurableSet_mainWallSmallSection d).inter (isOpen_mainWallChartDomain h).measurableSet
  have hsmall (i : Fin 3) (y : SectionCoordinates) (hy : y ∈ E i) :
      y ∈ mainWallChartDomain h ∧ |y 0| ≤ 1 / 8 ∧
        Real.exp (-y 1) ≤ h / 8 ∧ Real.exp (-y 2) ≤ h / 8 :=
    ⟨hy.2, hy.1.1.trans hd1, (le_max_left _ _).trans (hy.1.2.trans hdh.le),
      (le_max_right _ _).trans (hy.1.2.trans hdh.le)⟩
  filter_upwards [ae_smallAxis_success_hitting hh hh1 hE hsmall hF hfinite,
    ae_primaryAxis_infiniteReturns_of_decay hBirkhoff hh hhmax hd hdh] with z hcap hrec hz hprod
  exact hcap (hrec hz hprod)

/-- The fixed success target is reached outside one invariant exception, null in both physical dimensions. -/
theorem exists_common_borel_success_exception
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    (hBrehm : Literature.BrehmIXAttractorInput) {h d : ℝ}
    (hh : 0 < h) (hhmax : h ≤ 1 / 16) (hd : 0 < d) (hdh : d < h / 8)
    {F : Set (Fin 3 × SectionCoordinates)} (hF : MeasurableSet F)
    (hfinite : axisFamilyMeasure (fun _ : Fin 3 => h) F ≠ ⊤) :
    let E := fun _ : Fin 3 => mainWallSmallSection d ∩ mainWallChartDomain h
    ∃ N : Set NormalizedState, MeasurableSet N ∧ N ⊆ physicalPhaseSpace ∧
      geometricException ⊆ N ∧
      (∀ x : NormalizedState, ∀ t ∈ normalizedMaxDomain x 0,
        normalizedMaxCurve x 0 t ∈ N ↔ x ∈ N) ∧
      (∀ (C : SectionCoordinates → NormalizedState) (U : Set SectionCoordinates),
        IsOpen U → (∀ y ∈ U, ContDiffAt ℝ 1 C y) →
        (∀ y ∈ U, positiveWalls (C y)) → (∀ y ∈ U, stateConstraint (C y) = 1) →
        (∀ y ∈ U, normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) →
        volume (U ∩ C ⁻¹' N) = 0) ∧ NullInFourCoordinates N ∧
      ∀ x ∈ physicalPhaseSpace, x ∉ N →
        x ∈ globalAxisWallHittingDomain primaryAxisFrame (fun _ => h)
          (axisFamilySuccessTargets E F) (Ici 0) := by
  intro E
  obtain ⟨S, hSm, hSp, hSi, hSn, hSfour, hsuccess⟩ := exists_primaryAxis_saturated_null_exception hh
    (fun _ => (measurableSet_mainWallSmallSection d).inter (isOpen_mainWallChartDomain h).measurableSet)
    (fun _ _ hz => hz.2) (ae_primaryAxis_success_of_decay hBirkhoff hh hhmax hd hdh hF hfinite)
  let N := S ∪ geometricException
  refine ⟨N, hSm.union measurableSet_geometricException, ?_, subset_union_right, ?_, ?_,
    hSfour.union (nullInFourCoordinates_geometricException hBirkhoff hBrehm), ?_⟩
  · intro x hx
    exact hx.elim (hSp x) And.left
  · intro x t ht
    simp only [N, mem_union, hSi x t ht, mem_geometricException_maxCurve_iff ht]
  · intro C U hU hC hp hc hflux
    have heq : U ∩ C ⁻¹' N = (U ∩ C ⁻¹' S) ∪ (U ∩ C ⁻¹' geometricException) := by
      ext y; simp [N, and_or_left]
    rw [heq]
    exact measure_union_null (hSn C U hU hC hp hc hflux)
      (volume_preimage_geometricException hBirkhoff hBrehm hU hC hp hc hflux)
  · intro x hx hn
    have hns : x ∉ S := fun hS => hn (Or.inl hS)
    have hng : x ∉ geometricException := fun hG => hn (Or.inr hG)
    have hT : x ∉ taubSubspaces := fun hT => hng ⟨hx, Or.inl hT⟩
    have hprod := hBrehm.wallProductDecay hx hT
    obtain ⟨hr, hvisit⟩ := arbitrarily_late_taub_approach_of_not_mem_geometricException hx hng
    obtain ⟨i, hi⟩ := exists_arbitrarily_late_primaryAxis_crossing hx.2 hx.1 hr hh hhmax hd hdh hprod hvisit
    obtain ⟨t, ht, hdom, y, hy, heq, hs, hb, hw, _⟩ := hi 0 1 (by norm_num)
    have hys : axisWallChart (primaryAxisFrame i) h y ∉ S := by
      rw [heq, hSi x t hdom]
      exact hns
    have hyp : WallProductDecay (axisWallChart (primaryAxisFrame i) h y) := by
      rw [heq, wallProductDecay_maxCurve_iff hx.2 hdom]
      exact hprod
    have H := hsuccess (i, y) ⟨⟨hs.le, max_le hb.le hw.le⟩, hy⟩ hys hyp
    apply globalAxisWallHittingDomain_of_forward primaryAxisFrame (by simpa using ht.le) hdom
    simpa only [axisFamilyChart, heq] using H

end BianchiIX
