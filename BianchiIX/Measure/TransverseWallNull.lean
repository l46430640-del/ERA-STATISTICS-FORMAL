import BianchiIX.Dynamics.TransverseWallArrival
import BianchiIX.Measure.LocalDiffeomorphismNull

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology ENNReal

def transverseAxisWallOrbitPreimage (C : SectionCoordinates → NormalizedState)
    (A : NormalizedSymmetry) (h t₀ : ℝ) (Z : Set SectionCoordinates) : Set SectionCoordinates :=
  {y | ∃ t ∈ normalizedMaxDomain (C y) t₀, ∃ z ∈ Z,
    axisWallChart A h z = normalizedMaxCurve (C y) t₀ t}

/-- A null wall target has null orbit preimage on every transverse chart, simultaneously for all existing times. -/
theorem volume_transverseAxisWallOrbitPreimage (A : NormalizedSymmetry) {h t₀ : ℝ}
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates}
    (hh : 0 < h) (hU : IsOpen U) (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hp : ∀ y ∈ U, positiveWalls (C y)) (hc : ∀ y ∈ U, stateConstraint (C y) = 1)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0)
    {Z : Set SectionCoordinates} (hchart : Z ⊆ mainWallChartDomain h) (hZ : volume Z = 0) :
    volume (U ∩ transverseAxisWallOrbitPreimage C A h t₀ Z) = 0 := by
  let S : Set (SectionCoordinates × ℝ) := {p | p.1 ∈ U ∧
    p.2 ∈ normalizedMaxDomain (C p.1) t₀ ∧ ∃ z ∈ Z,
      axisWallChart A h z = normalizedMaxCurve (C p.1) t₀ p.2}
  have hlevel {p : SectionCoordinates × ℝ} (hpS : p ∈ S) :
      A.map (normalizedMaxCurve (C p.1) t₀ p.2) 2 = h := by
    obtain ⟨z, _, hz⟩ := hpS.2.2
    rw [← hz, axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
    rfl
  have htarget {p : SectionCoordinates × ℝ} (hpS : p ∈ S) :
      axisWallCoordinates A (normalizedMaxCurve (C p.1) t₀ p.2) ∈ Z := by
    obtain ⟨z, hz, heq⟩ := hpS.2.2
    rwa [← heq, axisWallCoordinates_chart]
  have hnull : volume (Prod.fst '' S) = 0 := by
    apply volume_fst_image_eq_zero_of_local_null
    intro p hpS
    have hneg : A.map (normalizedMaxCurve (C p.1) t₀ p.2) 0 < 0 := by
      obtain ⟨z, hz, heq⟩ := hpS.2.2
      rw [← heq, axisWallChart, ContinuousLinearEquiv.apply_symm_apply]
      exact mainWallChart_negative (hchart hz)
    obtain ⟨R, hR, hdet, hnear⟩ := exists_transverse_axisWall_arrival A (hC p.1 hpS.1)
      (hp p.1 hpS.1) ((show ∀ᶠ y in 𝓝 p.1, y ∈ U from hU.mem_nhds hpS.1).mono
        fun y hy => hc y hy) (hflux p.1 hpS.1) hpS.2.1 hh (hlevel hpS) hneg
    obtain ⟨W, hWo, hpW, hWnull⟩ := exists_local_null_preimage hR hdet
    have hfst : ∀ᶠ q : SectionCoordinates × ℝ in 𝓝 p, q.1 ∈ W :=
      continuousAt_fst.eventually (hWo.mem_nhds hpW)
    obtain ⟨V, hV, hVo, hpV⟩ := mem_nhds_iff.mp (hnear.and hfst)
    refine ⟨V, hVo, hpV, W ∩ R ⁻¹' Z, hWnull Z hZ, ?_⟩
    intro q hq
    refine ⟨(hV hq.2).2, ?_⟩
    change R q.1 ∈ Z
    rw [(hV hq.2).1 (hlevel hq.1)]
    exact htarget hq.1
  apply measure_mono_null _ hnull
  rintro y ⟨hy, t, ht, z, hz, heq⟩
  exact ⟨(y, t), ⟨hy, ht, z, hz, heq⟩, rfl⟩

theorem ae_transverse_orbit_avoids_axis_null_targets {ι : Type*} [Countable ι]
    (A : ι → NormalizedSymmetry) {h : ι → ℝ} {t₀ : ℝ}
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates}
    (hh : ∀ i, 0 < h i) (hU : IsOpen U) (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hp : ∀ y ∈ U, positiveWalls (C y)) (hc : ∀ y ∈ U, stateConstraint (C y) = 1)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0)
    {Z : ι → Set SectionCoordinates} (hchart : ∀ i, Z i ⊆ mainWallChartDomain (h i))
    (hZ : ∀ i, volume (Z i) = 0) (ρ : SectionCoordinates → ℝ≥0∞) :
    ∀ᵐ y ∂(volume.withDensity ρ), y ∈ U →
      ∀ t ∈ normalizedMaxDomain (C y) t₀, ∀ i, ∀ z ∈ Z i,
        axisWallChart (A i) (h i) z ≠ normalizedMaxCurve (C y) t₀ t := by
  have H (i : ι) : ∀ᵐ y ∂(volume.withDensity ρ),
      ¬(y ∈ U ∧ y ∈ transverseAxisWallOrbitPreimage C (A i) (h i) t₀ (Z i)) := by
    rw [ae_iff]
    simpa only [not_not, ofPred_and, ofPred_mem_eq] using withDensity_absolutelyContinuous volume ρ
      (volume_transverseAxisWallOrbitPreimage (A i) (hh i) hU hC hp hc hflux (hchart i) (hZ i))
  filter_upwards [ae_all_iff.mpr H] with y hy hyU t ht i z hz heq
  exact hy i ⟨hyU, t, ht, z, hz, heq⟩

end BianchiIX
