import BianchiIX.Dynamics.TransverseCoreArrival
import BianchiIX.Measure.LocalDiffeomorphismNull

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

def transverseCoreHittingDomain (C : SectionCoordinates → NormalizedState) (t₀ : ℝ)
    (Z : Set SectionCoordinates) : Set SectionCoordinates :=
  {y | ∃ t, t ∈ normalizedMaxDomain (C y) t₀ ∧
    projectiveActiveWall (normalizedMaxCurve (C y) t₀ t) = 1 ∧
    normalizedEventRate projectiveActiveWall (C y) t₀ t ≠ 0 ∧
    normalizedCoreCoordinates (normalizedMaxCurve (C y) t₀ t) ∈ Z}

/-- Core sets of zero outer volume are missed by almost every point of any transverse constraint chart. -/
theorem volume_transverseCoreHittingDomain
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates} {t₀ : ℝ}
    (hU : IsOpen U) (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hp : ∀ y ∈ U, positiveWalls (C y)) (hc : ∀ y ∈ U, stateConstraint (C y) = 1)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0)
    {Z : Set SectionCoordinates} (hZ : volume Z = 0) :
    volume (U ∩ transverseCoreHittingDomain C t₀ Z) = 0 := by
  let S : Set (SectionCoordinates × ℝ) := {p | p.1 ∈ U ∧
    p.2 ∈ normalizedMaxDomain (C p.1) t₀ ∧
    projectiveActiveWall (normalizedMaxCurve (C p.1) t₀ p.2) = 1 ∧
    normalizedEventRate projectiveActiveWall (C p.1) t₀ p.2 ≠ 0 ∧
    normalizedCoreCoordinates (normalizedMaxCurve (C p.1) t₀ p.2) ∈ Z}
  have hnull : volume (Prod.fst '' S) = 0 := by
    apply volume_fst_image_eq_zero_of_local_null
    intro p hpS
    obtain ⟨R, hR, hdet, hnear⟩ := exists_transverse_core_arrival (hC p.1 hpS.1)
      (hp p.1 hpS.1) ((show ∀ᶠ y in 𝓝 p.1, y ∈ U from hU.mem_nhds hpS.1).mono
        fun y hy => hc y hy)
      (hflux p.1 hpS.1) hpS.2.1 hpS.2.2.1 hpS.2.2.2.1
    obtain ⟨W, hWo, hpW, hWnull⟩ := exists_local_null_preimage hR hdet
    have hfst : ∀ᶠ q : SectionCoordinates × ℝ in 𝓝 p, q.1 ∈ W :=
      continuousAt_fst.eventually (hWo.mem_nhds hpW)
    obtain ⟨V, hV, hVo, hpV⟩ := mem_nhds_iff.mp (hnear.and hfst)
    refine ⟨V, hVo, hpV, W ∩ R ⁻¹' Z, hWnull Z hZ, ?_⟩
    intro q hq
    refine ⟨(hV hq.2).2, ?_⟩
    change R q.1 ∈ Z
    rw [(hV hq.2).1 hq.1.2.2.1]
    exact hq.1.2.2.2.2
  apply measure_mono_null _ hnull
  rintro y ⟨hy, t, ht⟩
  exact ⟨(y, t), ⟨hy, ht⟩, rfl⟩

theorem volume_axis_transverseCoreHittingDomain
    (A : NormalizedSymmetry) {C : SectionCoordinates → NormalizedState}
    {U : Set SectionCoordinates} {t₀ : ℝ}
    (hU : IsOpen U) (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hp : ∀ y ∈ U, positiveWalls (C y)) (hc : ∀ y ∈ U, stateConstraint (C y) = 1)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0)
    {Z : Set SectionCoordinates} (hZ : volume Z = 0) :
    volume (U ∩ transverseCoreHittingDomain (fun y => A.map (C y)) t₀ Z) = 0 := by
  apply volume_transverseCoreHittingDomain hU
  · intro y hy
    exact A.map.contDiff.contDiffAt.comp y (hC y hy)
  · exact fun y hy => (A.positive (C y)).mpr (hp y hy)
  · exact fun y hy => (A.constraint (C y)).trans (hc y hy)
  · intro y hy
    have hd := (A.map.hasFDerivAt.comp y ((hC y hy).differentiableAt (by norm_num)).hasFDerivAt).fderiv
    simp only [Function.comp_def] at hd
    rw [hd]
    change normalizedSectionFlux (A.map (C y))
      (fun i => A.map (fderiv ℝ C y (Pi.single i 1))) ≠ 0
    rw [A.sectionFlux]
    exact hflux y hy
  · exact hZ

end BianchiIX
