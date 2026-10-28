import BianchiIX.Measure.WallSaturation
import BianchiIX.Measure.TransverseStatisticalCapture
import BianchiIX.Measure.OrbitVolumeNull

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

/-- One Borel invariant exception, independent of the source chart, contains all exceptional section points. -/
theorem exists_primaryAxis_saturated_null_exception {h : ℝ} (hh : 0 < h)
    {E : Fin 3 → Set SectionCoordinates} {P : Fin 3 × SectionCoordinates → Prop}
    (hE : ∀ i, MeasurableSet (E i)) (hchart : ∀ i, E i ⊆ mainWallChartDomain h)
    (H : ∀ᵐ z ∂axisFamilyMeasure (fun _ : Fin 3 => h), z ∈ axisFamilySection E → P z) :
    ∃ N : Set NormalizedState, MeasurableSet N ∧
      (∀ x ∈ N, positiveWalls x ∧ stateConstraint x = 1) ∧
      (∀ x : NormalizedState, ∀ t ∈ normalizedMaxDomain x 0, normalizedMaxCurve x 0 t ∈ N ↔ x ∈ N) ∧
      (∀ (C : SectionCoordinates → NormalizedState) (U : Set SectionCoordinates),
        IsOpen U → (∀ y ∈ U, ContDiffAt ℝ 1 C y) →
        (∀ y ∈ U, positiveWalls (C y)) → (∀ y ∈ U, stateConstraint (C y) = 1) →
        (∀ y ∈ U, normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) →
        volume (U ∩ C ⁻¹' N) = 0) ∧ NullInFourCoordinates N ∧
      ∀ z ∈ axisFamilySection E, axisFamilyChart primaryAxisFrame (fun _ => h) z ∉ N → P z := by
  classical
  let Z : Fin 3 → Set SectionCoordinates := fun i =>
    toMeasurable volume {y | y ∈ E i ∧ ¬P (i, y)} ∩ E i
  have hZ (i : Fin 3) : MeasurableSet (Z i) := (measurableSet_toMeasurable _ _).inter (hE i)
  have hZchart (i : Fin 3) : Z i ⊆ mainWallChartDomain h := fun _ hz => hchart i hz.2
  have hZnull (i : Fin 3) : volume (Z i) = 0 := by
    apply measure_mono_null inter_subset_left
    rw [measure_toMeasurable]
    exact volume_axisFamily_exceptional_slice hh hchart H i
  let N := ⋃ i : Fin 3, normalizedOrbitSaturation (axisWallChart (primaryAxisFrame i) h '' Z i)
  refine ⟨N, MeasurableSet.iUnion (fun i =>
    measurableSet_axisWallOrbitSaturation (primaryAxisFrame i) hh (hZchart i) (hZ i)), ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact axisWallOrbitSaturation_physical (primaryAxisFrame i) hh (hZchart i) hi
  · intro x t ht
    simp only [N, mem_iUnion, mem_normalizedOrbitSaturation_flow_iff ht]
  · intro C U hU hC hp hc hflux
    have heq : U ∩ C ⁻¹' N = ⋃ i : Fin 3,
        U ∩ C ⁻¹' normalizedOrbitSaturation (axisWallChart (primaryAxisFrame i) h '' Z i) := by
      ext y
      simp only [N, mem_inter_iff, mem_preimage, mem_iUnion]
      constructor
      · rintro ⟨hy, i, hi⟩; exact ⟨i, hy, hi⟩
      · rintro ⟨i, hy, hi⟩; exact ⟨hy, i, hi⟩
    rw [heq]
    exact measure_iUnion_null fun i => volume_preimage_axisWallOrbitSaturation (primaryAxisFrame i)
      hh hU hC hp hc hflux (hZchart i) (hZnull i)
  · exact NullInFourCoordinates.iUnion fun i => nullInFourCoordinates_orbitSaturation
      (fun _ hy => contDiffAt_axisWallChart (primaryAxisFrame i) (hZchart i hy) 1) (hZnull i)
  · intro z hz hn
    by_contra hp
    have hzZ : z.2 ∈ Z z.1 := ⟨subset_toMeasurable volume _ ⟨hz, hp⟩, hz⟩
    apply hn
    exact mem_iUnion.mpr ⟨z.1, subset_normalizedOrbitSaturation _ (mem_image_of_mem _ hzZ)⟩

/-- The statistical failure part of the common invariant exception is instantiated from the exact-flow section theorem. -/
theorem exists_primaryAxis_borel_statistical_exception (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∃ dstar > (0 : ℝ),
            ∀ d ∈ Ioc (0 : ℝ) dstar,
              let E := fun _ : Fin 3 => mainWallSmallSection d ∩ mainWallChartDomain h
              ∃ N : Set NormalizedState, MeasurableSet N ∧
                (∀ x ∈ N, positiveWalls x ∧ stateConstraint x = 1) ∧
                (∀ x : NormalizedState, ∀ t ∈ normalizedMaxDomain x 0,
                  normalizedMaxCurve x 0 t ∈ N ↔ x ∈ N) ∧
                (∀ (C : SectionCoordinates → NormalizedState) (U : Set SectionCoordinates),
                  IsOpen U → (∀ y ∈ U, ContDiffAt ℝ 1 C y) →
                  (∀ y ∈ U, positiveWalls (C y)) → (∀ y ∈ U, stateConstraint (C y) = 1) →
                  (∀ y ∈ U, normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) →
                  volume (U ∩ C ⁻¹' N) = 0) ∧ NullInFourCoordinates N ∧
                ∀ z ∈ axisFamilySection E, axisFamilyChart primaryAxisFrame (fun _ => h) z ∉ N →
                  WallProductDecay (axisFamilyChart primaryAxisFrame (fun _ => h) z) →
                    StatisticalCoreFuture η J σ Bcap (axisFamilyChart primaryAxisFrame (fun _ => h) z) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_primaryAxis_statistics_of_decay hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, hS, hhS, ?_⟩
  intro h hh
  obtain ⟨dS, hdS, HdS⟩ := HS h hh
  refine ⟨dS, hdS, ?_⟩
  intro d hd E
  exact exists_primaryAxis_saturated_null_exception hh.1
    (fun _ => (measurableSet_mainWallSmallSection d).inter (isOpen_mainWallChartDomain h).measurableSet)
    (fun _ _ hz => hz.2) (HdS d hd)

end BianchiIX
