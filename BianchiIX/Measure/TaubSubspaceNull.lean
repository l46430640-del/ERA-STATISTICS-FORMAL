import BianchiIX.Measure.RegularLevelNull
import BianchiIX.Dynamics.TaubSubspace
import BianchiIX.Dynamics.AxisFamilySections

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

theorem normalizedSectionFlux_eq_zero_on_taub {x : NormalizedState}
    {v : Fin 3 → NormalizedState} (hs : x 1 = 0) (hw : x 3 = x 4)
    (hv : ∀ i, v i 1 = 0) : normalizedSectionFlux x v = 0 := by
  unfold normalizedSectionFlux normalizedConstraintVolume normalizedAmbientVolume
  rw [Pi.basisFun_det_apply]
  have hdet : (Matrix.of (Fin.cons ((1 / 2 : ℝ) • x) (Fin.cons (normalizedField x) v))).det = 0 := by
    apply Matrix.det_eq_zero_of_column_eq_zero 1
    intro j
    fin_cases j
    · simp [hs]
    · simp [normalizedField, shearMinus, hs, hw]
    · exact hv 0
    · exact hv 1
    · exact hv 2
  rw [hdet, zero_div]

/-- Transversality forces a regular shear level at each point of the Taub invariant subspace. -/
theorem volume_taub_subspace_section
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates}
    (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) :
    volume {y | y ∈ U ∧ normalizedTaubRadiusSq (C y) = 0} = 0 := by
  have hcoords {y : SectionCoordinates} (hy : normalizedTaubRadiusSq (C y) = 0) :
      C y 1 = 0 ∧ C y 3 = C y 4 := by
    dsimp [normalizedTaubRadiusSq, taubRadiusSq] at hy
    constructor
    · nlinarith only [hy, sq_nonneg (C y 3 - C y 4)]
    · nlinarith only [hy, sq_nonneg (C y 1)]
  apply volume_regular_scalar_level (g := fun y => C y 1)
  · intro y hy
    exact (contDiffAt_pi.mp (hC y hy.1)) 1
  · exact fun _ hy => (hcoords hy.2).1
  · intro y hy
    have hd := ((hasFDerivAt_apply 1 (C y)).comp y
      ((hC y hy.1).differentiableAt (by norm_num)).hasFDerivAt).fderiv
    simp only [Function.comp_def] at hd
    rw [hd]
    by_contra! hn
    apply hflux y hy.1
    exact normalizedSectionFlux_eq_zero_on_taub (hcoords hy.2).1 (hcoords hy.2).2 hn

theorem volume_axis_taub_subspace_section (A : NormalizedSymmetry)
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates}
    (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) :
    volume {y | y ∈ U ∧ normalizedTaubRadiusSq (A.map (C y)) = 0} = 0 := by
  apply volume_taub_subspace_section
    (fun y hy => A.map.contDiff.contDiffAt.comp y (hC y hy))
  intro y hy
  have hd := (A.map.hasFDerivAt.comp y ((hC y hy).differentiableAt (by norm_num)).hasFDerivAt).fderiv
  simp only [Function.comp_def] at hd ⊢
  rw [hd]
  change normalizedSectionFlux (A.map (C y))
    (fun i => A.map (fderiv ℝ C y (Pi.single i 1))) ≠ 0
  rw [A.sectionFlux]
  exact hflux y hy

theorem ae_primaryAxis_taubRadiusSq_pos
    {C : SectionCoordinates → NormalizedState} {U : Set SectionCoordinates}
    (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hflux : ∀ y ∈ U,
      normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0)
    (ρ : SectionCoordinates → ℝ≥0∞) :
    ∀ᵐ y ∂(volume.withDensity ρ), y ∈ U →
      ∀ i : Fin 3, 0 < normalizedTaubRadiusSq ((primaryAxisFrame i).map (C y)) := by
  have H (i : Fin 3) : ∀ᵐ y ∂(volume.withDensity ρ),
      ¬(y ∈ U ∧ normalizedTaubRadiusSq ((primaryAxisFrame i).map (C y)) = 0) := by
    rw [ae_iff]
    simpa only [not_not] using withDensity_absolutelyContinuous volume ρ
      (volume_axis_taub_subspace_section (primaryAxisFrame i) hC hflux)
  filter_upwards [ae_all_iff.mpr H] with y hy hyU i
  exact lt_of_le_of_ne (taubRadiusSq_nonneg _ _ _) (fun hz => hy i ⟨hyU, hz.symm⟩)

end BianchiIX
