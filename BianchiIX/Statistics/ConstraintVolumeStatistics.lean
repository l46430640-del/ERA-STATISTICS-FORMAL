import BianchiIX.Statistics.CommonException

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

theorem injective_of_normalizedConstraintVolume_ne_zero {x : NormalizedState}
    {L : FourCoordinates →L[ℝ] NormalizedState}
    (hvol : normalizedConstraintVolume x (fun i => L (Pi.single i 1)) ≠ 0) :
    Function.Injective L := by
  have hdet : normalizedAmbientVolume (Fin.cons ((1 / 2 : ℝ) • x)
      (fun i => L (Pi.single i 1))) ≠ 0 := by
    intro hz
    apply hvol
    simp only [normalizedConstraintVolume, hz, zero_div]
  have hli := ((Pi.basisFun ℝ (Fin 5)).is_basis_iff_det.mpr (isUnit_iff_ne_zero.mpr hdet)).1
  have hfour : LinearIndependent ℝ (fun i : Fin 4 => L (Pi.single i 1)) := by
    simpa only [Function.comp_def, Fin.cons_succ] using hli.comp Fin.succ (Fin.succ_injective 4)
  have hsum (v : FourCoordinates) : ∑ i, v i • L (Pi.single i 1) = L v := by
    simp only [← map_smul, ← map_sum]
    congr 1
    ext j
    simp [Pi.single_apply]
  intro v w hvw
  apply hfour.fintypeLinearCombination_injective
  simpa only [Fintype.linearCombination_apply, hsum] using hvw

/-- Nullity for the intrinsic constraint volume in any regular physical coordinates. -/
theorem NullInFourCoordinates.preimage_constraint {S : Set NormalizedState}
    (H : NullInFourCoordinates S) {C : FourCoordinates → NormalizedState} {U : Set FourCoordinates}
    (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hv : ∀ y ∈ U, normalizedConstraintVolume (C y)
      (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) : volume (U ∩ C ⁻¹' S) = 0 :=
  H.preimage hC (fun y hy => injective_of_normalizedConstraintVolume_ne_zero (hv y hy))

def normalizedConstraintChartDensity (C : FourCoordinates → NormalizedState) (y : FourCoordinates) : ℝ≥0∞ :=
  ENNReal.ofReal |normalizedConstraintVolume (C y) (fun i => fderiv ℝ C y (Pi.single i 1))|

theorem normalizedConstraintChartDensity_pos {C : FourCoordinates → NormalizedState} {y : FourCoordinates}
    (hv : normalizedConstraintVolume (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) :
    0 < normalizedConstraintChartDensity C y := ENNReal.ofReal_pos.mpr (abs_pos.mpr hv)

theorem NullInFourCoordinates.constraint_volume {S : Set NormalizedState}
    (H : NullInFourCoordinates S) {C : FourCoordinates → NormalizedState} {U : Set FourCoordinates}
    (hC : ∀ y ∈ U, ContDiffAt ℝ 1 C y)
    (hv : ∀ y ∈ U, normalizedConstraintVolume (C y)
      (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) :
    (volume.withDensity (normalizedConstraintChartDensity C)) (U ∩ C ⁻¹' S) = 0 :=
  withDensity_absolutelyContinuous volume _ (H.preimage_constraint hC hv)

/-- The same parameters give statistical cores for every smooth four-dimensional physical density. -/
theorem exists_constraint_statistics
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    (hBrehm : Literature.BrehmIXAttractorInput) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧
          ∀ (C : FourCoordinates → NormalizedState) (U : Set FourCoordinates),
            (∀ y ∈ U, ContDiffAt ℝ 1 C y) →
            (∀ y ∈ U, positiveWalls (C y)) → (∀ y ∈ U, stateConstraint (C y) = 1) →
            (∀ y ∈ U, normalizedConstraintVolume (C y)
              (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) →
            ∀ ρ : FourCoordinates → ℝ≥0∞,
              ∀ᵐ y ∂volume.withDensity ρ, y ∈ U → StatisticalCoreFuture η J σ Bcap (C y) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_common_borel_statistical_exception hBirkhoff hBrehm
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, N, _, _, _, _, hfour, hstat⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, ?_⟩
  intro C U hC hp hc hv ρ
  have H := hfour.ae_not_mem hC
    (fun y hy => injective_of_normalizedConstraintVolume_ne_zero (hv y hy)) ρ
  filter_upwards [H] with y hy hyU
  exact hstat (C y) ⟨hp y hyU, hc y hyU⟩ (hy hyU)

end BianchiIX
