import BianchiIX.Dynamics.AxisArrival
import BianchiIX.Measure.MainWallMeasure

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

namespace AxisWallArrival

variable {A B : NormalizedSymmetry} {h k t₀ : ℝ} (P : AxisWallArrival A B h k t₀)

theorem continuousOn_jacobian (hh : 0 < h) (hk : 0 < k) : ContinuousOn P.jacobian P.source := by
  have hcR : ContinuousOn P.map P.source := fun y hy => (P.map_regular y hy).continuousAt.continuousWithinAt
  have hcD : ContinuousOn (fderiv ℝ P.map) P.source :=
    (show ContDiffOn ℝ 1 P.map P.source from
      fun y hy => (P.map_regular y hy).contDiffWithinAt).continuousOn_fderiv_of_isOpen P.isOpen_source le_rfl
  have hcρ : ContinuousOn (fun y => mainWallChartDensity k (P.map y)) P.source :=
    fun y hy => (continuousAt_mainWallChartDensity hk (P.target_chart hy)).comp_continuousWithinAt
      (hcR y hy)
  exact (hcρ.mul ((ContinuousLinearMap.continuous_det.comp_continuousOn hcD).abs)).div
    (fun y hy => (continuousAt_mainWallChartDensity hh (P.source_chart hy)).continuousWithinAt)
    (fun y hy => ne_of_gt (mainWallChartDensity_pos hh (P.source_chart hy)))

theorem measurableSet_image {E : Set SectionCoordinates} (hE : MeasurableSet E) (hsub : E ⊆ P.source) :
    MeasurableSet (P.map '' E) :=
  hE.image_of_continuousOn_injOn
    (fun y hy => (P.map_regular y (hsub hy)).continuousAt.continuousWithinAt) (P.injOn.mono hsub)

/-- The axis charts have the same flux density, so the existing section measures apply directly. -/
theorem measure_image (hh : 0 < h) {E : Set SectionCoordinates}
    (hE : MeasurableSet E) (hsub : E ⊆ P.source) :
    mainWallMeasure k (P.map '' E) = ∫⁻ y in E, ENNReal.ofReal (P.jacobian y) ∂mainWallMeasure h := by
  have hdiff : ∀ y ∈ E, HasFDerivWithinAt P.map (fderiv ℝ P.map y) E y :=
    fun y hy => ((P.map_regular y (hsub hy)).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  rw [mainWallMeasure_apply (P.measurableSet_image hE hsub)
    (by rintro _ ⟨y, hy, rfl⟩; exact P.target_chart (hsub hy)),
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hE hdiff (P.injOn.mono hsub),
    lintegral_mainWallMeasure hE (hsub.trans P.source_chart)]
  apply lintegral_congr_ae
  apply ae_restrict_of_forall_mem hE
  intro y hy
  have hp := mainWallChartDensity_pos hh (P.source_chart (hsub hy))
  dsimp only
  rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul hp.le]
  congr 1
  unfold jacobian
  field_simp [ne_of_gt hp]

theorem measure_image_null_iff (hh : 0 < h) (hk : 0 < k) {E : Set SectionCoordinates}
    (hE : MeasurableSet E) (hsub : E ⊆ P.source) :
    mainWallMeasure k (P.map '' E) = 0 ↔ mainWallMeasure h E = 0 := by
  rw [P.measure_image hh hE hsub]
  have hj : AEMeasurable (fun y => ENNReal.ofReal (P.jacobian y)) ((mainWallMeasure h).restrict E) :=
    (((P.continuousOn_jacobian hh hk).mono hsub).aemeasurable hE).ennreal_ofReal
  constructor
  · intro hz
    have haez := (lintegral_eq_zero_iff' hj).mp hz
    have hfalse : ∀ᵐ y ∂(mainWallMeasure h).restrict E, False := by
      filter_upwards [haez, ae_restrict_mem hE] with y hy hEy
      exact (ne_of_gt (ENNReal.ofReal_pos.mpr (P.jacobian_pos hh hk (hsub hEy)))) hy
    have H : (mainWallMeasure h).restrict E = 0 := by simpa using hfalse
    simpa using H
  · intro hz
    have H : (mainWallMeasure h).restrict E = 0 := by simpa using hz
    simp only [H, lintegral_zero_measure]

theorem measure_image_strict (hh : 0 < h) (hk : 0 < k) {E : Set SectionCoordinates}
    (hE : MeasurableSet E) (hsub : E ⊆ P.source)
    (hfinite : mainWallMeasure h E ≠ ∞) (hpos : mainWallMeasure h E ≠ 0)
    (htime : ∀ y ∈ E, t₀ < P.time (axisWallChart A h y)) :
    mainWallMeasure h E < mainWallMeasure k (P.map '' E) := by
  rw [P.measure_image hh hE hsub]
  have hμ : (mainWallMeasure h).restrict E ≠ 0 := by simpa using hpos
  have hj : AEMeasurable P.jacobian ((mainWallMeasure h).restrict E) :=
    ((P.continuousOn_jacobian hh hk).mono hsub).aemeasurable hE
  have hexpand : ∀ᵐ y ∂(mainWallMeasure h).restrict E, 1 < ENNReal.ofReal (P.jacobian y) := by
    apply ae_restrict_of_forall_mem hE
    intro y hy
    exact ENNReal.one_lt_ofReal.mpr (P.jacobian_gt_one hh hk (hsub hy) (htime y hy))
  have H := lintegral_strict_mono (f := fun _ : SectionCoordinates => (1 : ℝ≥0∞))
    hμ hj.ennreal_ofReal (by simpa using hfinite) hexpand
  simpa using H

end AxisWallArrival

/-- An actual forward crossing between any two axis charts produces strict measure expansion. -/
theorem exists_strictly_expanding_axisWallArrival (A B : NormalizedSymmetry)
    {h k t₀ t : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hk : 0 < k) (hy : y ∈ mainWallChartDomain h) (htt : t₀ < t)
    (hlevel : B.map (normalizedMaxCurve (axisWallChart A h y) t₀ t) 2 = k)
    (hp : B.map (normalizedMaxCurve (axisWallChart A h y) t₀ t) 0 < 0) :
    ∃ P : AxisWallArrival A B h k t₀, y ∈ P.source ∧ P.time (axisWallChart A h y) = t ∧
      P.map y = axisWallCoordinates B (normalizedMaxCurve (axisWallChart A h y) t₀ t) ∧
      ∀ E : Set SectionCoordinates, MeasurableSet E → E ⊆ P.source →
        mainWallMeasure h E ≠ ∞ → mainWallMeasure h E ≠ 0 →
          mainWallMeasure h E < mainWallMeasure k (P.map '' E) := by
  obtain ⟨P, hyP, htime, hmap, hpositive⟩ := exists_forward_axisWallArrival A B hh hk hy htt hlevel hp
  refine ⟨P, hyP, htime, hmap, fun E hE hsub hfinite hpos => ?_⟩
  exact P.measure_image_strict hh hk hE hsub hfinite hpos (fun v hv => hpositive v (hsub hv))

/-- The symmetry hypotheses are discharged by the explicitly verified three-axis permutations. -/
theorem exists_strictly_expanding_axisPermutationArrival (σ π : Equiv.Perm (Fin 3))
    {h k t₀ t : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hk : 0 < k) (hy : y ∈ mainWallChartDomain h) (htt : t₀ < t)
    (hlevel : (axisPermutation π).map
      (normalizedMaxCurve (axisWallChart (axisPermutation σ) h y) t₀ t) 2 = k)
    (hp : (axisPermutation π).map
      (normalizedMaxCurve (axisWallChart (axisPermutation σ) h y) t₀ t) 0 < 0) :
    ∃ P : AxisWallArrival (axisPermutation σ) (axisPermutation π) h k t₀,
      y ∈ P.source ∧ P.time (axisWallChart (axisPermutation σ) h y) = t ∧
      P.map y = axisWallCoordinates (axisPermutation π)
        (normalizedMaxCurve (axisWallChart (axisPermutation σ) h y) t₀ t) ∧
      ∀ E : Set SectionCoordinates, MeasurableSet E → E ⊆ P.source →
        mainWallMeasure h E ≠ ∞ → mainWallMeasure h E ≠ 0 →
          mainWallMeasure h E < mainWallMeasure k (P.map '' E) :=
  exists_strictly_expanding_axisWallArrival (axisPermutation σ) (axisPermutation π) hh hk hy htt hlevel hp

end BianchiIX
