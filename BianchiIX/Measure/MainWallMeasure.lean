import BianchiIX.Dynamics.MainWallArrival
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.WithDensity

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

theorem measurable_mainWallChartDensity (h : ℝ) : Measurable (mainWallChartDensity h) := by
  unfold mainWallChartDensity correctedSectionFluxDensity sectionFluxDensity shearSq
    mainWallChart mainWallRadicand curvature wallAmplitude
  fun_prop

theorem continuousAt_mainWallChartDensity {h : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hy : y ∈ mainWallChartDomain h) : ContinuousAt (mainWallChartDensity h) y := by
  have hp : mainWallChart h y 0 ≠ 0 := ne_of_lt (mainWallChart_negative hy)
  have hH : 0 ≤ wallAmplitude h (Real.exp (-y 1)) (Real.exp (-y 2)) :=
    Real.rpow_nonneg (mul_pos (mul_pos hh (Real.exp_pos _)) (Real.exp_pos _)).le _
  have hc : Continuous (fun v : SectionCoordinates => mainWallChart h v 0) := by
    unfold mainWallChart mainWallRadicand curvature
    fun_prop
  have hcH : Continuous (fun v : SectionCoordinates =>
      wallAmplitude h (Real.exp (-v 1)) (Real.exp (-v 2))) := by
    unfold wallAmplitude
    exact (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 2 / 3)).comp (by fun_prop)
  unfold mainWallChartDensity correctedSectionFluxDensity sectionFluxDensity shearSq
  exact (((hc.continuousAt.pow 2).add ((continuous_apply (0 : Fin 3)).continuousAt.pow 2)).sub
    (continuousAt_const.mul hc.continuousAt)).div
      (continuousAt_const.mul hc.continuousAt.abs) (mul_ne_zero (by norm_num) (abs_ne_zero.mpr hp))
    |>.div (continuousAt_const.add (continuousAt_const.mul hcH.continuousAt)) (by linarith)

def mainWallMeasure (h : ℝ) : Measure SectionCoordinates :=
  (volume.restrict (mainWallChartDomain h)).withDensity (fun y => ENNReal.ofReal (mainWallChartDensity h y))

theorem mainWallMeasure_apply {h : ℝ} {A : Set SectionCoordinates}
    (hA : MeasurableSet A) (hsub : A ⊆ mainWallChartDomain h) :
    mainWallMeasure h A = ∫⁻ y in A, ENNReal.ofReal (mainWallChartDensity h y) := by
  rw [mainWallMeasure, withDensity_apply _ hA, Measure.restrict_restrict_of_subset hsub]

theorem mainWallMeasure_absolutelyContinuous (h : ℝ) :
    mainWallMeasure h ≪ volume.restrict (mainWallChartDomain h) := withDensity_absolutelyContinuous _ _

theorem volume_restrict_absolutelyContinuous_mainWallMeasure {h : ℝ} (hh : 0 < h) :
    volume.restrict (mainWallChartDomain h) ≪ mainWallMeasure h := by
  apply withDensity_absolutelyContinuous' (measurable_mainWallChartDensity h).ennreal_ofReal.aemeasurable
  apply ae_restrict_of_forall_mem (isOpen_mainWallChartDomain h).measurableSet
  intro y hy
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (mainWallChartDensity_pos hh hy))

theorem mainWallMeasure_null_iff {h : ℝ} (hh : 0 < h) (A : Set SectionCoordinates) :
    mainWallMeasure h A = 0 ↔ (volume.restrict (mainWallChartDomain h)) A = 0 :=
  ⟨fun hA => volume_restrict_absolutelyContinuous_mainWallMeasure hh hA,
    fun hA => mainWallMeasure_absolutelyContinuous h hA⟩

theorem lintegral_mainWallMeasure {h : ℝ} {A : Set SectionCoordinates}
    (hA : MeasurableSet A) (hsub : A ⊆ mainWallChartDomain h) (f : SectionCoordinates → ℝ≥0∞) :
    (∫⁻ y in A, f y ∂mainWallMeasure h) =
      ∫⁻ y in A, ENNReal.ofReal (mainWallChartDensity h y) * f y := by
  rw [mainWallMeasure, setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable _
    (measurable_mainWallChartDensity h).ennreal_ofReal f hA (Filter.Eventually.of_forall
      (fun _ => ENNReal.ofReal_lt_top)), Measure.restrict_restrict_of_subset hsub]
  rfl

namespace MainWallArrival

variable {h k t₀ : ℝ} (P : MainWallArrival h k t₀)

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

theorem measurableSet_image {A : Set SectionCoordinates} (hA : MeasurableSet A) (hsub : A ⊆ P.source) :
    MeasurableSet (P.map '' A) :=
  hA.image_of_continuousOn_injOn
    (fun y hy => (P.map_regular y (hsub hy)).continuousAt.continuousWithinAt) (P.injOn.mono hsub)

/-- The local arrival transports the actual section measure with its exact weighted Jacobian. -/
theorem measure_image (hh : 0 < h) {A : Set SectionCoordinates}
    (hA : MeasurableSet A) (hsub : A ⊆ P.source) :
    mainWallMeasure k (P.map '' A) = ∫⁻ y in A, ENNReal.ofReal (P.jacobian y) ∂mainWallMeasure h := by
  have hdiff : ∀ y ∈ A, HasFDerivWithinAt P.map (fderiv ℝ P.map y) A y :=
    fun y hy => ((P.map_regular y (hsub hy)).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  rw [mainWallMeasure_apply (P.measurableSet_image hA hsub)
    (by rintro _ ⟨y, hy, rfl⟩; exact P.target_chart (hsub hy)),
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA hdiff (P.injOn.mono hsub),
    lintegral_mainWallMeasure hA (hsub.trans P.source_chart)]
  apply lintegral_congr_ae
  apply ae_restrict_of_forall_mem hA
  intro y hy
  have hp := mainWallChartDensity_pos hh (P.source_chart (hsub hy))
  dsimp only
  rw [← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul hp.le]
  congr 1
  unfold jacobian
  field_simp [ne_of_gt hp]

theorem measure_image_null_iff (hh : 0 < h) (hk : 0 < k) {A : Set SectionCoordinates}
    (hA : MeasurableSet A) (hsub : A ⊆ P.source) :
    mainWallMeasure k (P.map '' A) = 0 ↔ mainWallMeasure h A = 0 := by
  rw [P.measure_image hh hA hsub]
  have hj : AEMeasurable (fun y => ENNReal.ofReal (P.jacobian y)) ((mainWallMeasure h).restrict A) :=
    (((P.continuousOn_jacobian hh hk).mono hsub).aemeasurable hA).ennreal_ofReal
  constructor
  · intro hz
    have haez := (lintegral_eq_zero_iff' hj).mp hz
    have hfalse : ∀ᵐ y ∂(mainWallMeasure h).restrict A, False := by
      filter_upwards [haez, ae_restrict_mem hA] with y hy hAy
      exact (ne_of_gt (ENNReal.ofReal_pos.mpr (P.jacobian_pos hh hk (hsub hAy)))) hy
    have H : (mainWallMeasure h).restrict A = 0 := by simpa using hfalse
    simpa using H
  · intro hz
    have H : (mainWallMeasure h).restrict A = 0 := by simpa using hz
    simp only [H, lintegral_zero_measure]

theorem measure_image_strict (hh : 0 < h) (hk : 0 < k) {A : Set SectionCoordinates}
    (hA : MeasurableSet A) (hsub : A ⊆ P.source)
    (hfinite : mainWallMeasure h A ≠ ∞) (hpos : mainWallMeasure h A ≠ 0)
    (htime : ∀ y ∈ A, t₀ < P.time (mainWallChart h y)) :
    mainWallMeasure h A < mainWallMeasure k (P.map '' A) := by
  rw [P.measure_image hh hA hsub]
  have hμ : (mainWallMeasure h).restrict A ≠ 0 := by simpa using hpos
  have hj : AEMeasurable P.jacobian ((mainWallMeasure h).restrict A) :=
    ((P.continuousOn_jacobian hh hk).mono hsub).aemeasurable hA
  have hexpand : ∀ᵐ y ∂(mainWallMeasure h).restrict A, 1 < ENNReal.ofReal (P.jacobian y) := by
    apply ae_restrict_of_forall_mem hA
    intro y hy
    exact ENNReal.one_lt_ofReal.mpr (P.jacobian_gt_one hh hk (hsub hy) (htime y hy))
  have H := lintegral_strict_mono (f := fun _ : SectionCoordinates => (1 : ℝ≥0∞))
    hμ hj.ennreal_ofReal (by simpa using hfinite) hexpand
  simpa using H

end MainWallArrival

/-- Local strict expansion follows from an actual forward crossing of the exact Einstein flow. -/
theorem exists_strictly_expanding_mainWallArrival {h k t₀ t : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hk : 0 < k) (hy : y ∈ mainWallChartDomain h) (htt : t₀ < t)
    (hlevel : normalizedMaxCurve (mainWallChart h y) t₀ t 2 = k)
    (hp : normalizedMaxCurve (mainWallChart h y) t₀ t 0 < 0) :
    ∃ P : MainWallArrival h k t₀, y ∈ P.source ∧ P.time (mainWallChart h y) = t ∧
      P.map y = mainWallCoordinates (normalizedMaxCurve (mainWallChart h y) t₀ t) ∧
      ∀ A : Set SectionCoordinates, MeasurableSet A → A ⊆ P.source →
        mainWallMeasure h A ≠ ∞ → mainWallMeasure h A ≠ 0 →
          mainWallMeasure h A < mainWallMeasure k (P.map '' A) := by
  obtain ⟨P, hyP, htime, hmap, hpositive⟩ := exists_forward_mainWallArrival hh hk hy htt hlevel hp
  refine ⟨P, hyP, htime, hmap, fun A hA hsub hfinite hpos => ?_⟩
  exact P.measure_image_strict hh hk hA hsub hfinite hpos (fun v hv => hpositive v (hsub hv))

end BianchiIX
