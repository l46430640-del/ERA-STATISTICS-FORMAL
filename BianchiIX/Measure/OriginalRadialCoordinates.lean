import BianchiIX.Measure.OriginalSectionMeasure
import BianchiIX.Measure.AngularLogCoordinates
import BianchiIX.Measure.MainWallReflection
import BianchiIX.Measure.ThreeCoordinateTonelli

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

theorem mainWallOriginalMeasure_image {h : ℝ} {A : Set SectionCoordinates}
    {f : SectionCoordinates → SectionCoordinates}
    {f' : SectionCoordinates → SectionCoordinates →L[ℝ] SectionCoordinates}
    (hA : MeasurableSet A) (hd : ∀ z ∈ A, HasFDerivAt f (f' z) z)
    (hi : InjOn f A) (hdom : f '' A ⊆ mainWallChartDomain h) :
    mainWallOriginalMeasure h (f '' A) =
      ∫⁻ z in A, ENNReal.ofReal |(f' z).det| * ENNReal.ofReal (mainWallOriginalDensity h (f z)) := by
  have himage := hA.image_of_continuousOn_injOn
    (fun z hz => (hd z hz).continuousAt.continuousWithinAt) hi
  rw [mainWallOriginalMeasure, withDensity_apply _ himage,
    Measure.restrict_restrict_of_subset hdom,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA
      (fun z hz => (hd z hz).hasFDerivWithinAt) hi]

theorem mainWallOriginalDensity_reflection (h : ℝ) (z : SectionCoordinates) :
    mainWallOriginalDensity h (mainWallReflection z) = mainWallOriginalDensity h z := by
  unfold mainWallOriginalDensity
  rw [mainWallChart_reflection]
  simp [axisSwap, mainWallReflection, sectionFluxDensity, shearSq]

theorem mainWallOriginalMeasure_reflection {h : ℝ} {A : Set SectionCoordinates}
    (hA : MeasurableSet A) :
    mainWallOriginalMeasure h (mainWallReflection '' A) = mainWallOriginalMeasure h A := by
  let D := mainWallChartDomain h
  have hD : MeasurableSet D := (isOpen_mainWallChartDomain h).measurableSet
  have hI : mainWallReflection '' (A ∩ D) = mainWallReflection '' A ∩ D := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hd⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, by simpa only [D, mainWallChartDomain, mem_ofPred_eq,
        mainWallRadicand_reflection] using hd⟩
    · rintro ⟨⟨x, hx, rfl⟩, hd⟩
      exact ⟨x, ⟨hx, by simpa only [D, mainWallChartDomain, mem_ofPred_eq,
        mainWallRadicand_reflection] using hd⟩, rfl⟩
  have H (B : Set SectionCoordinates) (hB : MeasurableSet B) :
      mainWallOriginalMeasure h B = ∫⁻ y in B ∩ D, ENNReal.ofReal (mainWallOriginalDensity h y) := by
    rw [mainWallOriginalMeasure, withDensity_apply _ hB, Measure.restrict_restrict hB]
  rw [H _ (measurableSet_mainWallReflection_image hA), H _ hA, ← hI]
  have hf (y : SectionCoordinates) : HasFDerivAt mainWallReflection
      mainWallReflectionEquiv.toContinuousLinearMap y := mainWallReflectionEquiv.hasFDerivAt
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hA.inter hD)
    (fun y _ => (hf y).hasFDerivWithinAt) mainWallReflectionEquiv.injective.injOn]
  have hdet : mainWallReflectionEquiv.toContinuousLinearMap.det = 1 := mainWallReflection_det
  simp only [hdet, abs_one, ENNReal.ofReal_one, mainWallOriginalDensity_reflection, one_mul]

def signedShearLogCoordinates (σ : ℝ) (z : SectionCoordinates) : SectionCoordinates :=
  ![σ * z 0, -Real.log (z 1), -Real.log (z 2)]

def signedShearLogDifferential (σ : ℝ) (z : SectionCoordinates) :
    SectionCoordinates →L[ℝ] SectionCoordinates :=
  ContinuousLinearMap.pi ![σ • ContinuousLinearMap.proj 0,
    (-(z 1)⁻¹) • ContinuousLinearMap.proj 1, (-(z 2)⁻¹) • ContinuousLinearMap.proj 2]

theorem hasFDerivAt_signedShearLogCoordinates {σ : ℝ} {z : SectionCoordinates}
    (h₁ : 0 < z 1) (h₂ : 0 < z 2) :
    HasFDerivAt (signedShearLogCoordinates σ) (signedShearLogDifferential σ z) z := by
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) z).const_mul σ
  · convert! ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) z).log h₁.ne').neg using 1
    ext v
    change -(z 1)⁻¹ * v 1 = -((z 1)⁻¹ * v 1)
    ring
  · convert! ((hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) z).log h₂.ne').neg using 1
    ext v
    change -(z 2)⁻¹ * v 2 = -((z 2)⁻¹ * v 2)
    ring

theorem signedShearLogDifferential_det (σ : ℝ) (z : SectionCoordinates) :
    (signedShearLogDifferential σ z).det = σ / (z 1 * z 2) := by
  change (signedShearLogDifferential σ z).toLinearMap.det = _
  rw [← LinearMap.det_toMatrix']
  have H : LinearMap.toMatrix' (signedShearLogDifferential σ z).toLinearMap =
      !![σ, 0, 0; 0, -(z 1)⁻¹, 0; 0, 0, -(z 2)⁻¹] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix'_apply, signedShearLogDifferential]
  rw [H, Matrix.det_fin_three]
  simp [div_eq_mul_inv, mul_assoc, mul_comm]

theorem signedShearLogCoordinates_injOn {σ : ℝ} (hσ : σ ≠ 0) :
    InjOn (signedShearLogCoordinates σ) {z : SectionCoordinates | 0 < z 1 ∧ 0 < z 2} := by
  intro z hz w hw heq
  have h0 : σ * z 0 = σ * w 0 := congrFun heq 0
  have h1 : -Real.log (z 1) = -Real.log (w 1) := congrFun heq 1
  have h2 : -Real.log (z 2) = -Real.log (w 2) := congrFun heq 2
  ext i
  fin_cases i
  · exact mul_left_cancel₀ hσ h0
  · exact Real.log_injOn_pos hz.1 hw.1 (neg_injective h1)
  · exact Real.log_injOn_pos hz.2 hw.2 (neg_injective h2)

theorem mainWallOriginalMeasure_signedShearLogCoordinates {h σ : ℝ} {A : Set SectionCoordinates}
    (hσ : |σ| = 1) (hA : MeasurableSet A) (hpos : ∀ z ∈ A, 0 < z 1 ∧ 0 < z 2)
    (hdom : signedShearLogCoordinates σ '' A ⊆ mainWallChartDomain h) :
    mainWallOriginalMeasure h (signedShearLogCoordinates σ '' A) =
      ∫⁻ z in A, ENNReal.ofReal (1 / (z 1 * z 2)) *
        ENNReal.ofReal (mainWallOriginalDensity h (signedShearLogCoordinates σ z)) := by
  have hσ0 : σ ≠ 0 := by intro heq; simp [heq] at hσ
  rw [mainWallOriginalMeasure_image hA
    (fun z hz => hasFDerivAt_signedShearLogCoordinates (hpos z hz).1 (hpos z hz).2)
    ((signedShearLogCoordinates_injOn hσ0).mono hpos) hdom]
  apply setLIntegral_congr_fun hA
  intro z hz
  dsimp only
  rw [signedShearLogDifferential_det, abs_div, hσ,
    abs_of_pos (mul_pos (hpos z hz).1 (hpos z hz).2)]

/-- The two orders give respectively (s,N2,N3) = (theta*r,r,zeta) and (-theta*r,zeta,r). -/
def orderedAngularLogCoordinates (otherWall : Bool) (z : SectionCoordinates) : SectionCoordinates :=
  if otherWall then mainWallReflection (scaledAngularLogCoordinates (1 / 2) z)
    else scaledAngularLogCoordinates (1 / 2) z

theorem mainWallOriginalMeasure_orderedAngularLogCoordinates {h : ℝ} {A : Set SectionCoordinates}
    (otherWall : Bool) (hA : MeasurableSet A) (hpos : ∀ z ∈ A, 0 < z 0 ∧ 0 < z 2)
    (hdom : scaledAngularLogCoordinates (1 / 2) '' A ⊆ mainWallChartDomain h) :
    mainWallOriginalMeasure h (orderedAngularLogCoordinates otherWall '' A) =
      ∫⁻ z in A, ENNReal.ofReal (1 / z 2) *
        ENNReal.ofReal (mainWallOriginalDensity h (orderedAngularLogCoordinates otherWall z)) := by
  have ha : (0 : ℝ) < 1 / 2 := by norm_num
  have hd (z : SectionCoordinates) (hz : z ∈ A) :=
    hasFDerivAt_scaledAngularLogCoordinates ha (hpos z hz).1 (hpos z hz).2
  have hi := (scaledAngularLogCoordinates_injOn ha).mono hpos
  have hbase : mainWallOriginalMeasure h (scaledAngularLogCoordinates (1 / 2) '' A) =
      ∫⁻ z in A, ENNReal.ofReal (1 / z 2) *
        ENNReal.ofReal (mainWallOriginalDensity h (scaledAngularLogCoordinates (1 / 2) z)) := by
    rw [mainWallOriginalMeasure_image hA hd hi hdom]
    apply setLIntegral_congr_fun hA
    intro z hz
    dsimp only
    rw [scaledAngularLogDifferential_det (hpos z hz).1.ne', abs_neg,
      abs_of_pos (inv_pos.mpr (hpos z hz).2)]
    simp only [one_div]
  cases otherWall
  · exact hbase
  · have himage := hA.image_of_continuousOn_injOn
      (fun z hz => (hd z hz).continuousAt.continuousWithinAt) hi
    change mainWallOriginalMeasure h ((mainWallReflection ∘ scaledAngularLogCoordinates (1 / 2)) '' A) = _
    rw [image_comp, mainWallOriginalMeasure_reflection himage, hbase]
    simp only [orderedAngularLogCoordinates, ↓reduceIte, mainWallOriginalDensity_reflection]

/-- The exact radius fiber of a Borel set is kept inside the radial integral. -/
theorem setLIntegral_three_coordinates {A : Set SectionCoordinates}
    (hA : MeasurableSet A) {f : SectionCoordinates → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z in A, f z) = ∫⁻ x : ℝ, ∫⁻ y : ℝ,
      ∫⁻ r in {r : ℝ | ![r, x, y] ∈ A}, f ![r, x, y] := by
  rw [← lintegral_indicator hA, lintegral_three_coordinates (hf.indicator hA)]
  apply lintegral_congr
  intro x
  apply lintegral_congr
  intro y
  have hv : Measurable (fun r : ℝ => ![r, x, y]) := by fun_prop
  have hAf : MeasurableSet {r : ℝ | ![r, x, y] ∈ A} := hA.preimage hv
  rw [← lintegral_indicator hAf]
  apply lintegral_congr
  intro r
  by_cases hr : ![r, x, y] ∈ A <;> simp [hr]

end BianchiIX
