import BianchiIX.Measure.ShearLogCoordinates
import BianchiIX.Measure.ShearRadialFlux
import BianchiIX.Measure.ThreeCoordinateTonelli
import BianchiIX.Measure.FailureFlux

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal Classical

def shearLabelFailureCoordinates (a : ℝ) (L : Set (ℝ × ℝ)) (F : ℝ × ℝ → Set ℝ) :
    Set SectionCoordinates :=
  {z | z 1 ∈ Ioo (0 : ℝ) 1 ∧ z 2 ∈ Ioo (0 : ℝ) 1 ∧
    (a * z 1, a * z 2) ∈ L ∧ z 0 ∈ F (a * z 1, a * z 2)}

def shearLabelFailureSection (a : ℝ) (L : Set (ℝ × ℝ)) (F : ℝ × ℝ → Set ℝ) :
    Set SectionCoordinates := scaledShearLogCoordinates a '' shearLabelFailureCoordinates a L F

def shearLabelFailureLayer (h a : ℝ) (L : Set (ℝ × ℝ)) (F : ℝ × ℝ → Set ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ y in Ioo (0 : ℝ) 1,
    if (a * x, a * y) ∈ L then
      restartShearRadialFlux h (a * x) (a * y) (F (a * x, a * y)) / ENNReal.ofReal (x * y)
    else 0

theorem mem_shearLabelFailureSection_image_iff {a : ℝ} {L : Set (ℝ × ℝ)}
    {F : ℝ × ℝ → Set ℝ} {z : SectionCoordinates} (ha : 0 < a) (hz : 0 < z 1 ∧ 0 < z 2) :
    scaledShearLogCoordinates a z ∈ shearLabelFailureSection a L F ↔
      z ∈ shearLabelFailureCoordinates a L F := by
  constructor
  · rintro ⟨w, hw, heq⟩
    exact scaledShearLogCoordinates_injOn ha ⟨hw.1.1, hw.2.1.1⟩ hz heq ▸ hw
  · exact fun hw => ⟨z, hw, rfl⟩

theorem mem_shearLabelFailureSection_iff {a n₂ n₃ ρ : ℝ} {L : Set (ℝ × ℝ)}
    {F : ℝ × ℝ → Set ℝ} (ha : 0 < a) (h₂ : n₂ ∈ Ioo 0 a) (h₃ : n₃ ∈ Ioo 0 a)
    (hl : (n₂, n₃) ∈ L) :
    ![ρ, -Real.log n₂, -Real.log n₃] ∈ shearLabelFailureSection a L F ↔ ρ ∈ F (n₂, n₃) := by
  have hx : n₂ / a ∈ Ioo (0 : ℝ) 1 := ⟨div_pos h₂.1 ha, (div_lt_one ha).mpr h₂.2⟩
  have hy : n₃ / a ∈ Ioo (0 : ℝ) 1 := ⟨div_pos h₃.1 ha, (div_lt_one ha).mpr h₃.2⟩
  have h₂a : a * (n₂ / a) = n₂ := mul_div_cancel₀ _ ha.ne'
  have h₃a : a * (n₃ / a) = n₃ := mul_div_cancel₀ _ ha.ne'
  have H := mem_shearLabelFailureSection_image_iff (L := L) (F := F)
    (z := ![ρ, n₂ / a, n₃ / a]) ha ⟨hx.1, hy.1⟩
  simpa [scaledShearLogCoordinates, shearLabelFailureCoordinates, h₂a, h₃a,
    hx.1, hx.2, hy.1, hy.2, hl] using H

/-- Joint measurability on the physical label and radial domain suffices for an ambient Borel failure set. -/
theorem measurableSet_shearLabelFailureCoordinates {a : ℝ} {L : Set (ℝ × ℝ)}
    {F : ℝ × ℝ → Set ℝ} (hL : MeasurableSet L)
    (hFI : ∀ z ∈ L, F z ⊆ Icc a (2 * a))
    (hjoint : MeasurableSet {p : L × Icc a (2 * a) | (p.2 : ℝ) ∈ F p.1.val}) :
    MeasurableSet (shearLabelFailureCoordinates a L F) := by
  let D : Set SectionCoordinates := {z | (a * z 1, a * z 2) ∈ L ∧ z 0 ∈ Icc a (2 * a)}
  have hD : MeasurableSet D := (hL.preimage (by fun_prop)).inter
    (measurableSet_Icc.preimage (measurable_pi_apply 0))
  let g : D → L × Icc a (2 * a) := fun z =>
    (⟨(a * z.val 1, a * z.val 2), z.property.1⟩, ⟨z.val 0, z.property.2⟩)
  have hg : Measurable g := by
    apply Measurable.prodMk
    · apply Measurable.subtype_mk
      exact (measurable_const.mul ((measurable_pi_apply 1).comp measurable_subtype_coe)).prodMk
        (measurable_const.mul ((measurable_pi_apply 2).comp measurable_subtype_coe))
    · exact ((measurable_pi_apply 0).comp measurable_subtype_coe).subtype_mk
  have H := hD.subtype_image (hjoint.preimage hg)
  have heq : Subtype.val '' g ⁻¹' {p : L × Icc a (2 * a) | (p.2 : ℝ) ∈ F p.1.val} =
      {z : SectionCoordinates | (a * z 1, a * z 2) ∈ L ∧ z 0 ∈ F (a * z 1, a * z 2)} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.property.1, hw⟩
    · intro hz
      exact ⟨⟨z, hz.1, hFI _ hz.1 hz.2⟩, hz.2, rfl⟩
  rw [heq] at H
  exact (measurableSet_Ioo.preimage (measurable_pi_apply 1)).inter
    ((measurableSet_Ioo.preimage (measurable_pi_apply 2)).inter H)

theorem measurableSet_shearLabelFailureSection {a : ℝ} {L : Set (ℝ × ℝ)}
    {F : ℝ × ℝ → Set ℝ} (ha : 0 < a) (hA : MeasurableSet (shearLabelFailureCoordinates a L F)) :
    MeasurableSet (shearLabelFailureSection a L F) := by
  apply hA.image_of_continuousOn_injOn
  · intro z hz
    exact (hasFDerivAt_scaledShearLogCoordinates ha hz.1.1 hz.2.1.1).continuousAt.continuousWithinAt
  · apply (scaledShearLogCoordinates_injOn ha).mono
    intro z hz
    exact ⟨hz.1.1, hz.2.1.1⟩

/-- Tonelli identifies arbitrary Borel label families with their actual radial flux integral. -/
theorem shearLabelFailureCoordinates_lintegral {h a : ℝ} {L : Set (ℝ × ℝ)}
    {F : ℝ × ℝ → Set ℝ} (hA : MeasurableSet (shearLabelFailureCoordinates a L F)) :
    (∫⁻ z in shearLabelFailureCoordinates a L F,
      ENNReal.ofReal (restartShearFluxDensity h (a * z 1) (a * z 2) (z 0) / (z 1 * z 2))) =
      shearLabelFailureLayer h a L F := by
  let A := shearLabelFailureCoordinates a L F
  let f : SectionCoordinates → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (restartShearFluxDensity h (a * z 1) (a * z 2) (z 0) / (z 1 * z 2))
  have hf : Measurable f := by
    have hg : Measurable (fun z : SectionCoordinates => ((a * z 1, a * z 2), z 0)) := by fun_prop
    have hd : Measurable (fun z : SectionCoordinates =>
        restartShearFluxDensity h (a * z 1) (a * z 2) (z 0)) := by
      simpa only [Function.comp_def] using (measurable_restartShearFluxDensity h).comp hg
    exact (hd.div ((measurable_pi_apply 1).mul (measurable_pi_apply 2))).ennreal_ofReal
  change (∫⁻ z in A, f z) = _
  rw [← lintegral_indicator hA, lintegral_three_coordinates (hf.indicator hA)]
  unfold shearLabelFailureLayer
  rw [← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro x
  by_cases hx : 0 < x ∧ x < 1
  · rw [indicator_of_mem (show x ∈ Ioo (0 : ℝ) 1 from hx), ← lintegral_indicator measurableSet_Ioo]
    apply lintegral_congr
    intro y
    by_cases hy : 0 < y ∧ y < 1
    · rw [indicator_of_mem (show y ∈ Ioo (0 : ℝ) 1 from hy)]
      by_cases hl : (a * x, a * y) ∈ L
      · rw [if_pos hl]
        have hF : MeasurableSet (F (a * x, a * y)) := by
          have H := hA.preimage (show Measurable (fun r : ℝ => ![r, x, y]) by fun_prop)
          simpa [shearLabelFailureCoordinates, hx, hy, hl] using H
        have heq : (fun r => A.indicator f ![r, x, y]) =
            (F (a * x, a * y)).indicator
              (fun r => ENNReal.ofReal (restartShearFluxDensity h (a * x) (a * y) r / (x * y))) := by
          funext r
          simp [indicator, A, shearLabelFailureCoordinates, f, hx, hy, hl]
        rw [heq, lintegral_indicator hF]
        simp_rw [ENNReal.ofReal_div_of_pos (mul_pos hx.1 hy.1), div_eq_mul_inv]
        exact lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr
          (ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos hx.1 hy.1))))
      · simp [indicator, shearLabelFailureCoordinates, hl]
    · simp [indicator, shearLabelFailureCoordinates, hy]
  · simp [indicator, shearLabelFailureCoordinates, hx]

theorem mainWallMeasure_shearLabelFailureSection {h a : ℝ} {L : Set (ℝ × ℝ)}
    {F : ℝ × ℝ → Set ℝ} (ha : 0 < a) (hA : MeasurableSet (shearLabelFailureCoordinates a L F))
    (hrad : ∀ z ∈ shearLabelFailureCoordinates a L F,
      0 < restartSectionRadicand h (restartShearCurve 1 (a * z 1) (a * z 2) (z 0))) :
    mainWallMeasure h (shearLabelFailureSection a L F) = shearLabelFailureLayer h a L F := by
  rw [shearLabelFailureSection, mainWallMeasure_scaledShearLogCoordinates ha hA
    (fun z hz => ⟨hz.1.1, hz.2.1.1⟩) hrad]
  exact shearLabelFailureCoordinates_lintegral hA

theorem shearLabelFailureLayer_le {h a C σ : ℝ} {L : Set (ℝ × ℝ)} {F : ℝ × ℝ → Set ℝ}
    (Hslice : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1, (a * x, a * y) ∈ L →
      restartShearRadialFlux h (a * x) (a * y) (F (a * x, a * y)) ≤
        ENNReal.ofReal (3 * min a ((C * a ^ (-2 * σ)) * (x * y) ^ σ))) :
    shearLabelFailureLayer h a L F ≤ 3 * logarithmicLayerCost a C σ := by
  let f := fun x y : ℝ => ENNReal.ofReal (min a ((C * a ^ (-2 * σ)) * (x * y) ^ σ) / (x * y))
  have Hpoint (x y : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
      (if (a * x, a * y) ∈ L then
        restartShearRadialFlux h (a * x) (a * y) (F (a * x, a * y)) / ENNReal.ofReal (x * y)
        else 0) ≤ 3 * f x y := by
    split_ifs with hl
    · have H := ENNReal.div_le_div_right (Hslice x hx y hy hl) (ENNReal.ofReal (x * y))
      refine H.trans_eq ?_
      rw [← ENNReal.ofReal_div_of_pos (mul_pos hx.1 hy.1)]
      change ENNReal.ofReal (3 * min a _ / (x * y)) = 3 * ENNReal.ofReal (min a _ / (x * y))
      rw [show (3 : ℝ) * min a _ / (x * y) = 3 * (min a _ / (x * y)) by ring,
        ENNReal.ofReal_mul (by norm_num)]
      norm_num
    · exact zero_le
  calc
    _ ≤ ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ y in Ioo (0 : ℝ) 1, 3 * f x y :=
      setLIntegral_mono' measurableSet_Ioo (fun x hx =>
        setLIntegral_mono' measurableSet_Ioo (fun y hy => Hpoint x y hx hy))
    _ = _ := by
      simp_rw [lintegral_const_mul' (3 : ℝ≥0∞) _ (by norm_num)]
      rfl

end BianchiIX
