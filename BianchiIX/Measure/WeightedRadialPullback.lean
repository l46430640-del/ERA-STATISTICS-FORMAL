import BianchiIX.Measure.RadialPhasePullback

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

theorem measurableSet_radial_failure {f : ℝ → ℝ} {a b : ℝ} {A G : Set ℝ}
    (hf : ContinuousOn f (Icc a b)) (hA : MeasurableSet A) (hAI : A ⊆ Icc a b)
    (hG : MeasurableSet G) : MeasurableSet (A \ f ⁻¹' G) := by
  have hm : Measurable (fun p : A => f p.val) := (hf.mono hAI).domRestrict.measurable
  have heq : A \ f ⁻¹' G = Subtype.val '' {p : A | f p.val ∉ G} := by
    ext x
    constructor
    · exact fun hx => ⟨⟨x, hx.1⟩, hx.2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.property, hp⟩
  rw [heq]
  exact hA.subtype_image (hG.compl.preimage hm)

/-- A bounded density preserves the unnormalized radial deletion bound. -/
theorem radial_phase_deleted_weighted {f : ℝ → ℝ} {a b c M : ℝ} {A F E : Set ℝ}
    {ω : ℝ → ℝ≥0∞} (hc : 0 < c) (hM : 0 ≤ M)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x) (hder : ∀ x ∈ Icc a b, c ≤ deriv f x)
    (hF : MeasurableSet F) (hFA : F ⊆ A) (hAI : A ⊆ Icc a b) (hE : f '' F ⊆ E)
    (hω : ∀ x ∈ A, ω x ≤ ENNReal.ofReal M) :
    (∫⁻ x in F, ω x) ≤ min (∫⁻ x in A, ω x) (ENNReal.ofReal (M / c) * volume E) := by
  have hlen := (radial_phase_deleted_length hc hf hder hF (hFA.trans hAI) hE).trans (min_le_right _ _)
  refine le_min (lintegral_mono_set hFA) ?_
  calc
    (∫⁻ x in F, ω x) ≤ ∫⁻ _ in F, ENNReal.ofReal M := setLIntegral_mono' hF (fun x hx => hω x (hFA hx))
    _ = ENNReal.ofReal M * volume F := by simp
    _ ≤ ENNReal.ofReal M * (ENNReal.ofReal (1 / c) * volume E) := mul_le_mul' le_rfl hlen
    _ = ENNReal.ofReal (M / c) * volume E := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hM]
      congr 2
      ring

theorem radial_phase_failure_weighted {f : ℝ → ℝ} {a b c M L : ℝ} {A G : Set ℝ}
    {ω : ℝ → ℝ≥0∞} (hc : 0 < c) (hM : 0 ≤ M)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x) (hder : ∀ x ∈ Icc a b, c ≤ deriv f x)
    (hA : MeasurableSet A) (hAI : A ⊆ Icc a b) (hunit : ∀ x ∈ A, f x ∈ Ioo 0 1)
    (hG : MeasurableSet G) (hloss : volume (Ioo 0 1 \ G) ≤ ENNReal.ofReal L)
    (hω : ∀ x ∈ A, ω x ≤ ENNReal.ofReal M) :
    MeasurableSet (A \ f ⁻¹' G) ∧
      (∫⁻ x in A \ f ⁻¹' G, ω x) ≤
        min (∫⁻ x in A, ω x) (ENNReal.ofReal (M / c) * ENNReal.ofReal L) := by
  have hF := measurableSet_radial_failure (fun x hx => (hf x hx).continuousAt.continuousWithinAt) hA hAI hG
  refine ⟨hF, ?_⟩
  have himage : f '' (A \ f ⁻¹' G) ⊆ Ioo 0 1 \ G := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hunit x hx.1, hx.2⟩
  exact (radial_phase_deleted_weighted hc hM hf hder hF sdiff_subset hAI himage hω).trans
    (min_le_min_left _ (mul_le_mul' le_rfl hloss))

end BianchiIX
