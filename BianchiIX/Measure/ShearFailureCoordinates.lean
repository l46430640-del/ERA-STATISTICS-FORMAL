import BianchiIX.Measure.ShearLogCoordinates
import BianchiIX.Measure.ShearFailureLayer

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def restartShearFailureCoordinates (h s a ε P η : ℝ) (J : ℕ) (σ Bcap : ℝ) : Set SectionCoordinates :=
  {z | z 1 ∈ Ioo (0 : ℝ) 1 ∧ z 2 ∈ Ioo (0 : ℝ) 1 ∧
    (a * z 1, a * z 2) ∈ restartShearLabelSet ε a P ∧
    z 0 ∈ eraRadialFailure η J σ (restartShearAmplitudeBudget a (a * z 1) (a * z 2)) Bcap a (2 * a)
      (restartShearReturnState h s (a * z 1) (a * z 2))}

def restartShearFailureSection (h s a ε P η : ℝ) (J : ℕ) (σ Bcap : ℝ) : Set SectionCoordinates :=
  scaledShearLogCoordinates a '' restartShearFailureCoordinates h s a ε P η J σ Bcap

theorem mem_restartShearFailureSection_image_iff {h s a ε P η σ Bcap : ℝ} {J : ℕ}
    {z : SectionCoordinates} (ha : 0 < a) (hz : 0 < z 1 ∧ 0 < z 2) :
    scaledShearLogCoordinates a z ∈ restartShearFailureSection h s a ε P η J σ Bcap ↔
      z ∈ restartShearFailureCoordinates h s a ε P η J σ Bcap := by
  constructor
  · rintro ⟨w, hw, heq⟩
    have hwz := scaledShearLogCoordinates_injOn ha ⟨hw.1.1, hw.2.1.1⟩ hz heq
    exact hwz ▸ hw
  · exact fun hw => ⟨z, hw, rfl⟩

/-- The normalized label window contains every admissible physical weak-wall label. -/
theorem mem_restartShearFailureSection_iff {h s a ε P η σ Bcap n₂ n₃ ρ : ℝ} {J : ℕ}
    (ha : 0 < a) (hε : ε ≤ 1 / 64)
    (hl : (n₂, n₃) ∈ restartShearLabelSet ε a P) :
    ![ρ, -Real.log n₂, -Real.log n₃] ∈ restartShearFailureSection h s a ε P η J σ Bcap ↔
      ρ ∈ eraRadialFailure η J σ (restartShearAmplitudeBudget a n₂ n₃) Bcap a (2 * a)
        (restartShearReturnState h s n₂ n₃) := by
  have hsmall : 2 * ε < 1 := by linarith only [hε]
  have hn₂ : n₂ < a := hl.1.2.trans_lt (mul_lt_of_lt_one_left ha hsmall)
  have hn₃ : n₃ < a := hl.2.1.2.trans_lt (mul_lt_of_lt_one_left ha hsmall)
  have hx : n₂ / a ∈ Ioo (0 : ℝ) 1 := ⟨div_pos hl.1.1 ha, (div_lt_one ha).mpr hn₂⟩
  have hy : n₃ / a ∈ Ioo (0 : ℝ) 1 := ⟨div_pos hl.2.1.1 ha, (div_lt_one ha).mpr hn₃⟩
  have h₂ : a * (n₂ / a) = n₂ := mul_div_cancel₀ _ ha.ne'
  have h₃ : a * (n₃ / a) = n₃ := mul_div_cancel₀ _ ha.ne'
  have H := mem_restartShearFailureSection_image_iff (h := h) (s := s) (ε := ε) (P := P)
    (η := η) (J := J) (σ := σ) (Bcap := Bcap) (z := ![ρ, n₂ / a, n₃ / a]) ha ⟨hx.1, hy.1⟩
  simpa [scaledShearLogCoordinates, restartShearFailureCoordinates, h₂, h₃,
    hx.1, hx.2, hy.1, hy.2, hl] using H

theorem measurableSet_restartShearFailureCoordinates {h s a ε P η σ Bcap : ℝ} {J : ℕ}
    (hjoint : MeasurableSet {p : restartShearLabelSet ε a P × Icc a (2 * a) |
      (p.2 : ℝ) ∈ eraRadialFailure η J σ
        (restartShearAmplitudeBudget a p.1.val.1 p.1.val.2) Bcap a (2 * a)
        (restartShearReturnState h s p.1.val.1 p.1.val.2)}) :
    MeasurableSet (restartShearFailureCoordinates h s a ε P η J σ Bcap) := by
  let D : Set SectionCoordinates :=
    {z | (a * z 1, a * z 2) ∈ restartShearLabelSet ε a P ∧ z 0 ∈ Icc a (2 * a)}
  have hD : MeasurableSet D :=
    ((measurableSet_restartShearLabelSet ε a P).preimage (by fun_prop)).inter
      (measurableSet_Icc.preimage (measurable_pi_apply 0))
  let g : D → restartShearLabelSet ε a P × Icc a (2 * a) := fun z =>
    (⟨(a * z.val 1, a * z.val 2), z.property.1⟩, ⟨z.val 0, z.property.2⟩)
  have hg : Measurable g := by
    apply Measurable.prodMk
    · apply Measurable.subtype_mk
      exact (measurable_const.mul ((measurable_pi_apply 1).comp measurable_subtype_coe)).prodMk
        (measurable_const.mul ((measurable_pi_apply 2).comp measurable_subtype_coe))
    · exact ((measurable_pi_apply 0).comp measurable_subtype_coe).subtype_mk
  have H := hD.subtype_image (hjoint.preimage hg)
  have heq : Subtype.val '' g ⁻¹' {p : restartShearLabelSet ε a P × Icc a (2 * a) |
      (p.2 : ℝ) ∈ eraRadialFailure η J σ
        (restartShearAmplitudeBudget a p.1.val.1 p.1.val.2) Bcap a (2 * a)
        (restartShearReturnState h s p.1.val.1 p.1.val.2)} =
      {z : SectionCoordinates | (a * z 1, a * z 2) ∈ restartShearLabelSet ε a P ∧
        z 0 ∈ eraRadialFailure η J σ (restartShearAmplitudeBudget a (a * z 1) (a * z 2)) Bcap a (2 * a)
          (restartShearReturnState h s (a * z 1) (a * z 2))} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.property.1, hw⟩
    · intro hz
      exact ⟨⟨z, hz.1, hz.2.1⟩, hz.2, rfl⟩
  rw [heq] at H
  exact (measurableSet_Ioo.preimage (measurable_pi_apply 1)).inter
    ((measurableSet_Ioo.preimage (measurable_pi_apply 2)).inter H)

theorem measurableSet_restartShearFailureSection {h s a ε P η σ Bcap : ℝ} {J : ℕ}
    (ha : 0 < a) (hA : MeasurableSet (restartShearFailureCoordinates h s a ε P η J σ Bcap)) :
    MeasurableSet (restartShearFailureSection h s a ε P η J σ Bcap) := by
  apply hA.image_of_continuousOn_injOn
  · intro z hz
    exact (hasFDerivAt_scaledShearLogCoordinates ha hz.1.1 hz.2.1.1).continuousAt.continuousWithinAt
  · apply (scaledShearLogCoordinates_injOn ha).mono
    intro z hz
    exact ⟨hz.1.1, hz.2.1.1⟩

end BianchiIX
