import BianchiIX.Measure.AngularLogCoordinates
import BianchiIX.Statistics.RestartEraStatistics

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def restartAngularFailureCoordinates (h s a L P η : ℝ) (J : ℕ) (σ Bcap : ℝ) : Set SectionCoordinates :=
  {z | z 1 ∈ Icc (-L) L ∧ z 2 ∈ Ioo (0 : ℝ) 1 ∧
    (z 1, 2 * a * z 2) ∈ restartLabelSet L a P ∧
    z 0 ∈ eraRadialFailure η J σ (restartAmplitudeBudget L a (2 * a * z 2)) Bcap a (2 * a)
      (restartReturnState h s (z 1) (2 * a * z 2))}

def restartAngularFailureSection (h s a L P η : ℝ) (J : ℕ) (σ Bcap : ℝ) : Set SectionCoordinates :=
  scaledAngularLogCoordinates a '' restartAngularFailureCoordinates h s a L P η J σ Bcap

theorem measurableSet_restartAngularFailureCoordinates {h s a L P η σ Bcap : ℝ} {J : ℕ}
    (hjoint : MeasurableSet {p : restartLabelSet L a P × Icc a (2 * a) |
      (p.2 : ℝ) ∈ eraRadialFailure η J σ (restartAmplitudeBudget L a p.1.val.2) Bcap a (2 * a)
        (restartReturnState h s p.1.val.1 p.1.val.2)}) :
    MeasurableSet (restartAngularFailureCoordinates h s a L P η J σ Bcap) := by
  let D : Set SectionCoordinates := {z | (z 1, 2 * a * z 2) ∈ restartLabelSet L a P ∧ z 0 ∈ Icc a (2 * a)}
  have hD : MeasurableSet D :=
    ((measurableSet_restartLabelSet L a P).preimage (by fun_prop)).inter
      (measurableSet_Icc.preimage (measurable_pi_apply 0))
  let g : D → restartLabelSet L a P × Icc a (2 * a) := fun z =>
    (⟨(z.val 1, 2 * a * z.val 2), z.property.1⟩, ⟨z.val 0, z.property.2⟩)
  have hg : Measurable g := by
    apply Measurable.prodMk
    · apply Measurable.subtype_mk
      exact ((measurable_pi_apply 1).comp measurable_subtype_coe).prodMk
        (measurable_const.mul ((measurable_pi_apply 2).comp measurable_subtype_coe))
    · exact ((measurable_pi_apply 0).comp measurable_subtype_coe).subtype_mk
  have H := hD.subtype_image (hjoint.preimage hg)
  have heq : Subtype.val '' g ⁻¹' {p : restartLabelSet L a P × Icc a (2 * a) |
      (p.2 : ℝ) ∈ eraRadialFailure η J σ (restartAmplitudeBudget L a p.1.val.2) Bcap a (2 * a)
        (restartReturnState h s p.1.val.1 p.1.val.2)} =
      {z : SectionCoordinates | (z 1, 2 * a * z 2) ∈ restartLabelSet L a P ∧
        z 0 ∈ eraRadialFailure η J σ (restartAmplitudeBudget L a (2 * a * z 2)) Bcap a (2 * a)
          (restartReturnState h s (z 1) (2 * a * z 2))} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.property.1, hw⟩
    · intro hz
      exact ⟨⟨z, hz.1, hz.2.1⟩, hz.2, rfl⟩
  rw [heq] at H
  exact (measurableSet_Icc.preimage (measurable_pi_apply 1)).inter
    ((measurableSet_Ioo.preimage (measurable_pi_apply 2)).inter H)

theorem measurableSet_restartAngularFailureSection {h s a L P η σ Bcap : ℝ} {J : ℕ}
    (ha : 0 < a) (hA : MeasurableSet (restartAngularFailureCoordinates h s a L P η J σ Bcap)) :
    MeasurableSet (restartAngularFailureSection h s a L P η J σ Bcap) := by
  have hpos (z : SectionCoordinates) (hz : z ∈ restartAngularFailureCoordinates h s a L P η J σ Bcap) :
      0 < z 0 ∧ 0 < z 2 := ⟨ha.trans_le hz.2.2.2.1.1, hz.2.1.1⟩
  exact hA.image_of_continuousOn_injOn
    (fun z hz => (hasFDerivAt_scaledAngularLogCoordinates ha (hpos z hz).1 (hpos z hz).2).continuousAt.continuousWithinAt)
    ((scaledAngularLogCoordinates_injOn ha).mono hpos)

theorem mem_restartAngularFailureSection_iff {h s a L P η σ Bcap θ ζ ρ : ℝ} {J : ℕ}
    (ha : 0 < a) (hθ : |θ| ≤ L) (hζ : 0 < ζ ∧ ζ < 2 * a) (hl : ζ ≤ a ^ P) (hρ : 0 < ρ) :
    ![θ * ρ, -Real.log ρ, -Real.log ζ] ∈ restartAngularFailureSection h s a L P η J σ Bcap ↔
      ρ ∈ eraRadialFailure η J σ (restartAmplitudeBudget L a ζ) Bcap a (2 * a)
        (restartReturnState h s θ ζ) := by
  let z : SectionCoordinates := ![ρ, θ, ζ / (2 * a)]
  have ht : ζ / (2 * a) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hζ.1 (by positivity), (div_lt_one (by positivity)).mpr hζ.2⟩
  have heq : 2 * a * (ζ / (2 * a)) = ζ := mul_div_cancel₀ _ (by positivity)
  have hmap : scaledAngularLogCoordinates a z = ![θ * ρ, -Real.log ρ, -Real.log ζ] := by
    simp [scaledAngularLogCoordinates, z, heq]
  have hmember : z ∈ restartAngularFailureCoordinates h s a L P η J σ Bcap ↔
      ρ ∈ eraRadialFailure η J σ (restartAmplitudeBudget L a ζ) Bcap a (2 * a)
        (restartReturnState h s θ ζ) := by
    simp [restartAngularFailureCoordinates, z, heq, ht.1, ht.2, restartLabelSet, hθ, hl, hζ.1,
      (abs_le.mp hθ).1, (abs_le.mp hθ).2]
  rw [← hmap, ← hmember]
  constructor
  · rintro ⟨w, hw, hwz⟩
    have hwpos : 0 < w 0 ∧ 0 < w 2 := ⟨ha.trans_le hw.2.2.2.1.1, hw.2.1.1⟩
    exact (scaledAngularLogCoordinates_injOn ha hwpos ⟨hρ, ht.1⟩ hwz) ▸ hw
  · exact fun hz => ⟨z, hz, rfl⟩

end BianchiIX
