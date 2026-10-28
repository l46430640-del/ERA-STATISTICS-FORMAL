import BianchiIX.Statistics.GaussComplete
import BianchiIX.Statistics.GaussDensity
import Mathlib.Dynamics.Ergodic.Ergodic

/-! Ergodicity from cylinder density bounds and outer regularity. -/

open Set Filter MeasureTheory
open scoped ENNReal

namespace BianchiIX

theorem gaussPrefix_image_measure_ge (a : ℕ → ℕ+) (n : ℕ) {A : Set ℝ}
    (hA : MeasurableSet A) (hsub : A ⊆ Ioo (0 : ℝ) 1) :
    (1 / 2 : ℝ≥0∞) * volume (gaussCylinder (digitPrefix a n)) * volume A ≤
      volume (gaussWord (digitPrefix a n) '' A) := by
  rw [volume_image_eq_lintegral_abs_deriv hA
    (fun x hx => (hasDerivAt_gaussWord_prefix a n (hsub hx).1.le).differentiableAt.hasDerivAt)
    (measurableEmbedding_gaussWord _).injective.injOn, volume_gaussCylinder_prefix]
  calc
    _ = ∫⁻ _ in A, ENNReal.ofReal ((1 / 2) * gaussPrefixLength a n) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    _ ≤ _ := by
      apply lintegral_mono_ae
      apply ae_restrict_of_forall_mem hA
      intro x hx
      exact ENNReal.ofReal_le_ofReal (gaussPrefix_density_bounds a n
        ⟨(hsub hx).1.le, (hsub hx).2.le⟩).1

theorem gaussWord_image_measure_ge (w : List ℕ) (hw : ∀ k ∈ w, 1 ≤ k) {A : Set ℝ}
    (hA : MeasurableSet A) (hsub : A ⊆ Ioo (0 : ℝ) 1) :
    (1 / 2 : ℝ≥0∞) * volume (gaussCylinder w) * volume A ≤ volume (gaussWord w '' A) := by
  obtain ⟨a, ha⟩ := exists_digitPrefix w hw
  simpa only [ha] using gaussPrefix_image_measure_ge a w.length hA hsub

theorem invariant_set_volume_domination {E : Set ℝ} (hE : MeasurableSet E)
    (hinv : gaussMap ⁻¹' E = E) :
    ((1 / 2 : ℝ≥0∞) * volume (Ioo (0 : ℝ) 1 ∩ E)) • volume.restrict (Ioo (0 : ℝ) 1) ≤
      volume.restrict (Ioo (0 : ℝ) 1 ∩ E) := by
  let B := Ioo (0 : ℝ) 1 ∩ E
  have hBfinite : volume B ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (measure_mono inter_subset_left)
  let : (volume.restrict B).Regular := Measure.Regular.restrict_of_measure_ne_top hBfinite
  apply measure_le_of_gaussCylinder_bounds
  · apply (Measure.ae_smul_measure_le _)
    exact (ae_restrict_mem measurableSet_Ioo).and
      (volume_restrict_absolutelyContinuous_gaussMeasure.ae_le ae_gaussMeasure_irrational)
  · intro w _ hw
    have hsub : gaussCylinder w ⊆ Ioo (0 : ℝ) 1 := by
      rintro _ ⟨x, hx, rfl⟩
      exact gaussWord_mem_open_unit w hw hx
    have h := gaussWord_image_measure_ge w hw (measurableSet_Ioo.inter hE) inter_subset_left
    rw [gaussWord_image_inter_invariant hinv w hw] at h
    simp only [Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply (measurableSet_gaussCylinder w), ← inter_assoc,
      inter_eq_left.mpr hsub]
    simpa only [mul_right_comm] using h

theorem invariant_set_volume_zero_or_compl_zero {E : Set ℝ} (hE : MeasurableSet E)
    (hinv : gaussMap ⁻¹' E = E) :
    (volume.restrict (Ioo (0 : ℝ) 1)) E = 0 ∨
      (volume.restrict (Ioo (0 : ℝ) 1)) Eᶜ = 0 := by
  have h := Measure.le_iff'.mp (invariant_set_volume_domination hE hinv) Eᶜ
  have hempty : Eᶜ ∩ (Ioo (0 : ℝ) 1 ∩ E) = ∅ := by
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false]
    tauto
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hE.compl,
    Measure.restrict_apply hE.compl, hempty, measure_empty] at h
  have hz := mul_eq_zero.mp (le_antisymm h bot_le)
  rcases hz with hz | hz
  · left
    have hB : volume (Ioo (0 : ℝ) 1 ∩ E) = 0 :=
      (mul_eq_zero.mp hz).resolve_left (by norm_num)
    simpa only [Measure.restrict_apply hE, inter_comm] using hB
  · right
    simpa only [Measure.restrict_apply hE.compl] using hz

theorem ergodic_gaussMap : Ergodic gaussMap gaussMeasure := by
  refine ⟨measurePreserving_gaussMap, ?_⟩
  constructor
  intro E hE hinv
  have h := invariant_set_volume_zero_or_compl_zero hE hinv
  have hν : gaussMeasure E = 0 ∨ gaussMeasure Eᶜ = 0 :=
    h.imp (fun h => gaussMeasure_absolutelyContinuous h)
      (fun h => gaussMeasure_absolutelyContinuous h)
  simpa [eventuallyConst_set'] using hν

theorem gaussMeasure_zero_or_one_of_ae_invariant {E : Set ℝ}
    (hE : NullMeasurableSet E gaussMeasure) (hinv : gaussMap ⁻¹' E =ᵐ[gaussMeasure] E) :
    gaussMeasure E = 0 ∨ gaussMeasure E = 1 := by
  have h := ergodic_gaussMap.quasiErgodic.ae_empty_or_univ₀ hE hinv
  rcases h with h | h
  · left
    simpa using measure_congr h
  · right
    simpa using measure_congr h

end BianchiIX
