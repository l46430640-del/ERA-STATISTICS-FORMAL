import Mathlib.MeasureTheory.Function.JacobianOneDim

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- A positive phase slope bounds the actual deleted radial length without normalizing the image. -/
theorem radial_phase_deleted_length {f : ℝ → ℝ} {a b c : ℝ} {A E : Set ℝ}
    (hc : 0 < c) (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hder : ∀ x ∈ Icc a b, c ≤ deriv f x)
    (hA : MeasurableSet A) (hAI : A ⊆ Icc a b) (hE : f '' A ⊆ E) :
    volume A ≤ min (ENNReal.ofReal (b - a)) (ENNReal.ofReal (1 / c) * volume E) := by
  have hmono : StrictMonoOn f (Icc a b) := strictMonoOn_of_deriv_pos (convex_Icc a b)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
    (fun x hx => hc.trans_le (hder x (interior_subset hx)))
  have hj := lintegral_image_eq_lintegral_abs_deriv_mul hA
    (fun x hx => (hf x (hAI hx)).hasDerivAt.hasDerivWithinAt)
    (hmono.injOn.mono hAI) (fun _ => (1 : ℝ≥0∞))
  simp only [lintegral_one, mul_one, Measure.restrict_apply_univ] at hj
  have hscale : ENNReal.ofReal c * volume A ≤ volume (f '' A) := by
    calc
      _ = ∫⁻ _ in A, ENNReal.ofReal c := by simp
      _ ≤ ∫⁻ x in A, ENNReal.ofReal |deriv f x| :=
        setLIntegral_mono' hA (fun x hx => ENNReal.ofReal_le_ofReal
          ((hder x (hAI hx)).trans (le_abs_self _)))
      _ = _ := hj.symm
  refine le_min ?_ ?_
  · simpa only [Real.volume_Icc] using (measure_mono hAI : volume A ≤ volume (Icc a b))
  · calc
      volume A = ENNReal.ofReal (1 / c) * (ENNReal.ofReal c * volume A) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), one_div_mul_cancel hc.ne']
        simp
      _ ≤ ENNReal.ofReal (1 / c) * volume E :=
        mul_le_mul' le_rfl (hscale.trans (measure_mono hE))

end BianchiIX
