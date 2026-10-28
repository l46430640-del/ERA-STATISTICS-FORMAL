import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem integrableOn_integral_tail_of_exp_bound {f : ℝ → ℝ} {K A T : ℝ}
    (hK : 0 < K) (hT : 0 ≤ T) (hf : ContinuousOn f (Ici 0))
    (hbound : ∀ s ≥ 0, |f s| ≤ A / K ^ 2 * Real.exp (-K / 16 * s)) :
    IntegrableOn f (Ioi T) ∧ |∫ s in Ioi T, f s| ≤ 16 * A / K ^ 3 * Real.exp (-K / 16 * T) := by
  have hneg : -K / 16 < 0 := by linarith
  have hg : IntegrableOn (fun s => A / K ^ 2 * Real.exp (-K / 16 * s)) (Ioi T) :=
    (integrableOn_exp_mul_Ioi hneg T).const_mul _
  have hmeas : AEStronglyMeasurable f (volume.restrict (Ioi T)) :=
    (hf.mono (fun _ hs => le_trans hT hs.le)).aestronglyMeasurable measurableSet_Ioi
  have hle : ∀ᵐ s ∂volume.restrict (Ioi T), ‖f s‖ ≤ A / K ^ 2 * Real.exp (-K / 16 * s) :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun s hs => hbound s (le_trans hT hs.le)))
  refine ⟨hg.mono' hmeas hle, ?_⟩
  have H := norm_integral_le_of_norm_le hg hle
  rw [integral_const_mul, integral_exp_mul_Ioi hneg T] at H
  simp only [Real.norm_eq_abs] at H
  convert! H using 1
  field_simp

end BianchiIX
