import BianchiIX.Analysis.CoordinateFactor
import BianchiIX.Analysis.HessianEvaluation
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

namespace BianchiIX

open Set

theorem coordinate_difference_bound {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {i : Fin n} {Y : Fin n → ℝ} {C : ℝ}
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ f (coordinateSegment i Y s))
    (hC : ∀ s ∈ Icc (0 : ℝ) 1, |fderiv ℝ f (coordinateSegment i Y s) (Pi.single i 1)| ≤ C) :
    |f Y - f (Function.update Y i 0)| ≤ |Y i| * C := by
  have HD (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t => f (coordinateSegment i Y t))
        (Y i * fderiv ℝ f (coordinateSegment i Y s) (Pi.single i 1)) s := by
    convert! (hf s hs).hasFDerivAt.comp_hasDerivAt s (hasDerivAt_coordinateSegment i Y s) using 1
    simp only [map_smul, smul_eq_mul]
  have HB (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ‖Y i * fderiv ℝ f (coordinateSegment i Y s) (Pi.single i 1)‖ ≤ |Y i| * C := by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hC s hs) (abs_nonneg _)
  have H := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (HD s hs).hasDerivWithinAt) HB (by norm_num : (0 : ℝ) ∈ Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  simpa [coordinateSegment] using H

theorem coordinate_fderiv_difference_bound {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {i : Fin n} {Y v : Fin n → ℝ} {C : ℝ}
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (fderiv ℝ f) (coordinateSegment i Y s))
    (hC : ∀ s ∈ Icc (0 : ℝ) 1,
      |fderiv ℝ (fderiv ℝ f) (coordinateSegment i Y s) (Pi.single i 1) v| ≤ C) :
    |fderiv ℝ f Y v - fderiv ℝ f (Function.update Y i 0) v| ≤ |Y i| * C := by
  have HD (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t => fderiv ℝ f (coordinateSegment i Y t) v)
        (Y i * fderiv ℝ (fderiv ℝ f) (coordinateSegment i Y s) (Pi.single i 1) v) s := by
    convert! hasDerivAt_fderiv_apply_const (hf s hs) (hasDerivAt_coordinateSegment i Y s) v using 1
    simp only [map_smul, smul_apply, smul_eq_mul]
  have HB (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ‖Y i * fderiv ℝ (fderiv ℝ f) (coordinateSegment i Y s) (Pi.single i 1) v‖ ≤ |Y i| * C := by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hC s hs) (abs_nonneg _)
  have H := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (HD s hs).hasDerivWithinAt) HB (by norm_num : (0 : ℝ) ∈ Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  simpa [coordinateSegment] using H

end BianchiIX
