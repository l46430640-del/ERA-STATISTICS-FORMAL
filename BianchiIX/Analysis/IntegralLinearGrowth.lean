import BianchiIX.Analysis.IntegralRowGrowth
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

namespace BianchiIX

open Set MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
theorem signedRowSum_toMatrix_le_opNorm (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) (i : ι) :
    signedRowSum (LinearMap.toMatrix' L.toLinearMap) i ≤ Fintype.card ι * ‖L‖ := by
  apply (signedRowSum_le_sum_abs _ i).trans
  calc
    ∑ j, |LinearMap.toMatrix' L.toLinearMap i j| ≤ ∑ _j : ι, ‖L‖ := by
      apply Finset.sum_le_sum
      intro j _
      have H := (norm_le_pi_norm (L (Pi.single j 1)) i).trans (L.le_opNorm (Pi.single j 1))
      simpa [Pi.norm_single] using H
    _ = _ := by simp

/-- An integrated operator bound suffices; the finite dimension is a harmless fixed factor. -/
theorem norm_le_exp_integral_of_forced_linear {f p : ℝ → (ι → ℝ)}
    {L : ℝ → (ι → ℝ) →L[ℝ] (ι → ℝ)} {R : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (L t (f t) + p t) t)
    (hL : ContinuousOn L (Icc a b)) (hR : ContinuousOn R (Icc a b))
    (hp : ∀ t ∈ Icc a b, ‖p t‖ ≤ R t) :
    ‖f b‖ ≤ Real.exp (Fintype.card ι * ∫ t in a..b, ‖L t‖) *
      (‖f a‖ + ∫ t in a..b, R t) := by
  have H := norm_le_exp_integral_of_forced_rows hab
    (A := fun t => LinearMap.toMatrix' (L t).toLinearMap)
    (σ := fun t => (Fintype.card ι : ℝ) * ‖L t‖)
    (fun t ht => by simpa using hf t ht)
    (continuousOn_const.mul hL.norm) (fun _ _ => by positivity)
    (fun t _ i => signedRowSum_toMatrix_le_opNorm (L t) i) hR hp
  simpa only [intervalIntegral.integral_const_mul] using H

theorem norm_le_exp_integral_of_linear {f : ℝ → (ι → ℝ)}
    {L : ℝ → (ι → ℝ) →L[ℝ] (ι → ℝ)} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (L t (f t)) t)
    (hL : ContinuousOn L (Icc a b)) :
    ‖f b‖ ≤ Real.exp (Fintype.card ι * ∫ t in a..b, ‖L t‖) * ‖f a‖ := by
  simpa using norm_le_exp_integral_of_forced_linear hab
    (p := fun _ => 0) (R := fun _ => 0) (fun t ht => by simpa using hf t ht)
    hL continuousOn_const (fun _ _ => by simp)

end BianchiIX
