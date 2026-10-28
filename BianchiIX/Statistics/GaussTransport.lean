import BianchiIX.Statistics.GaussDistortion
import BianchiIX.Statistics.GaussCylinders
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! Image measure bounds for the actual finite compositions, Section 3.3. -/

namespace BianchiIX

noncomputable section

open Set Finset MeasureTheory
open scoped ENNReal

theorem volume_image_eq_lintegral_abs_deriv {F F' : ℝ → ℝ} {A : Set ℝ}
    (hA : MeasurableSet A) (hF : ∀ x ∈ A, HasDerivAt F (F' x) x) (hinj : InjOn F A) :
    volume (F '' A) = ∫⁻ x in A, ENNReal.ofReal |F' x| := by
  simpa using lintegral_image_eq_lintegral_abs_deriv_mul hA
    (fun x hx => (hF x hx).hasDerivWithinAt) hinj (fun _ => 1)

theorem volume_image_le_mul_of_deriv_le {F F' G G' : ℝ → ℝ} {A : Set ℝ} {C : ℝ}
    (hA : MeasurableSet A) (hF : ∀ x ∈ A, HasDerivAt F (F' x) x)
    (hG : ∀ x ∈ A, HasDerivAt G (G' x) x) (hFinj : InjOn F A) (hGinj : InjOn G A)
    (hC : 0 ≤ C) (hbound : ∀ x ∈ A, |F' x| ≤ C * |G' x|) :
    volume (F '' A) ≤ ENNReal.ofReal C * volume (G '' A) := by
  rw [volume_image_eq_lintegral_abs_deriv hA hF hFinj,
    volume_image_eq_lintegral_abs_deriv hA hG hGinj]
  calc
    (∫⁻ x in A, ENNReal.ofReal |F' x|) ≤
        ∫⁻ x in A, ENNReal.ofReal C * ENNReal.ofReal |G' x| := by
      apply lintegral_mono_ae
      apply ae_restrict_of_forall_mem hA
      intro x hx
      rw [← ENNReal.ofReal_mul hC]
      exact ENNReal.ofReal_le_ofReal (hbound x hx)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem gaussPrefix_image_measure_le (a : ℕ → ℕ+) (n : ℕ) {F : ℝ → ℝ}
    {A : Set ℝ} {L : ℝ} (hA : MeasurableSet A) (hApos : ∀ x ∈ A, 0 ≤ x)
    (hF : ∀ x ∈ A, DifferentiableAt ℝ F x) (hinj : InjOn F A)
    (hbound : ∀ x ∈ A, |deriv F x| ≤
      Real.exp L * |deriv (gaussWord (digitPrefix a n)) x|) :
    volume (F '' A) ≤ ENNReal.ofReal (Real.exp L) *
      volume (gaussWord (digitPrefix a n) '' A) := by
  apply volume_image_le_mul_of_deriv_le hA (fun x hx => (hF x hx).hasDerivAt)
    (fun x hx => (hasDerivAt_gaussWord_prefix a n (hApos x hx)).differentiableAt.hasDerivAt)
    hinj (measurableEmbedding_gaussWord _).injective.injOn (Real.exp_pos L).le hbound

/-- The terminal set can be any Borel subset of the actual domain. -/
theorem gauss_actual_prefix_image_le (a : ℕ → ℕ+) (h : ℕ → ℝ → ℝ)
    (D Y : ℝ → ℕ → ℝ) (d e : ℕ → ℝ) (n : ℕ) {A : Set ℝ}
    (hA : MeasurableSet A) (hinj : InjOn (branchPrefix h n) A)
    (hterminal : ∀ t ∈ A, Y t n = t)
    (hrec : ∀ t ∈ A, ∀ j < n, h j (Y t (j + 1)) = Y t j)
    (hder : ∀ t ∈ A, ∀ j < n, HasDerivAt (h j) (D t j) (Y t (j + 1)))
    (hy : ∀ t ∈ A, ∀ j ≤ n, 0 ≤ Y t j) (hD : ∀ t ∈ A, ∀ j < n, D t j ≠ 0)
    (hvalue : ∀ t ∈ A, ∀ j < n,
      |h j (Y t (j + 1)) - gaussInv (a j) (Y t (j + 1))| ≤ d j)
    (hlog : ∀ t ∈ A, ∀ j < n,
      |Real.log (|D t j| / |deriv (gaussInv (a j)) (Y t (j + 1))|)| ≤ e j) :
    volume (branchPrefix h n '' A) ≤
      ENNReal.ofReal (Real.exp (∑ j ∈ range n, (e j + if j = 0 then 0 else 2 * d j))) *
        volume (gaussWord (digitPrefix a n) '' A) := by
  apply gaussPrefix_image_measure_le a n hA
  · intro t ht
    simpa only [hterminal t ht] using hy t ht n le_rfl
  · intro t ht
    have hd := hasDerivAt_branchPrefix h (D t) (Y t) n (hrec t ht) (hder t ht)
    rw [hterminal t ht] at hd
    exact hd.differentiableAt
  · exact hinj
  · intro t ht
    simpa only [hterminal t ht] using
      gauss_actual_prefix_deriv_bound a h (D t) (Y t) d e n (hrec t ht) (hder t ht)
        (hy t ht) (hD t ht) (hvalue t ht) (hlog t ht)

theorem gaussPrefix_cylinder_measure_le (a : ℕ → ℕ+) (n : ℕ) {F : ℝ → ℝ}
    {A : Set ℝ} {L : ℝ} (hA : MeasurableSet A) (hAsub : A ⊆ Ioo (0 : ℝ) 1)
    (hF : ∀ x ∈ A, DifferentiableAt ℝ F x) (hinj : InjOn F A)
    (hbound : ∀ x ∈ A, |deriv F x| ≤
      Real.exp L * |deriv (gaussWord (digitPrefix a n)) x|) :
    volume (F '' A) ≤ ENNReal.ofReal (Real.exp L) *
      volume (gaussCylinder (digitPrefix a n)) := by
  apply (gaussPrefix_image_measure_le a n hA (fun x hx => (hAsub hx).1.le) hF hinj hbound).trans
  exact mul_le_mul le_rfl (measure_mono (image_mono hAsub)) (by positivity) (by positivity)

end

end BianchiIX
