import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section

namespace BianchiIX

open Set

/-- Ordinary derivative bounds control both the full phase interval and all its subintervals. -/
theorem radial_phase_interval {f : ℝ → ℝ} {a b c C : ℝ} (hab : a ≤ b) (hc : 0 < c)
    (hf : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hder : ∀ x ∈ Icc a b, c ≤ deriv f x ∧ deriv f x ≤ C) :
    StrictMonoOn f (Icc a b) ∧ f '' Icc a b = Icc (f a) (f b) ∧
      ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
        c * (y - x) ≤ f y - f x ∧ f y - f x ≤ C * (y - x) := by
  have hcont : ContinuousOn f (Icc a b) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (interior (Icc a b)) :=
    fun x hx => (hf x (interior_subset hx)).differentiableWithinAt
  have hmono : StrictMonoOn f (Icc a b) := strictMonoOn_of_deriv_pos (convex_Icc a b) hcont
    (fun x hx => hc.trans_le (hder x (interior_subset hx)).1)
  refine ⟨hmono, hcont.image_Icc_of_monotoneOn hab hmono.monotoneOn, ?_⟩
  intro x hx y hy hxy
  exact ⟨(convex_Icc a b).mul_sub_le_image_sub_of_le_deriv hcont hdiff
    (fun z hz => (hder z (interior_subset hz)).1) x hx y hy hxy,
    (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le hcont hdiff
      (fun z hz => (hder z (interior_subset hz)).2) x hx y hy hxy⟩

end BianchiIX
