import BianchiIX.Dynamics.ProjectiveRegularity
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section

namespace BianchiIX

open Set

/-- The exact weak-wall product is nonincreasing under a nonnegative time scaling while the strong wall is at most one. -/
theorem scaled_projective_product_antitone {I : Set ℝ} {Y : ℝ → ProjectiveState} {A : ℝ → ℝ}
    (hI : Convex ℝ I) (hY : ∀ t ∈ I, HasDerivAt Y (A t • projectiveField (Y t)) t)
    (hA : ∀ t ∈ I, 0 ≤ A t)
    (hu : ∀ t ∈ I, 0 ≤ Y t 1 ∧ Y t 1 ≤ 1)
    (hv : ∀ t ∈ I, 0 ≤ Y t 2) (hw : ∀ t ∈ I, 0 ≤ Y t 3) :
    AntitoneOn (fun t => Y t 2 * Y t 3) I := by
  have HD (t : ℝ) (ht : t ∈ I) : HasDerivAt (fun r => Y r 2 * Y r 3)
      (-2 * A t * (1 + coupling (Y t 1) (Y t 2) (Y t 3)) * (Y t 2 * Y t 3)) t := by
    have H := (hasDerivAt_pi.mp (hY t ht) 2).mul (hasDerivAt_pi.mp (hY t ht) 3)
    convert! H using 1
    change _ = A t * activeVelocity (Y t 0) (Y t 1) (Y t 2) (Y t 3) * Y t 3 +
      Y t 2 * (A t * weakVelocity (Y t 0) (Y t 1) (Y t 2) (Y t 3))
    have Heq := weak_product_directional (Y t 0) (Y t 1) (Y t 2) (Y t 3)
    have Hmul := congrArg (fun r => A t * r) Heq
    nlinarith only [Hmul]
  apply antitoneOn_of_deriv_nonpos hI (HasDerivAt.continuousOn HD)
    (fun t ht => (HD t (interior_subset ht)).differentiableAt.differentiableWithinAt)
  intro t ht
  have htI := interior_subset ht
  rw [(HD t htI).deriv]
  have hc : 0 ≤ 1 + coupling (Y t 1) (Y t 2) (Y t 3) := by
    have hu2 := mul_le_mul_of_nonneg_left (hu t htI).2 (hu t htI).1
    dsimp only [coupling]
    nlinarith only [hu2, (hu t htI).2,
      mul_nonneg (hu t htI).1 (add_nonneg (hv t htI) (hw t htI))]
  have H := mul_nonneg (mul_nonneg (hA t htI) hc) (mul_nonneg (hv t htI) (hw t htI))
  nlinarith only [H]

end BianchiIX
