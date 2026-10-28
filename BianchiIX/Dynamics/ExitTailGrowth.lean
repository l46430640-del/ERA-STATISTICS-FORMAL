import BianchiIX.Dynamics.ExitTailCoordinates
import BianchiIX.Algebra.ExitTailPerturbation
import BianchiIX.Analysis.ClockDecayIntegrals
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section

namespace BianchiIX

open Set

/-- On positive tails with U no larger than V, the radius is nonincreasing and W grows only at rate alpha/(1+alpha). -/
theorem exitTail_positive_growth {Y : ℝ → ExitTailState} {v : ℝ → ℝ} {s t α : ℝ}
    (hst : s ≤ t) (hα : 0 ≤ α) (hinit : Y s 0 ≤ 2 + 2 * α)
    (hY : ∀ r ∈ Icc s t, HasDerivAt Y (exitTailField (v r) (Y r)) r)
    (hreg : ∀ r ∈ Icc s t,
      7 / 4 ≤ Y r 0 ∧ (0 ≤ v r ∧ v r ≤ 1) ∧ (0 ≤ Y r 1 ∧ Y r 1 ≤ v r) ∧ 0 ≤ Y r 2) :
    AntitoneOn (fun r => Y r 0) (Icc s t) ∧
      ∀ r ∈ Icc s t, Y r 2 ≤ Y s 2 * Real.exp (α / (1 + α) * (r - s)) := by
  have hcouple (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ coupling (Y r 1) (v r) (Y r 2) := by
    obtain ⟨_, _, hu, hw⟩ := hreg r hr
    exact mul_nonneg hu.1 (by linarith only [hu.2, hw])
  have hRder (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivAt (fun q => Y q 0) (exitTailRadial (Y r 0) (Y r 1) (v r) (Y r 2)) r :=
    hasDerivAt_pi.mp (hY r hr) 0
  have hanti : AntitoneOn (fun r => Y r 0) (Icc s t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
      (HasDerivAt.continuousOn hRder)
      (fun r hr => (hRder r (interior_subset hr)).differentiableAt.differentiableWithinAt)
    intro r hr
    have hrr := interior_subset hr
    rw [(hRder r hrr).deriv]
    have hreg' := hreg r hrr
    have ht := (exitTailGap_compact hreg'.1 hreg'.2.1).1
    have ht0 : 0 < exitTailGap (Y r 0) (v r) := by linarith only [ht]
    exact exitTailRadial_nonpos (by linarith only [hreg'.1]) ht0.le (hcouple r hrr)
      (add_pos_of_pos_of_nonneg ht0 (hcouple r hrr))
  refine ⟨hanti, ?_⟩
  have hrate (r : ℝ) (hr : r ∈ Icc s t) :
      exitTailWeakRate (Y r 0) (Y r 1) (v r) (Y r 2) ≤ α / (1 + α) := by
    have hg := exitTailGap_compact (hreg r hr).1 (hreg r hr).2.1
    exact exitTailWeakRate_le hα hg.1 hg.2
      ((hanti ⟨le_rfl, hst⟩ hr hr.1).trans hinit) (hcouple r hr)
  have hW (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivAt (fun q => Y q 2)
        (1 * (exitTailWeakRate (Y r 0) (Y r 1) (v r) (Y r 2) * Y r 2)) r := by
    have H := hasDerivAt_pi.mp (hY r hr) 2
    rw [one_mul]
    exact H
  have H := abs_le_exp_of_clock_damping (c := -(α / (1 + α))) hW
    (fun r _ => hasDerivAt_id r) (fun _ _ => by norm_num)
    (fun r hr => by simpa only [neg_neg] using hrate r hr)
  intro r hr
  simpa only [neg_neg, id_eq, abs_of_nonneg (hreg r hr).2.2.2,
    abs_of_nonneg (hreg s ⟨le_rfl, hst⟩).2.2.2] using H r hr

end BianchiIX
