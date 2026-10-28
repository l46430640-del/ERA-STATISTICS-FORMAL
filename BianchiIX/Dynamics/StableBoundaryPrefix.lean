import BianchiIX.Dynamics.StableBoundaryDecay
import BianchiIX.Dynamics.ProjectiveClock
import BianchiIX.Dynamics.ProjectiveRegularity
import BianchiIX.Dynamics.ConstrainedComplete

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

def stableBoundaryRegion (c : ℝ) (y : ProjectiveState) : Prop :=
  |y 0 - c| ≤ 1 / 10 ∧ |y 1| ≤ 1 / 100 ∧ y 2 = 0 ∧ |y 3| ≤ 1 / 100

def normalizedStableClock (x : NormalizedState) (t₀ s c t : ℝ) : ℝ :=
  (c + 1) * integralClock (normalizedProjectiveRate x t₀) s t

theorem isClosed_stableBoundaryRegion (c : ℝ) :
    IsClosed {y : ProjectiveState | stableBoundaryRegion c y} := by
  have hm : Continuous (fun y : ProjectiveState => |y 0 - c|) := by fun_prop
  exact (isClosed_le hm continuous_const).inter
    ((isClosed_le (continuous_apply 1).abs continuous_const).inter
      ((isClosed_eq (continuous_apply 2) continuous_const).inter
        (isClosed_le (continuous_apply 3).abs continuous_const)))

theorem normalized_stable_chart_lower {x : NormalizedState} {c : ℝ}
    (hc : 2 ≤ c) (hA : 1 + x 0 ≠ 0) (hx : stateConstraint x = 1)
    (hy : stableBoundaryRegion c (toProjectiveState x)) :
    3 / (c + 1) ^ 2 ≤ 1 + x 0 := by
  have hD := stable_boundary_denom hc hy.1 hy.2.1 hy.2.2.2
  have hscale := projective_inverse_scale hA hx
  change 6 / projectiveStateDenom (toProjectiveState x) = 1 + x 0 at hscale
  rw [← hscale]
  have heq : projectiveStateDenom (toProjectiveState x) =
      projectiveDenom (toProjectiveState x 0) (toProjectiveState x 1) 0 (toProjectiveState x 3) := by
    unfold projectiveStateDenom
    rw [hy.2.2.1]
  rw [heq]
  have hK : 0 < c + 1 := by linarith
  calc
    _ = 6 / (2 * (c + 1) ^ 2) := by field_simp; norm_num
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hD.1 hD.2

theorem hasDerivAt_normalizedStableClock {x : NormalizedState} {t₀ s c t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) (ht : t ∈ normalizedMaxDomain x t₀) :
    HasDerivAt (normalizedStableClock x t₀ s c)
      ((c + 1) * normalizedProjectiveRate x t₀ t) t :=
  ((hasStrictDerivAt_integralClock (convex_normalizedMaxDomain x t₀)
    (isOpen_normalizedMaxDomain x t₀) (continuousOn_normalizedProjectiveRate x t₀) hs ht).hasDerivAt).const_mul _

theorem normalized_stable_prefix_estimates {x : NormalizedState} {t₀ s t c : ℝ}
    (hx : stateConstraint x = 1) (hc : 2 ≤ c) (hs : t₀ ≤ s) (hst : s ≤ t)
    (hA : ∀ r ∈ Icc s t, 0 < normalizedProjectiveRate x t₀ r)
    (hy : ∀ r ∈ Icc s t, stableBoundaryRegion c (toProjectiveState (normalizedMaxCurve x t₀ r))) :
    let Y := fun r => toProjectiveState (normalizedMaxCurve x t₀ r)
    |Y t 0 - Y s 0| ≤ 8 * (|Y s 1| + |Y s 3|) ^ 2 / (c + 1) ∧
    (∀ r ∈ Icc s t,
      |Y r 1| ≤ |Y s 1| * Real.exp (-(c + 1) / 8 * normalizedStableClock x t₀ s c r) ∧
      |Y r 3| ≤ |Y s 3| * Real.exp (-(1 / 4) * normalizedStableClock x t₀ s c r)) ∧
    (∀ r ∈ Icc s t, |Y r 1| ≤ |Y s 1| ∧ |Y r 3| ≤ |Y s 3|) := by
  intro Y
  have hdom (r : ℝ) (hr : s ≤ r) : r ∈ normalizedMaxDomain x t₀ :=
    normalizedMaxDomain_contains_Ici_of_constraint hx t₀ (hs.trans hr)
  have hY (r : ℝ) (hr : r ∈ Icc s t) :
      HasDerivAt Y (normalizedProjectiveRate x t₀ r • projectiveField (Y r)) r := by
    have H := normalizedMaxCurve_forward_of_constraint hx (hs.trans hr.1)
    exact hasDerivAt_toProjectiveState_normalized H.1 (ne_of_gt (hA r hr)) H.2.1
  have hz (r : ℝ) (hr : r ∈ Icc s t) :=
    hasDerivAt_normalizedStableClock (c := c) (hdom s le_rfl) (hdom r hr.1)
  have hac : ContinuousOn (normalizedProjectiveRate x t₀) (Icc s t) :=
    (continuousOn_normalizedProjectiveRate x t₀).mono (fun r hr => hdom r hr.1)
  have H := scaled_stable_boundary_decay hc hY hz (fun r hr => (hA r hr).le)
    (fun r hr => (hy r hr).2.2.1) (fun r hr => (hy r hr).1)
    (fun r hr => (hy r hr).2.1) (fun r hr => (hy r hr).2.2.2)
  have hzero : normalizedStableClock x t₀ s c s = 0 := by
    simp [normalizedStableClock, integralClock_initial]
  simp only [hzero, sub_zero] at H
  refine ⟨scaled_stable_boundary_drift hst hc hY hz hac (fun r hr => (hA r hr).le)
    (fun r hr => (hy r hr).2.2.1) (fun r hr => (hy r hr).1)
    (fun r hr => (hy r hr).2.1) (fun r hr => (hy r hr).2.2.2), H, ?_⟩
  intro r hr
  have hz0 : 0 ≤ normalizedStableClock x t₀ s c r := by
    apply mul_nonneg (by linarith : 0 ≤ c + 1)
    apply intervalIntegral.integral_nonneg hr.1
    intro q hq
    exact (hA q ⟨hq.1, hq.2.trans hr.2⟩).le
  constructor
  · exact (H r hr).1.trans (mul_le_of_le_one_right (abs_nonneg _)
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hz0)))
  · exact (H r hr).2.trans (mul_le_of_le_one_right (abs_nonneg _)
      (Real.exp_le_one_iff.mpr (by linarith)))

end BianchiIX
