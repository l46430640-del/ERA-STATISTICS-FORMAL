import BianchiIX.Algebra.ConnectionDomain
import BianchiIX.Dynamics.ConnectionActualPrefix
import BianchiIX.Dynamics.CoreEntry

noncomputable section

namespace BianchiIX

open Set

def connectionRegion (μ : ℝ) (y : ProjectiveState) : Prop :=
  |-y 0 - μ| ≤ 1 / 2 ∧ (0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) ∧
    (0 ≤ y 2 ∧ y 2 ≤ 1) ∧ (0 ≤ y 3 ∧ y 3 ≤ 1)

theorem isClosed_connectionRegion (μ : ℝ) : IsClosed {y : ProjectiveState | connectionRegion μ y} := by
  have hm : Continuous (fun y : ProjectiveState => |-y 0 - μ|) := by fun_prop
  exact (isClosed_le hm continuous_const).inter
    (((isClosed_le continuous_const (continuous_apply 1)).inter (isClosed_le (continuous_apply 1) continuous_const)).inter
      (((isClosed_le continuous_const (continuous_apply 2)).inter (isClosed_le (continuous_apply 2) continuous_const)).inter
        ((isClosed_le continuous_const (continuous_apply 3)).inter (isClosed_le (continuous_apply 3) continuous_const))))

theorem normalized_connection_chart_lower {x : NormalizedState} {μ : ℝ}
    (hμ : 4 ≤ μ) (hA : 1 + x 0 ≠ 0) (hc : stateConstraint x = 1)
    (hy : connectionRegion μ (toProjectiveState x)) : 3 / μ ^ 2 ≤ 1 + x 0 := by
  have H := connection_inverse_scale_lower hμ hy.1 hy.2.1 hy.2.2.1 hy.2.2.2
  simp only [neg_neg] at H
  have heq := projective_inverse_scale hA hc
  change 6 / projectiveStateDenom (toProjectiveState x) = 1 + x 0 at heq
  exact H.trans_eq heq

theorem normalized_projective_wall_pos {x : NormalizedState} {t₀ s t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) (ht : t ∈ normalizedMaxDomain x t₀)
    (hAs : 0 < 1 + normalizedMaxCurve x t₀ s 0) (hAt : 0 < 1 + normalizedMaxCurve x t₀ t 0)
    (i : Fin 3) (hi : 0 < toProjectiveState (normalizedMaxCurve x t₀ s) i.succ) :
    0 < toProjectiveState (normalizedMaxCurve x t₀ t) i.succ := by
  have H := normalized_projective_wall_sign hs ht hAs hAt i
  have hne : toProjectiveState (normalizedMaxCurve x t₀ t) i.succ ≠ 0 :=
    fun h => (ne_of_gt hi) (H.1.mp h)
  exact lt_of_le_of_ne (H.2.mpr hi.le) hne.symm

end BianchiIX
