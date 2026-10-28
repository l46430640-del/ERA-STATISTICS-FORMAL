import BianchiIX.Dynamics.ExitExistence
import BianchiIX.Dynamics.CoreTail

noncomputable section

namespace BianchiIX

open Set

theorem normalized_exit_active_rate_neg {x : NormalizedState} {t₀ t h : ℝ}
    (hc : stateConstraint x = 1) (hh : 0 < h) (ht : t₀ ≤ t)
    (hA : 0 < 1 + normalizedMaxCurve x t₀ t 0)
    (hy : exitPhysicalRegion h (toProjectiveState (normalizedMaxCurve x t₀ t))) :
    normalizedEventRate projectiveActiveWall x t₀ t < 0 := by
  have hc' := (normalizedMaxCurve_forward_of_constraint hc ht).2.1
  change fderiv ℝ projectiveActiveWall (normalizedMaxCurve x t₀ t)
    (normalizedField (normalizedMaxCurve x t₀ t)) < 0
  rw [projectiveActiveWall_fderiv_field (ne_of_gt hA) hc']
  let y := toProjectiveState (normalizedMaxCurve x t₀ t)
  have heq : activeVelocity (y 0) (y 1) (y 2) (y 3) = -exitClockRate y * y 2 := by
    dsimp only [activeVelocity, exitClockRate]
    ring
  have hD : 0 < exitClockRate y := by
    have H := exitPhysicalRegion_clock hh hy
    change 1 / 2 ≤ exitClockRate y at H
    linarith only [H]
  change (1 + normalizedMaxCurve x t₀ t 0) * activeVelocity (y 0) (y 1) (y 2) (y 3) < 0
  rw [heq]
  exact mul_neg_of_pos_of_neg hA (mul_neg_of_neg_of_pos (neg_neg_of_pos hD)
    (hh.trans_le hy.2.2.2.1.1))

/-- A completed tail crosses its lower height exactly once and has no earlier hit. -/
theorem normalized_exit_first_hit {x : NormalizedState} {t₀ s t h : ℝ}
    (hc : stateConstraint x = 1) (hh : 0 < h) (hs : t₀ ≤ s) (hst : s < t)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    (∀ u ∈ Icc s t, exitPhysicalRegion h (β u)) → β t 2 = h →
    IsLeast {u | s < u ∧ u ∈ normalizedMaxDomain x t₀ ∧ β u 2 = h} t ∧
      StrictAntiOn (fun u => β u 2) (Icc s t) ∧ (∀ u ∈ Ico s t, h < β u 2) ∧
      (∀ u ∈ Icc s t, normalizedEventRate projectiveActiveWall x t₀ u < 0) := by
  intro β hreg hhit
  have hdom (u : ℝ) (hu : u ∈ Icc s t) :=
    normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hu.1)
  have hrate (u : ℝ) (hu : u ∈ Icc s t) :=
    normalized_exit_active_rate_neg hc hh (hs.trans hu.1) (hA u hu) (hreg u hu)
  have hderiv (u : ℝ) (hu : u ∈ Icc s t) :
      HasDerivAt (fun v => β v 2) (normalizedEventRate projectiveActiveWall x t₀ u) u := by
    exact ((contDiffAt_projectiveActiveWall 1 (ne_of_gt (hA u hu))).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt u (hasDerivAt_normalizedMaxCurve (hdom u hu))
  have hanti : StrictAntiOn (fun u => β u 2) (Icc s t) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (HasDerivAt.continuousOn hderiv)
    intro u hu
    rw [(hderiv u (interior_subset hu)).deriv]
    exact hrate u (interior_subset hu)
  have htmem : t ∈ Icc s t := ⟨hst.le, le_rfl⟩
  refine ⟨⟨⟨hst, hdom t htmem, hhit⟩, ?_⟩, hanti, ?_, hrate⟩
  · intro u hu
    by_contra hn
    have hut : u < t := lt_of_not_ge hn
    have H := hanti ⟨hu.1.le, hut.le⟩ htmem hut
    change β t 2 < β u 2 at H
    rw [hhit, hu.2.2] at H
    exact lt_irrefl _ H
  · intro u hu
    have H := hanti ⟨hu.1, hu.2.le⟩ htmem hu.2
    change β t 2 < β u 2 at H
    rwa [hhit] at H

end BianchiIX
