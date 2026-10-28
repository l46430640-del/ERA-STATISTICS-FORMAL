import BianchiIX.Dynamics.FlowTransport
import BianchiIX.Dynamics.ForwardComplete

noncomputable section

namespace BianchiIX

open Set

theorem normalizedMaxCurve_injOn (t₀ t : ℝ) :
    InjOn (fun x => normalizedMaxCurve x t₀ t) {x | t ∈ normalizedMaxDomain x t₀} := by
  intro x hx y hy heq
  dsimp only at heq
  have hx' := normalizedMaxCurve_rebase hx (initial_mem_normalizedMaxDomain x t₀)
  have hy' := normalizedMaxCurve_rebase hy (initial_mem_normalizedMaxDomain y t₀)
  rw [normalizedMaxCurve_initial] at hx' hy'
  rw [← hx', ← hy', heq]

/-- Equal endpoints at different forward times determine an intermediate point of the longer orbit. -/
theorem normalizedMaxCurve_eq_at_time_difference {x y : NormalizedState} {t₀ s t : ℝ}
    (hxpos : positiveWalls x) (hxcon : stateConstraint x = 1)
    (hypos : positiveWalls y) (hycon : stateConstraint y = 1)
    (hs : t₀ ≤ s) (hst : s ≤ t)
    (heq : normalizedMaxCurve x t₀ s = normalizedMaxCurve y t₀ t) :
    normalizedMaxCurve y t₀ (t₀ + (t - s)) = x := by
  have hu := normalizedMaxDomain_contains_Ici hypos hycon t₀
    (show t₀ ≤ t₀ + (t - s) by linarith)
  have ht := normalizedMaxDomain_contains_Ici hypos hycon t₀ (hs.trans hst)
  have hp := (maximalNormalizedSolution y t₀).physical hypos hycon hu
  apply normalizedMaxCurve_injOn t₀ s
    (normalizedMaxDomain_contains_Ici hp.1 hp.2 t₀ hs)
    (normalizedMaxDomain_contains_Ici hxpos hxcon t₀ hs)
  have H := normalizedMaxCurve_shift hu (show s + (t - s) ∈ normalizedMaxDomain y t₀ by
    simpa using ht)
  convert! H.trans (by simpa using heq.symm) using 1

end BianchiIX
