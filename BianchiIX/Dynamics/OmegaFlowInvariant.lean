import BianchiIX.Dynamics.NormalizedOmegaLimit
import BianchiIX.Dynamics.FlowSecondRegularity

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Every existing signed finite-time flow image of a limit point is again a limit point. -/
theorem normalizedOmegaLimit_flow {x z : NormalizedState} {t : ℝ}
    (hc : stateConstraint x = 1) (hz : z ∈ normalizedOmegaLimit x)
    (ht : t ∈ normalizedMaxDomain z 0) :
    normalizedMaxCurve z 0 t ∈ normalizedOmegaLimit x := by
  have hs : ContinuousAt (fun y : NormalizedState => (y, t)) z := continuousAt_id.prodMk continuousAt_const
  have hcont : ContinuousAt (fun y => normalizedMaxCurve y 0 t) z := by
    convert (contDiffAt_normalizedMaxCurve_two ht).continuousAt.comp_of_eq hs rfl using 1 <;> rfl
  have H := (show MapClusterPt z atTop (normalizedMaxCurve x 0) from hz).continuousAt_comp hcont
  have Heq : (fun u => normalizedMaxCurve (normalizedMaxCurve x 0 u) 0 t) =ᶠ[atTop]
      (fun u => normalizedMaxCurve x 0 (t + u)) := by
    filter_upwards [eventually_ge_atTop (max 0 (-t))] with u hu
    have hu0 : 0 ≤ u := (le_max_left _ _).trans hu
    have htu : 0 ≤ t + u := by linarith only [(le_max_right 0 (-t)).trans hu]
    have HF := normalizedMaxCurve_shift (t₀ := (0 : ℝ)) (t := t)
      (by simpa only [zero_add] using normalizedMaxDomain_contains_Ici_of_constraint hc 0 hu0)
      (normalizedMaxDomain_contains_Ici_of_constraint hc 0 htu)
    simpa only [zero_add] using HF
  have Hshift : MapClusterPt (normalizedMaxCurve z 0 t) atTop
      (fun u => normalizedMaxCurve x 0 (t + u)) := H.congrFun Heq
  have htrans : Tendsto (fun u : ℝ => t + u) atTop atTop := by
    simpa only [add_comm, id_eq] using tendsto_atTop_add_const_right atTop t
      (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  exact MapClusterPt.of_comp htrans Hshift

theorem closure_normalized_orbit_subset_omegaLimit {x z : NormalizedState}
    (hc : stateConstraint x = 1) (hz : z ∈ normalizedOmegaLimit x) :
    closure (normalizedMaxCurve z 0 '' normalizedMaxDomain z 0) ⊆ normalizedOmegaLimit x := by
  apply closure_minimal _ (isClosed_normalizedOmegaLimit x)
  rintro _ ⟨t, ht, rfl⟩
  exact normalizedOmegaLimit_flow hc hz ht

end BianchiIX
