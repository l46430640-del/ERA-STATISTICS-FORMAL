import BianchiIX.Dynamics.TaubBoundaryArc
import BianchiIX.Dynamics.OmegaFlowInvariant
import BianchiIX.Analysis.ImplicitEvent

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The nonzero scalar velocity gives actual signed travel times to every nearby point of the arc. -/
theorem exists_taubBoundaryArc_local_times {q : ℝ} (hq : q ∈ Ioo (-1) 1) :
    ∃ τ : ℝ → ℝ, τ q = 0 ∧ ∀ᶠ r in 𝓝 q,
      τ r ∈ normalizedMaxDomain (taubBoundaryArc q) 0 ∧
        normalizedMaxCurve (taubBoundaryArc q) 0 (τ r) = taubBoundaryArc r := by
  let Q : ℝ × ℝ → ℝ := fun p => -normalizedMaxCurve (taubBoundaryArc q) 0 p.2 0 - p.1
  have hpair : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => (taubBoundaryArc q, p.2)) (q, 0) :=
    contDiffAt_const.prodMk contDiffAt_snd
  have hstate := (contDiffAt_normalizedMaxCurve_two (initial_mem_normalizedMaxDomain (taubBoundaryArc q) 0)).comp (q, 0) hpair
  have hQ : ContDiffAt ℝ 2 Q (q, 0) :=
    ((contDiffAt_apply ℝ ℝ (0 : Fin 5) _).comp (q, 0) hstate).neg.sub contDiffAt_fst
  have hd : HasDerivAt (fun s => Q (q, s)) ((q + 2) * (1 - q ^ 2)) 0 := by
    have H := (hasDerivAt_taubBoundaryArc_parameter hq (initial_mem_normalizedMaxDomain (taubBoundaryArc q) 0)).sub_const q
    have heval : -normalizedMaxCurve (taubBoundaryArc q) 0 0 0 = q := by
      simp only [normalizedMaxCurve_initial, taubBoundaryArc, Matrix.cons_val_zero, neg_neg]
    change HasDerivAt (fun s => -normalizedMaxCurve (taubBoundaryArc q) 0 s 0 - q) _ 0
    simpa only [heval] using! H
  have ha : 0 < (q + 2) * (1 - q ^ 2) := mul_pos (by linarith only [hq.1]) (by nlinarith [hq.1, hq.2])
  obtain ⟨τ, hτ, hreg, _, hhit, _⟩ := exists_scalar_event_branch_two hQ hd ha.ne'
  have hdom : ∀ᶠ r in 𝓝 q, τ r ∈ normalizedMaxDomain (taubBoundaryArc q) 0 :=
    hreg.continuousAt.eventually ((isOpen_normalizedMaxDomain (taubBoundaryArc q) 0).mem_nhds
      (hτ.symm ▸ initial_mem_normalizedMaxDomain (taubBoundaryArc q) 0))
  refine ⟨τ, hτ, ?_⟩
  filter_upwards [hdom, hhit] with r hr he
  have hparam : -normalizedMaxCurve (taubBoundaryArc q) 0 (τ r) 0 = r := by
    have hzero : Q (q, 0) = 0 := by
      simp only [Q, normalizedMaxCurve_initial, taubBoundaryArc, Matrix.cons_val_zero, neg_neg, sub_self]
    rw [hzero] at he
    exact sub_eq_zero.mp he
  exact ⟨hr, (taubBoundaryArc_flow hq hr).2.trans (congrArg taubBoundaryArc hparam)⟩

/-- A closed invariant limit set containing one interior point contains the entire connected arc. -/
theorem taubBoundaryArc_mem_omegaLimit_of_one {x : NormalizedState} {q : ℝ}
    (hc : stateConstraint x = 1) (hq : q ∈ Ioo (-1) 1)
    (hz : taubBoundaryArc q ∈ normalizedOmegaLimit x) :
    ∀ r ∈ Ioo (-1 : ℝ) 1, taubBoundaryArc r ∈ normalizedOmegaLimit x := by
  let S := taubBoundaryArc ⁻¹' normalizedOmegaLimit x
  let U := Ioo (-1 : ℝ) 1 ∩ S
  have hS : IsClosed S := (isClosed_normalizedOmegaLimit x).preimage continuous_taubBoundaryArc
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro r hr
    obtain ⟨τ, _, Hτ⟩ := exists_taubBoundaryArc_local_times hr.1
    filter_upwards [isOpen_Ioo.mem_nhds hr.1, Hτ] with s hs htime
    refine ⟨hs, ?_⟩
    change taubBoundaryArc s ∈ normalizedOmegaLimit x
    rw [← htime.2]
    exact normalizedOmegaLimit_flow hc hr.2 htime.1
  have hcl : closure U ∩ Ioo (-1 : ℝ) 1 ⊆ U := by
    intro r hr
    exact ⟨hr.2, closure_minimal inter_subset_right hS hr.1⟩
  have H := (convex_Ioo (-1 : ℝ) 1).isPreconnected.subset_of_closure_inter_subset hU
    ⟨q, hq, hq, hz⟩ hcl
  exact fun r hr => (H hr).2

theorem taubBoundaryArc_closed_mem_omegaLimit {x : NormalizedState} {q : ℝ}
    (hc : stateConstraint x = 1) (hq : q ∈ Ioo (-1) 1)
    (hz : taubBoundaryArc q ∈ normalizedOmegaLimit x) :
    ∀ r ∈ Icc (-1 : ℝ) 1, taubBoundaryArc r ∈ normalizedOmegaLimit x := by
  have H : closure (Ioo (-1 : ℝ) 1) ⊆ taubBoundaryArc ⁻¹' normalizedOmegaLimit x :=
    closure_minimal (taubBoundaryArc_mem_omegaLimit_of_one hc hq hz)
      ((isClosed_normalizedOmegaLimit x).preimage continuous_taubBoundaryArc)
  rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1)] at H
  exact H

end BianchiIX
