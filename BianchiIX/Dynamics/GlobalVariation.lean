import BianchiIX.Dynamics.FlowDifferential

noncomputable section

namespace BianchiIX

open Set Filter Metric
open scoped Topology

theorem normalizedFlowDifferential_initial (x : NormalizedState) (t₀ : ℝ) :
    normalizedFlowDifferential x t₀ t₀ = ContinuousLinearMap.id ℝ NormalizedState := by
  simp [normalizedFlowDifferential, normalizedMaxCurve_initial]

/-- Differentiating the actual restart identity gives the variational cocycle. -/
theorem normalizedFlowDifferential_rebase {x : NormalizedState} {t₀ s t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) (ht : t ∈ normalizedMaxDomain x t₀) :
    (normalizedFlowDifferential (normalizedMaxCurve x t₀ s) s t).comp
      (normalizedFlowDifferential x t₀ s) = normalizedFlowDifferential x t₀ t := by
  have hst : t ∈ normalizedMaxDomain (normalizedMaxCurve x t₀ s) s := by
    rwa [normalizedMaxDomain_rebase hs]
  have hd := (hasFDerivAt_normalizedMaxCurve_initial hst).comp x
    (hasFDerivAt_normalizedMaxCurve_initial hs)
  have heq : (fun y => normalizedMaxCurve (normalizedMaxCurve y t₀ s) s t)
      =ᶠ[𝓝 x] (fun y => normalizedMaxCurve y t₀ t) := by
    have hc (u : ℝ) : ContinuousAt (fun y : NormalizedState => (y, u)) x := by fun_prop
    filter_upwards [(hc s).eventually ((isOpen_normalizedFlowDomain t₀).mem_nhds hs),
      (hc t).eventually ((isOpen_normalizedFlowDomain t₀).mem_nhds ht)] with y hys hyt
    exact normalizedMaxCurve_rebase hys hyt
  exact (hd.congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_normalizedMaxCurve_initial ht)

theorem normalizedFlowDifferential_inverse {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    (normalizedFlowDifferential (normalizedMaxCurve x t₀ t) t t₀).comp
        (normalizedFlowDifferential x t₀ t) = ContinuousLinearMap.id ℝ NormalizedState ∧
      (normalizedFlowDifferential x t₀ t).comp
        (normalizedFlowDifferential (normalizedMaxCurve x t₀ t) t t₀) =
          ContinuousLinearMap.id ℝ NormalizedState := by
  have ht₀ : t₀ ∈ normalizedMaxDomain (normalizedMaxCurve x t₀ t) t := by
    rw [normalizedMaxDomain_rebase ht]
    exact initial_mem_normalizedMaxDomain x t₀
  constructor
  · simpa only [normalizedFlowDifferential_initial] using
      normalizedFlowDifferential_rebase ht (initial_mem_normalizedMaxDomain x t₀)
  · have H := normalizedFlowDifferential_rebase ht₀
      (initial_mem_normalizedMaxDomain (normalizedMaxCurve x t₀ t) t)
    simpa only [normalizedMaxCurve_rebase ht (initial_mem_normalizedMaxDomain x t₀),
      normalizedMaxCurve_initial, normalizedFlowDifferential_initial] using H

/-- The time equation for the genuine initial-state derivative on the whole maximal interval. -/
theorem hasDerivAt_normalizedFlowDifferential {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    HasDerivAt (fun u => normalizedFlowDifferential x t₀ u)
      ((normalizedDifferential (normalizedMaxCurve x t₀ t)).comp
        (normalizedFlowDifferential x t₀ t)) t := by
  let z := normalizedMaxCurve x t₀ t
  obtain ⟨r, hr, ε, hε, J, _, _, hJ⟩ := exists_normalizedMaxCurve_local_derivative z t
  have hz : z ∈ ball z r := mem_ball_self hr
  have htt : t ∈ Ioo (t - ε) (t + ε) := by constructor <;> linarith
  have hd := ((hJ z hz).2.2 t htt).2.clm_comp
    (hasDerivAt_const t (normalizedFlowDifferential x t₀ t))
  have heq : (fun u => (J (z, u)).comp (normalizedFlowDifferential x t₀ t))
      =ᶠ[𝓝 t] (fun u => normalizedFlowDifferential x t₀ u) := by
    filter_upwards [Ioo_mem_nhds htt.1 htt.2,
      (isOpen_normalizedMaxDomain x t₀).mem_nhds ht] with u hu hdom
    have hJu : J (z, u) = normalizedFlowDifferential z t u :=
      ((hJ z hz).2.2 u hu).1.unique
        (hasFDerivAt_normalizedMaxCurve_initial ((hJ z hz).1 hu))
    rw [hJu]
    exact normalizedFlowDifferential_rebase ht hdom
  simpa only [(hJ z hz).2.1, normalizedMaxCurve_initial, ContinuousLinearMap.comp_id,
    ContinuousLinearMap.comp_zero, add_zero] using hd.congr_of_eventuallyEq heq.symm

end BianchiIX
