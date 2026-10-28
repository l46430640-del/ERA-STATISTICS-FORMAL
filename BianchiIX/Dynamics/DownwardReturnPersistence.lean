import BianchiIX.Dynamics.DownwardReturnRestart

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- A strict below-section prefix transfers first-event selection itself to an ordinary neighborhood. -/
theorem partialCoreDownwardReturn_first_eventually_of_prefix {y : ProjectiveState} {S : ℝ}
    (hD : 0 < projectiveStateDenom y) (hS : 0 ≤ S)
    (hreg : ∀ t ∈ Icc 0 S, t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0 ∧
      projectiveOriginalFlow y 0 t 2 < 1)
    (Hnear : ∀ᶠ z in 𝓝 (projectiveOriginalFlow y 0 S),
      IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
        projectiveOriginalFlow z 0 t 2 = 1 ∧
        normalizedEventRate projectiveActiveWall (fromProjectiveState z) 0 t < 0}
        (partialCoreDownwardReturnTime z)) :
    ∀ᶠ z in 𝓝 y,
      IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
        projectiveOriginalFlow z 0 t 2 = 1 ∧
        normalizedEventRate projectiveActiveWall (fromProjectiveState z) 0 t < 0}
        (partialCoreDownwardReturnTime z) := by
  have hc := (hasFDerivAt_projectiveOriginalFlow_initial hD
    (hreg S ⟨hS, le_rfl⟩).1 (hreg S ⟨hS, le_rfl⟩).2.1).continuousAt
  filter_upwards [continuous_projectiveStateDenom.continuousAt.eventually (lt_mem_nhds hD),
    eventually_projectiveOriginalFlow_below_section hD hreg, hc.tendsto.eventually Hnear] with z hd hz hn
  have H := partialCoreDownwardReturn_restart hd hS (hz S ⟨hS, le_rfl⟩).1
    (fun t ht hhit => by
      have hv := (hz t ⟨ht.1.le, ht.2⟩).2
      rw [hhit] at hv
      exact (lt_irrefl _ hv).elim) hn
  rw [H.2.1]
  exact H.1

end BianchiIX
