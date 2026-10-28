import BianchiIX.Dynamics.TaubDistance
import BianchiIX.Dynamics.FlowTransport
import BianchiIX.Dynamics.PhysicalEntranceData
import Mathlib.Topology.ClusterPt

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def normalizedOmegaLimit (x : NormalizedState) : Set NormalizedState :=
  {z | MapClusterPt z atTop (normalizedMaxCurve x 0)}

theorem isClosed_normalizedOmegaLimit (x : NormalizedState) : IsClosed (normalizedOmegaLimit x) :=
  isClosed_setOfPred_clusterPt

theorem mem_normalizedOmegaLimit_of_sequence {x z : NormalizedState} {c : ℕ → ℝ}
    (hc : Tendsto c atTop atTop)
    (hz : Tendsto (fun n => normalizedMaxCurve x 0 (c n)) atTop (𝓝 z)) :
    z ∈ normalizedOmegaLimit x :=
  MapClusterPt.of_comp hc hz.mapClusterPt

theorem normalizedOmegaLimit_late_visit {x z : NormalizedState} (hz : z ∈ normalizedOmegaLimit x) :
    ∀ ε > (0 : ℝ), ∀ R : ℝ, ∃ t ≥ R,
      normalizedEuclideanDistance (normalizedMaxCurve x 0 t) z < ε := by
  change MapClusterPt z atTop (normalizedMaxCurve x 0) at hz
  generalize normalizedMaxCurve x 0 = f at hz ⊢
  intro ε hε R
  have hpair : Continuous (fun y : NormalizedState => (y, z)) := continuous_id.prodMk continuous_const
  have hcont : Continuous (fun y => normalizedEuclideanDistance y z) := by
    convert continuous_normalizedEuclideanDistance.comp hpair using 1
    rfl
  have hn : {y | normalizedEuclideanDistance y z < ε} ∈ 𝓝 z :=
    (isOpen_lt hcont continuous_const).mem_nhds (by
      change normalizedEuclideanDistance z z < ε
      simpa only [normalizedEuclideanDistance, dist_self] using hε)
  have hf : ∃ᶠ t : ℝ in atTop, normalizedEuclideanDistance (f t) z < ε := hz.frequently hn
  obtain ⟨t, ht, hR⟩ := (hf.and_eventually (eventually_ge_atTop R)).exists
  exact ⟨t, hR, ht⟩

theorem normalizedOmegaLimit_symmetry (A : NormalizedSymmetry) {x z : NormalizedState}
    (hc : stateConstraint x = 1) (hz : z ∈ normalizedOmegaLimit x) :
    A.map z ∈ normalizedOmegaLimit (A.map x) := by
  have H := (show MapClusterPt z atTop (normalizedMaxCurve x 0) from hz).continuousAt_comp A.map.continuous.continuousAt
  apply H.congrFun
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact (A.maxCurve (normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht)).symm

theorem mem_normalizedOmegaLimit_of_late_visit {x z : NormalizedState}
    (H : ∀ ε > (0 : ℝ), ∀ R : ℝ, ∃ t ≥ R,
      normalizedEuclideanDistance (normalizedMaxCurve x 0 t) z < ε) :
    z ∈ normalizedOmegaLimit x := by
  choose c hc hd using (fun n : ℕ => H (1 / ((n : ℝ) + 1)) (by positivity) n)
  have ht : Tendsto c atTop atTop := tendsto_atTop_mono hc tendsto_natCast_atTop_atTop
  apply mem_normalizedOmegaLimit_of_sequence ht
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n =>
    (normalizedState_norm_sub_le_euclidean _ _).trans (hd n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

end BianchiIX
