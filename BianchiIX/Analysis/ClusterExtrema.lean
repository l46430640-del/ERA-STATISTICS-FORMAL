import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.Linarith

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

theorem limsup_eq_of_cluster_upper {α : Type*} {l : Filter α} [NeBot l]
    {f g : α → ℝ} {a : ℝ} (hc : MapClusterPt a l f)
    (hg : Tendsto g l (𝓝 a)) (hfg : f ≤ᶠ[l] g) : limsup f l = a := by
  have hco : l.IsCoboundedUnder (· ≤ ·) f :=
    IsCoboundedUnder.of_frequently_ge ((hc.frequently
      (eventually_gt_nhds (show a - 1 < a by linarith))).mono fun _ h => h.le)
  exact le_antisymm ((limsup_le_limsup hfg hco hg.isBoundedUnder_le).trans_eq hg.limsup_eq)
    (hc.le_limsup (hg.isBoundedUnder_le.mono_le hfg))

theorem liminf_eq_of_cluster_lower {α : Type*} {l : Filter α} [NeBot l]
    {f : α → ℝ} {a : ℝ} (hc : MapClusterPt a l f)
    (hlo : ∀ᶠ t in l, a ≤ f t) : liminf f l = a := by
  have hco : l.IsCoboundedUnder (· ≥ ·) f :=
    IsCoboundedUnder.of_frequently_le ((hc.frequently
      (eventually_lt_nhds (show a < a + 1 by linarith))).mono fun _ h => h.le)
  exact le_antisymm (hc.liminf_le ⟨a, hlo⟩) (le_liminf_of_le hco hlo)

end BianchiIX
