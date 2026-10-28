import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem deriv_nonpos_of_left_lower {f : ℝ → ℝ} {a b d : ℝ} (hab : a < b)
    (hf : HasDerivAt f d b) (hlower : ∀ t ∈ Ioo a b, f b ≤ f t) : d ≤ 0 := by
  apply le_of_tendsto (hf.tendsto_slope.mono_left (nhdsLT_le_nhdsNE b))
  filter_upwards [Ioo_mem_nhdsLT hab] with t ht
  rw [slope_def_field]
  exact div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hlower t ht)) (sub_nonpos.mpr ht.2.le)

theorem eventually_gt_right_of_deriv_pos {f : ℝ → ℝ} {a d : ℝ}
    (hf : HasDerivAt f d a) (hd : 0 < d) : ∀ᶠ t in 𝓝[>] a, f a < f t := by
  have H := (hf.tendsto_slope.mono_left (nhdsGT_le_nhdsNE a)).eventually
    (isOpen_Ioi.mem_nhds hd)
  filter_upwards [H, self_mem_nhdsWithin] with t ht hat
  rw [slope_def_field] at ht
  exact sub_pos.mp ((div_pos_iff_of_pos_right (sub_pos.mpr hat)).mp ht)

theorem eventually_lt_right_of_deriv_neg {f : ℝ → ℝ} {a d : ℝ}
    (hf : HasDerivAt f d a) (hd : d < 0) : ∀ᶠ t in 𝓝[>] a, f t < f a := by
  have H := eventually_gt_right_of_deriv_pos hf.neg (neg_pos.mpr hd)
  exact H.mono fun _ h => neg_lt_neg_iff.mp h

end BianchiIX
