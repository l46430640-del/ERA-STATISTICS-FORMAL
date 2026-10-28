import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

namespace BianchiIX

/-- The two relative radius errors combine before taking reciprocal phases. -/
theorem two_stage_radius_response {k μ dk df dg : ℝ} (hk : 0 < k) (hμ : k / 2 ≤ μ)
    (hdk : dk ≠ 0) (hdf : df ≠ 0) (hf : |df / dk| ≤ 5 / 4)
    (hcore : |df / dk - 1| ≤ 1 / (32 * k))
    (hconn : |dg / df - 1| ≤ 1 / (4 * μ)) :
    |dg - dk| ≤ |dk| / k := by
  have hμ0 : 0 < μ := (half_pos hk).trans_le hμ
  have hcore' : |df - dk| ≤ (1 / (32 * k)) * |dk| := by
    rw [div_sub_one hdk, abs_div] at hcore
    exact (div_le_iff₀ (abs_pos.mpr hdk)).mp hcore
  have hconn' : |dg - df| ≤ (1 / (4 * μ)) * |df| := by
    rw [div_sub_one hdf, abs_div] at hconn
    exact (div_le_iff₀ (abs_pos.mpr hdf)).mp hconn
  have hf' : |df| ≤ (5 / 4) * |dk| := by
    rw [abs_div] at hf
    exact (div_le_iff₀ (abs_pos.mpr hdk)).mp hf
  have hden : 1 / (4 * μ) ≤ 1 / (2 * k) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith only [hμ])
  calc
    _ ≤ |dg - df| + |df - dk| := abs_sub_le dg df dk
    _ ≤ (1 / (4 * μ)) * |df| + (1 / (32 * k)) * |dk| := add_le_add hconn' hcore'
    _ ≤ (1 / (2 * k)) * ((5 / 4) * |dk|) + (1 / (32 * k)) * |dk| := by gcongr
    _ = (21 / 32) * (|dk| / k) := by ring
    _ ≤ _ := mul_le_of_le_one_left (div_nonneg (abs_nonneg _) hk.le) (by norm_num)

end BianchiIX
