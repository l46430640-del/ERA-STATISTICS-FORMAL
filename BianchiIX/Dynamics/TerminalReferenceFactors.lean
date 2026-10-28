import BianchiIX.Dynamics.CoreTailReferenceLimits
import BianchiIX.Dynamics.TerminalWallFactors

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem coreTail_reference_cycleDenom {k h : ℝ} (hk : 1 < k) (hh : 0 < h ∧ h < 1) :
    projectiveCycleDenom (coreTailState h ![k, 0, 0]) =
      (k - 2) ^ 2 + 4 * h ^ 2 / (k + Real.sqrt (k ^ 2 - h ^ 2)) := by
  rw [(coreTail_reference_regular hk hh).2.1]
  change axisCycleDenom (1 - exitTailGap k h) 0 h 0 = _
  rw [exitCycle_denom_split (lt_trans zero_lt_one hk)
    (by nlinarith only [hk, hh.1, hh.2] : h ^ 2 ≤ k ^ 2)]
  simp only [sub_self, zero_pow (by decide : 2 ≠ 0), add_zero, mul_zero, sub_zero, exitTailGap]

theorem terminal_reference_cycleDenom_normalized {α h : ℝ} (hα : 0 < α)
    (hh : 0 < h ∧ h < 1) :
    projectiveCycleDenom (coreTailState h ![2 + 2 * α, 0, 0]) / (4 * α ^ 2) =
      1 + (h / α) ^ 2 / (2 + 2 * α + Real.sqrt ((2 + 2 * α) ^ 2 - h ^ 2)) := by
  rw [coreTail_reference_cycleDenom (by linarith only [hα]) hh]
  have hd : 2 + 2 * α + Real.sqrt ((2 + 2 * α) ^ 2 - h ^ 2) ≠ 0 := by positivity
  field_simp
  ring

theorem tendsto_terminal_reference_cycleDenom {η : ℝ} (hη : 0 < η) {J : ℕ} (hJ : 2 ≤ J) :
    Tendsto (fun α : ℝ =>
      projectiveCycleDenom (coreTailState (η * α ^ J) ![2 + 2 * α, 0, 0]) / (4 * α ^ 2))
      (𝓝[>] 0) (𝓝 1) := by
  have H : Tendsto (fun α : ℝ => α) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hk : Tendsto (fun α : ℝ => 2 + 2 * α) (𝓝[>] 0) (𝓝 2) := by
    simpa using (H.const_mul 2).const_add 2
  have hh := tendsto_terminal_height η (show 1 ≤ J by omega)
  have hs : Tendsto (fun α : ℝ => Real.sqrt ((2 + 2 * α) ^ 2 - (η * α ^ J) ^ 2))
      (𝓝[>] 0) (𝓝 2) := by
    simpa [Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp ((hk.pow 2).sub (hh.pow 2))
  have hd : Tendsto (fun α : ℝ => 2 + 2 * α + Real.sqrt ((2 + 2 * α) ^ 2 - (η * α ^ J) ^ 2))
      (𝓝[>] 0) (𝓝 4) := by convert hk.add hs using 1; norm_num
  have HE := (((tendsto_terminal_height_div_phase η hJ).pow 2).div hd
    (by norm_num : (4 : ℝ) ≠ 0)).const_add 1
  simp only [zero_pow (by decide : 2 ≠ 0), zero_div, add_zero] at HE
  apply HE.congr'
  filter_upwards [eventually_terminal_reference_parameters hη (show 1 ≤ J by omega)] with α ha
  exact (terminal_reference_cycleDenom_normalized ha.1 ha.2.2).symm

theorem tendsto_terminal_reference_wallFactor {η : ℝ} (hη : 0 < η) {J : ℕ} (hJ : 2 ≤ J)
    (i : Fin 2) :
    Tendsto (fun α : ℝ => α ^ 2 * terminalWallFactor (η * α ^ J) ![2 + 2 * α, 0, 0] i)
      (𝓝[>] 0) (𝓝 taubMultiplierConstant) := by
  have HE := (tendsto_terminal_reference_multiplier hη (show 1 ≤ J by omega) i).div
    (tendsto_terminal_reference_cycleDenom hη hJ) (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at HE
  apply HE.congr'
  filter_upwards [eventually_terminal_reference_parameters hη (show 1 ≤ J by omega)] with α ha
  have hα : 0 < α := ha.1
  have hH : 0 < projectiveCycleDenom (coreTailState (η * α ^ J) ![2 + 2 * α, 0, 0]) := by
    rw [coreTail_reference_cycleDenom ha.2.1 ha.2.2]
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (by linarith only [ha.1])) (by positivity)
  dsimp only [Pi.div_apply, terminalWallFactor]
  field_simp

end BianchiIX
