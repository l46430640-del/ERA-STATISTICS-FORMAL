import BianchiIX.Analysis.ArcoshGap
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def taubMultiplierConstant : ℝ := (2 + Real.sqrt 3) / 4

theorem taubMultiplierConstant_pos : 0 < taubMultiplierConstant := by
  unfold taubMultiplierConstant
  positivity

theorem exp_arcosh_two_sub_log_four :
    Real.exp (Real.arcosh 2 - Real.log 4) = taubMultiplierConstant := by
  rw [Real.exp_sub, Real.arcosh]
  norm_num only [show (2 : ℝ) ^ 2 - 1 = 3 by norm_num]
  rw [Real.exp_log (by positivity), Real.exp_log (by norm_num)]
  rfl

theorem arcoshGap_log_split {k h : ℝ} (hk : 1 < k) (hh : 0 < h ∧ h < 1) :
    arcoshGap k h = Real.log (k + Real.sqrt (k ^ 2 - h ^ 2)) - Real.log h - Real.arcosh k := by
  unfold arcoshGap
  congr 1
  rw [Real.arcosh, sqrt_scaled_gap hk hh, ← add_div,
    Real.log_div (by positivity) hh.1.ne']

theorem tendsto_referenceTail_log_offset {ι : Type*} {l : Filter ι} {k h : ι → ℝ}
    (hk : Tendsto k l (𝓝 2)) (hh : Tendsto h l (𝓝 0)) :
    Tendsto (fun x => Real.arcosh (k x) - Real.log (k x + Real.sqrt (k x ^ 2 - h x ^ 2)))
      l (𝓝 (Real.arcosh 2 - Real.log 4)) := by
  have hsqrt : Tendsto (fun x => Real.sqrt (k x ^ 2 - h x ^ 2)) l (𝓝 2) := by
    simpa [Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp ((hk.pow 2).sub (hh.pow 2))
  have hsum : Tendsto (fun x => k x + Real.sqrt (k x ^ 2 - h x ^ 2)) l (𝓝 4) := by
    convert hk.add hsqrt using 1
    norm_num
  exact ((Real.hasDerivAt_arcosh (by norm_num : (2 : ℝ) ∈ Ioi 1)).continuousAt.tendsto.comp hk).sub
    ((Real.continuousAt_log (by norm_num : (4 : ℝ) ≠ 0)).tendsto.comp hsum)

theorem tendsto_terminal_height (η : ℝ) {J : ℕ} (hJ : 1 ≤ J) :
    Tendsto (fun α : ℝ => η * α ^ J) (𝓝[>] 0) (𝓝 0) := by
  have H : Tendsto (fun α : ℝ => α) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  simpa [zero_pow (by omega : J ≠ 0)] using (H.pow J).const_mul η

theorem tendsto_terminal_scaled_log_height {η : ℝ} (hη : η ≠ 0) (J : ℕ) :
    Tendsto (fun α : ℝ => α * Real.log (η * α ^ J)) (𝓝[>] 0) (𝓝 0) := by
  have H : Tendsto (fun α : ℝ => α) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have HL : Tendsto (fun α : ℝ => α * Real.log α) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one, mul_comm] using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  have HT := (H.mul_const (Real.log η)).add (HL.const_mul (J : ℝ))
  simp only [zero_mul, mul_zero, zero_add] at HT
  apply HT.congr'
  filter_upwards [show ∀ᶠ α : ℝ in 𝓝[>] 0, 0 < α from self_mem_nhdsWithin] with α hα
  rw [Real.log_mul hη (pow_ne_zero J hα.ne'), Real.log_pow]
  ring

theorem eventually_terminal_reference_parameters {η : ℝ} (hη : 0 < η) {J : ℕ} (hJ : 1 ≤ J) :
    ∀ᶠ α : ℝ in 𝓝[>] 0, 0 < α ∧ 1 < 2 + 2 * α ∧ 0 < η * α ^ J ∧ η * α ^ J < 1 := by
  filter_upwards [show ∀ᶠ α : ℝ in 𝓝[>] 0, 0 < α from self_mem_nhdsWithin,
    (tendsto_terminal_height η hJ).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with α hα hh
  exact ⟨hα, by linarith only [hα], mul_pos hη (pow_pos hα J), hh⟩

theorem tendsto_terminal_height_div_phase (η : ℝ) {J : ℕ} (hJ : 2 ≤ J) :
    Tendsto (fun α : ℝ => η * α ^ J / α) (𝓝[>] 0) (𝓝 0) := by
  apply (tendsto_terminal_height η (show 1 ≤ J - 1 by omega)).congr'
  filter_upwards [show ∀ᶠ α : ℝ in 𝓝[>] 0, 0 < α from self_mem_nhdsWithin] with α hα
  have hp : α ^ J = α ^ (J - 1) * α := by
    conv_lhs => rw [show J = (J - 1) + 1 by omega, pow_succ]
  rw [hp]
  field_simp

end BianchiIX
