import BianchiIX.Analysis.TerminalReferenceLimits

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem eventually_equal_wall_budget {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (J : ℕ) :
    ∀ᶠ α : ℝ in 𝓝[>] 0, (0 < α ∧ α ≤ 1) ∧ 0 < c * α ^ (2 * J + 1) ∧
      0 < 2 * c * α ^ (2 * J + 1) ∧
      2 * c * α ^ (2 * J + 1) ≤ ε * α ^ (2 * J) ∧
      |c * α ^ (2 * J + 1)| + |c * α ^ (2 * J + 1)| ≤ 2 * c * α ^ (2 * J + 1) := by
  have H : Tendsto (fun α : ℝ => α) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have HT : Tendsto (fun α : ℝ => 2 * c * α) (𝓝[>] 0) (𝓝 0) := by simpa using H.const_mul (2 * c)
  filter_upwards [show ∀ᶠ α : ℝ in 𝓝[>] 0, 0 < α from self_mem_nhdsWithin,
    H.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)), HT.eventually (gt_mem_nhds hε)] with α hα hα1 hs
  have hp : 0 < c * α ^ (2 * J + 1) := mul_pos hc (pow_pos hα _)
  refine ⟨⟨hα, hα1.le⟩, hp, by positivity, ?_, ?_⟩
  · have HB := mul_le_mul_of_nonneg_right hs.le (pow_nonneg hα.le (2 * J))
    rw [pow_succ]
    nlinarith only [HB]
  · rw [abs_of_pos hp]
    ring_nf
    rfl

/-- A positive power profile has subcritical logarithmic flight length. -/
theorem tendsto_phase_log_of_power_profile {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c) (p : ℕ)
    (hf : Tendsto (fun α : ℝ => f α / α ^ p) (𝓝[>] 0) (𝓝 c)) :
    Tendsto (fun α : ℝ => α * Real.log (f α)) (𝓝[>] 0) (𝓝 0) := by
  have H : Tendsto (fun α : ℝ => α) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have HL := (Real.continuousAt_log hc.ne').tendsto.comp hf
  have HA : Tendsto (fun α : ℝ => α * Real.log α) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one, mul_comm] using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  have HT := ((HA.const_mul (p : ℝ)).add (H.mul HL))
  simp only [mul_zero, zero_mul, zero_add] at HT
  apply HT.congr'
  filter_upwards [show ∀ᶠ α : ℝ in 𝓝[>] 0, 0 < α from self_mem_nhdsWithin,
    hf.eventually (lt_mem_nhds hc)] with α hα hpos
  have heq : α ^ p * (f α / α ^ p) = f α := by field_simp
  have hlog : Real.log (f α) = (p : ℝ) * Real.log α + Real.log (f α / α ^ p) := calc
    _ = Real.log (α ^ p * (f α / α ^ p)) := congrArg Real.log heq.symm
    _ = _ := by rw [Real.log_mul (pow_ne_zero p hα.ne') hpos.ne', Real.log_pow]
  dsimp only [Function.comp_def]
  rw [hlog]
  ring

end BianchiIX
