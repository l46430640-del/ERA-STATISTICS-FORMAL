import BianchiIX.Dynamics.TerminalWeakDirectionalBounds
import BianchiIX.Dynamics.TerminalWeakOutputLimits

noncomputable section

namespace BianchiIX

open Filter Set
open scoped Topology

theorem tendsto_equal_wall_sqrt_div_phase (c : ℝ) {J : ℕ} (hJ : 1 ≤ J) :
    Tendsto (fun α : ℝ => Real.sqrt (c * α ^ (2 * J + 1)) / α) (𝓝[>] 0) (𝓝 0) := by
  have H : Tendsto (fun α : ℝ => α) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have HP : Tendsto (fun α : ℝ => c * α ^ (2 * J - 1)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_pow (by omega : 2 * J - 1 ≠ 0), mul_zero] using (H.pow (2 * J - 1)).const_mul c
  have HS := Real.continuous_sqrt.continuousAt.tendsto.comp HP
  simp only [Real.sqrt_zero] at HS
  apply HS.congr'
  filter_upwards [show ∀ᶠ α : ℝ in 𝓝[>] 0, 0 < α from self_mem_nhdsWithin] with α hα
  have hp : c * α ^ (2 * J + 1) = α ^ 2 * (c * α ^ (2 * J - 1)) := by
    rw [show 2 * J + 1 = 2 + (2 * J - 1) by omega, pow_add]
    ring
  dsimp only [Function.comp_def]
  rw [hp, Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq hα.le, mul_div_cancel_left₀ _ hα.ne']

/-- The normalized ordinary weak response tends to one along the positive equal-wall path. -/
theorem exists_terminal_equal_wall_weak_response_limits :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η c : ℝ, (0 < η ∧ η ≤ δ) → 0 < c →
      ∀ J : ℕ, 2 ≤ J →
      (∀ᶠ α : ℝ in 𝓝[>] 0,
        let Y := terminalEqualWallInitial J c α
        let h := η * α ^ J
        ContDiffAt ℝ 2 (terminalConnectionState h) Y ∧
          0 < terminalConnectionState h Y 1 ∧ 0 < terminalConnectionState h Y 3) ∧
      Tendsto (fun α : ℝ => Real.sqrt (c * α ^ (2 * J + 1)) *
        fderiv ℝ (terminalConnectionLogWalls (η * α ^ J)) (terminalEqualWallInitial J c α)
          (terminalSharpWeakDirection (c * α ^ (2 * J + 1))) 1) (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨δ, hδ, hδhi, HB⟩ := exists_terminal_weak_directional_error
  refine ⟨δ, hδ, hδhi, ?_⟩
  intro η c hη hc J hJ
  obtain ⟨C, hC, ε, hε, HC⟩ := HB η hη J hJ
  let u := fun α : ℝ => c * α ^ (2 * J + 1)
  let Y := terminalEqualWallInitial J c
  let L := fun α : ℝ => -Real.log (terminalEntranceInput (η * α ^ J) (Y α) 2)
  let f := fun α : ℝ => fderiv ℝ (terminalConnectionLogWalls (η * α ^ J)) (Y α)
    (terminalSharpWeakDirection (u α)) 1
  have HE : ∀ᶠ α : ℝ in 𝓝[>] 0,
      ContDiffAt ℝ 2 (terminalConnectionState (η * α ^ J)) (Y α) ∧
      0 < terminalConnectionState (η * α ^ J) (Y α) 1 ∧
      0 < terminalConnectionState (η * α ^ J) (Y α) 3 ∧
      |f α - 1 / Real.sqrt (u α)| ≤ C * (L α + 1 / α) := by
    filter_upwards [eventually_equal_wall_budget hc hε J] with α ha
    have H := HC η α (2 * c * α ^ (2 * J + 1)) (u α) (u α)
      le_rfl hη.2 ha.1 ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2 ha.2.1 ha.2.1
    exact ⟨H.2.1, H.2.2.1, H.2.2.2.1, H.2.2.2.2.2⟩
  refine ⟨HE.mono (fun _ ha => ⟨ha.1, ha.2.1, ha.2.2.1⟩), ?_⟩
  have hη' : 0 < η ∧ η ≤ 1 / 40000 := ⟨hη.1, hη.2.trans hδhi⟩
  have HL : Tendsto (fun α : ℝ => α * L α) (𝓝[>] 0) (𝓝 0) := by
    have H := (tendsto_phase_log_of_power_profile (mul_pos hc taubMultiplierConstant_pos) (2 * J - 1)
      (tendsto_terminal_equal_wall_active_profile hη' hc hJ)).neg
    simp only [neg_zero] at H
    apply H.congr'
    exact Eventually.of_forall fun α => by
      change -(α * Real.log (terminalCyclicInput (η * α ^ J) (terminalEqualWallInitial J c α) 2)) =
        α * (-Real.log (terminalCyclicInput (η * α ^ J) (terminalEqualWallInitial J c α) 2))
      ring
  have HS := tendsto_equal_wall_sqrt_div_phase c (show 1 ≤ J by omega)
  have HG : Tendsto (fun α : ℝ => Real.sqrt (u α) * (C * (L α + 1 / α))) (𝓝[>] 0) (𝓝 0) := by
    have H := (HS.mul (HL.add_const 1)).const_mul C
    simp only [zero_add, zero_mul, mul_zero] at H
    apply H.congr'
    filter_upwards [show ∀ᶠ α : ℝ in 𝓝[>] 0, 0 < α from self_mem_nhdsWithin] with α hα
    dsimp only [u, Function.comp_def]
    field_simp
  have Hdiff : Tendsto (fun α : ℝ => Real.sqrt (u α) * f α - 1) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' _ HG
    filter_upwards [HE, show ∀ᶠ α : ℝ in 𝓝[>] 0, 0 < α from self_mem_nhdsWithin] with α ha hα
    have hu : 0 < u α := mul_pos hc (pow_pos hα _)
    have hs : 0 < Real.sqrt (u α) := Real.sqrt_pos.2 hu
    rw [Real.norm_eq_abs, show Real.sqrt (u α) * f α - 1 =
      Real.sqrt (u α) * (f α - 1 / Real.sqrt (u α)) by field_simp,
      abs_mul, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_left ha.2.2.2 hs.le
  have H := Hdiff.add_const 1
  simpa only [sub_add_cancel, zero_add] using H

end BianchiIX
