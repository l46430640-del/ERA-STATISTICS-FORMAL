import BianchiIX.Dynamics.TerminalBoundaryReciprocal
import BianchiIX.Analysis.BoundarySlope

noncomputable section

namespace BianchiIX

open Filter Asymptotics Set
open scoped Topology

/-- The equal-wall boundary slope belongs to the actual terminal phase at the prescribed height. -/
theorem tendsto_terminal_phase_equal_wall_slope {α η : ℝ} {J : ℕ}
    (hα : 0 < α ∧ α ≤ 1) (hη : 0 < η ∧ η ≤ 1 / 40000) (hJ : 2 ≤ J) :
    Tendsto (fun t : ℝ =>
      (terminalConnectionPhase (η * α ^ J) ![2 + 2 * α, t, t] - 2 / α) / t)
      (𝓝[>] 0) (𝓝 (2 / ((2 + 2 * α) * α ^ 2))) := by
  let ξ := η * α ^ (J - 2)
  have hξ : 0 < ξ ∧ ξ ≤ 1 / 40000 :=
    ⟨mul_pos hη.1 (pow_pos hα.1 _),
      (mul_le_of_le_one_right hη.1.le (pow_le_one₀ hα.1.le hα.2)).trans hη.2⟩
  have HH : ξ * α ^ 2 = η * α ^ J := by
    dsimp only [ξ]
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hJ]
  have HT : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have HP : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t ∧ 0 < t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ⟨ht, ht⟩
  have H := (terminalConnectionPhase_reciprocal_boundary_expansion hα hξ HT HT HP).tendsto_div_nhds_zero
  rw [HH] at H
  have HS := (H.const_mul 2).add_const (2 / ((2 + 2 * α) * α ^ 2))
  simp only [mul_zero, zero_add] at HS
  apply HS.congr'
  filter_upwards [show ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t from self_mem_nhdsWithin] with t ht
  have hR : 2 + 2 * α ≠ 0 := by linarith only [hα.1]
  field_simp [ht.ne', hR, hα.1.ne']
  ring

/-- Along the equal-wall curve the derivative is the sum of the two ordinary amplitude columns. -/
theorem hasDerivAt_terminal_phase_equal_wall {h R t : ℝ}
    (hf : DifferentiableAt ℝ (terminalConnectionPhase h) ![R, t, t]) :
    HasDerivAt (fun s : ℝ => terminalConnectionPhase h ![R, s, s])
      (fderiv ℝ (terminalConnectionPhase h) ![R, t, t] (Pi.single 1 1) +
        fderiv ℝ (terminalConnectionPhase h) ![R, t, t] (Pi.single 2 1)) t := by
  have HL : HasDerivAt (fun s : ℝ => (![R, s, s] : ExitTailState))
      (Pi.single 1 1 + Pi.single 2 1) t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa using hasDerivAt_const t R
    · simpa using hasDerivAt_id' t
    · simpa using hasDerivAt_id' t
  simpa only [map_add, Function.comp_def] using hf.hasFDerivAt.comp_hasDerivAt t HL

end BianchiIX
