import BianchiIX.Analysis.PowerWallLimits
import BianchiIX.Dynamics.TerminalWeakProductBounds
import BianchiIX.Dynamics.TerminalWallFactorLimits

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def terminalEqualWallInitial (J : ℕ) (c α : ℝ) : ExitTailState :=
  ![2 + 2 * α, c * α ^ (2 * J + 1), c * α ^ (2 * J + 1)]

theorem tendsto_terminal_equal_wall_factor {η c : ℝ} (hη : 0 < η ∧ η ≤ 1 / 100)
    (hc : 0 < c) {J : ℕ} (hJ : 2 ≤ J) (i : Fin 2) :
    Tendsto (fun α : ℝ => α ^ 2 * terminalWallFactor (η * α ^ J) (terminalEqualWallInitial J c α) i)
      (𝓝[>] 0) (𝓝 taubMultiplierConstant) := by
  obtain ⟨ε, hε, HL⟩ := exists_terminalWallFactor_limits hη hJ
  have HB : ∀ᶠ α : ℝ in 𝓝[>] 0,
      |c * α ^ (2 * J + 1)| + |c * α ^ (2 * J + 1)| ≤ ε * α ^ (2 * J) :=
    (eventually_equal_wall_budget hc hε J).mono fun _ ha => ha.2.2.2.2.trans ha.2.2.2.1
  exact (HL (fun α => c * α ^ (2 * J + 1)) (fun α => c * α ^ (2 * J + 1)) HB i).2

theorem eventually_terminal_equal_wall_product {η c : ℝ} (hη : 0 < η ∧ η ≤ 1 / 40000)
    (hc : 0 < c) {J : ℕ} (hJ : 2 ≤ J) :
    ∀ᶠ α : ℝ in 𝓝[>] 0,
      let Y := terminalEqualWallInitial J c α
      let h := η * α ^ J
      let v := terminalCyclicInput h Y 2
      coreTailValid h Y ∧ (0 < v ∧ v < 1) ∧
        terminalConnectionState h Y 3 =
          (c * α ^ (2 * J + 1)) ^ 2 * (terminalWallFactor h Y 0 * terminalWallFactor h Y 1) *
            Real.exp (terminalWeakProductExponent h Y) ∧
        |terminalWeakProductExponent h Y| ≤ 8 * α * (-Real.log v) := by
  obtain ⟨ε, hε, HB⟩ := exists_terminal_weak_product_bound hη hJ
  filter_upwards [eventually_equal_wall_budget hc hε J] with α ha
  have H := HB η α (2 * c * α ^ (2 * J + 1)) (c * α ^ (2 * J + 1)) (c * α ^ (2 * J + 1))
    le_rfl hη.2 ha.1 ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2 ha.2.1 ha.2.1
  simpa only [terminalEqualWallInitial, pow_two] using H

theorem tendsto_terminal_equal_wall_active_profile {η c : ℝ} (hη : 0 < η ∧ η ≤ 1 / 40000)
    (hc : 0 < c) {J : ℕ} (hJ : 2 ≤ J) :
    Tendsto (fun α : ℝ => terminalCyclicInput (η * α ^ J) (terminalEqualWallInitial J c α) 2 /
      α ^ (2 * J - 1)) (𝓝[>] 0) (𝓝 (c * taubMultiplierConstant)) := by
  have hη100 : 0 < η ∧ η ≤ 1 / 100 := ⟨hη.1, by linarith only [hη.2]⟩
  have HT := (tendsto_terminal_equal_wall_factor hη100 hc hJ 1).const_mul c
  apply HT.congr'
  filter_upwards [eventually_terminal_equal_wall_product hη hc hJ,
    show ∀ᶠ α : ℝ in 𝓝[>] 0, 0 < α from self_mem_nhdsWithin] with α ha hα
  have HF := (terminalEntranceInput_wall_factors ha.1).2.1
  change terminalCyclicInput (η * α ^ J) (terminalEqualWallInitial J c α) 2 =
    c * α ^ (2 * J + 1) * terminalWallFactor (η * α ^ J) (terminalEqualWallInitial J c α) 1 at HF
  rw [HF]
  have hp : α ^ (2 * J + 1) = α ^ (2 * J - 1) * α ^ 2 := by
    rw [← pow_add, show 2 * J - 1 + 2 = 2 * J + 1 by omega]
  rw [hp]
  field_simp

theorem tendsto_terminal_equal_wall_exponent {η c : ℝ} (hη : 0 < η ∧ η ≤ 1 / 40000)
    (hc : 0 < c) {J : ℕ} (hJ : 2 ≤ J) :
    Tendsto (fun α : ℝ => terminalWeakProductExponent (η * α ^ J) (terminalEqualWallInitial J c α))
      (𝓝[>] 0) (𝓝 0) := by
  let v := fun α => terminalCyclicInput (η * α ^ J) (terminalEqualWallInitial J c α) 2
  have HL : Tendsto (fun α : ℝ => α * Real.log (v α)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_phase_log_of_power_profile (mul_pos hc taubMultiplierConstant_pos) (2 * J - 1)
      (tendsto_terminal_equal_wall_active_profile hη hc hJ)
  have HG : Tendsto (fun α : ℝ => 8 * α * (-Real.log (v α))) (𝓝[>] 0) (𝓝 0) := by
    have H := HL.const_mul (-8)
    simp only [mul_zero] at H
    apply H.congr'
    exact Eventually.of_forall fun α => by ring
  apply squeeze_zero_norm' _ HG
  filter_upwards [eventually_terminal_equal_wall_product hη hc hJ] with α ha
  simpa only [Real.norm_eq_abs] using ha.2.2.2

/-- The value asymptotic in (D.39) concerns the actual completed Einstein connection. -/
theorem tendsto_terminal_equal_wall_weak_output {η c : ℝ} (hη : 0 < η ∧ η ≤ 1 / 40000)
    (hc : 0 < c) {J : ℕ} (hJ : 2 ≤ J) :
    Tendsto (fun α : ℝ => α ^ 4 * terminalConnectionState (η * α ^ J) (terminalEqualWallInitial J c α) 3 /
      (c * α ^ (2 * J + 1)) ^ 2) (𝓝[>] 0) (𝓝 (taubMultiplierConstant ^ 2)) := by
  have hη100 : 0 < η ∧ η ≤ 1 / 100 := ⟨hη.1, by linarith only [hη.2]⟩
  have HE := Real.continuous_exp.continuousAt.tendsto.comp (tendsto_terminal_equal_wall_exponent hη hc hJ)
  simp only [Real.exp_zero] at HE
  have HT := ((tendsto_terminal_equal_wall_factor hη100 hc hJ 0).mul
    (tendsto_terminal_equal_wall_factor hη100 hc hJ 1)).mul HE
  rw [mul_one, ← pow_two] at HT
  apply HT.congr'
  filter_upwards [eventually_terminal_equal_wall_product hη hc hJ,
    show ∀ᶠ α : ℝ in 𝓝[>] 0, 0 < α from self_mem_nhdsWithin] with α ha hα
  dsimp only [Function.comp_def]
  rw [ha.2.2.1]
  field_simp

end BianchiIX
