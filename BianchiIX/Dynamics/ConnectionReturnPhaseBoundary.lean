import BianchiIX.Dynamics.ConnectionReturnPhaseResponse
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

/-- Ordinary phase-error derivatives extend to the zero strong-wall boundary by the actual C2 return map. -/
theorem connectionReturn_phase_response_bounds_nonneg {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    |fderiv ℝ connectionReturnPhaseError p ![1, 0, 0]| ≤ 50000 * (p 1 + (p 2) ^ 2) / (p 0) ^ 2 ∧
    |fderiv ℝ connectionReturnPhaseError p ![0, 1, 0]| ≤ 50000 / p 0 ∧
    |fderiv ℝ connectionReturnPhaseError p ![0, 0, 1]| ≤ 50000 * (p 1 + p 2) / p 0 := by
  by_cases hpos : 0 < p 1
  · exact connectionReturn_phase_response_bounds hμ ⟨hpos, hu.2⟩ hw
  have hp1 : p 1 = 0 := le_antisymm (le_of_not_gt hpos) hu.1
  have hμ0 : 0 < p 0 := by linarith only [hμ]
  have hμne := ne_of_gt hμ0
  let ε : ℝ := (1 / 10000) / p 0
  have hε : 0 < ε := by dsimp [ε]; positivity
  let q : ℕ → ConnectionParameters := fun n => ![p 0, ε / ((n : ℝ) + 1), p 2]
  have hqU (n : ℕ) : 0 < q n 1 ∧ q n 1 ≤ (1 / 10000) / q n 0 := by
    change 0 < ε / ((n : ℝ) + 1) ∧ ε / ((n : ℝ) + 1) ≤ ε
    exact ⟨div_pos hε (by positivity), div_le_self hε.le (by have H : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith only [H])⟩
  have hq : Tendsto q atTop (𝓝 p) := by
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i
    · exact tendsto_const_nhds
    · have H := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ε
      simpa [q, hp1, div_eq_mul_inv] using H
    · exact tendsto_const_nhds
  have H (n : ℕ) := connectionReturn_phase_response_bounds (p := q n) hμ (hqU n) hw
  have hd (v : ConnectionParameters) : ContinuousAt (fun r => |fderiv ℝ connectionReturnPhaseError r v|) p :=
    (((contDiffAt_connectionReturnPhaseError hμ hu hw).continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const).abs
  have hRμ : ContinuousAt (fun r : ConnectionParameters => 50000 * (r 1 + (r 2) ^ 2) / (r 0) ^ 2) p := by
    fun_prop (disch := exact pow_ne_zero 2 hμne)
  have hRU : ContinuousAt (fun r : ConnectionParameters => 50000 / r 0) p := by
    exact continuousAt_const.div (continuous_apply (0 : Fin 3)).continuousAt hμne
  have hRW : ContinuousAt (fun r : ConnectionParameters => 50000 * (r 1 + r 2) / r 0) p := by
    fun_prop (disch := exact hμne)
  exact ⟨le_of_tendsto_of_tendsto' ((hd ![1, 0, 0]).tendsto.comp hq) (hRμ.tendsto.comp hq) (fun n => (H n).1),
    le_of_tendsto_of_tendsto' ((hd ![0, 1, 0]).tendsto.comp hq) (hRU.tendsto.comp hq) (fun n => (H n).2.1),
    le_of_tendsto_of_tendsto' ((hd ![0, 0, 1]).tendsto.comp hq) (hRW.tendsto.comp hq) (fun n => (H n).2.2)⟩

end BianchiIX
