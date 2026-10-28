import BianchiIX.Algebra.StableResidualProfileBounds
import BianchiIX.Analysis.ReciprocalProfileBounds

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

theorem stableResidualCoefficient_reciprocal (i : Fin 4) {y : Fin 2 → ℝ} (hy : 1 < y 0) :
    stableResidualCoefficient i y = reciprocalParameter y * stableResidualProfile i (reciprocalParameterMap y) := by
  change _ = (y 0 + 1)⁻¹ * stableResidualProfile i ![(y 0 + 1)⁻¹, y 1]
  rw [← stableResidualCoefficient_compactification i hy]
  congr 1
  ext j
  fin_cases j <;> rfl

theorem stableResidualCoefficient_eventually_reciprocal (i : Fin 4) {y : Fin 2 → ℝ} (hy : 1 < y 0) :
    stableResidualCoefficient i =ᶠ[𝓝 y]
      (fun z => reciprocalParameter z * stableResidualProfile i (reciprocalParameterMap z)) := by
  filter_upwards [(continuous_apply 0).continuousAt.eventually (isOpen_Ioi.mem_nhds hy)] with z hz
  exact stableResidualCoefficient_reciprocal i hz

theorem exists_stableResidualCoefficient_derivative_bounds :
    ∃ C > (0 : ℝ), ∀ y : Fin 2 → ℝ, 3 / 2 ≤ y 0 → |y 1| ≤ 1 → ∀ i : Fin 4,
      ContDiffAt ℝ 2 (stableResidualCoefficient i) y ∧
        |stableResidualCoefficient i y| ≤ C / (y 0 + 1) ∧
        ‖fderiv ℝ (stableResidualCoefficient i) y‖ ≤ C / (y 0 + 1) ∧
        ‖fderiv ℝ (fderiv ℝ (stableResidualCoefficient i)) y‖ ≤ C / (y 0 + 1) := by
  obtain ⟨B, hB, HB⟩ := exists_stableResidualProfile_bounds
  refine ⟨7 * B, by positivity, ?_⟩
  intro y hy hw i
  have ha := reciprocalParameter_range hy
  have hcoords : 0 ≤ reciprocalParameterMap y 0 ∧ reciprocalParameterMap y 0 ≤ 2 / 5 := ⟨ha.1.le, ha.2⟩
  obtain ⟨h0, h1, h2⟩ := HB (reciprocalParameterMap y) hcoords hw i
  have hn : y 0 + 1 ≠ 0 := by linarith
  have hp := contDiffAt_stableResidualProfile 2 i (p := reciprocalParameterMap y) (by dsimp [reciprocalParameterMap]; linarith [ha.2])
  have heq := stableResidualCoefficient_eventually_reciprocal i (by linarith : 1 < y 0)
  have hreg := (contDiffAt_reciprocalParameter 2 hn).mul
    (hp.comp y (contDiffAt_reciprocalParameterMap 2 hn))
  refine ⟨hreg.congr_of_eventuallyEq heq, ?_⟩
  obtain ⟨H0, H1, H2⟩ := reciprocalProfile_derivative_bounds hy hB.le hp h0 h1 h2
  rw [heq.eq_of_nhds, heq.fderiv_eq, heq.fderiv.fderiv_eq]
  have hnonneg : 0 ≤ B * reciprocalParameter y := mul_nonneg hB.le ha.1.le
  simp only [reciprocalParameter, div_eq_mul_inv] at H0 H1 H2 hnonneg ⊢
  exact ⟨by nlinarith only [H0, hnonneg], by nlinarith only [H1, hnonneg], H2⟩

theorem exists_stableResidualCoefficient_band_derivative_bounds :
    ∃ C > (0 : ℝ), ∀ (c : ℝ) (y : Fin 2 → ℝ), 2 ≤ c → |y 0 - c| ≤ 1 / 10 → |y 1| ≤ 1 →
      ∀ i : Fin 4, ContDiffAt ℝ 2 (stableResidualCoefficient i) y ∧
        |stableResidualCoefficient i y| ≤ C / (c + 1) ∧
        ‖fderiv ℝ (stableResidualCoefficient i) y‖ ≤ C / (c + 1) ∧
        ‖fderiv ℝ (fderiv ℝ (stableResidualCoefficient i)) y‖ ≤ C / (c + 1) := by
  obtain ⟨C, hC, HC⟩ := exists_stableResidualCoefficient_derivative_bounds
  refine ⟨2 * C, by positivity, ?_⟩
  intro c y hc hm hw i
  have hml := (abs_le.mp hm).1
  have hy : 3 / 2 ≤ y 0 := by linarith
  obtain ⟨hreg, h0, h1, h2⟩ := HC y hy hw i
  have H : C / (y 0 + 1) ≤ (2 * C) / (c + 1) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith [hC]
  exact ⟨hreg, h0.trans H, h1.trans H, h2.trans H⟩

end BianchiIX
