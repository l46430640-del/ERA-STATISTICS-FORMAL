import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section

namespace BianchiIX

open Filter Asymptotics Set
open scoped Topology

/-- Joint wall-amplitude remainders give one amplitude threshold on every compact parameter set. -/
theorem compact_wall_remainder_uniform {K : Set ℝ} (hK : IsCompact K) {F : ℝ → ℝ → ℝ → ℝ}
    (H : ∀ R₀ ∈ K, ∀ R u w : ℕ → ℝ,
      Tendsto R atTop (𝓝 R₀) → Tendsto u atTop (𝓝 0) → Tendsto w atTop (𝓝 0) →
      (∀ n, 0 < u n ∧ 0 < w n) → (fun n => F (R n) (u n) (w n)) =o[atTop] (fun n => u n + w n))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ R ∈ K, ∀ u w : ℝ, 0 < u → 0 < w → u + w < δ →
      |F R u w| ≤ ε * (u + w) := by
  classical
  by_contra! Hfail
  have Hseq (n : ℕ) : ∃ R ∈ K, ∃ u w : ℝ, 0 < u ∧ 0 < w ∧ u + w < 1 / ((n : ℝ) + 1) ∧
      ε * (u + w) < |F R u w| := Hfail (1 / ((n : ℝ) + 1)) (by positivity)
  choose R hRK u w hu hw hsmall hbad using Hseq
  have HU : Tendsto u atTop (𝓝 0) := squeeze_zero (fun n => (hu n).le)
    (fun n => (le_add_of_nonneg_right (hw n).le).trans (hsmall n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  have HW : Tendsto w atTop (𝓝 0) := squeeze_zero (fun n => (hw n).le)
    (fun n => (le_add_of_nonneg_left (hu n).le).trans (hsmall n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨R₀, hR₀, φ, hφ, HR⟩ := hK.tendsto_subseq hRK
  have HE := H R₀ hR₀ (R ∘ φ) (u ∘ φ) (w ∘ φ) HR
    (HU.comp hφ.tendsto_atTop) (HW.comp hφ.tendsto_atTop) (fun n => ⟨hu (φ n), hw (φ n)⟩)
  obtain ⟨n, hn⟩ := (HE.bound (div_pos hε (by norm_num : (0 : ℝ) < 2))).exists
  simp only [Function.comp_def, Real.norm_eq_abs, abs_of_pos (add_pos (hu (φ n)) (hw (φ n)))] at hn
  have hb := add_pos (hu (φ n)) (hw (φ n))
  nlinarith only [hn, hbad (φ n), mul_pos hε hb]

end BianchiIX
