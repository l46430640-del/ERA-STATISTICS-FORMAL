import BianchiIX.Dynamics.EraBoundedPhase
import BianchiIX.Analysis.GraphPhaseInverse

noncomputable section

namespace BianchiIX

/-- Along every admissible C1 entrance graph the actual era phase has a positive local inverse. -/
theorem exists_era_graph_inverse :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 4 ≤ J → ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ C ≥ (1 : ℝ),
      ∀ (m : ℕ) (β r : ℝ) (U W : ℝ → ℝ), 0 < β → β < 1 / 2 →
        (0 < U r ∧ U r ≤ ε / r) → (0 < W r ∧ W r ≤ ε / r) →
        U r + W r ≤ ε * (β / 2) ^ (2 * J) →
        ((m : ℝ) + 1 + β ≤ r / 2 ∧ r / 2 ≤ (m : ℝ) + 2 - β) →
        C * (U r + W r) < β / 4 →
        ContDiffAt ℝ 1 U r → ContDiffAt ℝ 1 W r →
        |deriv U r| ≤ Real.sqrt (U r) → |deriv W r| ≤ Real.sqrt (W r) →
        let φ := graphPhase (eraBoundedPhase η J m) U W
        ContDiffAt ℝ 1 φ r ∧ (β / 2 < φ r ∧ φ r < 1 - β / 2) ∧
        |φ r - (r / 2 - ((m : ℝ) + 1))| ≤ C * (U r + W r) ∧
        0 < deriv φ r ∧ |Real.log (2 * deriv φ r)| ≤ C * Real.sqrt (U r + W r) ∧
        ∃ g, ScalarLocalInverseAt φ r g ∧ 0 < deriv g (φ r) ∧
          |Real.log (deriv g (φ r) / 2)| ≤ C * Real.sqrt (U r + W r) := by
  obtain ⟨δ, hδ, hδmax, H⟩ := exists_era_bounded_phase_estimates
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ
  obtain ⟨ε, hε, hεmax, C, hC, HE⟩ := H η hη hηδ J hJ
  refine ⟨ε, hε, hεmax, C, hC, ?_⟩
  intro m β r U W hβ hβmax hu hw hsmall hphase hmargin hU hW hdU hdW φ
  obtain ⟨_, HP, _, _, hwindow, hvalue, _, _, _, _, _, _, _, _, _, _, HD⟩ :=
    HE m β ![r, U r, W r] hβ hβmax hu hw hsmall hphase hmargin
  obtain ⟨Hφ, Hder⟩ := graphPhase_differential HP hU hW
  have Hdir := HD ![1, deriv U r, deriv W r] rfl hdU hdW
  have hpos : 0 < deriv φ r := by rw [Hder.deriv]; exact Hdir.1
  have hlog : |Real.log (2 * deriv φ r)| ≤ C * Real.sqrt (U r + W r) := by
    rw [Hder.deriv]
    exact Hdir.2
  obtain ⟨g, Hg⟩ := exists_scalarLocalInverseAt Hφ hpos.ne'
  refine ⟨Hφ, hwindow, hvalue, hpos, hlog, g, Hg, ?_, ?_⟩
  · rw [Hg.deriv_eq]
    exact inv_pos.mpr hpos
  · rw [Hg.deriv_eq, show (deriv φ r)⁻¹ / 2 = (2 * deriv φ r)⁻¹ by ring,
      Real.log_inv, abs_neg]
    exact hlog

end BianchiIX
