import BianchiIX.Analysis.ScalarLocalInverse
import BianchiIX.Analysis.InverseLogDistortion
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

noncomputable section

namespace BianchiIX

def graphPhase (F : (Fin 3 → ℝ) → ℝ) (U W : ℝ → ℝ) (r : ℝ) : ℝ := F ![r, U r, W r]

theorem graphPhase_differential {F : (Fin 3 → ℝ) → ℝ} {U W : ℝ → ℝ} {r : ℝ}
    (hF : ContDiffAt ℝ 1 F ![r, U r, W r])
    (hU : ContDiffAt ℝ 1 U r) (hW : ContDiffAt ℝ 1 W r) :
    ContDiffAt ℝ 1 (graphPhase F U W) r ∧
      HasDerivAt (graphPhase F U W)
        (fderiv ℝ F ![r, U r, W r] ![1, deriv U r, deriv W r]) r := by
  let γ := fun t => (![t, U t, W t] : Fin 3 → ℝ)
  have Hγ : ContDiffAt ℝ 1 γ r := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · exact contDiffAt_id
    · exact hU
    · exact hW
  have HDγ : HasDerivAt γ ![1, deriv U r, deriv W r] r := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hasDerivAt_id r
    · exact (hU.differentiableAt (by norm_num)).hasDerivAt
    · exact (hW.differentiableAt (by norm_num)).hasDerivAt
  exact ⟨hF.comp r Hγ,
    (hF.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt r HDγ⟩

/-- A relative phase differential gives an actual C1 local inverse along the entrance graph. -/
theorem exists_graph_phase_inverse {F : (Fin 3 → ℝ) → ℝ} {U W : ℝ → ℝ} {r α e : ℝ}
    (hF : ContDiffAt ℝ 2 F ![r, U r, W r])
    (hU : ContDiffAt ℝ 1 U r) (hW : ContDiffAt ℝ 1 W r)
    (hα : 0 < α) (he : e ≤ 1 / 4)
    (herr : |α ^ 2 * fderiv ℝ F ![r, U r, W r] ![1, deriv U r, deriv W r] + 1| ≤ e) :
    ContDiffAt ℝ 1 (graphPhase F U W) r ∧ deriv (graphPhase F U W) r < 0 ∧
      ∃ g, ScalarLocalInverseAt (graphPhase F U W) r g ∧
        |Real.log (|deriv (graphPhase F U W) r| / (1 / α ^ 2))| +
          |Real.log (|deriv g (graphPhase F U W r)| / α ^ 2)| ≤ 4 * e := by
  obtain ⟨Hf, HD⟩ := graphPhase_differential (hF.of_le (by norm_num)) hU hW
  have Herror : |α ^ 2 * deriv (graphPhase F U W) r + 1| ≤ e := by rwa [HD.deriv]
  have Hsign : α ^ 2 * deriv (graphPhase F U W) r ≤ -(3 / 4) := by
    linarith only [(abs_le.mp (Herror.trans he)).2]
  have Hneg : deriv (graphPhase F U W) r < 0 := by nlinarith only [Hsign, sq_nonneg α]
  obtain ⟨g, Hg⟩ := exists_scalarLocalInverseAt Hf Hneg.ne
  refine ⟨Hf, Hneg, g, Hg, ?_⟩
  rw [Hg.deriv_eq]
  exact negative_derivative_log_bounds hα Hneg he Herror

end BianchiIX
