import BianchiIX.Dynamics.EraOutputEstimates
import BianchiIX.Analysis.GraphPhaseInverse

noncomputable section

namespace BianchiIX

open Set

def eraGraphRadius (η : ℝ) (J m : ℕ) (U W : ℝ → ℝ) : ℝ → ℝ :=
  graphPhase (eraOutputRadius η J m) U W

def eraGraphWall (η : ℝ) (J m : ℕ) (U W : ℝ → ℝ) (i : Fin 4) : ℝ → ℝ :=
  graphPhase (fun X => eraOutputState η J m X i) U W

/-- The actual era maps every admissible entrance graph to a regular radial curve with uniform output bounds. -/
theorem exists_era_output_graph_estimates :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ C ≥ (1 : ℝ),
      ∀ (m : ℕ) (β B : ℝ) (U W : ℝ → ℝ), 0 < β → β < 1 / 4 →
        let a := 2 * ((m : ℝ) + 1 + β)
        let b := 2 * ((m : ℝ) + 2 - β)
        B * b ≤ ε → B ≤ ε * (β / 2) ^ (2 * J) → C * B < β / 4 →
        (∀ r ∈ Icc a b, 0 < U r ∧ 0 < W r ∧ U r + W r ≤ B ∧
          ContDiffAt ℝ 1 U r ∧ ContDiffAt ℝ 1 W r ∧
          |deriv U r| ≤ Real.sqrt (U r) ∧ |deriv W r| ≤ Real.sqrt (W r)) →
        let k := eraGraphRadius η J m U W
        let u := eraGraphWall η J m U W 1
        let w := eraGraphWall η J m U W 3
        ∀ r ∈ Icc a b, ContDiffAt ℝ 1 k r ∧ deriv k r < 0 ∧
          ContDiffAt ℝ 1 u r ∧ ContDiffAt ℝ 1 w r ∧ 0 < u r ∧ 0 < w r ∧
          u r + w r ≤ C * B ^ (19 / 10 : ℝ) ∧
          |deriv u r| ≤ (C * B ^ (7 / 24 : ℝ)) * (Real.sqrt (u r) * |deriv k r|) ∧
          |deriv w r| ≤ (C * B ^ (7 / 24 : ℝ)) * (Real.sqrt (w r) * |deriv k r|) := by
  obtain ⟨δ, hδ, hδmax, H⟩ := exists_era_output_estimates
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ
  obtain ⟨ε, hε, hεmax, C, hC, HE⟩ := H η hη hηδ J hJ
  refine ⟨ε, hε, hεmax, C, hC, ?_⟩
  intro m β B U W hβ hβmax a b hscale hsmall hmargin Hgraph k u w r hr
  obtain ⟨hu, hw, hsum, hU, hW, hdU, hdW⟩ := Hgraph r hr
  have hC0 : 0 ≤ C := by linarith
  have hB : 0 < B := by linarith
  have hr0 : 0 < r := by dsimp [a] at hr; nlinarith [hr.1, Nat.cast_nonneg (α := ℝ) m]
  have hBr : B * r ≤ ε := (mul_le_mul_of_nonneg_left hr.2 hB.le).trans hscale
  have hwall {z : ℝ} (hz : z ≤ B) : z ≤ ε / r :=
    (le_div_iff₀ hr0).mpr ((mul_le_mul_of_nonneg_right hz hr0.le).trans hBr)
  have hphase : (m : ℝ) + 1 + β ≤ r / 2 ∧ r / 2 ≤ (m : ℝ) + 2 - β := by
    dsimp [a, b] at hr
    constructor <;> linarith [hr.1, hr.2]
  have hUB : U r ≤ B := by linarith
  have hWB : W r ≤ B := by linarith
  obtain ⟨HS, HR, hpu, hpw, hamp, _, HD⟩ := HE m β ![r, U r, W r] hβ (by linarith)
    ⟨hu, hwall hUB⟩ ⟨hw, hwall hWB⟩ (hsum.trans hsmall) hphase
    ((mul_le_mul_of_nonneg_left hsum hC0).trans_lt hmargin)
  obtain ⟨Hk, Hdk⟩ := graphPhase_differential HR hU hW
  have Hwall (i : Fin 4) :
      ContDiffAt ℝ 1 (eraGraphWall η J m U W i) r ∧
      HasDerivAt (eraGraphWall η J m U W i)
        (fderiv ℝ (eraOutputState η J m) ![r, U r, W r] ![1, deriv U r, deriv W r] i) r := by
    obtain ⟨hc, hd⟩ := graphPhase_differential (contDiffAt_pi.mp HS i) hU hW
    rw [fderiv_apply (HS.differentiableAt (by norm_num)) i] at hd
    exact ⟨hc, hd⟩
  obtain ⟨hp, hcone⟩ := HD ![1, deriv U r, deriv W r] rfl hdU hdW
  have hkneg : deriv k r < 0 := Hdk.deriv ▸ hp
  have hc : (C * (U r + W r) ^ (7 / 24 : ℝ)) ≤ C * B ^ (7 / 24 : ℝ) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (add_pos hu hw).le hsum (by norm_num)) hC0
  have hcu := ((le_max_left _ _).trans hcone).trans hc
  have hcw := ((le_max_right _ _).trans hcone).trans hc
  rw [← Hdk.deriv, ← (Hwall 1).2.deriv] at hcu
  rw [← Hdk.deriv, ← (Hwall 3).2.deriv] at hcw
  refine ⟨Hk, hkneg, (Hwall 1).1, (Hwall 3).1, hpu, hpw, ?_, ?_, ?_⟩
  · exact hamp.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (add_pos hu hw).le hsum (by norm_num)) hC0)
  · exact (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr hpu) (abs_pos.mpr hkneg.ne))).mp hcu
  · exact (div_le_iff₀ (mul_pos (Real.sqrt_pos.mpr hpw) (abs_pos.mpr hkneg.ne))).mp hcw

end BianchiIX
