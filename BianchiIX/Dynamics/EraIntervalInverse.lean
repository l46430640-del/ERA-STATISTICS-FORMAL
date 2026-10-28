import BianchiIX.Dynamics.EraGraphInverse
import BianchiIX.Analysis.PositiveIntervalInverse

noncomputable section

namespace BianchiIX

open Set

/-- Actual era graphs cover the same output interval, with a unique C1 radius inverse there. -/
theorem exists_era_interval_inverse :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 4 ≤ J → ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ C ≥ (1 : ℝ),
      ∀ (m : ℕ) (β B : ℝ) (U W : ℝ → ℝ), 0 < β → β < 1 / 4 →
        let a := 2 * ((m : ℝ) + 1 + β)
        let b := 2 * ((m : ℝ) + 2 - β)
        B * b ≤ ε → B ≤ ε * (β / 2) ^ (2 * J) → C * B < β / 4 →
        (∀ r ∈ Icc a b, 0 < U r ∧ 0 < W r ∧ U r + W r ≤ B ∧
          ContDiffAt ℝ 1 U r ∧ ContDiffAt ℝ 1 W r ∧
          |deriv U r| ≤ Real.sqrt (U r) ∧ |deriv W r| ≤ Real.sqrt (W r)) →
        let φ := graphPhase (eraBoundedPhase η J m) U W
        let g := intervalRadiusInverse φ a b
        StrictMonoOn φ (Icc a b) ∧ LeftInvOn g φ (Icc a b) ∧
        φ a < 2 * β ∧ 1 - 2 * β < φ b ∧
        ∀ y ∈ Icc (2 * β) (1 - 2 * β),
          g y ∈ Ioo a b ∧ φ (g y) = y ∧
          (∀ r ∈ Icc a b, φ r = y → r = g y) ∧
          ContDiffAt ℝ 1 g y ∧ HasDerivAt g (deriv φ (g y))⁻¹ y ∧
          0 < deriv g y ∧ |g y / 2 - ((m : ℝ) + 1 + y)| ≤ C * B ∧
          |Real.log (deriv g y / 2)| ≤ C * Real.sqrt B := by
  obtain ⟨δ, hδ, hδmax, H⟩ := exists_era_graph_inverse
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ
  obtain ⟨ε, hε, hεmax, C, hC, HE⟩ := H η hη hηδ J hJ
  refine ⟨ε, hε, hεmax, C, hC, ?_⟩
  intro m β B U W hβ hβmax a b hscale hsmall hmargin Hgraph φ g
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hab : a < b := by dsimp [a, b]; linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have hB : 0 < B := by
    obtain ⟨hu, hw, hsum, _⟩ := Hgraph a ⟨le_rfl, hab.le⟩
    linarith
  have hC0 : 0 ≤ C := by linarith
  have Hφ (r : ℝ) (hr : r ∈ Icc a b) :
      ContDiffAt ℝ 1 φ r ∧ |φ r - (r / 2 - ((m : ℝ) + 1))| ≤ C * B ∧
      0 < deriv φ r ∧ |Real.log (2 * deriv φ r)| ≤ C * Real.sqrt B := by
    obtain ⟨hu, hw, hsum, hU, hW, hdU, hdW⟩ := Hgraph r hr
    have hr0 := ha.trans_le hr.1
    have hBr : B * r ≤ ε := (mul_le_mul_of_nonneg_left hr.2 hB.le).trans hscale
    have huε : U r ≤ ε / r := (le_div_iff₀ hr0).mpr (by
      exact (mul_le_mul_of_nonneg_right (by linarith : U r ≤ B) hr0.le).trans hBr)
    have hwε : W r ≤ ε / r := (le_div_iff₀ hr0).mpr (by
      exact (mul_le_mul_of_nonneg_right (by linarith : W r ≤ B) hr0.le).trans hBr)
    have hphase : (m : ℝ) + 1 + β ≤ r / 2 ∧ r / 2 ≤ (m : ℝ) + 2 - β := by
      dsimp [a, b] at hr
      constructor <;> linarith [hr.1, hr.2]
    have herror := mul_le_mul_of_nonneg_left hsum hC0
    obtain ⟨hf, _, hv, hd, hl, _⟩ := HE m β r U W hβ (by linarith)
      ⟨hu, huε⟩ ⟨hw, hwε⟩ (hsum.trans hsmall) hphase (herror.trans_lt hmargin)
      hU hW hdU hdW
    exact ⟨hf, hv.trans herror, hd,
      hl.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsum) hC0)⟩
  obtain ⟨hmono, _, hleft, _, hright, Hinv⟩ :=
    intervalRadiusInverse_positive_control hab (fun r hr => (Hφ r hr).1)
      (fun r hr => (Hφ r hr).2.2.1)
  have hfa : φ a < 2 * β := by
    have hv := (abs_le.mp (Hφ a ⟨le_rfl, hab.le⟩).2.1).2
    dsimp [a] at hv
    linarith
  have hfb : 1 - 2 * β < φ b := by
    have hv := (abs_le.mp (Hφ b ⟨hab.le, le_rfl⟩).2.1).1
    dsimp [b] at hv
    linarith
  refine ⟨hmono, hleft, hfa, hfb, ?_⟩
  intro y hy
  have hyi : y ∈ Ioo (φ a) (φ b) := ⟨hfa.trans_le hy.1, hy.2.trans_lt hfb⟩
  obtain ⟨hgi, hg, hgd⟩ := Hinv y hyi
  have hgc : g y ∈ Icc a b := ⟨hgi.1.le, hgi.2.le⟩
  have hfg : φ (g y) = y := hright ⟨hyi.1.le, hyi.2.le⟩
  have Hpoint := Hφ (g y) hgc
  refine ⟨hgi, hfg, ?_, hg, hgd, ?_, ?_, ?_⟩
  · intro r hr hfy
    exact hmono.injOn hr hgc (hfy.trans hfg.symm)
  · rw [hgd.deriv]
    exact inv_pos.mpr Hpoint.2.2.1
  · have hv := Hpoint.2.1
    rw [hfg] at hv
    rw [show g y / 2 - ((m : ℝ) + 1 + y) =
      -(y - (g y / 2 - ((m : ℝ) + 1))) by ring, abs_neg]
    exact hv
  · rw [hgd.deriv, show (deriv φ (g y))⁻¹ / 2 = (2 * deriv φ (g y))⁻¹ by ring,
      Real.log_inv, abs_neg]
    exact Hpoint.2.2.2

end BianchiIX
