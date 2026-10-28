import BianchiIX.Dynamics.EraIntervalInverse
import BianchiIX.Analysis.ReciprocalGaussEstimates

noncomputable section

namespace BianchiIX

open Set

def eraInverseBranch (η : ℝ) (J m : ℕ) (β : ℝ) (U W : ℝ → ℝ) : ℝ → ℝ :=
  fun y => 2 / intervalRadiusInverse (graphPhase (eraBoundedPhase η J m) U W)
    (2 * ((m : ℝ) + 1 + β)) (2 * ((m : ℝ) + 2 - β)) y

/-- The actual inverse era branch satisfies the Gauss value and logarithmic derivative estimates. -/
theorem exists_era_inverse_branch_estimates :
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
        let h := eraInverseBranch η J m β U W
        StrictAntiOn h (Icc (2 * β) (1 - 2 * β)) ∧
        ∀ y ∈ Icc (2 * β) (1 - 2 * β),
          h y ∈ Ioo (1 / ((m : ℝ) + 2)) (1 / ((m : ℝ) + 1)) ∧
          φ (2 / h y) = y ∧ ContDiffAt ℝ 1 h y ∧ deriv h y < 0 ∧
          |h y - gaussInv ((m : ℝ) + 1) y| ≤ C * B / ((m : ℝ) + 1) ^ 2 ∧
          |Real.log (|deriv h y| / |deriv (gaussInv ((m : ℝ) + 1)) y|)| ≤
            5 * C * Real.sqrt B := by
  obtain ⟨δ, hδ, hδmax, H⟩ := exists_era_interval_inverse
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ
  obtain ⟨ε, hε, hεmax, C, hC, HE⟩ := H η hη hηδ J hJ
  refine ⟨ε, hε, hεmax, C, hC, ?_⟩
  intro m β B U W hβ hβmax a b hscale hsmall hmargin Hgraph φ h
  obtain ⟨_, _, _, _, HI⟩ := HE m β B U W hβ hβmax hscale hsmall hmargin Hgraph
  let g := intervalRadiusInverse φ a b
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hab : a < b := by dsimp [a, b]; linarith
  have hB : 0 < B := by
    obtain ⟨hu, hw, hsum, _⟩ := Hgraph a ⟨le_rfl, hab.le⟩
    linarith
  have hb1 : 1 ≤ b := by dsimp [b]; linarith
  have hB1 : B ≤ 1 := by
    have Hmul := mul_le_mul_of_nonneg_left hb1 hB.le
    linarith
  have hBsqrt : B ≤ Real.sqrt B := by
    have hs := Real.sq_sqrt hB.le
    have hs0 := Real.sqrt_nonneg B
    nlinarith [mul_nonneg hB.le (sub_nonneg.mpr hB1)]
  have hC0 : 0 ≤ C := by linarith
  have Hpoint (y : ℝ) (hy : y ∈ Icc (2 * β) (1 - 2 * β)) :
      h y ∈ Ioo (1 / ((m : ℝ) + 2)) (1 / ((m : ℝ) + 1)) ∧
      φ (2 / h y) = y ∧ ContDiffAt ℝ 1 h y ∧ deriv h y < 0 ∧
      |h y - gaussInv ((m : ℝ) + 1) y| ≤ C * B / ((m : ℝ) + 1) ^ 2 ∧
      |Real.log (|deriv h y| / |deriv (gaussInv ((m : ℝ) + 1)) y|)| ≤
        5 * C * Real.sqrt B := by
    obtain ⟨hgi, hfg, _, hg, hgd, hgd0, hgv, hgl⟩ := HI y hy
    change g y ∈ Ioo a b at hgi
    have hg0 : 0 < g y := by dsimp [a, b] at hgi; linarith [hgi.1]
    have hhalf : (m : ℝ) + 1 < g y / 2 ∧ g y / 2 < (m : ℝ) + 2 := by
      dsimp [a, b] at hgi
      constructor <;> linarith [hgi.1, hgi.2]
    have hy0 : 0 ≤ y := by linarith [hy.1]
    have Hhalf : HasDerivAt (fun z => g z / 2) (deriv g y / 2) y :=
      (hg.differentiableAt (by norm_num)).hasDerivAt.div_const 2
    have hrec : (fun z => 1 / (g z / 2)) = h := by
      funext z
      change 1 / (g z / 2) = 2 / g z
      ring
    obtain ⟨_, hneg, hv, hl⟩ := reciprocal_gauss_estimates (by linarith : 1 ≤ (m : ℝ) + 1)
      hy0 hhalf.1.le Hhalf (div_pos hgd0 (by norm_num)) hgv (by linarith) hgl
    rw [hrec] at hneg hv hl
    refine ⟨?_, ?_, ?_, hneg, hv, ?_⟩
    · change 2 / g y ∈ _
      rw [show 2 / g y = 1 / (g y / 2) by ring]
      exact ⟨one_div_lt_one_div_of_lt (by positivity) hhalf.2,
        one_div_lt_one_div_of_lt (by positivity) hhalf.1⟩
    · change φ (2 / (2 / g y)) = y
      rw [show 2 / (2 / g y) = g y by field_simp]
      exact hfg
    · exact contDiffAt_const.div hg hg0.ne'
    · have Hsqrt := mul_le_mul_of_nonneg_left hBsqrt hC0
      linarith
  refine ⟨?_, Hpoint⟩
  exact strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (fun y hy => (Hpoint y hy).2.2.1.continuousAt.continuousWithinAt)
    (fun y hy => (Hpoint y (interior_subset hy)).2.2.2.1)

end BianchiIX
