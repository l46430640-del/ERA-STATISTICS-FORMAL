import BianchiIX.Dynamics.ShearRestartTailRadiusComparison
import BianchiIX.Analysis.ReciprocalRadialComparison

noncomputable section

namespace BianchiIX

open Set

/-- The complete long-tail return has the original reference phase with quadratic value error, linear derivative error, and positive radial slope. -/
theorem exists_restartShearTail_output_phase :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D : ℝ, 3 < q → 4 < D → ∃ C > (0 : ℝ),
        ∀ P : ℝ, 6 * D + 2 < P → ∃ astar > (0 : ℝ),
          ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
            (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let s := shearTailTime a D + q / 2 * Real.log (1 / a)
            let X := restartShearReturnPhase h s ζ ν
            let F := fun r => restartReferenceRadialPhase h (restartShearCurve 1 ζ ν r)
            DifferentiableAt ℝ X ρ ∧ |X ρ - F ρ| ≤ C * a ^ 2 ∧
            |deriv X ρ - deriv F ρ| ≤ C * a ∧
            1 / (8 * Real.sqrt 3) ≤ deriv X ρ ∧ deriv X ρ ≤ C := by
  obtain ⟨hR, hhR, HR⟩ := exists_restartShearTail_radius_comparison
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearTail_entrance_phase
  refine ⟨min hR hE, lt_min hhR hhE, ?_⟩
  intro h hh q D hq hD
  obtain ⟨K, hK, HK⟩ := HE h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q D
    (by linarith only [hq]) (by linarith only [hD])
  let A : ℝ := 2 * 96 ^ 2 * 1179648 + 4 * 24576 * 96 ^ 3 * 3
  let C := A + K + 2 / Real.sqrt 3 + 2
  have hA : 0 < A := by dsimp only [A]; norm_num
  have hC : 0 < C := by dsimp only [C]; positivity
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hAC : A + K ≤ C := by
    have H : 0 < 2 / Real.sqrt (3 : ℝ) := by positivity
    dsimp only [C]
    linarith only [H]
  refine ⟨C, hC, ?_⟩
  intro P hP
  obtain ⟨aR, haR, HAR⟩ := HR h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aE, haE, HAE⟩ := HK P hP
  refine ⟨min aR (min aE (min (1 / (8 * Real.sqrt 3 * A)) (1 / A))),
    lt_min haR (lt_min haE (lt_min (by positivity) (by positivity))), ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ s X F
  have ha' := ha.2.trans (min_le_right _ _)
  have ha'' := ha'.trans (min_le_right _ _)
  let κ := restartShearTailEntranceRadius h a q D ζ ν
  let g := fun r => restartShearReturnState h s ζ ν r 0
  let f := restartShearTailEntrancePhase h a q D ζ ν
  obtain ⟨Hκ, Hg, hκlo, hglo, Hval, Hκd, Hder⟩ :=
    HAR a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨_, Hf, Hfv, Hfd, Hflo, Hfhi, _⟩ :=
    HAE a ⟨ha.1, ha'.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  have hg0 : 0 < g ρ := (by positivity [ha.1] : 0 < 1 / (96 * a)).trans_le hglo
  have HX : DifferentiableAt ℝ X ρ :=
    ((hasDerivAt_const ρ (2 : ℝ)).div Hg.hasDerivAt hg0.ne').differentiableAt
  obtain ⟨_, HV, HD⟩ := reciprocal_radial_comparison ha.1 (by norm_num : (0 : ℝ) < 96)
    (by norm_num : (0 : ℝ) ≤ 24576) Hg Hκ hglo hκlo Hval Hκd Hder
  change |X ρ - f ρ| ≤ 2 * 96 ^ 2 * 3 * a ^ 2 at HV
  change |deriv (fun r => X r - f r) ρ| ≤ A * a at HD
  rw [deriv_fun_sub HX Hf] at HD
  have HV' : |X ρ - f ρ| ≤ A * a ^ 2 := HV.trans
    (mul_le_mul_of_nonneg_right (by dsimp only [A]; norm_num) (sq_nonneg a))
  have HA : A * a ≤ 1 / (8 * Real.sqrt 3) := by
    have H := mul_le_mul_of_nonneg_left (ha''.trans (min_le_left _ _)) hA.le
    exact H.trans_eq (by field_simp)
  have HA1 : A * a ≤ 1 := by
    nlinarith only [(le_div_iff₀ hA).mp (ha''.trans (min_le_right _ _))]
  have Habs := abs_le.mp HD
  refine ⟨HX, ?_, ?_, ?_, ?_⟩
  · calc
      _ ≤ |X ρ - f ρ| + |f ρ - F ρ| := abs_sub_le _ _ _
      _ ≤ A * a ^ 2 + K * a ^ 2 := add_le_add HV' Hfv
      _ = (A + K) * a ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hAC (sq_nonneg a)
  · calc
      _ ≤ |deriv X ρ - deriv f ρ| + |deriv f ρ - deriv F ρ| := abs_sub_le _ _ _
      _ ≤ A * a + K * a := add_le_add HD Hfd
      _ = (A + K) * a := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hAC ha.1.le
  · have heq : 1 / (4 * Real.sqrt 3) = 2 * (1 / (8 * Real.sqrt 3)) := by ring
    rw [heq] at Hflo
    linarith only [Hflo, Habs.1, HA]
  · dsimp only [C]
    linarith only [Hfhi, Habs.2, HA1, hA, hK]

end BianchiIX
