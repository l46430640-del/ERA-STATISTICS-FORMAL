import BianchiIX.Dynamics.ShearRestartEntranceRadiusComparison
import BianchiIX.Analysis.ReciprocalRadialComparison

noncomputable section

namespace BianchiIX

open Set

/-- After a preceding entrance, the same fixed shear return has the original reference
phase with quadratic value error, linear derivative error, and a uniform positive slope. -/
theorem exists_restartShearEntrance_output_phase :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∃ C > (0 : ℝ), ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
            (0 < n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
            n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
              let s := q / 2 * Real.log (1 / a)
              let X := restartShearReturnPhase h s n₂ n₃
              let F := fun r => restartReferenceRadialPhase h (restartShearCurve 1 n₂ n₃ r)
              restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ 2 < 1 →
              DifferentiableAt ℝ X ρ ∧ |X ρ - F ρ| ≤ C * a ^ 2 ∧
                |deriv X ρ - deriv F ρ| ≤ C * a ∧
                1 / (8 * Real.sqrt 3) ≤ deriv X ρ ∧ deriv X ρ ≤ C := by
  obtain ⟨hR, hhR, D, hD, HR⟩ := exists_restartShearEntrance_radius_comparison
  obtain ⟨hF, hhF, HF⟩ := exists_restartFastShearProjectionPhase_approximation
  refine ⟨min hR hF, lt_min hhR hhF, ?_⟩
  intro h hh
  obtain ⟨K, hK, HK⟩ := HF h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩
  let A := 8192 * D + 1048576 * D ^ 2
  let C := A + K + 2 / Real.sqrt 3 + 2
  have hA : 0 < A := by dsimp only [A]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hAC : A + K ≤ C := by
    have H : 0 < 2 / Real.sqrt (3 : ℝ) := by positivity
    dsimp only [C]
    linarith only [H]
  refine ⟨C, hC, ?_⟩
  intro q P hq hP
  obtain ⟨aR, haR, HaR⟩ := HR h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
  obtain ⟨aF, haF, HaF⟩ := HK q P (by linarith only [hq]) (by linarith only [hP])
  refine ⟨min aR (min aF (min (1 / (8 * Real.sqrt 3 * A)) (1 / A))),
    lt_min haR (lt_min haF (lt_min (by positivity) (by positivity))), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s X F hv
  have ha' := ha.2.trans (min_le_right _ _)
  have ha'' := ha'.trans (min_le_right _ _)
  have haA := ha''.trans (min_le_left _ _)
  have ha1 := ha''.trans (min_le_right _ _)
  let k := restartFastShearCoreRadius h s 1 n₂ n₃
  let g := fun r => restartShearReturnState h s n₂ n₃ r 0
  let x := restartFastShearProjectionPhase h s 1 n₂ n₃
  obtain ⟨Hk, Hg, hklo, hglo, hval, hdk, hder⟩ :=
    HaR a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  obtain ⟨_, _, Hx, hxv, hxd, hxlo, hxhi⟩ :=
    HaF a ⟨ha.1, ha'.trans (min_le_left _ _)⟩ ε 1 n₂ n₃ hε (by norm_num)
      ⟨h₂.1.le, h₂.2⟩ ⟨h₃.1.le, h₃.2⟩ h₃P ρ hρ
  have hg0 : 0 < g ρ := (by positivity [ha.1] : 0 < 1 / (64 * a)).trans_le hglo
  have HX : DifferentiableAt ℝ X ρ :=
    ((hasDerivAt_const ρ (2 : ℝ)).div Hg.hasDerivAt hg0.ne').differentiableAt
  obtain ⟨_, HV, HD⟩ := reciprocal_radial_comparison ha.1 (by norm_num : (0 : ℝ) < 64) hD.le
    Hg Hk hglo hklo hval hdk hder
  change |X ρ - x ρ| ≤ 2 * 64 ^ 2 * D * a ^ 2 at HV
  change |deriv (fun r => X r - x r) ρ| ≤ (2 * 64 ^ 2 * D + 4 * D * 64 ^ 3 * D) * a at HD
  rw [deriv_fun_sub HX Hx] at HD
  have HV' : |X ρ - x ρ| ≤ A * a ^ 2 := HV.trans (by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg a)
    dsimp only [A]
    nlinarith only [sq_nonneg D])
  have HD' : |deriv X ρ - deriv x ρ| ≤ A * a := HD.trans_eq (by dsimp only [A]; ring)
  have HA : A * a ≤ 1 / (8 * Real.sqrt 3) := by
    have H := mul_le_mul_of_nonneg_left haA hA.le
    exact H.trans_eq (by field_simp)
  have HA1 : A * a ≤ 1 := by nlinarith only [(le_div_iff₀ hA).mp ha1]
  have Habs := abs_le.mp HD'
  refine ⟨HX, ?_, ?_, ?_, ?_⟩
  · calc
      _ ≤ |X ρ - x ρ| + |x ρ - F ρ| := abs_sub_le _ _ _
      _ ≤ A * a ^ 2 + K * a ^ 2 := add_le_add HV' hxv
      _ = (A + K) * a ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hAC (sq_nonneg a)
  · calc
      _ ≤ |deriv X ρ - deriv x ρ| + |deriv x ρ - deriv F ρ| := abs_sub_le _ _ _
      _ ≤ A * a + K * a := add_le_add HD' hxd
      _ = (A + K) * a := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hAC ha.1.le
  · have heq : 1 / (4 * Real.sqrt 3) = 2 * (1 / (8 * Real.sqrt 3)) := by ring
    rw [heq] at hxlo
    linarith only [hxlo, Habs.1, HA]
  · dsimp only [C]
    linarith only [hxhi, Habs.2, HA1, hA, hK]

end BianchiIX
