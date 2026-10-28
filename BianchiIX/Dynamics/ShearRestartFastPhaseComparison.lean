import BianchiIX.Dynamics.ShearRestartFastProjectionError
import BianchiIX.Dynamics.ShearRestartFastPhase

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The exact reciprocal core radius has the reference shear phase and a uniformly positive ordinary derivative. -/
theorem exists_restartFastShearProjectionPhase_approximation :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∃ K > (0 : ℝ), ∀ q P : ℝ, 2 < q → 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε σ n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) → |σ| = 1 →
            (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → n₃ ≤ a ^ P →
            ∀ ρ ∈ Icc a (2 * a),
              let T := q / 2 * Real.log (1 / a)
              T ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) 0 ∧
              0 < restartFastShearHeight h T σ n₂ n₃ ρ ∧
              DifferentiableAt ℝ (restartFastShearProjectionPhase h T σ n₂ n₃) ρ ∧
              |restartFastShearProjectionPhase h T σ n₂ n₃ ρ -
                restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ ρ)| ≤ K * a ^ 2 ∧
              |deriv (restartFastShearProjectionPhase h T σ n₂ n₃) ρ -
                deriv (fun t => restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ t)) ρ| ≤ K * a ∧
              1 / (4 * Real.sqrt 3) ≤ deriv (restartFastShearProjectionPhase h T σ n₂ n₃) ρ ∧
              deriv (restartFastShearProjectionPhase h T σ n₂ n₃) ρ ≤ 2 / Real.sqrt 3 + 1 := by
  obtain ⟨hE, hhE, KE, hKE, HE⟩ := exists_restartShearFastProjectionError_bounds
  obtain ⟨hR, hhR, HR⟩ := exists_restartFastShearPhase_monotone
  refine ⟨min hE (min hR (1 / 16)), lt_min hhE (lt_min hhR (by norm_num)), ?_⟩
  intro h hh
  obtain ⟨KR, hKR, HKR⟩ := HR h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hhsmall : 0 ≤ h ∧ h ≤ 1 / 16 :=
    ⟨hh.1.le, hh.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  let K := KE + KR
  have hK : 0 < K := add_pos hKE hKR
  refine ⟨K, hK, ?_⟩
  intro q P hq hP
  obtain ⟨aE, haE, HaE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
  obtain ⟨aR, haR, HaR⟩ := HKR q hq
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hsqrt]
  refine ⟨min aE (min aR (1 / (4 * Real.sqrt 3 * K))),
    lt_min haE (lt_min haR (by positivity)), ?_⟩
  intro a ha ε σ n₂ n₃ hε hσ h₂ h₃ h₃P ρ hρ T
  let E := fun t => restartProjectionError (restartSectionRadialState h T (restartShearCurve σ n₂ n₃ t))
  obtain ⟨Hdom, HED, HEval, HEder, Hheight, Hgerm⟩ :=
    HaE a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε σ n₂ n₃ hε hσ h₂ h₃ h₃P ρ hρ
  obtain ⟨_, HRD, HRval, HRder, _, _⟩ :=
    HaR a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
      ε σ n₂ n₃ hε hσ h₂ h₃ ρ hρ
  have Hlocal : restartFastShearProjectionPhase h T σ n₂ n₃ =ᶠ[𝓝 ρ]
      (fun t => E t + restartFastShearPhase h T σ n₂ n₃ t) := by
    filter_upwards [Hgerm] with t ht
    apply ht.trans
    change restartProjectionPhase _ =
      (restartProjectionPhase _ - restartRadialPhase _) + restartRadialPhase _
    exact (sub_add_cancel _ _).symm
  have Hsum : HasDerivAt (restartFastShearProjectionPhase h T σ n₂ n₃)
      (deriv E ρ + deriv (restartFastShearPhase h T σ n₂ n₃) ρ) ρ := by
    convert! (HED.hasDerivAt.add HRD.hasDerivAt).congr_of_eventuallyEq Hlocal using 1
  have Hval : |restartFastShearProjectionPhase h T σ n₂ n₃ ρ -
      restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ ρ)| ≤ K * a ^ 2 := by
    rw [Hlocal.eq_of_nhds, add_sub_assoc]
    calc
      _ ≤ |E ρ| + |restartFastShearPhase h T σ n₂ n₃ ρ -
          restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ ρ)| := abs_add_le _ _
      _ ≤ KE * a ^ 2 + KR * a ^ 2 := add_le_add HEval HRval
      _ = K * a ^ 2 := by dsimp only [K]; ring
  have Hder : |deriv (restartFastShearProjectionPhase h T σ n₂ n₃) ρ -
      deriv (fun t => restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ t)) ρ| ≤ K * a := by
    rw [Hsum.deriv, add_sub_assoc]
    calc
      _ ≤ |deriv E ρ| + |deriv (restartFastShearPhase h T σ n₂ n₃) ρ -
          deriv (fun t => restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ t)) ρ| := abs_add_le _ _
      _ ≤ KE * a + KR * a := add_le_add HEder HRder
      _ = K * a := by dsimp only [K]; ring
  have Href := restartReferenceRadialPhase_shear_derivative hhsmall ha.1 hρ hσ hε h₂ h₃
  have hKa : K * a ≤ 1 / (4 * Real.sqrt 3) := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3 * K)).mp
      (ha.2.trans ((min_le_right _ _).trans (min_le_right _ _)))
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3)).mpr
    nlinarith only [H]
  have hquarter : 1 / (4 * Real.sqrt 3) ≤ 1 :=
    (div_le_one (by positivity : 0 < 4 * Real.sqrt 3)).mpr (by linarith only [hsqrt1])
  refine ⟨Hdom, Hheight, Hsum.differentiableAt, Hval, Hder, ?_, ?_⟩
  · have heq : 1 / (2 * Real.sqrt 3) = 2 * (1 / (4 * Real.sqrt 3)) := by ring
    rw [heq] at Href
    linarith only [(abs_le.mp Hder).1, Href.2.1, hKa]
  · linarith only [(abs_le.mp Hder).2, Href.2.2, hKa, hquarter]

end BianchiIX
