import BianchiIX.Dynamics.ShearRestartTailRadiusTransfer
import BianchiIX.Dynamics.ShearRestartFastPhase

noncomputable section

namespace BianchiIX

open Set

def restartShearTailPhase (h a q ζ ν t ρ : ℝ) : ℝ :=
  shearTailRadius (restartShearTailFlow h a q ζ ν t ρ) / Real.sqrt 3

theorem restartShearTailPhase_initial (h a q ζ ν : ℝ) :
    restartShearTailPhase h a q ζ ν 0 =
      restartFastShearPhase h (q / 2 * Real.log (1 / a)) 1 ζ ν := by
  funext ρ
  simp only [restartShearTailPhase, shearTailRadius, restartShearTailFlow, zero_add,
    restartFastShearPhase, restartRadialPhase, restartSectionCenterFlow]

/-- The endpoint physical phase retains the original reference phase and its positive ordinary radial slope. -/
theorem exists_restartShearTail_phase_approximation :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D : ℝ, 2 < q → 0 ≤ D → ∃ K > (0 : ℝ),
        ∀ P : ℝ, 6 * D + 2 < P → ∃ astar > (0 : ℝ),
          ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
            (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let f := restartShearTailPhase h a q ζ ν (shearTailTime a D)
            let f₀ := fun r => restartReferenceRadialPhase h (restartShearCurve 1 ζ ν r)
            DifferentiableAt ℝ f ρ ∧ |f ρ - f₀ ρ| ≤ K * a ^ 2 ∧
            |deriv f ρ - deriv f₀ ρ| ≤ K * a ∧
            1 / (4 * Real.sqrt 3) ≤ deriv f ρ ∧ deriv f ρ ≤ 2 / Real.sqrt 3 + 1 := by
  obtain ⟨C, hC, hT, hhT, HT⟩ := exists_restartShearTail_radius_transfer
  obtain ⟨hF, hhF, HF⟩ := exists_restartFastShearPhase_monotone
  refine ⟨min hT (min hF (1 / 16)), lt_min hhT (lt_min hhF (by norm_num)), ?_⟩
  intro h hh q D hq hD
  obtain ⟨KF, hKF, HKF⟩ := HF h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  let KT := 1280 + 32768 * (105 + 40 * C * q + 20 * D)
  have hC0 : 0 ≤ C := by linarith only [hC]
  have hq0 : 0 ≤ q := by linarith only [hq]
  have hKT : 0 < KT := by dsimp only [KT]; positivity
  let K := KT + KF
  have hK : 0 < K := add_pos hKT hKF
  refine ⟨K, hK, ?_⟩
  intro P hP
  obtain ⟨aT, haT, HAT⟩ := HT h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aF, haF, HAF⟩ := HKF q hq
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hsqrt]
  refine ⟨min aT (min aF (1 / (4 * Real.sqrt 3 * K))),
    lt_min haT (lt_min haF (by positivity)), ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ f f₀
  let F := fun r => shearTailRadius (restartShearTailFlow h a q ζ ν (shearTailTime a D) r) -
    shearTailRadius (restartShearTailFlow h a q ζ ν 0 r)
  let g := restartFastShearPhase h (q / 2 * Real.log (1 / a)) 1 ζ ν
  have hε' : 0 ≤ ε ∧ ε ≤ 1 / 64 := ⟨hε.1, by linarith only [hε.2]⟩
  obtain ⟨HFD, HFB⟩ := HAT a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  change DifferentiableAt ℝ F ρ at HFD
  change |F ρ| + a * |deriv F ρ| ≤ KT * a ^ 2 at HFB
  obtain ⟨_, HgD, Hgv, Hgd, _, _⟩ :=
    HAF a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
      ε 1 ζ ν hε' (by norm_num) ⟨hζ.1.le, hζ.2.2⟩ ⟨hν.1.le, hν.2⟩ ρ hρ
  have heq : f = fun r => F r / Real.sqrt 3 + g r := by
    funext r
    have H := congrFun (restartShearTailPhase_initial h a q ζ ν) r
    change shearTailRadius (restartShearTailFlow h a q ζ ν 0 r) / Real.sqrt 3 = g r at H
    change shearTailRadius (restartShearTailFlow h a q ζ ν (shearTailTime a D) r) / Real.sqrt 3 = _
    rw [← H]
    dsimp only [F]
    ring
  have HD : HasDerivAt f (deriv F ρ / Real.sqrt 3 + deriv g ρ) ρ := by
    rw [heq]
    exact (HFD.hasDerivAt.div_const _).add HgD.hasDerivAt
  have HFv : |F ρ / Real.sqrt 3| ≤ KT * a ^ 2 := by
    rw [abs_div, abs_of_pos hsqrt]
    exact (div_le_self (abs_nonneg _) hsqrt1).trans
      (by linarith only [HFB, mul_nonneg ha.1.le (abs_nonneg (deriv F ρ))])
  have HFd : |deriv F ρ / Real.sqrt 3| ≤ KT * a := by
    rw [abs_div, abs_of_pos hsqrt]
    apply (div_le_self (abs_nonneg _) hsqrt1).trans
    apply (mul_le_mul_iff_right₀ ha.1).mp
    nlinarith only [HFB, abs_nonneg (F ρ)]
  have Hv : |f ρ - f₀ ρ| ≤ K * a ^ 2 := by
    rw [heq, add_sub_assoc]
    exact (abs_add_le _ _).trans ((add_le_add HFv Hgv).trans_eq (by dsimp only [K]; ring))
  have Hd : |deriv f ρ - deriv f₀ ρ| ≤ K * a := by
    rw [HD.deriv, add_sub_assoc]
    exact (abs_add_le _ _).trans ((add_le_add HFd Hgd).trans_eq (by dsimp only [K]; ring))
  have Href := restartReferenceRadialPhase_shear_derivative
    ⟨hh.1.le, hh.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
    ha.1 hρ (by norm_num : |(1 : ℝ)| = 1) hε' ⟨hζ.1.le, hζ.2.2⟩ ⟨hν.1.le, hν.2⟩
  have hKa : K * a ≤ 1 / (4 * Real.sqrt 3) := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3 * K)).mp
      (ha.2.trans ((min_le_right _ _).trans (min_le_right _ _)))
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3)).mpr
    nlinarith only [H]
  have hquarter : 1 / (4 * Real.sqrt 3) ≤ 1 :=
    (div_le_one (by positivity : 0 < 4 * Real.sqrt 3)).mpr (by linarith only [hsqrt1])
  refine ⟨HD.differentiableAt, Hv, Hd, ?_, ?_⟩
  · have he : 1 / (2 * Real.sqrt 3) = 2 * (1 / (4 * Real.sqrt 3)) := by ring
    rw [he] at Href
    linarith only [(abs_le.mp Hd).1, Href.2.1, hKa]
  · linarith only [(abs_le.mp Hd).2, Href.2.2, hKa, hquarter]

end BianchiIX
