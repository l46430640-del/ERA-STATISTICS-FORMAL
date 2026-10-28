import BianchiIX.Dynamics.ShearRestartTailProjectionError

noncomputable section

namespace BianchiIX

open Set

/-- The actual growing-circle phase at the tail endpoint has the original reference phase and positive slope. -/
theorem exists_restartShearTail_projection_phase :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D : ℝ, 2 < q → 2 < D → ∃ K > (0 : ℝ),
        ∀ P : ℝ, 6 * D + 2 < P → ∃ astar > (0 : ℝ),
          ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
            (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let T := shearTailTime a D
            let f := restartShearTailProjectionPhase h a q ζ ν T
            let f₀ := fun r => restartReferenceRadialPhase h (restartShearCurve 1 ζ ν r)
            T + q / 2 * Real.log (1 / a) ∈
              normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 ζ ν ρ)) 0 ∧
            0 < 1 + restartShearTailFlow h a q ζ ν T ρ 0 ∧
            DifferentiableAt ℝ f ρ ∧ |f ρ - f₀ ρ| ≤ K * a ^ 2 ∧
            |deriv f ρ - deriv f₀ ρ| ≤ K * a ∧
            1 / (4 * Real.sqrt 3) ≤ deriv f ρ ∧ deriv f ρ ≤ 2 / Real.sqrt 3 + 1 := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearTail_projection_error
  obtain ⟨hR, hhR, HR⟩ := exists_restartShearTail_phase_approximation
  refine ⟨min hE (min hR (1 / 16)), lt_min hhE (lt_min hhR (by norm_num)), ?_⟩
  intro h hh q D hq hD
  obtain ⟨KE, hKE, HKE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D hq hD
  obtain ⟨KR, hKR, HKR⟩ := HR h
    ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ q D hq (by linarith only [hD])
  let K := KE + KR
  have hK : 0 < K := add_pos hKE hKR
  refine ⟨K, hK, ?_⟩
  intro P hP
  obtain ⟨aE, haE, HAE⟩ := HKE P hP
  obtain ⟨aR, haR, HAR⟩ := HKR P hP
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hsqrt]
  refine ⟨min aE (min aR (1 / (4 * Real.sqrt 3 * K))),
    lt_min haE (lt_min haR (by positivity)), ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ T f f₀
  let g := restartShearTailPhase h a q ζ ν T
  let E := fun r => f r - g r
  obtain ⟨Hdom, Hheight, HED, HEv, HEd⟩ :=
    HAE a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  obtain ⟨HRD, HRv, HRd, _, _⟩ :=
    HAR a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ ε ζ ν hε hζ hν ρ hρ
  have Hsum : HasDerivAt f (deriv E ρ + deriv g ρ) ρ := by
    convert! HED.hasDerivAt.add HRD.hasDerivAt using 1
    ext r
    exact (sub_add_cancel (f r) (g r)).symm
  have Hv : |f ρ - f₀ ρ| ≤ K * a ^ 2 := by
    have he : f ρ - f₀ ρ = E ρ + (g ρ - f₀ ρ) := by dsimp only [E]; ring
    rw [he]
    exact (abs_add_le _ _).trans ((add_le_add HEv HRv).trans_eq (by dsimp only [K]; ring))
  have Hd : |deriv f ρ - deriv f₀ ρ| ≤ K * a := by
    rw [Hsum.deriv, add_sub_assoc]
    exact (abs_add_le _ _).trans ((add_le_add HEd HRd).trans_eq (by dsimp only [K]; ring))
  have Href := restartReferenceRadialPhase_shear_derivative
    ⟨hh.1.le, hh.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
    ha.1 hρ (by norm_num : |(1 : ℝ)| = 1) ⟨hε.1, by linarith only [hε.2]⟩
    ⟨hζ.1.le, hζ.2.2⟩ ⟨hν.1.le, hν.2⟩
  have hKa : K * a ≤ 1 / (4 * Real.sqrt 3) := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3 * K)).mp
      (ha.2.trans ((min_le_right _ _).trans (min_le_right _ _)))
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3)).mpr
    nlinarith only [H]
  have hquarter : 1 / (4 * Real.sqrt 3) ≤ 1 :=
    (div_le_one (by positivity : 0 < 4 * Real.sqrt 3)).mpr (by linarith only [hsqrt1])
  refine ⟨Hdom, Hheight, Hsum.differentiableAt, Hv, Hd, ?_, ?_⟩
  · have he : 1 / (2 * Real.sqrt 3) = 2 * (1 / (4 * Real.sqrt 3)) := by ring
    rw [he] at Href
    linarith only [(abs_le.mp Hd).1, Href.2.1, hKa]
  · linarith only [(abs_le.mp Hd).2, Href.2.2, hKa, hquarter]

end BianchiIX
