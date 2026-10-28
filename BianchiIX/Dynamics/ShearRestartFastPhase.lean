import BianchiIX.Dynamics.ShearRestartCurves

noncomputable section

namespace BianchiIX

open Set

def restartFastShearPhase (h T σ n₂ n₃ ρ : ℝ) : ℝ :=
  restartRadialPhase (restartSectionCenterFlow h T (restartShearCurve σ n₂ n₃ ρ))

/-- The exact fast-layer phase retains the reference shear slope, uniformly in both weak walls. -/
theorem exists_restartFastShearPhase_monotone :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∃ K > (0 : ℝ), ∀ q : ℝ, 2 < q → ∃ astar > (0 : ℝ),
        ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε σ n₂ n₃ : ℝ,
          (0 ≤ ε ∧ ε ≤ 1 / 64) → |σ| = 1 →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let T := q / 2 * Real.log (1 / a)
            T ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) 0 ∧
            DifferentiableAt ℝ (restartFastShearPhase h T σ n₂ n₃) ρ ∧
            |restartFastShearPhase h T σ n₂ n₃ ρ -
              restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ ρ)| ≤ K * a ^ 2 ∧
            |deriv (restartFastShearPhase h T σ n₂ n₃) ρ -
              deriv (fun x => restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ x)) ρ| ≤ K * a ∧
            1 / (4 * Real.sqrt 3) ≤ deriv (restartFastShearPhase h T σ n₂ n₃) ρ ∧
            deriv (restartFastShearPhase h T σ n₂ n₃) ρ ≤ 2 / Real.sqrt 3 + 1 := by
  obtain ⟨h₀, hh₀, H₀⟩ := exists_restartSection_radial_approximation
  refine ⟨min h₀ (1 / 16), lt_min hh₀ (by norm_num), ?_⟩
  intro h hh
  have hhsmall : 0 ≤ h ∧ h ≤ 1 / 16 := ⟨hh.1.le, hh.2.trans (min_le_right _ _)⟩
  obtain ⟨K, hK, HK⟩ := H₀ h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ 1 2 (by norm_num) (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro q hq
  obtain ⟨a₀, ha₀, Ha₀⟩ := HK q hq
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := by positivity
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hsqrt]
  refine ⟨min a₀ (1 / (4 * Real.sqrt 3 * K)), lt_min ha₀ (by positivity), ?_⟩
  intro a ha ε σ n₂ n₃ hε hσ h₂ h₃ ρ hρ T
  let Z := restartShearCurve σ n₂ n₃ ρ
  have hann := restartShearCurve_annulus ha.1 hρ hσ hε h₂ h₃
  have H := Ha₀ a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ Z hann.1 (by simpa using hann.2.1)
  have Href := restartReferenceRadialPhase_shear_derivative hhsmall ha.1 hρ hσ hε h₂ h₃
  have Herr := H.2.1.hasFDerivAt.comp_hasDerivAt ρ (hasDerivAt_restartShearCurve σ n₂ n₃ ρ)
  have Hsum : HasDerivAt (restartFastShearPhase h T σ n₂ n₃)
      (fderiv ℝ (restartSectionRadialError h T) Z (restartShearDirection σ) +
        deriv (fun x => restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ x)) ρ) ρ := by
    convert! Herr.add Href.1.hasDerivAt using 1
    ext x
    simp only [Function.comp_apply, Pi.add_apply, restartSectionRadialError, restartFastShearPhase,
      sub_add_cancel, T]
  have HD : |deriv (restartFastShearPhase h T σ n₂ n₃) ρ -
      deriv (fun x => restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ x)) ρ| ≤ K * a := by
    rw [Hsum.deriv, add_sub_cancel_right]
    have HV := (fderiv ℝ (restartSectionRadialError h T) Z).le_opNorm (restartShearDirection σ)
    rw [restartShearDirection_norm hσ, mul_one] at HV
    exact HV.trans H.2.2.2
  have hKa : K * a ≤ 1 / (4 * Real.sqrt 3) := by
    have HB := (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3 * K)).mp
      (ha.2.trans (min_le_right _ _))
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3)).mpr
    nlinarith only [HB]
  have hquarter : 1 / (4 * Real.sqrt 3) ≤ 1 :=
    (div_le_one (by positivity : 0 < 4 * Real.sqrt 3)).mpr (by linarith only [hsqrt1])
  refine ⟨H.1, Hsum.differentiableAt, H.2.2.1, HD, ?_, ?_⟩
  · have Heq : 1 / (2 * Real.sqrt 3) = 2 * (1 / (4 * Real.sqrt 3)) := by ring
    rw [Heq] at Href
    linarith only [(abs_le.mp HD).1, Href.2.1, hKa]
  · linarith only [(abs_le.mp HD).2, Href.2.2, hKa, hquarter]

theorem exists_restartFastShearPhase_secant :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q : ℝ, 2 < q →
      ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε σ n₂ n₃ : ℝ,
        (0 ≤ ε ∧ ε ≤ 1 / 64) → |σ| = 1 →
        (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) →
          let f := restartFastShearPhase h (q / 2 * Real.log (1 / a)) σ n₂ n₃
          StrictMonoOn f (Icc a (2 * a)) ∧
          ∀ x ∈ Icc a (2 * a), ∀ y ∈ Icc a (2 * a), x ≤ y →
            (y - x) / (4 * Real.sqrt 3) ≤ f y - f x ∧
            f y - f x ≤ (2 / Real.sqrt 3 + 1) * (y - x) := by
  obtain ⟨hstar, hhstar, H⟩ := exists_restartFastShearPhase_monotone
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh q hq
  obtain ⟨K, _, HK⟩ := H h hh
  obtain ⟨astar, hastar, Ha⟩ := HK q hq
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε σ n₂ n₃ hε hσ h₂ h₃ f
  have HD (x : ℝ) (hx : x ∈ Icc a (2 * a)) : DifferentiableAt ℝ f x :=
    (Ha a ha ε σ n₂ n₃ hε hσ h₂ h₃ x hx).2.1
  have HL (x : ℝ) (hx : x ∈ Icc a (2 * a)) : 1 / (4 * Real.sqrt 3) ≤ deriv f x :=
    (Ha a ha ε σ n₂ n₃ hε hσ h₂ h₃ x hx).2.2.2.2.1
  have HU (x : ℝ) (hx : x ∈ Icc a (2 * a)) : deriv f x ≤ 2 / Real.sqrt 3 + 1 :=
    (Ha a ha ε σ n₂ n₃ hε hσ h₂ h₃ x hx).2.2.2.2.2
  have HC : ContinuousOn f (Icc a (2 * a)) := fun x hx => (HD x hx).continuousAt.continuousWithinAt
  have HI : DifferentiableOn ℝ f (interior (Icc a (2 * a))) :=
    fun x hx => (HD x (interior_subset hx)).differentiableWithinAt
  constructor
  · apply strictMonoOn_of_deriv_pos (convex_Icc _ _) HC
    intro x hx
    exact lt_of_lt_of_le (by positivity : 0 < 1 / (4 * Real.sqrt (3 : ℝ))) (HL x (interior_subset hx))
  · intro x hx y hy hxy
    constructor
    · have HB := (convex_Icc a (2 * a)).mul_sub_le_image_sub_of_le_deriv HC HI
        (fun t ht => HL t (interior_subset ht)) x hx y hy hxy
      simpa only [one_div_mul_eq_div] using HB
    · exact (convex_Icc a (2 * a)).image_sub_le_mul_sub_of_deriv_le HC HI
        (fun t ht => HU t (interior_subset ht)) x hx y hy hxy

end BianchiIX
