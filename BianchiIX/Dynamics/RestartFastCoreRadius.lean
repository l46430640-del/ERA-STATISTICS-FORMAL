import BianchiIX.Dynamics.RestartFastProjectionApproximation
import BianchiIX.Dynamics.RestartReferenceRadialBounds
import BianchiIX.Analysis.ReciprocalRadialBounds

noncomputable section

namespace BianchiIX

open Set

def restartFastCoreRadius (h T θ ζ ρ : ℝ) : ℝ :=
  let x := normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 T
  coreRadius (toProjectiveState x 0) (toProjectiveState x 2)

theorem restartFastCoreRadius_eq_reciprocal (h T θ ζ ρ : ℝ) :
    restartFastCoreRadius h T θ ζ ρ = 2 / restartFastProjectionPhase h T θ ζ ρ := by
  simp [restartFastCoreRadius, restartFastProjectionPhase]

theorem restartFastCoreRadius_deriv {h T θ ζ ρ : ℝ}
    (H : DifferentiableAt ℝ (restartFastProjectionPhase h T θ ζ) ρ)
    (hne : restartFastProjectionPhase h T θ ζ ρ ≠ 0) :
    deriv (restartFastCoreRadius h T θ ζ) ρ =
      -2 * deriv (restartFastProjectionPhase h T θ ζ) ρ /
        (restartFastProjectionPhase h T θ ζ ρ) ^ 2 := by
  have Heq : restartFastCoreRadius h T θ ζ = fun y => 2 / restartFastProjectionPhase h T θ ζ y :=
    funext (restartFastCoreRadius_eq_reciprocal h T θ ζ)
  rw [Heq, deriv_const_div 2 H hne]

/-- The exact projected entry radius and its ordinary derivative have the core scales, uniformly on the entire radial curve. -/
theorem exists_restartFastCoreRadius_bounds :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q : ℝ, 2 < q →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ 2) → ∀ ρ ∈ Icc r (2 * r),
            let T := q / 2 * Real.log (1 / r)
            let B := 8 * (L + 1) + 1
            T ∈ normalizedMaxDomain (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 ∧
            DifferentiableAt ℝ (restartFastCoreRadius h T θ ζ) ρ ∧
            6 ≤ restartFastCoreRadius h T θ ζ ρ ∧
            2 / (B * r) ≤ restartFastCoreRadius h T θ ζ ρ ∧
            restartFastCoreRadius h T θ ζ ρ ≤ 32 / r ∧
            1 / (4 * B ^ 2 * r ^ 2) ≤ -deriv (restartFastCoreRadius h T θ ζ) ρ ∧
            -deriv (restartFastCoreRadius h T θ ζ) ρ ≤ 512 * (2 * L + 4) / r ^ 2 := by
  obtain ⟨hstar, hhstar, HH⟩ := exists_restartFastProjectionPhase_approximation
  refine ⟨min hstar (1 / 16), lt_min hhstar (by norm_num), ?_⟩
  intro h hh L hL q hq
  obtain ⟨K, hK, HK⟩ := HH h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL
  obtain ⟨rA, hrA, HA⟩ := HK q hq
  let B := 8 * (L + 1) + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨min rA (min (1 / 9) (min (1 / (16 * K)) (1 / (3 * B)))),
    lt_min hrA (lt_min (by norm_num) (lt_min (by positivity) (by positivity))), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have hr9 : r ≤ 1 / 9 := (hr.2.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hrK : r ≤ 1 / (16 * K) :=
    ((hr.2.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hrB : r ≤ 1 / (3 * B) :=
    ((hr.2.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hKr : K * r ≤ 1 / 16 := by
    have H := (le_div_iff₀ (by positivity : 0 < 16 * K)).mp hrK
    linarith only [H]
  have herr : K * r ^ 2 ≤ r / 16 := by
    nlinarith only [mul_le_mul_of_nonneg_right hKr hr.1.le]
  let T := q / 2 * Real.log (1 / r)
  obtain ⟨Hdom, _, HD, Hval, _, Hdl, Hdu⟩ :=
    HA r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  obtain ⟨Hreflo, Hrefhi⟩ := restartReferenceRadialPhase_curve_bounds
    ⟨hh.1.le, hh.2.trans (min_le_right _ _)⟩ hr.1 hρ hL hθ
    ⟨hζ.1, hζ.2.trans (by nlinarith only [hr.1, hr9])⟩
  have Hlo : r / 16 ≤ restartFastProjectionPhase h T θ ζ ρ := by
    linarith only [(abs_le.mp Hval).1, Hreflo, herr]
  have Hhi : restartFastProjectionPhase h T θ ζ ρ ≤ B * r := by
    dsimp only [B]
    nlinarith only [(abs_le.mp Hval).2, Hrefhi, herr, hr.1]
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsqrtSq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by nlinarith only [hsqrtSq, hsqrt]
  have hsqrt2 : Real.sqrt (3 : ℝ) ≤ 2 := by nlinarith only [hsqrtSq, hsqrt]
  have Hdlo : 1 / 8 ≤ deriv (restartFastProjectionPhase h T θ ζ) ρ := by
    apply le_trans _ Hdl
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt 3)).mpr
    linarith only [hsqrt2]
  have Hdhi : deriv (restartFastProjectionPhase h T θ ζ) ρ ≤ 2 * L + 4 := by
    have H : (2 * L + 3) / Real.sqrt 3 ≤ 2 * L + 3 := by
      apply (div_le_iff₀ hsqrt).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hsqrt1 (by positivity : 0 ≤ 2 * L + 3)]
    linarith only [Hdu, H]
  obtain ⟨HKD, HKlo, HKhi, HKdlo, HKdhi⟩ :=
    reciprocal_radial_bounds hr.1 (show 0 ≤ 2 * L + 4 by positivity) HD Hlo Hhi Hdlo Hdhi
  have Heq : restartFastCoreRadius h T θ ζ = fun y => 2 / restartFastProjectionPhase h T θ ζ y :=
    funext (restartFastCoreRadius_eq_reciprocal h T θ ζ)
  have Hsix : 6 ≤ 2 / (B * r) := by
    apply (le_div_iff₀ (mul_pos hB hr.1)).mpr
    have H := (le_div_iff₀ (by positivity : 0 < 3 * B)).mp hrB
    nlinarith only [H]
  change _ ∧ DifferentiableAt ℝ (restartFastCoreRadius h T θ ζ) ρ ∧ _
  rw [Heq]
  exact ⟨Hdom, HKD, Hsix.trans HKlo, HKlo, HKhi, HKdlo, HKdhi⟩

end BianchiIX
