import BianchiIX.Dynamics.RestartConnectionPhase
import BianchiIX.Analysis.RestartOutputBudget
import BianchiIX.Analysis.MobiusRadialCurve

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The full E.14 phase approximation and its positive ordinary radial slope at the actual restart. -/
theorem exists_restartConnection_output_phase :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∃ C : ℝ, 0 < C ∧ ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) → ∀ ρ ∈ Icc r (2 * r),
            let s := q / 2 * Real.log (1 / r)
            let Y := restartFastProjectiveEntry h s θ ζ
            let F := fun a => restartReferenceRadialPhase h (restartRadialCurve θ ζ a)
            ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (Y ρ) 0 t 2 = 1} T ∧
              ∃ τ : ProjectiveState → ℝ, τ (Y ρ) = T ∧ ContDiffAt ℝ 2 τ (Y ρ) ∧
                (∀ᶠ y in 𝓝 (Y ρ), IsLeast {t | 0 < t ∧
                  t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧ projectiveOriginalFlow y 0 t 2 = 1} (τ y)) ∧
                let out := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a))
                let f := fun a => coreRadius (out a 0) (out a 2)
                let p := fun a => coreExitConnectionParameters ![f a, out a 1, out a 3]
                let xr := fun a => 2 / connectionReturnPhysicalState (p a) 0
                connectionReturnValid (p ρ) ∧ connectionReturnState (p ρ) = toProjectiveState
                  (normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0
                    (s + T + connectionReturnTime (p ρ))) ∧
                DifferentiableAt ℝ xr ρ ∧ |xr ρ - F ρ| ≤ C * r ^ 2 ∧
                |deriv xr ρ - deriv F ρ| ≤ C * r ∧
                1 / (8 * Real.sqrt 3) ≤ deriv xr ρ ∧ deriv xr ρ ≤ C := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartConnection_phase_error
  obtain ⟨hF, hhF, HF⟩ := exists_restartFastProjectionPhase_approximation
  obtain ⟨hV, hhV, HV⟩ := exists_restartFastProjectiveEntry_bounds
  refine ⟨min hE (min hF hV), lt_min hhE (lt_min hhF hhV), ?_⟩
  intro h hh L hL
  obtain ⟨K, hK, Cδ, hCδ, HKE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL
  obtain ⟨KF, hKF, HKF⟩ := HF h ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_left _ _)⟩ L hL
  let M := 8 * (L + 1)
  let B := 32 * h + 2048 * M
  let E := 16 * K + 4 * (4096 * coreVariationBound) * K ^ 2 + Cδ
  let D := (2 * L + 3) / Real.sqrt 3 + 1
  let V := 8 * E * K ^ 2 * B
  let A := (8 * E * K ^ 2 + 32 * E * K ^ 4) * B
  let H := A + 8 * K * D
  let C := 1 + KF + (V + 2 * K ^ 2) + H + D
  have hK0 : 0 < K := by linarith only [hK]
  have hM : 0 < M := by dsimp only [M]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity [hh.1]
  have hE : 0 < E := by dsimp only [E, coreVariationBound]; positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hH : 0 < H := by dsimp only [H]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro q P hq hP
  have hq2 : 2 < q := by linarith only [hq]
  obtain ⟨rE, hrE, HRE⟩ := HKE q P hq hP
  obtain ⟨rF, hrF, HRF⟩ := HKF q hq2
  obtain ⟨rV, hrV, HRV⟩ := HV h ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_right _ _)⟩ L hL q hq2
  refine ⟨min rE (min rF (min rV (min 1 (1 / (8 * Real.sqrt 3 * H))))),
    lt_min hrE (lt_min hrF (lt_min hrV (lt_min (by norm_num) (by positivity)))), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have hr0 := hr.1
  have hrF' := hr.2.trans (min_le_right _ _)
  have hrV' := hrF'.trans (min_le_right _ _)
  have hrB' := hrV'.trans (min_le_right _ _)
  have hr1 := hrB'.trans (min_le_left _ _)
  have hrH := hrB'.trans (min_le_right _ _)
  have hζ2 : 0 ≤ ζ ∧ ζ ≤ r ^ 2 := by
    refine ⟨hζ.1.le, hζ.2.trans ?_⟩
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hr.1 hr1 (by linarith only [hP] : (2 : ℝ) ≤ P)
  let s := q / 2 * Real.log (1 / r)
  let Y := restartFastProjectiveEntry h s θ ζ
  let k := restartFastCoreRadius h s θ ζ
  let x := restartFastProjectionPhase h s θ ζ
  let F := fun a => restartReferenceRadialPhase h (restartRadialCurve θ ζ a)
  let U := Y ρ 1
  let W := Y ρ 2 * Y ρ 3
  obtain ⟨_, _, hx, hxval, hxder, hxlo, hxhi⟩ :=
    HRF r ⟨hr.1, hrF'.trans (min_le_left _ _)⟩ θ ζ hθ hζ2 ρ hρ
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hu, _, hw, _⟩ :=
    HRV r ⟨hr.1, hrV'.trans (min_le_left _ _)⟩ θ ζ hθ hζ2 ρ hρ
  obtain ⟨T, hT, hfirst, τ, hτ, hcτ, hnear, hvalid, horbit, _, hk6, hklo, _, hU, hW,
    _, _, _, _, _, _, _, _, _, _, hRD, hRv, hRd⟩ := HRE r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  let out := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a))
  let f := fun a => coreRadius (out a 0) (out a 2)
  let p := fun a => coreExitConnectionParameters ![f a, out a 1, out a 3]
  let xr := fun a => 2 / connectionReturnPhysicalState (p a) 0
  let R := fun a => xr a - x a / (1 - x a)
  let Q := fun a => x a / (1 - x a) - x a
  change DifferentiableAt ℝ R ρ at hRD
  change |R ρ| ≤ 8 * E * K ^ 2 * r ^ 2 * (U + r * W ^ 2) at hRv
  change |deriv R ρ| ≤ (8 * E * K ^ 2 + 32 * E * K ^ 4) * (U + r * W) at hRd
  have Hsum := (restart_entry_linear_amplitude_budget ⟨hr.1, hr1⟩ hh.1.le hM.le hq hP
    ⟨hζ.1.le, hζ.2⟩ ⟨hu.1.le, hu.2⟩ hw).2.2
  change U + W ≤ B * r at Hsum
  have hW0 := hW.1
  have hWsq : r * W ^ 2 ≤ W := by
    have HW := mul_le_mul_of_nonneg_right hW.2 hW.1
    nlinarith only [HW, mul_le_mul_of_nonneg_right hr1 (sq_nonneg W)]
  have hvalueBudget : U + r * W ^ 2 ≤ B :=
    (add_le_add le_rfl hWsq).trans (Hsum.trans (mul_le_of_le_one_right hB.le hr1))
  have hderBudget : U + r * W ≤ B * r :=
    (add_le_add le_rfl (mul_le_of_le_one_left hW.1 hr1)).trans Hsum
  have HRv : |R ρ| ≤ V * r ^ 2 := hRv.trans
    ((mul_le_mul_of_nonneg_left hvalueBudget (by positivity)).trans_eq (by dsimp only [V]; ring))
  have HRd : |deriv R ρ| ≤ A * r := hRd.trans
    ((mul_le_mul_of_nonneg_left hderBudget (by positivity)).trans_eq (by dsimp only [A]; ring))
  have hk0 : 0 < k ρ := by linarith only [hk6]
  have hx0 : 0 ≤ x ρ := (div_pos (by norm_num) hk0).le
  have hxhalf : x ρ ≤ 1 / 2 := by
    change 2 / k ρ ≤ 1 / 2
    apply (div_le_iff₀ hk0).mpr
    linarith only [hk6]
  have hxr : x ρ ≤ K * r := by
    change 2 / k ρ ≤ K * r
    apply (div_le_iff₀ hk0).mpr
    nlinarith only [(div_le_iff₀ (mul_pos hK0 hr.1)).mp hklo]
  have hdx0 : 0 ≤ deriv x ρ := (by positivity : (0 : ℝ) ≤ 1 / (4 * Real.sqrt 3)).trans hxlo
  have hdx : |deriv x ρ| ≤ D := by rw [abs_of_nonneg hdx0]; exact hxhi
  obtain ⟨hQD, HQv, HQd⟩ := mobius_radial_correction_bounds hx hr.1.le hK0.le hD.le ⟨hx0, hxhalf⟩ hxr hdx
  change DifferentiableAt ℝ Q ρ at hQD
  have HX : HasDerivAt xr (deriv R ρ + deriv Q ρ + deriv x ρ) ρ := by
    apply ((hRD.hasDerivAt.add hQD.hasDerivAt).add hx.hasDerivAt).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun a => by
      change xr a = (R a + Q a) + x a
      dsimp only [R, Q]
      ring
  have Hder : |deriv xr ρ - deriv x ρ| ≤ H * r := by
    rw [HX.deriv]
    have Htri := (abs_add_le (deriv R ρ) (deriv Q ρ)).trans (add_le_add HRd HQd)
    simpa only [add_sub_cancel_right, show A * r + 8 * K * D * r = H * r by dsimp only [H]; ring] using Htri
  have Hsmall : H * r ≤ 1 / (8 * Real.sqrt 3) := by
    apply (le_div_iff₀ (by positivity : 0 < 8 * Real.sqrt 3)).mpr
    nlinarith only [(le_div_iff₀ (by positivity : 0 < 8 * Real.sqrt 3 * H)).mp hrH]
  have Hquarter : 1 / (8 * Real.sqrt 3) ≤ 1 := by
    have Hs : 1 ≤ Real.sqrt (3 : ℝ) := by nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hsqrt]
    exact (div_le_one (by positivity)).mpr (by linarith only [Hs])
  refine ⟨T, hT, hfirst, τ, hτ, hcτ, hnear, hvalid, horbit, HX.differentiableAt, ?_, ?_, ?_, ?_⟩
  · have heq : xr ρ - F ρ = R ρ + Q ρ + (x ρ - F ρ) := by dsimp only [R, Q]; ring
    rw [heq]
    have Htri := (abs_add_le (R ρ + Q ρ) (x ρ - F ρ)).trans
      (add_le_add ((abs_add_le (R ρ) (Q ρ)).trans (add_le_add HRv HQv)) hxval)
    have HC : V + 2 * K ^ 2 + KF ≤ C := by dsimp only [C]; linarith only [hH, hD]
    exact Htri.trans (by nlinarith only [mul_le_mul_of_nonneg_right HC (sq_nonneg r)])
  · have Htri := (abs_sub_le (deriv xr ρ) (deriv x ρ) (deriv F ρ)).trans (add_le_add Hder hxder)
    have HC : H + KF ≤ C := by dsimp only [C]; nlinarith only [hV, sq_nonneg K, hD]
    exact Htri.trans (by nlinarith only [mul_le_mul_of_nonneg_right HC hr.1.le])
  · have Heq : 1 / (4 * Real.sqrt 3) = 2 * (1 / (8 * Real.sqrt 3)) := by ring
    rw [Heq] at hxlo
    linarith only [(abs_le.mp Hder).1, hxlo, Hsmall]
  · have HC : D + 1 ≤ C := by dsimp only [C]; nlinarith only [hKF, hV, sq_nonneg K, hH]
    linarith only [(abs_le.mp Hder).2, hxhi, Hsmall, Hquarter, HC]

end BianchiIX
