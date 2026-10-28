import BianchiIX.Dynamics.ShearRestartConnectionPhase
import BianchiIX.Dynamics.ShearRestartFastPhaseComparison
import BianchiIX.Analysis.MobiusRadialCurve

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The actual shear connection retains the reference phase and a uniformly positive ordinary radial slope. -/
theorem exists_restartShearConnection_output_phase :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∃ C > (0 : ℝ), ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
            (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
            n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
              let s := q / 2 * Real.log (1 / a)
              let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃
              let T := partialCoreDownwardReturnTime (Y ρ)
              let out := fun b => projectiveOriginalFlow (Y b) 0 (partialCoreDownwardReturnTime (Y b))
              let f := fun b => coreRadius (out b 0) (out b 2)
              let p := fun b => coreExitConnectionParameters ![f b, out b 1, out b 3]
              let xr := fun b => 2 / connectionReturnPhysicalState (p b) 0
              let F := fun b => restartReferenceRadialPhase h (restartShearCurve 1 n₂ n₃ b)
              1 ≤ Y ρ 2 →
              0 < T ∧ IsLeast {t | s < t ∧ toProjectiveState
                (normalizedMaxCurve (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 t) 2 = 1} (s + T) ∧
              connectionReturnValid (p ρ) ∧ connectionReturnState (p ρ) = toProjectiveState
                (normalizedMaxCurve (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0
                  (s + T + connectionReturnTime (p ρ))) ∧
              DifferentiableAt ℝ xr ρ ∧ |xr ρ - F ρ| ≤ C * a ^ 2 ∧
              |deriv xr ρ - deriv F ρ| ≤ C * a ∧
              1 / (8 * Real.sqrt 3) ≤ deriv xr ρ ∧ deriv xr ρ ≤ C := by
  obtain ⟨hE, hhE, K, hK, Cδ, hCδ, HE⟩ := exists_restartShearConnection_phase_error
  obtain ⟨hF, hhF, HF⟩ := exists_restartFastShearProjectionPhase_approximation
  refine ⟨min hE hF, lt_min hhE hhF, ?_⟩
  intro h hh
  obtain ⟨KF, hKF, HKF⟩ := HF h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩
  let E := 16 * K + 4 * (4096 * coreVariationBound) * K ^ 2 + Cδ
  let D := 2 / Real.sqrt 3 + 1
  let V := 8 * E * K ^ 3
  let A := (8 * E * K ^ 2 + 32 * E * K ^ 4) * K
  let H := A + 8 * K * D
  let C := 1 + KF + (V + 2 * K ^ 2) + H + D
  have hK0 : 0 < K := by linarith only [hK]
  have hE : 0 < E := by dsimp only [E, coreVariationBound]; positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hH : 0 < H := by dsimp only [H]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro q P hq hP
  obtain ⟨aE, haE, HaE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
  obtain ⟨aF, haF, HaF⟩ := HKF q P (by linarith only [hq]) (by linarith only [hP])
  refine ⟨min aE (min aF (1 / (8 * Real.sqrt 3 * H))),
    lt_min haE (lt_min haF (by positivity)), ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s Y T out f p xr F hv
  have haF' := ha.2.trans (min_le_right _ _)
  have haH := haF'.trans (min_le_right _ _)
  let k := restartFastShearCoreRadius h s 1 n₂ n₃
  let x := restartFastShearProjectionPhase h s 1 n₂ n₃
  let U := Y ρ 1
  let W := Y ρ 2 * Y ρ 3
  obtain ⟨_, _, hx, hxval, hxder, hxlo, hxhi⟩ :=
    HaF a ⟨ha.1, haF'.trans (min_le_left _ _)⟩ ε 1 n₂ n₃ hε (by norm_num)
      h₂ ⟨h₃.1.le, h₃.2⟩ h₃P ρ hρ
  obtain ⟨hT, hfirst, hvalid, horbit, ha1, hk6, hklo, _, hU, hW, Hsum,
    _, _, _, _, _, _, _, _, _, hRD, hRv, hRd⟩ :=
    HaE a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ hv
  let R := fun b => xr b - x b / (1 - x b)
  let Q := fun b => x b / (1 - x b) - x b
  change DifferentiableAt ℝ R ρ at hRD
  change |R ρ| ≤ 8 * E * K ^ 2 * a ^ 2 * (U + a * W ^ 2) at hRv
  change |deriv R ρ| ≤ (8 * E * K ^ 2 + 32 * E * K ^ 4) * (U + a * W) at hRd
  have hW0 : 0 ≤ W := hW.1.le
  have hWsq : a * W ^ 2 ≤ W := by
    have HW := mul_le_mul_of_nonneg_right hW.2 hW0
    nlinarith only [HW, mul_le_mul_of_nonneg_right ha1 (sq_nonneg W)]
  have hvalueBudget : U + a * W ^ 2 ≤ K :=
    (add_le_add le_rfl hWsq).trans (Hsum.trans (mul_le_of_le_one_right hK0.le ha1))
  have hderBudget : U + a * W ≤ K * a :=
    (add_le_add le_rfl (mul_le_of_le_one_left hW0 ha1)).trans Hsum
  have HRv : |R ρ| ≤ V * a ^ 2 := hRv.trans
    ((mul_le_mul_of_nonneg_left hvalueBudget (by positivity)).trans_eq (by dsimp only [V]; ring))
  have HRd : |deriv R ρ| ≤ A * a := hRd.trans
    ((mul_le_mul_of_nonneg_left hderBudget (by positivity)).trans_eq (by dsimp only [A]; ring))
  have hk0 : 0 < k ρ := by linarith only [hk6]
  have hx0 : 0 ≤ x ρ := (div_pos (by norm_num) hk0).le
  have hxhalf : x ρ ≤ 1 / 2 := by
    change 2 / k ρ ≤ 1 / 2
    apply (div_le_iff₀ hk0).mpr
    linarith only [hk6]
  have hxa : x ρ ≤ K * a := by
    change 2 / k ρ ≤ K * a
    apply (div_le_iff₀ hk0).mpr
    nlinarith only [(div_le_iff₀ (mul_pos hK0 ha.1)).mp hklo]
  have hdx0 : 0 ≤ deriv x ρ := (by positivity : (0 : ℝ) ≤ 1 / (4 * Real.sqrt 3)).trans hxlo
  have hdx : |deriv x ρ| ≤ D := by rw [abs_of_nonneg hdx0]; exact hxhi
  obtain ⟨hQD, HQv, HQd⟩ := mobius_radial_correction_bounds hx ha.1.le hK0.le hD.le ⟨hx0, hxhalf⟩ hxa hdx
  change DifferentiableAt ℝ Q ρ at hQD
  have HX : HasDerivAt xr (deriv R ρ + deriv Q ρ + deriv x ρ) ρ := by
    apply ((hRD.hasDerivAt.add hQD.hasDerivAt).add hx.hasDerivAt).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun b => by
      change xr b = (R b + Q b) + x b
      dsimp only [R, Q]
      ring
  have Hder : |deriv xr ρ - deriv x ρ| ≤ H * a := by
    rw [HX.deriv]
    have Htri := (abs_add_le (deriv R ρ) (deriv Q ρ)).trans (add_le_add HRd HQd)
    simpa only [add_sub_cancel_right, show A * a + 8 * K * D * a = H * a by dsimp only [H]; ring] using Htri
  have Hsmall : H * a ≤ 1 / (8 * Real.sqrt 3) := by
    apply (le_div_iff₀ (by positivity : 0 < 8 * Real.sqrt 3)).mpr
    nlinarith only [(le_div_iff₀ (by positivity : 0 < 8 * Real.sqrt 3 * H)).mp haH]
  have Hquarter : 1 / (8 * Real.sqrt 3) ≤ 1 := by
    have Hs : 1 ≤ Real.sqrt (3 : ℝ) := by nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hsqrt]
    exact (div_le_one (by positivity)).mpr (by linarith only [Hs])
  refine ⟨hT, hfirst, hvalid, horbit, HX.differentiableAt, ?_, ?_, ?_, ?_⟩
  · have heq : xr ρ - F ρ = R ρ + Q ρ + (x ρ - F ρ) := by dsimp only [R, Q]; ring
    rw [heq]
    have Htri := (abs_add_le (R ρ + Q ρ) (x ρ - F ρ)).trans
      (add_le_add ((abs_add_le (R ρ) (Q ρ)).trans (add_le_add HRv HQv)) hxval)
    have HC : V + 2 * K ^ 2 + KF ≤ C := by dsimp only [C]; linarith only [hH, hD]
    exact Htri.trans (by nlinarith only [mul_le_mul_of_nonneg_right HC (sq_nonneg a)])
  · have Htri := (abs_sub_le (deriv xr ρ) (deriv x ρ) (deriv F ρ)).trans (add_le_add Hder hxder)
    have HC : H + KF ≤ C := by dsimp only [C]; nlinarith only [hV, sq_nonneg K, hD]
    exact Htri.trans (by nlinarith only [mul_le_mul_of_nonneg_right HC ha.1.le])
  · have Heq : 1 / (4 * Real.sqrt 3) = 2 * (1 / (8 * Real.sqrt 3)) := by ring
    rw [Heq] at hxlo
    linarith only [(abs_le.mp Hder).1, hxlo, Hsmall]
  · have HC : D + 1 ≤ C := by dsimp only [C]; nlinarith only [hKF, hV, sq_nonneg K, hH]
    linarith only [(abs_le.mp Hder).2, hxhi, Hsmall, Hquarter, HC]

end BianchiIX
