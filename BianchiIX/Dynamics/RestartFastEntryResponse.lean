import BianchiIX.Dynamics.RestartFastAngleResponse
import BianchiIX.Analysis.RadialAmplitudeDerivatives
import BianchiIX.Dynamics.ForwardComplete

noncomputable section

namespace BianchiIX

open Set

/-- Ordinary radial responses of the exact entry, with amplitude factors retained at zero weak walls. -/
theorem exists_restartFastEntry_radial_response :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∃ K : ℝ, 0 < K ∧ ∀ q : ℝ, 2 < q →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ 2) → ∀ ρ ∈ Icc r (2 * r),
            let T := q / 2 * Real.log (1 / r)
            let Y := restartFastProjectiveEntry h T θ ζ
            let p := fun y => Y y 2 * Y y 3
            T ∈ normalizedMaxDomain (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 ∧
            DifferentiableAt ℝ Y ρ ∧ DifferentiableAt ℝ (restartFastCoreAngle h T θ ζ) ρ ∧
            |deriv (restartFastCoreAngle h T θ ζ) ρ| ≤ K / r ∧
            (∀ i : Fin 3, 0 ≤ Y ρ i.succ ∧
              |deriv (fun y => Y y i.succ) ρ| ≤ K * Y ρ i.succ / r) ∧
            DifferentiableAt ℝ p ρ ∧ 0 ≤ p ρ ∧ |deriv p ρ| ≤ K * p ρ / r ∧
            0 < Y ρ 1 ∧ DifferentiableAt ℝ (fun y => Real.log (Y y 1)) ρ ∧
            |deriv (fun y => Real.log (Y y 1)) ρ| ≤ K / r ∧
            (0 < ζ → 0 < p ρ ∧ DifferentiableAt ℝ (fun y => Real.log (p y)) ρ ∧
              |deriv (fun y => Real.log (Y y 1)) ρ| + |deriv (fun y => Real.log (p y)) ρ| ≤ K / r) ∧
            (ζ = 0 → Y ρ 3 = 0 ∧ deriv (fun y => Y y 3) ρ = 0 ∧ p ρ = 0 ∧ deriv p ρ = 0) := by
  obtain ⟨C, hC, HC⟩ := exists_restartFastEntry_control
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hC
  refine ⟨1 / (4 * C), by positivity, ?_⟩
  intro h hh L hL
  let M := 8 * (L + 1)
  let D := 2 * (L + 1)
  let E := 8 * C * (L + 1)
  let F := 512 * M * D
  let B := E + F
  let K := 3 * B + 20 * M * D
  have hM : 0 < M := by dsimp only [M]; positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  have hE : 0 < E := by dsimp only [E]; positivity
  have hF : 0 < F := by dsimp only [F]; positivity
  have hB : 0 < B := add_pos hE hF
  have hK : 0 < K := by dsimp only [K]; positivity
  have hDE : 2 * D ≤ E := by
    dsimp only [D, E]
    nlinarith only [hL, mul_le_mul_of_nonneg_right hC (show 0 ≤ L + 1 by positivity)]
  have hBK : B ≤ K := by dsimp only [K]; nlinarith only [hB, mul_pos hM hD]
  have h2BK : B + B ≤ K := by dsimp only [K]; nlinarith only [hB, mul_pos hM hD]
  have h3BK : 3 * B ≤ K := by dsimp only [K]; nlinarith only [mul_pos hM hD]
  have hAK : 20 * M * D ≤ K := by dsimp only [K]; linarith only [hB]
  refine ⟨K, hK, ?_⟩
  intro q hq
  obtain ⟨rstar, hrstar, HR⟩ := HC h hh L hL q hq
  refine ⟨rstar, hrstar, ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  let T := q / 2 * Real.log (1 / r)
  let Z := restartRadialCurve θ ζ ρ
  let P := fun y => restartSectionRadialState h T (restartRadialCurve θ ζ y)
  let v := fderiv ℝ (restartSectionRadialState h T) Z (restartRadialDirection θ)
  let A := restartFastProjectionHeight h T θ ζ
  let Y := restartFastProjectiveEntry h T θ ζ
  let p := fun y => Y y 2 * Y y 3
  obtain ⟨_, hsmall, hT, hrad, hdom, _, hneg, Hcurve, hnpos, _, hp, ha, hb, hnsmall, hbsmall, hv, hnv, hwv⟩ :=
    HR r hr θ ζ hθ hζ ρ hρ
  change HasDerivAt P v ρ at Hcurve
  change ‖P ρ‖ ≤ M * r at hp
  change ‖v‖ ≤ D at hv
  change 0 < (P ρ).1 at hnpos
  change r / 2 ≤ (P ρ).2 1 at ha
  change 0 ≤ (P ρ).2 2 ∧ (P ρ).2 2 ≤ 2 * ζ at hb
  change |v.1| ≤ D * (P ρ).1 / r at hnv
  change |v.2 2| ≤ E * (P ρ).2 2 / r at hwv
  obtain ⟨HAD, HAlo, HAhi, HAd⟩ := restartFastProjectionHeight_bounds hrad hT
    (by linarith only [hneg]) Hcurve hr.1 hp hsmall ha ⟨hnpos.le, hnsmall⟩ ⟨hb.1, hbsmall⟩ hv
  change DifferentiableAt ℝ A ρ at HAD
  change r ^ 2 / 16 ≤ A ρ at HAlo
  change A ρ ≤ 10 * (M * r) ^ 2 at HAhi
  change |deriv A ρ| ≤ 32 * (M * r) * D at HAd
  have hA : 0 < A ρ := lt_of_lt_of_le (by positivity [hr.1]) HAlo
  have HArel : |deriv A ρ| ≤ F * A ρ / r := by
    apply (le_div_iff₀ hr.1).mpr
    have Hlo := mul_le_mul_of_nonneg_left HAlo hF.le
    have Hhi := mul_le_mul_of_nonneg_right HAd hr.1.le
    dsimp only [F] at Hlo ⊢
    nlinarith only [Hlo, Hhi]
  have Hn : HasDerivAt (fun y => (P y).1) v.1 ρ :=
    (ContinuousLinearMap.fst ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt ρ Hcurve
  have Hc (i : Fin 3) : HasDerivAt (fun y => (P y).2 i) (v.2 i) ρ := by
    let Q : RestartCenterState →L[ℝ] ℝ := ContinuousLinearMap.proj i
    exact Q.hasFDerivAt.comp_hasDerivAt ρ
      ((ContinuousLinearMap.snd ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt ρ Hcurve)
  have Hvc (i : Fin 3) : |v.2 i| ≤ D := (norm_le_pi_norm v.2 i).trans ((norm_snd_le v).trans hv)
  have ha0 : 0 < (P ρ).2 1 := by linarith only [ha, hr.1]
  have Hnrel : |v.1| ≤ E * (P ρ).1 / r := hnv.trans (by
    apply div_le_div_of_nonneg_right _ hr.1.le
    apply mul_le_mul_of_nonneg_right _ hnpos.le
    linarith only [hDE, hD])
  have Harel : |v.2 1| ≤ E * (P ρ).2 1 / r := (Hvc 1).trans (by
    apply (le_div_iff₀ hr.1).mpr
    have H₁ := mul_le_mul_of_nonneg_left ha hD.le
    have H₂ := mul_le_mul_of_nonneg_right hDE ha0.le
    nlinarith only [H₁, H₂])
  have HU := scaled_quotient_radial_derivative_bound Hn HAD.hasDerivAt hr.1
    (Real.sqrt_nonneg (3 : ℝ)) hnpos.le hA Hnrel HArel
  have HV := scaled_quotient_radial_derivative_bound (Hc 1) HAD.hasDerivAt hr.1
    (Real.sqrt_nonneg (3 : ℝ)) ha0.le hA Harel HArel
  have HW := scaled_quotient_radial_derivative_bound (Hc 2) HAD.hasDerivAt hr.1
    (Real.sqrt_nonneg (3 : ℝ)) hb.1 hA hwv HArel
  change DifferentiableAt ℝ (fun y => Y y 1) ρ ∧ |deriv (fun y => Y y 1) ρ| ≤ B * Y ρ 1 / r at HU
  change DifferentiableAt ℝ (fun y => Y y 2) ρ ∧ |deriv (fun y => Y y 2) ρ| ≤ B * Y ρ 2 / r at HV
  change DifferentiableAt ℝ (fun y => Y y 3) ρ ∧ |deriv (fun y => Y y 3) ρ| ≤ B * Y ρ 3 / r at HW
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hu : 0 < Y ρ 1 := div_pos (mul_pos hsqrt hnpos) hA
  have hvpos : 0 < Y ρ 2 := div_pos (mul_pos hsqrt ha0) hA
  have hw : 0 ≤ Y ρ 3 := div_nonneg (mul_nonneg hsqrt.le hb.1) hA.le
  have HP := product_radial_derivative_bound HV.1 HW.1 hvpos.le hw HV.2 HW.2
  change DifferentiableAt ℝ p ρ ∧ |deriv p ρ| ≤ (B + B) * p ρ / r at HP
  have hprod : 0 ≤ p ρ := mul_nonneg hvpos.le hw
  have HlogU := log_radial_derivative_bound HU.1 hu HU.2
  have HYD := differentiableAt_restartFastProjectiveEntry Hcurve HAD (ne_of_gt hA)
  have Hangle := restartFastCoreAngle_derivative_bound Hcurve HAD hr.1 hM.le hD.le hsmall hp hv ha hA HAhi HAd
  have Hwalls : ∀ i : Fin 3, 0 ≤ Y ρ i.succ ∧
      |deriv (fun y => Y y i.succ) ρ| ≤ K * Y ρ i.succ / r := by
    intro i
    fin_cases i
    · exact ⟨hu.le, HU.2.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBK hu.le) hr.1.le)⟩
    · exact ⟨hvpos.le, HV.2.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBK hvpos.le) hr.1.le)⟩
    · exact ⟨hw, HW.2.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBK hw) hr.1.le)⟩
  refine ⟨hdom, HYD, Hangle.1, Hangle.2.trans (div_le_div_of_nonneg_right hAK hr.1.le),
    Hwalls, HP.1, hprod, HP.2.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right h2BK hprod) hr.1.le), hu, HlogU.1,
    HlogU.2.trans (div_le_div_of_nonneg_right hBK hr.1.le), ?_, ?_⟩
  · intro hζpos
    have hinit : positiveWalls (restartSectionChart h Z) := ⟨hh.1, hr.1.trans_le hρ.1, hζpos⟩
    have Hpos := (normalizedMaxCurve_forward hinit (restartSectionChart_constraint hrad.le) hT).2.1
    have hwpos : 0 < Y ρ 3 := div_pos (mul_pos hsqrt Hpos.2.2) hA
    have hppos : 0 < p ρ := mul_pos hvpos hwpos
    have HlogP := log_radial_derivative_bound HP.1 hppos HP.2
    refine ⟨hppos, HlogP.1, ?_⟩
    calc
      _ ≤ B / r + (B + B) / r := add_le_add HlogU.2 HlogP.2
      _ = 3 * B / r := by ring
      _ ≤ K / r := div_le_div_of_nonneg_right h3BK hr.1.le
  · intro hζzero
    have Hb0 : (P ρ).2 2 = 0 := by rw [hζzero] at hb; linarith only [hb.1, hb.2]
    have Hw0 : Y ρ 3 = 0 := by
      change Real.sqrt 3 * (P ρ).2 2 / A ρ = 0
      rw [Hb0]
      simp
    have Hp0 : p ρ = 0 := by change Y ρ 2 * Y ρ 3 = 0; rw [Hw0, mul_zero]
    refine ⟨Hw0, ?_, Hp0, ?_⟩
    · exact abs_nonpos_iff.mp (by simpa only [Hw0, mul_zero, zero_div] using HW.2)
    · exact abs_nonpos_iff.mp (by simpa only [Hp0, mul_zero, zero_div] using HP.2)

end BianchiIX
