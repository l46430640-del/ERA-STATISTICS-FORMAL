import BianchiIX.Dynamics.ShearRestartProjectiveEntry
import BianchiIX.Analysis.RadialAmplitudeDerivatives

noncomputable section

namespace BianchiIX

open Set

/-- The exact shear-family projection retains each wall in its radial derivative, including zero walls. -/
theorem exists_restartFastShearProjectiveEntry_response :
    ∃ hstar > (0 : ℝ), ∃ K > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q : ℝ, 2 < q →
      ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε σ n₂ n₃ : ℝ,
        (0 ≤ ε ∧ ε ≤ 1 / 64) → |σ| = 1 →
        (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
          let T := q / 2 * Real.log (1 / a)
          let Y := restartFastShearProjectiveEntry h T σ n₂ n₃
          let p := fun t => Y t 2 * Y t 3
          T ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) 0 ∧
          DifferentiableAt ℝ Y ρ ∧ |deriv (fun t => Y t 0) ρ| ≤ K / a ^ 2 ∧
          (∀ i : Fin 3, 0 ≤ Y ρ i.succ ∧
            |deriv (fun t => Y t i.succ) ρ| ≤ K * Y ρ i.succ / a ∧
            (0 < Y ρ i.succ → DifferentiableAt ℝ (fun t => Real.log (Y t i.succ)) ρ ∧
              |deriv (fun t => Real.log (Y t i.succ)) ρ| ≤ K / a)) ∧
          DifferentiableAt ℝ p ρ ∧ 0 ≤ p ρ ∧ |deriv p ρ| ≤ K * p ρ / a ∧
          (0 < n₂ → 0 < n₃ → 0 < p ρ ∧
            |deriv (fun t => Real.log (Y t 1)) ρ| + |deriv (fun t => Real.log (Y t 2)) ρ| +
              |deriv (fun t => Real.log (Y t 3)) ρ| ≤ K / a) ∧
          (n₂ = 0 → Y ρ 2 = 0 ∧ deriv (fun t => Y t 2) ρ = 0) ∧
          (n₃ = 0 → Y ρ 3 = 0 ∧ deriv (fun t => Y t 3) ρ = 0) ∧
          (n₂ = 0 ∨ n₃ = 0 → p ρ = 0 ∧ deriv p ρ = 0) := by
  obtain ⟨C, hC, hE, hhE, HE⟩ := exists_restartShearFastEntry_control
  obtain ⟨hP, hhP, HP⟩ := exists_restartFastShearProjectiveEntry_bounds
  let B := 8 * C + 2048
  let K := 4 * B + 40000
  have hB : 0 < B := by dsimp only [B]; linarith only [hC]
  have hK : 0 < K := by dsimp only [K]; positivity
  have hBK : B ≤ K := by dsimp only [K]; linarith only [hB]
  have h2BK : B + B ≤ K := by dsimp only [K]; linarith only [hB]
  have h3BK : 3 * B ≤ K := by dsimp only [K]; linarith only [hB]
  have hMK : (4 + 2048) * 18 ≤ K := by dsimp only [K]; linarith only [hB]
  refine ⟨min hE hP, lt_min hhE hhP, K, hK, ?_⟩
  intro h hh q hq
  obtain ⟨aE, haE, HRE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q hq
  obtain ⟨aP, haP, HRP⟩ := HP h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q hq
  refine ⟨min aE aP, lt_min haE haP, ?_⟩
  intro a ha ε σ n₂ n₃ hε hσ h₂ h₃ ρ hρ T Y p
  let Z := restartShearCurve σ n₂ n₃ ρ
  let P := fun t => restartSectionRadialState h T (restartShearCurve σ n₂ n₃ t)
  let v := fderiv ℝ (restartSectionRadialState h T) Z (restartShearDirection σ)
  let A := restartFastShearHeight h T σ n₂ n₃
  obtain ⟨_, _, _, _, _, _, _, Hcurve, hnpos, _, hs, _, hv, hnrel, hw⟩ :=
    HRE a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε σ n₂ n₃ hε hσ h₂ h₃ ρ hρ
  obtain ⟨hdom, HYD, HAD, HAlo, _, HAd, HMval, HUval, HVval, HWval, _, _⟩ :=
    HRP a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε σ n₂ n₃ hε hσ h₂ h₃ ρ hρ
  change HasDerivAt P v ρ at Hcurve
  change ‖v‖ ≤ 2 at hv
  change 0 < (P ρ).1 at hnpos
  change |v.1| ≤ 2 * (P ρ).1 / a at hnrel
  change 3 * a / 4 ≤ σ * (P ρ).2 0 ∧ σ * (P ρ).2 0 ≤ 9 * a / 4 at hs
  change DifferentiableAt ℝ A ρ at HAD
  change a ^ 2 / 4 ≤ A ρ at HAlo
  change |deriv A ρ| ≤ 512 * a at HAd
  change DifferentiableAt ℝ Y ρ at HYD
  change 1 / (8 * a) ≤ σ * Y ρ 0 ∧ σ * Y ρ 0 ≤ 18 / a at HMval
  have hA : 0 < A ρ := (by positivity [ha.1] : 0 < a ^ 2 / 4).trans_le HAlo
  have HArel : |deriv A ρ| ≤ 2048 * A ρ / a := by
    apply (le_div_iff₀ ha.1).mpr
    nlinarith only [mul_le_mul_of_nonneg_right HAd ha.1.le, HAlo]
  have Hn : HasDerivAt (fun t => (P t).1) v.1 ρ :=
    (ContinuousLinearMap.fst ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt ρ Hcurve
  have Hc (i : Fin 3) : HasDerivAt (fun t => (P t).2 i) (v.2 i) ρ := by
    let Q : RestartCenterState →L[ℝ] ℝ := ContinuousLinearMap.proj i
    exact Q.hasFDerivAt.comp_hasDerivAt ρ
      ((ContinuousLinearMap.snd ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt ρ Hcurve)
  have Hvc (i : Fin 3) : |v.2 i| ≤ 2 := (norm_le_pi_norm v.2 i).trans ((norm_snd_le v).trans hv)
  have Hnrel : |v.1| ≤ (8 * C) * (P ρ).1 / a := hnrel.trans (by
    apply div_le_div_of_nonneg_right _ ha.1.le
    exact mul_le_mul_of_nonneg_right (by linarith only [hC]) hnpos.le)
  have Hweak (i : Fin 2) : 0 ≤ (P ρ).2 i.succ ∧ |v.2 i.succ| ≤ (8 * C) * (P ρ).2 i.succ / a := by
    have hZi : 0 ≤ Z i.succ := by fin_cases i; exact h₂.1; exact h₃.1
    exact ⟨(div_nonneg hZi (by norm_num)).trans (hw i).1, (hw i).2.2⟩
  have HU := scaled_quotient_radial_derivative_bound Hn HAD.hasDerivAt ha.1
    (Real.sqrt_nonneg (3 : ℝ)) hnpos.le hA Hnrel HArel
  have HV := scaled_quotient_radial_derivative_bound (Hc 1) HAD.hasDerivAt ha.1
    (Real.sqrt_nonneg (3 : ℝ)) (Hweak 0).1 hA (Hweak 0).2 HArel
  have HW := scaled_quotient_radial_derivative_bound (Hc 2) HAD.hasDerivAt ha.1
    (Real.sqrt_nonneg (3 : ℝ)) (Hweak 1).1 hA (Hweak 1).2 HArel
  change DifferentiableAt ℝ (fun t => Y t 1) ρ ∧ |deriv (fun t => Y t 1) ρ| ≤ B * Y ρ 1 / a at HU
  change DifferentiableAt ℝ (fun t => Y t 2) ρ ∧ |deriv (fun t => Y t 2) ρ| ≤ B * Y ρ 2 / a at HV
  change DifferentiableAt ℝ (fun t => Y t 3) ρ ∧ |deriv (fun t => Y t 3) ρ| ≤ B * Y ρ 3 / a at HW
  have hu : 0 < Y ρ 1 := HUval.1
  have hvpos : 0 ≤ Y ρ 2 := (div_nonneg h₂.1 (by positivity)).trans HVval.1
  have hwpos : 0 ≤ Y ρ 3 := (div_nonneg h₃.1 (by positivity)).trans HWval.1
  have HMder : |deriv (fun t => Y t 0) ρ| ≤ K / a ^ 2 := by
    have hspos : 0 ≤ σ * (P ρ).2 0 := (by positivity [ha.1] : 0 ≤ 3 * a / 4).trans hs.1
    have Hsrel : |σ * v.2 0| ≤ 4 * (σ * (P ρ).2 0) / a := by
      rw [abs_mul, hσ, one_mul]
      apply (Hvc 0).trans
      apply (le_div_iff₀ ha.1).mpr
      linarith only [hs.1, ha.1]
    have HM := scaled_quotient_radial_derivative_bound ((Hc 0).const_mul σ) HAD.hasDerivAt ha.1
      (Real.sqrt_nonneg (3 : ℝ)) hspos hA Hsrel HArel
    have heq : (fun t => Real.sqrt 3 * (σ * (P t).2 0) / A t) = fun t => σ * Y t 0 := by
      funext t
      change Real.sqrt 3 * (σ * (P t).2 0) / A t = σ * (Real.sqrt 3 * (P t).2 0 / A t)
      ring
    rw [heq] at HM
    rw [((differentiableAt_pi.mp HYD 0).hasDerivAt.const_mul σ).deriv, abs_mul, hσ, one_mul] at HM
    rw [congr_fun heq ρ] at HM
    calc
      _ ≤ (4 + 2048) * (σ * Y ρ 0) / a := HM.2
      _ ≤ (4 + 2048) * (18 / a) / a := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left HMval.2 (by norm_num)) ha.1.le
      _ = ((4 + 2048) * 18) / a ^ 2 := by ring
      _ ≤ K / a ^ 2 := div_le_div_of_nonneg_right hMK (sq_nonneg a)
  have Hwalls (i : Fin 3) : 0 ≤ Y ρ i.succ ∧
      |deriv (fun t => Y t i.succ) ρ| ≤ B * Y ρ i.succ / a := by
    fin_cases i
    · exact ⟨hu.le, HU.2⟩
    · exact ⟨hvpos, HV.2⟩
    · exact ⟨hwpos, HW.2⟩
  have Hprod := product_radial_derivative_bound HV.1 HW.1 hvpos hwpos HV.2 HW.2
  change DifferentiableAt ℝ p ρ ∧ |deriv p ρ| ≤ (B + B) * p ρ / a at Hprod
  have hprod : 0 ≤ p ρ := mul_nonneg hvpos hwpos
  have Hzero (i : Fin 3) (hz : Y ρ i.succ = 0) : deriv (fun t => Y t i.succ) ρ = 0 :=
    abs_nonpos_iff.mp (by simpa only [hz, mul_zero, zero_div] using (Hwalls i).2)
  have Hvzero (hz : n₂ = 0) : Y ρ 2 = 0 := by
    have H : Y ρ 2 ≤ 16 * n₂ / a ^ 2 := HVval.2
    rw [hz, mul_zero, zero_div] at H
    exact le_antisymm H hvpos
  have Hwzero (hz : n₃ = 0) : Y ρ 3 = 0 := by
    have H : Y ρ 3 ≤ 16 * n₃ / a ^ 2 := HWval.2
    rw [hz, mul_zero, zero_div] at H
    exact le_antisymm H hwpos
  refine ⟨hdom, HYD, HMder, ?_, Hprod.1, hprod,
    Hprod.2.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2BK hprod) ha.1.le),
    ?_, fun hz => ⟨Hvzero hz, Hzero 1 (Hvzero hz)⟩,
    fun hz => ⟨Hwzero hz, Hzero 2 (Hwzero hz)⟩, ?_⟩
  · intro i
    refine ⟨(Hwalls i).1, (Hwalls i).2.trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBK (Hwalls i).1) ha.1.le), ?_⟩
    intro hpos
    have Hlog := log_radial_derivative_bound (differentiableAt_pi.mp HYD i.succ) hpos (Hwalls i).2
    exact ⟨Hlog.1, Hlog.2.trans (div_le_div_of_nonneg_right hBK ha.1.le)⟩
  · intro h₂pos h₃pos
    have hV : 0 < Y ρ 2 := (by positivity [ha.1] : 0 < n₂ / (12 * a ^ 2)).trans_le HVval.1
    have hW : 0 < Y ρ 3 := (by positivity [ha.1] : 0 < n₃ / (12 * a ^ 2)).trans_le HWval.1
    refine ⟨mul_pos hV hW, ?_⟩
    have HUlog := log_radial_derivative_bound HU.1 hu HU.2
    have HVlog := log_radial_derivative_bound HV.1 hV HV.2
    have HWlog := log_radial_derivative_bound HW.1 hW HW.2
    exact (add_le_add (add_le_add HUlog.2 HVlog.2) HWlog.2).trans (by
      have H := div_le_div_of_nonneg_right h3BK ha.1.le
      convert! H using 1
      ring)
  · intro hz
    have hpzero : p ρ = 0 := by
      rcases hz with hz | hz
      · change Y ρ 2 * Y ρ 3 = 0
        rw [Hvzero hz, zero_mul]
      · change Y ρ 2 * Y ρ 3 = 0
        rw [Hwzero hz, mul_zero]
    exact ⟨hpzero, abs_nonpos_iff.mp (by simpa only [hpzero, mul_zero, zero_div] using Hprod.2)⟩

end BianchiIX
