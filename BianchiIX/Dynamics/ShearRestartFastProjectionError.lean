import BianchiIX.Dynamics.ShearRestartScaledError
import BianchiIX.Dynamics.ShearRestartProjectiveEntry

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def restartFastShearProjectionPhase (h T σ n₂ n₃ ρ : ℝ) : ℝ :=
  2 / coreRadius (restartFastShearProjectiveEntry h T σ n₂ n₃ ρ 0)
    (restartFastShearProjectiveEntry h T σ n₂ n₃ ρ 2)

/-- At the exact cutoff, a small decaying wall gives the quadratic phase error and its ordinary derivative. -/
theorem exists_restartShearFastProjectionError_bounds :
    ∃ hstar > (0 : ℝ), ∃ K > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 2 < q → 2 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε σ n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) → |σ| = 1 →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → n₃ ≤ a ^ P →
          ∀ ρ ∈ Icc a (2 * a),
            let T := q / 2 * Real.log (1 / a)
            let E := fun t => restartProjectionError (restartSectionRadialState h T (restartShearCurve σ n₂ n₃ t))
            T ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) 0 ∧
            DifferentiableAt ℝ E ρ ∧ |E ρ| ≤ K * a ^ 2 ∧ |deriv E ρ| ≤ K * a ∧
            0 < restartFastShearHeight h T σ n₂ n₃ ρ ∧
            restartFastShearProjectionPhase h T σ n₂ n₃ =ᶠ[𝓝 ρ]
              (fun t => restartProjectionPhase (restartSectionRadialState h T (restartShearCurve σ n₂ n₃ t))) := by
  obtain ⟨C, hC, hE, hhE, HE⟩ := exists_restartShearFastEntry_control
  obtain ⟨hP, hhP, HP⟩ := exists_restartFastShearProjectiveEntry_bounds
  obtain ⟨δ, hδ, B, hB, HB⟩ := exists_shearRestartProjectionScaledError_bounds (c := 3 / 4) (M := 8) (by norm_num)
  let K := B * (16 * C + 6)
  have hCpos : 0 < C := by linarith only [hC]
  have hBpos : 0 < B := by linarith only [hB]
  have hK : 0 < K := by dsimp only [K]; positivity
  have h2BK : 2 * B ≤ K := by dsimp only [K]; nlinarith only [hBpos, mul_pos hBpos hCpos]
  have hDK : B * (16 * C + 4) ≤ K := by dsimp only [K]; nlinarith only [hBpos]
  refine ⟨min hE (min hP 1), lt_min hhE (lt_min hhP (by norm_num)), K, hK, ?_⟩
  intro h hh q P hq hP
  obtain ⟨aE, haE, HRE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q hq
  obtain ⟨aP, haP, HRP⟩ := HP h ⟨hh.1, hh.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ q hq
  refine ⟨min aE (min aP (δ / 2)), lt_min haE (lt_min haP (by positivity)), ?_⟩
  intro a ha ε σ n₂ n₃ hε hσ h₂ h₃ h₃P ρ hρ T E
  have hapos := ha.1
  let Z := restartShearCurve σ n₂ n₃ ρ
  let R := fun t => restartSectionRadialState h T (restartShearCurve σ n₂ n₃ t)
  let v := fderiv ℝ (restartSectionRadialState h T) Z (restartShearDirection σ)
  obtain ⟨ha1, _, hT, hrad, hdom, _, hneg, Hcurve, hnpos, hnexp, hs, hp, hv, hnv, hw⟩ :=
    HRE a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε σ n₂ n₃ hε hσ h₂ h₃ ρ hρ
  change HasDerivAt R v ρ at Hcurve
  change 0 < (R ρ).1 at hnpos
  change (R ρ).1 ≤ h * a ^ q at hnexp
  change 3 * a / 4 ≤ σ * (R ρ).2 0 ∧ σ * (R ρ).2 0 ≤ 9 * a / 4 at hs
  change ‖(R ρ).2‖ ≤ 8 * a at hp
  change ‖v‖ ≤ 2 at hv
  change |v.1| ≤ 2 * (R ρ).1 / a at hnv
  have hpower (t : ℝ) (ht : 2 < t) : a ^ t ≤ a ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge ha.1 ha1 ht.le
  have hn : (R ρ).1 ≤ a ^ 2 := hnexp.trans
    ((mul_le_mul_of_nonneg_left (hpower q hq) hh.1.le).trans
      (mul_le_of_le_one_left (sq_nonneg a) (hh.2.trans ((min_le_right _ _).trans (min_le_right _ _)))))
  have hwpos : 0 ≤ (R ρ).2 2 := (div_nonneg h₃.1 (by norm_num)).trans (hw 1).1
  have hwall : (R ρ).2 2 ≤ 2 * a ^ 2 := (hw 1).2.1.trans
    (mul_le_mul_of_nonneg_left (h₃P.trans (hpower P hP)) (by norm_num))
  have hvwall : |v.2 2| ≤ 8 * C * (R ρ).2 2 / a := (hw 1).2.2
  let u := (restartProjectionParametersAt a (R ρ)).1
  let X := (restartProjectionParametersAt a (R ρ)).2
  let du := (restartProjectionParameterTangent a v).1
  let dX := (restartProjectionParameterTangent a v).2
  have hu : ‖u‖ ≤ 2 * a := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * a)).mpr
    intro i
    fin_cases i
    · change |a| ≤ 2 * a
      rw [abs_of_pos ha.1]
      linarith only [ha.1]
    · change |(R ρ).1 / a| ≤ 2 * a
      rw [abs_div, abs_of_pos hnpos, abs_of_pos ha.1]
      apply (div_le_iff₀ ha.1).mpr
      nlinarith only [hn, sq_nonneg a]
    · change |(R ρ).2 2 / a| ≤ 2 * a
      rw [abs_div, abs_of_nonneg hwpos, abs_of_pos ha.1]
      exact (div_le_iff₀ ha.1).mpr (by nlinarith only [hwall])
  have hXlo : 3 / 4 ≤ |X 0| := by
    change 3 / 4 ≤ |(R ρ).2 0 / a|
    rw [abs_div, abs_of_pos ha.1]
    apply (le_div_iff₀ ha.1).mpr
    have H : σ * (R ρ).2 0 ≤ |(R ρ).2 0| := by
      simpa only [abs_mul, hσ, one_mul] using le_abs_self (σ * (R ρ).2 0)
    linarith only [hs.1, H]
  have hXhi (i : Fin 2) : |X i| ≤ 8 := by
    have H (j : Fin 3) := (norm_le_pi_norm (R ρ).2 j).trans hp
    fin_cases i
    · change |(R ρ).2 0 / a| ≤ 8
      rw [abs_div, abs_of_pos ha.1]
      exact (div_le_iff₀ ha.1).mpr (H 0)
    · change |(R ρ).2 1 / a| ≤ 8
      rw [abs_div, abs_of_pos ha.1]
      exact (div_le_iff₀ ha.1).mpr (H 1)
  have Huδ : ‖u‖ ≤ δ := hu.trans (by
    linarith only [ha.2.trans ((min_le_right _ _).trans (min_le_right _ _))])
  have H := HB X hXlo (hXhi 0) (hXhi 1) u Huδ
  have hdu : ‖du‖ ≤ 16 * C := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 16 * C)).mpr
    intro i
    fin_cases i
    · change |(0 : ℝ)| ≤ 16 * C
      rw [abs_zero]
      positivity
    · change |v.1 / a| ≤ 16 * C
      rw [abs_div, abs_of_pos ha.1]
      apply (div_le_iff₀ ha.1).mpr
      have Hn : |v.1| ≤ 2 * a := hnv.trans (by
        apply (div_le_iff₀ ha.1).mpr
        nlinarith only [hn])
      nlinarith only [Hn, mul_le_mul_of_nonneg_right hC ha.1.le, ha.1]
    · change |v.2 2 / a| ≤ 16 * C
      rw [abs_div, abs_of_pos ha.1]
      apply (div_le_iff₀ ha.1).mpr
      apply hvwall.trans
      apply (div_le_iff₀ ha.1).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hwall (by positivity : 0 ≤ 8 * C)]
  have hdX : ‖dX‖ ≤ 2 / a := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 / a)).mpr
    intro i
    have Hvc (j : Fin 3) := (norm_le_pi_norm v.2 j).trans ((norm_snd_le v).trans hv)
    fin_cases i
    · change |v.2 0 / a| ≤ 2 / a
      rw [abs_div, abs_of_pos ha.1]
      exact div_le_div_of_nonneg_right (Hvc 0) ha.1.le
    · change |v.2 1 / a| ≤ 2 / a
      rw [abs_div, abs_of_pos ha.1]
      exact div_le_div_of_nonneg_right (Hvc 1) ha.1.le
  have HD := hasDerivAt_restartProjectionError ha.1 Hcurve (H.1.differentiableAt (by norm_num))
  have HBdir := restartProjectionScaledError_direction_bound (du := du) (dX := dX) H.2.2.1 H.2.2.2
  have HAlo := (HRP a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
    ε σ n₂ n₃ hε hσ h₂ h₃ ρ hρ).2.2.2.1
  have hheight : 0 < restartFastShearHeight h T σ n₂ n₃ ρ :=
    (by positivity : 0 < a ^ 2 / 4).trans_le HAlo
  have Hgerm := (eventually_restartSectionProjectionPhase_eq_core hrad hT
    (by linarith only [hneg]) hheight).comp_tendsto (hasDerivAt_restartShearCurve σ n₂ n₃ ρ).continuousAt
  refine ⟨hdom, HD.differentiableAt, ?_, ?_, hheight, Hgerm.symm⟩
  · change |restartProjectionError (R ρ)| ≤ K * a ^ 2
    rw [restartProjectionError_rescaled ha.1, abs_mul, abs_of_pos ha.1]
    calc
      _ ≤ a * (B * ‖u‖) := mul_le_mul_of_nonneg_left H.2.1 ha.1.le
      _ ≤ a * (B * (2 * a)) := by gcongr
      _ = (2 * B) * a ^ 2 := by ring
      _ ≤ K * a ^ 2 := mul_le_mul_of_nonneg_right h2BK (sq_nonneg a)
  · change |deriv (fun t => restartProjectionError (R t)) ρ| ≤ K * a
    rw [HD.deriv, abs_mul, abs_of_pos ha.1]
    calc
      _ ≤ a * (B * ‖du‖ + B * ‖u‖ * ‖dX‖) := mul_le_mul_of_nonneg_left HBdir ha.1.le
      _ ≤ a * (B * (16 * C) + B * (2 * a) * (2 / a)) := by gcongr
      _ = (B * (16 * C + 4)) * a := by field_simp; ring
      _ ≤ K * a := mul_le_mul_of_nonneg_right hDK ha.1.le

end BianchiIX
