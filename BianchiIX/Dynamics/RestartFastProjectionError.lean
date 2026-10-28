import BianchiIX.Dynamics.RestartRadialCurveControl
import BianchiIX.Dynamics.RestartProjectionErrorBounds
import BianchiIX.Dynamics.RestartProjectionDomain

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def restartFastProjectionPhase (h T θ ζ ρ : ℝ) : ℝ :=
  let x := normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 T
  2 / coreRadius (toProjectiveState x 0) (toProjectiveState x 2)

def restartFastProjectionError (h T θ ζ ρ : ℝ) : ℝ :=
  restartProjectionError (restartSectionRadialState h T (restartRadialCurve θ ζ ρ))

/-- The geometric comparison (E.15) is instantiated on the exact flow with one cutoff for the whole curve. -/
theorem exists_restartFastProjectionError_bounds :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∃ K : ℝ, 0 < K ∧ ∀ q : ℝ, 2 < q →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ 2) → ∀ ρ ∈ Icc r (2 * r),
            let T := q / 2 * Real.log (1 / r)
            let x := normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 T
            T ∈ normalizedMaxDomain (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0 ∧
            DifferentiableAt ℝ (restartFastProjectionError h T θ ζ) ρ ∧
            |restartFastProjectionError h T θ ζ ρ| ≤ K * r ^ 2 ∧
            |deriv (restartFastProjectionError h T θ ζ) ρ| ≤ K * r ∧
            0 < 1 + x 0 ∧
            (restartFastProjectionPhase h T θ ζ =ᶠ[𝓝 ρ]
              fun y => restartProjectionPhase (restartSectionRadialState h T (restartRadialCurve θ ζ y))) := by
  obtain ⟨C, hC, HC⟩ := exists_restartRadialCurve_control
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hC
  refine ⟨1 / (4 * C), by positivity, ?_⟩
  intro h hh L hL
  have hhpos := hh.1
  have hCh : C * h ≤ 1 / 4 := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp hh.2
    nlinarith only [H]
  have hhsmall : h ≤ 1 / 16 := by nlinarith only [hCh, mul_le_mul_of_nonneg_right hC hhpos.le]
  let M := 8 * (L + 1)
  let D := 8 * C * (L + 1)
  have hM : 0 < M := by dsimp only [M]; positivity
  have hD : 1 ≤ D := by
    dsimp only [D]
    nlinarith only [hC, mul_nonneg hCpos.le hL]
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hdir : 2 * (L + 1) ≤ D := by
    dsimp only [D]
    nlinarith only [hL, mul_le_mul_of_nonneg_right hC (show 0 ≤ L + 1 by positivity)]
  obtain ⟨δ, hδ, A, hA, HA⟩ := exists_restartProjectionError_bounds (M := M) (by norm_num : (0 : ℝ) < 1 / 2)
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  let K := 8 * A * D
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro q hq
  have Hevent : ∀ᶠ r : ℝ in 𝓝[>] 0,
      ((0 < r ∧ r ≤ 1) ∧ M * r ≤ 1 / 16 ∧ C * (M * r) * (q / 2 * Real.log (1 / r)) ≤ 1 / 8) ∧
      r * (q / 2 * Real.log (1 / r)) ≤ 1 := by
    filter_upwards [eventually_restart_cutoff_budget C (4 * (L + 1)) q,
      eventually_restart_cutoff_budget 1 1 q] with r H₁ H₂
    have heq : 2 * (4 * (L + 1)) * r = M * r := by dsimp only [M]; ring
    rw [heq] at H₁
    exact ⟨H₁, by nlinarith only [H₂.2.2]⟩
  obtain ⟨r₀, hr₀, Hr₀⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp Hevent
  refine ⟨min r₀ (min (1 / 64) (δ / 2)), lt_min hr₀ (lt_min (by norm_num) (by positivity)), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have Hr := Hr₀ ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
  have hrsmall : r ≤ 1 / 64 := (hr.2.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hrδ : r ≤ δ / 2 := (hr.2.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hζsmall : 0 ≤ ζ ∧ ζ ≤ r / 9 := ⟨hζ.1, hζ.2.trans (by nlinarith only [hrsmall, hr.1])⟩
  let T := q / 2 * Real.log (1 / r)
  let Z := restartRadialCurve θ ζ ρ
  let p := restartSectionRadialState h T Z
  let v := fderiv ℝ (restartSectionRadialState h T) Z (restartRadialDirection θ)
  have hT : 0 ≤ T := mul_nonneg (by linarith only [hq] : 0 ≤ q / 2)
    (Real.log_nonneg ((le_div_iff₀ hr.1).mpr (by linarith only [Hr.1.1.2])))
  have H := HC h r T L hhpos hCh Hr.1.1 hL Hr.1.2.1 hT Hr.1.2.2 Hr.2 θ ζ ρ hθ hζsmall hρ
  obtain ⟨Hcurve, hnegative, hnpos, hnexp, hcenter, hactive, hweak, hcv, hnv, hwv⟩ := H
  change HasDerivAt (fun x => restartSectionRadialState h T (restartRadialCurve θ ζ x)) v ρ at Hcurve
  change 0 < p.1 at hnpos
  change p.1 ≤ h * Real.exp (-2 * T) at hnexp
  change ‖p.2‖ ≤ M * r at hcenter
  change r / 2 ≤ p.2 1 at hactive
  change 0 ≤ p.2 2 ∧ p.2 2 ≤ 2 * ζ at hweak
  change ∀ i : Fin 3, |v.2 i| ≤ 2 * (L + 1) at hcv
  change |v.1| ≤ 2 * (L + 1) * p.1 / r at hnv
  change |v.2 2| ≤ D * p.2 2 / r at hwv
  have he : Real.exp (-2 * T) = r ^ q := by
    rw [Real.rpow_def_of_pos hr.1]
    congr 1
    dsimp only [T]
    rw [one_div, Real.log_inv]
    ring
  have hpower : r ^ q ≤ r ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hr.1 Hr.1.1.2 hq.le
  have hnsmall : p.1 ≤ r ^ 2 := by
    rw [he] at hnexp
    exact hnexp.trans ((mul_le_mul_of_nonneg_left hpower hhpos.le).trans
      (mul_le_of_le_one_left (sq_nonneg r) (by linarith only [hhsmall])))
  have hwsmall : p.2 2 ≤ 2 * r ^ 2 := hweak.2.trans (mul_le_mul_of_nonneg_left hζ.2 (by norm_num))
  have hgeom := HA r hr.1 (by linarith only [hrδ, hδ]) p
    ((norm_le_pi_norm p.2 0).trans hcenter) (by linarith only [hactive])
    ((le_abs_self _).trans ((norm_le_pi_norm p.2 1).trans hcenter))
    (by rw [abs_of_pos hnpos]; nlinarith only [hnsmall, mul_le_mul_of_nonneg_right hrδ hr.1.le])
    (by rw [abs_of_nonneg hweak.1]; nlinarith only [hwsmall, mul_le_mul_of_nonneg_right hrδ hr.1.le])
  have Hder := hgeom.2.2 D hDpos.le v ((hcv 0).trans hdir) ((hcv 1).trans hdir)
    (by rw [abs_of_pos hnpos]; exact hnv.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hdir hnpos.le) hr.1.le))
    (by rwa [abs_of_nonneg hweak.1])
  have HD := (hgeom.1.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt ρ Hcurve
  change HasDerivAt (restartFastProjectionError h T θ ζ) (fderiv ℝ restartProjectionError p v) ρ at HD
  have hZ := (restartRadialCurve_annulus hr.1 hρ hL hθ hζsmall).1
  have hrad := restartSectionRadicand_pos_of_small (h := h) (Z := Z)
    (by rwa [abs_of_pos hhpos]) (by
      change ‖Z‖ ≤ 2 * (L + 1) * r at hZ
      have Hb : 8 * (L + 1) * r ≤ 1 / 16 := Hr.1.2.1
      linarith only [hZ, Hb])
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hrad.le) 0 hT
  let x := normalizedMaxCurve (restartSectionChart h Z) 0 T
  have hxcon : stateConstraint x = 1 := (normalizedMaxCurve_forward_of_constraint
    (restartSectionChart_constraint hrad.le) hT).2.1
  have hxactive : 0 < x 3 := by change 0 < p.2 1; linarith only [hactive, hr.1]
  have hxstrong : 0 ≤ x 2 ∧ x 2 ≤ x 3 / 16 := by
    change 0 ≤ p.1 ∧ p.1 ≤ p.2 1 / 16
    exact ⟨hnpos.le, by nlinarith only [hnsmall, hactive, mul_le_mul_of_nonneg_right hrsmall hr.1.le]⟩
  have hxweak : 0 ≤ x 4 ∧ x 4 ≤ x 3 / 16 := by
    change 0 ≤ p.2 2 ∧ p.2 2 ≤ p.2 1 / 16
    exact ⟨hweak.1, by nlinarith only [hwsmall, hactive, mul_le_mul_of_nonneg_right hrsmall hr.1.le]⟩
  have hxheight := normalized_projective_height_pos_of_active_dominance hxcon hxactive hxstrong hxweak
  have hxnegative : x 0 < 0 := by change x 0 ≤ -(15 / 16) at hnegative; linarith only [hnegative]
  have Hnear := (eventually_restartSectionProjectionPhase_eq_core hrad hT hxnegative hxheight).comp_tendsto
    (hasDerivAt_restartRadialCurve θ ζ ρ).continuousAt
  refine ⟨hdom, HD.differentiableAt, ?_, ?_, hxheight, Hnear.symm⟩
  · change |restartProjectionError p| ≤ K * r ^ 2
    have HV := hgeom.2.1
    rw [abs_of_pos hnpos, abs_of_nonneg hweak.1] at HV
    have Hsmall := mul_le_mul_of_nonneg_left (add_le_add hnsmall hwsmall) hApos.le
    have HK : 4 * A ≤ K := by dsimp only [K]; nlinarith only [hApos, mul_le_mul_of_nonneg_left hD hApos.le]
    exact (HV.trans (by nlinarith only [Hsmall])).trans (mul_le_mul_of_nonneg_right HK (sq_nonneg r))
  · rw [HD.deriv]
    rw [abs_of_pos hnpos, abs_of_nonneg hweak.1] at Hder
    have Hn : p.1 / r ≤ r := (div_le_iff₀ hr.1).mpr (by nlinarith only [hnsmall])
    have Hw : p.2 2 / r ≤ 2 * r := (div_le_iff₀ hr.1).mpr (by nlinarith only [hwsmall])
    exact Hder.trans (by
      change 2 * A * D * (r + p.1 / r + p.2 2 / r) ≤ (8 * A * D) * r
      nlinarith only [mul_le_mul_of_nonneg_left (add_le_add Hn Hw) (show 0 ≤ 2 * A * D by positivity)])

end BianchiIX
