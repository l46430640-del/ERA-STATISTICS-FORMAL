import BianchiIX.Dynamics.RestartRadialCurveControl
import BianchiIX.Dynamics.RestartRadialApproximation

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Exact fast-layer data for the projective entry, with a cutoff uniform on every radial curve. -/
theorem exists_restartFastEntry_control :
    ∃ C ≥ (32 : ℝ), ∀ h ∈ Ioc (0 : ℝ) (1 / (4 * C)),
      ∀ L : ℝ, 0 ≤ L → ∀ q : ℝ, 2 < q → ∃ rstar : ℝ, 0 < rstar ∧
        ∀ r ∈ Ioc (0 : ℝ) rstar, ∀ θ ζ : ℝ, |θ| ≤ L → (0 ≤ ζ ∧ ζ ≤ r ^ 2) →
          ∀ ρ ∈ Icc r (2 * r),
            let T := q / 2 * Real.log (1 / r)
            let Z := restartRadialCurve θ ζ ρ
            let x := normalizedMaxCurve (restartSectionChart h Z) 0 T
            let p := restartSectionRadialState h T Z
            let v := fderiv ℝ (restartSectionRadialState h T) Z (restartRadialDirection θ)
            r ≤ 1 ∧ 8 * (L + 1) * r ≤ 1 / 16 ∧ 0 ≤ T ∧
            0 < restartSectionRadicand h Z ∧ T ∈ normalizedMaxDomain (restartSectionChart h Z) 0 ∧
            stateConstraint x = 1 ∧ x 0 ≤ -(15 / 16) ∧
            HasDerivAt (fun y => restartSectionRadialState h T (restartRadialCurve θ ζ y)) v ρ ∧
            0 < p.1 ∧ p.1 ≤ h * r ^ q ∧ ‖p‖ ≤ 8 * (L + 1) * r ∧ r / 2 ≤ p.2 1 ∧
            (0 ≤ p.2 2 ∧ p.2 2 ≤ 2 * ζ) ∧ p.1 ≤ p.2 1 / 16 ∧ p.2 2 ≤ p.2 1 / 16 ∧
            ‖v‖ ≤ 2 * (L + 1) ∧ |v.1| ≤ 2 * (L + 1) * p.1 / r ∧
            |v.2 2| ≤ 8 * C * (L + 1) * p.2 2 / r := by
  obtain ⟨C, hC, HC⟩ := exists_restartRadialCurve_control
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hC
  refine ⟨C, hC, ?_⟩
  intro h hh L hL q hq
  have hCh : C * h ≤ 1 / 4 := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp hh.2
    linarith only [H]
  have hhsmall : h ≤ 1 / 16 := by
    nlinarith only [hCh, mul_le_mul_of_nonneg_right hC hh.1.le]
  let M := 8 * (L + 1)
  have hM : 1 ≤ M := by dsimp only [M]; linarith only [hL]
  have Hevent : ∀ᶠ r : ℝ in 𝓝[>] 0,
      ((0 < r ∧ r ≤ 1) ∧ M * r ≤ 1 / 16 ∧ C * (M * r) * (q / 2 * Real.log (1 / r)) ≤ 1 / 8) ∧
      r * (q / 2 * Real.log (1 / r)) ≤ 1 := by
    filter_upwards [eventually_restart_cutoff_budget C (4 * (L + 1)) q,
      eventually_restart_cutoff_budget 1 1 q] with r H₁ H₂
    have heq : 2 * (4 * (L + 1)) * r = M * r := by dsimp only [M]; ring
    rw [heq] at H₁
    exact ⟨H₁, by nlinarith only [H₂.2.2]⟩
  obtain ⟨r₀, hr₀, Hr₀⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp Hevent
  refine ⟨min r₀ (1 / 64), lt_min hr₀ (by norm_num), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have Hr := Hr₀ ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
  have hrsmall : r ≤ 1 / 64 := hr.2.trans (min_le_right _ _)
  have hζsmall : 0 ≤ ζ ∧ ζ ≤ r / 9 := ⟨hζ.1, hζ.2.trans (by nlinarith only [hrsmall, hr.1])⟩
  let T := q / 2 * Real.log (1 / r)
  let Z := restartRadialCurve θ ζ ρ
  let p := restartSectionRadialState h T Z
  let v := fderiv ℝ (restartSectionRadialState h T) Z (restartRadialDirection θ)
  have hT : 0 ≤ T := mul_nonneg (by linarith only [hq] : 0 ≤ q / 2)
    (Real.log_nonneg ((le_div_iff₀ hr.1).mpr (by linarith only [Hr.1.1.2])))
  obtain ⟨Hcurve, hneg, hnpos, hnexp, hcenter, hactive, hweak, hcv, hnv, hwv⟩ :=
    HC h r T L hh.1 hCh Hr.1.1 hL Hr.1.2.1 hT Hr.1.2.2 Hr.2 θ ζ ρ hθ hζsmall hρ
  change 0 < p.1 at hnpos
  change p.1 ≤ h * Real.exp (-2 * T) at hnexp
  change ‖p.2‖ ≤ M * r at hcenter
  change r / 2 ≤ p.2 1 at hactive
  change 0 ≤ p.2 2 ∧ p.2 2 ≤ 2 * ζ at hweak
  change ∀ i : Fin 3, |v.2 i| ≤ 2 * (L + 1) at hcv
  change |v.1| ≤ 2 * (L + 1) * p.1 / r at hnv
  have he : Real.exp (-2 * T) = r ^ q := by
    rw [Real.rpow_def_of_pos hr.1]
    congr 1
    dsimp only [T]
    rw [one_div, Real.log_inv]
    ring
  rw [he] at hnexp
  have hpower : r ^ q ≤ r ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hr.1 Hr.1.1.2 hq.le
  have hnsmall : p.1 ≤ r ^ 2 := hnexp.trans
    ((mul_le_mul_of_nonneg_left hpower hh.1.le).trans
      (mul_le_of_le_one_left (sq_nonneg r) (by linarith only [hhsmall])))
  have hnr : p.1 ≤ r := hnsmall.trans (by nlinarith only [hr.1, Hr.1.1.2])
  have hp : ‖p‖ ≤ M * r := by
    rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs, abs_of_pos hnpos]
    exact ⟨hnr.trans (by nlinarith only [mul_le_mul_of_nonneg_right hM hr.1.le]), hcenter⟩
  have hv : ‖v‖ ≤ 2 * (L + 1) := by
    rw [Prod.norm_def, max_le_iff, Real.norm_eq_abs]
    refine ⟨hnv.trans ?_, (pi_norm_le_iff_of_nonneg (by positivity)).mpr hcv⟩
    apply (div_le_iff₀ hr.1).mpr
    exact mul_le_mul_of_nonneg_left hnr (by positivity)
  have hZ := (restartRadialCurve_annulus hr.1 hρ hL hθ hζsmall).1
  have hrad := restartSectionRadicand_pos_of_small (h := h) (Z := Z)
    (by rwa [abs_of_pos hh.1]) (by
      change ‖Z‖ ≤ 2 * (L + 1) * r at hZ
      have Hb : 8 * (L + 1) * r ≤ 1 / 16 := Hr.1.2.1
      linarith only [hZ, Hb])
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hrad.le) 0 hT
  have hcon := (normalizedMaxCurve_forward_of_constraint (restartSectionChart_constraint hrad.le) hT).2.1
  refine ⟨Hr.1.1.2, Hr.1.2.1, hT, hrad, hdom, hcon, hneg, Hcurve, hnpos, hnexp, hp,
    hactive, hweak, ?_, ?_, hv, hnv, hwv⟩
  · nlinarith only [hnsmall, hactive, mul_le_mul_of_nonneg_right hrsmall hr.1.le]
  · have Hw := hweak.2.trans (mul_le_mul_of_nonneg_left hζ.2 (by norm_num))
    nlinarith only [Hw, hactive, mul_le_mul_of_nonneg_right hrsmall hr.1.le]

end BianchiIX
