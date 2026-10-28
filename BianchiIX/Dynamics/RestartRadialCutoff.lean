import BianchiIX.Dynamics.RestartRadiusValue
import BianchiIX.Analysis.RestartCutoffScale

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def restartRadialPhase (Z : RestartCenterState) : ℝ := restartRadialNorm Z / Real.sqrt 3

def restartReferenceRadialPhase (h : ℝ) (Z : RestartCenterState) : ℝ :=
  Real.sqrt (restartQuadratic h (Z 0) (Z 1 - Z 2)) / Real.sqrt 3

/-- The first line of (E.11), with all three accumulated errors at the actual cutoff time. -/
theorem exists_restartSection_radial_cutoff_error :
    ∃ C ≥ (32 : ℝ), ∀ (h C₀ ρ q : ℝ),
      0 < h → C * h ≤ 1 / 4 → 0 < C₀ → (0 < ρ ∧ ρ ≤ 1) → 0 ≤ q →
      2 * C₀ * ρ ≤ 1 / 16 → C * (2 * C₀ * ρ) * (q / 2 * Real.log (1 / ρ)) ≤ 1 / 8 →
      ∀ Z : RestartCenterState, ‖Z‖ ≤ C₀ * ρ →
        let T := q / 2 * Real.log (1 / ρ)
        T ∈ normalizedMaxDomain (restartSectionChart h Z) 0 ∧
        |restartRadialPhase (restartSectionCenterFlow h T Z) - restartReferenceRadialPhase h Z| ≤
          4 * C * C₀ ^ 2 * h * ρ ^ 2 + 16 * C * C₀ ^ 3 * ρ ^ 3 * T + 48 * C₀ * h * ρ ^ (q + 1) := by
  obtain ⟨C, hC, HC⟩ := exists_restartSectionRadius_value_error
  refine ⟨C, hC, ?_⟩
  intro h C₀ ρ q hh hCh hC₀ hρ hq hb hCb Z hZ
  have hρ0 : 0 < ρ := hρ.1
  let b := 2 * C₀ * ρ
  let T := q / 2 * Real.log (1 / ρ)
  have hb0 : 0 < b := by dsimp only [b]; positivity
  have hT : 0 ≤ T := mul_nonneg (div_nonneg hq (by norm_num))
    (Real.log_nonneg ((le_div_iff₀ hρ.1).mpr (by linarith only [hρ.2])))
  have hZb : ‖Z‖ ≤ b / 2 := by dsimp only [b]; linarith only [hZ]
  have HV := (HC h b T Z hh hCh ⟨hb0, hb⟩ hT hCb hZb T ⟨hT, le_rfl⟩).2
  have hhsmall : h ≤ 1 / 16 := by
    nlinarith only [hCh, mul_le_mul_of_nonneg_right hC hh.le]
  have hrad := restartSectionRadicand_pos_of_small (h := h) (Z := Z)
    (by rwa [abs_of_pos hh]) (by linarith only [hZ, hb])
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint (restartSectionChart_constraint hrad.le) 0 hT
  have he : Real.exp (-2 * T) = ρ ^ q := by
    rw [Real.rpow_def_of_pos hρ.1]
    congr 1
    dsimp only [T]
    rw [one_div, Real.log_inv]
    ring
  have hsqrt : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt1 : 1 ≤ Real.sqrt (3 : ℝ) := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hsqrt]
  have Hnorm :
      |restartRadialPhase (restartSectionCenterFlow h T Z) - restartReferenceRadialPhase h Z| ≤
        |restartRadialNorm (restartSectionCenterFlow h T Z) - restartSectionRadius h 0 Z| := by
    dsimp only [restartRadialPhase, restartReferenceRadialPhase, restartSectionRadius]
    rw [restartSectionQuadratic_initial, ← sub_div, abs_div, abs_of_pos hsqrt]
    apply (div_le_iff₀ hsqrt).mpr
    nlinarith only [mul_nonneg
      (abs_nonneg (restartRadialNorm (restartSectionCenterFlow h T Z) -
        Real.sqrt (restartQuadratic h (Z 0) (Z 1 - Z 2)))) (sub_nonneg.mpr hsqrt1)]
  refine ⟨hdom, (Hnorm.trans HV).trans_eq ?_⟩
  rw [he, Real.rpow_add hρ0, Real.rpow_one]
  dsimp only [b]
  ring

/-- The quadratic radial value error has a constant chosen before the cutoff exponent. -/
theorem exists_restartSection_radial_value_approximation :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ C₀ : ℝ, 0 < C₀ → ∃ K : ℝ, 0 < K ∧ ∀ q : ℝ, 2 < q →
        ∃ ρstar : ℝ, 0 < ρstar ∧ ∀ ρ ∈ Ioc (0 : ℝ) ρstar,
          ∀ Z : RestartCenterState, ‖Z‖ ≤ C₀ * ρ →
            let T := q / 2 * Real.log (1 / ρ)
            T ∈ normalizedMaxDomain (restartSectionChart h Z) 0 ∧
            |restartRadialPhase (restartSectionCenterFlow h T Z) - restartReferenceRadialPhase h Z| ≤
              K * ρ ^ 2 := by
  obtain ⟨C, hC, HC⟩ := exists_restartSection_radial_cutoff_error
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hC
  let hstar := 1 / (4 * C)
  have hstarpos : 0 < hstar := by dsimp only [hstar]; positivity
  refine ⟨hstar, hstarpos, ?_⟩
  intro h hh C₀ hC₀
  have hhpos : 0 < h := hh.1
  have hCh : C * h ≤ 1 / 4 := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp hh.2
    nlinarith only [H]
  let K := 4 * C * C₀ ^ 2 * h + C₀ ^ 2 + 48 * C₀ * h
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro q hq
  obtain ⟨ρstar, hρstar, Hbudget⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (eventually_restart_cutoff_budget C C₀ q)
  refine ⟨ρstar, hρstar, ?_⟩
  intro ρ hρ Z hZ
  have Hb := Hbudget hρ
  have HR := HC h C₀ ρ q hhpos hCh hC₀ Hb.1 (by linarith only [hq]) Hb.2.1 Hb.2.2 Z hZ
  refine ⟨HR.1, HR.2.trans ?_⟩
  have Htime := mul_le_mul_of_nonneg_right Hb.2.2
    (by positivity : 0 ≤ 8 * C₀ ^ 2 * ρ ^ 2)
  have Hpower : ρ ^ (q + 1) ≤ ρ ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge Hb.1.1 Hb.1.2
      (by linarith only [hq] : (2 : ℝ) ≤ q + 1)
  have Htail := mul_le_mul_of_nonneg_left Hpower (by positivity : 0 ≤ 48 * C₀ * h)
  dsimp only [K]
  nlinarith only [Htime, Htail]

end BianchiIX
