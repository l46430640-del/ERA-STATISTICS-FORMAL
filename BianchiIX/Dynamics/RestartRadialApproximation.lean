import BianchiIX.Dynamics.RestartRadialCutoffDerivative

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Both lines of (E.11) hold on one actual domain, with a common constant chosen before q. -/
theorem exists_restartSection_radial_approximation :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ (c₀ C₀ : ℝ), 0 < c₀ → 0 < C₀ → ∃ K : ℝ, 0 < K ∧ ∀ q : ℝ, 2 < q →
        ∃ ρstar : ℝ, 0 < ρstar ∧ ∀ ρ ∈ Ioc (0 : ℝ) ρstar,
          ∀ Z : RestartCenterState, ‖Z‖ ≤ C₀ * ρ → c₀ * ρ ≤ restartRadialNorm Z →
            let T := q / 2 * Real.log (1 / ρ)
            T ∈ normalizedMaxDomain (restartSectionChart h Z) 0 ∧
            DifferentiableAt ℝ (restartSectionRadialError h T) Z ∧
            |restartSectionRadialError h T Z| ≤ K * ρ ^ 2 ∧
            ‖fderiv ℝ (restartSectionRadialError h T) Z‖ ≤ K * ρ := by
  obtain ⟨hV, hhV, HV⟩ := exists_restartSection_radial_value_approximation
  obtain ⟨C, hC, HC⟩ := exists_restartSection_radial_cutoff_derivative
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hC
  let hstar := min hV (1 / (4 * C))
  have hstarpos : 0 < hstar := lt_min hhV (by positivity)
  refine ⟨hstar, hstarpos, ?_⟩
  intro h hh c₀ C₀ hc₀ hC₀
  have hhpos := hh.1
  have hCh : C * h ≤ 1 / 4 := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp (hh.2.trans (min_le_right _ _))
    nlinarith only [H]
  obtain ⟨KV, hKV, HVscale⟩ := HV h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ C₀ hC₀
  obtain ⟨KD, hKD, HD⟩ := HC c₀ C₀ hc₀ hC₀
  let K := max KV (KD * (2 * h + 1))
  have hK : 0 < K := hKV.trans_le (le_max_left _ _)
  refine ⟨K, hK, ?_⟩
  intro q hq
  obtain ⟨ρV, hρV, HVρ⟩ := HVscale q hq
  have Hevent : ∀ᶠ ρ : ℝ in 𝓝[>] 0,
      ((0 < ρ ∧ ρ ≤ 1) ∧ 2 * C₀ * ρ ≤ 1 / 16 ∧
        C * (2 * C₀ * ρ) * (q / 2 * Real.log (1 / ρ)) ≤ 1 / 8) ∧
          ρ * (q / 2 * Real.log (1 / ρ)) ≤ 1 := by
    filter_upwards [eventually_restart_cutoff_budget C C₀ q,
      eventually_restart_cutoff_budget 1 1 q] with ρ H₁ H₂
    exact ⟨H₁, by nlinarith only [H₂.2.2]⟩
  obtain ⟨ρD, hρD, HDρ⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp Hevent
  refine ⟨min ρV ρD, lt_min hρV hρD, ?_⟩
  intro ρ hρ Z hZ hlower
  have HVZ := HVρ ρ ⟨hρ.1, hρ.2.trans (min_le_left _ _)⟩ Z hZ
  have Hb := HDρ ⟨hρ.1, hρ.2.trans (min_le_right _ _)⟩
  have HDR := HD h ρ q hhpos hCh Hb.1.1 (by linarith only [hq]) Hb.1.2.1 Hb.1.2.2 Z hZ hlower
  refine ⟨HVZ.1, HDR.1, ?_, ?_⟩
  · exact HVZ.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg ρ))
  · have Hpower : ρ ^ q ≤ ρ := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge Hb.1.1.1 Hb.1.1.2
        (by linarith only [hq] : (1 : ℝ) ≤ q)
    have Htime : ρ ^ 2 * (q / 2 * Real.log (1 / ρ)) ≤ ρ := by
      nlinarith only [mul_le_mul_of_nonneg_right Hb.2 hρ.1.le]
    apply HDR.2.trans
    calc
      _ ≤ KD * ((2 * h + 1) * ρ) := mul_le_mul_of_nonneg_left (by
        nlinarith only [Htime, mul_le_mul_of_nonneg_left Hpower hhpos.le]) hKD.le
      _ = (KD * (2 * h + 1)) * ρ := by ring
      _ ≤ K * ρ := mul_le_mul_of_nonneg_right (le_max_right _ _) hρ.1.le

end BianchiIX
