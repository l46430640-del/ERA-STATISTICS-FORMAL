import BianchiIX.Dynamics.RestartCutoffRemainder
import BianchiIX.Analysis.RestartCutoffScale

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The full displayed statement (E.1), with a genuine scale threshold after height and exponent are fixed. -/
theorem exists_restartSection_linear_approximation :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ C₀ : ℝ, 0 < C₀ → ∀ q : ℝ, 2 < q →
        ∃ K : ℝ, 0 < K ∧ ∃ ρstar : ℝ, 0 < ρstar ∧
          ∀ ρ ∈ Ioc (0 : ℝ) ρstar, ∀ Z : RestartCenterState, ‖Z‖ ≤ C₀ * ρ →
            let T := q / 2 * Real.log (1 / ρ)
            let x := normalizedMaxCurve (restartSectionChart h Z) 0 T
            T ∈ normalizedMaxDomain (restartSectionChart h Z) 0 ∧
            0 < x 2 ∧ x 2 ≤ h * ρ ^ q ∧
            restartSectionCenterFlow h T Z = restartCenterTransfer h Z + restartSectionRemainder h T Z ∧
            DifferentiableAt ℝ (restartSectionRemainder h T) Z ∧
            ‖restartSectionRemainder h T Z‖ ≤ K * ρ ^ 2 * (1 + |Real.log ρ|) ∧
            ‖fderiv ℝ (restartSectionRemainder h T) Z‖ ≤ K * ρ * (1 + |Real.log ρ|) := by
  obtain ⟨C, hC, HC⟩ := exists_restartSection_cutoff_remainder
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hC
  let hstar := 1 / (4 * C)
  have hstarpos : 0 < hstar := by dsimp only [hstar]; positivity
  refine ⟨hstar, hstarpos, ?_⟩
  intro h hh C₀ hC₀ q hq
  have hhpos : 0 < h := hh.1
  have hq0 : 0 < q := by linarith only [hq]
  have hCh : C * h ≤ 1 / 4 := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp hh.2
    nlinarith only [H]
  let KV := 2 * C * C₀ ^ 2 * q + 6 * h * C₀
  let KD := 4 * C * C₀ * q + 6 * h
  let K := max KV KD
  have hKD : 0 < KD := by dsimp only [KD]; positivity
  have hK : 0 < K := hKD.trans_le (le_max_right _ _)
  obtain ⟨ρstar, hρstar, Hbudget⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp
    (eventually_restart_cutoff_budget C C₀ q)
  refine ⟨K, hK, ρstar, hρstar, ?_⟩
  intro ρ hρ Z hZ
  have Hb := Hbudget hρ
  have HR := HC h C₀ ρ q hhpos hCh hC₀ Hb.1 hq0.le Hb.2.1 Hb.2.2 Z hZ
  have HS := restart_cutoff_scale_bounds hCpos.le hC₀.le hhpos.le Hb.1
    (by linarith only [hq] : (1 : ℝ) ≤ q)
  obtain ⟨Hdom, Hpos, Hwall, Hdecomp, Hdiff, Hvalue, Hderiv⟩ := HR
  refine ⟨Hdom, Hpos, Hwall, Hdecomp, Hdiff, ?_, ?_⟩
  · apply Hvalue.trans (HS.1.trans ?_)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left KV KD) (sq_nonneg ρ)) (by positivity)
  · apply Hderiv.trans (HS.2.trans ?_)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right KV KD) hρ.1.le) (by positivity)

end BianchiIX
