import BianchiIX.Dynamics.RestartCutoffRemainder
import BianchiIX.Dynamics.RestartSectionMultipliers
import BianchiIX.Analysis.RestartCutoffScale

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- One scale controls the whole interval between two fast cutoffs, including zero weak walls. -/
theorem exists_restartSection_fast_interval :
    ∃ C ≥ (32 : ℝ), ∀ h ∈ Ioc (0 : ℝ) (1 / (4 * C)),
      ∀ C₀ : ℝ, 0 < C₀ → ∀ q₀ q₁ : ℝ, 2 < q₀ → q₀ ≤ q₁ →
      ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        let T₀ := q₀ / 2 * Real.log (1 / a)
        let T₁ := q₁ / 2 * Real.log (1 / a)
        a ≤ 1 / 128 ∧ 0 ≤ T₀ ∧ T₀ ≤ T₁ ∧
        ∀ Z : RestartCenterState, ‖Z‖ ≤ C₀ * a →
          0 < restartSectionRadicand h Z ∧ ∀ t ∈ Icc T₀ T₁,
            let x := normalizedMaxCurve (restartSectionChart h Z) 0 t
            t ∈ normalizedMaxDomain (restartSectionChart h Z) 0 ∧
            stateConstraint x = 1 ∧ x 0 ≤ -(15 / 16) ∧
            (0 < x 2 ∧ x 2 ≤ h * a ^ q₀) ∧
            ‖restartSectionCenterFlow h t Z‖ < 2 * C₀ * a ∧
            ‖restartSectionRemainder h t Z‖ ≤
              4 * C * C₀ ^ 2 * a ^ 2 * T₁ + 6 * h * C₀ * a ^ (q₀ + 1) ∧
            ‖restartSectionRemainder h t Z‖ ≤ a / 8 ∧
            ∀ i : Fin 2, 0 ≤ Z i.succ →
              Z i.succ / 2 ≤ x (i.addNat 3) ∧ x (i.addNat 3) ≤ 2 * Z i.succ := by
  obtain ⟨A, hA, HA⟩ := exists_restartSectionRemainder_bounds
  obtain ⟨B, _, HB⟩ := exists_restartSection_fastLayer_control
  obtain ⟨D, hD, HD⟩ := exists_restartSectionWeakMultiplier_bounds
  let C := max A (max B D)
  have hAC : A ≤ C := le_max_left _ _
  have hBC : B ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hDC : D ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hC : 32 ≤ C := hA.trans hAC
  have hCp : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hC
  refine ⟨C, hC, ?_⟩
  intro h hh C₀ hC₀ q₀ q₁ hq₀ hq
  have hCh : C * h ≤ 1 / 4 := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp hh.2
    linarith only [H]
  have hhsmall : h ≤ 1 / 128 := by
    nlinarith only [hCh, mul_le_mul_of_nonneg_right hC hh.1.le]
  let K := 2 * C * C₀ ^ 2 * q₁ + 6 * h * C₀
  have hq₁ : 0 ≤ q₁ := by linarith only [hq₀, hq]
  have HI : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have HL : Tendsto (fun a : ℝ => a * Real.log a) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one, mul_comm] using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  have HE : Tendsto (fun a : ℝ => K * (a + |a * Real.log a|)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [abs_zero, add_zero, mul_zero] using (HI.add HL.abs).const_mul K
  have Hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0,
      ((0 < a ∧ a ≤ 1) ∧ 2 * C₀ * a ≤ 1 / 16 ∧
        C * (2 * C₀ * a) * (q₁ / 2 * Real.log (1 / a)) ≤ 1 / 8) ∧
      a ≤ 1 / 128 ∧ K * (a + |a * Real.log a|) ≤ 1 / 8 := by
    filter_upwards [eventually_restart_cutoff_budget C C₀ q₁,
      HI.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 128)),
      HE.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))] with a hb ha he
    exact ⟨hb, ha.le, he.le⟩
  obtain ⟨astar, hastar, Hscale⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp Hsmall
  refine ⟨astar, hastar, ?_⟩
  intro a ha T₀ T₁
  obtain ⟨Hb, hasmall, HEa⟩ := Hscale ha
  have hlog : 0 ≤ Real.log (1 / a) :=
    Real.log_nonneg ((le_div_iff₀ ha.1).mpr (by linarith only [Hb.1.2]))
  have hT₀ : 0 ≤ T₀ := mul_nonneg (by linarith only [hq₀]) hlog
  have hTT : T₀ ≤ T₁ := mul_le_mul_of_nonneg_right (by linarith only [hq]) hlog
  have hT₁ : 0 ≤ T₁ := hT₀.trans hTT
  let b := 2 * C₀ * a
  have hb : 0 < b := by dsimp only [b]; positivity [ha.1]
  have Hbudget (E : ℝ) (hEC : E ≤ C) :
      E * h ≤ 1 / 4 ∧ E * b * T₁ ≤ 1 / 8 :=
    ⟨(mul_le_mul_of_nonneg_right hEC hh.1.le).trans hCh,
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hEC hb.le) hT₁).trans Hb.2.2⟩
  refine ⟨hasmall, hT₀, hTT, ?_⟩
  intro Z hZ
  have hZb : ‖Z‖ ≤ b / 2 := by dsimp only [b]; linarith only [hZ]
  have hrad := restartSectionRadicand_pos_of_small
    (by rw [abs_of_pos hh.1]; linarith only [hhsmall] : |h| ≤ 1 / 16)
    (by linarith only [hZb, Hb.2.1] : ‖Z‖ ≤ 1 / 16)
  refine ⟨hrad, ?_⟩
  intro t ht x
  have ht0 : 0 ≤ t := hT₀.trans ht.1
  have htT : t ∈ Icc (0 : ℝ) T₁ := ⟨ht0, ht.2⟩
  have HF := HB h b T₁ Z hh.1 (Hbudget B hBC).1 ⟨hb, Hb.2.1⟩ hT₁
    (Hbudget B hBC).2 hZb t htT
  have HR := HA h b T₁ hh.1 (Hbudget A hAC).1 ⟨hb, Hb.2.1⟩ hT₁
    (Hbudget A hAC).2 t htT Z hZb
  have hdecay : Real.exp (-2 * t) ≤ a ^ q₀ := by
    calc
      _ ≤ Real.exp (-2 * T₀) := Real.exp_le_exp.mpr (by linarith only [ht.1])
      _ = _ := by
        rw [Real.rpow_def_of_pos ha.1]
        congr 1
        dsimp only [T₀]
        rw [one_div, Real.log_inv]
        ring
  have Herror : ‖restartSectionRemainder h t Z‖ ≤
      4 * C * C₀ ^ 2 * a ^ 2 * T₁ + 6 * h * C₀ * a ^ (q₀ + 1) := by
    apply HR.2.1.trans
    have H₁ : 4 * A * t * ‖Z‖ ^ 2 ≤ 4 * C * T₁ * (C₀ * a) ^ 2 := by
      gcongr
      exact ht.2
    have H₂ : 6 * h * Real.exp (-2 * t) * ‖Z‖ ≤ 6 * h * a ^ q₀ * (C₀ * a) := by
      gcongr <;> positivity [hh.1, ha.1]
    exact (add_le_add H₁ H₂).trans_eq (by rw [Real.rpow_add ha.1, Real.rpow_one]; ring)
  have Hpower : a ^ (q₀ + 1) ≤ a ^ (2 : ℕ) := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge ha.1 Hb.1.2
      (by linarith only [hq₀] : (2 : ℝ) ≤ q₀ + 1)
  have HerrorSmall : ‖restartSectionRemainder h t Z‖ ≤ a / 8 := by
    have H := mul_le_mul_of_nonneg_right HEa ha.1.le
    rw [abs_mul, abs_of_pos ha.1] at H
    have hloga : Real.log (1 / a) = |Real.log a| := by
      rw [one_div, Real.log_inv, abs_of_nonpos (Real.log_nonpos ha.1.le Hb.1.2)]
    have HT : T₁ = q₁ / 2 * |Real.log a| := by dsimp only [T₁]; rw [hloga]
    have HP := mul_le_mul_of_nonneg_left Hpower (show 0 ≤ 6 * h * C₀ by positivity [hh.1])
    have HA0 : 0 ≤ 2 * C * C₀ ^ 2 * q₁ * a ^ 2 := by positivity
    have HB0 : 0 ≤ 6 * h * C₀ * a ^ 2 * |Real.log a| := by positivity [hh.1]
    dsimp only [K] at H
    rw [HT] at Herror
    nlinarith only [Herror, H, HP, HA0, HB0]
  have hc := restartSectionChart_constraint hrad.le
  refine ⟨normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht0,
    (normalizedMaxCurve_forward_of_constraint hc ht0).2.1, HF.2.2.1,
    ⟨HF.1, HF.2.1.trans (mul_le_mul_of_nonneg_left hdecay hh.1.le)⟩,
    HF.2.2.2.2, Herror, HerrorSmall, ?_⟩
  intro i hi
  have HW := HD h b t hh.1 (Hbudget D hDC).1 ⟨hb, Hb.2.1⟩ ht0
    ((mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ D * b by
      have : 0 ≤ D := le_trans (by norm_num : (0 : ℝ) ≤ 32) hD
      positivity)).trans (Hbudget D hDC).2) Z hZb i
  dsimp only [x]
  rw [HW.1]
  exact ⟨by nlinarith only [mul_le_mul_of_nonneg_left HW.2.2.1.1.le hi],
    by nlinarith only [mul_le_mul_of_nonneg_left HW.2.2.1.2.le hi]⟩

end BianchiIX
