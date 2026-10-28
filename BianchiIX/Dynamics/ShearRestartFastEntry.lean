import BianchiIX.Dynamics.ShearRestartFastControl
import BianchiIX.Dynamics.RestartLinearApproximation

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Both signed shear families reach the fast-layer endpoint with preserved shear and wall-relative derivatives. -/
theorem exists_restartShearFastEntry_control :
    ∃ C ≥ (32 : ℝ), ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q : ℝ, 2 < q → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε σ n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) → |σ| = 1 →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let T := q / 2 * Real.log (1 / a)
            let Z := restartShearCurve σ n₂ n₃ ρ
            let x := normalizedMaxCurve (restartSectionChart h Z) 0 T
            let p := restartSectionRadialState h T Z
            let v := fderiv ℝ (restartSectionRadialState h T) Z (restartShearDirection σ)
            a ≤ 1 ∧ 8 * a ≤ 1 / 16 ∧ 0 ≤ T ∧ 0 < restartSectionRadicand h Z ∧
            T ∈ normalizedMaxDomain (restartSectionChart h Z) 0 ∧ stateConstraint x = 1 ∧ x 0 ≤ -(15 / 16) ∧
            HasDerivAt (fun y => restartSectionRadialState h T (restartShearCurve σ n₂ n₃ y)) v ρ ∧
            0 < p.1 ∧ p.1 ≤ h * a ^ q ∧
            (3 * a / 4 ≤ σ * p.2 0 ∧ σ * p.2 0 ≤ 9 * a / 4) ∧ ‖p.2‖ ≤ 8 * a ∧
            ‖v‖ ≤ 2 ∧ |v.1| ≤ 2 * p.1 / a ∧
            ∀ i : Fin 2, Z i.succ / 2 ≤ p.2 i.succ ∧ p.2 i.succ ≤ 2 * Z i.succ ∧
              |v.2 i.succ| ≤ 8 * C * p.2 i.succ / a := by
  obtain ⟨C, hC, HC⟩ := exists_restartShearCurve_control
  obtain ⟨hL, hhL, HL⟩ := exists_restartSection_linear_approximation
  have hCp : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32) hC
  refine ⟨C, hC, min hL (min (1 / (4 * C)) (1 / 64)),
    lt_min hhL (lt_min (by positivity) (by norm_num)), ?_⟩
  intro h hh q hq
  have hhsmall : h ≤ 1 / 64 := hh.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hCh : C * h ≤ 1 / 4 := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp
      (hh.2.trans ((min_le_right _ _).trans (min_le_left _ _)))
    nlinarith only [H]
  obtain ⟨K, _, aL, haL, HLa⟩ := HL h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ 2 (by norm_num) q hq
  have HI : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have Hlog : Tendsto (fun a : ℝ => a * Real.log a) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.rpow_one, mul_comm] using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  have HE : Tendsto (fun a : ℝ => K * (a + |a * Real.log a|)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [abs_zero, add_zero, mul_zero] using (HI.add Hlog.abs).const_mul K
  have Hbudget : ∀ᶠ a : ℝ in 𝓝[>] 0,
      ((0 < a ∧ a ≤ 1) ∧ 8 * a ≤ 1 / 16 ∧ C * (8 * a) * (q / 2 * Real.log (1 / a)) ≤ 1 / 8) ∧
      a * (q / 2 * Real.log (1 / a)) ≤ 1 ∧ K * (a + |a * Real.log a|) ≤ 1 / 8 := by
    filter_upwards [eventually_restart_cutoff_budget C 4 q, eventually_restart_cutoff_budget 1 1 q,
      HE.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))] with a H₁ H₂ H₃
    exact ⟨by simpa only [show (2 : ℝ) * 4 = 8 by norm_num] using H₁,
      by nlinarith only [H₂.2.2], H₃.le⟩
  obtain ⟨aB, haB, HBa⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp Hbudget
  refine ⟨min aL aB, lt_min haL haB, ?_⟩
  intro a ha ε σ n₂ n₃ hε hσ h₂ h₃ ρ hρ T Z x p v
  have Ha := HBa ⟨ha.1, ha.2.trans (min_le_right _ _)⟩
  have hT : 0 ≤ T := mul_nonneg (by linarith only [hq] : 0 ≤ q / 2)
    (Real.log_nonneg ((le_div_iff₀ ha.1).mpr (by linarith only [Ha.1.1.2])))
  obtain ⟨Hcurve, hneg, hnpos, hnexp, hcenter, hv, hnv, hwv⟩ := HC h a T hh.1 hCh Ha.1.1
    Ha.1.2.1 hT Ha.1.2.2 Ha.2.1 ε σ n₂ n₃ ρ hε hσ h₂ h₃ hρ
  have hZ := (restartShearCurve_annulus ha.1 hρ hσ hε h₂ h₃).1
  have hlin := HLa a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ Z hZ
  have herror : ‖restartSectionRemainder h T Z‖ ≤ a / 8 := by
    apply hlin.2.2.2.2.2.1.trans
    have H := mul_le_mul_of_nonneg_left Ha.2.2 ha.1.le
    rw [abs_mul, abs_of_pos ha.1] at H
    nlinarith only [H]
  have htransfer : ‖restartCenterTransfer h Z - Z‖ ≤ a / 8 := by
    have H := (restartCenterTransfer h - ContinuousLinearMap.id ℝ RestartCenterState).le_opNorm Z
    change ‖restartCenterTransfer h Z - Z‖ ≤ _ at H
    have HCbound := restartCenterTransfer_sub_id_bound ⟨hh.1.le, by linarith only [hhsmall]⟩
    have H' := H.trans (mul_le_mul HCbound hZ (norm_nonneg Z) (by positivity [hh.1]))
    exact H'.trans (by nlinarith only [mul_le_mul_of_nonneg_right hhsmall ha.1.le, ha.1])
  have hclose : ‖restartSectionCenterFlow h T Z - Z‖ ≤ a / 4 := by
    rw [hlin.2.2.2.1]
    have heq : restartCenterTransfer h Z + restartSectionRemainder h T Z - Z =
        (restartCenterTransfer h Z - Z) + restartSectionRemainder h T Z := by abel
    rw [heq]
    exact (norm_add_le _ _).trans (by linarith only [htransfer, herror])
  have hshear := restartShearCurve_shear_of_close hρ hσ hclose
  have hrad := restartSectionRadicand_pos_of_small (h := h) (Z := Z)
    (by rw [abs_of_pos hh.1]; linarith only [hhsmall]) (by linarith only [hZ, Ha.1.2.1])
  have he : Real.exp (-2 * T) = a ^ q := by
    rw [Real.rpow_def_of_pos ha.1]
    congr 1
    dsimp only [T]
    rw [one_div, Real.log_inv]
    ring
  rw [he] at hnexp
  exact ⟨Ha.1.1.2, Ha.1.2.1, hT, hrad, hlin.1,
    (normalizedMaxCurve_forward_of_constraint (restartSectionChart_constraint hrad.le) hT).2.1,
    hneg, Hcurve, hnpos, hnexp, hshear, hcenter, hv, hnv, hwv⟩

end BianchiIX
