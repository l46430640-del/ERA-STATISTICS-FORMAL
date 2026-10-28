import BianchiIX.Dynamics.TerminalWallFactorBounds

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

/-- The old-wall logarithm retains coefficient one under the actual terminal entrance. -/
theorem terminalEntranceInput_passive_log_fderiv {h : ℝ} {Y : ExitTailState}
    (hR : 1 < Y 0) (HV : coreTailValid h Y) (i : Fin 2)
    (hy : Y i.succ ≠ 0) (hB : terminalWallFactor h Y i ≠ 0)
    (HB : ContDiffAt ℝ 2 (fun Z => terminalWallFactor h Z i) Y) :
    ContDiffAt ℝ 2 (fun Z => Real.log (terminalEntranceInput h Z (if i = 0 then 3 else 2))) Y ∧
      ∀ d : ExitTailState,
        fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z (if i = 0 then 3 else 2))) Y d =
          d i.succ / Y i.succ + fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z i)) Y d := by
  have HY : ContDiffAt ℝ 2 (fun Z : ExitTailState => Real.log (Z i.succ)) Y :=
    (contDiffAt_apply ℝ ℝ i.succ Y).log hy
  have HL := HB.log hB
  have HE : (fun Z => Real.log (terminalEntranceInput h Z (if i = 0 then 3 else 2))) =ᶠ[𝓝 Y]
      (fun Z => Real.log (Z i.succ) + Real.log (terminalWallFactor h Z i)) := by
    filter_upwards [(coreTail_regular_of_valid hR HV).2.2,
      (continuousAt_apply i.succ Y).eventually_ne hy, HB.continuousAt.eventually_ne hB] with Z hZ hyZ hBZ
    have H : terminalEntranceInput h Z (if i = 0 then 3 else 2) = Z i.succ * terminalWallFactor h Z i := by
      fin_cases i
      · exact (terminalEntranceInput_wall_factors hZ).2.2
      · exact (terminalEntranceInput_wall_factors hZ).2.1
    rw [H, Real.log_mul hyZ hBZ]
  refine ⟨(HY.add HL).congr_of_eventuallyEq HE, ?_⟩
  intro d
  have HD := ((hasFDerivAt_apply (𝕜 := ℝ) i.succ Y).log hy).add
    (HL.differentiableAt (by norm_num)).hasFDerivAt
  change HasFDerivAt (fun Z => Real.log (Z i.succ) + Real.log (terminalWallFactor h Z i)) _ Y at HD
  rw [HE.fderiv_eq, HD.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [div_eq_mul_inv, mul_comm]

/-- Formula (D.35) for every normalized square-root cone direction, with no wall-ratio condition. -/
theorem exists_terminalEntranceInput_cone_uniform {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 1000)
    {J : ℕ} (hJ : 2 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 1000 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let z := terminalEntranceInput h Y
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalEntranceInput h) Y ∧
        (∀ i : Fin 3, 0 < z i.succ ∧
          ContDiffAt ℝ 2 (fun Z => Real.log (terminalEntranceInput h Z i.succ)) Y) ∧
        ∀ d : ExitTailState, d 0 = 1 → |d 1| ≤ Real.sqrt u → |d 2| ≤ Real.sqrt w →
          |fderiv ℝ (fun Z => terminalEntranceInput h Z 0) Y d| ≤ C / α ^ 2 ∧
          |fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 1)) Y d| ≤ C / α ∧
          |fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 2)) Y d| ≤ C / α + 1 / Real.sqrt w ∧
          |fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 3)) Y d| ≤ C / α + 1 / Real.sqrt u := by
  obtain ⟨A, hA, εd, hεd, HD⟩ := exists_terminalEntranceInput_derivative_uniform hη₀ hJ
  obtain ⟨B, hB, εm, hεm, HM⟩ := exists_terminalWallFactor_bounds_uniform
    ⟨hη₀.1, by linarith only [hη₀.2]⟩ hJ
  let C := A + B
  have hAC : A ≤ C := by dsimp only [C]; linarith only [hB]
  have hBC : B ≤ C := by dsimp only [C]; linarith only [hA]
  let ε := min εd (min εm 1)
  have hε : 0 < ε := lt_min hεd (lt_min hεm (by norm_num))
  refine ⟨C, hA.trans hAC, ε, hε, ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum hu hw Y h z
  have hsd := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left εd (min εm 1))
    (pow_nonneg hα.1.le (2 * J)))
  have hsm := hsmall.trans (mul_le_mul_of_nonneg_right
    ((min_le_right εd (min εm 1)).trans (min_le_left εm 1)) (pow_nonneg hα.1.le (2 * J)))
  have hb1 : b ≤ 1 := (hsmall.trans (mul_le_of_le_one_right hε.le
    (pow_le_one₀ hα.1.le hα.2))).trans ((min_le_right εd (min εm 1)).trans (min_le_right εm 1))
  have hsum' : u + w ≤ b := by simpa only [abs_of_pos hu, abs_of_pos hw] using hsum
  have hu1 : u ≤ 1 := by linarith only [hsum', hw, hb1]
  have hw1 : w ≤ 1 := by linarith only [hsum', hu, hb1]
  obtain ⟨HV, _, Hreg, _, Hder, _⟩ := HD η α b u w hηlo hηhi hα hb hsd hsum
  obtain ⟨_, Hv, Hw, Hu, Hlog, Hfactor⟩ := HM η α b u w hηlo
    (by linarith only [hηhi]) hα hb hsm hsum
  have Hz1 : 0 < z 1 := (mul_pos (div_pos (hη₀.1.trans_le hηlo) (by norm_num))
    (pow_pos hα.1 (J - 2))).trans_le Hu.1
  have Hz2 : 0 < z 2 := by change 0 < terminalEntranceInput h Y 2; rw [Hv]; exact mul_pos hw (Hfactor 1).1
  have Hz3 : 0 < z 3 := by change 0 < terminalEntranceInput h Y 3; rw [Hw]; exact mul_pos hu (Hfactor 0).1
  have Hz (i : Fin 3) : 0 < z i.succ := by fin_cases i <;> assumption
  have hR : 1 < Y 0 := by change 1 < 2 + 2 * α; linarith only [hα.1]
  refine ⟨HV, Hreg, fun i => ⟨Hz i, ((contDiffAt_pi.mp Hreg) i.succ).log (Hz i).ne'⟩, ?_⟩
  intro d hd0 hd1 hd2
  have hdnorm : ‖d‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    simp only [Real.norm_eq_abs]
    fin_cases i
    · simp [hd0]
    · exact hd1.trans (Real.sqrt_le_one.mpr hu1)
    · exact hd2.trans (Real.sqrt_le_one.mpr hw1)
  have Hbound (L : ExitTailState →L[ℝ] ℝ) {K : ℝ} (hL : ‖L‖ ≤ K) : |L d| ≤ K :=
    (L.le_opNorm d).trans ((mul_le_of_le_one_right (norm_nonneg L) hdnorm).trans hL)
  have Hpassive (i : Fin 2) (hy : 0 < Y i.succ) (hd : |d i.succ| ≤ Real.sqrt (Y i.succ)) :
      |fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z (if i = 0 then 3 else 2))) Y d| ≤
        C / α + 1 / Real.sqrt (Y i.succ) := by
    rw [(terminalEntranceInput_passive_log_fderiv hR HV i hy.ne' (Hfactor i).1.ne' (Hfactor i).2.1).2 d]
    have Hratio : |d i.succ / Y i.succ| ≤ 1 / Real.sqrt (Y i.succ) := by
      rw [abs_div, abs_of_pos hy]
      exact (div_le_div_of_nonneg_right hd hy.le).trans_eq Real.sqrt_div_self'
    have Hfactor' := Hbound _ (Hfactor i).2.2.2.2.2
    have Hconst := div_le_div_of_nonneg_right hBC hα.1.le
    exact (abs_add_le _ _).trans (by linarith only [Hratio, Hfactor', Hconst])
  refine ⟨?_, (Hbound _ Hlog).trans (div_le_div_of_nonneg_right hBC hα.1.le), Hpassive 1 hw hd2,
    Hpassive 0 hu hd1⟩
  rw [fderiv_apply (Hreg.differentiableAt (by norm_num))]
  exact (norm_le_pi_norm _ 0).trans (((fderiv ℝ (terminalEntranceInput h) Y).le_opNorm d).trans
    ((mul_le_of_le_one_right (norm_nonneg _) hdnorm).trans
      (Hder.trans (div_le_div_of_nonneg_right hAC (sq_nonneg α)))))

/-- The directional estimates persist on the proportional fixed-height phase window. -/
theorem exists_terminalEntranceInput_cone_frozen {η : ℝ} (hη : 0 < η) (hηhi : 2 * η ≤ 1 / 1000)
    {J : ℕ} (hJ : 2 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α₀ α b u w : ℝ,
      0 < α₀ → (0 < α ∧ α ≤ 1) → |Real.log (α / α₀)| < Real.log 2 / J →
      0 < b → b ≤ ε * α₀ ^ (2 * J + 1) → |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α₀ ^ J
      let z := terminalEntranceInput h Y
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalEntranceInput h) Y ∧
        (∀ i : Fin 3, 0 < z i.succ ∧
          ContDiffAt ℝ 2 (fun Z => Real.log (terminalEntranceInput h Z i.succ)) Y) ∧
        ∀ d : ExitTailState, d 0 = 1 → |d 1| ≤ Real.sqrt u → |d 2| ≤ Real.sqrt w →
          |fderiv ℝ (fun Z => terminalEntranceInput h Z 0) Y d| ≤ C / α ^ 2 ∧
          |fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 1)) Y d| ≤ C / α ∧
          |fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 2)) Y d| ≤ C / α + 1 / Real.sqrt w ∧
          |fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 3)) Y d| ≤ C / α + 1 / Real.sqrt u := by
  obtain ⟨C, hC, ε₀, hε₀, HC⟩ := exists_terminalEntranceInput_cone_uniform
    (η₀ := η / 2) ⟨by positivity, by linarith only [hη, hηhi]⟩ hJ
  refine ⟨C, hC, ε₀ / 8, by positivity, ?_⟩
  intro α₀ α b u w hα₀ hα hband hb hsmall hsum hu hw Y h z
  let ηeff := η * α₀ ^ J / α ^ J
  have hJ1 : 1 ≤ J := by omega
  have hηeff := terminal_frozen_height_coefficient hη hα.1 hα₀ hJ1 hband
  have hheight : ηeff * α ^ J = h := div_mul_cancel₀ _ (pow_ne_zero J hα.1.ne')
  have hratio := terminal_logBand_power_ratio hα.1 hα₀ hJ1 hband
  have hpower : α₀ ^ J ≤ 2 * α ^ J := by linarith only [hratio.1]
  have hamp := terminal_powerBand_amplitude_ratio hα.1 hα₀ hJ1 hpower
  have hsmall₀ : b ≤ ε₀ * α ^ (2 * J) := calc
    b ≤ (ε₀ / 8) * α₀ ^ (2 * J + 1) := hsmall
    _ ≤ (ε₀ / 8) * (8 * α ^ (2 * J + 1)) := mul_le_mul_of_nonneg_left hamp (by positivity)
    _ = ε₀ * α ^ (2 * J + 1) := by ring
    _ ≤ ε₀ * α ^ (2 * J) := mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one hα.1.le hα.2 (by omega)) hε₀.le
  have H := HC ηeff α b u w hηeff.1.le (hηeff.2.le.trans hηhi) hα hb hsmall₀ hsum hu hw
  dsimp only at H
  rwa [hheight] at H

end BianchiIX
