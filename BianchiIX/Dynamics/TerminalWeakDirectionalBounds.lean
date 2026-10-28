import BianchiIX.Dynamics.TerminalConnectionLogBounds
import BianchiIX.Analysis.TerminalWeakLogComposition

noncomputable section

namespace BianchiIX

def terminalSharpWeakDirection (u : ℝ) : ExitTailState := ![1, Real.sqrt u, 0]

/-- The actual terminal weak logarithmic response retains its old strong-wall diagonal. -/
theorem exists_terminal_weak_directional_error :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η₀ : ℝ, (0 < η₀ ∧ η₀ ≤ δ) →
      ∀ J : ℕ, 2 ≤ J → ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ δ → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let L := -Real.log (terminalEntranceInput h Y 2)
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalConnectionState h) Y ∧
        0 < terminalConnectionState h Y 1 ∧ 0 < terminalConnectionState h Y 3 ∧
        DifferentiableAt ℝ (terminalConnectionLogWalls h) Y ∧
        |fderiv ℝ (terminalConnectionLogWalls h) Y (terminalSharpWeakDirection u) 1 - 1 / Real.sqrt u| ≤
          C * (L + 1 / α) := by
  obtain ⟨A, hA, εin, hεin, hεinhi, HA⟩ := exists_entrance_return_full_columns
  let δ := min (εin / 4) (1 / 40000)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  refine ⟨δ, hδ, min_le_right _ _, ?_⟩
  intro η₀ hη₀ J hJ
  have hη₀hi : η₀ ≤ 1 / 1000 := hη₀.2.trans ((min_le_right _ _).trans (by norm_num))
  have hη₀hi' : η₀ ≤ 1 / 100 := hη₀hi.trans (by norm_num)
  obtain ⟨B, hB, εc, hεc, HC⟩ := exists_terminalEntranceInput_cone_uniform ⟨hη₀.1, hη₀hi⟩ hJ
  obtain ⟨E, hE, εm, hεm, HM⟩ := exists_terminalWallFactor_bounds_uniform ⟨hη₀.1, hη₀hi'⟩ hJ
  obtain ⟨εi, hεi, HI⟩ := exists_terminal_cycle_entrance_inputs_uniform hεin ⟨hη₀.1, hη₀hi'⟩ (q := 0) hJ
  obtain ⟨_, _, εg, hεg, HG⟩ := exists_terminal_axisCycle_endpoint_uniform ⟨hη₀.1, hη₀hi'⟩ hJ
  let D := B + E
  have hBD : B ≤ D := by dsimp only [D]; linarith only [hE]
  have hED : E ≤ D := by dsimp only [D]; linarith only [hB]
  have hD : 1 ≤ D := hB.trans hBD
  have hA1 : 1 ≤ A + 1 := by linarith only [hA]
  let ε := min εc (min εm (min εi (min εg 1)))
  have hε : 0 < ε := lt_min hεc (lt_min hεm (lt_min hεi (lt_min hεg (by norm_num))))
  have hC : 1 ≤ 5 * (A + 1) * D := by
    nlinarith only [hA1, hD, mul_le_mul_of_nonneg_left hD (by linarith only [hA] : 0 ≤ A + 1)]
  refine ⟨5 * (A + 1) * D, hC, ε, hε, ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum hu hw Y h L
  have hα0 : 0 < α := hα.1
  have hη1000 : η ≤ 1 / 1000 := hηhi.trans ((min_le_right _ _).trans (by norm_num))
  have hη100 : η ≤ 1 / 100 := hη1000.trans (by norm_num)
  have hηin : η ≤ εin / (4 * (11 / 5) ^ (0 : ℕ)) := by
    simpa only [pow_zero, mul_one] using hηhi.trans (min_le_left _ _)
  have small {a : ℝ} (ha : ε ≤ a) : b ≤ a * α ^ (2 * J) :=
    hsmall.trans (mul_le_mul_of_nonneg_right ha (pow_nonneg hα.1.le _))
  have hεm' : ε ≤ εm := (min_le_right _ _).trans (min_le_left _ _)
  have hεi' : ε ≤ εi := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεg' : ε ≤ εg := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨HV, Hreg, Hz, Hcone⟩ := HC η α b u w hηlo hη1000 hα hb (small (min_le_left _ _)) hsum hu hw
  obtain ⟨_, _, Hweak, _, _, Hfactor⟩ := HM η α b u w hηlo hη100 hα hb (small hεm') hsum
  obtain ⟨_, _, HK, Hm, Hu, Hv, Hw, _, HH⟩ := HI η α b u w hηlo hη100 hηin hα hb (small hεi') hsum hu hw
  obtain ⟨_, _, _, _, Hk, _⟩ := HG η α b u w hηlo hη100 hα hb (small hεg') hsum
  let y := terminalCyclicInput h Y
  let z := terminalEntranceInput h Y
  let k := coreRadius (y 0) (y 2)
  let d := terminalSharpWeakDirection u
  let e := fderiv ℝ (terminalEntranceInput h) Y d
  change 7 / 4 < k at HK
  change 0 < y 2 ∧ y 2 < 1 / 2 at Hv
  change z 3 = u * terminalWallFactor h Y 0 at Hweak
  have hk : 1 / α ≤ k := by
    change 19 / (10 * α) < k ∧ k < 11 / (5 * α) at Hk
    apply le_trans _ Hk.1.le
    apply (div_le_div_iff₀ hα.1 (by positivity : 0 < 10 * α)).mpr
    linarith only [hα.1]
  have hm : 1 ≤ y 0 := by change 2 < y 0 at Hm; linarith only [Hm]
  have hv : 0 < y 2 ∧ y 2 < 1 := ⟨Hv.1, by linarith only [Hv.2]⟩
  have hu' : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := ⟨Hu.1.le, Hu.2.1.trans hεinhi⟩
  have hw' : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := ⟨Hw.1.le, Hw.2.1.trans hεinhi⟩
  have hin1 : εin ≤ 1 := hεinhi.trans (by norm_num)
  have hR : 1 < Y 0 := by change 1 < 2 + 2 * α; linarith only [hα.1]
  have Hstate := (terminalConnection_regular_of_entrance hR HV HH.ne' HK.le hm hu' hv hw').2
  have Hcyc : ContDiffAt ℝ 2 (terminalCyclicInput h) Y :=
    ContDiffAt.comp (g := projectiveCycle) (f := coreTailState h) Y
      (contDiffAt_projectiveCycle 2 HH.ne') (coreTail_regular_of_valid hR HV).2.1
  have HR := entranceReturn_regular HK.le hm hu' hv hw'
  have Hpos := entranceReturn_walls_pos HK.le hm ⟨Hu.1, hu'.2⟩ hv ⟨Hw.1, hw'.2⟩
    (entranceReturnTime y) ⟨HR.1.1.1.1.le, le_rfl⟩
  obtain ⟨Ψ, HΨ, _, _, HW⟩ := HA y 1 HK.le hm ⟨Hu.1, Hu.2.1⟩ hv ⟨Hw.1, Hw.2.1⟩ (Or.inl rfl)
  let F := fun z => entranceLogWalls 1 (entranceReturnState (Ψ z))
  have HF : DifferentiableAt ℝ F z := by
    have Hlog : DifferentiableAt ℝ (entranceLogWalls 1) (entranceReturnState (Ψ z)) := by
      change DifferentiableAt ℝ (entranceLogWalls 1) (entranceReturnState (Ψ (entranceRadialCoordinates y)))
      rw [HΨ.apply_base]
      exact (hasFDerivAt_entranceLogWalls 1 Hpos.1.ne' Hpos.2.2.ne').differentiableAt
    exact Hlog.comp z (HΨ.hasFDerivAt_return HK.le hm hu' hv hw').differentiableAt
  have Hd := terminalConnectionLogWalls_differential HΨ Hcyc.continuousAt (Hreg.differentiableAt (by norm_num)) HF
  have hL : 0 ≤ L := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have hb1 : b ≤ 1 := (hsmall.trans (mul_le_of_le_one_right hε.le (pow_le_one₀ hα.1.le hα.2))).trans hε1
  have hu1 : u ≤ 1 := by linarith only [le_abs_self u, abs_nonneg w, hsum, hb1]
  have hd0 : d 0 = 1 := rfl
  have hd1 : |d 1| ≤ Real.sqrt u := by simp [d, terminalSharpWeakDirection, abs_of_nonneg (Real.sqrt_nonneg u)]
  have hd2 : |d 2| ≤ Real.sqrt w := by simp [d, terminalSharpWeakDirection]
  have hdnorm : ‖d‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    fin_cases i
    · norm_num [d, terminalSharpWeakDirection]
    · simpa [d, terminalSharpWeakDirection, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg u)] using Real.sqrt_le_one.mpr hu1
    · norm_num [d, terminalSharpWeakDirection]
  have Hfactorbound (i : Fin 2) : |fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z i)) Y d| ≤ D / α :=
    ((fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z i)) Y).le_opNorm d).trans
      ((mul_le_of_le_one_right (norm_nonneg _) hdnorm).trans
        ((Hfactor i).2.2.2.2.2.trans (div_le_div_of_nonneg_right hED hα.1.le)))
  have Hlv : |fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 2)) Y d| ≤ D / α := by
    have HP := (terminalEntranceInput_passive_log_fderiv hR HV 1 hw.ne' (Hfactor 1).1.ne' (Hfactor 1).2.1).2 d
    change fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 2)) Y d =
      0 / w + fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z 1)) Y d at HP
    rw [HP, zero_div, zero_add]
    exact Hfactorbound 1
  have Hlw : |fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 3)) Y d - 1 / Real.sqrt u| ≤ D / α := by
    have HP := (terminalEntranceInput_passive_log_fderiv hR HV 0 hu.ne' (Hfactor 0).1.ne' (Hfactor 0).2.1).2 d
    change fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 3)) Y d =
      Real.sqrt u / u + fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z 0)) Y d at HP
    rw [HP, Real.sqrt_div_self', add_sub_cancel_left]
    exact Hfactorbound 0
  have Hcomponent (i : Fin 3) : e i.succ = z i.succ *
      fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z i.succ)) Y d := by
    have H := hasFDerivAt_pi'.mp (Hreg.differentiableAt (by norm_num)).hasFDerivAt i.succ
    rw [(H.log (Hz i).1.ne').fderiv]
    simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
    change e i.succ = z i.succ * ((z i.succ)⁻¹ * e i.succ)
    rw [← mul_assoc, mul_inv_cancel₀ (show z i.succ ≠ 0 from (Hz i).1.ne'), one_mul]
  have Hscaled (i : Fin 3) {K : ℝ}
      (H : |fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z i.succ)) Y d| ≤ K) : |e i.succ| ≤ z i.succ * K := by
    rw [Hcomponent i, abs_mul, abs_of_pos (Hz i).1]
    exact mul_le_mul_of_nonneg_left H (Hz i).1.le
  obtain ⟨Hr, Hlu, _, _⟩ := Hcone d hd0 hd1 hd2
  have Hrd : |e 0| ≤ D / α ^ 2 := by
    have H0 := congrArg (fun T : ExitTailState →L[ℝ] ℝ => T d)
      (fderiv_apply (Hreg.differentiableAt (by norm_num)) 0)
    change fderiv ℝ (fun Z => terminalEntranceInput h Z 0) Y d = e 0 at H0
    rw [← H0]
    exact Hr.trans (div_le_div_of_nonneg_right hBD (sq_nonneg α))
  have Hwd : |e 3 / y 3 - 1 / Real.sqrt u| ≤ D / α := by
    change |e 3 / z 3 - 1 / Real.sqrt u| ≤ D / α
    have HE := Hcomponent 2
    change e 3 = z 3 * fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 3)) Y d at HE
    have hz3 : z 3 ≠ 0 := (Hz 2).1.ne'
    rw [HE, mul_div_cancel_left₀ _ hz3]
    exact Hlw
  have hwt : y 3 * (1 / Real.sqrt u) ≤ D / α ^ 2 := by
    change z 3 * (1 / Real.sqrt u) ≤ D / α ^ 2
    calc
      _ = terminalWallFactor h Y 0 * (u / Real.sqrt u) := by rw [Hweak]; ring
      _ = terminalWallFactor h Y 0 * Real.sqrt u := by rw [Real.div_sqrt]
      _ ≤ terminalWallFactor h Y 0 := mul_le_of_le_one_right (Hfactor 0).1.le (Real.sqrt_le_one.mpr hu1)
      _ ≤ E / α ^ 2 := (Hfactor 0).2.2.2.1
      _ ≤ D / α ^ 2 := div_le_div_of_nonneg_right hED (sq_nonneg α)
  have HAA : A ≤ A + 1 := by linarith
  have H := terminal_weak_log_composition_error (fderiv ℝ F z) e hA1 hD hα hk
    ⟨Hu.1, Hu.2.1.trans hin1⟩ hv.1 ⟨Hw.1, Hw.2.1.trans hin1⟩ hL (by positivity) hwt Hrd
    (Hscaled 0 (Hlu.trans (div_le_div_of_nonneg_right hBD hα.1.le))) (Hscaled 1 Hlv) Hwd
    (HW.1.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right HAA hL) (sq_nonneg k)))
    (HW.2.1.trans (div_le_div_of_nonneg_right HAA (sq_nonneg k)))
    (HW.2.2.1.trans (div_le_div_of_nonneg_right HAA hv.1.le))
    (HW.2.2.2.trans (div_le_div_of_nonneg_right HAA (sq_nonneg k)))
  refine ⟨HV, Hstate, Hpos.1, Hpos.2.2, Hd.1, ?_⟩
  rw [Hd.2 d]
  exact H

end BianchiIX
