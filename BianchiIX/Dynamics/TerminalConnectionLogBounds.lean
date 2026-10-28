import BianchiIX.Dynamics.TerminalEntranceCone
import BianchiIX.Dynamics.TerminalHeightInterval
import BianchiIX.Dynamics.EntranceFullReturnColumns
import BianchiIX.Analysis.TerminalLogComposition

noncomputable section

namespace BianchiIX

open Filter Set
open scoped Topology

def terminalConnectionLogWalls (h : ℝ) (Y : ExitTailState) : Fin 2 → ℝ :=
  entranceLogWalls 1 (terminalConnectionState h Y)

theorem terminalConnectionLogWalls_chart_germ {h : ℝ} {Y : ExitTailState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (terminalCyclicInput h Y) Ψ)
    (hc : ContinuousAt (terminalCyclicInput h) Y) :
    terminalConnectionLogWalls h =ᶠ[𝓝 Y] (fun Z =>
      entranceLogWalls 1 (entranceReturnState (Ψ (terminalEntranceInput h Z)))) := by
  filter_upwards [hc.tendsto.eventually HΨ.left_inverse] with Z hZ
  change Ψ (terminalEntranceInput h Z) = terminalCyclicInput h Z at hZ
  rw [hZ]
  rfl

/-- The complete logarithmic wall response belongs to the actual finite terminal passage. -/
theorem terminalConnectionLogWalls_differential {h : ℝ} {Y : ExitTailState}
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (terminalCyclicInput h Y) Ψ)
    (hc : ContinuousAt (terminalCyclicInput h) Y)
    (hz : DifferentiableAt ℝ (terminalEntranceInput h) Y)
    (hL : DifferentiableAt ℝ (fun z => entranceLogWalls 1 (entranceReturnState (Ψ z)))
      (terminalEntranceInput h Y)) :
    DifferentiableAt ℝ (terminalConnectionLogWalls h) Y ∧ ∀ d : ExitTailState,
      fderiv ℝ (terminalConnectionLogWalls h) Y d =
        fderiv ℝ (fun z => entranceLogWalls 1 (entranceReturnState (Ψ z)))
          (terminalEntranceInput h Y) (fderiv ℝ (terminalEntranceInput h) Y d) := by
  have HE := terminalConnectionLogWalls_chart_germ HΨ hc
  have HD := hL.hasFDerivAt.comp Y hz.hasFDerivAt
  refine ⟨HD.differentiableAt.congr_of_eventuallyEq HE, ?_⟩
  intro d
  rw [HE.fderiv_eq]
  exact congrArg (fun L : ExitTailState →L[ℝ] (Fin 2 → ℝ) => L d) HD.fderiv

theorem terminalConnectionLogWalls_fderiv {h : ℝ} {Y : ExitTailState}
    (hstate : DifferentiableAt ℝ (terminalConnectionState h) Y)
    (hu : terminalConnectionState h Y 1 ≠ 0) (hw : terminalConnectionState h Y 3 ≠ 0)
    (d : ExitTailState) :
    fderiv ℝ (terminalConnectionLogWalls h) Y d =
      ![fderiv ℝ (terminalConnectionState h) Y d 1 / terminalConnectionState h Y 1,
        fderiv ℝ (terminalConnectionState h) Y d 3 / terminalConnectionState h Y 3] := by
  have HD := (hasFDerivAt_entranceLogWalls 1 hu hw).differentiableAt.hasFDerivAt.comp Y hstate.hasFDerivAt
  change fderiv ℝ (entranceLogWalls 1 ∘ terminalConnectionState h) Y d = _
  rw [HD.fderiv, ContinuousLinearMap.comp_apply, entranceLogWalls_fderiv_apply 1 hu hw]
  simp only [entranceWallTangent, one_pow, one_mul]

/-- Formula (D.36) with separate logarithmic output rows and constants independent of both old walls. -/
theorem exists_terminalConnectionLogWalls_cone_uniform :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 1000 ∧ ∀ η₀ : ℝ, (0 < η₀ ∧ η₀ ≤ δ) →
      ∀ J : ℕ, 2 ≤ J → ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ δ → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let L := -Real.log (terminalEntranceInput h Y 2)
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalConnectionState h) Y ∧
        0 < terminalConnectionState h Y 1 ∧ 0 < terminalConnectionState h Y 3 ∧
        DifferentiableAt ℝ (terminalConnectionLogWalls h) Y ∧
        ∀ d : ExitTailState, d 0 = 1 → |d 1| ≤ Real.sqrt u → |d 2| ≤ Real.sqrt w →
          |fderiv ℝ (terminalConnectionLogWalls h) Y d 0| ≤
            C * ((1 + L) / α ^ 2 + 1 / (α * Real.sqrt w)) ∧
          |fderiv ℝ (terminalConnectionLogWalls h) Y d 1| ≤
            C * (L + 1 / α + 1 / Real.sqrt w + 1 / Real.sqrt u) := by
  obtain ⟨A, hA, εin, hεin, hεinhi, HA⟩ := exists_entrance_return_full_columns
  let δ := min (εin / 4) (1 / 1000)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  refine ⟨δ, hδ, min_le_right _ _, ?_⟩
  intro η₀ hη₀ J hJ
  have hη₀hi : η₀ ≤ 1 / 1000 := hη₀.2.trans (min_le_right _ _)
  have hη₀hi' : η₀ ≤ 1 / 100 := hη₀hi.trans (by norm_num)
  obtain ⟨B, hB, εc, hεc, HC⟩ := exists_terminalEntranceInput_cone_uniform ⟨hη₀.1, hη₀hi⟩ hJ
  obtain ⟨E, hE, εm, hεm, HM⟩ := exists_terminalWallFactor_bounds_uniform ⟨hη₀.1, hη₀hi'⟩ hJ
  obtain ⟨εi, hεi, HI⟩ := exists_terminal_cycle_entrance_inputs_uniform hεin ⟨hη₀.1, hη₀hi'⟩ (q := 0) hJ
  obtain ⟨_, _, εg, hεg, HG⟩ := exists_terminal_axisCycle_endpoint_uniform ⟨hη₀.1, hη₀hi'⟩ hJ
  let D := B + E
  have hBD : B ≤ D := by dsimp only [D]; linarith only [hE]
  have hED : E ≤ D := by dsimp only [D]; linarith only [hB]
  have hD : 1 ≤ D := hB.trans hBD
  have hD0 : 0 ≤ D := le_trans (by norm_num) hD
  have hA1 : 1 ≤ A + 1 := by linarith only [hA]
  let ε := min εc (min εm (min εi (min εg 1)))
  have hε : 0 < ε := lt_min hεc (lt_min hεm (lt_min hεi (lt_min hεg (by norm_num))))
  refine ⟨8 * (A + 1) * D, by nlinarith only [hA1, hD, mul_le_mul_of_nonneg_left hD (by linarith only [hA] : 0 ≤ A + 1)],
    ε, hε, ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum hu hw Y h L
  have hα0 : 0 < α := hα.1
  have hη1000 : η ≤ 1 / 1000 := hηhi.trans (min_le_right _ _)
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
  change 7 / 4 < k at HK
  change 0 < y 2 ∧ y 2 < 1 / 2 at Hv
  change z 3 = u * terminalWallFactor h Y 0 at Hweak
  have hk : 1 / α ≤ k ∧ k ≤ 3 / α := by
    change 19 / (10 * α) < k ∧ k < 11 / (5 * α) at Hk
    constructor
    · apply le_trans _ Hk.1.le
      apply (div_le_div_iff₀ hα.1 (by positivity : 0 < 10 * α)).mpr
      linarith only [hα.1]
    · apply Hk.2.le.trans
      apply (div_le_div_iff₀ (by positivity : 0 < 5 * α) hα.1).mpr
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
  obtain ⟨Ψ, HΨ, _, HU, HW⟩ := HA y 1 HK.le hm ⟨Hu.1, Hu.2.1⟩ hv ⟨Hw.1, Hw.2.1⟩ (Or.inl rfl)
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
  have hwt : y 3 * (1 / Real.sqrt u) ≤ D / α ^ 2 := by
    change z 3 * (1 / Real.sqrt u) ≤ D / α ^ 2
    calc
      _ = terminalWallFactor h Y 0 * (u / Real.sqrt u) := by rw [Hweak]; ring
      _ = terminalWallFactor h Y 0 * Real.sqrt u := by rw [Real.div_sqrt]
      _ ≤ terminalWallFactor h Y 0 := mul_le_of_le_one_right (Hfactor 0).1.le (Real.sqrt_le_one.mpr hu1)
      _ ≤ E / α ^ 2 := (Hfactor 0).2.2.2.1
      _ ≤ D / α ^ 2 := div_le_div_of_nonneg_right hED (sq_nonneg α)
  refine ⟨HV, Hstate, Hpos.1, Hpos.2.2, Hd.1, ?_⟩
  intro d hd0 hd1 hd2
  obtain ⟨Hr, Hlu, Hlv, Hlw⟩ := Hcone d hd0 hd1 hd2
  let e := fderiv ℝ (terminalEntranceInput h) Y d
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
  have Hrd : |e 0| ≤ D / α ^ 2 := by
    have H0 := congrArg (fun T : ExitTailState →L[ℝ] ℝ => T d)
      (fderiv_apply (Hreg.differentiableAt (by norm_num)) 0)
    change fderiv ℝ (fun Z => terminalEntranceInput h Z 0) Y d = e 0 at H0
    rw [← H0]
    exact Hr.trans (div_le_div_of_nonneg_right hBD (sq_nonneg α))
  have Hbd := div_le_div_of_nonneg_right hBD hα.1.le
  have HAA : A ≤ A + 1 := by linarith
  have H := terminal_log_composition_bounds (fderiv ℝ F z) e hA1 hD hα hk
    ⟨Hu.1, Hu.2.1.trans hin1⟩ hv.1 ⟨Hw.1, Hw.2.1.trans hin1⟩ hL
    (by positivity : 0 ≤ 1 / Real.sqrt w) (by positivity : 0 ≤ 1 / Real.sqrt u) hwt Hrd
    (Hscaled 0 (Hlu.trans Hbd)) (Hscaled 1 (Hlv.trans (add_le_add Hbd le_rfl)))
    (Hscaled 2 (Hlw.trans (add_le_add Hbd le_rfl)))
    (HU.1.trans (mul_le_mul_of_nonneg_right HAA hL)) (HU.2.1.trans HAA)
    (HU.2.2.1.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right HAA (by linarith only [HK] : 0 ≤ k)) hv.1.le))
    (HU.2.2.2.trans HAA)
    (HW.1.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right HAA hL) (sq_nonneg k)))
    (HW.2.1.trans (div_le_div_of_nonneg_right HAA (sq_nonneg k)))
    (HW.2.2.1.trans (div_le_div_of_nonneg_right HAA hv.1.le))
    (HW.2.2.2.trans (div_le_div_of_nonneg_right HAA (sq_nonneg k)))
  rw [Hd.2 d]
  have hfrac : 1 / Real.sqrt w / α = 1 / (α * Real.sqrt w) := by ring
  rw [hfrac] at H
  exact H

/-- The same output estimates hold throughout a common fixed-height phase neighborhood. -/
theorem exists_terminalConnectionLogWalls_cone_frozen :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 1000 ∧ ∀ η : ℝ, 0 < η → 2 * η ≤ δ →
      ∀ J : ℕ, 2 ≤ J → ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α₀ α b u w : ℝ,
      0 < α₀ → (0 < α ∧ α ≤ 1) → |Real.log (α / α₀)| < Real.log 2 / J →
      0 < b → b ≤ ε * α₀ ^ (2 * J + 1) → |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α₀ ^ J
      let L := -Real.log (terminalEntranceInput h Y 2)
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalConnectionState h) Y ∧
        0 < terminalConnectionState h Y 1 ∧ 0 < terminalConnectionState h Y 3 ∧
        DifferentiableAt ℝ (terminalConnectionLogWalls h) Y ∧
        ∀ d : ExitTailState, d 0 = 1 → |d 1| ≤ Real.sqrt u → |d 2| ≤ Real.sqrt w →
          |fderiv ℝ (terminalConnectionLogWalls h) Y d 0| ≤
            C * ((1 + L) / α ^ 2 + 1 / (α * Real.sqrt w)) ∧
          |fderiv ℝ (terminalConnectionLogWalls h) Y d 1| ≤
            C * (L + 1 / α + 1 / Real.sqrt w + 1 / Real.sqrt u) := by
  obtain ⟨δ, hδ, hδhi, HE⟩ := exists_terminalConnectionLogWalls_cone_uniform
  refine ⟨δ, hδ, hδhi, ?_⟩
  intro η hη hηhi J hJ
  obtain ⟨C, hC, ε₀, hε₀, HC⟩ := HE (η / 2) ⟨by positivity, by linarith only [hη, hηhi]⟩ J hJ
  refine ⟨C, hC, ε₀ / 8, by positivity, ?_⟩
  intro α₀ α b u w hα₀ hα hband hb hsmall hsum hu hw Y h L
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
