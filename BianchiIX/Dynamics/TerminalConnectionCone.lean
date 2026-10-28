import BianchiIX.Dynamics.TerminalConnectionLogBounds
import BianchiIX.Dynamics.TerminalConnectionSqrtBounds
import BianchiIX.Dynamics.TerminalPhaseCone
import BianchiIX.Analysis.TerminalConePowers
import BianchiIX.Analysis.SmallParameters

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

/-- Formula (D.37) for the actual terminal passage, including both phase powers. -/
theorem exists_terminal_connection_cone_scales :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η₀ : ℝ, (0 < η₀ ∧ η₀ ≤ δ) →
      ∀ J : ℕ, 4 ≤ J → ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b U W : ℝ,
      η₀ ≤ η → η ≤ δ → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |U| + |W| ≤ b → 0 < U → 0 < W →
      let Y : ExitTailState := ![2 + 2 * α, U, W]
      let h := η * α ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalConnectionState h) Y ∧
        ContDiffAt ℝ 2 (terminalConnectionPhase h) Y ∧
        0 < terminalConnectionState h Y 1 ∧ 0 < terminalConnectionState h Y 3 ∧
        ∀ d : ExitTailState, d 0 = 1 → |d 1| ≤ Real.sqrt U → |d 2| ≤ Real.sqrt W →
          let p := fderiv ℝ (terminalConnectionPhase h) Y d
          p < 0 ∧ 3 / (4 * α ^ 2) ≤ |p| ∧
          |fderiv ℝ (terminalConnectionState h) Y d 1| / (Real.sqrt (terminalConnectionState h Y 1) * |p|) ≤
            C * (α ^ (((J : ℝ) - 5) / 2) * W ^ (3 / 4 : ℝ) + α ^ ((J : ℝ) / 2 - 19 / 12) * W ^ (7 / 24 : ℝ)) ∧
          |fderiv ℝ (terminalConnectionState h) Y d 3| / (Real.sqrt (terminalConnectionState h Y 3) * |p|) ≤
            C * (Real.sqrt U + Real.sqrt W) := by
  obtain ⟨δp, hδp, hδphi, HP⟩ := exists_terminal_phase_cone_bounds
  obtain ⟨δl, hδl, _, HL⟩ := exists_terminalConnectionLogWalls_cone_uniform
  let δ := min δp δl
  have hδhi : δ ≤ 1 / 40000 := (min_le_left _ _).trans hδphi
  refine ⟨δ, lt_min hδp hδl, hδhi, ?_⟩
  intro η₀ hη₀ J hJ
  obtain ⟨_, _, εp, hεp, HP'⟩ := HP η₀ ⟨hη₀.1, hη₀.2.trans (min_le_left _ _)⟩ J hJ
  obtain ⟨B, hB, εl, hεl, HL'⟩ := HL η₀ ⟨hη₀.1, hη₀.2.trans (min_le_right _ _)⟩ J (by omega)
  obtain ⟨A, hA, εa, hεa, HA⟩ := exists_terminalConnection_sqrt_bounds_uniform
    ⟨hη₀.1, hη₀.2.trans hδhi⟩ (by omega : 2 ≤ J)
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hAA : A ≤ A ^ 2 := by nlinarith only [hA]
  let C := 48 * A ^ 2 * B
  have hC : 1 ≤ C := by
    dsimp only [C]
    nlinarith only [hA, hAA, mul_le_mul_of_nonneg_left hB (sq_nonneg A)]
  refine ⟨C, hC, min εp (min εl εa), lt_min hεp (lt_min hεl hεa), ?_⟩
  intro η α b U W hηlo hηhi hα hb hsmall hsum hU hW Y h
  have hα0 : 0 < α := hα.1
  have hsp := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hα.1.le _))
  have hsl := hsmall.trans (mul_le_mul_of_nonneg_right
    ((min_le_right _ _).trans (min_le_left _ _)) (pow_nonneg hα.1.le _))
  have hsa := hsmall.trans (mul_le_mul_of_nonneg_right
    ((min_le_right _ _).trans (min_le_right _ _)) (pow_nonneg hα.1.le _))
  obtain ⟨_, Hphase, _, Hphasecone⟩ := HP' η α b U W hηlo (hηhi.trans (min_le_left _ _)) hα hb hsp hsum hU hW
  obtain ⟨HV, Hstate, HoutU, HoutW, _, Hlogs⟩ := HL' η α b U W hηlo (hηhi.trans (min_le_right _ _))
    hα hb hsl hsum hU hW
  obtain ⟨Hv, Hsu, Hsv, Hsw, Hvscale, HUdec, HWdec⟩ := HA η α b U W hηlo (hηhi.trans hδhi) hα hb hsa hsum hU hW
  let z := terminalEntranceInput h Y
  have hzv : 0 < z 2 := Hv.1
  let β := ((J : ℝ) - 2) / 2
  let P := α ^ (((J : ℝ) - 5) / 2) * W ^ (3 / 4 : ℝ) + α ^ ((J : ℝ) / 2 - 19 / 12) * W ^ (7 / 24 : ℝ)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have Hpow := terminal_strong_cone_power (β := β) hα.1 ⟨Hv.1, Hv.2.le⟩ hW hA Hvscale
  rw [show β - 3 / 2 = ((J : ℝ) - 5) / 2 by dsimp only [β]; ring,
    show β - 7 / 12 = (J : ℝ) / 2 - 19 / 12 by dsimp only [β]; ring] at Hpow
  have Hweak := terminal_weak_cone_power hα ⟨Hv.1, Hv.2.le⟩ hU hW hA Hsw Hsv
  have Hroot : Real.sqrt (terminalConnectionState h Y 1) ≤ α ^ β * (z 2) ^ (19 / 24 : ℝ) :=
    HUdec.trans (mul_le_mul_of_nonneg_right Hsu (Real.rpow_nonneg Hv.1.le _))
  have hlog : -Real.log (z 2) = |Real.log (z 2)| := (abs_of_nonpos (Real.log_nonpos Hv.1.le Hv.2.le)).symm
  refine ⟨HV, Hstate, Hphase, HoutU, HoutW, ?_⟩
  intro d hd0 hd1 hd2 p
  obtain ⟨_, Hpneg, Hp⟩ := Hphasecone d hd0 hd1 hd2
  obtain ⟨HLu, HLw⟩ := Hlogs d hd0 hd1 hd2
  let l := fderiv ℝ (terminalConnectionLogWalls h) Y d
  change |l 0| ≤ B * ((1 + -Real.log (z 2)) / α ^ 2 + 1 / (α * Real.sqrt W)) at HLu
  change |l 1| ≤ B * (-Real.log (z 2) + 1 / α + 1 / Real.sqrt W + 1 / Real.sqrt U) at HLw
  rw [hlog] at HLu HLw
  have HUscaled : α ^ 2 * Real.sqrt (terminalConnectionState h Y 1) * |l 0| ≤ 24 * A * B * P := calc
    _ ≤ α ^ 2 * (α ^ β * (z 2) ^ (19 / 24 : ℝ)) *
        (B * ((1 + |Real.log (z 2)|) / α ^ 2 + 1 / (α * Real.sqrt W))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left Hroot (sq_nonneg α)) HLu (abs_nonneg _) (by positivity)
    _ = B * (α ^ β * ((z 2) ^ (19 / 24 : ℝ) * (1 + |Real.log (z 2)|) +
        α * (z 2) ^ (19 / 24 : ℝ) / Real.sqrt W)) := by field_simp [hα.1.ne']
    _ ≤ B * (24 * A * P) := mul_le_mul_of_nonneg_left Hpow hB0
    _ = _ := by ring
  have HWscaled : α ^ 2 * Real.sqrt (terminalConnectionState h Y 3) * |l 1| ≤
      4 * A ^ 2 * B * (Real.sqrt U + Real.sqrt W) := calc
    _ ≤ α ^ 2 * (Real.sqrt (z 3) * Real.sqrt (z 2)) *
        (B * (|Real.log (z 2)| + 1 / α + 1 / Real.sqrt W + 1 / Real.sqrt U)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left HWdec (sq_nonneg α)) HLw (abs_nonneg _) (by positivity)
    _ = B * (α ^ 2 * Real.sqrt (z 3) * Real.sqrt (z 2) *
        (|Real.log (z 2)| + 1 / α + 1 / Real.sqrt W + 1 / Real.sqrt U)) := by ring
    _ ≤ B * (4 * A ^ 2 * (Real.sqrt U + Real.sqrt W)) := mul_le_mul_of_nonneg_left Hweak hB0
    _ = _ := by ring
  have HD := terminalConnectionLogWalls_fderiv (Hstate.differentiableAt (by norm_num)) HoutU.ne' HoutW.ne' d
  have Hdu : l 0 = fderiv ℝ (terminalConnectionState h) Y d 1 / terminalConnectionState h Y 1 := congrFun HD 0
  have Hdw : l 1 = fderiv ℝ (terminalConnectionState h) Y d 3 / terminalConnectionState h Y 3 := congrFun HD 1
  rw [Hdu] at HUscaled
  rw [Hdw] at HWscaled
  have HUratio := sqrt_wall_ratio_of_scaled_log HoutU hα.1 (by positivity : 0 ≤ 24 * A * B * P) Hp HUscaled
  have HWratio := sqrt_wall_ratio_of_scaled_log HoutW hα.1
    (by positivity : 0 ≤ 4 * A ^ 2 * B * (Real.sqrt U + Real.sqrt W)) Hp HWscaled
  refine ⟨Hpneg, Hp, HUratio.trans ?_, HWratio.trans ?_⟩
  · dsimp only [C]
    nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAA hB0) hP]
  · dsimp only [C]
    nlinarith only [mul_nonneg (mul_nonneg (sq_nonneg A) hB0) (add_nonneg (Real.sqrt_nonneg U) (Real.sqrt_nonneg W))]

/-- Formula (D.38): the actual terminal connection reverses phase and strictly contracts
every square-root cone direction, uniformly over the positive wall ratio. -/
theorem exists_terminal_connection_cone :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η₀ : ℝ, (0 < η₀ ∧ η₀ ≤ δ) →
      ∀ J : ℕ, 5 ≤ J → ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b U W : ℝ,
      η₀ ≤ η → η ≤ δ → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |U| + |W| ≤ b → 0 < U → 0 < W →
      let Y : ExitTailState := ![2 + 2 * α, U, W]
      let h := η * α ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalConnectionState h) Y ∧
        ContDiffAt ℝ 2 (terminalConnectionPhase h) Y ∧
        0 < terminalConnectionState h Y 1 ∧ 0 < terminalConnectionState h Y 3 ∧
        C * b ^ (7 / 24 : ℝ) < 1 / 2 ∧
        ∀ d : ExitTailState, d 0 = 1 → |d 1| ≤ Real.sqrt U → |d 2| ≤ Real.sqrt W →
          let p := fderiv ℝ (terminalConnectionPhase h) Y d
          p < 0 ∧ 3 / (4 * α ^ 2) ≤ |p| ∧
          max (|fderiv ℝ (terminalConnectionState h) Y d 1| / (Real.sqrt (terminalConnectionState h Y 1) * |p|))
            (|fderiv ℝ (terminalConnectionState h) Y d 3| / (Real.sqrt (terminalConnectionState h Y 3) * |p|)) ≤
              C * b ^ (7 / 24 : ℝ) := by
  obtain ⟨δ, hδ, hδhi, HE⟩ := exists_terminal_connection_cone_scales
  refine ⟨δ, hδ, hδhi, ?_⟩
  intro η₀ hη₀ J hJ
  obtain ⟨A, hA, ε₀, hε₀, HA⟩ := HE η₀ hη₀ J (by omega)
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  let C := 2 * A
  have hC : 1 ≤ C := by dsimp only [C]; linarith only [hA]
  obtain ⟨ε, hε, hεmax, Hbudget⟩ := exists_common_rpow_budget (ι := Fin 1) Finset.univ
    (C := fun _ => C) (p := fun _ => 7 / 24) (ε := fun _ => 1 / 2)
    (by intros; dsimp only [C]; positivity) (by intros; norm_num) (by intros; norm_num)
    (lt_min hε₀ (by norm_num : (0 : ℝ) < 1))
  refine ⟨C, hC, ε, hε, ?_⟩
  intro η α b U W hηlo hηhi hα hb hsmall hsum hU hW Y h
  have hbε : b ≤ ε := hsmall.trans (mul_le_of_le_one_right hε.le (pow_le_one₀ hα.1.le hα.2))
  have hb1 : b ≤ 1 := hbε.trans (hεmax.le.trans (min_le_right _ _))
  have hs := hsmall.trans (mul_le_mul_of_nonneg_right (hεmax.le.trans (min_le_left _ _)) (pow_nonneg hα.1.le _))
  obtain ⟨HV, Hstate, Hphase, HU, HW, Hcone⟩ := HA η α b U W hηlo hηhi hα hb hs hsum hU hW
  have Hpowers := terminal_cone_power_budget hJ hα ⟨hb, hb1⟩ hU.le hW
    (by simpa only [abs_of_pos hU, abs_of_pos hW] using hsum)
  refine ⟨HV, Hstate, Hphase, HU, HW, Hbudget b ⟨hb, hbε⟩ 0 (Finset.mem_univ _), ?_⟩
  intro d hd0 hd1 hd2 p
  obtain ⟨Hneg, Hp, Hstrong, Hweak⟩ := Hcone d hd0 hd1 hd2
  refine ⟨Hneg, Hp, max_le ?_ ?_⟩
  · exact (Hstrong.trans (mul_le_mul_of_nonneg_left Hpowers.1 hA0)).trans_eq (by dsimp only [C]; ring)
  · exact (Hweak.trans (mul_le_mul_of_nonneg_left Hpowers.2 hA0)).trans_eq (by dsimp only [C]; ring)

end BianchiIX
