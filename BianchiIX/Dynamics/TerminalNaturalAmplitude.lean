import BianchiIX.Dynamics.TerminalNaturalCone
import BianchiIX.Dynamics.EntranceReturnRefinedDecay
import BianchiIX.Analysis.TerminalAmplitudePowers

noncomputable section

namespace BianchiIX

/-- The actual natural-height terminal output has superlinear amplitude contraction, uniformly in the wall ratio. -/
theorem exists_terminalNatural_amplitude_bound {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 40000)
    {J : ℕ} (hJ : 20 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 ∧ ∀ α b U W : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ (2 * J) →
      |U| + |W| ≤ b → 0 < U → 0 < W →
      let Y : ExitTailState := ![2 + 2 * α, U, W]
      0 < terminalNaturalState η J Y 1 ∧ 0 < terminalNaturalState η J Y 3 ∧
        terminalNaturalState η J Y 1 + terminalNaturalState η J Y 3 ≤ C * b ^ (19 / 10 : ℝ) := by
  have hη100 : 0 < η ∧ η ≤ 1 / 100 := ⟨hη.1, by linarith [hη.2]⟩
  obtain ⟨A, hA, εm, hεm, HM⟩ := exists_terminalWallFactor_bounds_uniform hη100 (by omega : 2 ≤ J)
  obtain ⟨εi, hεi, HI⟩ := exists_terminal_cycle_entrance_inputs_uniform
    (εin := 1 / 10000) (q := 0) (by norm_num) hη100 (by omega : 0 + 2 ≤ J)
  obtain ⟨_, _, εg, hεg, HG⟩ := exists_terminal_axisCycle_endpoint_uniform hη100 (by omega : 2 ≤ J)
  let ε := min 1 (min εm (min εi εg))
  let C := (Real.exp (1 / 1000) + 1) * A ^ 2
  have hε : 0 < ε := lt_min (by norm_num) (lt_min hεm (lt_min hεi hεg))
  have hA0 : 0 ≤ A := by linarith
  have hC : 1 ≤ C := by
    have hA2 : 1 ≤ A ^ 2 := one_le_pow₀ hA
    dsimp [C]
    nlinarith only [hA2, mul_nonneg (Real.exp_pos (1 / 1000)).le (sq_nonneg A)]
  refine ⟨C, hC, ε, hε, min_le_left _ _, ?_⟩
  intro α b U W hα hb hsmall hsum hU hW Y
  have hα0 := hα.1
  let h := η * α ^ J
  let z := terminalEntranceInput h Y
  let y := terminalCyclicInput h Y
  have hs {e : ℝ} (he : ε ≤ e) : b ≤ e * α ^ (2 * J) :=
    hsmall.trans (mul_le_mul_of_nonneg_right he (pow_nonneg hα.1.le _))
  obtain ⟨_, Hvfac, Hwfac, Hu, _, Hfactor⟩ := HM η α b U W le_rfl hη100.2 hα hb
    (hs ((min_le_right _ _).trans (min_le_left _ _))) hsum
  obtain ⟨_, _, _, Hm, HU, HV, HW, _, _⟩ := HI η α b U W le_rfl hη100.2
    (by norm_num; exact hη.2) hα hb
    (hs ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))) hsum hU hW
  have HK := (HG η α b U W le_rfl hη100.2 hα hb
    (hs ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))) hsum).2.2.2.2.1
  change 19 / (10 * α) < coreRadius (y 0) (y 2) ∧ _ at HK
  have hlow : 19 / 10 ≤ 19 / (10 * α) := (le_div_iff₀ (by positivity)).mpr (by linarith [hα.2])
  have hk : 19 / 10 ≤ coreRadius (y 0) (y 2) := hlow.trans HK.1.le
  change 2 < y 0 at Hm
  change 0 < y 1 ∧ y 1 ≤ 1 / 10000 ∧ _ at HU
  change 0 < y 2 ∧ y 2 < 1 / 2 at HV
  change 0 < y 3 ∧ y 3 ≤ 1 / 10000 ∧ _ at HW
  have hm : 1 ≤ y 0 := by linarith
  have hv : 0 < y 2 ∧ y 2 < 1 := ⟨HV.1, by linarith [HV.2]⟩
  have Hdec := entranceReturn_power_decay hk hm ⟨HU.1.le, HU.2.1⟩ hv ⟨HW.1.le, HW.2.1⟩
  have hk' : 7 / 4 ≤ coreRadius (y 0) (y 2) := by linarith
  have Hvalid := (entranceReturn_regular hk' hm ⟨HU.1.le, HU.2.1⟩ hv ⟨HW.1.le, HW.2.1⟩).1
  have Hpos := entranceReturn_walls_pos hk' hm ⟨HU.1, HU.2.1⟩ hv ⟨HW.1, HW.2.1⟩
    (entranceReturnTime y) ⟨Hvalid.1.1.1.le, le_rfl⟩
  change z 2 = W * terminalWallFactor h Y 1 at Hvfac
  change z 3 = U * terminalWallFactor h Y 0 at Hwfac
  have hvscale : y 2 ≤ A * W / α ^ 2 := by
    change z 2 ≤ _
    rw [Hvfac]
    exact (mul_le_mul_of_nonneg_left (Hfactor 1).2.2.2.1 hW.le).trans_eq (by ring)
  have hwscale : y 3 ≤ A * U / α ^ 2 := by
    change z 3 ≤ _
    rw [Hwfac]
    exact (mul_le_mul_of_nonneg_left (Hfactor 0).2.2.2.1 hU.le).trans_eq (by ring)
  have huscale : y 1 ≤ α ^ (4 : ℕ) := by
    exact (Hu.2.trans (mul_le_of_le_one_left (pow_nonneg hα.1.le _)
      (by linarith [hη.2] : 2 * η ≤ 1))).trans
      (pow_le_pow_of_le_one hα.1.le hα.2 (by omega : 4 ≤ J - 2))
  have hbα : b ≤ α ^ (40 : ℕ) :=
    (hsmall.trans (mul_le_of_le_one_left (pow_nonneg hα.1.le _) (min_le_left _ _))).trans
      (pow_le_pow_of_le_one hα.1.le hα.2 (by omega : 40 ≤ 2 * J))
  have Hp := terminal_amplitude_power_budget hα hb hbα hA hU.le hW.le
    (by simpa only [abs_of_pos hU, abs_of_pos hW] using hsum)
    ⟨HU.1.le, huscale⟩ ⟨hv.1.le, hvscale⟩ ⟨HW.1.le, hwscale⟩
  have hstate : terminalNaturalState η J Y = entranceReturnState y := by
    change terminalConnectionState (η * ((Y 0 - 2) / 2) ^ J) Y = _
    rw [show (Y 0 - 2) / 2 = α by change (2 + 2 * α - 2) / 2 = α; ring]
    rfl
  rw [hstate]
  refine ⟨Hpos.1, Hpos.2.2, ?_⟩
  calc
    _ ≤ Real.exp (1 / 1000) * (A ^ 2 * b ^ (19 / 10 : ℝ)) + A ^ 2 * b ^ (19 / 10 : ℝ) :=
      add_le_add (Hdec.1.trans (mul_le_mul_of_nonneg_left Hp.1 (Real.exp_pos _).le)) (Hdec.2.trans Hp.2)
    _ = _ := by dsimp [C]; ring

end BianchiIX
