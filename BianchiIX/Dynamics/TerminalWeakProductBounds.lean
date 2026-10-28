import BianchiIX.Dynamics.EntranceWeakProductBounds
import BianchiIX.Dynamics.TerminalHeightInterval
import BianchiIX.Dynamics.TerminalWallFactors

noncomputable section

namespace BianchiIX

def terminalWeakProductExponent (h : ℝ) (Y : ExitTailState) : ℝ :=
  entranceWeakProductExponent (terminalCyclicInput h Y)

theorem exists_terminal_weak_product_bound {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 40000)
    {J : ℕ} (hJ : 2 ≤ J) :
    ∃ ε > (0 : ℝ), ∀ η α b U W : ℝ,
      η₀ ≤ η → η ≤ 1 / 40000 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |U| + |W| ≤ b → 0 < U → 0 < W →
      let Y : ExitTailState := ![2 + 2 * α, U, W]
      let h := η * α ^ J
      let v := terminalCyclicInput h Y 2
      coreTailValid h Y ∧ (0 < v ∧ v < 1) ∧
        terminalConnectionState h Y 3 =
          U * W * (terminalWallFactor h Y 0 * terminalWallFactor h Y 1) *
            Real.exp (terminalWeakProductExponent h Y) ∧
        |terminalWeakProductExponent h Y| ≤ 8 * α * (-Real.log v) := by
  have hη₀' : 0 < η₀ ∧ η₀ ≤ 1 / 100 := ⟨hη₀.1, by linarith only [hη₀.2]⟩
  obtain ⟨εi, hεi, HI⟩ := exists_terminal_cycle_entrance_inputs_uniform
    (εin := 1 / 10000) (by norm_num) hη₀' (q := 0) hJ
  obtain ⟨C, hC, εg, hεg, HG⟩ := exists_terminal_axisCycle_endpoint_uniform hη₀' hJ
  refine ⟨min εi εg, lt_min hεi hεg, ?_⟩
  intro η α b U W hηlo hηhi hα hb hsmall hsum hU hW Y h v
  have hη100 : η ≤ 1 / 100 := by linarith only [hηhi]
  have hsi := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left εi εg) (pow_nonneg hα.1.le _))
  have hsg := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_right εi εg) (pow_nonneg hα.1.le _))
  obtain ⟨HV, _, HK, Hm, HU, HVa, HW, _, _⟩ := HI η α b U W hηlo hη100
    (by norm_num; exact hηhi) hα hb hsi hsum hU hW
  have Hrad := (HG η α b U W hηlo hη100 hα hb hsg hsum).2.2.2.2.1.1
  let y := terminalCyclicInput h Y
  change 7 / 4 < coreRadius (y 0) (y 2) at HK
  change 2 < y 0 at Hm
  change 0 < y 2 ∧ y 2 < 1 / 2 at HVa
  change 19 / (10 * α) < coreRadius (y 0) (y 2) at Hrad
  have hka : 1 / α ≤ coreRadius (y 0) (y 2) := le_trans (by
    apply (div_le_div_iff₀ hα.1 (mul_pos (by norm_num) hα.1)).mpr
    linarith only [hα.1]) Hrad.le
  have hv : 0 < y 2 ∧ y 2 < 1 := ⟨HVa.1, by linarith only [HVa.2]⟩
  have HP := entranceReturn_weak_product_bound (y := y) HK.le (by linarith only [Hm] : 1 ≤ y 0)
    ⟨HU.1.le, HU.2.1⟩ hv ⟨HW.1.le, HW.2.1⟩
  have HF := terminalEntranceInput_wall_factors HV
  have hvfac : y 2 = W * terminalWallFactor h Y 1 := HF.2.1
  have hwfac : y 3 = U * terminalWallFactor h Y 0 := HF.2.2
  refine ⟨HV, hv, ?_, ?_⟩
  · change entranceReturnState y 3 = _
    rw [HP.1, hvfac, hwfac]
    change _ = U * W * (terminalWallFactor h Y 0 * terminalWallFactor h Y 1) *
      Real.exp (entranceWeakProductExponent y)
    ring
  · have hk0 : 0 < coreRadius (y 0) (y 2) := by linarith only [HK]
    change |entranceWeakProductExponent y| ≤ 8 * α * (-Real.log (y 2))
    have hlog : 0 ≤ -Real.log (y 2) := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
    apply HP.2.trans
    apply (div_le_iff₀ hk0).mpr
    have Hmul := (div_le_iff₀ hα.1).mp hka
    have HB := mul_le_mul_of_nonneg_left Hmul (show 0 ≤ 8 * (-Real.log (y 2)) by positivity)
    convert! HB using 1 <;> ring

end BianchiIX
