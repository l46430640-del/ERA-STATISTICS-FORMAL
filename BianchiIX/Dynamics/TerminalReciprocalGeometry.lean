import BianchiIX.Dynamics.TerminalEntranceDerivativeBounds

noncomputable section

namespace BianchiIX

theorem exists_terminal_entrance_radius_lower {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 1000)
    {J : ℕ} (hJ : 2 ≤ J) :
    ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 1000 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧ 3 / (2 * α) ≤ terminalEntranceInput h Y 0 := by
  obtain ⟨K, hK, ε, hε, HE⟩ := exists_terminal_axisCycle_endpoint_uniform
    ⟨hη₀.1, hη₀.2.trans (by norm_num)⟩ hJ
  refine ⟨ε, hε, ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum Y h
  have hα0 := hα.1
  have hη0 : 0 < η := hη₀.1.trans_le hηlo
  obtain ⟨HV, _, _, HM, _, HU, HW, _, _, HB⟩ :=
    HE η α b u w hηlo (hηhi.trans (by norm_num)) hα hb hsmall hsum
  let z := terminalCyclicInput h Y
  change 19 / (10 * α) < z 0 - 1 ∧ z 0 - 1 < 21 / (10 * α) at HM
  change η / 2 * α ^ (J - 2) ≤ z 1 ∧ z 1 ≤ 2 * η * α ^ (J - 2) at HU
  change |z 2| ≤ 2 * (K * b) / α ^ 2 ∧ |z 3| ≤ 2 * (K * b) / α ^ 2 at HW
  have Hlow : 19 / 10 ≤ 19 / (10 * α) := by
    apply (le_div_iff₀ (by positivity : 0 < 10 * α)).mpr
    linarith only [hα.2]
  have hm : 2 ≤ z 0 := by linarith only [HM.1, Hlow]
  have hu : |z 1| ≤ 1 / 400 := by
    have hU0 : 0 ≤ z 1 := (by positivity : 0 ≤ η / 2 * α ^ (J - 2)).trans HU.1
    rw [abs_of_nonneg hU0]
    have Hpow := mul_le_mul_of_nonneg_left (pow_le_one₀ hα.1.le hα.2 (n := J - 2)) (by positivity : 0 ≤ 2 * η)
    nlinarith only [HU.2, Hpow, hηhi]
  have hw : |z 3| ≤ 1 / 400 := by
    have HB' : K * b ≤ α ^ 2 / 10000 := HB.trans (div_le_div_of_nonneg_right
      (pow_le_pow_of_le_one hα.1.le hα.2 (by omega : 2 ≤ 2 * J)) (by norm_num))
    apply HW.2.trans ((div_le_iff₀ (sq_pos_of_pos hα.1)).mpr ?_)
    nlinarith only [HB', sq_nonneg α]
  have HP := entranceStablePhase_signed_lower hm hu hw
  have HR : entranceStablePhase z - 1 ≤ entranceStableRadius z := phaseNorm_ge (sub_pos.mpr HP.2).le
  refine ⟨HV, ?_⟩
  change 3 / (2 * α) ≤ entranceStableRadius z
  have Hphase := (div_lt_iff₀ (by positivity : 0 < 10 * α)).mp HM.1
  apply (div_le_iff₀ (by positivity : 0 < 2 * α)).mpr
  have HPmul := mul_le_mul_of_nonneg_right (abs_le.mp HP.1).1 hα.1.le
  have HRmul := mul_le_mul_of_nonneg_right HR hα.1.le
  nlinarith only [Hphase, HPmul, HRmul, hα.2]

end BianchiIX
