import BianchiIX.Dynamics.ExitActualCycleEndpoint
import BianchiIX.Algebra.ExitCyclePowers

noncomputable section

namespace BianchiIX

open Set

/-- One choice of constants puts every cyclic endpoint in the prescribed power-small entrance domain. -/
theorem exists_terminal_cycle_entrance_inputs {εin η : ℝ} (hεin : 0 < εin)
    (hη : 0 < η ∧ η ≤ 1 / 100) {q J : ℕ} (hJ : q + 2 ≤ J)
    (hηin : η ≤ εin / (4 * (11 / 5) ^ q)) :
    ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ (2 * J) →
      |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let z := projectiveCycle (coreTailState h Y)
      let k := coreRadius (z 0) (z 2)
      let γ := normalizedMaxCurve (axisCycle (fromProjectiveState (coreTailEntry Y))) 0
      coreTailValid h Y ∧ toProjectiveState (γ (coreTailTime h Y)) = z ∧
        7 / 4 < k ∧ 2 < z 0 ∧
        (0 < z 1 ∧ z 1 ≤ εin ∧ z 1 * k ^ q ≤ εin / 2) ∧
        (0 < z 2 ∧ z 2 < 1 / 2) ∧
        (0 < z 3 ∧ z 3 ≤ εin ∧ z 3 * k ^ q ≤ εin / 2) ∧
        (∀ t ∈ Icc 0 (coreTailTime h Y), 0 < 1 + γ t 0 ∧ |toProjectiveState (γ t) 2| ≤ 1 / 5000) ∧
        0 < projectiveCycleDenom (coreTailState h Y) := by
  obtain ⟨C, hC, ε₀, hε₀, HE⟩ := exists_terminal_axisCycle_endpoint hη (by omega : 2 ≤ J)
  have hC0 : 0 < C := lt_of_lt_of_le (by norm_num) hC
  let δ := εin / (4 * (11 / 5 : ℝ) ^ q)
  have hδ : 0 < δ := div_pos hεin (by positivity)
  let ε := min ε₀ (δ / C)
  have hε : 0 < ε := lt_min hε₀ (div_pos hδ hC0)
  refine ⟨ε, hε, ?_⟩
  intro α b u w hα hb hsmall hsum hu hw Y h z k γ
  have hα0 : 0 < α := hα.1
  have hsmall₀ := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left ε₀ (δ / C)) (pow_nonneg hα.1.le (2 * J)))
  obtain ⟨HV, HEq, HH, HM, HK, HU, HW, HP, HF⟩ := HE α b u w hα hb hsmall₀ hsum
  have hbudget : C * b ≤ δ * α ^ (2 * J) := by
    have Hε := (le_div_iff₀ hC0).mp (min_le_right ε₀ (δ / C))
    nlinarith only [mul_le_mul_of_nonneg_left hsmall hC0.le,
      mul_le_mul_of_nonneg_right Hε (pow_nonneg hα.1.le (2 * J))]
  have hlow : (19 / 10 : ℝ) ≤ 19 / (10 * α) := by
    apply (le_div_iff₀ (by positivity : 0 < 10 * α)).mpr
    linarith only [hα.2]
  have hk : 7 / 4 < k := by dsimp only [k, z]; linarith only [HK.1, hlow]
  have hm : 2 < z 0 := by dsimp only [z]; linarith only [HM.1, hlow]
  have hk0 : 0 ≤ k := by linarith only [hk]
  have hkc : k ≤ (11 / 5) / α := HK.2.le.trans_eq (by ring)
  have hU : 0 < z 1 := lt_of_lt_of_le (mul_pos (div_pos hη.1 (by norm_num)) (pow_pos hα.1 (J - 2))) HU.1
  have hpos : 0 < z 2 ∧ 0 < z 3 := HP ⟨hu, hw⟩
  have hPu := (exitCycle_entrance_power hα hk0 hkc hη.1.le hηin HU.2 hJ).2
  have hWpower : z 3 ≤ 2 * δ * α ^ (2 * J - 2) :=
    (le_abs_self _).trans (HW.2.trans (exitCycle_scaled_wall_power hα.1 (by omega) hbudget))
  have hPw := (exitCycle_entrance_power hα hk0 hkc hδ.le le_rfl hWpower (by omega : q + 2 ≤ 2 * J)).2
  have hkp : 1 ≤ k ^ q := one_le_pow₀ (by linarith only [hk] : 1 ≤ k)
  have hsmallwall {a : ℝ} (ha : 0 < a) (hP : a * k ^ q ≤ εin / 2) : a ≤ εin := by
    nlinarith only [mul_le_mul_of_nonneg_left hkp ha.le, hP, hεin]
  have ht : coreTailTime h Y ∈ Icc 0 (coreTailTime h Y) := ⟨HV.1.1.1.le, le_rfl⟩
  have hvbound := (HF _ ht).2
  rw [HEq] at hvbound
  exact ⟨HV, HEq, hk, hm, ⟨hU, hsmallwall hU hPu, hPu⟩,
    ⟨hpos.1, by linarith only [le_abs_self (z 2), hvbound]⟩,
    ⟨hpos.2, hsmallwall hpos.2 hPw, hPw⟩, HF, lt_trans (by positivity) HH.1⟩

end BianchiIX
