import BianchiIX.Dynamics.TerminalStableComparison
import BianchiIX.Dynamics.TerminalCoreWalls
import BianchiIX.Dynamics.EntrancePhysicalValue

noncomputable section

namespace BianchiIX

open Set

theorem exists_entrance_value_active_bound :
    ∃ C > (0 : ℝ), ∀ y : ProjectiveState,
      7 / 4 ≤ coreRadius (y 0) (y 2) → 1 ≤ y 0 →
      (0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) → (0 < y 2 ∧ y 2 < 1) →
      (0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) →
      |coreRadius (entranceReturnState y 0) (entranceReturnState y 2) - entranceStableRadius y| ≤ C * y 2 := by
  obtain ⟨C, hC, HC⟩ := exists_entrance_physical_basic_value
  refine ⟨2 * C, by positivity, ?_⟩
  intro y hk hm hu hv hw
  have hsum : 0 ≤ y 1 + y 3 ∧ y 1 + y 3 ≤ 1 := ⟨add_nonneg hu.1 hw.1, by linarith only [hu.2, hw.2]⟩
  have hsq : (y 1 + y 3) ^ 2 ≤ 1 := by nlinarith only [hsum.1, hsum.2]
  have hv2 : (y 2) ^ 2 ≤ y 2 := by nlinarith only [hv.1, hv.2]
  have Hnum : y 1 * y 2 + (y 2) ^ 2 * (y 1 + y 3) ^ 2 ≤ 2 * y 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right (show y 1 ≤ 1 by linarith only [hu.2]) hv.1.le,
      mul_le_mul_of_nonneg_left hsq (sq_nonneg (y 2)), hv2]
  apply (HC y hk hm hu hv hw).trans
  apply (div_le_iff₀ (by linarith only [hk] : 0 < coreRadius (y 0) (y 2))).mpr
  have Hk := mul_le_mul_of_nonneg_left (show 1 ≤ coreRadius (y 0) (y 2) by linarith only [hk])
    (show 0 ≤ 2 * C * y 2 from mul_nonneg (mul_nonneg (by norm_num) hC.le) hv.1.le)
  nlinarith only [mul_le_mul_of_nonneg_left Hnum hC.le, Hk]

/-- The phase estimate is evaluated at the canonical arrival of the actual positive-wall orbit. -/
theorem exists_terminal_connection_radius_error {εin η : ℝ} (hεin : 0 < εin ∧ εin ≤ 1 / 10000)
    (hη : 0 < η ∧ η ≤ 1 / 100) {q J : ℕ} (hJ : q + 2 ≤ J)
    (hηin : η ≤ εin / (4 * (11 / 5) ^ q)) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ (2 * J) →
      |u| + |w| ≤ b → 0 < u → 0 < w →
      let Z := terminalConnectionState (η * α ^ J) ![2 + 2 * α, u, w]
      |coreRadius (Z 0) (Z 2) - 2 / α| ≤ C * b / α ^ 2 := by
  have hηsmall : η ≤ 1 / 1000 := by
    have Hp : 1 ≤ (11 / 5 : ℝ) ^ q := one_le_pow₀ (by norm_num)
    have He := (le_div_iff₀ (by positivity : 0 < 4 * (11 / 5 : ℝ) ^ q)).mp hηin
    nlinarith only [He, hεin.2, mul_le_mul_of_nonneg_left Hp hη.1.le]
  obtain ⟨S, hS, εs, hεs, HS⟩ := exists_terminal_stable_radius_comparison ⟨hη.1, hηsmall⟩ (by omega : 2 ≤ J)
  obtain ⟨A, hA, εa, hεa, HA⟩ := exists_terminal_axisCycle_endpoint hη (by omega : 2 ≤ J)
  obtain ⟨εi, hεi, HI⟩ := exists_terminal_cycle_entrance_inputs hεin.1 hη hJ hηin
  obtain ⟨D, hD, HD⟩ := exists_entrance_value_active_bound
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  refine ⟨S + 2 * D * A, by nlinarith only [hS, mul_pos hD hA0],
    min εs (min εa εi), lt_min hεs (lt_min hεa hεi), ?_⟩
  intro α b u w hα hb hsmall hsum hu hw Z
  have hs := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left εs (min εa εi)) (pow_nonneg hα.1.le (2 * J)))
  have ha := hsmall.trans (mul_le_mul_of_nonneg_right
    ((min_le_right εs (min εa εi)).trans (min_le_left εa εi)) (pow_nonneg hα.1.le (2 * J)))
  have hi := hsmall.trans (mul_le_mul_of_nonneg_right
    ((min_le_right εs (min εa εi)).trans (min_le_right εa εi)) (pow_nonneg hα.1.le (2 * J)))
  have Hr := (HS α b u w hα hb hs hsum).2
  obtain ⟨_, _, _, _, _, _, HW, _, _⟩ := HA α b u w hα hb ha hsum
  obtain ⟨_, _, HK, HM, HU, HV, HW', _, _⟩ := HI α b u w hα hb hi hsum hu hw
  let z := projectiveCycle (coreTailState (η * α ^ J) ![2 + 2 * α, u, w])
  have He := HD z HK.le (by linarith only [HM]) ⟨HU.1.le, HU.2.1.trans hεin.2⟩
    ⟨HV.1, by linarith only [HV.2]⟩ ⟨HW'.1.le, HW'.2.1.trans hεin.2⟩
  have Hv : z 2 ≤ 2 * (A * b) / α ^ 2 := (le_abs_self _).trans HW.1
  change |coreRadius (Z 0) (Z 2) - entranceStableRadius z| ≤ D * z 2 at He
  have HE := abs_sub_le (coreRadius (Z 0) (Z 2)) (entranceStableRadius z) (2 / α)
  have Hscale := mul_le_mul_of_nonneg_left Hv hD.le
  change |entranceStableRadius z - 2 / α| ≤ S * b / α ^ 2 at Hr
  calc
    _ ≤ D * (2 * (A * b) / α ^ 2) + S * b / α ^ 2 := by linarith only [HE, He, Hr, Hscale]
    _ = _ := by ring

/-- Full D.14, including the original-flow first arrival and the next-era branch criterion. -/
theorem exists_terminal_connection_phase_and_walls {εin η : ℝ} (hεin : 0 < εin ∧ εin ≤ 1 / 10000)
    (hη : 0 < η ∧ η ≤ 1 / 100) {q J : ℕ} (hq : 16 ≤ q) (hJ : q + 2 ≤ J)
    (hηin : η ≤ εin / (4 * (11 / 5) ^ q)) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ (2 * J) →
      |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let x := axisCycle (fromProjectiveState (coreTailEntry Y))
      let T := terminalConnectionTime h Y
      let Z := terminalConnectionState h Y
      let κ := coreRadius (Z 0) (Z 2)
      IsLeast {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧
        projectiveActiveWall (normalizedMaxCurve x 0 t) = 1} T ∧
        toProjectiveState (normalizedMaxCurve x 0 T) = Z ∧ Z 2 = 1 ∧
        0 < κ ∧ |κ - 2 / α| ≤ C * b / α ^ 2 ∧ |2 / κ - α| ≤ C * b ∧
        (0 < Z 1 ∧ Z 1 ≤ εin / κ ^ 16) ∧ (0 < Z 3 ∧ Z 3 ≤ εin / κ ^ 16) ∧
        (C * b < 1 - α → 2 / κ < 1 ∧ 2 < κ) := by
  obtain ⟨C, hC, εr, hεr, HR⟩ := exists_terminal_connection_radius_error hεin hη hJ hηin
  obtain ⟨εw, hεw, HW⟩ := exists_terminal_connection_core_walls hεin hη hq hJ hηin
  have hC0 : 0 < C := lt_of_lt_of_le (by norm_num) hC
  let ε := min εr (min εw (1 / C))
  have hε : 0 < ε := lt_min hεr (lt_min hεw (by positivity))
  have hεC : ε * C ≤ 1 := (le_div_iff₀ hC0).mp
    ((min_le_right εr (min εw (1 / C))).trans (min_le_right εw (1 / C)))
  refine ⟨C, hC, ε, hε, ?_⟩
  intro α b u w hα hb hsmall hsum hu hw Y h x T Z κ
  have hr := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left εr (min εw (1 / C)))
    (pow_nonneg hα.1.le (2 * J)))
  have hw' := hsmall.trans (mul_le_mul_of_nonneg_right
    ((min_le_right εr (min εw (1 / C))).trans (min_le_left εw (1 / C))) (pow_nonneg hα.1.le (2 * J)))
  have HE : |κ - 2 / α| ≤ C * b / α ^ 2 := HR α b u w hα hb hr hsum hu hw
  obtain ⟨HF, Hstate, Hactive, HU, HW'⟩ := HW α b u w hα hb hw' hsum hu hw
  have hbudget : C * b ≤ α := by
    have Hp : α ^ (2 * J) ≤ α := (pow_le_pow_of_le_one hα.1.le hα.2 (by omega : 1 ≤ 2 * J)).trans_eq (pow_one α)
    nlinarith only [mul_le_mul_of_nonneg_left hsmall hC0.le,
      mul_le_mul_of_nonneg_right hεC (pow_nonneg hα.1.le (2 * J)), Hp]
  have HP := terminal_phase_reciprocal hα.1 hbudget HE
  exact ⟨HF, Hstate, Hactive, lt_of_lt_of_le (one_div_pos.mpr hα.1) HP.1, HE, HP.2.1, HU, HW', HP.2.2⟩

end BianchiIX
