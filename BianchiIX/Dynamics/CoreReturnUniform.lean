import BianchiIX.Dynamics.CoreReturnCanonical
import BianchiIX.Dynamics.CompactCoreFactorBounds

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem coreRadiusReturn_large_walls {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) (i : Fin 2) :
    let F := coreReturnState coreRadiusReturnTime Y
    0 ≤ F i.succ ∧ (0 < F i.succ ↔ 0 < Y i.succ) ∧
      F i.succ ≤ Real.exp (-1 / (2 * Y 0)) * Y i.succ := by
  intro F
  have hfirst := (coreRadiusReturn_large_regular hk hu hw).2.2.2.self_of_nhds
  obtain ⟨T, _, hT, hpos, hU, hW⟩ := exists_large_core_multipliers hk hu hw
  have ht : T = coreRadiusReturnTime Y := hT.unique hfirst
  subst T
  have hformula : F i.succ = Y i.succ * coreReturnMultiplier coreRadiusReturnTime Y i := by
    fin_cases i
    · exact hU
    · change projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreRadiusReturnTime Y) 2 *
        projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreRadiusReturnTime Y) 3 = _
      rw [hfirst.1.2, one_mul]
      exact hW
  have hi : 0 ≤ Y i.succ := by
    fin_cases i
    · exact hu.1
    · exact hw.1
  have hc := coreReturnMultiplier_contraction hk hu hw hfirst
  have hbound : coreReturnMultiplier coreRadiusReturnTime Y i ≤ Real.exp (-1 / (2 * Y 0)) := by
    fin_cases i
    · apply hc.1.trans (Real.exp_le_exp.mpr ?_)
      apply (le_div_iff₀ (by linarith only [hk] : 0 < 2 * Y 0)).mpr
      nlinarith only [sq_nonneg (Y 0 - 6), hk]
    · exact hc.2
  rw [hformula]
  exact ⟨mul_nonneg hi (hpos i).le, mul_pos_iff_of_pos_right (hpos i),
    (mul_le_mul_of_nonneg_left hbound hi).trans_eq (mul_comm _ _)⟩

/-- One actual first-return map and one exponential loss rate apply to every core radius at least two. -/
theorem exists_coreRadiusReturn_uniform_contraction :
    ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ c > (0 : ℝ), c ≤ 1 / 2 ∧
      ∀ Y : CoreAngleState, 2 ≤ Y 0 →
        (0 ≤ Y 1 ∧ Y 1 ≤ ε / Y 0) → (0 ≤ Y 2 ∧ Y 2 ≤ ε / Y 0) →
        coreRadiusReturnValid Y ∧ ContDiffAt ℝ 1 coreRadiusReturnTime Y ∧
          ContDiffAt ℝ 1 (coreReturnState coreRadiusReturnTime) Y ∧
          ∀ i : Fin 2, 0 ≤ coreReturnState coreRadiusReturnTime Y i.succ ∧
            (0 < coreReturnState coreRadiusReturnTime Y i.succ ↔ 0 < Y i.succ) ∧
            coreReturnState coreRadiusReturnTime Y i.succ ≤ Real.exp (-c / Y 0) * Y i.succ := by
  obtain ⟨εf, hεf, q, hq, hq1, C, hC, HF⟩ := exists_compact_core_factor_bounds
  obtain ⟨εt, hεt, Ct, hCt, HT⟩ := exists_compact_core_return_two
  let ε := min (1 / 10000) (min εf εt)
  let c := min (1 / 2) (-2 * Real.log q)
  have hlog : Real.log q < 0 := Real.log_neg hq hq1
  have hε : 0 < ε := lt_min (by norm_num) (lt_min hεf hεt)
  have hc : 0 < c := lt_min (by norm_num) (by linarith only [hlog])
  have hcmax : c ≤ 1 / 2 := min_le_left _ _
  have hcq : c ≤ -2 * Real.log q := min_le_right _ _
  refine ⟨ε, hε, min_le_left _ _, c, hc, hcmax, ?_⟩
  intro Y hk hu hw
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hεk : ε / Y 0 ≤ ε := div_le_self hε.le (by linarith only [hk])
  by_cases hk6 : 6 ≤ Y 0
  · have hu' : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0 :=
      ⟨hu.1, hu.2.trans (div_le_div_of_nonneg_right (min_le_left _ _) hk0.le)⟩
    have hw' : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0 :=
      ⟨hw.1, hw.2.trans (div_le_div_of_nonneg_right (min_le_left _ _) hk0.le)⟩
    obtain ⟨hvalid, ht, hF, _⟩ := coreRadiusReturn_large_regular hk6 hu' hw'
    refine ⟨hvalid, ht, hF, ?_⟩
    intro i
    obtain ⟨hpos, hiff, hdec⟩ := coreRadiusReturn_large_walls hk6 hu' hw' i
    have hi : 0 ≤ Y i.succ := by
      fin_cases i
      · exact hu.1
      · exact hw.1
    refine ⟨hpos, hiff, hdec.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hi)⟩
    rw [show -1 / (2 * Y 0) = -(1 / 2) / Y 0 by ring]
    exact div_le_div_of_nonneg_right (by linarith only [hcmax]) hk0.le
  · have hkr : 2 ≤ Y 0 ∧ Y 0 ≤ 6 := ⟨hk, (lt_of_not_ge hk6).le⟩
    have huf : |Y 1| ≤ εf := by
      rw [abs_of_nonneg hu.1]
      exact (hu.2.trans hεk).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hwf : |Y 2| ≤ εf := by
      rw [abs_of_nonneg hw.1]
      exact (hw.2.trans hεk).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hut : |Y 1| ≤ εt := by
      rw [abs_of_nonneg hu.1]
      exact (hu.2.trans hεk).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hwt : |Y 2| ≤ εt := by
      rw [abs_of_nonneg hw.1]
      exact (hw.2.trans hεk).trans ((min_le_right _ _).trans (min_le_right _ _))
    obtain ⟨hvalid, hF, H⟩ := HF Y hkr huf hwf
    refine ⟨hvalid, (HT Y hkr hut hwt).2.1.of_le (by norm_num), hF.of_le (by norm_num), ?_⟩
    have hqe : q ≤ Real.exp (-c / Y 0) := by
      rw [← Real.exp_log hq]
      apply Real.exp_le_exp.mpr
      apply (le_div_iff₀ hk0).mpr
      nlinarith only [mul_le_mul_of_nonpos_right hk hlog.le, hcq]
    intro i
    have hi : 0 ≤ Y i.succ := by
      fin_cases i
      · exact hu.1
      · exact hw.1
    obtain ⟨hformula, hpos, hbound, _⟩ := H i
    rw [hformula]
    exact ⟨mul_nonneg hi hpos.le, mul_pos_iff_of_pos_right hpos,
      (mul_le_mul_of_nonneg_left (hbound.trans hqe) hi).trans_eq (mul_comm _ _)⟩

end BianchiIX
