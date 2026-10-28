import BianchiIX.Dynamics.ProjectiveCycle
import BianchiIX.Dynamics.ExitTailArrival
import BianchiIX.Dynamics.CoreTailMultipliers
import BianchiIX.Algebra.ExitCycleBounds

noncomputable section

namespace BianchiIX

open Set

/-- The cyclic chart stays regular along the entire actual tail and cannot encounter its new active section early. -/
theorem exists_terminal_axisCycle_regular {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 100) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let x := fromProjectiveState (coreTailEntry Y)
      let γ := fun t => normalizedMaxCurve x 0 t
      let γc := fun t => normalizedMaxCurve (axisCycle x) 0 t
      let β := fun t => toProjectiveState (γ t)
      let βc := fun t => toProjectiveState (γc t)
      coreTailValid h Y ∧ C * b ≤ α ^ (2 * J) / 10000 ∧
        (∀ t ∈ Icc 0 (coreTailTime h Y),
          β t 0 < 1 ∧ |coreRadius (β t 0) (β t 2) - (2 + 2 * α)| ≤ C * b ∧
          |β t 1| + |β t 3| ≤ C * b ∧
          39 / 10 * α ^ 2 + 2 / 5 * (β t 2) ^ 2 < projectiveCycleDenom (β t) ∧
          0 < 1 + γc t 0 ∧ βc t = projectiveCycle (β t) ∧
          (1 + γc t 0) / (1 + γ t 0) = projectiveCycleDenom (β t) / 4 ∧
          |βc t 2| ≤ 2 * (C * b) / α ^ 2 ∧ |βc t 2| ≤ 1 / 5000) ∧
        399 / 100 * α ^ 2 < projectiveCycleDenom (coreTailState h Y) ∧
        projectiveCycleDenom (coreTailState h Y) < 401 / 100 * α ^ 2 := by
  have hη1 : η < 1 := by linarith only [hη.2]
  obtain ⟨A, hA, εt, hεt, HE⟩ := exists_terminal_coreTail_valid ⟨hη.1, hη1⟩ hJ
  let C := 40 * A
  have hC : 1 ≤ C := by dsimp only [C]; linarith only [hA]
  have hC0 : 0 < C := lt_of_lt_of_le (by norm_num) hC
  let ε := min εt (1 / (10000 * C))
  have hε : 0 < ε := lt_min hεt (by positivity)
  have hCε : C * ε ≤ 1 / 10000 := by
    have H := (le_div_iff₀ (by positivity : 0 < 10000 * C)).mp (min_le_right εt (1 / (10000 * C)))
    nlinarith only [H]
  refine ⟨C, hC, ε, hε, ?_⟩
  intro α b u w hα hb hsmall hw Y h x γ γc β βc
  have hα0 : 0 < α := hα.1
  have hpJ : α ^ (2 * J) ≤ α ^ J := pow_le_pow_of_le_one hα.1.le hα.2 (by omega)
  have hp2 : α ^ (2 * J) ≤ α ^ 2 := pow_le_pow_of_le_one hα.1.le hα.2 (by omega)
  have hsmallt : b ≤ εt * α ^ J := hsmall.trans ((mul_le_mul_of_nonneg_left hpJ hε.le).trans
    (mul_le_mul_of_nonneg_right (min_le_left εt _) (pow_nonneg hα.1.le J)))
  have hCBpow : C * b ≤ α ^ (2 * J) / 10000 := by
    nlinarith only [mul_le_mul_of_nonneg_left hsmall hC0.le,
      mul_le_mul_of_nonneg_right hCε (pow_nonneg hα.1.le (2 * J))]
  have hCBsq : C * b ≤ α ^ 2 / 10000 := hCBpow.trans (div_le_div_of_nonneg_right hp2 (by norm_num))
  have hCB : C * b ≤ α / 10000 := hCBsq.trans (by nlinarith only [hα.1, hα.2])
  obtain ⟨hvalid, hT, _, HF⟩ := HE α b u w hα hb hsmallt hw
  change coreTailValid h Y at hvalid
  have hc : stateConstraint x = 1 := fromProjectiveState_constraint (coreTailValid_denom_pos hvalid).ne'
  have hraw (t : ℝ) (ht : t ∈ Icc 0 (coreTailTime h Y)) :
      0 < 1 + γ t 0 ∧ (β t 0 < 1) ∧ (0 ≤ β t 2 ∧ β t 2 ≤ 1) ∧
      |coreRadius (β t 0) (β t 2) - (2 + 2 * α)| ≤ C * b ∧ |β t 1| + |β t 3| ≤ C * b := by
    have H := HF t ht
    have hh : 0 < h := mul_pos hη.1 (pow_pos hα.1 J)
    refine ⟨lt_of_lt_of_le (by norm_num) H.1, lt_of_le_of_lt H.2.1.1 (by norm_num),
      ⟨hh.le.trans H.2.1.2.2.2.1.1, H.2.1.2.2.2.1.2⟩, H.2.2.2.1, ?_⟩
    exact H.2.2.1.trans (by dsimp only [C]; nlinarith only [mul_nonneg (by linarith only [hA] : 0 ≤ A) hb.le])
  have hgap (t : ℝ) (ht : t ∈ Icc 0 (coreTailTime h Y)) :
      1 - exitTailGap (coreRadius (β t 0) (β t 2)) (β t 2) = β t 0 := by
    rw [exitTailGap_of_coreRadius (hraw t ht).2.1]
    ring
  refine ⟨hvalid, hCBpow, ?_, ?_⟩
  · intro t ht
    have H := hraw t ht
    have HH := exitCycleDenom_lower hα hCB H.2.2.2.1 H.2.2.2.2 H.2.2.1
    rw [hgap t ht] at HH
    change 39 / 10 * α ^ 2 + 2 / 5 * (β t 2) ^ 2 < projectiveCycleDenom (β t) at HH
    have HH' : 39 / 10 * α ^ 2 < projectiveCycleDenom (β t) := by nlinarith only [HH, sq_nonneg (β t 2)]
    have HH0 : 0 < projectiveCycleDenom (β t) := lt_trans (by positivity) HH'
    have hct : stateConstraint (γ t) = 1 := (normalizedMaxCurve_forward_of_constraint hc ht.1).2.1
    have hcycle : γc t = axisCycle (γ t) := NormalizedSymmetry.cycle.maxCurve
      (normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1)
    have Hclock := axisCycle_projective_clock_pos H.1 hct HH0
    have Hmap := toProjectiveState_axisCycle H.1.ne' hct HH0.ne'
    have Hcmap : βc t = projectiveCycle (β t) := by change toProjectiveState (γc t) = _; rwa [hcycle]
    have Hweak : |β t 3| ≤ C * b := by linarith only [H.2.2.2.2, abs_nonneg (β t 1)]
    refine ⟨H.2.1, H.2.2.2.1, H.2.2.2.2, HH, by rw [hcycle]; exact Hclock.1,
      Hcmap, by rw [hcycle]; exact Hclock.2, ?_, ?_⟩
    · rw [Hcmap]
      exact exitCycle_newWall_bound hα.1 (mul_pos hC0 hb).le HH' Hweak
    · rw [Hcmap]
      exact exitCycle_newWall_small hα.1 (mul_pos hC0 hb).le hCBsq HH' Hweak
  · have ht : coreTailTime h Y ∈ Icc 0 (coreTailTime h Y) := ⟨hT.le, le_rfl⟩
    have H := hraw _ ht
    have hv : β (coreTailTime h Y) 2 = h := coreTailState_active hvalid
    have hp : α ^ J ≤ α := (pow_le_pow_of_le_one hα.1.le hα.2 hJ).trans_eq (pow_one α)
    have hvsmall : β (coreTailTime h Y) 2 ≤ α / 100 := by
      rw [hv]
      change η * α ^ J ≤ α / 100
      nlinarith only [mul_le_mul_of_nonneg_left hp hη.1.le, mul_le_mul_of_nonneg_right hη.2 hα.1.le]
    have HB := exitCycleDenom_terminal_bounds hα hCB H.2.2.2.1 H.2.2.2.2 ⟨H.2.2.1.1, hvsmall⟩
    rw [hgap _ ht] at HB
    exact HB

end BianchiIX
