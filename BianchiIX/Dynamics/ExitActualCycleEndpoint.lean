import BianchiIX.Dynamics.ExitActualCycle
import BianchiIX.Algebra.ExitCycleEndpoint

noncomputable section

namespace BianchiIX

open Set

/-- The actual cyclic endpoint has the phase, radius, and wall scales needed for the next entrance. -/
theorem exists_terminal_axisCycle_endpoint {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 100) {J : ℕ} (hJ : 2 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let y := coreTailState h Y
      let z := projectiveCycle y
      coreTailValid h Y ∧
        toProjectiveState (normalizedMaxCurve (axisCycle (fromProjectiveState (coreTailEntry Y))) 0 (coreTailTime h Y)) = z ∧
        (399 / 100 * α ^ 2 < projectiveCycleDenom y ∧ projectiveCycleDenom y < 401 / 100 * α ^ 2) ∧
        (19 / (10 * α) < z 0 - 1 ∧ z 0 - 1 < 21 / (10 * α)) ∧
        (19 / (10 * α) < coreRadius (z 0) (z 2) ∧ coreRadius (z 0) (z 2) < 11 / (5 * α)) ∧
        (η / 2 * α ^ (J - 2) ≤ z 1 ∧ z 1 ≤ 2 * η * α ^ (J - 2)) ∧
        (|z 2| ≤ 2 * (C * b) / α ^ 2 ∧ |z 3| ≤ 2 * (C * b) / α ^ 2) ∧
        ((0 < u ∧ 0 < w) → 0 < z 2 ∧ 0 < z 3) ∧
        (∀ t ∈ Icc 0 (coreTailTime h Y),
          let γ := normalizedMaxCurve (axisCycle (fromProjectiveState (coreTailEntry Y))) 0 t
          0 < 1 + γ 0 ∧ |toProjectiveState γ 2| ≤ 1 / 5000) := by
  obtain ⟨C, hC, ε, hε, HE⟩ := exists_terminal_axisCycle_regular hη (by omega : 1 ≤ J)
  refine ⟨C, hC, ε, hε, ?_⟩
  intro α b u w hα hb hsmall hw Y h y z
  have hα0 : 0 < α := hα.1
  have hC0 : 0 < C := lt_of_lt_of_le (by norm_num) hC
  obtain ⟨hvalid, hCBpow, HF, HH⟩ := HE α b u w hα hb hsmall hw
  change coreTailValid h Y at hvalid
  have ht : coreTailTime h Y ∈ Icc 0 (coreTailTime h Y) := ⟨hvalid.1.1.1.le, le_rfl⟩
  have H := HF _ ht
  have hm : y 0 < 1 := H.1
  have hR : |coreRadius (y 0) (y 2) - (2 + 2 * α)| ≤ C * b := H.2.1
  have hsum : |y 1| + |y 3| ≤ C * b := H.2.2.1
  have hv : y 2 = h := coreTailState_active hvalid
  have hh : 0 < h := mul_pos hη.1 (pow_pos hα.1 J)
  have hp2 : α ^ (2 * J) ≤ α ^ 2 := pow_le_pow_of_le_one hα.1.le hα.2 (by omega)
  have hCBsq : C * b ≤ α ^ 2 / 10000 := hCBpow.trans (div_le_div_of_nonneg_right hp2 (by norm_num))
  have hCB : C * b ≤ α / 10000 := hCBsq.trans (by nlinarith only [hα.1, hα.2])
  have hvsmall : 0 ≤ y 2 ∧ y 2 ≤ α / 100 := by
    rw [hv]
    refine ⟨hh.le, ?_⟩
    have hp : α ^ J ≤ α := (pow_le_pow_of_le_one hα.1.le hα.2 (by omega : 1 ≤ J)).trans_eq (pow_one α)
    change η * α ^ J ≤ α / 100
    nlinarith only [mul_le_mul_of_nonneg_left hp hη.1.le, mul_le_mul_of_nonneg_right hη.2 hα.1.le]
  have hsplit : 1 - exitTailGap (coreRadius (y 0) (y 2)) (y 2) = y 0 := by
    rw [exitTailGap_of_coreRadius hm]
    ring
  have hdelta : 2 - exitTailGap (coreRadius (y 0) (y 2)) (y 2) = y 0 + 1 := by linarith only [hsplit]
  have HP := exitCycle_terminal_phase_bounds hα hCB hR hsum hvsmall
  rw [hsplit] at HP
  have hphase : z 0 - 1 = 4 * (exitTailGap (coreRadius (y 0) (y 2)) (y 2) - 2) / projectiveCycleDenom y := by
    change 1 - 4 * (y 0 + 1) / projectiveCycleDenom y - 1 = _
    rw [← hdelta]
    ring
  have HK := exitCycle_terminal_radius_bounds hα hCBsq hR hsum hvsmall
  dsimp only at HK
  rw [hsplit, hdelta] at HK
  have Hwall := exitCycle_positive_wall_scale hα.1 hvsmall.1 HH
  have hpow : h = η * α ^ (J - 2) * α ^ 2 := by
    change η * α ^ J = _
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hJ]
  have Hstrong : η / 2 * α ^ (J - 2) ≤ z 1 ∧ z 1 ≤ 2 * η * α ^ (J - 2) := by
    change _ ≤ 4 * y 2 / projectiveCycleDenom y ∧ 4 * y 2 / projectiveCycleDenom y ≤ _
    constructor
    · convert Hwall.1 using 1
      rw [hv, hpow]
      field_simp
    · convert Hwall.2 using 1
      rw [hv, hpow]
      field_simp
  have HH' : 39 / 10 * α ^ 2 < projectiveCycleDenom y := by nlinarith only [HH.1, sq_pos_of_pos hα.1]
  have HH0 : 0 < projectiveCycleDenom y := lt_trans (by positivity) HH'
  refine ⟨hvalid, H.2.2.2.2.2.1, HH, ?_, HK, Hstrong, ?_, ?_, ?_⟩
  · rw [hphase]
    exact HP
  · exact ⟨exitCycle_newWall_bound hα.1 (mul_pos hC0 hb).le HH' (by linarith only [hsum, abs_nonneg (y 1)]),
      exitCycle_newWall_bound hα.1 (mul_pos hC0 hb).le HH' (by linarith only [hsum, abs_nonneg (y 3)])⟩
  · intro hpos
    have H0 : y 1 = u * coreTailMultiplier h Y 0 := coreTailMultiplier_formula hvalid 0
    have H1 : y 3 = w * coreTailMultiplier h Y 1 := coreTailMultiplier_formula hvalid 1
    have hu : 0 < y 1 := by rw [H0]; exact mul_pos hpos.1 (coreTailMultiplier_pos _ _ _)
    have hw : 0 < y 3 := by rw [H1]; exact mul_pos hpos.2 (coreTailMultiplier_pos _ _ _)
    exact ⟨div_pos (mul_pos (by norm_num) hw) HH0, div_pos (mul_pos (by norm_num) hu) HH0⟩
  · intro t ht
    have Ht := HF t ht
    exact ⟨Ht.2.2.2.2.1, Ht.2.2.2.2.2.2.2.2⟩

end BianchiIX
