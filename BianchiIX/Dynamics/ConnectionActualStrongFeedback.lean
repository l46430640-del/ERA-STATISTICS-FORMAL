import BianchiIX.Dynamics.ConnectionStrongFeedback
import BianchiIX.Dynamics.ConnectionLogFlowVariation

noncomputable section

namespace BianchiIX

open Set

/-- Ordinary strong-wall initial response of the exact flow at a fixed relative logarithmic clock. -/
theorem connectionLog_actual_strong_variation_bounds {y : ProjectiveState} {q : ℝ → ℝ}
    {t₀ μ a b : ℝ} (hab : a ≤ b) (hμ : 4 ≤ μ) (hden : 0 < projectiveStateDenom y)
    (hdom : ∀ z ∈ Icc a b, q z ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hchart : ∀ z ∈ Icc a b, 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ (q z) 0)
    (hm : ∀ z ∈ Icc a b, |-projectiveOriginalFlow y t₀ (q z) 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 < projectiveOriginalFlow y t₀ (q z) 1 ∧
      projectiveOriginalFlow y t₀ (q z) 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < projectiveOriginalFlow y t₀ (q z) 2 ∧
      projectiveOriginalFlow y t₀ (q z) 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 < projectiveOriginalFlow y t₀ (q z) 3 ∧
      projectiveOriginalFlow y t₀ (q z) 3 ≤ 1)
    (hentry : y 1 ≤ y 2) (hsmall : y 1 ≤ (1 / 10000) / μ) (hwall : y 3 ≤ 1 / 10000)
    (hq : ∀ z ∈ Icc a b,
      HasDerivAt q (1 / connectionOriginalClockRate (projectiveOriginalFlow y t₀ (q z))) z)
    (hqa : q a = t₀) :
    ∀ t ∈ Icc a b,
      |connectionLogFlowVariation y t₀ (q t) ![0, 1, 0, 0] 0| ≤ 70 / μ ∧
      |connectionLogFlowVariation y t₀ (q t) ![0, 1, 0, 0] 1| ≤ 1 / y 1 + 256 + 8960 * (t - a) / μ ∧
      |connectionLogFlowVariation y t₀ (q t) ![0, 1, 0, 0] 2| ≤ (256 + 8960 * (t - a) / μ) / μ ^ 2 := by
  have hu' (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ projectiveOriginalFlow y t₀ (q z) 1 ∧
      projectiveOriginalFlow y t₀ (q z) 1 ≤ 1 / 10000 := ⟨(hu z hz).1.le, (hu z hz).2⟩
  have hv' (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ projectiveOriginalFlow y t₀ (q z) 2 ∧
      projectiveOriginalFlow y t₀ (q z) 2 ≤ 1 := ⟨(hv z hz).1.le, (hv z hz).2⟩
  have hw' (z : ℝ) (hz : z ∈ Icc a b) : 0 ≤ projectiveOriginalFlow y t₀ (q z) 3 ∧
      projectiveOriginalFlow y t₀ (q z) 3 ≤ 1 := ⟨(hw z hz).1.le, (hw z hz).2⟩
  have hclock (z : ℝ) (hz : z ∈ Icc a b) : connectionClockRate (projectiveOriginalFlow y t₀ (q z)) ≠ 0 := by
    have H := (connection_speed_bounds hμ (hm z hz) (hu' z hz) (hv' z hz) (hw' z hz)).1
    change μ / 2 ≤ connectionClockRate (projectiveOriginalFlow y t₀ (q z)) at H
    linarith only [H, hμ]
  have hfield (z : ℝ) (hz : z ∈ Icc a b) :=
    hasDerivAt_projectiveOriginalFlow_connectionLog (y := y) (t₀ := t₀) (z := z) (q := q)
      hden (hdom z hz) (hchart z hz) (hclock z hz) (hq z hz)
  have hvar (z : ℝ) (hz : z ∈ Icc a b) :=
    hasDerivAt_connectionLogFlowVariation (y := y) (t₀ := t₀) (z := z) (q := q)
      hden (hdom z hz) (hchart z hz)
      (by linarith only [hμ, (abs_le.mp (hm z hz)).1]) (hclock z hz)
      (by have H := (matchingPhase_slope_bounds hμ (hm z hz) (hv' z hz) (hw' z hz)).1; linarith only [H])
      (ne_of_gt (hu z hz).1) (ne_of_gt (hv z hz).1) (ne_of_gt (hw z hz).1) (hq z hz) ![0, 1, 0, 0]
  have hinit : projectiveOriginalFlow y t₀ (q a) = y := by rw [hqa, projectiveOriginalFlow_initial hden]
  have hdinit : connectionLogFlowVariation y t₀ (q a) ![0, 1, 0, 0] = connectionLogTangent y ![0, 1, 0, 0] := by
    rw [hqa, connectionLogFlowVariation_initial hden]
  have hu0 : 0 < y 1 := by simpa only [hinit] using (hu a ⟨le_rfl, hab⟩).1
  have H := connectionLog_strong_variation_bounds
    (Y := fun z => projectiveOriginalFlow y t₀ (q z))
    (D := fun z => connectionLogFlowVariation y t₀ (q z) ![0, 1, 0, 0])
    hab hμ hfield hm hu' hv hw'
    (by simpa only [hinit] using hentry) (by simpa only [hinit] using hsmall) (by simpa only [hinit] using hwall)
    (by simpa only [hinit] using hu0) hvar
    (fun z hz => by rw [connectionLogFlowVariation_wall _ (hclock z hz) (ne_of_gt (hw z hz).1)]; simp)
    (by simp [hdinit, connectionLogTangent]) (by simp [hdinit, hinit, connectionLogTangent])
    (by simp [hdinit, connectionLogTangent])
  intro t ht
  have Ht := H t ht
  rw [hinit] at Ht
  have HC := connectionShiftedTangent_component_bounds (by linarith only [hμ] : 0 < μ) Ht.2
  rw [abs_of_pos (one_div_pos.mpr hu0)] at HC
  exact ⟨Ht.1, HC.1.trans_eq (by ring), HC.2⟩

end BianchiIX
