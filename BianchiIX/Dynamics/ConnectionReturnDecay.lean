import BianchiIX.Dynamics.ConnectionReturnClock
import BianchiIX.Analysis.ConnectionEndpointScales

noncomputable section

namespace BianchiIX

open Set

/-- The exact first return has the decay needed to control phase endpoint corrections. -/
theorem connectionReturn_endpoint_scales {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    connectionReturnState p 1 / p 2 ≤ 8 * p 1 / p 0 ∧
    (connectionReturnState p 2) ^ 2 ≤ (p 2) ^ 2 ∧
    (1 - Real.log (p 2)) * (connectionReturnState p 2) ^ 2 ≤ p 0 * (p 2) ^ 2 := by
  let y := connectionEntry (p 0) (p 1) (p 2)
  let L := -Real.log (p 2)
  obtain ⟨hL, q, hq0, hqL, H⟩ := exists_connectionReturn_log_clock hμ hu hw
  change q L = connectionReturnTime p at hqL
  let Y := fun z => projectiveOriginalFlow y 0 (q z)
  have hden := connection_entry_denom_pos hμ ⟨hu.1.le, hu.2⟩ hw
  have hm z hz := (H z hz).2.2.1.1
  have hU z hz := (H z hz).2.2.1.2.1
  have hV z hz := And.intro (H z hz).2.2.2.2.1 (H z hz).2.2.1.2.2.1.2
  have hW z hz := (H z hz).2.2.1.2.2.2
  have hD (z : ℝ) (hz : z ∈ Icc 0 L) : connectionClockRate (Y z) ≠ 0 := by
    have Hs := (connection_speed_bounds hμ (hm z hz) (hU z hz)
      ⟨(hV z hz).1.le, (hV z hz).2⟩ (hW z hz)).1
    change p 0 / 2 ≤ connectionClockRate (Y z) at Hs
    linarith only [Hs, hμ]
  have hY z hz := hasDerivAt_projectiveOriginalFlow_connectionLog (y := y) (t₀ := 0) (q := q) (z := z)
    hden (H z hz).1 (H z hz).2.1 (hD z hz) (H z hz).2.2.2.2.2.2
  have hinit : Y 0 = y := by dsimp [Y]; rw [hq0, projectiveOriginalFlow_initial hden]
  have hend : Y L = connectionReturnState p := by dsimp [Y]; rw [hqL]; rfl
  have hentry : Y 0 1 ≤ Y 0 2 := by
    rw [hinit]
    change p 1 ≤ 1
    have Hs := (le_div_iff₀ (show 0 < p 0 by linarith only [hμ])).mp hu.2
    nlinarith only [Hs, hμ, hu.1]
  have HP := connectionLog_prefix_estimates hL hμ hY hm hU hV hW hentry
  have hUdecay : connectionReturnState p 1 ≤ p 1 * Real.exp (-p 0 * L / 2) := by
    have Hs := HP.2.1
    change Y L 1 ≤ Y 0 1 * Real.exp (-p 0 * (L - 0) / 2) at Hs
    simpa [hinit, hend, y, connectionEntry] using Hs
  have hVdecay : connectionReturnState p 2 ≤ p 2 * Real.exp (-2 * L / p 0) := by
    have Hs := HP.2.2.2.1
    change Y L 2 * Y L 3 ≤ Y 0 2 * Y 0 3 * Real.exp (-2 * (L - 0) / p 0) at Hs
    rw [hend, hinit, (connectionReturn_growing_component hμ ⟨hu.1.le, hu.2⟩ hw).1] at Hs
    simpa [y, connectionEntry] using Hs
  exact connection_endpoint_envelope_bounds hμ hu.1.le hw
    (connectionReturn_wall_pos hμ ⟨hu.1.le, hu.2⟩ hw).1.le hUdecay hVdecay

theorem connectionReturn_phase_clock_correction {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    |connectionLogCoordinateRates (connectionReturnState p) 0| / p 2 ≤ 100 * (p 1 + p 2) / p 0 := by
  let μ := p 0
  let u := p 1
  let w := p 2
  let y := connectionReturnState p
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hw0 : 0 < w := hw.1
  have hscales := connectionReturn_endpoint_scales hμ hu hw
  have hc := connectionReturn_control hμ ⟨hu.1.le, hu.2⟩ hw
  have hr := (hc.2 (connectionReturnTime p) ⟨hc.1.le, le_rfl⟩).2
  change connectionRegion μ y at hr
  have hW : y 3 = 1 := (connectionReturn_growing_component hμ ⟨hu.1.le, hu.2⟩ hw).1
  have hD := (connection_speed_bounds hμ hr.1 hr.2.1 hr.2.2.1 hr.2.2.2).1
  have hD0 : 0 < connectionSpeed (-y 0) (y 1) (y 2) (y 3) := by linarith only [hD, hμ]
  have hrate : |connectionLogCoordinateRates y 0| ≤ 10 * y 1 + 8 * (y 2) ^ 2 / μ ^ 3 := by
    change |matchingPhaseRate (-y 0) (y 1) (y 2) (y 3) / connectionSpeed (-y 0) (y 1) (y 2) (y 3)| ≤ _
    rw [abs_div, abs_of_pos hD0]
    have H := matchingPhase_rate_bound hμ hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
    have H' : |matchingPhaseRate (-y 0) (y 1) (y 2) (y 3)| ≤ 5 * μ * y 1 + 4 / μ ^ 2 * (y 2) ^ 2 := by
      simpa only [hW, mul_one] using H
    calc
      _ ≤ (5 * μ * y 1 + 4 / μ ^ 2 * (y 2) ^ 2) / connectionSpeed (-y 0) (y 1) (y 2) (y 3) :=
        div_le_div_of_nonneg_right H' hD0.le
      _ ≤ (5 * μ * y 1 + 4 / μ ^ 2 * (y 2) ^ 2) / (μ / 2) :=
        div_le_div_of_nonneg_left (by have H0 := hr.2.1.1; positivity) (by positivity) hD
      _ = 10 * y 1 + 8 * (y 2) ^ 2 / μ ^ 3 := by field_simp; ring
  have hweak : (y 2) ^ 2 / (μ ^ 3 * w) ≤ w / μ := by
    have H : (y 2) ^ 2 / w ≤ w := (div_le_iff₀ hw0).mpr (by nlinarith only [hscales.2.1])
    calc
      (y 2) ^ 2 / (μ ^ 3 * w) = ((y 2) ^ 2 / w) / μ ^ 3 := by ring
      _ ≤ w / μ ^ 3 := div_le_div_of_nonneg_right H (by positivity)
      _ ≤ w / μ := div_le_div_of_nonneg_left hw0.le hμ0 (by nlinarith only [hμ, sq_nonneg (μ - 1)])
  change |connectionLogCoordinateRates y 0| / w ≤ 100 * (u + w) / μ
  calc
    _ ≤ (10 * y 1 + 8 * (y 2) ^ 2 / μ ^ 3) / w := div_le_div_of_nonneg_right hrate hw0.le
    _ = 10 * (y 1 / w) + 8 * ((y 2) ^ 2 / (μ ^ 3 * w)) := by ring
    _ ≤ 10 * (8 * u / μ) + 8 * (w / μ) := add_le_add
      (mul_le_mul_of_nonneg_left hscales.1 (by norm_num)) (mul_le_mul_of_nonneg_left hweak (by norm_num))
    _ = (80 * u + 8 * w) / μ := by ring
    _ ≤ 100 * (u + w) / μ := by
      apply div_le_div_of_nonneg_right _ hμ0.le
      have hu0 : 0 < u := hu.1
      nlinarith only [hu0, hw0]

end BianchiIX
