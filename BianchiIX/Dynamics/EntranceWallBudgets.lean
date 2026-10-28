import BianchiIX.Dynamics.EntranceDecay
import BianchiIX.Analysis.ClockWeightIntegrals

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- Wall budgets are measured in the active logarithmic clock and allow zero stable walls. -/
theorem scaled_entrance_wall_budgets {Y : ℝ → ProjectiveState} {a : ℝ → ℝ} {s t k : ℝ}
    (hk : 7 / 4 ≤ k) (hst : s ≤ t)
    (hY : ∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r)
    (hac : ContinuousOn a (Icc s t)) (ha : ∀ r ∈ Icc s t, 0 ≤ a r)
    (hy : ∀ r ∈ Icc s t, entranceRegion k (Y r)) (hv : ∀ r ∈ Icc s t, 0 < Y r 2) :
    (∀ r ∈ Icc s t, Y r 1 ≤ Y s 1 ∧ Y r 3 ≤ Y s 3) ∧
      (∫ r in s..t, Y r 1 * (a r * entranceClockRate (Y r))) ≤ 3 * Y s 1 / k ∧
      (∫ r in s..t, Y r 3 * (a r * entranceClockRate (Y r))) ≤ Y s 3 := by
  let z := fun r => Real.log (Y r 2)
  let q := fun r => a r * entranceClockRate (Y r)
  have hk0 : 0 < k := by linarith
  have hs : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hz (r : ℝ) (hr : r ∈ Icc s t) : HasDerivAt z (q r) r :=
    hasDerivAt_entranceLog_scaled (hY r hr) (hv r hr).ne'
  have hq (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ q r :=
    mul_nonneg (ha r hr) (entranceRegion_clock_pos hk (hy r hr)).le
  have hqc : ContinuousOn q (Icc s t) := hac.mul
    (continuous_entranceClockRate.comp_continuousOn (HasDerivAt.continuousOn hY))
  have hcoord (i : Fin 4) : ContinuousOn (fun r => Y r i) (Icc s t) :=
    (continuous_apply i).comp_continuousOn (HasDerivAt.continuousOn hY)
  have hmono : MonotoneOn z (Icc s t) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc s t) (HasDerivAt.continuousOn hz)
      (fun r hr => (hz r (interior_subset hr)).hasDerivWithinAt) (fun r hr => hq r (interior_subset hr))
  have hdz (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ z r - z s := sub_nonneg.mpr (hmono hs hr hr.1)
  have hdec := scaled_entrance_decay hk hY ha hy hv
  have hU (r : ℝ) (hr : r ∈ Icc s t) : Y r 1 ≤ Y s 1 * Real.exp (-(k / 3) * (z r - z s)) := by
    have H : Y r 1 ≤ Y s 1 * Real.exp (-(1 + k / 3) * (z r - z s)) := by
      simpa only [abs_of_nonneg (hy r hr).2.2.1.1, abs_of_nonneg (hy s hs).2.2.1.1] using (hdec r hr).1
    exact H.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith only [hdz r hr])) (hy s hs).2.2.1.1)
  have hW (r : ℝ) (hr : r ∈ Icc s t) : Y r 3 ≤ Y s 3 * Real.exp (-1 * (z r - z s)) := by
    have H : Y r 3 ≤ Y s 3 * Real.exp (-(1 + 1 / k) * (z r - z s)) := by
      simpa only [abs_of_nonneg (hy r hr).2.2.2.2.1, abs_of_nonneg (hy s hs).2.2.2.2.1] using (hdec r hr).2
    apply H.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hy s hs).2.2.2.2.1)
    nlinarith only [mul_nonneg (one_div_pos.mpr hk0).le (hdz r hr)]
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    exact ⟨(hU r hr).trans (mul_le_of_le_one_right (hy s hs).2.2.1.1
      (Real.exp_le_one_iff.mpr (by nlinarith only [mul_nonneg hk0.le (hdz r hr)]))),
      (hW r hr).trans (mul_le_of_le_one_right (hy s hs).2.2.2.2.1
      (Real.exp_le_one_iff.mpr (by linarith only [hdz r hr])))⟩
  · convert! integral_clock_le_of_exp_decay hst hz hqc hq
      (show 0 < k / 3 by positivity) (hy s hs).2.2.1.1 (hcoord 1) hU using 1
    ring
  · simpa only [div_one] using integral_clock_le_of_exp_decay hst hz hqc hq
      (by norm_num : (0 : ℝ) < 1) (hy s hs).2.2.2.2.1 (hcoord 3) hW

end BianchiIX
