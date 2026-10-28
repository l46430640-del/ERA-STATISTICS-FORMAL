import BianchiIX.Dynamics.EntranceWallBudgets

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- Column integrals follow from the two wall budgets without resolving each product separately. -/
theorem scaled_entrance_weighted_envelope_integrals {Y : ℝ → ProjectiveState} {a : ℝ → ℝ} {s t k : ℝ}
    (hk : 7 / 4 ≤ k) (hst : s ≤ t)
    (hY : ∀ r ∈ Icc s t, HasDerivAt Y (a r • projectiveField (Y r)) r)
    (hac : ContinuousOn a (Icc s t)) (ha : ∀ r ∈ Icc s t, 0 ≤ a r)
    (hy : ∀ r ∈ Icc s t, entranceRegion k (Y r)) (hv : ∀ r ∈ Icc s t, 0 < Y r 2) :
    (∫ r in s..t, (Y r 1 + k * Y r 1 * (Y r 2 + Y r 1 + Y r 3)) *
      (a r * entranceClockRate (Y r))) ≤ 12 * Y s 1 ∧
    (∫ r in s..t, (Y r 3 / k ^ 2 + Y r 1 * Y r 3 / k + Y r 3 * (Y r 1 + Y r 3) / k ^ 3) *
      (a r * entranceClockRate (Y r))) ≤ 6 * Y s 3 / k ^ 2 := by
  let q := fun r => a r * entranceClockRate (Y r)
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hs : s ∈ Icc s t := ⟨le_rfl, hst⟩
  have hu := (hy s hs).2.2.1.1
  have hw := (hy s hs).2.2.2.2.1
  have hu1 : Y s 1 ≤ 1 := by linarith [(hy s hs).2.2.1.2]
  have hq (r : ℝ) (hr : r ∈ Icc s t) : 0 ≤ q r :=
    mul_nonneg (ha r hr) (entranceRegion_clock_pos hk (hy r hr)).le
  have hqc : ContinuousOn q (Icc s t) := hac.mul
    (continuous_entranceClockRate.comp_continuousOn (HasDerivAt.continuousOn hY))
  have hcoord (i : Fin 4) : ContinuousOn (fun r => Y r i) (Icc s t) :=
    (continuous_apply i).comp_continuousOn (HasDerivAt.continuousOn hY)
  have hUq : IntervalIntegrable (fun r => Y r 1 * q r) volume s t :=
    ((hcoord 1).mul hqc).intervalIntegrable_of_Icc hst
  have hWq : IntervalIntegrable (fun r => Y r 3 * q r) volume s t :=
    ((hcoord 3).mul hqc).intervalIntegrable_of_Icc hst
  obtain ⟨hwall, hIU, hIW⟩ := scaled_entrance_wall_budgets hk hst hY hac ha hy hv
  change (∫ r in s..t, Y r 1 * q r) ≤ _ at hIU
  change (∫ r in s..t, Y r 3 * q r) ≤ _ at hIW
  constructor
  · have hc : ContinuousOn (fun r => (Y r 1 + k * Y r 1 * (Y r 2 + Y r 1 + Y r 3)) * q r) (Icc s t) :=
      ((hcoord 1).add (((hcoord 1).const_mul k).mul (((hcoord 2).add (hcoord 1)).add (hcoord 3)))).mul hqc
    have HB := intervalIntegral.integral_mono_on hst (hc.intervalIntegrable_of_Icc hst)
      (hUq.const_mul (1 + 3 * k)) (fun r hr => show
        (Y r 1 + k * Y r 1 * (Y r 2 + Y r 1 + Y r 3)) * q r ≤ (1 + 3 * k) * (Y r 1 * q r) from by
          have hsum : Y r 2 + Y r 1 + Y r 3 ≤ 3 := by
            linarith [(hy r hr).2.2.2.1.2, (hy r hr).2.2.1.2, (hy r hr).2.2.2.2.2]
          have hb : Y r 1 + k * Y r 1 * (Y r 2 + Y r 1 + Y r 3) ≤ (1 + 3 * k) * Y r 1 := by
            nlinarith only [mul_le_mul_of_nonneg_left hsum (mul_nonneg hk0.le (hy r hr).2.2.1.1)]
          convert! mul_le_mul_of_nonneg_right hb (hq r hr) using 1
          ring)
    rw [intervalIntegral.integral_const_mul] at HB
    apply HB.trans ((mul_le_mul_of_nonneg_left hIU (by positivity)).trans ?_)
    calc
      (1 + 3 * k) * (3 * Y s 1 / k) = 3 * Y s 1 / k + 9 * Y s 1 := by field_simp; ring
      _ ≤ 12 * Y s 1 := by linarith only [div_le_self (by positivity : 0 ≤ 3 * Y s 1) hk1]
  · have hc : ContinuousOn (fun r => (Y r 3 / k ^ 2 + Y r 1 * Y r 3 / k +
        Y r 3 * (Y r 1 + Y r 3) / k ^ 3) * q r) (Icc s t) :=
      ((((hcoord 3).div_const (k ^ 2)).add (((hcoord 1).mul (hcoord 3)).div_const k)).add
        (((hcoord 3).mul ((hcoord 1).add (hcoord 3))).div_const (k ^ 3))).mul hqc
    have HB := intervalIntegral.integral_mono_on hst (hc.intervalIntegrable_of_Icc hst)
      ((hUq.const_mul (Y s 3 / k)).add (hWq.const_mul (1 / k ^ 2 + 2 / k ^ 3)))
      (fun r hr => show (Y r 3 / k ^ 2 + Y r 1 * Y r 3 / k + Y r 3 * (Y r 1 + Y r 3) / k ^ 3) * q r ≤
        (Y s 3 / k) * (Y r 1 * q r) + (1 / k ^ 2 + 2 / k ^ 3) * (Y r 3 * q r) from by
          have hUW := div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hwall r hr).2 (hy r hr).2.2.1.1) hk0.le
          have hsum : Y r 1 + Y r 3 ≤ 2 := by linarith [(hy r hr).2.2.1.2, (hy r hr).2.2.2.2.2]
          have hWW := div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsum (hy r hr).2.2.2.2.1) (pow_nonneg hk0.le 3)
          have hb' : Y r 3 / k ^ 2 + Y r 1 * Y r 3 / k + Y r 3 * (Y r 1 + Y r 3) / k ^ 3 ≤
              Y r 3 / k ^ 2 + Y r 1 * Y s 3 / k + Y r 3 * 2 / k ^ 3 :=
            add_le_add (add_le_add le_rfl hUW) hWW
          convert! mul_le_mul_of_nonneg_right hb' (hq r hr) using 1
          ring)
    rw [intervalIntegral.integral_add (hUq.const_mul (Y s 3 / k))
      (hWq.const_mul (1 / k ^ 2 + 2 / k ^ 3)), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at HB
    apply HB.trans ((add_le_add (mul_le_mul_of_nonneg_left hIU (by positivity))
      (mul_le_mul_of_nonneg_left hIW (by positivity))).trans ?_)
    calc
      (Y s 3 / k) * (3 * Y s 1 / k) + (1 / k ^ 2 + 2 / k ^ 3) * Y s 3 =
          (Y s 3 / k ^ 2) * (3 * Y s 1 + 1 + 2 / k) := by field_simp; ring
      _ ≤ (Y s 3 / k ^ 2) * 6 := mul_le_mul_of_nonneg_left
        (by linarith only [hu1, div_le_self (by norm_num : (0 : ℝ) ≤ 2) hk1]) (by positivity)
      _ = _ := by ring

end BianchiIX
