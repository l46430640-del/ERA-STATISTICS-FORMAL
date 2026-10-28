import BianchiIX.Dynamics.EntranceStrongRadialDerivative

noncomputable section

namespace BianchiIX

set_option maxHeartbeats 600000 in
/-- The strong coefficient has the improved radial decay in (C.21). -/
theorem exists_entranceRadialStrong_radial_bounds :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y → 0 < y 2 →
      ∀ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ →
        let z := entranceRadialCoordinates y
        |entranceRadialStrongCoefficient y| ≤ C ∧
        |fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) z (Pi.single 0 1)| ≤ C / k ^ 2 ∧
        |fderiv ℝ (fun z => entranceStrongRemainder (Ψ z)) z (Pi.single 0 1)| ≤
          C * (y 2 * (y 1 + y 3) + (y 1 + y 3) ^ 2) / k := by
  obtain ⟨C, hC, HC⟩ := exists_entranceStrongRemainder_bounds
  obtain ⟨K, hK, HK⟩ := exists_entranceClock_radial_cancellation_bound
  obtain ⟨J, _, HJ⟩ := exists_entranceRadialInverse_column_bounds
  refine ⟨256 * (C + K + 1), by positivity, ?_⟩
  intro k y hk hy hv Ψ H
  let b := y 1 + y 3
  let s := y 2 * b + b ^ 2
  let z := entranceRadialCoordinates y
  let Q := fderiv ℝ (fun z => entranceClockRate (Ψ z)) z
  let E := fderiv ℝ (fun z => entranceStrongRemainder (Ψ z)) z
  have hU := hy.2.2.1.1
  have hV := hy.2.2.2.1.1
  have hW := hy.2.2.2.2.1
  have hb : 0 ≤ b := add_nonneg hU hW
  have hb1 : b ≤ 1 := by dsimp [b]; linarith [hy.2.2.1.2, hy.2.2.2.2.2]
  have hb2 : b ^ 2 ≤ 1 := by nlinarith only [hb, hb1]
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hs2 : s ≤ 2 := by
    have Hprod := mul_le_mul hy.2.2.2.1.2 hb1 hb (by norm_num : (0 : ℝ) ≤ 1)
    dsimp [s]; nlinarith only [Hprod, hb2]
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hU]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hW]; linarith [hy.2.2.2.2.2]
  obtain ⟨_, hE, hEM⟩ := HC k y hk hy
  have hMr := (HJ k y hk hy hv Ψ H).1
  rw [H.phase_partials.1] at hMr
  have hEr : |E (Pi.single 0 1)| ≤ 8 * C * s / k := by
    dsimp only [E, z]
    rw [(H.scalar_partials ((contDiffAt_entranceStrongRemainder_one hm hu hw).differentiableAt (by norm_num))).1,
      abs_mul, abs_of_nonneg (by linarith only [hMr.1])]
    calc
      _ ≤ 8 * (C * s / k) := mul_le_mul hMr.2 hEM (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have hEcoarse : |entranceStrongRemainder y| ≤ 2 * C :=
    hE.trans (by nlinarith only [mul_le_mul_of_nonneg_left hs2 hC.le])
  have hErcoarse : |E (Pi.single 0 1)| ≤ 16 * C / k := hEr.trans
    (div_le_div_of_nonneg_right (by nlinarith only [mul_le_mul_of_nonneg_left hs2 hC.le]) hk0.le)
  obtain ⟨_, hr, _⟩ := entranceRegion_stable_radial_bounds hk hy
  have hD := entranceRegion_speed hk hy
  have hr0 := entranceStableRadius_pos hv
  have hD0 := entranceRegion_clock_pos hk hy
  have hDlo : k / 2 ≤ entranceClockRate y := by linarith only [hD.1, hk0]
  have hden : k ^ 2 / 4 ≤ entranceStableRadius y * entranceClockRate y := by
    have Hprod := mul_le_mul hr.1 hDlo (by positivity) hr0.le
    nlinarith only [Hprod]
  have hDsq : k ^ 2 / 4 ≤ entranceClockRate y ^ 2 := by
    have Hpow := pow_le_pow_left₀ (show 0 ≤ k / 2 by positivity) hDlo 2
    nlinarith only [Hpow]
  have hQ : |Q (Pi.single 0 1)| ≤ 8 := by
    dsimp only [Q, z]
    rw [H.clock_partials.1, abs_of_nonneg (by linarith only [hMr.1])]
    exact hMr.2
  have hcancel : |entranceStableRadius y * Q (Pi.single 0 1) - entranceClockRate y| ≤ 3 * K := by
    have hv2 : y 2 ^ 2 ≤ 1 := by nlinarith only [hV, hy.2.2.2.1.2]
    have hvterm : y 2 ^ 2 / k ≤ 1 := (div_le_self (sq_nonneg _) hk1).trans hv2
    have huv : y 1 * y 2 ≤ 1 := by
      have Hprod := mul_le_mul (show y 1 ≤ 1 by linarith [hy.2.2.1.2]) hy.2.2.2.1.2 hV (by norm_num : (0 : ℝ) ≤ 1)
      simpa using Hprod
    exact (HK k y hk hy Ψ H).trans (by
      have HB := mul_le_mul_of_nonneg_left (show y 2 ^ 2 / k + y 1 * y 2 + b ^ 2 ≤ 3 by linarith only [hvterm, huv, hb2]) hK.le
      nlinarith only [HB])
  have hquot : |entranceStrongRemainder y / (entranceStableRadius y * entranceClockRate y)| ≤ 8 * C / k ^ 2 := by
    rw [abs_div, abs_of_pos (mul_pos hr0 hD0)]
    calc
      _ ≤ (2 * C) / (k ^ 2 / 4) := div_le_div₀ (by positivity) hEcoarse (by positivity) hden
      _ = _ := by ring
  have hvalue : |entranceRadialStrongCoefficient y| ≤ 4 + 8 * C := by
    rw [entranceRadialStrongCoefficient_split]
    calc
      _ ≤ |(-entranceStableRadius y) / entranceClockRate y| +
          |entranceStrongRemainder y / (entranceStableRadius y * entranceClockRate y)| := abs_add_le _ _
      _ = entranceStableRadius y / entranceClockRate y +
          |entranceStrongRemainder y / (entranceStableRadius y * entranceClockRate y)| := by
        rw [abs_div, abs_neg, abs_of_pos hr0, abs_of_pos hD0]
      _ ≤ (2 * k) / (k / 2) + 8 * C / k ^ 2 := add_le_add (div_le_div₀ (by positivity) hr.2 (by positivity) hDlo) hquot
      _ = 4 + 8 * C / k ^ 2 := by field_simp; ring
      _ ≤ _ := add_le_add le_rfl (div_le_self (by positivity) (one_le_pow₀ hk1))
  have hlog : |1 / entranceStableRadius y + Q (Pi.single 0 1) / entranceClockRate y| ≤ 18 / k := by
    calc
      _ ≤ 1 / entranceStableRadius y + |Q (Pi.single 0 1)| / entranceClockRate y := by
        simpa only [abs_div, abs_one, abs_of_pos hr0, abs_of_pos hD0] using
          abs_add_le (1 / entranceStableRadius y) (Q (Pi.single 0 1) / entranceClockRate y)
      _ ≤ 1 / (k / 2) + 8 / (k / 2) := add_le_add
        (div_le_div_of_nonneg_left (by norm_num) (by positivity) hr.1)
        (div_le_div₀ (by norm_num) hQ (by positivity) hDlo)
      _ = _ := by ring
  have hderiv : |fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) z (Pi.single 0 1)| ≤
      (12 * K + 208 * C) / k ^ 2 := by
    rw [H.strong_differential hk hy hv]
    change |(entranceStableRadius y * Q (Pi.single 0 1) - entranceClockRate y * 1) / entranceClockRate y ^ 2 +
      E (Pi.single 0 1) / (entranceStableRadius y * entranceClockRate y) -
      entranceStrongRemainder y / (entranceStableRadius y * entranceClockRate y) *
        (1 / entranceStableRadius y + Q (Pi.single 0 1) / entranceClockRate y)| ≤ _
    rw [mul_one]
    calc
      _ ≤ |entranceStableRadius y * Q (Pi.single 0 1) - entranceClockRate y| / entranceClockRate y ^ 2 +
          |E (Pi.single 0 1)| / (entranceStableRadius y * entranceClockRate y) +
          |entranceStrongRemainder y / (entranceStableRadius y * entranceClockRate y)| *
            |1 / entranceStableRadius y + Q (Pi.single 0 1) / entranceClockRate y| := by
        have Htri (a b c : ℝ) : |a + b - c| ≤ |a| + |b| + |c| :=
          (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        have ht := Htri ((entranceStableRadius y * Q (Pi.single 0 1) - entranceClockRate y) / entranceClockRate y ^ 2)
            (E (Pi.single 0 1) / (entranceStableRadius y * entranceClockRate y))
            (entranceStrongRemainder y / (entranceStableRadius y * entranceClockRate y) *
              (1 / entranceStableRadius y + Q (Pi.single 0 1) / entranceClockRate y))
        rw [abs_div (entranceStableRadius y * Q (Pi.single 0 1) - entranceClockRate y) (entranceClockRate y ^ 2),
          abs_of_nonneg (sq_nonneg (entranceClockRate y))] at ht
        simpa only [abs_div, abs_of_pos (mul_pos hr0 hD0), abs_mul] using ht
      _ ≤ (3 * K) / (k ^ 2 / 4) + (16 * C / k) / (k ^ 2 / 4) + (8 * C / k ^ 2) * (18 / k) :=
        add_le_add (add_le_add (div_le_div₀ (by positivity) hcancel (by positivity) hDsq)
          (div_le_div₀ (by positivity) hErcoarse (by positivity) hden))
          (mul_le_mul hquot hlog (abs_nonneg _) (by positivity))
      _ = 12 * K / k ^ 2 + 208 * C / k ^ 3 := by ring
      _ ≤ 12 * K / k ^ 2 + 208 * C / k ^ 2 := add_le_add le_rfl
        (div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ hk1 (by norm_num : 2 ≤ 3)))
      _ = _ := by ring
  dsimp only
  refine ⟨hvalue.trans (by linarith only [hC, hK]), hderiv.trans ?_, hEr.trans ?_⟩
  · exact div_le_div_of_nonneg_right (by linarith only [hC, hK]) (sq_nonneg k)
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by linarith only [hC, hK] : 8 * C ≤ 256 * (C + K + 1)) hs) hk0.le

end BianchiIX
