import BianchiIX.Dynamics.EntranceWeakRefinedBounds
import BianchiIX.Dynamics.EntranceWeakRadialBounds

noncomputable section

namespace BianchiIX

set_option maxHeartbeats 700000 in
/-- All four strengthened weak coefficient bounds in (C.23), in the actual radial coordinates. -/
theorem exists_entranceRadialWeakCoefficient_refined_bounds :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y →
      k * (y 1 + y 3) ^ 2 ≤ 1 → 0 < y 2 →
      ∀ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ →
        let b := y 1 + y 3
        let L := fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z)) (entranceRadialCoordinates y)
        |entranceRadialWeakCoefficient y| ≤ C * (y 1 * b / k ^ 2 + y 3 ^ 2 / k ^ 4) ∧
        |L (Pi.single 0 1)| ≤ C * (y 1 * b / k ^ 3 + y 3 ^ 2 / k ^ 5) ∧
        |L (Pi.single 1 1)| ≤ C * b / k ^ 2 ∧
        |L (Pi.single 3 1)| ≤ C * (y 1 / k ^ 2 + y 3 / k ^ 4) := by
  obtain ⟨A, hA, HA⟩ := exists_entranceWeakNumerator_refined_bounds
  obtain ⟨J, hJ, HJ⟩ := exists_entranceRadialInverse_column_bounds
  obtain ⟨T, hT, HT⟩ := exists_entranceRadialWeakCoefficient_bounds
  refine ⟨200 * A * (J + 4) + T, by positivity, ?_⟩
  intro k y hk hy hsmall hv Ψ H
  let b := y 1 + y 3
  let z := entranceRadialCoordinates y
  let N := fderiv ℝ (fun z => entranceWeakNumerator (Ψ z)) z
  let Q := fderiv ℝ (fun z => entranceClockRate (Ψ z)) z
  have hu0 := hy.2.2.1.1
  have hw0 := hy.2.2.2.2.1
  have hw1 : y 3 ≤ 1 := by linarith [hy.2.2.2.2.2]
  have hw2 : y 3 ^ 2 ≤ y 3 := by nlinarith only [hw0, hw1]
  have hb : 0 ≤ b := add_nonneg hu0 hw0
  have hb1 : b ≤ 1 := by dsimp [b]; linarith [hy.2.2.1.2, hy.2.2.2.2.2]
  have hb2 : b ^ 2 ≤ b := by nlinarith only [hb, hb1]
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hk2 : 1 ≤ k ^ 2 := one_le_pow₀ hk1
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hu0]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hw0]; linarith [hy.2.2.2.2.2]
  obtain ⟨hn, hnM, _, hnW⟩ := HA k y hk hy hsmall
  obtain ⟨hMr, _, _, hMW⟩ := HJ k y hk hy hv Ψ H
  obtain ⟨_, hr, _⟩ := entranceRegion_stable_radial_bounds hk hy
  have hD := entranceRegion_speed hk hy
  have hr0 := entranceStableRadius_pos hv
  have hD0 := entranceRegion_clock_pos hk hy
  have hden : k ^ 2 / 4 ≤ entranceStableRadius y * entranceClockRate y := by
    have Hp := mul_le_mul hr.1 (show k / 2 ≤ entranceClockRate y by linarith [hD.1]) (by positivity) hr0.le
    nlinarith only [Hp]
  have hnreg := (contDiffAt_entranceWeakNumerator_one hm hu hw).differentiableAt (by norm_num)
  obtain ⟨n0, _, _, n3⟩ := H.scalar_partials hnreg
  obtain ⟨m0, _, _, m3⟩ := H.phase_partials
  obtain ⟨q0, _, _, q3⟩ := H.clock_partials
  rw [m0] at hMr
  rw [m3, abs_div, abs_neg, ← abs_div] at hMW
  have hJsmall : J * b / k ≤ J :=
    (div_le_self (by positivity) hk1).trans (by nlinarith only [hb1, hJ])
  have hnMsmall : |fderiv ℝ entranceWeakNumerator y (Pi.single 0 1)| ≤ A * (y 1 + y 3 / k ^ 2) := by
    calc
      _ ≤ A * b ^ 2 / k ^ 3 := hnM
      _ ≤ A * b ^ 2 / k ^ 2 := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ hk1 (by norm_num : 2 ≤ 3))
      _ ≤ A * b / k ^ 2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb2 hA.le) (sq_nonneg k)
      _ = A * (y 1 / k ^ 2 + y 3 / k ^ 2) := by dsimp [b]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (div_le_self hu0 hk2) le_rfl) hA.le
  have hNr : |N (Pi.single 0 1)| ≤ 8 * A * b ^ 2 / k ^ 3 := by
    dsimp only [N, z]
    rw [n0, abs_mul, abs_of_nonneg (by linarith [hMr.1])]
    exact (mul_le_mul hMr.2 hnM (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  have hNw : |N (Pi.single 3 1)| ≤ A * (1 + J) * (y 1 + y 3 / k ^ 2) := by
    dsimp only [N, z]
    rw [n3]
    calc
      _ ≤ |fderiv ℝ entranceWeakNumerator y (Pi.single 3 1)| +
          |entranceStablePartial y 3 / entranceStablePartial y 0| * |fderiv ℝ entranceWeakNumerator y (Pi.single 0 1)| := by
        simpa only [abs_mul] using abs_sub (fderiv ℝ entranceWeakNumerator y (Pi.single 3 1))
          (entranceStablePartial y 3 / entranceStablePartial y 0 * fderiv ℝ entranceWeakNumerator y (Pi.single 0 1))
      _ ≤ A * (y 1 + y 3 / k ^ 2) + J * (A * (y 1 + y 3 / k ^ 2)) :=
        add_le_add hnW (mul_le_mul (hMW.trans hJsmall) hnMsmall (abs_nonneg _) hJ.le)
      _ = _ := by ring
  have hQr : |Q (Pi.single 0 1)| ≤ 8 := by
    dsimp only [Q, z]; rw [q0, abs_of_nonneg (by linarith [hMr.1])]; exact hMr.2
  have hQw : |Q (Pi.single 3 1)| ≤ J + 3 := by
    dsimp only [Q, z]; rw [q3, neg_div]
    calc
      _ ≤ |entranceStablePartial y 3 / entranceStablePartial y 0| + |y 1| := by
        simpa only [abs_neg] using abs_sub (-(entranceStablePartial y 3 / entranceStablePartial y 0)) (y 1)
      _ ≤ _ := add_le_add (hMW.trans hJsmall) (by rw [abs_of_nonneg hu0]; linarith [hy.2.2.1.2])
  have hB : |entranceRadialWeakCoefficient y| ≤ 4 * A * (y 1 * b / k ^ 2 + y 3 ^ 2 / k ^ 4) := by
    rw [entranceRadialWeakCoefficient, abs_div, abs_of_pos (mul_pos hr0 hD0)]
    calc
      _ ≤ (A * (y 1 * b + y 3 ^ 2 / k ^ 2)) / (k ^ 2 / 4) := div_le_div₀ (by positivity) hn (by positivity) hden
      _ = _ := by ring
  have hBsmall : |entranceRadialWeakCoefficient y| ≤ 4 * A * (y 1 / k ^ 2 + y 3 / k ^ 4) :=
    hB.trans (mul_le_mul_of_nonneg_left (add_le_add
      (div_le_div_of_nonneg_right (mul_le_of_le_one_right hu0 hb1) (sq_nonneg k))
      (div_le_div_of_nonneg_right hw2 (by positivity))) (by positivity))
  have hdivD (a : ℝ) (ha : 0 ≤ a) : a / entranceClockRate y ≤ 2 * a / k := by
    calc
      _ ≤ a / (k / 2) := div_le_div_of_nonneg_left ha (by positivity) (by linarith [hD.1])
      _ = _ := by ring
  have hlogR : |1 / entranceStableRadius y + Q (Pi.single 0 1) / entranceClockRate y| ≤ 18 / k := by
    calc
      _ ≤ 1 / entranceStableRadius y + |Q (Pi.single 0 1)| / entranceClockRate y := by
        simpa only [abs_div, abs_one, abs_of_pos hr0, abs_of_pos hD0] using
          abs_add_le (1 / entranceStableRadius y) (Q (Pi.single 0 1) / entranceClockRate y)
      _ ≤ 1 / (k / 2) + 2 * 8 / k := add_le_add
        (div_le_div_of_nonneg_left (by norm_num) (by positivity) hr.1)
        ((div_le_div_of_nonneg_right hQr hD0.le).trans (hdivD 8 (by norm_num)))
      _ = _ := by ring
  have hsplit : b ^ 2 / k ^ 5 ≤ 2 * (y 1 * b / k ^ 3 + y 3 ^ 2 / k ^ 5) := by
    have hbq : b ^ 2 ≤ 2 * y 1 * b + y 3 ^ 2 := by dsimp [b]; nlinarith only [sq_nonneg (y 1)]
    calc
      _ ≤ (2 * y 1 * b + y 3 ^ 2) / k ^ 5 := div_le_div_of_nonneg_right hbq (by positivity)
      _ = (2 * y 1 * b) / k ^ 5 + y 3 ^ 2 / k ^ 5 := by ring
      _ ≤ (2 * y 1 * b) / k ^ 3 + y 3 ^ 2 / k ^ 5 := add_le_add
        (div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ hk1 (by norm_num : 3 ≤ 5))) le_rfl
      _ = 2 * (y 1 * b / k ^ 3) + y 3 ^ 2 / k ^ 5 := by ring
      _ ≤ _ := by linarith only [show 0 ≤ y 3 ^ 2 / k ^ 5 by positivity]
  have hBR : |fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z)) z (Pi.single 0 1)| ≤
      136 * A * (y 1 * b / k ^ 3 + y 3 ^ 2 / k ^ 5) := by
    rw [H.weak_differential hk hy hv]
    change |N (Pi.single 0 1) / (entranceStableRadius y * entranceClockRate y) - entranceRadialWeakCoefficient y *
      (1 / entranceStableRadius y + Q (Pi.single 0 1) / entranceClockRate y)| ≤ _
    calc
      _ ≤ |N (Pi.single 0 1)| / (entranceStableRadius y * entranceClockRate y) + |entranceRadialWeakCoefficient y| *
          |1 / entranceStableRadius y + Q (Pi.single 0 1) / entranceClockRate y| := by
        simpa only [abs_div, abs_of_pos (mul_pos hr0 hD0), abs_mul] using abs_sub
          (N (Pi.single 0 1) / (entranceStableRadius y * entranceClockRate y))
          (entranceRadialWeakCoefficient y * (1 / entranceStableRadius y + Q (Pi.single 0 1) / entranceClockRate y))
      _ ≤ (8 * A * b ^ 2 / k ^ 3) / (k ^ 2 / 4) +
          (4 * A * (y 1 * b / k ^ 2 + y 3 ^ 2 / k ^ 4)) * (18 / k) :=
        add_le_add (div_le_div₀ (by positivity) hNr (by positivity) hden)
          (mul_le_mul hB hlogR (abs_nonneg _) (by positivity))
      _ = 32 * A * (b ^ 2 / k ^ 5) + 72 * A * (y 1 * b / k ^ 3 + y 3 ^ 2 / k ^ 5) := by ring
      _ ≤ 32 * A * (2 * (y 1 * b / k ^ 3 + y 3 ^ 2 / k ^ 5)) + 72 * A * (y 1 * b / k ^ 3 + y 3 ^ 2 / k ^ 5) :=
        add_le_add (mul_le_mul_of_nonneg_left hsplit (by positivity)) le_rfl
      _ = _ := by ring
  have hBW : |fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z)) z (Pi.single 3 1)| ≤
      A * (12 * J + 28) * (y 1 / k ^ 2 + y 3 / k ^ 4) := by
    have hquot : |Q (Pi.single 3 1) / entranceClockRate y| ≤ 2 * (J + 3) := by
      rw [abs_div, abs_of_pos hD0]
      exact ((div_le_div_of_nonneg_right hQw hD0.le).trans (hdivD _ (by positivity))).trans (div_le_self (by positivity) hk1)
    rw [H.weak_differential hk hy hv]
    change |N (Pi.single 3 1) / (entranceStableRadius y * entranceClockRate y) -
      entranceRadialWeakCoefficient y * (0 / entranceStableRadius y + Q (Pi.single 3 1) / entranceClockRate y)| ≤ _
    rw [zero_div, zero_add]
    calc
      _ ≤ |N (Pi.single 3 1)| / (entranceStableRadius y * entranceClockRate y) +
          |entranceRadialWeakCoefficient y| * |Q (Pi.single 3 1) / entranceClockRate y| := by
        simpa only [abs_div, abs_of_pos (mul_pos hr0 hD0), abs_mul] using abs_sub
          (N (Pi.single 3 1) / (entranceStableRadius y * entranceClockRate y))
          (entranceRadialWeakCoefficient y * (Q (Pi.single 3 1) / entranceClockRate y))
      _ ≤ (A * (1 + J) * (y 1 + y 3 / k ^ 2)) / (k ^ 2 / 4) +
          (4 * A * (y 1 / k ^ 2 + y 3 / k ^ 4)) * (2 * (J + 3)) :=
        add_le_add (div_le_div₀ (by positivity) hNw (by positivity) hden)
          (mul_le_mul hBsmall hquot (abs_nonneg _) (by positivity))
      _ = _ := by ring
  have hBU : |fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z)) z (Pi.single 1 1)| ≤ T * b / k ^ 2 := by
    have hboth := (HT k y hk hy hv Ψ H).2.2
    linarith only [hboth, abs_nonneg (fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z)) z (Pi.single 3 1))]
  dsimp only
  refine ⟨hB.trans ?_, hBR.trans ?_, hBU.trans ?_, hBW.trans ?_⟩
  · apply mul_le_mul_of_nonneg_right _ (by positivity)
    nlinarith only [hA, hT, mul_pos hA hJ]
  · apply mul_le_mul_of_nonneg_right _ (by positivity)
    nlinarith only [hA, hT, mul_pos hA hJ]
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hb) (sq_nonneg k)
  · apply mul_le_mul_of_nonneg_right _ (by positivity)
    nlinarith only [hA, hT, mul_pos hA hJ]

end BianchiIX
