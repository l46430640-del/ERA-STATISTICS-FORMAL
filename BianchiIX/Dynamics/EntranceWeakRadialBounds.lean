import BianchiIX.Dynamics.EntranceWeakNumeratorBounds
import BianchiIX.Dynamics.EntranceRadialQuotient

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

theorem EntranceRadialInverseAt.weak_differential {y : ProjectiveState} {k : ℝ}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) (v : ProjectiveState) :
    fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z)) (entranceRadialCoordinates y) v =
      fderiv ℝ (fun z => entranceWeakNumerator (Ψ z)) (entranceRadialCoordinates y) v /
        (entranceStableRadius y * entranceClockRate y) - entranceRadialWeakCoefficient y *
        (v 0 / entranceStableRadius y +
          fderiv ℝ (fun z => entranceClockRate (Ψ z)) (entranceRadialCoordinates y) v / entranceClockRate y) := by
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  exact H.radial_quotient_differential
    ((contDiffAt_entranceWeakNumerator_one hm hu hw).differentiableAt (by norm_num))
    (entranceStableRadius_pos hv).ne' (entranceRegion_clock_pos hk hy).ne' v

set_option maxHeartbeats 600000 in
/-- The value and the three derivative estimates for B in equation (C.20). -/
theorem exists_entranceRadialWeakCoefficient_bounds :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y → 0 < y 2 →
      ∀ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ →
        let b := y 1 + y 3
        let z := entranceRadialCoordinates y
        let L := fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z)) z
        |entranceRadialWeakCoefficient y| ≤ C * b ^ 2 / k ^ 2 ∧
        |L (Pi.single 0 1)| ≤ C * b ^ 2 / k ^ 3 ∧
        |L (Pi.single 1 1)| + |L (Pi.single 3 1)| ≤ C * b / k ^ 2 := by
  obtain ⟨A, hA, HA⟩ := exists_entranceWeakNumerator_bounds
  obtain ⟨J, hJ, HJ⟩ := exists_entranceRadialInverse_column_bounds
  refine ⟨128 * A * (J + 4), by positivity, ?_⟩
  intro k y hk hy hv Ψ H
  let b := y 1 + y 3
  let z := entranceRadialCoordinates y
  let N := fderiv ℝ (fun z => entranceWeakNumerator (Ψ z)) z
  let Q := fderiv ℝ (fun z => entranceClockRate (Ψ z)) z
  have hb : 0 ≤ b := add_nonneg hy.2.2.1.1 hy.2.2.2.2.1
  have hb1 : b ≤ 1 := by dsimp [b]; linarith [hy.2.2.1.2, hy.2.2.2.2.2]
  have hb2 : b ^ 2 ≤ b := by nlinarith
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hk2 : 1 ≤ k ^ 2 := one_le_pow₀ hk1
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  obtain ⟨hn, hnM, hnU, hnW⟩ := HA k y hk hy
  obtain ⟨hMr, hMU, _, hMW⟩ := HJ k y hk hy hv Ψ H
  obtain ⟨_, hr, _⟩ := entranceRegion_stable_radial_bounds hk hy
  have hD := entranceRegion_speed hk hy
  have hr0 := entranceStableRadius_pos hv
  have hD0 := entranceRegion_clock_pos hk hy
  have hden : k ^ 2 / 4 ≤ entranceStableRadius y * entranceClockRate y := by
    have Hp := mul_le_mul hr.1 (show k / 2 ≤ entranceClockRate y by linarith [hD.1]) (by positivity) hr0.le
    nlinarith only [Hp]
  have hnreg := (contDiffAt_entranceWeakNumerator_one hm hu hw).differentiableAt (by norm_num)
  obtain ⟨n0, n1, _, n3⟩ := H.scalar_partials hnreg
  obtain ⟨m0, m1, _, m3⟩ := H.phase_partials
  obtain ⟨q0, q1, _, q3⟩ := H.clock_partials
  rw [m0] at hMr
  rw [m1, abs_div, abs_neg, ← abs_div] at hMU
  rw [m3, abs_div, abs_neg, ← abs_div] at hMW
  have hJsmall : J * b / k ≤ J :=
    (div_le_self (mul_nonneg hJ.le hb) hk1).trans (by nlinarith only [hb1, hJ])
  have hnMsmall : |fderiv ℝ entranceWeakNumerator y (Pi.single 0 1)| ≤ A * b :=
    hnM.trans ((div_le_self (by positivity) hk2).trans (mul_le_mul_of_nonneg_left hb2 hA.le))
  have hNr : |N (Pi.single 0 1)| ≤ 8 * A * b ^ 2 / k ^ 2 := by
    dsimp only [N, z]
    rw [n0, abs_mul, abs_of_nonneg (by linarith [hMr.1])]
    calc
      _ ≤ 8 * (A * b ^ 2 / k ^ 2) := mul_le_mul hMr.2 hnM (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have hNwall (a t : ℝ) (ha : |a| ≤ A * b) (ht : |t| ≤ J * b / k) :
      |a - t * fderiv ℝ entranceWeakNumerator y (Pi.single 0 1)| ≤ A * (1 + J) * b := by
    calc
      _ ≤ |a| + |t| * |fderiv ℝ entranceWeakNumerator y (Pi.single 0 1)| := by
        simpa only [abs_mul] using abs_sub a (t * fderiv ℝ entranceWeakNumerator y (Pi.single 0 1))
      _ ≤ A * b + J * (A * b) := add_le_add ha (mul_le_mul (ht.trans hJsmall) hnMsmall (abs_nonneg _) hJ.le)
      _ = _ := by ring
  have hNu : |N (Pi.single 1 1)| ≤ A * (1 + J) * b := by
    dsimp only [N, z]; rw [n1]; exact hNwall _ _ hnU hMU
  have hNw : |N (Pi.single 3 1)| ≤ A * (1 + J) * b := by
    dsimp only [N, z]; rw [n3]; exact hNwall _ _ hnW hMW
  have hQr : |Q (Pi.single 0 1)| ≤ 8 := by
    dsimp only [Q, z]; rw [q0, abs_of_nonneg (by linarith [hMr.1])]; exact hMr.2
  have hQwall (a t : ℝ) (ha : |a| ≤ J * b / k) (ht : |t| ≤ 3) : |(-a) - t| ≤ J + 3 := by
    calc
      _ ≤ |a| + |t| := by simpa only [abs_neg] using abs_sub (-a) t
      _ ≤ J + 3 := add_le_add (ha.trans hJsmall) ht
  have hQu : |Q (Pi.single 1 1)| ≤ J + 3 := by
    dsimp only [Q, z]; rw [q1, neg_div]
    exact hQwall _ _ hMU (abs_le.mpr ⟨by linarith [hy.2.2.1.1, hy.2.2.1.2, hy.2.2.2.1.1, hy.2.2.2.2.1],
      by linarith [hy.2.2.1.1, hy.2.2.2.1.2, hy.2.2.2.2.2]⟩)
  have hQw : |Q (Pi.single 3 1)| ≤ J + 3 := by
    dsimp only [Q, z]; rw [q3, neg_div]
    exact hQwall _ _ hMW (by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2])
  have hB : |entranceRadialWeakCoefficient y| ≤ 4 * A * b ^ 2 / k ^ 2 := by
    rw [entranceRadialWeakCoefficient, abs_div, abs_of_pos (mul_pos hr0 hD0)]
    calc
      _ ≤ (A * b ^ 2) / (k ^ 2 / 4) := div_le_div₀ (by positivity) hn (by positivity) hden
      _ = _ := by ring
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
  have hBR : |fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z)) z (Pi.single 0 1)| ≤
      104 * A * b ^ 2 / k ^ 3 := by
    rw [H.weak_differential hk hy hv]
    change |N (Pi.single 0 1) / (entranceStableRadius y * entranceClockRate y) -
      entranceRadialWeakCoefficient y * (1 / entranceStableRadius y + Q (Pi.single 0 1) / entranceClockRate y)| ≤ _
    calc
      _ ≤ |N (Pi.single 0 1)| / (entranceStableRadius y * entranceClockRate y) +
          |entranceRadialWeakCoefficient y| * |1 / entranceStableRadius y + Q (Pi.single 0 1) / entranceClockRate y| := by
        simpa only [abs_div, abs_of_pos (mul_pos hr0 hD0), abs_mul] using abs_sub
          (N (Pi.single 0 1) / (entranceStableRadius y * entranceClockRate y))
          (entranceRadialWeakCoefficient y * (1 / entranceStableRadius y + Q (Pi.single 0 1) / entranceClockRate y))
      _ ≤ (8 * A * b ^ 2 / k ^ 2) / (k ^ 2 / 4) + (4 * A * b ^ 2 / k ^ 2) * (18 / k) :=
        add_le_add (div_le_div₀ (by positivity) hNr (by positivity) hden)
          (mul_le_mul hB hlogR (abs_nonneg _) (by positivity))
      _ = 32 * A * b ^ 2 / k ^ 4 + 72 * A * b ^ 2 / k ^ 3 := by ring
      _ ≤ 32 * A * b ^ 2 / k ^ 3 + 72 * A * b ^ 2 / k ^ 3 := add_le_add
        (div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ hk1 (by norm_num : 3 ≤ 4))) le_rfl
      _ = _ := by ring
  have hBW (i : Fin 4) (hi : i ≠ 0) (hn' : |N (Pi.single i 1)| ≤ A * (1 + J) * b)
      (hd' : |Q (Pi.single i 1)| ≤ J + 3) :
      |fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z)) z (Pi.single i 1)| ≤
        A * (12 * J + 28) * b / k ^ 2 := by
    rw [H.weak_differential hk hy hv]
    simp only [Pi.single_eq_of_ne hi.symm, zero_div, zero_add]
    change |N (Pi.single i 1) / (entranceStableRadius y * entranceClockRate y) -
      entranceRadialWeakCoefficient y * (Q (Pi.single i 1) / entranceClockRate y)| ≤ _
    have hquot : |Q (Pi.single i 1) / entranceClockRate y| ≤ 2 * (J + 3) / k := by
      rw [abs_div, abs_of_pos hD0]
      exact (div_le_div_of_nonneg_right hd' hD0.le).trans (hdivD _ (by positivity))
    calc
      _ ≤ |N (Pi.single i 1)| / (entranceStableRadius y * entranceClockRate y) +
          |entranceRadialWeakCoefficient y| * |Q (Pi.single i 1) / entranceClockRate y| := by
        simpa only [abs_div, abs_of_pos (mul_pos hr0 hD0), abs_mul] using abs_sub
          (N (Pi.single i 1) / (entranceStableRadius y * entranceClockRate y))
          (entranceRadialWeakCoefficient y * (Q (Pi.single i 1) / entranceClockRate y))
      _ ≤ (A * (1 + J) * b) / (k ^ 2 / 4) + (4 * A * b ^ 2 / k ^ 2) * (2 * (J + 3) / k) :=
        add_le_add (div_le_div₀ (by positivity) hn' (by positivity) hden)
          (mul_le_mul hB hquot (abs_nonneg _) (by positivity))
      _ = 4 * A * (1 + J) * b / k ^ 2 + (8 * A * (J + 3)) * (b ^ 2 / k) / k ^ 2 := by ring
      _ ≤ 4 * A * (1 + J) * b / k ^ 2 + (8 * A * (J + 3)) * b / k ^ 2 := add_le_add le_rfl
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          ((div_le_self (sq_nonneg b) hk1).trans hb2) (by positivity)) (sq_nonneg k))
      _ = _ := by ring
  dsimp only
  refine ⟨hB.trans ?_, hBR.trans ?_, (add_le_add (hBW 1 (by decide) hNu hQu) (hBW 3 (by decide) hNw hQw)).trans ?_⟩
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by nlinarith only [hA, mul_pos hA hJ] : 4 * A ≤ 128 * A * (J + 4)) (sq_nonneg b)) (sq_nonneg k)
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by nlinarith only [hA, mul_pos hA hJ] : 104 * A ≤ 128 * A * (J + 4)) (sq_nonneg b)) (by positivity)
  · rw [← add_div]
    apply div_le_div_of_nonneg_right _ (sq_nonneg k)
    have hc : 2 * (A * (12 * J + 28)) ≤ 128 * A * (J + 4) := by
      nlinarith only [hA, mul_pos hA hJ]
    convert! mul_le_mul_of_nonneg_right hc hb using 1
    ring

end BianchiIX
