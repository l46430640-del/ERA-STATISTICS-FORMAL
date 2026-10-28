import BianchiIX.Dynamics.EntranceWeakExpansion

noncomputable section

namespace BianchiIX

set_option maxHeartbeats 600000 in
/-- The nonlinear error in the weak numerator has fourth amplitude order, including its phase derivative. -/
theorem exists_entranceWeakRemainder_bounds :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y →
      let b := y 1 + y 3
      let L := fderiv ℝ entranceWeakRemainder y
      |entranceWeakRemainder y| + |L (Pi.single 0 1)| ≤ C * b ^ 4 / k ^ 2 ∧
      |L (Pi.single 1 1)| + |L (Pi.single 3 1)| ≤ C * b ^ 3 / k ^ 2 := by
  obtain ⟨R, hR, HR⟩ := exists_entranceQuarticRemainder_bounds
  obtain ⟨P, hP, HP⟩ := exists_entranceProjection_estimates
  refine ⟨10 * (R + P ^ 2 + 1), by positivity, ?_⟩
  intro k y hk hy
  let b := y 1 + y 3
  have hb : 0 ≤ b := add_nonneg hy.2.2.1.1 hy.2.2.2.2.1
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hm : 2 ≤ y 0 := by linarith [(entranceRegion_phase hk hy).1]
  have hm0 : 0 ≤ y 0 - 1 := by linarith
  have hm2 : y 0 - 1 ≤ 2 * k := by linarith [(entranceRegion_phase hk hy).2]
  have hu : |y 1| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.1.1]; linarith [hy.2.2.1.2]
  have hw : |y 3| < 1 / 200 := by rw [abs_of_nonneg hy.2.2.2.2.1]; linarith [hy.2.2.2.2.2]
  obtain ⟨hval, hM, hU, hW, hMM, hMU, hMW⟩ := HR k y hk hy
  obtain ⟨hQ, hQM, hQU, hQW, hQMM, hQMU, hQMW⟩ := HP k y hk hy
  have hscale (a : ℝ) (ha : 0 ≤ a) (n : ℕ) (hn : 2 ≤ n) : a / k ^ n ≤ a / k ^ 2 :=
    div_le_div_of_nonneg_left ha (by positivity) (pow_le_pow_right₀ hk1 hn)
  have hphase (a : ℝ) (n : ℕ) (ha : |a| ≤ R * b ^ n / k ^ 3) :
      |(y 0 - 1) * a| ≤ 2 * R * b ^ n / k ^ 2 := by
    rw [abs_mul, abs_of_nonneg hm0]
    calc
      _ ≤ (2 * k) * (R * b ^ n / k ^ 3) := mul_le_mul hm2 ha (abs_nonneg _) (by positivity)
      _ = _ := by field_simp
  have hproduct (a c : ℝ) (p q n m : ℕ) (hn : 2 ≤ n + m)
      (ha : |a| ≤ P * b ^ p / k ^ n) (hc : |c| ≤ P * b ^ q / k ^ m) :
      |a * c| ≤ P ^ 2 * b ^ (p + q) / k ^ 2 := by
    rw [abs_mul]
    calc
      _ ≤ (P * b ^ p / k ^ n) * (P * b ^ q / k ^ m) := mul_le_mul ha hc (abs_nonneg _) (by positivity)
      _ = P ^ 2 * b ^ (p + q) / k ^ (n + m) := by rw [pow_add, pow_add]; ring
      _ ≤ _ := hscale _ (by positivity) _ hn
  have hQ' : |entranceStablePhase y - y 0| ≤ P * b ^ 2 / k ^ 1 := by simpa using hQ
  have hprod0 := hproduct _ _ 2 2 1 2 (by norm_num) hQ' hQM
  have hprod1 := hproduct _ _ 2 2 2 2 (by norm_num) hQM hQM
  have hprod2 := hproduct _ _ 2 2 1 3 (by norm_num) hQ' hQMM
  have hneg3 (a c d : ℝ) : |-a - c - d| ≤ |a| + |c| + |d| := by
    simpa only [abs_neg] using (abs_sub (-a - c) d).trans (add_le_add (abs_sub (-a) c) le_rfl)
  have hE : |entranceWeakRemainder y| ≤ (3 * R + P ^ 2) * b ^ 4 / k ^ 2 := by
    unfold entranceWeakRemainder
    calc
      _ ≤ |entranceQuarticRemainder y| + |(y 0 - 1) * fderiv ℝ entranceQuarticRemainder y (Pi.single 0 1)| +
          |(entranceStablePhase y - y 0) * (entranceStablePartial y 0 - 1)| := hneg3 _ _ _
      _ ≤ R * b ^ 4 / k ^ 2 + 2 * R * b ^ 4 / k ^ 2 + P ^ 2 * b ^ 4 / k ^ 2 :=
        add_le_add (add_le_add (hval.trans (hscale _ (by positivity) 3 (by norm_num))) (hphase _ 4 hM)) hprod0
      _ = _ := by ring
  have hd := (entranceWeakRemainder_differential hm hu hw).2
  have hEM : |fderiv ℝ entranceWeakRemainder y (Pi.single 0 1)| ≤ (4 * R + 2 * P ^ 2) * b ^ 4 / k ^ 2 := by
    have heq : fderiv ℝ entranceWeakRemainder y (Pi.single 0 1) =
        -fderiv ℝ entranceQuarticRemainder y (Pi.single 0 1) - fderiv ℝ entranceQuarticRemainder y (Pi.single 0 1) -
        (y 0 - 1) * fderiv ℝ (fderiv ℝ entranceQuarticRemainder) y (Pi.single 0 1) (Pi.single 0 1) -
        (entranceStablePartial y 0 - 1) * (entranceStablePartial y 0 - 1) -
        (entranceStablePhase y - y 0) * fderiv ℝ (fderiv ℝ entranceStablePhase) y (Pi.single 0 1) (Pi.single 0 1) := by
      rw [hd]
      simp [entranceStablePartial]
    rw [heq]
    calc
      _ ≤ |fderiv ℝ entranceQuarticRemainder y (Pi.single 0 1)| + |fderiv ℝ entranceQuarticRemainder y (Pi.single 0 1)| +
          |(y 0 - 1) * fderiv ℝ (fderiv ℝ entranceQuarticRemainder) y (Pi.single 0 1) (Pi.single 0 1)| +
          |(entranceStablePartial y 0 - 1) * (entranceStablePartial y 0 - 1)| +
          |(entranceStablePhase y - y 0) * fderiv ℝ (fderiv ℝ entranceStablePhase) y (Pi.single 0 1) (Pi.single 0 1)| := by
        refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
        exact (abs_sub _ _).trans (add_le_add (hneg3 _ _ _) le_rfl)
      _ ≤ R * b ^ 4 / k ^ 2 + R * b ^ 4 / k ^ 2 + 2 * R * b ^ 4 / k ^ 2 +
          P ^ 2 * b ^ 4 / k ^ 2 + P ^ 2 * b ^ 4 / k ^ 2 :=
        add_le_add (add_le_add (add_le_add (add_le_add (hM.trans (hscale _ (by positivity) 3 (by norm_num)))
          (hM.trans (hscale _ (by positivity) 3 (by norm_num)))) (hphase _ 4 hMM)) hprod1) hprod2
      _ = _ := by ring
  have hwall (i : Fin 4) (hi : i ≠ 0)
      (hRi : |fderiv ℝ entranceQuarticRemainder y (Pi.single i 1)| ≤ R * b ^ 3 / k ^ 3)
      (hRMi : |fderiv ℝ (fderiv ℝ entranceQuarticRemainder) y (Pi.single i 1) (Pi.single 0 1)| ≤ R * b ^ 3 / k ^ 3)
      (hPi : |entranceStablePartial y i| ≤ P * b / k)
      (hPMi : |fderiv ℝ (fderiv ℝ entranceStablePhase) y (Pi.single i 1) (Pi.single 0 1)| ≤ P * b / k ^ 2) :
      |fderiv ℝ entranceWeakRemainder y (Pi.single i 1)| ≤ (3 * R + 2 * P ^ 2) * b ^ 3 / k ^ 2 := by
    have heq : fderiv ℝ entranceWeakRemainder y (Pi.single i 1) =
        -fderiv ℝ entranceQuarticRemainder y (Pi.single i 1) -
        (y 0 - 1) * fderiv ℝ (fderiv ℝ entranceQuarticRemainder) y (Pi.single i 1) (Pi.single 0 1) -
        entranceStablePartial y i * (entranceStablePartial y 0 - 1) -
        (entranceStablePhase y - y 0) * fderiv ℝ (fderiv ℝ entranceStablePhase) y (Pi.single i 1) (Pi.single 0 1) := by
      rw [hd]
      simp [entranceStablePartial, Ne.symm hi]
    have hpi' : |entranceStablePartial y i| ≤ P * b ^ 1 / k ^ 1 := by simpa using hPi
    have hpmi' : |fderiv ℝ (fderiv ℝ entranceStablePhase) y (Pi.single i 1) (Pi.single 0 1)| ≤ P * b ^ 1 / k ^ 2 := by simpa using hPMi
    have hp1 := hproduct _ _ 1 2 1 2 (by norm_num) hpi' hQM
    have hp2 := hproduct _ _ 2 1 1 2 (by norm_num) hQ' hpmi'
    rw [heq]
    calc
      _ ≤ |fderiv ℝ entranceQuarticRemainder y (Pi.single i 1)| +
          |(y 0 - 1) * fderiv ℝ (fderiv ℝ entranceQuarticRemainder) y (Pi.single i 1) (Pi.single 0 1)| +
          |entranceStablePartial y i * (entranceStablePartial y 0 - 1)| +
          |(entranceStablePhase y - y 0) * fderiv ℝ (fderiv ℝ entranceStablePhase) y (Pi.single i 1) (Pi.single 0 1)| := by
        exact (abs_sub _ _).trans (add_le_add (hneg3 _ _ _) le_rfl)
      _ ≤ R * b ^ 3 / k ^ 2 + 2 * R * b ^ 3 / k ^ 2 + P ^ 2 * b ^ 3 / k ^ 2 + P ^ 2 * b ^ 3 / k ^ 2 :=
        add_le_add (add_le_add (add_le_add (hRi.trans (hscale _ (by positivity) 3 (by norm_num))) (hphase _ 3 hRMi)) hp1) hp2
      _ = _ := by ring
  have hEU := hwall 1 (by decide) hU hMU hQU hQMU
  have hEW := hwall 3 (by decide) hW hMW hQW hQMW
  constructor
  · calc
      _ ≤ (3 * R + P ^ 2) * b ^ 4 / k ^ 2 + (4 * R + 2 * P ^ 2) * b ^ 4 / k ^ 2 := add_le_add hE hEM
      _ = (7 * R + 3 * P ^ 2) * b ^ 4 / k ^ 2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by nlinarith only [hR, sq_nonneg P]) (by positivity)) (sq_nonneg k)
  · calc
      _ ≤ (3 * R + 2 * P ^ 2) * b ^ 3 / k ^ 2 + (3 * R + 2 * P ^ 2) * b ^ 3 / k ^ 2 := add_le_add hEU hEW
      _ = (6 * R + 4 * P ^ 2) * b ^ 3 / k ^ 2 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by nlinarith only [hR, sq_nonneg P]) (by positivity)) (sq_nonneg k)

end BianchiIX
