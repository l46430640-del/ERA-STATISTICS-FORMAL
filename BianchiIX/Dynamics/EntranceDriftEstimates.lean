import BianchiIX.Dynamics.EntranceDriftDifferential

noncomputable section

namespace BianchiIX

set_option maxHeartbeats 600000 in
/-- Equation (C.22), with weighted wall derivatives also defined on zero stable walls. -/
theorem exists_entranceRadialDrift_basic_bounds :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y → 0 < y 2 →
      ∀ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ →
        let LG := fderiv ℝ (fun z => entranceRadialDrift (Ψ z)) (entranceRadialCoordinates y)
        |entranceRadialDrift y| ≤ C * (y 1 * y 2 + y 2 ^ 2 * y 3 ^ 2 / k ^ 2) ∧
        |LG (Pi.single 0 1)| ≤ C * (y 1 * y 2 / k ^ 2 + y 2 ^ 2 * y 3 ^ 2 / k ^ 3) ∧
        |y 1 * LG (Pi.single 1 1)| ≤ C * (y 1 * y 2) ∧
        |y 3 * LG (Pi.single 3 1)| ≤ C * (y 1 * y 2 * y 3 + y 2 ^ 2 * y 3 ^ 2 / k ^ 2) := by
  obtain ⟨C, hC, HC⟩ := exists_entranceRadialCoefficient_bounds
  obtain ⟨R, hR, HR⟩ := exists_entranceRadialDrift_radial_bound
  refine ⟨4 * (C + R), by positivity, ?_⟩
  intro k y hk hy hv Ψ H
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hu0 := hy.2.2.1.1
  have hv0 := hy.2.2.2.1.1
  have hw0 := hy.2.2.2.2.1
  have hu1 : y 1 ≤ 1 := by linarith [hy.2.2.1.2]
  have hv1 := hy.2.2.2.1.2
  have hw1 : y 3 ≤ 1 := by linarith [hy.2.2.2.2.2]
  have hb0 : 0 ≤ y 1 + y 3 := add_nonneg hu0 hw0
  have hb1 : y 1 + y 3 ≤ 1 := by linarith [hy.2.2.1.2, hy.2.2.2.2.2]
  have huv : 0 ≤ y 1 * y 2 := mul_nonneg hu0 hv0
  have hV2 : y 2 ^ 2 ≤ y 2 := by nlinarith only [hv0, hv1]
  have hb2 : (y 1 + y 3) ^ 2 ≤ 3 * y 1 + y 3 ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hu1 hu0, mul_le_mul_of_nonneg_left hw1 hu0]
  have hsplit : y 2 ^ 2 * (y 1 + y 3) ^ 2 ≤ 3 * (y 1 * y 2) + y 2 ^ 2 * y 3 ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hb2 (sq_nonneg (y 2)),
      mul_le_mul_of_nonneg_left hV2 (show 0 ≤ 3 * y 1 by positivity)]
  have hsq1 : 1 ≤ k ^ 2 := one_le_pow₀ hk1
  have hden : k ^ 2 ≤ k ^ 3 := by
    nlinarith only [mul_le_mul_of_nonneg_left hk1 (sq_nonneg k)]
  have htail (n : ℕ) : 0 ≤ y 2 ^ 2 * y 3 ^ 2 / k ^ n := by positivity
  have hsplit2 : y 2 ^ 2 * (y 1 + y 3) ^ 2 / k ^ 2 ≤
      3 * (y 1 * y 2) + y 2 ^ 2 * y 3 ^ 2 / k ^ 2 := by
    calc
      _ ≤ (3 * (y 1 * y 2) + y 2 ^ 2 * y 3 ^ 2) / k ^ 2 := div_le_div_of_nonneg_right hsplit (sq_nonneg k)
      _ = 3 * (y 1 * y 2) / k ^ 2 + y 2 ^ 2 * y 3 ^ 2 / k ^ 2 := by ring
      _ ≤ _ := add_le_add (div_le_self (by positivity) hsq1) le_rfl
  have hsplit3 : y 2 ^ 2 * (y 1 + y 3) ^ 2 / k ^ 3 ≤
      3 * (y 1 * y 2 / k ^ 2) + y 2 ^ 2 * y 3 ^ 2 / k ^ 3 := by
    calc
      _ ≤ (3 * (y 1 * y 2) + y 2 ^ 2 * y 3 ^ 2) / k ^ 3 := div_le_div_of_nonneg_right hsplit (by positivity)
      _ = 3 * (y 1 * y 2) / k ^ 3 + y 2 ^ 2 * y 3 ^ 2 / k ^ 3 := by ring
      _ ≤ (3 * (y 1 * y 2)) / k ^ 2 + y 2 ^ 2 * y 3 ^ 2 / k ^ 3 :=
        add_le_add (div_le_div_of_nonneg_left (by positivity) (by positivity) hden) le_rfl
      _ = _ := by ring
  obtain ⟨hA, hB, _, hBw⟩ := HC k y hk hy hv Ψ H
  have hAval : |entranceRadialStrongCoefficient y| ≤ C := by
    linarith only [hA, norm_nonneg
      (fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) (entranceRadialCoordinates y))]
  have hAnorm : ‖fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) (entranceRadialCoordinates y)‖ ≤ C := by
    linarith only [hA, abs_nonneg (entranceRadialStrongCoefficient y)]
  have hAp (i : Fin 4) : |fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z))
      (entranceRadialCoordinates y) (Pi.single i 1)| ≤ C := by
    have Hp := ((fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z))
      (entranceRadialCoordinates y)).le_opNorm (Pi.single i 1)).trans
        (mul_le_mul_of_nonneg_right hAnorm (norm_nonneg _))
    simpa [Pi.norm_single] using Hp
  have hBu : |fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z))
      (entranceRadialCoordinates y) (Pi.single 1 1)| ≤ C * (y 1 + y 3) / k ^ 2 := by
    linarith only [hBw, abs_nonneg (fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z))
      (entranceRadialCoordinates y) (Pi.single 3 1))]
  have hBw' : |fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z))
      (entranceRadialCoordinates y) (Pi.single 3 1)| ≤ C * (y 1 + y 3) / k ^ 2 := by
    linarith only [hBw, abs_nonneg (fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z))
      (entranceRadialCoordinates y) (Pi.single 1 1))]
  have habs (c a : ℝ) (hc : 0 ≤ c) : |c * a| = c * |a| := by rw [abs_mul, abs_of_nonneg hc]
  have hG : |entranceRadialDrift y| ≤ 4 * C * (y 1 * y 2 + y 2 ^ 2 * y 3 ^ 2 / k ^ 2) := by
    calc
      _ ≤ y 1 * y 2 * |entranceRadialStrongCoefficient y| + y 2 ^ 2 * |entranceRadialWeakCoefficient y| := by
        unfold entranceRadialDrift
        exact (abs_add_le _ _).trans (add_le_add (le_of_eq (habs _ _ huv)) (le_of_eq (habs _ _ (sq_nonneg _))))
      _ ≤ y 1 * y 2 * C + y 2 ^ 2 * (C * (y 1 + y 3) ^ 2 / k ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hAval huv) (mul_le_mul_of_nonneg_left hB (sq_nonneg _))
      _ = C * (y 1 * y 2 + y 2 ^ 2 * (y 1 + y 3) ^ 2 / k ^ 2) := by ring
      _ ≤ C * (y 1 * y 2 + (3 * (y 1 * y 2) + y 2 ^ 2 * y 3 ^ 2 / k ^ 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hsplit2) hC.le
      _ ≤ _ := by nlinarith only [mul_nonneg hC.le (htail 2)]
  have hGr : |fderiv ℝ (fun z => entranceRadialDrift (Ψ z)) (entranceRadialCoordinates y) (Pi.single 0 1)| ≤
      4 * R * (y 1 * y 2 / k ^ 2 + y 2 ^ 2 * y 3 ^ 2 / k ^ 3) := by
    calc
      _ ≤ R * (y 1 * y 2 / k ^ 2 + y 2 ^ 2 * (y 1 + y 3) ^ 2 / k ^ 3) := HR k y hk hy hv Ψ H
      _ ≤ R * (y 1 * y 2 / k ^ 2 + (3 * (y 1 * y 2 / k ^ 2) + y 2 ^ 2 * y 3 ^ 2 / k ^ 3)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hsplit3) hR.le
      _ ≤ _ := by nlinarith only [mul_nonneg hR.le (htail 3)]
  have hGu : |y 1 * fderiv ℝ (fun z => entranceRadialDrift (Ψ z)) (entranceRadialCoordinates y) (Pi.single 1 1)| ≤
      3 * C * (y 1 * y 2) := by
    have hterm : y 2 ^ 2 * (y 1 + y 3) / k ^ 2 ≤ y 2 :=
      (div_le_self (by positivity) hsq1).trans ((mul_le_mul_of_nonneg_left hb1 (sq_nonneg _)).trans (by simpa using hV2))
    rw [(H.drift_wall_partials hk hy hv).1, habs _ _ hu0]
    calc
      _ ≤ y 1 * (y 2 * |entranceRadialStrongCoefficient y| +
          y 1 * y 2 * |fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) (entranceRadialCoordinates y) (Pi.single 1 1)| +
          y 2 ^ 2 * |fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z)) (entranceRadialCoordinates y) (Pi.single 1 1)|) := by
        apply mul_le_mul_of_nonneg_left _ hu0
        exact ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
          (add_le_add (add_le_add (le_of_eq (habs _ _ hv0)) (le_of_eq (habs _ _ huv))) (le_of_eq (habs _ _ (sq_nonneg _))))
      _ ≤ y 1 * (y 2 * C + y 1 * y 2 * C + y 2 ^ 2 * (C * (y 1 + y 3) / k ^ 2)) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hAval hv0) (mul_le_mul_of_nonneg_left (hAp 1) huv))
            (mul_le_mul_of_nonneg_left hBu (sq_nonneg _))) hu0
      _ = C * (y 1 * y 2 + y 1 * (y 1 * y 2) + y 1 * (y 2 ^ 2 * (y 1 + y 3) / k ^ 2)) := by ring
      _ ≤ C * (y 1 * y 2 + y 1 * y 2 + y 1 * y 2) := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        exact add_le_add (add_le_add le_rfl (mul_le_of_le_one_left huv hu1)) (mul_le_mul_of_nonneg_left hterm hu0)
      _ = _ := by ring
  have hGw : |y 3 * fderiv ℝ (fun z => entranceRadialDrift (Ψ z)) (entranceRadialCoordinates y) (Pi.single 3 1)| ≤
      2 * C * (y 1 * y 2 * y 3 + y 2 ^ 2 * y 3 ^ 2 / k ^ 2) := by
    have hterm : y 2 ^ 2 * y 1 * y 3 / k ^ 2 ≤ y 1 * y 2 * y 3 := by
      calc
        _ ≤ y 2 ^ 2 * y 1 * y 3 := div_le_self (by positivity) hsq1
        _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hV2 (mul_nonneg hu0 hw0)]
    rw [(H.drift_wall_partials hk hy hv).2, habs _ _ hw0]
    calc
      _ ≤ y 3 * (y 1 * y 2 * |fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z))
          (entranceRadialCoordinates y) (Pi.single 3 1)| + y 2 ^ 2 * |fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z))
          (entranceRadialCoordinates y) (Pi.single 3 1)|) := by
        apply mul_le_mul_of_nonneg_left _ hw0
        exact (abs_add_le _ _).trans (add_le_add (le_of_eq (habs _ _ huv)) (le_of_eq (habs _ _ (sq_nonneg _))))
      _ ≤ y 3 * (y 1 * y 2 * C + y 2 ^ 2 * (C * (y 1 + y 3) / k ^ 2)) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left (hAp 3) huv)
          (mul_le_mul_of_nonneg_left hBw' (sq_nonneg _))) hw0
      _ = C * (y 1 * y 2 * y 3 + y 2 ^ 2 * y 1 * y 3 / k ^ 2 + y 2 ^ 2 * y 3 ^ 2 / k ^ 2) := by ring
      _ ≤ C * (y 1 * y 2 * y 3 + y 1 * y 2 * y 3 + y 2 ^ 2 * y 3 ^ 2 / k ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add le_rfl hterm) le_rfl) hC.le
      _ ≤ _ := by nlinarith only [mul_nonneg hC.le (htail 2)]
  refine ⟨hG.trans ?_, hGr.trans ?_, hGu.trans ?_, hGw.trans ?_⟩
  all_goals
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith only [hC, hR]

/-- The wall bounds in (C.22) are derivatives along actual multiplicative coordinate curves. -/
theorem exists_entranceRadialDrift_log_bounds :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y → 0 < y 2 →
      ∀ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ →
        let z := entranceRadialCoordinates y
        |deriv (fun t => entranceRadialDrift (Ψ (Function.update z 1 (y 1 * Real.exp t)))) 0| ≤ C * (y 1 * y 2) ∧
        |deriv (fun t => entranceRadialDrift (Ψ (Function.update z 3 (y 3 * Real.exp t)))) 0| ≤
          C * (y 1 * y 2 * y 3 + y 2 ^ 2 * y 3 ^ 2 / k ^ 2) := by
  obtain ⟨C, hC, HC⟩ := exists_entranceRadialDrift_basic_bounds
  refine ⟨C, hC, ?_⟩
  intro k y hk hy hv Ψ H
  dsimp only
  have hu := (H.drift_log_derivative hk hy hv 1).deriv
  have hw := (H.drift_log_derivative hk hy hv 3).deriv
  simp only [entranceRadialCoordinates, Matrix.cons_val_one, Matrix.cons_val, Matrix.cons_val_zero] at hu hw
  simp only [entranceRadialCoordinates]
  rw [hu, hw]
  exact (HC k y hk hy hv Ψ H).2.2

end BianchiIX
