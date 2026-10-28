import BianchiIX.Dynamics.EntranceWeakRefinedRadialBounds
import BianchiIX.Dynamics.EntranceDriftEstimates

noncomputable section

namespace BianchiIX

set_option maxHeartbeats 600000 in
/-- Equation (C.24), retaining the additional two inverse powers in the pure weak-wall terms. -/
theorem exists_entranceRadialDrift_refined_bounds :
    ∃ C > (0 : ℝ), ∀ (k : ℝ) (y : ProjectiveState), 7 / 4 ≤ k → entranceRegion k y →
      k * (y 1 + y 3) ^ 2 ≤ 1 → 0 < y 2 →
      ∀ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ →
        let LG := fderiv ℝ (fun z => entranceRadialDrift (Ψ z)) (entranceRadialCoordinates y)
        |entranceRadialDrift y| ≤ C * (y 1 * y 2 + y 2 ^ 2 * y 3 ^ 2 / k ^ 4) ∧
        |LG (Pi.single 0 1)| ≤ C * (y 1 * y 2 / k ^ 2 + y 2 ^ 2 * y 3 ^ 2 / k ^ 5) ∧
        |y 1 * LG (Pi.single 1 1)| ≤ C * (y 1 * y 2) ∧
        |y 3 * LG (Pi.single 3 1)| ≤ C * (y 1 * y 2 * y 3 + y 2 ^ 2 * y 3 ^ 2 / k ^ 4) := by
  obtain ⟨A, hA, HA⟩ := exists_entranceRadialStrong_derivative_bound
  obtain ⟨R, hR, HR⟩ := exists_entranceRadialStrong_radial_bounds
  obtain ⟨B, hB, HB⟩ := exists_entranceRadialWeakCoefficient_refined_bounds
  obtain ⟨T, hT, HT⟩ := exists_entranceRadialDrift_basic_bounds
  refine ⟨A + B + R + T, by positivity, ?_⟩
  intro k y hk hy hsmall hv Ψ H
  let b := y 1 + y 3
  let z := entranceRadialCoordinates y
  have hu0 := hy.2.2.1.1
  have hv0 := hy.2.2.2.1.1
  have hw0 := hy.2.2.2.2.1
  have hb : 0 ≤ b := add_nonneg hu0 hw0
  have hb1 : b ≤ 1 := by dsimp [b]; linarith [hy.2.2.1.2, hy.2.2.2.2.2]
  have hk1 : 1 ≤ k := by linarith
  have hk0 : 0 < k := by linarith
  have hk2 : 1 ≤ k ^ 2 := one_le_pow₀ hk1
  have huv : 0 ≤ y 1 * y 2 := mul_nonneg hu0 hv0
  have hV2 : y 2 ^ 2 ≤ y 2 := by nlinarith only [hv0, hy.2.2.2.1.2]
  have hnum : y 2 ^ 2 * y 1 * b ≤ y 1 * y 2 := by
    have Hp := ((mul_le_mul_of_nonneg_left hb1 (sq_nonneg (y 2))).trans (by simpa using hV2))
    nlinarith only [mul_le_mul_of_nonneg_left Hp hu0]
  have hscale0 : y 2 ^ 2 * y 1 * b / k ^ 2 ≤ y 1 * y 2 :=
    (div_le_self (by positivity) hk2).trans hnum
  have hscaleR : y 2 ^ 2 * y 1 * b / k ^ 3 ≤ y 1 * y 2 / k ^ 2 :=
    (div_le_div_of_nonneg_right hnum (by positivity)).trans
      (div_le_div_of_nonneg_left huv (by positivity) (pow_le_pow_right₀ hk1 (by norm_num : 2 ≤ 3)))
  have hscaleW : y 2 ^ 2 * y 1 * y 3 / k ^ 2 ≤ y 1 * y 2 * y 3 := by
    calc
      _ ≤ y 2 ^ 2 * y 1 * y 3 := div_le_self (by positivity) hk2
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hV2 (mul_nonneg hu0 hw0)]
  have hstrong := HA k y hk hy hv Ψ H
  have hAval : |entranceRadialStrongCoefficient y| ≤ A := by
    linarith only [hstrong, norm_nonneg (fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) z)]
  have hAnorm : ‖fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) z‖ ≤ A := by
    linarith only [hstrong, abs_nonneg (entranceRadialStrongCoefficient y)]
  have hAw : |fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) z (Pi.single 3 1)| ≤ A := by
    have Hp := ((fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) z).le_opNorm (Pi.single 3 1)).trans
      (mul_le_mul_of_nonneg_right hAnorm (norm_nonneg _))
    simpa [Pi.norm_single] using Hp
  have hAr := (HR k y hk hy hv Ψ H).2.1
  obtain ⟨hB0, hBr, _, hBw⟩ := HB k y hk hy hsmall hv Ψ H
  have habs (c a : ℝ) (hc : 0 ≤ c) : |c * a| = c * |a| := by rw [abs_mul, abs_of_nonneg hc]
  have hmerge (a c x t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) : a * x + c * (x + t) ≤ (a + c) * (x + t) := by
    nlinarith only [mul_nonneg ha ht]
  have hG : |entranceRadialDrift y| ≤ (A + B) * (y 1 * y 2 + y 2 ^ 2 * y 3 ^ 2 / k ^ 4) := by
    calc
      _ ≤ y 1 * y 2 * |entranceRadialStrongCoefficient y| + y 2 ^ 2 * |entranceRadialWeakCoefficient y| := by
        unfold entranceRadialDrift
        exact (abs_add_le _ _).trans (add_le_add (le_of_eq (habs _ _ huv)) (le_of_eq (habs _ _ (sq_nonneg _))))
      _ ≤ y 1 * y 2 * A + y 2 ^ 2 * (B * (y 1 * b / k ^ 2 + y 3 ^ 2 / k ^ 4)) :=
        add_le_add (mul_le_mul_of_nonneg_left hAval huv) (mul_le_mul_of_nonneg_left hB0 (sq_nonneg _))
      _ = A * (y 1 * y 2) + B * (y 2 ^ 2 * y 1 * b / k ^ 2 + y 2 ^ 2 * y 3 ^ 2 / k ^ 4) := by ring
      _ ≤ A * (y 1 * y 2) + B * (y 1 * y 2 + y 2 ^ 2 * y 3 ^ 2 / k ^ 4) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add hscale0 le_rfl) hB.le)
      _ ≤ _ := hmerge _ _ _ _ hA.le (by positivity)
  have hGr : |fderiv ℝ (fun z => entranceRadialDrift (Ψ z)) z (Pi.single 0 1)| ≤
      (R + B) * (y 1 * y 2 / k ^ 2 + y 2 ^ 2 * y 3 ^ 2 / k ^ 5) := by
    rw [H.drift_radial_derivative hk hy hv]
    calc
      _ ≤ y 1 * y 2 * |fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) z (Pi.single 0 1)| +
          y 2 ^ 2 * |fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z)) z (Pi.single 0 1)| :=
        (abs_add_le _ _).trans (add_le_add (le_of_eq (habs _ _ huv)) (le_of_eq (habs _ _ (sq_nonneg _))))
      _ ≤ y 1 * y 2 * (R / k ^ 2) + y 2 ^ 2 * (B * (y 1 * b / k ^ 3 + y 3 ^ 2 / k ^ 5)) :=
        add_le_add (mul_le_mul_of_nonneg_left hAr huv) (mul_le_mul_of_nonneg_left hBr (sq_nonneg _))
      _ = R * (y 1 * y 2 / k ^ 2) + B * (y 2 ^ 2 * y 1 * b / k ^ 3 + y 2 ^ 2 * y 3 ^ 2 / k ^ 5) := by ring
      _ ≤ R * (y 1 * y 2 / k ^ 2) + B * (y 1 * y 2 / k ^ 2 + y 2 ^ 2 * y 3 ^ 2 / k ^ 5) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add hscaleR le_rfl) hB.le)
      _ ≤ _ := hmerge _ _ _ _ hR.le (by positivity)
  have hGw : |y 3 * fderiv ℝ (fun z => entranceRadialDrift (Ψ z)) z (Pi.single 3 1)| ≤
      (A + B) * (y 1 * y 2 * y 3 + y 2 ^ 2 * y 3 ^ 2 / k ^ 4) := by
    rw [(H.drift_wall_partials hk hy hv).2, habs _ _ hw0]
    calc
      _ ≤ y 3 * (y 1 * y 2 * |fderiv ℝ (fun z => entranceRadialStrongCoefficient (Ψ z)) z (Pi.single 3 1)| +
          y 2 ^ 2 * |fderiv ℝ (fun z => entranceRadialWeakCoefficient (Ψ z)) z (Pi.single 3 1)|) := by
        apply mul_le_mul_of_nonneg_left _ hw0
        exact (abs_add_le _ _).trans (add_le_add (le_of_eq (habs _ _ huv)) (le_of_eq (habs _ _ (sq_nonneg _))))
      _ ≤ y 3 * (y 1 * y 2 * A + y 2 ^ 2 * (B * (y 1 / k ^ 2 + y 3 / k ^ 4))) :=
        mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hAw huv)
          (mul_le_mul_of_nonneg_left hBw (sq_nonneg _))) hw0
      _ = A * (y 1 * y 2 * y 3) + B * (y 2 ^ 2 * y 1 * y 3 / k ^ 2 + y 2 ^ 2 * y 3 ^ 2 / k ^ 4) := by ring
      _ ≤ A * (y 1 * y 2 * y 3) + B * (y 1 * y 2 * y 3 + y 2 ^ 2 * y 3 ^ 2 / k ^ 4) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add hscaleW le_rfl) hB.le)
      _ ≤ _ := hmerge _ _ _ _ hA.le (by positivity)
  have hGu := (HT k y hk hy hv Ψ H).2.2.1
  dsimp only
  refine ⟨hG.trans ?_, hGr.trans ?_, hGu.trans ?_, hGw.trans ?_⟩
  all_goals
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    linarith only [hA, hB, hR, hT]

end BianchiIX
