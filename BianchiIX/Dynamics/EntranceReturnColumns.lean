import BianchiIX.Dynamics.EntranceOrdinaryReturnResponse

noncomputable section

namespace BianchiIX

open Set

/-- Three ordinary columns of the actual return, with uniform weighted wall remainders. -/
theorem exists_entrance_return_radial_wall_columns :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ (y : ProjectiveState) (θ : ℝ),
      let k := coreRadius (y 0) (y 2)
      7 / 4 ≤ k → 1 ≤ y 0 → (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) →
      (0 < y 3 ∧ y 3 ≤ ε) → (θ = 1 ∨ (θ = 1 / k ^ 2 ∧ k * (y 1 + y 3) ^ 2 ≤ 1)) →
      ∃ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ ∧
      let z := entranceRadialCoordinates y
      let Q := fun z => entranceStableRadius (entranceReturnState (Ψ z))
      let L := fun z => entranceLogWalls k (entranceReturnState (Ψ z))
      let H := y 1 * y 2 + θ * (y 2 * y 3) ^ 2
      |fderiv ℝ Q z (Pi.single 0 1) - 1| ≤ C * H / k ^ 2 ∧
      |fderiv ℝ Q z (Pi.single 1 1)| ≤ C * y 2 / k ∧
      |fderiv ℝ Q z (Pi.single 3 1)| ≤ C * (y 1 * y 2 + θ * (y 2) ^ 2 * y 3) / k ∧
      |fderiv ℝ L z (Pi.single 0 1) 0| + |fderiv ℝ L z (Pi.single 0 1) 1| ≤ C * (-Real.log (y 2)) ∧
      |fderiv ℝ L z (Pi.single 1 1) 0 - 1 / y 1| + |fderiv ℝ L z (Pi.single 1 1) 1| ≤ C ∧
      |fderiv ℝ L z (Pi.single 3 1) 0| + |fderiv ℝ L z (Pi.single 3 1) 1 - k ^ 2 * (1 / y 3)| ≤ C := by
  obtain ⟨T, hT, K, hK, F, hF, ε, hε, hεsmall, HP⟩ := exists_entrance_ordinary_return_response
  let C := 2 * K + 2 * F + 2 * T + T * (1 + 4 * K)
  have hC : 0 < C := by dsimp [C]; positivity
  have hTK : 0 ≤ T * (1 + 4 * K) := by positivity
  have hCK : 2 * K ≤ C := by dsimp [C]; linarith only [hT, hF, hTK]
  have hCF : 2 * F ≤ C := by dsimp [C]; linarith only [hT, hK, hTK]
  have hCT : 2 * T ≤ C := by dsimp [C]; linarith only [hF, hK, hTK]
  have hCTK : T * (1 + 4 * K) ≤ C := by dsimp [C]; linarith only [hF, hK, hT]
  refine ⟨C, hC, ε, hε, hεsmall, ?_⟩
  intro y θ k hk hm hu hv hw hθ
  have hu' : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := ⟨hu.1.le, hu.2.trans hεsmall⟩
  have hw' : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := ⟨hw.1.le, hw.2.trans hεsmall⟩
  have hy : entranceRegion k y := ⟨hm, by rw [sub_self, abs_zero]; dsimp [k]; linarith,
    hu', ⟨hv.1.le, hv.2.le⟩, hw'⟩
  obtain ⟨Ψ, HΨ⟩ := exists_entranceRegion_radial_inverse hk hy hv.1
  refine ⟨Ψ, HΨ, ?_⟩
  dsimp only
  let z := entranceRadialCoordinates y
  let Q := fun z => entranceStableRadius (entranceReturnState (Ψ z))
  let L := fun z => entranceLogWalls k (entranceReturnState (Ψ z))
  let H := y 1 * y 2 + θ * (y 2 * y 3) ^ 2
  let S := y 1 * y 2 + θ * (y 2) ^ 2 * y 3
  have hk0 : 0 < k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hθ01 : 0 ≤ θ ∧ θ ≤ 1 := by
    rcases hθ with rfl | ⟨rfl, _⟩
    · norm_num
    · exact ⟨by positivity, (div_le_one (sq_pos_of_pos hk0)).mpr (one_le_pow₀ hk1)⟩
  have hH : 0 ≤ H := by dsimp [H]; positivity [hu.1, hv.1, hθ01.1]
  have hS : 0 ≤ S := by dsimp [S]; positivity [hu.1, hv.1, hw.1, hθ01.1]
  have hlog : 0 ≤ -Real.log (y 2) := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have Hr := HP y θ hk hm hu hv hw hθ Ψ HΨ (Pi.single 0 1) (by simp)
  have Hu := HP y θ hk hm hu hv hw hθ Ψ HΨ (Pi.single 1 1) (by simp)
  have Hw := HP y θ hk hm hu hv hw hθ Ψ HΨ (Pi.single 3 1) (by simp)
  dsimp only at Hr Hu Hw
  simp only [Pi.single_apply, Fin.isValue, ite_true, ite_false, zero_ne_one, one_ne_zero,
    show (3 : Fin 4) ≠ 0 by decide, show (0 : Fin 4) ≠ 3 by decide,
    show (3 : Fin 4) ≠ 1 by decide, show (1 : Fin 4) ≠ 3 by decide,
    abs_zero, abs_one, mul_zero, add_zero, zero_add, zero_div,
    mul_one, sub_zero] at Hr Hu Hw
  have hLv : (-Real.log (y 2)) * y 2 ≤ 1 := by
    simpa only [mul_comm] using mul_neg_log_le_one hv.1
  have hLS : (-Real.log (y 2)) * S ≤ 2 := by
    have HE := entrance_ordinary_log_weights ⟨hu.1.le, by linarith [hu'.2]⟩
      ⟨hv.1, hv.2.le⟩ ⟨hw.1.le, by linarith [hw'.2]⟩ hθ01 0 1
    simpa only [abs_zero, abs_one, mul_zero, add_zero, zero_add, mul_one] using HE
  have hUtime : (-Real.log (y 2)) * (K * y 2 / k) ≤ K := by
    calc
      _ = K / k * ((-Real.log (y 2)) * y 2) := by ring
      _ ≤ K / k := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hLv (show 0 ≤ K / k by positivity)
      _ ≤ K := div_le_self hK.le hk1
  have hWtime : (-Real.log (y 2)) * (K * S / k) ≤ 2 * K := by
    calc
      _ = K / k * ((-Real.log (y 2)) * S) := by ring
      _ ≤ K / k * 2 := mul_le_mul_of_nonneg_left hLS (by positivity)
      _ ≤ 2 * K := by nlinarith only [div_le_self hK.le hk1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply Hr.1.trans
    change 2 * (F * H / k ^ 2) ≤ C * H / k ^ 2
    simpa only [mul_div_assoc, mul_assoc] using mul_le_mul_of_nonneg_right hCF (show 0 ≤ H / k ^ 2 by positivity)
  · apply Hu.1.trans
    change 2 * (K * y 2 / k) ≤ C * y 2 / k
    simpa only [mul_div_assoc, mul_assoc] using mul_le_mul_of_nonneg_right hCK (div_nonneg hv.1.le hk0.le)
  · apply Hw.1.trans
    change 2 * (K * S / k) ≤ C * S / k
    simpa only [mul_div_assoc, mul_assoc] using mul_le_mul_of_nonneg_right hCK (show 0 ≤ S / k by positivity)
  · apply Hr.2.trans
    nlinarith only [mul_le_mul_of_nonneg_right hCT hlog]
  · apply Hu.2.trans (le_trans ?_ hCTK)
    exact mul_le_mul_of_nonneg_left (by nlinarith only [hUtime, hK]) hT.le
  · apply Hw.2.trans (le_trans ?_ hCTK)
    exact mul_le_mul_of_nonneg_left (by nlinarith only [hWtime]) hT.le

end BianchiIX
