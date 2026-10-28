import BianchiIX.Dynamics.EntranceActiveReturnResponse
import BianchiIX.Dynamics.EntranceReturnColumns

noncomputable section

namespace BianchiIX

open Set

/-- All ordinary columns of the actual first arrival, with unweighted logarithmic outputs. -/
theorem exists_entrance_return_full_columns :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ (y : ProjectiveState) (θ : ℝ),
      let k := coreRadius (y 0) (y 2)
      7 / 4 ≤ k → 1 ≤ y 0 → (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) →
      (0 < y 3 ∧ y 3 ≤ ε) → (θ = 1 ∨ (θ = 1 / k ^ 2 ∧ k * (y 1 + y 3) ^ 2 ≤ 1)) →
      ∃ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ ∧
      let z := entranceRadialCoordinates y
      let Q := fun z => entranceStableRadius (entranceReturnState (Ψ z))
      let L := fun z => entranceLogWalls 1 (entranceReturnState (Ψ z))
      let H := y 1 * y 2 + θ * (y 2 * y 3) ^ 2
      (|fderiv ℝ Q z (Pi.single 0 1) - 1| ≤ C * H / k ^ 2 ∧
       |fderiv ℝ Q z (Pi.single 1 1)| ≤ C * y 2 / k ∧
       |fderiv ℝ Q z (Pi.single 2 1)| ≤ C * (y 1 + θ * y 2 * (y 3) ^ 2) ∧
       |fderiv ℝ Q z (Pi.single 3 1)| ≤ C * (y 1 * y 2 + θ * (y 2) ^ 2 * y 3) / k) ∧
      (|fderiv ℝ L z (Pi.single 0 1) 0| ≤ C * (-Real.log (y 2)) ∧
       |fderiv ℝ L z (Pi.single 1 1) 0 - 1 / y 1| ≤ C ∧
       |fderiv ℝ L z (Pi.single 2 1) 0| ≤ C * k / y 2 ∧
       |fderiv ℝ L z (Pi.single 3 1) 0| ≤ C) ∧
      (|fderiv ℝ L z (Pi.single 0 1) 1| ≤ C * (-Real.log (y 2)) / k ^ 2 ∧
       |fderiv ℝ L z (Pi.single 1 1) 1| ≤ C / k ^ 2 ∧
       |fderiv ℝ L z (Pi.single 2 1) 1| ≤ C / y 2 ∧
       |fderiv ℝ L z (Pi.single 3 1) 1 - 1 / y 3| ≤ C / k ^ 2) := by
  obtain ⟨C₀, hC₀, ε₀, hε₀, hε₀small, H₀⟩ := exists_entrance_return_radial_wall_columns
  obtain ⟨C₁, hC₁, ε₁, hε₁, hε₁small, H₁⟩ := exists_entrance_active_return_response
  let C := C₀ + C₁
  have hC : 0 < C := add_pos hC₀ hC₁
  have hCC₀ : C₀ ≤ C := by dsimp [C]; linarith
  have hCC₁ : C₁ ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, min ε₀ ε₁, lt_min hε₀ hε₁, (min_le_left _ _).trans hε₀small, ?_⟩
  intro y θ k hk hm hu hv hw hθ
  have hu₀ : 0 < y 1 ∧ y 1 ≤ ε₀ := ⟨hu.1, hu.2.trans (min_le_left _ _)⟩
  have hw₀ : 0 < y 3 ∧ y 3 ≤ ε₀ := ⟨hw.1, hw.2.trans (min_le_left _ _)⟩
  have hu₁ : 0 < y 1 ∧ y 1 ≤ ε₁ := ⟨hu.1, hu.2.trans (min_le_right _ _)⟩
  have hw₁ : 0 < y 3 ∧ y 3 ≤ ε₁ := ⟨hw.1, hw.2.trans (min_le_right _ _)⟩
  obtain ⟨Ψ, HΨ, Hqr, Hqu, Hqw, Hlr, Hlu, Hlw⟩ := H₀ y θ hk hm hu₀ hv hw₀ hθ
  obtain ⟨Hqv, _, Huv, Hwv⟩ := H₁ y θ hk hm hu₁ hv hw₁ hθ Ψ HΨ
  refine ⟨Ψ, HΨ, ?_⟩
  dsimp only
  let z := entranceRadialCoordinates y
  let L := fun z => entranceLogWalls 1 (entranceReturnState (Ψ z))
  let Lk := fun z => entranceLogWalls k (entranceReturnState (Ψ z))
  have hk0 : 0 < k := by linarith
  have hk2 : 0 < k ^ 2 := sq_pos_of_pos hk0
  have hθ0 : 0 ≤ θ := by
    rcases hθ with rfl | ⟨rfl, _⟩
    · norm_num
    · positivity
  have hu' : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := ⟨hu.1.le, hu₀.2.trans hε₀small⟩
  have hw' : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := ⟨hw.1.le, hw₀.2.trans hε₀small⟩
  have HR := entranceReturn_regular hk hm hu' hv hw'
  have ht : entranceReturnTime y ∈ Icc 0 (entranceReturnTime y) := ⟨HR.1.1.1.1.le, le_rfl⟩
  have hpos := entranceReturn_walls_pos hk hm ⟨hu.1, hu'.2⟩ hv ⟨hw.1, hw'.2⟩ _ ht
  have hscale (i : Fin 4) : fderiv ℝ Lk z (Pi.single i 1) =
      ![fderiv ℝ L z (Pi.single i 1) 0, k ^ 2 * fderiv ℝ L z (Pi.single i 1) 1] := by
    apply entranceLogWalls_comp_fderiv_scale (HΨ.hasFDerivAt_return hk hm hu' hv hw').differentiableAt
    · rw [HΨ.apply_base]
      exact hpos.1.ne'
    · rw [HΨ.apply_base]
      exact hpos.2.2.ne'
  change |fderiv ℝ Lk z (Pi.single 0 1) 0| + |fderiv ℝ Lk z (Pi.single 0 1) 1| ≤
    C₀ * (-Real.log (y 2)) at Hlr
  change |fderiv ℝ Lk z (Pi.single 1 1) 0 - 1 / y 1| + |fderiv ℝ Lk z (Pi.single 1 1) 1| ≤ C₀ at Hlu
  change |fderiv ℝ Lk z (Pi.single 3 1) 0| + |fderiv ℝ Lk z (Pi.single 3 1) 1 - k ^ 2 * (1 / y 3)| ≤ C₀ at Hlw
  rw [hscale 0] at Hlr
  rw [hscale 1] at Hlu
  rw [hscale 3] at Hlw
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at Hlr Hlu Hlw
  rw [← mul_sub] at Hlw
  have unpack {a b B : ℝ} (h : |a| + |k ^ 2 * b| ≤ B) : |a| ≤ B ∧ |b| ≤ B / k ^ 2 := by
    rw [abs_mul, abs_of_pos hk2] at h
    exact ⟨by linarith only [h, mul_nonneg hk2.le (abs_nonneg b)],
      (le_div_iff₀ hk2).mpr (by nlinarith only [h, abs_nonneg a])⟩
  obtain ⟨HUr, HWr⟩ := unpack Hlr
  obtain ⟨HUu, HWu⟩ := unpack Hlu
  obtain ⟨HUw, HWw⟩ := unpack Hlw
  have hl : 0 ≤ -Real.log (y 2) := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  refine ⟨⟨Hqr.trans ?_, Hqu.trans ?_, Hqv.trans ?_, Hqw.trans ?_⟩,
    ⟨HUr.trans ?_, HUu.trans hCC₀, Huv.trans ?_, HUw.trans hCC₀⟩,
    ⟨HWr.trans ?_, HWu.trans ?_, Hwv.trans ?_, HWw.trans ?_⟩⟩
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCC₀ (by positivity [hu.1, hv.1])) hk2.le
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCC₀ hv.1.le) hk0.le
  · exact mul_le_mul_of_nonneg_right hCC₁ (by positivity [hu.1, hv.1])
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCC₀ (by positivity [hu.1, hv.1, hw.1])) hk0.le
  · exact mul_le_mul_of_nonneg_right hCC₀ hl
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCC₁ hk0.le) hv.1.le
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCC₀ hl) hk2.le
  · exact div_le_div_of_nonneg_right hCC₀ hk2.le
  · exact div_le_div_of_nonneg_right hCC₁ hv.1.le
  · exact div_le_div_of_nonneg_right hCC₀ hk2.le

end BianchiIX
