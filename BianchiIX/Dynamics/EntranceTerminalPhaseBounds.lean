import BianchiIX.Dynamics.EntrancePhysicalBounds

noncomputable section

namespace BianchiIX

/-- The actual entrance phase retains the growing-wall factor when the weak wall is below the strong wall. -/
theorem exists_entrance_terminal_phase_bounds :
    ∃ A ≥ (1 : ℝ), ∃ δ > (0 : ℝ), δ ≤ 1 / 10000 ∧ ∀ (α : ℝ) (y : ProjectiveState),
      (0 < α ∧ α ≤ 1) → 1 / α ≤ coreRadius (y 0) (y 2) →
      7 / 4 ≤ coreRadius (y 0) (y 2) → 1 ≤ y 0 →
      (0 < y 1 ∧ y 1 ≤ δ) → (0 < y 2 ∧ y 2 < 1) →
      (0 < y 3 ∧ y 3 ≤ δ) → y 3 ≤ y 1 →
      ∃ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ ∧
      let z := entranceRadialCoordinates y
      let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
      ContDiffAt ℝ 2 F z ∧ |F z - z 0| ≤ A * α * y 1 * y 2 ∧
        |fderiv ℝ F z (Pi.single 0 1) - 1| ≤ A * y 1 * y 2 ∧
        |fderiv ℝ F z (Pi.single 1 1)| ≤ A * α * y 2 ∧
        |fderiv ℝ F z (Pi.single 2 1)| ≤ A * y 1 ∧
        |fderiv ℝ F z (Pi.single 3 1)| ≤ A * α * y 1 * y 2 := by
  obtain ⟨C, hC, δ, hδ, hδsmall, HC⟩ := exists_entrance_physical_basic_bounds
  refine ⟨5 * C + 1, by linarith only [hC], δ, hδ, hδsmall, ?_⟩
  intro α y hα hka hk hm hu hv hw hwu
  obtain ⟨Ψ, HΨ, hF, H0, Hr, Hu, Hv, Hw⟩ := HC y hk hm hu hv hw
  have hu0 : 0 < y 1 := hu.1
  have hv0 : 0 < y 2 := hv.1
  have hk0 : 0 < coreRadius (y 0) (y 2) := by linarith only [hk]
  have hkinv : 1 / coreRadius (y 0) (y 2) ≤ α := by
    have H := (div_le_iff₀ hα.1).mp hka
    exact (div_le_iff₀ hk0).mpr (by nlinarith only [H])
  have hk2 : 1 ≤ coreRadius (y 0) (y 2) ^ 2 := by nlinarith only [hk]
  have hu1 : y 1 ≤ 1 := (hu.2.trans hδsmall).trans (by norm_num)
  have hsum : 0 ≤ y 1 + y 3 ∧ y 1 + y 3 ≤ 2 * y 1 :=
    ⟨add_nonneg hu.1.le hw.1.le, by linarith only [hwu]⟩
  have hsum2 : (y 1 + y 3) ^ 2 ≤ 4 * y 1 := by
    nlinarith only [sq_le_sq₀ hsum.1 (by positivity : 0 ≤ 2 * y 1) |>.mpr hsum.2,
      mul_nonneg hu.1.le (sub_nonneg.mpr hu1)]
  have hv2 : (y 2) ^ 2 ≤ y 2 := by nlinarith only [hv.1, hv.2]
  have Hnum : y 1 * y 2 + (y 2) ^ 2 * (y 1 + y 3) ^ 2 ≤ 5 * y 1 * y 2 := by
    nlinarith only [mul_le_mul hsum2 hv2 (sq_nonneg (y 2)) (by positivity : 0 ≤ 4 * y 1)]
  have Hunum : y 2 + (y 2) ^ 2 * (y 1 + y 3) ≤ 3 * y 2 := by
    have Hs : y 1 + y 3 ≤ 2 := by linarith only [hsum.2, hu1]
    nlinarith only [mul_le_mul Hs hv2 (sq_nonneg (y 2)) (by norm_num : (0 : ℝ) ≤ 2)]
  have Hvnum : y 1 + y 2 * (y 1 + y 3) ^ 2 ≤ 5 * y 1 := by
    nlinarith only [mul_le_mul hsum2 hv.2.le hv.1.le (by positivity : 0 ≤ 4 * y 1)]
  have Hwnum : y 1 * y 2 + (y 2) ^ 2 * (y 1 + y 3) ≤ 3 * y 1 * y 2 := by
    nlinarith only [mul_le_mul hsum.2 hv2 (sq_nonneg (y 2)) (by positivity : 0 ≤ 2 * y 1)]
  have hscale {x N Q : ℝ} (hQ : 0 ≤ Q) (hN : N ≤ Q)
      (H : x ≤ C * N / coreRadius (y 0) (y 2)) : x ≤ C * Q * α := by
    apply H.trans
    calc
      _ ≤ C * Q / coreRadius (y 0) (y 2) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hN hC.le) hk0.le
      _ = C * Q * (1 / coreRadius (y 0) (y 2)) := by ring
      _ ≤ C * Q * α := mul_le_mul_of_nonneg_left hkinv (mul_nonneg hC.le hQ)
  refine ⟨Ψ, HΨ, hF, ?_, ?_, ?_, ?_, ?_⟩
  · have H := hscale (by positivity : 0 ≤ 5 * y 1 * y 2) Hnum H0
    nlinarith only [H, mul_nonneg hα.1.le (mul_nonneg hu.1.le hv.1.le)]
  · have H := Hr.trans ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left Hnum hC.le)
      (sq_nonneg (coreRadius (y 0) (y 2)))).trans (div_le_self (by positivity) hk2))
    nlinarith only [H, mul_nonneg hu.1.le hv.1.le]
  · have H := hscale (by positivity : 0 ≤ 3 * y 2) Hunum Hu
    nlinarith only [H, mul_nonneg (mul_nonneg hC.le hα.1.le) hv.1.le, mul_nonneg hα.1.le hv.1.le]
  · have H := Hv.trans (mul_le_mul_of_nonneg_left Hvnum hC.le)
    nlinarith only [H, hu.1]
  · have H := hscale (by positivity : 0 ≤ 3 * y 1 * y 2) Hwnum Hw
    nlinarith only [H, mul_nonneg (mul_nonneg (mul_nonneg hC.le hα.1.le) hu.1.le) hv.1.le,
      mul_nonneg hα.1.le (mul_nonneg hu.1.le hv.1.le)]

end BianchiIX
