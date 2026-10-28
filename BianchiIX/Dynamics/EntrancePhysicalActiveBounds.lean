import BianchiIX.Dynamics.EntrancePhysicalActiveResponse

noncomputable section

namespace BianchiIX

/-- Both estimates in (C.42), for the actual physical radius and the stated entrance domain. -/
theorem exists_entrance_physical_active_bounds :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∀ (y : ProjectiveState),
      let k := coreRadius (y 0) (y 2)
      7 / 4 ≤ k → 1 ≤ y 0 →
      (0 < y 1 ∧ y 1 ≤ ε / k ^ 41) → (0 < y 2 ∧ y 2 < 1) →
      (0 < y 3 ∧ y 3 ≤ ε / k ^ 41) →
      ∀ (Ψ : ProjectiveState → ProjectiveState), EntranceRadialInverseAt y Ψ →
      let z := entranceRadialCoordinates y
      let ω := (y 2) ^ (2 / k)
      let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
      |fderiv ℝ F z (Pi.single 2 1)| ≤ C *
        (y 1 / k + y 1 * (y 2) ^ (k / 3) + y 2 * (y 3) ^ 2 / k * (1 / k ^ 2 + ω)) ∧
        (y 2 ≤ 1 / 2 → |fderiv ℝ F z (Pi.single 2 1)| ≤
          C / k * (y 1 + y 2 * (y 3) ^ 2 * (1 / k ^ 2 + ω))) := by
  obtain ⟨C, hC, ε, hε, hεcap, HC⟩ := exists_entrance_physical_active_response
  refine ⟨7 * C, by positivity, ε, hε, hεcap, ?_⟩
  intro y k hk hm hu hv hw Ψ HΨ z ω F
  have hk0 : 0 < k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hεk : ε / k ^ 41 ≤ ε := div_le_self hε.le (one_le_pow₀ hk1)
  have hscale : k ^ 2 * (ε / k ^ 41) ≤ ε := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (pow_pos hk0 41)).mpr
    have H := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hk1 (by decide : 2 ≤ 41)) hε.le
    simpa only [mul_comm] using H
  have hsmall : k ^ 2 * (y 1 + y 3) ≤ 1 := by
    have HU := (mul_le_mul_of_nonneg_left hu.2 (sq_nonneg k)).trans hscale
    have HW := (mul_le_mul_of_nonneg_left hw.2 (sq_nonneg k)).trans hscale
    nlinarith only [HU, HW, hεcap]
  have H := (HC y hk hm ⟨hu.1, hu.2.trans hεk⟩ hv ⟨hw.1, hw.2.trans hεk⟩ hsmall Ψ HΨ).2
  rw [entrance_strong_weight_eq_rpow hv.1, entrance_weak_weight_eq_rpow hv.1] at H
  let S := y 1 / k + y 1 * (y 2) ^ (k / 3) + y 2 * (y 3) ^ 2 / k * (1 / k ^ 2 + ω)
  let J := y 1 + y 2 * (y 3) ^ 2 * (1 / k ^ 2 + ω)
  have hω : 0 ≤ ω := Real.rpow_nonneg hv.1.le _
  have hS : 0 ≤ S := by dsimp [S]; positivity [hu.1, hv.1]
  constructor
  · exact H.trans (mul_le_mul_of_nonneg_right (by linarith : C ≤ 7 * C) hS)
  · intro hhalf
    have hdec := entrance_active_half_decay hv.1 hhalf hk1
    rw [entrance_strong_weight_eq_rpow hv.1] at hdec
    have htail : 0 ≤ y 2 * (y 3) ^ 2 / k * (1 / k ^ 2 + ω) := by positivity [hv.1]
    have hform : S ≤ 7 * (J / k) := by
      have HU := mul_le_mul_of_nonneg_left hdec hu.1.le
      dsimp [S, J]
      simp only [div_eq_mul_inv] at HU htail ⊢
      nlinarith only [HU, htail]
    exact H.trans ((mul_le_mul_of_nonneg_left hform hC.le).trans_eq (by ring))

end BianchiIX
