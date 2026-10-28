import BianchiIX.Dynamics.EntrancePhysicalBoundary

noncomputable section

namespace BianchiIX

/-- The five bounds of (C.25) hold for the same ordinary C2 arrival on nonnegative walls. -/
theorem exists_entrance_physical_basic_bounds_nonneg :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ y : ProjectiveState,
      let k := coreRadius (y 0) (y 2)
      7 / 4 ≤ k → 1 ≤ y 0 → (0 ≤ y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) →
      (0 ≤ y 3 ∧ y 3 ≤ ε) →
      ∃ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ ∧
      let z := entranceRadialCoordinates y
      let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
      ContDiffAt ℝ 2 F z ∧
      |F z - z 0| ≤ C * (y 1 * y 2 + (y 2) ^ 2 * (y 1 + y 3) ^ 2) / k ∧
      |fderiv ℝ F z (Pi.single 0 1) - 1| ≤
        C * (y 1 * y 2 + (y 2) ^ 2 * (y 1 + y 3) ^ 2) / k ^ 2 ∧
      |fderiv ℝ F z (Pi.single 1 1)| ≤ C * (y 2 + (y 2) ^ 2 * (y 1 + y 3)) / k ∧
      |fderiv ℝ F z (Pi.single 2 1)| ≤ C * (y 1 + y 2 * (y 1 + y 3) ^ 2) ∧
      |fderiv ℝ F z (Pi.single 3 1)| ≤ C * (y 1 * y 2 + (y 2) ^ 2 * (y 1 + y 3)) / k := by
  obtain ⟨C, hC, ε, hε, hεsmall, HC⟩ := exists_entrance_physical_bounds_nonneg
  refine ⟨2 * C, by positivity, ε, hε, hεsmall, ?_⟩
  intro y k hk hm hu hv hw
  obtain ⟨Ψ, HΨ, Hreg, H0, Hr, Hu, Hv, Hw⟩ := HC y 1 hk hm hu hv hw (Or.inl rfl)
  refine ⟨Ψ, HΨ, ?_⟩
  intro z F
  let L := -Real.log (y 2)
  let ω := Real.exp (-2 * L / k)
  have hk0 : 0 < k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hL : 0 ≤ L := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have hω : ω ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (by nlinarith only [hL]) hk0.le)
  have hwait : (1 + L / k) * ω ≤ 1 := (entrance_terminal_clock_weights hk1 hL).2.2.2.2
  have hsq : (y 3) ^ 2 ≤ (y 1 + y 3) ^ 2 :=
    pow_le_pow_left₀ hw.1 (by linarith only [hu.1]) 2
  have hprod := mul_le_mul_of_nonneg_left hsq (sq_nonneg (y 2))
  have hweight := mul_le_mul_of_nonneg_left hwait (show 0 ≤ (y 2) ^ 2 * (y 3) ^ 2 by positivity)
  have hnum0 : y 1 * y 2 + (y 2) ^ 2 * (y 3) ^ 2 * (1 + ω) ≤
      2 * (y 1 * y 2 + (y 2) ^ 2 * (y 1 + y 3) ^ 2) := by
    have H := mul_le_mul_of_nonneg_left hω (show 0 ≤ (y 2) ^ 2 * (y 3) ^ 2 by positivity)
    nlinarith only [H, hprod, mul_nonneg hu.1 hv.1.le]
  have hnumr : y 1 * y 2 + (y 2) ^ 2 * (y 3) ^ 2 * (1 + (1 + L / k) * ω) ≤
      2 * (y 1 * y 2 + (y 2) ^ 2 * (y 1 + y 3) ^ 2) := by
    nlinarith only [hweight, hprod, mul_nonneg hu.1 hv.1.le]
  have hnumu : y 2 ≤ 2 * (y 2 + (y 2) ^ 2 * (y 1 + y 3)) := by
    have H : 0 ≤ (y 2) ^ 2 * (y 1 + y 3) := by positivity [hu.1, hw.1]
    linarith only [H, hv.1]
  have hnumv : y 1 + y 2 * (y 3) ^ 2 ≤ 2 * (y 1 + y 2 * (y 1 + y 3) ^ 2) := by
    have H := mul_le_mul_of_nonneg_left hsq hv.1.le
    have H0 : 0 ≤ y 1 + y 2 * (y 1 + y 3) ^ 2 := by positivity [hu.1, hv.1]
    linarith only [H, H0]
  have hnumw : y 1 * y 2 + (y 2) ^ 2 * y 3 * (1 + ω) ≤
      2 * (y 1 * y 2 + (y 2) ^ 2 * (y 1 + y 3)) := by
    have H := mul_le_mul_of_nonneg_left hω (show 0 ≤ (y 2) ^ 2 * y 3 by positivity [hw.1])
    nlinarith only [H, mul_nonneg hu.1 hv.1.le, mul_nonneg (sq_nonneg (y 2)) hu.1]
  have hscale {x a b : ℝ} (hx : x ≤ C * a) (hab : a ≤ 2 * b) : x ≤ (2 * C) * b :=
    hx.trans ((mul_le_mul_of_nonneg_left hab hC.le).trans_eq (by ring))
  refine ⟨Hreg, ?_, ?_, ?_, hscale Hv hnumv, ?_⟩
  · simpa only [mul_div_assoc] using hscale (by simpa only [ω, L, k, mul_div_assoc] using H0)
      ((div_le_div_of_nonneg_right hnum0 hk0.le).trans_eq (by ring))
  · simpa only [mul_div_assoc] using hscale (by simpa only [ω, L, k, mul_div_assoc] using Hr)
      ((div_le_div_of_nonneg_right hnumr (sq_nonneg k)).trans_eq (by ring))
  · simpa only [mul_div_assoc] using hscale (by simpa only [mul_div_assoc] using Hu)
      ((div_le_div_of_nonneg_right hnumu hk0.le).trans_eq (by ring))
  · simpa only [mul_div_assoc] using hscale (by simpa only [ω, L, k, mul_div_assoc] using Hw)
      ((div_le_div_of_nonneg_right hnumw hk0.le).trans_eq (by ring))

end BianchiIX
