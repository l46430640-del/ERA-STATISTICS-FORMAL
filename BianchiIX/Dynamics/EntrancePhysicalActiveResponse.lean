import BianchiIX.Dynamics.EntranceActiveEndpointBounds
import BianchiIX.Dynamics.EntranceActiveTerminalDrift
import BianchiIX.Dynamics.EntrancePhysicalReturnDifferential

noncomputable section

namespace BianchiIX

open Set

/-- The physical active column retains both the fast terminal wall and the weak-wall square. -/
theorem exists_entrance_physical_active_response :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∀ (y : ProjectiveState),
      7 / 4 ≤ coreRadius (y 0) (y 2) → 1 ≤ y 0 →
      (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) → (0 < y 3 ∧ y 3 ≤ ε) →
      coreRadius (y 0) (y 2) ^ 2 * (y 1 + y 3) ≤ 1 →
      ∀ (Ψ : ProjectiveState → ProjectiveState), EntranceRadialInverseAt y Ψ →
      let k := coreRadius (y 0) (y 2)
      let z := entranceRadialCoordinates y
      let a := Real.exp (-k * (-Real.log (y 2)) / 3)
      let ω := Real.exp (-2 * (-Real.log (y 2)) / k)
      let E := fun z => entranceRadiusCorrection (entranceReturnState (Ψ z))
      let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
      |fderiv ℝ E z (Pi.single 2 1)| ≤ C * (y 1 * a + y 2 * (y 3) ^ 2 * ω / k) ∧
        |fderiv ℝ F z (Pi.single 2 1)| ≤ C *
          (y 1 / k + y 1 * a + y 2 * (y 3) ^ 2 / k * (1 / k ^ 2 + ω)) := by
  obtain ⟨C, hC, ε, hε, hεcap, HC⟩ := exists_entrance_active_endpoint_bounds
  obtain ⟨D, hD, HD⟩ := exists_entrance_active_terminal_drift
  obtain ⟨T, hT, HT⟩ := exists_entrance_return_correction_variation
  let K := 2 * C + 2 * D + 12
  let P := C + D + 5 * T * K
  have hK : 0 < K := by dsimp [K]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  refine ⟨P, hP, ε, hε, hεcap, ?_⟩
  intro y hk hm hu hv hw hsmall Ψ HΨ k z a ω E F
  let p := entranceReturnState y
  let b := p 1 + p 3
  let Q := fun z => entranceStableRadius (entranceReturnState (Ψ z))
  let A := y 1 * y 2 * a
  let B := (y 2) ^ 2 * (y 3) ^ 2 * ω
  let H := y 1 * y 2 + (y 2 * y 3) ^ 2 / k ^ 2
  let q := y 2 * fderiv ℝ Q z (Pi.single 2 1)
  have hk0 : 0 < k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hu' : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := ⟨hu.1.le, hu.2.trans hεcap⟩
  have hw' : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := ⟨hw.1.le, hw.2.trans hεcap⟩
  have hu1 : y 1 ≤ 1 := by linarith [hu'.2]
  have hw1 : y 3 ≤ 1 := by linarith [hw'.2]
  have hb01 : 0 ≤ y 1 + y 3 ∧ y 1 + y 3 ≤ 1 := ⟨by positivity [hu.1, hw.1], by linarith [hu'.2, hw'.2]⟩
  have hrefined : k * (y 1 + y 3) ^ 2 ≤ 1 := by
    have H1 : (y 1 + y 3) ^ 2 ≤ y 1 + y 3 := by nlinarith only [hb01.1, hb01.2]
    exact (mul_le_mul_of_nonneg_left H1 hk0.le).trans
      ((mul_le_mul_of_nonneg_right (by nlinarith only [hk1] : k ≤ k ^ 2) hb01.1).trans hsmall)
  have HR := (entranceReturn_regular hk hm hu' hv hw').1
  have hp : entranceRegion k p := entranceReturn_region hk hm hu' hv hw' _ ⟨HR.1.1.1.le, le_rfl⟩
  have hb : 0 ≤ b := add_nonneg hp.2.2.1.1 hp.2.2.2.2.1
  have hclock := entrance_terminal_clock_weights hk1 (neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le))
  have ha : 0 ≤ a ∧ a ≤ 1 := hclock.1
  have hω : 0 ≤ ω ∧ ω ≤ 1 := by
    dsimp only [ω]
    rw [← hclock.2.2.2.1]
    exact ⟨sq_nonneg _, pow_le_one₀ hclock.2.1.1 hclock.2.1.2⟩
  have hA : 0 ≤ A ∧ A ≤ 1 := ⟨by dsimp [A]; positivity [hu.1, hv.1, ha.1],
    (mul_le_of_le_one_right (mul_nonneg hu'.1 hv.1.le) ha.2).trans
      ((mul_le_of_le_one_right hu'.1 hv.2.le).trans hu1)⟩
  have hB : 0 ≤ B ∧ B ≤ 1 := by
    refine ⟨by dsimp [B]; positivity [hω.1], ?_⟩
    exact (mul_le_of_le_one_right (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hω.2).trans
      (mul_le_one₀ (pow_le_one₀ hv.1.le hv.2.le) (sq_nonneg _) (pow_le_one₀ hw'.1 hw1))
  have hθ : 0 ≤ 1 / k ^ 2 ∧ 1 / k ^ 2 ≤ 1 :=
    ⟨by positivity, (div_le_one (sq_pos_of_pos hk0)).mpr (one_le_pow₀ hk1)⟩
  have hH := entrance_phase_waiting_budget hu'.1 ⟨hv.1, hv.2.le⟩ ⟨hw'.1, hw1⟩ hθ
  simp only [one_div_mul_eq_div] at hH
  have hH2 : 0 ≤ H ∧ H ≤ 2 := ⟨hH.1, hH.2.1.trans (by linarith [hb01.2])⟩
  have hG : |entranceRadialDrift p| ≤ D * (A + B / k ^ 4) := HD y hk hm hu' hv hw' hrefined
  have hG2 : |entranceRadialDrift p| ≤ 2 * D := hG.trans
    ((mul_le_mul_of_nonneg_left (add_le_add hA.2
      ((div_le_self hB.1 (one_le_pow₀ hk1)).trans hB.2)) hD.le).trans_eq (by ring))
  have hresponse := HC y hk hm hu hv hw hsmall Ψ HΨ
  have hraw := entrance_active_endpoint_unshift hk1 hC.le hD.le hH2 hG2 hresponse.1 hresponse.2
    (entranceWallLogRates_base_bounds hk hp).2.1 (entranceWallLogRates_base_bounds hk hp).2.2
  have hdec := entranceReturn_decay hk hm hu' hv hw'
  have hproducts := entrance_active_terminal_products ⟨hu'.1, hu1⟩ ⟨hv.1.le, hv.2.le⟩ ⟨hw'.1, hw1⟩
    hp.2.2.1.1 hp.2.2.2.2.1 ha hclock.2.1 hdec.1 hdec.2
  have hforms : b ^ 2 ≤ 2 * (A + B) ∧ b * p 1 ≤ 2 * A ∧ b * p 3 ≤ A + B := by
    simpa only [hclock.2.2.2.1] using hproducts.2.2
  have hc := HT y hk hm ⟨hu.1, hu'.2⟩ hv ⟨hw.1, hw'.2⟩ Ψ HΨ (y 2 • Pi.single 2 1)
  simp only [map_smul, Pi.smul_apply, smul_eq_mul] at hc
  have hE : |y 2 * fderiv ℝ E z (Pi.single 2 1)| ≤ 5 * T * K * (A + B / k) :=
    entrance_active_terminal_correction hk1 hT.le hK.le hA.1 hB.1 hb hp.2.2.1.1 hp.2.2.2.2.1
      hforms.1 hforms.2.1 hforms.2.2 hraw.1 hraw.2.1 hraw.2.2 hc
  have hid := HΨ.return_correction_difference hk hm hu' hv hw' (y 2 • Pi.single 2 1)
  simp only [map_smul, smul_eq_mul] at hid
  have hphys : y 2 * fderiv ℝ F z (Pi.single 2 1) =
      (q + entranceRadialDrift p) - entranceRadialDrift p - y 2 * fderiv ℝ E z (Pi.single 2 1) := by
    linarith only [hid]
  have hBk : B / k ^ 4 ≤ B / k := div_le_div_of_nonneg_left hB.1 hk0 (by
    have H := pow_le_pow_right₀ hk1 (by decide : 1 ≤ 4)
    simpa only [pow_one] using H)
  have hF : |y 2 * fderiv ℝ F z (Pi.single 2 1)| ≤ C * H / k +
      (D + 5 * T * K) * (A + B / k) := by
    rw [hphys]
    exact ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans
      ((add_le_add (add_le_add hresponse.1 (hG.trans
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl hBk) hD.le))) hE).trans_eq (by ring))
  have hPk : 5 * T * K ≤ P := by dsimp [P]; linarith
  have hPC : C ≤ P := by
    have HH : 0 ≤ 5 * T * K := by positivity
    dsimp [P]
    linarith
  have hPD : D + 5 * T * K ≤ P := by dsimp [P]; linarith
  constructor
  · apply (mul_le_mul_iff_right₀ hv.1).mp
    calc
      y 2 * |fderiv ℝ E z (Pi.single 2 1)| = |y 2 * fderiv ℝ E z (Pi.single 2 1)| := by
        rw [abs_mul, abs_of_pos hv.1]
      _ ≤ 5 * T * K * (A + B / k) := hE
      _ ≤ P * (A + B / k) := mul_le_mul_of_nonneg_right hPk (by positivity [hA.1, hB.1])
      _ = y 2 * (P * (y 1 * a + y 2 * (y 3) ^ 2 * ω / k)) := by dsimp [A, B]; ring
  · apply (mul_le_mul_iff_right₀ hv.1).mp
    calc
      y 2 * |fderiv ℝ F z (Pi.single 2 1)| = |y 2 * fderiv ℝ F z (Pi.single 2 1)| := by
        rw [abs_mul, abs_of_pos hv.1]
      _ ≤ C * H / k + (D + 5 * T * K) * (A + B / k) := hF
      _ ≤ P * H / k + P * (A + B / k) := add_le_add
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hPC hH2.1) hk0.le)
        (mul_le_mul_of_nonneg_right hPD (by positivity [hA.1, hB.1]))
      _ = y 2 * (P * (y 1 / k + y 1 * a + y 2 * (y 3) ^ 2 / k * (1 / k ^ 2 + ω))) := by
        dsimp [A, B, H]
        ring

end BianchiIX
