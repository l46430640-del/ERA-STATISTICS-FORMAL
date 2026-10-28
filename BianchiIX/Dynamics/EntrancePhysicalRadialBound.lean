import BianchiIX.Dynamics.EntrancePhysicalReturnDifferential
import BianchiIX.Dynamics.EntranceReturnTerminalWeights
import BianchiIX.Dynamics.EntranceFullReturnColumns
import BianchiIX.Analysis.EntranceRadialTerminalCorrection

noncomputable section

namespace BianchiIX

/-- The radial column of the physical arrival retains the terminal weak decay in (C.39). -/
theorem exists_entrance_physical_radial_bound :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ (y : ProjectiveState) (θ : ℝ),
      let k := coreRadius (y 0) (y 2)
      7 / 4 ≤ k → 1 ≤ y 0 → (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) →
      (0 < y 3 ∧ y 3 ≤ ε) → (θ = 1 ∨ (θ = 1 / k ^ 2 ∧ k * (y 1 + y 3) ^ 2 ≤ 1)) →
      ∃ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ ∧
      let z := entranceRadialCoordinates y
      let L := -Real.log (y 2)
      let ω := Real.exp (-2 * L / k)
      let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
      let E := fun z => entranceRadiusCorrection (entranceReturnState (Ψ z))
      |fderiv ℝ E z (Pi.single 0 1)| ≤
        C * (y 1 * y 2 + (1 + L / k) * ((y 2) ^ 2 * (y 3) ^ 2 * ω)) / k ^ 2 ∧
      |fderiv ℝ F z (Pi.single 0 1) - 1| ≤
        C * (y 1 * y 2 + (y 2) ^ 2 * (y 3) ^ 2 * (θ + (1 + L / k) * ω)) / k ^ 2 := by
  obtain ⟨A, hA, ε, hε, hεsmall, HA⟩ := exists_entrance_return_full_columns
  obtain ⟨T, hT, HT⟩ := exists_entrance_return_correction_variation
  let B := T * (2 + 13 * A)
  let C := A + B
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := add_pos hA hB
  have hBC : B ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ε, hε, hεsmall, ?_⟩
  intro y θ k hk hm hu hv hw hθ
  obtain ⟨Ψ, HΨ, HQ, HU, HW⟩ := HA y θ hk hm hu hv hw hθ
  refine ⟨Ψ, HΨ, ?_⟩
  intro z L ω F E
  let Q := fun z => entranceStableRadius (entranceReturnState (Ψ z))
  let Logs := fun z => entranceLogWalls 1 (entranceReturnState (Ψ z))
  let p := entranceReturnState y
  let P := y 1 * y 2
  let S := (y 2) ^ 2 * (y 3) ^ 2 * ω
  let H := P + θ * (y 2 * y 3) ^ 2
  let J := P + (1 + L / k) * S
  let R := P + (y 2) ^ 2 * (y 3) ^ 2 * (θ + (1 + L / k) * ω)
  have hk0 : 0 < k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hL : 0 ≤ L := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have hθ01 : 0 ≤ θ ∧ θ ≤ 1 := by
    rcases hθ with rfl | ⟨rfl, _⟩
    · norm_num
    · exact ⟨by positivity, (div_le_one (sq_pos_of_pos hk0)).mpr (one_le_pow₀ hk1)⟩
  have hu' : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := ⟨hu.1.le, hu.2.trans hεsmall⟩
  have hw' : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := ⟨hw.1.le, hw.2.trans hεsmall⟩
  have hweights := entranceReturn_terminal_weights hk hm hu' hv hw'
  have hwait := entrance_phase_waiting_budget hu.1.le ⟨hv.1, hv.2.le⟩ ⟨hw.1.le, by linarith [hw'.2]⟩ hθ01
  have hH0 : 0 ≤ H := hwait.1
  have hH2 : H ≤ 2 := by linarith only [hwait.2.1, hu'.2, hw'.2]
  have hinc : |fderiv ℝ Q z (Pi.single 0 1) - 1| ≤ 2 * A := by
    apply HQ.1.trans
    calc
      A * H / k ^ 2 ≤ A * H := div_le_self (mul_nonneg hA.le hH0) (one_le_pow₀ hk1)
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hH2 hA.le]
  have hQ : |fderiv ℝ Q z (Pi.single 0 1)| ≤ 1 + 2 * A := by
    have Htriangle := abs_add_le (fderiv ℝ Q z (Pi.single 0 1) - 1) (1 : ℝ)
    simp only [sub_add_cancel, abs_one] at Htriangle
    linarith only [Htriangle, hinc]
  have HR := (entranceReturn_regular hk hm hu' hv hw').1
  have hp : entranceRegion k p := entranceReturn_region hk hm hu' hv hw' _ ⟨HR.1.1.1.le, le_rfl⟩
  have hS : 0 ≤ S := by dsimp [S, ω]; positivity
  have hJ : 0 ≤ J := by dsimp [J, P]; positivity [hu.1, hv.1]
  have hcorr := HT y hk hm ⟨hu.1, hu'.2⟩ hv ⟨hw.1, hw'.2⟩ Ψ HΨ (Pi.single 0 1)
  have hfast : k * L * (p 1 + p 3) * p 1 ≤ 6 * P := by
    simpa only [P, mul_assoc] using hweights.2.1
  have hslow : (L / k) * (p 1 + p 3) * p 3 ≤ 3 * P + (L / k) * S := by
    simpa only [P, S, mul_assoc] using hweights.2.2.1
  have HE : |fderiv ℝ E z (Pi.single 0 1)| ≤ B * J / k ^ 2 :=
    entrance_radial_terminal_correction hA.le hT.le hk0 hL hS hp.2.2.1.1 hp.2.2.2.2.1
      hweights.1 hfast hslow hQ HU.1 HW.1 hcorr
  have hHR : H ≤ R := by
    have hnonneg : 0 ≤ (1 + L / k) * S := by positivity
    dsimp [H, R, S] at *
    nlinarith only [hnonneg]
  have hJR : J ≤ R := by
    have hnonneg : 0 ≤ θ * (y 2 * y 3) ^ 2 := by positivity [hθ01.1]
    dsimp [J, R, S] at *
    nlinarith only [hnonneg]
  refine ⟨HE.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBC hJ) (sq_nonneg k)), ?_⟩
  have hid : fderiv ℝ F z (Pi.single 0 1) - 1 =
      (fderiv ℝ Q z (Pi.single 0 1) - 1) - fderiv ℝ E z (Pi.single 0 1) := by
    have Hdiff := HΨ.return_correction_difference hk hm hu' hv hw' (Pi.single 0 1)
    linarith only [Hdiff]
  rw [hid]
  calc
    _ ≤ |fderiv ℝ Q z (Pi.single 0 1) - 1| + |fderiv ℝ E z (Pi.single 0 1)| := abs_sub _ _
    _ ≤ A * H / k ^ 2 + B * J / k ^ 2 := add_le_add HQ.1 HE
    _ = (A * H + B * J) / k ^ 2 := by ring
    _ ≤ (A * R + B * R) / k ^ 2 := div_le_div_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_left hHR hA.le) (mul_le_mul_of_nonneg_left hJR hB.le)) (sq_nonneg k)
    _ = _ := by dsimp [C, R, P]; ring

/-- The physical radial derivative has the fixed-amplitude estimate stated in (C.25). -/
theorem exists_entrance_physical_radial_basic :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ y : ProjectiveState,
      let k := coreRadius (y 0) (y 2)
      7 / 4 ≤ k → 1 ≤ y 0 → (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) →
      (0 < y 3 ∧ y 3 ≤ ε) →
      ∃ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ ∧
      let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
      |fderiv ℝ F (entranceRadialCoordinates y) (Pi.single 0 1) - 1| ≤
        C * (y 1 * y 2 + (y 2) ^ 2 * (y 1 + y 3) ^ 2) / k ^ 2 := by
  obtain ⟨C, hC, ε, hε, hεsmall, HC⟩ := exists_entrance_physical_radial_bound
  refine ⟨2 * C, by positivity, ε, hε, hεsmall, ?_⟩
  intro y k hk hm hu hv hw
  obtain ⟨Ψ, HΨ, _, HF⟩ := HC y 1 hk hm hu hv hw (Or.inl rfl)
  refine ⟨Ψ, HΨ, HF.trans ?_⟩
  let L := -Real.log (y 2)
  let ω := Real.exp (-2 * L / k)
  have hk1 : 1 ≤ k := by linarith
  have hL : 0 ≤ L := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have hω : (1 + L / k) * ω ≤ 1 := (entrance_terminal_clock_weights hk1 hL).2.2.2.2
  have hsq : (y 3) ^ 2 ≤ (y 1 + y 3) ^ 2 :=
    pow_le_pow_left₀ hw.1.le (by linarith only [hu.1]) 2
  have hprod := mul_le_mul_of_nonneg_left hsq (sq_nonneg (y 2))
  have hweight := mul_le_mul_of_nonneg_left hω (show 0 ≤ (y 2) ^ 2 * (y 3) ^ 2 by positivity)
  have hnum : y 1 * y 2 + (y 2) ^ 2 * (y 3) ^ 2 * (1 + (1 + L / k) * ω) ≤
      2 * (y 1 * y 2 + (y 2) ^ 2 * (y 1 + y 3) ^ 2) := by
    nlinarith only [hweight, hprod, mul_nonneg hu.1.le hv.1.le]
  calc
    _ ≤ C * (2 * (y 1 * y 2 + (y 2) ^ 2 * (y 1 + y 3) ^ 2)) / k ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum hC.le) (sq_nonneg k)
    _ = _ := by ring

end BianchiIX
