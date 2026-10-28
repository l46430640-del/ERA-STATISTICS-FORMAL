import BianchiIX.Dynamics.EntrancePhysicalReturnDifferential
import BianchiIX.Dynamics.EntranceReturnTerminalWeights
import BianchiIX.Dynamics.EntranceFullReturnColumns
import BianchiIX.Analysis.EntranceWallTerminalCorrection

noncomputable section

namespace BianchiIX

/-- All three physical wall-input columns follow directly from terminal amplitude products. -/
theorem exists_entrance_physical_wall_bounds :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ (y : ProjectiveState) (θ : ℝ),
      let k := coreRadius (y 0) (y 2)
      7 / 4 ≤ k → 1 ≤ y 0 → (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) →
      (0 < y 3 ∧ y 3 ≤ ε) → (θ = 1 ∨ (θ = 1 / k ^ 2 ∧ k * (y 1 + y 3) ^ 2 ≤ 1)) →
      ∃ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ ∧
      let z := entranceRadialCoordinates y
      let ω := Real.exp (-2 * (-Real.log (y 2)) / k)
      let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
      |fderiv ℝ F z (Pi.single 1 1)| ≤ C * y 2 / k ∧
      |fderiv ℝ F z (Pi.single 2 1)| ≤ C * (y 1 + y 2 * (y 3) ^ 2) ∧
      |fderiv ℝ F z (Pi.single 3 1)| ≤ C * (y 1 * y 2 + (y 2) ^ 2 * y 3 * (θ + ω)) / k := by
  obtain ⟨A, hA, ε, hε, hεsmall, HA⟩ := exists_entrance_return_full_columns
  obtain ⟨T, hT, HT⟩ := exists_entrance_return_correction_variation
  let B := T * (2 + 8 * A)
  let C := A + B
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨C, add_pos hA hB, ε, hε, hεsmall, ?_⟩
  intro y θ k hk hm hu hv hw hθ
  obtain ⟨Ψ, HΨ, HQ, HU, HW⟩ := HA y θ hk hm hu hv hw hθ
  refine ⟨Ψ, HΨ, ?_⟩
  intro z ω F
  let p := entranceReturnState y
  let b := p 1 + p 3
  let Q := fun z => entranceStableRadius (entranceReturnState (Ψ z))
  let Logs := fun z => entranceLogWalls 1 (entranceReturnState (Ψ z))
  let E := fun z => entranceRadiusCorrection (entranceReturnState (Ψ z))
  let J := y 1 * y 2 + (y 2) ^ 2 * y 3 * (θ + ω)
  let K := y 1 + y 2 * (y 3) ^ 2
  have hk0 : 0 < k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hu' : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := ⟨hu.1.le, hu.2.trans hεsmall⟩
  have hw' : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := ⟨hw.1.le, hw.2.trans hεsmall⟩
  have hθ01 : 0 ≤ θ ∧ θ ≤ 1 := by
    rcases hθ with rfl | ⟨rfl, _⟩
    · norm_num
    · exact ⟨by positivity, (div_le_one (sq_pos_of_pos hk0)).mpr (one_le_pow₀ hk1)⟩
  have hL : 0 ≤ -Real.log (y 2) := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have hω : 0 ≤ ω ∧ ω ≤ 1 := ⟨(Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by nlinarith only [hL]) hk0.le)⟩
  have hJ : 0 ≤ J := by dsimp [J]; positivity [hu.1, hv.1, hw.1, hθ01.1, hω.1]
  have hK : 0 ≤ K := by dsimp [K]; positivity [hu.1, hv.1]
  have HR := (entranceReturn_regular hk hm hu' hv hw').1
  have hp : entranceRegion k p := entranceReturn_region hk hm hu' hv hw' _ ⟨HR.1.1.1.le, le_rfl⟩
  have hb : 0 ≤ b := add_nonneg hp.2.2.1.1 hp.2.2.2.2.1
  have Hw := entranceReturn_terminal_weights hk hm hu' hv hw'
  have Hforms := entrance_terminal_wall_forms hA.le hk1 ⟨hu.1, by linarith [hu'.2]⟩
    ⟨hv.1, hv.2.le⟩ ⟨hw.1, by linarith [hw'.2]⟩ hp.2.2.1.1 hp.2.2.2.2.1 hθ01.1 hω
    Hw.1 Hw.2.2.2.1 Hw.2.2.2.2.1 Hw.2.2.2.2.2
  have hQu : |fderiv ℝ Q z (Pi.single 1 1)| ≤ A * (y 2 / k) := by simpa only [mul_div_assoc] using HQ.2.1
  have hQw : |fderiv ℝ Q z (Pi.single 3 1)| ≤ A * (J / k) := by
    have Hnum : y 1 * y 2 + θ * (y 2) ^ 2 * y 3 ≤ J := by
      have H : 0 ≤ (y 2) ^ 2 * y 3 * ω := by positivity [hw.1, hω.1]
      dsimp [J]
      nlinarith only [H]
    apply HQ.2.2.2.trans
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right Hnum hk0.le) hA.le
  have hQv : |fderiv ℝ Q z (Pi.single 2 1)| ≤ A * K := by
    apply HQ.2.2.1.trans (mul_le_mul_of_nonneg_left ?_ hA.le)
    have H := mul_le_mul_of_nonneg_right hθ01.2 (show 0 ≤ y 2 * (y 3) ^ 2 by positivity [hv.1])
    dsimp [K]
    nlinarith only [H]
  have hdiag {x a c : ℝ} (ha : 0 ≤ a) (h : |x - a| ≤ c) : |x| ≤ a + c := by
    have H := abs_add_le (x - a) a
    rw [sub_add_cancel, abs_of_nonneg ha] at H
    linarith only [H, h]
  have hUu := hdiag (show 0 ≤ 1 / y 1 by positivity [hu.1]) HU.2.1
  have hWw := hdiag (show 0 ≤ 1 / y 3 by positivity [hw.1]) HW.2.2.2
  have hwall (i : Fin 4) {SU SW Z : ℝ}
      (hU : |fderiv ℝ Logs z (Pi.single i 1) 0| ≤ SU)
      (hW : |fderiv ℝ Logs z (Pi.single i 1) 1| ≤ SW)
      (hform : b / k * (p 1 * SU + p 3 * SW) ≤ (2 + 4 * A) * Z) :
      b / k * (p 1 * |fderiv ℝ Logs z (Pi.single i 1) 0| + p 3 * |fderiv ℝ Logs z (Pi.single i 1) 1|) ≤
        (2 + 4 * A) * Z :=
    (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hU hp.2.2.1.1)
      (mul_le_mul_of_nonneg_left hW hp.2.2.2.2.1)) (div_nonneg hb hk0.le)).trans hform
  have hcorr (i : Fin 4) := HT y hk hm ⟨hu.1, hu'.2⟩ hv ⟨hw.1, hw'.2⟩ Ψ HΨ (Pi.single i 1)
  have hEu : |fderiv ℝ E z (Pi.single 1 1)| ≤ B * (y 2 / k) :=
    entrance_terminal_correction_bound hA.le hT.le (div_nonneg hv.1.le hk0.le) Hforms.1 hQu
      (hwall 1 hUu HW.2.1 Hforms.2.1) (hcorr 1)
  have hEw : |fderiv ℝ E z (Pi.single 3 1)| ≤ B * (J / k) :=
    entrance_terminal_correction_bound hA.le hT.le (div_nonneg hJ hk0.le) Hforms.1 hQw
      (hwall 3 HU.2.2.2 hWw Hforms.2.2.1) (hcorr 3)
  have hEv : |fderiv ℝ E z (Pi.single 2 1)| ≤ B * K :=
    entrance_terminal_correction_bound hA.le hT.le hK Hforms.1 hQv
      (hwall 2 HU.2.2.1 HW.2.2.1 Hforms.2.2.2) (hcorr 2)
  have hphysical (i : Fin 4) {Z : ℝ}
      (hQ : |fderiv ℝ Q z (Pi.single i 1)| ≤ A * Z)
      (hE : |fderiv ℝ E z (Pi.single i 1)| ≤ B * Z) : |fderiv ℝ F z (Pi.single i 1)| ≤ C * Z := by
    have HE := HΨ.return_correction_difference hk hm hu' hv hw' (Pi.single i 1)
    have hid : fderiv ℝ F z (Pi.single i 1) = fderiv ℝ Q z (Pi.single i 1) - fderiv ℝ E z (Pi.single i 1) := by
      linarith only [HE]
    rw [hid]
    exact (abs_sub _ _).trans ((add_le_add hQ hE).trans_eq (by dsimp [C]; ring))
  refine ⟨?_, hphysical 2 hQv hEv, ?_⟩
  · simpa only [mul_div_assoc] using hphysical 1 hQu hEu
  · simpa only [mul_div_assoc] using hphysical 3 hQw hEw

end BianchiIX
