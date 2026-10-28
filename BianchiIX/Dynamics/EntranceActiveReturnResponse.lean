import BianchiIX.Dynamics.EntranceActiveTransport
import BianchiIX.Dynamics.EntranceOrdinaryReturnResponse
import BianchiIX.Dynamics.EntranceTransportDrift
import BianchiIX.Analysis.EntranceTransportResponse

noncomputable section

namespace BianchiIX

open Set

/-- The active-wall column of the actual return, recovered without integrating a fourth variational equation. -/
theorem exists_entrance_active_return_response :
    ∃ C > (0 : ℝ), ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧
      ∀ (y : ProjectiveState) (θ : ℝ),
      let k := coreRadius (y 0) (y 2)
      7 / 4 ≤ k → 1 ≤ y 0 → (0 < y 1 ∧ y 1 ≤ ε) → (0 < y 2 ∧ y 2 < 1) →
      (0 < y 3 ∧ y 3 ≤ ε) → (θ = 1 ∨ (θ = 1 / k ^ 2 ∧ k * (y 1 + y 3) ^ 2 ≤ 1)) →
      ∀ (Ψ : ProjectiveState → ProjectiveState), EntranceRadialInverseAt y Ψ →
      let z := entranceRadialCoordinates y
      let Q := fun z => entranceStableRadius (entranceReturnState (Ψ z))
      let L := fun z => entranceLogWalls 1 (entranceReturnState (Ψ z))
      let H := y 1 * y 2 + θ * (y 2 * y 3) ^ 2
      |fderiv ℝ Q z (Pi.single 2 1)| ≤ C * (y 1 + θ * y 2 * (y 3) ^ 2) ∧
      |y 2 * fderiv ℝ L z (Pi.single 2 1) 0 + entranceStrongLogRate y| +
        k ^ 2 * |y 2 * fderiv ℝ L z (Pi.single 2 1) 1 + entranceWeakLogRate y| ≤
          C * (k * y 1 + y 3 + (-Real.log (y 2)) * H) ∧
      |fderiv ℝ L z (Pi.single 2 1) 0| ≤ C * k / y 2 ∧
      |fderiv ℝ L z (Pi.single 2 1) 1| ≤ C / y 2 := by
  obtain ⟨T, hT, K, hK, F, hF, ε, hε, hεsmall, HP⟩ := exists_entrance_ordinary_return_response
  obtain ⟨A, hA, HA⟩ := exists_entrance_transport_drift_bound
  let P := A * (1 + 4 * F) + 42 * K
  let B := T * (21 + 2 * (A + 21 * K))
  let C := P + 12 + 5 * B
  have hP : 0 < P := by dsimp [P]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hCP : P ≤ C := by dsimp [C]; linarith only [hB]
  have hCB : B ≤ C := by dsimp [C]; linarith only [hP, hB]
  have hClog : 12 + 4 * B ≤ C := by dsimp [C]; linarith only [hP, hB]
  refine ⟨C, hC, ε, hε, hεsmall, ?_⟩
  intro y θ k hk hm hu hv hw hθ Ψ HΨ z Q L H
  have hk0 : 0 < k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hu' : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := ⟨hu.1.le, hu.2.trans hεsmall⟩
  have hw' : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := ⟨hw.1.le, hw.2.trans hεsmall⟩
  have hu1 : y 1 ≤ 1 := by linarith [hu'.2]
  have hw1 : y 3 ≤ 1 := by linarith [hw'.2]
  have hy : entranceRegion k y := ⟨hm, by rw [sub_self, abs_zero]; dsimp [k]; linarith,
    hu', ⟨hv.1.le, hv.2.le⟩, hw'⟩
  have hθ01 : 0 ≤ θ ∧ θ ≤ 1 := by
    rcases hθ with rfl | ⟨rfl, _⟩
    · norm_num
    · exact ⟨by positivity, (div_le_one (sq_pos_of_pos hk0)).mpr (one_le_pow₀ hk1)⟩
  have hH := entrance_phase_waiting_budget hu.1.le ⟨hv.1, hv.2.le⟩ ⟨hw.1.le, hw1⟩ hθ01
  have hH2 : H ≤ 2 := by linarith only [hH.2.1, hu1, hw1]
  have hLH : (-Real.log (y 2)) * H ≤ 2 := by linarith only [hH.2.2, hu1, hw1]
  have hlog : 0 ≤ -Real.log (y 2) := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have hG : |entranceRadialDrift y| ≤ A * H := HA k θ y hk hy hv.1 (hθ.imp_right And.left)
  obtain ⟨_, hU, hW⟩ := entranceWallLogRates_base_bounds hk hy
  let d : ProjectiveState := ![entranceRadialDrift y, y 1 * entranceStrongLogRate y, 0, y 3 * entranceWeakLogRate y]
  let J := y 2 * |d 1| + (y 1 * y 2 + θ * (y 2) ^ 2 * y 3) * |d 3|
  let Dk := fderiv ℝ (fun z => entranceLogWalls k (entranceReturnState (Ψ z))) z
  have hweights := entrance_transport_initial_weights hu.1.le hv.1.le ⟨hw.1.le, hw1⟩ hθ01.1 hk1 hU hW
  have hJ : J / k ≤ 21 * H := hweights.2
  have hresponse := HP y θ hk hm hu hv hw hθ Ψ HΨ d (by simp [d])
  change |fderiv ℝ Q z d - entranceRadialDrift y| ≤
      2 * (K * J / k) + 2 * (F * H / k ^ 2) * |entranceRadialDrift y| ∧
    |Dk d 0 - d 1 / y 1| + |Dk d 1 - k ^ 2 * (d 3 / y 3)| ≤
      T * (|d 1| + |d 3| + 2 * (-Real.log (y 2)) * (|entranceRadialDrift y| + K * J / k)) at hresponse
  have HR := entranceReturn_regular hk hm hu' hv hw'
  have ht : entranceReturnTime y ∈ Icc 0 (entranceReturnTime y) := ⟨HR.1.1.1.1.le, le_rfl⟩
  have hpos := entranceReturn_walls_pos hk hm ⟨hu.1, hu'.2⟩ hv ⟨hw.1, hw'.2⟩ _ ht
  have hreg : entranceRegion k (entranceReturnState y) := entranceReturn_region hk hm hu' hv hw' _ ht
  have hpQ : DifferentiableAt ℝ entranceStableRadius (entranceReturnState y) := by
    have hmR : 2 ≤ entranceReturnState y 0 := by linarith [(entranceRegion_phase hk hreg).1]
    have huR : |entranceReturnState y 1| < 1 / 200 := by
      rw [abs_of_nonneg hreg.2.2.1.1]; linarith [hreg.2.2.1.2]
    have hwR : |entranceReturnState y 3| < 1 / 200 := by
      rw [abs_of_nonneg hreg.2.2.2.2.1]; linarith [hreg.2.2.2.2.2]
    exact (contDiffAt_entranceStableRadius_two hmR huR hwR hpos.2.1).differentiableAt (by norm_num)
  have htransportQ : y 2 * fderiv ℝ Q z (Pi.single 2 1) = -fderiv ℝ Q z d :=
    HΨ.return_active_direction hk hm hu' hv hw' hpQ
  have htransportL : y 2 • Dk (Pi.single 2 1) = -Dk d :=
    HΨ.return_active_direction hk hm hu' hv hw'
      (hasFDerivAt_entranceLogWalls k hpos.1.ne' hpos.2.2.ne').differentiableAt
  have hphase : |fderiv ℝ Q z (Pi.single 2 1)| ≤ P * (y 1 + θ * y 2 * (y 3) ^ 2) := by
    have HE := entrance_active_phase_response hF.le hK.le ⟨hH.1, hH2⟩ hk1 hJ hG hresponse.1
    have HE' : |y 2 * fderiv ℝ Q z (Pi.single 2 1)| ≤ P * H := by
      rw [htransportQ, abs_neg]
      exact HE
    rw [abs_mul, abs_of_pos hv.1] at HE'
    apply (mul_le_mul_iff_left₀ hv.1).mp
    calc
      _ = y 2 * |fderiv ℝ Q z (Pi.single 2 1)| := by ring
      _ ≤ P * H := HE'
      _ = (P * (y 1 + θ * y 2 * (y 3) ^ 2)) * y 2 := by dsimp [H]; ring
  have hwalls := entrance_active_wall_response hT.le hA.le hK.le hH.1 hk0.le hu.1.le hw.1.le hlog
    hweights.1 hJ hG hresponse.2
  have hdU : d 1 / y 1 = entranceStrongLogRate y := by dsimp [d]; field_simp [hu.1.ne']
  have hdW : d 3 / y 3 = entranceWeakLogRate y := by dsimp [d]; field_simp [hw.1.ne']
  rw [hdU, hdW] at hwalls
  have hDk (i : Fin 2) : Dk d i = -(y 2 * Dk (Pi.single 2 1) i) := by
    have HE := congrFun htransportL i
    change y 2 * Dk (Pi.single 2 1) i = -Dk d i at HE
    linarith only [HE]
  have hscale : Dk (Pi.single 2 1) =
      ![fderiv ℝ L z (Pi.single 2 1) 0, k ^ 2 * fderiv ℝ L z (Pi.single 2 1) 1] := by
    apply entranceLogWalls_comp_fderiv_scale (HΨ.hasFDerivAt_return hk hm hu' hv hw').differentiableAt
    · rw [HΨ.apply_base]
      exact hpos.1.ne'
    · rw [HΨ.apply_base]
      exact hpos.2.2.ne'
  have heq : |Dk d 0 - entranceStrongLogRate y| + |Dk d 1 - k ^ 2 * entranceWeakLogRate y| =
      |y 2 * fderiv ℝ L z (Pi.single 2 1) 0 + entranceStrongLogRate y| +
        k ^ 2 * |y 2 * fderiv ℝ L z (Pi.single 2 1) 1 + entranceWeakLogRate y| := by
    rw [hDk 0, hDk 1, hscale]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show -(y 2 * fderiv ℝ L z (Pi.single 2 1) 0) - entranceStrongLogRate y =
      -(y 2 * fderiv ℝ L z (Pi.single 2 1) 0 + entranceStrongLogRate y) by ring,
      show -(y 2 * (k ^ 2 * fderiv ℝ L z (Pi.single 2 1) 1)) - k ^ 2 * entranceWeakLogRate y =
      -(k ^ 2 * (y 2 * fderiv ℝ L z (Pi.single 2 1) 1 + entranceWeakLogRate y)) by ring,
      abs_neg, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg k)]
  rw [heq] at hwalls
  have hlogs := entrance_active_log_columns hB.le hk1 hu1 hv.1 hw1 hLH hU hW hwalls
  refine ⟨hphase.trans (mul_le_mul_of_nonneg_right hCP (by positivity [hu.1, hv.1, hθ01.1])),
    hwalls.trans (mul_le_mul_of_nonneg_right hCB (by positivity [hu.1, hw.1, hH.1])),
    hlogs.1.trans ?_, hlogs.2.trans ?_⟩
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hClog hk0.le) hv.1.le
  · exact div_le_div_of_nonneg_right hClog hv.1.le

end BianchiIX
