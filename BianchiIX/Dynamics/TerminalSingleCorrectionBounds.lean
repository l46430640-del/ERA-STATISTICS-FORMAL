import BianchiIX.Dynamics.EntranceSingleReciprocalError
import BianchiIX.Dynamics.TerminalConnectionDifferential
import BianchiIX.Dynamics.TerminalWallFactorBounds

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def terminalSingleReciprocalError (h : ℝ) (Y : ExitTailState) : ℝ :=
  2 / terminalEntranceInput h Y 0 -
    singleStrongPhase (terminalCyclicInput h Y 0) (terminalCyclicInput h Y 1)

theorem terminalCyclicInput_radial_wall_bounds {h α D : ℝ} {Y : ExitTailState}
    (hR : 1 < Y 0) (HV : coreTailValid h Y) (hh : 0 < h)
    (hH : 0 < projectiveCycleDenom (coreTailState h Y))
    (hc : ContDiffAt ℝ 2 (terminalCyclicInput h) Y)
    (hi : ContDiffAt ℝ 2 (terminalEntranceInput h) Y)
    (hlog : ‖fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 1)) Y‖ ≤ D / α)
    (hlogB : ∀ i : Fin 2, ‖fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z i)) Y‖ ≤ D / α) :
    ∀ i : Fin 4, i ≠ 0 →
      |fderiv ℝ (terminalCyclicInput h) Y (Pi.single 0 1) i| ≤ D * |terminalCyclicInput h Y i| / α := by
  have HD := terminalEntranceInput_fderiv hR HV hh hH hi (Pi.single 0 1)
  have Hlog (L : ExitTailState →L[ℝ] ℝ) (H : ‖L‖ ≤ D / α) : |L (Pi.single 0 1)| ≤ D / α := by
    simpa only [Pi.norm_single, norm_one, mul_one, Real.norm_eq_abs] using
      (L.le_opNorm (Pi.single 0 1)).trans (mul_le_mul_of_nonneg_right H (norm_nonneg _))
  have Heq (i : Fin 4) (hi0 : i ≠ 0) :
      fderiv ℝ (terminalCyclicInput h) Y (Pi.single 0 1) i =
        fderiv ℝ (terminalEntranceInput h) Y (Pi.single 0 1) i := by
    have HE : (fun Z => terminalCyclicInput h Z i) = (fun Z => terminalEntranceInput h Z i) := by
      fin_cases i
      · exact False.elim (hi0 rfl)
      all_goals rfl
    have Hc := fderiv_apply (hc.differentiableAt (by norm_num)) i
    have Hi := fderiv_apply (hi.differentiableAt (by norm_num)) i
    rw [HE] at Hc
    exact congrArg (fun L : ExitTailState →L[ℝ] ℝ => L (Pi.single 0 1)) (Hc.symm.trans Hi)
  intro i hi0
  rw [Heq i hi0, HD]
  fin_cases i
  · exact False.elim (hi0 rfl)
  all_goals simp only [Pi.single_eq_of_ne (by decide : (1 : Fin 3) ≠ 0),
    Pi.single_eq_of_ne (by decide : (2 : Fin 3) ≠ 0), zero_mul, zero_add]
  · change |terminalEntranceInput h Y 1 *
      fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 1)) Y (Pi.single 0 1)| ≤
        D * |terminalEntranceInput h Y 1| / α
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (Hlog _ hlog) (abs_nonneg _)).trans_eq (by ring)
  · change |terminalEntranceInput h Y 2 *
      fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z 1)) Y (Pi.single 0 1)| ≤
        D * |terminalEntranceInput h Y 2| / α
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (Hlog _ (hlogB 1)) (abs_nonneg _)).trans_eq (by ring)
  · change |terminalEntranceInput h Y 3 *
      fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z 0)) Y (Pi.single 0 1)| ≤
        D * |terminalEntranceInput h Y 3| / α
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (Hlog _ (hlogB 0)) (abs_nonneg _)).trans_eq (by ring)

/-- The two stable corrections are estimated after composition with the actual finite tail. -/
theorem exists_terminal_single_correction_bounds {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 40000)
    {J : ℕ} (hJ : 2 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 40000 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let z := terminalCyclicInput h Y
      let E := |z 3| * (|z 1| + |z 3|) + (z 2) ^ 2
      let e := entranceSinglePhaseError ∘ terminalCyclicInput h
      let q := terminalSingleReciprocalError h
      coreTailValid h Y ∧ ContDiffAt ℝ 2 e Y ∧ ContDiffAt ℝ 2 q Y ∧
        |e Y| ≤ C * α * E ∧ |fderiv ℝ e Y (Pi.single 0 1)| ≤ C * E ∧
        |q Y| ≤ C * α ^ 3 * E ∧ |fderiv ℝ q Y (Pi.single 0 1)| ≤ C * α ^ 2 * E := by
  obtain ⟨A, hA, HA⟩ := exists_entranceSinglePhaseError_direction_bound
  obtain ⟨B, hB, HB⟩ := exists_entranceSinglePhaseError_scaled_bounds
  obtain ⟨Q, hQ, HQ⟩ := exists_entranceSingleReciprocalError_direction_bounds
  have hη1000 : 0 < η₀ ∧ η₀ ≤ 1 / 1000 := ⟨hη₀.1, hη₀.2.trans (by norm_num)⟩
  have hη100 : 0 < η₀ ∧ η₀ ≤ 1 / 100 := ⟨hη₀.1, hη₀.2.trans (by norm_num)⟩
  obtain ⟨D, hD, εd, hεd, HD⟩ := exists_terminalEntranceInput_derivative_uniform hη1000 hJ
  obtain ⟨M, hM, εm, hεm, HM⟩ := exists_terminalWallFactor_bounds_uniform hη100 hJ
  obtain ⟨K, hK, εg, hεg, HG⟩ := exists_terminal_axisCycle_endpoint_uniform hη100 hJ
  let L := D + M
  have hL : 1 ≤ L := by dsimp only [L]; linarith only [hD, hM]
  have hL0 : 0 ≤ L := (by norm_num : (0 : ℝ) ≤ 1).trans hL
  let C := (A + B + Q + 1) * (L + 1)
  have hcoeff : A ≤ A + B + Q + 1 ∧ B ≤ A + B + Q + 1 ∧ Q ≤ A + B + Q + 1 := by
    constructor <;> [skip; constructor] <;> linarith only [hA, hB, hQ]
  have hAC : A * L ≤ C := mul_le_mul hcoeff.1 (by linarith) hL0 (by positivity)
  have hBC : B ≤ C := by
    have H := mul_le_mul hcoeff.2.1 (by linarith only [hL0] : (1 : ℝ) ≤ L + 1) (by norm_num) (by positivity)
    simpa only [mul_one] using H
  have hQC : Q ≤ C := by
    have H := mul_le_mul hcoeff.2.2 (by linarith only [hL0] : (1 : ℝ) ≤ L + 1) (by norm_num) (by positivity)
    simpa only [mul_one] using H
  have hQLC : Q * L ≤ C := mul_le_mul hcoeff.2.2 (by linarith) hL0 (by positivity)
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
  let ε := min εd (min εm (min εg (1 / (20000 * K))))
  refine ⟨C, ?_, ε, lt_min hεd (lt_min hεm (lt_min hεg (by positivity))), ?_⟩
  · exact one_le_mul_of_one_le_of_one_le (by linarith only [hA, hB, hQ]) (by linarith only [hL0])
  intro η α b u w hηlo hηhi hα hb hsmall hsum Y h z E e q
  have hα0 := hα.1
  have hη0 := hη₀.1.trans_le hηlo
  have hs (a : ℝ) (ha : ε ≤ a) : b ≤ a * α ^ (2 * J) :=
    hsmall.trans (mul_le_mul_of_nonneg_right ha (pow_nonneg hα.1.le _))
  have hsd := hs εd (min_le_left _ _)
  have hsm := hs εm ((min_le_right _ _).trans (min_le_left _ _))
  have hsg := hs εg ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨HV, Hreg, Hinput, Hnorm, _, _⟩ := HD η α b u w hηlo (hηhi.trans (by norm_num)) hα hb hsd hsum
  obtain ⟨_, _, _, _, Hlog, HBfac⟩ := HM η α b u w hηlo (hηhi.trans (by norm_num)) hα hb hsm hsum
  obtain ⟨_, _, HH, Hm, _, Hu, Hw, _, _, _⟩ := HG η α b u w hηlo (hηhi.trans (by norm_num)) hα hb hsg hsum
  change 19 / (10 * α) < z 0 - 1 ∧ z 0 - 1 < 21 / (10 * α) at Hm
  change η / 2 * α ^ (J - 2) ≤ z 1 ∧ z 1 ≤ 2 * η * α ^ (J - 2) at Hu
  change |z 2| ≤ 2 * (K * b) / α ^ 2 ∧ |z 3| ≤ 2 * (K * b) / α ^ 2 at Hw
  have Hlow : 1 / α ≤ 19 / (10 * α) := by
    apply (div_le_div_iff₀ hα.1 (by positivity : 0 < 10 * α)).mpr
    linarith only [hα.1]
  have hscale : 1 / α ≤ z 0 + 1 := by linarith only [Hlow, Hm.1]
  have hone : 1 ≤ 1 / α := (le_div_iff₀ hα.1).mpr (by simpa using hα.2)
  have hm : 2 ≤ z 0 := by linarith only [hone, Hlow, Hm.1]
  have hu : |z 1| ≤ 1 / 10000 := by
    have hz1 : 0 ≤ z 1 := (by positivity : 0 ≤ η / 2 * α ^ (J - 2)).trans Hu.1
    rw [abs_of_nonneg hz1]
    have HP := mul_le_mul_of_nonneg_left (pow_le_one₀ hα.1.le hα.2 (n := J - 2)) (by positivity : 0 ≤ 2 * η)
    nlinarith only [Hu.2, HP, hηhi]
  have Hbudget : 2 * (K * b) ≤ α ^ 2 / 10000 := by
    have Hε : ε ≤ 1 / (20000 * K) := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have HE := (le_div_iff₀ (by positivity : 0 < 20000 * K)).mp Hε
    have HP := pow_le_pow_of_le_one hα.1.le hα.2 (by omega : 2 ≤ 2 * J)
    have H1 := mul_le_mul_of_nonneg_left hsmall hK0.le
    have H2 := mul_le_mul_of_nonneg_right HE (pow_nonneg hα.1.le (2 * J))
    nlinarith only [H1, H2, HP]
  have hw : |z 3| ≤ 1 / 10000 := Hw.2.trans ((div_le_iff₀ (sq_pos_of_pos hα.1)).mpr (by linarith only [Hbudget]))
  have hH : 0 < projectiveCycleDenom (coreTailState h Y) :=
    (by positivity : 0 < 399 / 100 * α ^ 2).trans HH.1
  have hR : 1 < Y 0 := by change 1 < 2 + 2 * α; linarith only [hα.1]
  have hDL : D ≤ L := by dsimp only [L]; linarith only [hM]
  have hML : M ≤ L := by dsimp only [L]; linarith only [hD]
  let d := fderiv ℝ (terminalCyclicInput h) Y (Pi.single 0 1)
  have hdnorm : ‖d‖ ≤ L / α ^ 2 := by
    have H := (fderiv ℝ (terminalCyclicInput h) Y).le_opNorm (Pi.single 0 1)
    simp only [Pi.norm_single, norm_one, mul_one] at H
    exact H.trans (Hnorm.trans (div_le_div_of_nonneg_right hDL (sq_nonneg α)))
  have hdwall : ∀ i : Fin 4, i ≠ 0 → |d i| ≤ L * |z i| / α :=
    terminalCyclicInput_radial_wall_bounds hR HV (mul_pos hη0 (pow_pos hα.1 J)) hH Hreg Hinput
      (Hlog.trans (div_le_div_of_nonneg_right hML hα.1.le))
      (fun i => (HBfac i).2.2.2.2.2.trans (div_le_div_of_nonneg_right hML hα.1.le))
  have He := HA α L z d hα.1 hL0 hscale hm hu hw hdnorm hdwall
  have He0 := HB α z hα.1 hscale hm hu hw
  obtain ⟨Hqreg, Hq0, HqD⟩ := HQ α L z d hα.1 hL0 hscale hm hu hw hdnorm hdwall
  have Hereg := (entranceSinglePhaseError_differential hm hu hw).1
  have Hnear : (entranceSingleReciprocalError ∘ terminalCyclicInput h) =ᶠ[𝓝 Y] q :=
    (entranceSingleReciprocalError_eventuallyEq_single hm (by linarith only [hu])).comp_tendsto
      Hreg.continuousAt.tendsto
  have Hqvalue : entranceSingleReciprocalError z = q Y := Hnear.self_of_nhds
  rw [Hqvalue] at Hq0
  have HEder : fderiv ℝ e Y (Pi.single 0 1) = fderiv ℝ entranceSinglePhaseError z d := by
    rw [fderiv_comp Y (Hereg.differentiableAt (by norm_num)) (Hreg.differentiableAt (by norm_num))]
    rfl
  have HQder : fderiv ℝ q Y (Pi.single 0 1) = fderiv ℝ entranceSingleReciprocalError z d := by
    have HH : fderiv ℝ (entranceSingleReciprocalError ∘ terminalCyclicInput h) Y = fderiv ℝ q Y := Hnear.fderiv_eq
    rw [← HH]
    rw [fderiv_comp Y (Hqreg.differentiableAt (by norm_num)) (Hreg.differentiableAt (by norm_num))]
    rfl
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  refine ⟨HV, Hereg.comp Y Hreg, (Hqreg.comp Y Hreg).congr_of_eventuallyEq Hnear.symm,
    He0.trans ?_, ?_, Hq0.trans ?_, ?_⟩
  · nlinarith only [mul_le_mul_of_nonneg_right hBC (by positivity : 0 ≤ α * E)]
  · rw [HEder]
    exact He.trans (mul_le_mul_of_nonneg_right hAC hE)
  · nlinarith only [mul_le_mul_of_nonneg_right hQC (by positivity : 0 ≤ α ^ 3 * E)]
  · rw [HQder]
    nlinarith only [HqD, mul_le_mul_of_nonneg_right hQLC (by positivity : 0 ≤ α ^ 2 * E)]

end BianchiIX
