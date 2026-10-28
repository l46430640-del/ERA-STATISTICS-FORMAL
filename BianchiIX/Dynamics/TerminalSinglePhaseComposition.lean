import BianchiIX.Dynamics.TerminalSinglePhaseGerm
import BianchiIX.Dynamics.ExitTailHeightRadialBounds
import BianchiIX.Dynamics.SinglePhaseCompositionBounds

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

/-- The actual finite-tail single-wall phase has O(b) value and radial errors, and bounded ordinary wall columns. -/
theorem exists_terminal_single_phase_composed_bounds {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 100)
    {J : ℕ} (hJ : 2 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 100 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalSinglePhase h) Y ∧
        (|terminalSinglePhase h Y - α| + |fderiv ℝ (terminalSinglePhase h) Y (Pi.single 0 1) - 1 / 2| ≤ C * b) ∧
        ‖fderiv ℝ (terminalSinglePhase h) Y‖ ≤ C := by
  have hJ1 : 1 ≤ J := by omega
  obtain ⟨A, hA, εt, hεt, HT⟩ := exists_terminal_exitReturn_radial_bounds_uniform
    ⟨hη₀.1, hη₀.2.trans_lt (by norm_num)⟩ hJ1
  obtain ⟨B, hB, εg, hεg, HG⟩ := exists_terminal_tail_geometry_uniform hη₀ hJ1
  have hA0 : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 1).trans hA
  have hB0 : 0 ≤ B := (by norm_num : (0 : ℝ) ≤ 1).trans hB
  let L := 1 + Real.log (1 / η₀) + J * Real.exp (-1)
  have hL : 0 ≤ L := by
    have Hlog : 0 ≤ Real.log (1 / η₀) := Real.log_nonneg ((le_div_iff₀ hη₀.1).mpr (by linarith only [hη₀.2]))
    dsimp only [L]; positivity
  let P := 1024 * B * (1 + B)
  let W := 1024 * (1 + B)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  let V := P + B
  let R := A * (P + W + 1 + L ^ 2)
  let N := 3 * A * (P + W + 1)
  let C := V + R + N + 1
  have hV : 0 ≤ V := add_nonneg hP hB0
  have hRad : 0 ≤ R := by dsimp only [R]; positivity
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  refine ⟨C, by dsimp only [C]; linarith only [hV, hRad, hN],
    min εt (min εg 1), lt_min hεt (lt_min hεg (by norm_num)), ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum Y h
  have hα0 := hα.1
  have hη : 0 < η := hη₀.1.trans_le hηlo
  have hst : b ≤ εt * α ^ J := hsmall.trans
    ((mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hα.1.le _)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hα.1.le hα.2 (by omega)) hεt.le))
  have hsg := hsmall.trans (mul_le_mul_of_nonneg_right
    ((min_le_right _ _).trans (min_le_left _ _)) (pow_nonneg hα.1.le (2 * J)))
  have hε1 : min εt (min εg 1) ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hbα : b ≤ α ^ 2 := hsmall.trans ((mul_le_of_le_one_left (pow_nonneg hα.1.le _) hε1).trans
    (pow_le_pow_of_le_one hα.1.le hα.2 (by omega : 2 ≤ 2 * J)))
  have hb1 : b ≤ 1 := hbα.trans (pow_le_one₀ hα.1.le hα.2)
  have hhα : h ≤ α ^ 2 := (mul_le_of_le_one_left (pow_nonneg hα.1.le J) (hηhi.trans (by norm_num))).trans
    (pow_le_pow_of_le_one hα.1.le hα.2 hJ)
  obtain ⟨HV, Hreg, Hnorm, Hrad, Hwall⟩ := HT η α b u w hηlo (hηhi.trans_lt (by norm_num)) hα hb hst hsum
  obtain ⟨_, hm, Hr, Hβ, HBsmall, Hv, _⟩ := HG η α b u w hηlo hηhi hα hb hsg hsum
  let F := fun Z => toExitTailState (coreTailState h Z)
  let z := F Y
  let β := |z 1| + |z 2|
  let f := fun Q : ExitTailState => exitSinglePhase (Q 0) (Q 1) h (Q 2)
  change ContDiffAt ℝ 2 F Y at Hreg
  change ‖fderiv ℝ F Y‖ ≤ A at Hnorm
  change |z 0 - (2 + 2 * α)| ≤ B * b at Hr
  change β ≤ B * b at Hβ
  have hβ : 0 ≤ β := by dsimp only [β]; positivity
  have Hactive : coreTailState h Y 2 = h := coreTailState_active HV
  rw [Hactive] at Hv
  have hβsmall : β ≤ α / 10000 := Hβ.trans HBsmall
  have hrsmall := Hr.trans HBsmall
  have Hfg := exitSinglePhase_derivative_bounds hα hβsmall hrsmall (le_refl β) Hv
  change ContDiffAt ℝ 2 f z ∧ _ at Hfg
  obtain ⟨_, _, _, _, Hsq, HH, _, _, HHpos, HNpos⟩ :=
    exitSingle_terminal_geometry hα hβsmall hrsmall (le_refl β) Hv
  have Hnear := terminalSinglePhase_eventuallyEq_radical
    (by change 1 < 2 + 2 * α; linarith only [hα.1]) HV hm Hreg.continuousAt Hsq
    ((sq_pos_of_pos hα.1).trans_le HH) HHpos HNpos
  change terminalSinglePhase h =ᶠ[𝓝 Y] f ∘ F at Hnear
  have Hsmooth : ContDiffAt ℝ 2 (terminalSinglePhase h) Y := (Hfg.1.comp Y Hreg).congr_of_eventuallyEq Hnear
  have Hder : fderiv ℝ (terminalSinglePhase h) Y = (fderiv ℝ f z).comp (fderiv ℝ F Y) :=
    Hnear.fderiv_eq.trans (fderiv_comp Y (Hfg.1.differentiableAt (by norm_num)) (Hreg.differentiableAt (by norm_num)))
  have Hsum : h + β ≤ (1 + B) * α ^ 2 := by
    nlinarith only [hhα, Hβ.trans (mul_le_mul_of_nonneg_left hbα hB0)]
  have Hf0 : |fderiv ℝ f z (Pi.single 0 1) - 1 / 2| ≤ P * b := Hfg.2.1.trans (by
    apply (div_le_iff₀ (sq_pos_of_pos hα.1)).mpr
    have H := mul_le_mul Hβ Hsum (by positivity : 0 ≤ h + β) (mul_nonneg hB0 hb.le)
    dsimp only [P]
    nlinarith only [H])
  have Hfw : |fderiv ℝ f z (Pi.single 1 1)| + |fderiv ℝ f z (Pi.single 2 1)| ≤ W * α := Hfg.2.2.trans (by
    apply (div_le_iff₀ hα.1).mpr
    dsimp only [W]
    nlinarith only [Hsum])
  have Hvalue : |terminalSinglePhase h Y - α| ≤ V * b := by
    have HE := exitSinglePhase_value_bound hα hβsmall hrsmall (le_refl β) Hv
    have Heq : terminalSinglePhase h Y = f z := Hnear.self_of_nhds
    rw [Heq]
    have HE' : |f z - (z 0 - 2) / 2| ≤ P * b := HE.trans (by
      apply (div_le_iff₀ hα.1).mpr
      have H := mul_le_mul Hβ Hsum (by positivity : 0 ≤ h + β) (mul_nonneg hB0 hb.le)
      have Hα := mul_le_mul_of_nonneg_left hα.2 (by positivity : 0 ≤ B * (1 + B) * b * α)
      dsimp only [P]
      nlinarith only [H, Hα, (by positivity : 0 ≤ B * (1 + B) * b * α)])
    have Hcenter : |(z 0 - 2) / 2 - α| ≤ B * b / 2 := by
      have HEQ : (z 0 - 2) / 2 - α = (z 0 - (2 + 2 * α)) / 2 := by ring
      rw [HEQ, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact div_le_div_of_nonneg_right Hr (by norm_num)
    have H := abs_sub_le (f z) ((z 0 - 2) / 2) α
    dsimp only [V]
    nlinarith only [H, HE', Hcenter, mul_nonneg hB0 hb.le]
  have Hradial : |fderiv ℝ (terminalSinglePhase h) Y (Pi.single 0 1) - 1 / 2| ≤ R * b := by
    let d := fderiv ℝ F Y (Pi.single 0 1)
    have Hd : ‖d‖ ≤ A := by
      simpa only [Pi.norm_single, norm_one, mul_one] using
        ((fderiv ℝ F Y).le_opNorm (Pi.single 0 1)).trans (mul_le_mul_of_nonneg_right Hnorm (norm_nonneg _))
    have Hd0 : |d 0| ≤ A := (norm_le_pi_norm d 0).trans Hd
    have Hdw : |d 1| + |d 2| ≤ A * b / α := by
      have H1 := (Hwall 0).2
      have H2 := (Hwall 1).2
      change |d 1| ≤ A * |u| / α at H1
      change |d 2| ≤ A * |w| / α at H2
      have Hsum := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hA0) hα.1.le
      rw [mul_add, add_div] at Hsum
      linarith only [H1, H2, Hsum]
    let S := exitTailLength η α J
    have hS : 0 ≤ S := exitTailLength_nonneg ⟨hη, hηhi.trans (by norm_num)⟩ hα J
    have HS : α * (1 + S) ≤ L := by
      have Hlog := Real.log_le_log (one_div_pos.mpr hη) (one_div_le_one_div_of_le hη₀.1 hηlo)
      have H := (exitTailLength_weighted_bounds ⟨hη, hηhi.trans (by norm_num)⟩ hα J).1
      dsimp only [L]
      nlinarith only [H, Hlog, hα.2]
    have HbT : b ^ 2 * (1 + S) ^ 2 ≤ L ^ 2 * b := by
      have H1 := mul_le_mul_of_nonneg_right hbα (by positivity : 0 ≤ b * (1 + S) ^ 2)
      have H2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity : 0 ≤ α * (1 + S)) HS 2) hb.le
      nlinarith only [H1, H2]
    have HdR : |d 0 - 1| ≤ A * (1 + L ^ 2) * b := Hrad.trans (by
      have Hu : |u| ≤ b := (le_add_of_nonneg_right (abs_nonneg w)).trans hsum
      nlinarith only [mul_le_mul_of_nonneg_left (add_le_add Hu HbT) hA0])
    rw [Hder, ContinuousLinearMap.comp_apply]
    have H := clm_three_radial_composition_bound (fderiv ℝ f z) d
    refine H.trans ?_
    have H1 := mul_le_mul Hf0 Hd0 (abs_nonneg _) (mul_nonneg hP hb.le)
    have H2 := mul_le_mul Hfw Hdw (add_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg hW hα.1.le)
    have Heq : (W * α) * (A * b / α) = W * A * b := by field_simp
    rw [Heq] at H2
    dsimp only [R]
    nlinarith only [H1, H2, HdR, (by positivity : 0 ≤ A * b * (1 + L ^ 2))]
  have Hnormf : ‖fderiv ℝ f z‖ ≤ 3 * (P + W + 1) := by
    apply clm_norm_le_card_mul_basis_bound _ (by positivity)
    intro i
    rw [Real.norm_eq_abs]
    fin_cases i
    · change |fderiv ℝ f z (Pi.single 0 1)| ≤ P + W + 1
      have H := abs_sub_le (fderiv ℝ f z (Pi.single 0 1)) (1 / 2) 0
      norm_num only [sub_zero, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at H
      nlinarith only [H, Hf0, mul_le_of_le_one_right hP hb1, hW]
    · change |fderiv ℝ f z (Pi.single 1 1)| ≤ P + W + 1
      nlinarith only [Hfw, mul_le_of_le_one_right hW hα.2, hP, abs_nonneg (fderiv ℝ f z (Pi.single 2 1))]
    · change |fderiv ℝ f z (Pi.single 2 1)| ≤ P + W + 1
      nlinarith only [Hfw, mul_le_of_le_one_right hW hα.2, hP, abs_nonneg (fderiv ℝ f z (Pi.single 1 1))]
  refine ⟨HV, Hsmooth, ?_, ?_⟩
  · have HC : V + R ≤ C := by dsimp only [C]; linarith only [hN]
    nlinarith only [Hvalue, Hradial, mul_le_mul_of_nonneg_right HC hb.le]
  · rw [Hder]
    have H := (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul Hnormf Hnorm (norm_nonneg _) (by positivity))
    have HC : N ≤ C := by dsimp only [C]; linarith only [hV, hRad]
    exact H.trans ((show 3 * (P + W + 1) * A = N by dsimp only [N]; ring).le.trans HC)

end BianchiIX
