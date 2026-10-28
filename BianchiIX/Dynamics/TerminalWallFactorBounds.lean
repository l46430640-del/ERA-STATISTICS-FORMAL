import BianchiIX.Dynamics.CoreTailMultiplierBounds
import BianchiIX.Dynamics.TerminalWallFactors

noncomputable section

namespace BianchiIX

/-- Formula (D.25), including the sharper inverse and logarithmic derivative powers, for the actual entrance. -/
theorem exists_terminalWallFactor_bounds_uniform {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 100)
    {J : ℕ} (hJ : 2 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 100 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let z := terminalEntranceInput h Y
      coreTailValid h Y ∧ z 2 = w * terminalWallFactor h Y 1 ∧ z 3 = u * terminalWallFactor h Y 0 ∧
        (η / 2 * α ^ (J - 2) ≤ z 1 ∧ z 1 ≤ 2 * η * α ^ (J - 2)) ∧
        ‖fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 1)) Y‖ ≤ C / α ∧
        ∀ i : Fin 2, 0 < terminalWallFactor h Y i ∧
          ContDiffAt ℝ 2 (fun Z => terminalWallFactor h Z i) Y ∧
          ContDiffAt ℝ 2 (fun Z => Real.log (terminalWallFactor h Z i)) Y ∧
          terminalWallFactor h Y i ≤ C / α ^ 2 ∧
          (terminalWallFactor h Y i)⁻¹ ≤ C * α ^ 2 ∧
          ‖fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z i)) Y‖ ≤ C / α := by
  have hJ1 : 1 ≤ J := by omega
  obtain ⟨A, hA, εm, hεm, HM⟩ := exists_coreTailMultiplier_bounds_uniform
    ⟨hη₀.1, by linarith only [hη₀.2]⟩ hJ1
  obtain ⟨B, hB, εd, hεd, HD⟩ := exists_terminalCyclicInput_derivative_uniform hη₀ hJ1
  obtain ⟨_, _, εg, hεg, HG⟩ := exists_terminal_axisCycle_endpoint_uniform hη₀ hJ
  let C := 4 * A + B
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have h4A : 4 * A ≤ C := by dsimp only [C]; linarith only [hB]
  have h2A : 2 * A ≤ C := by dsimp only [C]; linarith only [hA, hB]
  have hAB : A + B ≤ C := by dsimp only [C]; linarith only [hA]
  have hBC : B ≤ C := by dsimp only [C]; linarith only [hA]
  refine ⟨C, hB.trans hBC, min εm (min εd εg), lt_min hεm (lt_min hεd hεg), ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum Y h z
  have hα0 : 0 < α := hα.1
  have hη : 0 < η := hη₀.1.trans_le hηlo
  have hη1 : η < 1 := by linarith only [hηhi]
  have hsm : b ≤ εm * α ^ J := hsmall.trans
    ((mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hα.1.le (2 * J))).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hα.1.le hα.2 (by omega)) hεm.le))
  have hsd := hsmall.trans (mul_le_mul_of_nonneg_right
    ((min_le_right _ _).trans (min_le_left _ _)) (pow_nonneg hα.1.le (2 * J)))
  have hsg := hsmall.trans (mul_le_mul_of_nonneg_right
    ((min_le_right _ _).trans (min_le_right _ _)) (pow_nonneg hα.1.le (2 * J)))
  obtain ⟨HV, Hmult⟩ := HM η α b u w hηlo hη1 hα hb hsm hsum
  change coreTailValid h Y at HV
  have HlogH : ‖fderiv ℝ (fun Z => Real.log (projectiveCycleDenom (coreTailState h Z))) Y‖ ≤ B / α :=
    (HD η α b u w hηlo hηhi hα hb hsd hsum).2.2.2
  obtain ⟨_, _, HH, _, _, HU, _⟩ := HG η α b u w hηlo hηhi hα hb hsg hsum
  change 399 / 100 * α ^ 2 < projectiveCycleDenom (coreTailState h Y) ∧
    projectiveCycleDenom (coreTailState h Y) < 401 / 100 * α ^ 2 at HH
  have Hlow : α ^ 2 ≤ projectiveCycleDenom (coreTailState h Y) := by nlinarith only [HH.1, sq_nonneg α]
  have Hhigh : projectiveCycleDenom (coreTailState h Y) ≤ 8 * α ^ 2 := by nlinarith only [HH.2, sq_nonneg α]
  have hH : 0 < projectiveCycleDenom (coreTailState h Y) := (sq_pos_of_pos hα.1).trans_le Hlow
  have hR : 1 < Y 0 := by change 1 < 2 + 2 * α; linarith only [hα.1]
  have Hfac := terminalEntranceInput_wall_factors HV
  refine ⟨HV, Hfac.2.1, Hfac.2.2, HU, ?_, ?_⟩
  · rw [terminalEntranceInput_active_log_fderiv hR HV (mul_pos hη (pow_pos hα.1 J)) hH, norm_neg]
    exact HlogH.trans (div_le_div_of_nonneg_right hBC hα.1.le)
  · intro i
    have Hmi := Hmult i
    change ContDiffAt ℝ 2 (fun Z => coreTailMultiplier h Z i) Y ∧
      ContDiffAt ℝ 2 (fun Z => Real.log (coreTailMultiplier h Z i)) Y ∧
      1 / A ≤ coreTailMultiplier h Y i ∧ coreTailMultiplier h Y i ≤ A ∧
      ‖fderiv ℝ (fun Z => Real.log (coreTailMultiplier h Z i)) Y‖ ≤ A / α at Hmi
    have Hsmooth := contDiffAt_terminalWallFactor_two hR HV hH i
    have hM : 0 < coreTailMultiplier h Y i := coreTailMultiplier_pos h Y i
    refine ⟨terminalWallFactor_pos hH i, Hsmooth.1, Hsmooth.2, ?_, ?_, ?_⟩
    · change 4 * coreTailMultiplier h Y i / projectiveCycleDenom (coreTailState h Y) ≤ C / α ^ 2
      exact (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hα.1) Hlow).trans
        (div_le_div_of_nonneg_right
          ((mul_le_mul_of_nonneg_left Hmi.2.2.2.1 (by norm_num : (0 : ℝ) ≤ 4)).trans h4A) (sq_nonneg α))
    · rw [terminalWallFactor, inv_div]
      apply (div_le_iff₀ (mul_pos (by norm_num) hM)).mpr
      have HAM : 1 ≤ coreTailMultiplier h Y i * A := (div_le_iff₀ hA0).mp Hmi.2.2.1
      have Hprod := mul_le_mul_of_nonneg_right HAM (sq_nonneg α)
      have HC := mul_le_mul_of_nonneg_right h2A
        (mul_nonneg (sq_nonneg α) (mul_pos (by norm_num : (0 : ℝ) < 4) hM).le)
      nlinarith only [Hhigh, Hprod, HC]
    · rw [terminalWallFactor_log_fderiv hR HV hH i]
      exact (norm_sub_le _ _).trans ((add_le_add Hmi.2.2.2.2 HlogH).trans
        (by rw [← add_div]; exact div_le_div_of_nonneg_right hAB hα.1.le))

end BianchiIX
