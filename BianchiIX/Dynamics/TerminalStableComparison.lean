import BianchiIX.Algebra.ExitCycleComparison
import BianchiIX.Algebra.PhaseBoundaryStability
import BianchiIX.Dynamics.StableProjectionLipschitz
import BianchiIX.Dynamics.TerminalReferencePhase
import BianchiIX.Dynamics.ExitActualCycle

noncomputable section

namespace BianchiIX

/-- Compare at the same auxiliary height; no derivative of the tail map is needed. -/
theorem exists_exitCycle_stable_radius_comparison :
    ∃ C ≥ (1 : ℝ), ∀ α B R u v w : ℝ,
      (0 < α ∧ α ≤ 1) → B ≤ α ^ 2 / 10000 → |R - (2 + 2 * α)| ≤ B →
      |u| + |w| ≤ B → (0 ≤ v ∧ v ≤ α ^ 2 / 1000) →
      let t := exitTailGap R v
      let H := axisCycleDenom (1 - t) u v w
      |coreRadius (stableBoundaryProjection (1 - 4 * (2 - t) / H) (4 * v / H) (4 * u / H))
          (4 * w / H) - 2 / α| ≤ C * B / α ^ 2 := by
  obtain ⟨L, hL, HL⟩ := exists_stableBoundaryProjection_lipschitz
  refine ⟨42 * L, by linarith only [hL], ?_⟩
  intro α B R u v w hα hB hR hw hv t H
  have hα0 : 0 < α := hα.1
  have hB0 : 0 ≤ B := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hw
  have hBs : B ≤ α / 10000 := by nlinarith only [hB, mul_nonneg hα.1.le (sub_nonneg.mpr hα.2)]
  have hvs : v ≤ α / 100 := by nlinarith only [hv.2, mul_nonneg hα.1.le (sub_nonneg.mpr hα.2)]
  let t₀ := exitTailGap (2 + 2 * α) v
  let H₀ := axisCycleDenom (1 - t₀) 0 v 0
  let X : StableState := ![1 - 4 * (2 - t₀) / H₀, 4 * v / H₀, 0]
  let Y : StableState := ![1 - 4 * (2 - t) / H, 4 * v / H, 4 * u / H]
  have HH := exitCycleDenom_terminal_bounds hα hBs hR hw ⟨hv.1, hvs⟩
  have HH₀ := exitCycleDenom_terminal_bounds hα (B := 0) (R := 2 + 2 * α) (by positivity)
    (by simp) (by norm_num : |(0 : ℝ)| + |(0 : ℝ)| ≤ 0) ⟨hv.1, hvs⟩
  have hH : 0 < H := lt_of_lt_of_le (by positivity) HH.1.le
  have hH₀ : 0 < H₀ := lt_of_lt_of_le (by positivity) HH₀.1.le
  have hlow : (19 / 10 : ℝ) ≤ 19 / (10 * α) := by
    apply (le_div_iff₀ (by positivity : 0 < 10 * α)).mpr
    linarith only [hα.2]
  have hm : 2 ≤ Y 0 := by
    have HP := (exitCycle_terminal_phase_bounds hα hBs hR hw ⟨hv.1, hvs⟩).1
    have HE : Y 0 - 1 = 4 * (t - 2) / H := by dsimp only [Y]; simp only [Matrix.cons_val_zero]; ring
    change 19 / (10 * α) < 4 * (t - 2) / H at HP
    linarith only [HE, HP, hlow]
  have hm₀ : 2 ≤ X 0 := by
    have HP := (exitCycle_terminal_phase_bounds hα (B := 0) (R := 2 + 2 * α) (by positivity)
      (by simp) (by norm_num : |(0 : ℝ)| + |(0 : ℝ)| ≤ 0) ⟨hv.1, hvs⟩).1
    have HE : X 0 - 1 = 4 * (t₀ - 2) / H₀ := by dsimp only [X]; simp only [Matrix.cons_val_zero]; ring
    change 19 / (10 * α) < 4 * (t₀ - 2) / H₀ at HP
    linarith only [HE, HP, hlow]
  have hvsmall : 2 * v / α ^ 2 ≤ 1 / 400 := by
    apply (div_le_iff₀ (sq_pos_of_pos hα.1)).mpr
    linarith only [hv.2, sq_nonneg α]
  have hu : |Y 1| ≤ 1 / 400 := by
    change |4 * v / H| ≤ _
    rw [abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) hv.1) hH.le)]
    exact (exitCycle_positive_wall_scale hα.1 hv.1 HH).2.trans hvsmall
  have hu₀ : |X 1| ≤ 1 / 400 := by
    change |4 * v / H₀| ≤ _
    rw [abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) hv.1) hH₀.le)]
    exact (exitCycle_positive_wall_scale hα.1 hv.1 HH₀).2.trans hvsmall
  have hweak : |4 * u / H| ≤ 2 * B / α ^ 2 := exitCycle_newWall_bound hα.1 hB0
    (by nlinarith only [HH.1, sq_pos_of_pos hα.1])
    (by linarith only [hw, abs_nonneg w])
  have hwsmall : |Y 2| ≤ 1 / 400 := by
    apply hweak.trans
    apply (div_le_iff₀ (sq_pos_of_pos hα.1)).mpr
    linarith only [hB, sq_nonneg α]
  have Hcoord := exitCycle_reference_coordinate_difference hα hBs hR hw ⟨hv.1, hvs⟩
  have hnorm : ‖Y - X‖ ≤ 40 * B / α ^ 2 := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    fin_cases i
    · exact Hcoord.1
    · exact Hcoord.2
    · change |4 * u / H - 0| ≤ _
      rw [sub_zero]
      exact hweak.trans (by
        have HB : 0 ≤ B / α ^ 2 := by positivity
        simp only [mul_div_assoc]
        linarith only [HB])
  have HP := (HL X Y hm₀ hu₀ (by change |(0 : ℝ)| ≤ 1 / 400; norm_num) hm hu hwsmall).trans
    (mul_le_mul_of_nonneg_left hnorm (by linarith only [hL]))
  have Href := exitCycle_boundary_stable_projection hα ⟨hv.1, by linarith only [hv.2, sq_nonneg α]⟩
  change stableBoundaryProjection (X 0) (X 1) (X 2) = 1 + 2 / α at Href
  rw [Href] at HP
  have Hv := exitCycle_newWall_bound (H := H) hα.1 hB0
    (by nlinarith only [HH.1, sq_pos_of_pos hα.1])
    (show |w| ≤ B by linarith only [hw, abs_nonneg u])
  have HR := phaseNorm_boundary_error (a := stableBoundaryProjection (Y 0) (Y 1) (Y 2) - 1)
    (b := 4 * w / H) (show 0 ≤ 2 / α by positivity)
  have HE : stableBoundaryProjection (Y 0) (Y 1) (Y 2) - 1 - 2 / α =
      stableBoundaryProjection (Y 0) (Y 1) (Y 2) - (1 + 2 / α) := by ring
  rw [HE] at HR
  change |coreRadius (stableBoundaryProjection (Y 0) (Y 1) (Y 2)) (4 * w / H) - 2 / α| ≤ _ at HR ⊢
  have HB : 0 ≤ B / α ^ 2 := by positivity
  simp only [mul_div_assoc] at HR HP Hv ⊢
  nlinarith only [HR, HP, Hv, mul_le_mul_of_nonneg_right hL HB]

/-- The corrected phase of the actual tail differs from the exact reference by O(b / α²). -/
theorem exists_terminal_stable_radius_comparison {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 1000)
    {J : ℕ} (hJ : 2 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧
        |entranceStableRadius (projectiveCycle (coreTailState h Y)) - 2 / α| ≤ C * b / α ^ 2 := by
  obtain ⟨A, hA, ε, hε, HE⟩ := exists_terminal_axisCycle_regular ⟨hη.1, by linarith only [hη.2]⟩
    (show 1 ≤ J by omega)
  obtain ⟨L, hL, HL⟩ := exists_exitCycle_stable_radius_comparison
  refine ⟨L * A, one_le_mul_of_one_le_of_one_le hL hA, ε, hε, ?_⟩
  intro α b u w hα hb hsmall hw Y h
  have H := HE α b u w hα hb hsmall hw
  have HV : coreTailValid h Y := H.1
  have Ht := H.2.2.1 (coreTailTime h Y) ⟨HV.1.1.1.le, le_rfl⟩
  let y := coreTailState h Y
  have hm : y 0 < 1 := Ht.1
  have hR : |coreRadius (y 0) (y 2) - (2 + 2 * α)| ≤ A * b := Ht.2.1
  have hW : |y 1| + |y 3| ≤ A * b := Ht.2.2.1
  have hB : A * b ≤ α ^ 2 / 10000 := H.2.1.trans
    (div_le_div_of_nonneg_right (pow_le_pow_of_le_one hα.1.le hα.2 (by omega)) (by norm_num))
  have hv : 0 ≤ y 2 ∧ y 2 ≤ α ^ 2 / 1000 := by
    change 0 ≤ coreTailState h Y 2 ∧ coreTailState h Y 2 ≤ _
    rw [coreTailState_active HV]
    refine ⟨mul_nonneg hη.1.le (pow_nonneg hα.1.le J), ?_⟩
    have hp := pow_le_pow_of_le_one hα.1.le hα.2 hJ
    change η * α ^ J ≤ _
    nlinarith only [mul_le_mul_of_nonneg_left hp hη.1.le,
      mul_le_mul_of_nonneg_right hη.2 (sq_nonneg α)]
  have HP := HL α (A * b) (coreRadius (y 0) (y 2)) (y 1) (y 2) (y 3) hα hB hR hW hv
  have hgap : exitTailGap (coreRadius (y 0) (y 2)) (y 2) = 1 - y 0 := exitTailGap_of_coreRadius hm
  dsimp only at HP
  rw [hgap, show 1 - (1 - y 0) = y 0 by ring, show 2 - (1 - y 0) = y 0 + 1 by ring] at HP
  refine ⟨HV, ?_⟩
  change |entranceStableRadius (projectiveCycle y) - 2 / α| ≤ L * (A * b) / α ^ 2 at HP
  simpa only [mul_assoc] using HP

end BianchiIX
