import BianchiIX.Dynamics.TerminalSingleCorrectionBounds

noncomputable section

namespace BianchiIX

/-- The stable reciprocal correction has the precise old-wall numerator used in (D.31). -/
theorem exists_terminal_single_reciprocal_bounds {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 40000)
    {J : ℕ} (hJ : 2 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 40000 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalSingleReciprocalError h) Y ∧
        |terminalSingleReciprocalError h Y| ≤ C * (|u| * (h + b) + w ^ 2) / α ∧
        |fderiv ℝ (terminalSingleReciprocalError h) Y (Pi.single 0 1)| ≤
          C * (|u| * (h + b) + w ^ 2) / α ^ 2 := by
  obtain ⟨A, hA, εa, hεa, HA⟩ := exists_terminal_single_correction_bounds hη₀ hJ
  obtain ⟨M, hM, εm, hεm, HM⟩ := exists_terminalWallFactor_bounds_uniform
    ⟨hη₀.1, hη₀.2.trans (by norm_num)⟩ hJ
  have hA0 : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 1).trans hA
  have hM0 : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans hM
  have hC : 1 ≤ 2 * A * M ^ 2 := by nlinarith only [hA, hM, sq_nonneg (M - 1)]
  refine ⟨2 * A * M ^ 2, hC, min εa εm, lt_min hεa hεm, ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum Y h
  have hα0 := hα.1
  have hη0 := hη₀.1.trans_le hηlo
  have hsa := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left εa εm) (pow_nonneg hα.1.le _))
  have hsm := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_right εa εm) (pow_nonneg hα.1.le _))
  obtain ⟨HV, _, Hreg, _, _, H0, HD⟩ := HA η α b u w hηlo hηhi hα hb hsa hsum
  obtain ⟨_, Hvfac, Hwfac, Hu, _, HB⟩ := HM η α b u w hηlo (hηhi.trans (by norm_num)) hα hb hsm hsum
  let z := terminalCyclicInput h Y
  change z 2 = w * terminalWallFactor h Y 1 at Hvfac
  change z 3 = u * terminalWallFactor h Y 0 at Hwfac
  change η / 2 * α ^ (J - 2) ≤ z 1 ∧ z 1 ≤ 2 * η * α ^ (J - 2) at Hu
  have hz1 : 0 ≤ z 1 := (by positivity : 0 ≤ η / 2 * α ^ (J - 2)).trans Hu.1
  have Hu' : |z 1| ≤ 2 * h / α ^ 2 := by
    rw [abs_of_nonneg hz1]
    have HP : α ^ J = α ^ (J - 2) * α ^ 2 := by rw [← pow_add]; congr 1; omega
    refine Hu.2.trans_eq ?_
    dsimp only [h]
    rw [HP]
    field_simp
  have Hwall (i : Fin 2) (a : ℝ) : |a * terminalWallFactor h Y i| ≤ M * |a| / α ^ 2 := by
    rw [abs_mul, abs_of_pos (HB i).1]
    exact (mul_le_mul_of_nonneg_left (HB i).2.2.2.1 (abs_nonneg a)).trans_eq (by ring)
  have Hv : |z 2| ≤ M * |w| / α ^ 2 := by rw [Hvfac]; exact Hwall 1 w
  have Hw : |z 3| ≤ M * |u| / α ^ 2 := by rw [Hwfac]; exact Hwall 0 u
  have huB : |u| ≤ b := (le_add_of_nonneg_right (abs_nonneg w)).trans hsum
  let N := |u| * (h + b) + w ^ 2
  have HE : |z 3| * (|z 1| + |z 3|) + (z 2) ^ 2 ≤ 2 * M ^ 2 * N / α ^ 4 := by
    have HV2 : (z 2) ^ 2 ≤ (M * |w| / α ^ 2) ^ 2 := by
      have H := pow_le_pow_left₀ (abs_nonneg (z 2)) Hv 2
      simpa only [sq_abs] using H
    calc
      _ ≤ (M * |u| / α ^ 2) * (2 * h / α ^ 2 + M * |u| / α ^ 2) +
          (M * |w| / α ^ 2) ^ 2 := add_le_add
            (mul_le_mul Hw (add_le_add Hu' Hw) (by positivity) (by positivity)) HV2
      _ = (2 * M * |u| * h + M ^ 2 * |u| ^ 2 + M ^ 2 * w ^ 2) / α ^ 4 := by
        rw [div_pow, sq_abs]
        field_simp
        ring_nf
        simp only [sq_abs]
        ring
      _ ≤ _ := by
        apply (div_le_div_iff_of_pos_right (pow_pos hα.1 4)).mpr
        have Huh := mul_le_mul_of_nonneg_right hM (by positivity : 0 ≤ 2 * M * |u| * h)
        have Hub := mul_le_mul_of_nonneg_left huB (by positivity : 0 ≤ M ^ 2 * |u|)
        dsimp only [N]
        nlinarith only [Huh, Hub, (by positivity : 0 ≤ M ^ 2 * |u| * b), (by positivity : 0 ≤ M ^ 2 * w ^ 2)]
  refine ⟨HV, Hreg, ?_, ?_⟩
  · calc
      _ ≤ A * α ^ 3 * (|z 3| * (|z 1| + |z 3|) + (z 2) ^ 2) := H0
      _ ≤ A * α ^ 3 * (2 * M ^ 2 * N / α ^ 4) := mul_le_mul_of_nonneg_left HE (by positivity)
      _ = _ := by field_simp; ring
  · calc
      _ ≤ A * α ^ 2 * (|z 3| * (|z 1| + |z 3|) + (z 2) ^ 2) := HD
      _ ≤ A * α ^ 2 * (2 * M ^ 2 * N / α ^ 4) := mul_le_mul_of_nonneg_left HE (by positivity)
      _ = _ := by field_simp; ring

/-- The original raw budget makes the stable reciprocal correction and its radial column O(b). -/
theorem exists_terminal_single_reciprocal_linear_bound {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 40000)
    {J : ℕ} (hJ : 2 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 40000 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalSingleReciprocalError h) Y ∧
        |terminalSingleReciprocalError h Y| +
          |fderiv ℝ (terminalSingleReciprocalError h) Y (Pi.single 0 1)| ≤ C * b := by
  obtain ⟨A, hA, ε₀, hε₀, HA⟩ := exists_terminal_single_reciprocal_bounds hη₀ hJ
  have hA0 : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 1).trans hA
  refine ⟨6 * A, by linarith only [hA], min ε₀ 1, lt_min hε₀ (by norm_num), ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum Y h
  have hα0 := hα.1
  have hsa := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left ε₀ 1) (pow_nonneg hα.1.le _))
  obtain ⟨HV, Hreg, H0, HD⟩ := HA η α b u w hηlo hηhi hα hb hsa hsum
  have hbb : b ≤ α ^ 2 := hsmall.trans ((mul_le_of_le_one_left (pow_nonneg hα.1.le _) (min_le_right ε₀ 1)).trans
    (pow_le_pow_of_le_one hα.1.le hα.2 (by omega : 2 ≤ 2 * J)))
  have hh : h ≤ α ^ 2 :=
    (mul_le_of_le_one_left (pow_nonneg hα.1.le J) (hηhi.trans (by norm_num))).trans
      (pow_le_pow_of_le_one hα.1.le hα.2 hJ)
  have hu : |u| ≤ b := (le_add_of_nonneg_right (abs_nonneg w)).trans hsum
  have hw : |w| ≤ b := (le_add_of_nonneg_left (abs_nonneg u)).trans hsum
  have hη0 := hη₀.1.trans_le hηlo
  have hN : |u| * (h + b) + w ^ 2 ≤ 3 * b * α ^ 2 := by
    have Hu := mul_le_mul hu (add_le_add hh hbb) (by dsimp only [h]; positivity) hb.le
    have Hw := mul_le_mul hw (hw.trans hbb) (abs_nonneg w) hb.le
    nlinarith only [Hu, Hw, sq_abs w]
  have HDb : A * (|u| * (h + b) + w ^ 2) / α ^ 2 ≤ 3 * A * b :=
    (div_le_iff₀ (sq_pos_of_pos hα.1)).mpr (by nlinarith only [mul_le_mul_of_nonneg_left hN hA0])
  have H0b : A * (|u| * (h + b) + w ^ 2) / α ≤ 3 * A * b := by
    have H : A * (|u| * (h + b) + w ^ 2) / α ≤ 3 * A * b * α :=
      (div_le_iff₀ hα.1).mpr (by nlinarith only [mul_le_mul_of_nonneg_left hN hA0])
    exact H.trans (mul_le_of_le_one_right (by positivity) hα.2)
  exact ⟨HV, Hreg, by linarith only [H0.trans H0b, HD.trans HDb]⟩

end BianchiIX
