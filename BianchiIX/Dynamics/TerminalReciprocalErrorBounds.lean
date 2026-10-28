import BianchiIX.Dynamics.TerminalReciprocalError
import BianchiIX.Dynamics.TerminalReciprocalGeometry
import BianchiIX.Dynamics.TerminalConnectionErrorBounds

noncomputable section

namespace BianchiIX

/-- The actual reciprocal phase error has the amplitude-sensitive estimates in (D.30). -/
theorem exists_terminal_reciprocal_error_bounds :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 1000 ∧ ∀ η₀ : ℝ, (0 < η₀ ∧ η₀ ≤ δ) →
      ∀ J : ℕ, 2 ≤ J → ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ δ → (0 < α ∧ α ≤ 1) → 0 < b →
      b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let z := terminalEntranceInput h Y
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalReciprocalError h) Y ∧
        1 / α ≤ terminalConnectionPhase h Y ∧ 1 / α ≤ z 0 ∧
        |terminalReciprocalError h Y| ≤ C * α ^ 3 * z 1 * z 2 ∧
        (|fderiv ℝ (terminalReciprocalError h) Y (Pi.single 0 1)| +
          |fderiv ℝ (terminalReciprocalError h) Y (Pi.single 1 1)| ≤ C * z 1 * z 2) ∧
        |fderiv ℝ (terminalReciprocalError h) Y (Pi.single 2 1)| ≤ C * z 1 := by
  obtain ⟨δ, hδ, hδhi, HE⟩ := exists_terminal_connection_error_bounds
  refine ⟨δ, hδ, hδhi, ?_⟩
  intro η₀ hη₀ J hJ
  have hη₀small : 0 < η₀ ∧ η₀ ≤ 1 / 1000 := ⟨hη₀.1, hη₀.2.trans hδhi⟩
  have hη₀100 : 0 < η₀ ∧ η₀ ≤ 1 / 100 := ⟨hη₀.1, hη₀small.2.trans (by norm_num)⟩
  obtain ⟨A, hA, εe, hεe, HA⟩ := HE η₀ hη₀ J hJ
  obtain ⟨D, hD, εd, hεd, HD⟩ := exists_terminalEntranceInput_derivative_uniform hη₀small hJ
  obtain ⟨M, hM, εm, hεm, HM⟩ := exists_terminalWallFactor_bounds_uniform hη₀100 hJ
  obtain ⟨εr, hεr, HR⟩ := exists_terminal_entrance_radius_lower hη₀small hJ
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hD0 : 0 ≤ D := le_trans (by norm_num) hD
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM
  let ε := min εe (min εd (min εm (min εr (1 / (2 * A * M)))))
  refine ⟨10 * A * (D + 1), by nlinarith only [hA, hD, mul_nonneg hA0.le hD0], ε,
    lt_min hεe (lt_min hεd (lt_min hεm (lt_min hεr (by positivity)))), ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum hu hw Y h z
  have hα0 := hα.1
  have hη1000 : η ≤ 1 / 1000 := hηhi.trans hδhi
  have hη100 : η ≤ 1 / 100 := hη1000.trans (by norm_num)
  have hη0 : 0 < η := hη₀.1.trans_le hηlo
  have Hεe : ε ≤ εe := min_le_left _ _
  have Hεd : ε ≤ εd := (min_le_right _ _).trans (min_le_left _ _)
  have Hεm : ε ≤ εm := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have Hεr : ε ≤ εr := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have Hεsmall : ε ≤ 1 / (2 * A * M) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have Hsmall (c : ℝ) (hc : ε ≤ c) : b ≤ c * α ^ (2 * J) :=
    hsmall.trans (mul_le_mul_of_nonneg_right hc (pow_nonneg hα.1.le (2 * J)))
  obtain ⟨HV, HΘreg, HΘ, HΘ01, HΘ2, _⟩ := HA η α b u w hηlo hηhi hα hb (Hsmall εe Hεe) hsum hu hw
  obtain ⟨_, _, Hzreg, _, Hzder, _⟩ := HD η α b u w hηlo hη1000 hα hb (Hsmall εd Hεd) hsum
  obtain ⟨_, Hfactor, _, HU, _, HB⟩ := HM η α b u w hηlo hη100 hα hb (Hsmall εm Hεm) hsum
  have Hradius := (HR η α b u w hηlo hη1000 hα hb (Hsmall εr Hεr) hsum).2
  change 3 / (2 * α) ≤ z 0 at Hradius
  change z 2 = w * terminalWallFactor h Y 1 at Hfactor
  change η / 2 * α ^ (J - 2) ≤ z 1 ∧ z 1 ≤ 2 * η * α ^ (J - 2) at HU
  have hU0 : 0 ≤ z 1 := (by positivity : 0 ≤ η / 2 * α ^ (J - 2)).trans HU.1
  have hU1 : z 1 ≤ 1 := by
    have H := mul_le_mul_of_nonneg_left (pow_le_one₀ hα.1.le hα.2 (n := J - 2)) (by positivity : 0 ≤ 2 * η)
    nlinarith only [HU.2, H, hη1000]
  have hV0 : 0 ≤ z 2 := by rw [Hfactor]; exact mul_nonneg hw.le (HB 1).1.le
  have hwB : w ≤ b := by linarith only [hsum, le_abs_self w, abs_nonneg u]
  have hV : z 2 ≤ M * b / α ^ 2 := by
    rw [Hfactor]
    have H := mul_le_mul hwB (HB 1).2.2.2.1 (HB 1).1.le hb.le
    exact H.trans_eq (by ring)
  have Hbudget : A * M * b ≤ α ^ (2 * J) / 2 := by
    have Hε := (le_div_iff₀ (by positivity : 0 < 2 * A * M)).mp Hεsmall
    nlinarith only [mul_le_mul_of_nonneg_left hsmall (mul_pos hA0 hM0).le,
      mul_le_mul_of_nonneg_right Hε (pow_nonneg hα.1.le (2 * J))]
  have HMbudget : M * b ≤ α ^ 2 := by
    have Hpow := pow_le_pow_of_le_one hα.1.le hα.2 (by omega : 2 ≤ 2 * J)
    have H := mul_le_mul_of_nonneg_right hA (mul_nonneg hM0.le hb.le)
    nlinarith only [Hbudget, Hpow, H, sq_nonneg α]
  have hV1 : z 2 ≤ 1 := hV.trans ((div_le_one (sq_pos_of_pos hα.1)).mpr HMbudget)
  have HΘsmall : |terminalConnectionError h Y| ≤ 1 / (2 * α) := by
    calc
      _ ≤ A * α * z 1 * z 2 := HΘ
      _ ≤ A * α * 1 * (M * b / α ^ 2) := by gcongr
      _ = (A * M * b) / α := by field_simp
      _ ≤ (α ^ (2 * J) / 2) / α := div_le_div_of_nonneg_right Hbudget hα.1.le
      _ ≤ (1 / 2) / α := div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right (pow_le_one₀ hα.1.le hα.2) (by norm_num)) hα.1.le
      _ = _ := by ring
  have hRlow : 1 / α ≤ z 0 := le_trans (by
    apply (div_le_div_iff₀ hα.1 (by positivity : 0 < 2 * α)).mpr
    linarith only [hα.1]) Hradius
  have hFlow : 1 / α ≤ terminalConnectionPhase h Y := by
    have H := (abs_le.mp HΘsmall).1
    change -(1 / (2 * α)) ≤ terminalConnectionPhase h Y - z 0 at H
    have Hid : 3 / (2 * α) - 1 / (2 * α) = 1 / α := by ring
    linarith only [H, Hradius, Hid]
  have hF0 : 0 < terminalConnectionPhase h Y := (one_div_pos.mpr hα.1).trans_le hFlow
  have hR0 : 0 < z 0 := (one_div_pos.mpr hα.1).trans_le hRlow
  have Hdiff := terminalReciprocalError_differential HΘreg Hzreg hF0.ne' hR0.ne'
  have Hrcol (i : Fin 3) : |fderiv ℝ (fun Z => terminalEntranceInput h Z 0) Y (Pi.single i 1)| ≤ D / α ^ 2 := by
    rw [fderiv_apply (Hzreg.differentiableAt (by norm_num)) 0]
    have H := (fderiv ℝ (terminalEntranceInput h) Y).le_opNorm (Pi.single i 1)
    simp only [Pi.norm_single, norm_one, mul_one] at H
    exact (norm_le_pi_norm (fderiv ℝ (terminalEntranceInput h) Y (Pi.single i 1)) 0).trans (H.trans Hzder)
  have Hval := reciprocal_difference_value_bound hα.1 hFlow hRlow
  have Hder (i : Fin 3) : |fderiv ℝ (terminalReciprocalError h) Y (Pi.single i 1)| ≤
      2 * α ^ 2 * |fderiv ℝ (terminalConnectionError h) Y (Pi.single i 1)| +
        4 * D * α * |terminalConnectionError h Y| := by
    rw [Hdiff.2.2]
    exact reciprocal_difference_derivative_bound hα.1 hFlow hRlow (Hrcol i)
  exact ⟨HV, Hdiff.1, hFlow, hRlow,
    reciprocal_difference_amplitude_bounds hα hA0.le hD0 hU0 ⟨hV0, hV1⟩ HΘ Hval HΘ01 HΘ2 Hder⟩

end BianchiIX
