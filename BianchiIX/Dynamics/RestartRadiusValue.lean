import BianchiIX.Dynamics.RestartQuadraticControl
import BianchiIX.Algebra.RestartRadialTail

noncomputable section

namespace BianchiIX

open Set

/-- The accumulated radial value error retains the decaying strong-wall factor, including zero radius. -/
theorem exists_restartSectionRadius_value_error :
    ∃ C ≥ (32 : ℝ), ∀ (h b T : ℝ) (Z : RestartCenterState),
      0 < h → C * h ≤ 1 / 4 → (0 < b ∧ b ≤ 1 / 16) → 0 ≤ T → C * b * T ≤ 1 / 8 → ‖Z‖ ≤ b / 2 →
      ∀ t ∈ Icc (0 : ℝ) T,
        |restartSectionRadius h t Z - restartSectionRadius h 0 Z| ≤ C * h * b ^ 2 + 2 * C * b ^ 3 * t ∧
        |restartRadialNorm (restartSectionCenterFlow h t Z) - restartSectionRadius h 0 Z| ≤
          C * h * b ^ 2 + 2 * C * b ^ 3 * t + 24 * h * b * Real.exp (-2 * t) := by
  obtain ⟨C, hC, HC⟩ := exists_restartSectionQuadratic_control
  have hC0 : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 32) hC
  refine ⟨C, hC, ?_⟩
  intro h b T Z hh hCh hb hT hCb hZ
  have H := HC h b T Z hh hCh hb hT hCb hZ
  have hb0 : 0 ≤ b := hb.1.le
  have hcoord (W : RestartCenterState) : |W 1 - W 2| ≤ 2 * ‖W‖ := by
    have H1 : |W 1| ≤ ‖W‖ := norm_le_pi_norm W 1
    have H2 : |W 2| ≤ ‖W‖ := norm_le_pi_norm W 2
    linarith only [abs_sub (W 1) (W 2), H1, H2]
  have hcoords (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      |restartSectionCenterFlow h t Z 0| ≤ b ∧
        |restartSectionCenterFlow h t Z 1 - restartSectionCenterFlow h t Z 2| ≤ 2 * b :=
    ⟨(norm_le_pi_norm (restartSectionCenterFlow h t Z) 0).trans (H t ht).2.2.2.1,
      (hcoord _).trans (mul_le_mul_of_nonneg_left (H t ht).2.2.2.1 (by norm_num))⟩
  have HR (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : restartSectionRadius h t Z ≤ 4 * b :=
    sqrt_restartQuadratic_le_radius ⟨(H t ht).1.le, (H t ht).2.2.1⟩ hb0 (hcoords t ht).1 (hcoords t ht).2
  have Hvalue : ∀ t ∈ Icc (0 : ℝ) T,
      |restartSectionRadius h t Z - restartSectionRadius h 0 Z| ≤ C * h * b ^ 2 + 2 * C * b ^ 3 * t := by
    by_cases H0 : restartSectionQuadratic h 0 Z = 0
    · intro t ht
      have Ht : restartSectionQuadratic h t Z = 0 := by
        have Hu := (H t ht).2.2.2.2.2.2.2
        rw [H0] at Hu
        linarith only [Hu, restartSectionQuadratic_nonneg h t Z]
      simp only [restartSectionRadius, H0, Ht, Real.sqrt_zero, sub_self, abs_zero]
      positivity [ht.1]
    have Hpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : 0 < restartSectionQuadratic h t Z := by
      have Hinit := lt_of_le_of_ne (restartSectionQuadratic_nonneg h 0 Z) (Ne.symm H0)
      linarith only [Hinit, (H t ht).2.2.2.2.2.2.1]
    have HD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :=
      hasDerivAt_restartSectionRadius (H t ht).2.2.2.2.1 (Hpos t ht)
    have HB (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
        |restartSectionQuadraticRate h t Z / (2 * restartSectionRadius h t Z)| ≤
          (2 * C) * ((h * b ^ 2) * Real.exp (-2 * t) + b ^ 3) := by
      have hn0 : 0 ≤ restartSectionStrongWall h t Z := (H t ht).1.le
      have hRpos : 0 < restartSectionRadius h t Z := Real.sqrt_pos.mpr (Hpos t ht)
      have hnorm : ‖restartSectionCenterFlow h t Z‖ ≤ b := (H t ht).2.2.2.1
      have hsq : restartSectionRadius h t Z ^ 2 = restartSectionQuadratic h t Z :=
        Real.sq_sqrt (restartSectionQuadratic_nonneg h t Z)
      have Hcoeff : restartSectionStrongWall h t Z * ‖restartSectionCenterFlow h t Z‖ +
          ‖restartSectionCenterFlow h t Z‖ ^ 2 ≤ restartSectionStrongWall h t Z * b + b ^ 2 := by
        have Hs := mul_self_le_mul_self (norm_nonneg (restartSectionCenterFlow h t Z)) hnorm
        nlinarith only [Hs, mul_le_mul_of_nonneg_left hnorm hn0]
      have Hrate : |restartSectionQuadraticRate h t Z / (2 * restartSectionRadius h t Z)| ≤
          2 * C * (restartSectionStrongWall h t Z * b ^ 2 + b ^ 3) := by
        rw [abs_div, abs_of_pos (mul_pos (by norm_num) hRpos)]
        apply (div_le_iff₀ (mul_pos (by norm_num) hRpos)).mpr
        calc
          _ ≤ C * (restartSectionStrongWall h t Z * ‖restartSectionCenterFlow h t Z‖ +
              ‖restartSectionCenterFlow h t Z‖ ^ 2) * restartSectionQuadratic h t Z :=
            (H t ht).2.2.2.2.2.1
          _ = C * (restartSectionStrongWall h t Z * ‖restartSectionCenterFlow h t Z‖ +
              ‖restartSectionCenterFlow h t Z‖ ^ 2) * (restartSectionRadius h t Z * restartSectionRadius h t Z) := by
            rw [← hsq]
            ring
          _ ≤ C * (restartSectionStrongWall h t Z * b + b ^ 2) * (4 * b * restartSectionRadius h t Z) := by
            gcongr
            exact HR t ht
          _ = _ := by ring
      calc
        _ ≤ 2 * C * (restartSectionStrongWall h t Z * b ^ 2 + b ^ 3) := Hrate
        _ ≤ 2 * C * ((h * Real.exp (-2 * t)) * b ^ 2 + b ^ 3) := by
          gcongr
          exact (H t ht).2.1
        _ = _ := by ring
    have HP := abs_sub_le_of_deriv_primitive HD
      (fun t _ => hasDerivAt_restartFastBudget (2 * C) (h * b ^ 2) (b ^ 3) t) HB
    intro t ht
    have HV := HP t ht
    rw [restartFastBudget_zero, sub_zero] at HV
    have HE := restartFastBudget_le (by positivity : 0 ≤ 2 * C)
      (by positivity : 0 ≤ h * b ^ 2) (pow_nonneg hb0 3) (T := t) le_rfl
    exact HV.trans (by nlinarith only [HE])
  intro t ht
  refine ⟨Hvalue t ht, ?_⟩
  have Htail := sqrt_restartQuadratic_tail ⟨(H t ht).1.le, (H t ht).2.2.1⟩ hb0 (hcoords t ht).1 (hcoords t ht).2
  change |restartSectionRadius h t Z - restartRadialNorm (restartSectionCenterFlow h t Z)| ≤
    24 * restartSectionStrongWall h t Z * b at Htail
  calc
    _ ≤ |restartRadialNorm (restartSectionCenterFlow h t Z) - restartSectionRadius h t Z| +
        |restartSectionRadius h t Z - restartSectionRadius h 0 Z| := abs_sub_le _ _ _
    _ ≤ 24 * restartSectionStrongWall h t Z * b + (C * h * b ^ 2 + 2 * C * b ^ 3 * t) := by
      rw [abs_sub_comm]
      exact add_le_add Htail (Hvalue t ht)
    _ ≤ C * h * b ^ 2 + 2 * C * b ^ 3 * t + 24 * h * b * Real.exp (-2 * t) := by
      nlinarith only [mul_le_mul_of_nonneg_right (H t ht).2.1 hb0]

end BianchiIX
