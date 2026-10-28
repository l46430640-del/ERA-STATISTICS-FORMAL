import BianchiIX.Dynamics.CoreTailPerturbation
import BianchiIX.Dynamics.CompactTailMultiplierBounds
import BianchiIX.Algebra.CompactConnectionEntrance

noncomputable section

namespace BianchiIX

/-- One signed wall neighborhood gives B.45, B.46, the correct reflected branch, and the entrance phase range. -/
theorem exists_compact_tail_entrance {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 8) :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      coreTailValid η Y ∧ ContDiffAt ℝ 2 (coreTailTime η) Y ∧
        ContDiffAt ℝ 2 (coreTailState η) Y ∧ ContDiffAt ℝ 2 (coreTailReflectedRadius η) Y ∧
        7 / 4 ≤ -coreTailState η Y 0 - 1 ∧
        (7 / 4 ≤ coreTailReflectedRadius η Y ∧
          coreTailReflectedRadius η Y ≤ 4 - η ^ 2 / 24 ∧ coreTailReflectedRadius η Y < 4) ∧
        |coreTailReflectedRadius η Y - (Real.sqrt (Y 0 ^ 2 - η ^ 2) - 2)| ≤ C * (|Y 1| + |Y 2|) ∧
        C * (|Y 1| + |Y 2|) ≤ η ^ 2 / 24 ∧
        projectiveReflection (coreTailState η Y) =
          ![-coreTailState η Y 0, Y 1 * coreTailMultiplier η Y 0, Y 2 * coreTailMultiplier η Y 1, η] ∧
        ∀ i : Fin 2, 0 < coreTailMultiplier η Y i ∧
          ContDiffAt ℝ 2 (fun Z => coreTailMultiplier η Z i) Y ∧
          ContDiffAt ℝ 2 (fun Z => Real.log (coreTailMultiplier η Z i)) Y ∧
          coreTailMultiplier η Y i + (coreTailMultiplier η Y i)⁻¹ +
            ‖fderiv ℝ (fun Z => Real.log (coreTailMultiplier η Z i)) Y‖ +
            ‖fderiv ℝ (fderiv ℝ (fun Z => Real.log (coreTailMultiplier η Z i))) Y‖ ≤ C := by
  obtain ⟨εp, hεp, Cp, hCp, Hp⟩ := exists_compact_tail_phase_perturbation hη
  obtain ⟨εm, hεm, Cm, hCm, Hm⟩ := exists_compact_tail_multiplier_bounds hη
  let C := max Cp Cm
  have hC : 0 < C := lt_of_lt_of_le hCp (le_max_left _ _)
  let ε := min εp (min εm (η ^ 2 / (48 * C)))
  have hε : 0 < ε := lt_min hεp (lt_min hεm
    (div_pos (sq_pos_of_pos hη.1) (mul_pos (by norm_num) hC)))
  have hεp' : ε ≤ εp := min_le_left _ _
  have hεm' : ε ≤ εm := (min_le_right _ _).trans (min_le_left _ _)
  have hεb : ε ≤ η ^ 2 / (48 * C) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε, hε, C, hC, ?_⟩
  intro Y hk hu hw
  have Hphase := Hp Y hk (hu.trans hεp') (hw.trans hεp')
  have Hmult := Hm Y hk (hu.trans hεm') (hw.trans hεm')
  have hbudget : C * (|Y 1| + |Y 2|) ≤ η ^ 2 / 24 := by
    have H := (le_div_iff₀ (by positivity : 0 < 48 * C)).mp hεb
    nlinarith only [H, mul_le_mul_of_nonneg_left (add_le_add hu hw) hC.le]
  have henlarge : Cp * (|Y 1| + |Y 2|) ≤ C * (|Y 1| + |Y 2|) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hphase := Hphase.2.2.2.1.trans henlarge
  have hbranch := Hphase.2.2.2.2.trans (henlarge.trans hbudget)
  have hrange := compact_connection_perturbed_radius_range hk hη (hphase.trans hbudget)
  have hm : 7 / 4 ≤ -coreTailState η Y 0 - 1 :=
    (compact_connection_perturbed_radius_range hk hη hbranch).1
  refine ⟨Hphase.1, Hphase.2.1, Hphase.2.2.1,
    contDiffAt_coreTailReflectedRadius 2 Hphase.2.2.1 (by linarith only [hm]),
    hm, hrange, hphase, hbudget, Hmult.2.2.2.1, ?_⟩
  intro i
  have Hi := Hmult.2.2.2.2 i
  exact ⟨Hi.1, Hi.2.1, Hi.2.2.1, Hi.2.2.2.trans (le_max_right _ _)⟩

end BianchiIX
