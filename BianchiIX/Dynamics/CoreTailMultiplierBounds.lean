import BianchiIX.Dynamics.CoreTailClockMultiplier
import BianchiIX.Dynamics.CoreTailHeightOrder
import BianchiIX.Dynamics.ExitActualMultipliers

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The canonical tail multipliers and their logarithmic derivatives are uniform over terminal heights. -/
theorem exists_coreTailMultiplier_bounds_uniform {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ < 1)
    {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η < 1 → (0 < α ∧ α ≤ 1) → 0 < b →
      b ≤ ε * α ^ J → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧ ∀ i : Fin 2,
        ContDiffAt ℝ 2 (fun Z => coreTailMultiplier h Z i) Y ∧
        ContDiffAt ℝ 2 (fun Z => Real.log (coreTailMultiplier h Z i)) Y ∧
        1 / C ≤ coreTailMultiplier h Y i ∧ coreTailMultiplier h Y i ≤ C ∧
        ‖fderiv ℝ (fun Z => Real.log (coreTailMultiplier h Z i)) Y‖ ≤ C / α := by
  obtain ⟨A, hA, ε, hε, HA⟩ := exists_terminal_exitClock_multiplier_bounds hη₀ hJ
  let L := Real.log (1 / η₀) + J * Real.exp (-1)
  have hL : 0 ≤ L := add_nonneg
    (Real.log_nonneg ((le_div_iff₀ hη₀.1).mpr (by linarith only [hη₀.2])))
    (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)
  have hA0 : 0 < A := lt_of_lt_of_le (by norm_num) hA
  let C := A * (1 + L)
  have hAC : A ≤ C := by dsimp only [C]; nlinarith only [hA0, hL]
  refine ⟨C, hA.trans hAC, ε, hε, ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum Y h
  have hη : 0 < η := hη₀.1.trans_le hηlo
  obtain ⟨HV₀, I, hIo, hI, hcover, U, hUo, hYU, HR, _, _, HF⟩ := HA α b u w hα hb hsmall hsum
  have hh1 : h < 1 := by
    have H := mul_le_mul_of_nonneg_left (pow_le_one₀ hα.1.le hα.2 (n := J)) hη.le
    exact H.trans_lt (by simpa only [mul_one] using hηhi)
  obtain ⟨HV, htime⟩ := coreTailValid_of_height_le HV₀
    (mul_le_mul_of_nonneg_right hηlo (pow_nonneg hα.1.le J)) hh1
  let S := exitTailLength η α J
  let S₀ := exitTailLength η₀ α J
  have hS : 0 ≤ S := exitTailLength_nonneg ⟨hη, hηhi.le⟩ hα J
  have hSS₀ : S ≤ S₀ := by
    have H := mul_le_mul_of_nonneg_right hηlo (pow_nonneg hα.1.le J)
    rw [← exp_neg_exitTailLength hη₀.1 hα.1 J, ← exp_neg_exitTailLength hη hα.1 J] at H
    exact neg_le_neg_iff.mp (Real.exp_le_exp.mp H)
  have hclock : exitEntryClock (Y, coreTailTime (η₀ * α ^ J) Y) = S₀ := by
    change -Real.log (coreTailState (η₀ * α ^ J) Y 2) = S₀
    rw [coreTailState_active HV₀, ← exp_neg_exitTailLength hη₀.1 hα.1 J, Real.log_exp, neg_neg]
  have heh : -Real.log h = S := by
    change -Real.log (η * α ^ J) = S
    rw [← exp_neg_exitTailLength hη hα.1 J, Real.log_exp, neg_neg]
  have hR : 1 < Y 0 := by change 1 < 2 + 2 * α; linarith only [hα.1]
  have hreg := coreTail_regular_of_valid hR HV
  have Hbounds := HF S ⟨hS, hSS₀⟩
  have HsumD : ‖fderiv ℝ (fun Z => exitClockLogMultiplier I 0 Z S) Y‖ +
      ‖fderiv ℝ (fun Z => exitClockLogMultiplier I 1 Z S) Y‖ ≤ A * S := Hbounds.2.2.2
  have Hlength : S₀ ≤ L / α := by
    apply (le_div_iff₀ hα.1).mpr
    simpa only [mul_comm] using (exitTailLength_weighted_bounds ⟨hη₀.1, hη₀.2.le⟩ hα J).1
  refine ⟨HV, ?_⟩
  intro i
  have HE := coreTailMultiplier_eventuallyEq_exitClock hIo hI hUo hYU HR hR HV
    HV₀.1.1.1.le hcover htime (by rw [heh, hclock]; exact ⟨hS, hSS₀⟩) i
  rw [heh] at HE
  have heq : coreTailMultiplier h Y i = Real.exp (exitClockLogMultiplier I i Y S) := HE.self_of_nhds
  have Hlog : (fun Z => Real.log (coreTailMultiplier h Z i)) =ᶠ[𝓝 Y]
      (fun Z => exitClockLogMultiplier I i Z S) := by
    filter_upwards [HE] with Z hZ
    rw [hZ, Real.log_exp]
  have Hsmooth := contDiffAt_coreTailMultiplier_two hR HV hreg.1 i
  refine ⟨Hsmooth.1, Hsmooth.2, ?_, ?_, ?_⟩
  · rw [heq]
    exact (one_div_le_one_div_of_le hA0 hAC).trans (Hbounds.2.2.1 i).2.2.1
  · rw [heq]
    exact (Hbounds.2.2.1 i).2.2.2.1.trans hAC
  · rw [Hlog.fderiv_eq]
    have Hi : ‖fderiv ℝ (fun Z => exitClockLogMultiplier I i Z S) Y‖ ≤ A * S := by
      fin_cases i
      · exact (le_add_of_nonneg_right (norm_nonneg
          (fderiv ℝ (fun Z => exitClockLogMultiplier I 1 Z S) Y))).trans HsumD
      · exact (le_add_of_nonneg_left (norm_nonneg
          (fderiv ℝ (fun Z => exitClockLogMultiplier I 0 Z S) Y))).trans HsumD
    calc
      _ ≤ A * S := Hi
      _ ≤ A * (L / α) := mul_le_mul_of_nonneg_left (hSS₀.trans Hlength) hA0.le
      _ ≤ C / α := by
        rw [← mul_div_assoc]
        apply div_le_div_of_nonneg_right _ hα.1.le
        dsimp only [C]
        nlinarith only [hA0]

end BianchiIX
