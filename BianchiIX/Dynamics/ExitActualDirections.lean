import BianchiIX.Dynamics.ExitActualFineColumns

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem clm_three_coordinate_bound (L : ExitTailState →L[ℝ] ℝ) (v : ExitTailState) :
    |L v| ≤ |v 0| * |L (Pi.single 0 1)| + |v 1| * |L (Pi.single 1 1)| + |v 2| * |L (Pi.single 2 1)| := by
  have hv : v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 + v 2 • Pi.single 2 1 := by
    ext j
    fin_cases j <;> simp
  conv_lhs => rw [hv, map_add, map_add, map_smul, map_smul, map_smul]
  simpa only [smul_eq_mul, abs_mul] using
    (abs_add_le (v 0 * L (Pi.single 0 1) + v 1 * L (Pi.single 1 1))
      (v 2 * L (Pi.single 2 1))).trans (add_le_add (abs_add_le _ _) le_rfl)

/-- The weighted directional estimates of D.9, on every prefix, follow by coordinate linearity. -/
theorem exists_terminal_exitClock_direction_bounds {η : ℝ} (hη : 0 < η ∧ η < 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let S := exitTailLength η α J
      coreTailValid h Y ∧ ∃ I : Set ℝ, IsOpen I ∧ Convex ℝ I ∧ Icc 0 (coreTailTime h Y) ⊆ I ∧
        (∀ t ∈ I, exitEntryRegular Y t) ∧ exitClockFlow I (Y, 0) = Y ∧
        ((fun Z => toExitTailState (coreTailState h Z)) =ᶠ[𝓝 Y] (fun Z => exitClockFlow I (Z, S))) ∧
        ∀ s ∈ Icc 0 S, ∀ q ∈ Icc 0 s, ContDiffAt ℝ 2 (exitClockFlow I) (Y, q) ∧
          ∀ v : ExitTailState,
            |fderiv ℝ (fun Z => exitClockFlow I (Z, q)) Y v 0| ≤
              C * (|v 0| + |v 1| + b * (1 + s) * |v 2|) ∧
            ∀ i : Fin 2, ContDiffAt ℝ 1 (fun Z => exitClockLogMultiplier I i Z q) Y ∧
              |fderiv ℝ (fun Z => exitClockLogMultiplier I i Z q) Y v| ≤
                C * (|v 1| + |v 2| + s * (|v 0| + |v 1| + b * (1 + s) * |v 2|)) := by
  obtain ⟨C, hC, ε, hε, HE⟩ := exists_terminal_exitClock_fine_columns hη hJ
  refine ⟨C, hC, ε, hε, ?_⟩
  intro α b u w hα hb hsmall hw Y h S
  obtain ⟨hvalid, I, hIo, hI, hcover, Htube, hinit, hend, HF⟩ := HE α b u w hα hb hsmall hw
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  refine ⟨hvalid, I, hIo, hI, hcover, Htube, hinit, hend, ?_⟩
  intro s hs q hq
  have hqS : q ∈ Icc 0 S := ⟨hq.1, hq.2.trans hs.2⟩
  have hs0 : 0 ≤ s := hs.1
  have hq0 : 0 ≤ q := hq.1
  refine ⟨(HF q hqS).1, ?_⟩
  intro v
  let L := fderiv ℝ (fun Z => exitClockFlow I (Z, q)) Y
  have hcoord (j : Fin 3) : |L (Pi.single j 1) 0| ≤ C := by
    have H := (norm_le_pi_norm (L (Pi.single j 1)) 0).trans ((L.le_opNorm (Pi.single j 1)).trans
      (mul_le_mul_of_nonneg_right (HF q hqS).2.1 (norm_nonneg _)))
    simpa only [Real.norm_eq_abs, Pi.norm_single, norm_one, mul_one] using H
  have hweak : |L (Pi.single 2 1) 0| ≤ C * b * (1 + s) :=
    (HF q hqS).2.2.2.1.trans (by gcongr; exact hq.2)
  refine ⟨?_, ?_⟩
  · have H := clm_three_coordinate_bound ((ContinuousLinearMap.proj 0).comp L) v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at H
    have HB := add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left (hcoord 0) (abs_nonneg (v 0)))
      (mul_le_mul_of_nonneg_left (hcoord 1) (abs_nonneg (v 1))))
      (mul_le_mul_of_nonneg_left hweak (abs_nonneg (v 2)))
    exact H.trans (HB.trans_eq (by ring))
  · intro i
    have HL := (HF q hqS).2.2.2.2 i
    refine ⟨HL.1, ?_⟩
    have H0 : |fderiv ℝ (fun Z => exitClockLogMultiplier I i Z q) Y (Pi.single 0 1)| ≤ C * s :=
      HL.2.1.trans (mul_le_mul_of_nonneg_left hq.2 hC0)
    have H1 : |fderiv ℝ (fun Z => exitClockLogMultiplier I i Z q) Y (Pi.single 1 1)| ≤ C * s :=
      HL.2.2.1.trans (mul_le_mul_of_nonneg_left hq.2 hC0)
    have H2 : |fderiv ℝ (fun Z => exitClockLogMultiplier I i Z q) Y (Pi.single 2 1)| ≤
        C * (1 + b * s * (1 + s)) := HL.2.2.2.1.trans (by gcongr <;> exact hq.2)
    have H := clm_three_coordinate_bound (fderiv ℝ (fun Z => exitClockLogMultiplier I i Z q) Y) v
    have HB := add_le_add (add_le_add (mul_le_mul_of_nonneg_left H0 (abs_nonneg (v 0)))
      (mul_le_mul_of_nonneg_left H1 (abs_nonneg (v 1)))) (mul_le_mul_of_nonneg_left H2 (abs_nonneg (v 2)))
    exact H.trans (HB.trans (by nlinarith only [mul_nonneg hC0 (abs_nonneg (v 1))]))

end BianchiIX
