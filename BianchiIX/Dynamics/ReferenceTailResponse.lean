import BianchiIX.Dynamics.ReferenceRadiusResponse
import BianchiIX.Dynamics.ReferenceTail
import BianchiIX.Dynamics.ExitFlowVariation

noncomputable section

namespace BianchiIX

open Set

def referenceTailDuration (k h : ℝ) : ℝ :=
  referenceHeightTime k h - referenceHalfTime k

theorem referenceTailDuration_eq (k h : ℝ) :
    referenceTailDuration k h = (Real.arcosh (k / h) - Real.arcosh k) / k := by
  dsimp [referenceTailDuration, referenceHeightTime, referenceHalfTime]
  ring

theorem referenceShiftClock_tail (k h : ℝ) :
    referenceShiftClock k (referenceHalfTime k) (referenceHeightTime k h) =
      referenceTailTime k h := by
  rw [referenceTailTime, referencePulse_clock_integral]
  rfl

theorem referenceTransverseMode_tail_ratio {k h : ℝ} (hk : 1 < k)
    (hh : 0 < h ∧ h < 1) (r : ℝ) :
    referenceTransverseMode k r (referenceHeightTime k h) /
        referenceTransverseMode k r (referenceHalfTime k) =
      Real.exp (-r * referenceTailDuration k h) / h := by
  have hk0 : k ≠ 0 := (lt_trans zero_lt_one hk).ne'
  have hkh : 1 ≤ k / h := (one_lt_div hh.1).mpr (hh.2.trans hk) |>.le
  have ht : k * referenceHeightTime k h = Real.arcosh (k / h) := by
    dsimp [referenceHeightTime]; field_simp
  have hs : k * referenceHalfTime k = Real.arcosh k := by
    dsimp [referenceHalfTime]; field_simp
  rw [show -r * referenceTailDuration k h =
    -r * referenceHeightTime k h - (-r * referenceHalfTime k) by
      dsimp [referenceTailDuration]; ring, Real.exp_sub]
  dsimp only [referenceTransverseMode]
  rw [ht, hs, Real.cosh_arcosh hkh, Real.cosh_arcosh hk.le]
  field_simp

theorem toExitTailState_reference {k : ℝ} (hk : 0 ≤ k) (t : ℝ) :
    toExitTailState (referencePulse k t) = ![k, 0, 0] := by
  change ![coreRadius (referencePulse k t 0) (referencePulse k t 2), 0, 0] = _
  rw [referencePulse_radius hk]

theorem exitTailField_zero_walls (k h : ℝ) :
    exitTailField h ![k, 0, 0] = 0 := by
  ext i
  fin_cases i <;> simp [exitTailField, exitTailRadial, coupling]

theorem toExitTailState_fderiv {y : ProjectiveState} (hv : 0 < y 2) (w : ProjectiveState) :
    fderiv ℝ toExitTailState y w =
      ![fderiv ℝ (fun z : ProjectiveState => coreRadius (z 0) (z 2)) y w, w 1, w 3] := by
  have hd := (contDiffAt_toExitTailState 1 hv).differentiableAt (by norm_num)
  ext i
  have H := congrArg (fun L : ProjectiveState →L[ℝ] ℝ => L w) (fderiv_apply hd i)
  fin_cases i
  · exact H.symm
  · change fderiv ℝ (fun z : ProjectiveState => z 1) y w = _ at H
    rw [(hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 4) y).fderiv] at H
    exact H.symm
  · change fderiv ℝ (fun z : ProjectiveState => z 3) y w = _ at H
    rw [(hasFDerivAt_apply (𝕜 := ℝ) (3 : Fin 4) y).fderiv] at H
    exact H.symm

/-- The first integral removes the clock correction from the finite tail response. -/
theorem referenceTail_projected_variation {k h : ℝ} (hk : 1 < k)
    (hh : 0 < h ∧ h < 1) (w : ProjectiveState) :
    exitProjectedFlowVariation (referencePulse k (referenceHalfTime k)) 0
        (referenceTailTime k h) w =
      ![fderiv ℝ (fun z : ProjectiveState => coreRadius (z 0) (z 2))
          (referencePulse k (referenceHalfTime k)) w +
          2 * w 1 / k * (Real.exp (-(k ^ 2 / 2) * referenceTailDuration k h) - 1),
        Real.exp (-(k ^ 2 / 2) * referenceTailDuration k h) / h * w 1,
        Real.exp (-2 * referenceTailDuration k h) / h * w 3] := by
  have hk0 : 0 < k := lt_trans zero_lt_one hk
  have HR := referenceShiftedVariation_radius hk0 (referenceHalfTime k)
    (referenceHeightTime k h) w
  have HT := referenceForcedVariation_transverse (I := univ) convex_univ
    (fun t _ => hasDerivAt_referenceShiftedVariation k (referenceHalfTime k) t w)
    (mem_univ (referenceHalfTime k)) (mem_univ (referenceHeightTime k h))
  rw [referenceShiftedVariation_initial, referenceTransverseMode_tail_ratio hk hh,
    referenceTransverseMode_tail_ratio hk hh] at HT
  have hV : referencePulse k (referenceHalfTime k) 2 = 1 := by
    rw [referencePulse_exit hk]; rfl
  dsimp only at HR
  rw [hV, mul_one] at HR
  unfold exitProjectedFlowVariation exitClockProjection
  rw [← referenceShiftClock_tail, referenceShiftClock_projective_orbit,
    toExitTailState_reference hk0.le, exitTailField_zero_walls, smul_zero, sub_zero,
    toExitTailState_fderiv (referencePulse_active_pos hk0 _)]
  change ![_, referenceShiftedVariation k (referenceHalfTime k) w (referenceHeightTime k h) 1,
    referenceShiftedVariation k (referenceHalfTime k) w (referenceHeightTime k h) 3] = _
  ext i
  fin_cases i
  · exact HR
  · exact HT.1.trans (mul_comm _ _)
  · exact HT.2.trans (mul_comm _ _)

end BianchiIX
