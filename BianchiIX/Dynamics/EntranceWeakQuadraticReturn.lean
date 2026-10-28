import BianchiIX.Dynamics.EntranceWeakFactorization
import BianchiIX.Dynamics.EntranceWeakProduct
import BianchiIX.Dynamics.EntranceReturnSegment

noncomputable section

namespace BianchiIX

open Set MeasureTheory

def entranceWeakQuadraticLoss (y : ProjectiveState) : ℝ :=
  (∫ t in 0..entranceReturnTime y,
    normalizedProjectiveRate (fromProjectiveState y) 0 t *
      (y 2) ^ 2 * Real.exp (-4 * ∫ r in 0..t, normalizedProjectiveRate (fromProjectiveState y) 0 r) *
      entranceWeakDriftWeight (projectiveOriginalFlow y 0 t)) +
    (y 2) ^ 2 * Real.exp (-4 * ∫ r in 0..entranceReturnTime y,
      normalizedProjectiveRate (fromProjectiveState y) 0 r) * entranceWeakCorrectionWeight (entranceReturnState y)

/-- An exact quadratic factorization of the physical return, retaining the moving endpoint. -/
theorem entranceReturn_weak_quadratic_of_segment {y : ProjectiveState}
    (hD : 0 < projectiveStateDenom y) (H : entranceReturnValid y) (hu : y 1 = 0) (hv : 0 < y 2)
    (hM : ∀ t ∈ Icc 0 (entranceReturnTime y), 2 ≤ projectiveOriginalFlow y 0 t 0)
    (hW : ∀ t ∈ Icc 0 (entranceReturnTime y), |projectiveOriginalFlow y 0 t 3| < 1 / 200) :
    coreRadius (entranceReturnState y 0) (entranceReturnState y 2) =
      entranceStableRadius y - (y 3) ^ 2 * entranceWeakQuadraticLoss y ∧
      0 < entranceWeakQuadraticLoss y := by
  let x := fromProjectiveState y
  let T := entranceReturnTime y
  let Y := projectiveOriginalFlow y 0
  let a := normalizedProjectiveRate x 0
  let E := fun t => Real.exp (-4 * ∫ r in 0..t, a r)
  let I := fun t => a t * (y 2) ^ 2 * E t * entranceWeakDriftWeight (Y t)
  change ∀ t ∈ Icc 0 T, 2 ≤ Y t 0 at hM
  change ∀ t ∈ Icc 0 T, |Y t 3| < 1 / 200 at hW
  have hT : 0 < T := H.1.1.1
  have hA0 : 0 < 1 + x 0 := fromProjectiveState_clock_pos hD
  have hinit : Y 0 = y := projectiveOriginalFlow_initial hD 0
  have hend : Y T = entranceReturnState y := rfl
  have hA (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < a t := (H.2.1 t ht).2
  have hY (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivAt Y (a t • projectiveField (Y t)) t :=
    hasDerivAt_toProjectiveState_normalized (hasDerivAt_normalizedMaxCurve (H.2.1 t ht).1)
      (hA t ht).ne' ((normalizedMaxCurve_constraint (H.2.1 t ht).1).trans (fromProjectiveState_constraint hD.ne'))
  have hfactor (t : ℝ) (ht : t ∈ Icc 0 T) (i : Fin 3) :
      Y t i.succ = y i.succ * normalizedProjectiveWallMultiplier x t i := by
    have HF := normalizedProjectiveWallMultiplier_formula (H.2.1 t ht).1 hA0 (hA t ht) i
    rw [toProjectiveState_fromProjectiveState hD.ne'] at HF
    exact HF
  have hU (t : ℝ) (ht : t ∈ Icc 0 T) : Y t 1 = 0 := by
    simpa only [Fin.succ_zero_eq_one, hu, zero_mul] using hfactor t ht 0
  have hV (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < Y t 2 := by
    have HF := hfactor t ht 1
    change Y t 2 = y 2 * normalizedProjectiveWallMultiplier x t 1 at HF
    rw [HF]
    exact mul_pos hv (normalizedProjectiveWallMultiplier_pos _ _ _)
  have hac : ContinuousOn a (Icc 0 T) := (continuousOn_normalizedProjectiveRate x 0).mono
    (fun t ht => (H.2.1 t ht).1)
  have hclock : ContinuousOn (fun t => ∫ r in 0..t, a r) (Icc 0 T) := by
    simpa only [uIcc_of_le hT.le] using intervalIntegral.continuousOn_primitive_interval'
      (hac.intervalIntegrable_of_Icc hT.le) left_mem_uIcc
  have hEc : ContinuousOn E (Icc 0 T) := Real.continuous_exp.comp_continuousOn (hclock.const_mul (-4))
  have hproduct (t : ℝ) (ht : t ∈ Icc 0 T) :
      (Y t 2 * Y t 3) ^ 2 = (y 3) ^ 2 * (y 2) ^ 2 * E t := by
    have HP : Y t 2 * Y t 3 = y 2 * y 3 * Real.exp (-2 * ∫ r in 0..t, a r) :=
      entranceReturn_weak_product hD H hu ht
    have HE : (Real.exp (-2 * ∫ r in 0..t, a r)) ^ 2 = E t := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [HP, mul_pow, mul_pow, HE]
    ring
  have hgc : ContinuousOn (fun t => entranceWeakDriftWeight (Y t)) (Icc 0 T) := by
    intro t ht
    exact ((continuousAt_entranceWeak_weights (hM t ht) (by rw [hU t ht]; norm_num)
      (hW t ht) (hV t ht)).1.comp (hY t ht).continuousAt).continuousWithinAt
  have hIc : ContinuousOn I (Icc 0 T) := ((hac.mul continuousOn_const).mul hEc).mul hgc
  have hrc : ContinuousOn (fun t => entranceStableRadius (Y t)) (Icc 0 T) := by
    intro t ht
    exact ((contDiffAt_entranceStableRadius_two (hM t ht) (by rw [hU t ht]; norm_num)
      (hW t ht) (hV t ht)).continuousAt.comp (hY t ht).continuousAt).continuousWithinAt
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivAt (fun s => entranceStableRadius (Y s)) (-(y 3) ^ 2 * I t) t := by
    have HD := hasDerivAt_entranceStableRadius_zero_strong (hY t ht) (hM t ht) (hU t ht) (hW t ht) (hV t ht)
    rw [hproduct t ht] at HD
    convert! HD using 1
    dsimp [I]
    ring
  have HI := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le hrc
    (fun t ht => hd t (Ioo_subset_Icc_self ht)) ((hIc.const_mul (-(y 3) ^ 2)).intervalIntegrable_of_Icc hT.le)
  rw [intervalIntegral.integral_const_mul, hinit] at HI
  have hlast : T ∈ Icc 0 T := ⟨hT.le, le_rfl⟩
  have HE := entranceRadiusCorrection_zero_strong (hM T hlast) (hU T hlast) (hW T hlast).le (hV T hlast)
  change entranceStableRadius (Y T) - coreRadius (Y T 0) (Y T 2) =
    (Y T 3) ^ 2 * entranceWeakCorrectionWeight (Y T) at HE
  have HF := hproduct T hlast
  have hhit : Y T 2 = 1 := H.1.1.2.2
  rw [hhit, one_mul] at HF
  rw [HF] at HE
  have hcost : entranceWeakQuadraticLoss y = (∫ t in 0..T, I t) +
      (y 2) ^ 2 * E T * entranceWeakCorrectionWeight (Y T) := rfl
  constructor
  · rw [hcost, ← hend]
    nlinarith only [HI, HE]
  · rw [hcost]
    have hInonneg : 0 ≤ ∫ t in 0..T, I t := intervalIntegral.integral_nonneg hT.le (by
      intro t ht
      exact mul_nonneg (mul_nonneg (mul_nonneg (hA t ht).le (sq_nonneg _)) (Real.exp_pos _).le)
        (entranceWeak_weights_pos (hM t ht) (hV t ht)).1.le)
    exact add_pos_of_nonneg_of_pos hInonneg
      (mul_pos (mul_pos (sq_pos_of_pos hv) (Real.exp_pos _))
        (entranceWeak_weights_pos (hM T hlast) (hV T hlast)).2)

theorem entranceReturn_weak_quadratic {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0) (hu : y 1 = 0)
    (hv : 0 < y 2 ∧ y 2 < 1) (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    coreRadius (entranceReturnState y 0) (entranceReturnState y 2) =
      entranceStableRadius y - (y 3) ^ 2 * entranceWeakQuadraticLoss y ∧
      0 < entranceWeakQuadraticLoss y := by
  have hu' : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := by rw [hu]; norm_num
  have hy := entranceReturn_region hk hm hu' hv hw
  apply entranceReturn_weak_quadratic_of_segment (entrance_initial_denom_pos hk hm hu' hv hw)
    (entranceReturn_regular hk hm hu' hv hw).1 hu hv.1
  · intro t ht
    linarith [(entranceRegion_phase hk (hy t ht)).1]
  · intro t ht
    rw [abs_of_nonneg (hy t ht).2.2.2.2.1]
    linarith [(hy t ht).2.2.2.2.2]

theorem entranceReturn_weak_radius_lt {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0) (hu : y 1 = 0)
    (hv : 0 < y 2 ∧ y 2 < 1) (hw : 0 < y 3 ∧ y 3 ≤ 1 / 10000) :
    coreRadius (entranceReturnState y 0) (entranceReturnState y 2) < entranceStableRadius y := by
  obtain ⟨H, hpos⟩ := entranceReturn_weak_quadratic hk hm hu hv ⟨hw.1.le, hw.2⟩
  rw [H]
  exact sub_lt_self _ (mul_pos (sq_pos_of_pos hw.1) hpos)

end BianchiIX
