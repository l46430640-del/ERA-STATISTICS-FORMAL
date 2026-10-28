import BianchiIX.Dynamics.ReferenceShiftedVariation
import BianchiIX.Dynamics.ReferenceTail
import BianchiIX.Dynamics.EntranceReturnDifferential

noncomputable section

namespace BianchiIX

open Set

def referenceEntranceState (k v : ℝ) : ProjectiveState := ![1 + Real.sqrt (k ^ 2 - v ^ 2), 0, v, 0]

theorem referencePulse_height_entry {k v : ℝ} (hk : 0 < k) (hv : 0 < v ∧ v < k) :
    referencePulse k (-referenceHeightTime k v) = referenceEntranceState k v := by
  have H := referencePulse_height_exit hk hv
  have HM := congrFun H 0
  have HV := congrFun H 2
  change 1 - k * Real.tanh (k * referenceHeightTime k v) = 1 - Real.sqrt (k ^ 2 - v ^ 2) at HM
  change k / Real.cosh (k * referenceHeightTime k v) = v at HV
  ext i
  fin_cases i
  · dsimp [referencePulse, referenceEntranceState]
    rw [mul_neg, Real.tanh_neg]
    linarith only [HM]
  · rfl
  · change k / Real.cosh (k * (-referenceHeightTime k v)) = v
    rw [mul_neg, Real.cosh_neg]
    exact HV
  · rfl

theorem referencePulse_active_lt_one_before {k t : ℝ} (hk : 1 < k) (ht : t < -referenceHalfTime k) :
    referencePulse k t 2 < 1 := by
  have hk0 : 0 < k := lt_trans zero_lt_one hk
  have hhalf : k * referenceHalfTime k = Real.arcosh k := by
    dsimp [referenceHalfTime]
    field_simp
  have ht0 : t < 0 := ht.trans (neg_neg_of_pos (referenceHalfTime_pos hk))
  have H := mul_lt_mul_of_pos_left ht hk0
  rw [mul_neg, hhalf] at H
  have hcosh : k < Real.cosh (k * t) := by
    calc
      k = Real.cosh (Real.arcosh k) := (Real.cosh_arcosh hk.le).symm
      _ < Real.cosh (k * t) := by
        apply Real.cosh_lt_cosh.mpr
        rw [abs_of_pos (Real.arcosh_pos hk), abs_of_neg (mul_neg_of_pos_of_neg hk0 ht0)]
        linarith only [H]
  exact (div_lt_one (Real.cosh_pos _)).mpr hcosh

theorem referenceEntrance_radius {k v : ℝ} (hk : 0 < k) (hv : 0 < v ∧ v < k) :
    coreRadius (referenceEntranceState k v 0) (referenceEntranceState k v 2) = k := by
  rw [← referencePulse_height_entry hk hv, coreRadius, referencePulse_energy, Real.sqrt_sq hk.le]

/-- The canonical first arrival agrees with the explicit upward reference segment. -/
theorem referenceEntrance_return {k v : ℝ} (hk : 7 / 4 ≤ k) (hv : 0 < v ∧ v < 1) :
    entranceReturnTime (referenceEntranceState k v) =
        referenceShiftClock k (-referenceHeightTime k v) (-referenceHalfTime k) ∧
      entranceReturnState (referenceEntranceState k v) = referencePulse k (-referenceHalfTime k) := by
  let y := referenceEntranceState k v
  let s := -referenceHeightTime k v
  let t := -referenceHalfTime k
  let T := referenceShiftClock k s t
  have hk0 : 0 < k := by linarith
  have hk1 : 1 < k := by linarith
  have hentry : referencePulse k s = y := referencePulse_height_entry hk0 ⟨hv.1, hv.2.trans hk1⟩
  have hR : coreRadius (y 0) (y 2) = k := referenceEntrance_radius hk0 ⟨hv.1, hv.2.trans hk1⟩
  have hm : 1 ≤ y 0 := le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := by dsimp [y, referenceEntranceState]; norm_num
  have hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := by dsimp [y, referenceEntranceState]; norm_num
  have hvalid := (entranceReturn_regular (by rw [hR]; exact hk) hm hu hv hw).1
  have hst : s < t := neg_lt_neg (referenceHalfTime_lt_heightTime hk1 hv)
  have hT : 0 < T := by
    have H := referenceShiftClock_strictMono k s hst
    simpa only [referenceShiftClock_initial] using H
  have horbit (r : ℝ) : projectiveOriginalFlow y 0 (referenceShiftClock k s r) = referencePulse k r := by
    rw [← hentry]
    exact referenceShiftClock_projective_orbit k s r
  have hdom : T ∈ normalizedMaxDomain (fromProjectiveState y) 0 := by
    rw [← hentry]
    exact (referenceShiftClock_normalized_orbit k s t).1
  have hhit : projectiveActiveWall (normalizedMaxCurve (fromProjectiveState y) 0 T) = 1 := by
    change projectiveOriginalFlow y 0 T 2 = 1
    rw [horbit, referencePulse_entry hk1]
    rfl
  have hle : entranceReturnTime y ≤ T := hvalid.1.2 ⟨hT, hdom, hhit⟩
  have hclock : Continuous (referenceShiftClock k s) :=
    continuous_iff_continuousAt.mpr fun r => (hasDerivAt_referenceShiftClock k s r).continuousAt
  have hmem : entranceReturnTime y ∈ Icc (referenceShiftClock k s s) (referenceShiftClock k s t) := by
    rw [referenceShiftClock_initial]
    exact ⟨hvalid.1.1.1.le, hle⟩
  obtain ⟨r, hr, he⟩ := intermediate_value_Icc hst.le hclock.continuousOn hmem
  have hrhit : referencePulse k r 2 = 1 := by
    rw [← horbit, he]
    exact hvalid.1.1.2.2
  have hrt : r = t := by
    by_contra hn
    have H := referencePulse_active_lt_one_before hk1 (lt_of_le_of_ne hr.2 hn)
    rw [hrhit] at H
    exact lt_irrefl _ H
  have htime : entranceReturnTime y = T := by rw [hrt] at he; exact he.symm
  refine ⟨htime, ?_⟩
  change projectiveOriginalFlow y 0 (entranceReturnTime y) = referencePulse k t
  rw [htime, horbit]

end BianchiIX
