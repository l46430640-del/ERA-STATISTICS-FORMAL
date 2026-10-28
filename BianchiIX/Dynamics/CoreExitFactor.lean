import BianchiIX.Algebra.RadialArrival
import BianchiIX.Dynamics.CoreFlowGrowth

noncomputable section

namespace BianchiIX

open Set

def coreExitRadialFactor (y : ProjectiveState) : ℝ :=
  let z := coreAngle (y 0) (y 2)
  let r := coreRadius (y 0) (y 2)
  (-Real.tanh z) / (-Real.tanh z + coreAngleField z (toCoreAngleState y) 0 / r)

theorem coreAngleField_radius_projective {y : ProjectiveState} (hv : 0 < y 2) :
    coreAngleField (coreAngle (y 0) (y 2)) (toCoreAngleState y) 0 =
      (-coupling (y 1) (y 2) (y 3) - Real.tanh (coreAngle (y 0) (y 2)) * (y 1 - y 3) ^ 2 /
        coreRadius (y 0) (y 2)) / coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3) := by
  change (-coupling (y 1) (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2)))
    (y 2 * y 3 / (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2)))) -
      Real.tanh (coreAngle (y 0) (y 2)) *
        (y 1 - y 2 * y 3 / (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2)))) ^ 2 /
          coreRadius (y 0) (y 2)) /
      coreClockFactor (coreRadius (y 0) (y 2)) (y 1)
        (y 2 * y 3 / (coreRadius (y 0) (y 2) / Real.cosh (coreAngle (y 0) (y 2)))) = _
  rw [(coreAngle_coordinates hv).1, mul_div_cancel_left₀ _ (ne_of_gt hv)]

theorem coreRegion_exit_radius_velocity {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hV : y 2 = 1) (hM : y 0 < 1) :
    let f := coreAngleField (coreAngle (y 0) (y 2)) (toCoreAngleState y) 0
    f ≤ 0 ∧ |f| ≤ 2 * (y 1 + y 3 ^ 2 / coreRadius (y 0) (y 2)) := by
  intro f
  let r := coreRadius (y 0) (y 2)
  let z := coreAngle (y 0) (y 2)
  have hv : 0 < y 2 := by rw [hV]; norm_num
  have hr := coreRegion_radius_bounds hk hy
  obtain ⟨hu, hw⟩ := coreRegion_wall_bounds hy
  have hr0 : 0 < r := coreRadius_pos hv
  have hr1 : 1 ≤ r := by dsimp [r]; linarith only [hr.1, hk]
  have hd : 0 < coreClockFactor r (y 1) (y 3) := (coreRegion_clock_regular hk hy).2.1
  have hC := coreBootstrap_coupling_nonneg hk hy.2.1 hu hw.1
  have hz : 0 ≤ Real.tanh z := by
    rw [tanh_coreAngle hv]
    exact div_nonneg (sub_nonneg.mpr hM.le) hr0.le
  have hzabs : |Real.tanh z| ≤ 1 :=
    abs_le.mpr ⟨(Real.neg_one_lt_tanh z).le, (Real.tanh_lt_one z).le⟩
  have hid : f = (-coupling (y 1) (y 2) (y 3) - Real.tanh z * (y 1 - y 3) ^ 2 / r) /
      coreClockFactor r (y 1) (y 3) := coreAngleField_radius_projective hv
  constructor
  · rw [hid]
    exact div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (le_trans (neg_nonpos.mpr hC) (by positivity))) hd.le
  · have H := core_radial_velocity_bound hk hr.1 hy.2.1 hu hw hzabs
    change |(-coupling (y 1) (y 2) (y 3) - Real.tanh z * (y 1 - y 3) ^ 2 / r) /
      coreClockFactor r (y 1) (y 3)| ≤ _ at H
    rw [← hid] at H
    have hu' := coreBootstrap_wall_bound hk hu.2
    have hw' := coreBootstrap_wall_bound hk hw.2
    have huw : y 1 * y 3 ≤ y 1 / 60000 := by
      have H' := mul_le_mul_of_nonneg_left hw' hu.1
      linarith only [H']
    have huu : y 1 ^ 2 / r ≤ y 1 / 60000 := by
      have H' := mul_le_mul_of_nonneg_left hu' hu.1
      exact (div_le_self (sq_nonneg _) hr1).trans (by nlinarith only [H'])
    have hweak : 0 ≤ y 3 ^ 2 / r := div_nonneg (sq_nonneg _) hr0.le
    apply H.trans
    rw [show y 1 * y 2 = y 1 by rw [hV, mul_one]]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 999 / 1000)).mpr
    change y 1 + y 1 * y 3 + y 1 ^ 2 / r + y 3 ^ 2 / r ≤ _
    linarith only [huw, huu, hweak, hu.1]

theorem coreRegion_exit_factor_bounds {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hV : y 2 = 1) (hM : y 0 < 1) :
    0 < coreExitRadialFactor y ∧ coreExitRadialFactor y ≤ 1 ∧
      |coreExitRadialFactor y - 1| ≤ 8 * (y 1 / k + y 3 ^ 2 / k ^ 2) := by
  let r := coreRadius (y 0) (y 2)
  let c := -Real.tanh (coreAngle (y 0) (y 2))
  let f := coreAngleField (coreAngle (y 0) (y 2)) (toCoreAngleState y) 0
  have hv : 0 < y 2 := by rw [hV]; norm_num
  have hk0 : 0 < k := by linarith only [hk]
  have hr0 : 0 < r := coreRadius_pos hv
  have hr := coreRegion_radius_bounds hk hy
  have hgap := core_section_phase_gap hk (show 99 / 100 * k ≤ coreRadius (y 0) 1 by simpa only [hV] using hr.1)
  rw [abs_of_neg (sub_neg.mpr hM)] at hgap
  have hc : c ≤ -1 / 2 := by
    have hid : c = (y 0 - 1) / r := by dsimp [c]; rw [tanh_coreAngle hv]; dsimp [r]; ring
    rw [hid]
    apply (div_le_iff₀ hr0).mpr
    change y 0 - 1 ≤ (-1 / 2) * coreRadius (y 0) (y 2)
    linarith only [hgap, hr.2, hk]
  obtain ⟨hf, hfbound⟩ := coreRegion_exit_radius_velocity hk hy hV hM
  change f ≤ 0 at hf
  change |f| ≤ 2 * (y 1 + y 3 ^ 2 / r) at hfbound
  obtain ⟨_, hpos, hle, herr⟩ := radial_arrival_factor_bounds hr0 hc hf
  refine ⟨hpos, hle, herr.trans ?_⟩
  obtain ⟨_, _, _, _, _, hkr, hk2r2, _⟩ := coreBootstrap_coefficient_scales hk hr
  have hu0 := hy.2.2.1.1
  have huScale : y 1 / r ≤ (3 / 2) * (y 1 / k) := by
    calc
      _ = (k / r) * (y 1 / k) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hkr (div_nonneg hu0 hk0.le)
  have hwScale : y 3 ^ 2 / r ^ 2 ≤ (3 / 2) * (y 3 ^ 2 / k ^ 2) := by
    calc
      _ = (k ^ 2 / r ^ 2) * (y 3 ^ 2 / k ^ 2) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hk2r2 (by positivity)
  calc
    2 * |f| / r ≤ 2 * (2 * (y 1 + y 3 ^ 2 / r)) / r := by gcongr
    _ = 4 * (y 1 / r + y 3 ^ 2 / r ^ 2) := by field_simp; ring
    _ ≤ 8 * (y 1 / k + y 3 ^ 2 / k ^ 2) := by
      linarith only [huScale, hwScale, div_nonneg hu0 hk0.le,
        div_nonneg (sq_nonneg (y 3)) (sq_nonneg k)]

theorem exists_large_core_exit_factor {k u w : ℝ} (hk : 6 ≤ k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    let y : ProjectiveState := ![1 + Real.sqrt (k ^ 2 - 1), u, 1, w]
    ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} T ∧
      projectiveOriginalFlow y 0 T 0 < 1 ∧
      0 < coreExitRadialFactor (projectiveOriginalFlow y 0 T) ∧
      coreExitRadialFactor (projectiveOriginalFlow y 0 T) ≤ 1 ∧
      |coreExitRadialFactor (projectiveOriginalFlow y 0 T) - 1| ≤ 8 * (u / k + w ^ 2 / k ^ 2) := by
  intro y
  have hk0 : 0 < k := by linarith only [hk]
  obtain ⟨T, hT, hfirst, hcore, hM, _, _, _, hU, hW, _⟩ := exists_large_core_traversal hk hu hw
  have hy : coreRegion k (projectiveOriginalFlow y 0 T) := (hcore T ⟨hT.le, le_rfl⟩).2
  obtain ⟨hpos, hle, herr⟩ := coreRegion_exit_factor_bounds hk hy hfirst.1.2 hM
  have hUle : projectiveOriginalFlow y 0 T 1 ≤ u := hU.trans
    (mul_le_of_le_one_left hu.1 (Real.exp_le_one_iff.mpr (by linarith only [hk])))
  have hWle : projectiveOriginalFlow y 0 T 3 ≤ w := hW.trans
    (mul_le_of_le_one_left hw.1 (Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))))
  have hW0 := (coreRegion_wall_bounds hy).2.1
  refine ⟨T, hT, hfirst, hM, hpos, hle, herr.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (add_le_add (div_le_div_of_nonneg_right hUle hk0.le)
      (div_le_div_of_nonneg_right ((sq_le_sq₀ hW0 hw.1).mpr hWle) (sq_nonneg k))) (by norm_num)

end BianchiIX
