import BianchiIX.Dynamics.CoreEntryDifferential

noncomputable section

namespace BianchiIX

open Set

theorem coreRadiusEntry_gap {k : ℝ} (hk : 6 ≤ k) : k / 2 ≤ Real.sqrt (k ^ 2 - 1) := by
  have hs := Real.sq_sqrt (by nlinarith only [hk] : 0 ≤ k ^ 2 - 1)
  have hnonneg := Real.sqrt_nonneg (k ^ 2 - 1)
  by_contra! hlt
  have H := (sq_lt_sq₀ hnonneg (by linarith only [hk] : 0 ≤ k / 2)).mpr hlt
  nlinarith only [hs, H, hk, sq_nonneg (k - 6)]

theorem coreRadiusEntry_field_bounds {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    let f := coreAngleField (projectiveCoreAngle (coreRadiusEntry Y)) Y
    |f 0| ≤ 2 * (Y 1 + Y 2 ^ 2 / Y 0) ∧
      |f 1| ≤ 2 * Y 0 * Y 1 ∧ |f 2| ≤ 4 * Y 2 / Y 0 := by
  intro f
  let k := Y 0
  let u := Y 1
  let w := Y 2
  let z := projectiveCoreAngle (coreRadiusEntry Y)
  let q := coreAuxiliary z Y
  have hk0 : 0 < k := by dsimp [k]; linarith only [hk]
  have hk1 : 1 < Y 0 := by linarith only [hk]
  have hr : 99 / 100 * k ≤ Y 0 ∧ Y 0 ≤ 101 / 100 * k := by dsimp [k]; constructor <;> linarith only [hk]
  have hv : 0 < coreRadiusEntry Y 2 := by change (0 : ℝ) < 1; norm_num
  have hV : Y 0 / Real.cosh z = 1 := by
    have H := (coreAngle_coordinates (m := coreRadiusEntry Y 0) hv).1
    rw [coreRadius_coreRadiusEntry hk1] at H
    exact H
  obtain ⟨hC, ha, _, hd, _⟩ := coreAuxiliary_coefficient_bounds hk hr
    (by rw [hV]) hu (by simpa only [hV, div_one] using hw)
  change 0 ≤ q 0 ∧ q 0 ≤ 1 / 100 at hC
  change |q 2| ≤ k at ha
  change 999 / 1000 ≤ q 1 at hd
  have hd0 : 0 < q 1 := by linarith only [hd]
  have hu' := coreBootstrap_wall_bound hk hu.2
  have hw' := coreBootstrap_wall_bound hk hw.2
  have huw : u * w ≤ u / 4 := by
    have H := mul_le_mul_of_nonneg_left hw' hu.1
    change u * w ≤ u * (1 / 60000) at H
    nlinarith only [H, hu.1]
  have huu : u ^ 2 / k ≤ u / 4 := by
    have H := mul_le_mul_of_nonneg_left hu' hu.1
    exact (div_le_self (sq_nonneg u) (by dsimp [k]; linarith only [hk])).trans
      (by change u * u ≤ u * (1 / 60000) at H; nlinarith only [H, hu.1])
  have hf0 : f 0 = (-coupling u 1 w - Real.tanh z * (u - w) ^ 2 / k) / coreClockFactor k u w := by
    have H := coreAngleField_radius_projective hv
    rw [toCoreAngleState_coreRadiusEntry hk1, coreRadius_coreRadiusEntry hk1] at H
    exact H
  refine ⟨?_, ?_, ?_⟩
  · rw [hf0]
    have H := core_radial_velocity_bound hk hr.1 (v := 1) le_rfl hu hw (Real.abs_tanh_lt_one z).le
    apply H.trans
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 999 / 1000)).mpr
    change u * 1 + u * w + u ^ 2 / k + w ^ 2 / k ≤ _
    nlinarith only [huw, huu, hu.1, div_nonneg (sq_nonneg w) hk0.le]
  · change |u * q 2 / q 1| ≤ 2 * k * u
    rw [abs_div, abs_mul, abs_of_nonneg hu.1, abs_of_pos hd0]
    calc
      u * |q 2| / q 1 ≤ u * k / q 1 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left ha hu.1) hd0.le
      _ ≤ 2 * k * u := (div_le_iff₀ hd0).mpr (by
        nlinarith only [mul_le_mul_of_nonneg_left hd (mul_nonneg hk0.le hu.1), mul_nonneg hk0.le hu.1])
  · change |(-2 * w * (1 + q 0)) / (k * q 1)| ≤ 4 * w / k
    have hC0 : 0 ≤ 1 + q 0 := by linarith only [hC.1]
    have hratio : 2 * (1 + q 0) / q 1 ≤ 4 :=
      (div_le_iff₀ hd0).mpr (by linarith only [hC.2, hd])
    calc
      _ = (2 * (1 + q 0) / q 1) * (w / k) := by
        rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hw.1, abs_of_nonneg hC0,
          abs_mul, abs_of_pos hk0, abs_of_pos hd0]
        norm_num
        ring
      _ ≤ 4 * (w / k) := mul_le_mul_of_nonneg_right hratio (div_nonneg hw.1 hk0.le)
      _ = _ := by ring

/-- All three moving-entry errors retain their actual wall amplitudes. -/
theorem coreRadiusEntry_variation_bounds {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) (v : CoreAngleState) :
    let xi := coreClockProjection (coreRadiusEntry Y) (fderiv ℝ coreRadiusEntry Y v)
    |xi 0 - v 0| ≤ 4 * (Y 1 / Y 0 + Y 2 ^ 2 / Y 0 ^ 2) * |v 0| ∧
      |Y 0 * xi 1| ≤ Y 0 * |v 1| + 4 * Y 0 * Y 1 * |v 0| ∧
      |xi 2 - v 2| ≤ 8 * Y 2 / Y 0 ^ 2 * |v 0| := by
  intro xi
  let k := Y 0
  let f := coreAngleField (projectiveCoreAngle (coreRadiusEntry Y)) Y
  have hk0 : 0 < k := by dsimp [k]; linarith only [hk]
  have hgap := coreRadiusEntry_gap hk
  have hs : 0 < Real.sqrt (k ^ 2 - 1) := lt_of_lt_of_le (by positivity : 0 < k / 2) hgap
  have hratio : |v 0 / Real.sqrt (k ^ 2 - 1)| ≤ 2 * |v 0| / k := by
    rw [abs_div, abs_of_pos hs]
    exact (div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hgap).trans_eq (by ring)
  have hproj := coreRadiusEntry_projection (by linarith only [hk] : 1 < Y 0) v
  have hid (i : Fin 3) : xi i - v i = (v 0 / Real.sqrt (k ^ 2 - 1)) * f i := by
    change coreClockProjection (coreRadiusEntry Y) (fderiv ℝ coreRadiusEntry Y v) i - v i = _
    rw [hproj]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
    rfl
  obtain ⟨hR, hU, hP⟩ := coreRadiusEntry_field_bounds hk hu hw
  change |f 0| ≤ 2 * (Y 1 + Y 2 ^ 2 / k) at hR
  change |f 1| ≤ 2 * k * Y 1 at hU
  change |f 2| ≤ 4 * Y 2 / k at hP
  have hbound (i : Fin 3) : |xi i - v i| ≤ (2 * |v 0| / k) * |f i| := by
    rw [hid i, abs_mul]
    exact mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ (2 * |v 0| / k) * |f 0| := hbound 0
      _ ≤ (2 * |v 0| / k) * (2 * (Y 1 + Y 2 ^ 2 / k)) := by gcongr
      _ = _ := by dsimp [k]; field_simp; ring
  · have H : |xi 1| ≤ |v 1| + (2 * |v 0| / k) * (2 * k * Y 1) := by
      calc
        _ ≤ |v 1| + |xi 1 - v 1| := by
          convert! abs_add_le (v 1) (xi 1 - v 1) using 1
          congr 1
          ring
        _ ≤ _ := add_le_add (le_refl _) ((hbound 1).trans (mul_le_mul_of_nonneg_left hU (by positivity)))
    rw [abs_mul, abs_of_pos hk0]
    have H' := mul_le_mul_of_nonneg_left H hk0.le
    convert! H' using 1
    dsimp [k]
    field_simp
    ring
  · calc
      _ ≤ (2 * |v 0| / k) * |f 2| := hbound 2
      _ ≤ (2 * |v 0| / k) * (4 * Y 2 / k) := by gcongr
      _ = _ := by dsimp [k]; field_simp; ring

theorem coreRadiusEntry_variation_norm {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) (v : CoreAngleState) :
    ‖scaleCoreVariation (Y 0)
      (coreClockProjection (coreRadiusEntry Y) (fderiv ℝ coreRadiusEntry Y v))‖ ≤
        2 * (|v 0| + Y 0 * |v 1| + |v 2|) := by
  let k := Y 0
  let xi := coreClockProjection (coreRadiusEntry Y) (fderiv ℝ coreRadiusEntry Y v)
  have hk0 : 0 < k := by dsimp [k]; linarith only [hk]
  have hu1 : Y 1 ≤ 1 := (coreBootstrap_wall_bound hk hu.2).trans (by norm_num)
  have hw1 : Y 2 ≤ 1 := (coreBootstrap_wall_bound hk hw.2).trans (by norm_num)
  have hw2 : Y 2 ^ 2 ≤ 1 := by nlinarith only [hw.1, hw1]
  have hku : k * Y 1 ≤ 1 / 10000 := by
    have H := (le_div_iff₀ hk0).mp hu.2
    linarith only [H]
  have huk : Y 1 / k ≤ 1 / 6 := (div_le_iff₀ hk0).mpr (by dsimp [k]; linarith only [hu1, hk])
  have hwk : Y 2 ^ 2 / k ^ 2 ≤ 1 / 36 := (div_le_iff₀ (sq_pos_of_pos hk0)).mpr (by
    dsimp [k]
    nlinarith only [hw2, hk, sq_nonneg (Y 0 - 6)])
  have hsmallR : 4 * (Y 1 / k + Y 2 ^ 2 / k ^ 2) ≤ 1 := by linarith only [huk, hwk]
  have hsmallU : 4 * k * Y 1 ≤ 1 := by linarith only [hku]
  have hsmallP : 8 * Y 2 / k ^ 2 ≤ 1 := (div_le_iff₀ (sq_pos_of_pos hk0)).mpr (by
    dsimp [k]
    nlinarith only [hw1, hk, sq_nonneg (Y 0 - 6)])
  obtain ⟨hR, hU, hP⟩ := coreRadiusEntry_variation_bounds hk hu hw v
  change |xi 0 - v 0| ≤ 4 * (Y 1 / k + Y 2 ^ 2 / k ^ 2) * |v 0| at hR
  change |k * xi 1| ≤ k * |v 1| + 4 * k * Y 1 * |v 0| at hU
  change |xi 2 - v 2| ≤ 8 * Y 2 / k ^ 2 * |v 0| at hP
  have hR' : |xi 0 - v 0| ≤ |v 0| := hR.trans (mul_le_of_le_one_left (abs_nonneg _) hsmallR)
  have hU' : |k * xi 1| ≤ k * |v 1| + |v 0| :=
    hU.trans (add_le_add (le_refl _) (mul_le_of_le_one_left (abs_nonneg _) hsmallU))
  have hP' : |xi 2 - v 2| ≤ |v 0| := hP.trans (mul_le_of_le_one_left (abs_nonneg _) hsmallP)
  have htri (i : Fin 3) : |xi i| ≤ |xi i - v i| + |v i| := by
    simpa only [sub_add_cancel] using abs_add_le (xi i - v i) (v i)
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro i
  fin_cases i
  · change |xi 0| ≤ _
    nlinarith only [htri 0, hR', abs_nonneg (v 0), abs_nonneg (v 2), mul_nonneg hk0.le (abs_nonneg (v 1))]
  · change |k * xi 1| ≤ _
    nlinarith only [hU', abs_nonneg (v 0), abs_nonneg (v 2), mul_nonneg hk0.le (abs_nonneg (v 1))]
  · change |xi 2| ≤ _
    nlinarith only [htri 2, hP', abs_nonneg (v 0), abs_nonneg (v 2), mul_nonneg hk0.le (abs_nonneg (v 1))]

/-- The initial directional size controls the projected variation throughout the core. -/
theorem exists_large_core_entry_variation {Y : CoreAngleState} (hk : 6 ≤ Y 0)
    (hu : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0) :
    ∃ T > 0,
      IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2 = 1} T ∧
      (∀ t ∈ Icc 0 T, coreRegion (Y 0) (projectiveOriginalFlow (coreRadiusEntry Y) 0 t)) ∧
      ∀ t ∈ Icc 0 T, ∀ v : CoreAngleState,
        ‖scaleCoreVariation (Y 0) (coreProjectedFlowVariation (coreRadiusEntry Y) 0 t
          (fderiv ℝ coreRadiusEntry Y v))‖ ≤
          (2 * coreVariationBound) * (|v 0| + Y 0 * |v 1| + |v 2|) := by
  obtain ⟨T, hT, hfirst, hcore, hvar⟩ := exists_large_core_projected_growth hk hu hw
  refine ⟨T, hT, hfirst, fun t ht => (hcore t ht).2, ?_⟩
  intro t ht v
  have H := hvar t ht (fderiv ℝ coreRadiusEntry Y v)
  apply H.trans
  have hK : 0 ≤ coreVariationBound := (Real.exp_pos _).le
  have H' := mul_le_mul_of_nonneg_right (coreRadiusEntry_variation_norm hk hu hw v) hK
  convert! H' using 1
  ring

end BianchiIX
