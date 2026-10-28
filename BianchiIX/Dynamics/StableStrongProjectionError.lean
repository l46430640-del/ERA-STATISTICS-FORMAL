import BianchiIX.Dynamics.StableProjectionRefinedDerivatives
import BianchiIX.Dynamics.StableSingleStrongWall
import BianchiIX.Analysis.CoordinateSegmentBounds

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def stableStrongBase : StableState →L[ℝ] StableState :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 1, 0]

theorem stableStrongBase_apply (y : StableState) : stableStrongBase y = ![y 0, y 1, 0] := by
  ext i; fin_cases i <;> rfl

theorem stableStrongBase_eq_update (y : StableState) : stableStrongBase y = Function.update y 2 0 := by
  ext i; fin_cases i <;> simp [stableStrongBase_apply]

def stableStrongProjectionError (y : StableState) : ℝ :=
  stableBoundaryProjection (y 0) (y 1) (y 2) - stableBoundaryProjection (y 0) (y 1) 0

theorem stableStrongProjectionError_eq {y : StableState} (hm : 2 ≤ y 0) (hu : |y 1| ≤ 1 / 200) :
    stableStrongProjectionError y = stableBoundaryProjection (y 0) (y 1) (y 2) -
      singleStrongUpperRoot (singleStrongInvariant (y 0) (y 1)) := by
  rw [stableStrongProjectionError, stableBoundaryProjection_strong hm (by simp) hu]

theorem stableStrongProjectionError_eventuallyEq_single {y : StableState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) :
    stableStrongProjectionError =ᶠ[𝓝 y] (fun z : StableState =>
      stableBoundaryProjection (z 0) (z 1) (z 2) -
        singleStrongUpperRoot (singleStrongInvariant (z 0) (z 1))) := by
  have HMc : ContinuousAt (fun z : StableState => |z 0 - y 0|) y :=
    (((continuous_apply 0).sub continuous_const).abs).continuousAt
  have HUc : ContinuousAt (fun z : StableState => |z 1|) y := (continuous_apply 1).abs.continuousAt
  have HM : ∀ᶠ z : StableState in 𝓝 y, |z 0 - y 0| < 1 / 40 :=
    HMc.eventually
      (isOpen_Iio.mem_nhds (by simp : |y 0 - y 0| < (1 / 40 : ℝ)))
  have HU : ∀ᶠ z : StableState in 𝓝 y, |z 1| < 1 / 200 :=
    HUc.eventually (isOpen_Iio.mem_nhds hu)
  filter_upwards [HM, HU] with z hz huZ
  rw [stableStrongProjectionError, stableBoundaryProjection_strong hm hz.le huZ.le]

theorem stableStrongProjectionError_differential {y : StableState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    ContDiffAt ℝ 2 stableStrongProjectionError y ∧
      ∀ d : StableState,
      fderiv ℝ stableStrongProjectionError y d =
        fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) y d -
        fderiv ℝ (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2))
          (stableStrongBase y) (stableStrongBase d) := by
  let P := fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)
  have HP : ContDiffAt ℝ 2 P y := contDiffAt_stableBoundaryProjection_two hm hu hw
  have HQ : ContDiffAt ℝ 2 P (stableStrongBase y) :=
    contDiffAt_stableBoundaryProjection_two hm hu (by change |(0 : ℝ)| < 1 / 200; norm_num)
  have HR := HP.sub (HQ.comp y stableStrongBase.contDiff.contDiffAt)
  have HD := (HP.differentiableAt (by norm_num)).hasFDerivAt.sub
    ((HQ.differentiableAt (by norm_num)).hasFDerivAt.comp y stableStrongBase.hasFDerivAt)
  change ContDiffAt ℝ 2 stableStrongProjectionError y at HR
  change HasFDerivAt stableStrongProjectionError _ y at HD
  refine ⟨HR, ?_⟩
  intro d
  rw [HD.fderiv]
  rfl

/-- Both the value and the two tangential derivatives retain the removed weak wall. -/
theorem exists_stableStrongProjectionError_bounds :
    ∃ C > (0 : ℝ), ∀ y : StableState, 2 ≤ y 0 → |y 1| < 1 / 200 → |y 2| < 1 / 200 →
      let b := |y 1| + |y 2|
      let L := y 0 + 1
      |stableStrongProjectionError y| ≤ C * |y 2| * b / L ∧
      |fderiv ℝ stableStrongProjectionError y (Pi.single 0 1)| ≤ C * |y 2| * b / L ^ 2 ∧
      |fderiv ℝ stableStrongProjectionError y (Pi.single 1 1)| ≤ C * |y 2| / L ∧
      |fderiv ℝ stableStrongProjectionError y (Pi.single 2 1)| ≤ C * b / L := by
  obtain ⟨C, hC, HC⟩ := exists_stableBoundaryProjection_refined_derivatives
  refine ⟨C, hC, ?_⟩
  intro y hm hu hw b L
  let P := fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)
  have hL : 0 < L := by dsimp only [L]; linarith only [hm]
  have hseg (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      |coordinateSegment 2 y s 1| < 1 / 200 ∧ |coordinateSegment 2 y s 2| < 1 / 200 ∧
      |coordinateSegment 2 y s 1| + |coordinateSegment 2 y s 2| ≤ b := by
    have H : |s * y 2| ≤ |y 2| := by
      rw [abs_mul, abs_of_nonneg hs.1]
      exact mul_le_of_le_one_left (abs_nonneg _) hs.2
    simpa [coordinateSegment, b] using And.intro hu (And.intro (H.trans_lt hw) (add_le_add_left H |y 1|))
  have Hreg (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : ContDiffAt ℝ 2 P (coordinateSegment 2 y s) :=
    contDiffAt_stableBoundaryProjection_two (by simpa [coordinateSegment] using hm) (hseg s hs).1 (hseg s hs).2.1
  have Hwall (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      |fderiv ℝ P (coordinateSegment 2 y s) (Pi.single 2 1)| ≤ C / L * b := by
    have H := (HC (coordinateSegment 2 y s) (by simpa [coordinateSegment] using hm)
      (hseg s hs).1 (hseg s hs).2.1).2.1 (Pi.single 2 1) (by simp)
    simp only [Pi.norm_single, norm_one, mul_one] at H
    change _ ≤ C / L * _ at H
    exact H.trans (mul_le_mul_of_nonneg_left (hseg s hs).2.2 (by positivity))
  have Hmixed (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      |fderiv ℝ (fderiv ℝ P) (coordinateSegment 2 y s) (Pi.single 2 1) (Pi.single 0 1)| ≤ C / L ^ 2 * b := by
    rw [((Hreg s hs).isSymmSndFDerivAt (by norm_num)).eq (Pi.single 2 1) (Pi.single 0 1)]
    have H := (HC (coordinateSegment 2 y s) (by simpa [coordinateSegment] using hm)
      (hseg s hs).1 (hseg s hs).2.1).2.2.2.1 (Pi.single 0 1) (Pi.single 2 1) (by simp) (by simp) (by simp)
    simp only [Pi.norm_single, norm_one, mul_one] at H
    change _ ≤ C / L ^ 2 * _ at H
    exact H.trans (mul_le_mul_of_nonneg_left (hseg s hs).2.2 (by positivity))
  have Hstable (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      |fderiv ℝ (fderiv ℝ P) (coordinateSegment 2 y s) (Pi.single 2 1) (Pi.single 1 1)| ≤ C / L := by
    have H := (HC (coordinateSegment 2 y s) (by simpa [coordinateSegment] using hm)
      (hseg s hs).1 (hseg s hs).2.1).2.2.2.2 (Pi.single 2 1) (Pi.single 1 1) (by simp) (by simp)
    simpa [Pi.norm_single, coordinateSegment, L] using H
  have Hval := coordinate_difference_bound (fun s hs => (Hreg s hs).differentiableAt (by norm_num)) Hwall
  have Hrad := coordinate_fderiv_difference_bound
    (fun s hs => ((Hreg s hs).fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)) Hmixed
  have Hstrong := coordinate_fderiv_difference_bound
    (fun s hs => ((Hreg s hs).fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)) Hstable
  have HD := (stableStrongProjectionError_differential hm hu hw).2
  have Hb0 : stableStrongBase (Pi.single 0 1) = Pi.single 0 1 := by ext i; fin_cases i <;> simp [stableStrongBase_apply]
  have Hb1 : stableStrongBase (Pi.single 1 1) = Pi.single 1 1 := by ext i; fin_cases i <;> simp [stableStrongBase_apply]
  have Hb2 : stableStrongBase (Pi.single 2 1) = 0 := by ext i; fin_cases i <;> simp [stableStrongBase_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change |stableStrongProjectionError y| ≤ _ at Hval
    convert Hval using 1; ring
  · rw [HD, Hb0, stableStrongBase_eq_update]
    convert Hrad using 1; ring
  · rw [HD, Hb1, stableStrongBase_eq_update]
    convert Hstrong using 1; ring
  · rw [HD, Hb2, map_zero, sub_zero]
    have H := Hwall 1 (by norm_num)
    simp only [coordinateSegment, one_mul, Function.update_eq_self] at H
    convert H using 1; ring

theorem exists_stableStrongProjectionError_scaled_bounds :
    ∃ C > (0 : ℝ), ∀ (α : ℝ) (y : StableState), 0 < α → 1 / α ≤ y 0 + 1 →
      2 ≤ y 0 → |y 1| < 1 / 200 → |y 2| < 1 / 200 →
      let b := |y 1| + |y 2|
      |stableStrongProjectionError y| ≤ C * α * |y 2| * b ∧
      |fderiv ℝ stableStrongProjectionError y (Pi.single 0 1)| ≤ C * α ^ 2 * |y 2| * b ∧
      |fderiv ℝ stableStrongProjectionError y (Pi.single 1 1)| ≤ C * α * |y 2| ∧
      |fderiv ℝ stableStrongProjectionError y (Pi.single 2 1)| ≤ C * α * b := by
  obtain ⟨C, hC, HC⟩ := exists_stableStrongProjectionError_bounds
  refine ⟨C, hC, ?_⟩
  intro α y hα hscale hm hu hw b
  have hL : 0 < y 0 + 1 := by linarith only [hm]
  have Hinv : 1 / (y 0 + 1) ≤ α := (div_le_iff₀ hL).mpr
    (by have H := (div_le_iff₀ hα).mp hscale; nlinarith only [H])
  have Hinv2 : 1 / (y 0 + 1) ^ 2 ≤ α ^ 2 := by
    have H := pow_le_pow_left₀ (by positivity : 0 ≤ 1 / (y 0 + 1)) Hinv 2
    simpa only [div_pow, one_pow] using H
  have Hlinear (a : ℝ) (ha : 0 ≤ a) : a / (y 0 + 1) ≤ a * α := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left Hinv ha
  have Hsquare (a : ℝ) (ha : 0 ≤ a) : a / (y 0 + 1) ^ 2 ≤ a * α ^ 2 := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left Hinv2 ha
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  obtain ⟨H0, HM, HU, HW⟩ := HC y hm hu hw
  refine ⟨H0.trans ?_, HM.trans ?_, HU.trans ?_, HW.trans ?_⟩
  · exact (Hlinear _ (by positivity)).trans_eq (by ring)
  · exact (Hsquare _ (by positivity)).trans_eq (by ring)
  · exact (Hlinear _ (by positivity)).trans_eq (by ring)
  · exact (Hlinear _ (by positivity)).trans_eq (by ring)

end BianchiIX
