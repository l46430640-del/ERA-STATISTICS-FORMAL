import BianchiIX.Dynamics.EntranceWeakQuadraticReturn
import BianchiIX.Dynamics.ProjectiveFlowSecondRegularity
import BianchiIX.Analysis.CompactIntegralSecondRegularity

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem contDiffAt_entranceWeak_weights_two {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 3| < 1 / 200) (hv : 0 < y 2) :
    ContDiffAt ℝ 2 entranceWeakDriftWeight y ∧ ContDiffAt ℝ 2 entranceWeakCorrectionWeight y := by
  have hr := contDiffAt_entranceStableRadius_two hm hu hw hv
  have hR : ContDiffAt ℝ 2 (fun z : ProjectiveState => coreRadius (z 0) (z 2)) y := by
    unfold coreRadius coreEnergy
    apply ContDiffAt.sqrt (by fun_prop)
    positivity
  have hm0 : 0 < y 0 + 1 := by linarith
  have hS : ContDiffAt ℝ 2 (fun z : ProjectiveState => stableWeakRadius (z 0) (z 3)) y := by
    unfold stableWeakRadius phaseNorm
    apply ContDiffAt.sqrt (by fun_prop)
    positivity
  have hs := stableWeakRadius_pos (w := y 3) (show -1 < y 0 by linarith)
  have hs' : stableWeakRadius (y 0) (y 3) + y 0 + 1 ≠ 0 := by linarith
  have hr' := (entranceStableRadius_pos hv).ne'
  have hsum := (add_pos (entranceStableRadius_pos hv) (coreRadius_pos (m := y 0) hv)).ne'
  exact ⟨contDiffAt_const.div ((hr.mul hS).mul ((hS.add (by fun_prop)).add contDiffAt_const))
      (mul_ne_zero (mul_ne_zero hr' hs.ne') hs'),
    (((hS.add (by fun_prop)).sub contDiffAt_const).div
      ((hr.add hR).mul ((hS.add (by fun_prop)).add contDiffAt_const)) (mul_ne_zero hsum hs'))⟩

theorem contDiffAt_projectiveRate_parameter_two {y : ProjectiveState} {t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) 0) :
    ContDiffAt ℝ 2 (fun p : ProjectiveState × ℝ => normalizedProjectiveRate (fromProjectiveState p.1) 0 p.2) (y, t) := by
  have hp : ContDiffAt ℝ 2 (fun p : ProjectiveState × ℝ => (fromProjectiveState p.1, p.2)) (y, t) :=
    ((contDiffAt_fromProjectiveState 2 hD.ne').comp (y, t) contDiffAt_fst).prodMk contDiffAt_snd
  have hN := (contDiffAt_normalizedMaxCurve_two ht).comp (y, t) hp
  exact contDiffAt_const.add (contDiffAt_pi.mp hN 0)

theorem contDiffAt_projectiveIntegralClock_two {y : ProjectiveState} {t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : 0 ≤ t)
    (hdom : Icc 0 t ⊆ normalizedMaxDomain (fromProjectiveState y) 0) :
    ContDiffAt ℝ 2 (fun p : ProjectiveState × ℝ =>
      ∫ s in 0..p.2, normalizedProjectiveRate (fromProjectiveState p.1) 0 s) (y, t) := by
  apply contDiffAt_moving_intervalIntegral_two
    (F := fun p : (ProjectiveState × ℝ) × ℝ => normalizedProjectiveRate (fromProjectiveState p.1.1) 0 p.2)
    (x := (y, t)) contDiffAt_snd ht
  intro s hs
  have hp : ContDiffAt ℝ 2 (fun p : (ProjectiveState × ℝ) × ℝ => (p.1.1, p.2)) ((y, t), s) := by fun_prop
  exact (contDiffAt_projectiveRate_parameter_two hD (hdom hs)).comp ((y, t), s)
    (g := fun p : ProjectiveState × ℝ => normalizedProjectiveRate (fromProjectiveState p.1) 0 p.2)
    (f := fun p : (ProjectiveState × ℝ) × ℝ => (p.1.1, p.2)) hp

theorem contDiffAt_entranceWeakQuadraticLoss_two_of_segment {y : ProjectiveState}
    (hD : 0 < projectiveStateDenom y) (H : entranceReturnValid y)
    (hT : ContDiffAt ℝ 2 entranceReturnTime y) (hP : ContDiffAt ℝ 2 entranceReturnState y)
    (hM : ∀ t ∈ Icc 0 (entranceReturnTime y), 2 ≤ projectiveOriginalFlow y 0 t 0)
    (hU : ∀ t ∈ Icc 0 (entranceReturnTime y), |projectiveOriginalFlow y 0 t 1| < 1 / 200)
    (hW : ∀ t ∈ Icc 0 (entranceReturnTime y), |projectiveOriginalFlow y 0 t 3| < 1 / 200)
    (hV : ∀ t ∈ Icc 0 (entranceReturnTime y), 0 < projectiveOriginalFlow y 0 t 2) :
    ContDiffAt ℝ 2 entranceWeakQuadraticLoss y := by
  let T := entranceReturnTime y
  let F := fun p : ProjectiveState × ℝ =>
    normalizedProjectiveRate (fromProjectiveState p.1) 0 p.2 * (p.1 2) ^ 2 *
      Real.exp (-4 * ∫ s in 0..p.2, normalizedProjectiveRate (fromProjectiveState p.1) 0 s) *
      entranceWeakDriftWeight (projectiveOriginalFlow p.1 0 p.2)
  have htime (t : ℝ) (ht : t ∈ Icc 0 T) := contDiffAt_projectiveIntegralClock_two hD ht.1
    (fun s hs => (H.2.1 s ⟨hs.1, hs.2.trans ht.2⟩).1)
  have hF (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiffAt ℝ 2 F (y, t) := by
    have hY := contDiffAt_projectiveOriginalFlow_two hD (H.2.1 t ht).1 (H.2.1 t ht).2
    have hg := (contDiffAt_entranceWeak_weights_two (hM t ht) (hU t ht) (hW t ht) (hV t ht)).1.comp (y, t) hY
    have he : ContDiffAt ℝ 2 (fun p : ProjectiveState × ℝ =>
        Real.exp (-4 * ∫ s in 0..p.2, normalizedProjectiveRate (fromProjectiveState p.1) 0 s)) (y, t) :=
      (contDiffAt_const.mul (htime t ht)).exp
    exact (((contDiffAt_projectiveRate_parameter_two hD (H.2.1 t ht).1).mul (by fun_prop)).mul he).mul hg
  have hInt := contDiffAt_moving_intervalIntegral_two hT H.1.1.1.le hF
  have hlast : T ∈ Icc 0 T := ⟨H.1.1.1.le, le_rfl⟩
  have hclock := (htime T hlast).comp y (contDiffAt_id.prodMk hT)
  have hend : projectiveOriginalFlow y 0 T = entranceReturnState y := rfl
  have hcorr := (contDiffAt_entranceWeak_weights_two (hM T hlast) (hU T hlast) (hW T hlast) (hV T hlast)).2
  rw [hend] at hcorr
  have hterm : ContDiffAt ℝ 2 (fun z : ProjectiveState => (z 2) ^ 2 *
      Real.exp (-4 * ∫ s in 0..entranceReturnTime z, normalizedProjectiveRate (fromProjectiveState z) 0 s) *
      entranceWeakCorrectionWeight (entranceReturnState z)) y :=
    ((by fun_prop : ContDiffAt ℝ 2 (fun z : ProjectiveState => (z 2) ^ 2) y).mul
      (contDiffAt_const.mul hclock).exp).mul (hcorr.comp y hP)
  exact hInt.add hterm

theorem contDiffAt_entranceWeakQuadraticLoss_two {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) : ContDiffAt ℝ 2 entranceWeakQuadraticLoss y := by
  have H := entranceReturn_regular hk hm hu hv hw
  have hD := entrance_initial_denom_pos hk hm hu hv hw
  have hy := entranceReturn_region hk hm hu hv hw
  apply contDiffAt_entranceWeakQuadraticLoss_two_of_segment hD H.1 H.2.1 H.2.2.1
  · intro t ht
    linarith [(entranceRegion_phase hk (hy t ht)).1]
  · intro t ht
    rw [abs_of_nonneg (hy t ht).2.2.1.1]
    linarith [(hy t ht).2.2.1.2]
  · intro t ht
    rw [abs_of_nonneg (hy t ht).2.2.2.2.1]
    linarith [(hy t ht).2.2.2.2.2]
  · intro t ht
    have HF := normalizedProjectiveWallMultiplier_formula (H.1.2.1 t ht).1
      (fromProjectiveState_clock_pos hD) (H.1.2.1 t ht).2 1
    rw [toProjectiveState_fromProjectiveState hD.ne'] at HF
    change projectiveOriginalFlow y 0 t 2 = y 2 * normalizedProjectiveWallMultiplier (fromProjectiveState y) t 1 at HF
    rw [HF]
    exact mul_pos hv.1 (normalizedProjectiveWallMultiplier_pos _ _ _)

end BianchiIX
