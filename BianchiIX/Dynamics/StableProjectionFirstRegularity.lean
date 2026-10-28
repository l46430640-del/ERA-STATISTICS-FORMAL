import BianchiIX.Dynamics.StableBoundaryDifferentialLimit
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def stableParameterDomain (c : ℝ) : Set StableState :=
  {y | |y 0 - c| < 1 / 40 ∧ |y 1| < 1 / 200 ∧ |y 2| < 1 / 200}

def stableCenterApproximation (c s : ℝ) (y : StableState) : ℝ := stableRescaledFlow (c + 1) y s 0

theorem isOpen_stableParameterDomain (c : ℝ) : IsOpen (stableParameterDomain c) :=
  (isOpen_lt ((continuous_apply 0).sub continuous_const).abs continuous_const).inter
    ((isOpen_lt (continuous_apply 1).abs continuous_const).inter
      (isOpen_lt (continuous_apply 2).abs continuous_const))

theorem hasFDerivAt_stableCenterApproximation {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    HasFDerivAt (stableCenterApproximation c s) (stableCenterDifferential c y s) y :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).hasFDerivAt.comp y
    (hasFDerivAt_stableRescaledFlow (by linarith : 0 < c + 1) hc hm hu hw hs)

theorem contDiffAt_stableCenterApproximation_two {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    ContDiffAt ℝ 2 (stableCenterApproximation c s) y := by
  have H := contDiffAt_stableRescaledFlow_two (by linarith : 0 < c + 1) hc hm hu hw hs
  have hmap : ContDiffAt ℝ 2 (fun z : StableState => (z, s)) y := contDiffAt_id.prodMk contDiffAt_const
  have H' := H.comp y hmap
  exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).contDiff.contDiffAt.comp y H'

theorem continuousOn_stableCenterDifferential {c s : ℝ} (hc : 2 ≤ c) (hs : 0 ≤ s) :
    ContinuousOn (fun y => stableCenterDifferential c y s) (stableParameterDomain c) := by
  intro y hy
  have H := ((contDiffAt_stableCenterApproximation_two hc hy.1.le hy.2.1.le hy.2.2.le hs).fderiv_right
    (m := 1) (by norm_num)).continuousAt
  have heq : (fun z => stableCenterDifferential c z s) =ᶠ[𝓝 y] fderiv ℝ (stableCenterApproximation c s) := by
    filter_upwards [(isOpen_stableParameterDomain c).mem_nhds hy] with z hz
    exact (hasFDerivAt_stableCenterApproximation hc hz.1.le hz.2.1.le hz.2.2.le hs).fderiv.symm
  exact (H.congr_of_eventuallyEq heq).continuousWithinAt

theorem stableCenterTailCoefficient_uniform {y : StableState}
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) :
    stableCenterTailCoefficient y ≤ 2 + 4 * Real.exp 6 := by
  have hb : |y 1| + |y 2| ≤ 1 / 100 := by linarith
  have hb2 : (|y 1| + |y 2|) ^ 2 ≤ (1 / 100 : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by norm_num)).mpr hb
  have he : Real.exp (512 * (|y 1| + |y 2|)) ≤ Real.exp 6 :=
    Real.exp_le_exp.mpr (by linarith)
  have H := mul_le_mul hb2 he (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ (1 / 100) ^ 2)
  unfold stableCenterTailCoefficient
  nlinarith [Real.exp_pos 6]

theorem stableCenterDifferential_uniform {c : ℝ} (hc : 2 ≤ c) :
    TendstoUniformlyOn (fun n : ℕ => fun y => stableCenterDifferential c y n)
      (stableCenterDifferentialLimit c) atTop (stableParameterDomain c) := by
  have hdec : Tendsto (fun n : ℕ => 2 * (2 + 4 * Real.exp 6) * Real.exp (-(n : ℝ) / 2)) atTop (𝓝 0) := by
    have H := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2) tendsto_natCast_atTop_atTop)).const_mul
        (2 * (2 + 4 * Real.exp 6))
    convert! H using 1
    · ext n
      simp only [Function.comp_def]
      congr 2
      ring
    · simp
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hdec.eventually (gt_mem_nhds hε)] with n hn
  intro y hy
  rw [dist_eq_norm]
  have H := stableCenterDifferentialLimit_tail hc hy.1.le hy.2.1.le hy.2.2.le (Nat.cast_nonneg n)
  have H' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (stableCenterTailCoefficient_uniform hy.2.1.le hy.2.2.le)
      (by norm_num : (0 : ℝ) ≤ 2)) (Real.exp_pos (-(n : ℝ) / 2)).le
  exact H.trans_lt (H'.trans_lt hn)

theorem continuousOn_stableCenterDifferentialLimit {c : ℝ} (hc : 2 ≤ c) :
    ContinuousOn (stableCenterDifferentialLimit c) (stableParameterDomain c) :=
  (stableCenterDifferential_uniform hc).continuousOn
    (Eventually.of_forall (fun n : ℕ => continuousOn_stableCenterDifferential hc (Nat.cast_nonneg n))).frequently

theorem hasFDerivAt_stableBoundaryProjection_in_band {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    HasFDerivAt (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2))
      (stableCenterDifferentialLimit c y) y := by
  have hpoint (z : StableState) (hz : z ∈ stableParameterDomain c) :
      Tendsto (fun n : ℕ => stableCenterApproximation c n z) atTop
        (𝓝 (stableBoundaryProjection (z 0) (z 1) (z 2))) := by
    have H := (tendsto_pi_nhds.mp (stableRescaledFlow_limit (by linarith : 0 < c + 1)
      hc hz.1.le hz.2.1.le hz.2.2.le) 0).comp tendsto_natCast_atTop_atTop
    exact H
  exact hasFDerivAt_of_tendstoUniformlyOn (isOpen_stableParameterDomain c)
    (stableCenterDifferential_uniform hc)
    (fun n z hz => hasFDerivAt_stableCenterApproximation hc hz.1.le hz.2.1.le hz.2.2.le (Nat.cast_nonneg n))
    hpoint ⟨hm, hu, hw⟩

theorem contDiffAt_stableBoundaryProjection_one {y : StableState}
    (hm : 2 ≤ y 0) (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    ContDiffAt ℝ 1 (fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)) y := by
  apply contDiffAt_one_iff.mpr
  refine ⟨stableCenterDifferentialLimit (y 0), stableParameterDomain (y 0),
    (isOpen_stableParameterDomain (y 0)).mem_nhds ⟨by simp, hu, hw⟩,
    continuousOn_stableCenterDifferentialLimit hm, ?_⟩
  intro z hz
  exact hasFDerivAt_stableBoundaryProjection_in_band hm hz.1 hz.2.1 hz.2.2

theorem stableCenterDifferentialLimit_independent {y : StableState} {c d : ℝ}
    (hc : 2 ≤ c) (hd : 2 ≤ d) (hmc : |y 0 - c| < 1 / 40) (hmd : |y 0 - d| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    stableCenterDifferentialLimit c y = stableCenterDifferentialLimit d y :=
  (hasFDerivAt_stableBoundaryProjection_in_band hc hmc hu hw).unique
    (hasFDerivAt_stableBoundaryProjection_in_band hd hmd hu hw)

end BianchiIX
