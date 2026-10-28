import BianchiIX.Dynamics.StableCenterSecondDifferential

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem stableSecondCenterBudget_uniform {y : StableState}
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) :
    stableSecondCenterBudget y ≤ 80000 * (Real.exp 6) ^ 3 + 10000 * (Real.exp 6) ^ 2 := by
  have hb : 192 * (|y 1| + |y 2|) ≤ 2 := by linarith
  have he : Real.exp (512 * (|y 1| + |y 2|)) ≤ Real.exp 6 :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 := pow_le_pow_left₀ (Real.exp_pos _).le he 2
  have h3 := pow_le_pow_left₀ (Real.exp_pos _).le he 3
  have H := mul_le_mul hb
    (mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 40000))
    (by positivity) (by norm_num : (0 : ℝ) ≤ 2)
  unfold stableSecondCenterBudget
  nlinarith only [H, h2]

theorem stableCenterSecondDifferential_uniform {c : ℝ} (hc : 2 ≤ c) :
    TendstoUniformlyOn (fun n : ℕ => fun y => stableCenterSecondDifferential c y n)
      (stableCenterSecondDifferentialLimit c) atTop (stableParameterDomain c) := by
  let B := 80000 * (Real.exp 6) ^ 3 + 10000 * (Real.exp 6) ^ 2
  have hdec : Tendsto (fun n : ℕ => 4 * B * Real.exp (-(n : ℝ) / 4)) atTop (𝓝 0) := by
    have H := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 4) tendsto_natCast_atTop_atTop)).const_mul (4 * B)
    convert! H using 1
    · ext n
      simp only [Function.comp_def]
      congr 2
      ring
    · simp
  apply (Metric.tendstoUniformlyOn_iff
    (F := fun n : ℕ => fun y => stableCenterSecondDifferential c y n)
    (f := stableCenterSecondDifferentialLimit c)).mpr
  intro ε hε
  filter_upwards [hdec.eventually (gt_mem_nhds hε)] with n hn
  intro y hy
  rw [dist_eq_norm (stableCenterSecondDifferentialLimit c y) (stableCenterSecondDifferential c y n)]
  have H := stableCenterSecondDifferentialLimit_tail hc hy.1 hy.2.1 hy.2.2 (Nat.cast_nonneg n)
  have H' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (stableSecondCenterBudget_uniform hy.2.1.le hy.2.2.le)
      (by norm_num : (0 : ℝ) ≤ 4)) (Real.exp_pos (-(n : ℝ) / 4)).le
  exact H.trans_lt (H'.trans_lt hn)

theorem continuousOn_stableCenterSecondDifferentialLimit {c : ℝ} (hc : 2 ≤ c) :
    ContinuousOn (stableCenterSecondDifferentialLimit c) (stableParameterDomain c) :=
  (stableCenterSecondDifferential_uniform hc).continuousOn
    (Eventually.of_forall (fun n : ℕ => continuousOn_stableCenterSecondDifferential hc (Nat.cast_nonneg n))).frequently

theorem hasFDerivAt_stableCenterDifferentialLimit {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    HasFDerivAt (stableCenterDifferentialLimit c) (stableCenterSecondDifferentialLimit c y) y := by
  have hpoint (z : StableState) (hz : z ∈ stableParameterDomain c) :
      Tendsto (fun n : ℕ => stableCenterDifferential c z n) atTop
        (𝓝 (stableCenterDifferentialLimit c z)) :=
    (stableCenterDifferential_tendsto hc hz.1.le hz.2.1.le hz.2.2.le).comp tendsto_natCast_atTop_atTop
  exact hasFDerivAt_of_tendstoUniformlyOn (isOpen_stableParameterDomain c)
    (stableCenterSecondDifferential_uniform hc)
    (fun n z hz => hasFDerivAt_stableCenterDifferential hc hz.1.le hz.2.1.le hz.2.2.le (Nat.cast_nonneg n))
    hpoint ⟨hm, hu, hw⟩

theorem contDiffAt_stableCenterDifferentialLimit_one {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) :
    ContDiffAt ℝ 1 (stableCenterDifferentialLimit c) y := by
  apply contDiffAt_one_iff.mpr
  refine ⟨stableCenterSecondDifferentialLimit c, stableParameterDomain c,
    (isOpen_stableParameterDomain c).mem_nhds ⟨hm, hu, hw⟩,
    continuousOn_stableCenterSecondDifferentialLimit hc, ?_⟩
  intro z hz
  exact hasFDerivAt_stableCenterDifferentialLimit hc hz.1 hz.2.1 hz.2.2

end BianchiIX
