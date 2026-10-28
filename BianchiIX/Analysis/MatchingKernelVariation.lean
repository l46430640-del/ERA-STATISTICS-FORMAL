import BianchiIX.Analysis.MatchingKernelDifferential

noncomputable section

namespace BianchiIX

def matchingPhaseKernelDm (m v w : ℝ) : ℝ :=
  phaseNormKernelDa (m + 1) v - phaseNormKernelDa (m - 1) w

def matchingPhaseKernelPartials (m v w : ℝ) : Fin 4 → ℝ :=
  ![matchingPhaseKernelDm m v w / matchingPhaseSlope m v w, 0,
    matchingPhaseKernelDm m v w * matchingPhaseVVariation m v w + v * phaseNormKernelDb (m + 1) v,
    matchingPhaseKernelDm m v w * matchingPhaseWVariation m v w - w * phaseNormKernelDb (m - 1) w]

theorem hasDerivAt_matchingPhaseKernel {m v w : ℝ → ℝ} {m' v' w' t : ℝ}
    (hm : HasDerivAt m m' t) (hv : HasDerivAt v v' t) (hw : HasDerivAt w w' t) (hmt : 1 < m t) :
    HasDerivAt (fun s => matchingPhaseKernel (m s) (v s) (w s))
      (matchingPhaseKernelDm (m t) (v t) (w t) * m' +
        phaseNormKernelDb (m t + 1) (v t) * v' - phaseNormKernelDb (m t - 1) (w t) * w') t := by
  apply ((hasDerivAt_phaseNormKernel (hm.add_const 1) hv (by linarith only [hmt])).sub
    (hasDerivAt_phaseNormKernel (hm.sub_const 1) hw (by linarith only [hmt]))).congr_deriv
  dsimp [matchingPhaseKernelDm]
  ring

theorem hasDerivAt_matchingPhaseKernel_weighted {m v w : ℝ → ℝ} {t : ℝ} (d : Fin 4 → ℝ)
    (hm : HasDerivAt m (d 0 / matchingPhaseSlope (m t) (v t) (w t) +
      matchingPhaseVVariation (m t) (v t) (w t) * d 2 + matchingPhaseWVariation (m t) (v t) (w t) * d 3) t)
    (hv : HasDerivAt v (v t * d 2) t) (hw : HasDerivAt w (w t * d 3) t) (hmt : 1 < m t) :
    HasDerivAt (fun s => matchingPhaseKernel (m s) (v s) (w s))
      (∑ i : Fin 4, matchingPhaseKernelPartials (m t) (v t) (w t) i * d i) t := by
  apply (hasDerivAt_matchingPhaseKernel hm hv hw hmt).congr_deriv
  simp [Fin.sum_univ_succ, matchingPhaseKernelPartials]
  ring

theorem matchingPhase_kernel_derivative_bounds {μ m v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |matchingPhaseKernel m v w| ≤ 3 / μ ^ 2 ∧
    |matchingPhaseKernelDm m v w| ≤ 9 / μ ^ 3 ∧
    |matchingPhaseKernelPartials m v w 0| ≤ 12 / μ ^ 3 ∧
    |matchingPhaseKernelPartials m v w 2| ≤ 32 * v ^ 2 / μ ^ 4 ∧
    |matchingPhaseKernelPartials m v w 3| ≤ 32 * w ^ 2 / μ ^ 4 := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hμne := ne_of_gt hμ0
  have hp := phaseNormKernel_derivative_bounds (b := v) hμ0
    (show μ ≤ m + 1 by linarith only [(abs_le.mp hm).1])
  have hn := phaseNormKernel_derivative_bounds (b := w)
    (by positivity : 0 < 5 * μ / 8) (show 5 * μ / 8 ≤ m - 1 by linarith only [hμ, (abs_le.mp hm).1])
  have hpρ : phaseNormKernel (m + 1) v ≤ 1 / μ ^ 2 := by
    exact hp.2.1.trans (by convert! div_le_div_of_nonneg_right (show (1 / 2 : ℝ) ≤ 1 by norm_num) (sq_nonneg μ) using 1; ring)
  have hnρ : phaseNormKernel (m - 1) w ≤ 2 / μ ^ 2 := by
    exact hn.2.1.trans (by convert! div_le_div_of_nonneg_right (show (32 / 25 : ℝ) ≤ 2 by norm_num) (sq_nonneg μ) using 1; ring)
  have hna : |phaseNormKernelDa (m - 1) w| ≤ 8 / μ ^ 3 := by
    exact hn.2.2.1.trans (by convert! div_le_div_of_nonneg_right (show (512 / 125 : ℝ) ≤ 8 by norm_num) (by positivity : 0 ≤ μ ^ 3) using 1; ring)
  have hpq : |v * phaseNormKernelDb (m + 1) v| ≤ 5 * v ^ 2 / μ ^ 4 := by
    apply hp.2.2.2.trans
    convert! div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show (3 / 4 : ℝ) ≤ 5 by norm_num) (sq_nonneg v))
      (by positivity : 0 ≤ μ ^ 4) using 1
    ring
  have hnq : |w * phaseNormKernelDb (m - 1) w| ≤ 5 * w ^ 2 / μ ^ 4 := by
    apply hn.2.2.2.trans
    convert! div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show (3072 / 625 : ℝ) ≤ 5 by norm_num) (sq_nonneg w))
      (by positivity : 0 ≤ μ ^ 4) using 1
    ring
  have hRm : |matchingPhaseKernelDm m v w| ≤ 9 / μ ^ 3 :=
    ((abs_sub _ _).trans (add_le_add hp.2.2.1 hna)).trans_eq (by ring)
  have hvar := matchingPhase_inverse_weighted_bounds hμ hm hv hw
  have wall_bound (r e : ℝ) (he : |e| ≤ 3 * r ^ 2 / μ) :
      |matchingPhaseKernelDm m v w * e| ≤ 27 * r ^ 2 / μ ^ 4 := by
    rw [abs_mul]
    exact (mul_le_mul hRm he (abs_nonneg _) (by positivity)).trans_eq (by ring)
  refine ⟨?_, hRm, ?_, ?_, ?_⟩
  · change |phaseNormKernel (m + 1) v - phaseNormKernel (m - 1) w| ≤ _
    have H := abs_sub (phaseNormKernel (m + 1) v) (phaseNormKernel (m - 1) w)
    rw [abs_of_nonneg hp.1, abs_of_nonneg hn.1] at H
    exact (H.trans (add_le_add hpρ hnρ)).trans_eq (by ring)
  · change |matchingPhaseKernelDm m v w / matchingPhaseSlope m v w| ≤ _
    rw [div_eq_mul_inv, abs_mul]
    have H := mul_le_mul hRm (by simpa only [one_div] using hvar.1) (abs_nonneg _) (by positivity : 0 ≤ 9 / μ ^ 3)
    exact H.trans_eq (by ring)
  · exact ((abs_add_le _ _).trans (add_le_add (wall_bound v _ hvar.2.1) hpq)).trans_eq (by ring)
  · exact ((abs_sub _ _).trans (add_le_add (wall_bound w _ hvar.2.2) hnq)).trans_eq (by ring)

end BianchiIX
