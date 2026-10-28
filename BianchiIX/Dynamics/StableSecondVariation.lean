import BianchiIX.Dynamics.StableSecondIntegral
import BianchiIX.Dynamics.StableBoundaryStrongVariation

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem stableRescaledSecondDifferential_symm {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s) (v w : StableState) :
    stableRescaledSecondDifferential K y s v w = stableRescaledSecondDifferential K y s w v := by
  rw [← stableRescaledFlow_fderiv2 hK hc hm hu hw hs]
  have hp : ContDiffAt ℝ 2 (fun z : StableState => (z, s)) y :=
    contDiffAt_id.prodMk contDiffAt_const
  have H := (contDiffAt_stableRescaledFlow_two hK hc hm.le hu.le hw.le hs).comp y hp
  exact (H.isSymmSndFDerivAt (by norm_num)).eq v w

theorem stableSecondIntegral_initial (K : ℝ) (y w : StableState) :
    stableSecondIntegral K y w 0 = 0 := by
  simp [stableSecondIntegral]

/-- A genuine two-sided differentiable extension also supplies the initial endpoint for comparisons. -/
theorem stableSecondIntegral_variational_equation {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s) (v w : StableState) :
    HasDerivAt (fun r => stableSecondIntegral K y w r v)
      (K • ((stableOriginalJacobian (stableRescaledFlow K y s)).mulVec
          (stableSecondIntegral K y w s v) +
        stableOriginalHessian (stableRescaledFlow K y s)
          (stableRescaledDifferential K y s v) (stableRescaledDifferential K y s w))) s := by
  simpa only [stableRescaledSecondSource,
    stableRescaledSecondDifferential_eq_integral hK hc hm hu hw hs v w, add_comm] using
    hasDerivAt_stableSecondIntegral_apply hK hc hm.le hu.le hw.le hs v w

theorem hasDerivWithinAt_stableRescaledSecondDifferential {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s) (v w : StableState) :
    HasDerivWithinAt (fun r => stableRescaledSecondDifferential K y r v w)
      (stableRescaledSecondSource K v w (y, s)) (Ici 0) s :=
  (hasDerivAt_stableSecondIntegral_apply hK hc hm.le hu.le hw.le hs v w).hasDerivWithinAt.congr_of_mem
    (fun _ hr => stableRescaledSecondDifferential_eq_integral hK hc hm hu hw hr v w) hs

theorem hasDerivAt_stableRescaledSecondDifferential {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 < s) (v w : StableState) :
    HasDerivAt (fun r => stableRescaledSecondDifferential K y r v w)
      (stableRescaledSecondSource K v w (y, s)) s :=
  (hasDerivWithinAt_stableRescaledSecondDifferential hK hc hm hu hw hs.le v w).hasDerivAt
    (Ici_mem_nhds hs)

theorem stableRescaledSecondDifferential_strong_zero {y v w : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| < 1 / 40)
    (hu : |y 1| < 1 / 200) (hw : |y 2| < 1 / 200) (hs : 0 ≤ s)
    (hy : y 1 = 0) (hv : v 1 = 0) (hw' : w 1 = 0) :
    stableRescaledSecondDifferential (c + 1) y s v w 1 = 0 := by
  have hl : HasDerivAt (fun r : ℝ => y + r • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hD := (hasFDerivAt_stableRescaledDifferential (by linarith : 0 < c + 1)
    hc hm.le hu.le hw.le hs).clm_apply (hasFDerivAt_const w y)
  have H := hasDerivAt_pi.mp (hD.comp_hasDerivAt_of_eq 0 hl (by simp)) 1
  have hnear : ∀ᶠ r : ℝ in 𝓝 0, y + r • v ∈ stableParameterDomain c := by
    apply hl.continuousAt.eventually
    simpa using (isOpen_stableParameterDomain c).mem_nhds ⟨hm, hu, hw⟩
  have heq : (fun r : ℝ => stableRescaledDifferential (c + 1) (y + r • v) s w 1)
      =ᶠ[𝓝 0] (fun _ => (0 : ℝ)) := by
    filter_upwards [hnear] with r hr
    apply stableRescaledDifferential_strong_zero hc hr.1.le hr.2.1.le hr.2.2.le hs _ hw'
    simp [hy, hv]
  have Hz := (hasDerivAt_const 0 (0 : ℝ)).congr_of_eventuallyEq heq
  simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply, add_apply, zero_apply,
    map_zero, zero_add, ContinuousLinearMap.flip_apply] using H.unique Hz

end BianchiIX
