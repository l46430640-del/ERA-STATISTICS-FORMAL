import BianchiIX.Analysis.HessianEvaluation

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_parameterSlice_apply {Φ : E × ℝ → F} {x : E} {t : ℝ}
    (H : DifferentiableAt ℝ Φ (x, t)) (v : E) :
    fderiv ℝ (fun y => Φ (y, t)) x v = fderiv ℝ Φ (x, t) (v, 0) := by
  have HD := H.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)
  change HasFDerivAt (fun y => Φ (y, t)) _ x at HD
  rw [HD.fderiv]
  rfl

theorem contDiffAt_parameterVariation {Φ : E × ℝ → F} {x : E} {t : ℝ}
    (H : ContDiffAt ℝ 2 Φ (x, t)) (w : E) :
    ContDiffAt ℝ 1 (fun p => fderiv ℝ Φ p (w, 0)) (x, t) :=
  (H.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const

/-- The derivative of the joint first variation is the ordinary Hessian of the fixed-time map. -/
theorem fderiv_parameterVariation_apply {Φ : E × ℝ → F} {x : E} {t : ℝ}
    (H : ContDiffAt ℝ 2 Φ (x, t)) (v w : E) :
    fderiv ℝ (fun y => fderiv ℝ Φ (y, t) (w, 0)) x v =
      fderiv ℝ (fderiv ℝ (fun y => Φ (y, t))) x v w := by
  have heq : (fun y => fderiv ℝ Φ (y, t) (w, 0)) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ (fun z => Φ (z, t)) y w) := by
    have hnear := (continuousAt_id.prodMk continuousAt_const).eventually (H.eventually (by norm_num))
    filter_upwards [hnear] with y hy
    exact (fderiv_parameterSlice_apply (hy.differentiableAt (by norm_num)) w).symm
  have hslice : ContDiffAt ℝ 2 (fun y => Φ (y, t)) x :=
    H.comp x (contDiffAt_id.prodMk contDiffAt_const)
  have HD := ((hslice.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  rw [heq.fderiv_eq, HD.fderiv]
  simp

end BianchiIX
