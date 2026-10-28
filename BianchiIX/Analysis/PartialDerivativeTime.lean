import BianchiIX.Analysis.ParameterSlice
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A local time-derivative identity can be differentiated in the ordinary parameter. -/
theorem hasDerivAt_parameter_fderiv_of_local_time {Φ G : E × ℝ → F} {x : E} {t : ℝ}
    (hΦ : ContDiffAt ℝ 2 Φ (x, t))
    (htime : (fun p => fderiv ℝ Φ p (0, 1)) =ᶠ[𝓝 (x, t)] G) (v : E) :
    HasDerivAt (fun s => fderiv ℝ (fun y => Φ (y, s)) x v)
      (fderiv ℝ (fun y => G (y, t)) x v) t := by
  have hD := (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have Htime := (hD.hasFDerivAt.clm_apply (hasFDerivAt_const (0, 1) (x, t))).congr_of_eventuallyEq htime.symm
  have hpath : HasDerivAt (fun s : ℝ => (x, s)) (0, 1) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  have H := hasDerivAt_fderiv_apply_const hD hpath (v, 0)
  have Hrate : fderiv ℝ (fderiv ℝ Φ) (x, t) (0, 1) (v, 0) =
      fderiv ℝ (fun y => G (y, t)) x v := by
    rw [(hΦ.isSymmSndFDerivAt (by norm_num)).eq (0, 1) (v, 0),
      fderiv_parameterSlice_apply Htime.differentiableAt v, Htime.fderiv]
    simp
  have Hslice : (fun s => fderiv ℝ (fun y => Φ (y, s)) x v) =ᶠ[𝓝 t]
      (fun s => fderiv ℝ Φ (x, s) (v, 0)) := by
    have Hnear := (continuousAt_const.prodMk continuousAt_id).eventually
      (hΦ.eventually (by norm_num))
    filter_upwards [Hnear] with s hs
    exact fderiv_parameterSlice_apply (hs.differentiableAt (by norm_num)) v
  exact (H.congr_deriv Hrate).congr_of_eventuallyEq Hslice

end BianchiIX
