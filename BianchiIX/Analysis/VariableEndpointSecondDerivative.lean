import BianchiIX.Analysis.MovingIntegralDerivative
import BianchiIX.Analysis.SecondDerivativeRules

noncomputable section

namespace BianchiIX

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The full Hessian at a moving endpoint, retaining both mixed terms. -/
theorem fderiv2_variable_endpoint {F : E × ℝ → ℝ} {τ : E → ℝ} {x : E} {b : ℝ}
    (hF : ContDiffAt ℝ 2 F (x, τ x)) (hτ : ContDiffAt ℝ 2 τ x)
    (hright : HasDerivAt (fun t => F (x, t)) b (τ x)) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => F (y, τ y))) x v w =
      fderiv ℝ (fderiv ℝ F) (x, τ x) (v, 0) (w, 0) +
      fderiv ℝ τ x v * fderiv ℝ (fderiv ℝ F) (x, τ x) (0, 1) (w, 0) +
      fderiv ℝ τ x w * fderiv ℝ (fderiv ℝ F) (x, τ x) (v, 0) (0, 1) +
      fderiv ℝ τ x v * fderiv ℝ τ x w *
        fderiv ℝ (fderiv ℝ F) (x, τ x) (0, 1) (0, 1) +
      b * fderiv ℝ (fderiv ℝ τ) x v w := by
  let J : E → E × ℝ := fun y => (y, τ y)
  have hJ : ContDiffAt ℝ 2 J x := contDiffAt_id.prodMk hτ
  have hJ1 (u : E) : fderiv ℝ J x u = (u, fderiv ℝ τ x u) := by
    change fderiv ℝ (fun y => (id y, τ y)) x u = _
    rw [((hasFDerivAt_id x).prodMk (hτ.differentiableAt (by norm_num)).hasFDerivAt).fderiv]
    rfl
  have hJ2 : fderiv ℝ (fderiv ℝ J) x v w = (0, fderiv ℝ (fderiv ℝ τ) x v w) := by
    have hfst := fderiv2_clm_comp_apply hJ (ContinuousLinearMap.fst ℝ E ℝ) v w
    have hsnd := fderiv2_clm_comp_apply hJ (ContinuousLinearMap.snd ℝ E ℝ) v w
    apply Prod.ext
    · change fderiv ℝ (fderiv ℝ (fun y : E => y)) x v w =
        (fderiv ℝ (fderiv ℝ J) x v w).1 at hfst
      have hid : fderiv ℝ (fun y : E => y) = fun _ => ContinuousLinearMap.id ℝ E :=
        funext (fun _ => fderiv_fun_id)
      simpa only [hid, fderiv_const_apply, zero_apply] using hfst.symm
    · exact hsnd.symm
  have htime : fderiv ℝ F (x, τ x) (0, 1) = b :=
    ((hF.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt (τ x)
      ((hasDerivAt_const (τ x) x).prodMk (hasDerivAt_id (τ x)))).unique hright
  have he (u : E) : (u, fderiv ℝ τ x u) =
      (u, (0 : ℝ)) + (fderiv ℝ τ x u) • ((0 : E), (1 : ℝ)) := by ext <;> simp
  have he2 : ((0 : E), fderiv ℝ (fderiv ℝ τ) x v w) =
      (fderiv ℝ (fderiv ℝ τ) x v w) • ((0 : E), (1 : ℝ)) := by simp
  have H := fderiv2_comp_apply hJ hF v w
  change fderiv ℝ (fderiv ℝ (fun y => F (y, τ y))) x v w = _ at H
  rw [hJ2, hJ1, hJ1, he v, he w, he2] at H
  dsimp only [J] at H
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, htime] at H
  convert H using 1
  ring

end BianchiIX
