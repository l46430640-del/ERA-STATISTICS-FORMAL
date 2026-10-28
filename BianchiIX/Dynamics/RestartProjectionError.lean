import BianchiIX.Dynamics.RestartProjectionScaledBounds
import Mathlib.Analysis.Calculus.Deriv.Pi

noncomputable section

namespace BianchiIX

def restartProjectionError (p : RestartRadialState) : ℝ :=
  restartProjectionPhase p - restartRadialPhase p.2

def restartProjectionParametersAt (r : ℝ) (p : RestartRadialState) : RestartProjectionParameters :=
  (![r, p.1 / r, p.2 2 / r], ![p.2 0 / r, p.2 1 / r])

def restartProjectionParameterTangent (r : ℝ) (v : RestartRadialState) : RestartProjectionParameters :=
  (![0, v.1 / r, v.2 2 / r], ![v.2 0 / r, v.2 1 / r])

theorem restartProjectionScaledState_parameters {r : ℝ} (hr : r ≠ 0) (p : RestartRadialState) :
    restartProjectionScaledState (restartProjectionParametersAt r p) = p := by
  apply Prod.ext
  · change r * (p.1 / r) = p.1
    field_simp
  · ext i
    fin_cases i <;> change r * (_ / r) = _ <;> field_simp <;> rfl

theorem restartProjectionError_rescaled {r : ℝ} (hr : 0 < r) (p : RestartRadialState) :
    restartProjectionError p = r * restartProjectionScaledError (restartProjectionParametersAt r p) := by
  have H := restartProjectionPhase_scaled (p := restartProjectionParametersAt r p) hr
  rw [restartProjectionScaledState_parameters hr.ne'] at H
  exact H

theorem contDiff_restartProjectionParametersAt (r : ℝ) (k : WithTop ℕ∞) :
    ContDiff ℝ k (restartProjectionParametersAt r) := by
  unfold restartProjectionParametersAt
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ k (fun _ : RestartRadialState => r)
      fun_prop
    · change ContDiff ℝ k (fun x : RestartRadialState => x.1 / r)
      fun_prop
    · change ContDiff ℝ k (fun x : RestartRadialState => x.2 2 / r)
      fun_prop
  · apply contDiff_pi.mpr
    intro i
    fin_cases i
    · change ContDiff ℝ k (fun x : RestartRadialState => x.2 0 / r)
      fun_prop
    · change ContDiff ℝ k (fun x : RestartRadialState => x.2 1 / r)
      fun_prop

theorem hasDerivAt_restartProjectionParametersAt {p : ℝ → RestartRadialState} {v : RestartRadialState}
    {t : ℝ} (H : HasDerivAt p v t) (r : ℝ) :
    HasDerivAt (fun s => restartProjectionParametersAt r (p s)) (restartProjectionParameterTangent r v) t := by
  have Hfst : HasDerivAt (fun s => (p s).1) v.1 t :=
    (ContinuousLinearMap.fst ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt t H
  have Hsnd : HasDerivAt (fun s => (p s).2) v.2 t :=
    (ContinuousLinearMap.snd ℝ ℝ RestartCenterState).hasFDerivAt.comp_hasDerivAt t H
  have HN : HasDerivAt (fun s => (restartProjectionParametersAt r (p s)).1)
      (restartProjectionParameterTangent r v).1 t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert! hasDerivAt_const t r using 1
    · convert! Hfst.div_const r using 1
    · convert! (hasDerivAt_pi.mp Hsnd 2).div_const r using 1
  have HC : HasDerivAt (fun s => (restartProjectionParametersAt r (p s)).2)
      (restartProjectionParameterTangent r v).2 t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert! (hasDerivAt_pi.mp Hsnd 0).div_const r using 1
    · convert! (hasDerivAt_pi.mp Hsnd 1).div_const r using 1
  exact HN.prodMk HC

theorem contDiffAt_restartProjectionError {r : ℝ} {p : RestartRadialState} (hr : 0 < r)
    (H : ContDiffAt ℝ 2 restartProjectionScaledError (restartProjectionParametersAt r p)) :
    ContDiffAt ℝ 2 restartProjectionError p := by
  have heq : restartProjectionError = fun q => r * restartProjectionScaledError (restartProjectionParametersAt r q) :=
    funext (restartProjectionError_rescaled hr)
  rw [heq]
  exact contDiffAt_const.mul (H.comp p (contDiff_restartProjectionParametersAt r 2).contDiffAt)

theorem hasDerivAt_restartProjectionError {p : ℝ → RestartRadialState} {v : RestartRadialState}
    {r t : ℝ} (hr : 0 < r) (Hp : HasDerivAt p v t)
    (H : DifferentiableAt ℝ restartProjectionScaledError (restartProjectionParametersAt r (p t))) :
    HasDerivAt (fun s => restartProjectionError (p s))
      (r * fderiv ℝ restartProjectionScaledError (restartProjectionParametersAt r (p t))
        (restartProjectionParameterTangent r v)) t := by
  have HD := (H.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_restartProjectionParametersAt Hp r)).const_mul r
  simpa only [Function.comp_apply, restartProjectionError_rescaled hr] using HD

theorem fderiv_restartProjectionError {r : ℝ} {p : RestartRadialState} (hr : 0 < r)
    (H : ContDiffAt ℝ 2 restartProjectionScaledError (restartProjectionParametersAt r p)) (v : RestartRadialState) :
    fderiv ℝ restartProjectionError p v = r *
      fderiv ℝ restartProjectionScaledError (restartProjectionParametersAt r p) (restartProjectionParameterTangent r v) := by
  have Hline : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p using 1
    simp
  have Hscaled : DifferentiableAt ℝ restartProjectionScaledError
      (restartProjectionParametersAt r (p + (0 : ℝ) • v)) := by simpa using H.differentiableAt (by norm_num)
  have H₁ := hasDerivAt_restartProjectionError hr Hline Hscaled
  have H₂ := ((contDiffAt_restartProjectionError hr H).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt_of_eq
    0 Hline (by simp)
  apply H₂.unique
  convert! H₁ using 1
  simp

end BianchiIX
