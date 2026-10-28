import BianchiIX.Dynamics.ProjectiveCycle
import BianchiIX.Analysis.HessianEvaluation

noncomputable section

namespace BianchiIX

open scoped Topology

def cycleNumerator (i : Fin 4) (y : ProjectiveState) : ℝ :=
  ![-4 * (y 0 + 1), 4 * y 2, 4 * y 3, 4 * y 1] i

def cycleNumeratorSlope (i : Fin 4) (v : ProjectiveState) : ℝ :=
  ![-4 * v 0, 4 * v 2, 4 * v 3, 4 * v 1] i

def cycleDenomDifferential (y v : ProjectiveState) : ℝ :=
  2 * (y 0 + 1) * v 0 + 2 * (y 1 - y 2 - y 3) * v 1 +
    2 * (y 2 - y 1 - y 3) * v 2 + 2 * (y 3 - y 1 - y 2) * v 3

def cycleDenomHessian (v w : ProjectiveState) : ℝ :=
  2 * (v 0 * w 0 + (v 1 - v 2 - v 3) * w 1 +
    (v 2 - v 1 - v 3) * w 2 + (v 3 - v 1 - v 2) * w 3)

def cycleDifferential (i : Fin 4) (y v : ProjectiveState) : ℝ :=
  cycleNumeratorSlope i v / projectiveCycleDenom y -
    cycleNumerator i y * cycleDenomDifferential y v / projectiveCycleDenom y ^ 2

def cycleHessian (i : Fin 4) (y v w : ProjectiveState) : ℝ :=
  -(cycleNumeratorSlope i v * cycleDenomDifferential y w +
    cycleNumeratorSlope i w * cycleDenomDifferential y v +
    cycleNumerator i y * cycleDenomHessian v w) / projectiveCycleDenom y ^ 2 +
    2 * cycleNumerator i y * cycleDenomDifferential y v * cycleDenomDifferential y w /
      projectiveCycleDenom y ^ 3

theorem projectiveCycle_component (i : Fin 4) (y : ProjectiveState) :
    projectiveCycle y i = (if i = 0 then 1 else 0) + cycleNumerator i y / projectiveCycleDenom y := by
  fin_cases i <;> simp [projectiveCycle, cycleNumerator]
  ring

theorem hasDerivAt_cycleNumerator {γ : ℝ → ProjectiveState} {v : ProjectiveState} {t : ℝ}
    (hγ : HasDerivAt γ v t) (i : Fin 4) :
    HasDerivAt (fun s => cycleNumerator i (γ s)) (cycleNumeratorSlope i v) t := by
  fin_cases i
  · exact ((hasDerivAt_pi.mp hγ 0).add_const 1).const_mul (-4)
  · exact (hasDerivAt_pi.mp hγ 2).const_mul 4
  · exact (hasDerivAt_pi.mp hγ 3).const_mul 4
  · exact (hasDerivAt_pi.mp hγ 1).const_mul 4

theorem hasDerivAt_projectiveCycleDenom {γ : ℝ → ProjectiveState} {v : ProjectiveState} {t : ℝ}
    (hγ : HasDerivAt γ v t) :
    HasDerivAt (fun s => projectiveCycleDenom (γ s)) (cycleDenomDifferential (γ t) v) t := by
  have h0 := hasDerivAt_pi.mp hγ 0
  have h1 := hasDerivAt_pi.mp hγ 1
  have h2 := hasDerivAt_pi.mp hγ 2
  have h3 := hasDerivAt_pi.mp hγ 3
  have hquad := ((((h0.add_const 1).pow 2).add (h1.pow 2)).add (h2.pow 2)).add (h3.pow 2)
  have hcross := (((h1.mul h2).add (h1.mul h3)).add (h2.mul h3)).const_mul 2
  have H := hquad.sub hcross
  convert! H using 1
  · funext s
    dsimp [projectiveCycleDenom, axisCycleDenom, curvature]
    ring
  · dsimp [cycleDenomDifferential]
    ring

theorem projectiveCycleDenom_fderiv (y v : ProjectiveState) :
    fderiv ℝ projectiveCycleDenom y v = cycleDenomDifferential y v := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hd := ((contDiff_projectiveCycleDenom 1).differentiable (by norm_num) y).hasFDerivAt
  have H := (show HasFDerivAt projectiveCycleDenom (fderiv ℝ projectiveCycleDenom y)
    (y + (0 : ℝ) • v) by simpa using hd).comp_hasDerivAt 0 hl
  simpa only [zero_smul, add_zero] using H.unique (hasDerivAt_projectiveCycleDenom hl)

theorem hasDerivAt_cycleDenomDifferential {γ : ℝ → ProjectiveState} {v : ProjectiveState} {t : ℝ}
    (hγ : HasDerivAt γ v t) (w : ProjectiveState) :
    HasDerivAt (fun s => cycleDenomDifferential (γ s) w) (cycleDenomHessian v w) t := by
  have h0 := hasDerivAt_pi.mp hγ 0
  have h1 := hasDerivAt_pi.mp hγ 1
  have h2 := hasDerivAt_pi.mp hγ 2
  have h3 := hasDerivAt_pi.mp hγ 3
  have H := (((((h0.add_const 1).const_mul 2).mul_const (w 0)).add
    ((((h1.sub h2).sub h3).const_mul 2).mul_const (w 1))).add
    ((((h2.sub h1).sub h3).const_mul 2).mul_const (w 2))).add
    ((((h3.sub h1).sub h2).const_mul 2).mul_const (w 3))
  convert! H using 1
  dsimp [cycleDenomHessian]
  ring

theorem hasDerivAt_projectiveCycle_component {γ : ℝ → ProjectiveState} {v : ProjectiveState} {t : ℝ}
    (hγ : HasDerivAt γ v t) (hH : projectiveCycleDenom (γ t) ≠ 0) (i : Fin 4) :
    HasDerivAt (fun s => projectiveCycle (γ s) i) (cycleDifferential i (γ t) v) t := by
  simp only [projectiveCycle_component]
  apply (((hasDerivAt_cycleNumerator hγ i).div (hasDerivAt_projectiveCycleDenom hγ) hH).const_add
    (if i = 0 then 1 else 0)).congr_deriv
  dsimp [cycleDifferential]
  field_simp

theorem projectiveCycle_fderiv_component {y : ProjectiveState} (hH : projectiveCycleDenom y ≠ 0)
    (i : Fin 4) (v : ProjectiveState) :
    fderiv ℝ (fun z => projectiveCycle z i) y v = cycleDifferential i y v := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hreg := contDiffAt_pi.mp (contDiffAt_projectiveCycle 1 hH) i
  have H := (show HasFDerivAt (fun z => projectiveCycle z i) (fderiv ℝ (fun z => projectiveCycle z i) y)
    (y + (0 : ℝ) • v) by simpa using (hreg.differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt 0 hl
  simpa only [zero_smul, add_zero] using H.unique (hasDerivAt_projectiveCycle_component hl (by simpa using hH) i)

theorem hasDerivAt_cycleDifferential {γ : ℝ → ProjectiveState} {v : ProjectiveState} {t : ℝ}
    (hγ : HasDerivAt γ v t) (hH : projectiveCycleDenom (γ t) ≠ 0) (i : Fin 4) (w : ProjectiveState) :
    HasDerivAt (fun s => cycleDifferential i (γ s) w) (cycleHessian i (γ t) v w) t := by
  have hD := hasDerivAt_projectiveCycleDenom hγ
  have H := ((hasDerivAt_const t (cycleNumeratorSlope i w)).div hD hH).sub
    (((hasDerivAt_cycleNumerator hγ i).mul (hasDerivAt_cycleDenomDifferential hγ w)).div
      (hD.pow 2) (pow_ne_zero 2 hH))
  apply H.congr_deriv
  dsimp [cycleHessian]
  field_simp
  ring

theorem projectiveCycle_fderiv2_component {y : ProjectiveState} (hH : projectiveCycleDenom y ≠ 0)
    (i : Fin 4) (v w : ProjectiveState) :
    fderiv ℝ (fderiv ℝ (fun z => projectiveCycle z i)) y v w = cycleHessian i y v w := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hreg := contDiffAt_pi.mp (contDiffAt_projectiveCycle 2 (y := y + (0 : ℝ) • v) (by simpa using hH)) i
  have hD := (hreg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have H := hasDerivAt_fderiv_apply_const hD hl w
  have hnear : ∀ᶠ s : ℝ in 𝓝 0, projectiveCycleDenom (y + s • v) ≠ 0 :=
    (((contDiff_projectiveCycleDenom 0).continuous.continuousAt.comp hl.continuousAt).eventually_ne
      (by simpa using hH))
  have heq : (fun s : ℝ => fderiv ℝ (fun z => projectiveCycle z i) (y + s • v) w) =ᶠ[𝓝 0]
      (fun s => cycleDifferential i (y + s • v) w) := by
    filter_upwards [hnear] with s hs
    exact projectiveCycle_fderiv_component hs i w
  simpa only [zero_smul, add_zero] using (H.congr_of_eventuallyEq heq.symm).unique
    (hasDerivAt_cycleDifferential hl (by simpa using hH) i w)

end BianchiIX
