import BianchiIX.Dynamics.ProjectiveState

noncomputable section

namespace BianchiIX

def projectiveBoundaryVariation (m v : ℝ) (xi : ProjectiveState) : ProjectiveState :=
  ![(1 - m) * v * xi 1 - 2 * v * xi 2,
    (1 - m ^ 2 - v ^ 2) / 2 * xi 1,
    v * xi 0 - v ^ 2 * xi 1 + (m - 1) * xi 2,
    (-m - 1) * xi 3]

theorem contDiff_projectiveField (n : WithTop ℕ∞) : ContDiff ℝ n projectiveField := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;>
    dsimp [projectiveField, phaseVelocity, strongVelocity, activeVelocity, weakVelocity, coupling] <;>
    fun_prop

theorem hasDerivAt_projectiveField_boundary {gamma : ℝ → ProjectiveState}
    {xi : ProjectiveState} {t m v : ℝ}
    (hg : HasDerivAt gamma xi t) (hb : gamma t = ![m, 0, v, 0]) :
    HasDerivAt (fun s => projectiveField (gamma s)) (projectiveBoundaryVariation m v xi) t := by
  have hm := hasDerivAt_pi.mp hg 0
  have hu := hasDerivAt_pi.mp hg 1
  have hv := hasDerivAt_pi.mp hg 2
  have hw := hasDerivAt_pi.mp hg 3
  have hc := hu.mul ((hv.add hw).sub hu)
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert! ((((hv.pow 2).neg.add (hw.pow 2)).add (hu.mul (hv.sub hw))).sub (hm.mul hc)) using 1
    dsimp [projectiveBoundaryVariation]
    simp only [hb]
    dsimp
    ring
  · convert! (((((hm.pow 2).const_sub 1).sub ((hv.sub hw).pow 2)).add (hu.pow 2)).mul hu).div_const 2 using 1
    dsimp [projectiveBoundaryVariation]
    simp only [hb]
    dsimp
    ring
  · convert! (((hm.sub_const 1).sub hc).mul hv) using 1
    dsimp [projectiveBoundaryVariation]
    simp only [hb]
    dsimp
    ring
  · convert! (((hm.neg.sub_const 1).sub hc).mul hw) using 1
    dsimp [projectiveBoundaryVariation]
    simp only [hb]
    dsimp
    ring

theorem projectiveField_boundary_fderiv (m v : ℝ) (xi : ProjectiveState) :
    fderiv ℝ projectiveField ![m, 0, v, 0] xi = projectiveBoundaryVariation m v xi := by
  have hl : HasDerivAt (fun s : ℝ => ![m, 0, v, 0] + s • xi) xi 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (![m, 0, v, 0] : ProjectiveState)).add
      ((hasDerivAt_id (0 : ℝ)).smul_const xi) using 1
    simp
  have hb : (![m, 0, v, 0] : ProjectiveState) + (0 : ℝ) • xi = ![m, 0, v, 0] := by simp
  have hf := ((contDiff_projectiveField 1).differentiable (by norm_num) ![m, 0, v, 0]).hasFDerivAt
  have hf' := (hb.symm ▸ hf).comp_hasDerivAt 0 hl
  simpa only [hb] using hf'.unique (hasDerivAt_projectiveField_boundary hl hb)

end BianchiIX
