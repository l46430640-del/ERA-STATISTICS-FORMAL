import BianchiIX.Dynamics.MainWallDensity
import BianchiIX.Dynamics.ArrivalFlux

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The coordinate Jacobian of an actual moving-time map between main-wall sections. -/
theorem mainWall_coordinate_jacobian {h k t₀ : ℝ} {y : SectionCoordinates}
    {τ : NormalizedState → ℝ} {R : SectionCoordinates → SectionCoordinates}
    (hh : 0 < h) (hk : 0 < k) (hy : y ∈ mainWallChartDomain h)
    (hRy : R y ∈ mainWallChartDomain k)
    (ht : τ (mainWallChart h y) ∈ normalizedMaxDomain (mainWallChart h y) t₀)
    (hτ : DifferentiableAt ℝ τ (mainWallChart h y)) (hR : DifferentiableAt ℝ R y)
    (heq : (fun v => mainWallChart k (R v)) =ᶠ[𝓝 y]
      (fun v => normalizedMaxCurve (mainWallChart h v) t₀ (τ (mainWallChart h v)))) :
    mainWallChartDensity k (R y) * |(fderiv ℝ R y).det| =
      Real.exp (∫ u in t₀..τ (mainWallChart h y),
        normalizedCorrectedDivergence (normalizedMaxCurve (mainWallChart h y) t₀ u)) *
          mainWallChartDensity h y := by
  let A := fun x => normalizedMaxCurve x t₀ (τ x)
  have hdA := (hasFDerivAt_normalized_arrival ht hτ).differentiableAt.hasFDerivAt
  have hleft := (hasFDerivAt_mainWallChart hRy).comp y hR.hasFDerivAt
  have hright := hdA.comp y (hasFDerivAt_mainWallChart hy)
  have hder : (mainWallChartDifferential k (R y)).comp (fderiv ℝ R y) =
      (fderiv ℝ A (mainWallChart h y)).comp (mainWallChartDifferential h y) := by
    exact hleft.unique (hright.congr_of_eventuallyEq heq)
  have hframe : (fun i => fderiv ℝ A (mainWallChart h y) (mainWallChartFrame h y i)) =
      (fun i => mainWallChartDifferential k (R y) (fderiv ℝ R y (Pi.single i 1))) := by
    funext i
    exact congrArg (fun L : SectionCoordinates →L[ℝ] NormalizedState => L (Pi.single i 1)) hder.symm
  have H := normalizedSectionFlux_arrival_abs (mainWallChart_positive hh y)
    (mainWallChart_constraint hy) ht hτ (mainWallChartFrame h y) (mainWallChartFrame_tangent hy)
  have hvalue : mainWallChart k (R y) =
      normalizedMaxCurve (mainWallChart h y) t₀ (τ (mainWallChart h y)) := by
    convert! heq.self_of_nhds using 1
  rw [← hvalue] at H
  rw [show (fun i => fderiv ℝ (fun x => normalizedMaxCurve x t₀ (τ x)) (mainWallChart h y)
      (mainWallChartFrame h y i)) = _ from hframe,
    mainWallChart_flux_linear hk hRy, mainWallChart_flux hh hy] at H
  exact H

theorem mainWall_coordinate_det_ne_zero {h k t₀ : ℝ} {y : SectionCoordinates}
    {τ : NormalizedState → ℝ} {R : SectionCoordinates → SectionCoordinates}
    (hh : 0 < h) (hk : 0 < k) (hy : y ∈ mainWallChartDomain h)
    (hRy : R y ∈ mainWallChartDomain k)
    (ht : τ (mainWallChart h y) ∈ normalizedMaxDomain (mainWallChart h y) t₀)
    (hτ : DifferentiableAt ℝ τ (mainWallChart h y)) (hR : DifferentiableAt ℝ R y)
    (heq : (fun v => mainWallChart k (R v)) =ᶠ[𝓝 y]
      (fun v => normalizedMaxCurve (mainWallChart h v) t₀ (τ (mainWallChart h v)))) :
    (fderiv ℝ R y).det ≠ 0 := by
  have H := mainWall_coordinate_jacobian hh hk hy hRy ht hτ hR heq
  intro hz
  rw [hz, abs_zero, mul_zero] at H
  exact (ne_of_gt (mul_pos (Real.exp_pos _) (mainWallChartDensity_pos hh hy))) H.symm

theorem mainWall_coordinate_strict_expansion {h k t₀ : ℝ} {y : SectionCoordinates}
    {τ : NormalizedState → ℝ} {R : SectionCoordinates → SectionCoordinates}
    (hh : 0 < h) (hk : 0 < k) (hy : y ∈ mainWallChartDomain h)
    (hRy : R y ∈ mainWallChartDomain k) (htt : t₀ < τ (mainWallChart h y))
    (hτ : DifferentiableAt ℝ τ (mainWallChart h y)) (hR : DifferentiableAt ℝ R y)
    (heq : (fun v => mainWallChart k (R v)) =ᶠ[𝓝 y]
      (fun v => normalizedMaxCurve (mainWallChart h v) t₀ (τ (mainWallChart h v)))) :
    mainWallChartDensity h y < mainWallChartDensity k (R y) * |(fderiv ℝ R y).det| := by
  have hpos := mainWallChart_positive hh y
  have hcon := mainWallChart_constraint hy
  have ht := normalizedMaxDomain_contains_Ici hpos hcon t₀ htt.le
  rw [mainWall_coordinate_jacobian hh hk hy hRy ht hτ hR heq,
    ← normalizedVolumeJacobian_eq_exp_integral hpos hcon ht]
  simpa only [one_mul] using mul_lt_mul_of_pos_right
    (normalizedVolumeJacobian_gt_one hpos hcon htt) (mainWallChartDensity_pos hh hy)

/-- Every actual transverse crossing admits smooth coordinates satisfying the Jacobian formula. -/
theorem exists_mainWall_coordinate_event {h k t₀ t : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hk : 0 < k) (hy : y ∈ mainWallChartDomain h)
    (ht : t ∈ normalizedMaxDomain (mainWallChart h y) t₀)
    (hlevel : normalizedMaxCurve (mainWallChart h y) t₀ t 2 = k)
    (hp : normalizedMaxCurve (mainWallChart h y) t₀ t 0 < 0) :
    ∃ (τ : NormalizedState → ℝ) (R : SectionCoordinates → SectionCoordinates),
      τ (mainWallChart h y) = t ∧ ContDiffAt ℝ 1 τ (mainWallChart h y) ∧
      ContDiffAt ℝ 1 R y ∧ R y = mainWallCoordinates (normalizedMaxCurve (mainWallChart h y) t₀ t) ∧
      (∀ᶠ v in 𝓝 y, v ∈ mainWallChartDomain h ∧
        τ (mainWallChart h v) ∈ normalizedMaxDomain (mainWallChart h v) t₀ ∧
        R v ∈ mainWallChartDomain k ∧
        mainWallChart k (R v) = normalizedMaxCurve (mainWallChart h v) t₀ (τ (mainWallChart h v))) ∧
      (fderiv ℝ R y).det ≠ 0 ∧
      mainWallChartDensity k (R y) * |(fderiv ℝ R y).det| =
        Real.exp (∫ u in t₀..t,
          normalizedCorrectedDivergence (normalizedMaxCurve (mainWallChart h y) t₀ u)) *
            mainWallChartDensity h y ∧
      (∀ᶠ z : SectionCoordinates × ℝ in 𝓝 (y, t),
        z.2 ∈ normalizedMaxDomain (mainWallChart h z.1) t₀ ∧
        (normalizedMaxCurve (mainWallChart h z.1) t₀ z.2 2 = k ↔ τ (mainWallChart h z.1) = z.2)) := by
  obtain ⟨τ, hτ, hcτ, hhit, huniq, hcA⟩ := exists_normalized_mainWall_event ht hk hlevel hp
  let A := fun x => normalizedMaxCurve x t₀ (τ x)
  let R := fun v => mainWallCoordinates (A (mainWallChart h v))
  have hA : A (mainWallChart h y) = normalizedMaxCurve (mainWallChart h y) t₀ t := by
    simp only [A, hτ]
  have hphysical := (maximalNormalizedSolution (mainWallChart h y) t₀).physical
    (mainWallChart_positive hh y) (mainWallChart_constraint hy) ht
  have hpos : positiveWalls (A (mainWallChart h y)) := by rw [hA]; exact hphysical.1
  have hcC := contDiffAt_mainWallChart hy (1 : WithTop ℕ∞)
  have hcAC : ContDiffAt ℝ 1 (fun v => A (mainWallChart h v)) y := hcA.comp y hcC
  have hcR : ContDiffAt ℝ 1 R y := by
    convert! (contDiffAt_mainWallCoordinates hpos 1).comp y hcAC using 1
  have hneg : ∀ᶠ v in 𝓝 y, A (mainWallChart h v) 0 < 0 := by
    have hc : ContinuousAt (fun v => A (mainWallChart h v) 0) y :=
      (continuous_apply (0 : Fin 5)).continuousAt.comp hcAC.continuousAt
    exact hc.eventually_lt continuousAt_const (by rw [hA]; exact hp)
  have hlocal : ∀ᶠ v in 𝓝 y, v ∈ mainWallChartDomain h ∧
      τ (mainWallChart h v) ∈ normalizedMaxDomain (mainWallChart h v) t₀ ∧
      R v ∈ mainWallChartDomain k ∧ mainWallChart k (R v) = A (mainWallChart h v) := by
    filter_upwards [(isOpen_mainWallChartDomain h).mem_nhds hy,
      hcC.continuousAt.eventually hhit, hneg] with v hv he hn
    have hphys := (maximalNormalizedSolution (mainWallChart h v) t₀).physical
      (mainWallChart_positive hh v) (mainWallChart_constraint hv) he.1
    exact ⟨hv, he.1, mainWallChart_coordinates hphys.1 hphys.2 hn he.2⟩
  have heq : (fun v => mainWallChart k (R v)) =ᶠ[𝓝 y] (fun v => A (mainWallChart h v)) :=
    hlocal.mono (fun _ hv => hv.2.2.2)
  refine ⟨τ, R, hτ, hcτ, hcR, ?_, hlocal, ?_, ?_, ?_⟩
  · exact congrArg mainWallCoordinates hA
  · exact mainWall_coordinate_det_ne_zero hh hk hy (hlocal.self_of_nhds.2.2.1)
      (hlocal.self_of_nhds.2.1) (hcτ.differentiableAt (by norm_num))
      (hcR.differentiableAt (by norm_num)) heq
  · have H := mainWall_coordinate_jacobian hh hk hy (hlocal.self_of_nhds.2.2.1)
      (hlocal.self_of_nhds.2.1) (hcτ.differentiableAt (by norm_num))
      (hcR.differentiableAt (by norm_num)) heq
    simpa only [hτ] using H
  · have hc : ContinuousAt (fun z : SectionCoordinates × ℝ => (mainWallChart h z.1, z.2)) (y, t) := by
      convert! ((contDiffAt_mainWallChart hy 1).continuousAt.comp
        (continuousAt_fst (p := (y, t)))).prodMk continuousAt_snd using 1
    exact hc.eventually huniq

end BianchiIX
