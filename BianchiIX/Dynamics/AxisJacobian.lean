import BianchiIX.Dynamics.AxisEvents
import BianchiIX.Dynamics.ArrivalFlux

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem axisWallChartFrame_tangent (A : NormalizedSymmetry) {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) (i : Fin 3) :
    normalizedConstraintDifferential (axisWallChart A h y) (axisWallChartFrame A h y i) = 0 :=
  congrArg (fun L : SectionCoordinates →L[ℝ] ℝ => L (Pi.single i 1))
    (axisWallChartDifferential_tangent A hy)

theorem axisWallChart_flux (A : NormalizedSymmetry) {h : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hy : y ∈ mainWallChartDomain h) :
    |normalizedSectionFlux (axisWallChart A h y) (axisWallChartFrame A h y)| = mainWallChartDensity h y := by
  rw [axisWallChart_signed_flux A hh hy, abs_neg, abs_of_pos (mainWallChartDensity_pos hh hy)]

/-- Exact weighted Jacobian between independently chosen source and target axis charts. -/
theorem axisWall_coordinate_jacobian (A B : NormalizedSymmetry) {h k t₀ : ℝ} {y : SectionCoordinates}
    {τ : NormalizedState → ℝ} {R : SectionCoordinates → SectionCoordinates}
    (hh : 0 < h) (hk : 0 < k) (hy : y ∈ mainWallChartDomain h)
    (hRy : R y ∈ mainWallChartDomain k)
    (ht : τ (axisWallChart A h y) ∈ normalizedMaxDomain (axisWallChart A h y) t₀)
    (hτ : DifferentiableAt ℝ τ (axisWallChart A h y)) (hR : DifferentiableAt ℝ R y)
    (heq : (fun v => axisWallChart B k (R v)) =ᶠ[𝓝 y]
      (fun v => normalizedMaxCurve (axisWallChart A h v) t₀ (τ (axisWallChart A h v)))) :
    mainWallChartDensity k (R y) * |(fderiv ℝ R y).det| =
      Real.exp (∫ u in t₀..τ (axisWallChart A h y),
        normalizedCorrectedDivergence (normalizedMaxCurve (axisWallChart A h y) t₀ u)) *
          mainWallChartDensity h y := by
  let F := fun x => normalizedMaxCurve x t₀ (τ x)
  have hdF := (hasFDerivAt_normalized_arrival ht hτ).differentiableAt.hasFDerivAt
  have hdsource := ((contDiffAt_axisWallChart A hy 1).differentiableAt (by norm_num)).hasFDerivAt
  have hdtarget := ((contDiffAt_axisWallChart B hRy 1).differentiableAt (by norm_num)).hasFDerivAt
  have hder : (axisWallChartDifferential B k (R y)).comp (fderiv ℝ R y) =
      (fderiv ℝ F (axisWallChart A h y)).comp (axisWallChartDifferential A h y) :=
    (hdtarget.comp y hR.hasFDerivAt).unique ((hdF.comp y hdsource).congr_of_eventuallyEq heq)
  have hframe : (fun i => fderiv ℝ F (axisWallChart A h y) (axisWallChartFrame A h y i)) =
      (fun i => axisWallChartDifferential B k (R y) (fderiv ℝ R y (Pi.single i 1))) := by
    funext i
    exact congrArg (fun L : SectionCoordinates →L[ℝ] NormalizedState => L (Pi.single i 1)) hder.symm
  have H := normalizedSectionFlux_arrival_abs (axisWallChart_positive A hh y)
    (axisWallChart_constraint A hy) ht hτ (axisWallChartFrame A h y) (axisWallChartFrame_tangent A hy)
  have hvalue : axisWallChart B k (R y) =
      normalizedMaxCurve (axisWallChart A h y) t₀ (τ (axisWallChart A h y)) := by
    convert! heq.self_of_nhds using 1
  rw [← hvalue] at H
  rw [show (fun i => fderiv ℝ (fun x => normalizedMaxCurve x t₀ (τ x)) (axisWallChart A h y)
      (axisWallChartFrame A h y i)) = _ from hframe,
    axisWallChart_flux_linear B hk hRy, axisWallChart_flux A hh hy] at H
  exact H

theorem axisWall_coordinate_det_ne_zero (A B : NormalizedSymmetry) {h k t₀ : ℝ} {y : SectionCoordinates}
    {τ : NormalizedState → ℝ} {R : SectionCoordinates → SectionCoordinates}
    (hh : 0 < h) (hk : 0 < k) (hy : y ∈ mainWallChartDomain h)
    (hRy : R y ∈ mainWallChartDomain k)
    (ht : τ (axisWallChart A h y) ∈ normalizedMaxDomain (axisWallChart A h y) t₀)
    (hτ : DifferentiableAt ℝ τ (axisWallChart A h y)) (hR : DifferentiableAt ℝ R y)
    (heq : (fun v => axisWallChart B k (R v)) =ᶠ[𝓝 y]
      (fun v => normalizedMaxCurve (axisWallChart A h v) t₀ (τ (axisWallChart A h v)))) :
    (fderiv ℝ R y).det ≠ 0 := by
  have H := axisWall_coordinate_jacobian A B hh hk hy hRy ht hτ hR heq
  intro hz
  rw [hz, abs_zero, mul_zero] at H
  exact (ne_of_gt (mul_pos (Real.exp_pos _) (mainWallChartDensity_pos hh hy))) H.symm

/-- Every actual crossing between two axis charts has locally unique smooth event coordinates. -/
theorem exists_axisWall_coordinate_event (A B : NormalizedSymmetry) {h k t₀ t : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hk : 0 < k) (hy : y ∈ mainWallChartDomain h)
    (ht : t ∈ normalizedMaxDomain (axisWallChart A h y) t₀)
    (hlevel : B.map (normalizedMaxCurve (axisWallChart A h y) t₀ t) 2 = k)
    (hp : B.map (normalizedMaxCurve (axisWallChart A h y) t₀ t) 0 < 0) :
    ∃ (τ : NormalizedState → ℝ) (R : SectionCoordinates → SectionCoordinates),
      τ (axisWallChart A h y) = t ∧ ContDiffAt ℝ 1 τ (axisWallChart A h y) ∧
      ContDiffAt ℝ 1 R y ∧ R y = axisWallCoordinates B (normalizedMaxCurve (axisWallChart A h y) t₀ t) ∧
      (∀ᶠ v in 𝓝 y, v ∈ mainWallChartDomain h ∧
        τ (axisWallChart A h v) ∈ normalizedMaxDomain (axisWallChart A h v) t₀ ∧
        R v ∈ mainWallChartDomain k ∧
        axisWallChart B k (R v) = normalizedMaxCurve (axisWallChart A h v) t₀ (τ (axisWallChart A h v))) ∧
      (fderiv ℝ R y).det ≠ 0 ∧
      mainWallChartDensity k (R y) * |(fderiv ℝ R y).det| =
        Real.exp (∫ u in t₀..t,
          normalizedCorrectedDivergence (normalizedMaxCurve (axisWallChart A h y) t₀ u)) *
            mainWallChartDensity h y ∧
      (∀ᶠ z : SectionCoordinates × ℝ in 𝓝 (y, t),
        z.2 ∈ normalizedMaxDomain (axisWallChart A h z.1) t₀ ∧
        (B.map (normalizedMaxCurve (axisWallChart A h z.1) t₀ z.2) 2 = k ↔
          τ (axisWallChart A h z.1) = z.2)) := by
  obtain ⟨τ, hτ, hcτ, hhit, huniq, hcF⟩ := exists_normalized_axisWall_event B ht hk hlevel hp
  let F := fun x => normalizedMaxCurve x t₀ (τ x)
  let R := fun v => axisWallCoordinates B (F (axisWallChart A h v))
  have hF : F (axisWallChart A h y) = normalizedMaxCurve (axisWallChart A h y) t₀ t := by
    simp only [F, hτ]
  have hphysical := (maximalNormalizedSolution (axisWallChart A h y) t₀).physical
    (axisWallChart_positive A hh y) (axisWallChart_constraint A hy) ht
  have hpos : positiveWalls (F (axisWallChart A h y)) := by rw [hF]; exact hphysical.1
  have hcC := contDiffAt_axisWallChart A hy (1 : WithTop ℕ∞)
  have hcFC : ContDiffAt ℝ 1 (fun v => F (axisWallChart A h v)) y := hcF.comp y hcC
  have hcR : ContDiffAt ℝ 1 R y := by
    convert! (contDiffAt_axisWallCoordinates B hpos 1).comp y hcFC using 1
  have hneg : ∀ᶠ v in 𝓝 y, B.map (F (axisWallChart A h v)) 0 < 0 := by
    have hc : ContinuousAt (fun v => B.map (F (axisWallChart A h v)) 0) y :=
      (continuous_apply (0 : Fin 5)).continuousAt.comp (B.map.continuous.continuousAt.comp hcFC.continuousAt)
    exact hc.eventually_lt continuousAt_const (by rw [hF]; exact hp)
  have hlocal : ∀ᶠ v in 𝓝 y, v ∈ mainWallChartDomain h ∧
      τ (axisWallChart A h v) ∈ normalizedMaxDomain (axisWallChart A h v) t₀ ∧
      R v ∈ mainWallChartDomain k ∧ axisWallChart B k (R v) = F (axisWallChart A h v) := by
    filter_upwards [(isOpen_mainWallChartDomain h).mem_nhds hy,
      hcC.continuousAt.eventually hhit, hneg] with v hv he hn
    have hphys := (maximalNormalizedSolution (axisWallChart A h v) t₀).physical
      (axisWallChart_positive A hh v) (axisWallChart_constraint A hv) he.1
    exact ⟨hv, he.1, axisWallChart_coordinates B hphys.1 hphys.2 hn he.2⟩
  have heq : (fun v => axisWallChart B k (R v)) =ᶠ[𝓝 y] (fun v => F (axisWallChart A h v)) :=
    hlocal.mono (fun _ hv => hv.2.2.2)
  refine ⟨τ, R, hτ, hcτ, hcR, ?_, hlocal, ?_, ?_, ?_⟩
  · exact congrArg (axisWallCoordinates B) hF
  · exact axisWall_coordinate_det_ne_zero A B hh hk hy (hlocal.self_of_nhds.2.2.1)
      (hlocal.self_of_nhds.2.1) (hcτ.differentiableAt (by norm_num))
      (hcR.differentiableAt (by norm_num)) heq
  · have H := axisWall_coordinate_jacobian A B hh hk hy (hlocal.self_of_nhds.2.2.1)
      (hlocal.self_of_nhds.2.1) (hcτ.differentiableAt (by norm_num))
      (hcR.differentiableAt (by norm_num)) heq
    simpa only [hτ] using H
  · have hc : ContinuousAt (fun z : SectionCoordinates × ℝ => (axisWallChart A h z.1, z.2)) (y, t) := by
      convert! ((contDiffAt_axisWallChart A hy 1).continuousAt.comp
        (continuousAt_fst (p := (y, t)))).prodMk continuousAt_snd using 1
    exact hc.eventually huniq

end BianchiIX
