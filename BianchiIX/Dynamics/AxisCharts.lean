import BianchiIX.Dynamics.AxisPermutations
import BianchiIX.Dynamics.MainWallDensity

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def axisWallChart (A : NormalizedSymmetry) (h : ℝ) (y : SectionCoordinates) : NormalizedState :=
  A.map.symm (mainWallChart h y)

def axisWallCoordinates (A : NormalizedSymmetry) (x : NormalizedState) : SectionCoordinates :=
  mainWallCoordinates (A.map x)

theorem axisWallCoordinates_chart (A : NormalizedSymmetry) (h : ℝ) (y : SectionCoordinates) :
    axisWallCoordinates A (axisWallChart A h y) = y := by
  simp [axisWallCoordinates, axisWallChart, mainWallCoordinates_chart]

theorem axisWallChart_injective (A : NormalizedSymmetry) (h : ℝ) :
    Function.Injective (axisWallChart A h) :=
  Function.LeftInverse.injective (axisWallCoordinates_chart A h)

theorem axisWallChart_constraint (A : NormalizedSymmetry) {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) : stateConstraint (axisWallChart A h y) = 1 :=
  (A.symm.constraint (mainWallChart h y)).trans (mainWallChart_constraint hy)

theorem axisWallChart_positive (A : NormalizedSymmetry) {h : ℝ} (hh : 0 < h) (y : SectionCoordinates) :
    positiveWalls (axisWallChart A h y) :=
  (A.symm.positive (mainWallChart h y)).mpr (mainWallChart_positive hh y)

theorem axisWallChart_coordinates (A : NormalizedSymmetry) {h : ℝ} {x : NormalizedState}
    (hpos : positiveWalls x) (hcon : stateConstraint x = 1)
    (hp : A.map x 0 < 0) (hh : A.map x 2 = h) :
    axisWallCoordinates A x ∈ mainWallChartDomain h ∧ axisWallChart A h (axisWallCoordinates A x) = x := by
  have H := mainWallChart_coordinates ((A.positive x).mpr hpos) ((A.constraint x).trans hcon) hp hh
  refine ⟨H.1, ?_⟩
  unfold axisWallChart axisWallCoordinates
  rw [H.2, ContinuousLinearEquiv.symm_apply_apply]

theorem contDiffAt_axisWallChart (A : NormalizedSymmetry) {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) (n : WithTop ℕ∞) : ContDiffAt ℝ n (axisWallChart A h) y :=
  A.map.symm.contDiff.contDiffAt.comp y (contDiffAt_mainWallChart hy n)

theorem contDiffAt_axisWallCoordinates (A : NormalizedSymmetry) {x : NormalizedState}
    (hx : positiveWalls x) (n : WithTop ℕ∞) : ContDiffAt ℝ n (axisWallCoordinates A) x :=
  (contDiffAt_mainWallCoordinates ((A.positive x).mpr hx) n).comp x A.map.contDiff.contDiffAt

def axisWallChartDifferential (A : NormalizedSymmetry) (h : ℝ) (y : SectionCoordinates) :
    SectionCoordinates →L[ℝ] NormalizedState := fderiv ℝ (axisWallChart A h) y

theorem hasFDerivAt_axisWallChart (A : NormalizedSymmetry) {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) :
    HasFDerivAt (axisWallChart A h) (A.map.symm.toContinuousLinearMap.comp (mainWallChartDifferential h y)) y := by
  convert! A.map.symm.hasFDerivAt.comp y (hasFDerivAt_mainWallChart hy) using 1

theorem axisWallChartDifferential_eq (A : NormalizedSymmetry) {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) :
    axisWallChartDifferential A h y = A.map.symm.toContinuousLinearMap.comp (mainWallChartDifferential h y) :=
  (hasFDerivAt_axisWallChart A hy).fderiv

theorem axisWallChartDifferential_tangent (A : NormalizedSymmetry) {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) :
    (normalizedConstraintDifferential (axisWallChart A h y)).comp (axisWallChartDifferential A h y) = 0 := by
  have hd : HasFDerivAt (axisWallChart A h) (axisWallChartDifferential A h y) y :=
    ((contDiffAt_axisWallChart A hy 1).differentiableAt (by norm_num)).hasFDerivAt
  have H := (hasFDerivAt_stateConstraint (axisWallChart A h y)).comp y hd
  have heq : (fun _ : SectionCoordinates => (1 : ℝ)) =ᶠ[𝓝 y]
      (fun z => stateConstraint (axisWallChart A h z)) := by
    filter_upwards [(isOpen_mainWallChartDomain h).mem_nhds hy] with z hz
    exact (axisWallChart_constraint A hz).symm
  exact (H.congr_of_eventuallyEq heq).unique (hasFDerivAt_const 1 y)

def axisWallChartFrame (A : NormalizedSymmetry) (h : ℝ) (y : SectionCoordinates) : Fin 3 → NormalizedState :=
  fun i => axisWallChartDifferential A h y (Pi.single i 1)

theorem axisWallChart_signed_flux (A : NormalizedSymmetry) {h : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hy : y ∈ mainWallChartDomain h) :
    normalizedSectionFlux (axisWallChart A h y) (axisWallChartFrame A h y) = -mainWallChartDensity h y := by
  have H := A.symm.sectionFlux (mainWallChart h y) (mainWallChartFrame h y)
  have heq : axisWallChartFrame A h y = fun i => A.map.symm (mainWallChartFrame h y i) := by
    funext i
    rw [axisWallChartFrame, axisWallChartDifferential_eq A hy]
    rfl
  rw [heq]
  exact H.trans (mainWallChart_signed_flux hh hy)

theorem axisWallChart_flux_linear (A : NormalizedSymmetry) {h : ℝ} {y : SectionCoordinates}
    (hh : 0 < h) (hy : y ∈ mainWallChartDomain h) (L : SectionCoordinates →L[ℝ] SectionCoordinates) :
    |normalizedSectionFlux (axisWallChart A h y)
        (fun i => axisWallChartDifferential A h y (L (Pi.single i 1)))| =
      mainWallChartDensity h y * |L.det| := by
  rw [axisWallChartDifferential_eq A hy]
  have H := A.symm.sectionFlux (mainWallChart h y)
    (fun i => mainWallChartDifferential h y (L (Pi.single i 1)))
  exact (congrArg abs H).trans (mainWallChart_flux_linear hh hy L)

end BianchiIX
