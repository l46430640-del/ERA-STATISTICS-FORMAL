import BianchiIX.Dynamics.FlowTransport
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

abbrev SectionCoordinates := Fin 3 → ℝ

def mainWallRadicand (h : ℝ) (y : SectionCoordinates) : ℝ :=
  1 - y 0 ^ 2 - curvature h (Real.exp (-y 1)) (Real.exp (-y 2))

def mainWallChartDomain (h : ℝ) : Set SectionCoordinates := {y | 0 < mainWallRadicand h y}

def mainWallChart (h : ℝ) (y : SectionCoordinates) : NormalizedState :=
  ![-Real.sqrt (mainWallRadicand h y), y 0, h, Real.exp (-y 1), Real.exp (-y 2)]

def mainWallCoordinates (x : NormalizedState) : SectionCoordinates :=
  ![x 1, -Real.log (x 3), -Real.log (x 4)]

theorem contDiff_mainWallRadicand (h : ℝ) (n : WithTop ℕ∞) : ContDiff ℝ n (mainWallRadicand h) := by
  unfold mainWallRadicand curvature
  fun_prop

theorem isOpen_mainWallChartDomain (h : ℝ) : IsOpen (mainWallChartDomain h) :=
  isOpen_lt continuous_const (contDiff_mainWallRadicand h 1).continuous

theorem contDiffAt_mainWallChart {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) (n : WithTop ℕ∞) : ContDiffAt ℝ n (mainWallChart h) y := by
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact ((contDiff_mainWallRadicand h n).contDiffAt.sqrt (ne_of_gt hy)).neg
  · exact contDiffAt_apply ℝ ℝ (0 : Fin 3) y
  · exact contDiffAt_const
  · exact (contDiffAt_apply ℝ ℝ (1 : Fin 3) y).neg.exp
  · exact (contDiffAt_apply ℝ ℝ (2 : Fin 3) y).neg.exp

theorem mainWallChart_constraint {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) : stateConstraint (mainWallChart h y) = 1 := by
  have H := Real.sq_sqrt hy.le
  dsimp [stateConstraint, constraint, shearSq, mainWallChart]
  rw [neg_sq, H]
  unfold mainWallRadicand
  ring

theorem mainWallChart_negative {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) : mainWallChart h y 0 < 0 :=
  neg_neg_of_pos (Real.sqrt_pos.mpr hy)

theorem mainWallChart_positive {h : ℝ} (hh : 0 < h) (y : SectionCoordinates) :
    positiveWalls (mainWallChart h y) := ⟨hh, Real.exp_pos _, Real.exp_pos _⟩

theorem mainWallCoordinates_chart (h : ℝ) (y : SectionCoordinates) :
    mainWallCoordinates (mainWallChart h y) = y := by
  ext i
  fin_cases i <;> simp [mainWallCoordinates, mainWallChart]

theorem contDiffAt_mainWallCoordinates {x : NormalizedState} (hx : positiveWalls x)
    (n : WithTop ℕ∞) : ContDiffAt ℝ n mainWallCoordinates x := by
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact contDiffAt_apply ℝ ℝ (1 : Fin 5) x
  · exact ((contDiffAt_apply ℝ ℝ (3 : Fin 5) x).log (ne_of_gt hx.2.1)).neg
  · exact ((contDiffAt_apply ℝ ℝ (4 : Fin 5) x).log (ne_of_gt hx.2.2)).neg

theorem mainWallChart_injective (h : ℝ) : Function.Injective (mainWallChart h) :=
  Function.LeftInverse.injective (mainWallCoordinates_chart h)

theorem mainWallChart_coordinates {h : ℝ} {x : NormalizedState}
    (hpos : positiveWalls x) (hcon : stateConstraint x = 1) (hp : x 0 < 0) (hh : x 2 = h) :
    mainWallCoordinates x ∈ mainWallChartDomain h ∧ mainWallChart h (mainWallCoordinates x) = x := by
  have hr : mainWallRadicand h (mainWallCoordinates x) = x 0 ^ 2 := by
    change 1 - x 1 ^ 2 - curvature h (Real.exp (- -Real.log (x 3)))
      (Real.exp (- -Real.log (x 4))) = x 0 ^ 2
    rw [neg_neg, neg_neg, Real.exp_log hpos.2.1, Real.exp_log hpos.2.2]
    have H : x 0 ^ 2 + x 1 ^ 2 + curvature h (x 3) (x 4) = 1 := by
      simpa only [stateConstraint, constraint, shearSq, hh] using hcon
    linarith
  refine ⟨by change 0 < mainWallRadicand h (mainWallCoordinates x)
             rw [hr]; exact sq_pos_of_ne_zero (ne_of_lt hp), ?_⟩
  ext i
  fin_cases i
  · change -Real.sqrt (mainWallRadicand h (mainWallCoordinates x)) = x 0
    rw [hr, Real.sqrt_sq_eq_abs, abs_of_neg hp, neg_neg]
  · rfl
  · exact hh.symm
  · simp [mainWallChart, mainWallCoordinates, Real.exp_log hpos.2.1]
  · simp [mainWallChart, mainWallCoordinates, Real.exp_log hpos.2.2]

def mainWallChartDifferential (h : ℝ) (y : SectionCoordinates) : SectionCoordinates →L[ℝ] NormalizedState :=
  fderiv ℝ (mainWallChart h) y

theorem hasFDerivAt_mainWallChart {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) :
    HasFDerivAt (mainWallChart h) (mainWallChartDifferential h y) y :=
  ((contDiffAt_mainWallChart hy 1).differentiableAt (by norm_num)).hasFDerivAt

theorem mainWallChartDifferential_tangent {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) :
    (normalizedConstraintDifferential (mainWallChart h y)).comp (mainWallChartDifferential h y) = 0 := by
  have H := (hasFDerivAt_stateConstraint (mainWallChart h y)).comp y (hasFDerivAt_mainWallChart hy)
  have heq : (fun _ : SectionCoordinates => (1 : ℝ)) =ᶠ[𝓝 y]
      (fun z => stateConstraint (mainWallChart h z)) := by
    filter_upwards [(isOpen_mainWallChartDomain h).mem_nhds hy] with z hz
    exact (mainWallChart_constraint hz).symm
  exact (H.congr_of_eventuallyEq heq).unique (hasFDerivAt_const 1 y)

theorem mainWallChartDifferential_components {h : ℝ} {y : SectionCoordinates}
    (hy : y ∈ mainWallChartDomain h) (v : SectionCoordinates) :
    mainWallChartDifferential h y v 1 = v 0 ∧
      mainWallChartDifferential h y v 2 = 0 ∧
      mainWallChartDifferential h y v 3 = -Real.exp (-y 1) * v 1 ∧
      mainWallChartDifferential h y v 4 = -Real.exp (-y 2) * v 2 := by
  have H (i : Fin 5) := (hasFDerivAt_apply (𝕜 := ℝ) i (mainWallChart h y)).comp y
    (hasFDerivAt_mainWallChart hy)
  have h₁ := congrArg (fun L : SectionCoordinates →L[ℝ] ℝ => L v)
    ((H 1).unique (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) y))
  have h₂ := congrArg (fun L : SectionCoordinates →L[ℝ] ℝ => L v)
    ((H 2).unique (hasFDerivAt_const h y))
  have h₃ := congrArg (fun L : SectionCoordinates →L[ℝ] ℝ => L v)
    ((H 3).unique (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) y).neg.exp)
  have h₄ := congrArg (fun L : SectionCoordinates →L[ℝ] ℝ => L v)
    ((H 4).unique (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) y).neg.exp)
  exact ⟨h₁, h₂, by simpa using h₃, by simpa using h₄⟩

end BianchiIX
