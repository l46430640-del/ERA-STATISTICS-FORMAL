import BianchiIX.Dynamics.RestartEquations
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

namespace BianchiIX

abbrev RestartState := Fin 4 → ℝ

def restartRadicand (x : RestartState) : ℝ :=
  1 - x 1 ^ 2 - curvature (x 0) (x 2) (x 3)

def restartCompactRoot (x : RestartState) : ℝ := Real.sqrt (restartRadicand x)

def restartCompactWeakRate (ε : ℝ) (x : RestartState) : ℝ :=
  curvature (x 0) (x 2) (x 3) - 1 + restartCompactRoot x + ε * Real.sqrt 3 * x 1

/-- The logarithmic strong-wall rate extends smoothly to zero strong wall. -/
def restartCompactField (x : RestartState) : RestartState :=
  ![curvature (x 0) (x 2) (x 3) - 1 - 2 * restartCompactRoot x,
    shearMinus (x 1) (x 0) (x 2) (x 3),
    x 2 * restartCompactWeakRate 1 x, x 3 * restartCompactWeakRate (-1) x]

def restartExpCoordinates (y : RestartState) : RestartState := ![Real.exp (y 0), y 1, y 2, y 3]

def restartMixedField : RestartState → RestartState := restartCompactField ∘ restartExpCoordinates

def restartMixedCoordinates (x : NormalizedState) : RestartState := ![Real.log (x 2), x 1, x 3, x 4]

theorem contDiff_restartRadicand (k : WithTop ℕ∞) : ContDiff ℝ k restartRadicand := by
  unfold restartRadicand curvature
  fun_prop

theorem contDiffAt_restartCompactRoot {x : RestartState} (hx : 0 < restartRadicand x)
    (k : WithTop ℕ∞) : ContDiffAt ℝ k restartCompactRoot x :=
  (contDiff_restartRadicand k).contDiffAt.sqrt hx.ne'

theorem contDiffAt_restartCompactField {x : RestartState} (hx : 0 < restartRadicand x)
    (k : WithTop ℕ∞) : ContDiffAt ℝ k restartCompactField x := by
  have hr := contDiffAt_restartCompactRoot hx k
  rw [contDiffAt_pi]
  intro i
  fin_cases i <;> dsimp [restartCompactField, restartCompactWeakRate, shearMinus, curvature] <;> fun_prop

theorem contDiff_restartExpCoordinates (k : WithTop ℕ∞) : ContDiff ℝ k restartExpCoordinates := by
  rw [contDiff_pi]
  intro i
  fin_cases i <;> dsimp [restartExpCoordinates] <;> fun_prop

theorem contDiffAt_restartMixedField {y : RestartState}
    (hy : 0 < restartRadicand (restartExpCoordinates y)) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k restartMixedField y :=
  (contDiffAt_restartCompactField hy k).comp y (contDiff_restartExpCoordinates k).contDiffAt

/-- The four compactified rates have no first-order term at the all-zero wall and center state. -/
theorem hasFDerivAt_restartCompactField_zero : HasFDerivAt (𝕜 := ℝ) restartCompactField 0 0 := by
  have hp (i : Fin 4) := hasFDerivAt_apply (𝕜 := ℝ) i (0 : RestartState)
  have hQ : HasFDerivAt (𝕜 := ℝ) (fun x : RestartState => curvature (x 0) (x 2) (x 3)) 0 0 := by
    have H := (((hp 0).pow 2).add ((hp 2).pow 2) |>.add ((hp 3).pow 2)).sub
      ((((hp 0).mul (hp 2)).add ((hp 2).mul (hp 3)) |>.add ((hp 3).mul (hp 0))).const_mul 2)
    convert! H using 1
    simp
  have hR : HasFDerivAt (𝕜 := ℝ) restartRadicand 0 0 := by
    convert! (((hp 1).pow 2).const_sub 1).sub hQ using 1
    simp
  have hr : HasFDerivAt (𝕜 := ℝ) restartCompactRoot 0 0 := by
    convert! hR.sqrt (by norm_num [restartRadicand, curvature] : restartRadicand 0 ≠ 0) using 1
    simp
  have hH : HasFDerivAt (𝕜 := ℝ) (fun x : RestartState => -(x 2) ^ 2 + (x 3) ^ 2 + x 0 * x 2 - x 0 * x 3) 0 0 := by
    convert! ((((hp 2).pow 2).neg.add ((hp 3).pow 2)).add ((hp 0).mul (hp 2))).sub
      ((hp 0).mul (hp 3)) using 1
    simp
  have hg (ε : ℝ) := ((hQ.sub_const 1).add hr).add ((hp 1).const_mul (ε * Real.sqrt 3))
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · convert! (hQ.sub_const 1).sub (hr.const_mul 2) using 1
    simp
  · convert! (hQ.mul (hp 1)).add (hH.const_mul (Real.sqrt 3)) using 1
    simp [curvature]
  · convert! (hp 2).mul (hg 1) using 1
    simp [curvature, restartCompactRoot, restartRadicand]
  · convert! (hp 3).mul (hg (-1)) using 1
    simp [curvature, restartCompactRoot, restartRadicand]

theorem restartCompactField_fderiv_zero : fderiv ℝ restartCompactField 0 = 0 :=
  hasFDerivAt_restartCompactField_zero.fderiv

theorem restartMixedField_coordinates {x : NormalizedState}
    (hc : stateConstraint x = 1) (hp : x 0 < 0) (hn : 0 < x 2) :
    restartMixedField (restartMixedCoordinates x) =
      ![rateOne (x 0) (x 1), shearMinus (x 1) (x 2) (x 3) (x 4),
        rateTwo (x 0) (x 1) * x 3, rateThree (x 0) (x 1) * x 4] := by
  have hroot := restart_negative_branch_root hc hp
  have hq : curvature (x 2) (x 3) (x 4) = 1 - shearSq (x 0) (x 1) := by
    dsimp only [stateConstraint, constraint] at hc
    linarith only [hc]
  ext i
  fin_cases i <;>
    simp [restartMixedField, restartMixedCoordinates, restartExpCoordinates, restartCompactField,
      restartCompactWeakRate, restartCompactRoot, restartRadicand, Real.exp_log hn] <;>
    rw [← hroot, hq] <;> dsimp only [rateOne, rateTwo, rateThree] <;> ring

/-- Exact original-time evolution in the mixed coordinates, with no lower bound on either weak wall. -/
theorem hasDerivAt_restartMixedCoordinates {x : ℝ → NormalizedState} {t : ℝ}
    (hx : HasDerivAt x (normalizedField (x t)) t) (hc : stateConstraint (x t) = 1)
    (hp : x t 0 < 0) (hn : 0 < x t 2) :
    HasDerivAt (fun r => restartMixedCoordinates (x r))
      (restartMixedField (restartMixedCoordinates (x t))) t := by
  rw [restartMixedField_coordinates hc hp hn]
  obtain ⟨_, hs, hN, ha, hb⟩ := hasDerivAt_normalized_components hx
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · change HasDerivAt (fun r => Real.log (x r 2)) (rateOne (x t 0) (x t 1)) t
    convert! hN.log hn.ne' using 1
    simp only [mul_div_cancel_right₀ _ hn.ne']
  · exact hs
  · exact ha
  · exact hb

end BianchiIX
