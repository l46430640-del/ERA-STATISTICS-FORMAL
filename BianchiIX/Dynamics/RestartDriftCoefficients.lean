import BianchiIX.Dynamics.RestartQuadratic
import BianchiIX.Dynamics.RestartStrongCoordinates
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section

namespace BianchiIX

abbrev RestartRadialState := ℝ × RestartCenterState

def restartGramCoefficients (n : ℝ) : Fin 3 → ℝ :=
  ![restartShearFactor n ^ 2, 2 * restartShearFactor n * restartShearCoupling n,
    restartShearCoupling n ^ 2 + restartWallFactor n ^ 2]

def restartRootCoefficients (n : ℝ) : Fin 3 → ℝ :=
  ![0, restartShearFactor n * restartShearCoupling n,
    restartShearCoupling n ^ 2 + restartWallFactor n ^ 2]

def restartRotationCoefficients (n : ℝ) : Fin 3 → ℝ :=
  ![restartShearFactor n * restartShearCoupling n,
    restartShearCoupling n ^ 2 + restartWallFactor n ^ 2 - restartShearFactor n ^ 2,
    -(restartShearFactor n * restartShearCoupling n)]

def restartRadialCurvatureDifference (p : RestartRadialState) : ℝ :=
  (p.2 1 - p.2 2) ^ 2 - 2 * p.1 * (p.2 1 + p.2 2)

def restartRadialRootDifference (p : RestartRadialState) : ℝ :=
  Real.sqrt (restartSectionRadicand p.1 p.2) - restartReferenceRoot p.1

/-- Coefficients of the exact radial drift in the monomials s^2, s v, v^2. -/
def restartRadialDriftCoefficients (p : RestartRadialState) : Fin 3 → ℝ :=
  (p.1 * (restartRadialCurvatureDifference p - 2 * restartRadialRootDifference p)) •
      deriv restartGramCoefficients p.1 +
    (2 * restartRadialCurvatureDifference p) • restartGramCoefficients p.1 +
    (2 * restartRadialRootDifference p) • restartRootCoefficients p.1 +
    (2 * Real.sqrt 3 * (p.2 1 + p.2 2)) • restartRotationCoefficients p.1

theorem contDiffAt_restartGramCoefficients {n : ℝ} (hn : n ^ 2 < 1) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k restartGramCoefficients n ∧
      ContDiffAt ℝ k restartRootCoefficients n ∧ ContDiffAt ℝ k restartRotationCoefficients n := by
  obtain ⟨ha, hc, hk⟩ := contDiffAt_restart_coefficients hn k
  constructor
  · rw [contDiffAt_pi]
    intro i
    fin_cases i <;> dsimp [restartGramCoefficients] <;> fun_prop
  constructor <;> rw [contDiffAt_pi] <;> intro i <;>
    fin_cases i <;> dsimp [restartRootCoefficients, restartRotationCoefficients] <;> fun_prop

theorem deriv_restartGramCoefficients {n : ℝ} (hn : n ^ 2 < 1) :
    deriv restartGramCoefficients n =
      ![2 * restartShearFactor n * deriv restartShearFactor n,
        2 * (deriv restartShearFactor n * restartShearCoupling n +
          restartShearFactor n * deriv restartShearCoupling n),
        2 * (restartShearCoupling n * deriv restartShearCoupling n +
          restartWallFactor n * deriv restartWallFactor n)] := by
  have ha := (hasDerivAt_restartShearFactor hn).differentiableAt.hasDerivAt
  have hc := (hasDerivAt_restartWallFactor hn).differentiableAt.hasDerivAt
  have hk := (hasDerivAt_restartShearCoupling hn).differentiableAt.hasDerivAt
  apply HasDerivAt.deriv
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · change HasDerivAt (fun m => restartShearFactor m ^ 2)
      (2 * restartShearFactor n * deriv restartShearFactor n) n
    convert! ha.pow 2 using 1
    ring
  · change HasDerivAt (fun m => 2 * restartShearFactor m * restartShearCoupling m)
      (2 * (deriv restartShearFactor n * restartShearCoupling n +
        restartShearFactor n * deriv restartShearCoupling n)) n
    convert! (ha.const_mul 2).mul hk using 1
    ring
  · change HasDerivAt (fun m => restartShearCoupling m ^ 2 + restartWallFactor m ^ 2)
      (2 * (restartShearCoupling n * deriv restartShearCoupling n +
        restartWallFactor n * deriv restartWallFactor n)) n
    convert! (hk.pow 2).add (hc.pow 2) using 1
    ring

theorem restartRadialDriftCoefficients_axis (n : ℝ) : restartRadialDriftCoefficients (n, 0) = 0 := by
  simp [restartRadialDriftCoefficients, restartRadialCurvatureDifference, restartRadialRootDifference,
    restartSectionRadicand, curvature, restartReferenceRoot]

theorem restartRotationCoefficients_zero : restartRotationCoefficients 0 = 0 := by
  ext i
  fin_cases i <;> simp [restartRotationCoefficients, restart_coefficients_zero.1,
    restart_coefficients_zero.2.1, restart_coefficients_zero.2.2]

theorem contDiffAt_restartRadialDriftCoefficients {p : RestartRadialState}
    (hn : p.1 ^ 2 < 1) (hr : 0 < restartSectionRadicand p.1 p.2) :
    ContDiffAt ℝ 3 restartRadialDriftCoefficients p := by
  have hQ : ContDiff ℝ 3 restartRadialCurvatureDifference := by
    unfold restartRadialCurvatureDifference
    fun_prop
  have hrad : ContDiff ℝ 3 (fun p : RestartRadialState => restartSectionRadicand p.1 p.2) := by
    unfold restartSectionRadicand curvature
    fun_prop
  have hroot : ContDiffAt ℝ 3 (fun p : RestartRadialState => restartReferenceRoot p.1) p :=
    (contDiffAt_const.sub (contDiffAt_fst.pow 2)).sqrt (sub_pos.mpr hn).ne'
  have hdiff : ContDiffAt ℝ 3 restartRadialRootDifference p := (hrad.contDiffAt.sqrt hr.ne').sub hroot
  have hG := (contDiffAt_restartGramCoefficients hn 3).1.comp p contDiffAt_fst
  have hH := (contDiffAt_restartGramCoefficients hn 3).2.1.comp p contDiffAt_fst
  have hR := (contDiffAt_restartGramCoefficients hn 3).2.2.comp p contDiffAt_fst
  have hG' := (((contDiffAt_restartGramCoefficients hn 4).1).derivWithin
    (by norm_num : (3 : WithTop ℕ∞) + 1 ≤ 4)).comp p contDiffAt_fst
  unfold restartRadialDriftCoefficients
  fun_prop

theorem hasFDerivAt_restartRadialDifferences_zero :
    HasFDerivAt (𝕜 := ℝ) restartRadialCurvatureDifference 0 0 ∧
      HasFDerivAt (𝕜 := ℝ) restartRadialRootDifference 0 0 := by
  have hn : DifferentiableAt ℝ (fun p : RestartRadialState => p.1) 0 := by fun_prop
  have hp (i : Fin 3) : DifferentiableAt ℝ (fun p : RestartRadialState => p.2 i) 0 := by fun_prop
  have hQ : HasFDerivAt (𝕜 := ℝ) restartRadialCurvatureDifference 0 0 := by
    convert! (((hp 1).hasFDerivAt.sub (hp 2).hasFDerivAt).pow 2).sub
      ((hn.hasFDerivAt.mul ((hp 1).hasFDerivAt.add (hp 2).hasFDerivAt)).const_mul 2) using 1
    · ext p
      dsimp [restartRadialCurvatureDifference]
      ring
    · simp
  have hrad : HasFDerivAt (𝕜 := ℝ)
      (fun p : RestartRadialState => restartSectionRadicand p.1 p.2) 0 0 := by
    have H := (((hp 0).hasFDerivAt.pow 2).const_sub 1).sub ((hn.hasFDerivAt.pow 2).add hQ)
    convert! H using 1
    · ext p
      dsimp [restartSectionRadicand, restartRadialCurvatureDifference, curvature]
      ring
    · simp
  have hroot0 : HasFDerivAt (𝕜 := ℝ) (fun p : RestartRadialState => restartReferenceRoot p.1) 0 0 := by
    convert! ((hn.hasFDerivAt.pow 2).const_sub 1).sqrt (by norm_num : (1 : ℝ) - (0 : ℝ) ^ 2 ≠ 0) using 1
    simp
  refine ⟨hQ, ?_⟩
  convert! (hrad.sqrt (by norm_num [restartSectionRadicand, curvature])).sub hroot0 using 1
  simp

theorem restartRadialDriftCoefficients_fderiv_zero : fderiv ℝ restartRadialDriftCoefficients 0 = 0 := by
  obtain ⟨hQ, hξ⟩ := hasFDerivAt_restartRadialDifferences_zero
  have hn : HasFDerivAt (fun p : RestartRadialState => p.1) (ContinuousLinearMap.fst ℝ ℝ RestartCenterState) 0 :=
    hasFDerivAt_fst
  have hp (i : Fin 3) : DifferentiableAt ℝ (fun p : RestartRadialState => p.2 i) 0 := by fun_prop
  have hg := contDiffAt_restartGramCoefficients (by norm_num : (0 : ℝ) ^ 2 < 1) 2
  have hG := (hg.1.comp (0 : RestartRadialState) contDiffAt_fst).differentiableAt (by norm_num)
  have hH := (hg.2.1.comp (0 : RestartRadialState) contDiffAt_fst).differentiableAt (by norm_num)
  have hR := (hg.2.2.comp (0 : RestartRadialState) contDiffAt_fst).differentiableAt (by norm_num)
  have hG' := ((hg.1.derivWithin (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).comp
    (0 : RestartRadialState) contDiffAt_fst).differentiableAt (by norm_num)
  have H := (((hn.mul (hQ.sub (hξ.const_mul 2))).smul hG'.hasFDerivAt).add
    ((hQ.const_mul 2).smul hG.hasFDerivAt) |>.add
    ((hξ.const_mul 2).smul hH.hasFDerivAt)).add
    ((((hp 1).hasFDerivAt.add (hp 2).hasFDerivAt).const_mul (2 * Real.sqrt 3)).smul hR.hasFDerivAt)
  have HD : HasFDerivAt (𝕜 := ℝ) restartRadialDriftCoefficients 0 0 := by
    convert! H using 1
    simp [restartRadialCurvatureDifference, restartRadialRootDifference, restartSectionRadicand,
      curvature, restartReferenceRoot, restartRotationCoefficients_zero]
  exact HD.fderiv

end BianchiIX
