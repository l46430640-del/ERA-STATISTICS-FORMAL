import BianchiIX.Algebra.Flow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp

noncomputable section

namespace BianchiIX

def restartReferenceRoot (n : ℝ) : ℝ := Real.sqrt (1 - n ^ 2)

def restartShearFactor (n : ℝ) : ℝ := 3 / (2 + restartReferenceRoot n)

def restartWallFactor (n : ℝ) : ℝ :=
  9 * (1 + restartReferenceRoot n) / (2 * (2 + restartReferenceRoot n) ^ 2)

def restartShearCoupling (n : ℝ) : ℝ :=
  3 * Real.sqrt 3 * n / (2 + restartReferenceRoot n) ^ 2

def restartReferenceStrongRate (n : ℝ) : ℝ := n ^ 2 - 1 - 2 * restartReferenceRoot n

def restartReferenceWallRate (n : ℝ) : ℝ := n ^ 2 - 1 + restartReferenceRoot n

/-- The square of the transported radial phase, before the normalization by three. -/
def restartQuadratic (n s v : ℝ) : ℝ :=
  (restartShearFactor n * s + restartShearCoupling n * v) ^ 2 +
    (restartWallFactor n * v) ^ 2

def restartQuadraticStrongDerivative (n s v : ℝ) : ℝ :=
  2 * (restartShearFactor n * s + restartShearCoupling n * v) *
      (deriv restartShearFactor n * s + deriv restartShearCoupling n * v) +
    2 * restartWallFactor n * deriv restartWallFactor n * v ^ 2

def restartRotationDefect (n s v : ℝ) : ℝ :=
  restartShearFactor n * restartShearCoupling n * (s ^ 2 - v ^ 2) +
    (restartShearCoupling n ^ 2 + restartWallFactor n ^ 2 - restartShearFactor n ^ 2) * s * v

theorem restartReferenceRoot_pos {n : ℝ} (hn : n ^ 2 < 1) : 0 < restartReferenceRoot n :=
  Real.sqrt_pos.mpr (sub_pos.mpr hn)

theorem restartReferenceRoot_sq {n : ℝ} (hn : n ^ 2 ≤ 1) :
    restartReferenceRoot n ^ 2 = 1 - n ^ 2 := Real.sq_sqrt (sub_nonneg.mpr hn)

theorem hasDerivAt_restartReferenceRoot {n : ℝ} (hn : n ^ 2 < 1) :
    HasDerivAt restartReferenceRoot (-n / restartReferenceRoot n) n := by
  convert! (((hasDerivAt_id' n).pow 2).const_sub 1).sqrt (sub_pos.mpr hn).ne' using 1
  simp only [Pi.pow_apply]
  dsimp only [restartReferenceRoot]
  ring

theorem hasDerivAt_restartShearFactor {n : ℝ} (hn : n ^ 2 < 1) :
    HasDerivAt restartShearFactor
      (3 * n / (restartReferenceRoot n * (2 + restartReferenceRoot n) ^ 2)) n := by
  have hz := restartReferenceRoot_pos hn
  have hd : 2 + restartReferenceRoot n ≠ 0 := by positivity
  convert! (hasDerivAt_const n (3 : ℝ)).div
    ((hasDerivAt_restartReferenceRoot hn).const_add 2) hd using 1
  field_simp
  ring

theorem hasDerivAt_restartWallFactor {n : ℝ} (hn : n ^ 2 < 1) :
    HasDerivAt restartWallFactor (9 * n / (2 * (2 + restartReferenceRoot n) ^ 3)) n := by
  have hz := restartReferenceRoot_pos hn
  have hd : 2 + restartReferenceRoot n ≠ 0 := by positivity
  have hroot := hasDerivAt_restartReferenceRoot hn
  convert! ((hroot.const_add 1).const_mul 9).div
    (((hroot.const_add 2).pow 2).const_mul 2)
    (by change 2 * (2 + restartReferenceRoot n) ^ 2 ≠ 0; positivity) using 1
  simp only [Pi.pow_apply]
  field_simp
  ring

theorem hasDerivAt_restartShearCoupling {n : ℝ} (hn : n ^ 2 < 1) :
    HasDerivAt restartShearCoupling
      (3 * Real.sqrt 3 * (restartReferenceRoot n * (2 + restartReferenceRoot n) + 2 * n ^ 2) /
        (restartReferenceRoot n * (2 + restartReferenceRoot n) ^ 3)) n := by
  have hz := restartReferenceRoot_pos hn
  have hd : 2 + restartReferenceRoot n ≠ 0 := by positivity
  convert! ((hasDerivAt_id' n).const_mul (3 * Real.sqrt 3)).div
    (((hasDerivAt_restartReferenceRoot hn).const_add 2).pow 2) (pow_ne_zero 2 hd) using 1
  simp only [Pi.pow_apply]
  field_simp
  ring

/-- The stronger first-order identity underlying (E.8): the transported reference vector is constant. -/
theorem restart_transport_cancellation {n : ℝ} (hn : n ^ 2 < 1) :
    n * restartReferenceStrongRate n * deriv restartShearFactor n + restartShearFactor n * n ^ 2 = 0 ∧
    n * restartReferenceStrongRate n * deriv restartWallFactor n +
      restartWallFactor n * restartReferenceWallRate n = 0 ∧
    n * restartReferenceStrongRate n * deriv restartShearCoupling n +
      restartShearFactor n * Real.sqrt 3 * n +
      restartShearCoupling n * restartReferenceWallRate n = 0 := by
  have hz := restartReferenceRoot_pos hn
  have hd : 2 + restartReferenceRoot n ≠ 0 := by positivity
  have hn2 : n ^ 2 = 1 - restartReferenceRoot n ^ 2 := by
    linarith only [restartReferenceRoot_sq hn.le]
  have hF : restartReferenceStrongRate n = -restartReferenceRoot n * (2 + restartReferenceRoot n) := by
    dsimp only [restartReferenceStrongRate]
    rw [hn2]
    ring
  have hb : restartReferenceWallRate n = restartReferenceRoot n * (1 - restartReferenceRoot n) := by
    dsimp only [restartReferenceWallRate]
    rw [hn2]
    ring
  rw [(hasDerivAt_restartShearFactor hn).deriv, (hasDerivAt_restartWallFactor hn).deriv,
    (hasDerivAt_restartShearCoupling hn).deriv, hF, hb]
  dsimp only [restartShearFactor, restartWallFactor, restartShearCoupling]
  constructor
  · field_simp
    ring
  constructor
  · field_simp
    linear_combination -9 * restartReferenceRoot n * (restartReferenceRoot_sq hn.le)
  · field_simp
    linear_combination -6 * Real.sqrt 3 * n * (restartReferenceRoot_sq hn.le)

/-- Equation (E.8) evaluated on an arbitrary center vector. -/
theorem restartQuadratic_reference_cancellation {n : ℝ} (hn : n ^ 2 < 1) (s v : ℝ) :
    n * restartReferenceStrongRate n * restartQuadraticStrongDerivative n s v +
      2 * (restartShearFactor n * s + restartShearCoupling n * v) *
        (restartShearFactor n * (n ^ 2 * s + Real.sqrt 3 * n * v) +
          restartShearCoupling n * restartReferenceWallRate n * v) +
      2 * restartWallFactor n ^ 2 * restartReferenceWallRate n * v ^ 2 = 0 := by
  obtain ⟨HA, HC, HK⟩ := restart_transport_cancellation hn
  dsimp only [restartQuadraticStrongDerivative]
  linear_combination
    2 * (restartShearFactor n * s + restartShearCoupling n * v) * s * HA +
    2 * restartWallFactor n * v ^ 2 * HC +
    2 * (restartShearFactor n * s + restartShearCoupling n * v) * v * HK

theorem restart_coefficients_zero :
    restartShearFactor 0 = 1 ∧ restartWallFactor 0 = 1 ∧ restartShearCoupling 0 = 0 := by
  norm_num [restartShearFactor, restartWallFactor, restartShearCoupling, restartReferenceRoot]

theorem restartQuadratic_zero (s v : ℝ) : restartQuadratic 0 s v = s ^ 2 + v ^ 2 := by
  simp only [restartQuadratic, restart_coefficients_zero.1, restart_coefficients_zero.2.1,
    restart_coefficients_zero.2.2, one_mul, zero_mul, add_zero]

theorem restartRotationDefect_zero (s v : ℝ) : restartRotationDefect 0 s v = 0 := by
  simp [restartRotationDefect, restart_coefficients_zero.1, restart_coefficients_zero.2.1,
    restart_coefficients_zero.2.2]

theorem contDiffAt_restart_coefficients {n : ℝ} (hn : n ^ 2 < 1) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k restartShearFactor n ∧ ContDiffAt ℝ k restartWallFactor n ∧
      ContDiffAt ℝ k restartShearCoupling n := by
  have hr : ContDiffAt ℝ k restartReferenceRoot n :=
    (contDiffAt_const.sub (contDiffAt_id.pow 2)).sqrt (sub_pos.mpr hn).ne'
  have hd : 2 + restartReferenceRoot n ≠ 0 := by positivity [restartReferenceRoot_pos hn]
  refine ⟨contDiffAt_const.div (contDiffAt_const.add hr) hd, ?_, ?_⟩
  · exact (contDiffAt_const.mul (contDiffAt_const.add hr)).div
      (contDiffAt_const.mul ((contDiffAt_const.add hr).pow 2)) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hd))
  · exact (contDiffAt_const.mul contDiffAt_id).div ((contDiffAt_const.add hr).pow 2) (pow_ne_zero 2 hd)

theorem restart_coefficients_pos {n : ℝ} (hn : n ^ 2 < 1) :
    0 < restartShearFactor n ∧ 0 < restartWallFactor n := by
  have hz := restartReferenceRoot_pos hn
  constructor <;> dsimp only [restartShearFactor, restartWallFactor] <;> positivity

theorem restartQuadratic_pos {n s v : ℝ} (hn : n ^ 2 < 1) (hsv : s ≠ 0 ∨ v ≠ 0) :
    0 < restartQuadratic n s v := by
  obtain ⟨ha, hc⟩ := restart_coefficients_pos hn
  rcases eq_or_ne v 0 with hv | hv
  · have hs : s ≠ 0 := hsv.resolve_right (by simp only [hv, ne_eq, not_true_eq_false, not_false_eq_true])
    simpa only [restartQuadratic, hv, mul_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0)] using
      sq_pos_of_ne_zero (mul_ne_zero ha.ne' hs)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (mul_ne_zero hc.ne' hv))

end BianchiIX
