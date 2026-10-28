import BianchiIX.Algebra.Projective
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp

noncomputable section

namespace BianchiIX

def coreRadius (m v : ℝ) : ℝ := Real.sqrt (coreEnergy m v)

def coreAngle (m v : ℝ) : ℝ := Real.arsinh ((1 - m) / v)

def coreClockFactor (r u w : ℝ) : ℝ := 1 - (u - w) ^ 2 / r ^ 2

theorem coreRadius_sq (m v : ℝ) : coreRadius m v ^ 2 = coreEnergy m v :=
  Real.sq_sqrt (by unfold coreEnergy; positivity)

theorem coreRadius_pos {m v : ℝ} (hv : 0 < v) : 0 < coreRadius m v := by
  apply Real.sqrt_pos.mpr
  unfold coreEnergy
  positivity

theorem coreAngle_sqrt {m v : ℝ} (hv : 0 < v) :
    Real.sqrt (1 + ((1 - m) / v) ^ 2) = coreRadius m v / v := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (div_nonneg (coreRadius_pos hv).le hv.le)).mpr
  simp only [div_pow, coreRadius_sq]
  unfold coreEnergy
  field_simp
  ring

theorem cosh_coreAngle {m v : ℝ} (hv : 0 < v) :
    Real.cosh (coreAngle m v) = coreRadius m v / v := by
  rw [coreAngle, Real.cosh_arsinh, coreAngle_sqrt hv]

theorem tanh_coreAngle {m v : ℝ} (hv : 0 < v) :
    Real.tanh (coreAngle m v) = (1 - m) / coreRadius m v := by
  rw [coreAngle, Real.tanh_arsinh, coreAngle_sqrt hv]
  field_simp

theorem coreAngle_coordinates {m v : ℝ} (hv : 0 < v) :
    coreRadius m v / Real.cosh (coreAngle m v) = v ∧
      1 - coreRadius m v * Real.tanh (coreAngle m v) = m := by
  have hr := ne_of_gt (coreRadius_pos (m := m) hv)
  rw [cosh_coreAngle hv, tanh_coreAngle hv]
  constructor
  · field_simp
  · field_simp
    ring

theorem coreRadius_directional {m u v w : ℝ} (hv : 0 < v) :
    ((m - 1) * phaseVelocity m u v w + v * activeVelocity m u v w) / coreRadius m v =
      -coupling u v w * coreRadius m v + (m - 1) / coreRadius m v * (u - w) ^ 2 := by
  have hr := ne_of_gt (coreRadius_pos (m := m) hv)
  apply (div_eq_iff hr).mpr
  field_simp
  rw [coreRadius_sq]
  unfold phaseVelocity activeVelocity coupling coreEnergy
  ring

theorem coreAngle_directional {m u v w : ℝ} (hv : 0 < v) :
    ((m - 1) * activeVelocity m u v w - v * phaseVelocity m u v w) /
        (coreRadius m v * v) = coreRadius m v * coreClockFactor (coreRadius m v) u w := by
  have hr := ne_of_gt (coreRadius_pos (m := m) hv)
  have hv0 := ne_of_gt hv
  unfold coreClockFactor
  field_simp
  have he := coreRadius_sq m v
  unfold coreEnergy at he
  unfold phaseVelocity activeVelocity coupling
  nlinarith [he]

theorem hasDerivAt_coreRadius {m v : ℝ → ℝ} {m' v' t : ℝ}
    (hm : HasDerivAt m m' t) (hdv : HasDerivAt v v' t) (hv : 0 < v t) :
    HasDerivAt (fun s => coreRadius (m s) (v s))
      (((m t - 1) * m' + v t * v') / coreRadius (m t) (v t)) t := by
  have he : coreEnergy (m t) (v t) ≠ 0 := by unfold coreEnergy; positivity
  have hd := (((hm.sub_const 1).pow 2).add (hdv.pow 2)).sqrt he
  convert! hd using 1
  dsimp [coreRadius, coreEnergy]
  ring

theorem hasDerivAt_coreAngle {m v : ℝ → ℝ} {m' v' t : ℝ}
    (hm : HasDerivAt m m' t) (hdv : HasDerivAt v v' t) (hv : 0 < v t) :
    HasDerivAt (fun s => coreAngle (m s) (v s))
      (((m t - 1) * v' - v t * m') / (coreRadius (m t) (v t) * v t)) t := by
  have hd := ((hm.const_sub 1).div hdv (ne_of_gt hv)).arsinh
  convert! hd using 1
  simp only [Pi.div_apply]
  rw [coreAngle_sqrt hv]
  have hr := ne_of_gt (coreRadius_pos (m := m t) hv)
  simp only [smul_eq_mul]
  field_simp
  ring

end BianchiIX
