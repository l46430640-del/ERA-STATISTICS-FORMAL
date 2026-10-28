import BianchiIX.Dynamics.RestartRadialObservable
import BianchiIX.Dynamics.ShearTailVariationBounds

noncomputable section

namespace BianchiIX

def shearTailRadius (z : NormalizedState) : ℝ :=
  restartRadialNorm (restartCenterProjection z)

def shearTailRadiusDifferential (z v : NormalizedState) : ℝ :=
  (z 1 * v 1 + (z 3 - z 4) * (v 3 - v 4)) / shearTailRadius z

def shearTailRadiusRate (z : NormalizedState) : ℝ :=
  curvature (z 2) (z 3) (z 4) * shearTailRadius z -
    (1 + z 0) * (z 3 - z 4) ^ 2 / shearTailRadius z +
      Real.sqrt 3 * z 2 * z 1 * (z 3 - z 4) / shearTailRadius z

def shearTailRadiusEnergy (z : NormalizedState) : ℝ :=
  z 2 + z 3 ^ 2 + z 4 ^ 2

theorem shearTailRadius_sq (z : NormalizedState) :
    shearTailRadius z ^ 2 = z 1 ^ 2 + (z 3 - z 4) ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem shearTailRadius_pos {z : NormalizedState} (hs : z 1 ≠ 0) : 0 < shearTailRadius z :=
  Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hs) (sq_nonneg _))

theorem contDiffAt_shearTailRadius {z : NormalizedState} (hs : z 1 ≠ 0) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k shearTailRadius z := by
  have H : ContDiff ℝ k (fun z : NormalizedState => z 1 ^ 2 + (z 3 - z 4) ^ 2) := by fun_prop
  exact H.contDiffAt.sqrt (ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hs) (sq_nonneg _)))

/-- The physical radius is the same Euclidean observable already used in the fast layer. -/
theorem hasDerivAt_shearTailRadius {α : ℝ → NormalizedState} {v : NormalizedState} {r : ℝ}
    (hα : HasDerivAt α v r) (hs : α r 1 ≠ 0) :
    HasDerivAt (fun u => shearTailRadius (α u)) (shearTailRadiusDifferential (α r) v) r := by
  have H := (((hasDerivAt_pi.mp hα 1).pow 2).add
    (((hasDerivAt_pi.mp hα 3).sub (hasDerivAt_pi.mp hα 4)).pow 2)).sqrt
      (ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hs) (sq_nonneg _)))
  convert! H using 1
  change (α r 1 * v 1 + (α r 3 - α r 4) * (v 3 - v 4)) /
    Real.sqrt (α r 1 ^ 2 + (α r 3 - α r 4) ^ 2) = _
  norm_num only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

/-- The shear and weak-wall quadratic cross terms cancel exactly on the Einstein constraint. -/
theorem shearTailRadius_field {z : NormalizedState} (hc : stateConstraint z = 1) (hs : z 1 ≠ 0) :
    shearTailRadiusDifferential z (normalizedField z) = shearTailRadiusRate z := by
  have hR := shearTailRadius_pos hs
  change (z 1 * shearMinus (z 1) (z 2) (z 3) (z 4) +
    (z 3 - z 4) * (rateTwo (z 0) (z 1) * z 3 - rateThree (z 0) (z 1) * z 4)) / shearTailRadius z = _
  dsimp only [shearTailRadiusRate]
  field_simp [hR.ne']
  rw [shearTailRadius_sq]
  dsimp only [stateConstraint, constraint, shearSq] at hc
  dsimp only [shearMinus, rateTwo, rateThree, shearSq]
  linear_combination -(z 3 - z 4) ^ 2 * hc

theorem hasDerivAt_shearTailRadius_time {α : ℝ → NormalizedState} {t : ℝ}
    (hα : HasDerivAt α (normalizedField (α t)) t) (hc : stateConstraint (α t) = 1) (hs : α t 1 ≠ 0) :
    HasDerivAt (fun u => shearTailRadius (α u)) (shearTailRadiusRate (α t)) t :=
  (hasDerivAt_shearTailRadius hα hs).congr_deriv (shearTailRadius_field hc hs)

theorem shearTailRadius_region_bounds {a : ℝ} {z : NormalizedState}
    (ha : 0 < a ∧ a ≤ 1) (hr : shearTailRegion a z)
    (hn : 0 ≤ z 3 ∧ 0 ≤ z 4) :
    a / 2 ≤ shearTailRadius z ∧ shearTailRadius z ≤ 4 * a := by
  have hs : 0 ≤ z 1 := by linarith only [hr.2.1, ha.1]
  have ha2 : a ^ 2 ≤ a := by nlinarith only [ha.1, ha.2]
  have hd : |z 3 - z 4| ≤ 2 * a := abs_le.mpr
    ⟨by linarith only [hn.1, hr.2.2.2.2.2, ha.1],
      by linarith only [hn.2, hr.2.2.2.2.1, ha2, ha.1]⟩
  have Hs := pow_le_pow_left₀ hs hr.2.2.1 2
  have Hd := pow_le_pow_left₀ (abs_nonneg (z 3 - z 4)) hd 2
  rw [sq_abs] at Hd
  have Hsq := shearTailRadius_sq z
  have Hpos : 0 ≤ shearTailRadius z := Real.sqrt_nonneg _
  constructor
  · have Hlo := pow_le_pow_left₀ (by positivity [ha.1] : 0 ≤ a / 2) hr.2.1 2
    nlinarith only [Hlo, Hsq, Hpos, sq_nonneg (z 3 - z 4), ha.1]
  · nlinarith only [Hs, Hd, Hsq, Hpos, ha.1]

/-- Radius drift retains a linear strong-wall term and squared weak-wall terms. -/
theorem shearTailRadius_energy_bounds {a : ℝ} {z : NormalizedState}
    (ha : 0 < a ∧ a ≤ 1) (hr : shearTailRegion a z)
    (hn : 0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4) :
    0 ≤ shearTailRadiusEnergy z ∧ shearTailRadiusEnergy z ≤ 3 * a ^ 2 ∧
    shearTailEnergy z ≤ 3 * shearTailRadiusEnergy z := by
  have ha2 : a ^ 2 ≤ a := by nlinarith only [ha.1, ha.2]
  have hx : z 3 ≤ a := hr.2.2.2.2.1.trans ha2
  have hy : z 4 ≤ a := by linarith only [hr.2.2.2.2.2, ha.1]
  have hn1 : z 2 ≤ 1 := hr.2.2.2.1.trans (ha2.trans ha.2)
  have hxy : z 3 + z 4 ≤ 2 := by linarith only [hx, hy, ha.2]
  have Hx := pow_le_pow_left₀ hn.2.1 hx 2
  have Hy := pow_le_pow_left₀ hn.2.2 hy 2
  have Hn := mul_le_mul_of_nonneg_left hn1 hn.1
  have Hxy := mul_le_mul_of_nonneg_left hxy hn.1
  dsimp only [shearTailRadiusEnergy, shearTailEnergy]
  exact ⟨by positivity [hn.1], by linarith only [Hx, Hy, hr.2.2.2.1],
    by nlinarith only [Hn, Hxy, sq_nonneg (z 3), sq_nonneg (z 4)]⟩

end BianchiIX
