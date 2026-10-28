import BianchiIX.Dynamics.ShearTailVariationBounds
import BianchiIX.Dynamics.ShearTailProjection

noncomputable section

namespace BianchiIX

def shearTailProjectiveLogState (z : NormalizedState) : Fin 5 → ℝ :=
  ![Real.log (1 + z 0), Real.log (projectiveCoord (z 0) (z 1)),
    Real.log (projectiveCoord (z 0) (z 2)), Real.log (projectiveCoord (z 0) (z 3)),
    Real.log (projectiveCoord (z 0) (z 4))]

def shearTailProjectiveLogVariation (z v : NormalizedState) : Fin 5 → ℝ :=
  ![v 0 / (1 + z 0), v 1 / z 1 - v 0 / (1 + z 0),
    v 2 / z 2 - v 0 / (1 + z 0), v 3 / z 3 - v 0 / (1 + z 0),
    v 4 / z 4 - v 0 / (1 + z 0)]

/-- Ordinary differentiation of the denominator and all four projective logarithms. -/
theorem hasDerivAt_shearTailProjectiveLogState {α : ℝ → NormalizedState} {v : NormalizedState} {r : ℝ}
    (hα : HasDerivAt α v r) (hA : 1 + α r 0 ≠ 0) (hs : α r 1 ≠ 0)
    (hn : α r 2 ≠ 0) (hx : α r 3 ≠ 0) (hy : α r 4 ≠ 0) :
    HasDerivAt (fun u => shearTailProjectiveLogState (α u)) (shearTailProjectiveLogVariation (α r) v) r := by
  have Hp := hasDerivAt_pi.mp hα 0
  have H (i : Fin 5) (hi : α r i ≠ 0) :
      HasDerivAt (fun u => Real.log (projectiveCoord (α u 0) (α u i)))
        (v i / α r i - v 0 / (1 + α r 0)) r := by
    have hroot : Real.sqrt (3 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
    have hcoord : projectiveCoord (α r 0) (α r i) ≠ 0 := div_ne_zero (mul_ne_zero hroot hi) hA
    convert! (hasDerivAt_projectiveCoord Hp (hasDerivAt_pi.mp hα i) hA).log hcoord using 1
    dsimp only [projectiveCoord]
    field_simp
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact (Hp.const_add 1).log hA
  · exact H 1 hs
  · exact H 2 hn
  · exact H 3 hx
  · exact H 4 hy

/-- A weighted energy response controls the singular projective denominator and every log coordinate. -/
theorem shearTail_projective_log_variation_bounds {a K : ℝ} {z v : NormalizedState}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hK : 0 ≤ K)
    (hc : stateConstraint z = 1) (hr : shearTailRegion a z) (hn : positiveWalls z)
    (hv : normalizedConstraintDifferential z v = 0)
    (hs : |v 1| ≤ 5) (hL : shearTailEnergy z * shearTailLogSize z v ≤ K * a) :
    let w := shearTailProjectiveLogVariation z v
    |w 0| + |w 1| ≤ (610 + 80 * K) / a ∧
    |w 2| + |w 3| + |w 4| ≤ 3 * shearTailLogSize z v + (900 + 120 * K) / a := by
  intro w
  have Hwall (i : Fin 3) (hi : 0 < z (i.addNat 2)) : |v (i.addNat 2)| ≤ z (i.addNat 2) * shearTailLogSize z v := by
    have H := norm_le_pi_norm (fun j : Fin 3 => v (j.addNat 2) / z (j.addNat 2)) i
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hi] at H
    simpa only [shearTailLogSize, mul_comm] using (div_le_iff₀ hi).mp H
  have HQ := (shearTail_polynomial_variation_bounds (norm_nonneg _) ⟨hn.1.le, hn.2.1.le, hn.2.2.le⟩
    ⟨Hwall 0 hn.1, Hwall 1 hn.2.1, Hwall 2 hn.2.2⟩).2.1
  change |shearTailCurvatureDifferential z v| ≤ 4 * shearTailEnergy z * shearTailLogSize z v at HQ
  have HQ' : |shearTailCurvatureDifferential z v| ≤ 4 * K * a := by nlinarith only [HQ, hL]
  have hp : z 0 < 0 := by linarith only [hr.1]
  have hs0 : 0 < z 1 := by linarith only [hr.2.1, ha.1]
  obtain ⟨_, _, _, _, _, HAl, _⟩ := shearTail_constraint_bounds ha hp ⟨hr.2.1, hr.2.2.1⟩
    ⟨hn.1.le, hr.2.2.2.1⟩ ⟨hn.2.1.le, hr.2.2.2.2.1⟩ ⟨hn.2.2.le, hr.2.2.2.2.2⟩ hc
  have hA : 0 < 1 + z 0 := (div_pos (sq_pos_of_pos ha.1) (by norm_num)).trans_le HAl
  have Hv0 : |v 0| ≤ (30 + 4 * K) * a := by
    rw [normalizedConstraintDifferential_shearTail] at hv
    have he : (-z 0) * v 0 = z 1 * v 1 + shearTailCurvatureDifferential z v / 2 := by nlinarith only [hv]
    have HE := congrArg abs he
    rw [abs_mul, abs_of_pos (neg_pos.mpr hp)] at HE
    have Habs := abs_add_le (z 1 * v 1) (shearTailCurvatureDifferential z v / 2)
    rw [abs_mul, abs_of_pos hs0, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at Habs
    have Hs := mul_le_mul hr.2.2.1 hs (abs_nonneg _) (by positivity [ha.1] : 0 ≤ 3 * a)
    have Hp := mul_le_mul_of_nonneg_right (show (1 / 2 : ℝ) ≤ -z 0 by linarith only [hr.1]) (abs_nonneg (v 0))
    nlinarith only [HE, Habs, Hs, Hp, HQ']
  have HA : |v 0 / (1 + z 0)| ≤ (300 + 40 * K) / a := by
    rw [abs_div, abs_of_pos hA]
    calc
      _ ≤ ((30 + 4 * K) * a) / (a ^ 2 / 10) := div_le_div₀
        (by positivity [ha.1] : 0 ≤ (30 + 4 * K) * a) Hv0
        (by positivity [ha.1] : 0 < a ^ 2 / 10) HAl
      _ = _ := by field_simp [ha.1.ne']; ring
  have HS : |v 1 / z 1| ≤ 10 / a := by
    rw [abs_div, abs_of_pos hs0]
    calc
      _ ≤ 5 / (a / 2) := div_le_div₀ (by norm_num) hs (by positivity [ha.1]) hr.2.1
      _ = _ := by ring
  have HM := (abs_sub (v 1 / z 1) (v 0 / (1 + z 0))).trans (add_le_add HS HA)
  have HW (i : Fin 3) : |v (i.addNat 2) / z (i.addNat 2) - v 0 / (1 + z 0)| ≤
      shearTailLogSize z v + (300 + 40 * K) / a :=
    (abs_sub _ _).trans (add_le_add (norm_le_pi_norm (fun j : Fin 3 => v (j.addNat 2) / z (j.addNat 2)) i) HA)
  constructor
  · change |v 0 / (1 + z 0)| + |v 1 / z 1 - v 0 / (1 + z 0)| ≤ _
    have H := add_le_add HA HM
    convert! H using 1
    ring
  · have H := add_le_add (add_le_add (HW 0) (HW 1)) (HW 2)
    change |v 2 / z 2 - v 0 / (1 + z 0)| + |v 3 / z 3 - v 0 / (1 + z 0)| +
      |v 4 / z 4 - v 0 / (1 + z 0)| ≤ _ at H
    convert! H using 1
    ring

/-- The logarithmic shear estimate gives the ordinary projective shear response. -/
theorem shearTail_projective_shear_response {a K r : ℝ} {α : ℝ → NormalizedState} {v : NormalizedState}
    (ha : 0 < a) (hα : HasDerivAt α v r)
    (hA : a ^ 2 / 10 ≤ 1 + α r 0) (hs : 0 < α r 1 ∧ α r 1 ≤ 3 * a)
    (hlog : |shearTailProjectiveLogVariation (α r) v 1| ≤ K / a) :
    HasDerivAt (fun u => projectiveCoord (α u 0) (α u 1))
      (projectiveCoord (α r 0) (α r 1) * shearTailProjectiveLogVariation (α r) v 1) r ∧
    |deriv (fun u => projectiveCoord (α u 0) (α u 1)) r| ≤ 60 * K / a ^ 2 := by
  have hApos : 0 < 1 + α r 0 := (div_pos (sq_pos_of_pos ha) (by norm_num)).trans_le hA
  have HD : HasDerivAt (fun u => projectiveCoord (α u 0) (α u 1))
      (projectiveCoord (α r 0) (α r 1) * shearTailProjectiveLogVariation (α r) v 1) r := by
    convert! hasDerivAt_projectiveCoord (hasDerivAt_pi.mp hα 0) (hasDerivAt_pi.mp hα 1) hApos.ne' using 1
    dsimp [projectiveCoord, shearTailProjectiveLogVariation]
    field_simp [hs.1.ne']
  have HM := shearTail_projectiveCoordinate_le ha hA ⟨hs.1.le, hs.2⟩
  have HM' : projectiveCoord (α r 0) (α r 1) ≤ 60 / a := by
    convert! HM.2 using 1
    field_simp [ha.ne']
    norm_num
  refine ⟨HD, ?_⟩
  rw [HD.deriv, abs_mul, abs_of_nonneg HM.1]
  calc
    _ ≤ (60 / a) * (K / a) := mul_le_mul HM' hlog (abs_nonneg _) (by positivity)
    _ = _ := by ring

end BianchiIX
