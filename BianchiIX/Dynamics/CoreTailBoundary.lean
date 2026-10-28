import BianchiIX.Dynamics.CompactCoreTail
import BianchiIX.Dynamics.ProjectiveReflection
import BianchiIX.Algebra.CompactConnectionRadius

noncomputable section

namespace BianchiIX

open Set

theorem coreTailState_active {η : ℝ} {Y : CoreAngleState} (hvalid : coreTailValid η Y) :
    coreTailState η Y 2 = η := hvalid.1.1.2.2

theorem coreTail_no_growing_hit {η : ℝ} {Y : CoreAngleState} (hvalid : coreTailValid η Y)
    {t : ℝ} (ht : t ∈ Icc 0 (coreTailTime η Y)) :
    projectiveOriginalFlow (coreTailEntry Y) 0 t 3 ≠ 1 := by
  have H := hvalid.2.2.2.2 t ht
  change |projectiveOriginalFlow (coreTailEntry Y) 0 t 3| < 1 / 2 at H
  intro heq
  rw [heq, abs_one] at H
  norm_num at H

/-- The two transverse coordinate hyperplanes are invariant on the actual finite tail. -/
theorem coreTailState_wall_zero {η : ℝ} {Y : CoreAngleState} (hvalid : coreTailValid η Y)
    (i : Fin 2) (hi : Y i.succ = 0) : coreTailState η Y (if i = 0 then 1 else 3) = 0 := by
  let x := fromProjectiveState (coreTailEntry Y)
  let T := coreTailTime η Y
  have hT : 0 < T := hvalid.1.1.1
  have hdom : T ∈ normalizedMaxDomain x 0 := hvalid.1.1.2.1
  have hA : 0 < 1 + normalizedMaxCurve x 0 T 0 := (hvalid.2.1 T ⟨hT.le, le_rfl⟩).2
  have hzero (j : Fin 3) (hj : wallValue j x = 0) :
      toProjectiveState (normalizedMaxCurve x 0 T) j.succ = 0 := by
    have H := normalized_wall_sign (convex_normalizedMaxDomain x 0) (isOpen_normalizedMaxDomain x 0)
      (fun _ ht => hasDerivAt_normalizedMaxCurve ht) (initial_mem_normalizedMaxDomain x 0) hdom j
    rw [normalizedMaxCurve_initial] at H
    exact (toProjectiveState_wall_sign hA j).1.mpr (H.1.mpr hj)
  fin_cases i
  · change Y 1 = 0 at hi
    exact hzero 0 (by simp [x, fromProjectiveState, coreTailEntry, wallValue, hi])
  · change Y 2 = 0 at hi
    exact hzero 2 (by simp [x, fromProjectiveState, coreTailEntry, wallValue, hi])

theorem coreTail_reflected_reference {k η : ℝ} (hk : 1 < k) (hη : 0 < η ∧ η < 1) :
    projectiveReflection (coreTailState η ![k, 0, 0]) =
      ![Real.sqrt (k ^ 2 - η ^ 2) - 1, 0, 0, η] := by
  rw [(coreTail_reference_regular hk hη).2.1]
  ext i
  fin_cases i <;> dsimp [projectiveReflection]
  ring

/-- The exact boundary phase after the finite tail and wall exchange is the one in B.46. -/
theorem coreTail_reflected_reference_radius {k η : ℝ}
    (hk : 31 / 8 ≤ k ∧ k ≤ 6) (hη : 0 < η ∧ η ≤ 1 / 8) :
    let y := projectiveReflection (coreTailState η ![k, 0, 0])
    coreRadius (y 0) (y 2) = Real.sqrt (k ^ 2 - η ^ 2) - 2 ∧
      (15 / 8 - 8 * η ^ 2 / 31 ≤ coreRadius (y 0) (y 2) ∧
        coreRadius (y 0) (y 2) ≤ 4 - η ^ 2 / 12) := by
  intro y
  have H := compact_connection_boundary_radius_bounds hk hη
  have hpos : 0 ≤ Real.sqrt (k ^ 2 - η ^ 2) - 2 := by
    have hηsq : η ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := pow_le_pow_left₀ hη.1.le hη.2 2
    nlinarith only [H.1, hηsq]
  have heq : coreRadius (y 0) (y 2) = Real.sqrt (k ^ 2 - η ^ 2) - 2 := by
    dsimp only [y]
    rw [coreTail_reflected_reference (by linarith only [hk.1]) ⟨hη.1, by linarith only [hη.2]⟩]
    change Real.sqrt ((Real.sqrt (k ^ 2 - η ^ 2) - 1 - 1) ^ 2 + 0 ^ 2) = _
    rw [show (Real.sqrt (k ^ 2 - η ^ 2) - 1 - 1) ^ 2 + 0 ^ 2 =
      (Real.sqrt (k ^ 2 - η ^ 2) - 2) ^ 2 by ring, Real.sqrt_sq hpos]
  exact ⟨heq, heq.symm ▸ H⟩

end BianchiIX
