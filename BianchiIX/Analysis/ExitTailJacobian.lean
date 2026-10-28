import BianchiIX.Analysis.ExitTailGradientBounds
import BianchiIX.Dynamics.ExitTailMultipliers

noncomputable section

namespace BianchiIX

def exitTailRateGradient (v : ℝ) (Y : ExitTailState) (i : Fin 2) : ExitTailState :=
  if i = 0 then exitTailStrongRateGradient (Y 0) (Y 1) v (Y 2)
  else exitTailWeakRateGradient (Y 0) (Y 1) v (Y 2)

theorem exitTailField_radial_partial {v : ℝ} {Y : ExitTailState} (hR : 0 < Y 0)
    (hv : v ^ 2 < (Y 0) ^ 2) (hd : exitTailSpeed (Y 0) (Y 1) v (Y 2) ≠ 0)
    (j : Fin 3) : fderiv ℝ (exitTailField v) Y (Pi.single j 1) 0 =
      exitTailRadialGradient (Y 0) (Y 1) v (Y 2) j := by
  rw [exitTailField_fderiv hR hv hd]
  fin_cases j <;> simp [exitTailLinearization, Pi.single_apply]

theorem exitTailField_wall_partial {v : ℝ} {Y : ExitTailState} (hR : 0 < Y 0)
    (hv : v ^ 2 < (Y 0) ^ 2) (hd : exitTailSpeed (Y 0) (Y 1) v (Y 2) ≠ 0)
    (i : Fin 2) (j : Fin 3) : fderiv ℝ (exitTailField v) Y (Pi.single j 1) i.succ =
      Y i.succ * exitTailRateGradient v Y i j + exitTailWallRate v Y i * (if j = i.succ then 1 else 0) := by
  rw [exitTailField_fderiv hR hv hd]
  fin_cases i <;> fin_cases j <;>
    simp [exitTailLinearization, exitTailRateGradient, exitTailWallRate, Pi.single_apply]

theorem exitTailRateGradient_bounds {v : ℝ} {Y : ExitTailState}
    (hR : 7 / 4 ≤ Y 0 ∧ Y 0 ≤ 17 / 4) (hu : |Y 1| ≤ 1 / 100)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : |Y 2| ≤ 1 / 100) (i : Fin 2) :
    |exitTailRateGradient v Y i 0| ≤ 512 ∧
      ∀ j : Fin 2, |exitTailRateGradient v Y i j.succ| ≤ 256 * (v + |Y 1| + |Y 2|) := by
  have H := exitTail_rate_gradient_bounds hR hu hv hw
  fin_cases i
  · exact ⟨H.1, fun j => (H.2.2 j).1⟩
  · exact ⟨H.2.1, fun j => (H.2.2 j).2⟩

/-- The actual Jacobian has the small four-block structure of D.6, with the wall factors intact. -/
theorem exitTailField_jacobian_bounds {v : ℝ} {Y : ExitTailState}
    (hR : 7 / 4 ≤ Y 0 ∧ Y 0 ≤ 17 / 4) (hu : |Y 1| ≤ 1 / 100)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : |Y 2| ≤ 1 / 100) :
    let L := fderiv ℝ (exitTailField v) Y
    |L (Pi.single 0 1) 0| ≤ 256 * (|Y 1| * v + (|Y 1| + |Y 2|) ^ 2) ∧
      (∀ j : Fin 2, |L (Pi.single j.succ 1) 0| ≤ 32 * (v + |Y 1| + |Y 2|)) ∧
      (∀ i : Fin 2, |L (Pi.single 0 1) i.succ| ≤ 512 * |Y i.succ| ∧
        ∀ j : Fin 2, |L (Pi.single j.succ 1) i.succ - (if j = i then exitTailWallRate v Y i else 0)| ≤
          256 * |Y i.succ| * (v + |Y 1| + |Y 2|)) := by
  intro L
  have hR0 : 0 < Y 0 := by linarith only [hR.1]
  have hvR : v ^ 2 < (Y 0) ^ 2 := by nlinarith only [hR.1, hv.1, hv.2]
  have hd : exitTailSpeed (Y 0) (Y 1) v (Y 2) ≠ 0 := by
    have H := exitTailSpeed_compact hR.1 hu hv hw
    linarith only [H]
  have HR := exitTail_radial_gradient_bounds hR hu hv hw
  refine ⟨?_, ?_, ?_⟩
  · change |fderiv ℝ (exitTailField v) Y (Pi.single 0 1) 0| ≤ _
    rw [exitTailField_radial_partial hR0 hvR hd]
    exact HR.1
  · intro j
    change |fderiv ℝ (exitTailField v) Y (Pi.single j.succ 1) 0| ≤ _
    rw [exitTailField_radial_partial hR0 hvR hd]
    fin_cases j
    · exact HR.2.1
    · have H := HR.2.2
      change |exitTailRadialGradient (Y 0) (Y 1) v (Y 2) 2| ≤ _
      linarith only [H, hv.1, abs_nonneg (Y 1), abs_nonneg (Y 2)]
  · intro i
    have HI := exitTailRateGradient_bounds hR hu hv hw i
    constructor
    · have heq : L (Pi.single 0 1) i.succ = Y i.succ * exitTailRateGradient v Y i 0 := by
        change fderiv ℝ (exitTailField v) Y (Pi.single 0 1) i.succ = _
        rw [exitTailField_wall_partial hR0 hvR hd]
        fin_cases i <;> simp
      rw [heq, abs_mul]
      have H := mul_le_mul_of_nonneg_left HI.1 (abs_nonneg (Y i.succ))
      nlinarith only [H]
    · intro j
      have heq : L (Pi.single j.succ 1) i.succ - (if j = i then exitTailWallRate v Y i else 0) =
          Y i.succ * exitTailRateGradient v Y i j.succ := by
        change fderiv ℝ (exitTailField v) Y (Pi.single j.succ 1) i.succ - _ = _
        rw [exitTailField_wall_partial hR0 hvR hd]
        by_cases hij : j = i <;> simp [hij]
      rw [heq, abs_mul]
      have H := mul_le_mul_of_nonneg_left (HI.2 j) (abs_nonneg (Y i.succ))
      nlinarith only [H]

end BianchiIX
