import BianchiIX.Dynamics.ConnectionReturnCone
import BianchiIX.Algebra.ConnectionRadialDecay

noncomputable section

namespace BianchiIX

/-- The two physical wall responses to a unit radial input retain the radial inverse square. -/
theorem connectionReturn_radial_wall_bounds {p v : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000)
    (hL : 1 ≤ -Real.log (p 2))
    (hv : ((p 0 + 1) / phaseNorm (p 0 + 1) 1) * v 0 = 1)
    (hv1 : v 1 = 0) (hv2 : v 2 = 0) :
    let L := -Real.log (p 2)
    let d := fderiv ℝ connectionReturnPhysicalState p v
    |d 1| ≤ (17536 * Real.sqrt (p 1) / p 0 ^ 2) * Real.sqrt (connectionReturnState p 1) ∧
      |d 2| ≤ (274 * L * Real.sqrt (p 2) / p 0 ^ 2) * Real.sqrt (connectionReturnState p 2) := by
  intro L d
  have hμ0 : 0 < p 0 := by linarith only [hμ]
  have hL0 : 0 ≤ L := by linarith only [hL]
  let J := fderiv ℝ (connectionLogCoordinates ∘ connectionReturnState) p
  have Hj (i : Fin 4) : |J v i| ≤ |v 0| * |J ![1, 0, 0] i| := by
    have H := three_coordinate_linear_bound
      ((ContinuousLinearMap.proj i : (Fin 4 → ℝ) →L[ℝ] ℝ).comp J) v
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      hv1, hv2, abs_zero, zero_mul, add_zero] using H
  have Hv := connection_unit_phase_direction hμ hv
  have HA := connectionReturn_log_amplitude_bounds hμ hu hw
  have Hstrong : |J v 1| ≤ 274 * L :=
    ((Hj 1).trans (mul_le_mul Hv HA.1 (abs_nonneg _) (by norm_num))).trans_eq (by ring)
  have Hweak : |J v 2| ≤ 274 * L / p 0 ^ 2 :=
    ((Hj 2).trans (mul_le_mul Hv HA.2.1 (abs_nonneg _) (by norm_num))).trans_eq (by ring)
  have Hdec := connectionReturn_exponential_decay hμ hu hw
  have Hpos := connectionReturn_wall_pos hμ ⟨hu.1.le, hu.2⟩ hw
  have Hd := connectionReturnPhysicalState_differential hμ hu hw v
  have hU : Real.sqrt (connectionReturnState p 1) ≤ Real.sqrt (p 1) * Real.exp (-p 0 * L / 4) := by
    have Hb := sqrt_le_sqrt_mul_exp_half hu.1.le Hdec.1
    have heq : (-p 0 * (-Real.log (p 2)) / 2) / 2 = -p 0 * L / 4 := by dsimp only [L]; ring
    rwa [heq] at Hb
  have hV : Real.sqrt (connectionReturnState p 2) ≤ Real.sqrt (p 2) := by
    apply Real.sqrt_le_sqrt
    have He : Real.exp (-2 * L / p 0) ≤ 1 :=
      Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith only [hL0]) hμ0.le)
    exact Hdec.2.trans ((mul_le_mul_of_nonneg_left He hw.1.le).trans_eq (mul_one _))
  have Hs : Real.sqrt (connectionReturnState p 1) * |J v 1| ≤ 17536 * Real.sqrt (p 1) / p 0 ^ 2 := by
    calc
      _ ≤ (Real.sqrt (p 1) * Real.exp (-p 0 * L / 4)) * (274 * L) :=
        mul_le_mul hU Hstrong (abs_nonneg _) (by positivity)
      _ = (274 * Real.sqrt (p 1)) * (L * Real.exp (-p 0 * L / 4)) := by ring
      _ ≤ (274 * Real.sqrt (p 1)) * (64 / p 0 ^ 2) :=
        mul_le_mul_of_nonneg_left (connection_radial_decay hμ0 hL) (by positivity)
      _ = _ := by ring
  have Hw : Real.sqrt (connectionReturnState p 2) * |J v 2| ≤ 274 * L * Real.sqrt (p 2) / p 0 ^ 2 :=
    (mul_le_mul hV Hweak (abs_nonneg _) (Real.sqrt_nonneg _)).trans_eq (by ring)
  constructor
  · calc
      |d 1| = Real.sqrt (connectionReturnState p 1) * (Real.sqrt (connectionReturnState p 1) * |J v 1|) := by
        dsimp only [d]
        rw [Hd.2.1, abs_mul, abs_of_pos (Hpos.2 hu.1), ← mul_assoc, Real.mul_self_sqrt (Hpos.2 hu.1).le]
      _ ≤ Real.sqrt (connectionReturnState p 1) * (17536 * Real.sqrt (p 1) / p 0 ^ 2) :=
        mul_le_mul_of_nonneg_left Hs (Real.sqrt_nonneg _)
      _ = _ := by ring
  · calc
      |d 2| = Real.sqrt (connectionReturnState p 2) * (Real.sqrt (connectionReturnState p 2) * |J v 2|) := by
        dsimp only [d]
        rw [Hd.2.2, abs_mul, abs_of_pos Hpos.1, ← mul_assoc, Real.mul_self_sqrt Hpos.1.le]
      _ ≤ Real.sqrt (connectionReturnState p 2) * (274 * L * Real.sqrt (p 2) / p 0 ^ 2) :=
        mul_le_mul_of_nonneg_left Hw (Real.sqrt_nonneg _)
      _ = _ := by ring

end BianchiIX
