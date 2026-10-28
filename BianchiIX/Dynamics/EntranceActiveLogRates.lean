import BianchiIX.Dynamics.EntranceWallLinearization
import BianchiIX.Analysis.EntranceActiveLogEstimates

noncomputable section

namespace BianchiIX

/-- Exact activity derivatives at fixed corrected radius, including the change of M. -/
theorem EntranceRadialInverseAt.activeLogRate_partials {y : ProjectiveState} {k : ℝ}
    {Ψ : ProjectiveState → ProjectiveState} (H : EntranceRadialInverseAt y Ψ)
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    let z := entranceRadialCoordinates y
    let m := fderiv ℝ Ψ z (Pi.single 2 1) 0
    fderiv ℝ (fun z => entranceStrongLogRate (Ψ z)) z (Pi.single 2 1) =
        (-(y 0 + entranceStrongLogRate y) * m - (y 2 - y 3) + entranceStrongLogRate y * y 1) /
          entranceClockRate y ∧
      fderiv ℝ (fun z => entranceWeakLogRate (Ψ z)) z (Pi.single 2 1) =
        (2 * (1 + coupling (y 1) (y 2) (y 3)) * m - 2 * y 0 * y 1) / entranceClockRate y ^ 2 := by
  have hD := (entranceRegion_clock_pos hk hy).ne'
  obtain ⟨hs, hw⟩ := contDiffAt_entranceWallLogRates 1 hD
  have ns := (H.scalar_partials (hs.differentiableAt (by norm_num))).2.2.1
  have nw := (H.scalar_partials (hw.differentiableAt (by norm_num))).2.2.1
  have m := H.phase_partials.2.2.1
  have ds (v : ProjectiveState) := (entranceWallLogRates_fderiv hD v).1
  have dw (v : ProjectiveState) := (entranceWallLogRates_fderiv hD v).2
  dsimp only
  rw [ns, nw, m]
  constructor <;> simp [ds, dw] <;> ring

theorem entrance_active_log_derivative_bounds {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    |y 2 * entranceStrongLogDifferential y (Pi.single 2 1)| ≤
        128 * ((y 2) ^ 2 / k + y 2 * (y 1 + y 3)) ∧
      |y 2 * entranceWeakLogDifferential y (Pi.single 2 1)| ≤
        64 * (y 1 * y 2 / k + (y 2) ^ 2 / k ^ 3) := by
  obtain ⟨Ψ, HΨ⟩ := exists_entranceRegion_radial_inverse hk hy hv
  obtain ⟨J, _, HJ⟩ := exists_entranceRadialInverse_column_bounds
  have hm := (HJ k y hk hy hv Ψ HΨ).2.2.1
  have hM : |y 0| ≤ 3 * k := by
    rw [abs_of_nonneg (by linarith [hy.1] : 0 ≤ y 0)]
    linarith [(entranceRegion_phase hk hy).2]
  have hbase := entranceWallLogRates_base_bounds hk hy
  have H := entrance_active_log_rate_bounds (by linarith : 1 ≤ k)
    (by linarith [(entranceRegion_speed hk hy).1] : k / 2 ≤ entranceClockRate y)
    hM hy.2.2.1.1 hv.le hy.2.2.2.2.1 hbase.1 hbase.2.1 hm
  have hp := HΨ.activeLogRate_partials hk hy
  have he := HΨ.wallLogDifferential_eq hk hy
  dsimp only at hp
  rw [he.1, he.2] at hp
  rw [hp.1, hp.2]
  exact H

def entranceWallActiveSource (k : ℝ) (y : ProjectiveState) : Fin 2 → ℝ :=
  ![y 2 * entranceStrongLogDifferential y (Pi.single 2 1),
    k ^ 2 * (y 2 * entranceWeakLogDifferential y (Pi.single 2 1))]

theorem continuousAt_entranceWallActiveSource {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    ContinuousAt (entranceWallActiveSource k) y := by
  obtain ⟨hs, hw⟩ := continuousAt_entranceWallLogDifferential_apply hk hy hv (Pi.single 2 1)
  apply continuousAt_pi.mpr
  intro i
  fin_cases i
  · exact (continuousAt_apply 2 y).mul hs
  · exact ((continuousAt_apply 2 y).mul hw).const_mul _

/-- The sum norm of the weighted amplitude forcing retains all three decay scales. -/
theorem entranceWallActiveSource_sum_bound {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    |entranceWallActiveSource k y 0| + |entranceWallActiveSource k y 1| ≤
      192 * ((y 2) ^ 2 / k + y 2 * (y 1 + y 3) + k * y 1 * y 2) := by
  have hk0 : 0 < k := by linarith
  obtain ⟨hs, hw⟩ := entrance_active_log_derivative_bounds hk hy hv
  have hP : 0 ≤ y 2 * (y 1 + y 3) := mul_nonneg hv.le (add_nonneg hy.2.2.1.1 hy.2.2.2.2.1)
  have hQ : 0 ≤ (y 2) ^ 2 / k := by positivity
  have hR : 0 ≤ k * y 1 * y 2 := by positivity [hy.2.2.1.1]
  have H := mul_le_mul_of_nonneg_left hw (sq_nonneg k)
  have heq : k ^ 2 * (64 * (y 1 * y 2 / k + (y 2) ^ 2 / k ^ 3)) =
      64 * (k * y 1 * y 2 + (y 2) ^ 2 / k) := by field_simp
  rw [heq] at H
  change |y 2 * entranceStrongLogDifferential y (Pi.single 2 1)| +
    |k ^ 2 * (y 2 * entranceWeakLogDifferential y (Pi.single 2 1))| ≤ _
  rw [abs_mul (k ^ 2), abs_of_nonneg (sq_nonneg k)]
  linarith only [hs, H, hP, hQ, hR]

theorem entranceWallActiveSource_bound {y : ProjectiveState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) (hv : 0 < y 2) :
    ‖entranceWallActiveSource k y‖ ≤
      192 * ((y 2) ^ 2 / k + y 2 * (y 1 + y 3) + k * y 1 * y 2) := by
  have H := entranceWallActiveSource_sum_bound hk hy hv
  apply (pi_norm_le_iff_of_nonneg (le_trans (by positivity) H)).mpr
  intro i
  fin_cases i
  · exact (le_add_of_nonneg_right (abs_nonneg _)).trans H
  · exact (le_add_of_nonneg_left (abs_nonneg _)).trans H

end BianchiIX
