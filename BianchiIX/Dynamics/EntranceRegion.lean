import BianchiIX.Algebra.EntranceBounds
import BianchiIX.Dynamics.ConnectionRegion

noncomputable section

namespace BianchiIX

open Set

def entranceRegion (k : ℝ) (y : ProjectiveState) : Prop :=
  1 ≤ y 0 ∧ |coreRadius (y 0) (y 2) - k| ≤ k / 100 ∧
    (0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) ∧ (0 ≤ y 2 ∧ y 2 ≤ 1) ∧
    (0 ≤ y 3 ∧ y 3 ≤ 1 / 10000)

def entranceClockRate (y : ProjectiveState) : ℝ := connectionSpeed (y 0) (y 1) (y 2) (y 3)

theorem isClosed_entranceRegion (k : ℝ) : IsClosed {y : ProjectiveState | entranceRegion k y} := by
  have hR : Continuous (fun y : ProjectiveState => |coreRadius (y 0) (y 2) - k|) := by
    unfold coreRadius coreEnergy
    fun_prop
  exact (isClosed_le continuous_const (continuous_apply 0)).inter
    ((isClosed_le hR continuous_const).inter
      (((isClosed_le continuous_const (continuous_apply 1)).inter (isClosed_le (continuous_apply 1) continuous_const)).inter
        (((isClosed_le continuous_const (continuous_apply 2)).inter (isClosed_le (continuous_apply 2) continuous_const)).inter
          ((isClosed_le continuous_const (continuous_apply 3)).inter (isClosed_le (continuous_apply 3) continuous_const)))))

theorem continuous_entranceClockRate : Continuous entranceClockRate := by
  unfold entranceClockRate connectionSpeed coupling
  fun_prop

theorem entranceRegion_phase {k : ℝ} {y : ProjectiveState} (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    4 / 5 * k ≤ y 0 - 1 ∧ y 0 - 1 ≤ 101 / 100 * k :=
  entrance_phase_bounds hk hy.1 hy.2.1 hy.2.2.2.1

theorem entranceRegion_speed {k : ℝ} {y : ProjectiveState} (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    3 / 4 * k ≤ entranceClockRate y ∧ entranceClockRate y ≤ 21 / 20 * k :=
  entrance_speed_bounds hk (entranceRegion_phase hk hy) hy.2.2.1 hy.2.2.2.1 hy.2.2.2.2

theorem entranceRegion_clock_pos {k : ℝ} {y : ProjectiveState} (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    0 < entranceClockRate y := by linarith [(entranceRegion_speed hk hy).1]

theorem entranceRegion_wall_rates {k : ℝ} {y : ProjectiveState} (hk : 7 / 4 ≤ k) (hy : entranceRegion k y) :
    connectionStrongRate (y 0) (y 1) (y 2) (y 3) / entranceClockRate y ≤ -(1 + k / 3) ∧
      (-y 0 - 1 - coupling (y 1) (y 2) (y 3)) / entranceClockRate y ≤ -(1 + 1 / k) :=
  ⟨entrance_strong_clock_rate hk (entranceRegion_phase hk hy) hy.2.2.1 hy.2.2.2.1 hy.2.2.2.2,
    entrance_weak_clock_rate hk (entranceRegion_phase hk hy) hy.2.2.1 hy.2.2.2.1 hy.2.2.2.2⟩

theorem normalized_entrance_chart_lower {x : NormalizedState} {k : ℝ}
    (hk : 7 / 4 ≤ k) (hA : 1 + x 0 ≠ 0) (hc : stateConstraint x = 1)
    (hy : entranceRegion k (toProjectiveState x)) : 1 / (k + 1) ^ 2 ≤ 1 + x 0 := by
  have hD := entrance_denom_bounds hk (entranceRegion_phase hk hy) hy.2.2.1 hy.2.2.2.1 hy.2.2.2.2
  have hscale := projective_inverse_scale hA hc
  change 6 / projectiveStateDenom (toProjectiveState x) = 1 + x 0 at hscale
  rw [← hscale]
  change 1 / (k + 1) ^ 2 ≤ 6 / projectiveDenom _ _ _ _
  calc
    _ = 6 / (6 * (k + 1) ^ 2) := by
      have hK : k + 1 ≠ 0 := by linarith
      field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hD.1 hD.2

theorem hasDerivAt_entranceLog_scaled {Y : ℝ → ProjectiveState} {a t : ℝ}
    (hY : HasDerivAt Y (a • projectiveField (Y t)) t) (hv : Y t 2 ≠ 0) :
    HasDerivAt (fun s => Real.log (Y s 2)) (a * entranceClockRate (Y t)) t := by
  convert! (hasDerivAt_pi.mp hY 2).log hv using 1
  change _ = (a * activeVelocity (Y t 0) (Y t 1) (Y t 2) (Y t 3)) / Y t 2
  unfold activeVelocity entranceClockRate connectionSpeed
  field_simp

end BianchiIX
