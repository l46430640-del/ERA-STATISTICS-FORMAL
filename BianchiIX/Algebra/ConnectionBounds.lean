import BianchiIX.Algebra.Coordinates

noncomputable section

namespace BianchiIX

def connectionSpeed (m u v w : ℝ) : ℝ := m - 1 - coupling u v w

def connectionStrongRate (m u v w : ℝ) : ℝ :=
  (1 - m ^ 2 - (v - w) ^ 2 + u ^ 2) / 2

theorem connection_coupling_bounds {u v w : ℝ} (hu : 0 ≤ u)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    -u ^ 2 ≤ coupling u v w ∧ coupling u v w ≤ 2 * u := by
  unfold coupling
  constructor
  · nlinarith only [mul_nonneg hu hv.1, mul_nonneg hu hw.1]
  · nlinarith only [mul_le_mul_of_nonneg_left hv.2 hu,
      mul_le_mul_of_nonneg_left hw.2 hu, sq_nonneg u]

theorem connection_speed_bounds {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    μ / 2 ≤ connectionSpeed m u v w ∧ connectionSpeed m u v w ≤ μ := by
  obtain ⟨hc₀, hc₁⟩ := connection_coupling_bounds hu.1 hv hw
  obtain ⟨hm₀, hm₁⟩ := abs_le.mp hm
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  unfold connectionSpeed
  constructor <;> nlinarith only [hc₀, hc₁, hm₀, hm₁, hu.2, hu2, hμ]

theorem connection_denom_bound {m u v w : ℝ}
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    3 + m ^ 2 - 4 * u ≤ projectiveDenom (-m) u v w ∧ 0 < projectiveDenom (-m) u v w := by
  have H : 3 + m ^ 2 - 4 * u ≤ projectiveDenom (-m) u v w := by
    dsimp [projectiveDenom, curvature]
    nlinarith only [mul_le_mul_of_nonneg_left hv.2 hu.1,
      mul_le_mul_of_nonneg_left hw.2 hu.1, sq_nonneg u, sq_nonneg (v - w)]
  exact ⟨H, by nlinarith only [H, hu.2, sq_nonneg m]⟩

theorem connection_coupling_nonneg {u v w : ℝ}
    (hu : 0 ≤ u) (hw : 0 ≤ w) (huv : u ≤ v) : 0 ≤ coupling u v w := by
  unfold coupling
  exact mul_nonneg hu (by linarith only [hw, huv])

theorem connection_ratio_rate_neg {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    connectionStrongRate m u v w + m + 1 + coupling u v w < 0 := by
  have hm0 : 7 / 2 ≤ m := by linarith only [(abs_le.mp hm).1, hμ]
  have hm2 := mul_nonneg (sub_nonneg.mpr hm0) (show 0 ≤ m by linarith only [hm0])
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  have hc := (connection_coupling_bounds hu.1 hv hw).2
  unfold connectionStrongRate
  nlinarith only [hm0, hm2, hu2, hc, hu.2, sq_nonneg (v - w)]

theorem connection_strong_rate_le {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000) :
    connectionStrongRate m u v w ≤ -μ ^ 2 / 4 := by
  have hm0 : 7 * μ / 8 ≤ m := by linarith only [(abs_le.mp hm).1, hμ]
  have hm2 := mul_nonneg (sub_nonneg.mpr hm0)
    (show 0 ≤ m + 7 * μ / 8 by linarith only [hm0, hμ])
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  unfold connectionStrongRate
  nlinarith only [hm2, hu2, hμ, sq_nonneg (μ - 4), sq_nonneg (v - w)]

theorem connection_strong_clock_rate_le {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) (huv : u ≤ v) :
    connectionStrongRate m u v w / connectionSpeed m u v w ≤ -μ / 2 := by
  have hD := (connection_speed_bounds hμ hm hu hv hw).1
  have hDpos : 0 < connectionSpeed m u v w := by linarith only [hD, hμ]
  have hc := connection_coupling_nonneg hu.1 hw.1 huv
  have hm0 : 0 ≤ m := by linarith only [(abs_le.mp hm).1, hμ]
  have hprod := mul_nonneg (show 0 ≤ m - μ + 1 / 2 by linarith only [(abs_le.mp hm).1]) hm0
  have hu2 : u ^ 2 ≤ (1 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hu.1 hu.2 2
  apply (div_le_iff₀ hDpos).mpr
  dsimp [connectionStrongRate, connectionSpeed]
  nlinarith only [hprod, hu2, (abs_le.mp hm).2, hμ, sq_nonneg (v - w),
    mul_nonneg (show 0 ≤ μ by linarith only [hμ]) hc]

theorem connection_clock_identities {m u v w : ℝ} (hD : connectionSpeed m u v w ≠ 0) :
    (-m - 1 - coupling u v w) / connectionSpeed m u v w =
      -1 - 2 * (1 + coupling u v w) / connectionSpeed m u v w ∧
    connectionStrongRate m u v w / connectionSpeed m u v w + (m + 1) / 2 =
      (-(v - w) ^ 2 + u ^ 2 - (m + 1) * coupling u v w) / (2 * connectionSpeed m u v w) := by
  constructor <;> dsimp [connectionSpeed, connectionStrongRate] at * <;> field_simp <;> ring

theorem connection_weak_clock_rates {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) (huv : u ≤ v) :
    (-m - 1 - coupling u v w) / connectionSpeed m u v w ≤ -(1 + 2 / μ) ∧
      -2 * (1 + coupling u v w) / connectionSpeed m u v w ≤ -2 / μ := by
  obtain ⟨hD₀, hD₁⟩ := connection_speed_bounds hμ hm hu hv hw
  have hD : 0 < connectionSpeed m u v w := by linarith only [hD₀, hμ]
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hc := connection_coupling_nonneg hu.1 hw.1 huv
  have H : 2 / μ ≤ 2 * (1 + coupling u v w) / connectionSpeed m u v w := by
    apply (div_le_div_iff₀ hμ0 hD).mpr
    nlinarith only [hD₁, mul_nonneg hμ0.le hc]
  have hid := (connection_clock_identities (ne_of_gt hD)).1
  constructor
  · linarith only [H, hid]
  · convert! neg_le_neg H using 1 <;> ring

theorem connection_phase_velocity_bound {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) (huv : u ≤ v) :
    |phaseVelocity (-m) u v w| ≤ v ^ 2 + w ^ 2 + 3 * μ * u := by
  have hm0 : 0 ≤ m := by linarith only [(abs_le.mp hm).1, hμ]
  have hc := connection_coupling_nonneg hu.1 hw.1 huv
  have hmc₀ := mul_nonneg hm0 hc
  have hmc₁ := mul_le_mul_of_nonneg_left (connection_coupling_bounds hu.1 hv hw).2 hm0
  have hdiff : -1 ≤ v - w ∧ v - w ≤ 1 := by constructor <;> linarith only [hv.1, hv.2, hw.1, hw.2]
  have hd₀ := mul_le_mul_of_nonneg_left hdiff.1 hu.1
  have hd₁ := mul_le_mul_of_nonneg_left hdiff.2 hu.1
  have hcoeff := mul_le_mul_of_nonneg_right
    (show 1 + 2 * m ≤ 3 * μ by linarith only [(abs_le.mp hm).2, hμ]) hu.1
  rw [abs_le]
  dsimp [phaseVelocity]
  constructor <;> nlinarith only [hmc₀, hmc₁, hd₀, hd₁, hcoeff, sq_nonneg v, sq_nonneg w]

end BianchiIX
