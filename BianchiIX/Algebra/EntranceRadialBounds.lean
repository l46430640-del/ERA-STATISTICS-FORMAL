import BianchiIX.Algebra.EntranceBounds

noncomputable section

namespace BianchiIX

theorem entrance_radius_clock_bound {k m u v w : ℝ} (hk : 7 / 4 ≤ k) (hm : 1 ≤ m)
    (hr : |coreRadius m v - k| ≤ k / 100)
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 < v ∧ v ≤ 1)
    (hw : 0 ≤ w ∧ w ≤ 1 / 10000) :
    |(-coupling u v w * coreRadius m v + (m - 1) / coreRadius m v * (u - w) ^ 2) /
      connectionSpeed m u v w| ≤ 4 * (u * (v + w) + u ^ 2 + w ^ 2 / k) := by
  let R := coreRadius m v
  let D := connectionSpeed m u v w
  let B := u * (v + w) + u ^ 2
  have hk0 : 0 < k := by linarith
  have hR : 0 < R := coreRadius_pos hv.1
  have hphase := entrance_phase_bounds hk hm hr ⟨hv.1.le, hv.2⟩
  have hspeed := entrance_speed_bounds hk hphase hu ⟨hv.1.le, hv.2⟩ hw
  have hD : 0 < D := by dsimp [D]; linarith [hspeed.1]
  have hRD : R / D ≤ 2 := (div_le_iff₀ hD).mpr (by dsimp [R, D]; linarith [(abs_le.mp hr).2, hspeed.1])
  have htR : (m - 1) / R ≤ 1 := by
    apply (div_le_iff₀ hR).mpr
    have he := coreRadius_sq m v
    unfold coreEnergy at he
    dsimp [R]
    nlinarith only [he, hR, hm, sq_nonneg v]
  have htR0 : 0 ≤ (m - 1) / R := div_nonneg (sub_nonneg.mpr hm) hR.le
  have hDi : 1 / D ≤ 2 / k := (div_le_div_iff₀ hD hk0).mpr (by dsimp [D]; linarith [hspeed.1])
  have hC : |coupling u v w| ≤ B := by
    rw [abs_le]
    dsimp [coupling, B]
    constructor <;> nlinarith only [mul_nonneg hu.1 (add_nonneg hv.1.le hw.1), sq_nonneg u]
  have hB : 0 ≤ B := add_nonneg (mul_nonneg hu.1 (add_nonneg hv.1.le hw.1)) (sq_nonneg u)
  have h1 : |-coupling u v w * (R / D)| ≤ 2 * B := by
    rw [abs_mul, abs_neg, abs_of_pos (div_pos hR hD)]
    have H := mul_le_mul hC hRD (div_nonneg hR.le hD.le) hB
    linarith only [H]
  have hnum : (m - 1) / R * (u - w) ^ 2 ≤ u ^ 2 + w ^ 2 := by
    have H := mul_le_mul_of_nonneg_right htR (sq_nonneg (u - w))
    nlinarith only [H, mul_nonneg hu.1 hw.1]
  have h2 : |((m - 1) / R * (u - w) ^ 2) / D| ≤ (u ^ 2 + w ^ 2) * (2 / k) := by
    rw [abs_of_nonneg (div_nonneg (mul_nonneg htR0 (sq_nonneg _)) hD.le)]
    calc
      _ ≤ (u ^ 2 + w ^ 2) / D := div_le_div_of_nonneg_right hnum hD.le
      _ = (u ^ 2 + w ^ 2) * (1 / D) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hDi (by positivity)
  have H := (abs_add_le (-coupling u v w * (R / D)) (((m - 1) / R * (u - w) ^ 2) / D)).trans
    (add_le_add h1 h2)
  have heq : (-coupling u v w * R + (m - 1) / R * (u - w) ^ 2) / D =
      -coupling u v w * (R / D) + ((m - 1) / R * (u - w) ^ 2) / D := by ring
  change |(-coupling u v w * R + (m - 1) / R * (u - w) ^ 2) / D| ≤ _
  rw [heq]
  apply H.trans
  have hku : u ^ 2 / k ≤ u ^ 2 := div_le_self (sq_nonneg u) (by linarith)
  have hkw : 0 ≤ w ^ 2 / k := by positivity
  have hBV : 0 ≤ u * (v + w) := mul_nonneg hu.1 (add_nonneg hv.1.le hw.1)
  calc
    2 * B + (u ^ 2 + w ^ 2) * (2 / k) = 2 * B + 2 * (u ^ 2 / k) + 2 * (w ^ 2 / k) := by ring
    _ ≤ 4 * (u * (v + w) + u ^ 2 + w ^ 2 / k) := by dsimp [B]; linarith only [hku, hkw, hBV]

theorem entrance_radius_budget_small {k u v w : ℝ} (hk : 7 / 4 ≤ k)
    (hu : 0 ≤ u ∧ u ≤ 1 / 10000) (hv : 0 ≤ v ∧ v ≤ 1)
    (hw : 0 ≤ w ∧ w ≤ 1 / 10000) :
    12 / k * (u * (v + w) + u ^ 2 + w ^ 2) < k / 200 := by
  have hk0 : 0 < k := by linarith
  have hprod : u * (v + w) ≤ (1 / 10000 : ℝ) * (1 + 1 / 10000) :=
    mul_le_mul hu.2 (add_le_add hv.2 hw.2) (add_nonneg hv.1 hw.1) (by norm_num)
  have hu2 := pow_le_pow_left₀ hu.1 hu.2 2
  have hw2 := pow_le_pow_left₀ hw.1 hw.2 2
  have hk2 := mul_nonneg (sub_nonneg.mpr hk) (show 0 ≤ k + 7 / 4 by linarith)
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ hk0).mpr
  nlinarith only [hprod, hu2, hw2, hk2]

end BianchiIX
