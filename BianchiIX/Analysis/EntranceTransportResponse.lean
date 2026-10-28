import BianchiIX.Analysis.EntranceTransportWeights

noncomputable section

namespace BianchiIX

theorem entrance_active_phase_response {A F K H J G Q k : ℝ}
    (hF : 0 ≤ F) (hK : 0 ≤ K) (hH : 0 ≤ H ∧ H ≤ 2) (hk : 1 ≤ k)
    (hJ : J / k ≤ 21 * H) (hG : |G| ≤ A * H)
    (hresponse : |Q - G| ≤ 2 * (K * J / k) + 2 * (F * H / k ^ 2) * |G|) :
    |Q| ≤ (A * (1 + 4 * F) + 42 * K) * H := by
  have hsource : K * J / k ≤ 21 * K * H := by
    simpa only [mul_div_assoc, mul_assoc, mul_left_comm K 21] using mul_le_mul_of_nonneg_left hJ hK
  have hphase : F * H / k ^ 2 ≤ 2 * F := by
    calc
      _ ≤ F * H := div_le_self (mul_nonneg hF hH.1) (one_le_pow₀ hk)
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hH.2 hF]
  have hinc : |Q - G| ≤ 42 * K * H + 4 * F * |G| := by
    nlinarith only [hresponse, hsource, mul_le_mul_of_nonneg_right hphase (abs_nonneg G)]
  have htriangle : |Q| ≤ |Q - G| + |G| := by simpa using abs_add_le (Q - G) G
  have HG := mul_le_mul_of_nonneg_left hG (show 0 ≤ 1 + 4 * F by positivity)
  nlinarith only [hinc, htriangle, HG]

theorem entrance_active_wall_response {T A K H J G R A₀ k u w l : ℝ}
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hK : 0 ≤ K) (hH : 0 ≤ H)
    (hk : 0 ≤ k) (hu : 0 ≤ u) (hw : 0 ≤ w) (hl : 0 ≤ l)
    (hinitial : A₀ ≤ 12 * k * u + 9 * w) (hJ : J / k ≤ 21 * H) (hG : |G| ≤ A * H)
    (hresponse : R ≤ T * (A₀ + 2 * l * (|G| + K * J / k))) :
    R ≤ T * (21 + 2 * (A + 21 * K)) * (k * u + w + l * H) := by
  have hsource : K * J / k ≤ 21 * K * H := by
    simpa only [mul_div_assoc, mul_assoc, mul_left_comm K 21] using mul_le_mul_of_nonneg_left hJ hK
  have HG : |G| + K * J / k ≤ (A + 21 * K) * H :=
    (add_le_add hG hsource).trans_eq (by ring)
  have Hscaled := mul_le_mul_of_nonneg_left HG (show 0 ≤ 2 * l by positivity)
  have HC : A₀ + 2 * l * (|G| + K * J / k) ≤
      (21 + 2 * (A + 21 * K)) * (k * u + w + l * H) := by
    have hnonneg : 0 ≤ 2 * (A + 21 * K) * (k * u + w) := by positivity
    nlinarith only [hinitial, Hscaled, hnonneg, mul_nonneg hk hu, hw, mul_nonneg hl hH]
  exact hresponse.trans ((mul_le_mul_of_nonneg_left HC hT).trans_eq (by ring))

theorem entrance_active_log_columns {C k u v w l H p q βU βW : ℝ}
    (hC : 0 ≤ C) (hk : 1 ≤ k) (hu : u ≤ 1) (hv : 0 < v) (hw : w ≤ 1)
    (hLH : l * H ≤ 2) (hU : |βU| ≤ 12 * k) (hW : |βW| ≤ 9)
    (herror : |v * p + βU| + k ^ 2 * |v * q + βW| ≤ C * (k * u + w + l * H)) :
    |p| ≤ (12 + 4 * C) * k / v ∧ |q| ≤ (12 + 4 * C) / v := by
  have hk0 : 0 < k := by linarith
  have hsum : k * u + w + l * H ≤ 4 * k := by
    nlinarith only [mul_le_mul_of_nonneg_left hu hk0.le, hw, hLH, hk]
  have HE : |v * p + βU| + k ^ 2 * |v * q + βW| ≤ 4 * C * k :=
    herror.trans ((mul_le_mul_of_nonneg_left hsum hC).trans_eq (by ring))
  have hstrong : |v * p| ≤ |v * p + βU| + |βU| := by
    simpa using abs_sub (v * p + βU) βU
  have hweak : |v * q| ≤ |v * q + βW| + |βW| := by
    simpa using abs_sub (v * q + βW) βW
  have hwerr : |v * q + βW| ≤ 4 * C := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hk0)).mp
    have hkk : k ≤ k ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_left hk hk0.le]
    have HC := mul_le_mul_of_nonneg_left hkk (show 0 ≤ 4 * C by positivity)
    nlinarith only [HE, HC, abs_nonneg (v * p + βU)]
  constructor
  · apply (le_div_iff₀ hv).mpr
    rw [abs_mul, abs_of_pos hv] at hstrong
    nlinarith only [hstrong, hU, HE, mul_nonneg (sq_nonneg k) (abs_nonneg (v * q + βW))]
  · apply (le_div_iff₀ hv).mpr
    rw [abs_mul, abs_of_pos hv] at hweak
    nlinarith only [hweak, hwerr, hW]

end BianchiIX
