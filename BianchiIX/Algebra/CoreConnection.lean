import BianchiIX.Algebra.CoreCrossing
import BianchiIX.Algebra.MatchingPhase

noncomputable section

namespace BianchiIX

theorem core_exit_connection_radial_range {k m : ℝ} (hk : 6 ≤ k) (hm : m < 1)
    (hE : |coreEnergy m 1 - k ^ 2| ≤ 1 / 8) : 4 ≤ -m ∧ k / 2 ≤ -m ∧ -m < k := by
  have hElo := (abs_le.mp hE).1
  have hEhi := (abs_le.mp hE).2
  dsimp [coreEnergy] at hElo hEhi
  have hm4 : 4 ≤ -m := by
    by_contra H
    have hm5 : 1 - m < 5 := by linarith only [H]
    have hs : (1 - m) ^ 2 < 5 ^ 2 :=
      (sq_lt_sq₀ (by linarith only [hm] : 0 ≤ 1 - m) (by norm_num)).mpr hm5
    nlinarith only [hs, hElo, hk, sq_nonneg (k - 6)]
  refine ⟨hm4, ?_, ?_⟩
  · by_contra H
    have hs : (1 - m) ^ 2 < (k / 2 + 1) ^ 2 :=
      (sq_lt_sq₀ (by linarith only [hm] : 0 ≤ 1 - m) (by linarith only [hk])).mpr (by linarith only [H])
    nlinarith only [hs, hElo, hk, sq_nonneg (k - 6)]
  · by_contra H
    have hs : k ^ 2 ≤ (-m) ^ 2 := (sq_le_sq₀ (by linarith only [hk]) (by linarith only [hm4])).mpr (by linarith only [H])
    nlinarith only [hs, hEhi, hm4]

theorem core_connection_phase_error {k μ K n b : ℝ} (hk : 0 < k) (hμ : 0 < μ)
    (hkμ : k ≤ 2 * μ) (hb : 0 ≤ b)
    (hcore : |K - k| ≤ 16 / k * b) (hconn : |n - K + 2| ≤ 24 * b / μ) :
    |n - (k - 2)| ≤ 64 * b / k := by
  have H : 24 * b / μ ≤ 48 * b / k := by
    apply (div_le_div_iff₀ hμ hk).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hkμ hb]
  calc
    _ = |(n - K + 2) + (K - k)| := by congr 1; ring
    _ ≤ |n - K + 2| + |K - k| := abs_add_le _ _
    _ ≤ 48 * b / k + 16 / k * b := add_le_add (hconn.trans H) hcore
    _ = _ := by ring

theorem core_connection_phase_decrease {k n u w : ℝ} (hk : 6 ≤ k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k)
    (herr : |n - (k - 2)| ≤ 64 * (u + w ^ 2) / k) : 1 ≤ k - n ∧ k - n ≤ 3 := by
  have hk0 : 0 < k := by linarith only [hk]
  have hu0 : u ≤ 1 / 10000 := hu.2.trans (div_le_self (by norm_num) (by linarith only [hk]))
  have hw0 : w ≤ 1 / 10000 := hw.2.trans (div_le_self (by norm_num) (by linarith only [hk]))
  have hw2 : w ^ 2 ≤ w := by nlinarith only [hw.1, hw0]
  have H : 64 * (u + w ^ 2) / k ≤ 1 := (div_le_one hk0).mpr (by linarith only [hu0, hw0, hw2, hk])
  have Ha := abs_le.mp (herr.trans H)
  constructor <;> linarith only [Ha.1, Ha.2]

end BianchiIX
