import BianchiIX.Analysis.ConnectionEndpointScales
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace BianchiIX

/-- An exponential core loss pays for every positive power of the incoming amplitude. -/
theorem rpow_div_le_core_loss {a b k c p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hk : 2 ≤ k) (hc : 0 < c) (hp : 0 < p) (hdec : b ≤ Real.exp (-c / k) * a) :
    a ^ p / k ≤ (1 + p * c / 2) / (p * c) * (a ^ p - b ^ p) := by
  have hk0 : 0 < k := by linarith only [hk]
  have hpc : 0 < p * c := mul_pos hp hc
  have hz : 0 ≤ p * c / k := (div_pos hpc hk0).le
  have hpow : b ^ p ≤ Real.exp (-(p * c / k)) * a ^ p := by
    have H := Real.rpow_le_rpow hb hdec hp.le
    rw [Real.mul_rpow (Real.exp_pos _).le ha, ← Real.exp_mul] at H
    convert! H using 1
    congr 2
    ring
  have hab : b ^ p ≤ a ^ p := hpow.trans
    ((mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hz))
      (Real.rpow_nonneg ha p)).trans_eq (one_mul _))
  have H := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 1 + p * c / k)
  have He := mul_le_mul_of_nonneg_right (affine_mul_exp_neg_le_one (p * c / k))
    (Real.rpow_nonneg ha p)
  have hpaid : (p * c / k) * a ^ p ≤ (1 + p * c / k) * (a ^ p - b ^ p) := by
    nlinarith only [H, He]
  have hzmax : p * c / k ≤ p * c / 2 :=
    div_le_div_of_nonneg_left hpc.le (by norm_num) hk
  have Hmax := mul_le_mul_of_nonneg_right (add_le_add_left hzmax 1) (sub_nonneg.mpr hab)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hpc).mpr
  calc
    a ^ p / k * (p * c) = (p * c / k) * a ^ p := by ring
    _ ≤ (1 + p * c / k) * (a ^ p - b ^ p) := hpaid
    _ ≤ (1 + p * c / 2) * (a ^ p - b ^ p) := by simpa only [add_comm] using Hmax

/-- Nonincreasing intermediate connections make the core losses telescope without a length factor. -/
theorem sum_rpow_div_le_core_losses {a b k : ℕ → ℝ} {c p : ℝ}
    (hc : 0 < c) (hp : 0 < p) (n : ℕ)
    (ha : ∀ j ≤ n, 0 ≤ a j) (hk : ∀ j < n, 2 ≤ k j)
    (hdec : ∀ j < n, b j ≤ Real.exp (-c / k j) * a j)
    (hconn : ∀ j < n, a (j + 1) ≤ b j) :
    ∑ j ∈ Finset.range n, a j ^ p / k j ≤
      (1 + p * c / 2) / (p * c) * (a 0 ^ p - a n ^ p) := by
  let A := (1 + p * c / 2) / (p * c)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hstep (j : ℕ) (hj : j < n) : a j ^ p / k j ≤ A * (a j ^ p - a (j + 1) ^ p) := by
    have hnext : 0 ≤ a (j + 1) := ha _ (by omega)
    have H := rpow_div_le_core_loss (ha j hj.le) (hnext.trans (hconn j hj))
      (hk j hj) hc hp (hdec j hj)
    exact H.trans (mul_le_mul_of_nonneg_left
      (sub_le_sub_left (Real.rpow_le_rpow hnext (hconn j hj) hp.le) _) hA)
  have htel (m : ℕ) : ∑ j ∈ Finset.range m, (a j ^ p - a (j + 1) ^ p) = a 0 ^ p - a m ^ p := by
    induction m with
    | zero => simp
    | succ m hm => rw [Finset.sum_range_succ, hm]; ring
  calc
    _ ≤ ∑ j ∈ Finset.range n, A * (a j ^ p - a (j + 1) ^ p) :=
      Finset.sum_le_sum fun j hj => hstep j (Finset.mem_range.mp hj)
    _ = A * (a 0 ^ p - a n ^ p) := by rw [← Finset.mul_sum, htel]

end BianchiIX
