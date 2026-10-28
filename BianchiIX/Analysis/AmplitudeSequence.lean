import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def eraAmplitude (B : ℝ) (m : ℕ) : ℝ := B ^ ((4 / 3 : ℝ) ^ m)

@[simp] theorem eraAmplitude_zero (B : ℝ) : eraAmplitude B 0 = B := by
  simp [eraAmplitude]

theorem eraAmplitude_pos {B : ℝ} (hB : 0 < B) (m : ℕ) : 0 < eraAmplitude B m :=
  Real.rpow_pos_of_pos hB _

theorem eraAmplitude_le {B : ℝ} (hB : 0 ≤ B) (hB1 : B ≤ 1) (m : ℕ) : eraAmplitude B m ≤ B :=
  Real.rpow_le_self_of_le_one hB hB1 (one_le_pow₀ (by norm_num))

theorem eraAmplitude_succ {B : ℝ} (hB : 0 ≤ B) (m : ℕ) :
    eraAmplitude B (m + 1) = eraAmplitude B m ^ (4 / 3 : ℝ) := by
  simp only [eraAmplitude, pow_succ, Real.rpow_mul hB]

theorem eraAmplitude_power_succ {B : ℝ} (hB : 0 < B) (p : ℝ) (m : ℕ) :
    eraAmplitude B (m + 1) ^ p = eraAmplitude B m ^ p * eraAmplitude B m ^ (p / 3) := by
  rw [eraAmplitude_succ hB.le, ← Real.rpow_mul (eraAmplitude_pos hB m).le,
    ← Real.rpow_add (eraAmplitude_pos hB m)]
  congr 1
  ring

theorem amplitude_power_budget {B Bmax η p : ℝ} (hB : 0 < B) (hmax : B ≤ Bmax)
    (hmax1 : Bmax ≤ 1) (hη : 0 ≤ η) (hηp : η ≤ p)
    (hsmall : Bmax ^ (η / 3) ≤ 1 / 2) : B ^ (p / 3) ≤ 1 / 2 := by
  exact ((Real.rpow_le_rpow_of_exponent_ge hB (hmax.trans hmax1)
    (by linarith : η / 3 ≤ p / 3)).trans
      (Real.rpow_le_rpow hB.le hmax (by positivity))).trans hsmall

theorem amplitude_halving_of_small_beta {B η : ℝ} (hB : 0 ≤ B)
    (hsmall : B ^ η < 1 / 160) : B ^ (η / 3) ≤ 1 / 2 := by
  have hcube : (B ^ (η / 3)) ^ (3 : ℕ) = B ^ η := by
    rw [← Real.rpow_mul_natCast hB]
    congr 1
    norm_num
  by_contra h
  have hle : (1 / 2 : ℝ) ≤ B ^ (η / 3) := (lt_of_not_ge h).le
  have H := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hle 3
  rw [hcube] at H
  norm_num at H
  linarith

theorem eraAmplitude_power_halving {B p : ℝ} (hB : 0 < B) (hB1 : B ≤ 1) (hp : 0 ≤ p)
    (hsmall : B ^ (p / 3) ≤ 1 / 2) (m : ℕ) :
    eraAmplitude B (m + 1) ^ p ≤ (1 / 2) * eraAmplitude B m ^ p := by
  rw [eraAmplitude_power_succ hB]
  have hfactor : eraAmplitude B m ^ (p / 3) ≤ 1 / 2 :=
    (Real.rpow_le_rpow (eraAmplitude_pos hB m).le (eraAmplitude_le hB.le hB1 m)
      (by positivity)).trans hsmall
  nlinarith [mul_le_mul_of_nonneg_left hfactor (Real.rpow_nonneg (eraAmplitude_pos hB m).le p)]

/-- A nonnegative sequence with one-step contraction has a quantitative sum. -/
theorem summable_tsum_le_of_halving {u : ℕ → ℝ} (hu : ∀ m, 0 ≤ u m)
    (hstep : ∀ m, u (m + 1) ≤ (1 / 2) * u m) :
    Summable u ∧ (∑' m, u m) ≤ 2 * u 0 := by
  have hbound : ∀ m, u m ≤ (1 / 2 : ℝ) ^ m * u 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc
        u (m + 1) ≤ (1 / 2) * u m := hstep m
        _ ≤ (1 / 2) * ((1 / 2 : ℝ) ^ m * u 0) := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 2 : ℝ) ^ (m + 1) * u 0 := by rw [pow_succ]; ring
  have hgeom := summable_geometric_two.mul_right (u 0)
  have hs : Summable u := Summable.of_nonneg_of_le hu hbound hgeom
  refine ⟨hs, (hs.tsum_le_tsum hbound hgeom).trans_eq ?_⟩
  rw [tsum_mul_right, tsum_geometric_two]

theorem eraAmplitude_power_series {B p : ℝ} (hB : 0 < B) (hB1 : B ≤ 1) (hp : 0 ≤ p)
    (hsmall : B ^ (p / 3) ≤ 1 / 2) (k : ℕ) :
    (Summable fun m => eraAmplitude B (m + k) ^ p) ∧
      (∑' m, eraAmplitude B (m + k) ^ p) ≤ 2 * eraAmplitude B k ^ p := by
  have H := summable_tsum_le_of_halving
    (fun m => Real.rpow_nonneg (eraAmplitude_pos hB (m + k)).le p)
    (fun m => by
      simpa only [Nat.add_right_comm m 1 k] using
        eraAmplitude_power_halving hB hB1 hp hsmall (m + k))
  simpa only [Nat.zero_add] using H

theorem eraAmplitude_tendsto_zero {B : ℝ} (hB : 0 < B) (hB1 : B ≤ 1)
    (hsmall : B ^ (1 / 3 : ℝ) ≤ 1 / 2) : Tendsto (eraAmplitude B) atTop (𝓝 0) := by
  have H := (eraAmplitude_power_series (p := 1) hB hB1 (by norm_num) hsmall 0).1
  simpa only [Nat.add_zero, Real.rpow_one] using H.tendsto_atTop_zero

theorem eraAmplitude_series_of_small_beta {B η p : ℝ} (hB : 0 < B) (hB1 : B ≤ 1)
    (hη : 0 ≤ η) (hηp : η ≤ p) (hsmall : B ^ η < 1 / 160) (k : ℕ) :
    (Summable fun m => eraAmplitude B (m + k) ^ p) ∧
      (∑' m, eraAmplitude B (m + k) ^ p) ≤ 2 * eraAmplitude B k ^ p :=
  eraAmplitude_power_series hB hB1 (hη.trans hηp)
    (amplitude_power_budget hB le_rfl hB1 hη hηp (amplitude_halving_of_small_beta hB.le hsmall)) k

end BianchiIX
