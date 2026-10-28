import BianchiIX.Algebra.Flow
import Mathlib.Tactic.LinearCombination

noncomputable section

namespace BianchiIX

def taubRadiusSq (s b c : ℝ) : ℝ := s ^ 2 + (b - c) ^ 2

def taubRadiusHalfRate (p s n b c : ℝ) : ℝ :=
  s * shearMinus s n b c + (b - c) * (rateTwo p s * b - rateThree p s * c)

theorem taubRadiusSq_nonneg (s b c : ℝ) : 0 ≤ taubRadiusSq s b c :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

/-- A polynomial version of the radial identity, valid even on the Taub invariant subspace. -/
theorem taubRadiusHalfRate_identity {p s n b c : ℝ} (hc : constraint p s n b c = 1) :
    (1 - p) * taubRadiusHalfRate p s n b c =
      -p * (b - c) ^ 2 * taubRadiusSq s b c +
        n * ((n - 2 * (b + c)) * ((1 - p) * taubRadiusSq s b c - (b - c) ^ 2) +
          (1 - p) * Real.sqrt 3 * s * (b - c)) := by
  unfold constraint shearSq curvature at hc
  unfold taubRadiusHalfRate taubRadiusSq shearMinus rateTwo rateThree shearSq curvature
  linear_combination p * (b - c) ^ 2 * hc

theorem taub_negative_wall_rate {p s : ℝ} (hp : p ≤ -1 / 2) : rateOne p s ≤ -5 / 4 := by
  unfold rateOne shearSq
  nlinarith [sq_nonneg (p + 1 / 2), sq_nonneg s]

/-- The radial loss is at most five times the decaying wall; no division by the radius is needed. -/
theorem taubRadiusHalfRate_lower {p s n b c : ℝ}
    (hc : constraint p s n b c = 1) (hp : p ≤ -1 / 2) (hn : 0 ≤ n)
    (hwall : n ^ 2 + b ^ 2 + c ^ 2 ≤ 2) :
    -5 * n * taubRadiusSq s b c ≤ taubRadiusHalfRate p s n b c := by
  let R := taubRadiusSq s b c
  let A := (1 - p) * R - (b - c) ^ 2
  have hR : 0 ≤ R := taubRadiusSq_nonneg s b c
  have hvR : (b - c) ^ 2 ≤ R := by dsimp [R, taubRadiusSq]; nlinarith [sq_nonneg s]
  have hP : 0 < 1 - p := by linarith only [hp]
  have hA : 0 ≤ A := by
    have H := mul_nonneg (by linarith only [hp] : 0 ≤ -p) hR
    dsimp [A]
    nlinarith only [hvR, H]
  have hsum : b + c ≤ 2 := by nlinarith [sq_nonneg n, sq_nonneg (b - c), sq_nonneg (b + c - 2)]
  have hq : -4 ≤ n - 2 * (b + c) := by linarith only [hn, hsum]
  have hprod : -4 * (1 - p) * R ≤ (n - 2 * (b + c)) * A := by
    have H := mul_le_mul_of_nonneg_right hq hA
    dsimp [A] at H
    dsimp [A]
    nlinarith only [H, sq_nonneg (b - c)]
  have hcross : -R ≤ Real.sqrt 3 * s * (b - c) := by
    have hsqrt : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have H := sq_nonneg (2 * s + Real.sqrt 3 * (b - c))
    dsimp [R, taubRadiusSq]
    nlinarith [sq_nonneg (b - c)]
  have hcrossP := mul_le_mul_of_nonneg_left hcross hP.le
  have hterms : -5 * (1 - p) * R ≤
      (n - 2 * (b + c)) * A + (1 - p) * Real.sqrt 3 * s * (b - c) := by
    nlinarith only [hprod, hcrossP]
  have htermsN := mul_le_mul_of_nonneg_left hterms hn
  have hgood := mul_nonneg (mul_nonneg (by linarith only [hp] : 0 ≤ -p) (sq_nonneg (b - c))) hR
  have Hid := taubRadiusHalfRate_identity hc
  change (1 - p) * taubRadiusHalfRate p s n b c =
    -p * (b - c) ^ 2 * R + n * ((n - 2 * (b + c)) * A + (1 - p) * Real.sqrt 3 * s * (b - c)) at Hid
  apply (mul_le_mul_iff_right₀ hP).mp
  change (1 - p) * (-5 * n * R) ≤ (1 - p) * taubRadiusHalfRate p s n b c
  nlinarith only [Hid, htermsN, hgood]

end BianchiIX
