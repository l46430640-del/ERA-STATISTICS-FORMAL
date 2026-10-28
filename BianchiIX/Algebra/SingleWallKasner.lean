import BianchiIX.Algebra.SingleStrongWall

noncomputable section

namespace BianchiIX

def singleWallBeta (p s : ℝ) : ℝ := s / (2 - p)

def singleWallXi (β p : ℝ) : ℝ := (1 + β ^ 2) * p - 2 * β ^ 2

def singleWallChi (β : ℝ) : ℝ := Real.sqrt (1 - 3 * β ^ 2)

def singleWallIncomingPlus (β : ℝ) : ℝ := (2 * β ^ 2 + singleWallChi β) / (1 + β ^ 2)

def singleWallIncomingMinus (β : ℝ) : ℝ := β * (2 - singleWallIncomingPlus β)

theorem singleWall_beta_line {p s : ℝ} (hp : 2 - p ≠ 0) :
    s = singleWallBeta p s * (2 - p) := by
  exact (div_mul_cancel₀ s hp).symm

theorem singleWall_shear_bounds {p s n : ℝ} (hc : constraint p s n 0 0 = 1) :
    -1 ≤ p ∧ p ≤ 1 ∧ 1 ≤ 2 - p ∧ 2 - p ≤ 3 := by
  have H : p ^ 2 + s ^ 2 + n ^ 2 = 1 := by simpa [constraint, shearSq, curvature] using hc
  have hlo : -1 ≤ p := by nlinarith only [H, sq_nonneg s, sq_nonneg n]
  have hhi : p ≤ 1 := by nlinarith only [H, sq_nonneg s, sq_nonneg n]
  exact ⟨hlo, hhi, by linarith only [hhi], by linarith only [hlo]⟩

/-- The single-wall constraint and growth rate in its conserved straight-line coordinate. -/
theorem singleWall_reduction {p s n β : ℝ}
    (hc : constraint p s n 0 0 = 1) (hline : s = β * (2 - p)) :
    (1 + β ^ 2) * n ^ 2 + singleWallXi β p ^ 2 = 1 - 3 * β ^ 2 ∧
      rateOne p s = (2 - p) * singleWallXi β p ∧
      (1 + β ^ 2) * shearPlus p n 0 0 = -(2 - singleWallXi β p) * n ^ 2 := by
  have H : p ^ 2 + (β * (2 - p)) ^ 2 + n ^ 2 = 1 := by
    simpa [constraint, shearSq, curvature, hline] using hc
  refine ⟨?_, ?_, ?_⟩
  · dsimp [singleWallXi]
    linear_combination (1 + β ^ 2) * H
  · rw [hline]
    dsimp [rateOne, shearSq, singleWallXi]
    ring
  · dsimp [shearPlus, curvature, singleWallXi]
    ring

theorem singleWall_upward_bounds {p s n β g : ℝ}
    (hc : constraint p s n 0 0 = 1) (hline : s = β * (2 - p))
    (hg : 0 < g) (hr : g ≤ rateOne p s) :
    1 ≤ 1 + β ^ 2 ∧ 1 + β ^ 2 ≤ 4 / 3 ∧
      singleWallChi β ^ 2 = 1 - 3 * β ^ 2 ∧
      g / 3 ≤ singleWallXi β p ∧ 0 < singleWallXi β p ∧
      singleWallXi β p ≤ singleWallChi β ∧
      singleWallXi β p = Real.sqrt (singleWallChi β ^ 2 - (1 + β ^ 2) * n ^ 2) := by
  obtain ⟨heq, hrate, _⟩ := singleWall_reduction hc hline
  obtain ⟨_, _, hp1, hp3⟩ := singleWall_shear_bounds hc
  have ha : 0 < 1 + β ^ 2 := by positivity
  have hrad : 0 ≤ 1 - 3 * β ^ 2 := by
    nlinarith only [heq, mul_nonneg ha.le (sq_nonneg n), sq_nonneg (singleWallXi β p)]
  have hχ : singleWallChi β ^ 2 = 1 - 3 * β ^ 2 := Real.sq_sqrt hrad
  have hχ0 : 0 ≤ singleWallChi β := Real.sqrt_nonneg _
  have hξ : 0 < singleWallXi β p := by nlinarith only [hr, hg, hrate, hp1]
  have hξg : g / 3 ≤ singleWallXi β p := by
    nlinarith only [hr, hrate, mul_le_mul_of_nonneg_right hp3 hξ.le]
  have hξχ : singleWallXi β p ≤ singleWallChi β := by
    nlinarith only [heq, hχ, hχ0, mul_nonneg ha.le (sq_nonneg n)]
  refine ⟨by nlinarith only [sq_nonneg β], by linarith only [hrad], hχ, hξg, hξ, hξχ, ?_⟩
  rw [show singleWallChi β ^ 2 - (1 + β ^ 2) * n ^ 2 = singleWallXi β p ^ 2 by linarith only [heq, hχ]]
  exact (Real.sqrt_sq hξ.le).symm

theorem singleWall_incoming_circle {β : ℝ} (hβ : 0 ≤ 1 - 3 * β ^ 2) :
    shearSq (singleWallIncomingPlus β) (singleWallIncomingMinus β) = 1 ∧
      singleWallXi β (singleWallIncomingPlus β) = singleWallChi β := by
  have ha : 1 + β ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hχ : singleWallChi β ^ 2 = 1 - 3 * β ^ 2 := Real.sq_sqrt hβ
  refine ⟨?_, ?_⟩
  · dsimp [shearSq, singleWallIncomingMinus, singleWallIncomingPlus]
    field_simp
    linear_combination (1 + β ^ 2) * hχ
  · dsimp [singleWallXi, singleWallIncomingPlus]
    field_simp
    ring

/-- The incoming displacement follows from factoring the two roots of the constraint. -/
theorem singleWall_incoming_displacement {p s n β g : ℝ}
    (hc : constraint p s n 0 0 = 1) (hline : s = β * (2 - p))
    (hg : 0 < g) (hr : g ≤ rateOne p s) :
    singleWallIncomingPlus β - p = n ^ 2 / (singleWallChi β + singleWallXi β p) ∧
      singleWallIncomingMinus β - s = -β * (singleWallIncomingPlus β - p) ∧
      Real.sqrt ((singleWallIncomingPlus β - p) ^ 2 + (singleWallIncomingMinus β - s) ^ 2) =
        Real.sqrt (1 + β ^ 2) * n ^ 2 / (singleWallChi β + singleWallXi β p) ∧
      Real.sqrt ((singleWallIncomingPlus β - p) ^ 2 + (singleWallIncomingMinus β - s) ^ 2) ≤
        2 * n ^ 2 / g := by
  obtain ⟨_, haMax, hχ, hξg, hξ, hξχ, _⟩ := singleWall_upward_bounds hc hline hg hr
  have heq := (singleWall_reduction hc hline).1
  have ha : 0 < 1 + β ^ 2 := by positivity
  have hden : 0 < singleWallChi β + singleWallXi β p := by linarith only [hξ, hξχ]
  have hp : singleWallIncomingPlus β - p = n ^ 2 / (singleWallChi β + singleWallXi β p) := by
    apply (eq_div_iff hden.ne').mpr
    apply mul_left_injective₀ ha.ne'
    have H : (singleWallIncomingPlus β - p) * (singleWallChi β + singleWallXi β p) * (1 + β ^ 2) =
        singleWallChi β ^ 2 - singleWallXi β p ^ 2 := by
      dsimp [singleWallIncomingPlus, singleWallXi]
      field_simp
      ring
    dsimp only
    rw [H]
    nlinarith only [heq, hχ]
  have hs : singleWallIncomingMinus β - s = -β * (singleWallIncomingPlus β - p) := by
    rw [hline]
    dsimp [singleWallIncomingMinus]
    ring
  have hdiff0 : 0 ≤ singleWallIncomingPlus β - p := by rw [hp]; positivity
  have hdist : Real.sqrt ((singleWallIncomingPlus β - p) ^ 2 + (singleWallIncomingMinus β - s) ^ 2) =
      Real.sqrt (1 + β ^ 2) * n ^ 2 / (singleWallChi β + singleWallXi β p) := by
    rw [hs, show (singleWallIncomingPlus β - p) ^ 2 + (-β * (singleWallIncomingPlus β - p)) ^ 2 =
        (1 + β ^ 2) * (singleWallIncomingPlus β - p) ^ 2 by ring,
      Real.sqrt_mul ha.le, Real.sqrt_sq hdiff0, hp]
    ring
  refine ⟨hp, hs, hdist, ?_⟩
  rw [hdist]
  have hsqrt : Real.sqrt (1 + β ^ 2) ≤ 4 / 3 := by
    have H := Real.sq_sqrt ha.le
    have H0 := Real.sqrt_nonneg (1 + β ^ 2)
    nlinarith only [H, H0, haMax]
  have hbound : Real.sqrt (1 + β ^ 2) * g ≤ 2 * (singleWallChi β + singleWallXi β p) := by
    nlinarith only [mul_le_mul_of_nonneg_right hsqrt hg.le, hξg, hξχ]
  apply (div_le_div_iff₀ hden hg).mpr
  nlinarith only [mul_le_mul_of_nonneg_right hbound (sq_nonneg n)]

end BianchiIX
