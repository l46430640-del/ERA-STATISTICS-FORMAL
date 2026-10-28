import BianchiIX.Algebra.MatchingPhase
import BianchiIX.Algebra.StableBoundaryBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section

namespace BianchiIX

def stableWeakRadius (m w : ℝ) : ℝ := phaseNorm (m + 1) w

def stableCorrectionA (m : ℝ) : ℝ := m / (m ^ 2 - 1)

def stableCorrectionC (m : ℝ) : ℝ := -2 / (m + 1)

def stableCorrectedPhase (m u w : ℝ) : ℝ :=
  stableWeakRadius m w - 1 + stableCorrectionA m * u ^ 2 + stableCorrectionC m * u * w

def stableCorrectedGradient (m u w : ℝ) : Fin 3 → ℝ :=
  ![(m + 1) / stableWeakRadius m w - (m ^ 2 + 1) / (m ^ 2 - 1) ^ 2 * u ^ 2 +
      2 / (m + 1) ^ 2 * u * w,
    2 * stableCorrectionA m * u + stableCorrectionC m * w,
    w / stableWeakRadius m w + stableCorrectionC m * u]

theorem stableWeakRadius_pos {m w : ℝ} (hm : -1 < m) : 0 < stableWeakRadius m w :=
  phaseNorm_pos (by linarith : 0 < m + 1)

theorem stableWeakRadius_sq (m w : ℝ) :
    stableWeakRadius m w ^ 2 = (m + 1) ^ 2 + w ^ 2 := phaseNorm_sq _ _

theorem stableCorrectedPhase_zero {m : ℝ} (hm : -1 ≤ m) :
    stableCorrectedPhase m 0 0 = m := by
  simp only [stableCorrectedPhase, stableWeakRadius, phaseNorm_zero (by linarith : 0 ≤ m + 1),
    zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero]
  ring

theorem stableWeakRadius_quartic_defect {m w : ℝ} (hm : -1 < m) :
    stableWeakRadius m w - (m + 1) - w ^ 2 / (2 * (m + 1)) =
      -w ^ 4 / (2 * (m + 1) * (stableWeakRadius m w + (m + 1)) ^ 2) := by
  have hL : 0 < m + 1 := by linarith
  have hS := stableWeakRadius_pos (w := w) hm
  have hsum : stableWeakRadius m w + (m + 1) ≠ 0 := ne_of_gt (add_pos hS hL)
  have hd := phaseNorm_defect (b := w) hL
  change stableWeakRadius m w - (m + 1) = w ^ 2 / (stableWeakRadius m w + (m + 1)) at hd
  rw [hd]
  field_simp
  nlinarith only [stableWeakRadius_sq m w]

theorem hasDerivAt_stableCorrectionA {m : ℝ} (hm : 1 < m) :
    HasDerivAt stableCorrectionA (-(m ^ 2 + 1) / (m ^ 2 - 1) ^ 2) m := by
  have hd : m ^ 2 - 1 ≠ 0 := by nlinarith
  convert! (hasDerivAt_id m).div (((hasDerivAt_id m).pow 2).sub_const 1) hd using 1
  dsimp
  congr 1
  ring

theorem hasDerivAt_stableCorrectionC {m : ℝ} (hm : -1 < m) :
    HasDerivAt stableCorrectionC (2 / (m + 1) ^ 2) m := by
  have hd : m + 1 ≠ 0 := by linarith
  convert! (hasDerivAt_const m (-2 : ℝ)).div ((hasDerivAt_id m).add_const 1) hd using 1
  simp

theorem hasDerivAt_stableWeakRadius {m w : ℝ → ℝ} {m' w' t : ℝ}
    (hm : HasDerivAt m m' t) (hw : HasDerivAt w w' t) (hpos : -1 < m t) :
    HasDerivAt (fun s => stableWeakRadius (m s) (w s))
      (((m t + 1) * m' + w t * w') / stableWeakRadius (m t) (w t)) t := by
  have hn : (m t + 1) ^ 2 + w t ^ 2 ≠ 0 := by
    have h : 0 < m t + 1 := by linarith
    positivity
  convert! ((((hm.add_const 1).pow 2).add (hw.pow 2)).sqrt hn) using 1
  dsimp [stableWeakRadius, phaseNorm]
  ring

theorem hasDerivAt_stableCorrectedPhase {m u w : ℝ → ℝ} {m' u' w' t : ℝ}
    (hm : HasDerivAt m m' t) (hu : HasDerivAt u u' t) (hw : HasDerivAt w w' t)
    (hpos : 1 < m t) :
    HasDerivAt (fun s => stableCorrectedPhase (m s) (u s) (w s))
      (stableCorrectedGradient (m t) (u t) (w t) 0 * m' +
        stableCorrectedGradient (m t) (u t) (w t) 1 * u' +
        stableCorrectedGradient (m t) (u t) (w t) 2 * w') t := by
  have hS := hasDerivAt_stableWeakRadius hm hw (by linarith)
  have hA := (hasDerivAt_stableCorrectionA hpos).comp t hm
  have hC := (hasDerivAt_stableCorrectionC (by linarith : -1 < m t)).comp t hm
  convert! ((hS.sub_const 1).add (hA.mul (hu.pow 2))).add ((hC.mul hu).mul hw) using 1
  dsimp [stableCorrectedGradient]
  ring

theorem contDiffAt_stableCorrectedPhase (n : WithTop ℕ∞) {y : Fin 3 → ℝ}
    (hm : 1 < y 0) :
    ContDiffAt ℝ n (fun z : Fin 3 → ℝ => stableCorrectedPhase (z 0) (z 1) (z 2)) y := by
  have hL : y 0 + 1 ≠ 0 := by linarith
  have hD : y 0 ^ 2 - 1 ≠ 0 := by nlinarith
  have hS : (y 0 + 1) ^ 2 + y 2 ^ 2 ≠ 0 := by
    have h : 0 < y 0 + 1 := by linarith
    positivity
  unfold stableCorrectedPhase stableWeakRadius phaseNorm stableCorrectionA stableCorrectionC
  fun_prop

end BianchiIX
