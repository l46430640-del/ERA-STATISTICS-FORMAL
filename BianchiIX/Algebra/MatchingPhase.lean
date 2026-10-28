import BianchiIX.Algebra.ConnectionBounds
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section

namespace BianchiIX

def phaseNorm (a b : ℝ) : ℝ := Real.sqrt (a ^ 2 + b ^ 2)

def matchingPhase (m v w : ℝ) : ℝ := phaseNorm (m + 1) v + phaseNorm (m - 1) w - m

def matchingPhaseSlope (m v w : ℝ) : ℝ :=
  (m + 1) / phaseNorm (m + 1) v + (m - 1) / phaseNorm (m - 1) w - 1

def matchingPhaseWeight (m v w : ℝ) : ℝ :=
  m * matchingPhaseSlope m v w + v ^ 2 / phaseNorm (m + 1) v + w ^ 2 / phaseNorm (m - 1) w

def phaseNormKernel (a b : ℝ) : ℝ := 1 / (phaseNorm a b * (phaseNorm a b + a))

def matchingPhaseKernel (m v w : ℝ) : ℝ := phaseNormKernel (m + 1) v - phaseNormKernel (m - 1) w

def matchingPhaseRate (m u v w : ℝ) : ℝ :=
  (v * w) ^ 2 * matchingPhaseKernel m v w - u * matchingPhaseSlope m v w * (v - w) -
    coupling u v w * matchingPhaseWeight m v w

theorem phaseNorm_sq (a b : ℝ) : phaseNorm a b ^ 2 = a ^ 2 + b ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem phaseNorm_ge {a b : ℝ} (ha : 0 ≤ a) : a ≤ phaseNorm a b := by
  calc
    a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ phaseNorm a b := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg b))

theorem phaseNorm_pos {a b : ℝ} (ha : 0 < a) : 0 < phaseNorm a b :=
  ha.trans_le (phaseNorm_ge ha.le)

theorem phaseNorm_zero {a : ℝ} (ha : 0 ≤ a) : phaseNorm a 0 = a := by
  simp [phaseNorm, Real.sqrt_sq ha]

theorem phaseNorm_defect {a b : ℝ} (ha : 0 < a) :
    phaseNorm a b - a = b ^ 2 / (phaseNorm a b + a) := by
  apply (eq_div_iff (ne_of_gt (add_pos (phaseNorm_pos ha) ha))).mpr
  nlinarith only [phaseNorm_sq a b]

theorem phaseNorm_ratio_defect {a b : ℝ} (ha : 0 < a) :
    1 - a / phaseNorm a b = b ^ 2 * phaseNormKernel a b := by
  have hn := ne_of_gt (phaseNorm_pos (b := b) ha)
  have hs := ne_of_gt (add_pos (phaseNorm_pos (b := b) ha) ha)
  dsimp [phaseNormKernel]
  field_simp
  nlinarith only [phaseNorm_sq a b]

theorem matchingPhase_one_wall {m v w : ℝ} (hm : 1 < m) :
    matchingPhase m v 0 = phaseNorm (m + 1) v - 1 ∧
      matchingPhase m 0 w = phaseNorm (m - 1) w + 1 := by
  constructor <;> dsimp [matchingPhase]
  · rw [phaseNorm_zero (by linarith only [hm])]
    ring
  · rw [phaseNorm_zero (by linarith only [hm])]
    ring

theorem matchingPhase_interaction {m v w : ℝ} (hm : 1 < m) :
    v ^ 2 * ((m - 1) / phaseNorm (m - 1) w - 1) +
      w ^ 2 * (1 - (m + 1) / phaseNorm (m + 1) v) = (v * w) ^ 2 * matchingPhaseKernel m v w := by
  have hp := phaseNorm_ratio_defect (b := v) (show 0 < m + 1 by linarith only [hm])
  have hn := phaseNorm_ratio_defect (b := w) (show 0 < m - 1 by linarith only [hm])
  have hn' : (m - 1) / phaseNorm (m - 1) w - 1 = -(w ^ 2 * phaseNormKernel (m - 1) w) := by
    linarith only [hn]
  rw [hp, hn']
  unfold matchingPhaseKernel
  ring

/-- The exact cancellation leaves the product of the two weak walls squared. -/
theorem matchingPhase_directional {m u v w : ℝ} (hm : 1 < m) :
    matchingPhaseSlope m v w * (-phaseVelocity (-m) u v w) +
      v / phaseNorm (m + 1) v * activeVelocity (-m) u v w +
      w / phaseNorm (m - 1) w * weakVelocity (-m) u v w = matchingPhaseRate m u v w := by
  calc
    _ = v ^ 2 * ((m - 1) / phaseNorm (m - 1) w - 1) +
        w ^ 2 * (1 - (m + 1) / phaseNorm (m + 1) v) -
        u * matchingPhaseSlope m v w * (v - w) - coupling u v w * matchingPhaseWeight m v w := by
      dsimp [matchingPhaseSlope, matchingPhaseWeight, phaseVelocity, activeVelocity, weakVelocity]
      ring
    _ = _ := by rw [matchingPhase_interaction hm]; rfl

theorem hasDerivAt_matchingPhase {m v w : ℝ → ℝ} {m' v' w' t : ℝ}
    (hm : HasDerivAt m m' t) (hv : HasDerivAt v v' t) (hw : HasDerivAt w w' t) (hmt : 1 < m t) :
    HasDerivAt (fun s => matchingPhase (m s) (v s) (w s))
      (matchingPhaseSlope (m t) (v t) (w t) * m' +
        v t / phaseNorm (m t + 1) (v t) * v' + w t / phaseNorm (m t - 1) (w t) * w') t := by
  have hp : (m t + 1) ^ 2 + v t ^ 2 ≠ 0 := by
    have H : 0 < m t + 1 := by linarith only [hmt]
    positivity
  have hn : (m t - 1) ^ 2 + w t ^ 2 ≠ 0 := by
    have H : 0 < m t - 1 := by linarith only [hmt]
    positivity
  have H := ((((hm.add_const 1).pow 2).add (hv.pow 2)).sqrt hp).add
    ((((hm.sub_const 1).pow 2).add (hw.pow 2)).sqrt hn)
  convert! H.sub hm using 1
  dsimp [matchingPhaseSlope, phaseNorm]
  ring

end BianchiIX
