import BianchiIX.Algebra.StablePhaseCorrection
import BianchiIX.Analysis.HessianEvaluation

noncomputable section

namespace BianchiIX

open scoped Topology

def stableCorrectionADeriv (m : ℝ) : ℝ := -(m ^ 2 + 1) / (m ^ 2 - 1) ^ 2

def stableCorrectionASecond (m : ℝ) : ℝ := 2 * m * (m ^ 2 + 3) / (m ^ 2 - 1) ^ 3

def stableCorrectionCDeriv (m : ℝ) : ℝ := 2 / (m + 1) ^ 2

def stableCorrectionCSecond (m : ℝ) : ℝ := -4 / (m + 1) ^ 3

def stableCorrectedHessian (m u w : ℝ) (v r : Fin 3 → ℝ) : ℝ :=
  (w ^ 2 / stableWeakRadius m w ^ 3 + stableCorrectionASecond m * u ^ 2 +
    stableCorrectionCSecond m * u * w) * v 0 * r 0 +
  (2 * stableCorrectionADeriv m * u + stableCorrectionCDeriv m * w) * (v 0 * r 1 + v 1 * r 0) +
  (-(m + 1) * w / stableWeakRadius m w ^ 3 + stableCorrectionCDeriv m * u) * (v 0 * r 2 + v 2 * r 0) +
  2 * stableCorrectionA m * v 1 * r 1 +
  stableCorrectionC m * (v 1 * r 2 + v 2 * r 1) +
  (m + 1) ^ 2 / stableWeakRadius m w ^ 3 * v 2 * r 2

theorem hasDerivAt_stableCorrectionADeriv {m : ℝ} (hm : 1 < m) :
    HasDerivAt stableCorrectionADeriv (stableCorrectionASecond m) m := by
  have hd : m ^ 2 - 1 ≠ 0 := by nlinarith
  apply (((((hasDerivAt_id m).pow 2).add_const 1).neg).div
    ((((hasDerivAt_id m).pow 2).sub_const 1).pow 2) (pow_ne_zero 2 hd)).congr_deriv
  dsimp [stableCorrectionASecond]
  field_simp
  ring

theorem hasDerivAt_stableCorrectionCDeriv {m : ℝ} (hm : -1 < m) :
    HasDerivAt stableCorrectionCDeriv (stableCorrectionCSecond m) m := by
  have hd : m + 1 ≠ 0 := by linarith
  apply ((hasDerivAt_const m (2 : ℝ)).div (((hasDerivAt_id m).add_const 1).pow 2)
    (pow_ne_zero 2 hd)).congr_deriv
  dsimp [stableCorrectionCSecond]
  field_simp
  ring

theorem hasDerivAt_stableWeakSlopes {m w : ℝ → ℝ} {m' w' t : ℝ}
    (hm : HasDerivAt m m' t) (hw : HasDerivAt w w' t) (hpos : -1 < m t) :
    HasDerivAt (fun s => (m s + 1) / stableWeakRadius (m s) (w s))
      ((w t) ^ 2 / stableWeakRadius (m t) (w t) ^ 3 * m' -
        (m t + 1) * w t / stableWeakRadius (m t) (w t) ^ 3 * w') t ∧
    HasDerivAt (fun s => w s / stableWeakRadius (m s) (w s))
      (-(m t + 1) * w t / stableWeakRadius (m t) (w t) ^ 3 * m' +
        (m t + 1) ^ 2 / stableWeakRadius (m t) (w t) ^ 3 * w') t := by
  have hs := hasDerivAt_stableWeakRadius hm hw hpos
  have hn := ne_of_gt (stableWeakRadius_pos (w := w t) hpos)
  have hsq := stableWeakRadius_sq (m t) (w t)
  constructor
  · apply ((hm.add_const 1).div hs hn).congr_deriv
    field_simp
    nlinarith only [congrArg (fun z : ℝ => z * m') hsq]
  · apply (hw.div hs hn).congr_deriv
    field_simp
    nlinarith only [congrArg (fun z : ℝ => z * w') hsq]

theorem stableCorrectedPhase_fderiv {y : Fin 3 → ℝ} (hm : 1 < y 0) (v : Fin 3 → ℝ) :
    fderiv ℝ (fun z : Fin 3 → ℝ => stableCorrectedPhase (z 0) (z 1) (z 2)) y v =
      stableCorrectedGradient (y 0) (y 1) (y 2) 0 * v 0 +
      stableCorrectedGradient (y 0) (y 1) (y 2) 1 * v 1 +
      stableCorrectedGradient (y 0) (y 1) (y 2) 2 * v 2 := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hreg := contDiffAt_stableCorrectedPhase 1 (y := y + (0 : ℝ) • v) (by simpa using hm)
  have H := (hreg.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt 0 hl
  have G := hasDerivAt_stableCorrectedPhase (hasDerivAt_pi.mp hl 0)
    (hasDerivAt_pi.mp hl 1) (hasDerivAt_pi.mp hl 2) (by simpa using hm)
  simpa using H.unique G

theorem hasDerivAt_stableCorrectedGradient_apply {gamma : ℝ → (Fin 3 → ℝ)} {v : Fin 3 → ℝ} {t : ℝ}
    (h : HasDerivAt gamma v t) (hm : 1 < gamma t 0) (r : Fin 3 → ℝ) :
    HasDerivAt (fun s => stableCorrectedGradient (gamma s 0) (gamma s 1) (gamma s 2) 0 * r 0 +
      stableCorrectedGradient (gamma s 0) (gamma s 1) (gamma s 2) 1 * r 1 +
      stableCorrectedGradient (gamma s 0) (gamma s 1) (gamma s 2) 2 * r 2)
      (stableCorrectedHessian (gamma t 0) (gamma t 1) (gamma t 2) v r) t := by
  have hM := hasDerivAt_pi.mp h 0
  have hU := hasDerivAt_pi.mp h 1
  have hW := hasDerivAt_pi.mp h 2
  have hs := hasDerivAt_stableWeakSlopes hM hW (by linarith)
  have ha := (hasDerivAt_stableCorrectionA hm).comp t hM
  have hc := (hasDerivAt_stableCorrectionC (by linarith : -1 < gamma t 0)).comp t hM
  have ha1 := (hasDerivAt_stableCorrectionADeriv hm).comp t hM
  have hc1 := (hasDerivAt_stableCorrectionCDeriv (by linarith : -1 < gamma t 0)).comp t hM
  have h0 := (hs.1.add (ha1.mul (hU.pow 2))).add ((hc1.mul hU).mul hW)
  have h1 := ((ha.const_mul 2).mul hU).add (hc.mul hW)
  have h2 := hs.2.add (hc.mul hU)
  have H := ((h0.mul_const (r 0)).add (h1.mul_const (r 1))).add (h2.mul_const (r 2))
  convert! H using 1
  · funext s
    dsimp [stableCorrectedGradient, stableCorrectionADeriv, stableCorrectionCDeriv]
    ring
  · dsimp [stableCorrectedHessian, stableCorrectionADeriv, stableCorrectionCDeriv]
    ring

theorem stableCorrectedPhase_fderiv2 {y : Fin 3 → ℝ} (hm : 1 < y 0) (v r : Fin 3 → ℝ) :
    fderiv ℝ (fderiv ℝ (fun z : Fin 3 → ℝ => stableCorrectedPhase (z 0) (z 1) (z 2))) y v r =
      stableCorrectedHessian (y 0) (y 1) (y 2) v r := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hreg := contDiffAt_stableCorrectedPhase 2 (y := y + (0 : ℝ) • v) (by simpa using hm)
  have hD := (hreg.fderiv_right
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have H := hasDerivAt_fderiv_apply_const hD hl r
  have heq : (fun s : ℝ => fderiv ℝ (fun z : Fin 3 → ℝ => stableCorrectedPhase (z 0) (z 1) (z 2)) (y + s • v) r)
      =ᶠ[𝓝 0] (fun s => stableCorrectedGradient ((y + s • v) 0) ((y + s • v) 1) ((y + s • v) 2) 0 * r 0 +
        stableCorrectedGradient ((y + s • v) 0) ((y + s • v) 1) ((y + s • v) 2) 1 * r 1 +
        stableCorrectedGradient ((y + s • v) 0) ((y + s • v) 1) ((y + s • v) 2) 2 * r 2) := by
    have hnear : ∀ᶠ s : ℝ in 𝓝 0, 1 < (y + s • v) 0 :=
      ((hasDerivAt_pi.mp hl 0).continuousAt.eventually (isOpen_Ioi.mem_nhds (by simpa using hm)))
    filter_upwards [hnear] with s hs
    exact stableCorrectedPhase_fderiv hs r
  have G := hasDerivAt_stableCorrectedGradient_apply hl (by simpa using hm) r
  simpa using (H.congr_of_eventuallyEq heq.symm).unique G

end BianchiIX
