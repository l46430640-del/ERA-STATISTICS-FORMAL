import BianchiIX.Algebra.StablePhaseHessian

noncomputable section

namespace BianchiIX

open scoped Topology

def stableWeakRemainder (m w : ℝ) : ℝ :=
  stableWeakRadius m w - (m + 1) - w ^ 2 / (2 * (m + 1))

def stableWeakRemainderM (m w : ℝ) : ℝ :=
  (m + 1) / stableWeakRadius m w - 1 + w ^ 2 / (2 * (m + 1) ^ 2)

def stableWeakRemainderW (m w : ℝ) : ℝ :=
  w / stableWeakRadius m w - w / (m + 1)

def stableWeakRemainderMM (m w : ℝ) : ℝ :=
  w ^ 2 / stableWeakRadius m w ^ 3 - w ^ 2 / (m + 1) ^ 3

def stableWeakRemainderMW (m w : ℝ) : ℝ :=
  -(m + 1) * w / stableWeakRadius m w ^ 3 + w / (m + 1) ^ 2

def stableWeakRemainderWW (m w : ℝ) : ℝ :=
  (m + 1) ^ 2 / stableWeakRadius m w ^ 3 - 1 / (m + 1)

theorem contDiffAt_stableWeakRemainder (n : WithTop ℕ∞) {y : Fin 3 → ℝ} (hm : -1 < y 0) :
    ContDiffAt ℝ n (fun z : Fin 3 → ℝ => stableWeakRemainder (z 0) (z 2)) y := by
  have hL : y 0 + 1 ≠ 0 := by linarith
  have h2L : 2 * (y 0 + 1) ≠ 0 := mul_ne_zero (by norm_num) hL
  have hS : (y 0 + 1) ^ 2 + y 2 ^ 2 ≠ 0 := by
    have h : 0 < y 0 + 1 := by linarith
    positivity
  unfold stableWeakRemainder stableWeakRadius phaseNorm
  fun_prop

theorem hasDerivAt_stableWeakRemainder {m w : ℝ → ℝ} {m' w' t : ℝ}
    (hm : HasDerivAt m m' t) (hw : HasDerivAt w w' t) (hpos : -1 < m t) :
    HasDerivAt (fun s => stableWeakRemainder (m s) (w s))
      (stableWeakRemainderM (m t) (w t) * m' + stableWeakRemainderW (m t) (w t) * w') t := by
  have hL : m t + 1 ≠ 0 := by linarith
  have hS := ne_of_gt (stableWeakRadius_pos (w := w t) hpos)
  apply (((hasDerivAt_stableWeakRadius hm hw hpos).sub (hm.add_const 1)).sub
    ((hw.pow 2).div ((hm.add_const 1).const_mul 2) (by positivity))).congr_deriv
  dsimp [stableWeakRemainderM, stableWeakRemainderW]
  field_simp
  ring

theorem hasDerivAt_stableWeakRemainder_gradient {m w : ℝ → ℝ} {m' w' t : ℝ}
    (hm : HasDerivAt m m' t) (hw : HasDerivAt w w' t) (hpos : -1 < m t) :
    HasDerivAt (fun s => stableWeakRemainderM (m s) (w s))
      (stableWeakRemainderMM (m t) (w t) * m' + stableWeakRemainderMW (m t) (w t) * w') t ∧
    HasDerivAt (fun s => stableWeakRemainderW (m s) (w s))
      (stableWeakRemainderMW (m t) (w t) * m' + stableWeakRemainderWW (m t) (w t) * w') t := by
  have hL : m t + 1 ≠ 0 := by linarith
  have hS := ne_of_gt (stableWeakRadius_pos (w := w t) hpos)
  have H := hasDerivAt_stableWeakSlopes hm hw hpos
  constructor
  · apply ((H.1.sub_const 1).add ((hw.pow 2).div (((hm.add_const 1).pow 2).const_mul 2)
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hL)))).congr_deriv
    dsimp [stableWeakRemainderMM, stableWeakRemainderMW]
    field_simp
    ring
  · apply (H.2.sub (hw.div (hm.add_const 1) hL)).congr_deriv
    dsimp [stableWeakRemainderMW, stableWeakRemainderWW]
    field_simp
    ring

theorem stableWeakRemainder_fderiv {y : Fin 3 → ℝ} (hm : -1 < y 0) (v : Fin 3 → ℝ) :
    fderiv ℝ (fun z : Fin 3 → ℝ => stableWeakRemainder (z 0) (z 2)) y v =
      stableWeakRemainderM (y 0) (y 2) * v 0 + stableWeakRemainderW (y 0) (y 2) * v 2 := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hreg := contDiffAt_stableWeakRemainder 1 (y := y + (0 : ℝ) • v) (by simpa using hm)
  have H := (hreg.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt 0 hl
  have G := hasDerivAt_stableWeakRemainder (hasDerivAt_pi.mp hl 0) (hasDerivAt_pi.mp hl 2) (by simpa using hm)
  simpa using H.unique G

theorem stableWeakRemainder_fderiv2 {y : Fin 3 → ℝ} (hm : -1 < y 0) (v r : Fin 3 → ℝ) :
    fderiv ℝ (fderiv ℝ (fun z : Fin 3 → ℝ => stableWeakRemainder (z 0) (z 2))) y v r =
      stableWeakRemainderMM (y 0) (y 2) * v 0 * r 0 +
      stableWeakRemainderMW (y 0) (y 2) * (v 0 * r 2 + v 2 * r 0) +
      stableWeakRemainderWW (y 0) (y 2) * v 2 * r 2 := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hreg := contDiffAt_stableWeakRemainder 2 (y := y + (0 : ℝ) • v) (by simpa using hm)
  have hD := (hreg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have H := hasDerivAt_fderiv_apply_const hD hl r
  have heq : (fun s : ℝ => fderiv ℝ (fun z : Fin 3 → ℝ => stableWeakRemainder (z 0) (z 2)) (y + s • v) r)
      =ᶠ[𝓝 0] (fun s => stableWeakRemainderM ((y + s • v) 0) ((y + s • v) 2) * r 0 +
        stableWeakRemainderW ((y + s • v) 0) ((y + s • v) 2) * r 2) := by
    have hnear : ∀ᶠ s : ℝ in 𝓝 0, -1 < (y + s • v) 0 :=
      (hasDerivAt_pi.mp hl 0).continuousAt.eventually (isOpen_Ioi.mem_nhds (by simpa using hm))
    filter_upwards [hnear] with s hs
    exact stableWeakRemainder_fderiv hs r
  have G := hasDerivAt_stableWeakRemainder_gradient (hasDerivAt_pi.mp hl 0) (hasDerivAt_pi.mp hl 2)
    (by simpa using hm)
  have H0 := (H.congr_of_eventuallyEq heq.symm).unique ((G.1.mul_const (r 0)).add (G.2.mul_const (r 2)))
  simp only [zero_smul, Pi.add_apply, Pi.zero_apply, add_zero] at H0
  rw [H0]
  ring

end BianchiIX
