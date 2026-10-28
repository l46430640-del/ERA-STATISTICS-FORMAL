import BianchiIX.Dynamics.ExitTailCoordinates
import BianchiIX.Algebra.ExitTailPerturbation

noncomputable section

namespace BianchiIX

def exitTailRadialGradient (R u v w : ℝ) : Fin 3 → ℝ :=
  let t := exitTailGap R v
  let d := exitTailSpeed R u v w
  let g := exitTailRadial R u v w
  ![(-coupling u v w - (1 / t - t / R ^ 2) * (u - w) ^ 2 - g * R / t) / d,
    (-(v + w - 2 * u) * R - 2 * t * (u - w) / R - g * (v + w - 2 * u)) / d,
    (-u * R + 2 * t * (u - w) / R - g * u) / d]

def exitTailStrongRateGradient (R u v w : ℝ) : Fin 3 → ℝ :=
  let t := exitTailGap R v
  let d := exitTailSpeed R u v w
  let a := exitTailStrongRate R u v w
  ![(R / t - R - a * R / t) / d,
    (u - a * (v + w - 2 * u)) / d, (v - w - a * u) / d]

def exitTailWeakRateGradient (R u v w : ℝ) : Fin 3 → ℝ :=
  let t := exitTailGap R v
  let d := exitTailSpeed R u v w
  let a := exitTailWeakRate R u v w
  ![((1 - a) * R / t) / d,
    (-(1 + a) * (v + w - 2 * u)) / d, (-(1 + a) * u) / d]

theorem hasDerivAt_exitTailGap {R : ℝ → ℝ} {r s v : ℝ}
    (hR : HasDerivAt R r s) (hv : v ^ 2 < (R s) ^ 2) :
    HasDerivAt (fun q => exitTailGap (R q) v) (R s * r / exitTailGap (R s) v) s := by
  have ht : exitTailGap (R s) v ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hv))
  convert! ((hR.pow 2).sub_const (v ^ 2)).sqrt (ne_of_gt (sub_pos.mpr hv)) using 1
  norm_num only [Nat.reduceSub, pow_one, Pi.pow_apply, Nat.cast_ofNat]
  change R s * r / exitTailGap (R s) v = 2 * R s * r / (2 * exitTailGap (R s) v)
  field_simp

theorem hasDerivAt_exitTail_radial {Y : ℝ → ExitTailState} {ξ : ExitTailState} {s v : ℝ}
    (hY : HasDerivAt Y ξ s) (hR : 0 < Y s 0) (hv : v ^ 2 < (Y s 0) ^ 2)
    (hd : exitTailSpeed (Y s 0) (Y s 1) v (Y s 2) ≠ 0) :
    HasDerivAt (fun q => exitTailRadial (Y q 0) (Y q 1) v (Y q 2))
      (∑ i : Fin 3, exitTailRadialGradient (Y s 0) (Y s 1) v (Y s 2) i * ξ i) s := by
  have h0 := hasDerivAt_pi.mp hY 0
  have h1 := hasDerivAt_pi.mp hY 1
  have h2 := hasDerivAt_pi.mp hY 2
  have ht := hasDerivAt_exitTailGap h0 hv
  have hc := h1.mul (((hasDerivAt_const s v).add h2).sub h1)
  have hs := ht.add hc
  have hn := (hc.neg.mul h0).sub ((ht.mul ((h1.sub h2).pow 2)).div h0 (ne_of_gt hR))
  have H := hn.div hs hd
  apply H.congr_deriv
  have ht0 : exitTailGap (Y s 0) v ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hv))
  simp [Fin.sum_univ_succ, exitTailRadialGradient, exitTailRadial, exitTailSpeed, coupling]
  dsimp only [exitTailSpeed, coupling] at hd
  field_simp
  ring

theorem hasDerivAt_exitTail_strongRate {Y : ℝ → ExitTailState} {ξ : ExitTailState} {s v : ℝ}
    (hY : HasDerivAt Y ξ s) (hv : v ^ 2 < (Y s 0) ^ 2)
    (hd : exitTailSpeed (Y s 0) (Y s 1) v (Y s 2) ≠ 0) :
    HasDerivAt (fun q => exitTailStrongRate (Y q 0) (Y q 1) v (Y q 2))
      (∑ i : Fin 3, exitTailStrongRateGradient (Y s 0) (Y s 1) v (Y s 2) i * ξ i) s := by
  have h0 := hasDerivAt_pi.mp hY 0
  have h1 := hasDerivAt_pi.mp hY 1
  have h2 := hasDerivAt_pi.mp hY 2
  have ht := hasDerivAt_exitTailGap h0 hv
  have hc := h1.mul (((hasDerivAt_const s v).add h2).sub h1)
  have hs := ht.add hc
  have hn := (((ht.const_mul 2).sub (h0.pow 2)).add (h2.const_mul (2 * v))).sub (h2.pow 2) |>.add (h1.pow 2)
  have H := hn.div (hs.const_mul 2) (mul_ne_zero (by norm_num) hd)
  apply H.congr_deriv
  have ht0 : exitTailGap (Y s 0) v ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hv))
  simp [Fin.sum_univ_succ, exitTailStrongRateGradient, exitTailStrongRate, exitTailSpeed, coupling]
  dsimp only [exitTailSpeed, coupling] at hd
  field_simp
  ring

theorem hasDerivAt_exitTail_weakRate {Y : ℝ → ExitTailState} {ξ : ExitTailState} {s v : ℝ}
    (hY : HasDerivAt Y ξ s) (hv : v ^ 2 < (Y s 0) ^ 2)
    (hd : exitTailSpeed (Y s 0) (Y s 1) v (Y s 2) ≠ 0) :
    HasDerivAt (fun q => exitTailWeakRate (Y q 0) (Y q 1) v (Y q 2))
      (∑ i : Fin 3, exitTailWeakRateGradient (Y s 0) (Y s 1) v (Y s 2) i * ξ i) s := by
  have h0 := hasDerivAt_pi.mp hY 0
  have h1 := hasDerivAt_pi.mp hY 1
  have h2 := hasDerivAt_pi.mp hY 2
  have ht := hasDerivAt_exitTailGap h0 hv
  have hc := h1.mul (((hasDerivAt_const s v).add h2).sub h1)
  have hs := ht.add hc
  have H := ((ht.sub_const 2).sub hc).div hs hd
  apply H.congr_deriv
  have ht0 : exitTailGap (Y s 0) v ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hv))
  simp [Fin.sum_univ_succ, exitTailWeakRateGradient, exitTailWeakRate, exitTailSpeed, coupling]
  dsimp only [exitTailSpeed, coupling] at hd
  field_simp
  ring

def exitTailLinearization (v : ℝ) (Y ξ : ExitTailState) : ExitTailState :=
  ![∑ i : Fin 3, exitTailRadialGradient (Y 0) (Y 1) v (Y 2) i * ξ i,
    Y 1 * (∑ i : Fin 3, exitTailStrongRateGradient (Y 0) (Y 1) v (Y 2) i * ξ i) +
      exitTailStrongRate (Y 0) (Y 1) v (Y 2) * ξ 1,
    Y 2 * (∑ i : Fin 3, exitTailWeakRateGradient (Y 0) (Y 1) v (Y 2) i * ξ i) +
      exitTailWeakRate (Y 0) (Y 1) v (Y 2) * ξ 2]

theorem hasDerivAt_exitTailField {Y : ℝ → ExitTailState} {ξ : ExitTailState} {s v : ℝ}
    (hY : HasDerivAt Y ξ s) (hR : 0 < Y s 0) (hv : v ^ 2 < (Y s 0) ^ 2)
    (hd : exitTailSpeed (Y s 0) (Y s 1) v (Y s 2) ≠ 0) :
    HasDerivAt (fun q => exitTailField v (Y q)) (exitTailLinearization v (Y s) ξ) s := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_exitTail_radial hY hR hv hd
  · convert! (hasDerivAt_exitTail_strongRate hY hv hd).mul (hasDerivAt_pi.mp hY 1) using 1
    dsimp [exitTailLinearization]
    ring
  · convert! (hasDerivAt_exitTail_weakRate hY hv hd).mul (hasDerivAt_pi.mp hY 2) using 1
    dsimp [exitTailLinearization]
    ring

theorem exitTailField_fderiv {v : ℝ} {Y : ExitTailState} (hR : 0 < Y 0)
    (hv : v ^ 2 < (Y 0) ^ 2) (hd : exitTailSpeed (Y 0) (Y 1) v (Y 2) ≠ 0)
    (ξ : ExitTailState) : fderiv ℝ (exitTailField v) Y ξ = exitTailLinearization v Y ξ := by
  have hreg : ContDiffAt ℝ 1 (exitTailField v) Y :=
    (contDiffAt_exitTailField 1 hv (ne_of_gt hR) hd).comp Y (by fun_prop)
  have hline : HasDerivAt (fun s : ℝ => Y + s • ξ) ξ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ξ).const_add Y
  have hf : HasFDerivAt (exitTailField v) (fderiv ℝ (exitTailField v) Y) (Y + (0 : ℝ) • ξ) := by
    simpa using (hreg.differentiableAt (by norm_num)).hasFDerivAt
  have H := hf.comp_hasDerivAt 0 hline
  have K := hasDerivAt_exitTailField hline (by simpa using hR) (by simpa using hv) (by simpa using hd)
  simpa only [zero_smul, add_zero] using H.unique K

end BianchiIX
