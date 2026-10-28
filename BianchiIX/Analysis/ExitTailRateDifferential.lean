import BianchiIX.Analysis.ExitTailJacobian

noncomputable section

namespace BianchiIX

theorem contDiffAt_exitTailWallRate (n : WithTop ℕ∞) {v : ℝ} {Y : ExitTailState}
    (hv : v ^ 2 < (Y 0) ^ 2) (hd : exitTailSpeed (Y 0) (Y 1) v (Y 2) ≠ 0) :
    ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailWallRate q.1 q.2) (v, Y) := by
  have hcoord (i : Fin 3) : ContDiffAt ℝ n (fun q : ℝ × ExitTailState => q.2 i) (v, Y) := by fun_prop
  have ht : ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailGap (q.2 0) q.1) (v, Y) := by
    unfold exitTailGap
    exact (((hcoord 0).pow 2).sub (contDiffAt_fst.pow 2)).sqrt (ne_of_gt (sub_pos.mpr hv))
  have hc : ContDiffAt ℝ n (fun q : ℝ × ExitTailState => coupling (q.2 1) q.1 (q.2 2)) (v, Y) := by
    unfold coupling
    fun_prop
  have hs : ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailSpeed (q.2 0) (q.2 1) q.1 (q.2 2)) (v, Y) :=
    ht.add hc
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · change ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailStrongRate (q.2 0) (q.2 1) q.1 (q.2 2)) (v, Y)
    exact (((((contDiffAt_const.mul ht).sub ((hcoord 0).pow 2)).add
      ((contDiffAt_const.mul contDiffAt_fst).mul (hcoord 2))).sub ((hcoord 2).pow 2)).add ((hcoord 1).pow 2)).div
      (contDiffAt_const.mul hs) (mul_ne_zero (by norm_num) hd)
  · change ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailWeakRate (q.2 0) (q.2 1) q.1 (q.2 2)) (v, Y)
    exact ((ht.sub contDiffAt_const).sub hc).div hs hd

theorem hasDerivAt_exitTailWallRate {Y : ℝ → ExitTailState} {ξ : ExitTailState} {s v : ℝ}
    (hY : HasDerivAt Y ξ s) (hv : v ^ 2 < (Y s 0) ^ 2)
    (hd : exitTailSpeed (Y s 0) (Y s 1) v (Y s 2) ≠ 0) :
    HasDerivAt (fun q => exitTailWallRate v (Y q))
      (fun i => ∑ j : Fin 3, exitTailRateGradient v (Y s) i j * ξ j) s := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_exitTail_strongRate hY hv hd
  · exact hasDerivAt_exitTail_weakRate hY hv hd

theorem exitTailWallRate_fderiv {v : ℝ} {Y : ExitTailState}
    (hv : v ^ 2 < (Y 0) ^ 2) (hd : exitTailSpeed (Y 0) (Y 1) v (Y 2) ≠ 0)
    (ξ : ExitTailState) (i : Fin 2) :
    fderiv ℝ (exitTailWallRate v) Y ξ i = ∑ j : Fin 3, exitTailRateGradient v Y i j * ξ j := by
  have hreg : ContDiffAt ℝ 1 (exitTailWallRate v) Y :=
    (contDiffAt_exitTailWallRate 1 hv hd).comp Y (by fun_prop)
  have hline : HasDerivAt (fun s : ℝ => Y + s • ξ) ξ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ξ).const_add Y
  have hf : HasFDerivAt (exitTailWallRate v) (fderiv ℝ (exitTailWallRate v) Y) (Y + (0 : ℝ) • ξ) := by
    simpa using (hreg.differentiableAt (by norm_num)).hasFDerivAt
  have H := hf.comp_hasDerivAt 0 hline
  have K := hasDerivAt_exitTailWallRate hline (by simpa using hv) (by simpa using hd)
  simpa only [zero_smul, add_zero] using congrFun (H.unique K) i

theorem exitTailWallRate_partial {v : ℝ} {Y : ExitTailState}
    (hv : v ^ 2 < (Y 0) ^ 2) (hd : exitTailSpeed (Y 0) (Y 1) v (Y 2) ≠ 0)
    (i : Fin 2) (j : Fin 3) :
    fderiv ℝ (exitTailWallRate v) Y (Pi.single j 1) i = exitTailRateGradient v Y i j := by
  rw [exitTailWallRate_fderiv hv hd]
  simp [Pi.single_apply]

theorem exitTailWallRate_partial_bounds {v : ℝ} {Y : ExitTailState}
    (hR : 7 / 4 ≤ Y 0 ∧ Y 0 ≤ 17 / 4) (hu : |Y 1| ≤ 1 / 100)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : |Y 2| ≤ 1 / 100) (i : Fin 2) :
    |fderiv ℝ (exitTailWallRate v) Y (Pi.single 0 1) i| ≤ 512 ∧
      ∀ j : Fin 2, |fderiv ℝ (exitTailWallRate v) Y (Pi.single j.succ 1) i| ≤
        256 * (v + |Y 1| + |Y 2|) := by
  have hvR : v ^ 2 < (Y 0) ^ 2 := by nlinarith only [hR.1, hv.1, hv.2]
  have hd : exitTailSpeed (Y 0) (Y 1) v (Y 2) ≠ 0 := by
    have H := exitTailSpeed_compact hR.1 hu hv hw
    linarith only [H]
  simp only [exitTailWallRate_partial hvR hd]
  exact exitTailRateGradient_bounds hR hu hv hw i

end BianchiIX
