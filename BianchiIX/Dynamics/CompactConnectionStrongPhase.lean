import BianchiIX.Dynamics.CompactConnectionFinitePhase
import BianchiIX.Dynamics.CoreTailStrongDifferential
import BianchiIX.Dynamics.StableWeakDifferential

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

/-- The strong boundary response in (B.48) is independent of the auxiliary tail height. -/
theorem compactConnectionFinitePhase_strong_reference {k η : ℝ}
    (hk : 7 / 2 ≤ k) (hη : 0 < η ∧ η ≤ 1 / 10000) :
    fderiv ℝ (compactConnectionFinitePhase η) ![k, 0, 0] (Pi.single 1 1) = -2 / k := by
  let Y : CoreAngleState := ![k, 0, 0]
  let c := fun a : ℝ => (![k, a, 0] : CoreAngleState)
  let Z := coreTailState η Y
  let v := fderiv ℝ (coreTailState η) Y (Pi.single 1 1)
  let y : StableState := ![-Z 0, Z 1, Z 2]
  let w : StableState := ![-v 0, v 1, v 2]
  let P := fun z : StableState => stableBoundaryProjection (z 0) (z 1) (z 2)
  let q := fderiv ℝ P y w
  let d := fderiv ℝ (compactConnectionFinitePhase η) Y (Pi.single 1 1)
  have hk1 : 1 < k := by linarith
  have hη1 : 0 < η ∧ η < 1 := ⟨hη.1, by linarith [hη.2]⟩
  have HT := coreTail_reference_regular hk1 hη1
  have hZ : Z = ![1 - Real.sqrt (k ^ 2 - η ^ 2), 0, η, 0] := HT.2.1
  have hm : 2 ≤ y 0 := (compactConnection_reference_stable_phase hk hη).1.le
  have hu : y 1 = 0 := by change Z 1 = 0; rw [hZ]; rfl
  have hw : |y 2| < 1 / 200 := by
    change |Z 2| < 1 / 200
    rw [hZ]
    change |η| < 1 / 200
    rw [abs_of_pos hη.1]
    linarith [hη.2]
  have hPval : entranceStablePhase (compactConnectionEntry η Y) = k - 1 :=
    (compactConnection_reference_stable_phase hk hη).2
  have hFval : compactConnectionFinitePhase η Y = k - 2 := compactConnectionFinitePhase_reference hk hη
  have hlinear := stableBoundaryProjection_fderiv_weak hm (by simp : |y 0 - y 0| < (1 : ℝ) / 40) hu hw w
  change (entranceStablePhase (compactConnectionEntry η Y) + 1) * q =
    (-Z 0 + 1) * (-v 0) + Z 2 * (v 2 - 2 * v 1) at hlinear
  rw [hPval] at hlinear
  have HI := coreTail_strong_variation_invariant hk1 hη1
  change (Z 0 - 1) * v 0 + Z 2 * v 2 - 2 * Z 2 * v 1 = -2 at HI
  have hq : k * q = -2 := by nlinarith only [hlinear, HI]
  have hline : HasDerivAt c (Pi.single 1 1) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [c] using hasDerivAt_const (0 : ℝ) k
    · change HasDerivAt (fun a : ℝ => a) 1 0
      exact hasDerivAt_id' 0
    · simpa [c] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  have htD : HasFDerivAt (coreTailState η) (fderiv ℝ (coreTailState η) Y) Y :=
    (HT.2.2.2.1.differentiableAt (by norm_num)).hasFDerivAt
  have htail : HasDerivAt (fun a => coreTailState η (c a)) v 0 := by
    have H := htD.comp_hasDerivAt (0 : ℝ) hline
    exact H
  have hstable : HasDerivAt (fun a => (![-coreTailState η (c a) 0,
      coreTailState η (c a) 1, coreTailState η (c a) 2] : StableState)) w 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact (hasDerivAt_pi.mp htail 0).neg
    · exact hasDerivAt_pi.mp htail 1
    · exact hasDerivAt_pi.mp htail 2
  have hpD : HasFDerivAt P (fderiv ℝ P y) y :=
    ((contDiffAt_stableBoundaryProjection_two hm (by rw [hu]; norm_num) hw).differentiableAt (by norm_num)).hasFDerivAt
  have hP : HasDerivAt (fun a => entranceStablePhase (compactConnectionEntry η (c a))) q 0 := by
    have H := hpD.comp_hasDerivAt (0 : ℝ) hstable
    exact H
  have hfD : HasFDerivAt (compactConnectionFinitePhase η) (fderiv ℝ (compactConnectionFinitePhase η) Y) Y :=
    ((contDiffAt_compactConnectionFinitePhase_reference hk hη).differentiableAt (by norm_num)).hasFDerivAt
  have hF : HasDerivAt (fun a => compactConnectionFinitePhase η (c a)) d 0 := by
    have H := hfD.comp_hasDerivAt (0 : ℝ) hline
    exact H
  have hV : HasDerivAt (fun a => compactConnectionEntry η (c a) 2) (v 3) 0 := hasDerivAt_pi.mp htail 3
  have heq : (fun a => compactConnectionFinitePhase η (c a) ^ 2) =ᶠ[𝓝 0]
      (fun a => (entranceStablePhase (compactConnectionEntry η (c a)) - 1) ^ 2 +
        compactConnectionEntry η (c a) 2 ^ 2) :=
    Eventually.of_forall (fun a => entranceStableRadius_sq (compactConnectionEntry η (c a)))
  have HE := ((hF.pow 2).congr_of_eventuallyEq heq.symm).unique (((hP.sub_const 1).pow 2).add (hV.pow 2))
  change 2 * (compactConnectionFinitePhase η Y) ^ (2 - 1) * d =
    2 * (entranceStablePhase (compactConnectionEntry η Y) - 1) ^ (2 - 1) * q +
      2 * (Z 3) ^ (2 - 1) * v 3 at HE
  rw [hFval, hPval, hZ] at HE
  change 2 * (k - 2) ^ (2 - 1) * d = 2 * (k - 1 - 1) ^ (2 - 1) * q +
    2 * (0 : ℝ) ^ (2 - 1) * v 3 at HE
  norm_num at HE
  have hpos : 0 < 2 * (k - 2) := by linarith
  have hdq : d = q := mul_left_cancel₀ hpos.ne' (by nlinarith only [HE])
  change d = -2 / k
  rw [hdq]
  apply (eq_div_iff (by linarith : k ≠ 0)).mpr
  linarith only [hq]

end BianchiIX
