import BianchiIX.Dynamics.CompactConnectionFinitePhase
import BianchiIX.Dynamics.CoreTailWeakEnergy

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def compactConnectionWeakCoefficient (η : ℝ) (Y : CoreAngleState) : ℝ :=
  (coreTailWeakEnergyCoefficient η Y * (1 - 4 / (coreRadius (coreTailState η Y 0) η + Y 0)) +
    coreTailMultiplier η Y 1 ^ 2) / (compactConnectionFinitePhase η Y + Y 0 - 2)

/-- Rationalizing twice retains the weak-wall square without differentiating a third-order flow. -/
theorem compactConnectionFinitePhase_weak_factorization {η : ℝ} {Y : CoreAngleState}
    (hk : 2 < Y 0) (hη : |η| ≤ 1 / 200) (H : coreTailValid η Y)
    (hm : 2 ≤ -coreTailState η Y 0) (hu : Y 1 = 0) :
    compactConnectionFinitePhase η Y = Y 0 - 2 + (Y 2) ^ 2 * compactConnectionWeakCoefficient η Y := by
  let F := compactConnectionFinitePhase η Y
  let R := coreRadius (coreTailState η Y 0) η
  let I := coreTailWeakEnergyCoefficient η Y
  let B := coreTailMultiplier η Y 1
  have hF0 : 0 ≤ F := Real.sqrt_nonneg _
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hdR : R + Y 0 ≠ 0 := by linarith only [hR0, hk]
  have hdF : F + Y 0 - 2 ≠ 0 := by linarith only [hF0, hk]
  have hE : R ^ 2 = (Y 0) ^ 2 + (Y 2) ^ 2 * I := coreTail_weak_energy_factorization (by linarith) H hu
  have hW : coreTailState η Y 3 = Y 2 * B := coreTailMultiplier_formula H 1
  have hF2 : F ^ 2 = (R - 2) ^ 2 + (Y 2 * B) ^ 2 := by
    dsimp only [F]
    rw [compactConnectionFinitePhase_weak hη H hm hu, phaseNorm_sq, hW]
  have hRdiff : R - Y 0 = (Y 2) ^ 2 * I / (R + Y 0) := by
    apply (eq_div_iff hdR).mpr
    nlinarith only [hE]
  have hprod : (F - (Y 0 - 2)) * (F + Y 0 - 2) =
      (Y 2) ^ 2 * (I * (1 - 4 / (R + Y 0)) + B ^ 2) := by
    calc
      _ = (R ^ 2 - (Y 0) ^ 2) - 4 * (R - Y 0) + (Y 2 * B) ^ 2 := by nlinarith only [hF2]
      _ = _ := by rw [hE, hRdiff]; ring
  have hdiff : F - (Y 0 - 2) = (Y 2) ^ 2 *
      ((I * (1 - 4 / (R + Y 0)) + B ^ 2) / (F + Y 0 - 2)) := by
    rw [← mul_div_assoc]
    exact (eq_div_iff hdF).mpr hprod
  change F = Y 0 - 2 + (Y 2) ^ 2 * ((I * (1 - 4 / (R + Y 0)) + B ^ 2) / (F + Y 0 - 2))
  linarith only [hdiff]

theorem contDiffAt_compactConnectionWeakCoefficient_reference {k η : ℝ}
    (hk : 7 / 2 ≤ k) (hη : 0 < η ∧ η ≤ 1 / 10000) :
    ContDiffAt ℝ 2 (compactConnectionWeakCoefficient η) ![k, 0, 0] := by
  let Y : CoreAngleState := ![k, 0, 0]
  have hk1 : 1 < k := by linarith
  have H := coreTail_reference_regular hk1 ⟨hη.1, by linarith [hη.2]⟩
  have htail : coreTailValid η Y := H.2.2.2.2.self_of_nhds
  have hI := contDiffAt_coreTailWeakEnergyCoefficient_two hk1 htail H.2.2.1
  have hB := (contDiffAt_coreTailMultiplier_two hk1 htail H.2.2.1 1).1
  have hF := contDiffAt_compactConnectionFinitePhase_reference hk hη
  have hR : ContDiffAt ℝ 2 (fun Z => coreRadius (coreTailState η Z 0) η) Y := by
    have hM := contDiffAt_pi.mp H.2.2.2.1 0
    exact (((hM.sub contDiffAt_const).pow 2).add contDiffAt_const).sqrt (by positivity [hη.1])
  have hK : ContDiffAt ℝ 2 (fun Z : CoreAngleState => Z 0) Y := by fun_prop
  have hdR : coreRadius (coreTailState η Y 0) η + Y 0 ≠ 0 := by
    have hR0 : 0 ≤ coreRadius (coreTailState η Y 0) η := Real.sqrt_nonneg _
    change coreRadius (coreTailState η Y 0) η + k ≠ 0
    linarith only [hk, hR0]
  have hdF : compactConnectionFinitePhase η Y + Y 0 - 2 ≠ 0 := by
    rw [compactConnectionFinitePhase_reference hk hη]
    change k - 2 + k - 2 ≠ 0
    linarith only [hk]
  exact ((hI.mul (contDiffAt_const.sub (contDiffAt_const.div (hR.add hK) hdR))).add (hB.pow 2)).div
    ((hF.add hK).sub contDiffAt_const) hdF

theorem compactConnectionFinitePhase_weak_germ {k η : ℝ}
    (hk : 7 / 2 ≤ k) (hη : 0 < η ∧ η ≤ 1 / 10000) :
    (fun p : ℝ × ℝ => compactConnectionFinitePhase η ![p.1, 0, p.2]) =ᶠ[𝓝 (k, 0)]
      (fun p => p.1 - 2 + p.2 ^ 2 * compactConnectionWeakCoefficient η ![p.1, 0, p.2]) := by
  let c := fun p : ℝ × ℝ => (![p.1, 0, p.2] : CoreAngleState)
  have hc : Tendsto c (𝓝 (k, 0)) (𝓝 (![k, 0, 0] : CoreAngleState)) :=
    (by fun_prop : Continuous c).continuousAt.tendsto
  have H := coreTail_reference_regular (by linarith : 1 < k) ⟨hη.1, by linarith [hη.2]⟩
  have hm0 : 2 < -coreTailState η ![k, 0, 0] 0 := (compactConnection_reference_stable_phase hk hη).1
  have hm := ((contDiffAt_pi.mp H.2.2.2.1 0).neg.continuousAt).eventually (eventually_gt_nhds hm0)
  have hkp : ∀ᶠ p : ℝ × ℝ in 𝓝 (k, 0), 2 < p.1 :=
    continuousAt_fst.eventually (eventually_gt_nhds (show 2 < k by linarith))
  filter_upwards [hc.eventually H.2.2.2.2, hc.eventually hm, hkp] with p hp hm' hk'
  exact compactConnectionFinitePhase_weak_factorization hk'
    (by rw [abs_of_pos hη.1]; linarith [hη.2]) hp hm'.le rfl

theorem compactConnectionFinitePhase_weak_reference {k η : ℝ}
    (hk : 7 / 2 ≤ k) (hη : 0 < η ∧ η ≤ 1 / 10000) :
    fderiv ℝ (compactConnectionFinitePhase η) ![k, 0, 0] (Pi.single 2 1) = 0 := by
  have hline : HasDerivAt (fun w : ℝ => (![k, 0, w] : CoreAngleState)) (Pi.single 2 1) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa using hasDerivAt_const (0 : ℝ) k
    · simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · change HasDerivAt (fun w : ℝ => w) 1 0
      exact hasDerivAt_id' 0
  have hQ := ((contDiffAt_compactConnectionWeakCoefficient_reference hk hη).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt 0 hline
  have hF := ((contDiffAt_compactConnectionFinitePhase_reference hk hη).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt 0 hline
  have hd : HasDerivAt (fun w : ℝ => k - 2 + w ^ 2 * compactConnectionWeakCoefficient η ![k, 0, w]) 0 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (k - 2)).add (((hasDerivAt_id' (0 : ℝ)).pow 2).mul hQ) using 1
    simp
  have heq : (fun w : ℝ => compactConnectionFinitePhase η ![k, 0, w]) =ᶠ[𝓝 0]
      (fun w => k - 2 + w ^ 2 * compactConnectionWeakCoefficient η ![k, 0, w]) :=
    (by fun_prop : Continuous (fun w : ℝ => (k, w))).continuousAt.tendsto.eventually
      (compactConnectionFinitePhase_weak_germ hk hη)
  exact (hF.congr_of_eventuallyEq heq.symm).unique hd

end BianchiIX
