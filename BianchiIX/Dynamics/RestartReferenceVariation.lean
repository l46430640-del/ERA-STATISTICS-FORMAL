import BianchiIX.Dynamics.RestartReferenceFlow
import BianchiIX.Dynamics.RestartReferenceTransfer
import BianchiIX.Dynamics.GlobalVariation

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The center block of the genuine Einstein-field differential is independent of the other two directions. -/
theorem normalizedDifferential_restart_reference_center {n : ℝ} (hn : n ^ 2 < 1) (d : NormalizedState) :
    normalizedDifferential (restartReferenceInitial n) d 1 = n ^ 2 * d 1 + Real.sqrt 3 * n * (d 3 - d 4) ∧
    normalizedDifferential (restartReferenceInitial n) d 3 = restartReferenceWallRate n * d 3 ∧
    normalizedDifferential (restartReferenceInitial n) d 4 = restartReferenceWallRate n * d 4 := by
  let γ : ℝ → NormalizedState := fun r => restartReferenceInitial n + r • d
  have Hγ : HasDerivAt γ d 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (restartReferenceInitial n)).add ((hasDerivAt_id' 0).smul_const d) using 1
    simp
  have Hfield : HasDerivAt (fun r => normalizedField (γ r))
      (normalizedDifferential (restartReferenceInitial n) d) 0 := by
    simpa only [Function.comp_def] using
      (hasFDerivAt_normalizedField (restartReferenceInitial n)).comp_hasDerivAt_of_eq 0 Hγ (by simp [γ])
  have hp := hasDerivAt_pi.mp Hγ 0
  have hs := hasDerivAt_pi.mp Hγ 1
  have hN := hasDerivAt_pi.mp Hγ 2
  have ha := hasDerivAt_pi.mp Hγ 3
  have hb := hasDerivAt_pi.mp Hγ 4
  have HQ := ((hN.pow 2).add (ha.pow 2) |>.add (hb.pow 2)).sub
    (((hN.mul ha).add (ha.mul hb) |>.add (hb.mul hN)).const_mul 2)
  constructor
  · apply (hasDerivAt_pi.mp Hfield 1).unique
    convert! (HQ.mul hs).add
      ((((ha.pow 2).neg.add (hb.pow 2)).add (hN.mul ha) |>.sub (hN.mul hb)).const_mul (Real.sqrt 3)) using 1
    simp [γ, restartReferenceInitial]
    ring
  constructor
  · apply (hasDerivAt_pi.mp Hfield 3).unique
    convert! (((hp.pow 2).add (hs.pow 2)).neg.sub hp |>.add (hs.const_mul (Real.sqrt 3))).mul ha using 1
    simp [γ, restartReferenceInitial, restartReferenceWallRate, restartReferenceRoot_sq hn.le]
  · apply (hasDerivAt_pi.mp Hfield 4).unique
    convert! (((hp.pow 2).add (hs.pow 2)).neg.sub hp |>.sub (hs.const_mul (Real.sqrt 3))).mul hb using 1
    simp [γ, restartReferenceInitial, restartReferenceWallRate, restartReferenceRoot_sq hn.le]

def restartReferenceVariation (h : ℝ) (d : NormalizedState) (t : ℝ) : NormalizedState :=
  normalizedFlowDifferential (restartReferenceInitial h) 0 t d

theorem restartReferenceVariation_initial (h : ℝ) (d : NormalizedState) :
    restartReferenceVariation h d 0 = d := by
  simp only [restartReferenceVariation, normalizedFlowDifferential_initial, ContinuousLinearMap.id_apply]

/-- The reference center system is the actual initial-state variational equation. -/
theorem hasDerivAt_restartReferenceVariation_center {h t : ℝ}
    (hh : h ^ 2 < 1) (ht : 0 ≤ t) (d : NormalizedState) :
    HasDerivAt (fun r => restartReferenceVariation h d r 1)
      (restartReferenceCurve h t 2 ^ 2 * restartReferenceVariation h d t 1 +
        Real.sqrt 3 * restartReferenceCurve h t 2 *
          (restartReferenceVariation h d t 3 - restartReferenceVariation h d t 4)) t ∧
    HasDerivAt (fun r => restartReferenceVariation h d r 3)
      (restartReferenceWallRate (restartReferenceCurve h t 2) * restartReferenceVariation h d t 3) t ∧
    HasDerivAt (fun r => restartReferenceVariation h d r 4)
      (restartReferenceWallRate (restartReferenceCurve h t 2) * restartReferenceVariation h d t 4) t := by
  have HD : HasDerivAt (restartReferenceVariation h d)
      (normalizedDifferential (restartReferenceCurve h t) (restartReferenceVariation h d t)) t := by
    convert!
      (hasDerivAt_normalizedFlowDifferential (restartReferenceCurve_forward hh.le ht).1).clm_apply
        (hasDerivAt_const t d) using 1
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.map_zero, add_zero]
    rfl
  have HC := normalizedDifferential_restart_reference_center (restartReferenceCurve_shape hh ht).1
    (restartReferenceVariation h d t)
  rw [← (restartReferenceCurve_shape hh ht).2] at HC
  exact ⟨(hasDerivAt_pi.mp HD 1).congr_deriv HC.1,
    (hasDerivAt_pi.mp HD 3).congr_deriv HC.2.1, (hasDerivAt_pi.mp HD 4).congr_deriv HC.2.2⟩

/-- The finite conserved quantities hold for every ambient initial-state variation of the exact flow. -/
theorem restartReferenceVariation_conservation {h t : ℝ} (hh : h ^ 2 < 1) (ht : 0 ≤ t) (d : NormalizedState) :
    let n := restartReferenceCurve h t 2
    let v := restartReferenceVariation h d t
    restartShearFactor n * v 1 + restartShearCoupling n * (v 3 - v 4) =
        restartShearFactor h * d 1 + restartShearCoupling h * (d 3 - d 4) ∧
      restartWallFactor n * v 3 = restartWallFactor h * d 3 ∧
      restartWallFactor n * v 4 = restartWallFactor h * d 4 := by
  have HC := restart_reference_linear_conservation (I := Ici (0 : ℝ)) (convex_Ici 0)
    (fun r hr => (restartReferenceCurve_shape hh hr).1)
    (fun r hr => hasDerivAt_restartReference_strong hh hr)
    (fun r hr => (hasDerivAt_restartReferenceVariation_center hh hr d).1)
    (fun r hr => (hasDerivAt_restartReferenceVariation_center hh hr d).2.1)
    (fun r hr => (hasDerivAt_restartReferenceVariation_center hh hr d).2.2)
    (t₀ := 0) (t := t) (by simp) ht
  simpa [restartReferenceCurve_initial, restartReferenceInitial, restartReferenceVariation_initial] using HC

/-- Formulas (E.2)--(E.3) are the center limit of the genuine Einstein-flow differential. -/
theorem tendsto_restartReferenceVariation_center {h : ℝ} (hh : 0 < h ∧ h ≤ 1 / 16) (d : NormalizedState) :
    Tendsto (fun t => restartReferenceVariation h d t 1) atTop
        (𝓝 (restartShearFactor h * d 1 + restartShearCoupling h * (d 3 - d 4))) ∧
      Tendsto (fun t => restartReferenceVariation h d t 3) atTop (𝓝 (restartWallFactor h * d 3)) ∧
      Tendsto (fun t => restartReferenceVariation h d t 4) atTop (𝓝 (restartWallFactor h * d 4)) := by
  have hh2 : h ^ 2 < 1 := by nlinarith only [hh.1, hh.2]
  have HC := tendsto_restart_reference_linear_transfer
    (fun r hr => (restartReferenceCurve_shape hh2 hr).1)
    (fun r hr => hasDerivAt_restartReference_strong hh2 hr)
    (fun r hr => (hasDerivAt_restartReferenceVariation_center hh2 hr d).1)
    (fun r hr => (hasDerivAt_restartReferenceVariation_center hh2 hr d).2.1)
    (fun r hr => (hasDerivAt_restartReferenceVariation_center hh2 hr d).2.2)
    (tendsto_restartReference_strong hh)
  simpa [restartReferenceCurve_initial, restartReferenceInitial, restartReferenceVariation_initial] using HC

end BianchiIX
