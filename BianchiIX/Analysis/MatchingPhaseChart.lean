import BianchiIX.Analysis.MatchingPhaseDifferential

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

abbrev MatchingPhaseParameters := Fin 3 → ℝ

def matchingPhaseSeed (m v w : ℝ) : MatchingPhaseParameters := ![matchingPhase m v w, v, w]

theorem matchingPhase_inverse_fderiv {M : MatchingPhaseParameters → ℝ} {p : MatchingPhaseParameters}
    (hM : DifferentiableAt ℝ M p) (hm : 1 < M p) (hf : matchingPhaseSlope (M p) (p 1) (p 2) ≠ 0)
    (heq : ∀ᶠ q in 𝓝 p, matchingPhase (M q) (q 1) (q 2) = q 0) (z : MatchingPhaseParameters) :
    fderiv ℝ M p z = (z 0 - p 1 / phaseNorm (M p + 1) (p 1) * z 1 -
      p 2 / phaseNorm (M p - 1) (p 2) * z 2) / matchingPhaseSlope (M p) (p 1) (p 2) := by
  have H := hasFDerivAt_matchingPhase_comp hM.hasFDerivAt
    (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 3) p) (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 3) p) hm
  have H' := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 3) p).congr_of_eventuallyEq heq
  have hz := congrArg (fun L : MatchingPhaseParameters →L[ℝ] ℝ => L z) (H.unique H')
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul] at hz
  apply (eq_div_iff hf).mpr
  linarith only [hz]

/-- The phase has a genuine local inverse in m, with ordinary wall parameters including zero. -/
theorem exists_matchingPhase_chart {μ m v w : ℝ} (hμ : 4 ≤ μ) (hm : |m - μ| ≤ 1 / 2)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    let p := matchingPhaseSeed m v w
    ∃ M : MatchingPhaseParameters → ℝ, M p = m ∧ ContDiffAt ℝ 2 M p ∧
      (∀ᶠ q in 𝓝 p, matchingPhase (M q) (q 1) (q 2) = q 0) ∧
      (∀ᶠ z : MatchingPhaseParameters × ℝ in 𝓝 (p, m), matchingPhase z.2 (z.1 1) (z.1 2) = z.1 0 ↔ M z.1 = z.2) ∧
      (∀ z : MatchingPhaseParameters, fderiv ℝ M p z =
        (z 0 - v / phaseNorm (m + 1) v * z 1 - w / phaseNorm (m - 1) w * z 2) / matchingPhaseSlope m v w) := by
  intro p
  have hm1 : 1 < m := by linarith only [hμ, (abs_le.mp hm).1]
  have hf : matchingPhaseSlope m v w ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (by norm_num) (matchingPhase_slope_bounds hμ hm hv hw).1)
  let Q : MatchingPhaseParameters × ℝ → ℝ := fun z => matchingPhase z.2 (z.1 1) (z.1 2) - z.1 0
  have hcQ : ContDiffAt ℝ 2 Q (p, m) :=
    (contDiffAt_matchingPhase_comp 2 (by fun_prop) (by fun_prop) (by fun_prop) hm1).sub (by fun_prop)
  have hd : HasDerivAt (fun s => Q (p, s)) (matchingPhaseSlope m v w) m := by
    have H := (hasDerivAt_matchingPhase (hasDerivAt_id m) (hasDerivAt_const m v) (hasDerivAt_const m w) hm1).sub_const (p 0)
    simpa [Q, p, matchingPhaseSeed] using H
  have htime : (fderiv ℝ Q (p, m)).comp (ContinuousLinearMap.inr ℝ MatchingPhaseParameters ℝ) =
      matchingPhaseSlope m v w • ContinuousLinearMap.id ℝ ℝ := by
    have H := ((hcQ.differentiableAt (by norm_num)).hasFDerivAt.comp m
      (hasFDerivAt_prodMk_right p m)).unique hd.hasFDerivAt
    rw [H]
    ext
    simp [mul_comm]
  have hinv : ((fderiv ℝ Q (p, m)).comp (ContinuousLinearMap.inr ℝ MatchingPhaseParameters ℝ)).IsInvertible := by
    rw [htime]
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := (matchingPhaseSlope m v w)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · ext
      simp [hf]
    · ext
      simp [hf]
  let M := hcQ.implicitFunction (by norm_num) hinv
  have hM : M p = m := hcQ.implicitFunction_apply_self (by norm_num) hinv
  have hcM : ContDiffAt ℝ 2 M p := hcQ.contDiffAt_implicitFunction (by norm_num) hinv
  have hbase : Q (p, m) = 0 := sub_self _
  have heq : ∀ᶠ q in 𝓝 p, matchingPhase (M q) (q 1) (q 2) = q 0 := by
    filter_upwards [hcQ.eventually_apply_implicitFunction (by norm_num) hinv] with q hq
    exact sub_eq_zero.mp (hq.trans hbase)
  refine ⟨M, hM, hcM, heq, ?_, ?_⟩
  · filter_upwards [hcQ.eventually_apply_eq_iff_implicitFunction (by norm_num) hinv] with z hz
    simpa only [hbase, Q, sub_eq_zero] using hz
  · intro z
    have hp1 : p 1 = v := rfl
    have hp2 : p 2 = w := rfl
    have H := matchingPhase_inverse_fderiv (hcM.differentiableAt (by norm_num))
      (by rw [hM]; exact hm1) (by rw [hM, hp1, hp2]; exact hf) heq z
    simpa only [hM, hp1, hp2] using H

end BianchiIX
