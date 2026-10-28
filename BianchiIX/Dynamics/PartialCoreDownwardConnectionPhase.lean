import BianchiIX.Dynamics.PartialCoreDownwardConnection
import BianchiIX.Dynamics.CoreConnectionDifferential
import BianchiIX.Dynamics.ConnectionPhaseCurve
import BianchiIX.Analysis.ConnectionPhaseComposition

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Uniform E.28 for a radial curve through the fixed downward return, including its incoming boundary. -/
theorem exists_partialCoreDownwardConnection_phase_error {K : ℝ} (hK : 1 ≤ K) :
    ∃ C > (0 : ℝ), ∀ {Y : ℝ → ProjectiveState} {x r Z : ℝ},
      (0 < r ∧ r ≤ 1) → 0 ≤ Z → DifferentiableAt ℝ Y x →
      let k := fun a => coreRadius (Y a 0) (Y a 2)
      let U := Y x 1
      let W := Y x 2 * Y x 3
      let z := fun a => projectiveCoreAngle (Y a)
      let τ := partialCoreDownwardReturnTime
      let out := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a))
      let f := fun a => coreRadius (out a 0) (out a 2)
      let p := fun a => coreExitConnectionParameters ![f a, out a 1, out a 3]
      let Δ := fun a => connectionReturnPhaseError (p a)
      let g := fun a => connectionReturnPhysicalState (p a) 0
      let E := 16 * K + 4 * (4096 * coreVariationBound) * K ^ 2 + C
      let R := fun a => 2 / g a - (2 / k a) / (1 - 2 / k a)
      6 ≤ k x → coreRegion (k x) (Y x) → (1 < Y x 2 ∨ (Y x 2 = 1 ∧ 1 ≤ Y x 0)) →
      2 * Real.cosh Z ≤ k x → z x ≤ Z → 0 < U → 0 < W →
      2 / (K * r) ≤ k x → k x ≤ K / r → |deriv k x| ≤ K / r ^ 2 →
      |deriv (fun a => Y a 1) x| ≤ K * U / r →
      |deriv (fun a => Y a 2 * Y a 3) x| ≤ K * W / r → |deriv z x| ≤ K / r →
      connectionReturnValid (p x) ∧
      connectionReturnState (p x) = projectiveOriginalFlow (Y x) 0 (τ (Y x) + connectionReturnTime (p x)) ∧
      DifferentiableAt ℝ k x ∧ DifferentiableAt ℝ f x ∧
      |f x - k x| ≤ 16 * K * (U + r * W ^ 2) ∧
      |deriv (fun a => f a - k a) x| ≤ 4 * (4096 * coreVariationBound) * K ^ 2 * (U + r * W) / r ^ 2 ∧
      DifferentiableAt ℝ Δ x ∧ |Δ x| ≤ C * r * (U + W ^ 2) ∧ |deriv Δ x| ≤ C * (U + W ^ 2) ∧
      DifferentiableAt ℝ g x ∧ k x / 4 ≤ g x ∧
      DifferentiableAt ℝ R x ∧ |R x| ≤ 8 * E * K ^ 2 * r ^ 2 * (U + r * W ^ 2) ∧
      |deriv R x| ≤ (8 * E * K ^ 2 + 32 * E * K ^ 4) * (U + r * W) := by
  let A := (200 * coreVariationBound + 2) * K ^ 2
  let B := 1180 * coreVariationBound * K ^ 4 + 4 * K ^ 2
  let F := K + 8 * (4096 * coreVariationBound) * K ^ 2
  let CU := K * (1 + 576 * A)
  let CW := K * (1 + B)
  let C := 1 + 24 * K + 50000 * (K ^ 2 * (2 * F) + K * CU + K * CW)
  have hK0 : 0 < K := by linarith only [hK]
  have hA : 0 ≤ A := by dsimp only [A, coreVariationBound]; positivity
  have hB : 0 ≤ B := by dsimp only [B, coreVariationBound]; positivity
  have hF : 0 ≤ F := by dsimp only [F, coreVariationBound]; positivity
  have hCU : 0 ≤ CU := by dsimp only [CU]; positivity
  have hCW : 0 ≤ CW := by dsimp only [CW]; positivity
  have hcoef : 0 ≤ 50000 * (K ^ 2 * (2 * F) + K * CU + K * CW) := by positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Y x r Z hr hZ hY k U W z τ out f p Δ g E R hk hy hV hkZ hz hUpos hWpos hklo hkhi hdk hdU hdW hdz
  have hr0 := hr.1
  have hk0 : 0 < k x := by linarith only [hk]
  have hU : 0 ≤ U := hy.2.2.1.1
  have hW : 0 ≤ W ∧ W ≤ 1 :=
    ⟨hy.2.2.2.1, (coreBootstrap_wall_bound hk hy.2.2.2.2).trans (by norm_num)⟩
  have hU1 : U ≤ 1 := (coreBootstrap_wall_bound hk hy.2.2.1.2).trans (by norm_num)
  have hki : 1 / k x ≤ K * r := by
    apply (div_le_iff₀ hk0).mpr
    nlinarith only [(div_le_iff₀ (mul_pos hK0 hr.1)).mp hklo]
  obtain ⟨hf, _, _, _, hfval, hfder, _⟩ := partialCoreDownwardReturn_radial_response hr hK hY
    hk hy hV hklo hkhi hdk hdU hdW hdz
  obtain ⟨_, _, _, _, _, hu, hw, hu0, hw0, hdu, hdw, _⟩ :=
    partialCoreDownwardReturn_radial_multipliers hr hK hY hk hy hV hki hkhi hdk hdU hdW hdz
  obtain ⟨_, hμ, huε, hwε, hdecU, hdecW, hphase, _, hvalid, _, _, horbit⟩ :=
    partialCoreDownwardReturn_connection_domain hk hy rfl hV hZ hkZ hz
      ⟨by norm_num, le_rfl⟩ ⟨hUpos, hy.2.2.1.2⟩ ⟨hWpos, hy.2.2.2.2⟩
  let u := fun a => out a 1
  let w := fun a => out a 3
  have hp : p x = coreExitConnectionParameters (partialCoreDownwardReturnState (Y x)) :=
    (partialCoreDownwardReturn_connectionParameters_eventuallyEq hk hy rfl hV).self_of_nhds
  rw [← hp] at hμ huε hwε hdecU hdecW hphase hvalid horbit
  have hphase' : phaseNorm (p x 0 + 1) 1 = f x := hphase
  have hf1 : 1 < f x := by
    have Hb := phaseNorm_ge (b := 1) (show 0 ≤ p x 0 + 1 by linarith only [hμ.1])
    rw [hphase'] at Hb
    linarith only [hμ.1, Hb]
  have hkd : DifferentiableAt ℝ k x := by
    have H := ((contDiffAt_toCoreAngleState 1 (zero_lt_one.trans_le hy.2.1)).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt x hY.hasDerivAt
    exact (hasDerivAt_pi.mp H 0).differentiableAt
  change DifferentiableAt ℝ f x at hf
  change |deriv (fun a => f a - k a) x| ≤
    4 * (4096 * coreVariationBound) * K ^ 2 * (U + r * W) / r ^ 2 at hfder
  have hfhi : |deriv f x| ≤ F / r ^ 2 := by
    have hs : U + r * W ≤ 2 := by nlinarith only [hU1, mul_le_mul hr.2 hW.2 hW.1 (by norm_num : (0 : ℝ) ≤ 1)]
    have He := hfder.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs (by dsimp only [coreVariationBound]; positivity)) (sq_nonneg r))
    rw [deriv_fun_sub hf hkd] at He
    calc
      _ = |deriv k x + (deriv f x - deriv k x)| := by congr 1; ring
      _ ≤ |deriv k x| + |deriv f x - deriv k x| := abs_add_le _ _
      _ ≤ K / r ^ 2 + 4 * (4096 * coreVariationBound) * K ^ 2 * 2 / r ^ 2 := add_le_add hdk He
      _ = _ := by dsimp only [F]; ring
  have Hwall := partial_core_connection_wall_budget hr.1 hK0.le hk hki hkhi hA hB hU hu0 hw0 hdecU hdecW hdu hdw
  let v : CoreAngleState := ![deriv f x, deriv u x, deriv w x]
  have hcurve : HasDerivAt (fun a => ![f a, u a, w a]) v x := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hf.hasDerivAt
    · exact hu.hasDerivAt
    · exact hw.hasDerivAt
  let ξ := fderiv ℝ coreExitConnectionParameters ![f x, u x, w x] v
  have Hp : HasDerivAt p ξ x := ((contDiffAt_coreExitConnectionParameters 1 hf1).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt (f := fun a => ![f a, u a, w a]) x hcurve
  have Hξ := coreExitConnectionParameters_differential (Z := ![f x, u x, w x]) hf1 v
  change ((p x 0 + 1) / phaseNorm (p x 0 + 1) 1) * ξ 0 = deriv f x ∧
    ξ 1 = deriv u x ∧ ξ 2 = deriv w x at Hξ
  have hμi : 1 / p x 0 ≤ K * r := by
    apply (div_le_iff₀ (by linarith only [hμ.1] : 0 < p x 0)).mpr
    have H := (div_le_iff₀ (mul_pos hK0 hr.1)).mp hklo
    have H' := mul_le_mul_of_nonneg_right hμ.2.1 (mul_pos hK0 hr.1).le
    nlinarith only [H, H']
  have hξ0 : |ξ 0| ≤ 2 * |deriv f x| := by
    let L := (p x 0 + 1) / phaseNorm (p x 0 + 1) 1
    have HL := (phaseNorm_ratio_bounds (b := 1) (by linarith only [hμ.1] : 2 ≤ p x 0 + 1) (by norm_num)).1
    have HL0 : 0 ≤ L := by dsimp only [L]; linarith only [HL]
    have HE : L * |ξ 0| = |deriv f x| := by rw [← Hξ.1, abs_mul, abs_of_nonneg HL0]
    nlinarith only [mul_le_mul_of_nonneg_right HL (abs_nonneg (ξ 0)), HE, abs_nonneg (ξ 0)]
  have HΔ := connectionReturn_phase_curve_bounds Hp hr.1 hK0.le (by positivity : 0 ≤ 2 * F) hCU hCW
    hμ.1 hμi ⟨huε.1.le, huε.2⟩ hwε hU hW Hwall.1 hdecW
    (hξ0.trans ((mul_le_mul_of_nonneg_left hfhi (by norm_num)).trans_eq (by ring)))
    (by rw [Hξ.2.1]; exact Hwall.2.1) (by rw [Hξ.2.2]; exact Hwall.2.2)
  have hΔval : |Δ x| ≤ C * r * (U + W ^ 2) :=
    HΔ.2.1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show 24 * K ≤ C by dsimp only [C]; linarith only [hcoef]) hr.1.le)
      (by positivity))
  have hΔder : |deriv Δ x| ≤ C * (U + W ^ 2) :=
    HΔ.2.2.trans (mul_le_mul_of_nonneg_right
      (show 50000 * (K ^ 2 * (2 * F) + K * CU + K * CW) ≤ C by dsimp only [C]; linarith only [hK0])
      (by positivity))
  have hE : 0 ≤ E := by dsimp only [E, coreVariationBound]; positivity
  have Hgerm : g =ᶠ[𝓝 x] (fun a => f a - 2 + Δ a) := by
    filter_upwards [hf.continuousAt.eventually (lt_mem_nhds hf1)] with a ha
    have Hphase := coreExitConnectionParameters_phase (Z := ![f a, u a, w a]) ha
    change phaseNorm (p a 0 + 1) 1 = f a at Hphase
    dsimp only [g, Δ, connectionReturnPhysicalState, connectionReturnPhaseError]
    simp only [Matrix.cons_val_zero, Hphase]
    ring
  have hglo : k x / 4 ≤ g x := by
    have Hcontrol := connectionReturn_control hμ.1 ⟨huε.1.le, huε.2⟩ hwε
    have Hregion := (Hcontrol.2 (connectionReturnTime (p x)) ⟨Hcontrol.1.le, le_rfl⟩).2
    change connectionRegion (p x 0) (connectionReturnState (p x)) at Hregion
    have HM := (abs_le.mp Hregion.1).1
    have Hleft : p x 0 / 2 ≤ -connectionReturnState (p x) 0 - 1 := by linarith only [HM, hμ.1]
    have Hnorm := phaseNorm_ge (b := 1) (show 0 ≤ -connectionReturnState (p x) 0 - 1 by linarith only [Hleft, hμ.1])
    change _ ≤ g x at Hnorm
    linarith only [hμ.2.1, Hleft, Hnorm]
  have Hcomp := connection_phase_composition_bounds hr hU hW (by positivity : 0 ≤ 16 * K)
    (by dsimp only [coreVariationBound]; positivity : 0 ≤ 4 * (4096 * coreVariationBound) * K ^ 2)
    hC.le hf hkd HΔ.1 Hgerm hfval hfder hΔval hΔder
  have Hrec := connection_reciprocal_radial_bounds hr hK hE hU hW Hcomp.1 hkd hk hklo hglo hdk Hcomp.2.1 Hcomp.2.2
  exact ⟨hvalid, horbit, hkd, hf, hfval, hfder, HΔ.1, hΔval, hΔder, Hcomp.1, hglo, Hrec⟩

end BianchiIX
