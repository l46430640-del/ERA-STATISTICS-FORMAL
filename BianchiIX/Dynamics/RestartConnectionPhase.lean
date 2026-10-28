import BianchiIX.Dynamics.RestartPartialCoreConnection
import BianchiIX.Dynamics.PartialCoreRadialMultipliers
import BianchiIX.Dynamics.CoreConnectionDifferential
import BianchiIX.Dynamics.ConnectionPhaseCurve
import BianchiIX.Analysis.ConnectionReciprocalCurve

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The actual family satisfies the amplitude-sensitive connection correction and full E.28. -/
theorem exists_restartConnection_phase_error :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∃ K : ℝ, 1 ≤ K ∧ ∃ C : ℝ, 0 < C ∧
        ∀ q P : ℝ, 3 < q → 4 < P → ∃ rstar : ℝ, 0 < rstar ∧
          ∀ r ∈ Ioc (0 : ℝ) rstar, ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) →
            ∀ ρ ∈ Icc r (2 * r),
              let s := q / 2 * Real.log (1 / r)
              let Y := restartFastProjectiveEntry h s θ ζ
              let k := restartFastCoreRadius h s θ ζ
              let U := Y ρ 1
              let W := Y ρ 2 * Y ρ 3
              ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (Y ρ) 0 t 2 = 1} T ∧
                ∃ τ : ProjectiveState → ℝ, τ (Y ρ) = T ∧ ContDiffAt ℝ 2 τ (Y ρ) ∧
                  (∀ᶠ y in 𝓝 (Y ρ), IsLeast {t | 0 < t ∧
                    t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧ projectiveOriginalFlow y 0 t 2 = 1} (τ y)) ∧
                  let out := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a))
                  let f := fun a => coreRadius (out a 0) (out a 2)
                  let p := fun a => coreExitConnectionParameters ![f a, out a 1, out a 3]
                  let Δ := fun a => connectionReturnPhaseError (p a)
                  let g := fun a => connectionReturnPhysicalState (p a) 0
                  let E := 16 * K + 4 * (4096 * coreVariationBound) * K ^ 2 + C
                  let R := fun a => 2 / g a - (2 / k a) / (1 - 2 / k a)
                  connectionReturnValid (p ρ) ∧ connectionReturnState (p ρ) = toProjectiveState
                    (normalizedMaxCurve (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0
                      (s + T + connectionReturnTime (p ρ))) ∧
                  r ≤ 1 ∧ 6 ≤ k ρ ∧ 2 / (K * r) ≤ k ρ ∧ k ρ ≤ K / r ∧
                  0 ≤ U ∧ (0 ≤ W ∧ W ≤ 1) ∧
                  DifferentiableAt ℝ k ρ ∧ DifferentiableAt ℝ f ρ ∧
                  |deriv k ρ| ≤ K / r ^ 2 ∧
                  |f ρ - k ρ| ≤ 16 * K * (U + r * W ^ 2) ∧
                  |deriv (fun a => f a - k a) ρ| ≤
                    4 * (4096 * coreVariationBound) * K ^ 2 * (U + r * W) / r ^ 2 ∧
                  DifferentiableAt ℝ Δ ρ ∧ |Δ ρ| ≤ C * r * (U + W ^ 2) ∧
                  |deriv Δ ρ| ≤ C * (U + W ^ 2) ∧
                  DifferentiableAt ℝ g ρ ∧ k ρ / 4 ≤ g ρ ∧
                  DifferentiableAt ℝ R ρ ∧ |R ρ| ≤ 8 * E * K ^ 2 * r ^ 2 * (U + r * W ^ 2) ∧
                  |deriv R ρ| ≤ (8 * E * K ^ 2 + 32 * E * K ^ 4) * (U + r * W) := by
  obtain ⟨hD, hhD, HD⟩ := exists_restartPartialCore_radial_data
  obtain ⟨hE, hhE, HE⟩ := exists_restartPartialCore_connection
  refine ⟨min hD hE, lt_min hhD hhE, ?_⟩
  intro h hh L hL
  obtain ⟨K, hK, _, _, HK⟩ := HD h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL
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
  refine ⟨K, hK, C, hC, ?_⟩
  intro q P hq hP
  obtain ⟨rD, hrD, HRD⟩ := HK q P hq hP
  obtain ⟨rE, hrE, HRE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ L hL q P hq hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  refine ⟨min rD rE, lt_min hrD hrE, ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have hr0 := hr.1
  let s := q / 2 * Real.log (1 / r)
  let Y := restartFastProjectiveEntry h s θ ζ
  let k := restartFastCoreRadius h s θ ζ
  let U := Y ρ 1
  let W := Y ρ 2 * Y ρ 3
  obtain ⟨hr1, _, _, _, _, hY, _, hkZ, _, hy, hV, _, hklo, hkhi, hdk, _, hdU, hdW, hdz⟩ :=
    HRD r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ ⟨hζ.1.le, hζ.2⟩ ρ hρ
  have hk : 6 ≤ k ρ := (le_max_left _ _).trans hkZ
  have hk0 : 0 < k ρ := by linarith only [hk]
  have hU : 0 ≤ U := hy.2.2.1.1
  have hW : 0 ≤ W ∧ W ≤ 1 :=
    ⟨hy.2.2.2.1, (coreBootstrap_wall_bound hk hy.2.2.2.2).trans (by norm_num)⟩
  have hU1 : U ≤ 1 := (coreBootstrap_wall_bound hk hy.2.2.1.2).trans (by norm_num)
  have hki : 1 / k ρ ≤ K * r := by
    apply (div_le_iff₀ hk0).mpr
    nlinarith only [(div_le_iff₀ (mul_pos hK0 hr.1)).mp hklo]
  obtain ⟨T, hT, hfirst, τ, hτ, hcτ, hnear, hf, _, _, _, hfval, hfder, _⟩ :=
    exists_partialCore_radial_curve_response ⟨hr.1, hr1⟩ hK hY hk hy hV hklo hkhi hdk hdU hdW hdz
  have hfirstnear := hnear.mono fun _ h => h.1
  obtain ⟨_, _, _, _, _, hu, hw, hu0, hw0, hdu, hdw, _⟩ :=
    partialCore_radial_multiplier_response ⟨hr.1, hr1⟩ hK hY hfirstnear hk hy hV hki hkhi hdk hdU hdW hdz
  obtain ⟨S, _, hfirstS, _, _, hμ, huε, hwε, hdecU, hdecW, hphase, hvalid, _, _, horbit⟩ :=
    HRE r ⟨hr.1, hr.2.trans (min_le_right _ _)⟩ θ ζ hθ hζ ρ hρ
  have hST : S = T := hfirstS.unique hfirst
  rw [hST] at hμ huε hwε hdecU hdecW hphase hvalid horbit
  let out := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a))
  let f := fun a => coreRadius (out a 0) (out a 2)
  let u := fun a => out a 1
  let w := fun a => out a 3
  let p := fun a => coreExitConnectionParameters ![f a, u a, w a]
  have hout : out ρ = projectiveOriginalFlow (Y ρ) 0 T := by dsimp only [out]; rw [hτ]
  have houtV : out ρ 2 = 1 := by rw [hout]; exact hfirst.1.2
  have hZ : ![f ρ, u ρ, w ρ] = toCoreAngleState (out ρ) := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · change out ρ 3 = out ρ 2 * out ρ 3
      rw [houtV, one_mul]
  have hp : p ρ = coreExitConnectionParameters (toCoreAngleState (projectiveOriginalFlow (Y ρ) 0 T)) := by
    change coreExitConnectionParameters ![f ρ, u ρ, w ρ] = _
    rw [hZ, hout]
  rw [← hp] at hμ huε hwε hdecU hdecW hphase hvalid horbit
  have hphase' : phaseNorm (p ρ 0 + 1) 1 = f ρ := by dsimp only [f]; rw [hout]; exact hphase
  have hf1 : 1 < f ρ := by
    have Hb := phaseNorm_ge (b := 1) (show 0 ≤ p ρ 0 + 1 by linarith only [hμ.1])
    rw [hphase'] at Hb
    linarith only [hμ.1, Hb]
  have hkd : DifferentiableAt ℝ k ρ := by
    have H := ((contDiffAt_toCoreAngleState 1 (zero_lt_one.trans hV)).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt ρ hY.hasDerivAt
    exact (hasDerivAt_pi.mp H 0).differentiableAt
  change DifferentiableAt ℝ f ρ at hf
  change |deriv (fun a => f a - k a) ρ| ≤
    4 * (4096 * coreVariationBound) * K ^ 2 * (U + r * W) / r ^ 2 at hfder
  have hfhi : |deriv f ρ| ≤ F / r ^ 2 := by
    have hs : U + r * W ≤ 2 := by nlinarith only [hU1, mul_le_mul hr1 hW.2 hW.1 (by norm_num : (0 : ℝ) ≤ 1)]
    have He := hfder.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs (by dsimp only [coreVariationBound]; positivity)) (sq_nonneg r))
    rw [deriv_fun_sub hf hkd] at He
    calc
      _ = |deriv k ρ + (deriv f ρ - deriv k ρ)| := by congr 1; ring
      _ ≤ |deriv k ρ| + |deriv f ρ - deriv k ρ| := abs_add_le _ _
      _ ≤ K / r ^ 2 + 4 * (4096 * coreVariationBound) * K ^ 2 * 2 / r ^ 2 := add_le_add hdk He
      _ = _ := by dsimp only [F]; ring
  have Hwall := partial_core_connection_wall_budget hr.1 hK0.le hk hki hkhi hA hB hU hu0 hw0 hdecU hdecW hdu hdw
  let v : CoreAngleState := ![deriv f ρ, deriv u ρ, deriv w ρ]
  have hcurve : HasDerivAt (fun a => ![f a, u a, w a]) v ρ := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hf.hasDerivAt
    · exact hu.hasDerivAt
    · exact hw.hasDerivAt
  let ξ := fderiv ℝ coreExitConnectionParameters ![f ρ, u ρ, w ρ] v
  have Hp : HasDerivAt p ξ ρ := ((contDiffAt_coreExitConnectionParameters 1 hf1).differentiableAt
    (by norm_num)).hasFDerivAt.comp_hasDerivAt (f := fun a => ![f a, u a, w a]) ρ hcurve
  have Hξ := coreExitConnectionParameters_differential (Z := ![f ρ, u ρ, w ρ]) hf1 v
  change ((p ρ 0 + 1) / phaseNorm (p ρ 0 + 1) 1) * ξ 0 = deriv f ρ ∧
    ξ 1 = deriv u ρ ∧ ξ 2 = deriv w ρ at Hξ
  have hμi : 1 / p ρ 0 ≤ K * r := by
    apply (div_le_iff₀ (by linarith only [hμ.1] : 0 < p ρ 0)).mpr
    have H := (div_le_iff₀ (mul_pos hK0 hr.1)).mp hklo
    have H' := mul_le_mul_of_nonneg_right hμ.2.1 (mul_pos hK0 hr.1).le
    nlinarith only [H, H']
  have hξ0 : |ξ 0| ≤ 2 * |deriv f ρ| := by
    let R := (p ρ 0 + 1) / phaseNorm (p ρ 0 + 1) 1
    have HR := (phaseNorm_ratio_bounds (b := 1) (by linarith only [hμ.1] : 2 ≤ p ρ 0 + 1) (by norm_num)).1
    have HR0 : 0 ≤ R := by dsimp only [R]; linarith only [HR]
    have HE : R * |ξ 0| = |deriv f ρ| := by rw [← Hξ.1, abs_mul, abs_of_nonneg HR0]
    nlinarith only [mul_le_mul_of_nonneg_right HR (abs_nonneg (ξ 0)), HE, abs_nonneg (ξ 0)]
  have HΔ := connectionReturn_phase_curve_bounds Hp hr.1 hK0.le (by positivity : 0 ≤ 2 * F) hCU hCW
    hμ.1 hμi ⟨huε.1.le, huε.2⟩ hwε hU hW Hwall.1 hdecW
    (hξ0.trans ((mul_le_mul_of_nonneg_left hfhi (by norm_num)).trans_eq (by ring)))
    (by rw [Hξ.2.1]; exact Hwall.2.1) (by rw [Hξ.2.2]; exact Hwall.2.2)
  have hΔval : |connectionReturnPhaseError (p ρ)| ≤ C * r * (U + W ^ 2) :=
    HΔ.2.1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show 24 * K ≤ C by dsimp only [C]; linarith only [hcoef]) hr.1.le)
      (by positivity))
  have hΔder : |deriv (fun a => connectionReturnPhaseError (p a)) ρ| ≤ C * (U + W ^ 2) :=
    HΔ.2.2.trans (mul_le_mul_of_nonneg_right
      (show 50000 * (K ^ 2 * (2 * F) + K * CU + K * CW) ≤ C by dsimp only [C]; linarith only [hK0])
      (by positivity))
  let Δ := fun a => connectionReturnPhaseError (p a)
  let g := fun a => connectionReturnPhysicalState (p a) 0
  let E := 16 * K + 4 * (4096 * coreVariationBound) * K ^ 2 + C
  have hE : 0 ≤ E := by dsimp only [E, coreVariationBound]; positivity
  have Hgerm : g =ᶠ[𝓝 ρ] (fun a => f a - 2 + Δ a) := by
    filter_upwards [hf.continuousAt.eventually (lt_mem_nhds hf1)] with a ha
    have Hphase := coreExitConnectionParameters_phase (Z := ![f a, u a, w a]) ha
    change phaseNorm (p a 0 + 1) 1 = f a at Hphase
    dsimp only [g, Δ, connectionReturnPhysicalState, connectionReturnPhaseError]
    simp only [Matrix.cons_val_zero, Hphase]
    ring
  have Hg : HasDerivAt g (deriv f ρ + deriv Δ ρ) ρ :=
    ((hf.hasDerivAt.sub_const 2).add HΔ.1.hasDerivAt).congr_of_eventuallyEq Hgerm
  have hglo : k ρ / 4 ≤ g ρ := by
    have Hcontrol := connectionReturn_control hμ.1 ⟨huε.1.le, huε.2⟩ hwε
    have Hregion := (Hcontrol.2 (connectionReturnTime (p ρ)) ⟨Hcontrol.1.le, le_rfl⟩).2
    change connectionRegion (p ρ 0) (connectionReturnState (p ρ)) at Hregion
    have HM := (abs_le.mp Hregion.1).1
    have Hleft : p ρ 0 / 2 ≤ -connectionReturnState (p ρ) 0 - 1 := by linarith only [HM, hμ.1]
    have Hnorm := phaseNorm_ge (b := 1) (show 0 ≤ -connectionReturnState (p ρ) 0 - 1 by linarith only [Hleft, hμ.1])
    change _ ≤ g ρ at Hnorm
    linarith only [hμ.2.1, Hleft, Hnorm]
  have hW0 := hW.1
  have hRU : r * U ≤ U := mul_le_of_le_one_left hU hr1
  have hvalue : |g ρ - (k ρ - 2)| ≤ E * (U + r * W ^ 2) := by
    have heq : g ρ - (k ρ - 2) = (f ρ - k ρ) + Δ ρ := by rw [Hgerm.self_of_nhds]; ring
    rw [heq]
    have HΔvalue : |Δ ρ| ≤ C * (U + r * W ^ 2) := hΔval.trans (by
      have H := mul_le_mul_of_nonneg_left hRU hC.le
      nlinarith only [H])
    have Htotal := (abs_add_le (f ρ - k ρ) (Δ ρ)).trans (add_le_add hfval HΔvalue)
    have Hextra : 0 ≤ (4 * (4096 * coreVariationBound) * K ^ 2) * (U + r * W ^ 2) := by
      dsimp only [coreVariationBound]
      positivity
    dsimp only [E]
    nlinarith only [Htotal, Hextra]
  have hder : |deriv g ρ - deriv k ρ| ≤ E * (U + r * W) / r ^ 2 := by
    have hRW : 0 ≤ r * W ∧ r * W ≤ 1 :=
      ⟨mul_nonneg hr.1.le hW.1, (mul_le_mul hr1 hW.2 hW.1 (by norm_num)).trans_eq (by ring)⟩
    have hsmall : r ^ 2 * (U + W ^ 2) ≤ U + r * W := by
      have hr2 : r ^ 2 ≤ 1 := by nlinarith only [hr.1, hr1]
      nlinarith only [mul_le_mul_of_nonneg_right hr2 hU,
        mul_le_mul_of_nonneg_right hRW.2 hRW.1]
    have Hδ : |deriv Δ ρ| ≤ C * (U + r * W) / r ^ 2 := hΔder.trans (by
      apply (le_div_iff₀ (sq_pos_of_pos hr.1)).mpr
      have H := mul_le_mul_of_nonneg_left hsmall hC.le
      nlinarith only [H])
    have Hf := hfder
    rw [deriv_fun_sub hf hkd] at Hf
    rw [Hg.deriv]
    have Htotal := (abs_add_le (deriv f ρ - deriv k ρ) (deriv Δ ρ)).trans (add_le_add Hf Hδ)
    have Hextra : 0 ≤ 16 * K * (U + r * W) / r ^ 2 := by positivity
    calc
      _ = |(deriv f ρ - deriv k ρ) + deriv Δ ρ| := by congr 1; ring
      _ ≤ 4 * (4096 * coreVariationBound) * K ^ 2 * (U + r * W) / r ^ 2 + C * (U + r * W) / r ^ 2 := Htotal
      _ ≤ 16 * K * (U + r * W) / r ^ 2 +
          (4 * (4096 * coreVariationBound) * K ^ 2 * (U + r * W) / r ^ 2 + C * (U + r * W) / r ^ 2) := le_add_of_nonneg_left Hextra
      _ = _ := by dsimp only [E]; ring
  have Hrec := connection_reciprocal_radial_bounds ⟨hr.1, hr1⟩ hK hE hU hW
    Hg.differentiableAt hkd hk hklo hglo hdk hvalue hder
  exact ⟨T, hT, hfirst, τ, hτ, hcτ, hfirstnear, hvalid, horbit, hr1, hk, hklo, hkhi,
    hU, hW, hkd, hf, hdk, hfval, hfder, HΔ.1, hΔval, hΔder, Hg.differentiableAt, hglo, Hrec⟩

end BianchiIX
