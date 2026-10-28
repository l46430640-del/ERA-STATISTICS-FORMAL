import BianchiIX.Dynamics.CoreConnectionBounds
import BianchiIX.Dynamics.ConnectionReturnContraction

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- A complete core and connection, followed by the verified wall exchange, is one actual orbit segment. -/
theorem coreReflection_actual_step {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hk : 6 ≤ Y 0) (hu : 0 < Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 < Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0)
    (hfirst : IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2 = 1} (τ Y)) :
    let p := coreConnectionParameters τ Y
    let Z := coreReflectionState τ Y
    connectionReturnValid p ∧ 0 < connectionReturnTime p ∧
      coreRadiusEntry Z = projectiveReflection (projectiveOriginalFlow (coreRadiusEntry Y) 0
        (connectionReturnTime p + τ Y)) ∧
      |Z 0 - (Y 0 - 2)| ≤ 64 * (Y 1 + Y 2 ^ 2) / Y 0 ∧
      (0 < Z 1 ∧ Z 1 ≤ Y 1) ∧ (0 < Z 2 ∧ Z 2 ≤ Y 2) ∧
      (1 ≤ Y 0 - Z 0 ∧ Y 0 - Z 0 ≤ 3) := by
  intro p Z
  have hk0 : 0 < Y 0 := by linarith only [hk]
  obtain ⟨hy, hμ, hpU, hpW, hphase, hA⟩ := coreReturn_connection_data hk hu hw hfirst
  have hdom := coreReturn_connection_domain (ε := 1 / 10000) hk (by norm_num) hu hw hfirst
  have hμ0 : 0 < p 0 := by linarith only [hμ.1]
  have hU : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0 := hdom.2.1
  have hW : 0 < p 2 ∧ p 2 ≤ 1 / 10000 := hdom.2.2
  have Hvalid := (connectionReturn_regular hμ.1 ⟨hU.1.le, hU.2⟩ hW).1
  have Hcontrol := connectionReturn_control hμ.1 ⟨hU.1.le, hU.2⟩ hW
  have Hpos := connectionReturn_wall_pos hμ.1 ⟨hU.1.le, hU.2⟩ hW
  have Hdec := connectionReturn_exponential_decay hμ.1 hU hW
  have hL : 0 ≤ -Real.log (p 2) := neg_nonneg.mpr (Real.log_nonpos hW.1.le (by linarith only [hW.2]))
  have hstrong : connectionReturnState p 1 ≤ p 1 := Hdec.1.trans
    ((mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr
      (by nlinarith only [hL, hμ0] : -p 0 * (-Real.log (p 2)) / 2 ≤ 0)) hU.1.le).trans_eq (mul_one _))
  have hweak : connectionReturnState p 2 ≤ p 2 := Hdec.2.trans
    ((mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (by linarith only [hL]) hμ0.le)) hW.1.le).trans_eq (mul_one _))
  have hZu : 0 < Z 1 ∧ Z 1 ≤ Y 1 := ⟨Hpos.2 hU.1, hstrong.trans hpU.2⟩
  have hZw : 0 < Z 2 ∧ Z 2 ≤ Y 2 := ⟨Hpos.1, hweak.trans hpW.2⟩
  have hD := (coreRegion_clock_regular hk (coreRadiusEntry_region hk ⟨hu.1.le, hu.2⟩ ⟨hw.1.le, hw.2⟩)).1
  have Hrestart := projectiveOriginalFlow_restart hD hfirst.1.1.le Hcontrol.1.le hA
  have hendpoint : connectionReturnState p = projectiveOriginalFlow (coreRadiusEntry Y) 0
      (connectionReturnTime p + τ Y) := by
    change projectiveOriginalFlow (connectionEntry (p 0) (p 1) (p 2)) 0 (connectionReturnTime p) = _
    rw [← hy]
    exact Hrestart
  have hregion := (Hcontrol.2 (connectionReturnTime p) ⟨Hcontrol.1.le, le_rfl⟩).2
  change connectionRegion (p 0) (connectionReturnState p) at hregion
  have hM : 1 < -connectionReturnState p 0 := by linarith only [hμ.1, (abs_le.mp hregion.1).1]
  have hentry : coreRadiusEntry Z = projectiveReflection (projectiveOriginalFlow (coreRadiusEntry Y) 0
      (connectionReturnTime p + τ Y)) := by
    have H := coreRadiusEntry_reflected_exit hM (connectionReturn_growing_component hμ.1 ⟨hU.1.le, hU.2⟩ hW).1
    exact H.trans (congrArg projectiveReflection hendpoint)
  have hb : p 1 + p 2 ^ 2 ≤ Y 1 + Y 2 ^ 2 := add_le_add hpU.2 (pow_le_pow_left₀ hpW.1.le hpW.2 2)
  have hconn : |Z 0 - phaseNorm (p 0 + 1) 1 + 2| ≤ 24 * (Y 1 + Y 2 ^ 2) / p 0 := by
    exact (connectionReturn_phase_bound hμ.1 ⟨hU.1.le, hU.2⟩ hW).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num)) hμ0.le)
  have Herr := core_connection_phase_error hk0 hμ0 (by linarith only [hμ.2.1])
    (add_nonneg hu.1.le (sq_nonneg (Y 2))) hphase hconn
  have Hdrop := core_connection_phase_decrease hk ⟨hu.1.le, hu.2⟩ ⟨hw.1.le, hw.2⟩ Herr
  exact ⟨Hvalid, Hcontrol.1, hentry, Herr, hZu, hZw, Hdrop⟩

theorem contDiffAt_coreReflectionState {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hk : 6 ≤ Y 0) (hu : 0 < Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 < Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0)
    (hfirst : IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2 = 1} (τ Y))
    (hcore : ContDiffAt ℝ 1 (coreReturnState τ) Y) :
    ContDiffAt ℝ 1 (coreConnectionParameters τ) Y ∧ ContDiffAt ℝ 1 (coreReflectionState τ) Y := by
  let p := coreConnectionParameters τ Y
  obtain ⟨hy, hμ, _⟩ := coreReturn_connection_data hk hu hw hfirst
  have hK : 1 < coreReturnState τ Y 0 := by
    change 1 < coreRadius (projectiveOriginalFlow (coreRadiusEntry Y) 0 (τ Y) 0)
      (projectiveOriginalFlow (coreRadiusEntry Y) 0 (τ Y) 2)
    rw [hy]
    change 1 < coreRadius (-p 0) 1
    have heq : coreRadius (-p 0) 1 = phaseNorm (p 0 + 1) 1 := by
      dsimp [coreRadius, coreEnergy, phaseNorm]
      congr 1
      ring
    rw [heq]
    exact lt_of_lt_of_le (by linarith only [hμ.1]) (phaseNorm_ge (by linarith only [hμ.1]))
  have hp : ContDiffAt ℝ 1 (coreConnectionParameters τ) Y :=
    (contDiffAt_coreExitConnectionParameters 1 hK).comp Y hcore
  have hd := coreReturn_connection_domain (ε := 1 / 10000) hk (by norm_num) hu hw hfirst
  have hconn := contDiffAt_connectionReturnPhysicalState hd.1 ⟨hd.2.1.1.le, hd.2.1.2⟩ hd.2.2
  exact ⟨hp, (hconn.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).comp Y hp⟩

/-- B.10 with an actual smooth reflection map and persistence of the common small-wall domain. -/
theorem exists_large_core_reflection :
    ∃ ε > 0, ε ≤ 1 / 10000 ∧ ∀ (Y : CoreAngleState), 6 ≤ Y 0 →
      (0 < Y 1 ∧ Y 1 ≤ ε / Y 0) → (0 < Y 2 ∧ Y 2 ≤ ε / Y 0) →
      ∃ τ : CoreAngleState → ℝ, 0 < τ Y ∧ ContDiffAt ℝ 1 τ Y ∧
        (∀ᶠ X in 𝓝 Y, IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry X) 0 t 2 = 1} (τ X)) ∧
        ContDiffAt ℝ 1 (coreReflectionState τ) Y ∧
        let p := coreConnectionParameters τ Y
        let Z := coreReflectionState τ Y
        connectionReturnValid p ∧ 0 < connectionReturnTime p ∧
          coreRadiusEntry Z = projectiveReflection (projectiveOriginalFlow (coreRadiusEntry Y) 0
            (connectionReturnTime p + τ Y)) ∧
          |Z 0 - (Y 0 - 2)| ≤ 64 * (Y 1 + Y 2 ^ 2) / Y 0 ∧
          (0 < Z 1 ∧ Z 1 ≤ Y 1) ∧ (0 < Z 2 ∧ Z 2 ≤ Y 2) ∧
          (1 ≤ Y 0 - Z 0 ∧ Y 0 - Z 0 ≤ 3) ∧
          (6 ≤ Z 0 → Z 1 ≤ ε / Z 0 ∧ Z 2 ≤ ε / Z 0) := by
  obtain ⟨ε, hε, hεmax, Hcore⟩ := exists_large_core_invariant_cone
  refine ⟨ε, hε, hεmax, ?_⟩
  intro Y hk hu hw
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hu' : 0 < Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0 :=
    ⟨hu.1, hu.2.trans (div_le_div_of_nonneg_right hεmax hk0.le)⟩
  have hw' : 0 < Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0 :=
    ⟨hw.1, hw.2.trans (div_le_div_of_nonneg_right hεmax hk0.le)⟩
  obtain ⟨τ, hτ, hcτ, hcF, hnear, _⟩ := Hcore Y hk ⟨hu.1.le, hu.2⟩ ⟨hw.1.le, hw.2⟩
  have hfirst := hnear.mono fun _ h => h.1
  have H := coreReflection_actual_step hk hu' hw' hfirst.self_of_nhds
  have hreg := (contDiffAt_coreReflectionState hk hu' hw' hfirst.self_of_nhds hcF).2
  refine ⟨τ, hτ, hcτ, hfirst, hreg, H.1, H.2.1, H.2.2.1, H.2.2.2.1,
    H.2.2.2.2.1, H.2.2.2.2.2.1, H.2.2.2.2.2.2, ?_⟩
  intro hn
  have hnk : coreReflectionState τ Y 0 ≤ Y 0 := by linarith only [H.2.2.2.2.2.2.1]
  have hdiv := div_le_div_of_nonneg_left hε.le (by linarith only [hn] : 0 < coreReflectionState τ Y 0) hnk
  exact ⟨H.2.2.2.2.1.2.trans (hu.2.trans hdiv), H.2.2.2.2.2.1.2.trans (hw.2.trans hdiv)⟩

end BianchiIX
