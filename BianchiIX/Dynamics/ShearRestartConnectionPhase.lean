import BianchiIX.Dynamics.PartialCoreDownwardConnectionPhase
import BianchiIX.Dynamics.ShearRestartPartialCoreRadialData
import BianchiIX.Dynamics.ShearRestartPartialCoreResponse

noncomputable section

namespace BianchiIX

open Set

/-- Amplitude-sensitive E.28 on the actual shear family, with the canonical downward event on the original orbit. -/
theorem exists_restartShearConnection_phase_error :
    ∃ hstar > (0 : ℝ), ∃ K ≥ (1 : ℝ), ∃ C > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let Y := restartFastShearProjectiveEntry h s 1 n₂ n₃
            let k := restartFastShearCoreRadius h s 1 n₂ n₃
            let U := Y ρ 1
            let W := Y ρ 2 * Y ρ 3
            let T := partialCoreDownwardReturnTime (Y ρ)
            let out := fun b => projectiveOriginalFlow (Y b) 0 (partialCoreDownwardReturnTime (Y b))
            let f := fun b => coreRadius (out b 0) (out b 2)
            let p := fun b => coreExitConnectionParameters ![f b, out b 1, out b 3]
            let Δ := fun b => connectionReturnPhaseError (p b)
            let g := fun b => connectionReturnPhysicalState (p b) 0
            let E := 16 * K + 4 * (4096 * coreVariationBound) * K ^ 2 + C
            let R := fun b => 2 / g b - (2 / k b) / (1 - 2 / k b)
            1 ≤ Y ρ 2 →
            0 < T ∧ IsLeast {t | s < t ∧ toProjectiveState
              (normalizedMaxCurve (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0 t) 2 = 1} (s + T) ∧
            connectionReturnValid (p ρ) ∧ connectionReturnState (p ρ) = toProjectiveState
              (normalizedMaxCurve (restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)) 0
                (s + T + connectionReturnTime (p ρ))) ∧
            a ≤ 1 ∧ 6 ≤ k ρ ∧ 2 / (K * a) ≤ k ρ ∧ k ρ ≤ K / a ∧
            0 < U ∧ (0 < W ∧ W ≤ 1) ∧ U + W ≤ K * a ∧
            DifferentiableAt ℝ k ρ ∧ DifferentiableAt ℝ f ρ ∧
            |f ρ - k ρ| ≤ 16 * K * (U + a * W ^ 2) ∧
            |deriv (fun b => f b - k b) ρ| ≤ 4 * (4096 * coreVariationBound) * K ^ 2 * (U + a * W) / a ^ 2 ∧
            DifferentiableAt ℝ Δ ρ ∧ |Δ ρ| ≤ C * a * (U + W ^ 2) ∧ |deriv Δ ρ| ≤ C * (U + W ^ 2) ∧
            DifferentiableAt ℝ g ρ ∧ k ρ / 4 ≤ g ρ ∧
            DifferentiableAt ℝ R ρ ∧ |R ρ| ≤ 8 * E * K ^ 2 * a ^ 2 * (U + a * W ^ 2) ∧
            |deriv R ρ| ≤ (8 * E * K ^ 2 + 32 * E * K ^ 4) * (U + a * W) := by
  obtain ⟨hstar, hhstar, K, hK, Hdata⟩ := exists_restartShearPartialCore_radial_data
  obtain ⟨C, hC, Hphase⟩ := exists_partialCoreDownwardConnection_phase_error hK
  have hK0 : 0 < K := by linarith only [hK]
  refine ⟨hstar, hhstar, K, hK, C, hC, ?_⟩
  intro h hh q P hq hP
  obtain ⟨astar, hastar, Ha⟩ := Hdata h hh q P hq hP
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s Y k U W T out f p Δ g E R hv
  obtain ⟨ha1, hs, hrad, hdom, hA, hY, hk, hy, hvcase, hz, hsum,
    hklo, hkhi, hdk, _, hdU, hdW, hdz⟩ :=
    Ha a ha ε n₂ n₃ hε h₂ ⟨h₃.1.le, h₃.2⟩ h₃P ρ hρ hv
  let x := restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)
  have hc : stateConstraint x = 1 := restartSectionChart_constraint hrad.le
  have hpos (i : Fin 3) (hi : 0 < wallValue i x) :
      0 < wallValue i (normalizedMaxCurve x 0 s) := by
    have H := normalizedMaxCurve_wall_sign hc hs i
    have Hnn := H.2.mpr hi.le
    have Hne : wallValue i (normalizedMaxCurve x 0 s) ≠ 0 := fun hz => hi.ne' (H.1.mp hz)
    exact lt_of_le_of_ne Hnn (Ne.symm Hne)
  have hU : 0 < U := div_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) (hpos 0 hh.1)) hA
  have hw : 0 < Y ρ 3 := div_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) (hpos 2 h₃.1)) hA
  have hW : 0 < W := mul_pos (zero_lt_one.trans_le hv) hw
  have hW1 : W ≤ 1 := (coreBootstrap_wall_bound hk hy.2.2.2.2).trans (by norm_num)
  have hk0 : 0 < k ρ := by linarith only [hk]
  have hki : 1 / k ρ ≤ K * a := by
    apply (div_le_iff₀ hk0).mpr
    nlinarith only [(div_le_iff₀ (mul_pos hK0 ha.1)).mp hklo]
  have hkZ : 2 * Real.cosh 0 ≤ k ρ := by rw [Real.cosh_zero]; linarith only [hk]
  obtain ⟨hvalid, Hconn, Hrest⟩ := Hphase ⟨ha.1, ha1⟩ (le_refl (0 : ℝ)) hY
    hk hy hvcase hkZ hz hU hW hklo hkhi hdk hdU hdW hdz
  have hfirst := (partialCoreDownwardReturn_regular hk hy rfl hvcase).1
  have hT : 0 < T := hfirst.1.1
  have htc : 0 < connectionReturnTime (p ρ) := hvalid.1.1.1
  have Hflow (t : ℝ) (ht : 0 ≤ t) := restartFastShearProjectiveEntry_flow hrad.le hs hA ht
  have Hfast := Hflow (T + connectionReturnTime (p ρ)) (add_nonneg hT.le htc.le)
  refine ⟨hT, ?_, hvalid, ?_, ha1, hk, hklo, hkhi, hU, ⟨hW, hW1⟩, hsum.trans hki, Hrest⟩
  · refine ⟨⟨by linarith only [hT], ?_⟩, ?_⟩
    · rw [← Hflow T hT.le]
      exact hfirst.1.2
    · intro t ht
      have hsub : 0 < t - s := sub_pos.mpr ht.1
      have HF := Hflow (t - s) hsub.le
      rw [add_sub_cancel] at HF
      have Hleast := hfirst.2 ⟨hsub, by rw [HF]; exact ht.2⟩
      linarith only [Hleast]
  · exact (Hconn.trans Hfast).trans (by rw [add_assoc])

end BianchiIX
