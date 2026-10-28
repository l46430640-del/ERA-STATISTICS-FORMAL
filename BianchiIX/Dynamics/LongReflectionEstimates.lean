import BianchiIX.Dynamics.ReflectionParameters
import BianchiIX.Dynamics.ConnectionPhaseAmplitude
import BianchiIX.Dynamics.ConnectionReturnCone
import BianchiIX.Dynamics.ConnectionRestartBounds

noncomputable section

namespace BianchiIX

open Set

/-- Long reflection estimates in the physical radius, for the canonical first arrival. -/
theorem exists_long_reflection_estimates :
    ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∀ Y : CoreAngleState,
      11 / 2 ≤ Y 0 → (0 < Y 1 ∧ Y 1 ≤ ε / Y 0) → (0 < Y 2 ∧ Y 2 ≤ ε / Y 0) →
      IsLeast {t : ℝ | 0 < t ∧ projectiveOriginalFlow (coreTailEntry Y) 0 t 3 = 1}
        (reflectionReturnTime Y) ∧
      coreRadiusEntry (reflectionReturnState Y) =
        projectiveReflection (projectiveOriginalFlow (coreTailEntry Y) 0 (reflectionReturnTime Y)) ∧
      ContDiffAt ℝ 2 reflectionReturnTime Y ∧ ContDiffAt ℝ 2 reflectionReturnState Y ∧
      |reflectionReturnState Y 0 - (Y 0 - 2)| ≤ 300000 * (Y 1 + Y 2) / Y 0 ∧
      (∀ i : Fin 2, 0 < reflectionReturnState Y i.succ ∧ reflectionReturnState Y i.succ ≤ Y i.succ) ∧
      ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
        let d := fderiv ℝ reflectionReturnState Y v
        1 / 2 ≤ d 0 ∧ |d 0 - 1| ≤ 300000 * Real.sqrt (Y 1 + Y 2) / Y 0 ∧
          ∀ i : Fin 2, |d i.succ| ≤ Real.sqrt (reflectionReturnState Y i.succ) * d 0 := by
  obtain ⟨ε, hε, hεmax, hsε, hεL⟩ := exists_connection_cone_threshold
  refine ⟨ε, hε, hεmax, ?_⟩
  intro Y hR hu hw
  let p := coreExitConnectionParameters Y
  obtain ⟨hμ, hRμ, hμR⟩ := coreExitConnectionParameters_long_range hR
  have hR0 : 0 < Y 0 := by linarith only [hR]
  have hR1 : 1 < Y 0 := by linarith only [hR]
  have hμ0 : 0 < p 0 := by linarith only [hμ]
  have hup : 0 < p 1 ∧ p 1 ≤ ε / p 0 :=
    ⟨hu.1, hu.2.trans (div_le_div_of_nonneg_left hε.le hμ0 hμR.le)⟩
  have hwp : 0 < p 2 ∧ p 2 ≤ ε :=
    ⟨hw.1, hw.2.trans (div_le_self hε.le (by linarith only [hR]))⟩
  have hu' : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0 :=
    ⟨hup.1, hup.2.trans (div_le_div_of_nonneg_right hεmax hμ0.le)⟩
  have hw' : 0 < p 2 ∧ p 2 ≤ 1 / 10000 := ⟨hwp.1, hwp.2.trans hεmax⟩
  have HR := connectionReturn_regular hμ ⟨hu'.1.le, hu'.2⟩ hw'
  have hP := contDiffAt_coreExitConnectionParameters 2 hR1
  have hphys := contDiffAt_connectionReturnPhysicalState hμ ⟨hu'.1.le, hu'.2⟩ hw'
  have hx : connectionInitialState p = fromProjectiveState (coreTailEntry Y) := by
    dsimp only [connectionInitialState, p]
    rw [connectionEntry_coreExitParameters]
  have hden := connection_entry_denom_pos hμ ⟨hu'.1.le, hu'.2⟩ hw'
  have hdom (t : ℝ) (ht : 0 ≤ t) : t ∈ normalizedMaxDomain (connectionInitialState p) 0 :=
    normalizedMaxDomain_contains_Ici_of_constraint (fromProjectiveState_constraint hden.ne') 0 ht
  have hfirst : IsLeast {t : ℝ | 0 < t ∧ projectiveOriginalFlow (coreTailEntry Y) 0 t 3 = 1}
      (reflectionReturnTime Y) := by
    refine ⟨⟨HR.1.1.1.1, ?_⟩, ?_⟩
    · have H := HR.1.1.1.2.2
      change connectionReturnState p 3 = 1 at H
      rwa [connectionReturnState_coreExitParameters] at H
    · intro t ht
      apply HR.1.1.2
      refine ⟨ht.1, hdom t ht.1.le, ?_⟩
      rw [hx]
      exact ht.2
  obtain ⟨_, _, _, _, _, hactual⟩ := connectionReturn_restart_bounds hμ hu' hw'
  rw [connectionReturnState_coreExitParameters] at hactual
  have hpos := connectionReturn_wall_pos hμ ⟨hu'.1.le, hu'.2⟩ hw'
  have hdec := connectionReturn_exponential_decay hμ hu' hw'
  have hw1 : p 2 ≤ 1 := hw'.2.trans (by norm_num)
  have hL : 0 ≤ -Real.log (p 2) := neg_nonneg.mpr (Real.log_nonpos hw'.1.le hw1)
  have hU : connectionReturnState p 1 ≤ p 1 := hdec.1.trans (mul_le_of_le_one_right hu'.1.le
    (Real.exp_le_one_iff.mpr (by nlinarith only [mul_nonneg hμ0.le hL])))
  have hW : connectionReturnState p 2 ≤ p 2 := hdec.2.trans (mul_le_of_le_one_right hw'.1.le
    (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith only [hL]) hμ0.le)))
  have hb : 0 ≤ Y 1 + Y 2 := add_nonneg hu.1.le hw.1.le
  have hphase : |reflectionReturnState Y 0 - (Y 0 - 2)| ≤ 24 * (p 1 + p 2 ^ 2) / p 0 := by
    have H := connectionReturn_phase_bound hμ ⟨hu'.1.le, hu'.2⟩ hw'
    have heq : connectionReturnPhaseError p = reflectionReturnState Y 0 - (Y 0 - 2) := by
      dsimp only [connectionReturnPhaseError, reflectionReturnState, connectionReturnPhysicalState,
        Matrix.cons_val_zero]
      rw [coreExitConnectionParameters_phase hR1]
      ring
    rwa [heq] at H
  refine ⟨hfirst, hactual, HR.2.1.comp Y hP, hphys.comp Y hP, ?_, ?_, ?_⟩
  · apply hphase.trans
    have hw2 : p 2 ^ 2 ≤ p 2 := by nlinarith only [hw'.1.le, hw1]
    calc
      _ ≤ 24 * (Y 1 + Y 2) / p 0 := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl hw2) (by norm_num)) hμ0.le
      _ ≤ 24 * (Y 1 + Y 2) / (Y 0 / 2) :=
        div_le_div_of_nonneg_left (by positivity) (half_pos hR0) hRμ
      _ = 48 * (Y 1 + Y 2) / Y 0 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hb) hR0.le
  · intro i
    fin_cases i
    · exact ⟨hpos.2 hu'.1, hU⟩
    · exact ⟨hpos.1, hW⟩
  · intro v hv0 hv1 hv2 d
    let w := fderiv ℝ coreExitConnectionParameters Y v
    obtain ⟨hw0, hwv1, hwv2⟩ := coreExitConnectionParameters_unit_phase hR1 hv0
    have hw1' : |w 1| ≤ Real.sqrt (p 1) := by dsimp only [w]; rw [hwv1]; exact hv1
    have hw2' : |w 2| ≤ Real.sqrt (p 2) := by dsimp only [w]; rw [hwv2]; exact hv2
    have hd : d = fderiv ℝ connectionReturnPhysicalState p w := by
      change fderiv ℝ (connectionReturnPhysicalState ∘ coreExitConnectionParameters) Y v = _
      rw [fderiv_comp Y (hphys.differentiableAt (by norm_num)) (hP.differentiableAt (by norm_num)),
        ContinuousLinearMap.comp_apply]
    obtain ⟨hmargin, _, hcone1, hcone2⟩ :=
      connectionReturn_unit_cone hμ ⟨hε, hεmax⟩ hsε hεL hup hwp hw0 hw1' hw2'
    have hdf := (connectionReturnPhysicalState_differential hμ hu' hw' w).1
    rw [hw0] at hdf
    have herr : |d 0 - 1| ≤ 150000 * Real.sqrt (Y 1 + Y 2) / p 0 := by
      rw [hd, hdf, add_sub_cancel_left]
      exact connectionReturn_phase_cone_amplitude hμ hu' hw' hw0 hw1' hw2'
    refine ⟨by rw [hd]; linarith only [hmargin], herr.trans ?_, ?_⟩
    · calc
        _ ≤ 150000 * Real.sqrt (Y 1 + Y 2) / (Y 0 / 2) :=
          div_le_div_of_nonneg_left (by positivity) (half_pos hR0) hRμ
        _ = _ := by ring
    · intro i
      rw [hd]
      have hd0 : 0 ≤ fderiv ℝ connectionReturnPhysicalState p w 0 := by linarith only [hmargin]
      have hweak : 1 - (1 - Real.exp (-(-Real.log (p 2)) / (2 * p 0))) / 2 ≤ 1 := by
        have Hexp := Real.exp_le_one_iff.mpr
          (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hL) (by positivity : 0 ≤ 2 * p 0))
        linarith only [Hexp]
      fin_cases i
      · change |fderiv ℝ connectionReturnPhysicalState p w 1| ≤
          Real.sqrt (connectionReturnState p 1) * fderiv ℝ connectionReturnPhysicalState p w 0
        exact hcone1.trans (by
          simpa only [one_mul] using! mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) / 3 ≤ 1)
              (Real.sqrt_nonneg (connectionReturnState p 1))) hd0)
      · change |fderiv ℝ connectionReturnPhysicalState p w 2| ≤
          Real.sqrt (connectionReturnState p 2) * fderiv ℝ connectionReturnPhysicalState p w 0
        exact hcone2.trans (by
          simpa only [one_mul] using! mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hweak (Real.sqrt_nonneg (connectionReturnState p 2))) hd0)

end BianchiIX
