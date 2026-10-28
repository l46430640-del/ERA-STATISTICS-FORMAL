import BianchiIX.Dynamics.CompactReflectionRegularity
import BianchiIX.Dynamics.CompactConnectionCone

noncomputable section

namespace BianchiIX

open Set

theorem compactConnectionPhysicalState_differential {η : ℝ} {Y : CoreAngleState}
    (hs : DifferentiableAt ℝ (compactConnectionState η) Y)
    (hf : DifferentiableAt ℝ (compactConnectionPhysicalState η) Y) (v : CoreAngleState) :
    fderiv ℝ (compactConnectionPhysicalState η) Y v =
      ![fderiv ℝ (compactConnectionPhase η) Y v,
        fderiv ℝ (compactConnectionState η) Y v 1, fderiv ℝ (compactConnectionState η) Y v 3] := by
  ext i
  fin_cases i
  · exact (congrArg (fun L : CoreAngleState →L[ℝ] ℝ => L v) (fderiv_apply hf 0)).symm
  · have heq : (fun Z => compactConnectionPhysicalState η Z 1) =
        (fun Z => compactConnectionState η Z 1) := rfl
    have H := congrArg (fun f : CoreAngleState → ℝ => fderiv ℝ f Y) heq
    rw [fderiv_apply hf 1, fderiv_apply hs 1] at H
    exact congrArg (fun L : CoreAngleState →L[ℝ] ℝ => L v) H
  · have heq : (fun Z => compactConnectionPhysicalState η Z 2) =
        (fun Z => compactConnectionState η Z 3) := rfl
    have H := congrArg (fun f : CoreAngleState → ℝ => fderiv ℝ f Y) heq
    rw [fderiv_apply hf 2, fderiv_apply hs 3] at H
    exact congrArg (fun L : CoreAngleState →L[ℝ] ℝ => L v) H

/-- Compact reflection bounds belong to the canonical next-wall return, without an auxiliary tail-height parameter. -/
theorem exists_compact_reflection_estimates :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → (0 < Y 1 ∧ Y 1 ≤ ε) → (0 < Y 2 ∧ Y 2 ≤ ε) →
      IsLeast {t : ℝ | 0 < t ∧ projectiveOriginalFlow (coreTailEntry Y) 0 t 3 = 1}
        (reflectionReturnTime Y) ∧
      coreRadiusEntry (reflectionReturnState Y) =
        projectiveReflection (projectiveOriginalFlow (coreTailEntry Y) 0 (reflectionReturnTime Y)) ∧
      ContDiffAt ℝ 2 reflectionReturnTime Y ∧ ContDiffAt ℝ 2 reflectionReturnState Y ∧
      |reflectionReturnState Y 0 - (Y 0 - 2)| ≤ C * (Y 1 + Y 2) / Y 0 ∧
      (∀ i : Fin 2, 0 < reflectionReturnState Y i.succ ∧ reflectionReturnState Y i.succ ≤ Y i.succ) ∧
      ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
        let d := fderiv ℝ reflectionReturnState Y v
        1 / 2 ≤ d 0 ∧ |d 0 - 1| ≤ C * Real.sqrt (Y 1 + Y 2) / Y 0 ∧
          ∀ i : Fin 2, |d i.succ| ≤ Real.sqrt (reflectionReturnState Y i.succ) * d 0 := by
  obtain ⟨δp, hδp, hδsmall, Hp⟩ := exists_compact_connection_phase_bounds
  obtain ⟨δc, hδc, _, Hc⟩ := exists_compact_connection_cone
  let η := min δp δc
  have hη : 0 < η ∧ η ≤ 1 / 10000 := ⟨lt_min hδp hδc, (min_le_left _ _).trans hδsmall⟩
  obtain ⟨εp, hεp, P, hP, HP⟩ := Hp η ⟨hη.1, min_le_left _ _⟩
  obtain ⟨εc, hεc, Q, hQ, HC⟩ := Hc η ⟨hη.1, min_le_right _ _⟩
  obtain ⟨εr, hεr, _, _, HR⟩ := exists_compact_connection_return hη
  obtain ⟨εg, hεg, HG⟩ := exists_compact_reflection_regular hη
  let ε := min εr (min εg (min εp (min εc (1 / 2))))
  have hε : 0 < ε := lt_min hεr (lt_min hεg (lt_min hεp (lt_min hεc (by norm_num))))
  have hεr' : ε ≤ εr := min_le_left _ _
  have hεg' : ε ≤ εg := (min_le_right _ _).trans (min_le_left _ _)
  have hεp' : ε ≤ εp := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεc' : ε ≤ εc := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hεhalf : ε ≤ 1 / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  let C := max (6 * (P + 1)) (12 * Q)
  have hPC : 6 * (P + 1) ≤ C := le_max_left _ _
  have hQC : 12 * Q ≤ C := le_max_right _ _
  refine ⟨ε, hε, C, lt_of_lt_of_le (by positivity : 0 < 6 * (P + 1)) hPC, ?_⟩
  intro Y hk hu hw
  obtain ⟨heqT, heqF, ht, hF⟩ := HG Y hk
    ⟨hu.1, hu.2.trans hεg'⟩ ⟨hw.1, hw.2.trans hεg'⟩
  obtain ⟨_, _, _, hs, hactual, hfirst, hm, _, hU, hW⟩ := HR Y hk
    ⟨hu.1, hu.2.trans hεr'⟩ ⟨hw.1, hw.2.trans hεr'⟩
  obtain ⟨_, _, _, hval, _⟩ := HP Y hk
    ⟨hu.1, hu.2.trans hεp'⟩ ⟨hw.1, hw.2.trans hεp'⟩
  obtain ⟨_, _, _, _, _, _, hfactor, hcone⟩ := HC Y hk
    ⟨hu.1, hu.2.trans hεc'⟩ ⟨hw.1, hw.2.trans hεc'⟩
  have hk0 : 0 < Y 0 := by linarith only [hk.1]
  have hb : 0 ≤ Y 1 + Y 2 := add_nonneg hu.1.le hw.1.le
  have hb1 : Y 1 + Y 2 ≤ 1 := by linarith only [hu.2.trans hεhalf, hw.2.trans hεhalf]
  have hval' : |compactConnectionPhase η Y - (Y 0 - 2)| ≤ (P + 1) * (Y 1 + Y 2) := by
    have hsmall : 2 * Y 1 / Y 0 ≤ Y 1 := (div_le_iff₀ hk0).mpr (by
      nlinarith only [mul_le_mul_of_nonneg_right hk.1 hu.1.le, hu.1.le])
    have hsplit : compactConnectionPhase η Y - (Y 0 - 2) =
        (compactConnectionPhase η Y - (Y 0 - 2) + 2 * Y 1 / Y 0) - 2 * Y 1 / Y 0 := by ring
    have H := (abs_sub (compactConnectionPhase η Y - (Y 0 - 2) + 2 * Y 1 / Y 0)
      (2 * Y 1 / Y 0)).trans (add_le_add hval le_rfl)
    rw [← hsplit, abs_of_nonneg (div_nonneg (mul_nonneg (by norm_num) hu.1.le) hk0.le)] at H
    have hsq : (Y 1 + Y 2) ^ 2 ≤ Y 1 + Y 2 := by nlinarith only [hb, hb1]
    nlinarith only [H, hsmall, mul_le_mul_of_nonneg_left hsq hP.le, hw.1.le]
  refine ⟨?_, ?_, ht, hF, ?_, ?_, ?_⟩
  · rw [heqT.self_of_nhds]
    exact hfirst
  · apply reflectionReturn_state_reconstruction
    · rw [heqT.self_of_nhds]
      rw [hactual] at hm
      exact hm
    · rw [heqT.self_of_nhds]
      exact hfirst.1.2
  · rw [heqF.self_of_nhds]
    change |compactConnectionPhase η Y - (Y 0 - 2)| ≤ _
    apply hval'.trans
    apply (le_div_iff₀ hk0).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hk.2 (mul_nonneg (by linarith only [hP] : 0 ≤ P + 1) hb),
      mul_le_mul_of_nonneg_right hPC hb]
  · intro i
    rw [heqF.self_of_nhds]
    fin_cases i
    · exact ⟨hU.1, hU.2.2⟩
    · exact ⟨hW.1, hW.2.2⟩
  · intro v hv0 hv1 hv2 d
    obtain ⟨hr, herr, hc1, hc2⟩ := hcone v hv0 hv1 hv2
    have hd := compactConnectionPhysicalState_differential (hs.differentiableAt (by norm_num))
      ((hF.congr_of_eventuallyEq heqF.symm).differentiableAt (by norm_num)) v
    have heqd : d = ![fderiv ℝ (compactConnectionPhase η) Y v,
        fderiv ℝ (compactConnectionState η) Y v 1, fderiv ℝ (compactConnectionState η) Y v 3] :=
      (congrArg (fun L : CoreAngleState →L[ℝ] CoreAngleState => L v) heqF.fderiv_eq).trans hd
    rw [heqd]
    refine ⟨hr, herr.trans ?_, ?_⟩
    · have hroot : Real.sqrt (Y 1) + Y 2 * Real.sqrt (Y 2) ≤ 2 * Real.sqrt (Y 1 + Y 2) := by
        have hsu : Real.sqrt (Y 1) ≤ Real.sqrt (Y 1 + Y 2) :=
          Real.sqrt_le_sqrt (le_add_of_nonneg_right hw.1.le)
        have hsw : Real.sqrt (Y 2) ≤ Real.sqrt (Y 1 + Y 2) :=
          Real.sqrt_le_sqrt (le_add_of_nonneg_left hu.1.le)
        have hw1 : Y 2 ≤ 1 := by linarith only [hw.2.trans hεhalf]
        nlinarith only [hsu, hsw, mul_le_mul_of_nonneg_right hw1 (Real.sqrt_nonneg (Y 2))]
      apply (mul_le_mul_of_nonneg_left hroot hQ.le).trans
      apply (le_div_iff₀ hk0).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hk.2 (by positivity : 0 ≤ 2 * Q * Real.sqrt (Y 1 + Y 2)),
        mul_le_mul_of_nonneg_right hQC (Real.sqrt_nonneg (Y 1 + Y 2))]
    · intro i
      rw [heqF.self_of_nhds]
      have hfac : Q * (Y 1 + Y 2) ^ (2 / 9 : ℝ) ≤ 1 := by linarith only [hfactor]
      have hbound := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hfac (Real.sqrt_nonneg (compactConnectionPhysicalState η Y i.succ)))
        (show 0 ≤ fderiv ℝ (compactConnectionPhase η) Y v by linarith only [hr])
      simp only [one_mul] at hbound
      fin_cases i
      · exact hc1.trans hbound
      · exact hc2.trans hbound

end BianchiIX
