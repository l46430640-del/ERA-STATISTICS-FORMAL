import BianchiIX.Dynamics.RestartReturnMap
import BianchiIX.Dynamics.RestartPartialCoreConnection

noncomputable section

namespace BianchiIX

open Set

theorem contDiffAt_restartFastProjectiveEntry_joint {h s θ ζ ρ : ℝ}
    (hZ : 0 < restartSectionRadicand h (restartRadialCurve θ ζ ρ))
    (hs : s ∈ normalizedMaxDomain (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0)
    (hA : restartFastProjectionHeight h s θ ζ ρ ≠ 0) :
    ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartFastProjectiveEntry h s p.1.1 p.1.2 p.2)
      ((θ, ζ), ρ) := by
  have hc : ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartRadialCurve p.1.1 p.1.2 p.2) ((θ, ζ), ρ) := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i <;> dsimp [restartRadialCurve] <;> fun_prop
  have hchart := (contDiffAt_restartSectionChart hZ 2).comp ((θ, ζ), ρ) hc
  have hflow := (contDiffAt_normalizedMaxCurve_two hs).comp ((θ, ζ), ρ)
    (g := fun p : NormalizedState × ℝ => normalizedMaxCurve p.1 0 p.2)
    (hchart.prodMk (contDiffAt_const (c := s)))
  exact (contDiffAt_toProjectiveState 2 hA).comp ((θ, ζ), ρ) hflow

theorem contDiffAt_restartFastProjectiveEntry_two {h s θ ζ ρ : ℝ}
    (hZ : 0 < restartSectionRadicand h (restartRadialCurve θ ζ ρ))
    (hs : s ∈ normalizedMaxDomain (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0)
    (hA : restartFastProjectionHeight h s θ ζ ρ ≠ 0) :
    ContDiffAt ℝ 2 (restartFastProjectiveEntry h s θ ζ) ρ :=
  (contDiffAt_restartFastProjectiveEntry_joint hZ hs hA).comp ρ (by fun_prop)

/-- The canonical restart is jointly C2 in the two labels and the ordinary radial coordinate. -/
theorem exists_restartReturn_joint_regular :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) → ∀ ρ ∈ Icc r (2 * r),
            let s := q / 2 * Real.log (1 / r)
            ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartFastProjectiveEntry h s p.1.1 p.1.2 p.2) ((θ, ζ), ρ) ∧
              ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartReturnParameters h s p.1.1 p.1.2 p.2) ((θ, ζ), ρ) ∧
              ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartReturnState h s p.1.1 p.1.2 p.2) ((θ, ζ), ρ) ∧
              ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartReturnPhase h s p.1.1 p.1.2 p.2) ((θ, ζ), ρ) ∧
              ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartReturnTime h s p.1.1 p.1.2 p.2) ((θ, ζ), ρ) := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartPartialCore_entry
  obtain ⟨hC, hhC, HC⟩ := exists_restartPartialCore_connection
  refine ⟨min hE hC, lt_min hhE hhC, ?_⟩
  intro h hh L hL q P hq hP
  obtain ⟨rE, hrE, HRE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL q P hq hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨rC, hrC, HRC⟩ := HC h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ L hL q P hq hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  refine ⟨min rE rC, lt_min hrE hrC, ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  obtain ⟨_, hrad, hdom, hA, hk, _, hR, _, _, _, hV, _, hy⟩ :=
    HRE r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ ⟨hζ.1.le, hζ.2⟩ ρ hρ
  obtain ⟨T, _, hfirst, _, _, hμ, hu, hw, _, _, hphase, _, hct, _⟩ :=
    HRC r ⟨hr.1, hr.2.trans (min_le_right _ _)⟩ θ ζ hθ hζ ρ hρ
  let s := q / 2 * Real.log (1 / r)
  let base : (ℝ × ℝ) × ℝ := ((θ, ζ), ρ)
  let Y := fun p : (ℝ × ℝ) × ℝ => restartFastProjectiveEntry h s p.1.1 p.1.2 p.2
  have hcY : ContDiffAt ℝ 2 Y base := contDiffAt_restartFastProjectiveEntry_joint hrad hdom hA.ne'
  have Hcore := partialCoreReturn_regular ((le_max_left _ _).trans hk) hy hR
    (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hV)
  have ht : partialCoreReturnTime (Y base) = T := Hcore.1.unique hfirst
  have hZeq : partialCoreReturnState (Y base) = toCoreAngleState (projectiveOriginalFlow (Y base) 0 T) := by
    simp only [partialCoreReturnState, ht]
  have hp : restartReturnParameters h s θ ζ ρ =
      coreExitConnectionParameters (toCoreAngleState (projectiveOriginalFlow (Y base) 0 T)) :=
    congrArg coreExitConnectionParameters hZeq
  have hZlo : 1 < partialCoreReturnState (Y base) 0 := by
    have H := phaseNorm_ge (b := 1) (show 0 ≤ coreExitConnectionParameters
      (toCoreAngleState (projectiveOriginalFlow (Y base) 0 T)) 0 + 1 by linarith only [hμ.1])
    rw [hphase] at H
    rw [hZeq]
    change 1 < coreRadius (projectiveOriginalFlow (Y base) 0 T 0) (projectiveOriginalFlow (Y base) 0 T 2)
    linarith only [hμ.1, H]
  have hcZ := Hcore.2.2.1.comp base hcY
  have hcp : ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartReturnParameters h s p.1.1 p.1.2 p.2) base :=
    (contDiffAt_coreExitConnectionParameters 2 hZlo).comp base hcZ
  have hcG : ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartReturnState h s p.1.1 p.1.2 p.2) base := by
    apply ContDiffAt.comp (g := connectionReturnPhysicalState) base _ hcp
    change ContDiffAt ℝ 2 connectionReturnPhysicalState (restartReturnParameters h s θ ζ ρ)
    rw [hp]
    exact contDiffAt_connectionReturnPhysicalState hμ.1 ⟨hu.1.le, hu.2⟩ hw
  have hg0 : restartReturnState h s θ ζ ρ 0 ≠ 0 := by
    change phaseNorm (-connectionReturnState (restartReturnParameters h s θ ζ ρ) 0 - 1) 1 ≠ 0
    exact ne_of_gt (by unfold phaseNorm; positivity)
  have hcphase : ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartReturnPhase h s p.1.1 p.1.2 p.2) base :=
    contDiffAt_const.div (contDiffAt_pi.mp hcG 0) hg0
  have hctime : ContDiffAt ℝ 2 (fun p : (ℝ × ℝ) × ℝ => restartReturnTime h s p.1.1 p.1.2 p.2) base := by
    apply (contDiffAt_const.add (Hcore.2.1.comp base hcY)).add
    apply ContDiffAt.comp (g := connectionReturnTime) base _ hcp
    change ContDiffAt ℝ 2 connectionReturnTime (restartReturnParameters h s θ ζ ρ)
    rw [hp]
    exact hct
  exact ⟨hcY, hcp, hcG, hcphase, hctime⟩

/-- Restriction of the joint ordinary regularity to any fixed radial curve. -/
theorem exists_restartReturn_regular :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) → ∀ ρ ∈ Icc r (2 * r),
            let s := q / 2 * Real.log (1 / r)
            ContDiffAt ℝ 2 (restartFastProjectiveEntry h s θ ζ) ρ ∧
              ContDiffAt ℝ 2 (restartReturnParameters h s θ ζ) ρ ∧
              ContDiffAt ℝ 2 (restartReturnState h s θ ζ) ρ ∧
              ContDiffAt ℝ 2 (restartReturnPhase h s θ ζ) ρ ∧
              ContDiffAt ℝ 2 (restartReturnTime h s θ ζ) ρ := by
  obtain ⟨hstar, hhstar, HH⟩ := exists_restartReturn_joint_regular
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh L hL q P hq hP
  obtain ⟨rstar, hrstar, HR⟩ := HH h hh L hL q P hq hP
  refine ⟨rstar, hrstar, ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  obtain ⟨hY, hp, hG, hf, ht⟩ := HR r hr θ ζ hθ hζ ρ hρ
  have hc : ContDiffAt ℝ 2 (fun a : ℝ => ((θ, ζ), a)) ρ := by fun_prop
  exact ⟨hY.comp ρ hc, hp.comp ρ hc, hG.comp ρ hc, hf.comp ρ hc, ht.comp ρ hc⟩

end BianchiIX
