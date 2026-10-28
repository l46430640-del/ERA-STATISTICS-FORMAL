import BianchiIX.Dynamics.MainWallReflection
import BianchiIX.Dynamics.RestartReturnControl

noncomputable section

namespace BianchiIX

open Set

theorem mainWallChart_restartRadial {h θ ζ ρ : ℝ} (hρ : 0 < ρ) (hζ : 0 < ζ) :
    mainWallChart h ![θ * ρ, -Real.log ρ, -Real.log ζ] =
      restartSectionChart h (restartRadialCurve θ ζ ρ) := by
  simp [mainWallChart, mainWallRadicand, restartSectionChart, restartSectionRadicand,
    restartRadialCurve, Real.exp_log hρ, Real.exp_log hζ]

/-- Both weak-wall orderings reach the same canonical core, with the frame change stated at the actual Einstein return time. -/
theorem exists_restartReturn_reflected_orbit :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ L : ℝ, 0 ≤ L →
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ a ^ P) → ∀ ρ ∈ Icc a (2 * a),
          let s := q / 2 * Real.log (1 / a)
          let y : SectionCoordinates := ![θ * ρ, -Real.log ρ, -Real.log ζ]
          let T := restartReturnTime h s θ ζ ρ
          let G := restartReturnState h s θ ζ ρ
          y ∈ mainWallChartDomain h ∧ 0 < T ∧ T ∈ normalizedMaxDomain (mainWallChart h y) 0 ∧
            coreRadiusEntry G = projectiveReflection (toProjectiveState (normalizedMaxCurve (mainWallChart h y) 0 T)) ∧
            coreRadiusEntry G = toProjectiveState (normalizedMaxCurve (mainWallChart h (mainWallReflection y)) 0 T) := by
  obtain ⟨hC, hhC, HC⟩ := exists_restartReturn_control
  obtain ⟨C, hC32, HV⟩ := exists_restartFastEntry_control
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC32
  refine ⟨min hC (1 / (4 * C)), lt_min hhC (by positivity), ?_⟩
  intro h hh L hL q P hq hP
  obtain ⟨K, _, HK⟩ := HC h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL
  obtain ⟨aC, haC, HaC⟩ := HK q P hq hP
  obtain ⟨aV, haV, HaV⟩ := HV h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ L hL q (by linarith)
  refine ⟨min aC (min aV 1), lt_min haC (lt_min haV zero_lt_one), ?_⟩
  intro a ha θ ζ hθ hζ ρ hρ s y T G
  have ha1 : a ≤ 1 := ha.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hζ2 : 0 ≤ ζ ∧ ζ ≤ a ^ 2 := ⟨hζ.1.le, hζ.2.trans (by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge ha.1 ha1 (by linarith : (2 : ℝ) ≤ P))⟩
  obtain ⟨_, _, hs, hrad, _⟩ := HaV a
    ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ θ ζ hθ hζ2 ρ hρ
  obtain ⟨hfirst, _, hvalid, _, _, _, _, _, horbit, _⟩ :=
    HaC a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  have heq : mainWallChart h y = restartSectionChart h (restartRadialCurve θ ζ ρ) :=
    mainWallChart_restartRadial (ha.1.trans_le hρ.1) hζ.1
  have hy : y ∈ mainWallChartDomain h := by
    change 0 < mainWallRadicand h y
    change 0 < 1 - (θ * ρ) ^ 2 - curvature h ρ ζ at hrad
    simpa [y, mainWallRadicand, Real.exp_log (ha.1.trans_le hρ.1), Real.exp_log hζ.1] using hrad
  have ht : 0 < T := add_pos (add_pos_of_nonneg_of_pos hs hfirst.1.1) hvalid.1.1.1
  have hdom : T ∈ normalizedMaxDomain (mainWallChart h y) 0 :=
    normalizedMaxDomain_contains_Ici_of_constraint (mainWallChart_constraint hy) 0 ht.le
  have ho : coreRadiusEntry G = projectiveReflection (toProjectiveState (normalizedMaxCurve (mainWallChart h y) 0 T)) := by
    simpa only [heq] using horbit
  refine ⟨hy, ht, hdom, ho, ?_⟩
  rw [normalizedMaxCurve_mainWallReflection hdom, toProjectiveState_axisSwap]
  exact ho

end BianchiIX
