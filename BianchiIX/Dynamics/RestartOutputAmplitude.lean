import BianchiIX.Dynamics.RestartPartialCoreConnection
import BianchiIX.Dynamics.ConnectionRestartBounds

noncomputable section

namespace BianchiIX

open Set

/-- E.13 holds at the reflected endpoint of the same original Einstein orbit. -/
theorem exists_restartConnection_output_bounds :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) → ∀ ρ ∈ Icc r (2 * r),
            let s := q / 2 * Real.log (1 / r)
            let y := restartFastProjectiveEntry h s θ ζ ρ
            let x := restartSectionChart h (restartRadialCurve θ ζ ρ)
            let M := 8 * (L + 1)
            let B := M + 1
            ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} T ∧
              let p := coreExitConnectionParameters (toCoreAngleState (projectiveOriginalFlow y 0 T))
              let G := connectionReturnPhysicalState p
              connectionReturnValid p ∧
              1 / (2 * B * r) ≤ G 0 ∧ G 0 ≤ 64 / r ∧
              0 < G 1 ∧ 0 < G 2 ∧ G 1 + G 2 ≤ 4096 * M * ζ / r ^ 3 ∧
              coreRadiusEntry G = projectiveReflection (toProjectiveState
                (normalizedMaxCurve x 0 (s + T + connectionReturnTime p))) := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartPartialCore_connection
  obtain ⟨hV, hhV, HV⟩ := exists_restartFastProjectiveEntry_bounds
  obtain ⟨hR, hhR, HR⟩ := exists_restartFastCoreRadius_bounds
  refine ⟨min hE (min hV hR), lt_min hhE (lt_min hhV hhR), ?_⟩
  intro h hh L hL q P hq hP
  have hq2 : 2 < q := by linarith only [hq]
  obtain ⟨rE, hrE, HRE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL q P hq hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨rV, hrV, HRV⟩ := HV h ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_left _ _)⟩ L hL q hq2
  obtain ⟨rR, hrR, HRR⟩ := HR h ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_right _ _)⟩ L hL q hq2
  refine ⟨min rE (min rV (min rR 1)), lt_min hrE (lt_min hrV (lt_min hrR (by norm_num))), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have hrV' := hr.2.trans (min_le_right _ _)
  have hrR' := hrV'.trans (min_le_right _ _)
  have hr1 := hrR'.trans (min_le_right _ _)
  have hζ2 : 0 ≤ ζ ∧ ζ ≤ r ^ 2 := by
    refine ⟨hζ.1.le, hζ.2.trans ?_⟩
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_ge hr.1 hr1 (by linarith only [hP] : (2 : ℝ) ≤ P)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hprod, _⟩ :=
    HRV r ⟨hr.1, hrV'.trans (min_le_left _ _)⟩ θ ζ hθ hζ2 ρ hρ
  obtain ⟨_, _, _, hklo, hkhi, _⟩ := HRR r ⟨hr.1, hrR'.trans (min_le_left _ _)⟩ θ ζ hθ hζ2 ρ hρ
  obtain ⟨T, hT, hfirst, _, _, hμ, hu, hw, _, hweak, _, hvalid, _, _, horbit⟩ :=
    HRE r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  let s := q / 2 * Real.log (1 / r)
  let y := restartFastProjectiveEntry h s θ ζ ρ
  let p := coreExitConnectionParameters (toCoreAngleState (projectiveOriginalFlow y 0 T))
  let G := connectionReturnPhysicalState p
  let M := 8 * (L + 1)
  let B := M + 1
  obtain ⟨Hlo, Hhi, Hstrong, Hweak, Hsum, Hentry⟩ := connectionReturn_restart_bounds hμ.1 hu hw
  have Hlower : 1 / (2 * B * r) ≤ G 0 := by
    have H := hμ.2.1
    have Heq : 2 / ((8 * (L + 1) + 1) * r) = 4 * (1 / (2 * B * r)) := by dsimp only [B, M]; field_simp; norm_num
    rw [Heq] at hklo
    linarith only [hklo, H, Hlo]
  have Hupper : G 0 ≤ 64 / r := by
    have H := hμ.2.2.le.trans hkhi
    exact Hhi.trans ((mul_le_mul_of_nonneg_left H (by norm_num)).trans_eq (by ring))
  refine ⟨T, hT, hfirst, hvalid, Hlower, Hupper, Hstrong.1, Hweak.1, ?_, ?_⟩
  · exact Hsum.trans ((mul_le_mul_of_nonneg_left (hweak.trans hprod.2) (by norm_num)).trans_eq (by ring))
  · rw [horbit] at Hentry
    exact Hentry

end BianchiIX
