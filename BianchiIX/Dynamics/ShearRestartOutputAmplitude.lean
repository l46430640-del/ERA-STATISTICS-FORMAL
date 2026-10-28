import BianchiIX.Dynamics.ShearRestartPartialCoreResponse
import BianchiIX.Dynamics.PartialCoreDownwardConnection
import BianchiIX.Dynamics.ConnectionRestartBounds

noncomputable section

namespace BianchiIX

open Set

/-- E.36 radius and amplitude bounds for the actual positive-shear downward route, including V = 1. -/
theorem exists_restartShearConnection_output_bounds :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
        ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
          (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
          n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
            let s := q / 2 * Real.log (1 / a)
            let y := restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ
            let x := restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)
            let T := partialCoreDownwardReturnTime y
            let p := coreExitConnectionParameters (partialCoreDownwardReturnState y)
            let G := connectionReturnPhysicalState p
            1 ≤ y 2 →
            0 < T ∧ IsLeast {t | s < t ∧ toProjectiveState (normalizedMaxCurve x 0 t) 2 = 1} (s + T) ∧
            connectionReturnValid p ∧ 1 / (64 * a) ≤ G 0 ∧ G 0 ≤ 64 / a ∧
            0 < G 1 ∧ 0 < G 2 ∧ G 1 + G 2 ≤ 512 * n₂ * n₃ / a ^ 4 ∧
            coreRadiusEntry G = projectiveReflection (toProjectiveState
              (normalizedMaxCurve x 0 (s + T + connectionReturnTime p))) := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartShearPartialCore_entry
  obtain ⟨hV, hhV, HV⟩ := exists_restartFastShearProjectiveEntry_bounds
  refine ⟨min hE hV, lt_min hhE hhV, ?_⟩
  intro h hh q P hq hP
  obtain ⟨aE, haE, HaE⟩ := HE h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q P hq hP
    (1 / 10000) ⟨by norm_num, le_rfl⟩
  obtain ⟨aV, haV, HaV⟩ := HV h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q (by linarith only [hq])
  refine ⟨min aE aV, lt_min haE haV, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s y x T p G hv
  obtain ⟨hs, hrad, _, hA, _, hk, hklo, hkhi, hR, hu0, hp0, hsum, Hentry⟩ :=
    HaE a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε n₂ n₃ hε h₂ ⟨h₃.1.le, h₃.2⟩ h₃P ρ hρ
  obtain ⟨hz, _, hy, hvcase⟩ := Hentry hv
  obtain ⟨_, _, _, _, _, _, _, _, _, hw, _, hprod⟩ :=
    HaV a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε 1 n₂ n₃ hε (by norm_num) h₂ ⟨h₃.1.le, h₃.2⟩ ρ hρ
  have hw0 : 0 < y 3 := (div_pos h₃.1 (by positivity [ha.1])).trans_le hw.1
  have hp0' : 0 < y 2 * y 3 := mul_pos (zero_lt_one.trans_le hv) hw0
  have huη := (le_add_of_nonneg_right hp0).trans hsum
  have hpη := (le_add_of_nonneg_left hu0.le).trans hsum
  have hkZ : 2 * Real.cosh 0 ≤ restartFastShearCoreRadius h s 1 n₂ n₃ ρ := by
    rw [Real.cosh_zero]
    linarith only [hk]
  obtain ⟨_, hμ, hu, hw', _, hweak, _, _, hvalid, _, _, horbit⟩ :=
    partialCoreDownwardReturn_connection_domain hk hy hR hvcase (le_refl (0 : ℝ)) hkZ hz.2
      ⟨by norm_num, le_rfl⟩ ⟨hu0, huη⟩ ⟨hp0', hpη⟩
  obtain ⟨Hlo, Hhi, Hstrong, Hweak, Hsum, Hentry'⟩ := connectionReturn_restart_bounds hμ.1 hu hw'
  have hfirst := (partialCoreDownwardReturn_regular hk hy hR hvcase).1
  have hT : 0 < T := hfirst.1.1
  have htc : 0 < connectionReturnTime p := hvalid.1.1.1
  have Hflow (t : ℝ) (ht : 0 ≤ t) := restartFastShearProjectiveEntry_flow hrad.le hs hA ht
  have Hfast := Hflow (T + connectionReturnTime p) (add_nonneg hT.le htc.le)
  have Hlower : 1 / (64 * a) ≤ G 0 := by
    have Heq : 1 / (16 * a) = 4 * (1 / (64 * a)) := by ring
    rw [Heq] at hklo
    linarith only [hklo, hμ.2.1, Hlo]
  have Hupper : G 0 ≤ 64 / a := Hhi.trans
    ((mul_le_mul_of_nonneg_left (hμ.2.2.le.trans hkhi) (by norm_num)).trans_eq (by ring))
  refine ⟨hT, ?_, hvalid, Hlower, Hupper, Hstrong.1, Hweak.1, ?_, ?_⟩
  · refine ⟨⟨by linarith only [hT], ?_⟩, ?_⟩
    · rw [← Hflow T hT.le]
      exact hfirst.1.2
    · intro t ht
      have hsub : 0 < t - s := sub_pos.mpr ht.1
      have HF := Hflow (t - s) hsub.le
      rw [add_sub_cancel] at HF
      have Hleast := hfirst.2 ⟨hsub, by rw [HF]; exact ht.2⟩
      linarith only [Hleast]
  · exact Hsum.trans ((mul_le_mul_of_nonneg_left (hweak.trans hprod.2) (by norm_num)).trans_eq (by ring))
  · rw [horbit.trans Hfast] at Hentry'
    simpa only [add_assoc] using Hentry'

end BianchiIX
