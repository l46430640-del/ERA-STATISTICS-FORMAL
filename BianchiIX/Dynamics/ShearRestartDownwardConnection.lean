import BianchiIX.Dynamics.PartialCoreDownwardConnection
import BianchiIX.Dynamics.ShearRestartDownwardReturn

noncomputable section

namespace BianchiIX

open Set

/-- Actual positive-decaying-wall shear entries reach a regular long connection on the original Einstein orbit. -/
theorem exists_restartShearPartialCore_downward_connection :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q P : ℝ, 3 < q → 4 < P → ∀ η ∈ Ioc (0 : ℝ) (1 / 10000),
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
            (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 < n₃ ∧ n₃ ≤ 2 * ε * a) →
            n₃ ≤ a ^ P → ∀ ρ ∈ Icc a (2 * a),
              let s := q / 2 * Real.log (1 / a)
              let x := restartSectionChart h (restartShearCurve 1 n₂ n₃ ρ)
              let y := restartFastShearProjectiveEntry h s 1 n₂ n₃ ρ
              let k := restartFastShearCoreRadius h s 1 n₂ n₃ ρ
              let T := partialCoreDownwardReturnTime y
              let out := projectiveOriginalFlow y 0 T
              let p := coreExitConnectionParameters (partialCoreDownwardReturnState y)
              1 ≤ y 2 →
              0 < T ∧ IsLeast {t | s < t ∧ toProjectiveState (normalizedMaxCurve x 0 t) 2 = 1} (s + T) ∧
              out = connectionEntry (p 0) (p 1) (p 2) ∧
              (4 ≤ p 0 ∧ k / 2 ≤ p 0 ∧ p 0 < k) ∧
              (0 < p 1 ∧ p 1 ≤ η / p 0) ∧ (0 < p 2 ∧ p 2 ≤ η) ∧
              p 1 ≤ y 1 * Real.exp (-k / 12) ∧ p 2 ≤ y 2 * y 3 ∧
              phaseNorm (p 0 + 1) 1 = coreRadius (out 0) (out 2) ∧
              connectionReturnValid p ∧ ContDiffAt ℝ 2 connectionReturnTime p ∧
              ContDiffAt ℝ 2 connectionReturnState p ∧
              connectionReturnState p = toProjectiveState
                (normalizedMaxCurve x 0 (s + T + connectionReturnTime p)) ∧
              let Q := fun z => coreExitConnectionParameters (partialCoreDownwardReturnState z)
              ContDiffAt ℝ 2 Q y ∧
                ContDiffAt ℝ 2 (fun z => partialCoreDownwardReturnTime z + connectionReturnTime (Q z)) y ∧
                ContDiffAt ℝ 2 (fun z => connectionReturnState (Q z)) y := by
  obtain ⟨hstar, hhstar, H⟩ := exists_restartShearPartialCore_entry
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh q P hq hP η hη
  obtain ⟨astar, hastar, Ha⟩ := H h hh q P hq hP η hη
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε n₂ n₃ hε h₂ h₃ h₃P ρ hρ s x y k T out p hv
  obtain ⟨hs, hrad, _, hA, _, hk, _, _, hR, hu0, hp0, hsum, Hentry⟩ :=
    Ha a ha ε n₂ n₃ hε h₂ ⟨h₃.1.le, h₃.2⟩ h₃P ρ hρ
  obtain ⟨hz, _, hy, hvcase⟩ := Hentry hv
  have hc : stateConstraint x = 1 := restartSectionChart_constraint hrad.le
  have Hsign := normalizedMaxCurve_wall_sign hc hs (2 : Fin 3)
  have hnpos : 0 < normalizedMaxCurve x 0 s 4 := by
    have Hnonneg : 0 ≤ wallValue 2 (normalizedMaxCurve x 0 s) := Hsign.2.mpr h₃.1.le
    have Hne : wallValue 2 (normalizedMaxCurve x 0 s) ≠ 0 := fun hzero => h₃.1.ne' (Hsign.1.mp hzero)
    exact lt_of_le_of_ne Hnonneg (Ne.symm Hne)
  have hwpos : 0 < y 3 := div_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) hnpos) hA
  have hp : 0 < y 2 * y 3 := mul_pos (zero_lt_one.trans_le hv) hwpos
  have huη : y 1 ≤ η / k := (le_add_of_nonneg_right hp0).trans hsum
  have hpη : y 2 * y 3 ≤ η / k := (le_add_of_nonneg_left hu0.le).trans hsum
  have hkZ : 2 * Real.cosh 0 ≤ k := by rw [Real.cosh_zero]; linarith only [hk]
  obtain ⟨hentry, hμ, hu, hw, hdecU, hdecP, hphase, _, hvalid, hct, hcs, Hconn⟩ :=
    partialCoreDownwardReturn_connection_domain hk hy hR hvcase (le_refl (0 : ℝ)) hkZ hz.2 hη
      ⟨hu0, huη⟩ ⟨hp, hpη⟩
  have Hreg := partialCoreDownwardConnection_regular hk hy hR hvcase (le_refl (0 : ℝ)) hkZ hz.2 hη
    ⟨hu0, huη⟩ ⟨hp, hpη⟩
  have hfirst := (partialCoreDownwardReturn_regular hk hy hR hvcase).1
  have hT : 0 < T := hfirst.1.1
  have htc : 0 < connectionReturnTime p := hvalid.1.1.1
  have Hflow (t : ℝ) (ht : 0 ≤ t) := restartFastShearProjectiveEntry_flow hrad.le hs hA ht
  have Hfast := Hflow (T + connectionReturnTime p) (add_nonneg hT.le htc.le)
  refine ⟨hT, ?_, hentry, hμ, hu, hw, hdecU, hdecP, hphase, hvalid, hct, hcs, ?_, Hreg⟩
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
