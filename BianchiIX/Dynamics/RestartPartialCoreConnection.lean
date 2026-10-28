import BianchiIX.Dynamics.PartialCoreConnectionEntry
import BianchiIX.Dynamics.RestartPartialCoreResponse

noncomputable section

namespace BianchiIX

open Set

/-- The positive weak-wall family reaches a regular long connection along the same Einstein orbit. -/
theorem exists_restartPartialCore_connection :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q P : ℝ, 3 < q → 4 < P →
        ∀ ε ∈ Ioc (0 : ℝ) (1 / 10000), ∃ rstar : ℝ, 0 < rstar ∧
          ∀ r ∈ Ioc (0 : ℝ) rstar, ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) →
            ∀ ρ ∈ Icc r (2 * r),
              let s := q / 2 * Real.log (1 / r)
              let x := restartSectionChart h (restartRadialCurve θ ζ ρ)
              let y := restartFastProjectiveEntry h s θ ζ ρ
              let k := restartFastCoreRadius h s θ ζ ρ
              ∃ T > 0, IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} T ∧
                IsLeast {t | s < t ∧ toProjectiveState (normalizedMaxCurve x 0 t) 2 = 1} (s + T) ∧
                let out := projectiveOriginalFlow y 0 T
                let p := coreExitConnectionParameters (toCoreAngleState out)
                out = connectionEntry (p 0) (p 1) (p 2) ∧
                (4 ≤ p 0 ∧ k / 2 ≤ p 0 ∧ p 0 < k) ∧
                (0 < p 1 ∧ p 1 ≤ ε / p 0) ∧ (0 < p 2 ∧ p 2 ≤ ε) ∧
                p 1 ≤ y 1 * Real.exp (-k / 12) ∧ p 2 ≤ y 2 * y 3 ∧
                phaseNorm (p 0 + 1) 1 = coreRadius (out 0) (out 2) ∧
                connectionReturnValid p ∧ ContDiffAt ℝ 2 connectionReturnTime p ∧
                ContDiffAt ℝ 2 connectionReturnState p ∧
                connectionReturnState p = toProjectiveState
                  (normalizedMaxCurve x 0 (s + T + connectionReturnTime p)) := by
  obtain ⟨hstar, hhstar, HH⟩ := exists_restartPartialCore_entry
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh L hL q P hq hP ε hε
  obtain ⟨rstar, hrstar, HR⟩ := HH h hh L hL q P hq hP ε hε
  refine ⟨rstar, hrstar, ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  let s := q / 2 * Real.log (1 / r)
  let x := restartSectionChart h (restartRadialCurve θ ζ ρ)
  let y := restartFastProjectiveEntry h s θ ζ ρ
  let k := restartFastCoreRadius h s θ ζ ρ
  let Z := Real.arsinh (4 * (8 * (L + 1)))
  obtain ⟨hs, hrad, _, hA, hk6, hz, hR, hu0, hp0, hsum, hV, _, hy⟩ :=
    HR r hr θ ζ hθ ⟨hζ.1.le, hζ.2⟩ ρ hρ
  have hk : 6 ≤ k := (le_max_left _ _).trans hk6
  have hc : stateConstraint x = 1 := restartSectionChart_constraint hrad.le
  have hinit : positiveWalls x := ⟨hh.1, hr.1.trans_le hρ.1, hζ.1⟩
  have hpos := (normalizedMaxCurve_forward hinit hc hs).2.1
  have hwpos : 0 < y 3 := div_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) hpos.2.2) hA
  have hp : 0 < y 2 * y 3 := mul_pos (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hV) hwpos
  have huε : y 1 ≤ ε / k := (le_add_of_nonneg_right hp0).trans hsum
  have hpε : y 2 * y 3 ≤ ε / k := (le_add_of_nonneg_left hu0.le).trans hsum
  have hV1 : 1 < y 2 := lt_of_lt_of_le (by norm_num) hV
  have hZ : 0 ≤ Z := Real.arsinh_nonneg_iff.mpr (by positivity)
  obtain ⟨T, hT, hfirst, _⟩ := exists_partialCore_entry_variation hk hy hR hV1
  let out := projectiveOriginalFlow y 0 T
  let p := coreExitConnectionParameters (toCoreAngleState out)
  obtain ⟨hentry, hμ, hu, hw, hdecU, hdecP, hphase, hAt, hvalid, hct, hcs⟩ :=
    partialCore_firstReturn_connection_domain hk hy hR hV1 hZ ((le_max_right _ _).trans hk6)
      hz.2 hε ⟨hu0, huε⟩ ⟨hp, hpε⟩ hfirst
  have htc : 0 < connectionReturnTime p := hvalid.1.1.1
  have hD := (coreRegion_clock_regular hk hy).1
  have Hrestart := projectiveOriginalFlow_restart hD hT.le htc.le hAt
  have Hconn : connectionReturnState p = projectiveOriginalFlow y 0 (T + connectionReturnTime p) := by
    change projectiveOriginalFlow (connectionEntry (p 0) (p 1) (p 2)) 0 (connectionReturnTime p) = _
    rw [← hentry]
    simpa only [add_comm (connectionReturnTime p) T] using Hrestart
  have Hfast := restartFastProjectiveEntry_flow hrad.le hs hA (add_nonneg hT.le htc.le)
  refine ⟨T, hT, hfirst, restartFastProjectiveEntry_firstReturn hrad.le hs hA hfirst,
    hentry, hμ, hu, hw, hdecU, hdecP, hphase, hvalid, hct, hcs, ?_⟩
  exact (Hconn.trans Hfast).trans (by rw [add_assoc])

end BianchiIX
