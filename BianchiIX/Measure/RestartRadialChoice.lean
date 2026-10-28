import BianchiIX.Measure.RadialRestartSelection
import BianchiIX.Measure.RestartRadialFlux

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

/-- The prescribed failure set, its exact quantitative flux, and a Borel physical statistical restart use the same data. -/
theorem exists_restartRadialFailure_borel_restart (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ), hstar ≤ 1 / 8 ∧
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
            ∀ ε ∈ Ioc (0 : ℝ) (1 / 128), ∃ C > (0 : ℝ),
              ∀ Bbound : ℝ, 0 < Bbound → ∃ dstar > (0 : ℝ), dstar ≤ h / 8 ∧
                ∀ d ∈ Ioc (0 : ℝ) dstar,
                  let F := restartRadialFailureFamily h q d ε P η J σ Bcap
                  let E := radialFailureSet d ε F
                  (∀ i, MeasurableSet (F i)) ∧ MeasurableSet E ∧
                    mainWallOriginalMeasure h E = (∑' i, radialFailureIntegral h d ε F i) ∧
                    mainWallOriginalMeasure h E ≤ ENNReal.ofReal (C * d * (1 + |Real.log d|) ^ 2) ∧
                    mainWallOriginalMeasure h E ≠ ⊤ ∧
                    ∃ W : SectionCoordinates → CoreRestartData, Measurable W ∧
                      ∀ y ∈ mainWallOpenSection d \ E,
                        y ∈ mainWallChartDomain h ∧ (W y).2.1 ≤ Bbound ∧
                        CoreRestartWitness η J σ Bcap (mainWallChart h y) (W y) ∧
                        ∃ i : RadialPieceIndex, y ∈ physicalRadialPiece d ε i ∧
                          (W y).2 = restartRadialOutput h q d ε i (radialPieceInverse i.1 y) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartRadialFailure_quantitative hBirkhoff
  obtain ⟨hAR, hhAR, HAR⟩ := exists_restartReturn_joint_regular
  obtain ⟨hSR, hhSR, HSR⟩ := exists_restartShearReturn_common_regular
  obtain ⟨hAO, hhAO, HAO⟩ := exists_restartReturn_reflected_orbit
  obtain ⟨hSO, hhSO, HSO⟩ := exists_restartShearReturn_common_bounds
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσ1 hσJ
  obtain ⟨Bcap, hcap, hcap1, hQ, hhQ, hhQ1, HQ⟩ := Hδ η hη hηδ J hJ σ hσ hσ1 hσJ
  refine ⟨Bcap, hcap, hcap1, min hQ (min hAR (min hSR (min hAO hSO))),
    lt_min hhQ (lt_min hhAR (lt_min hhSR (lt_min hhAO hhSO))), (min_le_left _ _).trans hhQ1, ?_⟩
  intro h hh q D P hq hD hP ε hε
  have hh' := hh.2.trans (min_le_right _ _)
  have hh'' := hh'.trans (min_le_right _ _)
  have hh''' := hh''.trans (min_le_right _ _)
  let L := 1 / ε
  have hL : 0 ≤ L := by dsimp only [L]; positivity [hε.1]
  have hP4 : 4 < P := by linarith only [hD, hP]
  obtain ⟨C, hC, dQ, hdQ, hdQh, HDQ⟩ :=
    HQ h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP ε hε
  obtain ⟨aAR, haAR, HAReg⟩ := HAR h ⟨hh.1, hh'.trans (min_le_left _ _)⟩ L hL q P hq hP4
  obtain ⟨aSR, haSR, HSReg⟩ := HSR h ⟨hh.1, hh''.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aAO, haAO, HAOrbit⟩ := HAO h ⟨hh.1, hh'''.trans (min_le_left _ _)⟩ L hL q P hq hP4
  obtain ⟨aSO, haSO, HSOrbit⟩ := HSO h ⟨hh.1, hh'''.trans (min_le_right _ _)⟩ q D P hq hD hP
  let K := 51200 * (L + 1)
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨C, hC, ?_⟩
  intro Bbound hBbound
  let d₀ := min dQ (min aAR (min aSR (min aAO aSO)))
  refine ⟨min d₀ (min 1 (min (Bbound / 800) (Bbound / K))),
    lt_min (lt_min hdQ (lt_min haAR (lt_min haSR (lt_min haAO haSO))))
      (lt_min zero_lt_one (lt_min (div_pos hBbound (by norm_num)) (div_pos hBbound hK))),
    ((min_le_left _ _).trans (min_le_left _ _)).trans hdQh, ?_⟩
  intro d hd F E
  have hd₀ : d ≤ d₀ := hd.2.trans (min_le_left _ _)
  have hd' := hd₀.trans (min_le_right _ _)
  have hd'' := hd'.trans (min_le_right _ _)
  have hd''' := hd''.trans (min_le_right _ _)
  have hdnum := hd.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hd1 : d ≤ 1 := hd.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSd : 800 * d ≤ Bbound := by
    have H := (le_div_iff₀ (by norm_num : (0 : ℝ) < 800)).mp (hdnum.trans (min_le_left _ _))
    nlinarith only [H]
  have hAd : K * d ≤ Bbound := by
    have H := (le_div_iff₀ hK).mp (hdnum.trans (min_le_right _ _))
    nlinarith only [H]
  obtain ⟨hF, hE, Heq, Hbound, Hfin, _, Hstats⟩ := HDQ d ⟨hd.1, hd₀.trans (min_le_left _ _)⟩
  have hdata (i : RadialPieceIndex) : Measurable
      ((radialRestartParameterDomain (dyadicScale d i.2) ε P i.1).domRestrict
        (radialRestartData h (q / 2 * Real.log (1 / dyadicScale d i.2)) (dyadicScale d i.2) ε i.1)) := by
    rcases i with ⟨neg | other, j⟩
    · have H (v : (ℝ × ℝ) × ℝ) (hv : v ∈ shearRestartParameterDomain ε (dyadicScale d j) P) :=
        HSReg (dyadicScale d j) ⟨dyadicScale_pos hd.1 j,
          (dyadicScale_le hd.1.le j).trans (hd''.trans (min_le_left _ _))⟩
          ε v.1.1 v.1.2 ⟨hε.1.le, hε.2⟩ hv.1.1 hv.1.2.1 hv.1.2.2 v.2 hv.2
      exact measurable_shearRestartData neg (fun v hv => (H v hv).2.2.2) (fun v hv => (H v hv).2.1)
    · have H (v : (ℝ × ℝ) × ℝ) (hv : v ∈ angularRestartParameterDomain (dyadicScale d j) L P) :=
        HAReg (dyadicScale d j) ⟨dyadicScale_pos hd.1 j,
          (dyadicScale_le hd.1.le j).trans (hd'.trans (min_le_left _ _))⟩ v.1.1 v.1.2 hv.1.1 hv.1.2 v.2 hv.2
      exact measurable_angularRestartData other (fun v hv => (H v hv).2.2.2.2) (fun v hv => (H v hv).2.2.1)
  have Hpoint (i : RadialPieceIndex) (v : (ℝ × ℝ) × ℝ)
      (hv : v ∈ radialRestartParameterDomain (dyadicScale d i.2) ε P i.1)
      (p : eraSurvivorDomain η J σ Bcap)
      (hp : p.val = (radialRestartData h (q / 2 * Real.log (1 / dyadicScale d i.2))
        (dyadicScale d i.2) ε i.1 v).2)
      (hs : EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p)) :
      radialRestartChart i.1 v ∈ mainWallChartDomain h ∧
      (radialRestartData h (q / 2 * Real.log (1 / dyadicScale d i.2)) (dyadicScale d i.2) ε i.1 v).2.1 ≤ Bbound ∧
      CoreRestartWitness η J σ Bcap (mainWallChart h (radialRestartChart i.1 v))
        (radialRestartData h (q / 2 * Real.log (1 / dyadicScale d i.2)) (dyadicScale d i.2) ε i.1 v) := by
    rcases i with ⟨neg | other, j⟩
    · have ha := dyadicScale_pos hd.1 j
      have had := dyadicScale_le hd.1.le j
      have hweak : 2 * ε * dyadicScale d j ≤ dyadicScale d j :=
        mul_le_of_le_one_left ha.le (by linarith only [hε.2])
      have hb := (restartShearAmplitudeBudget_le_of_min ⟨ha, had.trans hd1⟩ hP4.le
        ⟨hv.1.1.1, hv.1.1.2.trans hweak⟩ ⟨hv.1.2.1.1, hv.1.2.1.2.trans hweak⟩ hv.1.2.2).2.trans
          ((mul_le_mul_of_nonneg_left had (by norm_num : (0 : ℝ) ≤ 800)).trans hSd)
      obtain ⟨hrad, htime, ht, hdom, _, _, _, _, _, _, ho⟩ := HSOrbit (dyadicScale d j)
        ⟨ha, had.trans (hd'''.trans (min_le_right _ _))⟩ ε v.1.1 v.1.2 ⟨hε.1.le, hε.2⟩
        hv.1.1 hv.1.2.1 hv.1.2.2 v.2 hv.2
      rw [← mainWallRadicand_restartShear hv.1.1.1 hv.1.2.1.1, one_mul] at hrad
      rw [← mainWallChart_restartShear hv.1.1.1 hv.1.2.1.1, one_mul] at hdom ho
      refine ⟨?_, hb, coreRestartWitness_reflected_entry (htime.trans_lt ht) hdom ho p hp hs neg⟩
      cases neg
      · exact hrad
      · simpa only [radialRestartChart, shearRestartChart, ite_true, mainWallChartDomain,
          mem_ofPred_eq, mainWallRadicand_reflection] using hrad
    · have ha := dyadicScale_pos hd.1 j
      have had := dyadicScale_le hd.1.le j
      have hb := (restartAmplitudeBudget_le_scale hL ha (had.trans hd1) hP4.le hv.1.2.2).trans
        ((mul_le_mul_of_nonneg_left had hK.le).trans hAd)
      obtain ⟨hy, ht, hdom, ho, _⟩ := HAOrbit (dyadicScale d j)
        ⟨ha, had.trans (hd'''.trans (min_le_left _ _))⟩ v.1.1 v.1.2 hv.1.1 hv.1.2 v.2 hv.2
      refine ⟨?_, hb, coreRestartWitness_reflected_entry ht hdom ho p hp hs other⟩
      cases other
      · exact hy
      · simpa only [radialRestartChart, angularRestartChart, ite_true, mainWallChartDomain,
          mem_ofPred_eq, mainWallRadicand_reflection] using hy
  obtain ⟨W, hW, HW⟩ := exists_measurable_radial_restart hd.1 hε.1 (by linarith only [hε.2]) hF hdata
  refine ⟨hF, hE, Heq, Hbound, Hfin, W, hW, ?_⟩
  intro y hy
  obtain ⟨i, z, hz, hn, heq, hval⟩ := HW y hy
  obtain ⟨p, hp, hs⟩ := Hstats i z hz hn
  have H := Hpoint i (radialRestartParameter i.1 z) (radialRestartParameter_selected hz hn)
    p (hp.trans (radialRestartData_output h q d ε i z).symm) hs
  rw [radialRestartChart_parameter, heq, ← hval] at H
  refine ⟨H.1, H.2.1, H.2.2, i, ⟨z, hz, heq⟩, ?_⟩
  rw [hval, radialRestartData_output, ← heq, radialPieceInverse_map hd.1 hz]

end BianchiIX
