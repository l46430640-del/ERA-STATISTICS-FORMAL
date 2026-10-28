import BianchiIX.Measure.PrimaryAxisRecurrence
import BianchiIX.Measure.MainWallAxisCapture

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology ENNReal

/-- On a sufficiently small complete three-axis section, wall-product decay suffices for almost-everywhere statistical capture. -/
theorem exists_primaryAxis_statistics_of_decay (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∃ dstar > (0 : ℝ),
            ∀ d ∈ Ioc (0 : ℝ) dstar,
              let E := fun _ : Fin 3 => mainWallSmallSection d ∩ mainWallChartDomain h
              ∀ᵐ z ∂axisFamilyMeasure (fun _ : Fin 3 => h), z ∈ axisFamilySection E →
                (∀ i j : Fin 3, i ≠ j → Tendsto
                  (fun t => wallValue i
                      (normalizedMaxCurve (axisFamilyChart primaryAxisFrame (fun _ => h) z) 0 t) *
                    wallValue j (normalizedMaxCurve (axisFamilyChart primaryAxisFrame (fun _ => h) z) 0 t))
                      atTop (𝓝 0)) →
                StatisticalCoreFuture η J σ Bcap (axisFamilyChart primaryAxisFrame (fun _ => h) z) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_mainWall_primaryAxis_capture hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, min hS (1 / 16), lt_min hhS (by norm_num), ?_⟩
  intro h hh
  obtain ⟨dS, hdS, C, hC, HdS⟩ := HS h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩
  refine ⟨min dS (h / 16), lt_min hdS (div_pos hh.1 (by norm_num)), ?_⟩
  intro d hd E
  obtain ⟨F, _, _, _, _, _, _, hcapture⟩ := HdS d ⟨hd.1, hd.2.trans (min_le_left _ _)⟩
  have hdh : d < h / 8 := lt_of_le_of_lt (hd.2.trans (min_le_right _ _))
    (by linarith only [hh.1])
  filter_upwards [hcapture, ae_primaryAxis_infiniteReturns_of_decay hBirkhoff hh.1
    (hh.2.trans (min_le_right _ _)) hd.1 hdh] with z hz hrec hzE hprod
  exact hz (hrec hzE hprod)

end BianchiIX
