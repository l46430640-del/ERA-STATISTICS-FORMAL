import BianchiIX.Dynamics.ConnectionReturnClock
import BianchiIX.Dynamics.ConnectionActualPhaseFeedback
import BianchiIX.Dynamics.ConnectionActualStrongFeedback
import BianchiIX.Dynamics.ConnectionActualGrowingFeedback

noncomputable section

namespace BianchiIX

open Set

/-- Fixed-relative-clock responses at the canonical arrival, with all orbit hypotheses discharged. -/
theorem connectionReturn_fixed_clock_bounds {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    let μ := p 0
    let u := p 1
    let w := p 2
    let L := -Real.log w
    let y := connectionEntry μ u w
    let D := connectionLogFlowVariation y 0 (connectionReturnTime p)
    (|D ![-1, 0, 0, 0] 0| ≤ 16 / 15 ∧
      |D ![-1, 0, 0, 0] 0 - connectionLogTangent y ![-1, 0, 0, 0] 0| ≤
        (16 / 15) * connectionPhaseFeedbackBudget μ u w ∧
      ‖connectionWeightedTangent μ (D ![-1, 0, 0, 0])‖ ≤ (2048 / 15) * L) ∧
    (|D ![0, 1, 0, 0] 0| ≤ 70 / μ ∧
      |D ![0, 1, 0, 0] 1| ≤ 1 / u + 256 + 8960 * L / μ ∧
      |D ![0, 1, 0, 0] 2| ≤ (256 + 8960 * L / μ) / μ ^ 2) ∧
    (|D ![0, 0, 0, 1] 0| ≤ 8000 * (u + w) / μ ∧
      |D ![0, 0, 0, 1] 1| ≤ 32 + 12800 * u + 96 / (μ * w) + 1024000 * L * (u + w) / μ ∧
      |D ![0, 0, 0, 1] 2| ≤ (12800 * u + 64 / (μ * w) + 1024000 * L * (u + w) / μ) / μ ^ 2) := by
  intro μ u w L y D
  obtain ⟨hL, q, hq0, hqL, H⟩ := exists_connectionReturn_log_clock hμ hu hw
  change q L = connectionReturnTime p at hqL
  have hden := connection_entry_denom_pos hμ ⟨hu.1.le, hu.2⟩ hw
  have hdom z hz := (H z hz).1
  have hchart z hz := (H z hz).2.1
  have hm z hz := (H z hz).2.2.1.1
  have hU z hz := And.intro (H z hz).2.2.2.1 (H z hz).2.2.1.2.1.2
  have hV z hz := And.intro (H z hz).2.2.2.2.1 (H z hz).2.2.1.2.2.1.2
  have hW z hz := And.intro (H z hz).2.2.2.2.2.1 (H z hz).2.2.1.2.2.2.2
  have hq z hz := (H z hz).2.2.2.2.2.2
  have hentry : y 1 ≤ y 2 := by
    change p 1 ≤ 1
    have hμ0 : 0 < p 0 := by linarith only [hμ]
    have huμ := (le_div_iff₀ hμ0).mp hu.2
    nlinarith only [huμ, hμ, hu.1]
  have hend : L ∈ Icc 0 L := ⟨hL, le_rfl⟩
  have hr := connectionLog_actual_radial_variation_bounds hL hμ hden hdom hchart hm hU hV hW
    hentry hu.2 hw.2 hq hq0 ![-1, 0, 0, 0] (by rfl) (by rfl) (by rfl) L hend
  have hs := connectionLog_actual_strong_variation_bounds hL hμ hden hdom hchart hm hU hV hW
    hentry hu.2 hw.2 hq hq0 L hend
  have hg := connectionLog_actual_growing_variation_bounds hL hμ hden hdom hchart hm hU hV hW
    hentry hu.2 hw.2 hq hq0 L hend
  have hWend : projectiveOriginalFlow y 0 (q L) 3 = 1 := by
    rw [hqL]
    exact (connectionReturn_growing_component hμ ⟨hu.1.le, hu.2⟩ hw).1
  change projectiveOriginalFlow (connectionEntry (p 0) (p 1) (p 2)) 0 (q L) 3 = 1 at hWend
  rw [hWend] at hg
  rw [hqL] at hr hs hg
  refine ⟨?_, ?_, ?_⟩
  · simpa [D, y, μ, u, w, connectionEntry] using hr
  · simpa [D, y, μ, u, w, connectionEntry] using hs
  · simpa [D, y, μ, u, w, connectionEntry] using hg

end BianchiIX
