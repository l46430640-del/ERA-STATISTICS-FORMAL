import BianchiIX.Dynamics.EntranceRadiusDriftIntegral
import BianchiIX.Dynamics.EntranceReturnDecay
import BianchiIX.Analysis.EntranceActiveTerminalCorrection

noncomputable section

namespace BianchiIX

open Set

theorem exists_entrance_active_terminal_drift :
    ∃ C > (0 : ℝ), ∀ (y : ProjectiveState),
      let k := coreRadius (y 0) (y 2)
      7 / 4 ≤ k → 1 ≤ y 0 →
      (0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) → (0 < y 2 ∧ y 2 < 1) →
      (0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) → k * (y 1 + y 3) ^ 2 ≤ 1 →
      let L := -Real.log (y 2)
      |entranceRadialDrift (entranceReturnState y)| ≤ C *
        (y 1 * y 2 * Real.exp (-k * L / 3) +
          (y 2) ^ 2 * (y 3) ^ 2 * Real.exp (-2 * L / k) / k ^ 4) := by
  obtain ⟨C, hC, HC⟩ := exists_entranceRadialDrift_weighted_bound
  refine ⟨C, hC, ?_⟩
  intro y k hk hm hu hv hw hsmall L
  let p := entranceReturnState y
  have hk0 : 0 < k := by linarith
  have hk1 : 1 ≤ k := by linarith
  have hL : 0 ≤ L := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have HR := (entranceReturn_regular hk hm hu hv hw).1
  have hp : entranceRegion k p := entranceReturn_region hk hm hu hv hw _ ⟨HR.1.1.1.le, le_rfl⟩
  have hhit : p 2 = 1 := (entranceReturn_active_component hk hm hu hv hw).1
  have hclock := entrance_terminal_clock_weights hk1 hL
  have hdec := entranceReturn_decay hk hm hu hv hw
  have H := entrance_active_terminal_products ⟨hu.1, by linarith [hu.2]⟩ ⟨hv.1.le, hv.2.le⟩
    ⟨hw.1, by linarith [hw.2]⟩ hp.2.2.1.1 hp.2.2.2.2.1 hclock.1 hclock.2.1 hdec.1 hdec.2
  have hs : k * (p 1 + p 3) ^ 2 ≤ 1 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (add_nonneg hp.2.2.1.1 hp.2.2.2.2.1) H.1 2) hk0.le).trans hsmall
  have HG := HC k (1 / k ^ 2) p hk hp (by rw [hhit]; norm_num) (Or.inr ⟨rfl, hs⟩)
  rw [hhit, mul_one, one_mul] at HG
  have he : (1 / k ^ 2) * (p 3) ^ 2 / k ^ 2 = (p 3) ^ 2 / k ^ 4 := by field_simp
  rw [he] at HG
  have hW : (p 3) ^ 2 ≤ (y 2) ^ 2 * (y 3) ^ 2 * Real.exp (-2 * L / k) := by
    simpa only [hclock.2.2.2.1] using H.2.1
  exact HG.trans (mul_le_mul_of_nonneg_left
    (add_le_add hdec.1 (div_le_div_of_nonneg_right hW (by positivity))) hC.le)

end BianchiIX
