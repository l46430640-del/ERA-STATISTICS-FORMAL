import BianchiIX.Dynamics.EntranceReturnDecay
import BianchiIX.Analysis.EntranceTerminalWeights

noncomputable section

namespace BianchiIX

open Set

theorem entranceReturn_terminal_weights {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    let k := coreRadius (y 0) (y 2)
    let L := -Real.log (y 2)
    let ω := Real.exp (-2 * L / k)
    let p := entranceReturnState y
    let b := p 1 + p 3
    b ^ 2 ≤ 2 * (y 1 * y 2 + (y 2) ^ 2 * (y 3) ^ 2 * ω) ∧
    k * L * b * p 1 ≤ 6 * y 1 * y 2 ∧
    (L / k) * b * p 3 ≤ 3 * y 1 * y 2 + (L / k) * ((y 2) ^ 2 * (y 3) ^ 2 * ω) ∧
    b * p 1 ≤ 2 * y 1 * y 2 ∧
    b * p 3 ≤ y 3 * (y 1 * y 2 + (y 2) ^ 2 * y 3 * ω) ∧
    b ≤ 2 * y 2 := by
  intro k L ω p b
  have hk1 : 1 ≤ k := by linarith
  have hL : 0 ≤ L := neg_nonneg.mpr (Real.log_nonpos hv.1.le hv.2.le)
  have H := entrance_terminal_clock_weights hk1 hL
  have HR := (entranceReturn_regular hk hm hu hv hw).1
  have hreg : entranceRegion k p := entranceReturn_region hk hm hu hv hw _ ⟨HR.1.1.1.le, le_rfl⟩
  have hdec := entranceReturn_decay hk hm hu hv hw
  have HE := entrance_terminal_wall_weights hk1 hL ⟨hu.1, by linarith [hu.2]⟩
    ⟨hv.1.le, hv.2.le⟩ ⟨hw.1, by linarith [hw.2]⟩ hreg.2.2.1.1 hreg.2.2.2.2.1
    H.1 H.2.1 H.2.2.1 hdec.1 hdec.2
  simpa only [H.2.2.2.1] using HE

end BianchiIX
