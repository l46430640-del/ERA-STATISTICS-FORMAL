import BianchiIX.Dynamics.EntranceReturnSegment
import BianchiIX.Dynamics.EntranceDecay

noncomputable section

namespace BianchiIX

open Set

theorem entranceReturn_decay {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    let k := coreRadius (y 0) (y 2)
    let L := -Real.log (y 2)
    entranceReturnState y 1 ≤ y 1 * y 2 * Real.exp (-k * L / 3) ∧
      entranceReturnState y 3 ≤ y 3 * y 2 * Real.exp (-L / k) := by
  intro k L
  have hD := entrance_initial_denom_pos hk hm hu hv hw
  have hc := fromProjectiveState_constraint hD.ne'
  have HR := (entranceReturn_regular hk hm hu hv hw).1
  have ht : 0 ≤ entranceReturnTime y := HR.1.1.1.le
  have hinit : projectiveOriginalFlow y 0 0 = y := projectiveOriginalFlow_initial hD 0
  have H := normalized_entrance_decay hc hk le_rfl ht (fun r hr => (HR.2.1 r hr).2)
    (entranceReturn_region hk hm hu hv hw)
    (by change 0 < projectiveOriginalFlow y 0 0 2; rw [hinit]; exact hv.1)
    (entranceReturnTime y) ⟨ht, le_rfl⟩
  change entranceReturnState y 1 ≤ projectiveOriginalFlow y 0 0 1 *
      Real.exp (-(1 + k / 3) * (Real.log (entranceReturnState y 2) - Real.log (projectiveOriginalFlow y 0 0 2))) ∧
    entranceReturnState y 3 ≤ projectiveOriginalFlow y 0 0 3 *
      Real.exp (-(1 + 1 / k) * (Real.log (entranceReturnState y 2) - Real.log (projectiveOriginalFlow y 0 0 2))) at H
  rw [hinit, (entranceReturn_active_component hk hm hu hv hw).1, Real.log_one, zero_sub] at H
  have he (a : ℝ) : Real.exp (-(1 + a) * L) = y 2 * Real.exp (-a * L) := by
    rw [show -(1 + a) * L = -L + -a * L by ring, Real.exp_add]
    simp only [L, neg_neg, Real.exp_log hv.1]
  change entranceReturnState y 1 ≤ y 1 * Real.exp (-(1 + k / 3) * L) ∧
    entranceReturnState y 3 ≤ y 3 * Real.exp (-(1 + 1 / k) * L) at H
  rw [he, he] at H
  rw [show -(k / 3) * L = -k * L / 3 by ring,
    show -(1 / k) * L = -L / k by ring] at H
  simpa only [mul_assoc] using H

end BianchiIX
