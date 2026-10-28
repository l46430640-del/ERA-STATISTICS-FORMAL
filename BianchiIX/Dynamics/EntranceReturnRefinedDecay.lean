import BianchiIX.Dynamics.EntranceReturnDecay
import BianchiIX.Dynamics.EntranceRefinedArrival

noncomputable section

namespace BianchiIX

open Set

/-- The named first arrival retains the refined strong-wall exponent and its uniform prefactor. -/
theorem entranceReturn_power_decay {y : ProjectiveState}
    (hk : 19 / 10 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    entranceReturnState y 1 ≤ Real.exp (1 / 1000) * (y 1 * (y 2) ^ (19 / 10 : ℝ)) ∧
      entranceReturnState y 3 ≤ y 3 * y 2 := by
  have hk' : 7 / 4 ≤ coreRadius (y 0) (y 2) := by linarith
  have hk0 : 0 < coreRadius (y 0) (y 2) := by linarith
  have hD := entrance_initial_denom_pos hk' hm hu hv hw
  have hc := fromProjectiveState_constraint hD.ne'
  have HR := (entranceReturn_regular hk' hm hu hv hw).1
  have ht : 0 ≤ entranceReturnTime y := HR.1.1.1.le
  have hinit : projectiveOriginalFlow y 0 0 = y := projectiveOriginalFlow_initial hD 0
  have H := normalized_entrance_arc_decay hc hk' le_rfl ht
    (fun r hr => (HR.2.1 r hr).2) (entranceReturn_region hk' hm hu hv hw)
    (by change 0 < projectiveOriginalFlow y 0 0 2; rw [hinit]; exact hv.1)
  change entranceReturnState y 1 ≤ projectiveOriginalFlow y 0 0 1 *
    Real.exp ((2 * projectiveOriginalFlow y 0 0 3 + 3 * (projectiveOriginalFlow y 0 0 1) ^ 2) /
      coreRadius (y 0) (y 2)) * Real.exp (-(1 + 99 * coreRadius (y 0) (y 2) / 200) *
        (Real.log (entranceReturnState y 2) - Real.log (projectiveOriginalFlow y 0 0 2))) at H
  rw [hinit, (entranceReturn_active_component hk' hm hu hv hw).1,
    Real.log_one, zero_sub, neg_mul_neg] at H
  have hpow : Real.exp ((1 + 99 * coreRadius (y 0) (y 2) / 200) * Real.log (y 2)) ≤
      (y 2) ^ (19 / 10 : ℝ) := by
    rw [Real.rpow_def_of_pos hv.1]
    apply Real.exp_le_exp.mpr
    have he : 19 / 10 ≤ 1 + 99 * coreRadius (y 0) (y 2) / 200 := by linarith
    nlinarith only [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr he)
      (Real.log_nonpos hv.1.le hv.2.le)]
  refine ⟨H.trans ?_, ?_⟩
  · calc
      _ ≤ (y 1 * Real.exp (1 / 1000)) * (y 2) ^ (19 / 10 : ℝ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (entrance_arc_prefactor_bound hk' hu hw) hu.1)
          hpow (Real.exp_pos _).le (mul_nonneg hu.1 (Real.exp_pos _).le)
      _ = _ := by ring
  · exact (entranceReturn_decay hk' hm hu hv hw).2.trans
      (mul_le_of_le_one_right (mul_nonneg hw.1 hv.1.le)
        (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
          (by simpa using Real.log_nonpos hv.1.le hv.2.le) hk0.le)))

end BianchiIX
