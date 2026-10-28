import BianchiIX.Dynamics.ConnectionReturnContraction
import BianchiIX.Dynamics.CoreConnectionChart

noncomputable section

namespace BianchiIX

/-- The reflected connection exit is an ascending core entry with both walls bounded by the incoming weak wall. -/
theorem connectionReturn_restart_bounds {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 < p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    let G := connectionReturnPhysicalState p
    p 0 / 2 ≤ G 0 ∧ G 0 ≤ 2 * p 0 ∧
      (0 < G 1 ∧ G 1 ≤ p 2) ∧ (0 < G 2 ∧ G 2 ≤ p 2) ∧ G 1 + G 2 ≤ 2 * p 2 ∧
      coreRadiusEntry G = projectiveReflection (connectionReturnState p) := by
  intro G
  have hμ0 : 0 < p 0 := by linarith only [hμ]
  have hu' : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0 := ⟨hu.1.le, hu.2⟩
  have hu1 : p 1 ≤ 1 := hu.2.trans ((div_le_self (by norm_num) (by linarith only [hμ])).trans (by norm_num))
  have hw1 : p 2 ≤ 1 := hw.2.trans (by norm_num)
  let L := -Real.log (p 2)
  have hL : 0 ≤ L := neg_nonneg.mpr (Real.log_nonpos hw.1.le hw1)
  have hdec := connectionReturn_exponential_decay hμ hu hw
  have Hstrong : Real.exp (-p 0 * L / 2) ≤ p 2 := by
    calc
      _ ≤ Real.exp (-L) := Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg (by linarith only [hμ] : 0 ≤ p 0 - 2) hL])
      _ = _ := by dsimp only [L]; rw [neg_neg, Real.exp_log hw.1]
  have Hweak : Real.exp (-2 * L / p 0) ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (by linarith only [hL]) hμ0.le)
  have hU : G 1 ≤ p 2 := hdec.1.trans (le_trans
    (mul_le_mul_of_nonneg_left Hstrong hu.1.le) (mul_le_of_le_one_left hw.1.le hu1))
  have hW : G 2 ≤ p 2 := hdec.2.trans (mul_le_of_le_one_right hw.1.le Hweak)
  have Hpos := connectionReturn_wall_pos hμ hu' hw
  have Hcontrol := connectionReturn_control hμ hu' hw
  have Hr := (Hcontrol.2 (connectionReturnTime p) ⟨Hcontrol.1.le, le_rfl⟩).2
  change connectionRegion (p 0) (connectionReturnState p) at Hr
  have Hm := abs_le.mp Hr.1
  let a := -connectionReturnState p 0 - 1
  have ha : p 0 / 2 ≤ a ∧ a ≤ p 0 := by dsimp only [a]; constructor <;> linarith only [Hm.1, Hm.2, hμ]
  have ha0 : 0 ≤ a := (half_pos hμ0).le.trans ha.1
  have Hlo : p 0 / 2 ≤ G 0 := ha.1.trans (phaseNorm_ge (b := 1) ha0)
  have Hsq : (G 0) ^ 2 = a ^ 2 + 1 := by
    change phaseNorm a 1 ^ 2 = a ^ 2 + 1
    simpa only [one_pow] using phaseNorm_sq a 1
  have Hhi : G 0 ≤ 2 * p 0 := by
    have Ha := pow_le_pow_left₀ ha0 ha.2 2
    have Hg0 : 0 ≤ G 0 := Real.sqrt_nonneg _
    nlinarith only [Hsq, Ha, Hg0, hμ]
  refine ⟨Hlo, Hhi, ⟨Hpos.2 hu.1, hU⟩, ⟨Hpos.1, hW⟩, by linarith only [hU, hW], ?_⟩
  exact coreRadiusEntry_reflected_exit (by dsimp only [a] at ha; linarith only [ha.1, hμ])
    (connectionReturn_growing_component hμ hu' hw).1

end BianchiIX
