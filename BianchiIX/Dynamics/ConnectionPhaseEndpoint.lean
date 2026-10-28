import BianchiIX.Algebra.MatchingPhaseEndpoints
import BianchiIX.Dynamics.MatchingPhaseDrift

noncomputable section

namespace BianchiIX

open Set

theorem connectionLog_endpoint_phase_bound {Y : ℝ → ProjectiveState} {μ a b : ℝ}
    (hab : a ≤ b) (hμ : 4 ≤ μ)
    (hY : ∀ z ∈ Icc a b, HasDerivAt Y (connectionLogField (Y z)) z)
    (hm : ∀ z ∈ Icc a b, |-Y z 0 - μ| ≤ 1 / 2)
    (hu : ∀ z ∈ Icc a b, 0 ≤ Y z 1 ∧ Y z 1 ≤ 1 / 10000)
    (hv : ∀ z ∈ Icc a b, 0 < Y z 2 ∧ Y z 2 ≤ 1)
    (hw : ∀ z ∈ Icc a b, 0 ≤ Y z 3 ∧ Y z 3 ≤ 1)
    (hinit : -Y a 0 = μ) (hV : Y a 2 = 1) (hhit : Y b 3 = 1) :
    |phaseNorm (-Y b 0 - 1) 1 - phaseNorm (μ + 1) 1 + 2| ≤ 24 * (Y a 1 + (Y a 3) ^ 2) / μ := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hentry : Y a 1 ≤ Y a 2 := by rw [hV]; linarith only [(hu a ha).2]
  have hp := (connectionLog_prefix_estimates hab hμ hY hm hu hv hw hentry).2.2.2.1
  have hexp : Real.exp (-2 * (b - a) / μ) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sub_nonneg.mpr hab))
      (by linarith only [hμ])
  have hvw : Y b 2 ≤ Y a 3 := by
    rw [hV, hhit, mul_one, one_mul] at hp
    exact hp.trans ((mul_le_mul_of_nonneg_left hexp (hw a ha).1).trans_eq (mul_one _))
  have hJ := connectionLog_matchingPhase_drift hab hμ hY hm hu hv hw hentry
  rw [hinit, hV, hhit, one_mul] at hJ
  exact matchingPhase_endpoint_bound hμ (hm b hb) (hu a ha).1 ⟨(hv b hb).1.le, hvw⟩ hJ

end BianchiIX
