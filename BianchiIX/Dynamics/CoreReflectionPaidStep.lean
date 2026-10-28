import BianchiIX.Dynamics.CoreReflectionStep
import BianchiIX.Analysis.DiscreteDissipation

noncomputable section

namespace BianchiIX

/-- On the full range above `4 - 1/16`, each actual step pays its phase error by wall loss. -/
theorem exists_coreReflection_paid_step :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 10000 ∧ ∃ C ≥ (1 : ℝ), ∀ Y : CoreAngleState,
      63 / 16 ≤ Y 0 → 0 < Y 1 → 0 < Y 2 → Y 1 + Y 2 ≤ δ / (1 + Y 0) →
      let G := coreReflectionState coreRadiusReturnTime
      coreRadiusReturnValid Y ∧ 0 < coreReflectionTime Y ∧
        coreRadiusEntry (G Y) = projectiveReflection
          (projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreReflectionTime Y)) ∧
        (3 / 2 ≤ Y 0 - G Y 0 ∧ Y 0 - G Y 0 ≤ 5 / 2) ∧
        (∀ i : Fin 2, 0 < G Y i.succ ∧ G Y i.succ ≤ Y i.succ) ∧
        |G Y 0 - (Y 0 - 2)| ≤ C * ((Y 1 + Y 2) - (G Y 1 + G Y 2)) := by
  obtain ⟨ε, hε, hεmax, K, hK, c, hc, _, H⟩ := exists_coreReflection_step
  let δ := min ε (1 / (16 * K))
  let A := (1 + c / 2) / c
  have hδ : 0 < δ := lt_min hε (by positivity)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨δ, hδ, (min_le_left _ _).trans hεmax, max 1 (K * A), le_max_left _ _, ?_⟩
  intro Y hk hu hw hb G
  have hk2 : 2 ≤ Y 0 := by linarith only [hk]
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hb0 : 0 < Y 1 + Y 2 := add_pos hu hw
  have hbudget : δ / (1 + Y 0) ≤ ε / Y 0 :=
    (div_le_div_of_nonneg_left hδ.le hk0 (by linarith)).trans
      (div_le_div_of_nonneg_right (min_le_left _ _) hk0.le)
  have hsmall : Y 1 + Y 2 ≤ δ := hb.trans (div_le_self hδ.le (by linarith only [hk]))
  have hδK : K * δ ≤ 1 / 16 := by
    have HH := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 16) hK)).mp (min_le_right ε (1 / (16 * K)))
    nlinarith only [HH]
  obtain ⟨hvalid, _, _, hcore, hstep⟩ := H Y hk2
    ⟨hu, (by linarith only [hw, hb] : Y 1 ≤ δ / (1 + Y 0)).trans hbudget⟩
    ⟨hw, (by linarith only [hu, hb] : Y 2 ≤ δ / (1 + Y 0)).trans hbudget⟩
  let Z := coreReturnState coreRadiusReturnTime Y
  have herror : |Z 0 - Y 0| ≤ 1 / 16 := hcore.2.1.trans (by
    calc
      _ ≤ K * δ / Y 0 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall hK.le) hk0.le
      _ ≤ K * δ := div_le_self (mul_nonneg hK.le hδ.le) (by linarith only [hk])
      _ ≤ _ := hδK)
  have hguard : 31 / 8 ≤ Z 0 := by linarith only [hk, (abs_le.mp herror).1]
  obtain ⟨hT, horbit, _, _, _, herr, hdrop, hwall, _, _⟩ := hstep hguard
  have hnext (i : Fin 2) : 0 < G Y i.succ ∧ G Y i.succ ≤ Y i.succ := by
    refine ⟨(hwall i).2.1, (hwall i).2.2.1.trans ?_⟩
    have hpos : 0 ≤ Y i.succ := by
      fin_cases i
      · exact hu.le
      · exact hw.le
    exact (hwall i).2.2.2.trans ((mul_le_mul_of_nonneg_right
      (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) hk0.le)) hpos).trans_eq (one_mul _))
  have hdec : Z 1 + Z 2 ≤ Real.exp (-c / Y 0) * (Y 1 + Y 2) := by
    simpa only [Z, mul_add] using! add_le_add (hwall 0).2.2.2 (hwall 1).2.2.2
  have hconn : G Y 1 + G Y 2 ≤ Z 1 + Z 2 := add_le_add (hwall 0).2.2.1 (hwall 1).2.2.1
  have hpaid : (Y 1 + Y 2) / Y 0 ≤ A * ((Y 1 + Y 2) - (G Y 1 + G Y 2)) := by
    have HL := rpow_div_le_core_loss hb0.le
      (add_nonneg (hwall 0).1.le (hwall 1).1.le) hk2 hc zero_lt_one hdec
    simp only [Real.rpow_one, one_mul] at HL
    exact HL.trans (mul_le_mul_of_nonneg_left (sub_le_sub_left hconn _) hA.le)
  refine ⟨hvalid, hT, horbit, hdrop, hnext, herr.trans ?_⟩
  calc
    _ = K * ((Y 1 + Y 2) / Y 0) := by ring
    _ ≤ K * (A * ((Y 1 + Y 2) - (G Y 1 + G Y 2))) := mul_le_mul_of_nonneg_left hpaid hK.le
    _ = (K * A) * ((Y 1 + Y 2) - (G Y 1 + G Y 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _)
      (sub_nonneg.mpr (add_le_add (hnext 0).2 (hnext 1).2))

end BianchiIX
