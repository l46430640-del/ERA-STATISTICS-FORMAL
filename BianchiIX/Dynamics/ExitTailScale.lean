import BianchiIX.Dynamics.ExitTailTube
import BianchiIX.Dynamics.ExitTailGrowth
import BianchiIX.Analysis.ExitTailLength

noncomputable section

namespace BianchiIX

open Set

/-- The D.5 scale yields constants uniform in alpha and in the signed wall ratio on every existing tail prefix. -/
theorem exists_exitTail_scale_bounds {η : ℝ} (hη : 0 < η ∧ η ≤ 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ A ≥ (2 : ℝ), ∃ ε > (0 : ℝ), ∀ α b T : ℝ, ∀ Y : ℝ → ExitTailState,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J → (0 ≤ T ∧ T ≤ exitTailLength η α J) →
      Y 0 0 = 2 + 2 * α → |Y 0 1| + |Y 0 2| ≤ b →
      (∀ s ∈ Icc 0 T, HasDerivAt Y (exitTailField (Real.exp (-s)) (Y s)) s) →
      ∀ r ∈ Icc 0 T, exitTailRegion α b A (80 * A) (Y r) ∧
        (∀ i : Fin 2, Y r i.succ = Y 0 i.succ * exitTailMultiplier Y i r ∧
          2 / A ≤ exitTailMultiplier Y i r ∧ exitTailMultiplier Y i r ≤ A / 2) ∧
        |Y r 1| + |Y r 2| ≤ A * b / 2 ∧ |Y r 0 - Y 0 0| ≤ 40 * A * b ∧
        2 + α < Y r 0 ∧ |Y r 1| ≤ Real.exp (-r) / 2 := by
  let K := Real.log (1 / η) + J * Real.exp (-1)
  let Q := 1 + Real.log (1 / η) + Real.exp (-1)
  have he : 0 ≤ Real.log (1 / η) := Real.log_nonneg ((le_div_iff₀ hη.1).mpr (by linarith only [hη.2]))
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  obtain ⟨A, hA, ε₀, hε₀, H⟩ := exists_exitTail_uniform_tube_bounds hK
  have hA0 : 0 < A := by linarith only [hA]
  let ε := min (ε₀ / Q) (min (1 / (1000 * A)) (η / A))
  have hε : 0 < ε := lt_min (div_pos hε₀ hQ) (lt_min (by positivity) (div_pos hη.1 hA0))
  have hAε : A * ε ≤ 1 / 1000 := by
    have Hε := (le_div_iff₀ (by positivity : 0 < 1000 * A)).mp
      ((min_le_right _ _).trans (min_le_left _ _) : ε ≤ 1 / (1000 * A))
    nlinarith only [Hε]
  have hAη : A * ε ≤ η := by
    have Hε := (le_div_iff₀ hA0).mp ((min_le_right _ _).trans (min_le_right _ _) : ε ≤ η / A)
    nlinarith only [Hε]
  refine ⟨A, hA, ε, hε, ?_⟩
  intro α b T Y hα hb hsmall hT hR hw hY
  have HB := (exitTail_smallness_budgets hη hα hε.le hJ hsmall).1
  have HbT : b * (1 + T) ≤ ε₀ := by
    have HQ : ε * Q ≤ ε₀ := (le_div_iff₀ hQ).mp (min_le_left _ _)
    change b * (1 + exitTailLength η α J) ≤ ε * Q at HB
    exact (mul_le_mul_of_nonneg_left (add_le_add le_rfl hT.2) hb.le).trans (HB.trans HQ)
  have Hwait := (exitTailLength_weighted_bounds hη hα J).1
  have Hpath := H T α b Y hT.1 ⟨hα.1.le, hα.2⟩ hb HbT
    ((mul_le_mul_of_nonneg_left hT.2 hα.1.le).trans Hwait) hR hw hY
  have hp : α ^ J ≤ α := by
    have Hpow : α ^ (J - 1) ≤ 1 := pow_le_one₀ hα.1.le hα.2
    have heq : α ^ J = α ^ (J - 1) * α := by rw [← pow_succ, Nat.sub_add_cancel hJ]
    rw [heq]
    nlinarith only [mul_le_mul_of_nonneg_right Hpow hα.1.le]
  have hbα : b ≤ ε * α := hsmall.trans (mul_le_mul_of_nonneg_left hp hε.le)
  have hAbα : A * b ≤ α / 1000 := by
    nlinarith only [mul_le_mul_of_nonneg_left hbα hA0.le,
      mul_le_mul_of_nonneg_right hAε hα.1.le]
  have hAbV : A * b ≤ η * α ^ J := by
    nlinarith only [mul_le_mul_of_nonneg_left hsmall hA0.le,
      mul_le_mul_of_nonneg_right hAη (pow_nonneg hα.1.le J)]
  intro r hr
  obtain ⟨hreg, hmult, hsum, hrad⟩ := Hpath r hr
  refine ⟨hreg, hmult, hsum, hrad, ?_, ?_⟩
  · rw [hR] at hrad
    linarith only [(abs_le.mp hrad).1, hAbα, hα.1]
  · have hV : η * α ^ J ≤ Real.exp (-r) := by
      rw [← exp_neg_exitTailLength hη.1 hα.1 J]
      exact Real.exp_le_exp.mpr (neg_le_neg (hr.2.trans hT.2))
    linarith only [hsum, hAbV, hV, abs_nonneg (Y r 2)]

/-- The positive initial walls imply all positive-tail hypotheses along the whole existing prefix. -/
theorem exists_exitTail_positive_scale_bounds {η : ℝ} (hη : 0 < η ∧ η ≤ 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ A ≥ (2 : ℝ), ∃ ε > (0 : ℝ), ∀ α b T : ℝ, ∀ Y : ℝ → ExitTailState,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J → (0 ≤ T ∧ T ≤ exitTailLength η α J) →
      Y 0 0 = 2 + 2 * α → (0 ≤ Y 0 1 ∧ 0 ≤ Y 0 2) → Y 0 1 + Y 0 2 ≤ b →
      (∀ s ∈ Icc 0 T, HasDerivAt Y (exitTailField (Real.exp (-s)) (Y s)) s) →
      AntitoneOn (fun r => Y r 0) (Icc 0 T) ∧
      ∀ r ∈ Icc 0 T, (2 + α < Y r 0 ∧ Y r 0 ≤ 2 + 2 * α) ∧
        (0 ≤ Y r 1 ∧ Y r 1 ≤ Real.exp (-r) / 2) ∧
        (0 ≤ Y r 2 ∧ Y r 2 ≤ Y 0 2 * Real.exp (α / (1 + α) * r)) ∧
        Y r 1 + Y r 2 ≤ A * b / 2 ∧ |Y r 0 - Y 0 0| ≤ 40 * A * b := by
  obtain ⟨A, hA, ε, hε, H⟩ := exists_exitTail_scale_bounds hη hJ
  refine ⟨A, hA, ε, hε, ?_⟩
  intro α b T Y hα hb hsmall hT hR hpos hsum hY
  have hsumabs : |Y 0 1| + |Y 0 2| ≤ b := by
    simpa only [abs_of_nonneg hpos.1, abs_of_nonneg hpos.2] using hsum
  have HP := H α b T Y hα hb hsmall hT hR hsumabs hY
  have hwall (r : ℝ) (hr : r ∈ Icc 0 T) : 0 ≤ Y r 1 ∧ 0 ≤ Y r 2 := by
    have h0 := ((HP r hr).2.1 0).1
    have h1 := ((HP r hr).2.1 1).1
    change Y r 1 = Y 0 1 * exitTailMultiplier Y 0 r at h0
    change Y r 2 = Y 0 2 * exitTailMultiplier Y 1 r at h1
    rw [h0, h1]
    exact ⟨mul_nonneg hpos.1 (Real.exp_pos _).le, mul_nonneg hpos.2 (Real.exp_pos _).le⟩
  have HG := exitTail_positive_growth hT.1 hα.1.le hR.le hY (fun r hr => ?_)
  · refine ⟨HG.1, ?_⟩
    intro r hr
    have Hr := HP r hr
    have hp := hwall r hr
    refine ⟨⟨Hr.2.2.2.2.1, (HG.1 ⟨le_rfl, hT.1⟩ hr hr.1).trans hR.le⟩,
      ⟨hp.1, ?_⟩, ⟨hp.2, ?_⟩, ?_, Hr.2.2.2.1⟩
    · simpa only [abs_of_nonneg hp.1] using Hr.2.2.2.2.2
    · simpa only [sub_zero] using HG.2 r hr
    · simpa only [abs_of_nonneg hp.1, abs_of_nonneg hp.2] using Hr.2.2.1
  · have Hr := HP r hr
    have hp := hwall r hr
    have hv : 0 ≤ Real.exp (-r) ∧ Real.exp (-r) ≤ 1 :=
      ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr.1)⟩
    refine ⟨Hr.1.1.1, hv, ⟨hp.1, ?_⟩, hp.2⟩
    have Hsep := Hr.2.2.2.2.2
    rw [abs_of_nonneg hp.1] at Hsep
    linarith only [Hsep, hv.1]

end BianchiIX
