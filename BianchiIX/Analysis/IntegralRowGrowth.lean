import BianchiIX.Analysis.ForcedBudgetGrowth

noncomputable section

namespace BianchiIX

open Set MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
theorem signedRowSum_le_sum_abs (A : Matrix ι ι ℝ) (i : ι) :
    signedRowSum A i ≤ ∑ j, |A i j| := by
  rw [← Finset.add_sum_erase Finset.univ (fun j => |A i j|) (Finset.mem_univ i)]
  exact add_le_add (le_abs_self _) le_rfl

/-- The growth factor depends on the integrated row bound, rather than the duration. -/
theorem norm_le_exp_integral_of_forced_rows {f p : ℝ → (ι → ℝ)}
    {A : ℝ → Matrix ι ι ℝ} {σ R : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f ((A t).mulVec (f t) + p t) t)
    (hσ : ContinuousOn σ (Icc a b)) (hσ0 : ∀ t ∈ Icc a b, 0 ≤ σ t)
    (hA : ∀ t ∈ Icc a b, ∀ i, signedRowSum (A t) i ≤ σ t)
    (hR : ContinuousOn R (Icc a b)) (hp : ∀ t ∈ Icc a b, ‖p t‖ ≤ R t) :
    ‖f b‖ ≤ Real.exp (∫ t in a..b, σ t) * (‖f a‖ + ∫ t in a..b, R t) := by
  let S : ℝ → ℝ := fun t => σ (projIcc a b hab t)
  let E : ℝ → ℝ := fun t => -(∫ r in a..t, S r)
  have hS : Continuous S := hσ.domRestrict.comp continuous_projIcc
  have hSe (t : ℝ) (ht : t ∈ Icc a b) : S t = σ t := by simp only [S, projIcc_of_mem hab ht]
  have hEe (t : ℝ) (ht : t ∈ Icc a b) : E t = -(∫ r in a..t, σ r) := by
    dsimp only [E]
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    exact hSe r ⟨(uIcc_of_le ht.1 ▸ hr).1, (uIcc_of_le ht.1 ▸ hr).2.trans ht.2⟩
  have hE (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt E (-σ t) t := by
    rw [← hSe t ht]
    exact (intervalIntegral.integral_hasDerivAt_right (hS.intervalIntegrable _ _)
      hS.stronglyMeasurable.stronglyMeasurableAtFilter hS.continuousAt).neg
  have hEa (t : ℝ) (ht : t ∈ Icc a b) : E t ≤ E a := by
    rw [hEe t ht]
    simp only [E, intervalIntegral.integral_same, neg_zero]
    exact neg_nonpos.mpr (intervalIntegral.integral_nonneg ht.1
      (fun r hr => hσ0 r ⟨hr.1, hr.2.trans ht.2⟩))
  have H := norm_le_integral_envelope_of_forced_budget hab hf hE
    (fun t ht i => by simpa only [neg_neg] using hA t ht i) hEa hR hp
  rw [hEe b ⟨hab, le_rfl⟩] at H
  simpa only [E, intervalIntegral.integral_same, neg_zero, zero_sub, neg_neg] using H

theorem norm_sub_initial_le_exp_integral_of_forced_rows {f p : ℝ → (ι → ℝ)}
    {A : ℝ → Matrix ι ι ℝ} {σ R : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f ((A t).mulVec (f t) + p t) t)
    (hσ : ContinuousOn σ (Icc a b)) (hσ0 : ∀ t ∈ Icc a b, 0 ≤ σ t)
    (hA : ∀ t ∈ Icc a b, ∀ i, signedRowSum (A t) i ≤ σ t)
    (hR : ContinuousOn R (Icc a b))
    (hp : ∀ t ∈ Icc a b, ‖(A t).mulVec (f a) + p t‖ ≤ R t) :
    ‖f b - f a‖ ≤ Real.exp (∫ t in a..b, σ t) * ∫ t in a..b, R t := by
  have hg (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt (fun s => f s - f a)
      ((A t).mulVec (f t - f a) + ((A t).mulVec (f a) + p t)) t := by
    convert! (hf t ht).sub_const (f a) using 1
    rw [Matrix.mulVec_sub]
    abel
  simpa only [sub_self, norm_zero, zero_add] using
    norm_le_exp_integral_of_forced_rows hab hg hσ hσ0 hA hR hp

end BianchiIX
