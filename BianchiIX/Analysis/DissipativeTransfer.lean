import BianchiIX.Analysis.ForcedBudgetGrowth

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- Integration by parts retains the decaying amplitude in forced transfer. -/
theorem abs_le_of_dissipative_transfer {f c g u u' P Q r : ℝ → ℝ} {a b K κ : ℝ}
    (hK : 0 ≤ K) (hκ : 0 < κ)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (c t * f t + g t) t)
    (hc : ∀ t ∈ Icc a b, c t ≤ 0)
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u' t) t)
    (hdecay : ∀ t ∈ Icc a b, u' t ≤ -κ * u t)
    (hP : ∀ t ∈ Icc a b, HasDerivAt P (r t) t)
    (hQ : ∀ t ∈ Icc a b, HasDerivAt Q (u t * r t) t)
    (hPpos : ∀ t ∈ Icc a b, 0 ≤ P t)
    (hfzero : f a = 0) (hPzero : P a = 0) (hQzero : Q a = 0)
    (hg : ∀ t ∈ Icc a b, |g t| ≤ K * u t * P t) :
    ∀ t ∈ Icc a b, |f t| ≤ (K / κ) * (Q t - u t * P t) := by
  have hB (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun s => (K / κ) * (Q s - u s * P s)) (-(K / κ) * u' t * P t) t := by
    convert! ((hQ t ht).sub ((hu t ht).mul (hP t ht))).const_mul (K / κ) using 1
    ring
  apply abs_le_of_forced_nonpos hf hc hB (by simp [hfzero, hPzero, hQzero])
  intro t ht
  have Hd : κ * u t ≤ -u' t := by linarith only [hdecay t ht]
  calc
    |g t| ≤ K * u t * P t := hg t ht
    _ = (K / κ) * (κ * u t) * P t := by field_simp
    _ ≤ (K / κ) * (-u' t) * P t :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hd (div_nonneg hK hκ.le)) (hPpos t ht)
    _ = -(K / κ) * u' t * P t := by ring

theorem abs_le_integral_of_dissipative_transfer {f c g u u' r : ℝ → ℝ} {a b K κ : ℝ}
    (hab : a ≤ b) (hK : 0 ≤ K) (hκ : 0 < κ)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (c t * f t + g t) t)
    (hc : ∀ t ∈ Icc a b, c t ≤ 0)
    (hu : ∀ t ∈ Icc a b, HasDerivAt u (u' t) t)
    (hdecay : ∀ t ∈ Icc a b, u' t ≤ -κ * u t)
    (hu0 : ∀ t ∈ Icc a b, 0 ≤ u t) (hr : ContinuousOn r (Icc a b))
    (hr0 : ∀ t ∈ Icc a b, 0 ≤ r t) (hfzero : f a = 0)
    (hg : ∀ t ∈ Icc a b, |g t| ≤ K * u t * ∫ s in a..t, r s) :
    |f b| ≤ (K / κ) * ((∫ t in a..b, u t * r t) - u b * ∫ t in a..b, r t) ∧
      |f b| ≤ (K / κ) * ∫ t in a..b, u t * r t := by
  let R : ℝ → ℝ := fun t => r (projIcc a b hab t)
  let U : ℝ → ℝ := fun t => u (projIcc a b hab t)
  let P : ℝ → ℝ := fun t => ∫ s in a..t, R s
  let Q : ℝ → ℝ := fun t => ∫ s in a..t, U s * R s
  have hR : Continuous R := hr.domRestrict.comp continuous_projIcc
  have hU : Continuous U := (HasDerivAt.continuousOn hu).domRestrict.comp continuous_projIcc
  have heR (t : ℝ) (ht : t ∈ Icc a b) : R t = r t := by simp only [R, projIcc_of_mem hab ht]
  have heU (t : ℝ) (ht : t ∈ Icc a b) : U t = u t := by simp only [U, projIcc_of_mem hab ht]
  have heP (t : ℝ) (ht : t ∈ Icc a b) : P t = ∫ s in a..t, r s := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact heR s ((Icc_subset_Icc_right ht.2) (uIcc_of_le ht.1 ▸ hs))
  have heQ : Q b = ∫ t in a..b, u t * r t := by
    apply intervalIntegral.integral_congr
    intro t ht
    change U t * R t = u t * r t
    rw [heU t (uIcc_of_le hab ▸ ht), heR t (uIcc_of_le hab ▸ ht)]
  have hP (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt P (r t) t := by
    rw [← heR t ht]
    exact intervalIntegral.integral_hasDerivAt_right (hR.intervalIntegrable _ _)
      hR.stronglyMeasurable.stronglyMeasurableAtFilter hR.continuousAt
  have hQ (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt Q (u t * r t) t := by
    rw [← heR t ht, ← heU t ht]
    exact intervalIntegral.integral_hasDerivAt_right ((hU.mul hR).intervalIntegrable _ _)
      (hU.mul hR).stronglyMeasurable.stronglyMeasurableAtFilter (hU.mul hR).continuousAt
  have hP0 (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ P t := by
    rw [heP t ht]
    exact intervalIntegral.integral_nonneg ht.1 (fun s hs => hr0 s ⟨hs.1, hs.2.trans ht.2⟩)
  have H := abs_le_of_dissipative_transfer hK hκ hf hc hu hdecay hP hQ hP0 hfzero
    (by simp [P]) (by simp [Q]) (fun t ht => by rw [heP t ht]; exact hg t ht) b ⟨hab, le_rfl⟩
  have H' : |f b| ≤ (K / κ) * Q b := H.trans
    (mul_le_mul_of_nonneg_left (sub_le_self _ (mul_nonneg (hu0 b ⟨hab, le_rfl⟩) (hP0 b ⟨hab, le_rfl⟩)))
      (div_nonneg hK hκ.le))
  rw [heQ, heP b ⟨hab, le_rfl⟩] at H
  rw [heQ] at H'
  exact ⟨H, H'⟩

end BianchiIX
