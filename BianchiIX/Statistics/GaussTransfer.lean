import BianchiIX.Statistics.GaussMeasure

/-! Exact inverse-branch identities for the invariant Gauss density. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace BianchiIX

theorem gaussWeight_inverse_jacobian {a x : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) :
    gaussWeight (gaussInv a x) * |deriv (gaussInv a) x| =
      (1 / Real.log 2) * (1 / (a + x) - 1 / (a + 1 + x)) := by
  have hax : 0 < a + x := by linarith
  have hax1 : 0 < a + 1 + x := by linarith
  rw [(hasDerivAt_gaussInv ha hx).deriv]
  simp only [gaussWeight, gaussInv, abs_div, abs_neg, abs_one, abs_pow, abs_of_pos hax]
  field_simp
  ring

theorem gaussWeight_transfer_sum {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    (∑ j ∈ Finset.range N,
      gaussWeight (gaussInv ((j : ℝ) + 1) x) * |deriv (gaussInv ((j : ℝ) + 1)) x|) =
      (1 / Real.log 2) * (1 / (1 + x) - 1 / ((N : ℝ) + 1 + x)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih,
      gaussWeight_inverse_jacobian (by linarith [Nat.cast_nonneg (α := ℝ) N]) hx]
    push_cast
    ring

theorem gaussWeight_transfer_hasSum {x : ℝ} (hx : 0 ≤ x) :
    HasSum (fun j : ℕ =>
      gaussWeight (gaussInv ((j : ℝ) + 1) x) * |deriv (gaussInv ((j : ℝ) + 1)) x|) (gaussWeight x) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun j =>
    mul_nonneg (gaussWeight_pos
      (gaussInv_pos (by linarith [Nat.cast_nonneg (α := ℝ) j]) hx).le).le (abs_nonneg _)) _).mpr
  simp_rw [gaussWeight_transfer_sum hx]
  have hN : Tendsto (fun N : ℕ => (N : ℝ) + (1 + x)) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 + x) tendsto_natCast_atTop_atTop
  have hinv := tendsto_inv_atTop_zero.comp hN
  have hlim := ((tendsto_const_nhds (x := (1 / (1 + x) : ℝ))).sub hinv).const_mul (1 / Real.log 2)
  simpa only [Function.comp_def, one_div, add_assoc, sub_zero, gaussWeight,
    mul_inv_rev, mul_comm] using hlim

theorem gaussWeight_transfer_tsum {x : ℝ} (hx : 0 ≤ x) :
    (∑' j : ℕ, ENNReal.ofReal
      (gaussWeight (gaussInv ((j : ℝ) + 1) x) * |deriv (gaussInv ((j : ℝ) + 1)) x|)) =
      ENNReal.ofReal (gaussWeight x) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j =>
    mul_nonneg (gaussWeight_pos
      (gaussInv_pos (by linarith [Nat.cast_nonneg (α := ℝ) j]) hx).le).le (abs_nonneg _))
    (gaussWeight_transfer_hasSum hx).summable, (gaussWeight_transfer_hasSum hx).tsum_eq]

theorem gaussMeasure_inverse_image {a : ℝ} (ha : 1 ≤ a) {A : Set ℝ}
    (hA : MeasurableSet A) (hsub : A ⊆ Ioo (0 : ℝ) 1) :
    gaussMeasure (gaussInv a '' A) = ∫⁻ x in A,
      ENNReal.ofReal (gaussWeight (gaussInv a x) * |deriv (gaussInv a) x|) := by
  have himg : gaussInv a '' A ⊆ Ioo (0 : ℝ) 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have ht := hsub hx
    refine ⟨gaussInv_pos ha ht.1.le, ?_⟩
    exact (div_lt_one (by linarith [ht.1] : 0 < a + x)).mpr (by linarith [ht.1])
  rw [gaussMeasure_apply ((measurableEmbedding_gaussInv a).measurableSet_image.mpr hA) himg]
  rw [lintegral_image_eq_lintegral_abs_deriv_mul hA
    (fun x hx => (hasDerivAt_gaussInv ha (hsub hx).1.le).differentiableAt.hasDerivAt.hasDerivWithinAt)
    (measurableEmbedding_gaussInv a).injective.injOn]
  apply lintegral_congr
  intro x
  rw [mul_comm, ← ENNReal.ofReal_mul' (abs_nonneg _)]

theorem gaussMeasure_inverse_sum {A : Set ℝ}
    (hA : MeasurableSet A) (hsub : A ⊆ Ioo (0 : ℝ) 1) :
    (∑' j : ℕ, gaussMeasure (gaussInv ((j : ℝ) + 1) '' A)) = gaussMeasure A := by
  have heq (j : ℕ) := gaussMeasure_inverse_image
    (a := (j : ℝ) + 1) (by linarith [Nat.cast_nonneg (α := ℝ) j]) hA hsub
  simp_rw [heq]
  rw [← lintegral_tsum, gaussMeasure_apply hA hsub]
  · apply lintegral_congr_ae
    apply ae_restrict_of_forall_mem hA
    exact fun x hx => gaussWeight_transfer_tsum (hsub hx).1.le
  · intro j
    have hm : Measurable (fun x : ℝ => ENNReal.ofReal
        ((1 / Real.log 2) * (1 / ((j : ℝ) + 1 + x) - 1 / ((j : ℝ) + 1 + 1 + x)))) :=
      (measurable_const.mul
        ((measurable_const.div (measurable_const.add measurable_id)).sub
          (measurable_const.div (measurable_const.add measurable_id)))).ennreal_ofReal
    apply hm.aemeasurable.congr
    apply ae_restrict_of_forall_mem hA
    intro x hx
    dsimp only
    rw [gaussWeight_inverse_jacobian (by linarith [Nat.cast_nonneg (α := ℝ) j]) (hsub hx).1.le]

end BianchiIX
