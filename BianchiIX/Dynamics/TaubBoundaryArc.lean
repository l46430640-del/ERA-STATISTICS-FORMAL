import BianchiIX.Dynamics.SingleStrongChart

noncomputable section

namespace BianchiIX

open Set

def taubBoundaryArc (q : ℝ) : NormalizedState := ![-q, 0, Real.sqrt (1 - q ^ 2), 0, 0]

theorem continuous_taubBoundaryArc : Continuous taubBoundaryArc := by
  unfold taubBoundaryArc
  fun_prop

theorem taubBoundaryArc_constraint {q : ℝ} (hq : q ∈ Icc (-1) 1) :
    stateConstraint (taubBoundaryArc q) = 1 := by
  have hsq : 0 ≤ 1 - q ^ 2 := by nlinarith [hq.1, hq.2]
  simp [stateConstraint, taubBoundaryArc, constraint, shearSq, curvature, Real.sq_sqrt hsq]

theorem taubBoundaryArc_wall_pos {q : ℝ} (hq : q ∈ Ioo (-1) 1) :
    0 < taubBoundaryArc q 2 :=
  Real.sqrt_pos.mpr (by nlinarith [hq.1, hq.2])

theorem taubBoundaryArc_field {q : ℝ} (hq : q ∈ Icc (-1) 1) :
    normalizedField (taubBoundaryArc q) =
      ![-((q + 2) * (1 - q ^ 2)), 0, -q * (q + 2) * Real.sqrt (1 - q ^ 2), 0, 0] := by
  have hsq : 0 ≤ 1 - q ^ 2 := by nlinarith [hq.1, hq.2]
  ext j
  fin_cases j <;>
    simp [normalizedField, taubBoundaryArc, shearPlus, shearMinus, rateOne, rateTwo, rateThree,
      shearSq, curvature, Real.sq_sqrt hsq] <;> ring

/-- Every existing signed segment stays on the open single-wall arc, with strictly positive active wall. -/
theorem taubBoundaryArc_flow {q t : ℝ} (hq : q ∈ Ioo (-1) 1)
    (ht : t ∈ normalizedMaxDomain (taubBoundaryArc q) 0) :
    -normalizedMaxCurve (taubBoundaryArc q) 0 t 0 ∈ Ioo (-1) 1 ∧
      normalizedMaxCurve (taubBoundaryArc q) 0 t =
        taubBoundaryArc (-normalizedMaxCurve (taubBoundaryArc q) 0 t 0) := by
  let y := normalizedMaxCurve (taubBoundaryArc q) 0 t
  obtain ⟨h3, h4⟩ := normalized_single_strong_zeros (x := taubBoundaryArc q) rfl rfl ht
  change y 3 = 0 at h3
  change y 4 = 0 at h4
  have h1 : y 1 = 0 := by
    rw [show y 1 = normalizedMaxCurve (taubBoundaryArc q) 0 t 1 from rfl,
      normalized_single_strong_shear rfl rfl ht]
    simp only [taubBoundaryArc, Matrix.cons_val_one, Matrix.cons_val_zero, zero_mul]
  have hn : 0 < y 2 := by
    have H := normalized_wall_pos (convex_normalizedMaxDomain (taubBoundaryArc q) 0)
      (isOpen_normalizedMaxDomain (taubBoundaryArc q) 0)
      (fun _ hs => hasDerivAt_normalizedMaxCurve hs)
      (initial_mem_normalizedMaxDomain (taubBoundaryArc q) 0) ht 0
    apply H
    change 0 < normalizedMaxCurve (taubBoundaryArc q) 0 0 2
    rw [normalizedMaxCurve_initial]
    exact taubBoundaryArc_wall_pos hq
  have hc := (normalizedMaxCurve_constraint ht).trans (taubBoundaryArc_constraint (Ioo_subset_Icc_self hq))
  change stateConstraint y = 1 at hc
  have he : y 0 ^ 2 + y 2 ^ 2 = 1 := by
    simpa only [stateConstraint, constraint, shearSq, curvature,
      h1, h3, h4, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, add_zero, sub_zero] using hc
  have hμ : -y 0 ∈ Ioo (-1) 1 := by
    constructor <;> nlinarith [sq_pos_of_pos hn, sq_nonneg (y 0 - 1), sq_nonneg (y 0 + 1)]
  refine ⟨hμ, ?_⟩
  have hsqrt : Real.sqrt (1 - y 0 ^ 2) = y 2 := by
    rw [show 1 - y 0 ^ 2 = y 2 ^ 2 by linarith only [he], Real.sqrt_sq hn.le]
  change y = taubBoundaryArc (-y 0)
  ext j
  fin_cases j <;> simp [taubBoundaryArc, h1, h3, h4, hsqrt]

theorem hasDerivAt_taubBoundaryArc_parameter {q t : ℝ} (hq : q ∈ Ioo (-1) 1)
    (ht : t ∈ normalizedMaxDomain (taubBoundaryArc q) 0) :
    HasDerivAt (fun s => -normalizedMaxCurve (taubBoundaryArc q) 0 s 0)
      ((-normalizedMaxCurve (taubBoundaryArc q) 0 t 0 + 2) *
        (1 - (-normalizedMaxCurve (taubBoundaryArc q) 0 t 0) ^ 2)) t := by
  have H := (hasDerivAt_pi.mp (hasDerivAt_normalizedMaxCurve ht) 0).neg
  obtain ⟨hμ, he⟩ := taubBoundaryArc_flow hq ht
  rw [he, taubBoundaryArc_field (Ioo_subset_Icc_self hμ)] at H
  simpa only [Pi.neg_apply, Matrix.cons_val_zero, neg_neg] using! H

theorem hasDerivAt_taubBoundaryArc_log_wall {q t : ℝ} (hq : q ∈ Ioo (-1) 1)
    (ht : t ∈ normalizedMaxDomain (taubBoundaryArc q) 0) :
    HasDerivAt (fun s => Real.log (normalizedMaxCurve (taubBoundaryArc q) 0 s 2))
      (-(-normalizedMaxCurve (taubBoundaryArc q) 0 t 0) *
        (-normalizedMaxCurve (taubBoundaryArc q) 0 t 0 + 2)) t := by
  obtain ⟨hμ, he⟩ := taubBoundaryArc_flow hq ht
  have hn : 0 < normalizedMaxCurve (taubBoundaryArc q) 0 t 2 := by
    rw [he]
    exact taubBoundaryArc_wall_pos hμ
  have hf : normalizedField (normalizedMaxCurve (taubBoundaryArc q) 0 t) 2 =
      -(-normalizedMaxCurve (taubBoundaryArc q) 0 t 0) *
        (-normalizedMaxCurve (taubBoundaryArc q) 0 t 0 + 2) *
          normalizedMaxCurve (taubBoundaryArc q) 0 t 2 := by
    rw [he, taubBoundaryArc_field (Ioo_subset_Icc_self hμ)]
    simp [taubBoundaryArc]
  apply ((hasDerivAt_pi.mp (hasDerivAt_normalizedMaxCurve ht) 2).log hn.ne').congr_deriv
  rw [hf, mul_div_cancel_right₀ _ hn.ne']

end BianchiIX
