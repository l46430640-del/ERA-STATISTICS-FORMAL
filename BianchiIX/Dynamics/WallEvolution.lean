import BianchiIX.Dynamics.Normalized
import BianchiIX.Algebra.SectionBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem homogeneous_solution_eq_exp_integral {I : Set ℝ} (hI : Convex ℝ I) (hopen : IsOpen I)
    {f a : ℝ → ℝ} (ha : ContinuousOn a I)
    (hf : ∀ t ∈ I, HasDerivAt f (a t * f t) t) {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) :
    f t = f t₀ * Real.exp (∫ u in t₀..t, a u) := by
  let P : ℝ → ℝ := fun v => ∫ u in t₀..v, a u
  have hP (v : ℝ) (hv : v ∈ I) : HasDerivAt P (a v) v :=
    intervalIntegral.integral_hasDerivAt_right
      (ha.mono (hI.ordConnected.uIcc_subset ht₀ hv)).intervalIntegrable
      (ContinuousOn.stronglyMeasurableAtFilter hopen ha v hv)
      (ha.continuousAt (hopen.mem_nhds hv))
  have hF (v : ℝ) (hv : v ∈ I) :
      HasDerivAt (fun u => f u * Real.exp (-P u)) 0 v := by
    convert! (hf v hv).mul (hP v hv).neg.exp using 1
    ring
  have H := hI.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v hv => (hF v hv).hasDerivWithinAt) (C := 0) (fun _ _ => by simp) ht₀ ht
  have heq : f t * Real.exp (-P t) = f t₀ := by
    simpa [P, sub_eq_zero] using H
  calc
    f t = (f t * Real.exp (-P t)) * Real.exp (P t) := by
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ = f t₀ * Real.exp (P t) := by rw [heq]

def wallValue (i : Fin 3) (x : NormalizedState) : ℝ := x (i.addNat 2)

def wallRate (i : Fin 3) (x : NormalizedState) : ℝ :=
  ![rateOne (x 0) (x 1), rateTwo (x 0) (x 1), rateThree (x 0) (x 1)] i

theorem continuous_wallRate (i : Fin 3) : Continuous (wallRate i) := by
  change Continuous (fun x => wallRate i x)
  fin_cases i <;> dsimp [wallRate, rateOne, rateTwo, rateThree, shearSq] <;> fun_prop

theorem wallRate_le_one (i : Fin 3) (x : NormalizedState) : wallRate i x ≤ 1 := by
  have H := wall_rates_le_one (x 0) (x 1)
  fin_cases i
  · exact H.1
  · exact H.2.1
  · exact H.2.2

theorem hasDerivAt_wallValue {α : ℝ → NormalizedState} {t : ℝ}
    (hα : HasDerivAt α (normalizedField (α t)) t) (i : Fin 3) :
    HasDerivAt (fun u => wallValue i (α u)) (wallRate i (α t) * wallValue i (α t)) t := by
  have H := hasDerivAt_pi.mp hα (i.addNat 2)
  fin_cases i <;> exact H

theorem normalized_wall_formula {I : Set ℝ} (hI : Convex ℝ I) (hopen : IsOpen I)
    {α : ℝ → NormalizedState} (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) (i : Fin 3) :
    wallValue i (α t) = wallValue i (α t₀) * Real.exp (∫ u in t₀..t, wallRate i (α u)) :=
  homogeneous_solution_eq_exp_integral hI hopen
    ((continuous_wallRate i).comp_continuousOn (HasDerivAt.continuousOn hα))
    (fun u hu => hasDerivAt_wallValue (hα u hu) i) ht₀ ht

theorem normalized_wall_pos {I : Set ℝ} (hI : Convex ℝ I) (hopen : IsOpen I)
    {α : ℝ → NormalizedState} (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) (i : Fin 3) (hpos : 0 < wallValue i (α t₀)) :
    0 < wallValue i (α t) := by
  rw [normalized_wall_formula hI hopen hα ht₀ ht i]
  exact mul_pos hpos (Real.exp_pos _)

theorem normalized_positive_walls_invariant {I : Set ℝ} (hI : Convex ℝ I) (hopen : IsOpen I)
    {α : ℝ → NormalizedState} (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) (hpos : positiveWalls (α t₀)) :
    positiveWalls (α t) :=
  ⟨normalized_wall_pos hI hopen hα ht₀ ht 0 hpos.1,
    normalized_wall_pos hI hopen hα ht₀ ht 1 hpos.2.1,
    normalized_wall_pos hI hopen hα ht₀ ht 2 hpos.2.2⟩

theorem normalized_wall_growth {I : Set ℝ} (hI : Convex ℝ I) (hopen : IsOpen I)
    {α : ℝ → NormalizedState} (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) (htt : t₀ ≤ t)
    (i : Fin 3) (hpos : 0 ≤ wallValue i (α t₀)) :
    wallValue i (α t) ≤ wallValue i (α t₀) * Real.exp (t - t₀) := by
  have hc : ContinuousOn (fun u => wallRate i (α u)) I :=
    (continuous_wallRate i).comp_continuousOn (HasDerivAt.continuousOn hα)
  have hi : IntervalIntegrable (fun u => wallRate i (α u)) volume t₀ t :=
    (hc.mono (hI.ordConnected.uIcc_subset ht₀ ht)).intervalIntegrable
  have H : (∫ u in t₀..t, wallRate i (α u)) ≤ t - t₀ := by
    have H := intervalIntegral.integral_mono_on htt hi (intervalIntegrable_const (c := (1 : ℝ)))
      (fun u _ => wallRate_le_one i (α u))
    simpa using H
  rw [normalized_wall_formula hI hopen hα ht₀ ht i]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr H) hpos

theorem normalizedState_norm_bound {x : NormalizedState} {M : ℝ}
    (hpos : positiveWalls x) (hcon : stateConstraint x = 1)
    (hwall : ∀ i : Fin 3, wallValue i x ≤ M) : ‖x‖ ≤ 1 + 3 * M := by
  have hM : 0 ≤ M := (le_of_lt hpos.1).trans (hwall 0)
  have hQ := (abs_le.mp (curvature_abs_le_sum_sq hpos.1.le hpos.2.1.le hpos.2.2.le)).1
  have hsum : x 2 + x 3 + x 4 ≤ 3 * M := by
    have h₁ := hwall 0
    have h₂ := hwall 1
    have h₃ := hwall 2
    change x 2 ≤ M at h₁
    change x 3 ≤ M at h₂
    change x 4 ≤ M at h₃
    linarith
  have hsum2 := pow_le_pow_left₀ (by linarith [hpos.1, hpos.2.1, hpos.2.2] : 0 ≤ x 2 + x 3 + x 4) hsum 2
  have hconstraint : x 0 ^ 2 + x 1 ^ 2 + curvature (x 2) (x 3) (x 4) = 1 := hcon
  have hS : x 0 ^ 2 + x 1 ^ 2 ≤ 1 + 9 * M ^ 2 := by nlinarith
  have hR : 0 ≤ 1 + 3 * M := by positivity
  have h₀ : |x 0| ≤ 1 + 3 * M := by
    apply (sq_le_sq₀ (abs_nonneg _) hR).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (x 1)]
  have h₁ : |x 1| ≤ 1 + 3 * M := by
    apply (sq_le_sq₀ (abs_nonneg _) hR).mp
    rw [sq_abs]
    nlinarith [sq_nonneg (x 0)]
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  fin_cases i
  · exact h₀
  · exact h₁
  · have H := hwall 0
    change x 2 ≤ M at H
    change |x 2| ≤ 1 + 3 * M
    rw [abs_of_pos hpos.1]
    linarith
  · have H := hwall 1
    change x 3 ≤ M at H
    change |x 3| ≤ 1 + 3 * M
    rw [abs_of_pos hpos.2.1]
    linarith
  · have H := hwall 2
    change x 4 ≤ M at H
    change |x 4| ≤ 1 + 3 * M
    rw [abs_of_pos hpos.2.2]
    linarith

theorem normalized_forward_bound {I : Set ℝ} (hI : Convex ℝ I) (hopen : IsOpen I)
    {α : ℝ → NormalizedState} (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    {t₀ t M : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) (htt : t₀ ≤ t)
    (hpos : positiveWalls (α t₀)) (hcon : stateConstraint (α t₀) = 1)
    (hwall : ∀ i : Fin 3, wallValue i (α t₀) ≤ M) :
    ‖α t‖ ≤ 1 + 3 * M * Real.exp (t - t₀) := by
  have hposall := normalized_positive_walls_invariant hI hopen hα ht₀ ht hpos
  have hp (i : Fin 3) : 0 ≤ wallValue i (α t₀) := by
    fin_cases i
    · exact hpos.1.le
    · exact hpos.2.1.le
    · exact hpos.2.2.le
  have H := normalizedState_norm_bound hposall
    ((normalized_constraint_constant hI hα ht₀ ht).trans hcon)
    (fun i => (normalized_wall_growth hI hopen hα ht₀ ht htt i (hp i)).trans
      (mul_le_mul_of_nonneg_right (hwall i) (Real.exp_pos _).le))
  simpa only [mul_assoc] using H

end BianchiIX
