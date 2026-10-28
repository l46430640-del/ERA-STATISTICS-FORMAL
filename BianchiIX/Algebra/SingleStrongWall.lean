import BianchiIX.Algebra.StablePhaseCorrection

noncomputable section

namespace BianchiIX

def singleStrongInvariant (m u : ℝ) : ℝ := (1 + m ^ 2 + u ^ 2) / m

def singleStrongUpperRoot (I : ℝ) : ℝ := (I + Real.sqrt (I ^ 2 - 4)) / 2

def singleStrongLowerRoot (I : ℝ) : ℝ := (I - Real.sqrt (I ^ 2 - 4)) / 2

def singleStrongPhase (m u : ℝ) : ℝ := 2 / (singleStrongUpperRoot (singleStrongInvariant m u) - 1)

theorem singleStrongInvariant_defect {m u : ℝ} (hm : m ≠ 0) :
    singleStrongInvariant m u - 2 = ((m - 1) ^ 2 + u ^ 2) / m := by
  unfold singleStrongInvariant
  field_simp
  ring

theorem singleStrongInvariant_gt_two {m u : ℝ} (hm : 0 < m) (hn : m ≠ 1 ∨ u ≠ 0) :
    2 < singleStrongInvariant m u := by
  have hnum : 0 < (m - 1) ^ 2 + u ^ 2 := by
    rcases hn with h | h
    · have H := sq_pos_of_ne_zero (sub_ne_zero.mpr h)
      nlinarith only [H, sq_nonneg u]
    · have H := sq_pos_of_ne_zero h
      nlinarith only [H, sq_nonneg (m - 1)]
  have H := singleStrongInvariant_defect (u := u) hm.ne'
  linarith only [H, div_pos hnum hm]

theorem singleStrongRoot_relations {I : ℝ} (hI : 2 < I) :
    1 < singleStrongUpperRoot I ∧ 0 < singleStrongLowerRoot I ∧ singleStrongLowerRoot I < 1 ∧
      singleStrongLowerRoot I + singleStrongUpperRoot I = I ∧
      singleStrongLowerRoot I * singleStrongUpperRoot I = 1 := by
  have hD : 0 < I ^ 2 - 4 := by nlinarith
  have hS := Real.sqrt_nonneg (I ^ 2 - 4)
  have hsq := Real.sq_sqrt hD.le
  have hSI : Real.sqrt (I ^ 2 - 4) < I := by nlinarith
  have hSlo : I - 2 < Real.sqrt (I ^ 2 - 4) := by nlinarith
  dsimp [singleStrongLowerRoot, singleStrongUpperRoot]
  refine ⟨by linarith, by linarith, by linarith, by ring, ?_⟩
  nlinarith only [hsq]

theorem singleStrongUpperRoot_unique {I q : ℝ} (hI : 2 < I) (hq : 1 < q)
    (hpoly : q ^ 2 - I * q + 1 = 0) : q = singleStrongUpperRoot I := by
  obtain ⟨_, _, hl, hsum, hprod⟩ := singleStrongRoot_relations hI
  have hfactor : (q - singleStrongLowerRoot I) * (q - singleStrongUpperRoot I) = 0 := by
    nlinarith only [hpoly, hprod, congrArg (fun z : ℝ => z * q) hsum]
  rcases mul_eq_zero.mp hfactor with h | h
  · have H := sub_eq_zero.mp h
    linarith
  · exact sub_eq_zero.mp h

theorem singleStrongInvariant_factorization {m u : ℝ} (hm : 0 < m)
    (hI : 2 < singleStrongInvariant m u) :
    u ^ 2 = (m - singleStrongLowerRoot (singleStrongInvariant m u)) *
      (singleStrongUpperRoot (singleStrongInvariant m u) - m) := by
  obtain ⟨_, _, _, hsum, hprod⟩ := singleStrongRoot_relations hI
  have hid : singleStrongInvariant m u * m = 1 + m ^ 2 + u ^ 2 := by
    unfold singleStrongInvariant
    field_simp
  nlinarith only [hid, hprod, congrArg (fun z : ℝ => z * m) hsum]

theorem singleStrongUpperRoot_ge {m u : ℝ} (hm : 1 < m) :
    m ≤ singleStrongUpperRoot (singleStrongInvariant m u) := by
  have hm0 : 0 < m := by linarith
  have hI := singleStrongInvariant_gt_two (u := u) hm0 (Or.inl (ne_of_gt hm))
  have hl := (singleStrongRoot_relations hI).2.2.1
  have H := singleStrongInvariant_factorization hm0 hI
  have hpos : 0 < m - singleStrongLowerRoot (singleStrongInvariant m u) := by linarith
  have hnonneg : 0 ≤ singleStrongUpperRoot (singleStrongInvariant m u) - m :=
    nonneg_of_mul_nonneg_left (by rw [mul_comm, ← H]; positivity) hpos
  linarith

theorem singleStrongRoot_bracket {m u : ℝ} (hm : 0 < m) (hu : u ≠ 0) :
    singleStrongLowerRoot (singleStrongInvariant m u) < m ∧
      m < singleStrongUpperRoot (singleStrongInvariant m u) := by
  have hI := singleStrongInvariant_gt_two hm (Or.inr hu)
  obtain ⟨hupper, _, hlower, _, _⟩ := singleStrongRoot_relations hI
  have H := singleStrongInvariant_factorization hm hI
  have hpos : 0 < (m - singleStrongLowerRoot (singleStrongInvariant m u)) *
      (singleStrongUpperRoot (singleStrongInvariant m u) - m) := by
    rw [← H]
    exact sq_pos_of_ne_zero hu
  rcases mul_pos_iff.mp hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · constructor <;> linarith
  · exfalso
    linarith

theorem singleStrongUpperRoot_zero {m : ℝ} (hm : 1 < m) :
    singleStrongUpperRoot (singleStrongInvariant m 0) = m := by
  have hm0 : 0 < m := by linarith
  apply Eq.symm
  apply singleStrongUpperRoot_unique (singleStrongInvariant_gt_two hm0 (Or.inl (ne_of_gt hm))) hm
  dsimp [singleStrongInvariant]
  field_simp
  ring

theorem contDiffAt_singleStrongInvariant (n : WithTop ℕ∞) {y : Fin 3 → ℝ} (hm : y 0 ≠ 0) :
    ContDiffAt ℝ n (fun z : Fin 3 → ℝ => singleStrongInvariant (z 0) (z 1)) y := by
  unfold singleStrongInvariant
  fun_prop

theorem hasDerivAt_singleStrongInvariant {m u : ℝ → ℝ} {a t : ℝ}
    (hm : HasDerivAt m (a * (m t * u t ^ 2)) t)
    (hu : HasDerivAt u (a * ((1 - m t ^ 2 + u t ^ 2) / 2 * u t)) t) (hn : m t ≠ 0) :
    HasDerivAt (fun s => singleStrongInvariant (m s) (u s)) 0 t := by
  apply ((((hm.pow 2).const_add 1).add (hu.pow 2)).div hm hn).congr_deriv
  dsimp
  field_simp
  ring

end BianchiIX
