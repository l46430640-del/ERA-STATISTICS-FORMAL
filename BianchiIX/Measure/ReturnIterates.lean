import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Data.ENNReal.BigOperators

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

variable {X : Type*}

/-- Exactly the first `n` applications must lie in the actual return domain. -/
def finiteReturnDomain (R : X → X) (D : Set X) (n : ℕ) : Set X :=
  {x | ∀ i < n, R^[i] x ∈ D}

def finiteReturnJacobian (R : X → X) (j : X → ℝ≥0∞) (n : ℕ) (x : X) : ℝ≥0∞ :=
  ∏ i ∈ Finset.range n, j (R^[i] x)

@[simp] theorem finiteReturnDomain_zero (R : X → X) (D : Set X) :
    finiteReturnDomain R D 0 = univ := by simp [finiteReturnDomain]

theorem finiteReturnDomain_succ (R : X → X) (D : Set X) (n : ℕ) :
    finiteReturnDomain R D (n + 1) = finiteReturnDomain R D n ∩ (R^[n]) ⁻¹' D := by
  ext x
  constructor
  · intro hx
    exact ⟨fun i hi => hx i (Nat.lt_succ_of_lt hi), hx n (Nat.lt_succ_self n)⟩
  · rintro ⟨hx, hn⟩ i hi
    obtain hi | rfl := lt_or_eq_of_le (Nat.le_of_lt_succ hi)
    · exact hx i hi
    · exact hn

theorem finiteReturnDomain_antitone (R : X → X) (D : Set X) :
    Antitone (finiteReturnDomain R D) :=
  fun _ _ hmn _ hx i hi => hx i (Nat.lt_of_lt_of_le hi hmn)

theorem injOn_finiteReturnIterate {R : X → X} {D : Set X} (hR : InjOn R D) (n : ℕ) :
    InjOn (R^[n]) (finiteReturnDomain R D n) := by
  induction n with
  | zero => exact fun _ _ _ _ h => h
  | succ n ih =>
    intro x hx y hy heq
    apply ih ((finiteReturnDomain_antitone R D (Nat.le_succ n)) hx)
      ((finiteReturnDomain_antitone R D (Nat.le_succ n)) hy)
    exact hR (hx n (Nat.lt_succ_self n)) (hy n (Nat.lt_succ_self n))
      (by simpa only [Function.iterate_succ_apply'] using heq)

@[simp] theorem finiteReturnJacobian_zero (R : X → X) (j : X → ℝ≥0∞) (x : X) :
    finiteReturnJacobian R j 0 x = 1 := by simp [finiteReturnJacobian]

theorem finiteReturnJacobian_succ (R : X → X) (j : X → ℝ≥0∞) (n : ℕ) (x : X) :
    finiteReturnJacobian R j (n + 1) x = finiteReturnJacobian R j n x * j (R^[n] x) := by
  exact Finset.prod_range_succ _ _

theorem one_le_finiteReturnJacobian {R : X → X} {D : Set X} {j : X → ℝ≥0∞}
    (hj : ∀ x ∈ D, 1 ≤ j x) {n : ℕ} {x : X} (hx : x ∈ finiteReturnDomain R D n) :
    1 ≤ finiteReturnJacobian R j n x :=
  Finset.one_le_prod' fun i hi => hj _ (hx i (Finset.mem_range.mp hi))

theorem one_lt_finiteReturnJacobian {R : X → X} {D : Set X} {j : X → ℝ≥0∞}
    (hj : ∀ x ∈ D, 1 < j x) {n : ℕ} (hn : 0 < n) {x : X}
    (hx : x ∈ finiteReturnDomain R D n) : 1 < finiteReturnJacobian R j n x := by
  apply (Finset.one_lt_prod_iff_of_one_le (fun i hi => (hj _ (hx i (Finset.mem_range.mp hi))).le)).mpr
  exact ⟨0, Finset.mem_range.mpr hn, hj _ (hx 0 hn)⟩

theorem finiteReturnJacobian_lt_top {R : X → X} {D : Set X} {j : X → ℝ≥0∞}
    (hj : ∀ x ∈ D, j x < ∞) {n : ℕ} {x : X} (hx : x ∈ finiteReturnDomain R D n) :
    finiteReturnJacobian R j n x < ∞ :=
  ENNReal.prod_lt_top fun i hi => hj _ (hx i (Finset.mem_range.mp hi))

variable [MeasurableSpace X]

theorem measurableSet_finiteReturnDomain {R : X → X} {D : Set X}
    (hR : Measurable R) (hD : MeasurableSet D) (n : ℕ) :
    MeasurableSet (finiteReturnDomain R D n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [finiteReturnDomain_succ]; exact ih.inter (hD.preimage (hR.iterate n))

theorem measurable_finiteReturnJacobian {R : X → X} {j : X → ℝ≥0∞}
    (hR : Measurable R) (hj : Measurable j) (n : ℕ) :
    Measurable (finiteReturnJacobian R j n) :=
  (Finset.range n).measurable_prod fun i _ => hj.comp (hR.iterate i)

end BianchiIX
