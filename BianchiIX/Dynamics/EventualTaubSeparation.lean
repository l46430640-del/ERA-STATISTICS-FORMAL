import BianchiIX.Dynamics.PhysicalPhaseSpace
import BianchiIX.Dynamics.WallProductDecay

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

def EventuallyTaubSeparated (x : NormalizedState) : Prop :=
  ∃ ε > (0 : ℝ), ∀ᶠ t in atTop, ∀ i : Fin 3,
    ε ≤ normalizedEuclideanDistance (normalizedMaxCurve x 0 t) (taubPoint i)

/-- Closed tails use every real time; only thresholds and starting times need be counted. -/
theorem eventuallyTaubSeparated_iff_countable (x : NormalizedState) :
    EventuallyTaubSeparated x ↔ ∃ n m : ℕ, ∀ t : ℝ, (m : ℝ) ≤ t → ∀ i : Fin 3,
      1 / (n + 1 : ℝ) ≤ normalizedEuclideanDistance (normalizedMaxCurve x 0 t) (taubPoint i) := by
  constructor
  · rintro ⟨ε, hε, H⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨T, hT⟩ := eventually_atTop.mp H
    obtain ⟨m, hm⟩ := exists_nat_ge T
    exact ⟨n, m, fun t ht i => hn.le.trans (hT t (hm.trans ht) i)⟩
  · rintro ⟨n, m, H⟩
    exact ⟨1 / (n + 1 : ℝ), by positivity,
      (eventually_ge_atTop (m : ℝ)).mono fun t ht => H t ht⟩

theorem measurableSet_physical_eventuallyTaubSeparated :
    MeasurableSet {x | x ∈ physicalPhaseSpace ∧ EventuallyTaubSeparated x} := by
  let S : Set physicalPhaseSpace := {x | EventuallyTaubSeparated x.val}
  have hS : MeasurableSet S := by
    have heq : S = ⋃ n : ℕ, ⋃ m : ℕ, ⋂ t : ℝ, ⋂ (_ : (m : ℝ) ≤ t), ⋂ i : Fin 3,
        {x : physicalPhaseSpace | 1 / (n + 1 : ℝ) ≤
          normalizedEuclideanDistance (normalizedMaxCurve x.val 0 t) (taubPoint i)} := by
      ext x
      simp only [S, mem_ofPred_eq, mem_iUnion, mem_iInter,
        eventuallyTaubSeparated_iff_countable]
    rw [heq]
    apply MeasurableSet.iUnion
    intro n
    apply MeasurableSet.iUnion
    intro m
    apply IsClosed.measurableSet
    apply isClosed_iInter
    intro t
    apply isClosed_iInter
    intro ht
    apply isClosed_iInter
    intro i
    have hf := continuous_physical_forwardFlow ((Nat.cast_nonneg m).trans ht)
    have hd := continuous_normalizedEuclideanDistance.comp
      (hf.prodMk (continuous_const : Continuous (fun _ : physicalPhaseSpace => taubPoint i)))
    exact isClosed_le (continuous_const : Continuous (fun _ : physicalPhaseSpace => 1 / (n + 1 : ℝ))) hd
  have H := measurableSet_physicalPhaseSpace.subtype_image hS
  convert H using 1
  ext x
  simp only [mem_ofPred_eq, mem_image, S, Subtype.exists, exists_and_right, exists_eq_right, exists_prop]

theorem eventuallyTaubSeparated_maxCurve_iff {x : NormalizedState} {s : ℝ}
    (hc : stateConstraint x = 1) (hs : s ∈ normalizedMaxDomain x 0) :
    EventuallyTaubSeparated (normalizedMaxCurve x 0 s) ↔ EventuallyTaubSeparated x := by
  unfold EventuallyTaubSeparated
  apply exists_congr
  intro ε
  apply and_congr_right
  intro _
  have heq : (fun t => ∀ i, ε ≤ normalizedEuclideanDistance
        (normalizedMaxCurve (normalizedMaxCurve x 0 s) 0 t) (taubPoint i)) =ᶠ[atTop]
      (fun t => ∀ i, ε ≤ normalizedEuclideanDistance
        (normalizedMaxCurve x 0 (t + s)) (taubPoint i)) := by
    filter_upwards [eventually_ge_atTop (-s)] with t ht
    have hdom := normalizedMaxDomain_contains_Ici_of_constraint hc 0 (show 0 ≤ t + s by linarith)
    have H := normalizedMaxCurve_shift (by simpa only [zero_add] using hs) hdom
    simp only [zero_add] at H
    rw [H]
  rw [eventually_congr (heq.mono fun _ h => h.to_iff)]
  have H := (eventually_map (f := atTop) (m := fun t : ℝ => t + s)
    (P := fun t => ∀ i, ε ≤ normalizedEuclideanDistance (normalizedMaxCurve x 0 t) (taubPoint i)))
  rw [map_add_atTop_eq] at H
  exact H.symm

theorem not_eventuallyTaubSeparated_iff (x : NormalizedState) :
    ¬EventuallyTaubSeparated x ↔ ∀ ε > (0 : ℝ), ∀ R : ℝ, ∃ t ≥ R, ∃ i : Fin 3,
      normalizedEuclideanDistance (normalizedMaxCurve x 0 t) (taubPoint i) < ε := by
  constructor
  · intro H ε hε R
    by_contra! hn
    exact H ⟨ε, hε, (eventually_ge_atTop R).mono fun t ht i => hn t ht i⟩
  · rintro H ⟨ε, hε, Ha⟩
    obtain ⟨T, hT⟩ := eventually_atTop.mp Ha
    obtain ⟨t, ht, i, hi⟩ := H ε hε T
    exact (not_lt_of_ge (hT t ht i)) hi

end BianchiIX
