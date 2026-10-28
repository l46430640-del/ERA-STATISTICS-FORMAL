import BianchiIX.Measure.LocalDiffeomorphismNull

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem volume_eq_zero_of_local_null {n : ℕ} {S : Set (Fin n → ℝ)}
    (H : ∀ x ∈ S, ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x ∈ U ∧ volume (S ∩ U) = 0) :
    volume S = 0 := by
  classical
  by_cases hS : S.Nonempty
  · let : Nonempty S := hS.to_subtype
    choose U hU hxU hnull using (fun x : S => H x.val x.property)
    obtain ⟨f, hf⟩ := (HereditarilyLindelofSpace.isLindelof S).indexed_countable_subcover U hU
      (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
    apply measure_mono_null (t := ⋃ m : ℕ, S ∩ U (f m)) _
      (measure_iUnion_null fun m => hnull (f m))
    intro x hx
    obtain ⟨m, hm⟩ := mem_iUnion.mp (hf hx)
    exact mem_iUnion.mpr ⟨m, hx, hm⟩
  · rw [Set.not_nonempty_iff_eq_empty.mp hS, measure_empty]

/-- Replacing one coordinate by a scalar with a nonzero partial derivative gives a local null chart. -/
theorem exists_local_null_scalar_level {n : ℕ} {g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hg : ContDiffAt ℝ 1 g x) {i : Fin n}
    (hi : fderiv ℝ g x (Pi.single i 1) ≠ 0) :
    ∃ U : Set (Fin n → ℝ), IsOpen U ∧ x ∈ U ∧ volume (U ∩ {y | g y = 0}) = 0 := by
  classical
  let f : (Fin n → ℝ) → (Fin n → ℝ) := fun y j => if j = i then g y else y j
  let D : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := ContinuousLinearMap.pi
    (fun j => if j = i then fderiv ℝ g x else ContinuousLinearMap.proj j)
  have hf : ContDiffAt ℝ 1 f x := by
    apply contDiffAt_pi.mpr
    intro j
    by_cases hj : j = i
    · simpa [f, hj] using hg
    · simp only [f, hj, if_false]
      fun_prop
  have hd : HasFDerivAt f D x := by
    apply hasFDerivAt_pi.mpr
    intro j
    by_cases hj : j = i
    · simpa [f, D, hj] using (hg.differentiableAt (by norm_num)).hasFDerivAt
    · simpa [f, D, hj] using (hasFDerivAt_apply j x)
  have hker : LinearMap.ker D.toLinearMap = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have hvj (j : Fin n) (hj : j ≠ i) : v j = 0 := by
      have H := congrFun hv j
      simpa [D, hj] using H
    have hvi : v = v i • Pi.single i (1 : ℝ) := by
      ext j
      by_cases hj : j = i
      · subst j; simp
      · simp [Pi.single_eq_of_ne hj, hvj j hj]
    have H := congrFun hv i
    have H' : fderiv ℝ g x v = 0 := by simpa [D] using H
    rw [hvi, map_smul] at H'
    have hv0 : v i = 0 := (mul_eq_zero.mp H').resolve_right hi
    rw [hvi, hv0, zero_smul]
  have hdet : (fderiv ℝ f x).det ≠ 0 := by
    rw [hd.fderiv]
    exact fun H => (LinearMap.det_eq_zero_iff_ker_ne_bot.mp H) hker
  obtain ⟨U, hU, hxU, H⟩ := exists_local_null_preimage hf hdet
  refine ⟨U, hU, hxU, ?_⟩
  have hnull : volume {z : Fin n → ℝ | z i = 0} = 0 :=
    Measure.pi_hyperplane (fun _ => (volume : Measure ℝ)) i 0
  convert H {z | z i = 0} hnull using 1
  simp [f]

/-- Every subset of a regular scalar level is outer-null, without a measurability assumption on the subset. -/
theorem volume_regular_scalar_level {n : ℕ} {g : (Fin n → ℝ) → ℝ} {S : Set (Fin n → ℝ)}
    (hg : ∀ x ∈ S, ContDiffAt ℝ 1 g x) (hz : ∀ x ∈ S, g x = 0)
    (hd : ∀ x ∈ S, ∃ i : Fin n, fderiv ℝ g x (Pi.single i 1) ≠ 0) :
    volume S = 0 := by
  apply volume_eq_zero_of_local_null
  intro x hx
  obtain ⟨i, hi⟩ := hd x hx
  obtain ⟨U, hU, hxU, hnull⟩ := exists_local_null_scalar_level (hg x hx) hi
  refine ⟨U, hU, hxU, measure_mono_null ?_ hnull⟩
  exact fun y hy => ⟨hy.2, hz y hy.1⟩

end BianchiIX
