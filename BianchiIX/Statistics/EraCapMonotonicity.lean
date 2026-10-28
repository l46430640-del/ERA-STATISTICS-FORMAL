import BianchiIX.Statistics.PhysicalFuture

noncomputable section

namespace BianchiIX

open Set

theorem eraSelectedInputs_mono_cap {η σ B₁ B₂ : ℝ} {J m : ℕ} (hB : B₁ ≤ B₂) :
    eraSelectedInputs η J σ B₁ m ⊆ eraSelectedInputs η J σ B₂ m := by
  intro p hp
  exact ⟨⟨⟨hp.1.1.1, hp.1.1.2.trans hB⟩, hp.1.2⟩, hp.2⟩

theorem eraPrefixDomain_mono_cap {η σ B₁ B₂ : ℝ} {J : ℕ} (hB : B₁ ≤ B₂) (w : List ℕ+) :
    eraPrefixDomain η J σ B₁ w ⊆ eraPrefixDomain η J σ B₂ w := by
  induction w with
  | nil => exact Subset.refl _
  | cons a w ih =>
    intro p hp
    exact ⟨eraSelectedInputs_mono_cap hB hp.1, ih hp.2⟩

theorem eraSurvivorDomain_mono_cap {η σ B₁ B₂ : ℝ} {J : ℕ} (hB : B₁ ≤ B₂) :
    eraSurvivorDomain η J σ B₁ ⊆ eraSurvivorDomain η J σ B₂ := by
  intro p hp
  apply mem_iInter.mpr
  intro n
  obtain ⟨w, hw⟩ := mem_iUnion.mp (mem_iInter.mp hp n)
  exact mem_iUnion.mpr ⟨w, eraPrefixDomain_mono_cap hB w.val hw⟩

/-- Every later budget is at most the initial one, so a smaller cap retaining that budget retains the whole history. -/
theorem eraPrefixDomain_restrict_cap {η σ B₁ B₂ : ℝ} {J : ℕ} {w : List ℕ+}
    {p : ℝ × CoreAngleState} (hp : p ∈ eraPrefixDomain η J σ B₁ w)
    (hone : p.1 ≤ 1) (hB : p.1 ≤ B₂) : p ∈ eraPrefixDomain η J σ B₂ w := by
  induction w generalizing p with
  | nil => exact Set.mem_univ _
  | cons a w ih =>
    have hstep : (eraBudgetReturn η J a.natPred p).1 ≤ p.1 :=
      Real.rpow_le_self_of_le_one hp.1.1.1.1.le hone (by norm_num)
    exact ⟨⟨⟨⟨hp.1.1.1.1, hB⟩, hp.1.1.2⟩, hp.1.2⟩,
      ih hp.2 (hstep.trans hone) (hstep.trans hB)⟩

theorem eraSurvivorDomain_restrict_cap {η σ B₁ B₂ : ℝ} {J : ℕ}
    {p : ℝ × CoreAngleState} (hp : p ∈ eraSurvivorDomain η J σ B₁)
    (hone : p.1 ≤ 1) (hB : p.1 ≤ B₂) : p ∈ eraSurvivorDomain η J σ B₂ := by
  apply mem_iInter.mpr
  intro n
  obtain ⟨w, hw⟩ := mem_iUnion.mp (mem_iInter.mp hp n)
  exact mem_iUnion.mpr ⟨w, eraPrefixDomain_restrict_cap hw hone hB⟩

namespace EraSurvivor

/-- The same initial budget and state have the same finite history under any two admissible caps. -/
theorem word_eq_of_val {η σ B₁ B₂ : ℝ} {J : ℕ}
    (p : eraSurvivorDomain η J σ B₁) (q : eraSurvivorDomain η J σ B₂)
    (hpq : p.val = q.val) (n : ℕ) : word p n = word q n := by
  apply eraPrefixDomain_unique η J σ (max B₁ B₂) ((word_length p n).trans (word_length q n).symm)
    (eraPrefixDomain_mono_cap (le_max_left B₁ B₂) _ (mem_word_domain p n))
  rw [hpq]
  exact eraPrefixDomain_mono_cap (le_max_right B₁ B₂) _ (mem_word_domain q n)

theorem digits_eq_of_val {η σ B₁ B₂ : ℝ} {J : ℕ}
    (p : eraSurvivorDomain η J σ B₁) (q : eraSurvivorDomain η J σ B₂)
    (hpq : p.val = q.val) : digits p = digits q := by
  funext n
  have H := (word_succ p n).symm.trans ((word_eq_of_val p q hpq (n + 1)).trans (word_succ q n))
  rw [word_eq_of_val p q hpq n] at H
  exact List.singleton_inj.mp (List.append_inj_right H rfl)

theorem phase_eq_of_val {η σ B₁ B₂ : ℝ} {J : ℕ}
    (p : eraSurvivorDomain η J σ B₁) (q : eraSurvivorDomain η J σ B₂)
    (hpq : p.val = q.val) : phase p = phase q := by
  funext n
  unfold phase
  rw [word_eq_of_val p q hpq n, hpq]

theorem typicalDomain_mono_cap {η σ B₁ B₂ : ℝ} {J : ℕ} (hB : B₁ ≤ B₂) :
    typicalDomain η J σ B₁ ⊆ typicalDomain η J σ B₂ := by
  rintro _ ⟨p, hp, rfl⟩
  let q : eraSurvivorDomain η J σ B₂ := ⟨p.val, eraSurvivorDomain_mono_cap hB p.property⟩
  refine ⟨q, ?_, rfl⟩
  change gaussCode (digits q) ∈ gaussCylinderTypicalSet
  rw [← digits_eq_of_val p q rfl]
  exact hp

end EraSurvivor

/-- Enlarging only the auxiliary cap preserves the exact statistical orbit, its digit sequence and its phase sequence. -/
theorem StatisticalCoreFuture.mono_cap {η σ B₁ B₂ : ℝ} {J : ℕ} {x : NormalizedState}
    (H : StatisticalCoreFuture η J σ B₁ x) (hB : B₁ ≤ B₂) :
    StatisticalCoreFuture η J σ B₂ x := by
  obtain ⟨T, ht, hdom, i, p, hstat, ho⟩ := H
  let q : eraSurvivorDomain η J σ B₂ := ⟨p.val, eraSurvivorDomain_mono_cap hB p.property⟩
  refine ⟨T, ht, hdom, i, q, ?_, ho⟩
  rw [← EraSurvivor.digits_eq_of_val p q rfl, ← EraSurvivor.phase_eq_of_val p q rfl]
  exact hstat

end BianchiIX
