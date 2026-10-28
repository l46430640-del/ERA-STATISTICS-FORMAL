import BianchiIX.Statistics.EraPrefixMeasurability
import BianchiIX.Statistics.GaussTypical

noncomputable section

namespace BianchiIX

open Set

namespace EraSurvivor

variable {η σ Bstar : ℝ} {J : ℕ}

private theorem exists_word (p : eraSurvivorDomain η J σ Bstar) (n : ℕ) :
    ∃ w : List ℕ+, w.length = n ∧ p.val ∈ eraPrefixDomain η J σ Bstar w := by
  obtain ⟨w, hw⟩ := mem_iUnion.mp (mem_iInter.mp p.property n)
  exact ⟨w.val, w.property, hw⟩

def word (p : eraSurvivorDomain η J σ Bstar) (n : ℕ) : List ℕ+ := (exists_word p n).choose

theorem word_length (p : eraSurvivorDomain η J σ Bstar) (n : ℕ) : (word p n).length = n :=
  (exists_word p n).choose_spec.1

theorem mem_word_domain (p : eraSurvivorDomain η J σ Bstar) (n : ℕ) :
    p.val ∈ eraPrefixDomain η J σ Bstar (word p n) := (exists_word p n).choose_spec.2

theorem word_eq_iff (p : eraSurvivorDomain η J σ Bstar) {n : ℕ} {w : List ℕ+} (hw : w.length = n) :
    word p n = w ↔ p.val ∈ eraPrefixDomain η J σ Bstar w := by
  constructor
  · exact fun h => h ▸ mem_word_domain p n
  · exact fun h => eraPrefixDomain_unique η J σ Bstar ((word_length p n).trans hw.symm) (mem_word_domain p n) h

private theorem exists_next_digit (p : eraSurvivorDomain η J σ Bstar) (n : ℕ) :
    ∃ a : ℕ+, word p (n + 1) = word p n ++ [a] := by
  have hl := word_length p (n + 1)
  have hp := mem_word_domain p (n + 1)
  generalize word p (n + 1) = w at hl hp ⊢
  induction w using List.reverseRecOn with
  | nil => simp at hl
  | append_singleton w a _ =>
    have hw : w = word p n := eraPrefixDomain_unique η J σ Bstar
      (by simpa [word_length] using hl)
      ((mem_eraPrefixDomain_append η J σ Bstar w [a] p.val).mp hp).1 (mem_word_domain p n)
    exact ⟨a, congrArg (fun v => v ++ [a]) hw⟩

def digits (p : eraSurvivorDomain η J σ Bstar) (n : ℕ) : ℕ+ := (exists_next_digit p n).choose

theorem word_succ (p : eraSurvivorDomain η J σ Bstar) (n : ℕ) :
    word p (n + 1) = word p n ++ [digits p n] := (exists_next_digit p n).choose_spec

theorem digits_prefix (p : eraSurvivorDomain η J σ Bstar) (n : ℕ) :
    digitPrefix (digits p) n = (word p n).map (fun a : ℕ+ => (a : ℕ)) := by
  induction n with
  | zero =>
    have hw : word p 0 = [] := List.length_eq_zero_iff.mp (word_length p 0)
    simp [digitPrefix, hw]
  | succ n ih =>
    rw [word_succ, List.map_append, List.map_singleton, ← ih]
    simp [digitPrefix, List.range_succ]

theorem digit_fiber (n : ℕ) (a : ℕ+) :
    {p : eraSurvivorDomain η J σ Bstar | digits p n = a} =
      ⋃ w : {w : List ℕ+ // w.length = n},
        (Subtype.val : eraSurvivorDomain η J σ Bstar → ℝ × CoreAngleState) ⁻¹'
          eraPrefixDomain η J σ Bstar (w.val ++ [a]) := by
  ext p
  simp only [mem_ofPred_eq, mem_iUnion, mem_preimage]
  constructor
  · intro h
    refine ⟨⟨word p n, word_length p n⟩, ?_⟩
    simpa only [word_succ, h] using mem_word_domain p (n + 1)
  · rintro ⟨⟨w, hw⟩, hp⟩
    have heq := (word_eq_iff p (by simp [hw] : (w ++ [a]).length = n + 1)).mpr hp
    rw [word_succ] at heq
    exact List.singleton_inj.mp (List.append_inj_right heq ((word_length p n).trans hw.symm))

theorem digits_measurable
    (H : ∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bstar m) ∧
      Measurable (fun p : eraSelectedInputs η J σ Bstar m => eraBudgetReturn η J m p.val)) :
    Measurable (digits (η := η) (J := J) (σ := σ) (Bstar := Bstar)) := by
  apply measurable_pi_lambda
  intro n
  apply measurable_to_countable'
  intro a
  change MeasurableSet {p : eraSurvivorDomain η J σ Bstar | digits p n = a}
  rw [digit_fiber]
  exact MeasurableSet.iUnion (fun w =>
    ((eraPrefixDomain_measurable H (w.val ++ [a])).1).preimage measurable_subtype_coe)

def code (p : eraSurvivorDomain η J σ Bstar) : ℝ := gaussCode (digits p)

theorem code_measurable
    (H : ∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bstar m) ∧
      Measurable (fun p : eraSelectedInputs η J σ Bstar m => eraBudgetReturn η J m p.val)) :
    Measurable (code (η := η) (J := J) (σ := σ) (Bstar := Bstar)) :=
  measurable_gaussCode.comp (digits_measurable H)

def typicalDomain (η : ℝ) (J : ℕ) (σ Bstar : ℝ) : Set (ℝ × CoreAngleState) :=
  Subtype.val '' {p : eraSurvivorDomain η J σ Bstar | code p ∈ gaussCylinderTypicalSet}

theorem typicalDomain_subset : typicalDomain η J σ Bstar ⊆ eraSurvivorDomain η J σ Bstar := by
  rintro _ ⟨p, _, rfl⟩
  exact p.property

theorem mem_typicalDomain (p : eraSurvivorDomain η J σ Bstar) :
    p.val ∈ typicalDomain η J σ Bstar ↔ code p ∈ gaussCylinderTypicalSet := by
  constructor
  · rintro ⟨q, hq, heq⟩
    have hp : q = p := Subtype.ext heq
    simpa only [hp, mem_ofPred_eq] using hq
  · exact fun hp => ⟨p, hp, rfl⟩

theorem typicalDomain_measurable
    (H : ∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bstar m) ∧
      Measurable (fun p : eraSelectedInputs η J σ Bstar m => eraBudgetReturn η J m p.val)) :
    MeasurableSet (typicalDomain η J σ Bstar) :=
  (eraSurvivorDomain_measurable H).subtype_image
    (gaussCylinderTypicalSet_measurable.preimage (code_measurable H))

end EraSurvivor

theorem exists_era_survivor_coding_measurable :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bstar > (0 : ℝ), Bstar < 1 ∧ MeasurableSet (eraSurvivorDomain η J σ Bstar) ∧
          Measurable (EraSurvivor.digits (η := η) (J := J) (σ := σ) (Bstar := Bstar)) ∧
          Measurable (EraSurvivor.code (η := η) (J := J) (σ := σ) (Bstar := Bstar)) ∧
          MeasurableSet (EraSurvivor.typicalDomain η J σ Bstar) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_selected_return
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bstar, hBs, hBsone, H, _⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  exact ⟨Bstar, hBs, hBsone, eraSurvivorDomain_measurable H, EraSurvivor.digits_measurable H,
    EraSurvivor.code_measurable H, EraSurvivor.typicalDomain_measurable H⟩

end BianchiIX
