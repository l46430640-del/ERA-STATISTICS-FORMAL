import BianchiIX.Dynamics.EraSelectionInverse
import BianchiIX.Analysis.AmplitudeSequence
import Mathlib.Data.PNat.Basic

noncomputable section

namespace BianchiIX

open Set

def eraPrefixState (η : ℝ) (J : ℕ) : List ℕ+ → (ℝ × CoreAngleState) → ℝ × CoreAngleState
  | [] => id
  | a :: w => eraPrefixState η J w ∘ eraBudgetReturn η J a.natPred

def eraPrefixDomain (η : ℝ) (J : ℕ) (σ Bstar : ℝ) : List ℕ+ → Set (ℝ × CoreAngleState)
  | [] => univ
  | a :: w => eraSelectedInputs η J σ Bstar a.natPred ∩
      eraBudgetReturn η J a.natPred ⁻¹' eraPrefixDomain η J σ Bstar w

def eraSurvivorDomain (η : ℝ) (J : ℕ) (σ Bstar : ℝ) : Set (ℝ × CoreAngleState) :=
  ⋂ n : ℕ, ⋃ w : {w : List ℕ+ // w.length = n}, eraPrefixDomain η J σ Bstar w.val

theorem eraPrefixState_append (η : ℝ) (J : ℕ) (v w : List ℕ+) (p : ℝ × CoreAngleState) :
    eraPrefixState η J (v ++ w) p = eraPrefixState η J w (eraPrefixState η J v p) := by
  induction v generalizing p with
  | nil => rfl
  | cons a v ih => exact ih _

theorem mem_eraPrefixDomain_append (η : ℝ) (J : ℕ) (σ Bstar : ℝ)
    (v w : List ℕ+) (p : ℝ × CoreAngleState) :
    p ∈ eraPrefixDomain η J σ Bstar (v ++ w) ↔
      p ∈ eraPrefixDomain η J σ Bstar v ∧ eraPrefixState η J v p ∈ eraPrefixDomain η J σ Bstar w := by
  induction v generalizing p with
  | nil => simp [eraPrefixDomain, eraPrefixState]
  | cons a v ih =>
    simp only [List.cons_append, eraPrefixDomain, mem_inter_iff, mem_preimage, eraPrefixState,
      Function.comp_apply, ih]
    exact and_assoc.symm

theorem eraPrefixState_budget (η : ℝ) (J : ℕ) (w : List ℕ+) (p : ℝ × CoreAngleState)
    (hp : 0 ≤ p.1) : (eraPrefixState η J w p).1 = eraAmplitude p.1 w.length := by
  induction w using List.reverseRecOn with
  | nil => simp [eraPrefixState]
  | append_singleton w a ih =>
    rw [eraPrefixState_append]
    change (eraPrefixState η J w p).1 ^ (4 / 3 : ℝ) = _
    rw [ih, List.length_append, List.length_singleton, eraAmplitude_succ hp]

theorem eraPrefixDomain_unique (η : ℝ) (J : ℕ) (σ Bstar : ℝ) {v w : List ℕ+}
    (hlen : v.length = w.length) {p : ℝ × CoreAngleState}
    (hv : p ∈ eraPrefixDomain η J σ Bstar v) (hw : p ∈ eraPrefixDomain η J σ Bstar w) : v = w := by
  induction v generalizing w p with
  | nil => exact (List.length_eq_zero_iff.mp hlen.symm).symm
  | cons a v ih =>
    cases w with
    | nil => simp at hlen
    | cons b w =>
      have hab : a = b := by
        by_contra hne
        have hd := eraSelectedInputs_disjoint η J σ Bstar
          (fun he => hne (PNat.natPred_injective he))
        exact Set.disjoint_left.mp hd hv.1 hw.1
      subst b
      exact congrArg (List.cons a) (ih (Nat.succ.inj hlen) hv.2 hw.2)

/-- Finite actual histories are measurable using only restricted return maps. -/
theorem eraPrefixDomain_measurable {η σ Bstar : ℝ} {J : ℕ}
    (H : ∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bstar m) ∧
      Measurable (fun p : eraSelectedInputs η J σ Bstar m => eraBudgetReturn η J m p.val))
    (w : List ℕ+) : MeasurableSet (eraPrefixDomain η J σ Bstar w) ∧
      Measurable (fun p : eraPrefixDomain η J σ Bstar w => eraPrefixState η J w p.val) := by
  induction w with
  | nil => exact ⟨MeasurableSet.univ, measurable_subtype_coe⟩
  | cons a w ih =>
    let S := eraSelectedInputs η J σ Bstar a.natPred
    let D := eraPrefixDomain η J σ Bstar w
    let Q := eraBudgetReturn η J a.natPred
    have hA : MeasurableSet {p : S | Q p.val ∈ D} := ih.1.preimage (H a.natPred).2
    have heq : eraPrefixDomain η J σ Bstar (a :: w) = Subtype.val '' {p : S | Q p.val ∈ D} := by
      ext p
      constructor
      · exact fun hp => ⟨⟨p, hp.1⟩, hp.2, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p.property, hp⟩
    refine ⟨by rw [heq]; exact (H a.natPred).1.subtype_image hA, ?_⟩
    have hi : Measurable (fun p : eraPrefixDomain η J σ Bstar (a :: w) => (⟨p.val, p.property.1⟩ : S)) :=
      measurable_subtype_coe.subtype_mk
    have hQ : Measurable (fun p : eraPrefixDomain η J σ Bstar (a :: w) => Q p.val) :=
      (H a.natPred).2.comp hi
    have hmap : Measurable (fun p : eraPrefixDomain η J σ Bstar (a :: w) => (⟨Q p.val, p.property.2⟩ : D)) :=
      hQ.subtype_mk
    exact ih.2.comp hmap

theorem eraSurvivorDomain_measurable {η σ Bstar : ℝ} {J : ℕ}
    (H : ∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bstar m) ∧
      Measurable (fun p : eraSelectedInputs η J σ Bstar m => eraBudgetReturn η J m p.val)) :
    MeasurableSet (eraSurvivorDomain η J σ Bstar) :=
  MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun w => (eraPrefixDomain_measurable H w.val).1

/-- Joint measurability is pulled back along any measurable initial-state family. -/
theorem eraPrefixDomain_family_measurable {η σ Bstar : ℝ} {J : ℕ}
    (H : ∀ m : ℕ, MeasurableSet (eraSelectedInputs η J σ Bstar m) ∧
      Measurable (fun p : eraSelectedInputs η J σ Bstar m => eraBudgetReturn η J m p.val))
    {X : Type*} [MeasurableSpace X] {Y : X → ℝ × CoreAngleState} (hY : Measurable Y) :
    (∀ w : List ℕ+, MeasurableSet (Y ⁻¹' eraPrefixDomain η J σ Bstar w) ∧
      Measurable (fun p : Y ⁻¹' eraPrefixDomain η J σ Bstar w => eraPrefixState η J w (Y p.val))) ∧
      MeasurableSet (Y ⁻¹' eraSurvivorDomain η J σ Bstar) := by
  refine ⟨?_, (eraSurvivorDomain_measurable H).preimage hY⟩
  intro w
  have h := eraPrefixDomain_measurable H w
  have hm : Measurable (fun p : Y ⁻¹' eraPrefixDomain η J σ Bstar w =>
      (⟨Y p.val, p.property⟩ : eraPrefixDomain η J σ Bstar w)) :=
    (hY.comp measurable_subtype_coe).subtype_mk
  exact ⟨h.1.preimage hY, h.2.comp hm⟩

theorem exists_era_prefix_measurable :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bstar > (0 : ℝ), Bstar < 1 ∧
          (∀ w : List ℕ+, MeasurableSet (eraPrefixDomain η J σ Bstar w) ∧
            Measurable (fun p : eraPrefixDomain η J σ Bstar w => eraPrefixState η J w p.val)) ∧
          MeasurableSet (eraSurvivorDomain η J σ Bstar) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_selected_return
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bstar, hBs, hBsone, H, _⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  exact ⟨Bstar, hBs, hBsone, eraPrefixDomain_measurable H, eraSurvivorDomain_measurable H⟩

end BianchiIX
