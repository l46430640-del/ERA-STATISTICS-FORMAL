import Mathlib.MeasureTheory.Constructions.Polish.Basic

noncomputable section

namespace BianchiIX

open Set MeasureTheory

/-- A fixed countable ordering selects one of the measurable candidate values on their union. -/
theorem exists_measurable_countable_selection {ι X Y : Type*} [Countable ι] [Nonempty ι]
    [MeasurableSpace X] [MeasurableSpace Y] (S : ι → Set X) (f : ι → X → Y)
    (hS : ∀ i, MeasurableSet (S i)) (hf : ∀ i, Measurable (f i)) :
    ∃ g : X → Y, Measurable g ∧ ∀ x ∈ ⋃ i, S i, ∃ i, x ∈ S i ∧ g x = f i x := by
  classical
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  let U := ⋃ i, S i
  have hU : MeasurableSet U := MeasurableSet.iUnion hS
  have hcover (x : U) : ∃ n, x.val ∈ S (e n) := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp x.property
    obtain ⟨n, rfl⟩ := he i
    exact ⟨n, hi⟩
  let g₀ : U → Y := fun x => f (e (Nat.find (hcover x))) x.val
  have hg₀ : Measurable g₀ := Measurable.find
    (fun n => (hf (e n)).comp measurable_subtype_coe)
    (fun n => (hS (e n)).preimage measurable_subtype_coe) hcover
  let g : X → Y := fun x => if hx : x ∈ U then g₀ ⟨x, hx⟩ else f (e 0) x
  refine ⟨g, hg₀.dite ((hf (e 0)).comp measurable_subtype_coe) hU, ?_⟩
  intro x hx
  change x ∈ U at hx
  refine ⟨e (Nat.find (hcover ⟨x, hx⟩)), Nat.find_spec (hcover ⟨x, hx⟩), ?_⟩
  simp only [g, dif_pos hx, g₀]

/-- A Borel inverse of an injective chart transports measurable parameter data to physical points. -/
theorem exists_measurable_chart_extension {X Y V : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableSpace V] [Nonempty V] {D : Set X} {C : X → Y} {G : X → V}
    (hD : MeasurableSet D) (hC : ContinuousOn C D) (hinj : InjOn C D)
    (hG : Measurable (D.domRestrict G)) :
    ∃ g : Y → V, Measurable g ∧ ∀ x ∈ D, g (C x) = G x := by
  classical
  by_cases hne : D.Nonempty
  · let : Nonempty D := hne.to_subtype
    have H := hC.measurableEmbedding hD hinj
    refine ⟨fun y => G (H.invFun y).val, hG.comp H.measurable_invFun, ?_⟩
    intro x hx
    exact congrArg (fun z : D => G z.val) (H.leftInverse_invFun ⟨x, hx⟩)
  · exact ⟨fun _ => Classical.arbitrary V, measurable_const, fun x hx => (hne ⟨x, hx⟩).elim⟩

/-- Countably many injective Borel charts suffice; no projection over an uncountable budget is used. -/
theorem exists_measurable_chart_selection {ι X Y V : Type*} [Countable ι] [Nonempty ι]
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableSpace V] [Nonempty V]
    (D : ι → Set X) (C : ι → X → Y) (G : ι → X → V)
    (hD : ∀ i, MeasurableSet (D i)) (hC : ∀ i, ContinuousOn (C i) (D i))
    (hinj : ∀ i, InjOn (C i) (D i)) (hG : ∀ i, Measurable ((D i).domRestrict (G i))) :
    ∃ g : Y → V, Measurable g ∧
      ∀ y ∈ ⋃ i, C i '' D i, ∃ i, ∃ x ∈ D i, C i x = y ∧ g y = G i x := by
  choose f hfm hfeq using fun i => exists_measurable_chart_extension (hD i) (hC i) (hinj i) (hG i)
  obtain ⟨g, hgm, hg⟩ := exists_measurable_countable_selection (fun i => C i '' D i) f
    (fun i => (hD i).image_of_continuousOn_injOn (hC i) (hinj i)) hfm
  refine ⟨g, hgm, ?_⟩
  intro y hy
  obtain ⟨i, ⟨x, hx, rfl⟩, heq⟩ := hg y hy
  exact ⟨i, x, hx, rfl, heq.trans (hfeq i x hx)⟩

end BianchiIX
