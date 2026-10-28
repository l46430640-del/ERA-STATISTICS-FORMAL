import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

variable {X : Type*} [TopologicalSpace X]

/-- Compactness remains uniform when the right endpoint varies continuously. -/
theorem eventually_forall_movingInterval {x₀ : X} {T : X → ℝ} {P : X → ℝ → Prop}
    (hT : ContinuousAt T x₀) (hpos : 0 < T x₀)
    (hP : ∀ t ∈ Icc 0 (T x₀), ∀ᶠ z : X × ℝ in 𝓝 (x₀, t), P z.1 z.2) :
    ∀ᶠ x in 𝓝 x₀, ∀ t ∈ Icc 0 (T x), P x t := by
  have H : ∀ᶠ x in 𝓝 x₀, ∀ u ∈ Icc (0 : ℝ) 1, P x (u * T x) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro u hu
    have ht : u * T x₀ ∈ Icc 0 (T x₀) :=
      ⟨mul_nonneg hu.1 hpos.le, by simpa using mul_le_mul_of_nonneg_right hu.2 hpos.le⟩
    have hc : ContinuousAt (fun z : X × ℝ => (z.1, z.2 * T z.1)) (x₀, u) :=
      continuousAt_fst.prodMk (continuousAt_snd.mul (hT.comp continuousAt_fst))
    exact hc.eventually (hP _ ht)
  have hp : ∀ᶠ x in 𝓝 x₀, 0 < T x := hT.eventually (isOpen_Ioi.mem_nhds hpos)
  filter_upwards [H, hp] with x hx hpx
  intro t ht
  have hu : t / T x ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg ht.1 hpx.le, (div_le_one hpx).mpr ht.2⟩
  simpa only [div_mul_cancel₀ _ (ne_of_gt hpx)] using hx _ hu

/-- Local uniqueness at both crossings and compact interior avoidance persist. -/
theorem eventually_no_intermediate_return {x₀ : X} {T : X → ℝ}
    {g : X → ℝ → ℝ} {c : ℝ} (hT : ContinuousAt T x₀) (hpos : 0 < T x₀)
    (hentry : ∀ᶠ z : X × ℝ in 𝓝 (x₀, 0), g z.1 z.2 = c → z.2 = 0)
    (hexit : ∀ᶠ z : X × ℝ in 𝓝 (x₀, T x₀), g z.1 z.2 = c → z.2 = T z.1)
    (hcont : ∀ t ∈ Ioo 0 (T x₀), ContinuousAt (fun z : X × ℝ => g z.1 z.2) (x₀, t))
    (havoid : ∀ t ∈ Ioo 0 (T x₀), g x₀ t ≠ c) :
    ∀ᶠ x in 𝓝 x₀, ∀ t ∈ Ioo 0 (T x), g x t ≠ c := by
  have H : ∀ᶠ x in 𝓝 x₀, ∀ t ∈ Icc 0 (T x), g x t = c → t = 0 ∨ t = T x := by
    apply eventually_forall_movingInterval hT hpos
    intro t ht
    by_cases hzero : t = 0
    · subst t
      exact hentry.mono fun _ h heq => Or.inl (h heq)
    by_cases hend : t = T x₀
    · subst t
      exact hexit.mono fun _ h heq => Or.inr (h heq)
    have hi : t ∈ Ioo 0 (T x₀) :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm hzero), lt_of_le_of_ne ht.2 hend⟩
    exact ((hcont t hi).eventually_ne (havoid t hi)).mono fun _ h heq => (h heq).elim
  filter_upwards [H] with x hx
  intro t ht heq
  rcases hx t ⟨ht.1.le, ht.2.le⟩ heq with h | h
  · exact (ne_of_gt ht.1) h
  · exact (ne_of_lt ht.2) h

theorem strict_above_of_no_return {a b c m : ℝ} {f : ℝ → ℝ}
    (hc : ContinuousOn f (Ioo a b)) (hm : m ∈ Ioo a b) (hmid : c < f m)
    (hne : ∀ t ∈ Ioo a b, f t ≠ c) : ∀ t ∈ Ioo a b, c < f t := by
  intro t ht
  by_contra! hle
  obtain ⟨s, hs, heq⟩ := isPreconnected_Ioo.intermediate_value ht hm hc ⟨hle, hmid.le⟩
  exact hne s hs heq

end BianchiIX
