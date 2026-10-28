import BianchiIX.Statistics.EraCapMonotonicity

noncomputable section

namespace BianchiIX

/-- Physical frame, elapsed time, budget, and actual core state. -/
abbrev CoreRestartData := (Fin 6 × ℝ) × (ℝ × CoreAngleState)

def CoreRestartWitness (η : ℝ) (J : ℕ) (σ Bcap : ℝ) (x : NormalizedState)
    (w : CoreRestartData) : Prop :=
  0 < w.1.2 ∧ w.1.2 ∈ normalizedMaxDomain x 0 ∧
    ∃ p : eraSurvivorDomain η J σ Bcap, p.val = w.2 ∧
      EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) ∧
      coreRadiusEntry p.val.2 = toProjectiveState ((axisFrame w.1.1).map (normalizedMaxCurve x 0 w.1.2))

theorem CoreRestartWitness.statisticalCoreFuture {η σ Bcap : ℝ} {J : ℕ}
    {x : NormalizedState} {w : CoreRestartData} (H : CoreRestartWitness η J σ Bcap x w) :
    StatisticalCoreFuture η J σ Bcap x := by
  obtain ⟨ht, hdom, p, _, hstat, ho⟩ := H
  exact ⟨w.1.2, ht, hdom, w.1.1, p, hstat, ho⟩

/-- Enlarging the auxiliary cap keeps all chosen data and the statistical orbit unchanged. -/
theorem CoreRestartWitness.mono_cap {η σ B₁ B₂ : ℝ} {J : ℕ}
    {x : NormalizedState} {w : CoreRestartData} (H : CoreRestartWitness η J σ B₁ x w)
    (hB : B₁ ≤ B₂) : CoreRestartWitness η J σ B₂ x w := by
  obtain ⟨ht, hdom, p, hp, hstat, ho⟩ := H
  let q : eraSurvivorDomain η J σ B₂ := ⟨p.val, eraSurvivorDomain_mono_cap hB p.property⟩
  refine ⟨ht, hdom, q, hp, ?_, ho⟩
  rw [← EraSurvivor.digits_eq_of_val p q rfl, ← EraSurvivor.phase_eq_of_val p q rfl]
  exact hstat

theorem CoreRestartWitness.restrict_cap {η σ B₁ B₂ : ℝ} {J : ℕ}
    {x : NormalizedState} {w : CoreRestartData} (H : CoreRestartWitness η J σ B₁ x w)
    (hone : w.2.1 ≤ 1) (hB : w.2.1 ≤ B₂) : CoreRestartWitness η J σ B₂ x w := by
  obtain ⟨ht, hdom, p, hp, hstat, ho⟩ := H
  let q : eraSurvivorDomain η J σ B₂ := ⟨p.val,
    eraSurvivorDomain_restrict_cap p.property (by simpa only [hp] using hone) (by simpa only [hp] using hB)⟩
  refine ⟨ht, hdom, q, hp, ?_, ho⟩
  rw [← EraSurvivor.digits_eq_of_val p q rfl, ← EraSurvivor.phase_eq_of_val p q rfl]
  exact hstat

/-- Once the budget and state are measurable, lifting them to the survivor subtype needs no further selection. -/
theorem CoreRestartWitness.exists_measurable_survivor {X : Type*} [MeasurableSpace X]
    {η σ Bcap : ℝ} {J : ℕ} {S : Set X} {C : X → NormalizedState}
    {W : X → CoreRestartData} (hW : Measurable W)
    (H : ∀ x ∈ S, CoreRestartWitness η J σ Bcap (C x) (W x)) :
    ∃ p : S → eraSurvivorDomain η J σ Bcap, Measurable p ∧
      ∀ x, (p x).val = (W x.val).2 ∧
        EraStatistics (EraSurvivor.digits (p x)) (EraSurvivor.phase (p x)) := by
  have hmem (x : S) : (W x.val).2 ∈ eraSurvivorDomain η J σ Bcap := by
    obtain ⟨_, _, p, hp, _, _⟩ := H x.val x.property
    exact hp ▸ p.property
  let p : S → eraSurvivorDomain η J σ Bcap := fun x => ⟨(W x.val).2, hmem x⟩
  refine ⟨p, (hW.snd.comp measurable_subtype_coe).subtype_mk, ?_⟩
  intro x
  obtain ⟨_, _, q, hq, hstat, _⟩ := H x.val x.property
  have heq : q = p x := Subtype.ext hq
  exact ⟨rfl, heq ▸ hstat⟩

end BianchiIX
