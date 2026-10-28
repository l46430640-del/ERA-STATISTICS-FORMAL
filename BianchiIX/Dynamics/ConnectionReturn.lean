import BianchiIX.Dynamics.ConnectionSecondEvent

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

abbrev ConnectionParameters := Fin 3 → ℝ

def connectionInitialState (p : ConnectionParameters) : NormalizedState :=
  fromProjectiveState (connectionEntry (p 0) (p 1) (p 2))

def connectionReturnTime (p : ConnectionParameters) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain (connectionInitialState p) 0 ∧
    projectiveGrowingWall (normalizedMaxCurve (connectionInitialState p) 0 t) = 1}

def connectionReturnState (p : ConnectionParameters) : ProjectiveState :=
  toProjectiveState (normalizedMaxCurve (connectionInitialState p) 0 (connectionReturnTime p))

def connectionReturnValid (p : ConnectionParameters) : Prop :=
  let x := connectionInitialState p
  let T := connectionReturnTime p
  IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧ projectiveGrowingWall (normalizedMaxCurve x 0 t) = 1} T ∧
    (∀ t ∈ Icc 0 T, t ∈ normalizedMaxDomain x 0 ∧ 0 < 1 + normalizedMaxCurve x 0 t 0) ∧
    (∀ t ∈ Ico 0 T, projectiveGrowingWall (normalizedMaxCurve x 0 t) < 1) ∧
    0 < normalizedEventRate projectiveGrowingWall x 0 T

theorem contDiffAt_connectionInitialState (n : WithTop ℕ∞) {p : ConnectionParameters}
    (hD : projectiveStateDenom (connectionEntry (p 0) (p 1) (p 2)) ≠ 0) :
    ContDiffAt ℝ n connectionInitialState p := by
  apply (contDiffAt_fromProjectiveState n hD).comp p
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [connectionEntry] <;> fun_prop

theorem connection_entry_denom_pos {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    0 < projectiveStateDenom (connectionEntry (p 0) (p 1) (p 2)) := by
  have hu' : 0 ≤ p 1 ∧ p 1 ≤ 1 / 10000 :=
    ⟨hu.1, hu.2.trans (div_le_self (by norm_num) (by linarith only [hμ]))⟩
  exact (connection_denom_bound (m := p 0) (v := 1) hu' (by norm_num)
    ⟨hw.1.le, hw.2.trans (by norm_num)⟩).2

/-- The canonical first hit is C2 in all three ordinary entry parameters, including U = 0. -/
theorem connectionReturn_regular {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    let x := connectionInitialState p
    let T := connectionReturnTime p
    connectionReturnValid p ∧ ContDiffAt ℝ 2 connectionReturnTime p ∧
      ContDiffAt ℝ 2 connectionReturnState p ∧
      HasFDerivAt connectionReturnTime
        ((normalizedEventTimeDifferential projectiveGrowingWall x 0 T).comp
          (fderiv ℝ connectionInitialState p)) p ∧
      HasFDerivAt connectionReturnState
        (((fderiv ℝ toProjectiveState (normalizedMaxCurve x 0 T)).comp
          (normalizedEventDifferential projectiveGrowingWall x 0 T)).comp
          (fderiv ℝ connectionInitialState p)) p ∧
      (∀ᶠ q in 𝓝 p, connectionReturnValid q) := by
  intro x T₀
  have hD := connection_entry_denom_pos hμ hu hw
  have hc : stateConstraint x = 1 := fromProjectiveState_constraint (ne_of_gt hD)
  have hinit : toProjectiveState (normalizedMaxCurve x 0 0) = connectionEntry (p 0) (p 1) (p 2) := by
    rw [normalizedMaxCurve_initial]
    exact toProjectiveState_fromProjectiveState (ne_of_gt hD)
  obtain ⟨T, hT, hfirst, hprefix, _⟩ := exists_connection_first_return hμ hu hw
  have hreg : ∀ t ∈ Icc 0 T, t ∈ normalizedMaxDomain x 0 ∧ 0 < 1 + normalizedMaxCurve x 0 t 0 := by
    intro t ht
    exact ⟨normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1,
      lt_of_lt_of_le (by positivity) (hprefix t ht).1⟩
  have hrate : ∀ t ∈ Icc 0 T, 0 < normalizedEventRate projectiveGrowingWall x 0 t := by
    intro t ht
    apply normalized_connection_event_rate_pos hc hμ (le_refl 0) ht.1
      (hreg 0 ⟨le_rfl, hT.le⟩).2 (hreg t ht).2 (hprefix t ht).2
    change 0 < toProjectiveState (normalizedMaxCurve x 0 0) 3
    simpa [hinit, connectionEntry] using hw.1
  obtain ⟨τ, hτ, hcτ, hcP, hdτ, hdP, hnear⟩ := exists_growingWall_first_hit_two hT hreg hrate hfirst.1.2.2
  have hcI := contDiffAt_connectionInitialState 2 (ne_of_gt hD)
  have hnear' := hcI.continuousAt.eventually hnear
  have heq : connectionReturnTime =ᶠ[𝓝 p] (fun q => τ (connectionInitialState q)) := by
    filter_upwards [hnear'] with q hq
    exact hq.1.csInf_eq
  have hT₀ : T₀ = T := heq.self_of_nhds.trans hτ
  have hnearValid : ∀ᶠ q in 𝓝 p, connectionReturnValid q := by
    filter_upwards [hnear', heq] with q hq htime
    dsimp only [connectionReturnValid]
    rw [htime]
    exact hq
  have hcTime : ContDiffAt ℝ 2 connectionReturnTime p :=
    (hcτ.comp p hcI).congr_of_eventuallyEq heq
  have heqP : connectionReturnState =ᶠ[𝓝 p]
      (fun q => toProjectiveState (normalizedMaxCurve (connectionInitialState q) 0 (τ (connectionInitialState q)))) := by
    filter_upwards [heq] with q hq
    simp only [connectionReturnState, hq]
  have hcState : ContDiffAt ℝ 2 connectionReturnState p :=
    (ContDiffAt.comp (g := fun y => toProjectiveState (normalizedMaxCurve y 0 (τ y)))
      (f := connectionInitialState) p hcP hcI).congr_of_eventuallyEq heqP
  have hdI := (hcI.differentiableAt (by norm_num)).hasFDerivAt
  have hdTime := (hdτ.comp p hdI).congr_of_eventuallyEq heq
  have hdState := (hdP.comp p hdI).congr_of_eventuallyEq heqP
  refine ⟨hnearValid.self_of_nhds, hcTime, hcState, ?_, ?_, hnearValid⟩
  · simpa only [hT₀] using hdTime
  · simpa only [hT₀] using hdState

theorem connectionReturn_regular_germ {p : ConnectionParameters} (hμ : 4 ≤ p 0)
    (hu : 0 ≤ p 1 ∧ p 1 ≤ (1 / 10000) / p 0) (hw : 0 < p 2 ∧ p 2 ≤ 1 / 10000) :
    ∀ᶠ q in 𝓝 p, connectionReturnValid q ∧ ContDiffAt ℝ 2 connectionReturnTime q ∧
      ContDiffAt ℝ 2 connectionReturnState q := by
  have H := connectionReturn_regular hμ hu hw
  filter_upwards [H.2.2.2.2.2, H.2.1.eventually (by norm_num), H.2.2.1.eventually (by norm_num)]
    with q hq ht hs
  exact ⟨hq, ht, hs⟩

end BianchiIX
