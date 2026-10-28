import BianchiIX.Dynamics.ActiveWallUpwardHit
import BianchiIX.Dynamics.EntranceTime

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def entranceReturnTime (y : ProjectiveState) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
    projectiveActiveWall (normalizedMaxCurve (fromProjectiveState y) 0 t) = 1}

def entranceReturnState (y : ProjectiveState) : ProjectiveState :=
  toProjectiveState (normalizedMaxCurve (fromProjectiveState y) 0 (entranceReturnTime y))

def entranceReturnValid (y : ProjectiveState) : Prop :=
  let x := fromProjectiveState y
  let T := entranceReturnTime y
  IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain x 0 ∧ projectiveActiveWall (normalizedMaxCurve x 0 t) = 1} T ∧
    (∀ t ∈ Icc 0 T, t ∈ normalizedMaxDomain x 0 ∧ 0 < 1 + normalizedMaxCurve x 0 t 0) ∧
    (∀ t ∈ Ico 0 T, projectiveActiveWall (normalizedMaxCurve x 0 t) < 1) ∧
    (∀ t ∈ Icc 0 T, 0 < normalizedEventRate projectiveActiveWall x 0 t)

theorem entrance_initial_denom_pos {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) : 0 < projectiveStateDenom y := by
  have hr : |coreRadius (y 0) (y 2) - coreRadius (y 0) (y 2)| ≤ coreRadius (y 0) (y 2) / 100 := by
    rw [sub_self, abs_zero]
    linarith
  exact (entrance_denom_bounds hk (entrance_phase_bounds hk hm hr ⟨hv.1.le, hv.2.le⟩)
    hu ⟨hv.1.le, hv.2.le⟩ hw).1

/-- The actual first upward arrival is C2 in all four ordinary initial coordinates. -/
theorem entranceReturn_regular {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    let x := fromProjectiveState y
    let T := entranceReturnTime y
    entranceReturnValid y ∧ ContDiffAt ℝ 2 entranceReturnTime y ∧
      ContDiffAt ℝ 2 entranceReturnState y ∧
      HasFDerivAt entranceReturnTime
        ((normalizedEventTimeDifferential projectiveActiveWall x 0 T).comp
          (fderiv ℝ fromProjectiveState y)) y ∧
      HasFDerivAt entranceReturnState
        (((fderiv ℝ toProjectiveState (normalizedMaxCurve x 0 T)).comp
          (normalizedEventDifferential projectiveActiveWall x 0 T)).comp
          (fderiv ℝ fromProjectiveState y)) y ∧
      (∀ᶠ z in 𝓝 y, entranceReturnValid z) := by
  intro x T₀
  have hD := entrance_initial_denom_pos hk hm hu hv hw
  have hc : stateConstraint x = 1 := fromProjectiveState_constraint hD.ne'
  have hinit : toProjectiveState (normalizedMaxCurve x 0 0) = y := by
    rw [normalizedMaxCurve_initial]
    exact toProjectiveState_fromProjectiveState hD.ne'
  have hA : 0 < normalizedProjectiveRate x 0 0 := by
    unfold normalizedProjectiveRate
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  obtain ⟨T, hT, hhit, _, hregion, _⟩ := exists_normalized_entrance_first_arrival hc hk le_rfl hA
    (by simpa only [hinit] using hm) (by simp only [hinit]) (by simpa only [hinit] using hu)
    (by simpa only [hinit] using hv) (by simpa only [hinit] using hw)
  have hreg : ∀ t ∈ Icc 0 T, t ∈ normalizedMaxDomain x 0 ∧ 0 < 1 + normalizedMaxCurve x 0 t 0 := by
    intro t ht
    have hK : 0 < coreRadius (y 0) (y 2) + 1 := by linarith
    exact ⟨normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1,
      lt_of_lt_of_le (by positivity) (hregion t ht).1⟩
  have hrate : ∀ t ∈ Icc 0 T, 0 < normalizedEventRate projectiveActiveWall x 0 t := by
    intro t ht
    have hv0 : 0 < toProjectiveState (normalizedMaxCurve x 0 0) 2 := by rw [hinit]; exact hv.1
    have hvt := normalized_projective_wall_pos (hreg 0 ⟨le_rfl, hT.le⟩).1 (hreg t ht).1
      (hreg 0 ⟨le_rfl, hT.le⟩).2 (hreg t ht).2 1 hv0
    change 0 < fderiv ℝ projectiveActiveWall (normalizedMaxCurve x 0 t) (normalizedField (normalizedMaxCurve x 0 t))
    rw [projectiveActiveWall_fderiv_field (hreg t ht).2.ne'
      ((normalizedMaxCurve_constraint (hreg t ht).1).trans hc)]
    exact mul_pos (hreg t ht).2 (mul_pos (entranceRegion_clock_pos hk (hregion t ht).2) hvt)
  obtain ⟨τ, hτ, hcτ, hcP, hdτ, hdP, hnear⟩ := exists_activeWall_first_upward_hit_two hT hreg hrate hhit
  have hcI := contDiffAt_fromProjectiveState 2 hD.ne'
  have hnear' := hcI.continuousAt.eventually hnear
  have heq : entranceReturnTime =ᶠ[𝓝 y] (fun z => τ (fromProjectiveState z)) := by
    filter_upwards [hnear'] with z hz
    exact hz.1.csInf_eq
  have hT₀ : T₀ = T := heq.self_of_nhds.trans hτ
  have hnearValid : ∀ᶠ z in 𝓝 y, entranceReturnValid z := by
    filter_upwards [hnear', heq] with z hz htime
    dsimp only [entranceReturnValid]
    rw [htime]
    exact hz
  have hcTime : ContDiffAt ℝ 2 entranceReturnTime y :=
    (hcτ.comp y hcI).congr_of_eventuallyEq heq
  have heqP : entranceReturnState =ᶠ[𝓝 y]
      (fun z => toProjectiveState (normalizedMaxCurve (fromProjectiveState z) 0 (τ (fromProjectiveState z)))) := by
    filter_upwards [heq] with z hz
    simp only [entranceReturnState, hz]
  have hcState : ContDiffAt ℝ 2 entranceReturnState y :=
    (ContDiffAt.comp (g := fun z => toProjectiveState (normalizedMaxCurve z 0 (τ z)))
      (f := fromProjectiveState) y hcP hcI).congr_of_eventuallyEq heqP
  have hdI := (hcI.differentiableAt (by norm_num)).hasFDerivAt
  have hdTime := (hdτ.comp y hdI).congr_of_eventuallyEq heq
  have hdState := (hdP.comp y hdI).congr_of_eventuallyEq heqP
  refine ⟨hnearValid.self_of_nhds, hcTime, hcState, ?_, ?_, hnearValid⟩
  · simpa only [hT₀] using hdTime
  · simpa only [hT₀] using hdState

theorem entranceReturn_regular_germ {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    ∀ᶠ z in 𝓝 y, entranceReturnValid z ∧ ContDiffAt ℝ 2 entranceReturnTime z ∧
      ContDiffAt ℝ 2 entranceReturnState z := by
  have H := entranceReturn_regular hk hm hu hv hw
  filter_upwards [H.2.2.2.2.2, H.2.1.eventually (by norm_num), H.2.2.1.eventually (by norm_num)]
    with z hz ht hs
  exact ⟨hz, ht, hs⟩

end BianchiIX
