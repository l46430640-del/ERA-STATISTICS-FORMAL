import BianchiIX.Measure.OrbitVolumeNull
import BianchiIX.Measure.GeometricException

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

theorem NullInFourCoordinates.linear_image {S : Set NormalizedState}
    (H : NullInFourCoordinates S) (A : NormalizedState →L[ℝ] NormalizedState) :
    NullInFourCoordinates (A '' S) := by
  intro P hP
  rw [← image_comp]
  exact H (P ∘ A) (hP.comp A.differentiable)

theorem nullInFourCoordinates_taubSubspace :
    NullInFourCoordinates {x | normalizedTaubRadiusSq x = 0} := by
  intro P hP
  let C : FourCoordinates → NormalizedState := fun q => ![q 1, 0, q 2, q 3, q 3]
  have hC : Differentiable ℝ C := by
    apply differentiable_pi.mpr
    intro i
    fin_cases i <;> dsimp [C] <;> fun_prop
  have hn : volume ((P ∘ C) '' {q : FourCoordinates | q 0 = 0}) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (hP.comp hC).differentiableOn volume_first_coordinate_zero
  apply measure_mono_null _ hn
  rintro _ ⟨x, hx, rfl⟩
  have hs : x 1 = 0 := by
    dsimp [normalizedTaubRadiusSq, taubRadiusSq] at hx
    nlinarith only [hx, sq_nonneg (x 3 - x 4)]
  have hw : x 3 = x 4 := by
    dsimp [normalizedTaubRadiusSq, taubRadiusSq] at hx
    nlinarith only [hx, sq_nonneg (x 1)]
  refine ⟨![0, x 0, x 2, x 3], by simp, congrArg P ?_⟩
  ext i
  fin_cases i <;> simp [C, hs, hw]

theorem nullInFourCoordinates_taubSubspaces : NullInFourCoordinates taubSubspaces := by
  apply (NullInFourCoordinates.iUnion (fun i : Fin 3 =>
    nullInFourCoordinates_taubSubspace.linear_image (primaryAxisFrame i).map.symm.toContinuousLinearMap)).mono
  intro x hx
  obtain ⟨i, hi⟩ := hx
  exact mem_iUnion.mpr ⟨i, (primaryAxisFrame i).map x, hi,
    (primaryAxisFrame i).map.symm_apply_apply x⟩

def corePhasePhysicalState (q : CoreAngleState) : NormalizedState :=
  fromProjectiveState (coreRadiusEntry ![2 / q 0, q 1, q 2])

theorem contDiffAt_corePhasePhysicalState {q : CoreAngleState}
    (hq : q 0 ∈ Ioo (0 : ℝ) 1)
    (hD : projectiveStateDenom (coreRadiusEntry ![2 / q 0, q 1, q 2]) ≠ 0) :
    ContDiffAt ℝ 1 corePhasePhysicalState q := by
  have hk : 1 < 2 / q 0 := (lt_div_iff₀ hq.1).mpr (by linarith only [hq.2])
  have hcoord : ContDiffAt ℝ 1 (fun z : CoreAngleState => (![2 / z 0, z 1, z 2] : CoreAngleState)) q := by
    have hne := hq.1.ne'
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  exact (contDiffAt_fromProjectiveState 1 hD).comp q
    ((contDiffAt_coreRadiusEntry 1 hk).comp q hcoord)

theorem nullInFourCoordinates_fixed_taub_avoidance
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) {ε : ℝ} (hε : 0 < ε) :
    NullInFourCoordinates {x | x ∈ physicalPhaseSpace ∧
      (∀ᶠ t in atTop, ∀ i, ε ≤ normalizedEuclideanDistance (normalizedMaxCurve x 0 t) (taubPoint i)) ∧
      WallProductDecay x} := by
  obtain ⟨B, _, hnull, Hhit⟩ := exists_late_null_core_target hBirkhoff hε
  let Z := coreTaubAvoidance ε B ∩
    {q | projectiveStateDenom (coreRadiusEntry ![2 / q 0, q 1, q 2]) ≠ 0}
  let C : Fin 6 → CoreAngleState → NormalizedState := fun a q =>
    (axisFrame a).map.symm (corePhasePhysicalState q)
  have hC (a : Fin 6) : ∀ q ∈ Z, ContDiffAt ℝ 1 (C a) q := fun q hq =>
    (axisFrame a).map.symm.contDiff.contDiffAt.comp q
      (contDiffAt_corePhasePhysicalState hq.1.1 hq.2)
  have hn := NullInFourCoordinates.iUnion (fun a => nullInFourCoordinates_orbitSaturation
    (hC a) (measure_mono_null inter_subset_left hnull))
  apply hn.mono
  intro x hx
  obtain ⟨T, _, a, q, hq, hdom, heq, _⟩ := Hhit x hx.1.2 hx.1.1 hx.2.1 hx.2.2 0
  have hposit : positiveWalls (corePhasePhysicalState q) := by
    change positiveWalls (fromProjectiveState _)
    rw [heq]
    exact ((axisFrame a).positive _).mpr ((maximalNormalizedSolution x 0).physical hx.1.1 hx.1.2 hdom).1
  have hqZ : q ∈ Z := by
    refine ⟨hq, ?_⟩
    intro hz
    simpa [corePhasePhysicalState, fromProjectiveState, hz] using hposit.1
  have hentry : C a q = normalizedMaxCurve x 0 T := by
    dsimp [C, corePhasePhysicalState]
    rw [heq, ContinuousLinearEquiv.symm_apply_apply]
  have hinv := normalizedMaxCurve_inverse hdom
  rw [← hentry] at hinv
  exact mem_iUnion.mpr ⟨a, C a q, mem_image_of_mem (C a) hqZ, -T, hinv.1, hinv.2⟩

theorem nullInFourCoordinates_geometricException
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    (hBrehm : Literature.BrehmIXAttractorInput) : NullInFourCoordinates geometricException := by
  let E := fun n : ℕ => {x | x ∈ physicalPhaseSpace ∧
    (∀ᶠ t in atTop, ∀ i, 1 / (n + 1 : ℝ) ≤
      normalizedEuclideanDistance (normalizedMaxCurve x 0 t) (taubPoint i)) ∧ WallProductDecay x}
  have hE : ∀ n, NullInFourCoordinates (E n) := fun n =>
    nullInFourCoordinates_fixed_taub_avoidance hBirkhoff (by positivity)
  apply (nullInFourCoordinates_taubSubspaces.union (NullInFourCoordinates.iUnion hE)).mono
  intro x hx
  by_cases hT : x ∈ taubSubspaces
  · exact Or.inl hT
  · obtain ⟨ε, hε, H⟩ := hx.2.resolve_left hT
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact Or.inr (mem_iUnion.mpr ⟨n, hx.1,
      H.mono (fun t ht i => hn.le.trans (ht i)), hBrehm.wallProductDecay hx.1 hT⟩)

end BianchiIX
