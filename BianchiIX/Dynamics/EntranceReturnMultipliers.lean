import BianchiIX.Dynamics.EntranceReturn
import BianchiIX.Dynamics.ProjectiveWallMultipliers

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def entranceReturnMultiplier (y : ProjectiveState) (i : Fin 3) : ℝ :=
  normalizedProjectiveWallMultiplier (fromProjectiveState y) (entranceReturnTime y) i

theorem entranceReturnMultiplier_pos (y : ProjectiveState) (i : Fin 3) :
    0 < entranceReturnMultiplier y i := normalizedProjectiveWallMultiplier_pos _ _ _

theorem entranceReturn_wall_factorization {y : ProjectiveState}
    (hD : 0 < projectiveStateDenom y) (hy : entranceReturnValid y) (i : Fin 3) :
    entranceReturnState y i.succ = y i.succ * entranceReturnMultiplier y i := by
  have hA := (hy.2.1 _ ⟨hy.1.1.1.le, le_rfl⟩).2
  have H := normalizedProjectiveWallMultiplier_formula hy.1.1.2.1 (fromProjectiveState_clock_pos hD) hA i
  rw [toProjectiveState_fromProjectiveState hD.ne'] at H
  exact H

/-- The wall factors and their logarithms are C2 even when a stable entrance wall vanishes. -/
theorem entranceReturnMultiplier_regular {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) (i : Fin 3) :
    ContDiffAt ℝ 2 (fun z => entranceReturnMultiplier z i) y ∧
      ContDiffAt ℝ 2 (fun z => Real.log (entranceReturnMultiplier z i)) y ∧
      (∀ᶠ z in 𝓝 y, entranceReturnState z i.succ = z i.succ * entranceReturnMultiplier z i) := by
  have hD := entrance_initial_denom_pos hk hm hu hv hw
  have H := entranceReturn_regular hk hm hu hv hw
  have hmultip := contDiffAt_normalizedProjectiveWallMultiplier_two
    (contDiffAt_fromProjectiveState 2 hD.ne') H.2.1 H.1.1.1.1.le
    (fun _ ht => (H.1.2.1 _ ht).1) (fromProjectiveState_clock_pos hD)
    (H.1.2.1 _ ⟨H.1.1.1.1.le, le_rfl⟩).2 i
  refine ⟨hmultip.1, hmultip.2, ?_⟩
  filter_upwards [H.2.2.2.2.2, continuous_projectiveStateDenom.continuousAt.eventually
    (isOpen_Ioi.mem_nhds hD)] with z hz hDz
  exact entranceReturn_wall_factorization hDz hz i

theorem entranceReturn_wall_differential {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) (i : Fin 3) (v : ProjectiveState) :
    fderiv ℝ entranceReturnState y v i.succ =
      v i.succ * entranceReturnMultiplier y i +
        y i.succ * fderiv ℝ (fun z => entranceReturnMultiplier z i) y v := by
  have H := entranceReturn_regular hk hm hu hv hw
  have hΛ := entranceReturnMultiplier_regular hk hm hu hv hw i
  have hprod := ((hasFDerivAt_apply (𝕜 := ℝ) i.succ y).mul
    (hΛ.1.differentiableAt (by norm_num)).hasFDerivAt).congr_of_eventuallyEq hΛ.2.2
  have hout := (hasFDerivAt_apply (𝕜 := ℝ) i.succ (entranceReturnState y)).comp y
    (H.2.2.1.differentiableAt (by norm_num)).hasFDerivAt
  have heq := congrArg (fun L : ProjectiveState →L[ℝ] ℝ => L v) (hout.unique hprod)
  simpa only [ContinuousLinearMap.comp_apply, add_apply,
    smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, mul_comm, add_comm] using heq

theorem entranceReturn_zero_wall_differential {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) (i : Fin 3) (hi : y i.succ = 0) :
    entranceReturnState y i.succ = 0 ∧
      ∀ v : ProjectiveState, fderiv ℝ entranceReturnState y v i.succ =
        v i.succ * entranceReturnMultiplier y i := by
  constructor
  · simpa only [hi, zero_mul] using entranceReturn_wall_factorization
      (entrance_initial_denom_pos hk hm hu hv hw) (entranceReturn_regular hk hm hu hv hw).1 i
  · intro v
    simpa only [hi, zero_mul, add_zero] using entranceReturn_wall_differential hk hm hu hv hw i v

end BianchiIX
