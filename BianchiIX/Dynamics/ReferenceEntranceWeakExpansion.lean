import BianchiIX.Dynamics.EntranceWeakGerm
import BianchiIX.Dynamics.ReferenceEntranceMixedResponse
import Mathlib.Analysis.Asymptotics.Lemmas

noncomputable section

namespace BianchiIX

open Set Filter Asymptotics
open scoped Topology

theorem referenceEntrance_weak_regular {k v : ℝ} (hk : 7 / 4 ≤ k) (hv : 0 < v ∧ v < 1) :
    ContDiffAt ℝ 2 entranceWeakQuadraticLoss (referenceEntranceState k v) ∧
      (∀ᶠ z in 𝓝 (referenceEntranceState k v), z 1 = 0 →
        coreRadius (entranceReturnState z 0) (entranceReturnState z 2) =
          entranceStableRadius z - (z 3) ^ 2 * entranceWeakQuadraticLoss z ∧
          0 < entranceWeakQuadraticLoss z) ∧
      0 < entranceWeakQuadraticLoss (referenceEntranceState k v) := by
  let y := referenceEntranceState k v
  have hR := referenceEntrance_radius (show 0 < k by linarith) ⟨hv.1, by linarith [hv.2]⟩
  have hk' : 7 / 4 ≤ coreRadius (y 0) (y 2) := by rw [hR]; exact hk
  have hm : 1 ≤ y 0 := le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000 := by dsimp [y, referenceEntranceState]; norm_num
  have hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000 := by dsimp [y, referenceEntranceState]; norm_num
  exact ⟨contDiffAt_entranceWeakQuadraticLoss_two hk' hm hu hv hw,
    entranceReturn_weak_quadratic_germ hk' hm hu hv hw,
    (entranceReturn_weak_quadratic hk' hm rfl hv hw).2⟩

theorem EntranceRadialInverseAt.referenceEntrance_weak_factorization_germ {k v : ℝ}
    (hk : 7 / 4 ≤ k) (hv : 0 < v ∧ v < 1)
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (referenceEntranceState k v) Ψ) :
    ∀ᶠ w : ℝ in 𝓝 0,
      coreRadius (entranceReturnState (Ψ ![k, 0, v, w]) 0) (entranceReturnState (Ψ ![k, 0, v, w]) 2) =
        k - w ^ 2 * entranceWeakQuadraticLoss (Ψ ![k, 0, v, w]) := by
  let c := fun w : ℝ => (![k, 0, v, w] : ProjectiveState)
  have hc : Tendsto c (𝓝 0) (𝓝 (entranceRadialCoordinates (referenceEntranceState k v))) := by
    rw [referenceEntrance_radialCoordinates hk hv]
    exact (by fun_prop : Continuous c).continuousAt.tendsto
  have hΨ : Tendsto Ψ (𝓝 (entranceRadialCoordinates (referenceEntranceState k v)))
      (𝓝 (referenceEntranceState k v)) := by
    simpa only [HΨ.apply_base] using HΨ.contDiffAt.continuousAt.tendsto
  have hg := (hΨ.comp hc).eventually (referenceEntrance_weak_regular hk hv).2.1
  filter_upwards [hg, hc.eventually HΨ.right_inverse] with w hgw hcoord
  have hu : Ψ (c w) 1 = 0 := congrFun hcoord 1
  have hw : Ψ (c w) 3 = w := congrFun hcoord 3
  have hr : entranceStableRadius (Ψ (c w)) = k := congrFun hcoord 0
  have H := (hgw hu).1
  dsimp only [Function.comp_apply] at H
  rw [hr, hw] at H
  exact H

/-- The exact quadratic factor and its continuity give a two-sided little-o expansion. -/
theorem EntranceRadialInverseAt.referenceEntrance_weak_expansion {k v : ℝ}
    (hk : 7 / 4 ≤ k) (hv : 0 < v ∧ v < 1)
    {Ψ : ProjectiveState → ProjectiveState} (HΨ : EntranceRadialInverseAt (referenceEntranceState k v) Ψ) :
    (fun w : ℝ =>
      coreRadius (entranceReturnState (Ψ ![k, 0, v, w]) 0) (entranceReturnState (Ψ ![k, 0, v, w]) 2) - k +
        entranceWeakQuadraticLoss (referenceEntranceState k v) * w ^ 2) =o[𝓝 0] (fun w => w ^ 2) := by
  let y := referenceEntranceState k v
  let c := fun w : ℝ => (![k, 0, v, w] : ProjectiveState)
  let Q := entranceWeakQuadraticLoss
  have hc : Tendsto c (𝓝 0) (𝓝 (entranceRadialCoordinates y)) := by
    rw [referenceEntrance_radialCoordinates hk hv]
    exact (by fun_prop : Continuous c).continuousAt.tendsto
  have hΨ : Tendsto Ψ (𝓝 (entranceRadialCoordinates y)) (𝓝 y) := by
    simpa only [HΨ.apply_base] using HΨ.contDiffAt.continuousAt.tendsto
  have hQ : Tendsto (fun w => Q (Ψ (c w))) (𝓝 0) (𝓝 (Q y)) :=
    (referenceEntrance_weak_regular hk hv).1.continuousAt.tendsto.comp (hΨ.comp hc)
  have hzero : Tendsto (fun w => Q y - Q (Ψ (c w))) (𝓝 0) (𝓝 0) := by
    simpa only [sub_self] using hQ.const_sub (Q y)
  have hsmall := ((isLittleO_one_iff ℝ).mpr hzero).mul_isBigO (isBigO_refl (fun w : ℝ => w ^ 2) (𝓝 0))
  apply hsmall.congr' ?_ (Eventually.of_forall (fun _ => one_mul _))
  filter_upwards [HΨ.referenceEntrance_weak_factorization_germ hk hv] with w hw
  rw [hw]
  dsimp [Q, y, c]
  ring

theorem exists_referenceEntrance_weak_expansion {k v : ℝ} (hk : 7 / 4 ≤ k) (hv : 0 < v ∧ v < 1) :
    ∃ Ψ : ProjectiveState → ProjectiveState,
      EntranceRadialInverseAt (referenceEntranceState k v) Ψ ∧
      0 < entranceWeakQuadraticLoss (referenceEntranceState k v) ∧
      (fun w : ℝ =>
        coreRadius (entranceReturnState (Ψ ![k, 0, v, w]) 0) (entranceReturnState (Ψ ![k, 0, v, w]) 2) - k +
          entranceWeakQuadraticLoss (referenceEntranceState k v) * w ^ 2) =o[𝓝 0] (fun w => w ^ 2) := by
  obtain ⟨Ψ, HΨ⟩ := exists_entranceRegion_radial_inverse hk (referenceEntrance_region hk hv) hv.1
  exact ⟨Ψ, HΨ, (referenceEntrance_weak_regular hk hv).2.2, HΨ.referenceEntrance_weak_expansion hk hv⟩

end BianchiIX
