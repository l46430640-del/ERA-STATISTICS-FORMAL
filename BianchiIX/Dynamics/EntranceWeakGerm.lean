import BianchiIX.Dynamics.EntranceWeakRegularity

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Rescaling the flight to [0,1] supplies one neighborhood for the entire moving segment. -/
theorem entranceReturn_weak_quadratic_germ {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    ∀ᶠ z in 𝓝 y, z 1 = 0 →
      coreRadius (entranceReturnState z 0) (entranceReturnState z 2) =
        entranceStableRadius z - (z 3) ^ 2 * entranceWeakQuadraticLoss z ∧
        0 < entranceWeakQuadraticLoss z := by
  have H := entranceReturn_regular hk hm hu hv hw
  have hD := entrance_initial_denom_pos hk hm hu hv hw
  have hy := entranceReturn_region hk hm hu hv hw
  have hτbase : ContinuousAt entranceReturnTime y := H.2.1.continuousAt
  let F := fun p : ProjectiveState × ℝ => projectiveOriginalFlow p.1 0 (p.2 * entranceReturnTime p.1)
  have hseg : ∀ᶠ z in 𝓝 y, ∀ s ∈ Icc (0 : ℝ) 1,
      2 ≤ F (z, s) 0 ∧ |F (z, s) 3| < 1 / 200 := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    have ht : s * entranceReturnTime y ∈ Icc 0 (entranceReturnTime y) :=
      ⟨mul_nonneg hs.1 H.1.1.1.1.le, by simpa using mul_le_mul_of_nonneg_right hs.2 H.1.1.1.1.le⟩
    have hflow : ContinuousAt (fun p : ProjectiveState × ℝ => projectiveOriginalFlow p.1 0 p.2)
        (y, s * entranceReturnTime y) :=
      (contDiffAt_projectiveOriginalFlow_two hD (H.1.2.1 _ ht).1 (H.1.2.1 _ ht).2).continuousAt
    have hτ : ContinuousAt (fun p : ProjectiveState × ℝ => entranceReturnTime p.1) (y, s) :=
      ContinuousAt.comp (g := entranceReturnTime)
        (f := fun p : ProjectiveState × ℝ => p.1) (x := (y, s)) hτbase continuousAt_fst
    have hp : ContinuousAt (fun p : ProjectiveState × ℝ => (p.1, p.2 * entranceReturnTime p.1)) (y, s) :=
      continuousAt_fst.prodMk (continuousAt_snd.mul hτ)
    have hc : ContinuousAt F (y, s) :=
      ContinuousAt.comp (g := fun p : ProjectiveState × ℝ => projectiveOriginalFlow p.1 0 p.2)
        (f := fun p : ProjectiveState × ℝ => (p.1, p.2 * entranceReturnTime p.1))
        (x := (y, s)) hflow hp
    have hmc : ContinuousAt (fun p => F p 0) (y, s) := (continuous_apply 0).continuousAt.comp hc
    have hwc : ContinuousAt (fun p => |F p 3|) (y, s) := ((continuous_apply 3).continuousAt.comp hc).abs
    have hm' : 2 < F (y, s) 0 := by linarith [(entranceRegion_phase hk (hy _ ht)).1]
    have hw' : |F (y, s) 3| < 1 / 200 := by
      rw [abs_of_nonneg (hy _ ht).2.2.2.2.1]
      linarith [(hy _ ht).2.2.2.2.2]
    exact ((hmc.eventually (eventually_gt_nhds hm')).and
      (hwc.eventually (eventually_lt_nhds hw'))).mono (fun _ h => ⟨h.1.le, h.2⟩)
  filter_upwards [H.2.2.2.2.2, continuous_projectiveStateDenom.continuousAt.eventually
    (eventually_gt_nhds hD), (continuous_apply (2 : Fin 4)).continuousAt.eventually
    (eventually_gt_nhds hv.1), hseg] with z hz hDz hvz hsz
  intro huz
  have hprefix : ∀ t ∈ Icc 0 (entranceReturnTime z),
      2 ≤ projectiveOriginalFlow z 0 t 0 ∧ |projectiveOriginalFlow z 0 t 3| < 1 / 200 := by
    intro t ht
    have ht' : t / entranceReturnTime z ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg ht.1 hz.1.1.1.le, (div_le_one hz.1.1.1).mpr ht.2⟩
    have HH := hsz _ ht'
    dsimp only [F] at HH
    rw [div_mul_cancel₀ _ hz.1.1.1.ne'] at HH
    exact HH
  exact entranceReturn_weak_quadratic_of_segment hDz hz huz hvz
    (fun t ht => (hprefix t ht).1) (fun t ht => (hprefix t ht).2)

end BianchiIX
