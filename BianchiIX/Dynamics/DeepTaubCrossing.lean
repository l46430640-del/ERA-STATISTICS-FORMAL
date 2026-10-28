import BianchiIX.Dynamics.TaubWeightedRadius
import BianchiIX.Analysis.LastSublevelInterval
import BianchiIX.Dynamics.SingleWallExit
import BianchiIX.Dynamics.TaubDistance
import Mathlib.Topology.Order.Lattice

noncomputable section

namespace BianchiIX

open Set

theorem normalizedTaubDistance_sq (x : NormalizedState) :
    normalizedEuclideanDistance x (taubPoint 0) ^ 2 =
      (1 + x 0) ^ 2 + normalizedTaubRadiusSq x + x 2 ^ 2 + 2 * x 3 * x 4 := by
  rw [normalizedEuclideanDistance_sq]
  simp [taubPoint, Fin.sum_univ_succ, normalizedTaubRadiusSq, taubRadiusSq]
  ring

/-- A deep Taub visit is preceded by a transverse crossing of the fixed small main-wall section. -/
theorem exists_deep_taub_crossing {α : ℝ → NormalizedState} {a b h d ε : ℝ}
    (hab : a < b) (hh : 0 < h) (hhmax : h ≤ 1 / 16) (hd : 0 < d) (hdh : d < h / 8)
    (hε : 0 < ε) (hεd : ε < d / 4)
    (hα : ∀ t ∈ Icc a b, HasDerivAt α (normalizedField (α t)) t)
    (hc : ∀ t ∈ Icc a b, stateConstraint (α t) = 1)
    (hp : ∀ t ∈ Icc a b, positiveWalls (α t))
    (hprod : ∀ t ∈ Icc a b, normalizedWallProductsBound (d / 4) (α t))
    (ha : 4 * ε ^ 2 < normalizedTaubRadiusSq (α a))
    (hb : normalizedEuclideanDistance (α b) (taubPoint 0) ≤ ε) :
    ∃ c ∈ Ioo a b, α c 2 = h ∧ α c 0 < -1 / 2 ∧ |α c 1| < d ∧
      α c 3 < d ∧ α c 4 < d ∧
      normalizedTaubRadiusSq (α c) ≤ 2 * normalizedTaubRadiusSq (α b) ∧
      normalizedField (α c) 2 ≤ -5 * h / 4 := by
  have hbmem : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hεh : ε < h := by linarith only [hεd, hdh, hd, hh]
  have hεsmall : ε < 1 / 16 := hεh.trans_le hhmax
  have hdist : normalizedEuclideanDistance (α b) (taubPoint 0) ^ 2 ≤ ε ^ 2 :=
    pow_le_pow_left₀ (normalizedEuclideanDistance_nonneg _ _) hb 2
  rw [normalizedTaubDistance_sq] at hdist
  have hR0 : 0 ≤ normalizedTaubRadiusSq (α b) := taubRadiusSq_nonneg _ _ _
  have hbc : 0 ≤ α b 3 * α b 4 := mul_nonneg (hp b hbmem).2.1.le (hp b hbmem).2.2.le
  have hRb : normalizedTaubRadiusSq (α b) ≤ ε ^ 2 := by
    nlinarith only [hdist, hbc, sq_nonneg (1 + α b 0), sq_nonneg (α b 2)]
  have hpb : α b 0 < -1 / 2 := by
    nlinarith [sq_nonneg (α b 0 + 1 - ε), sq_nonneg (α b 2)]
  have hnb : α b 2 < h := by
    have hn := (hp b hbmem).1
    nlinarith [sq_nonneg (1 + α b 0)]
  let f := fun t => max (α t 0 + 1 / 2) (α t 2 - h)
  have hf : ContinuousOn f (Icc a b) := by
    have hpcont := HasDerivAt.continuousOn fun t ht => (hasDerivAt_normalized_components (hα t ht)).1
    have hncont := HasDerivAt.continuousOn fun t ht => (hasDerivAt_normalized_components (hα t ht)).2.2.1
    exact (hpcont.add continuousOn_const).sup (hncont.sub continuousOn_const)
  obtain ⟨c, hcab, hboundary, hclosed, _⟩ := exists_last_sublevel_interval hab hf
    (max_lt (by linarith only [hpb]) (by linarith only [hnb]))
  have hsub : Icc c b ⊆ Icc a b := Icc_subset_Icc hcab.1 le_rfl
  have hbounds (t : ℝ) (ht : t ∈ Icc c b) : α t 0 ≤ -1 / 2 ∧ α t 2 ≤ h := by
    have H := max_le_iff.mp (hclosed t ht)
    constructor <;> linarith only [H.1, H.2]
  have hwall (t : ℝ) (ht : t ∈ Icc a b) :
      (α t 2) ^ 2 + (α t 3) ^ 2 + (α t 4) ^ 2 ≤ 2 := by
    have H := (constraint_small_wall_products (hc t ht) (hprod t ht).1
      (hprod t ht).2.1 (hprod t ht).2.2
      ⟨by positivity, by linarith only [hdh, hhmax]⟩).2.1
    nlinarith only [H, sq_nonneg (α t 0), sq_nonneg (α t 1)]
  have hmono := weightedTaubRadiusSq_monotone (fun t ht => hα t (hsub ht))
    (fun t ht => hc t (hsub ht)) (fun t ht => (hbounds t ht).1)
    (fun t ht => (hp t (hsub ht)).1.le) (fun t ht => hwall t (hsub ht))
  have hcc : c ∈ Icc c b := ⟨le_rfl, hcab.2.le⟩
  have hcfull : c ∈ Icc a b := hsub hcc
  have hRc := taubRadiusSq_backward_bound hcab.2.le hhmax hmono (hbounds c hcc).2 (hp b hbmem).1.le
  have hRε : normalizedTaubRadiusSq (α c) ≤ 2 * ε ^ 2 := hRc.trans (by linarith only [hRb])
  have hca : a < c := by
    apply lt_of_le_of_ne hcab.1
    intro heq
    subst c
    nlinarith only [ha, hRε, sq_nonneg ε]
  have hpc : α c 0 < -1 / 2 := by
    have Hc := hc c hcfull
    have Hn := (hp c hcfull).1.le
    have Hbc := mul_nonneg Hn (add_nonneg (hp c hcfull).2.1.le (hp c hcfull).2.2.le)
    have Hrad : (α c 0) ^ 2 + normalizedTaubRadiusSq (α c) + (α c 2) ^ 2 -
        2 * α c 2 * (α c 3 + α c 4) = 1 := by
      dsimp [stateConstraint, constraint, shearSq, curvature] at Hc
      dsimp [normalizedTaubRadiusSq, taubRadiusSq]
      nlinarith only [Hc]
    have Hn2 := pow_le_pow_left₀ Hn ((hbounds c hcc).2.trans hhmax) 2
    have Hε2 := pow_le_pow_left₀ hε.le hεsmall.le 2
    have Hple := (hbounds c hcc).1
    apply lt_of_le_of_ne Hple
    intro heq
    rw [heq] at Hrad
    nlinarith only [Hrad, Hbc, Hn2, Hε2, hRε]
  have hnc : α c 2 = h := by
    have heq : f c = 0 := hboundary.resolve_left (ne_of_gt hca)
    apply le_antisymm (hbounds c hcc).2
    by_contra! hlt
    have H : f c < 0 := max_lt (by linarith only [hpc]) (by linarith only [hlt])
    rw [heq] at H
    exact (lt_irrefl 0) H
  have hs : |α c 1| < d := by
    have H := sq_nonneg (α c 3 - α c 4)
    dsimp [normalizedTaubRadiusSq, taubRadiusSq] at hRε
    rw [abs_lt]
    constructor <;> nlinarith
  have hsum : α c 3 + α c 4 < d := by
    have H := (hprod c hcfull).2.1
    have Hr : (α c 3 - α c 4) ^ 2 ≤ 2 * ε ^ 2 := by
      dsimp [normalizedTaubRadiusSq, taubRadiusSq] at hRε
      nlinarith only [hRε, sq_nonneg (α c 1)]
    nlinarith only [H, Hr, hεd, hε, hd, sq_nonneg (d - 4 * ε)]
  refine ⟨c, ⟨hca, hcab.2⟩, hnc, hpc, hs, ?_, ?_, hRc, ?_⟩
  · linarith only [hsum, (hp c hcfull).2.2]
  · linarith only [hsum, (hp c hcfull).2.1]
  · change rateOne (α c 0) (α c 1) * α c 2 ≤ _
    rw [hnc]
    have H := mul_le_mul_of_nonneg_right (taub_negative_wall_rate (s := α c 1) hpc.le) hh.le
    linarith only [H]

end BianchiIX
