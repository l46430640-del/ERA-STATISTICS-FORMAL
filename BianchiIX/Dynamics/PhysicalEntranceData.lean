import BianchiIX.Dynamics.CompactReferenceEntrance
import BianchiIX.Analysis.CompactSmoothNeighborhood

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- Time, projective endpoint, physical endpoint, and radius in ordinary physical initial coordinates. -/
def physicalEntranceData (x : NormalizedState) : ℝ × ProjectiveState × NormalizedState × ℝ :=
  let y := toProjectiveState x
  let P := entranceReturnState y
  (entranceReturnTime y, P, fromProjectiveState P, coreRadius (P 0) (P 2))

theorem normalizedState_norm_sub_le_euclidean (x y : NormalizedState) :
    ‖x - y‖ ≤ normalizedEuclideanDistance x y := by
  apply (pi_norm_le_iff_of_nonneg (normalizedEuclideanDistance_nonneg x y)).mpr
  intro i
  simpa only [Pi.sub_apply, Real.norm_eq_abs, Real.dist_eq, normalizedEuclideanDistance] using
    PiLp.dist_apply_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 5)) (WithLp.toLp 2 y) i

theorem physicalEntranceData_reference {k v : ℝ} (hk : 2 ≤ k) (hv : 0 < v ∧ v < 1) :
    physicalEntranceData (fromProjectiveState (referenceEntranceState k v)) =
      (referenceShiftClock k (-referenceHeightTime k v) (-referenceHalfTime k),
        referencePulse k (-referenceHalfTime k),
        fromProjectiveState (referencePulse k (-referenceHalfTime k)), k) := by
  have hD : 0 < projectiveStateDenom (referenceEntranceState k v) := by
    simp [referenceEntranceState, projectiveStateDenom, projectiveDenom, curvature]
    positivity
  obtain ⟨ht, hP⟩ := referenceEntrance_return (k := k) (by linarith only [hk]) hv
  simp only [physicalEntranceData, toProjectiveState_fromProjectiveState hD.ne', ht, hP]
  have hR : coreRadius (referencePulse k (-referenceHalfTime k) 0) (referencePulse k (-referenceHalfTime k) 2) = k := by
    rw [coreRadius, referencePulse_energy, Real.sqrt_sq (by linarith only [hk])]
  rw [hR]

theorem physicalEntranceData_reference_germ {k v : ℝ} (hk : 2 ≤ k) (hv : 0 < v ∧ v < 1) :
    ∀ᶠ x in 𝓝 (fromProjectiveState (referenceEntranceState k v)),
      (0 < 1 + x 0 ∧ entranceReturnValid (toProjectiveState x)) ∧
        ContDiffAt ℝ 2 physicalEntranceData x := by
  let q := referenceEntranceState k v
  let z := fromProjectiveState q
  have hD : 0 < projectiveStateDenom q := by
    simp [q, referenceEntranceState, projectiveStateDenom, projectiveDenom, curvature]
    positivity
  have hA : 0 < 1 + z 0 := fromProjectiveState_clock_pos hD
  have he : toProjectiveState z = q := toProjectiveState_fromProjectiveState hD.ne'
  have hqR : 7 / 4 ≤ coreRadius (q 0) (q 2) := by
    rw [referenceEntrance_radius (by linarith only [hk]) ⟨hv.1, by linarith only [hk, hv.2]⟩]
    linarith only [hk]
  have hreg := entranceReturn_regular hqR
    (show 1 ≤ q 0 from le_add_of_nonneg_right (Real.sqrt_nonneg _))
    (by dsimp [q, referenceEntranceState]; norm_num) hv (by dsimp [q, referenceEntranceState]; norm_num)
  have hq := contDiffAt_toProjectiveState 2 hA.ne'
  have hT : ContDiffAt ℝ 2 (fun x => entranceReturnTime (toProjectiveState x)) z :=
    (he.symm ▸ hreg.2.1).comp z hq
  have hP : ContDiffAt ℝ 2 (fun x => entranceReturnState (toProjectiveState x)) z :=
    (he.symm ▸ hreg.2.2.1).comp z hq
  have hval : entranceReturnState (toProjectiveState z) = referencePulse k (-referenceHalfTime k) := by
    rw [he]
    exact (referenceEntrance_return (by linarith only [hk]) hv).2
  have hPD : 0 < projectiveStateDenom (entranceReturnState (toProjectiveState z)) := by
    rw [hval]
    exact referencePulse_denom_pos _ _
  have hPV : 0 < entranceReturnState (toProjectiveState z) 2 := by
    rw [hval]
    exact referencePulse_active_pos (by linarith only [hk]) _
  have hX := (contDiffAt_fromProjectiveState 2 hPD.ne').comp z hP
  have hR := contDiffAt_pi.mp ((contDiffAt_toCoreAngleState 2 hPV).comp z hP) 0
  have hF : ContDiffAt ℝ 2 physicalEntranceData z := hT.prodMk (hP.prodMk (hX.prodMk hR))
  have hnear := hq.continuousAt.eventually (he.symm ▸ hreg.2.2.2.2.2)
  have hnearA : ∀ᶠ x in 𝓝 z, 0 < 1 + x 0 :=
    (show Continuous (fun x : NormalizedState => 1 + x 0) from
      continuous_const.add (continuous_apply (0 : Fin 5))).continuousAt.eventually (isOpen_Ioi.mem_nhds hA)
  filter_upwards [hnearA, hnear, hF.eventually (by norm_num)] with x hx hvx hFx
  exact ⟨⟨hx, hvx⟩, hFx⟩

/-- All event observables are controlled directly by physical entrance error on the compact reference family. -/
theorem exists_compact_physicalEntrance_data {K a : ℝ} (ha : 0 < a) :
    ∃ δ > (0 : ℝ), ∃ C ≥ (1 : ℝ), ∀ k ∈ Icc 2 K, ∀ v ∈ Icc a (1 / 2),
      ∀ x : NormalizedState,
        normalizedEuclideanDistance (fromProjectiveState (referenceEntranceState k v)) x ≤ δ →
        (0 < 1 + x 0 ∧ entranceReturnValid (toProjectiveState x)) ∧
          ContDiffAt ℝ 2 physicalEntranceData x ∧ ‖physicalEntranceData x‖ ≤ C ∧
          ‖physicalEntranceData x - physicalEntranceData (fromProjectiveState (referenceEntranceState k v))‖ ≤
            C * normalizedEuclideanDistance (fromProjectiveState (referenceEntranceState k v)) x := by
  let Q : ℝ × ℝ → NormalizedState := fun p => fromProjectiveState (referenceEntranceState p.1 p.2)
  let B : Set (ℝ × ℝ) := Icc 2 K ×ˢ Icc a (1 / 2)
  have hQ : ContinuousOn Q B := by
    intro p hp
    have hD : 0 < projectiveStateDenom (referenceEntranceState p.1 p.2) := by
      simp [referenceEntranceState, projectiveStateDenom, projectiveDenom, curvature]
      positivity
    exact ((contDiffAt_fromProjectiveState 1 hD.ne').continuousAt.comp
      (f := fun p : ℝ × ℝ => referenceEntranceState p.1 p.2)
      continuous_referenceEntranceState.continuousAt).continuousWithinAt
  have hS : IsCompact (Q '' B) := (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn hQ
  obtain ⟨δ, hδ, C, hC, H⟩ := exists_compact_smooth_neighborhood hS
    (P := fun x => 0 < 1 + x 0 ∧ entranceReturnValid (toProjectiveState x))
    (f := physicalEntranceData) (by
      rintro z ⟨⟨k, v⟩, ⟨hk, hv⟩, rfl⟩
      exact physicalEntranceData_reference_germ hk.1 ⟨ha.trans_le hv.1, by linarith only [hv.2]⟩)
  refine ⟨δ, hδ, C, hC, ?_⟩
  intro k hk v hv x hx
  let z := fromProjectiveState (referenceEntranceState k v)
  have hnorm : ‖x - z‖ ≤ normalizedEuclideanDistance z x := by
    rw [norm_sub_rev]
    exact normalizedState_norm_sub_le_euclidean z x
  have HH := H z ⟨(k, v), ⟨hk, hv⟩, rfl⟩ x (hnorm.trans hx)
  exact ⟨HH.1, HH.2.1, HH.2.2.1,
    HH.2.2.2.trans (mul_le_mul_of_nonneg_left hnorm (by linarith only [hC]))⟩

end BianchiIX
