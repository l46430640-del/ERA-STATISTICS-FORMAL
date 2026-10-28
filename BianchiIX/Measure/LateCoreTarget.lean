import BianchiIX.Dynamics.LateCoreLimit
import BianchiIX.Measure.AwayCoreNull

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

/-- Eventually Taub-avoiding orbits with decaying wall products hit one common null core target at arbitrarily late times. -/
theorem exists_late_null_core_target (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B > (0 : ℝ), volume (coreTaubAvoidance ε B) = 0 ∧
      ∀ x : NormalizedState, stateConstraint x = 1 → positiveWalls x →
        (∀ᶠ t in atTop, ∀ i, ε ≤ normalizedEuclideanDistance (normalizedMaxCurve x 0 t) (taubPoint i)) →
        (∀ i j : Fin 3, i ≠ j → Tendsto
          (fun t => wallValue i (normalizedMaxCurve x 0 t) * wallValue j (normalizedMaxCurve x 0 t)) atTop (𝓝 0)) →
        ∀ r : ℝ, ∃ T > max r 0, ∃ a : Fin 6, ∃ q ∈ coreTaubAvoidance ε B,
          T ∈ normalizedMaxDomain x 0 ∧
          fromProjectiveState (coreRadiusEntry ![2 / q 0, q 1, q 2]) =
            (axisFrame a).map (normalizedMaxCurve x 0 T) ∧
          0 < fderiv ℝ projectiveActiveWall (fromProjectiveState (coreRadiusEntry ![2 / q 0, q 1, q 2]))
            (normalizedField (fromProjectiveState (coreRadiusEntry ![2 / q 0, q 1, q 2]))) := by
  obtain ⟨B, hB, Hnull⟩ := exists_taubAvoidingCore_null hBirkhoff hε
  obtain ⟨N, γ, hγ, _, Hcore⟩ := exists_arbitrarily_late_compact_core hε
  refine ⟨B, hB, (Hnull B ⟨hB, le_rfl⟩).2, ?_⟩
  intro x hc hp ha hprod r
  obtain ⟨T, hT, a, Y, hdom, heq, hphase, hU, hW, hsum, havoid, htrans⟩ :=
    Hcore B hB x hc hp ha (fun _ hΔ => eventually_normalizedWallProductsBound hprod hΔ) r
  have hk : 2 < Y 0 := by linarith only [hphase.1, hγ]
  have hkpos : 0 < Y 0 := by linarith only [hk]
  let q : CoreAngleState := ![2 / Y 0, Y 1, Y 2]
  have hrec : (![2 / q 0, q 1, q 2] : CoreAngleState) = Y := by
    ext i
    fin_cases i
    · change 2 / (2 / Y 0) = Y 0
      field_simp
    · rfl
    · rfl
  have hq : q ∈ coreTaubAvoidance ε B := by
    refine ⟨⟨div_pos (by norm_num) hkpos, (div_lt_one hkpos).mpr hk⟩, hU, hW, hsum, ?_⟩
    rw [hrec]
    exact havoid
  refine ⟨T, hT, a, q, hq, hdom, ?_, ?_⟩
  · rwa [hrec]
  · rwa [hrec]

end BianchiIX
