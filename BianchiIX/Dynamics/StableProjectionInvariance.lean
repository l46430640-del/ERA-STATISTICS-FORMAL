import BianchiIX.Dynamics.StableBoundaryLimit
import BianchiIX.Dynamics.FlowComposition

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem stableBoundaryOrbit_restart {m c u w s t : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    let Y := stableBoundaryOrbit m u w
    stableBoundaryOrbit (Y s 0) (Y s 1) (Y s 3) t = Y (t + s) := by
  intro Y
  let x := fromProjectiveState (stableBoundaryEntry m u w)
  have hx : stateConstraint x = 1 :=
    fromProjectiveState_constraint (ne_of_gt (stableBoundaryEntry_denom_pos m u w))
  have hglobal := stableBoundaryOrbit_global hc hm hu hw s hs
  have hK : 0 < c + 1 := by linarith
  have hAs : 0 < 1 + normalizedMaxCurve x 0 s 0 :=
    lt_of_lt_of_le (by positivity : 0 < 3 / (c + 1) ^ 2) hglobal.1
  have hxs := normalizedMaxCurve_forward_of_constraint hx hs
  have hent : stableBoundaryEntry (Y s 0) (Y s 1) (Y s 3) = Y s := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · exact hglobal.2.1.2.2.1.symm
    · rfl
  have hinv : fromProjectiveState (stableBoundaryEntry (Y s 0) (Y s 1) (Y s 3)) =
      normalizedMaxCurve x 0 s := by
    rw [hent]
    exact fromProjectiveState_toProjectiveState (ne_of_gt hAs) hxs.2.1
  change toProjectiveState (normalizedMaxCurve
    (fromProjectiveState (stableBoundaryEntry (Y s 0) (Y s 1) (Y s 3))) 0 t) = Y (t + s)
  rw [hinv]
  have ht' := normalizedMaxDomain_contains_Ici_of_constraint hxs.2.1 0 ht
  have hretime := normalizedMaxCurve_retime (t₀ := s) ht'
  simp only [sub_zero] at hretime
  rw [hretime, normalizedMaxCurve_rebase
    (normalizedMaxDomain_contains_Ici_of_constraint hx 0 hs)
    (normalizedMaxDomain_contains_Ici_of_constraint hx 0 (add_nonneg ht hs))]
  rfl

theorem stableBoundaryProjection_invariant {m c u w s : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) (hs : 0 ≤ s) :
    let Y := stableBoundaryOrbit m u w
    stableBoundaryProjection (Y s 0) (Y s 1) (Y s 3) = stableBoundaryProjection m u w := by
  intro Y
  have hP := (stableBoundaryProjection_exists hc hm hu hw).1
  have hshift : Tendsto (fun t => Y (t + s) 0) atTop (𝓝 (stableBoundaryProjection m u w)) :=
    hP.comp (tendsto_atTop_add_const_right atTop s tendsto_id)
  have hnew : Tendsto (fun t => stableBoundaryOrbit (Y s 0) (Y s 1) (Y s 3) t 0)
      atTop (𝓝 (stableBoundaryProjection m u w)) := by
    apply hshift.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [stableBoundaryOrbit_restart hc hm hu hw hs ht]
  exact hnew.limUnder_eq

end BianchiIX
