import BianchiIX.Dynamics.PhysicalPhaseSpace
import BianchiIX.Dynamics.WallProductDecay

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

/-- Brehm's delta for the complementary wall pair. -/
def brehmPairDelta (x : NormalizedState) (i j : Fin 3) : ℝ :=
  2 * Real.sqrt |wallValue i x * wallValue j x|

theorem brehmPairDelta_sq (x : NormalizedState) (i j : Fin 3) :
    brehmPairDelta x i j ^ 2 = 4 * |wallValue i x * wallValue j x| := by
  unfold brehmPairDelta
  rw [mul_pow, Real.sq_sqrt (abs_nonneg _)]
  norm_num

/-- The delta-decay consequence of Brehm's Section 6 local and Bianchi IX global
attractor theorems (2016, arXiv:1606.08058). The source uses the same coordinates
and singularity-directed time as `normalizedField`; see its unpacked
Wainwright-Hsu equations and the definitions of the Taub spaces in Section 2.
For positive walls, the excluded spaces are exactly `taubSubspaces`.
This proposition is an explicit literature parameter, not a project axiom.
It asserts no era coding, statistical conclusion, or transverse nullity. -/
def Literature.BrehmIXAttractorInput : Prop :=
  ∀ x : NormalizedState, x ∈ physicalPhaseSpace → x ∉ taubSubspaces →
    ∀ i j : Fin 3, i ≠ j → Tendsto
      (fun t => brehmPairDelta (normalizedMaxCurve x 0 t) i j) atTop (𝓝 0)

theorem Literature.BrehmIXAttractorInput.wallProductDecay
    (H : Literature.BrehmIXAttractorInput) {x : NormalizedState}
    (hx : x ∈ physicalPhaseSpace) (hT : x ∉ taubSubspaces) : WallProductDecay x := by
  intro i j hij
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hlim := ((H x hx hT i j hij).pow 2).div_const 4
  simp only [brehmPairDelta_sq, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div] at hlim
  convert hlim using 1
  ext t
  rw [Real.norm_eq_abs]
  ring

end BianchiIX
