import BianchiIX.Dynamics.ShearRestartTail
import BianchiIX.Dynamics.ShearTailVariationBounds

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def restartShearInitialVariation (h ζ ν ρ : ℝ) : NormalizedState :=
  fderiv ℝ (restartSectionChart h) (restartShearCurve 1 ζ ν ρ) (restartShearDirection 1)

/-- The initial radial tangent lies on the exact constraint surface. -/
theorem restartShearInitialVariation_tangent {h ζ ν ρ : ℝ}
    (hrad : 0 < restartSectionRadicand h (restartShearCurve 1 ζ ν ρ)) :
    HasDerivAt (fun r => restartSectionChart h (restartShearCurve 1 ζ ν r))
      (restartShearInitialVariation h ζ ν ρ) ρ ∧
    normalizedConstraintDifferential (restartSectionChart h (restartShearCurve 1 ζ ν ρ))
      (restartShearInitialVariation h ζ ν ρ) = 0 := by
  have HD := ((contDiffAt_restartSectionChart hrad 1).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
    ρ (hasDerivAt_restartShearCurve 1 ζ ν ρ)
  refine ⟨HD, ?_⟩
  have HR : Continuous (fun r => restartSectionRadicand h (restartShearCurve 1 ζ ν r)) := by
    unfold restartSectionRadicand restartShearCurve curvature
    fun_prop
  have HE : (fun r => stateConstraint (restartSectionChart h (restartShearCurve 1 ζ ν r))) =ᶠ[𝓝 ρ]
      fun _ => (1 : ℝ) := by
    filter_upwards [HR.continuousAt.eventually (isOpen_Ioi.mem_nhds hrad)] with r hr
    exact restartSectionChart_constraint hr.le
  exact ((hasFDerivAt_stateConstraint _).comp_hasDerivAt ρ HD).unique
    ((hasDerivAt_const ρ (1 : ℝ)).congr_of_eventuallyEq HE)

def restartShearTailRadialVariation (h a q ζ ν t ρ : ℝ) : NormalizedState :=
  normalizedFlowDifferential (restartSectionChart h (restartShearCurve 1 ζ ν ρ)) 0
    (t + q / 2 * Real.log (1 / a)) (restartShearInitialVariation h ζ ν ρ)

/-- This is the ordinary derivative of the joined physical flow with respect to its radius. -/
theorem hasDerivAt_restartShearTailFlow {h a q ζ ν t ρ : ℝ}
    (hrad : 0 < restartSectionRadicand h (restartShearCurve 1 ζ ν ρ))
    (ht : t + q / 2 * Real.log (1 / a) ∈
      normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 ζ ν ρ)) 0) :
    HasDerivAt (restartShearTailFlow h a q ζ ν t) (restartShearTailRadialVariation h a q ζ ν t ρ) ρ := by
  exact (hasFDerivAt_normalizedMaxCurve_initial ht).comp_hasDerivAt ρ
    (restartShearInitialVariation_tangent hrad).1

theorem hasDerivAt_restartShearTailLogState {h a q ζ ν t ρ : ℝ}
    (hrad : 0 < restartSectionRadicand h (restartShearCurve 1 ζ ν ρ))
    (ht : t + q / 2 * Real.log (1 / a) ∈
      normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 ζ ν ρ)) 0)
    (hn : positiveWalls (restartShearTailFlow h a q ζ ν t ρ)) :
    HasDerivAt (fun r =>
      ![restartShearTailFlow h a q ζ ν t r 1,
        Real.log (restartShearTailFlow h a q ζ ν t r 2),
        Real.log (restartShearTailFlow h a q ζ ν t r 3),
        Real.log (restartShearTailFlow h a q ζ ν t r 4)])
      (shearTailVariation (restartShearTailFlow h a q ζ ν t ρ)
        (restartShearTailRadialVariation h a q ζ ν t ρ)) ρ := by
  exact hasDerivAt_shearTailLogState (hasDerivAt_restartShearTailFlow hrad ht)
    hn.1.ne' hn.2.1.ne' hn.2.2.ne'

/-- Exact radial log derivatives obey (E.42) and (E.43) in original time. -/
theorem restartShearTail_radial_equation {h a q ζ ν t ρ : ℝ}
    (hrad : 0 < restartSectionRadicand h (restartShearCurve 1 ζ ν ρ))
    (ht : t + q / 2 * Real.log (1 / a) ∈
      normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 ζ ν ρ)) 0)
    (hp : restartShearTailFlow h a q ζ ν t ρ 0 ≤ -(15 / 16))
    (hs : |restartShearTailFlow h a q ζ ν t ρ 1| ≤ 1 / 8)
    (hn : positiveWalls (restartShearTailFlow h a q ζ ν t ρ)) :
    let z := restartShearTailFlow h a q ζ ν t ρ
    let v := restartShearTailRadialVariation h a q ζ ν t ρ
    HasDerivAt (fun u => shearTailVariation (restartShearTailFlow h a q ζ ν u ρ)
      (restartShearTailRadialVariation h a q ζ ν u ρ)) (shearTailVariationRate z v) t ∧
    |shearTailVariationRate z v 0| ≤ 2 * shearTailEnergy z * |v 1| +
      4 * shearTailEnergy z * shearTailLogSize z v ∧
    ∀ i : Fin 3, |shearTailVariationRate z v i.succ| ≤ 2 * |v 1| +
      9 * shearTailEnergy z * shearTailLogSize z v := by
  intro z v
  refine ⟨?_, shearTailVariationRate_log_bounds hp hs hn⟩
  have H := normalizedFlow_shearTailVariation ht (restartShearInitialVariation_tangent hrad).2
    (by change z 0 ≠ 0; linarith only [hp]) hn.1.ne' hn.2.1.ne' hn.2.2.ne'
  have Ht := H.scomp t ((hasDerivAt_id' t).add_const (q / 2 * Real.log (1 / a)))
  simpa only [Function.comp_def, one_smul, restartShearTailFlow, restartShearTailRadialVariation, z, v] using Ht

end BianchiIX
