import BianchiIX.Dynamics.ShearRestartTailEndpoint
import BianchiIX.Dynamics.ShearRestartProjectionQuadratic
import BianchiIX.Dynamics.ShearRestartTailPhase
import BianchiIX.Dynamics.RestartProjectionDomain

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def restartShearTailProjectionPhase (h a q ζ ν t ρ : ℝ) : ℝ :=
  2 / coreRadius (toProjectiveState (restartShearTailFlow h a q ζ ν t ρ) 0)
    (toProjectiveState (restartShearTailFlow h a q ζ ν t ρ) 2)

/-- The instantaneous growing-circle phase and the physical radius agree to first radial order. -/
theorem exists_restartShearTail_projection_error :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D : ℝ, 2 < q → 2 < D → ∃ K > (0 : ℝ),
        ∀ P : ℝ, 6 * D + 2 < P → ∃ astar > (0 : ℝ),
          ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε ζ ν : ℝ,
            (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let T := shearTailTime a D
            let E := fun r => restartShearTailProjectionPhase h a q ζ ν T r -
              restartShearTailPhase h a q ζ ν T r
            T + q / 2 * Real.log (1 / a) ∈
              normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 ζ ν ρ)) 0 ∧
            0 < 1 + restartShearTailFlow h a q ζ ν T ρ 0 ∧
            DifferentiableAt ℝ E ρ ∧ |E ρ| ≤ K * a ^ 2 ∧ |deriv E ρ| ≤ K * a := by
  obtain ⟨C, hC, hstar, hhstar, H⟩ := exists_restartShearTail_endpoint_control
  obtain ⟨δ, hδ, CE, hCE, HE⟩ := exists_shearRestartProjectionError_quadratic
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh q D hq hD
  let B := 13 + 16 * C * q + 40 * D
  have hC0 : 0 ≤ C := by linarith only [hC]
  have hq0 : 0 ≤ q := by linarith only [hq]
  have hD0 : 0 ≤ D := by linarith only [hD]
  have hB : 1 ≤ B := by dsimp only [B]; nlinarith only [mul_nonneg hC0 hq0, hD0]
  have hCE0 : 0 < CE := by linarith only [hCE]
  let K := 2 * CE * B
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro P hP
  obtain ⟨a₀, ha₀, HA⟩ := H h hh q D P hq hD hP
  refine ⟨min a₀ δ, lt_min ha₀ hδ, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ T E
  let z := restartShearTailFlow h a q ζ ν T ρ
  let v := restartShearTailRadialVariation h a q ζ ν T ρ
  let τ := T + q / 2 * Real.log (1 / a)
  let R := fun r => restartSectionRadialState h τ (restartShearCurve 1 ζ ν r)
  let vR : RestartRadialState := (v 2, restartCenterProjection v)
  obtain ⟨hasmall, hτ, hrad, Hdom, _, Hpos, Hreg, Hheight, HD, Hn, Hy, HS, HX, HN, HY⟩ :=
    HA a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε ζ ν hε hζ hν ρ hρ
  have HR : HasDerivAt R vR ρ :=
    (hasDerivAt_pi.mp HD 2).prodMk (restartCenterProjection.hasFDerivAt.comp_hasDerivAt ρ HD)
  have hs : 0 < z 1 := by linarith only [Hreg.2.1, ha.1]
  have hslo : a / 2 ≤ |(R ρ).2 0| := by
    change a / 2 ≤ |z 1|
    rw [abs_of_pos hs]
    exact Hreg.2.1
  have hshi : |(R ρ).2 0| ≤ 4 * a := by
    change |z 1| ≤ 4 * a
    rw [abs_of_pos hs]
    linarith only [Hreg.2.2.1, ha.1]
  have hx : |(R ρ).2 1| ≤ 4 * a := by
    change |z 3| ≤ 4 * a
    rw [abs_of_pos Hpos.2.1]
    nlinarith only [Hreg.2.2.2.2.1, hasmall, ha.1]
  obtain ⟨_, HED, HEv, HEd⟩ := HE a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ R vR ρ B HR
    (by linarith only [hB]) hslo hshi hx Hn Hy HS HX HN HY
  have hneg : z 0 < 0 := by linarith only [Hreg.1]
  have Hgerm := (eventually_restartSectionProjectionPhase_eq_core hrad hτ
    hneg Hheight).comp_tendsto
    (hasDerivAt_restartShearCurve 1 ζ ν ρ).continuousAt
  have Hlocal : E =ᶠ[𝓝 ρ] (fun r => restartProjectionError (R r)) := by
    filter_upwards [Hgerm] with r hr
    change restartProjectionPhase (R r) = restartShearTailProjectionPhase h a q ζ ν T r at hr
    change restartShearTailProjectionPhase h a q ζ ν T r - restartRadialPhase (R r).2 =
      restartProjectionPhase (R r) - restartRadialPhase (R r).2
    rw [hr]
  have HEder : HasDerivAt E (deriv (fun r => restartProjectionError (R r)) ρ) ρ :=
    HED.hasDerivAt.congr_of_eventuallyEq Hlocal
  have hCEK : CE ≤ K := by
    dsimp only [K]
    nlinarith only [mul_le_mul_of_nonneg_left hB hCE0.le, hCE0]
  refine ⟨Hdom, Hheight, HEder.differentiableAt, ?_, ?_⟩
  · rw [Hlocal.eq_of_nhds]
    exact HEv.trans (mul_le_mul_of_nonneg_right hCEK (sq_nonneg a))
  · rw [HEder.deriv]
    exact HEd

end BianchiIX
