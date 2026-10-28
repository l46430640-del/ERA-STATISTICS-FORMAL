import BianchiIX.Dynamics.PartialCoreReturnOrientation
import BianchiIX.Dynamics.RestartReturnRegularity
import BianchiIX.Dynamics.ShearRestartReturnMap

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The angular labels and the positive-shear chart describe exactly the same initial state. -/
theorem restartFastProjectiveEntry_eq_shear (h s θ ζ ρ : ℝ) :
    restartFastProjectiveEntry h s θ ζ ρ = restartFastShearProjectiveEntry h s 1 ρ ζ (θ * ρ) := by
  simp only [restartFastProjectiveEntry, restartFastShearProjectiveEntry,
    restartRadialCurve, restartShearCurve, one_mul]

/-- On their common core entrance, the angular and shear constructions are the same ordinary return germ. -/
theorem restartReturn_shear_eventuallyEq {h s θ ζ ρ k : ℝ}
    (hrad : 0 < restartSectionRadicand h (restartRadialCurve θ ζ ρ))
    (hdom : s ∈ normalizedMaxDomain (restartSectionChart h (restartRadialCurve θ ζ ρ)) 0)
    (hA : 0 < restartFastProjectionHeight h s θ ζ ρ)
    (hk : 6 ≤ k) (hy : coreRegion k (restartFastProjectiveEntry h s θ ζ ρ))
    (hR : coreRadius (restartFastProjectiveEntry h s θ ζ ρ 0)
      (restartFastProjectiveEntry h s θ ζ ρ 2) = k)
    (hV : 1 < restartFastProjectiveEntry h s θ ζ ρ 2) :
    (fun v : (ℝ × ℝ) × ℝ => restartReturnParameters h s v.1.1 v.1.2 v.2) =ᶠ[𝓝 ((θ, ζ), ρ)]
      (fun v => restartShearReturnParameters h s v.2 v.1.2 (v.1.1 * v.2)) ∧
    (fun v : (ℝ × ℝ) × ℝ => restartReturnState h s v.1.1 v.1.2 v.2) =ᶠ[𝓝 ((θ, ζ), ρ)]
      (fun v => restartShearReturnState h s v.2 v.1.2 (v.1.1 * v.2)) ∧
    (fun v : (ℝ × ℝ) × ℝ => restartReturnPhase h s v.1.1 v.1.2 v.2) =ᶠ[𝓝 ((θ, ζ), ρ)]
      (fun v => restartShearReturnPhase h s v.2 v.1.2 (v.1.1 * v.2)) ∧
    (fun v : (ℝ × ℝ) × ℝ => restartReturnTime h s v.1.1 v.1.2 v.2) =ᶠ[𝓝 ((θ, ζ), ρ)]
      (fun v => restartShearReturnTime h s v.2 v.1.2 (v.1.1 * v.2)) := by
  let base : (ℝ × ℝ) × ℝ := ((θ, ζ), ρ)
  let Y := fun v : (ℝ × ℝ) × ℝ => restartFastProjectiveEntry h s v.1.1 v.1.2 v.2
  have hc : ContinuousAt Y base := (contDiffAt_restartFastProjectiveEntry_joint hrad hdom hA.ne').continuousAt
  have HE := partialCoreDownwardReturn_agrees_eventually hk hy hR hV
  have H : ∀ᶠ v in 𝓝 base,
      restartReturnParameters h s v.1.1 v.1.2 v.2 = restartShearReturnParameters h s v.2 v.1.2 (v.1.1 * v.2) ∧
      restartReturnState h s v.1.1 v.1.2 v.2 = restartShearReturnState h s v.2 v.1.2 (v.1.1 * v.2) ∧
      restartReturnPhase h s v.1.1 v.1.2 v.2 = restartShearReturnPhase h s v.2 v.1.2 (v.1.1 * v.2) ∧
      restartReturnTime h s v.1.1 v.1.2 v.2 = restartShearReturnTime h s v.2 v.1.2 (v.1.1 * v.2) := by
    filter_upwards [hc.tendsto.eventually HE.1, hc.tendsto.eventually HE.2] with v ht hz
    have ht' : partialCoreReturnTime (Y v) =
        partialCoreDownwardReturnTime (restartFastShearProjectiveEntry h s 1 v.2 v.1.2 (v.1.1 * v.2)) := by
      rw [← restartFastProjectiveEntry_eq_shear]
      exact ht.symm
    have hz' : partialCoreReturnState (Y v) =
        partialCoreDownwardReturnState (restartFastShearProjectiveEntry h s 1 v.2 v.1.2 (v.1.1 * v.2)) := by
      rw [← restartFastProjectiveEntry_eq_shear]
      exact hz.symm
    have hp : restartReturnParameters h s v.1.1 v.1.2 v.2 =
        restartShearReturnParameters h s v.2 v.1.2 (v.1.1 * v.2) := congrArg coreExitConnectionParameters hz'
    have hg : restartReturnState h s v.1.1 v.1.2 v.2 =
        restartShearReturnState h s v.2 v.1.2 (v.1.1 * v.2) := congrArg connectionReturnPhysicalState hp
    refine ⟨hp, hg, congrArg (fun G : CoreAngleState => 2 / G 0) hg, ?_⟩
    dsimp only [restartReturnTime, restartShearReturnTime]
    change s + partialCoreReturnTime (Y v) + _ = _
    rw [ht', hp]
  exact ⟨H.mono fun _ h => h.1, H.mono fun _ h => h.2.1,
    H.mono fun _ h => h.2.2.1, H.mono fun _ h => h.2.2.2⟩

/-- The positive angular family realizes the same return in shear coordinates without a new dynamical estimate. -/
theorem exists_restartAngular_shear_germs :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar, ∀ θ ζ : ℝ,
          (0 < θ ∧ θ ≤ L) → (0 ≤ ζ ∧ ζ ≤ a ^ P) → ∀ ρ ∈ Icc a (2 * a),
          let s := q / 2 * Real.log (1 / a)
          let base := ((θ, ζ), ρ)
          let F := fun v : (ℝ × ℝ) × ℝ => restartReturnParameters h s v.1.1 v.1.2 v.2
          let F' := fun v : (ℝ × ℝ) × ℝ => restartShearReturnParameters h s v.2 v.1.2 (v.1.1 * v.2)
          let G := fun v : (ℝ × ℝ) × ℝ => restartReturnState h s v.1.1 v.1.2 v.2
          let G' := fun v : (ℝ × ℝ) × ℝ => restartShearReturnState h s v.2 v.1.2 (v.1.1 * v.2)
          let X := fun v : (ℝ × ℝ) × ℝ => restartReturnPhase h s v.1.1 v.1.2 v.2
          let X' := fun v : (ℝ × ℝ) × ℝ => restartShearReturnPhase h s v.2 v.1.2 (v.1.1 * v.2)
          let T := fun v : (ℝ × ℝ) × ℝ => restartReturnTime h s v.1.1 v.1.2 v.2
          let T' := fun v : (ℝ × ℝ) × ℝ => restartShearReturnTime h s v.2 v.1.2 (v.1.1 * v.2)
          F =ᶠ[𝓝 base] F' ∧ G =ᶠ[𝓝 base] G' ∧ X =ᶠ[𝓝 base] X' ∧ T =ᶠ[𝓝 base] T' ∧
          ∀ n : ℕ, iteratedFDeriv ℝ n F base = iteratedFDeriv ℝ n F' base ∧
            iteratedFDeriv ℝ n G base = iteratedFDeriv ℝ n G' base ∧
            iteratedFDeriv ℝ n X base = iteratedFDeriv ℝ n X' base ∧
            iteratedFDeriv ℝ n T base = iteratedFDeriv ℝ n T' base := by
  obtain ⟨hE, hhE, HE⟩ := exists_restartPartialCore_entry
  refine ⟨hE, hhE, ?_⟩
  intro h hh L hL q P hq hP
  obtain ⟨aE, haE, HAE⟩ := HE h hh L hL q P hq hP (1 / 10000) ⟨by norm_num, le_rfl⟩
  refine ⟨aE, haE, ?_⟩
  intro a ha θ ζ hθ hζ ρ hρ s base F F' G G' X X' T T'
  have hθ' : |θ| ≤ L := by simpa only [abs_of_pos hθ.1] using hθ.2
  obtain ⟨_, hrad, hdom, hA, hk, _, hR, _, _, _, hV, _, hy⟩ := HAE a ha θ ζ hθ' hζ ρ hρ
  obtain ⟨HF, HG, HX, HT⟩ := restartReturn_shear_eventuallyEq hrad hdom hA
    ((le_max_left _ _).trans hk) hy hR ((by norm_num : (1 : ℝ) < 2).trans_le hV)
  refine ⟨HF, HG, HX, HT, ?_⟩
  intro n
  exact ⟨(HF.iteratedFDeriv ℝ n).self_of_nhds, (HG.iteratedFDeriv ℝ n).self_of_nhds,
    (HX.iteratedFDeriv ℝ n).self_of_nhds, (HT.iteratedFDeriv ℝ n).self_of_nhds⟩

end BianchiIX
