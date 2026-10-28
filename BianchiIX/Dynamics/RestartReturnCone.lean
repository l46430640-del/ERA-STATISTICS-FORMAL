import BianchiIX.Dynamics.RestartReturnRegularity
import BianchiIX.Dynamics.RestartReturnControl
import BianchiIX.Dynamics.RestartConnectionCurve

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The fixed C2 restart curve satisfies the physical square-root cone on the full annulus. -/
theorem exists_restartReturn_cone :
    ∃ hstar : ℝ, 0 < hstar ∧ ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ L : ℝ, 0 ≤ L → ∀ q P : ℝ, 3 < q → 4 < P →
        ∃ rstar : ℝ, 0 < rstar ∧ ∀ r ∈ Ioc (0 : ℝ) rstar,
          ∀ θ ζ : ℝ, |θ| ≤ L → (0 < ζ ∧ ζ ≤ r ^ P) → ∀ ρ ∈ Icc r (2 * r),
            let s := q / 2 * Real.log (1 / r)
            let G := restartReturnState h s θ ζ
            let k := fun a => G a 0
            ContDiffAt ℝ 2 G ρ ∧ 0 < G ρ 1 ∧ 0 < G ρ 2 ∧
              G ρ 1 + G ρ 2 ≤ 4096 * (8 * (L + 1)) * ζ / r ^ 3 ∧ deriv k ρ < 0 ∧
              |deriv (fun a => G a 1) ρ| ≤ Real.sqrt (G ρ 1) * |deriv k ρ| ∧
              |deriv (fun a => G a 2) ρ| ≤ Real.sqrt (G ρ 2) * |deriv k ρ| := by
  obtain ⟨hR, hhR, HR⟩ := exists_restartReturn_regular
  obtain ⟨hC, hhC, HC⟩ := exists_restartConnection_radial_curve
  obtain ⟨hB, hhB, HB⟩ := exists_restartReturn_control
  refine ⟨min hR (min hC hB), lt_min hhR (lt_min hhC hhB), ?_⟩
  intro h hh L hL q P hq hP
  obtain ⟨rR, hrR, HRR⟩ := HR h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL q P hq hP
  obtain ⟨rC, hrC, HRC⟩ := HC h ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_left _ _)⟩ L hL q P hq hP
  obtain ⟨_, _, HB'⟩ := HB h ⟨hh.1, (hh.2.trans (min_le_right _ _)).trans (min_le_right _ _)⟩ L hL
  obtain ⟨rB, hrB, HRB⟩ := HB' q P hq hP
  refine ⟨min rR (min rC rB), lt_min hrR (lt_min hrC hrB), ?_⟩
  intro r hr θ ζ hθ hζ ρ hρ
  have hrCB := hr.2.trans (min_le_right _ _)
  obtain ⟨hcY, _, hcG, _⟩ := HRR r ⟨hr.1, hr.2.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  obtain ⟨_, _, _, τ, _, _, hnear, _, _, _, _, _, hneg, _, _, hcone, _⟩ :=
    HRC r ⟨hr.1, hrCB.trans (min_le_left _ _)⟩ θ ζ hθ hζ ρ hρ
  obtain ⟨_, _, _, _, _, hu, hw, hsum, _⟩ :=
    HRB r ⟨hr.1, hrCB.trans (min_le_right _ _)⟩ θ ζ hθ hζ ρ hρ
  let s := q / 2 * Real.log (1 / r)
  let Y := restartFastProjectiveEntry h s θ ζ
  let out := fun a => projectiveOriginalFlow (Y a) 0 (τ (Y a))
  let p := fun a => coreExitConnectionParameters
    ![coreRadius (out a 0) (out a 2), out a 1, out a 3]
  have heq := restartReturnParameters_eventuallyEq hcY.continuousAt hnear
  have heqG : restartReturnState h s θ ζ =ᶠ[𝓝 ρ] fun a => connectionReturnPhysicalState (p a) :=
    heq.mono fun _ ha => congrArg connectionReturnPhysicalState ha
  have heqi (i : Fin 3) : (fun a => restartReturnState h s θ ζ a i) =ᶠ[𝓝 ρ]
      fun a => connectionReturnPhysicalState (p a) i :=
    heqG.mono fun _ ha => congrArg (fun z => z i) ha
  have hd0 := (heqi 0).deriv_eq
  have hd1 := (heqi 1).deriv_eq
  have hd2 := (heqi 2).deriv_eq
  have hv1 := (heqi 1).self_of_nhds
  have hv2 := (heqi 2).self_of_nhds
  dsimp only [s, Y, p, out] at hd0 hd1 hd2 hv1 hv2
  refine ⟨hcG, hu, hw, hsum, ?_, ?_, ?_⟩
  · simpa only [hd0] using hneg.2
  · simpa only [hd0, hd1, hv1] using hcone.1
  · simpa only [hd0, hd2, hv2] using hcone.2

end BianchiIX
