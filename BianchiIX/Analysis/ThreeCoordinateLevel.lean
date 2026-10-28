import BianchiIX.Analysis.ImplicitEvent
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def threeCoordinateInput : ((Fin 2 → ℝ) × ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) ℝ,
    (ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) ℝ),
    (ContinuousLinearMap.proj 1).comp (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) ℝ)]

theorem threeCoordinateInput_apply (p : Fin 2 → ℝ) (k : ℝ) :
    threeCoordinateInput (p, k) = ![k, p 0, p 1] := by
  ext i
  fin_cases i <;> rfl

theorem hasDerivAt_three_coordinate_line (p : Fin 2 → ℝ) (k : ℝ) :
    HasDerivAt (fun a : ℝ => (![a, p 0, p 1] : Fin 3 → ℝ)) (Pi.single 0 1) k := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_id' k
  · simpa using hasDerivAt_const k (p 0)
  · simpa using hasDerivAt_const k (p 1)

theorem exists_three_coordinate_level_branch {F : (Fin 3 → ℝ) → ℝ} {p : Fin 2 → ℝ} {k : ℝ}
    (hF : ContDiffAt ℝ 2 F ![k, p 0, p 1])
    (ha : fderiv ℝ F ![k, p 0, p 1] (Pi.single 0 1) ≠ 0) :
    ∃ τ : (Fin 2 → ℝ) → ℝ, τ p = k ∧ ContDiffAt ℝ 2 τ p ∧
      (∀ᶠ q in 𝓝 p, F ![τ q, q 0, q 1] = F ![k, p 0, p 1]) ∧
      ∀ i : Fin 2, fderiv ℝ τ p (Pi.single i 1) =
        -fderiv ℝ F ![k, p 0, p 1] (Pi.single i.succ 1) /
          fderiv ℝ F ![k, p 0, p 1] (Pi.single 0 1) := by
  let Q := F ∘ threeCoordinateInput
  have hF' : ContDiffAt ℝ 2 F (threeCoordinateInput (p, k)) := by rw [threeCoordinateInput_apply]; exact hF
  have hQ : ContDiffAt ℝ 2 Q (p, k) := hF'.comp (p, k) threeCoordinateInput.contDiff.contDiffAt
  have hdQ := (hF'.differentiableAt (by norm_num)).hasFDerivAt.comp (p, k) threeCoordinateInput.hasFDerivAt
  have hd : HasDerivAt (fun a => Q (p, a)) (fderiv ℝ F ![k, p 0, p 1] (Pi.single 0 1)) k := by
    have H := (hF.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt k (hasDerivAt_three_coordinate_line p k)
    simpa only [Q, Function.comp_def, threeCoordinateInput_apply] using H
  obtain ⟨τ, hτ, hcτ, hdτ, hhit, _⟩ := exists_scalar_event_branch_two hQ hd ha
  refine ⟨τ, hτ, hcτ, ?_, ?_⟩
  · simpa only [Q, Function.comp_def, threeCoordinateInput_apply] using hhit
  intro i
  change HasFDerivAt Q _ (p, k) at hdQ
  rw [hdτ.fderiv, hdQ.fderiv]
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
    threeCoordinateInput_apply]
  have he : (![0, (Pi.single i 1 : Fin 2 → ℝ) 0, (Pi.single i 1 : Fin 2 → ℝ) 1] : Fin 3 → ℝ) = Pi.single i.succ 1 := by
    ext j
    fin_cases i <;> fin_cases j <;> simp
  rw [he]
  ring

end BianchiIX
