import BianchiIX.Analysis.TwoMomentVariation
import BianchiIX.Dynamics.ShearTailVariationBounds

noncomputable section

namespace BianchiIX

open Set MeasureTheory

theorem shearTailLogSize_eq_norm_variation (z v : NormalizedState) :
    shearTailLogSize z v = ‖fun i : Fin 3 => shearTailVariation z v i.succ‖ := by
  congr 1

/-- The two-moment bound applies to the ordinary derivative of the actual maximal Einstein flow. -/
theorem normalizedFlow_shearTail_moment_variation {z v : NormalizedState} {T : ℝ}
    (hT : 0 ≤ T) (hc : normalizedConstraintDifferential z v = 0)
    (hd : ∀ t ∈ Icc (0 : ℝ) T, t ∈ normalizedMaxDomain z 0)
    (hp : ∀ t ∈ Icc (0 : ℝ) T, normalizedMaxCurve z 0 t 0 ≤ -(15 / 16))
    (hs : ∀ t ∈ Icc (0 : ℝ) T, |normalizedMaxCurve z 0 t 1| ≤ 1 / 8)
    (hn : ∀ t ∈ Icc (0 : ℝ) T, positiveWalls (normalizedMaxCurve z 0 t)) :
    let α := normalizedMaxCurve z 0
    let V := fun t => normalizedFlowDifferential z 0 t v
    let J₀ := ∫ t in 0..T, shearTailEnergy (α t)
    let J₁ := ∫ t in 0..T, t * shearTailEnergy (α t)
    let L₀ := shearTailLogSize (α 0) (V 0)
    let c := Real.exp (9 * J₀)
    let B := (|V 0 1| + 4 * c * L₀ * J₀) * Real.exp (2 * J₀ + 8 * c * J₁)
    (∀ t ∈ Icc (0 : ℝ) T, |V t 1| ≤ B ∧ shearTailLogSize (α t) (V t) ≤ c * (L₀ + 2 * t * B)) ∧
    (|V 0 1| ≤ 2 → 9 * J₀ ≤ Real.log 2 → 2 * J₀ + 16 * J₁ ≤ 1 / 2 → L₀ * J₀ ≤ 1 / 16 →
      ∀ t ∈ Icc (0 : ℝ) T, |V t 1| ≤ 5 ∧ shearTailLogSize (α t) (V t) ≤ 2 * L₀ + 20 * t) := by
  intro α V J₀ J₁ L₀ c B
  let S : ℝ → ℝ := fun t => V t 1
  let L : ℝ → (Fin 3 → ℝ) := fun t i => shearTailVariation (α t) (V t) i.succ
  let S' : ℝ → ℝ := fun t => shearTailVariationRate (α t) (V t) 0
  let L' : ℝ → (Fin 3 → ℝ) := fun t i => shearTailVariationRate (α t) (V t) i.succ
  have HE (t : ℝ) : shearTailLogSize (α t) (V t) = ‖L t‖ := shearTailLogSize_eq_norm_variation _ _
  have HD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) := normalizedFlow_shearTailVariation (hd t ht) hc
    (by linarith only [hp t ht]) (hn t ht).1.ne' (hn t ht).2.1.ne' (hn t ht).2.2.ne'
  have HS (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : HasDerivAt S (S' t) t := hasDerivAt_pi.mp (HD t ht) 0
  have HL (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : HasDerivAt L (L' t) t :=
    hasDerivAt_pi.mpr (fun i => hasDerivAt_pi.mp (HD t ht) i.succ)
  have Hα : ContinuousOn α (Icc (0 : ℝ) T) :=
    HasDerivAt.continuousOn (fun t ht => hasDerivAt_normalizedMaxCurve (hd t ht))
  have Hb : ContinuousOn (fun t => shearTailEnergy (α t)) (Icc (0 : ℝ) T) := by
    unfold shearTailEnergy
    fun_prop
  have Hb0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : 0 ≤ shearTailEnergy (α t) := by
    dsimp only [shearTailEnergy]
    positivity [(hn t ht).1, (hn t ht).2.1, (hn t ht).2.2]
  have HB (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) := shearTailVariationRate_log_bounds
    (v := V t) (hp t ht) (hs t ht) (hn t ht)
  have HSb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      |S' t| ≤ 2 * shearTailEnergy (α t) * |S t| + 4 * shearTailEnergy (α t) * ‖L t‖ := by
    simpa only [← HE t] using (HB t ht).1
  have HLb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ‖L' t‖ ≤ 2 * |S t| + 9 * shearTailEnergy (α t) * ‖L t‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity [Hb0 t ht])).mpr
    intro i
    simpa only [Real.norm_eq_abs, ← HE t] using (HB t ht).2 i
  constructor
  · simpa only [← HE, S] using two_moment_variation_bound hT HS HL Hb Hb0 HSb HLb
  · intro Hi H0 H1 HL0
    have H := two_moment_variation_small hT HS HL Hb Hb0 HSb HLb Hi ⟨H0, H1, by simpa only [← HE 0] using HL0⟩
    simpa only [← HE, S] using H

end BianchiIX
