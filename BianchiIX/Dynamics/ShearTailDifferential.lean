import BianchiIX.Dynamics.FlowTransport

noncomputable section

namespace BianchiIX

def shearTailCurvatureDifferential (z v : NormalizedState) : ℝ :=
  2 * ((z 2 - z 3 - z 4) * v 2 + (z 3 - z 2 - z 4) * v 3 + (z 4 - z 2 - z 3) * v 4)

def shearTailCouplingDifferential (z v : NormalizedState) : ℝ :=
  (z 3 - z 4) * v 2 + (z 2 - 2 * z 3) * v 3 + (2 * z 4 - z 2) * v 4

theorem hasDerivAt_shearTail_polynomials {α : ℝ → NormalizedState} {v : NormalizedState} {t : ℝ}
    (hα : HasDerivAt α v t) :
    HasDerivAt (fun u => curvature (α u 2) (α u 3) (α u 4)) (shearTailCurvatureDifferential (α t) v) t ∧
    HasDerivAt (fun u => -(α u 3) ^ 2 + (α u 4) ^ 2 + α u 2 * α u 3 - α u 2 * α u 4)
      (shearTailCouplingDifferential (α t) v) t := by
  have hn := hasDerivAt_pi.mp hα 2
  have hx := hasDerivAt_pi.mp hα 3
  have hy := hasDerivAt_pi.mp hα 4
  constructor
  · convert! (((hn.pow 2).add (hx.pow 2)).add (hy.pow 2)).sub
      ((((hn.mul hx).add (hx.mul hy)).add (hy.mul hn)).const_mul 2) using 1
    dsimp only [shearTailCurvatureDifferential]
    ring
  · convert! ((((hx.pow 2).neg.add (hy.pow 2)).add (hn.mul hx)).sub (hn.mul hy)) using 1
    dsimp only [shearTailCouplingDifferential]
    ring

theorem normalizedConstraintDifferential_shearTail (z v : NormalizedState) :
    normalizedConstraintDifferential z v = 2 * z 0 * v 0 + 2 * z 1 * v 1 +
      shearTailCurvatureDifferential z v := by
  let α : ℝ → NormalizedState := fun t i => z i + t * v i
  have hα : HasDerivAt α v 0 := hasDerivAt_pi.mpr (fun i => by
    simpa only [one_mul] using ((hasDerivAt_id' (0 : ℝ)).mul_const (v i)).const_add (z i))
  have hz : α 0 = z := by ext i; simp [α]
  have H := (hasFDerivAt_stateConstraint (α 0)).comp_hasDerivAt 0 hα
  have HQ := (hasDerivAt_shearTail_polynomials hα).1
  have H' := (((hasDerivAt_pi.mp hα 0).pow 2).add ((hasDerivAt_pi.mp hα 1).pow 2)).add HQ
  change HasDerivAt (fun t => stateConstraint (α t)) _ 0 at H'
  have HE := H.unique H'
  rw [hz] at HE
  convert! HE using 1
  ring

theorem normalizedDifferential_shearTail (z v : NormalizedState) :
    normalizedDifferential z v 1 = curvature (z 2) (z 3) (z 4) * v 1 +
      z 1 * shearTailCurvatureDifferential z v + Real.sqrt 3 * shearTailCouplingDifferential z v ∧
    normalizedDifferential z v 2 = (-2 * z 0 * v 0 - 2 * z 1 * v 1 + 2 * v 0) * z 2 +
      rateOne (z 0) (z 1) * v 2 ∧
    normalizedDifferential z v 3 = (-2 * z 0 * v 0 - 2 * z 1 * v 1 - v 0 + Real.sqrt 3 * v 1) * z 3 +
      rateTwo (z 0) (z 1) * v 3 ∧
    normalizedDifferential z v 4 = (-2 * z 0 * v 0 - 2 * z 1 * v 1 - v 0 - Real.sqrt 3 * v 1) * z 4 +
      rateThree (z 0) (z 1) * v 4 := by
  let α : ℝ → NormalizedState := fun t i => z i + t * v i
  have hα : HasDerivAt α v 0 := hasDerivAt_pi.mpr (fun i => by
    simpa only [one_mul] using ((hasDerivAt_id' (0 : ℝ)).mul_const (v i)).const_add (z i))
  have hz : α 0 = z := by ext i; simp [α]
  have HD := (hasFDerivAt_normalizedField (α 0)).comp_hasDerivAt 0 hα
  have H (i : Fin 5) := hasDerivAt_pi.mp HD i
  obtain ⟨HQ, HH⟩ := hasDerivAt_shearTail_polynomials hα
  have Hp := hasDerivAt_pi.mp hα 0
  have Hs := hasDerivAt_pi.mp hα 1
  have Hshear := (HQ.mul Hs).add (HH.const_mul (Real.sqrt 3))
  have Hr := ((Hp.pow 2).add (Hs.pow 2)).neg
  have Hn := (Hr.add (Hp.const_mul 2)).mul (hasDerivAt_pi.mp hα 2)
  have Hx := ((Hr.sub Hp).add (Hs.const_mul (Real.sqrt 3))).mul (hasDerivAt_pi.mp hα 3)
  have Hy := ((Hr.sub Hp).sub (Hs.const_mul (Real.sqrt 3))).mul (hasDerivAt_pi.mp hα 4)
  have H1 := (H 1).unique Hshear
  have H2 := (H 2).unique Hn
  have H3 := (H 3).unique Hx
  have H4 := (H 4).unique Hy
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply, hz] at H1 H2 H3 H4
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert! H1 using 1
    ring
  · convert! H2 using 1
    dsimp only [rateOne, shearSq]
    ring
  · convert! H3 using 1
    dsimp only [rateTwo, shearSq]
    ring
  · convert! H4 using 1
    dsimp only [rateThree, shearSq]
    ring

def shearTailVariation (z v : NormalizedState) : Fin 4 → ℝ :=
  ![v 1, v 2 / z 2, v 3 / z 3, v 4 / z 4]

theorem hasDerivAt_shearTailLogState {α : ℝ → NormalizedState} {v : NormalizedState} {t : ℝ}
    (hα : HasDerivAt α v t) (hn : α t 2 ≠ 0) (hx : α t 3 ≠ 0) (hy : α t 4 ≠ 0) :
    HasDerivAt (fun u => ![α u 1, Real.log (α u 2), Real.log (α u 3), Real.log (α u 4)])
      (shearTailVariation (α t) v) t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_pi.mp hα 1
  · exact (hasDerivAt_pi.mp hα 2).log hn
  · exact (hasDerivAt_pi.mp hα 3).log hx
  · exact (hasDerivAt_pi.mp hα 4).log hy

def shearTailVariationRate (z v : NormalizedState) : Fin 4 → ℝ :=
  let ξ := -z 0
  let dQ := shearTailCurvatureDifferential z v
  ![curvature (z 2) (z 3) (z 4) * v 1 + z 1 * dQ + Real.sqrt 3 * shearTailCouplingDifferential z v,
    (1 + ξ⁻¹) * dQ + 2 * z 1 * ξ⁻¹ * v 1,
    (1 - (2 * ξ)⁻¹) * dQ + (-z 1 * ξ⁻¹ + Real.sqrt 3) * v 1,
    (1 - (2 * ξ)⁻¹) * dQ + (-z 1 * ξ⁻¹ - Real.sqrt 3) * v 1]

/-- The logarithmic wall variation is obtained from ordinary derivatives on the constraint surface. -/
theorem hasDerivAt_shearTailVariation {α v : ℝ → NormalizedState} {t : ℝ}
    (hα : HasDerivAt α (normalizedField (α t)) t)
    (hv : HasDerivAt v (normalizedDifferential (α t) (v t)) t)
    (hc : normalizedConstraintDifferential (α t) (v t) = 0)
    (hp : α t 0 ≠ 0) (hn : α t 2 ≠ 0) (hx : α t 3 ≠ 0) (hy : α t 4 ≠ 0) :
    HasDerivAt (fun u => shearTailVariation (α u) (v u)) (shearTailVariationRate (α t) (v t)) t := by
  rw [normalizedConstraintDifferential_shearTail] at hc
  have Hvp : v t 0 = (α t 1 * v t 1 + shearTailCurvatureDifferential (α t) (v t) / 2) / (-α t 0) := by
    apply (eq_div_iff (neg_ne_zero.mpr hp)).mpr
    nlinarith only [hc]
  obtain ⟨HS, HN, HX, HY⟩ := normalizedDifferential_shearTail (α t) (v t)
  obtain ⟨_, _, Hn, Hx, Hy⟩ := hasDerivAt_normalized_components hα
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert! hasDerivAt_pi.mp hv 1 using 1
    exact HS.symm
  · convert! (hasDerivAt_pi.mp hv 2).div Hn hn using 1
    dsimp [shearTailVariationRate]
    rw [HN, Hvp]
    field_simp [hp, hn]
    ring
  · convert! (hasDerivAt_pi.mp hv 3).div Hx hx using 1
    dsimp [shearTailVariationRate]
    rw [HX, Hvp]
    field_simp [hp, hx]
    ring
  · convert! (hasDerivAt_pi.mp hv 4).div Hy hy using 1
    dsimp [shearTailVariationRate]
    rw [HY, Hvp]
    field_simp [hp, hy]
    ring

/-- The same equations hold for the derivative of the actual maximal flow. -/
theorem normalizedFlow_shearTailVariation {z v : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain z t₀) (hc : normalizedConstraintDifferential z v = 0)
    (hp : normalizedMaxCurve z t₀ t 0 ≠ 0)
    (hn : normalizedMaxCurve z t₀ t 2 ≠ 0) (hx : normalizedMaxCurve z t₀ t 3 ≠ 0)
    (hy : normalizedMaxCurve z t₀ t 4 ≠ 0) :
    HasDerivAt (fun u => shearTailVariation (normalizedMaxCurve z t₀ u) (normalizedFlowDifferential z t₀ u v))
      (shearTailVariationRate (normalizedMaxCurve z t₀ t) (normalizedFlowDifferential z t₀ t v)) t := by
  have Hv := (hasDerivAt_normalizedFlowDifferential ht).clm_apply (hasDerivAt_const t v)
  have Hc := congrArg (fun L : NormalizedState →L[ℝ] ℝ => L v) (normalizedConstraintDifferential_flow ht)
  simp only [ContinuousLinearMap.comp_apply, hc] at Hc
  apply hasDerivAt_shearTailVariation (hasDerivAt_normalizedMaxCurve ht) _ Hc hp hn hx hy
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.map_zero, add_zero] using Hv

end BianchiIX
