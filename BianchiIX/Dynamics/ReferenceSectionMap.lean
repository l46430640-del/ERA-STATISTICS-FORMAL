import BianchiIX.Dynamics.ReferenceActualVariation

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

abbrev CoreCoordinates := Fin 3 → ℝ

def coreSectionEmbedding (z : CoreCoordinates) : ProjectiveState := ![z 0, z 1, 1, z 2]

def coreSectionCoordinates (y : ProjectiveState) : CoreCoordinates := ![y 0, y 1, y 3]

def coreSectionChart (z : CoreCoordinates) : NormalizedState := fromProjectiveState (coreSectionEmbedding z)

def referenceCoreInput (k : ℝ) : CoreCoordinates := ![1 + Real.sqrt (k ^ 2 - 1), 0, 0]

def referenceCoreOutput (k : ℝ) : CoreCoordinates := ![1 - Real.sqrt (k ^ 2 - 1), 0, 0]

theorem contDiff_coreSectionEmbedding (n : WithTop ℕ∞) : ContDiff ℝ n coreSectionEmbedding := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreSectionEmbedding] <;> fun_prop

theorem contDiff_coreSectionCoordinates (n : WithTop ℕ∞) : ContDiff ℝ n coreSectionCoordinates := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreSectionCoordinates] <;> fun_prop

theorem coreSectionEmbedding_fderiv (z v : CoreCoordinates) :
    fderiv ℝ coreSectionEmbedding z v = ![v 0, v 1, 0, v 2] := by
  have hd : HasDerivAt (fun s : ℝ => coreSectionEmbedding (z + s • v)) ![v 0, v 1, 0, v 2] 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [coreSectionEmbedding] using ((hasDerivAt_id (0 : ℝ)).mul_const (v 0)).const_add (z 0)
    · simpa [coreSectionEmbedding] using ((hasDerivAt_id (0 : ℝ)).mul_const (v 1)).const_add (z 1)
    · exact hasDerivAt_const 0 1
    · simpa [coreSectionEmbedding] using ((hasDerivAt_id (0 : ℝ)).mul_const (v 2)).const_add (z 2)
  have hl : HasDerivAt (fun s : ℝ => z + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) z).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hf : HasFDerivAt coreSectionEmbedding (fderiv ℝ coreSectionEmbedding z) (z + (0 : ℝ) • v) := by
    simpa only [zero_smul, add_zero] using
      ((contDiff_coreSectionEmbedding 1).differentiable (by norm_num) z).hasFDerivAt
  have H : HasDerivAt (fun s : ℝ => coreSectionEmbedding (z + s • v))
      (fderiv ℝ coreSectionEmbedding z v) 0 := by
    convert! hf.comp_hasDerivAt 0 hl using 1
  exact H.unique hd

theorem coreSectionCoordinates_fderiv (y v : ProjectiveState) :
    fderiv ℝ coreSectionCoordinates y v = coreSectionCoordinates v := by
  have hd : HasDerivAt (fun s : ℝ => coreSectionCoordinates (y + s • v)) (coreSectionCoordinates v) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [coreSectionCoordinates] using ((hasDerivAt_id (0 : ℝ)).mul_const (v 0)).const_add (y 0)
    · simpa [coreSectionCoordinates] using ((hasDerivAt_id (0 : ℝ)).mul_const (v 1)).const_add (y 1)
    · simpa [coreSectionCoordinates] using ((hasDerivAt_id (0 : ℝ)).mul_const (v 3)).const_add (y 3)
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hf : HasFDerivAt coreSectionCoordinates (fderiv ℝ coreSectionCoordinates y) (y + (0 : ℝ) • v) := by
    simpa only [zero_smul, add_zero] using
      ((contDiff_coreSectionCoordinates 1).differentiable (by norm_num) y).hasFDerivAt
  have H : HasDerivAt (fun s : ℝ => coreSectionCoordinates (y + s • v))
      (fderiv ℝ coreSectionCoordinates y v) 0 := by
    convert! hf.comp_hasDerivAt 0 hl using 1
  exact H.unique hd

theorem referenceCoreInput_embedding {k : ℝ} (hk : 1 < k) :
    coreSectionEmbedding (referenceCoreInput k) = referencePulse k (-referenceHalfTime k) := by
  rw [referencePulse_entry hk]
  rfl

theorem referenceCoreInput_chart {k : ℝ} (hk : 1 < k) :
    coreSectionChart (referenceCoreInput k) = referenceEntryState k := by
  rw [coreSectionChart, referenceCoreInput_embedding hk]
  rfl

/-- A local three-coordinate exit map with the fully evaluated derivative of (A.4). -/
theorem exists_referenceCore_section_event {k : ℝ} (hk : 1 < k) :
    ∃ (tau : CoreCoordinates → ℝ) (P : CoreCoordinates → CoreCoordinates),
      tau (referenceCoreInput k) = referenceNormalizedTime k ∧
      P (referenceCoreInput k) = referenceCoreOutput k ∧
      ContDiffAt ℝ 1 tau (referenceCoreInput k) ∧ ContDiffAt ℝ 1 P (referenceCoreInput k) ∧
      (∀ᶠ z in 𝓝 (referenceCoreInput k), 0 < tau z ∧
        tau z ∈ normalizedMaxDomain (coreSectionChart z) 0 ∧
        toProjectiveState (normalizedMaxCurve (coreSectionChart z) 0 (tau z)) = coreSectionEmbedding (P z)) ∧
      (∀ᶠ z : CoreCoordinates × ℝ in 𝓝 (referenceCoreInput k, referenceNormalizedTime k),
        z.2 ∈ normalizedMaxDomain (coreSectionChart z.1) 0 ∧
        (projectiveActiveWall (normalizedMaxCurve (coreSectionChart z.1) 0 z.2) = 1 ↔ tau z.1 = z.2)) ∧
      (∀ v : CoreCoordinates, fderiv ℝ P (referenceCoreInput k) v =
        ![-v 0 + (2 / Real.sqrt (k ^ 2 - 1)) * (1 - Real.exp (-k * Real.arcosh k)) * v 1,
          Real.exp (-k * Real.arcosh k) * v 1, Real.exp (-4 * Real.arcosh k / k) * v 2]) := by
  let z₀ := referenceCoreInput k
  have hemb := referenceCoreInput_embedding hk
  have hbase := referenceCoreInput_chart hk
  have hcC : ContDiffAt ℝ 1 coreSectionChart z₀ := by
    have hf := contDiffAt_fromProjectiveState 1 (ne_of_gt (referencePulse_denom_pos k (-referenceHalfTime k)))
    rw [← hemb] at hf
    exact hf.comp z₀ (contDiff_coreSectionEmbedding 1).contDiffAt
  obtain ⟨T, hT, hcT, _, hhit, huniq, hcE, hdE⟩ := exists_referenceCore_event hk
  let E : NormalizedState → NormalizedState := fun y => normalizedMaxCurve y 0 (T y)
  let tau : CoreCoordinates → ℝ := fun z => T (coreSectionChart z)
  let P : CoreCoordinates → CoreCoordinates := fun z =>
    coreSectionCoordinates (toProjectiveState (E (coreSectionChart z)))
  have hE : E (coreSectionChart z₀) = referenceExitState k := by
    dsimp [E, z₀]
    rw [hbase, hT, (referenceEntryState_crossing hk).2]
  have hτ : tau z₀ = referenceNormalizedTime k := by dsimp [tau, z₀]; rw [hbase, hT]
  have hcτ : ContDiffAt ℝ 1 tau z₀ := (hbase.symm ▸ hcT).comp z₀ hcC
  have hto := contDiffAt_toProjectiveState 1 (ne_of_gt (referenceExitState_clock_pos k))
  have hcEC : ContDiffAt ℝ 1 (fun z => E (coreSectionChart z)) z₀ := by
    convert! (hbase.symm ▸ hcE).comp z₀ hcC using 1
  have hto' : ContDiffAt ℝ 1 toProjectiveState (E (coreSectionChart z₀)) := by rw [hE]; exact hto
  have hcP : ContDiffAt ℝ 1 P z₀ := by
    convert! (contDiff_coreSectionCoordinates 1).contDiffAt.comp z₀ (hto'.comp z₀ hcEC) using 1
  refine ⟨tau, P, hτ, ?_, hcτ, hcP, ?_, ?_, ?_⟩
  · dsimp [P]
    rw [hE, referenceExitState_projective, referencePulse_exit hk]
    rfl
  · have hpos : ∀ᶠ z in 𝓝 z₀, 0 < tau z :=
      (isOpen_Ioi.mem_nhds (show tau z₀ ∈ Ioi 0 by rw [hτ]; exact referenceNormalizedTime_pos hk))
        |> hcτ.continuousAt.eventually
    have hlocal := hcC.continuousAt.eventually (hbase.symm ▸ hhit)
    filter_upwards [hpos, hlocal] with z hz hloc
    refine ⟨hz, hloc.1, ?_⟩
    ext i
    fin_cases i
    · rfl
    · rfl
    · exact hloc.2
    · rfl
  · have hmap : ContinuousAt (fun z : CoreCoordinates × ℝ => (coreSectionChart z.1, z.2))
        (z₀, referenceNormalizedTime k) := by
      have hfst : ContinuousAt (fun z : CoreCoordinates × ℝ => coreSectionChart z.1)
          (z₀, referenceNormalizedTime k) := by
        have hf : ContinuousAt (Prod.fst : CoreCoordinates × ℝ → CoreCoordinates)
            (z₀, referenceNormalizedTime k) := continuousAt_fst
        exact ContinuousAt.comp (f := (Prod.fst : CoreCoordinates × ℝ → CoreCoordinates))
          (g := coreSectionChart) hcC.continuousAt hf
      exact hfst.prodMk continuousAt_snd
    have H := hmap.eventually (hbase.symm ▸ huniq)
    exact H
  · intro v
    have hdfrom := ((contDiffAt_fromProjectiveState 1
      (ne_of_gt (referencePulse_denom_pos k (-referenceHalfTime k)))).differentiableAt (by norm_num)).hasFDerivAt
    have hdemb := ((contDiff_coreSectionEmbedding 1).differentiable (by norm_num) z₀).hasFDerivAt
    have hdC' := (hemb.symm ▸ hdfrom).comp z₀ hdemb
    have hdE' := (hbase.symm ▸ hdE).comp z₀ hdC'
    have hdto := ((hE.symm ▸ hto).differentiableAt (by norm_num)).hasFDerivAt.comp z₀ hdE'
    have hdP := ((contDiff_coreSectionCoordinates 1).differentiable (by norm_num)
      (toProjectiveState (E (coreSectionChart z₀)))).hasFDerivAt.comp z₀ hdto
    rw [show fderiv ℝ P z₀ = _ from hdP.fderiv]
    simp only [ContinuousLinearMap.comp_apply, coreSectionCoordinates_fderiv,
      coreSectionEmbedding_fderiv, hE, hemb, hbase]
    rw [referenceCore_actual_derivative hk (w := ![v 0, v 1, 0, v 2]) rfl]
    rfl

end BianchiIX
