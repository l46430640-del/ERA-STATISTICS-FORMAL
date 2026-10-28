import BianchiIX.Analysis.CompactVectorIntegral

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffAt_intervalIntegral_two {F : E × ℝ → ℝ} {x : E} {a b : ℝ}
    (hab : a ≤ b) (hF : ∀ t ∈ Icc a b, ContDiffAt ℝ 2 F (x, t)) :
    ContDiffAt ℝ 2 (fun y => ∫ t in a..b, F (y, t)) x := by
  let D : E × ℝ → E →L[ℝ] ℝ := fun p =>
    (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hD (t : ℝ) (ht : t ∈ Icc a b) : ContDiffAt ℝ 1 D (x, t) :=
    ((hF t ht).fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_comp contDiffAt_const
  have hs : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc a b, ContDiffAt ℝ 1 F (y, t) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    exact ((hF t ht).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).eventually (by norm_num)
  change ContDiffAt ℝ ((1 : ℕ) + 1) (fun y => ∫ t in a..b, F (y, t)) x
  apply contDiffAt_succ_iff_hasFDerivAt.mpr
  refine ⟨fun y => ∫ t in a..b, D (y, t), ⟨_, hs, ?_⟩,
    contDiffAt_compact_vector_integral hab hD⟩
  intro y hy
  exact hasFDerivAt_intervalIntegral_of_contDiffAt hab hy

/-- A variable endpoint retains two derivatives after rescaling to a fixed compact interval. -/
theorem contDiffAt_moving_intervalIntegral_two
    {F : E × ℝ → ℝ} {τ : E → ℝ} {x : E} (hτ : ContDiffAt ℝ 2 τ x) (hpos : 0 ≤ τ x)
    (hF : ∀ t ∈ Icc 0 (τ x), ContDiffAt ℝ 2 F (x, t)) :
    ContDiffAt ℝ 2 (fun y => ∫ t in 0..τ y, F (y, t)) x := by
  have hG (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ContDiffAt ℝ 2 (fun p : E × ℝ => τ p.1 * F (p.1, p.2 * τ p.1)) (x, t) := by
    have htime : t * τ x ∈ Icc 0 (τ x) :=
      ⟨mul_nonneg ht.1 hpos, by simpa using mul_le_mul_of_nonneg_right ht.2 hpos⟩
    have hcτ : ContDiffAt ℝ 2 (fun p : E × ℝ => τ p.1) (x, t) := hτ.comp (x, t) contDiffAt_fst
    have hp : ContDiffAt ℝ 2 (fun p : E × ℝ => (p.1, p.2 * τ p.1)) (x, t) :=
      contDiffAt_fst.prodMk (contDiffAt_snd.mul hcτ)
    exact hcτ.mul ((hF _ htime).comp (x, t) (g := F)
      (f := fun p : E × ℝ => (p.1, p.2 * τ p.1)) hp)
  convert! contDiffAt_intervalIntegral_two (by norm_num : (0 : ℝ) ≤ 1) hG using 1
  ext y
  exact integral_rescale_zero_one (fun t => F (y, t)) (τ y)

end BianchiIX
