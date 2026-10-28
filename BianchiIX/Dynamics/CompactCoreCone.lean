import BianchiIX.Dynamics.CompactCoreRadial
import BianchiIX.Algebra.CoreConeSize

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

theorem compactCoreFactor_transverse_differential {Y : CoreAngleState} (i : Fin 2)
    (hF : DifferentiableAt ℝ (coreReturnState coreRadiusReturnTime) Y)
    (hm : DifferentiableAt ℝ (fun Z => compactCoreFactor Z i) Y)
    (hpos : 0 < compactCoreFactor Y i)
    (hnear : ∀ᶠ Z in 𝓝 Y,
      coreReturnState coreRadiusReturnTime Z i.succ = Z i.succ * compactCoreFactor Z i)
    (v : CoreAngleState) :
    (fderiv ℝ (coreReturnState coreRadiusReturnTime) Y v) i.succ = compactCoreFactor Y i *
      (v i.succ + Y i.succ * fderiv ℝ (fun Z => Real.log (compactCoreFactor Z i)) Y v) := by
  have hprod := (hasFDerivAt_apply (𝕜 := ℝ) i.succ Y).mul hm.hasFDerivAt
  change HasFDerivAt (fun Z => Z i.succ * compactCoreFactor Z i) _ Y at hprod
  change (fun Z => coreReturnState coreRadiusReturnTime Z i.succ) =ᶠ[𝓝 Y]
    (fun Z => Z i.succ * compactCoreFactor Z i) at hnear
  have H := congrArg (fun L : CoreAngleState →L[ℝ] ℝ => L v)
    (hnear.fderiv_eq.trans hprod.fderiv)
  rw [fderiv_apply hF i.succ] at H
  rw [(hm.hasFDerivAt.log (ne_of_gt hpos)).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    add_apply, smul_apply, smul_eq_mul] at H ⊢
  rw [H]
  field_simp [ne_of_gt hpos]
  ring

/-- A fixed strict cone contraction holds on the compact reference segment, including zero walls. -/
theorem exists_compact_core_cone :
    ∃ ε > (0 : ℝ), ∃ σ > (0 : ℝ), σ < 1 ∧
      ∀ Y : CoreAngleState, (2 ≤ Y 0 ∧ Y 0 ≤ 6) →
        (0 ≤ Y 1 ∧ Y 1 ≤ ε) → (0 ≤ Y 2 ∧ Y 2 ≤ ε) →
        coreRadiusReturnValid Y ∧ ContDiffAt ℝ 2 (coreReturnState coreRadiusReturnTime) Y ∧
        ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
          let d := fderiv ℝ (coreReturnState coreRadiusReturnTime) Y v
          0 < d 0 ∧ ∀ i : Fin 2,
            |d i.succ| ≤ σ * Real.sqrt (coreReturnState coreRadiusReturnTime Y i.succ) * d 0 := by
  obtain ⟨εf, hεf, q, hq, hq1, L, hL, hf⟩ := exists_compact_core_factor_bounds
  let s := Real.sqrt q
  have hs : 0 < s := Real.sqrt_pos.mpr hq
  have hs1 : s < 1 := by
    dsimp [s]
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt hq.le hq1
  let e := (1 - s) / 4
  have he : 0 < e := by dsimp [e]; linarith only [hs1]
  have he4 : e < 1 / 4 := by dsimp [e]; linarith only [hs]
  have hse : s + 4 * e = 1 := by dsimp [e]; ring
  obtain ⟨εr, hεr, R, hR, hr⟩ := exists_compact_core_radial_margin he
  let b := e / (1 + R + L)
  have hb : 0 < b := by dsimp [b]; positivity
  have hbudget : (1 + R + L) * b = e := by dsimp [b]; field_simp
  let ε := min εf (min εr (min 1 (b ^ 2)))
  have hε : 0 < ε := lt_min hεf (lt_min hεr (lt_min zero_lt_one (sq_pos_of_pos hb)))
  have hεf' : ε ≤ εf := min_le_left _ _
  have hεr' : ε ≤ εr := (min_le_right _ _).trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεb : ε ≤ b ^ 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hseb : Real.sqrt ε ≤ b := (Real.sqrt_le_iff).mpr ⟨hb.le, hεb⟩
  have hLe : L * Real.sqrt ε ≤ e := by
    have H := mul_le_mul_of_nonneg_left hseb hL.le
    nlinarith only [H, hbudget, hb.le, mul_nonneg hR.le hb.le]
  have hRe : R * Real.sqrt ε ≤ e := by
    have H := mul_le_mul_of_nonneg_left hseb hR.le
    nlinarith only [H, hbudget, hb.le, mul_nonneg hL.le hb.le]
  have hσ : 0 < 1 - e := by linarith only [he4]
  refine ⟨ε, hε, 1 - e, hσ, by linarith only [he], ?_⟩
  intro Y hk hu hw
  have habsu : |Y 1| ≤ ε := (abs_of_nonneg hu.1).le.trans hu.2
  have habsw : |Y 2| ≤ ε := (abs_of_nonneg hw.1).le.trans hw.2
  obtain ⟨hvalid, hF, hfac⟩ := hf Y hk (habsu.trans hεf') (habsw.trans hεf')
  obtain ⟨hrad, hnorm⟩ := hr Y hk (habsu.trans hεr') (habsw.trans hεr')
  refine ⟨hvalid, hF, ?_⟩
  intro v hv ha hb'
  let D := fderiv ℝ (coreReturnState coreRadiusReturnTime) Y
  let v₀ : CoreAngleState := Pi.single 0 1
  have hsu := Real.sqrt_le_sqrt hu.2
  have hsw := Real.sqrt_le_sqrt hw.2
  have hse1 : Real.sqrt ε ≤ 1 := (Real.sqrt_le_one).mpr hε1
  have hvnorm : ‖v‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    fin_cases i
    · simp [hv]
    · exact ha.trans (hsu.trans hse1)
    · exact hb'.trans (hsw.trans hse1)
  have hdiff : ‖v - v₀‖ ≤ Real.sqrt ε := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    fin_cases i
    · simp [v₀, hv, Real.sqrt_nonneg]
    · simpa [v₀] using ha.trans hsu
    · simpa [v₀] using hb'.trans hsw
  have herror : |D (v - v₀) 0| ≤ e := by
    calc
      _ ≤ ‖D (v - v₀)‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (D (v - v₀)) 0
      _ ≤ ‖D‖ * ‖v - v₀‖ := D.le_opNorm _
      _ ≤ R * Real.sqrt ε := mul_le_mul hnorm hdiff (norm_nonneg _) hR.le
      _ ≤ e := hRe
  have hradial : |D v 0 - 1| ≤ 2 * e := by
    calc
      _ = |(D v₀ 0 - 1) + D (v - v₀) 0| := by rw [map_sub]; congr 1; simp
      _ ≤ |D v₀ 0 - 1| + |D (v - v₀) 0| := abs_add_le _ _
      _ ≤ 2 * e := by linarith only [hrad, herror]
  have hdlo : 1 - 2 * e ≤ D v 0 := by linarith only [(abs_le.mp hradial).1]
  have hdpos : 0 < D v 0 := by linarith only [he4, hdlo]
  refine ⟨hdpos, ?_⟩
  intro i
  obtain ⟨hprod, hmpos, hmq, hm, _, hlog, hnear⟩ := hfac i
  have hui : 0 ≤ Y i.succ ∧ Y i.succ ≤ ε := by fin_cases i <;> assumption
  have hvi : |v i.succ| ≤ Real.sqrt (Y i.succ) := by fin_cases i <;> assumption
  let l := fderiv ℝ (fun Z => Real.log (compactCoreFactor Z i)) Y v
  have hl : |l| ≤ L := by
    calc
      _ ≤ ‖fderiv ℝ (fun Z => Real.log (compactCoreFactor Z i)) Y‖ * ‖v‖ :=
        (fderiv ℝ (fun Z => Real.log (compactCoreFactor Z i)) Y).le_opNorm v
      _ ≤ L * 1 := mul_le_mul hlog hvnorm (norm_nonneg _) hL.le
      _ = L := mul_one _
  have hsqrtm : Real.sqrt (compactCoreFactor Y i) ≤ s := Real.sqrt_le_sqrt hmq
  have hsqrtu : Real.sqrt (Y i.succ) * |l| ≤ e := by
    calc
      _ ≤ Real.sqrt ε * L := mul_le_mul (Real.sqrt_le_sqrt hui.2) hl (abs_nonneg _) (Real.sqrt_nonneg _)
      _ ≤ e := by simpa only [mul_comm] using hLe
  have hcoeff : Real.sqrt (compactCoreFactor Y i) +
      Real.sqrt (compactCoreFactor Y i) * Real.sqrt (Y i.succ) * |l| ≤ s + e := by
    have H : Real.sqrt (compactCoreFactor Y i) * (Real.sqrt (Y i.succ) * |l|) ≤ 1 * e :=
      mul_le_mul (hsqrtm.trans hs1.le) hsqrtu (by positivity) zero_le_one
    nlinarith only [H, hsqrtm]
  have hgain : s + e ≤ (1 - e) * D v 0 := by
    have H := mul_le_mul_of_nonneg_left hdlo hσ.le
    nlinarith only [H, hse, sq_nonneg e]
  have hd := compactCoreFactor_transverse_differential i
    (hF.differentiableAt (by norm_num)) (hm.differentiableAt (by norm_num)) hmpos hnear v
  have H := wall_multiplier_cone_bound hui.1 hmpos (θ := 1) (by simpa using hvi) hd
  simp only [mul_one] at H
  calc
    |D v i.succ| ≤ Real.sqrt (Y i.succ * compactCoreFactor Y i) *
        (Real.sqrt (compactCoreFactor Y i) + Real.sqrt (compactCoreFactor Y i) * Real.sqrt (Y i.succ) * |l|) := H
    _ ≤ Real.sqrt (Y i.succ * compactCoreFactor Y i) * ((1 - e) * D v 0) :=
      mul_le_mul_of_nonneg_left (hcoeff.trans hgain) (Real.sqrt_nonneg _)
    _ = (1 - e) * Real.sqrt (coreReturnState coreRadiusReturnTime Y i.succ) * D v 0 := by rw [hprod]; ring

end BianchiIX
