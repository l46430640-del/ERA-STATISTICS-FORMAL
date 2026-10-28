import BianchiIX.Measure.ShearRadialFlux
import BianchiIX.Measure.FailureFlux

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal Classical

def shearFailureFluxConstant (σ : ℝ) : ℝ := 640 * Real.sqrt 3 * (800 : ℝ) ^ σ

theorem shearFailureFluxConstant_ge_one {σ : ℝ} (hσ : 0 ≤ σ) : 1 ≤ shearFailureFluxConstant σ := by
  have hp : 1 ≤ (800 : ℝ) ^ σ := Real.one_le_rpow (by norm_num) hσ
  have hs : 1 ≤ Real.sqrt (3 : ℝ) := Real.one_le_sqrt.mpr (by norm_num)
  have H := mul_le_mul hs hp (by norm_num : (0 : ℝ) ≤ 1) (Real.sqrt_nonneg _)
  dsimp only [shearFailureFluxConstant]
  nlinarith only [H]

/-- Normalizing both weak-wall labels retains their product and the inverse-square radial scale. -/
theorem restartShearAmplitudeBudget_normalized {a x y σ : ℝ}
    (ha : 0 < a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    640 * Real.sqrt 3 * (restartShearAmplitudeBudget a (a * x) (a * y)) ^ σ =
      (shearFailureFluxConstant σ * a ^ (-2 * σ)) * (x * y) ^ σ := by
  have hB : restartShearAmplitudeBudget a (a * x) (a * y) =
      800 * (a ^ (-2 : ℝ) * (x * y)) := by
    rw [Real.rpow_neg ha.le, Real.rpow_two]
    unfold restartShearAmplitudeBudget
    field_simp
  rw [hB, Real.mul_rpow (by norm_num) (mul_nonneg (Real.rpow_nonneg ha.le _) (mul_nonneg hx hy)),
    Real.mul_rpow (Real.rpow_nonneg ha.le _) (mul_nonneg hx hy), ← Real.rpow_mul ha.le]
  dsimp only [shearFailureFluxConstant]
  ring

/-- Corrected flux integrated against the two logarithmic weak-wall labels on the selected positive-shear layer. -/
def restartShearFailureLayer (h s a ε P η : ℝ) (J : ℕ) (σ Bcap : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ y in Ioo (0 : ℝ) 1,
    if (a * x, a * y) ∈ restartShearLabelSet ε a P then
      restartShearRadialFlux h (a * x) (a * y)
        (eraRadialFailure η J σ (restartShearAmplitudeBudget a (a * x) (a * y)) Bcap a (2 * a)
          (restartShearReturnState h s (a * x) (a * y))) / ENNReal.ofReal (x * y)
    else 0

theorem restartShearFailureLayer_le {h s a ε P η σ Bcap : ℝ} {J : ℕ} (ha : 0 < a)
    (Hslice : ∀ n₂ n₃ : ℝ, (n₂, n₃) ∈ restartShearLabelSet ε a P →
      restartShearRadialFlux h n₂ n₃
        (eraRadialFailure η J σ (restartShearAmplitudeBudget a n₂ n₃) Bcap a (2 * a)
          (restartShearReturnState h s n₂ n₃)) ≤
        ENNReal.ofReal (3 * min a (640 * Real.sqrt 3 * (restartShearAmplitudeBudget a n₂ n₃) ^ σ))) :
    restartShearFailureLayer h s a ε P η J σ Bcap ≤
      3 * logarithmicLayerCost a (shearFailureFluxConstant σ) σ := by
  let f := fun x y : ℝ => ENNReal.ofReal
    (min a ((shearFailureFluxConstant σ * a ^ (-2 * σ)) * (x * y) ^ σ) / (x * y))
  have Hpoint (x y : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
      (if (a * x, a * y) ∈ restartShearLabelSet ε a P then
        restartShearRadialFlux h (a * x) (a * y)
          (eraRadialFailure η J σ (restartShearAmplitudeBudget a (a * x) (a * y)) Bcap a (2 * a)
            (restartShearReturnState h s (a * x) (a * y))) / ENNReal.ofReal (x * y)
        else 0) ≤ 3 * f x y := by
    split_ifs with hlabel
    · have H := ENNReal.div_le_div_right (Hslice (a * x) (a * y) hlabel) (ENNReal.ofReal (x * y))
      rw [restartShearAmplitudeBudget_normalized ha hx.1.le hy.1.le] at H
      refine H.trans_eq ?_
      rw [← ENNReal.ofReal_div_of_pos (mul_pos hx.1 hy.1)]
      change ENNReal.ofReal (3 * min a _ / (x * y)) = 3 * ENNReal.ofReal (min a _ / (x * y))
      rw [show (3 : ℝ) * min a _ / (x * y) = 3 * (min a _ / (x * y)) by ring,
        ENNReal.ofReal_mul (by norm_num)]
      norm_num
    · exact zero_le
  calc
    _ ≤ ∫⁻ x in Ioo (0 : ℝ) 1, ∫⁻ y in Ioo (0 : ℝ) 1, 3 * f x y :=
      setLIntegral_mono' measurableSet_Ioo (fun x hx =>
        setLIntegral_mono' measurableSet_Ioo (fun y hy => Hpoint x y hx hy))
    _ = _ := by
      simp_rw [lintegral_const_mul' (3 : ℝ≥0∞) _ (by norm_num)]
      rfl

/-- The selected actual shear family has finite logarithmic flux on every sufficiently small layer. -/
theorem exists_restartShear_failure_layer (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q P : ℝ, 3 < q → 4 < P → ∃ astar > (0 : ℝ),
            ∀ a ∈ Ioc (0 : ℝ) astar, ∀ ε : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) →
              let s := q / 2 * Real.log (1 / a)
              let K := 3 * logarithmicFluxConstant (shearFailureFluxConstant σ) σ
              restartShearFailureLayer h s a ε P η J σ Bcap ≤
                ENNReal.ofReal (K * a * (1 + |Real.log a|) ^ 2) ∧
                restartShearFailureLayer h s a ε P η J σ Bcap ≠ ⊤ := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartShear_failure_flux_slices hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hstar, hhstar, HH⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, hstar, hhstar, ?_⟩
  intro h hh q P hq hP
  obtain ⟨aS, haS, HaS⟩ := HH h hh q P hq hP
  refine ⟨min aS 1, lt_min haS zero_lt_one, ?_⟩
  intro a ha ε hε s K
  have Hslice (n₂ n₃ : ℝ) (hlabel : (n₂, n₃) ∈ restartShearLabelSet ε a P) :=
    (HaS a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε hε n₂ n₃
      hlabel.1 hlabel.2.1 hlabel.2.2).2 (Icc a (2 * a)) measurableSet_Icc (Subset.refl _)
  have H := restartShearFailureLayer_le ha.1 (fun n₂ n₃ hlabel => by
    have H' := Hslice n₂ n₃ hlabel
    rw [inter_eq_right.mpr (show eraRadialFailure η J σ (restartShearAmplitudeBudget a n₂ n₃)
      Bcap a (2 * a) (restartShearReturnState h s n₂ n₃) ⊆ Icc a (2 * a) from fun _ hρ => hρ.1)] at H'
    exact H')
  have Hbound := logarithmicLayerCost_le ha.1 (ha.2.trans (min_le_right _ _))
    (shearFailureFluxConstant_ge_one hσ.le) hσ
  have Hfinal : restartShearFailureLayer h s a ε P η J σ Bcap ≤
      ENNReal.ofReal (K * a * (1 + |Real.log a|) ^ 2) := calc
    _ ≤ _ := H
    _ ≤ 3 * ENNReal.ofReal (logarithmicFluxConstant (shearFailureFluxConstant σ) σ * a * (1 + |Real.log a|) ^ 2) :=
      mul_le_mul' le_rfl Hbound
    _ = _ := by
      rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      dsimp only [K]
      ring
  exact ⟨Hfinal, ne_top_of_le_ne_top ENNReal.ofReal_ne_top Hfinal⟩

end BianchiIX
