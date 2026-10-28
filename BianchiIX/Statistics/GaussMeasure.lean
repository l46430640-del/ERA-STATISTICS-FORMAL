import BianchiIX.Statistics.GaussTransport
import Mathlib.MeasureTheory.Measure.WithDensity

/-! The normalized Gauss density, its interval masses, and its equivalence to phase length. -/

open Set MeasureTheory
open scoped ENNReal

namespace BianchiIX

noncomputable section

def gaussWeight (x : ℝ) : ℝ := 1 / (Real.log 2 * (1 + x))

def gaussMeasure : Measure ℝ :=
  (volume.restrict (Ioo (0 : ℝ) 1)).withDensity (fun x => ENNReal.ofReal (gaussWeight x))

def gaussPrimitive (x : ℝ) : ℝ := Real.log (1 + x) / Real.log 2

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem gaussWeight_pos {x : ℝ} (hx : 0 ≤ x) : 0 < gaussWeight x := by
  unfold gaussWeight
  exact one_div_pos.mpr (mul_pos log_two_pos (by linarith))

theorem measurable_gaussWeight : Measurable gaussWeight :=
  measurable_const.div (measurable_const.mul (measurable_const.add measurable_id))

theorem hasDerivAt_gaussPrimitive {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt gaussPrimitive (gaussWeight x) x := by
  have h := (((hasDerivAt_id x).const_add 1).log (by linarith : (1 : ℝ) + x ≠ 0)).div_const (Real.log 2)
  convert! h using 1
  dsimp only [id_eq]
  simp only [gaussWeight, div_eq_mul_inv, mul_inv_rev, one_mul]

theorem gaussPrimitive_strictMonoOn : StrictMonoOn gaussPrimitive (Ici 0) := by
  intro x hx y _ hxy
  apply (div_lt_div_iff_of_pos_right log_two_pos).mpr
  exact Real.log_lt_log (by change 0 ≤ x at hx; linarith) (by linarith)

theorem gaussWeight_lintegral_Ioo {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫⁻ x in Ioo a b, ENNReal.ofReal (gaussWeight x)) =
      ENNReal.ofReal (gaussPrimitive b - gaussPrimitive a) := by
  have hcont : ContinuousOn gaussPrimitive (Icc a b) :=
    fun x hx => (hasDerivAt_gaussPrimitive (ha.trans hx.1)).continuousAt.continuousWithinAt
  have hsub : Icc a b ⊆ Ici (0 : ℝ) := fun _ hx => ha.trans hx.1
  have himg := hcont.image_Ioo_of_strictMonoOn hab (gaussPrimitive_strictMonoOn.mono hsub)
  have hchange := volume_image_eq_lintegral_abs_deriv measurableSet_Ioo
    (fun x (hx : x ∈ Ioo a b) => hasDerivAt_gaussPrimitive (ha.trans hx.1.le))
    (gaussPrimitive_strictMonoOn.injOn.mono (fun _ hx => ha.trans hx.1.le))
  have heq : (∫⁻ x in Ioo a b, ENNReal.ofReal (gaussWeight x)) =
      ∫⁻ x in Ioo a b, ENNReal.ofReal |gaussWeight x| := by
    apply lintegral_congr_ae
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro x hx
    dsimp only
    rw [abs_of_pos (gaussWeight_pos (ha.trans hx.1.le))]
  rw [heq, ← hchange, himg, Real.volume_Ioo]

theorem gaussMeasure_apply {A : Set ℝ} (hA : MeasurableSet A) (hsub : A ⊆ Ioo (0 : ℝ) 1) :
    gaussMeasure A = ∫⁻ x in A, ENNReal.ofReal (gaussWeight x) := by
  rw [gaussMeasure, withDensity_apply _ hA, Measure.restrict_restrict_of_subset hsub]

theorem gaussMeasure_Ioo {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    gaussMeasure (Ioo a b) = ENNReal.ofReal ((Real.log (1 + b) - Real.log (1 + a)) / Real.log 2) := by
  rw [gaussMeasure_apply measurableSet_Ioo
    (fun _ hx => ⟨ha.trans_lt hx.1, hx.2.trans_le hb⟩), gaussWeight_lintegral_Ioo ha hab]
  congr 1
  simp only [gaussPrimitive, sub_div]

theorem gaussMeasure_univ : gaussMeasure univ = 1 := by
  rw [gaussMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    gaussWeight_lintegral_Ioo (a := 0) (b := 1) le_rfl zero_le_one]
  norm_num [gaussPrimitive]

instance : IsProbabilityMeasure gaussMeasure := ⟨gaussMeasure_univ⟩

instance : NullSingletonClass gaussMeasure := by
  unfold gaussMeasure
  infer_instance

theorem gaussMeasure_absolutelyContinuous : gaussMeasure ≪ volume.restrict (Ioo (0 : ℝ) 1) :=
  withDensity_absolutelyContinuous _ _

theorem volume_restrict_absolutelyContinuous_gaussMeasure :
    volume.restrict (Ioo (0 : ℝ) 1) ≪ gaussMeasure := by
  apply withDensity_absolutelyContinuous' measurable_gaussWeight.ennreal_ofReal.aemeasurable
  apply ae_restrict_of_forall_mem measurableSet_Ioo
  intro x hx
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (gaussWeight_pos hx.1.le))

theorem gaussMeasure_null_iff (A : Set ℝ) :
    gaussMeasure A = 0 ↔ (volume.restrict (Ioo (0 : ℝ) 1)) A = 0 :=
  ⟨fun h => volume_restrict_absolutelyContinuous_gaussMeasure h,
    fun h => gaussMeasure_absolutelyContinuous h⟩

theorem ae_gaussMeasure_mem_unit : ∀ᵐ x ∂gaussMeasure, x ∈ Ioo (0 : ℝ) 1 :=
  gaussMeasure_absolutelyContinuous.ae_le (ae_restrict_mem measurableSet_Ioo)

theorem ae_gaussMeasure_irrational : ∀ᵐ x ∂gaussMeasure, Irrational x := by
  rw [ae_iff]
  have heq : {x : ℝ | ¬ Irrational x} = Set.range ((↑) : ℚ → ℝ) := by
    ext x
    simp [Irrational]
  rw [heq]
  exact (countable_range ((↑) : ℚ → ℝ)).measure_zero gaussMeasure

theorem gaussWeight_bounds {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    1 / (2 * Real.log 2) ≤ gaussWeight x ∧ gaussWeight x ≤ 1 / Real.log 2 := by
  have hc := log_two_pos
  have hd : 0 < Real.log 2 * (1 + x) := mul_pos hc (by linarith [hx.1])
  constructor
  · apply (div_le_div_iff₀ (mul_pos (by norm_num) hc) hd).mpr
    nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hx.2)]
  · apply (div_le_div_iff₀ hd hc).mpr
    nlinarith [mul_nonneg hc.le hx.1]

theorem gaussMeasure_bounds :
    ENNReal.ofReal (1 / (2 * Real.log 2)) • volume.restrict (Ioo (0 : ℝ) 1) ≤ gaussMeasure ∧
      gaussMeasure ≤ ENNReal.ofReal (1 / Real.log 2) • volume.restrict (Ioo (0 : ℝ) 1) := by
  constructor
  · rw [← withDensity_const]
    apply withDensity_mono
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro x hx
    exact ENNReal.ofReal_le_ofReal (gaussWeight_bounds ⟨hx.1.le, hx.2.le⟩).1
  · rw [← withDensity_const]
    apply withDensity_mono
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro x hx
    exact ENNReal.ofReal_le_ofReal (gaussWeight_bounds ⟨hx.1.le, hx.2.le⟩).2

theorem gaussMeasure_tail_interval (k : ℕ+) :
    gaussMeasure (Ioo 0 (1 / (k : ℝ))) = ENNReal.ofReal (Real.log (1 + 1 / (k : ℝ)) / Real.log 2) := by
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast k.pos
  have hkpos : (0 : ℝ) < k := by linarith
  simpa using gaussMeasure_Ioo (a := 0) (b := 1 / k) le_rfl (by positivity)
    ((div_le_one hkpos).mpr hk)

theorem gaussMeasure_digit_interval (k : ℕ+) :
    gaussMeasure (Ioo (1 / ((k : ℝ) + 1)) (1 / (k : ℝ))) =
      ENNReal.ofReal (Real.log (((k : ℝ) + 1) ^ 2 / ((k : ℝ) * ((k : ℝ) + 2))) / Real.log 2) := by
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast k.pos
  have hkpos : (0 : ℝ) < k := by linarith
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by linarith
  rw [gaussMeasure_Ioo (by positivity)
    ((div_le_div_iff₀ hk1 hkpos).mpr (by linarith)) ((div_le_one hkpos).mpr hk)]
  rw [← Real.log_div (by positivity : (1 : ℝ) + 1 / (k : ℝ) ≠ 0)
    (by positivity : (1 : ℝ) + 1 / ((k : ℝ) + 1) ≠ 0)]
  congr 3
  field_simp
  ring

theorem gauss_log_tail_sum (R : ℕ) :
    (∑ j ∈ Finset.range R, Real.log (1 + 1 / ((j : ℝ) + 1)) / Real.log 2) =
      Real.log ((R : ℝ) + 1) / Real.log 2 := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ, ih, ← add_div]
    have hr : (0 : ℝ) < (R : ℝ) + 1 := by positivity
    have hfrac : (1 : ℝ) + 1 / ((R : ℝ) + 1) = ((R : ℝ) + 2) / ((R : ℝ) + 1) := by
      field_simp
      ring
    rw [hfrac, Real.log_div (by positivity) hr.ne']
    congr 1
    push_cast
    rw [show (R : ℝ) + 1 + 1 = (R : ℝ) + 2 by ring]
    ring

end
end BianchiIX
