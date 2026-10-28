import BianchiIX.Algebra.CoreDomain

noncomputable section

namespace BianchiIX

theorem core_section_phase_gap {k m : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ coreRadius m 1) : 3 * k / 4 ≤ |m - 1| := by
  have hr2 := (sq_le_sq₀ (by linarith : 0 ≤ 99 / 100 * k)
    (show 0 ≤ coreRadius m 1 from Real.sqrt_nonneg _)).mpr hr
  rw [coreRadius_sq] at hr2
  unfold coreEnergy at hr2
  apply (sq_le_sq₀ (by linarith : 0 ≤ 3 * k / 4) (abs_nonneg _)).mp
  rw [sq_abs]
  nlinarith [sq_nonneg (k - 6)]

theorem core_section_coupling_bound {k u w : ℝ} (hk : 6 ≤ k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    0 ≤ coupling u 1 w ∧ coupling u 1 w ≤ 1 / 1000 := by
  have hu' := coreBootstrap_wall_bound hk hu.2
  have hw' := coreBootstrap_wall_bound hk hw.2
  refine ⟨coreBootstrap_coupling_nonneg hk le_rfl hu hw.1, ?_⟩
  have H := mul_le_mul hu' (show 1 + w - u ≤ 2 by linarith)
    (show 0 ≤ 1 + w - u by linarith) (by norm_num : (0 : ℝ) ≤ 1 / 60000)
  exact H.trans (by norm_num)

/-- The activity equation alone determines the orientation of both core crossings. -/
theorem core_section_velocity {k m u w : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ coreRadius m 1)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    (1 < m ∧ k / 2 ≤ activeVelocity m u 1 w) ∨
      (m < 1 ∧ activeVelocity m u 1 w ≤ -k / 2) := by
  have hgap := core_section_phase_gap hk hr
  have hC := core_section_coupling_bound hk hu hw
  by_cases hm : 1 ≤ m
  · rw [abs_of_nonneg (sub_nonneg.mpr hm)] at hgap
    left
    unfold activeVelocity
    constructor <;> nlinarith
  · rw [abs_of_neg (by linarith : m - 1 < 0)] at hgap
    right
    unfold activeVelocity
    constructor <;> nlinarith

theorem coreAngle_section_sign (m : ℝ) :
    (coreAngle m 1 < 0 ↔ 1 < m) ∧ (0 < coreAngle m 1 ↔ m < 1) := by
  simp only [coreAngle, div_one, Real.arsinh_neg_iff, Real.arsinh_pos_iff]
  constructor <;> constructor <;> intro h <;> linarith

theorem coreBootstrap_phase_bound {k m v : ℝ} (hk : 6 ≤ k)
    (hr : coreRadius m v ≤ 101 / 100 * k) : |m| ≤ 6 / 5 * k := by
  have H := (coreRadius_component_bounds m v).1.trans hr
  calc
    |m| = |(m - 1) + 1| := by congr 1; ring
    _ ≤ |m - 1| + |(1 : ℝ)| := abs_add_le _ _
    _ ≤ 6 / 5 * k := by norm_num at *; linarith

/-- The factored phase equation gives two-sided speed bounds throughout the core. -/
theorem coreBootstrap_phase_velocity {k m u v w : ℝ} (hk : 6 ≤ k)
    (hm : |m| ≤ 6 / 5 * k) (hv : 1 ≤ v)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k) (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    v ^ 2 / 2 ≤ -phaseVelocity m u v w ∧ -phaseVelocity m u v w ≤ 2 * v ^ 2 := by
  have hk0 : 0 < k := by linarith
  have hu' := coreBootstrap_wall_bound hk hu.2
  have hw' := coreBootstrap_wall_bound hk hw.2
  have hmu : |m * u| ≤ 1 / 1000 := by
    rw [abs_mul, abs_of_nonneg hu.1]
    calc
      |m| * u ≤ (6 / 5 * k) * ((1 / 10000) / k) :=
        mul_le_mul hm hu.2 hu.1 (by positivity)
      _ ≤ 1 / 1000 := by field_simp; norm_num
  have hmul := abs_le.mp hmu
  have h₁ : 9 / 10 * v ≤ v + w - u ∧ v + w - u ≤ 11 / 10 * v := by
    constructor <;> linarith
  have h₂ : 9 / 10 * v ≤ v - w + m * u ∧ v - w + m * u ≤ 11 / 10 * v := by
    constructor <;> linarith
  have hlo := mul_le_mul h₁.1 h₂.1 (by linarith : 0 ≤ 9 / 10 * v)
    (by linarith : 0 ≤ v + w - u)
  have hhi := mul_le_mul h₁.2 h₂.2 (by linarith : 0 ≤ v - w + m * u)
    (by linarith : 0 ≤ 11 / 10 * v)
  rw [phaseVelocity_factor]
  constructor <;> nlinarith [sq_nonneg v]

theorem coreBootstrap_strong_velocity {k m u v w : ℝ} (hk : 6 ≤ k)
    (hr : 99 / 100 * k ≤ coreRadius m v ∧ coreRadius m v ≤ 101 / 100 * k)
    (hu : 0 ≤ u ∧ u ≤ (1 / 10000) / k)
    (hw : 0 ≤ w ∧ w ≤ (1 / 10000) / k) :
    strongVelocity m u v w ≤ (-k ^ 2 / 10) * u := by
  have hm := (abs_le.mp ((coreRadius_component_bounds m v).1.trans hr.2)).1
  have hvhi : v ≤ 101 / 100 * k :=
    (le_abs_self v).trans ((coreRadius_component_bounds m v).2.trans hr.2)
  have hr2 : (99 / 100 * k) ^ 2 ≤ coreRadius m v ^ 2 :=
    (sq_le_sq₀ (by linarith) (by exact Real.sqrt_nonneg _)).mpr hr.1
  rw [coreRadius_sq] at hr2
  unfold coreEnergy at hr2
  have hu' := coreBootstrap_wall_bound hk hu.2
  have hw' := coreBootstrap_wall_bound hk hw.2
  have hu2 := (sq_le_sq₀ hu.1 (by norm_num : (0 : ℝ) ≤ 1 / 60000)).mpr hu'
  have hvw := mul_le_mul hvhi hw' hw.1 (by linarith : 0 ≤ 101 / 100 * k)
  have hbase : 1 - m ^ 2 - (v - w) ^ 2 + u ^ 2 ≤ -k ^ 2 / 5 := by
    nlinarith [sq_nonneg (k - 6), sq_nonneg w]
  have H := mul_le_mul_of_nonneg_right hbase hu.1
  unfold strongVelocity
  nlinarith

end BianchiIX
