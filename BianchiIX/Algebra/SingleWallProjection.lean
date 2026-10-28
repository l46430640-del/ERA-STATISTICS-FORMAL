import BianchiIX.Algebra.SingleWallBounds

noncomputable section

namespace BianchiIX

/-- The radial shear factor preserving the height of the first wall. -/
def singleWallProjectionScale (p s n : ℝ) : ℝ :=
  Real.sqrt ((1 - n ^ 2) / shearSq p s)

theorem singleWall_shear_defect {p s n b c Δ : ℝ}
    (hc : constraint p s n b c = 1) (hn : 0 < n) (hnmax : n ≤ 1 / 4)
    (hb : 0 ≤ b) (hc' : 0 ≤ c) (hΔ : 0 ≤ Δ ∧ Δ ≤ n / 8)
    (hnb : 4 * n * b ≤ Δ ^ 2) (hcn : 4 * c * n ≤ Δ ^ 2) :
    0 ≤ shearSq p s - (1 - n ^ 2) ∧
      shearSq p s - (1 - n ^ 2) ≤ Δ ^ 2 ∧
      15 / 16 ≤ shearSq p s ∧ shearSq p s ≤ 2 := by
  have hw := (weak_wall_sum_of_products hn le_rfl hb hc' hΔ hnb hcn).2
  have hsum : 2 * n * (b + c) ≤ Δ ^ 2 := by nlinarith only [hnb, hcn]
  have hsmall : b + c ≤ 2 * n := by linarith only [hw, hn]
  have hprod := mul_le_mul_of_nonneg_left hsmall (add_nonneg hb hc')
  have hdiff : (b - c) ^ 2 ≤ (b + c) ^ 2 := by nlinarith only [mul_nonneg hb hc']
  have heq : shearSq p s - (1 - n ^ 2) = 2 * n * (b + c) - (b - c) ^ 2 := by
    dsimp [constraint, curvature] at hc
    nlinarith only [hc]
  have hlo : 0 ≤ shearSq p s - (1 - n ^ 2) := by
    nlinarith only [heq, hprod, hdiff]
  have hhi : shearSq p s - (1 - n ^ 2) ≤ Δ ^ 2 := by
    nlinarith only [heq, hsum, sq_nonneg (b - c)]
  have hnsq : n ^ 2 ≤ 1 / 16 := by nlinarith only [hn, hnmax]
  have hΔsq : Δ ^ 2 ≤ 1 := by nlinarith only [hΔ.1, hΔ.2, hnmax]
  exact ⟨hlo, hhi, by linarith only [hlo, hnsq],
    by linarith only [hhi, hΔsq, sq_nonneg n]⟩

theorem singleWall_projection_scale_bounds {p s n b c Δ : ℝ}
    (hc : constraint p s n b c = 1) (hn : 0 < n) (hnmax : n ≤ 1 / 4)
    (hb : 0 ≤ b) (hc' : 0 ≤ c) (hΔ : 0 ≤ Δ ∧ Δ ≤ n / 8)
    (hnb : 4 * n * b ≤ Δ ^ 2) (hcn : 4 * c * n ≤ Δ ^ 2) :
    0 ≤ singleWallProjectionScale p s n ∧ singleWallProjectionScale p s n ≤ 1 ∧
      shearSq (singleWallProjectionScale p s n * p) (singleWallProjectionScale p s n * s) =
        1 - n ^ 2 ∧ 1 - singleWallProjectionScale p s n ≤ 2 * Δ ^ 2 := by
  obtain ⟨hlo, hhi, hq, _⟩ := singleWall_shear_defect hc hn hnmax hb hc' hΔ hnb hcn
  let q := shearSq p s
  let l := singleWallProjectionScale p s n
  have hqpos : 0 < q := by dsimp [q]; linarith only [hq]
  have hrad : 0 ≤ 1 - n ^ 2 := by nlinarith only [hn, hnmax]
  have hl0 : 0 ≤ l := Real.sqrt_nonneg _
  have hlsq : l ^ 2 * q = 1 - n ^ 2 := by
    dsimp [l, singleWallProjectionScale]
    rw [Real.sq_sqrt (div_nonneg hrad hqpos.le), div_mul_cancel₀ _ hqpos.ne']
  have hl1 : l ≤ 1 := by
    have H : l ^ 2 ≤ 1 := by nlinarith only [hlsq, hlo, hqpos]
    nlinarith only [H, hl0]
  have hlsql : l ^ 2 ≤ l := by nlinarith only [hl0, hl1]
  have H := mul_le_mul_of_nonneg_left hlsql hqpos.le
  have H' := mul_le_mul_of_nonneg_right (show 1 / 2 ≤ q by dsimp [q]; linarith only [hq])
    (sub_nonneg.mpr hl1)
  refine ⟨hl0, hl1, ?_, ?_⟩
  · change shearSq (l * p) (l * s) = 1 - n ^ 2
    calc
      _ = l ^ 2 * q := by dsimp [shearSq, q]; ring
      _ = _ := hlsq
  · change 1 - l ≤ 2 * Δ ^ 2
    change q - (1 - n ^ 2) ≤ Δ ^ 2 at hhi
    nlinarith only [H, H', hlsq, hhi]

/-- The radial change is quadratic in the weak-wall product scale. -/
theorem singleWall_projection_errors {p s n b c Δ : ℝ}
    (hc : constraint p s n b c = 1) (hn : 0 < n) (hnmax : n ≤ 1 / 4)
    (hb : 0 ≤ b) (hc' : 0 ≤ c) (hΔ : 0 ≤ Δ ∧ Δ ≤ n / 8)
    (hnb : 4 * n * b ≤ Δ ^ 2) (hcn : 4 * c * n ≤ Δ ^ 2) :
    |singleWallProjectionScale p s n * p - p| ≤ 4 * Δ ^ 2 ∧
      |singleWallProjectionScale p s n * s - s| ≤ 4 * Δ ^ 2 ∧
      |rateOne (singleWallProjectionScale p s n * p) (singleWallProjectionScale p s n * s) -
        rateOne p s| ≤ 9 * Δ ^ 2 := by
  obtain ⟨hlo, hhi, _, hq⟩ := singleWall_shear_defect hc hn hnmax hb hc' hΔ hnb hcn
  obtain ⟨hl0, hl1, hrad, hl⟩ := singleWall_projection_scale_bounds hc hn hnmax hb hc' hΔ hnb hcn
  let l := singleWallProjectionScale p s n
  have hp : |p| ≤ 2 := by
    dsimp [shearSq] at hq
    exact abs_le.mpr ⟨by nlinarith only [hq, sq_nonneg s], by nlinarith only [hq, sq_nonneg s]⟩
  have hs : |s| ≤ 2 := by
    dsimp [shearSq] at hq
    exact abs_le.mpr ⟨by nlinarith only [hq, sq_nonneg p], by nlinarith only [hq, sq_nonneg p]⟩
  have herr (z : ℝ) (hz : |z| ≤ 2) : |l * z - z| ≤ 4 * Δ ^ 2 := by
    rw [show l * z - z = -(1 - l) * z by ring, abs_mul, abs_neg,
      abs_of_nonneg (sub_nonneg.mpr hl1)]
    nlinarith only [mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr hl1), hl]
  have hep := herr p hp
  have hes := herr s hs
  refine ⟨hep, hes, ?_⟩
  change |rateOne (l * p) (l * s) - rateOne p s| ≤ 9 * Δ ^ 2
  have heq : rateOne (l * p) (l * s) - rateOne p s =
      (shearSq p s - (1 - n ^ 2)) + 2 * (l * p - p) := by
    dsimp [rateOne]
    rw [hrad]
    ring
  rw [heq]
  calc
    _ ≤ |shearSq p s - (1 - n ^ 2)| + |2 * (l * p - p)| := abs_add_le _ _
    _ ≤ 9 * Δ ^ 2 := by rw [abs_of_nonneg hlo, abs_mul]; norm_num; linarith only [hhi, hep]

end BianchiIX
