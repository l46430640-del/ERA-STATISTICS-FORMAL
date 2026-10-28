import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Ideal inverse branches and uniform cylinder contraction, Section 3.2. -/

namespace BianchiIX

noncomputable section

open Filter
open scoped Topology

def gaussInv (a x : ℝ) : ℝ := 1 / (a + x)

theorem gaussInv_pos {a x : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) : 0 < gaussInv a x := by
  unfold gaussInv
  exact one_div_pos.mpr (by linarith)

theorem gaussInv_le_one {a x : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) : gaussInv a x ≤ 1 := by
  unfold gaussInv
  exact (div_le_one (by linarith : 0 < a + x)).mpr (by linarith)

theorem hasDerivAt_gaussInv {a x : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) :
    HasDerivAt (gaussInv a) (-1 / (a + x) ^ 2) x := by
  have hden : a + x ≠ 0 := ne_of_gt (by linarith)
  unfold gaussInv
  simpa only [one_div, id_eq] using ((hasDerivAt_id x).const_add a).fun_inv hden

theorem gaussInv_pair_eq {a b x : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hx : 0 ≤ x) :
    gaussInv a (gaussInv b x) = (b + x) / (a * (b + x) + 1) := by
  have hbpos : 0 < b + x := by linarith
  have hapos : 0 < a + 1 / (b + x) := by positivity
  have hprod : 0 < a * (b + x) + 1 := by positivity
  unfold gaussInv
  field_simp

theorem hasDerivAt_gaussInv_pair {a b x : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hx : 0 ≤ x) :
    HasDerivAt (fun t => gaussInv a (gaussInv b t)) (1 / (a * (b + x) + 1) ^ 2) x := by
  have hbpos : 0 < b + x := by linarith
  have hapos : 0 < a + 1 / (b + x) := by positivity
  have hprod : 0 < a * (b + x) + 1 := by positivity
  have h := (hasDerivAt_gaussInv ha (gaussInv_pos hb hx).le).comp x (hasDerivAt_gaussInv hb hx)
  convert h using 1 <;> first | rfl | (
    unfold gaussInv
    field_simp)

theorem gaussInv_lipschitz {a x y : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |gaussInv a x - gaussInv a y| ≤ |x - y| := by
  have hax : 0 < a + x := by linarith
  have hay : 0 < a + y := by linarith
  have hden : 1 ≤ (a + x) * (a + y) := by
    nlinarith [mul_nonneg (show 0 ≤ a + x - 1 by linarith)
      (show 0 ≤ a + y - 1 by linarith)]
  have hid : gaussInv a x - gaussInv a y = (y - x) / ((a + x) * (a + y)) := by
    unfold gaussInv
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos (mul_pos hax hay), abs_sub_comm y x]
  exact div_le_self (abs_nonneg _) hden

theorem gaussInv_pair_lipschitz
    {a b x y : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |gaussInv a (gaussInv b x) - gaussInv a (gaussInv b y)| ≤ (1 / 4) * |x - y| := by
  have hdx : 2 ≤ a * (b + x) + 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ b + x by linarith)]
  have hdy : 2 ≤ a * (b + y) + 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ b + y by linarith)]
  have hdxpos : 0 < a * (b + x) + 1 := by linarith
  have hdypos : 0 < a * (b + y) + 1 := by linarith
  have hden : 4 ≤ (a * (b + x) + 1) * (a * (b + y) + 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdx) (sub_nonneg.mpr hdy)]
  rw [gaussInv_pair_eq ha hb hx, gaussInv_pair_eq ha hb hy]
  have hid : (b + x) / (a * (b + x) + 1) - (b + y) / (a * (b + y) + 1) =
      (x - y) / ((a * (b + x) + 1) * (a * (b + y) + 1)) := by
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos (mul_pos hdxpos hdypos)]
  calc
    _ ≤ |x - y| / 4 := div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) hden
    _ = (1 / 4) * |x - y| := by ring

def gaussWord : List ℕ → ℝ → ℝ
  | [], x => x
  | a :: w, x => gaussInv a (gaussWord w x)

theorem gaussWord_nonneg (w : List ℕ) (hw : ∀ a ∈ w, 1 ≤ a) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ gaussWord w x := by
  induction w with
  | nil => exact hx
  | cons a w ih =>
    have ha : (1 : ℝ) ≤ a := by exact_mod_cast hw a (by simp)
    exact (gaussInv_pos ha (ih (fun b hb => hw b (by simp [hb])))).le

theorem gaussWord_lipschitz (w : List ℕ) (hw : ∀ a ∈ w, 1 ≤ a)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |gaussWord w x - gaussWord w y| ≤ (1 / 4 : ℝ) ^ (w.length / 2) * |x - y| := by
  induction w using List.twoStepInduction with
  | nil => simp [gaussWord]
  | singleton a =>
    have ha : (1 : ℝ) ≤ a := by exact_mod_cast hw a (by simp)
    simpa [gaussWord] using gaussInv_lipschitz ha hx hy
  | cons_cons a b w ih _ =>
    have ha : (1 : ℝ) ≤ a := by exact_mod_cast hw a (by simp)
    have hb : (1 : ℝ) ≤ b := by exact_mod_cast hw b (by simp)
    have htail : ∀ c ∈ w, 1 ≤ c := fun c hc => hw c (by simp [hc])
    have hlen : (a :: b :: w).length / 2 = w.length / 2 + 1 := by
      simp [Nat.add_assoc, Nat.add_div_right]
    calc
      _ ≤ (1 / 4) * |gaussWord w x - gaussWord w y| :=
        gaussInv_pair_lipschitz ha hb (gaussWord_nonneg w htail hx) (gaussWord_nonneg w htail hy)
      _ ≤ (1 / 4) * ((1 / 4) ^ (w.length / 2) * |x - y|) :=
        mul_le_mul_of_nonneg_left (ih htail) (by norm_num)
      _ = _ := by rw [hlen, pow_succ]; ring

theorem gaussWord_diameter (w : List ℕ) (hw : ∀ a ∈ w, 1 ≤ a)
    {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |gaussWord w x - gaussWord w y| ≤ (1 / 4 : ℝ) ^ (w.length / 2) := by
  have hxy : |x - y| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hy.1, hx.2]⟩
  calc
    _ ≤ (1 / 4 : ℝ) ^ (w.length / 2) * |x - y| := gaussWord_lipschitz w hw hx.1 hy.1
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hxy (by positivity :
      0 ≤ (1 / 4 : ℝ) ^ (w.length / 2))

theorem gauss_two_step_error {a b y0 y1 y2 z2 : ℝ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hy1 : 0 ≤ y1) (hy2 : 0 ≤ y2) (hz2 : 0 ≤ z2) :
    |y0 - gaussInv a (gaussInv b z2)| ≤
      |y0 - gaussInv a y1| + |y1 - gaussInv b y2| + (1 / 4) * |y2 - z2| := by
  have h1 := abs_sub_le y0 (gaussInv a y1) (gaussInv a (gaussInv b z2))
  have h2 := abs_sub_le (gaussInv a y1) (gaussInv a (gaussInv b y2)) (gaussInv a (gaussInv b z2))
  have hsingle := gaussInv_lipschitz ha hy1 (gaussInv_pos hb hy2).le
  have hpair := gaussInv_pair_lipschitz ha hb hy2 hz2
  linarith

def inverseError (digits : ℕ → ℕ) (y : ℕ → ℝ) (m : ℕ) : ℝ :=
  |y m - gaussInv (digits m) (y (m + 1))|

theorem gauss_comparison_step {digits : ℕ → ℕ} {y z : ℕ → ℝ}
    (hdigits : ∀ m, 1 ≤ digits m) (hy : ∀ m, 0 ≤ y m) (hz : ∀ m, 0 ≤ z m)
    (hrec : ∀ m, z m = gaussInv (digits m) (z (m + 1))) (m : ℕ) :
    |y m - z m| ≤ inverseError digits y m + inverseError digits y (m + 1) +
      (1 / 4) * |y (m + 2) - z (m + 2)| := by
  have ha : (1 : ℝ) ≤ digits m := by exact_mod_cast hdigits m
  have hb : (1 : ℝ) ≤ digits (m + 1) := by exact_mod_cast hdigits (m + 1)
  have h := gauss_two_step_error (y0 := y m) ha hb (hy (m + 1)) (hy (m + 2)) (hz (m + 2))
  rw [hrec m, hrec (m + 1)]
  simpa only [inverseError, Nat.add_assoc] using h

/-- Finite expansion retains the actual terminal discrepancy. -/
theorem gauss_error_finite {digits : ℕ → ℕ} {y z : ℕ → ℝ}
    (hdigits : ∀ m, 1 ≤ digits m) (hy : ∀ m, 0 ≤ y m) (hz : ∀ m, 0 ≤ z m)
    (hrec : ∀ m, z m = gaussInv (digits m) (z (m + 1))) (m N : ℕ) :
    |y m - z m| ≤
      (∑ j ∈ Finset.range N, (1 / 4 : ℝ) ^ j *
        (inverseError digits y (m + 2 * j) + inverseError digits y (m + 2 * j + 1))) +
      (1 / 4 : ℝ) ^ N * |y (m + 2 * N) - z (m + 2 * N)| := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hs := gauss_comparison_step hdigits hy hz hrec (m + 2 * N)
    have hnext : m + 2 * N + 2 = m + 2 * (N + 1) := by ring
    calc
      _ ≤ (∑ j ∈ Finset.range N, (1 / 4 : ℝ) ^ j *
          (inverseError digits y (m + 2 * j) + inverseError digits y (m + 2 * j + 1))) +
          (1 / 4 : ℝ) ^ N * |y (m + 2 * N) - z (m + 2 * N)| := ih
      _ ≤ (∑ j ∈ Finset.range N, (1 / 4 : ℝ) ^ j *
          (inverseError digits y (m + 2 * j) + inverseError digits y (m + 2 * j + 1))) +
          (1 / 4 : ℝ) ^ N * (inverseError digits y (m + 2 * N) +
            inverseError digits y (m + 2 * N + 1) +
            (1 / 4) * |y (m + 2 * N + 2) - z (m + 2 * N + 2)|) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hs (by positivity :
          0 ≤ (1 / 4 : ℝ) ^ N))
      _ = _ := by rw [Finset.sum_range_succ, pow_succ, hnext]; ring

theorem gauss_error_finite_bound {digits : ℕ → ℕ} {y z : ℕ → ℝ}
    (hdigits : ∀ m, 1 ≤ digits m)
    (hy : ∀ m, y m ∈ Set.Icc (0 : ℝ) 1) (hz : ∀ m, z m ∈ Set.Icc (0 : ℝ) 1)
    (hrec : ∀ m, z m = gaussInv (digits m) (z (m + 1))) (m N : ℕ) :
    |y m - z m| ≤
      (∑ j ∈ Finset.range N, (1 / 4 : ℝ) ^ j *
        (inverseError digits y (m + 2 * j) + inverseError digits y (m + 2 * j + 1))) +
      (1 / 4 : ℝ) ^ N := by
  have htail : |y (m + 2 * N) - z (m + 2 * N)| ≤ 1 :=
    abs_le.mpr ⟨by linarith [(hy (m + 2 * N)).1, (hz (m + 2 * N)).2],
      by linarith [(hz (m + 2 * N)).1, (hy (m + 2 * N)).2]⟩
  have h := gauss_error_finite hdigits (fun n => (hy n).1) (fun n => (hz n).1) hrec m N
  have htail' := mul_le_mul_of_nonneg_left htail (by positivity : 0 ≤ (1 / 4 : ℝ) ^ N)
  linarith

theorem inverseError_le_one {digits : ℕ → ℕ} {y : ℕ → ℝ}
    (hdigits : ∀ m, 1 ≤ digits m) (hy : ∀ m, y m ∈ Set.Icc (0 : ℝ) 1) (m : ℕ) :
    inverseError digits y m ≤ 1 := by
  have ha : (1 : ℝ) ≤ digits m := by exact_mod_cast hdigits m
  have hpos := gaussInv_pos ha (hy (m + 1)).1
  have hle := gaussInv_le_one ha (hy (m + 1)).1
  exact abs_le.mpr ⟨by linarith [(hy m).1], by linarith [(hy m).2]⟩

theorem gauss_error_weights_summable {digits : ℕ → ℕ} {y : ℕ → ℝ}
    (hdigits : ∀ m, 1 ≤ digits m) (hy : ∀ m, y m ∈ Set.Icc (0 : ℝ) 1) (m : ℕ) :
    Summable (fun j => (1 / 4 : ℝ) ^ j *
      (inverseError digits y (m + 2 * j) + inverseError digits y (m + 2 * j + 1))) := by
  have hgeom : Summable (fun j : ℕ => (1 / 4 : ℝ) ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  apply Summable.of_nonneg_of_le _ _ (hgeom.mul_right 2)
  · intro j
    unfold inverseError
    positivity
  · intro j
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (1 / 4 : ℝ) ^ j)
    have h0 := inverseError_le_one hdigits hy (m + 2 * j)
    have h1 := inverseError_le_one hdigits hy (m + 2 * j + 1)
    linarith

/-- Equation (3.10), with the exact comparison sequence specified by its recurrence. -/
theorem gauss_error_infinite {digits : ℕ → ℕ} {y z : ℕ → ℝ}
    (hdigits : ∀ m, 1 ≤ digits m)
    (hy : ∀ m, y m ∈ Set.Icc (0 : ℝ) 1) (hz : ∀ m, z m ∈ Set.Icc (0 : ℝ) 1)
    (hrec : ∀ m, z m = gaussInv (digits m) (z (m + 1))) (m : ℕ) :
    |y m - z m| ≤ ∑' j : ℕ, (1 / 4 : ℝ) ^ j *
      (inverseError digits y (m + 2 * j) + inverseError digits y (m + 2 * j + 1)) := by
  have hsum := (gauss_error_weights_summable hdigits hy m).hasSum.tendsto_sum_nat
  have hpow : Tendsto (fun N : ℕ => (1 / 4 : ℝ) ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h := ge_of_tendsto' (hsum.add hpow) (gauss_error_finite_bound hdigits hy hz hrec m)
  simpa only [add_zero] using h

theorem gauss_shadowing_of_error_tendsto_zero {digits : ℕ → ℕ} {y z : ℕ → ℝ}
    (hdigits : ∀ m, 1 ≤ digits m)
    (hy : ∀ m, y m ∈ Set.Icc (0 : ℝ) 1) (hz : ∀ m, z m ∈ Set.Icc (0 : ℝ) 1)
    (hrec : ∀ m, z m = gaussInv (digits m) (z (m + 1)))
    (herror : Tendsto (inverseError digits y) atTop (𝓝 0)) :
    Tendsto (fun m => y m - z m) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp herror (eps * 3 / 16) (by positivity)
  have hsmall : ∀ k ≥ N, inverseError digits y k < eps * 3 / 16 := by
    intro k hk
    apply (le_abs_self _).trans_lt
    simpa only [Real.dist_eq, sub_zero] using hN k hk
  refine ⟨N, fun m hm => ?_⟩
  have hgeom : Summable (fun j : ℕ => (1 / 4 : ℝ) ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hbound := (gauss_error_weights_summable hdigits hy m).tsum_le_tsum
    (g := fun j => (1 / 4 : ℝ) ^ j * (eps * 3 / 8))
    (fun j => mul_le_mul_of_nonneg_left (show
      inverseError digits y (m + 2 * j) + inverseError digits y (m + 2 * j + 1) ≤
        eps * 3 / 8 by
          have h0 := hsmall (m + 2 * j) (by omega)
          have h1 := hsmall (m + 2 * j + 1) (by omega)
          linarith) (by positivity : 0 ≤ (1 / 4 : ℝ) ^ j))
    (hgeom.mul_right _)
  rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)] at hbound
  have h := gauss_error_infinite hdigits hy hz hrec m
  have hlt : |y m - z m| < eps := by norm_num at hbound; linarith
  simpa only [Real.dist_eq, sub_zero] using hlt

theorem geometric_even_error_total {eta : ℕ → ℝ}
    (hnonneg : ∀ m, 0 ≤ eta m) (heta : Summable eta) :
    Summable (fun m => ∑' j : ℕ, (1 / 4 : ℝ) ^ j * (eta (m + 2 * j) + eta (m + 2 * j + 1))) ∧
    (∑' m : ℕ, ∑' j : ℕ, (1 / 4 : ℝ) ^ j * (eta (m + 2 * j) + eta (m + 2 * j + 1))) ≤
      (8 / 3) * ∑' m, eta m := by
  let F : ℕ → ℕ → ℝ := fun j m => (1 / 4 : ℝ) ^ j * (eta (m + 2 * j) + eta (m + 2 * j + 1))
  have hshift (k : ℕ) : Summable (fun m => eta (m + k)) :=
    heta.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hshift_le (k : ℕ) : (∑' m, eta (m + k)) ≤ ∑' m, eta m :=
    tsum_comp_le_tsum_of_inj heta hnonneg (fun _ _ h => Nat.add_right_cancel h)
  have hF : ∀ j m, 0 ≤ F j m := fun j m =>
    mul_nonneg (by positivity) (add_nonneg (hnonneg _) (hnonneg _))
  have hrow (j : ℕ) : Summable (F j) := by
    simpa only [F, Nat.add_assoc] using ((hshift (2 * j)).add (hshift (2 * j + 1))).mul_left ((1 / 4 : ℝ) ^ j)
  have hrow_le (j : ℕ) : (∑' m, F j m) ≤ (1 / 4 : ℝ) ^ j * (2 * ∑' m, eta m) := by
    simp only [F, Nat.add_assoc, tsum_mul_left]
    rw [(hshift (2 * j)).tsum_add (hshift (2 * j + 1))]
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (1 / 4 : ℝ) ^ j)
    linarith [hshift_le (2 * j), hshift_le (2 * j + 1)]
  have hgeom : Summable (fun j : ℕ => (1 / 4 : ℝ) ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hrows : Summable (fun j => ∑' m, F j m) :=
    Summable.of_nonneg_of_le (fun j => tsum_nonneg (hF j)) hrow_le (hgeom.mul_right _)
  have hfull : Summable (Function.uncurry F) :=
    (summable_prod_of_nonneg (fun p => hF p.1 p.2)).mpr ⟨hrow, hrows⟩
  refine ⟨hfull.prod_symm.prod, ?_⟩
  change (∑' m, ∑' j, F j m) ≤ _
  rw [hfull.tsum_comm]
  calc
    _ ≤ ∑' j : ℕ, (1 / 4 : ℝ) ^ j * (2 * ∑' m, eta m) :=
      hrows.tsum_le_tsum hrow_le (hgeom.mul_right _)
    _ = _ := by
      rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      ring

/-- Equation (3.11), including summability of the phase discrepancy. -/
theorem gauss_error_summable {digits : ℕ → ℕ} {y z : ℕ → ℝ}
    (hdigits : ∀ m, 1 ≤ digits m)
    (hy : ∀ m, y m ∈ Set.Icc (0 : ℝ) 1) (hz : ∀ m, z m ∈ Set.Icc (0 : ℝ) 1)
    (hrec : ∀ m, z m = gaussInv (digits m) (z (m + 1)))
    (herror : Summable (inverseError digits y)) :
    Summable (fun m => |y m - z m|) ∧
      (∑' m, |y m - z m|) ≤ (8 / 3) * ∑' m, inverseError digits y m := by
  have hdom := geometric_even_error_total (fun m => abs_nonneg _) herror
  have hsum : Summable (fun m => |y m - z m|) :=
    Summable.of_nonneg_of_le (fun m => abs_nonneg _) (gauss_error_infinite hdigits hy hz hrec) hdom.1
  exact ⟨hsum, (hsum.tsum_le_tsum (gauss_error_infinite hdigits hy hz hrec) hdom.1).trans hdom.2⟩

end

end BianchiIX
