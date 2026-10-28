import BianchiIX.Statistics.GaussInverse
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat

/-! Infinite positive digit strings, their real values, and measurable coding. -/

namespace BianchiIX

noncomputable section

open Filter Set
open scoped Topology

instance : MeasurableSpace ℕ+ := inferInstanceAs (MeasurableSpace {n : ℕ // 0 < n})
instance : MeasurableSingletonClass ℕ+ :=
  inferInstanceAs (MeasurableSingletonClass {n : ℕ // 0 < n})

def shiftDigits (a : ℕ → ℕ+) (k : ℕ) : ℕ → ℕ+ := fun i => a (k + i)

@[simp] theorem shiftDigits_zero (a : ℕ → ℕ+) : shiftDigits a 0 = a := by
  funext i
  simp only [shiftDigits, Nat.zero_add]

def digitPrefix (a : ℕ → ℕ+) (n : ℕ) : List ℕ :=
  (List.range n).map (fun i => (a i : ℕ))

def gaussApprox (a : ℕ → ℕ+) (n : ℕ) : ℝ := gaussWord (digitPrefix a n) 0

theorem shiftDigits_add (a : ℕ → ℕ+) (m n : ℕ) :
    shiftDigits (shiftDigits a m) n = shiftDigits a (m + n) := by
  funext i
  simp only [shiftDigits, Nat.add_assoc]

theorem digitPrefix_positive (a : ℕ → ℕ+) (n : ℕ) :
    ∀ k ∈ digitPrefix a n, 1 ≤ k := by
  intro k hk
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hk
  exact Nat.succ_le_of_lt (a i).pos

theorem digitPrefix_length (a : ℕ → ℕ+) (n : ℕ) : (digitPrefix a n).length = n := by
  simp [digitPrefix]

theorem digitPrefix_add (a : ℕ → ℕ+) (n k : ℕ) :
    digitPrefix a (n + k) = digitPrefix a n ++ digitPrefix (shiftDigits a n) k := by
  simp [digitPrefix, List.range_add, List.map_map, Function.comp_def, shiftDigits]

theorem digitPrefix_succ (a : ℕ → ℕ+) (n : ℕ) :
    digitPrefix a (n + 1) = (a 0 : ℕ) :: digitPrefix (shiftDigits a 1) n := by
  simp [digitPrefix, List.range_succ_eq_map, List.map_map, Function.comp_def, shiftDigits,
    Nat.add_comm]

theorem gaussWord_append (w v : List ℕ) (x : ℝ) :
    gaussWord (w ++ v) x = gaussWord w (gaussWord v x) := by
  induction w with
  | nil => rfl
  | cons a w ih => simpa only [List.cons_append, gaussWord] using congrArg (gaussInv a) ih

theorem gaussWord_mem_unit (w : List ℕ) (hw : ∀ a ∈ w, 1 ≤ a)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : gaussWord w x ∈ Icc (0 : ℝ) 1 := by
  induction w with
  | nil => exact hx
  | cons a w ih =>
    have ha : (1 : ℝ) ≤ a := by exact_mod_cast hw a (by simp)
    have ht := ih (fun b hb => hw b (by simp [hb]))
    exact ⟨(gaussInv_pos ha ht.1).le, gaussInv_le_one ha ht.1⟩

theorem gaussApprox_mem_unit (a : ℕ → ℕ+) (n : ℕ) : gaussApprox a n ∈ Icc (0 : ℝ) 1 :=
  gaussWord_mem_unit _ (digitPrefix_positive a n) ⟨le_rfl, zero_le_one⟩

theorem gaussApprox_add (a : ℕ → ℕ+) (n k : ℕ) :
    gaussApprox a (n + k) = gaussWord (digitPrefix a n) (gaussApprox (shiftDigits a n) k) := by
  simp only [gaussApprox, digitPrefix_add, gaussWord_append]

theorem gaussApprox_succ (a : ℕ → ℕ+) (n : ℕ) :
    gaussApprox a (n + 1) = gaussInv (a 0) (gaussApprox (shiftDigits a 1) n) := by
  simp only [gaussApprox, digitPrefix_succ, gaussWord]

theorem gaussApprox_distance (a : ℕ → ℕ+) {n k : ℕ} (hnk : n ≤ k) :
    |gaussApprox a n - gaussApprox a k| ≤ (1 / 4 : ℝ) ^ (n / 2) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnk
  rw [gaussApprox_add]
  simpa only [gaussApprox, digitPrefix_length] using
    gaussWord_diameter (digitPrefix a n) (digitPrefix_positive a n)
      (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩) (gaussApprox_mem_unit (shiftDigits a n) j)

theorem gauss_diameter_tendsto_zero :
    Tendsto (fun n : ℕ => (1 / 4 : ℝ) ^ (n / 2)) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun n : ℕ => n / 2) atTop atTop := by
    refine tendsto_atTop.mpr fun k => eventually_atTop.mpr ⟨2 * k, ?_⟩
    intro n hn
    omega
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp hdiv

theorem gaussApprox_cauchy (a : ℕ → ℕ+) : CauchySeq (gaussApprox a) := by
  apply cauchySeq_of_le_tendsto_0' (fun n => (1 / 4 : ℝ) ^ (n / 2))
  · intro n k hnk
    simpa only [Real.dist_eq] using gaussApprox_distance a hnk
  · exact gauss_diameter_tendsto_zero

def gaussCode (a : ℕ → ℕ+) : ℝ :=
  (cauchySeq_tendsto_of_complete (gaussApprox_cauchy a)).choose

theorem gaussCode_tendsto (a : ℕ → ℕ+) : Tendsto (gaussApprox a) atTop (𝓝 (gaussCode a)) :=
  (cauchySeq_tendsto_of_complete (gaussApprox_cauchy a)).choose_spec

theorem gaussCode_mem_unit (a : ℕ → ℕ+) : gaussCode a ∈ Icc (0 : ℝ) 1 :=
  isClosed_Icc.mem_of_tendsto (gaussCode_tendsto a) (Eventually.of_forall (gaussApprox_mem_unit a))

theorem gaussCode_recurrence (a : ℕ → ℕ+) :
    gaussCode a = gaussInv (a 0) (gaussCode (shiftDigits a 1)) := by
  have ha : (1 : ℝ) ≤ a 0 := by exact_mod_cast Nat.succ_le_of_lt (a 0).pos
  have h := (hasDerivAt_gaussInv ha (gaussCode_mem_unit (shiftDigits a 1)).1).continuousAt.tendsto.comp
    (gaussCode_tendsto (shiftDigits a 1))
  apply tendsto_nhds_unique ((gaussCode_tendsto a).comp (tendsto_add_atTop_nat 1))
  simpa only [Function.comp_def, gaussApprox_succ] using h

theorem gaussCode_pos (a : ℕ → ℕ+) : 0 < gaussCode a := by
  rw [gaussCode_recurrence a]
  apply gaussInv_pos _ (gaussCode_mem_unit (shiftDigits a 1)).1
  exact_mod_cast Nat.succ_le_of_lt (a 0).pos

theorem gaussCode_lt_one (a : ℕ → ℕ+) : gaussCode a < 1 := by
  rw [gaussCode_recurrence a]
  have ha : (1 : ℝ) ≤ a 0 := by exact_mod_cast Nat.succ_le_of_lt (a 0).pos
  have ht := gaussCode_pos (shiftDigits a 1)
  unfold gaussInv
  exact (div_lt_one (by positivity)).mpr (by linarith)

theorem gaussCode_prefix (a : ℕ → ℕ+) (n : ℕ) :
    gaussCode a = gaussWord (digitPrefix a n) (gaussCode (shiftDigits a n)) := by
  induction n generalizing a with
  | zero => simp [digitPrefix, gaussWord]
  | succ n ih =>
    rw [gaussCode_recurrence a, digitPrefix_succ]
    simpa only [gaussWord, shiftDigits_add, Nat.one_add] using
      congrArg (gaussInv (a 0)) (ih (shiftDigits a 1))

theorem gaussCode_prefix_distance {a b : ℕ → ℕ+} {n : ℕ}
    (h : digitPrefix a n = digitPrefix b n) :
    |gaussCode a - gaussCode b| ≤ (1 / 4 : ℝ) ^ (n / 2) := by
  rw [gaussCode_prefix a n, gaussCode_prefix b n, ← h]
  simpa only [digitPrefix_length] using gaussWord_diameter _ (digitPrefix_positive a n)
    (gaussCode_mem_unit (shiftDigits a n)) (gaussCode_mem_unit (shiftDigits b n))

def gaussMap (x : ℝ) : ℝ := Int.fract (1 / x)

theorem gaussCode_reciprocal (a : ℕ → ℕ+) :
    1 / gaussCode a = (a 0 : ℝ) + gaussCode (shiftDigits a 1) := by
  rw [gaussCode_recurrence a]
  simp only [gaussInv, one_div_one_div]

theorem gaussCode_digit (a : ℕ → ℕ+) : ⌊1 / gaussCode a⌋ = (a 0 : ℤ) := by
  apply Int.floor_eq_iff.mpr
  rw [gaussCode_reciprocal]
  change ((a 0 : ℕ) : ℝ) ≤ ((a 0 : ℕ) : ℝ) + gaussCode (shiftDigits a 1) ∧
    ((a 0 : ℕ) : ℝ) + gaussCode (shiftDigits a 1) < ((a 0 : ℕ) : ℝ) + 1
  exact ⟨by linarith [gaussCode_pos (shiftDigits a 1)],
    by linarith [gaussCode_lt_one (shiftDigits a 1)]⟩

theorem gaussMap_code (a : ℕ → ℕ+) : gaussMap (gaussCode a) = gaussCode (shiftDigits a 1) := by
  unfold gaussMap Int.fract
  rw [gaussCode_digit, gaussCode_reciprocal]
  push_cast
  ring

theorem gaussMap_iterate_code (a : ℕ → ℕ+) (n : ℕ) :
    gaussMap^[n] (gaussCode a) = gaussCode (shiftDigits a n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, gaussMap_code, shiftDigits_add]

theorem gaussCode_injective : Function.Injective gaussCode := by
  intro a b hab
  funext n
  have ha := gaussCode_digit (shiftDigits a n)
  have hb := gaussCode_digit (shiftDigits b n)
  rw [← gaussMap_iterate_code a n, hab, gaussMap_iterate_code b n] at ha
  have h := ha.symm.trans hb
  simp only [shiftDigits, Nat.add_zero] at h
  exact_mod_cast h

private theorem rat_gauss_den_lt {q : ℚ} (hq0 : 0 < q) (hq1 : q < 1) :
    (Int.fract q⁻¹).den < q.den := by
  rw [Rat.den_intFract, Rat.den_inv_of_ne_zero hq0.ne']
  have hnum0 : 0 ≤ q.num := (Rat.num_nonneg.mpr hq0.le)
  have hden : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
  have hnum : (q.num : ℚ) < q.den := by
    apply (div_lt_one hden).mp
    simpa only [Rat.num_div_den] using hq1
  have hnum' : q.num < (q.den : ℤ) := by exact_mod_cast hnum
  have habs := Int.natAbs_of_nonneg hnum0
  omega

private theorem rat_gauss_cast (q : ℚ) :
    ((Int.fract q⁻¹ : ℚ) : ℝ) = gaussMap (q : ℝ) := by
  simp only [Rat.cast_fract, Rat.cast_inv, gaussMap, one_div]

theorem gaussCode_irrational (a : ℕ → ℕ+) : Irrational (gaussCode a) := by
  rintro ⟨q, hq⟩
  let f : ℚ → ℚ := fun q => Int.fract q⁻¹
  have hcast (n : ℕ) : ((f^[n] q : ℚ) : ℝ) = gaussCode (shiftDigits a n) := by
    induction n with
    | zero => simpa using hq
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      change ((Int.fract (f^[n] q)⁻¹ : ℚ) : ℝ) = _
      rw [rat_gauss_cast, ih, gaussMap_code, shiftDigits_add]
  have hdec : ∀ n, (f^[n + 1] q).den < (f^[n] q).den := by
    intro n
    rw [Function.iterate_succ_apply']
    apply rat_gauss_den_lt
    · have h := gaussCode_pos (shiftDigits a n)
      rw [← hcast n] at h
      exact_mod_cast h
    · have h := gaussCode_lt_one (shiftDigits a n)
      rw [← hcast n] at h
      exact_mod_cast h
  exact not_strictAnti_of_wellFoundedLT (fun n => (f^[n] q).den)
    (strictAnti_nat_of_succ_lt hdec)

theorem measurable_gaussApprox (n : ℕ) : Measurable (fun a : ℕ → ℕ+ => gaussApprox a n) := by
  induction n with
  | zero => simp [gaussApprox, digitPrefix, gaussWord]
  | succ n ih =>
    have hshift : Measurable (fun a : ℕ → ℕ+ => shiftDigits a 1) :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply (1 + i))
    have hcast : Measurable (fun k : ℕ+ => (k : ℝ)) := measurable_of_countable _
    have h := (measurable_const (a := (1 : ℝ))).div
      ((hcast.comp (measurable_pi_apply 0)).add (ih.comp hshift))
    simpa only [gaussApprox_succ, gaussInv, Pi.div_def, Pi.add_def,
      Function.comp_def] using h

theorem measurable_gaussCode : Measurable gaussCode :=
  measurable_of_tendsto_metrizable measurable_gaussApprox
    (tendsto_pi_nhds.mpr gaussCode_tendsto)

theorem measurable_gaussCode_of_digits {X : Type*} [MeasurableSpace X]
    {a : ℕ → X → ℕ+} (ha : ∀ n, Measurable (a n)) :
    Measurable (fun x => gaussCode (fun n => a n x)) :=
  measurable_gaussCode.comp (measurable_pi_lambda _ ha)

theorem gaussCode_shift_recurrence (a : ℕ → ℕ+) (m : ℕ) :
    gaussCode (shiftDigits a m) =
      gaussInv (a m) (gaussCode (shiftDigits a (m + 1))) := by
  simpa only [shiftDigits_add, shiftDigits, Nat.add_zero] using
    gaussCode_recurrence (shiftDigits a m)

/-- The comparison orbit is now the explicitly constructed code of the prescribed digits. -/
theorem gaussCode_error_bound (a : ℕ → ℕ+) {y : ℕ → ℝ}
    (hy : ∀ m, y m ∈ Icc (0 : ℝ) 1) (m : ℕ) :
    |y m - gaussCode (shiftDigits a m)| ≤ ∑' j : ℕ, (1 / 4 : ℝ) ^ j *
      (inverseError (fun k => (a k : ℕ)) y (m + 2 * j) +
        inverseError (fun k => (a k : ℕ)) y (m + 2 * j + 1)) :=
  gauss_error_infinite (fun k => Nat.succ_le_of_lt (a k).pos) hy
    (fun k => gaussCode_mem_unit (shiftDigits a k)) (gaussCode_shift_recurrence a) m

theorem gaussCode_shadowing (a : ℕ → ℕ+) {y : ℕ → ℝ}
    (hy : ∀ m, y m ∈ Icc (0 : ℝ) 1)
    (herror : Tendsto (inverseError (fun k => (a k : ℕ)) y) atTop (𝓝 0)) :
    Tendsto (fun m => y m - gaussMap^[m] (gaussCode a)) atTop (𝓝 0) := by
  simp only [gaussMap_iterate_code]
  exact gauss_shadowing_of_error_tendsto_zero
    (fun k => Nat.succ_le_of_lt (a k).pos) hy
    (fun k => gaussCode_mem_unit (shiftDigits a k)) (gaussCode_shift_recurrence a) herror

theorem gaussCode_error_summable (a : ℕ → ℕ+) {y : ℕ → ℝ}
    (hy : ∀ m, y m ∈ Icc (0 : ℝ) 1)
    (herror : Summable (inverseError (fun k => (a k : ℕ)) y)) :
    Summable (fun m => |y m - gaussMap^[m] (gaussCode a)|) ∧
      (∑' m, |y m - gaussMap^[m] (gaussCode a)|) ≤
        (8 / 3) * ∑' m, inverseError (fun k => (a k : ℕ)) y m := by
  simp only [gaussMap_iterate_code]
  exact gauss_error_summable (fun k => Nat.succ_le_of_lt (a k).pos) hy
    (fun k => gaussCode_mem_unit (shiftDigits a k)) (gaussCode_shift_recurrence a) herror

end

end BianchiIX
