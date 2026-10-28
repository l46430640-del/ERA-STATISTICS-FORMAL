import BianchiIX.Dynamics.CoreReflectionPrefix
import Mathlib.Algebra.Order.Floor.Ring

noncomputable section

namespace BianchiIX

/-- An entrance interval with a fixed phase margin constructs all cores, with the prescribed terminal index. -/
theorem exists_core_itinerary :
    ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ K > (0 : ℝ),
      ∀ (m : ℕ) (β : ℝ) (X : CoreAngleState), 0 < β → β < 1 / 2 →
        (0 < X 1 ∧ X 1 ≤ ε / X 0) → (0 < X 2 ∧ X 2 ≤ ε / X 0) →
        ((m : ℝ) + 1 + β ≤ X 0 / 2 ∧ X 0 / 2 ≤ (m : ℝ) + 2 - β) →
        K * (X 1 + X 2) < β / 2 →
        let F := coreReturnState coreRadiusReturnTime
        let G := coreReflectionState coreRadiusReturnTime
        let Y := fun j => G^[j] X
        (∀ j ≤ m,
          2 + 3 * β / 2 < Y j 0 ∧ coreRadiusReturnValid (Y j) ∧
          ContDiffAt ℝ 1 (G^[j]) X ∧ ContDiffAt ℝ 1 (F ∘ G^[j]) X ∧
          ContDiffAt ℝ 1 (coreRadiusReturnTime ∘ G^[j]) X ∧
          (∀ i : Fin 2, 0 < F (Y j) i.succ) ∧ F (Y j) 1 + F (Y j) 2 ≤ X 1 + X 2 ∧
          |Y j 0 - (X 0 - 2 * j)| + |F (Y j) 0 - (X 0 - 2 * j)| ≤ K * (X 1 + X 2) ∧
          ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (X 1) → |v 2| ≤ Real.sqrt (X 2) →
            let d := fderiv ℝ (F ∘ G^[j]) X v
            0 < d 0 ∧ |Real.log (d 0)| ≤ K * Real.sqrt (X 1 + X 2) ∧
              ∀ i : Fin 2, |d i.succ| ≤ Real.sqrt (F (Y j) i.succ) * d 0) ∧
        (∀ j < m, 4 + 3 * β / 2 < F (Y j) 0 ∧ 0 < coreReflectionTime (Y j) ∧
          coreRadiusEntry (Y (j + 1)) = projectiveReflection
            (projectiveOriginalFlow (coreRadiusEntry (Y j)) 0 (coreReflectionTime (Y j)))) ∧
        (2 + 3 * β / 2 < F (Y m) 0 ∧ F (Y m) 0 < 4 - 3 * β / 2) ∧
        Nat.floor (X 0 / 2) = m + 1 ∧
        (3 * β / 4 < (F (Y m) 0 - 2) / 2 ∧ (F (Y m) 0 - 2) / 2 < 1 - 3 * β / 4) := by
  obtain ⟨ε, hε, hεmax, C, hC, c, hc, _, H⟩ := exists_coreReflection_prefix_bounds
  let A := C * ((1 + c / 2) / c)
  let D := C * ((1 + c / 4) / (c / 2))
  let K := 2 * A + D
  have hA : 0 < A := by dsimp [A]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hAK : A ≤ K := by dsimp [K]; linarith only [hA, hD]
  have hDK : D ≤ K := by dsimp [K]; linarith only [hA]
  have hAAK : 2 * A ≤ K := by dsimp [K]; linarith only [hD]
  refine ⟨ε, hε, hεmax, K, hK, ?_⟩
  intro m β X hβ _ hu hw hphase hsmall F G Y
  let b := X 1 + X 2
  have hb : 0 ≤ b := add_nonneg hu.1.le hw.1.le
  have horbit (j : ℕ) : Y (j + 1) = G (Y j) := Function.iterate_succ_apply' G j X
  have HP (j : ℕ) (hguard : ∀ i < j, 2 ≤ Y i 0 ∧ 31 / 8 ≤ F (Y i) 0) :=
    H j Y hu hw hguard (fun i _ => horbit i)
  have HC (j : ℕ) (hguard : ∀ i < j, 2 ≤ Y i 0 ∧ 31 / 8 ≤ F (Y i) 0) (hk : 2 ≤ Y j 0) :=
    (HP j hguard).2.2.2.2.2.2.2 hk
  have hentryError (j : ℕ) (hguard : ∀ i < j, 2 ≤ Y i 0 ∧ 31 / 8 ≤ F (Y i) 0) :
      |Y j 0 - (X 0 - 2 * j)| ≤ A * b := by
    have HJ := HP j hguard
    have hbj : 0 ≤ Y j 1 + Y j 2 := add_nonneg (HJ.1 j le_rfl 0).le (HJ.1 j le_rfl 1).le
    exact HJ.2.2.2.1.trans (mul_le_mul_of_nonneg_left (sub_le_self _ hbj) hA.le)
  have hexitError (j : ℕ) (hguard : ∀ i < j, 2 ≤ Y i 0 ∧ 31 / 8 ≤ F (Y i) 0) (hk : 2 ≤ Y j 0) :
      |F (Y j) 0 - (X 0 - 2 * j)| ≤ A * b := by
    obtain ⟨_, _, _, hpos, _, herr, _⟩ := HC j hguard hk
    exact herr.trans (mul_le_mul_of_nonneg_left
      (sub_le_self _ (add_nonneg (hpos 0).le (hpos 1).le)) hA.le)
  have hstrict {e : ℝ} (he : |e| ≤ A * b) : |e| < β / 2 :=
    (he.trans (mul_le_mul_of_nonneg_right hAK hb)).trans_lt hsmall
  have hconstruct : ∀ j ≤ m,
      (∀ i < j, 2 ≤ Y i 0 ∧ 31 / 8 ≤ F (Y i) 0) ∧ 2 + 3 * β / 2 < Y j 0 := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨fun i hi => by omega, ?_⟩
      change 2 + 3 * β / 2 < X 0
      nlinarith only [hphase.1, hβ, Nat.cast_nonneg (α := ℝ) m]
    | succ j ih =>
      intro hj
      obtain ⟨hprev, hk⟩ := ih (by omega)
      have hk2 : 2 ≤ Y j 0 := by linarith only [hk, hβ]
      have hR := abs_lt.mp (hstrict (hexitError j hprev hk2))
      have hjm : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
      have hR4 : 4 + 3 * β / 2 < F (Y j) 0 := by
        nlinarith only [hphase.1, hjm, hR.1]
      have hnextGuard : ∀ i < j + 1, 2 ≤ Y i 0 ∧ 31 / 8 ≤ F (Y i) 0 := by
        intro i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
        · exact hprev i hlt
        · exact ⟨hk2, by linarith only [hR4, hβ]⟩
      have hnext := abs_lt.mp (hstrict (hentryError (j + 1) hnextGuard))
      refine ⟨hnextGuard, ?_⟩
      push_cast at hnext
      nlinarith only [hphase.1, hjm, hnext.1]
  have hR4 (j : ℕ) (hj : j < m) : 4 + 3 * β / 2 < F (Y j) 0 := by
    obtain ⟨hguard, hk⟩ := hconstruct j hj.le
    have HR := abs_lt.mp (hstrict (hexitError j hguard (by linarith only [hk, hβ])))
    have hjm : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
    nlinarith only [hphase.1, hjm, HR.1]
  have hterminal : 2 + 3 * β / 2 < F (Y m) 0 ∧ F (Y m) 0 < 4 - 3 * β / 2 := by
    obtain ⟨hguard, hk⟩ := hconstruct m le_rfl
    have HR := abs_lt.mp (hstrict (hexitError m hguard (by linarith only [hk, hβ])))
    constructor
    · nlinarith only [hphase.1, HR.1]
    · nlinarith only [hphase.2, HR.2]
  refine ⟨?_, ?_, hterminal, ?_, ?_⟩
  · intro j hj
    obtain ⟨hguard, hk⟩ := hconstruct j hj
    obtain ⟨hvalid, hreg, ht, hpos, hbudget, _, hdiff⟩ :=
      HC j hguard (by linarith only [hk, hβ])
    refine ⟨hk, hvalid, (HP j hguard).2.2.2.2.2.1.1, hreg, ht, hpos, hbudget, ?_, ?_⟩
    · calc
        _ ≤ A * b + A * b := add_le_add (hentryError j hguard)
          (hexitError j hguard (by linarith only [hk, hβ]))
        _ = (2 * A) * b := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hAAK hb
    · intro v hv0 hv1 hv2 d
      obtain ⟨hp, hl, hcone⟩ := hdiff v hv0 hv1 hv2
      refine ⟨hp, hl.trans ?_, hcone⟩
      calc
        _ ≤ D * Real.sqrt b := mul_le_mul_of_nonneg_left (sub_le_self _ (Real.sqrt_nonneg _)) hD.le
        _ ≤ _ := mul_le_mul_of_nonneg_right hDK (Real.sqrt_nonneg _)
  · intro j hj
    exact ⟨hR4 j hj, (HP m (hconstruct m le_rfl).1).2.2.2.2.2.1.2 j hj⟩
  · have hX : 0 ≤ X 0 / 2 := by nlinarith only [hphase.1, hβ, Nat.cast_nonneg (α := ℝ) m]
    apply (Nat.floor_eq_iff hX).mpr
    push_cast
    constructor
    · linarith only [hphase.1, hβ]
    · linarith only [hphase.2, hβ]
  · constructor <;> linarith only [hterminal.1, hterminal.2]

end BianchiIX
