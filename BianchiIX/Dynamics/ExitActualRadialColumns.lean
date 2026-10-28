import BianchiIX.Dynamics.ExitActualMultipliers
import BianchiIX.Dynamics.ExitClockRadialColumn

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The two radial columns of D.10 follow by direct integration of the actual first variation. -/
theorem exists_terminal_exitClock_radial_columns {η : ℝ} (hη : 0 < η ∧ η < 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let S := exitTailLength η α J
      coreTailValid h Y ∧ ∃ I : Set ℝ, IsOpen I ∧ Convex ℝ I ∧ Icc 0 (coreTailTime h Y) ⊆ I ∧
        (∀ t ∈ I, exitEntryRegular Y t) ∧ exitClockFlow I (Y, 0) = Y ∧
        ((fun Z => toExitTailState (coreTailState h Z)) =ᶠ[𝓝 Y] (fun Z => exitClockFlow I (Z, S))) ∧
        ∀ s ∈ Icc 0 S, ContDiffAt ℝ 2 (exitClockFlow I) (Y, s) ∧
          ‖fderiv ℝ (fun Z => exitClockFlow I (Z, s)) Y‖ ≤ C ∧
          ((7 / 4 ≤ exitClockFlow I (Y, s) 0 ∧ exitClockFlow I (Y, s) 0 ≤ 17 / 4) ∧
            |exitClockFlow I (Y, s) 1| ≤ 1 / 100 ∧ |exitClockFlow I (Y, s) 2| ≤ 1 / 100) ∧
          |exitClockFlow I (Y, s) 1| + |exitClockFlow I (Y, s) 2| ≤ C * b ∧
          |fderiv ℝ (fun Z => exitClockFlow I (Z, s)) Y (Pi.single 0 1) 0 - 1| ≤
            C * (|u| + b ^ 2 * (1 + s) ^ 2) ∧
          |fderiv ℝ (fun Z => exitClockFlow I (Z, s)) Y (Pi.single 2 1) 0| ≤ C * b * (1 + s) := by
  obtain ⟨K, hK, εm, hεm, HM⟩ := exists_terminal_exitClock_multiplier_bounds hη hJ
  obtain ⟨A, _, εr, hεr, HR⟩ := exists_exitTail_scale_bounds ⟨hη.1, hη.2.le⟩ hJ
  let Q := 1 + Real.log (1 / η) + Real.exp (-1)
  have hlog : 0 ≤ Real.log (1 / η) := Real.log_nonneg ((le_div_iff₀ hη.1).mpr (by linarith only [hη.2]))
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  let ε := min εm (min εr (1 / Q))
  let C := 1024 * K ^ 3
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  have hKK : K ≤ K ^ 2 := by nlinarith only [hK]
  have hKKK : K ^ 2 ≤ K ^ 3 := by nlinarith only [mul_nonneg (sq_nonneg K) (sub_nonneg.mpr hK)]
  have hKC : K ≤ C := by dsimp only [C]; nlinarith only [hK, hKK, hKKK]
  refine ⟨C, hK.trans hKC, ε, lt_min hεm (lt_min hεr (one_div_pos.mpr hQ)), ?_⟩
  intro α b u w hα hb hsmall hw Y h S
  have hm := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left εm _) (pow_nonneg hα.1.le J))
  have hr := hsmall.trans (mul_le_mul_of_nonneg_right ((min_le_right εm _).trans (min_le_left εr _))
    (pow_nonneg hα.1.le J))
  have hε0 : 0 ≤ ε := (lt_min hεm (lt_min hεr (one_div_pos.mpr hQ))).le
  have hbudget : b * (1 + S) ≤ 1 := by
    have HB := (exitTail_smallness_budgets ⟨hη.1, hη.2.le⟩ hα hε0 hJ hsmall).1
    have HQ : ε * Q ≤ 1 := (le_div_iff₀ hQ).mp ((min_le_right εm _).trans (min_le_right εr _))
    exact HB.trans HQ
  obtain ⟨hvalid, I, hIo, hI, hcover, U, hUo, hYU, Htube, hinit, hend, HF⟩ := HM α b u w hα hb hm hw
  change coreTailValid h Y at hvalid
  have hT : 0 ≤ coreTailTime h Y := hvalid.1.1.1.le
  have hS : 0 ≤ S := exitTailLength_nonneg ⟨hη.1, hη.2.le⟩ hα J
  have hclock : exitEntryClock (Y, coreTailTime h Y) = S := by
    change -Real.log (coreTailState h Y 2) = S
    rw [coreTailState_active hvalid]
    change -Real.log (η * α ^ J) = exitTailLength η α J
    rw [← exp_neg_exitTailLength hη.1 hα.1 J, Real.log_exp, neg_neg]
  let β : ℝ → ExitTailState := fun s => exitClockFlow I (Y, s)
  have hβ0 : β 0 = Y := hinit
  have hR : β 0 0 = 2 + 2 * α := by rw [hβ0]; rfl
  have hwall : |β 0 1| + |β 0 2| ≤ b := by rw [hβ0]; exact hw
  have hβ (s : ℝ) (hs : s ∈ Icc 0 S) : HasDerivAt β (exitTailField (Real.exp (-s)) (β s)) s :=
    (exitClockFlow_on_interval hIo hI hUo hYU Htube hT hcover (hclock ▸ hs)).2.1
  have HP := HR α b S β hα hb hr ⟨hS, le_rfl⟩ hR hwall hβ
  have hreg (s : ℝ) (hs : s ∈ Icc 0 S) :=
    And.intro (HP s hs).1.1 (And.intro (HP s hs).1.2.1 (HP s hs).1.2.2.1)
  have hmult (s : ℝ) (hs : s ∈ Icc 0 S) (i : Fin 2) :
      Real.exp (exitClockLogMultiplier I i Y s) ≤ K ∧
      ‖fderiv ℝ (fun Z => exitClockLogMultiplier I i Z s) Y‖ ≤ K * s := by
    refine ⟨((HF s hs).2.2.1 i).2.2.2.1, ?_⟩
    have Hsum : ‖fderiv ℝ (fun Z => exitClockLogMultiplier I 0 Z s) Y‖ +
        ‖fderiv ℝ (fun Z => exitClockLogMultiplier I 1 Z s) Y‖ ≤ K * s := (HF s hs).2.2.2
    fin_cases i
    · exact (le_add_of_nonneg_right (norm_nonneg _)).trans Hsum
    · exact (le_add_of_nonneg_left (norm_nonneg _)).trans Hsum
  refine ⟨hvalid, I, hIo, hI, hcover, Htube Y hYU, hinit, hend, ?_⟩
  intro s hs
  have hsub : Icc 0 s ⊆ Icc 0 S := fun _ ht => ⟨ht.1, ht.2.trans hs.2⟩
  have Hcol (v : ExitTailState) (hv : v 1 = 0) := exitClock_radial_column_bound hIo hI hUo hYU Htube hT hcover
    (hclock ▸ hs) hK (show |Y 1| + |Y 2| ≤ b from hw) (fun r hr => hreg r (hsub hr))
    (fun r hr => (HF r (hsub hr)).2.1) (fun r hr => hmult r (hsub hr)) v hv
  have hKb : |β s 1| + |β s 2| ≤ K * b := by
    have hamp (i : Fin 2) : |β s i.succ| ≤ K * |Y i.succ| := by
      have Hval : β s i.succ = Y i.succ * Real.exp (exitClockLogMultiplier I i Y s) := ((HF s hs).2.2.1 i).1
      rw [Hval, abs_mul, abs_of_pos (Real.exp_pos _)]
      nlinarith only [mul_le_mul_of_nonneg_left (hmult s hs i).1 (abs_nonneg (Y i.succ))]
    have H0 : |β s 1| ≤ K * |u| := hamp 0
    have H1 : |β s 2| ≤ K * |w| := hamp 1
    nlinarith only [H0, H1, mul_le_mul_of_nonneg_left hw hK0]
  refine ⟨(HF s hs).1, (HF s hs).2.1.trans hKC, hreg s hs,
    hKb.trans (mul_le_mul_of_nonneg_right hKC hb.le), ?_, ?_⟩
  · have H0 := Hcol (Pi.single 0 1) (by simp)
    change |fderiv ℝ (fun Z => exitClockFlow I (Z, s)) Y (Pi.single 0 1) 0 - (Pi.single 0 1 : ExitTailState) 0| ≤
      512 * K ^ 3 * ((2 * |u| + b ^ 2 * s * (1 + s)) * ‖(Pi.single 0 1 : ExitTailState)‖ +
        b * |(Pi.single 0 1 : ExitTailState) 2| * s) at H0
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (2 : Fin 3) ≠ 0),
      abs_zero, mul_zero, zero_mul, add_zero, Pi.norm_single, norm_one, mul_one] at H0
    apply H0.trans
    change _ ≤ 1024 * K ^ 3 * (|u| + b ^ 2 * (1 + s) ^ 2)
    have HE : s * (1 + s) ≤ (1 + s) ^ 2 := by nlinarith only [hs.1]
    nlinarith only [mul_le_mul_of_nonneg_left HE (by positivity : 0 ≤ K ^ 3 * b ^ 2),
      mul_nonneg (by positivity : 0 ≤ K ^ 3) (abs_nonneg u),
      mul_nonneg (by positivity : 0 ≤ K ^ 3 * b ^ 2) (sq_nonneg (1 + s))]
  · have H2 := Hcol (Pi.single 2 1) (by simp)
    change |fderiv ℝ (fun Z => exitClockFlow I (Z, s)) Y (Pi.single 2 1) 0 - (Pi.single 2 1 : ExitTailState) 0| ≤
      512 * K ^ 3 * ((2 * |u| + b ^ 2 * s * (1 + s)) * ‖(Pi.single 2 1 : ExitTailState)‖ +
        b * |(Pi.single 2 1 : ExitTailState) 2| * s) at H2
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (0 : Fin 3) ≠ 2),
      sub_zero, abs_one, mul_one, Pi.norm_single, norm_one] at H2
    have Hbs : b * (1 + s) ≤ 1 := (mul_le_mul_of_nonneg_left (add_le_add_right hs.2 1) hb.le).trans hbudget
    have Hu : |u| ≤ b := by linarith only [hw, abs_nonneg w]
    apply H2.trans
    change _ ≤ 1024 * K ^ 3 * b * (1 + s)
    have hs0 : 0 ≤ s := hs.1
    nlinarith only [mul_le_mul_of_nonneg_left Hbs (by positivity : 0 ≤ K ^ 3 * b * s),
      mul_le_mul_of_nonneg_left Hu (by positivity : 0 ≤ K ^ 3)]

end BianchiIX
