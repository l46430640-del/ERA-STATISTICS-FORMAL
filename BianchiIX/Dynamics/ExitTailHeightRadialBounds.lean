import BianchiIX.Dynamics.ExitActualRadialColumns
import BianchiIX.Dynamics.CoreTailHeightOrder

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

/-- The radial cancellation and wall amplitudes hold for every higher endpoint of one finite tail. -/
theorem exists_terminal_exitReturn_radial_bounds_uniform {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ < 1)
    {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η < 1 → (0 < α ∧ α ≤ 1) → 0 < b →
      b ≤ ε * α ^ J → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let F := fun Z => toExitTailState (coreTailState h Z)
      coreTailValid h Y ∧ ContDiffAt ℝ 2 F Y ∧ ‖fderiv ℝ F Y‖ ≤ C ∧
        |fderiv ℝ F Y (Pi.single 0 1) 0 - 1| ≤ C * (|u| + b ^ 2 * (1 + exitTailLength η α J) ^ 2) ∧
        ∀ i : Fin 2, |F Y i.succ| ≤ C * |Y i.succ| ∧
          |fderiv ℝ F Y (Pi.single 0 1) i.succ| ≤ C * |Y i.succ| / α := by
  obtain ⟨K, hK, εm, hεm, HM⟩ := exists_terminal_exitClock_multiplier_bounds hη₀ hJ
  obtain ⟨_, _, εr, hεr, HR⟩ := exists_exitTail_scale_bounds ⟨hη₀.1, hη₀.2.le⟩ hJ
  let L := Real.log (1 / η₀) + J * Real.exp (-1)
  have hL : 0 ≤ L := add_nonneg
    (Real.log_nonneg ((le_div_iff₀ hη₀.1).mpr (by linarith only [hη₀.2])))
    (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)
  have hK0 : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 1).trans hK
  let C := 1024 * K ^ 3 + K ^ 2 * (L + 1)
  have hradC : 1024 * K ^ 3 ≤ C := le_add_of_nonneg_right (by positivity)
  have hKC : K ≤ C := by
    have H1 : K ≤ K ^ 2 := by nlinarith only [hK]
    have H2 : K ^ 2 ≤ K ^ 3 := by nlinarith only [mul_nonneg (sq_nonneg K) (sub_nonneg.mpr hK)]
    nlinarith only [H1, H2, hradC, hK]
  have hwallC : K ^ 2 * L ≤ C := by
    dsimp only [C]
    nlinarith only [sq_nonneg K, (by positivity : 0 ≤ K ^ 3)]
  refine ⟨C, hK.trans hKC, min εm εr, lt_min hεm hεr, ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum Y h F
  have hη : 0 < η := hη₀.1.trans_le hηlo
  have hsm := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left εm εr) (pow_nonneg hα.1.le J))
  have hsr := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_right εm εr) (pow_nonneg hα.1.le J))
  obtain ⟨HV₀, I, hIo, hI, hcover, U, hUo, hYU, Htube, hinit, _, HF⟩ := HM α b u w hα hb hsm hsum
  have hh1 : h < 1 := by
    have H := mul_le_mul_of_nonneg_left (pow_le_one₀ hα.1.le hα.2 (n := J)) hη.le
    exact H.trans_lt (by simpa only [mul_one] using hηhi)
  obtain ⟨HV, htime⟩ := coreTailValid_of_height_le HV₀
    (mul_le_mul_of_nonneg_right hηlo (pow_nonneg hα.1.le J)) hh1
  let S := exitTailLength η α J
  let S₀ := exitTailLength η₀ α J
  have hS : 0 ≤ S := exitTailLength_nonneg ⟨hη, hηhi.le⟩ hα J
  have hS₀ : 0 ≤ S₀ := exitTailLength_nonneg ⟨hη₀.1, hη₀.2.le⟩ hα J
  have hSS₀ : S ≤ S₀ := by
    have H := mul_le_mul_of_nonneg_right hηlo (pow_nonneg hα.1.le J)
    rw [← exp_neg_exitTailLength hη₀.1 hα.1 J, ← exp_neg_exitTailLength hη hα.1 J] at H
    exact neg_le_neg_iff.mp (Real.exp_le_exp.mp H)
  have hs : S ∈ Icc 0 S₀ := ⟨hS, hSS₀⟩
  have hsub : Icc 0 S ⊆ Icc 0 S₀ := fun _ ht => ⟨ht.1, ht.2.trans hSS₀⟩
  have hT : 0 ≤ coreTailTime (η₀ * α ^ J) Y := HV₀.1.1.1.le
  have hclock : exitEntryClock (Y, coreTailTime (η₀ * α ^ J) Y) = S₀ := by
    change -Real.log (coreTailState (η₀ * α ^ J) Y 2) = S₀
    rw [coreTailState_active HV₀, ← exp_neg_exitTailLength hη₀.1 hα.1 J, Real.log_exp, neg_neg]
  have heh : -Real.log h = S := by
    change -Real.log (η * α ^ J) = S
    rw [← exp_neg_exitTailLength hη hα.1 J, Real.log_exp, neg_neg]
  have hend := coreTailState_eventuallyEq_exitClockFlow hIo hI hUo hYU Htube HV
    (hcover ⟨HV.1.1.1.le, htime⟩)
  rw [heh] at hend
  let β : ℝ → ExitTailState := fun s => exitClockFlow I (Y, s)
  have hβ0 : β 0 = Y := hinit
  have hR : β 0 0 = 2 + 2 * α := by rw [hβ0]; rfl
  have hwall : |β 0 1| + |β 0 2| ≤ b := by rw [hβ0]; exact hsum
  have hβ (s : ℝ) (hs : s ∈ Icc 0 S₀) : HasDerivAt β (exitTailField (Real.exp (-s)) (β s)) s :=
    (exitClockFlow_on_interval hIo hI hUo hYU Htube hT hcover (hclock ▸ hs)).2.1
  have HP := HR α b S₀ β hα hb hsr ⟨hS₀, le_rfl⟩ hR hwall hβ
  have hreg (s : ℝ) (hs : s ∈ Icc 0 S₀) :=
    And.intro (HP s hs).1.1 (And.intro (HP s hs).1.2.1 (HP s hs).1.2.2.1)
  have hmult (s : ℝ) (hs : s ∈ Icc 0 S₀) (i : Fin 2) :
      Real.exp (exitClockLogMultiplier I i Y s) ≤ K ∧
        ‖fderiv ℝ (fun Z => exitClockLogMultiplier I i Z s) Y‖ ≤ K * s := by
    refine ⟨((HF s hs).2.2.1 i).2.2.2.1, ?_⟩
    have Hsum : ‖fderiv ℝ (fun Z => exitClockLogMultiplier I 0 Z s) Y‖ +
      ‖fderiv ℝ (fun Z => exitClockLogMultiplier I 1 Z s) Y‖ ≤ K * s := (HF s hs).2.2.2
    fin_cases i
    · exact (le_add_of_nonneg_right (norm_nonneg _)).trans Hsum
    · exact (le_add_of_nonneg_left (norm_nonneg _)).trans Hsum
  have Hslice : ContDiffAt ℝ 2 (fun Z => exitClockFlow I (Z, S)) Y :=
    ContDiffAt.comp (g := exitClockFlow I) (f := fun Z : ExitTailState => (Z, S)) Y
      (HF S hs).1 (contDiffAt_id.prodMk (contDiffAt_const (c := S)))
  have Hder : fderiv ℝ F Y = fderiv ℝ (fun Z => exitClockFlow I (Z, S)) Y := hend.fderiv_eq
  have Hpoint : F Y = exitClockFlow I (Y, S) := hend.self_of_nhds
  refine ⟨HV, Hslice.congr_of_eventuallyEq hend, ?_, ?_, ?_⟩
  · rw [Hder]
    exact (HF S hs).2.1.trans hKC
  · rw [Hder]
    have H := exitClock_radial_column_bound hIo hI hUo hYU Htube hT hcover (hclock ▸ hs) hK
      (show |Y 1| + |Y 2| ≤ b from hsum) (fun r hr => hreg r (hsub hr))
      (fun r hr => (HF r (hsub hr)).2.1) (fun r hr => hmult r (hsub hr))
      (Pi.single 0 1) (by simp)
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (2 : Fin 3) ≠ 0),
      abs_zero, mul_zero, zero_mul, add_zero, Pi.norm_single, norm_one, mul_one] at H
    change _ ≤ 512 * K ^ 3 * (2 * |u| + b ^ 2 * S * (1 + S)) at H
    refine H.trans ((show 512 * K ^ 3 * (2 * |u| + b ^ 2 * S * (1 + S)) ≤
      1024 * K ^ 3 * (|u| + b ^ 2 * (1 + S) ^ 2) from ?_).trans
      (mul_le_mul_of_nonneg_right hradC (by positivity)))
    have HE : S * (1 + S) ≤ (1 + S) ^ 2 := by nlinarith only [hS]
    nlinarith only [mul_le_mul_of_nonneg_left HE (by positivity : 0 ≤ K ^ 3 * b ^ 2),
      (by positivity : 0 ≤ K ^ 3 * b ^ 2 * (1 + S) ^ 2)]
  · intro i
    have Hval := ((HF S hs).2.2.1 i).1
    have hamp : |F Y i.succ| ≤ K * |Y i.succ| := by
      rw [Hpoint, Hval, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul_of_nonneg_left (hmult S hs i).1 (abs_nonneg _)).trans_eq (by ring)
    refine ⟨hamp.trans (mul_le_mul_of_nonneg_right hKC (abs_nonneg _)), ?_⟩
    rw [Hder, ((HF S hs).2.2.1 i).2.2.2.2]
    have hz : (Pi.single 0 1 : ExitTailState) i.succ = 0 := by fin_cases i <;> simp
    rw [hz, mul_zero, zero_add, abs_mul, ← Hpoint]
    have Hlog := (fderiv ℝ (fun Z => exitClockLogMultiplier I i Z S) Y).le_opNorm (Pi.single 0 1)
    simp only [Pi.norm_single, norm_one, mul_one, Real.norm_eq_abs] at Hlog
    have Hlength : S ≤ L / α := hSS₀.trans ((le_div_iff₀ hα.1).mpr (by
      simpa only [mul_comm] using (exitTailLength_weighted_bounds ⟨hη₀.1, hη₀.2.le⟩ hα J).1))
    calc
      _ ≤ (K * |Y i.succ|) * (K * (L / α)) :=
        mul_le_mul hamp (Hlog.trans ((hmult S hs i).2.trans (mul_le_mul_of_nonneg_left Hlength hK0)))
          (abs_nonneg _) (by positivity)
      _ = (K ^ 2 * L) * |Y i.succ| / α := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hwallC (abs_nonneg _)) hα.1.le

end BianchiIX
