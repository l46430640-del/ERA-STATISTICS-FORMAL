import BianchiIX.Dynamics.CoreReflectionStep
import BianchiIX.Analysis.PositiveConeIterates
import BianchiIX.Analysis.DiscreteDissipation

noncomputable section

namespace BianchiIX

/-- The actual finite core-reflection orbit pays for its phase and composite derivative errors by amplitude loss. -/
theorem exists_coreReflection_prefix_bounds :
    ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), c ≤ 1 / 2 ∧
      ∀ (n : ℕ) (Y : ℕ → CoreAngleState),
        let F := coreReturnState coreRadiusReturnTime
        let G := coreReflectionState coreRadiusReturnTime
        let b := fun j => Y j 1 + Y j 2
        (0 < Y 0 1 ∧ Y 0 1 ≤ ε / Y 0 0) → (0 < Y 0 2 ∧ Y 0 2 ≤ ε / Y 0 0) →
        (∀ j < n, 2 ≤ Y j 0 ∧ 31 / 8 ≤ F (Y j) 0) →
        (∀ j < n, Y (j + 1) = G (Y j)) →
        (∀ j ≤ n, ∀ i : Fin 2, 0 < Y j i.succ) ∧
        (∀ p > (0 : ℝ), ∑ j ∈ Finset.range n, (b j) ^ p / Y j 0 ≤
          ((1 + p * c / 2) / (p * c)) * ((b 0) ^ p - (b n) ^ p)) ∧
        (∑ j ∈ Finset.range n, (|F (Y j) 0 - Y j 0| + |Y (j + 1) 0 - (F (Y j) 0 - 2)|)) ≤
          C * ((1 + c / 2) / c) * (b 0 - b n) ∧
        |Y n 0 - (Y 0 0 - 2 * n)| ≤ C * ((1 + c / 2) / c) * (b 0 - b n) ∧
        G^[n] (Y 0) = Y n ∧ (ContDiffAt ℝ 1 (G^[n]) (Y 0) ∧
          ∀ j < n, 0 < coreReflectionTime (Y j) ∧
            coreRadiusEntry (Y (j + 1)) = projectiveReflection
              (projectiveOriginalFlow (coreRadiusEntry (Y j)) 0 (coreReflectionTime (Y j)))) ∧
        (∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 0 1) → |v 2| ≤ Real.sqrt (Y 0 2) →
          let d := fderiv ℝ (G^[n]) (Y 0) v
          0 < d 0 ∧ |Real.log (d 0)| ≤
            C * ((1 + c / 4) / (c / 2)) * (Real.sqrt (b 0) - Real.sqrt (b n)) ∧
            ∀ i : Fin 2, |d i.succ| ≤ Real.sqrt (Y n i.succ) * d 0) ∧
        (2 ≤ Y n 0 →
          let Z := F (Y n)
          let B := Z 1 + Z 2
          let J := F ∘ G^[n]
          coreRadiusReturnValid (Y n) ∧ ContDiffAt ℝ 1 J (Y 0) ∧
          ContDiffAt ℝ 1 (coreRadiusReturnTime ∘ G^[n]) (Y 0) ∧
          (∀ i : Fin 2, 0 < Z i.succ) ∧ B ≤ b 0 ∧
          |Z 0 - (Y 0 0 - 2 * n)| ≤ C * ((1 + c / 2) / c) * (b 0 - B) ∧
          ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 0 1) → |v 2| ≤ Real.sqrt (Y 0 2) →
            let d := fderiv ℝ J (Y 0) v
            0 < d 0 ∧ |Real.log (d 0)| ≤
              C * ((1 + c / 4) / (c / 2)) * (Real.sqrt (b 0) - Real.sqrt B) ∧
              ∀ i : Fin 2, |d i.succ| ≤ Real.sqrt (Z i.succ) * d 0) := by
  obtain ⟨ε, hε, hεmax, C, hC, c, hc, hcmax, H⟩ := exists_coreReflection_step
  refine ⟨ε, hε, hεmax, C, hC, c, hc, hcmax, ?_⟩
  intro n Y F G b hu hw hphase horbit
  have hentry : ∀ j ≤ n, ∀ i : Fin 2,
      0 < Y j i.succ ∧ (2 ≤ Y j 0 → Y j i.succ ≤ ε / Y j 0) := by
    intro j
    induction j with
    | zero =>
      intro _ i
      fin_cases i
      · exact ⟨hu.1, fun _ => hu.2⟩
      · exact ⟨hw.1, fun _ => hw.2⟩
    | succ j ih =>
      intro hj i
      have hjn : j < n := by omega
      have hp := ih (by omega)
      obtain ⟨_, _, _, _, HS⟩ := H (Y j) (hphase j hjn).1
        ⟨(hp 0).1, (hp 0).2 (hphase j hjn).1⟩ ⟨(hp 1).1, (hp 1).2 (hphase j hjn).1⟩
      obtain ⟨_, _, _, _, _, _, _, hwall, hnext, _⟩ := HS (hphase j hjn).2
      rw [horbit j hjn]
      exact ⟨(hwall i).2.1, fun hk => hnext hk i⟩
  have HE (j : ℕ) (hj : j < n) := (H (Y j) (hphase j hj).1
    ⟨(hentry j hj.le 0).1, (hentry j hj.le 0).2 (hphase j hj).1⟩
    ⟨(hentry j hj.le 1).1, (hentry j hj.le 1).2 (hphase j hj).1⟩).2.2.2.2 (hphase j hj).2
  have hnonneg (j : ℕ) (hj : j ≤ n) : 0 ≤ b j :=
    add_nonneg (hentry j hj 0).1.le (hentry j hj 1).1.le
  have hdec (j : ℕ) (hj : j < n) : F (Y j) 1 + F (Y j) 2 ≤ Real.exp (-c / Y j 0) * b j := by
    obtain ⟨_, _, _, _, _, _, _, hwall, _, _⟩ := HE j hj
    simpa only [b, F, mul_add] using! add_le_add (hwall 0).2.2.2 (hwall 1).2.2.2
  have hconn (j : ℕ) (hj : j < n) : b (j + 1) ≤ F (Y j) 1 + F (Y j) 2 := by
    obtain ⟨_, _, _, _, _, _, _, hwall, _, _⟩ := HE j hj
    dsimp only [b]
    rw [horbit j hj]
    exact add_le_add (hwall 0).2.2.1 (hwall 1).2.2.1
  have hbudget (p : ℝ) (hp : 0 < p) := sum_rpow_div_le_core_losses
    (a := b) (b := fun j => F (Y j) 1 + F (Y j) 2) (k := fun j => Y j 0)
    hc hp n hnonneg (fun j hj => (hphase j hj).1) hdec hconn
  have hlinear : ∑ j ∈ Finset.range n, b j / Y j 0 ≤ ((1 + c / 2) / c) * (b 0 - b n) := by
    simpa only [Real.rpow_one, one_mul] using hbudget 1 zero_lt_one
  have hroot : ∑ j ∈ Finset.range n, Real.sqrt (b j) / Y j 0 ≤
      ((1 + c / 4) / (c / 2)) * (Real.sqrt (b 0) - Real.sqrt (b n)) := by
    have Hhalf := hbudget (1 / 2) (by norm_num)
    simpa only [← Real.sqrt_eq_rpow, show (1 / 2 : ℝ) * c = c / 2 by ring,
      show c / 2 / 2 = c / 4 by ring] using Hhalf
  have hsum : (∑ j ∈ Finset.range n, (|F (Y j) 0 - Y j 0| + |Y (j + 1) 0 - (F (Y j) 0 - 2)|)) ≤
      C * ((1 + c / 2) / c) * (b 0 - b n) := by
    calc
      _ ≤ ∑ j ∈ Finset.range n, C * (b j / Y j 0) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjn := Finset.mem_range.mp hj
        rw [horbit j hjn]
        exact (HE j hjn).2.2.2.2.1.trans_eq (by ring)
      _ = C * ∑ j ∈ Finset.range n, b j / Y j 0 := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := (mul_le_mul_of_nonneg_left hlinear hC.le).trans_eq (by ring)
  have htel (m : ℕ) : ∑ j ∈ Finset.range m, (Y (j + 1) 0 - (Y j 0 - 2)) =
      Y m 0 - (Y 0 0 - 2 * m) := by
    induction m with
    | zero => simp
    | succ m hm => rw [Finset.sum_range_succ, hm, Nat.cast_add, Nat.cast_one]; ring
  have hphaseSum : |Y n 0 - (Y 0 0 - 2 * n)| ≤ C * ((1 + c / 2) / c) * (b 0 - b n) := by
    rw [← htel]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply LE.le.trans _ hsum
    apply Finset.sum_le_sum
    intro j _
    have heq : Y (j + 1) 0 - (Y j 0 - 2) =
        (F (Y j) 0 - Y j 0) + (Y (j + 1) 0 - (F (Y j) 0 - 2)) := by ring
    rw [heq]
    exact abs_add_le _ _
  have hiter (v : CoreAngleState) (hv0 : v 0 = 1)
      (hv : ∀ i : Fin 2, |v i.succ| ≤ Real.sqrt (Y 0 i.succ)) :=
    positive_cone_iterate G Y (fun j i => Real.sqrt (Y j i.succ))
      (fun j => C * Real.sqrt (b j) / Y j 0) n horbit
      (fun j hj => (HE j hj).2.2.2.1.differentiableAt (by norm_num))
      (fun j hj z hz0 hz => by
        obtain ⟨_, _, _, _, _, _, _, _, _, HD⟩ := HE j hj
        simpa only [horbit j hj] using HD z hz0 (hz 0) (hz 1)) hv0 hv
  have hregular := contDiffAt_iterate_along_orbit G Y n horbit (fun j hj => (HE j hj).2.2.2.1)
  have hgeometry (j : ℕ) (hj : j < n) : 0 < coreReflectionTime (Y j) ∧
      coreRadiusEntry (Y (j + 1)) = projectiveReflection
        (projectiveOriginalFlow (coreRadiusEntry (Y j)) 0 (coreReflectionTime (Y j))) := by
    rw [horbit j hj]
    exact ⟨(HE j hj).1, (HE j hj).2.1⟩
  have hderiv (v : CoreAngleState) (hv0 : v 0 = 1) (hv1 : |v 1| ≤ Real.sqrt (Y 0 1))
      (hv2 : |v 2| ≤ Real.sqrt (Y 0 2)) :
      let d := fderiv ℝ (G^[n]) (Y 0) v
      0 < d 0 ∧ |Real.log (d 0)| ≤
        C * ((1 + c / 4) / (c / 2)) * (Real.sqrt (b 0) - Real.sqrt (b n)) ∧
        ∀ i : Fin 2, |d i.succ| ≤ Real.sqrt (Y n i.succ) * d 0 := by
    have hv (i : Fin 2) : |v i.succ| ≤ Real.sqrt (Y 0 i.succ) := by
      fin_cases i
      · exact hv1
      · exact hv2
    obtain ⟨_, _, hd0, hlog, hdcone⟩ := hiter v hv0 hv
    refine ⟨hd0, hlog.trans ?_, hdcone⟩
    calc
      _ = C * ∑ j ∈ Finset.range n, Real.sqrt (b j) / Y j 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hroot hC.le).trans_eq (by ring)
  refine ⟨fun j hj i => (hentry j hj i).1, hbudget, hsum, hphaseSum,
    hregular.1, ⟨hregular.2, hgeometry⟩, hderiv, ?_⟩
  intro hk Z B J
  obtain ⟨hvalid, hF, _, ⟨ht, hval, hwall, hdiff⟩, _⟩ := H (Y n) hk
    ⟨(hentry n le_rfl 0).1, (hentry n le_rfl 0).2 hk⟩
    ⟨(hentry n le_rfl 1).1, (hentry n le_rfl 1).2 hk⟩
  have hB : 0 ≤ B := add_nonneg (hwall 0).1.le (hwall 1).1.le
  have hlast : B ≤ Real.exp (-c / Y n 0) * b n := by
    simpa only [B, Z, F, b, mul_add] using! add_le_add (hwall 0).2 (hwall 1).2
  have hBnext : B ≤ b n := hlast.trans
    ((mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (by linarith only [hk])))
      (hnonneg n le_rfl)).trans_eq (one_mul _))
  have hbn : b n ≤ b 0 := by
    have hs : 0 ≤ ∑ j ∈ Finset.range n, b j / Y j 0 := Finset.sum_nonneg (by
      intro j hj
      have hjn := Finset.mem_range.mp hj
      exact div_nonneg (hnonneg j hjn.le) (by linarith only [(hphase j hjn).1]))
    have hA : 0 < (1 + c / 2) / c := by positivity
    nlinarith only [hs.trans hlinear, hA]
  have hfinal (p : ℝ) (hp : 0 < p) := rpow_div_le_core_loss (hnonneg n le_rfl) hB hk hc hp hlast
  have hlastLinear : b n / Y n 0 ≤ ((1 + c / 2) / c) * (b n - B) := by
    simpa only [Real.rpow_one, one_mul] using hfinal 1 zero_lt_one
  have hlastRoot : Real.sqrt (b n) / Y n 0 ≤
      ((1 + c / 4) / (c / 2)) * (Real.sqrt (b n) - Real.sqrt B) := by
    simpa only [← Real.sqrt_eq_rpow, show (1 / 2 : ℝ) * c = c / 2 by ring,
      show c / 2 / 2 = c / 4 by ring] using hfinal (1 / 2) (by norm_num)
  have hF' : ContDiffAt ℝ 1 F (G^[n] (Y 0)) := by rw [hregular.1]; exact hF
  have ht' : ContDiffAt ℝ 1 coreRadiusReturnTime (G^[n] (Y 0)) := by rw [hregular.1]; exact ht
  have hlastValue : |Z 0 - Y n 0| ≤ C * ((1 + c / 2) / c) * (b n - B) := by
    calc
      _ ≤ C * (b n / Y n 0) := hval.trans_eq (by ring)
      _ ≤ _ := (mul_le_mul_of_nonneg_left hlastLinear hC.le).trans_eq (by ring)
  refine ⟨hvalid, hF'.comp _ hregular.2, ht'.comp _ hregular.2,
    fun i => (hwall i).1, hBnext.trans hbn, ?_, ?_⟩
  · calc
      _ ≤ |Z 0 - Y n 0| + |Y n 0 - (Y 0 0 - 2 * n)| := abs_sub_le _ _ _
      _ ≤ C * ((1 + c / 2) / c) * (b n - B) +
          C * ((1 + c / 2) / c) * (b 0 - b n) := add_le_add hlastValue hphaseSum
      _ = _ := by ring
  · intro v hv0 hv1 hv2 d
    obtain ⟨hp, hl, hcone⟩ := hderiv v hv0 hv1 hv2
    have HT := positive_cone_transport (fderiv ℝ F (Y n)) hp hcone
      (fun z hz0 hz => hdiff z hz0 (hz 0) (hz 1))
    have hd : d = fderiv ℝ F (Y n) (fderiv ℝ (G^[n]) (Y 0) v) := by
      change fderiv ℝ (F ∘ G^[n]) (Y 0) v = _
      rw [fderiv_comp _ (hF'.differentiableAt (by norm_num))
        (hregular.2.differentiableAt (by norm_num)), ContinuousLinearMap.comp_apply, hregular.1]
    rw [hd]
    refine ⟨HT.1, HT.2.1.trans ?_, HT.2.2⟩
    have hpaid : C * Real.sqrt (b n) / Y n 0 ≤
        C * ((1 + c / 4) / (c / 2)) * (Real.sqrt (b n) - Real.sqrt B) := by
      calc
        _ = C * (Real.sqrt (b n) / Y n 0) := by ring
        _ ≤ _ := (mul_le_mul_of_nonneg_left hlastRoot hC.le).trans_eq (by ring)
    exact (add_le_add hl hpaid).trans_eq (by ring)

end BianchiIX
