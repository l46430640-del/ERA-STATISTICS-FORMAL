import BianchiIX.Dynamics.CoreReflectionOrbit
import BianchiIX.Analysis.PositiveConeTransport

noncomputable section

namespace BianchiIX

/-- One common amplitude domain supports the actual core-reflection step and its phase, loss and cone estimates. -/
theorem exists_coreReflection_step :
    ∃ ε > (0 : ℝ), ε ≤ 1 / 10000 ∧ ∃ C > (0 : ℝ), ∃ c > (0 : ℝ), c ≤ 1 / 2 ∧
      ∀ Y : CoreAngleState, 2 ≤ Y 0 →
        (0 < Y 1 ∧ Y 1 ≤ ε / Y 0) → (0 < Y 2 ∧ Y 2 ≤ ε / Y 0) →
        let F := coreReturnState coreRadiusReturnTime
        let Z := F Y
        let G := coreReflectionState coreRadiusReturnTime
        coreRadiusReturnValid Y ∧ ContDiffAt ℝ 1 F Y ∧ |Z 0 - Y 0| ≤ 1 / 8 ∧
        (ContDiffAt ℝ 1 coreRadiusReturnTime Y ∧ |Z 0 - Y 0| ≤ C * (Y 1 + Y 2) / Y 0 ∧
          (∀ i : Fin 2, 0 < Z i.succ ∧ Z i.succ ≤ Real.exp (-c / Y 0) * Y i.succ) ∧
          ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
            let d := fderiv ℝ F Y v
            0 < d 0 ∧ |Real.log (d 0)| ≤ C * Real.sqrt (Y 1 + Y 2) / Y 0 ∧
              ∀ i : Fin 2, |d i.succ| ≤ Real.sqrt (Z i.succ) * d 0) ∧
        (31 / 8 ≤ Z 0 →
          0 < coreReflectionTime Y ∧
          coreRadiusEntry (G Y) = projectiveReflection
            (projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreReflectionTime Y)) ∧
          ContDiffAt ℝ 1 coreReflectionTime Y ∧ ContDiffAt ℝ 1 G Y ∧
          |Z 0 - Y 0| + |G Y 0 - (Z 0 - 2)| ≤ C * (Y 1 + Y 2) / Y 0 ∧
          |G Y 0 - (Y 0 - 2)| ≤ C * (Y 1 + Y 2) / Y 0 ∧
          (3 / 2 ≤ Y 0 - G Y 0 ∧ Y 0 - G Y 0 ≤ 5 / 2) ∧
          (∀ i : Fin 2, 0 < Z i.succ ∧ 0 < G Y i.succ ∧ G Y i.succ ≤ Z i.succ ∧
            Z i.succ ≤ Real.exp (-c / Y 0) * Y i.succ) ∧
          (2 ≤ G Y 0 → ∀ i : Fin 2, G Y i.succ ≤ ε / G Y 0) ∧
          ∀ v : CoreAngleState, v 0 = 1 → |v 1| ≤ Real.sqrt (Y 1) → |v 2| ≤ Real.sqrt (Y 2) →
            let d := fderiv ℝ G Y v
            0 < d 0 ∧ |Real.log (d 0)| ≤ C * Real.sqrt (Y 1 + Y 2) / Y 0 ∧
              ∀ i : Fin 2, |d i.succ| ≤ Real.sqrt (G Y i.succ) * d 0) := by
  obtain ⟨εk, hεk, _, K, hK, c, hc, hcmax, HK⟩ := exists_coreRadiusReturn_estimates
  obtain ⟨εr, hεr, _, R, hR, HR⟩ := exists_reflectionReturn_estimates
  let C := K + 2 * R
  have hC : 0 < C := by dsimp [C]; positivity
  let ε := min εk (min (εr / 2) (min (1 / 10000) (min (1 / (4 * K)) (1 / C))))
  have hε : 0 < ε := lt_min hεk (lt_min (half_pos hεr)
    (lt_min (by norm_num) (lt_min (by positivity) (by positivity))))
  have hεk' : ε ≤ εk := min_le_left _ _
  have hεr' : ε ≤ εr / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hεmax : ε ≤ 1 / 10000 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεK : ε ≤ 1 / (4 * K) := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hεC : ε ≤ 1 / C := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hKε : K * ε ≤ 1 / 4 := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * K)).mp hεK
    nlinarith only [H]
  have hCε : C * ε ≤ 1 := by simpa only [mul_comm] using (le_div_iff₀ hC).mp hεC
  refine ⟨ε, hε, hεmax, C, hC, c, hc, hcmax, ?_⟩
  intro Y hk hu hw F Z G
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hb : 0 ≤ Y 1 + Y 2 := add_nonneg hu.1.le hw.1.le
  have hbε : Y 1 + Y 2 ≤ ε := by
    nlinarith only [(le_div_iff₀ hk0).mp hu.2, (le_div_iff₀ hk0).mp hw.2,
      mul_le_mul_of_nonneg_right hk hu.1.le, mul_le_mul_of_nonneg_right hk hw.1.le]
  have hεscale := div_le_div_of_nonneg_right hεk' hk0.le
  obtain ⟨hvalid, ht, hF, hval, hwall, hdiff⟩ := HK Y hk
    ⟨hu.1.le, hu.2.trans hεscale⟩ ⟨hw.1.le, hw.2.trans hεscale⟩
  have hpos (i : Fin 2) : 0 < Y i.succ := by
    fin_cases i
    · exact hu.1
    · exact hw.1
  have hin (i : Fin 2) : Y i.succ ≤ ε / Y 0 := by
    fin_cases i
    · exact hu.2
    · exact hw.2
  have hzpos (i : Fin 2) : 0 < Z i.succ := (hwall i).2.1.mpr (hpos i)
  have hzle (i : Fin 2) : Z i.succ ≤ Y i.succ := (hwall i).2.2.trans
    ((mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) hk0.le))
      (hpos i).le).trans_eq (one_mul _))
  have hsmall : |Z 0 - Y 0| ≤ 1 / 8 := hval.trans (by
    calc
      _ ≤ K * ε / Y 0 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbε hK.le) hk0.le
      _ ≤ K * ε / 2 := div_le_div_of_nonneg_left (mul_nonneg hK.le hε.le) (by norm_num) hk
      _ ≤ _ := by linarith only [hKε])
  have hZrange : Y 0 / 2 ≤ Z 0 ∧ Z 0 ≤ 2 * Y 0 := by
    constructor <;> linarith only [(abs_le.mp hsmall).1, (abs_le.mp hsmall).2, hk]
  have hZ0 : 0 < Z 0 := (half_pos hk0).trans_le hZrange.1
  have hKC : K ≤ C := by dsimp [C]; linarith only [hR]
  have hcoefficient {a : ℝ} (ha : 0 ≤ a) : K * a / Y 0 ≤ C * a / Y 0 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hKC ha) hk0.le
  refine ⟨hvalid, hF, hsmall, ?_, ?_⟩
  · refine ⟨ht, hval.trans (hcoefficient hb), fun i => ⟨hzpos i, (hwall i).2.2⟩, ?_⟩
    intro v hv0 hv1 hv2 d
    obtain ⟨hm, hl, hcone⟩ := hdiff v hv0 hv1 hv2
    exact ⟨by linarith only [hm.1], hl.trans (hcoefficient (Real.sqrt_nonneg _)), hcone⟩
  intro hguard
  have hzquarter (i : Fin 2) : Z i.succ ≤ 1 / 4 :=
    ((hzle i).trans (hin i)).trans ((div_le_self hε.le (by linarith only [hk])).trans
      (hεmax.trans (by norm_num)))
  have hchart := coreRadiusReturn_exit_chart hvalid (by linarith only [hguard])
    ⟨(hzpos 0).le, hzquarter 0⟩ ⟨(hzpos 1).le, hzquarter 1⟩
  have hbudget : ε / Y 0 ≤ εr / Z 0 := by
    calc
      _ = (2 * ε) / (2 * Y 0) := by ring
      _ ≤ (2 * ε) / Z 0 := div_le_div_of_nonneg_left (by positivity) hZ0 hZrange.2
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith only [hεr']) hZ0.le
  obtain ⟨hfirst, hactual, hrt, hrf, hrval, hrwall, hrdiff⟩ := HR Z hguard
    ⟨hzpos 0, ((hzle 0).trans hu.2).trans hbudget⟩
    ⟨hzpos 1, ((hzle 1).trans hw.2).trans hbudget⟩
  obtain ⟨htotal, horbit⟩ := coreReflection_canonical_orbit hvalid hchart hfirst.1.1 hactual
  have hGt : ContDiffAt ℝ 1 coreReflectionTime Y := by
    change ContDiffAt ℝ 1 (fun X => reflectionReturnTime (F X) + coreRadiusReturnTime X) Y
    exact ((hrt.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).comp Y hF).add ht
  have hG : ContDiffAt ℝ 1 G Y := by
    change ContDiffAt ℝ 1 (reflectionReturnState ∘ F) Y
    exact (hrf.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).comp Y hF
  have hzb : Z 1 + Z 2 ≤ Y 1 + Y 2 := add_le_add (hzle 0) (hzle 1)
  have hscale {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : R * a / Z 0 ≤ 2 * R * b / Y 0 := by
    calc
      _ ≤ R * a / (Y 0 / 2) := div_le_div_of_nonneg_left (mul_nonneg hR.le ha) (half_pos hk0) hZrange.1
      _ = 2 * R * a / Y 0 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hab (by positivity)) hk0.le
  have hconn : |G Y 0 - (Z 0 - 2)| ≤ 2 * R * (Y 1 + Y 2) / Y 0 :=
    hrval.trans (hscale (add_nonneg (hzpos 0).le (hzpos 1).le) hzb)
  have hsum : |Z 0 - Y 0| + |G Y 0 - (Z 0 - 2)| ≤ C * (Y 1 + Y 2) / Y 0 :=
    (add_le_add hval hconn).trans_eq (by dsimp [C]; ring)
  have htotalErr : |G Y 0 - (Y 0 - 2)| ≤ C * (Y 1 + Y 2) / Y 0 := by
    have heq : G Y 0 - (Y 0 - 2) = (Z 0 - Y 0) + (G Y 0 - (Z 0 - 2)) := by ring
    rw [heq]
    exact (abs_add_le _ _).trans hsum
  have hhalf : C * (Y 1 + Y 2) / Y 0 ≤ 1 / 2 := by
    calc
      _ ≤ C * ε / Y 0 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbε hC.le) hk0.le
      _ ≤ C * ε / 2 := div_le_div_of_nonneg_left (mul_nonneg hC.le hε.le) (by norm_num) hk
      _ ≤ _ := div_le_div_of_nonneg_right hCε (by norm_num)
  have hdrop : 3 / 2 ≤ Y 0 - G Y 0 ∧ Y 0 - G Y 0 ≤ 5 / 2 := by
    have HH := abs_le.mp (htotalErr.trans hhalf)
    constructor <;> linarith only [HH.1, HH.2]
  refine ⟨htotal, horbit, hGt, hG, hsum, htotalErr, hdrop, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hzpos i, (hrwall i).1, (hrwall i).2, (hwall i).2.2⟩
  · intro hnext i
    exact ((hrwall i).2.trans ((hzle i).trans (hin i))).trans
      (div_le_div_of_nonneg_left hε.le (by linarith only [hnext]) (by linarith only [hdrop.1]))
  · intro v hv0 hv1 hv2 d
    let w := fderiv ℝ F Y v
    obtain ⟨hm, hl, hcone⟩ := hdiff v hv0 hv1 hv2
    have hw0 : 0 < w 0 := by linarith only [hm.1]
    have Htransport := positive_cone_transport (fderiv ℝ reflectionReturnState Z) hw0 hcone (by
      intro z hz0 hz
      obtain ⟨hmargin, _, hlog, hzc⟩ := hrdiff z hz0 (hz 0) (hz 1)
      exact ⟨by linarith only [hmargin], hlog, hzc⟩)
    have hd : d = fderiv ℝ reflectionReturnState Z w := by
      change fderiv ℝ (reflectionReturnState ∘ F) Y v = _
      rw [fderiv_comp Y (hrf.differentiableAt (by norm_num)) (hF.differentiableAt (by norm_num)),
        ContinuousLinearMap.comp_apply]
    rw [hd]
    refine ⟨Htransport.1, Htransport.2.1.trans ?_, Htransport.2.2⟩
    have hrlog := hscale (Real.sqrt_nonneg (Z 1 + Z 2)) (Real.sqrt_le_sqrt hzb)
    exact (add_le_add hl hrlog).trans_eq (by dsimp [C]; ring)

end BianchiIX
