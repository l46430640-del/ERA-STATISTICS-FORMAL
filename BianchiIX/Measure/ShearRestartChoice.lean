import BianchiIX.Analysis.BorelSelection
import BianchiIX.Measure.ShearRegionStatistics
import BianchiIX.Statistics.CoreRestartWitness

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def shearRestartParameterDomain (ε a P : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  restartShearCommonLabelSet ε a P ×ˢ Icc a (2 * a)

def shearRestartChart (o : Bool) (p : (ℝ × ℝ) × ℝ) : SectionCoordinates :=
  let y : SectionCoordinates := ![p.2, -Real.log p.1.1, -Real.log p.1.2]
  if o then mainWallReflection y else y

def shearRestartData (h s a : ℝ) (o : Bool) (p : (ℝ × ℝ) × ℝ) : CoreRestartData :=
  ((if o then 0 else 3, restartShearReturnTime h s p.1.1 p.1.2 p.2),
    (restartShearAmplitudeBudget a p.1.1 p.1.2, restartShearReturnState h s p.1.1 p.1.2 p.2))

theorem measurableSet_shearRestartParameterDomain (ε a P : ℝ) :
    MeasurableSet (shearRestartParameterDomain ε a P) :=
  (measurableSet_restartShearCommonLabelSet ε a P).prod measurableSet_Icc

theorem continuousOn_shearRestartChart (ε a P : ℝ) (o : Bool) :
    ContinuousOn (shearRestartChart o) (shearRestartParameterDomain ε a P) := by
  have H : ContinuousOn (fun p : (ℝ × ℝ) × ℝ =>
      (![p.2, -Real.log p.1.1, -Real.log p.1.2] : SectionCoordinates))
      (shearRestartParameterDomain ε a P) := by
    intro p hp
    have h₂ : p.1.1 ≠ 0 := hp.1.1.1.ne'
    have h₃ : p.1.2 ≠ 0 := hp.1.2.1.1.ne'
    apply ContinuousAt.continuousWithinAt
    fun_prop
  cases o
  · exact H
  · exact mainWallReflectionEquiv.continuous.comp_continuousOn H

theorem injOn_shearRestartChart (ε a P : ℝ) (o : Bool) :
    InjOn (shearRestartChart o) (shearRestartParameterDomain ε a P) := by
  have H : InjOn (shearRestartChart false) (shearRestartParameterDomain ε a P) := by
    intro p hp q hq heq
    have h₂ := Real.log_injOn_pos hp.1.1.1 hq.1.1.1 (neg_injective (congrFun heq 1))
    have h₃ := Real.log_injOn_pos hp.1.2.1.1 hq.1.2.1.1 (neg_injective (congrFun heq 2))
    exact Prod.ext (Prod.ext h₂ h₃) (congrFun heq 0)
  cases o
  · exact H
  · intro p hp q hq heq
    exact H hp hq (mainWallReflectionEquiv.injective heq)

theorem measurable_shearRestartData {h s ε a P : ℝ} (o : Bool)
    (hT : ∀ p ∈ shearRestartParameterDomain ε a P,
      ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnTime h s v.1.1 v.1.2 v.2) p)
    (hY : ∀ p ∈ shearRestartParameterDomain ε a P,
      ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartShearReturnState h s v.1.1 v.1.2 v.2) p) :
    Measurable ((shearRestartParameterDomain ε a P).domRestrict (shearRestartData h s a o)) := by
  have hTm := (continuousOn_iff_continuous_domRestrict.mp
    (fun p hp => (hT p hp).continuousAt.continuousWithinAt)).measurable
  have hYm := (continuousOn_iff_continuous_domRestrict.mp
    (fun p hp => (hY p hp).continuousAt.continuousWithinAt)).measurable
  have hBm : Measurable (fun p : shearRestartParameterDomain ε a P =>
      restartShearAmplitudeBudget a p.val.1.1 p.val.1.2) := by
    unfold restartShearAmplitudeBudget
    fun_prop
  exact (measurable_const.prodMk hTm).prodMk (hBm.prodMk hYm)

set_option maxHeartbeats 800000 in
/-- Both shear signs retain a quantitative failure bound together with the same Borel restart. -/
theorem exists_shearRegion_borel_restart_quantitative (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
            ∀ Bbound : ℝ, 0 < Bbound → ∃ dstar > (0 : ℝ), ∀ d ∈ Ioc (0 : ℝ) dstar,
              ∀ ε : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
              let F := shearFailureRegion h q d ε P η J σ Bcap
              let C := 66 * logarithmicFluxConstant (shearFailureFluxConstant σ) σ + 132 * P ^ 2
              MeasurableSet F ∧ mainWallMeasure h F ≤ ENNReal.ofReal (C * d * (1 + |Real.log d|) ^ 2) ∧
                mainWallMeasure h F ≠ ⊤ ∧
                ∃ W : SectionCoordinates → CoreRestartData, Measurable W ∧
                  ∀ z ∈ shearSection d ε \ F, z ∈ mainWallChartDomain h ∧ (W z).2.1 ≤ Bbound ∧
                    CoreRestartWitness η J σ Bcap (mainWallChart h z) (W z) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartShear_signed_physical_failure_dyadic hBirkhoff
  obtain ⟨hR, hhR, HR⟩ := exists_restartShearReturn_common_regular
  obtain ⟨hO, hhO, HO⟩ := exists_restartShearReturn_common_bounds
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, min hR (min hO (min hS (1 / 8))),
    lt_min hhR (lt_min hhO (lt_min hhS (by norm_num))), ?_⟩
  intro h hh q D P hq hD hP Bbound hBbound
  have hh' := hh.2.trans (min_le_right _ _)
  have hh'' := hh'.trans (min_le_right _ _)
  have hh1 : h ≤ 1 / 8 := hh''.trans (min_le_right _ _)
  obtain ⟨aR, haR, HAR⟩ := HR h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aO, haO, HAO⟩ := HO h ⟨hh.1, hh'.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨dS, hdS, HdS⟩ := HS h ⟨hh.1, hh''.trans (min_le_left _ _)⟩ q D P hq hD hP
  let d₀ := min aR (min aO (min dS (h / 8)))
  refine ⟨min d₀ (min 1 (Bbound / 800)),
    lt_min (lt_min haR (lt_min haO (lt_min hdS (div_pos hh.1 (by norm_num)))))
      (lt_min zero_lt_one (div_pos hBbound (by norm_num))), ?_⟩
  intro d hd₀ ε hε F Cflux
  have hd : d ∈ Ioc 0 d₀ := ⟨hd₀.1, hd₀.2.trans (min_le_left _ _)⟩
  have hd1 : d ≤ 1 := hd₀.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdB : 800 * d ≤ Bbound := by
    have H := (le_div_iff₀ (by norm_num : (0 : ℝ) < 800)).mp
      (hd₀.2.trans ((min_le_right _ _).trans (min_le_right _ _)))
    simpa only [mul_comm] using H
  have hd' := hd.2.trans (min_le_right _ _)
  have hd'' := hd'.trans (min_le_right _ _)
  obtain ⟨_, hS, _, HSbound, _, Hgood⟩ := HdS d ⟨hd.1, hd''.trans (min_le_left _ _)⟩ ε hε
  obtain ⟨hU, _, HUbound, _⟩ := mainWallMeasure_shearUnselectedSection_dyadic
    hh.1 hh1 hd.1 (hd''.trans (min_le_right _ _))
    ⟨hε.1, hε.2.trans (by norm_num)⟩ (by linarith only [hD, hP] : 0 ≤ P)
  let Kflux := 66 * logarithmicFluxConstant (shearFailureFluxConstant σ) σ
  let Aflux := 132 * P ^ 2
  have hKflux : 0 ≤ Kflux := mul_nonneg (by norm_num)
    (logarithmicFluxConstant_nonneg (shearFailureFluxConstant_ge_one hσ.le) hσ)
  have hAflux : 0 ≤ Aflux := by dsimp only [Aflux]; positivity
  have Hbound : mainWallMeasure h F ≤ ENNReal.ofReal (Cflux * d * (1 + |Real.log d|) ^ 2) := calc
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Kflux * d * (1 + |Real.log d|) ^ 2) +
        ENNReal.ofReal (Aflux * d * (1 + |Real.log d|) ^ 2) := add_le_add HSbound HUbound
    _ = _ := by
      rw [← ENNReal.ofReal_add (mul_nonneg (mul_nonneg hKflux hd.1.le) (sq_nonneg _))
        (mul_nonneg (mul_nonneg hAflux hd.1.le) (sq_nonneg _))]
      congr 1
      change Kflux * d * _ + Aflux * d * _ = (Kflux + Aflux) * d * _
      ring
  let A : ℕ × Bool → Set ((ℝ × ℝ) × ℝ) := fun i => shearRestartParameterDomain ε (dyadicScale d i.1) P
  let C : ℕ × Bool → ((ℝ × ℝ) × ℝ) → SectionCoordinates := fun i => shearRestartChart i.2
  let G : ℕ × Bool → ((ℝ × ℝ) × ℝ) → CoreRestartData := fun i =>
    shearRestartData h (q / 2 * Real.log (1 / dyadicScale d i.1)) (dyadicScale d i.1) i.2
  have hreg (i : ℕ × Bool) (p : (ℝ × ℝ) × ℝ) (hp : p ∈ A i) :=
    HAR (dyadicScale d i.1)
      ⟨dyadicScale_pos hd.1 i.1, (dyadicScale_le hd.1.le i.1).trans (hd.2.trans (min_le_left _ _))⟩
      ε p.1.1 p.1.2 hε hp.1.1 hp.1.2.1 hp.1.2.2 p.2 hp.2
  obtain ⟨W, hWm, HW⟩ := exists_measurable_chart_selection A C G
    (fun i => measurableSet_shearRestartParameterDomain _ _ _)
    (fun i => continuousOn_shearRestartChart _ _ _ i.2)
    (fun i => injOn_shearRestartChart _ _ _ i.2)
    (fun i => measurable_shearRestartData i.2 (fun p hp => (hreg i p hp).2.2.2)
      (fun p hp => (hreg i p hp).2.1))
  refine ⟨hS.union hU, Hbound, ne_top_of_le_ne_top ENNReal.ofReal_ne_top Hbound, W, hWm, ?_⟩
  intro z hz
  have hcover : z ∈ ⋃ i, C i '' A i := by
    have hannuli : z ∈ ⋃ j, shearSectionAnnulus (dyadicScale d j) ε := by
      rw [← shearSection_dyadic_cover hd.1]
      exact hz.1
    obtain ⟨j, hj⟩ := mem_iUnion.mp hannuli
    have hn : z ∉ shearUnselectedSection (dyadicScale d j) ε P :=
      fun hbad => hz.2 (Or.inr (mem_iUnion_of_mem j hbad))
    obtain ⟨τ, n₂, n₃, ρ, hτ, hl, hρ, rfl⟩ := shearSection_selected_representation hε.1 hj hn
    rcases hτ with rfl | rfl
    · exact mem_iUnion.mpr ⟨(j, false), ((n₂, n₃), ρ), ⟨hl, hρ⟩, by simp [C, shearRestartChart]⟩
    · exact mem_iUnion.mpr ⟨(j, true), ((n₃, n₂), ρ),
        ⟨mem_restartShearCommonLabelSet_swap hl, hρ⟩, by simp [C, shearRestartChart, mainWallReflection]⟩
  obtain ⟨⟨j, o⟩, v, hv, heq, hW⟩ := HW z hcover
  have hscale := dyadicScale_le hd.1.le j
  have hweak : 2 * ε * dyadicScale d j ≤ dyadicScale d j :=
    mul_le_of_le_one_left (dyadicScale_pos hd.1 j).le (by linarith only [hε.2])
  have hbudget : restartShearAmplitudeBudget (dyadicScale d j) v.1.1 v.1.2 ≤ Bbound :=
    (restartShearAmplitudeBudget_le_of_min ⟨dyadicScale_pos hd.1 j, hscale.trans hd1⟩
      (by linarith only [hD, hP]) ⟨hv.1.1.1, hv.1.1.2.trans hweak⟩
      ⟨hv.1.2.1.1, hv.1.2.1.2.trans hweak⟩ hv.1.2.2).2.trans
      ((mul_le_mul_of_nonneg_left hscale (by norm_num : (0 : ℝ) ≤ 800)).trans hdB)
  have hn := fun hbad => hz.2 (Or.inl hbad)
  obtain ⟨hrad, hs, ht, hdom, _, _, _, _, _, _, ho⟩ := HAO (dyadicScale d j)
    ⟨dyadicScale_pos hd.1 j, (dyadicScale_le hd.1.le j).trans (hd'.trans (min_le_left _ _))⟩
    ε v.1.1 v.1.2 hε hv.1.1 hv.1.2.1 hv.1.2.2 v.2 hv.2
  rw [← mainWallRadicand_restartShear hv.1.1.1 hv.1.2.1.1, one_mul] at hrad
  rw [← mainWallChart_restartShear hv.1.1.1 hv.1.2.1.1, one_mul] at hdom ho
  have hy : ![v.2, -Real.log v.1.1, -Real.log v.1.2] ∈ mainWallChartDomain h := hrad
  rw [hW]
  subst z
  dsimp only [C, G, shearRestartChart, shearRestartData]
  cases o
  · simp only [Bool.false_eq_true, ite_false]
    change ![v.2, -Real.log v.1.1, -Real.log v.1.2] ∉ _ at hn
    obtain ⟨p, hp, hstat⟩ := Hgood j 1 (Or.inl rfl) v.1.1 v.1.2 hv.1 v.2 hv.2
      (by simpa only [one_mul] using hn)
    simp only [ite_true] at hp
    refine ⟨hy, hbudget, hs.trans_lt ht, hdom, p, hp, hstat, ?_⟩
    change coreRadiusEntry p.val.2 = toProjectiveState (axisSwap _)
    rw [toProjectiveState_axisSwap]
    simpa only [hp] using ho
  · simp only [ite_true]
    change ![-v.2, -Real.log v.1.2, -Real.log v.1.1] ∉ _ at hn
    obtain ⟨p, hp, hstat⟩ := Hgood j (-1) (Or.inr rfl) v.1.2 v.1.1
      (mem_restartShearCommonLabelSet_swap hv.1) v.2 hv.2 (by simpa only [neg_one_mul] using hn)
    have hp' : p.val = (restartShearAmplitudeBudget (dyadicScale d j) v.1.1 v.1.2,
        restartShearReturnState h (q / 2 * Real.log (1 / dyadicScale d j)) v.1.1 v.1.2 v.2) := by
      simpa only [if_neg (by norm_num : (-1 : ℝ) ≠ 1),
        restartShearAmplitudeBudget_swap _ v.1.1 v.1.2] using hp
    have hy' : mainWallReflection ![v.2, -Real.log v.1.1, -Real.log v.1.2] ∈ mainWallChartDomain h := by
      simpa only [mainWallChartDomain, mem_ofPred_eq, mainWallRadicand_reflection] using hy
    refine ⟨hy', hbudget, hs.trans_lt ht, ?_, p, hp', hstat, ?_⟩
    · rwa [normalizedMaxDomain_mainWallReflection]
    · change coreRadiusEntry p.val.2 = toProjectiveState
        (normalizedMaxCurve (mainWallChart h (mainWallReflection ![v.2, -Real.log v.1.1, -Real.log v.1.2])) 0 _)
      rw [normalizedMaxCurve_mainWallReflection hdom, toProjectiveState_axisSwap]
      simpa only [hp'] using ho

/-- Both shear signs have one Borel choice of actual time, physical frame, budget, and statistical survivor state. -/
theorem exists_shearRegion_borel_restart (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
            ∀ Bbound : ℝ, 0 < Bbound → ∃ dstar > (0 : ℝ), ∀ d ∈ Ioc (0 : ℝ) dstar,
              ∀ ε : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
              let F := shearFailureRegion h q d ε P η J σ Bcap
              MeasurableSet F ∧ mainWallMeasure h F ≠ ⊤ ∧
                ∃ W : SectionCoordinates → CoreRestartData, Measurable W ∧
                  ∀ z ∈ shearSection d ε \ F, z ∈ mainWallChartDomain h ∧ (W z).2.1 ≤ Bbound ∧
                    CoreRestartWitness η J σ Bcap (mainWallChart h z) (W z) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_shearRegion_borel_restart_quantitative hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, hS, hhS, ?_⟩
  intro h hh q D P hq hD hP Bbound hBbound
  obtain ⟨dS, hdS, HdS⟩ := HS h hh q D P hq hD hP Bbound hBbound
  refine ⟨dS, hdS, ?_⟩
  intro d hd ε hε
  obtain ⟨hF, _, H⟩ := HdS d hd ε hε
  exact ⟨hF, H⟩

end BianchiIX
