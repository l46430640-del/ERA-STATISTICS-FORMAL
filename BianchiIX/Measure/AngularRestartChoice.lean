import BianchiIX.Analysis.BorelSelection
import BianchiIX.Measure.AngularRegionStatistics
import BianchiIX.Statistics.CoreRestartWitness

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def angularRestartParameterDomain (a L P : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  restartLabelSet L a P ×ˢ Icc a (2 * a)

def angularRestartChart (o : Bool) (p : (ℝ × ℝ) × ℝ) : SectionCoordinates :=
  let y : SectionCoordinates := ![p.1.1 * p.2, -Real.log p.2, -Real.log p.1.2]
  if o then mainWallReflection y else y

def angularRestartData (h s a L : ℝ) (o : Bool) (p : (ℝ × ℝ) × ℝ) : CoreRestartData :=
  ((if o then 0 else 3, restartReturnTime h s p.1.1 p.1.2 p.2),
    (restartAmplitudeBudget L a p.1.2, restartReturnState h s p.1.1 p.1.2 p.2))

theorem measurableSet_angularRestartParameterDomain (a L P : ℝ) :
    MeasurableSet (angularRestartParameterDomain a L P) :=
  (measurableSet_restartLabelSet L a P).prod measurableSet_Icc

theorem continuousOn_angularRestartChart {a L P : ℝ} (ha : 0 < a) (o : Bool) :
    ContinuousOn (angularRestartChart o) (angularRestartParameterDomain a L P) := by
  have H : ContinuousOn (fun p : (ℝ × ℝ) × ℝ =>
      (![p.1.1 * p.2, -Real.log p.2, -Real.log p.1.2] : SectionCoordinates))
      (angularRestartParameterDomain a L P) := by
    intro p hp
    have hr : p.2 ≠ 0 := (ha.trans_le hp.2.1).ne'
    have hz : p.1.2 ≠ 0 := hp.1.2.1.ne'
    apply ContinuousAt.continuousWithinAt
    fun_prop
  cases o
  · exact H
  · exact mainWallReflectionEquiv.continuous.comp_continuousOn H

theorem injOn_angularRestartChart {a L P : ℝ} (ha : 0 < a) (o : Bool) :
    InjOn (angularRestartChart o) (angularRestartParameterDomain a L P) := by
  have H : InjOn (angularRestartChart false) (angularRestartParameterDomain a L P) := by
    intro p hp q hq heq
    have hpρ : 0 < p.2 := ha.trans_le hp.2.1
    have hqρ : 0 < q.2 := ha.trans_le hq.2.1
    have hρ := Real.log_injOn_pos hpρ hqρ (neg_injective (congrFun heq 1))
    have hζ := Real.log_injOn_pos hp.1.2.1 hq.1.2.1 (neg_injective (congrFun heq 2))
    have hθ := congrFun heq 0
    change p.1.1 * p.2 = q.1.1 * q.2 at hθ
    rw [hρ] at hθ
    exact Prod.ext (Prod.ext (mul_right_cancel₀ hqρ.ne' hθ) hζ) hρ
  cases o
  · exact H
  · intro p hp q hq heq
    exact H hp hq (mainWallReflectionEquiv.injective heq)

theorem measurable_angularRestartData {h s a L P : ℝ} (o : Bool)
    (hT : ∀ p ∈ angularRestartParameterDomain a L P,
      ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartReturnTime h s v.1.1 v.1.2 v.2) p)
    (hY : ∀ p ∈ angularRestartParameterDomain a L P,
      ContDiffAt ℝ 2 (fun v : (ℝ × ℝ) × ℝ => restartReturnState h s v.1.1 v.1.2 v.2) p) :
    Measurable ((angularRestartParameterDomain a L P).domRestrict (angularRestartData h s a L o)) := by
  have hTm := (continuousOn_iff_continuous_domRestrict.mp
    (fun p hp => (hT p hp).continuousAt.continuousWithinAt)).measurable
  have hYm := (continuousOn_iff_continuous_domRestrict.mp
    (fun p hp => (hY p hp).continuousAt.continuousWithinAt)).measurable
  have hBm : Measurable (fun p : angularRestartParameterDomain a L P => restartAmplitudeBudget L a p.val.1.2) := by
    unfold restartAmplitudeBudget
    fun_prop
  exact (measurable_const.prodMk hTm).prodMk (hBm.prodMk hYm)

theorem restartAmplitudeBudget_le_scale {L a ζ P : ℝ} (hL : 0 ≤ L)
    (ha : 0 < a) (haone : a ≤ 1) (hP : 4 ≤ P) (hζ : ζ ≤ a ^ P) :
    restartAmplitudeBudget L a ζ ≤ 51200 * (L + 1) * a := by
  have hζ4 : ζ ≤ a ^ (4 : ℕ) := hζ.trans (by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_ge ha haone hP)
  calc
    _ ≤ 6400 * (8 * (L + 1)) * a ^ 4 / a ^ 3 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hζ4 (by positivity)) (by positivity)
    _ = _ := by field_simp; ring

/-- A jointly Borel angular restart retains the quantitative bound for the same failure set. -/
theorem exists_angularRegion_borel_restart_quantitative (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ L : ℝ, 0 ≤ L →
            ∀ q P : ℝ, 3 < q → 4 < P → ∀ Bbound : ℝ, 0 < Bbound → ∃ dstar > (0 : ℝ),
              ∀ d ∈ Ioc (0 : ℝ) dstar,
                let F := angularFailureRegion h q d L P η J σ Bcap
                let C := 12 * L * logarithmicFluxConstantOne (angularFailureFluxConstant L σ) σ +
                  24 * L * P * Real.log 2
                MeasurableSet F ∧ mainWallMeasure h F ≤ ENNReal.ofReal (C * d * (1 + |Real.log d| + 2 * Real.log 2)) ∧
                mainWallMeasure h F ≠ ⊤ ∧
                ∃ W : SectionCoordinates → CoreRestartData, Measurable W ∧
                  ∀ z ∈ angularSection d L \ F, z ∈ mainWallChartDomain h ∧ (W z).2.1 ≤ Bbound ∧
                    CoreRestartWitness η J σ Bcap (mainWallChart h z) (W z) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartAngular_two_orders_dyadic hBirkhoff
  obtain ⟨hR, hhR, HR⟩ := exists_restartReturn_joint_regular
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, min hR (min hS (1 / 8)), lt_min hhR (lt_min hhS (by norm_num)), ?_⟩
  intro h hh L hL q P hq hP Bbound hBbound
  have hh' := hh.2.trans (min_le_right _ _)
  have hh1 : h ≤ 1 / 8 := hh'.trans (min_le_right _ _)
  obtain ⟨rR, hrR, HRR⟩ := HR h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL q P hq hP
  obtain ⟨dS, hdS, HdS⟩ := HS h ⟨hh.1, hh'.trans (min_le_left _ _)⟩ L hL q P hq hP
  let K := 51200 * (L + 1)
  have hK : 0 < K := by dsimp only [K]; positivity
  let d₀ := min rR (min dS (min (h / 16) (1 / (16 * (L + 1)))))
  refine ⟨min d₀ (min 1 (Bbound / K)),
    lt_min (lt_min hrR (lt_min hdS (lt_min (div_pos hh.1 (by norm_num)) (by positivity))))
      (lt_min zero_lt_one (div_pos hBbound hK)), ?_⟩
  intro d hd₀ F Cflux
  have hd : d ∈ Ioc 0 d₀ := ⟨hd₀.1, hd₀.2.trans (min_le_left _ _)⟩
  have hd1 : d ≤ 1 := hd₀.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdB : K * d ≤ Bbound := by
    have H := (le_div_iff₀ hK).mp (hd₀.2.trans ((min_le_right _ _).trans (min_le_right _ _)))
    simpa only [mul_comm] using H
  have hd' := hd.2.trans (min_le_right _ _)
  have hd'' := hd'.trans (min_le_right _ _)
  have hdh : d ≤ h / 16 := hd''.trans (min_le_left _ _)
  have hLd : 2 * L * d ≤ 1 / 8 := by
    have H := (le_div_iff₀ (by positivity : 0 < 16 * (L + 1))).mp (hd''.trans (min_le_right _ _))
    nlinarith only [H, hd.1]
  obtain ⟨_, hS, _, HSbound, _, Hgood⟩ := HdS d ⟨hd.1, hd'.trans (min_le_left _ _)⟩
  obtain ⟨hU, _, HUbound, _⟩ := mainWallMeasure_angularUnselectedSection_dyadic
    hh.1 hh1 hd.1 hdh hL hLd (by linarith only [hP])
  let Kflux := 12 * L * logarithmicFluxConstantOne (angularFailureFluxConstant L σ) σ
  let Aflux := 24 * L * P * Real.log 2
  have hKflux : 0 ≤ Kflux := mul_nonneg (mul_nonneg (by norm_num) hL)
    (logarithmicFluxConstantOne_nonneg (angularFailureFluxConstant_ge_one hL hσ.le) hσ)
  have hAflux : 0 ≤ Aflux := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL)
    (by linarith only [hP])) (Real.log_nonneg (by norm_num))
  have hweight : 0 ≤ 1 + |Real.log d| + 2 * Real.log 2 :=
    by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); positivity
  have HU' : mainWallMeasure h (⋃ j : ℕ, angularUnselectedSection (dyadicScale d j) L P) ≤
      ENNReal.ofReal (Aflux * d * (1 + |Real.log d| + 2 * Real.log 2)) :=
    HUbound.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hAflux hd.1.le)))
  have Hbound : mainWallMeasure h F ≤ ENNReal.ofReal (Cflux * d * (1 + |Real.log d| + 2 * Real.log 2)) := calc
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (Kflux * d * (1 + |Real.log d| + 2 * Real.log 2)) +
        ENNReal.ofReal (Aflux * d * (1 + |Real.log d| + 2 * Real.log 2)) := add_le_add HSbound HU'
    _ = _ := by
      rw [← ENNReal.ofReal_add (mul_nonneg (mul_nonneg hKflux hd.1.le) hweight)
        (mul_nonneg (mul_nonneg hAflux hd.1.le) hweight)]
      congr 1
      change Kflux * d * _ + Aflux * d * _ = (Kflux + Aflux) * d * _
      ring
  let D : ℕ × Bool → Set ((ℝ × ℝ) × ℝ) := fun i => angularRestartParameterDomain (dyadicScale d i.1) L P
  let C : ℕ × Bool → ((ℝ × ℝ) × ℝ) → SectionCoordinates := fun i => angularRestartChart i.2
  let G : ℕ × Bool → ((ℝ × ℝ) × ℝ) → CoreRestartData := fun i =>
    angularRestartData h (q / 2 * Real.log (1 / dyadicScale d i.1)) (dyadicScale d i.1) L i.2
  have hreg (i : ℕ × Bool) (p : (ℝ × ℝ) × ℝ) (hp : p ∈ D i) :=
    HRR (dyadicScale d i.1)
      ⟨dyadicScale_pos hd.1 i.1, (dyadicScale_le hd.1.le i.1).trans (hd.2.trans (min_le_left _ _))⟩
      p.1.1 p.1.2 hp.1.1 hp.1.2 p.2 hp.2
  obtain ⟨W, hWm, HW⟩ := exists_measurable_chart_selection D C G
    (fun i => measurableSet_angularRestartParameterDomain _ _ _)
    (fun i => continuousOn_angularRestartChart (dyadicScale_pos hd.1 i.1) i.2)
    (fun i => injOn_angularRestartChart (dyadicScale_pos hd.1 i.1) i.2)
    (fun i => measurable_angularRestartData i.2 (fun p hp => (hreg i p hp).2.2.2.2)
      (fun p hp => (hreg i p hp).2.2.1))
  refine ⟨hS.union hU, Hbound, ne_top_of_le_ne_top ENNReal.ofReal_ne_top Hbound, W, hWm, ?_⟩
  intro z hz
  have hcover : z ∈ ⋃ i, C i '' D i := by
    have hannuli : z ∈ ⋃ j, angularSectionAnnulus (dyadicScale d j) L := by
      rw [← angularSection_dyadic_cover hd.1]
      exact hz.1
    obtain ⟨j, hj⟩ := mem_iUnion.mp hannuli
    have hn : z ∉ angularUnselectedSection (dyadicScale d j) L P :=
      fun hbad => hz.2 (Or.inr (mem_iUnion_of_mem j hbad))
    obtain ⟨θ, ζ, ρ, hθ, hζ, hρ, heq⟩ := angularSection_selected_representation hj hn
    rcases heq with heq | heq
    · exact mem_iUnion.mpr ⟨(j, false), ((θ, ζ), ρ), ⟨⟨hθ, hζ⟩, hρ⟩, heq.symm⟩
    · exact mem_iUnion.mpr ⟨(j, true), ((θ, ζ), ρ), ⟨⟨hθ, hζ⟩, hρ⟩, heq.symm⟩
  obtain ⟨⟨j, o⟩, v, hv, heq, hW⟩ := HW z hcover
  have hbudget : restartAmplitudeBudget L (dyadicScale d j) v.1.2 ≤ Bbound :=
    (restartAmplitudeBudget_le_scale hL (dyadicScale_pos hd.1 j)
      ((dyadicScale_le hd.1.le j).trans hd1) hP.le hv.1.2.2).trans
      ((mul_le_mul_of_nonneg_left (dyadicScale_le hd.1.le j) hK.le).trans hdB)
  have hn := fun hbad => hz.2 (Or.inl hbad)
  obtain ⟨hy, ht, hdom, Hstats⟩ := Hgood j v.1.1 v.1.2 hv.1.1 hv.1.2 v.2 hv.2
  rw [hW]
  subst z
  cases o
  · obtain ⟨p, hp, hstat, horbit, _⟩ := Hstats (Or.inl hn)
    refine ⟨hy, hbudget, ht, hdom, p, hp, hstat, ?_⟩
    change coreRadiusEntry p.val.2 = toProjectiveState (axisSwap _)
    rw [toProjectiveState_axisSwap]
    exact horbit
  · obtain ⟨p, hp, hstat, _, horbit⟩ := Hstats (Or.inr hn)
    have hy' : mainWallReflection ![v.1.1 * v.2, -Real.log v.2, -Real.log v.1.2] ∈ mainWallChartDomain h := by
      simpa only [mainWallChartDomain, mem_ofPred_eq, mainWallRadicand_reflection] using hy
    have hdom' := hdom
    rw [← normalizedMaxDomain_mainWallReflection h 0 ![v.1.1 * v.2, -Real.log v.2, -Real.log v.1.2]] at hdom'
    exact ⟨hy', hbudget, ht, hdom', p, hp, hstat, horbit⟩

/-- The selected time, frame, budget, and survivor state are jointly Borel on the full angular success region. -/
theorem exists_angularRegion_borel_restart (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ L : ℝ, 0 ≤ L →
            ∀ q P : ℝ, 3 < q → 4 < P → ∀ Bbound : ℝ, 0 < Bbound → ∃ dstar > (0 : ℝ),
              ∀ d ∈ Ioc (0 : ℝ) dstar,
                let F := angularFailureRegion h q d L P η J σ Bcap
                MeasurableSet F ∧ mainWallMeasure h F ≠ ⊤ ∧
                ∃ W : SectionCoordinates → CoreRestartData, Measurable W ∧
                  ∀ z ∈ angularSection d L \ F, z ∈ mainWallChartDomain h ∧ (W z).2.1 ≤ Bbound ∧
                    CoreRestartWitness η J σ Bcap (mainWallChart h z) (W z) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_angularRegion_borel_restart_quantitative hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, hS, hhS, ?_⟩
  intro h hh L hL q P hq hP Bbound hBbound
  obtain ⟨dS, hdS, HdS⟩ := HS h hh L hL q P hq hP Bbound hBbound
  refine ⟨dS, hdS, ?_⟩
  intro d hd
  obtain ⟨hF, _, H⟩ := HdS d hd
  exact ⟨hF, H⟩

end BianchiIX
