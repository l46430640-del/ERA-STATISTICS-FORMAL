import BianchiIX.Measure.AngularFailureOrdersDyadic
import BianchiIX.Measure.AngularUnselectedFlux
import BianchiIX.Measure.AngularSectionGeometry
import BianchiIX.Statistics.PhysicalFuture

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def angularFailureRegion (h q d L P η : ℝ) (J : ℕ) (σ Bcap : ℝ) : Set SectionCoordinates :=
  (⋃ j : ℕ, mainWallSymmetrization (restartAngularFailureSection h
    (q / 2 * Real.log (1 / dyadicScale d j)) (dyadicScale d j) L P η J σ Bcap)) ∪
  ⋃ j : ℕ, angularUnselectedSection (dyadicScale d j) L P

/-- Outside one finite-flux Borel set, every point of the full bounded-angle section reaches a statistical core on its exact orbit. -/
theorem exists_angularRegion_statistics (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ L : ℝ, 0 ≤ L →
            ∀ q P : ℝ, 3 < q → 4 < P → ∃ dstar > (0 : ℝ),
              ∀ d ∈ Ioc (0 : ℝ) dstar,
                let F := angularFailureRegion h q d L P η J σ Bcap
                let C := 12 * L * logarithmicFluxConstantOne (angularFailureFluxConstant L σ) σ +
                  24 * L * P * Real.log 2
                MeasurableSet F ∧ mainWallMeasure h F ≤ ENNReal.ofReal (C * d * (1 + |Real.log d| + 2 * Real.log 2)) ∧
                  mainWallMeasure h F ≠ ⊤ ∧
                  ∀ z ∈ angularSection d L \ F,
                    z ∈ mainWallChartDomain h ∧ StatisticalCoreFuture η J σ Bcap (mainWallChart h z) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartAngular_two_orders_dyadic hBirkhoff
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, min hS (1 / 8), lt_min hhS (by norm_num), ?_⟩
  intro h hh L hL q P hq hP
  obtain ⟨dS, hdS, HdS⟩ := HS h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ L hL q P hq hP
  refine ⟨min dS (min (h / 16) (1 / (16 * (L + 1)))),
    lt_min hdS (lt_min (div_pos hh.1 (by norm_num)) (by positivity)), ?_⟩
  intro d hd F C
  have hh1 : h ≤ 1 / 8 := hh.2.trans (min_le_right _ _)
  have hdh : d ≤ h / 16 := hd.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hLd : 2 * L * d ≤ 1 / 8 := by
    have H := (le_div_iff₀ (by positivity : 0 < 16 * (L + 1))).mp
      (hd.2.trans ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith only [H, hd.1]
  let S := ⋃ j : ℕ, mainWallSymmetrization (restartAngularFailureSection h
    (q / 2 * Real.log (1 / dyadicScale d j)) (dyadicScale d j) L P η J σ Bcap)
  let U := ⋃ j : ℕ, angularUnselectedSection (dyadicScale d j) L P
  let K := 12 * L * logarithmicFluxConstantOne (angularFailureFluxConstant L σ) σ
  let A := 24 * L * P * Real.log 2
  obtain ⟨_, hS, _, HSbound, _, Hgood⟩ := HdS d ⟨hd.1, hd.2.trans (min_le_left _ _)⟩
  obtain ⟨hU, _, HUbound, _⟩ := mainWallMeasure_angularUnselectedSection_dyadic hh.1 hh1 hd.1 hdh hL hLd (by linarith : 0 ≤ P)
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (by norm_num) hL)
    (logarithmicFluxConstantOne_nonneg (angularFailureFluxConstant_ge_one hL hσ.le) hσ)
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) (by linarith)) hlog
  have hW : 0 ≤ 1 + |Real.log d| + 2 * Real.log 2 := by positivity
  have HU' : mainWallMeasure h U ≤ ENNReal.ofReal (A * d * (1 + |Real.log d| + 2 * Real.log 2)) :=
    HUbound.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hA hd.1.le)))
  have Hbound : mainWallMeasure h F ≤ ENNReal.ofReal (C * d * (1 + |Real.log d| + 2 * Real.log 2)) := calc
    _ ≤ mainWallMeasure h S + mainWallMeasure h U := measure_union_le S U
    _ ≤ ENNReal.ofReal (K * d * (1 + |Real.log d| + 2 * Real.log 2)) +
        ENNReal.ofReal (A * d * (1 + |Real.log d| + 2 * Real.log 2)) := add_le_add HSbound HU'
    _ = _ := by
      rw [← ENNReal.ofReal_add (mul_nonneg (mul_nonneg hK hd.1.le) hW)
        (mul_nonneg (mul_nonneg hA hd.1.le) hW)]
      congr 1
      change K * d * _ + A * d * _ = (K + A) * d * _
      ring
  refine ⟨hS.union hU, Hbound, ne_top_of_le_ne_top ENNReal.ofReal_ne_top Hbound, ?_⟩
  intro z hz
  have hcover : z ∈ ⋃ j : ℕ, angularSectionAnnulus (dyadicScale d j) L := by
    rw [← angularSection_dyadic_cover hd.1]
    exact hz.1
  obtain ⟨j, hj⟩ := mem_iUnion.mp hcover
  have hzS : z ∉ S := fun hbad => hz.2 (Or.inl hbad)
  have hzU : z ∉ angularUnselectedSection (dyadicScale d j) L P :=
    fun hbad => hz.2 (Or.inr (mem_iUnion_of_mem j hbad))
  obtain ⟨θ, ζ, ρ, hθ, hζ, hρ, hzcoord⟩ := angularSection_selected_representation hj hzU
  obtain ⟨hy, ht, hdom, Hstats⟩ := Hgood j θ ζ hθ hζ ρ hρ
  rcases hzcoord with heq | heq
  · subst z
    obtain ⟨p, _, hstat, horbit, _⟩ := Hstats (Or.inl hzS)
    exact ⟨hy, statisticalCoreFuture_of_entry_or_reflection ht hdom hstat (Or.inr horbit)⟩
  · subst z
    obtain ⟨p, _, hstat, _, horbit⟩ := Hstats (Or.inr hzS)
    have hy' : mainWallReflection ![θ * ρ, -Real.log ρ, -Real.log ζ] ∈ mainWallChartDomain h := by
      simpa only [mainWallChartDomain, mem_ofPred_eq, mainWallRadicand_reflection] using hy
    have hdom' := hdom
    rw [← normalizedMaxDomain_mainWallReflection h 0 ![θ * ρ, -Real.log ρ, -Real.log ζ]] at hdom'
    exact ⟨hy', statisticalCoreFuture_of_entry_or_reflection ht hdom' hstat (Or.inl horbit)⟩

end BianchiIX
