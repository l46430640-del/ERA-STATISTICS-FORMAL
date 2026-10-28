import BianchiIX.Measure.ShearSignedFailureDyadic
import BianchiIX.Measure.ShearSectionGeometry
import BianchiIX.Measure.ShearUnselectedFlux
import BianchiIX.Dynamics.ShearRestartSignedOrbit
import BianchiIX.Statistics.PhysicalFuture

noncomputable section

namespace BianchiIX

open Set MeasureTheory
open scoped ENNReal

def shearFailureRegion (h q d ε P η : ℝ) (J : ℕ) (σ Bcap : ℝ) : Set SectionCoordinates :=
  (⋃ j : ℕ, mainWallSymmetrization (restartShearCommonFailureSection h
    (q / 2 * Real.log (1 / dyadicScale d j)) (dyadicScale d j) ε P η J σ Bcap)) ∪
  ⋃ j : ℕ, shearUnselectedSection (dyadicScale d j) ε P

/-- Every point of the full shear-dominated region outside one finite-flux Borel set reaches a statistical core along its exact Einstein orbit. -/
theorem exists_shearRegion_statistics (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ),
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
            ∃ dstar > (0 : ℝ), ∀ d ∈ Ioc (0 : ℝ) dstar,
              ∀ ε : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
              let F := shearFailureRegion h q d ε P η J σ Bcap
              let C := 66 * logarithmicFluxConstant (shearFailureFluxConstant σ) σ + 132 * P ^ 2
              MeasurableSet F ∧ mainWallMeasure h F ≤ ENNReal.ofReal (C * d * (1 + |Real.log d|) ^ 2) ∧
                mainWallMeasure h F ≠ ⊤ ∧
                ∀ z ∈ shearSection d ε \ F,
                  z ∈ mainWallChartDomain h ∧ StatisticalCoreFuture η J σ Bcap (mainWallChart h z) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_restartShear_signed_physical_failure_dyadic hBirkhoff
  obtain ⟨hO, hhO, HO⟩ := exists_restartShear_signed_orbit
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, hcap, hcapone, hS, hhS, HS⟩ := Hδ η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨Bcap, hcap, hcapone, min hS (min hO (1 / 8)), lt_min hhS (lt_min hhO (by norm_num)), ?_⟩
  intro h hh q D P hq hD hP
  have hh' := hh.2.trans (min_le_right _ _)
  have hh1 : h ≤ 1 / 8 := hh'.trans (min_le_right _ _)
  obtain ⟨dS, hdS, HdS⟩ := HS h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aO, haO, HaO⟩ := HO h ⟨hh.1, hh'.trans (min_le_left _ _)⟩ q D P hq hD hP
  refine ⟨min dS (min aO (h / 8)), lt_min hdS (lt_min haO (div_pos hh.1 (by norm_num))), ?_⟩
  intro d hd ε hε F C
  have hdh : d ≤ h / 8 := hd.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdO : d ≤ aO := hd.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hε64 : 0 ≤ ε ∧ ε ≤ 1 / 64 := ⟨hε.1, hε.2.trans (by norm_num)⟩
  let S := ⋃ j : ℕ, mainWallSymmetrization (restartShearCommonFailureSection h
    (q / 2 * Real.log (1 / dyadicScale d j)) (dyadicScale d j) ε P η J σ Bcap)
  let U := ⋃ j : ℕ, shearUnselectedSection (dyadicScale d j) ε P
  let K := 66 * logarithmicFluxConstant (shearFailureFluxConstant σ) σ
  let A := 132 * P ^ 2
  obtain ⟨_, hS, _, HSbound, _, Hgood⟩ := HdS d ⟨hd.1, hd.2.trans (min_le_left _ _)⟩ ε hε
  obtain ⟨hU, _, HUbound, _⟩ := mainWallMeasure_shearUnselectedSection_dyadic hh.1 hh1 hd.1 hdh hε64
    (by linarith only [hD, hP] : 0 ≤ P)
  have hK : 0 ≤ K := mul_nonneg (by norm_num)
    (logarithmicFluxConstant_nonneg (shearFailureFluxConstant_ge_one hσ.le) hσ)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hW : 0 ≤ (1 + |Real.log d|) ^ 2 := sq_nonneg _
  have Hbound : mainWallMeasure h F ≤ ENNReal.ofReal (C * d * (1 + |Real.log d|) ^ 2) := calc
    _ ≤ mainWallMeasure h S + mainWallMeasure h U := measure_union_le S U
    _ ≤ ENNReal.ofReal (K * d * (1 + |Real.log d|) ^ 2) +
        ENNReal.ofReal (A * d * (1 + |Real.log d|) ^ 2) := add_le_add HSbound HUbound
    _ = _ := by
      rw [← ENNReal.ofReal_add (mul_nonneg (mul_nonneg hK hd.1.le) hW)
        (mul_nonneg (mul_nonneg hA hd.1.le) hW)]
      congr 1
      change K * d * _ + A * d * _ = (K + A) * d * _
      ring
  refine ⟨hS.union hU, Hbound, ne_top_of_le_ne_top ENNReal.ofReal_ne_top Hbound, ?_⟩
  intro z hz
  have hcover : z ∈ ⋃ j : ℕ, shearSectionAnnulus (dyadicScale d j) ε := by
    rw [← shearSection_dyadic_cover hd.1]
    exact hz.1
  obtain ⟨j, hj⟩ := mem_iUnion.mp hcover
  have hzS : z ∉ S := fun hbad => hz.2 (Or.inl hbad)
  have hzU : z ∉ shearUnselectedSection (dyadicScale d j) ε P :=
    fun hbad => hz.2 (Or.inr (mem_iUnion_of_mem j hbad))
  obtain ⟨τ, n₂, n₃, ρ, hτ, hl, hρ, rfl⟩ := shearSection_selected_representation hε.1 hj hzU
  obtain ⟨p, hp, hstat⟩ := Hgood j τ hτ n₂ n₃ hl ρ hρ hzS
  obtain ⟨hy, ht, hdom, ho⟩ := HaO (dyadicScale d j)
    ⟨dyadicScale_pos hd.1 j, (dyadicScale_le hd.1.le j).trans hdO⟩
    ε τ n₂ n₃ hε hτ hl.1 hl.2.1 hl.2.2 ρ hρ
  exact ⟨hy, statisticalCoreFuture_of_entry_or_reflection ht hdom hstat (by simpa only [hp] using ho)⟩

end BianchiIX
