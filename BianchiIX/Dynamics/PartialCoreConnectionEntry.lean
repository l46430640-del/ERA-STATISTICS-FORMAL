import BianchiIX.Dynamics.PartialCoreRadialCone
import BianchiIX.Dynamics.CoreConnectionBounds

noncomputable section

namespace BianchiIX

open Set

/-- Every positive-wall partial-core exit is an actual regular long-connection entrance. -/
theorem partialCore_firstReturn_connection_domain {k Z T ε : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2) (hZ : 0 ≤ Z) (hkZ : 2 * Real.cosh Z ≤ k)
    (hz : projectiveCoreAngle y ≤ Z) (hε : 0 < ε ∧ ε ≤ 1 / 10000)
    (hu : 0 < y 1 ∧ y 1 ≤ ε / k) (hp : 0 < y 2 * y 3 ∧ y 2 * y 3 ≤ ε / k)
    (hfirst : IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} T) :
    let out := projectiveOriginalFlow y 0 T
    let p := coreExitConnectionParameters (toCoreAngleState out)
    out = connectionEntry (p 0) (p 1) (p 2) ∧
      (4 ≤ p 0 ∧ k / 2 ≤ p 0 ∧ p 0 < k) ∧
      (0 < p 1 ∧ p 1 ≤ ε / p 0) ∧ (0 < p 2 ∧ p 2 ≤ ε) ∧
      p 1 ≤ y 1 * Real.exp (-k / 12) ∧ p 2 ≤ y 2 * y 3 ∧
      phaseNorm (p 0 + 1) 1 = coreRadius (out 0) (out 2) ∧
      0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 T 0 ∧
      connectionReturnValid p ∧ ContDiffAt ℝ 2 connectionReturnTime p ∧
      ContDiffAt ℝ 2 connectionReturnState p := by
  intro out p
  have hk0 : 0 < k := by linarith only [hk]
  obtain ⟨S, _, hfirstS, hreg, _⟩ := exists_partialCore_entry_variation hk hy hR hV
  have hST : S = T := hfirstS.unique hfirst
  rw [hST] at hreg
  have htm : T ∈ Icc 0 T := ⟨hfirst.1.1.le, le_rfl⟩
  have hr : coreRegion k out := (hreg T htm).2
  have hD := (coreRegion_clock_regular hk hy).1
  have hc := fromProjectiveState_constraint hD.ne'
  have hhit : out 2 = 1 := hfirst.1.2
  have hdown := normalized_core_return_downward hc hk le_rfl hfirst.1.1 (hreg T htm).1 hhit
    (fun t ht => (hreg t ⟨ht.1.le, ht.2.le⟩).2.2.1)
    (coreRegion_radius_bounds hk hr).1 (coreRegion_wall_bounds hr).1 (coreRegion_wall_bounds hr).2
  have hM : out 0 < 1 := hdown.1
  have heq : p = ![-out 0, out 1, out 3] := coreExitConnectionParameters_of_exit hM hhit
  have hμ := core_exit_connection_radial_range hk hM (by simpa only [hhit] using hr.1)
  have hentry : out = connectionEntry (p 0) (p 1) (p 2) := by
    rw [heq]
    ext i
    fin_cases i <;> simp [connectionEntry, hhit]
  have hpos (i : Fin 3) (hi : 0 < y i.succ) : 0 < out i.succ := by
    apply normalized_projective_wall_pos (initial_mem_normalizedMaxDomain _ 0)
      (normalizedMaxDomain_contains_Ici_of_constraint hc 0 hfirst.1.1.le)
      (hreg 0 ⟨le_rfl, hfirst.1.1.le⟩).1 (hreg T htm).1 i
    change 0 < projectiveOriginalFlow y 0 0 i.succ
    rw [projectiveOriginalFlow_initial hD]
    exact hi
  have huout : 0 < out 1 := hpos 0 hu.1
  have hpout : 0 < out 3 := hpos 2 ((mul_pos_iff_of_pos_left (zero_lt_one.trans hV)).mp hp.1)
  have HC := partialCore_firstReturn_contraction hk hy hR hV hZ hkZ hz hfirst
  have huexp : y 1 * Real.exp (-k / 12) ≤ y 1 :=
    mul_le_of_le_one_right hu.1.le (Real.exp_le_one_iff.mpr (by linarith only [hk]))
  have hdomainU : 0 < p 1 ∧ p 1 ≤ ε / p 0 := by
    change 0 < out 1 ∧ out 1 ≤ ε / (p 0)
    refine ⟨huout, (HC.1.trans huexp).trans (hu.2.trans ?_)⟩
    rw [heq]
    exact div_le_div_of_nonneg_left hε.1.le (by simpa using lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) hμ.1) hμ.2.2.le
  have hdomainP : 0 < p 2 ∧ p 2 ≤ ε := by
    change 0 < out 2 * out 3 ∧ out 2 * out 3 ≤ ε
    rw [hhit, one_mul]
    exact ⟨hpout, HC.2.trans (hp.2.trans (div_le_self hε.1.le (by linarith only [hk])))⟩
  have hμp : 4 ≤ p 0 ∧ k / 2 ≤ p 0 ∧ p 0 < k := by simpa only [heq, Matrix.cons_val_zero] using hμ
  have HR := connectionReturn_regular hμp.1
    ⟨hdomainU.1.le, hdomainU.2.trans (div_le_div_of_nonneg_right hε.2 (by linarith only [hμp.1]))⟩
    ⟨hdomainP.1, hdomainP.2.trans hε.2⟩
  refine ⟨hentry, hμp, hdomainU, hdomainP, ?_, ?_, ?_, (hreg T htm).1, HR.1, HR.2.1, HR.2.2.1⟩
  · exact HC.1
  · change out 2 * out 3 ≤ y 2 * y 3
    rw [hhit, one_mul]
    exact HC.2
  · apply coreExitConnectionParameters_phase
    exact lt_of_lt_of_le (by linarith only [hk] : 1 < 99 / 100 * k) (coreRegion_radius_bounds hk hr).1

end BianchiIX
