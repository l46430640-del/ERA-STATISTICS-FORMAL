import BianchiIX.Dynamics.CoreConnectionChart
import BianchiIX.Dynamics.CoreConeInvariance
import BianchiIX.Algebra.CoreConnection

noncomputable section

namespace BianchiIX

open Set

def coreConnectionParameters (τ : CoreAngleState → ℝ) (Y : CoreAngleState) : ConnectionParameters :=
  coreExitConnectionParameters (coreReturnState τ Y)

def coreReflectionState (τ : CoreAngleState → ℝ) (Y : CoreAngleState) : CoreAngleState :=
  connectionReturnPhysicalState (coreConnectionParameters τ Y)

/-- Every admissible actual core exit lies in the long-connection entry domain. -/
theorem coreReturn_connection_data {Y : CoreAngleState} {τ : CoreAngleState → ℝ}
    (hk : 6 ≤ Y 0) (hu : 0 < Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0)
    (hw : 0 < Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0)
    (hfirst : IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2 = 1} (τ Y)) :
    let y := projectiveOriginalFlow (coreRadiusEntry Y) 0 (τ Y)
    let p := coreConnectionParameters τ Y
    y = connectionEntry (p 0) (p 1) (p 2) ∧
      (4 ≤ p 0 ∧ Y 0 / 2 ≤ p 0 ∧ p 0 < Y 0) ∧
      (0 < p 1 ∧ p 1 ≤ Y 1) ∧ (0 < p 2 ∧ p 2 ≤ Y 2) ∧
      |phaseNorm (p 0 + 1) 1 - Y 0| ≤ 16 / Y 0 * (Y 1 + Y 2 ^ 2) ∧
      0 < 1 + normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 (τ Y) 0 := by
  intro y p
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hu' : 0 ≤ Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0 := ⟨hu.1.le, hu.2⟩
  have hw' : 0 ≤ Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0 := ⟨hw.1.le, hw.2⟩
  obtain ⟨T, _, hfirstT, hreg, hm, _, _, hphase, hU, hW, _⟩ := exists_large_core_traversal hk hu' hw'
  have hT : T = τ Y := hfirstT.unique hfirst
  subst T
  have ht : τ Y ∈ Icc 0 (τ Y) := ⟨hfirst.1.1.le, le_rfl⟩
  have hr : coreRegion (Y 0) y := (hreg (τ Y) ht).2
  have hV : y 2 = 1 := hfirst.1.2
  have hM : y 0 < 1 := hm
  have hp : p = ![-y 0, y 1, y 3] := coreExitConnectionParameters_of_exit hM hV
  have hrange := core_exit_connection_radial_range hk hM (by simpa only [hV] using hr.1)
  have hentry : y = connectionEntry (p 0) (p 1) (p 2) := by
    rw [hp]
    ext i
    fin_cases i <;> simp [connectionEntry, hV]
  have hD := (coreRegion_clock_regular hk (coreRadiusEntry_region hk hu' hw')).1
  have hc := fromProjectiveState_constraint (ne_of_gt hD)
  have hpos (i : Fin 3) (hi : 0 < coreRadiusEntry Y i.succ) : 0 < y i.succ := by
    apply normalized_projective_wall_pos (initial_mem_normalizedMaxDomain _ 0)
      (normalizedMaxDomain_contains_Ici_of_constraint hc 0 hfirst.1.1.le)
      (hreg 0 ⟨le_rfl, hfirst.1.1.le⟩).1 (hreg (τ Y) ht).1 i
    change 0 < projectiveOriginalFlow (coreRadiusEntry Y) 0 0 i.succ
    rw [projectiveOriginalFlow_initial hD]
    exact hi
  have hUp : 0 < y 1 := hpos 0 hu.1
  have hWp : 0 < y 3 := hpos 2 hw.1
  have hUle : y 1 ≤ Y 1 := hU.trans ((mul_le_mul_of_nonneg_right
    (Real.exp_le_one_iff.mpr (by linarith only [hk] : -Y 0 / 40 ≤ 0)) hu.1.le).trans_eq (one_mul _))
  have hWle : y 3 ≤ Y 2 := hW.trans ((mul_le_mul_of_nonneg_right
    (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))) hw.1.le).trans_eq (one_mul _))
  have heq : phaseNorm (p 0 + 1) 1 = coreRadius (y 0) (y 2) := by
    rw [hp, hV]
    dsimp [phaseNorm, coreRadius, coreEnergy]
    congr 1
    ring
  refine ⟨hentry, ?_, ?_, ?_, ?_, (hreg (τ Y) ht).1⟩
  · simpa only [hp, Matrix.cons_val_zero] using hrange
  · exact ⟨hUp, hUle⟩
  · simpa [hp] using And.intro hWp hWle
  · rw [heq]
    exact hphase

theorem coreReturn_connection_domain {Y : CoreAngleState} {τ : CoreAngleState → ℝ} {ε : ℝ}
    (hk : 6 ≤ Y 0) (hε : 0 < ε ∧ ε ≤ 1 / 10000)
    (hu : 0 < Y 1 ∧ Y 1 ≤ ε / Y 0) (hw : 0 < Y 2 ∧ Y 2 ≤ ε / Y 0)
    (hfirst : IsLeast {t | 0 < t ∧ projectiveOriginalFlow (coreRadiusEntry Y) 0 t 2 = 1} (τ Y)) :
    let p := coreConnectionParameters τ Y
    4 ≤ p 0 ∧ (0 < p 1 ∧ p 1 ≤ ε / p 0) ∧ (0 < p 2 ∧ p 2 ≤ ε) := by
  intro p
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hu' : 0 < Y 1 ∧ Y 1 ≤ (1 / 10000) / Y 0 :=
    ⟨hu.1, hu.2.trans (div_le_div_of_nonneg_right hε.2 hk0.le)⟩
  have hw' : 0 < Y 2 ∧ Y 2 ≤ (1 / 10000) / Y 0 :=
    ⟨hw.1, hw.2.trans (div_le_div_of_nonneg_right hε.2 hk0.le)⟩
  obtain ⟨_, hμ, hpU, hpW, _⟩ := coreReturn_connection_data hk hu' hw' hfirst
  refine ⟨hμ.1, ⟨hpU.1, ?_⟩, ⟨hpW.1, ?_⟩⟩
  · exact hpU.2.trans (hu.2.trans (div_le_div_of_nonneg_left hε.1.le (by linarith only [hμ.1]) hμ.2.2.le))
  · exact hpW.2.trans (hw.2.trans (div_le_self hε.1.le (by linarith only [hk])))

end BianchiIX
