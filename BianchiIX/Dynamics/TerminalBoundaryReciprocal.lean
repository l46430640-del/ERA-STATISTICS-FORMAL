import BianchiIX.Dynamics.TerminalBoundaryExpansion

noncomputable section

namespace BianchiIX

open Filter Asymptotics Set
open scoped Topology

theorem tendsto_terminalConnection_bounded_phase_boundary {ι : Type*} {l : Filter ι}
    {u w : ι → ℝ} {α η : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hη : 0 < η ∧ η ≤ 1 / 40000)
    (hu : Tendsto u l (𝓝 0)) (hw : Tendsto w l (𝓝 0))
    (hpos : ∀ᶠ x in l, 0 < u x ∧ 0 < w x) :
    Tendsto (fun x => 2 / terminalConnectionPhase (η * α ^ 2) ![2 + 2 * α, u x, w x]) l (𝓝 α) := by
  have HE := (terminalConnectionPhase_boundary_expansion hα hη hu hw hpos).tendsto_zero_of_tendsto (hu.add hw)
  have H := (HE.sub (hu.div_const (2 + 2 * α))).add_const α
  simp only [zero_div, sub_zero, zero_add] at H
  convert H using 1
  ext x
  ring

/-- Taking the reciprocal preserves the first-order remainder on arbitrary positive wall paths. -/
theorem terminalConnectionPhase_reciprocal_boundary_expansion {ι : Type*} {l : Filter ι}
    {u w : ι → ℝ} {α η : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hη : 0 < η ∧ η ≤ 1 / 40000)
    (hu : Tendsto u l (𝓝 0)) (hw : Tendsto w l (𝓝 0))
    (hpos : ∀ᶠ x in l, 0 < u x ∧ 0 < w x) :
    (fun x => terminalConnectionPhase (η * α ^ 2) ![2 + 2 * α, u x, w x] - 2 / α -
      2 * u x / ((2 + 2 * α) * α ^ 2)) =o[l] (fun x => u x + w x) := by
  let R := 2 + 2 * α
  let f := fun x => 2 / terminalConnectionPhase (η * α ^ 2) ![R, u x, w x]
  have HE : (fun x => f x - α + u x / R) =o[l] (fun x => u x + w x) :=
    terminalConnectionPhase_boundary_expansion hα hη hu hw hpos
  have HF : Tendsto f l (𝓝 α) := tendsto_terminalConnection_bounded_phase_boundary hα hη hu hw hpos
  have HU : u =O[l] (fun x => u x + w x) := by
    apply IsBigO.of_bound'
    filter_upwards [hpos] with x hx
    simp only [Real.norm_eq_abs, abs_of_pos hx.1, abs_of_pos (add_pos hx.1 hx.2)]
    exact le_add_of_nonneg_right hx.2.le
  have HDiv : (fun x => u x / R) =O[l] (fun x => u x + w x) := by
    simpa only [div_eq_mul_inv, mul_comm] using HU.const_mul_left R⁻¹
  have HO : (fun x => f x - α) =O[l] (fun x => u x + w x) := by
    apply (HE.isBigO.sub HDiv).congr_left
    intro x
    ring
  have HD : HasDerivAt (fun z : ℝ => 2 / z) (-2 / α ^ 2) α := by
    simpa [div_eq_mul_inv] using (hasDerivAt_inv hα.1.ne').const_mul 2
  have HT := (HD.isLittleO.comp_tendsto HF).trans_isBigO HO
  have H := HT.add (HE.const_mul_left (-2 / α ^ 2))
  apply H.congr_left
  intro x
  have Hinv : 2 / f x = terminalConnectionPhase (η * α ^ 2) ![R, u x, w x] := by
    dsimp only [f]
    simp
  dsimp only [Function.comp_def]
  simp only [smul_eq_mul]
  rw [Hinv]
  simp only [div_mul_eq_div_div]
  dsimp only [R]
  ring

/-- Both expansions of (D.40) hold in the two-variable positive-quadrant neighborhood at each fixed radius. -/
theorem terminalConnection_boundary_expansions {R η : ℝ} {J : ℕ}
    (hR : 2 < R ∧ R < 4) (hη : 0 < η ∧ η ≤ 1 / 40000) (hJ : 2 ≤ J) :
    let α := (R - 2) / 2
    let h := η * α ^ J
    let l := 𝓝[{p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2}] (0, 0)
    ((fun p : ℝ × ℝ => 2 / terminalConnectionPhase h ![R, p.1, p.2] - α + p.1 / R)
      =o[l] (fun p => p.1 + p.2)) ∧
    ((fun p : ℝ × ℝ => terminalConnectionPhase h ![R, p.1, p.2] - 2 / α - 2 * p.1 / (R * α ^ 2))
      =o[l] (fun p => p.1 + p.2)) := by
  intro α h l
  have hα : 0 < α ∧ α ≤ 1 := by dsimp only [α]; constructor <;> linarith only [hR.1, hR.2]
  have HR : 2 + 2 * α = R := by dsimp only [α]; ring
  let ηeff := η * α ^ (J - 2)
  have hηeff : 0 < ηeff ∧ ηeff ≤ 1 / 40000 :=
    ⟨mul_pos hη.1 (pow_pos hα.1 _),
      (mul_le_of_le_one_right hη.1.le (pow_le_one₀ hα.1.le hα.2)).trans hη.2⟩
  have Hheight : ηeff * α ^ 2 = h := by
    dsimp only [ηeff, h]
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hJ]
  have HU : Tendsto (fun p : ℝ × ℝ => p.1) l (𝓝 0) :=
    continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have HW : Tendsto (fun p : ℝ × ℝ => p.2) l (𝓝 0) :=
    continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have HP : ∀ᶠ p : ℝ × ℝ in l, 0 < p.1 ∧ 0 < p.2 := self_mem_nhdsWithin
  have H1 := terminalConnectionPhase_boundary_expansion hα hηeff HU HW HP
  have H2 := terminalConnectionPhase_reciprocal_boundary_expansion hα hηeff HU HW HP
  rw [HR, Hheight] at H1 H2
  exact ⟨H1, H2⟩

end BianchiIX
