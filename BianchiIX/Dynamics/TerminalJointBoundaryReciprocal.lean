import BianchiIX.Dynamics.TerminalJointBoundaryExpansion

noncomputable section

namespace BianchiIX

open Filter Asymptotics
open scoped Topology

theorem terminalConnectionPhase_joint_reciprocal_expansion {ι : Type*} {l : Filter ι}
    {α ξ u w : ι → ℝ} {α₀ ξ₀ : ℝ} (hα₀ : 0 < α₀ ∧ α₀ < 1)
    (hξ₀ : 0 < ξ₀ ∧ ξ₀ ≤ 1 / 40000)
    (hα : Tendsto α l (𝓝 α₀)) (hξ : Tendsto ξ l (𝓝 ξ₀))
    (hu : Tendsto u l (𝓝 0)) (hw : Tendsto w l (𝓝 0))
    (hpos : ∀ᶠ x in l, ξ x ≤ 1 / 40000 ∧ 0 < u x ∧ 0 < w x) :
    (fun x => terminalConnectionPhase (ξ x * α x ^ 2) ![2 + 2 * α x, u x, w x] - 2 / α x -
      2 * u x / ((2 + 2 * α x) * α x ^ 2)) =o[l] (fun x => u x + w x) := by
  let R := fun x => 2 + 2 * α x
  let R₀ := 2 + 2 * α₀
  let f := fun x => 2 / terminalConnectionPhase (ξ x * α x ^ 2) ![R x, u x, w x]
  have HE : (fun x => f x - α x + u x / R x) =o[l] (fun x => u x + w x) :=
    terminalConnectionPhase_joint_boundary_expansion hα₀ hξ₀ hα hξ hu hw hpos
  have hR₀ : R₀ ≠ 0 := by dsimp only [R₀]; linarith only [hα₀.1]
  have HR : Tendsto R l (𝓝 R₀) := (hα.const_mul 2).const_add 2
  have HI : Tendsto (fun x => 1 / R x) l (𝓝 (1 / R₀)) := tendsto_const_nhds.div HR hR₀
  have HQ : Tendsto (fun x => u x / R x) l (𝓝 0) := by
    simpa only [div_eq_mul_inv, one_mul, zero_mul] using hu.mul HI
  have HF : Tendsto f l (𝓝 α₀) := by
    have H := ((HE.tendsto_zero_of_tendsto (hu.add hw)).sub HQ).add hα
    simp only [sub_zero, zero_add] at H
    convert H using 1
    ext x
    ring
  have HU : u =O[l] (fun x => u x + w x) := by
    apply IsBigO.of_bound'
    filter_upwards [hpos] with x hx
    simp only [Real.norm_eq_abs, abs_of_pos hx.2.1, abs_of_pos (add_pos hx.2.1 hx.2.2)]
    exact le_add_of_nonneg_right hx.2.2.le
  have HQO : (fun x => u x / R x) =O[l] (fun x => u x + w x) := by
    simpa only [mul_one, div_eq_mul_inv, one_mul] using HU.mul (isBigO_const_of_tendsto HI (one_ne_zero : (1 : ℝ) ≠ 0))
  have HO : (fun x => f x - α x) =O[l] (fun x => u x + w x) := by
    apply (HE.isBigO.sub HQO).congr_left
    intro x
    ring
  have HD : HasStrictDerivAt (fun z : ℝ => 2 / z) (-2 / α₀ ^ 2) α₀ := by
    simpa [div_eq_mul_inv] using (hasStrictDerivAt_inv hα₀.1.ne').const_mul 2
  have HT := (HD.isLittleO.comp_tendsto (HF.prodMk_nhds hα)).trans_isBigO HO
  have HA : Tendsto (fun x => 1 / α x ^ 2) l (𝓝 (1 / α₀ ^ 2)) :=
    tendsto_const_nhds.div (hα.pow 2) (pow_ne_zero 2 hα₀.1.ne')
  have HK : Tendsto (fun x => (1 / α₀ ^ 2 - 1 / α x ^ 2) * (2 * (1 / R x))) l (𝓝 0) := by
    convert (HA.const_sub (1 / α₀ ^ 2)).mul (HI.const_mul 2) using 1; ring_nf
  have HKsmall : (fun x => (1 / α₀ ^ 2 - 1 / α x ^ 2) * (2 * (1 / R x))) =o[l] (fun _ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).mpr HK
  have Hcorr := HKsmall.mul_isBigO HU
  simp only [one_mul] at Hcorr
  apply ((HT.add (HE.const_mul_left (-2 / α₀ ^ 2))).add Hcorr).congr_left
  intro x
  have Hinv : 2 / f x = terminalConnectionPhase (ξ x * α x ^ 2) ![R x, u x, w x] := by dsimp only [f]; simp
  dsimp only [Function.comp_def]
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  rw [Hinv]
  simp only [div_mul_eq_div_div]
  dsimp only [R]
  ring

/-- Both remainders are little-o for jointly moving radii, at every prescribed auxiliary height power. -/
theorem terminalConnection_moving_boundary_expansions {ι : Type*} {l : Filter ι}
    {R u w : ι → ℝ} {R₀ η : ℝ} {J : ℕ}
    (hR₀ : 2 < R₀ ∧ R₀ < 4) (hη : 0 < η ∧ η ≤ 1 / 40000) (hJ : 2 ≤ J)
    (hR : Tendsto R l (𝓝 R₀)) (hu : Tendsto u l (𝓝 0)) (hw : Tendsto w l (𝓝 0))
    (hpos : ∀ᶠ x in l, 0 < u x ∧ 0 < w x) :
    let α := fun x => (R x - 2) / 2
    let h := fun x => η * α x ^ J
    ((fun x => 2 / terminalConnectionPhase (h x) ![R x, u x, w x] - α x + u x / R x)
      =o[l] (fun x => u x + w x)) ∧
    ((fun x => terminalConnectionPhase (h x) ![R x, u x, w x] - 2 / α x - 2 * u x / (R x * α x ^ 2))
      =o[l] (fun x => u x + w x)) := by
  intro α h
  let α₀ := (R₀ - 2) / 2
  let ξ := fun x => η * α x ^ (J - 2)
  let ξ₀ := η * α₀ ^ (J - 2)
  have hα₀ : 0 < α₀ ∧ α₀ < 1 := by dsimp only [α₀]; constructor <;> linarith only [hR₀.1, hR₀.2]
  have Hα : Tendsto α l (𝓝 α₀) := (hR.sub_const 2).div_const 2
  have Hξ : Tendsto ξ l (𝓝 ξ₀) := (Hα.pow (J - 2)).const_mul η
  have hξ₀ : 0 < ξ₀ ∧ ξ₀ ≤ 1 / 40000 :=
    ⟨mul_pos hη.1 (pow_pos hα₀.1 _),
      (mul_le_of_le_one_right hη.1.le (pow_le_one₀ hα₀.1.le hα₀.2.le)).trans hη.2⟩
  have HP : ∀ᶠ x in l, ξ x ≤ 1 / 40000 ∧ 0 < u x ∧ 0 < w x := by
    filter_upwards [hpos, Hα.eventually (lt_mem_nhds hα₀.1), Hα.eventually (gt_mem_nhds hα₀.2)] with x hx hxa hxb
    exact ⟨(mul_le_of_le_one_right hη.1.le (pow_le_one₀ hxa.le hxb.le)).trans hη.2, hx⟩
  have H1 := terminalConnectionPhase_joint_boundary_expansion hα₀ hξ₀ Hα Hξ hu hw HP
  have H2 := terminalConnectionPhase_joint_reciprocal_expansion hα₀ hξ₀ Hα Hξ hu hw HP
  have HR (x : ι) : 2 + 2 * α x = R x := by dsimp only [α]; ring
  have HH (x : ι) : ξ x * α x ^ 2 = h x := by
    dsimp only [ξ, h]
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hJ]
  exact ⟨H1.congr_left (fun x => by rw [HH, HR]), H2.congr_left (fun x => by rw [HH, HR])⟩

end BianchiIX
