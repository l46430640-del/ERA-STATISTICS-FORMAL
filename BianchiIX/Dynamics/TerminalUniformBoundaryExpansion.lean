import BianchiIX.Dynamics.TerminalJointBoundaryReciprocal
import BianchiIX.Analysis.CompactWallRemainder

noncomputable section

namespace BianchiIX

open Filter Asymptotics Set
open scoped Topology

/-- The complete compact-uniform statement of (D.40), on a common domain of actual tail and entrance events. -/
theorem terminalConnection_boundary_expansions_uniform {K : Set ℝ}
    (hK : IsCompact K) (hKR : K ⊆ Ioo 2 4) {η : ℝ} {J : ℕ}
    (hη : 0 < η ∧ η ≤ 1 / 40000) (hJ : 2 ≤ J) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ R ∈ K, ∀ u w : ℝ, 0 < u → 0 < w → u + w < δ →
      let α := (R - 2) / 2
      let h := η * α ^ J
      let Y : ExitTailState := ![R, u, w]
      coreTailValid h Y ∧ entranceReturnValid (terminalCyclicInput h Y) ∧
        |2 / terminalConnectionPhase h Y - α + u / R| ≤ ε * (u + w) ∧
        |terminalConnectionPhase h Y - 2 / α - 2 * u / (R * α ^ 2)| ≤ ε * (u + w) := by
  classical
  by_cases hne : K.Nonempty
  swap
  · refine ⟨1, by norm_num, ?_⟩
    intro R hR
    exact (hne ⟨R, hR⟩).elim
  let F₁ := fun R u w => 2 / terminalConnectionPhase (η * ((R - 2) / 2) ^ J) ![R, u, w] -
    (R - 2) / 2 + u / R
  let F₂ := fun R u w => terminalConnectionPhase (η * ((R - 2) / 2) ^ J) ![R, u, w] -
    2 / ((R - 2) / 2) - 2 * u / (R * ((R - 2) / 2) ^ 2)
  have H₁ : ∃ δ > (0 : ℝ), ∀ R ∈ K, ∀ u w : ℝ, 0 < u → 0 < w → u + w < δ →
      |F₁ R u w| ≤ ε * (u + w) := by
    apply compact_wall_remainder_uniform hK _ hε
    intro R₀ hR₀ R u w hR hu hw hp
    exact (terminalConnection_moving_boundary_expansions (hKR hR₀) hη hJ hR hu hw
      (Eventually.of_forall hp)).1
  have H₂ : ∃ δ > (0 : ℝ), ∀ R ∈ K, ∀ u w : ℝ, 0 < u → 0 < w → u + w < δ →
      |F₂ R u w| ≤ ε * (u + w) := by
    apply compact_wall_remainder_uniform hK _ hε
    intro R₀ hR₀ R u w hR hu hw hp
    exact (terminalConnection_moving_boundary_expansions (hKR hR₀) hη hJ hR hu hw
      (Eventually.of_forall hp)).2
  obtain ⟨δ₁, hδ₁, HE₁⟩ := H₁
  obtain ⟨δ₂, hδ₂, HE₂⟩ := H₂
  obtain ⟨Rmin, hRmin, Hmin⟩ := hK.exists_isMinOn hne continuous_id.continuousOn
  let αmin := (Rmin - 2) / 2
  have hαmin : 0 < αmin := div_pos (sub_pos.mpr (hKR hRmin).1) (by norm_num)
  obtain ⟨b₀, hb₀, HV⟩ := exists_terminal_connection_height_interval
    (by norm_num : 0 < (1 / 10000 : ℝ) ∧ (1 / 10000 : ℝ) ≤ 1 / 10000)
    ⟨hη.1, by linarith only [hη.2]⟩ (q := 0) (by omega : 0 + 2 ≤ J)
  refine ⟨min (min δ₁ δ₂) (b₀ * αmin ^ (2 * J)),
    lt_min (lt_min hδ₁ hδ₂) (mul_pos hb₀ (pow_pos hαmin _)), ?_⟩
  intro R hR u w hu hw hsmall α h Y
  have ha : 0 < α ∧ α ≤ 1 := by
    dsimp only [α]
    have HR := hKR hR
    constructor <;> linarith only [HR.1, HR.2]
  have hamin : αmin ≤ α := by
    have H : Rmin ≤ R := Hmin hR
    dsimp only [αmin, α]
    linarith only [H]
  have hbudget : u + w ≤ b₀ * α ^ (2 * J) :=
    ((hsmall.trans_le (min_le_right _ _)).le).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hαmin.le hamin _) hb₀.le)
  have Hvalid := HV η α (u + w) u w le_rfl (by linarith only [hη.2])
    (by norm_num; exact hη.2) ha (add_pos hu hw) hbudget (by rw [abs_of_pos hu, abs_of_pos hw]) hu hw
  have HR : 2 + 2 * α = R := by dsimp only [α]; ring
  rw [HR] at Hvalid
  exact ⟨Hvalid.1, Hvalid.2.1,
    HE₁ R hR u w hu hw (hsmall.trans_le ((min_le_left _ _).trans (min_le_left _ _))),
    HE₂ R hR u w hu hw (hsmall.trans_le ((min_le_left _ _).trans (min_le_right _ _)))⟩

end BianchiIX
