import BianchiIX.Statistics.EraTreeRealization
import BianchiIX.Statistics.EraBudget

noncomputable section

namespace BianchiIX

open Set

namespace EraSurvivor

def phase {η σ Bcap : ℝ} {J : ℕ} (p : eraSurvivorDomain η J σ Bcap) (n : ℕ) : ℝ :=
  2 / (eraPrefixState η J (word p n) p.val).2 0

def curveTypicalSet (Γ : EraCurve) (η : ℝ) (J : ℕ) (σ B Bcap : ℝ) : Set ℝ :=
  Ioo 0 1 ∩ (fun x => (B, Γ.state (2 / x))) ⁻¹' typicalDomain η J σ Bcap

end EraSurvivor

namespace EraCurve.Realization

variable {Γ : EraCurve} {η σ B Bcap : ℝ} {J : ℕ} {T : InverseBranchTree}
variable (R : Γ.Realization η J σ B Bcap T)

include R

theorem word_eq_tree (x : T.survivors) (p : eraSurvivorDomain η J σ Bcap)
    (hp : p.val = (B, Γ.state (2 / x.val))) (n : ℕ) : EraSurvivor.word p n = T.word x n := by
  apply (EraSurvivor.word_eq_iff p (T.word_length x n)).mpr
  rw [hp]
  exact (R.prefix_domain_iff_cell _ _ (T.survivors_subset_root x.property)).mpr (T.mem_word_cell x n)

theorem digits_eq_tree (x : T.survivors) (p : eraSurvivorDomain η J σ Bcap)
    (hp : p.val = (B, Γ.state (2 / x.val))) : EraSurvivor.digits p = T.digits x := by
  funext n
  have heq := (EraSurvivor.word_succ p n).symm.trans
    ((R.word_eq_tree x p hp (n + 1)).trans (T.word_succ x n))
  rw [R.word_eq_tree x p hp n] at heq
  exact List.singleton_inj.mp (List.append_inj_right heq rfl)

theorem code_eq_tree (x : T.survivors) (p : eraSurvivorDomain η J σ Bcap)
    (hp : p.val = (B, Γ.state (2 / x.val))) : EraSurvivor.code p = T.code x := by
  exact congrArg gaussCode (R.digits_eq_tree x p hp)

theorem phase_eq_tree (x : T.survivors) (p : eraSurvivorDomain η J σ Bcap)
    (hp : p.val = (B, Γ.state (2 / x.val))) : EraSurvivor.phase p = T.phase x := by
  funext n
  unfold EraSurvivor.phase
  rw [R.word_eq_tree x p hp n, hp]
  have hs := R.prefix_state (T.word x n) (T.phase x n) (T.phase_mem_terminal x n)
  rw [T.toRoot_phase] at hs
  rw [hs]
  change 2 / (2 / T.phase x n) = T.phase x n
  field_simp

theorem curveTypicalSet_eq : EraSurvivor.curveTypicalSet Γ η J σ B Bcap = T.typicalSurvivors := by
  ext x
  constructor
  · intro hx
    have hxroot : x ∈ T.root := by rw [R.root]; exact hx.1
    have hs := EraSurvivor.typicalDomain_subset hx.2
    let xt : T.survivors := ⟨x, (R.survivor_iff x hxroot).mp hs⟩
    let p : eraSurvivorDomain η J σ Bcap := ⟨(B, Γ.state (2 / x)), hs⟩
    apply (T.mem_typicalSurvivors xt).mpr
    rw [← R.code_eq_tree xt p rfl]
    exact (EraSurvivor.mem_typicalDomain p).mp hx.2
  · intro hx
    let xt : T.survivors := ⟨x, T.typicalSurvivors_subset hx⟩
    have hxroot : x ∈ T.root := T.survivors_subset_root xt.property
    let p : eraSurvivorDomain η J σ Bcap := ⟨(B, Γ.state (2 / x)), (R.survivor_iff x hxroot).mpr xt.property⟩
    refine ⟨by rwa [← R.root], ?_⟩
    apply (EraSurvivor.mem_typicalDomain p).mpr
    rw [R.code_eq_tree xt p rfl]
    exact (T.mem_typicalSurvivors xt).mp hx

end EraCurve.Realization
end BianchiIX
