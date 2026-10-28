import BianchiIX.Analysis.ScalarLocalInverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section

namespace BianchiIX

open Set Filter
open scoped Topology

def intervalRadiusInverse (k : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ := Function.invFunOn k (Icc a b)

/-- The inverse on the closed radius interval has the correct one-sided derivatives at both ends. -/
theorem intervalRadiusInverse_control {k : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hk : ∀ x ∈ Icc a b, ContDiffAt ℝ 1 k x)
    (hd : ∀ x ∈ Icc a b, deriv k x < 0) :
    let J := Icc (k b) (k a)
    let g := intervalRadiusInverse k a b
    k b < k a ∧ k '' Icc a b = J ∧ LeftInvOn g k (Icc a b) ∧
      MapsTo g J (Icc a b) ∧ RightInvOn g k J ∧
      ∀ t ∈ J, HasDerivWithinAt g (deriv k (g t))⁻¹ J t := by
  intro J g
  have hc : ContinuousOn k (Icc a b) := fun x hx => (hk x hx).continuousAt.continuousWithinAt
  have hanti := strictAntiOn_of_deriv_neg (convex_Icc a b) hc
    (fun x hx => hd x (interior_subset hx))
  have himage : k '' Icc a b = J := hc.image_Icc_of_antitoneOn hab.le hanti.antitoneOn
  have hleft : LeftInvOn g k (Icc a b) := hanti.injOn.leftInvOn_invFunOn
  have honto : SurjOn k (Icc a b) J := by rw [← himage]; exact surjOn_image k (Icc a b)
  have hmaps : MapsTo g J (Icc a b) := honto.mapsTo_invFunOn
  have hright : RightInvOn g k J := honto.rightInvOn_invFunOn
  have hnear (x : ℝ) (hx : x ∈ Icc a b) :
      ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 1 k y ∧ deriv k y < 0 := by
    have hcder : ContinuousAt (deriv k) x :=
      ((hk x hx).derivWithin (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuousAt
    exact ((hk x hx).eventually (by norm_num)).and (hcder.eventually (gt_mem_nhds (hd x hx)))
  obtain ⟨l, u, hlu, hluG⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hnear a ⟨le_rfl, hab.le⟩)
  obtain ⟨v, w, hvw, hvwG⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hnear b ⟨hab.le, le_rfl⟩)
  have hgood (x : ℝ) (hx : x ∈ Ioo l w) : ContDiffAt ℝ 1 k x ∧ deriv k x < 0 := by
    by_cases hxa : x < a
    · exact hluG ⟨hx.1, hxa.trans hlu.2⟩
    by_cases hbx : b < x
    · exact hvwG ⟨hvw.1.trans hbx, hx.2⟩
    exact ⟨hk x ⟨le_of_not_gt hxa, le_of_not_gt hbx⟩, hd x ⟨le_of_not_gt hxa, le_of_not_gt hbx⟩⟩
  have hIS : Icc a b ⊆ Ioo l w := fun x hx => ⟨hlu.1.trans_le hx.1, hx.2.trans_lt hvw.2⟩
  have hantiS := strictAntiOn_of_deriv_neg (convex_Ioo l w)
    (fun x hx => (hgood x hx).1.continuousAt.continuousWithinAt)
    (fun x hx => (hgood x (interior_subset hx)).2)
  refine ⟨hanti ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab, himage, hleft, hmaps, hright, ?_⟩
  intro t ht
  obtain ⟨x, hx, rfl⟩ := (show t ∈ k '' Icc a b by rw [himage]; exact ht)
  obtain ⟨j, hj⟩ := exists_scalarLocalInverseAt (hk x hx) (hd x hx).ne
  have hjlim : Tendsto j (𝓝 (k x)) (𝓝 x) := by
    simpa only [ContinuousAt, hj.apply_base] using hj.contDiffAt.continuousAt
  have hjS : ∀ᶠ t in 𝓝 (k x), j t ∈ Ioo l w := hjlim.eventually (Ioo_mem_nhds (hIS hx).1 (hIS hx).2)
  have heq : g =ᶠ[𝓝[J] (k x)] j := by
    filter_upwards [self_mem_nhdsWithin, hjS.filter_mono nhdsWithin_le_nhds,
      hj.right_inverse.filter_mono nhdsWithin_le_nhds] with z hz hjz hrightz
    exact hantiS.injOn (hIS (hmaps hz)) hjz ((hright hz).trans hrightz.symm)
  rw [hleft hx]
  exact hj.hasDerivAt.hasDerivWithinAt.congr_of_eventuallyEq_of_mem heq ht

end BianchiIX
