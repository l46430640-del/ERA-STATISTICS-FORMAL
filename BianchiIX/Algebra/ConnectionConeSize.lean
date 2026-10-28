import BianchiIX.Algebra.CoreConeSize
import BianchiIX.Analysis.ConnectionEndpointScales

noncomputable section

namespace BianchiIX

theorem sqrt_exp_half (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
  apply (Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos x).le (Real.exp_pos (x / 2)).le).mpr
  rw [← Real.exp_add, add_halves]

theorem sqrt_le_sqrt_mul_exp_half {U u x : ℝ} (hu : 0 ≤ u) (hU : U ≤ u * Real.exp x) :
    Real.sqrt U ≤ Real.sqrt u * Real.exp (x / 2) := by
  simpa only [Real.sqrt_mul hu, sqrt_exp_half] using Real.sqrt_le_sqrt hU

theorem connection_cone_phase_size {μ ε u w : ℝ} (hμ : 4 ≤ μ) (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hu : 0 ≤ u ∧ u ≤ ε / μ) (hw : 0 ≤ w ∧ w ≤ ε) :
    2 * (u + w ^ 2) / μ + Real.sqrt u + (u + w) * Real.sqrt w ≤ 4 * Real.sqrt ε := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hue : u ≤ ε := hu.2.trans (div_le_self hε.1 (by linarith only [hμ]))
  have hsu := Real.sqrt_le_sqrt hue
  have hsw := Real.sqrt_le_sqrt hw.2
  have hse := Real.sqrt_nonneg ε
  have hes : ε ≤ Real.sqrt ε := by
    have hs1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε.2
    nlinarith only [Real.sq_sqrt hε.1, hs1, hse]
  have hw2 : w ^ 2 ≤ ε := by nlinarith only [hw.1, hw.2, hε.2]
  have hfirst : 2 * (u + w ^ 2) / μ ≤ Real.sqrt ε := by
    apply (div_le_iff₀ hμ0).mpr
    have H := mul_le_mul_of_nonneg_right hμ hse
    nlinarith only [hue, hw2, hes, H]
  have hlast : (u + w) * Real.sqrt w ≤ 2 * Real.sqrt ε := by
    exact (mul_le_mul (show u + w ≤ 2 by linarith only [hue, hw.2, hε.2]) hsw
      (Real.sqrt_nonneg w) (by norm_num)).trans_eq (by ring)
  linarith only [hfirst, hsu, hlast]

/-- The strong row is uniformly small even when the radial parameter is unbounded. -/
theorem connection_strong_cone_size {μ ε u w L : ℝ} (hμ : 4 ≤ μ) (hε : 0 ≤ ε ∧ ε ≤ 1)
    (hu : 0 < u ∧ u ≤ ε / μ) (hw : 0 < w ∧ w ≤ ε) (hL : 1 ≤ L) (hwexp : w = Real.exp (-L)) :
    (Real.sqrt u * Real.exp (-μ * L / 4)) *
      (274 * L + 9000 * (1 / u + L / μ) * Real.sqrt u + 32 * μ / w * Real.sqrt w) ≤ 20000 * Real.sqrt ε := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hue : u ≤ ε := hu.2.trans (div_le_self hε.1 (by linarith only [hμ]))
  have hsu := Real.sqrt_le_sqrt hue
  have hse := Real.sqrt_nonneg ε
  have hes : ε ≤ Real.sqrt ε := by
    have hs1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.mpr hε.2
    nlinarith only [Real.sq_sqrt hε.1, hs1, hse]
  let E := Real.exp (-μ * L / 4)
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hEw : E ≤ w := by rw [hwexp]; exact Real.exp_le_exp.mpr (by nlinarith only [hμ, hL0])
  have hLE : L * E ≤ 1 := by
    have H := affine_mul_exp_neg_le_one L
    have H' := mul_le_mul_of_nonneg_left hEw hL0
    rw [hwexp] at H'
    nlinarith only [H, H', Real.exp_pos (-L)]
  have hcross : μ * Real.exp ((-μ / 4 + 1 / 2) * L) ≤ 8 := by
    have hx : (-μ / 4 + 1 / 2) * L ≤ -μ / 8 := by nlinarith only [hμ, hL]
    have H := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx) hμ0.le
    have H' := affine_mul_exp_neg_le_one (μ / 8)
    rw [show -(μ / 8) = -μ / 8 by ring] at H'
    nlinarith only [H, H', Real.exp_pos (-μ / 8)]
  have hwroot : Real.sqrt w / w = Real.exp (L / 2) := by
    rw [hwexp, sqrt_exp_half, ← Real.exp_sub]
    congr 1
    ring
  have hjoin : E * (Real.sqrt w / w) = Real.exp ((-μ / 4 + 1 / 2) * L) := by
    change Real.exp (-μ * L / 4) * (Real.sqrt w / w) = _
    rw [hwroot, ← Real.exp_add]
    congr 1
    ring
  have hid : (Real.sqrt u * E) *
      (274 * L + 9000 * (1 / u + L / μ) * Real.sqrt u + 32 * μ / w * Real.sqrt w) =
      274 * Real.sqrt u * (L * E) + 9000 * E + 9000 * (u / μ) * (L * E) +
        32 * Real.sqrt u * (μ * Real.exp ((-μ / 4 + 1 / 2) * L)) := by
    rw [← hjoin]
    calc
      _ = 274 * Real.sqrt u * (L * E) + 9000 * ((Real.sqrt u) ^ 2 / u) * E +
          9000 * ((Real.sqrt u) ^ 2 / μ) * (L * E) + 32 * Real.sqrt u * (μ * (E * (Real.sqrt w / w))) := by ring
      _ = _ := by rw [Real.sq_sqrt hu.1.le, div_self (ne_of_gt hu.1)]; ring
  rw [hid]
  have H1 : 274 * Real.sqrt u * (L * E) ≤ 274 * Real.sqrt ε := by
    have H := mul_le_mul hsu hLE (mul_nonneg hL0 hE0) hse
    nlinarith only [H]
  have H2 : 9000 * E ≤ 9000 * Real.sqrt ε := mul_le_mul_of_nonneg_left (hEw.trans (hw.2.trans hes)) (by norm_num)
  have H3 : 9000 * (u / μ) * (L * E) ≤ 9000 * Real.sqrt ε := by
    have huq : u / μ ≤ Real.sqrt ε :=
      (div_le_self hu.1.le (by linarith only [hμ])).trans (hue.trans hes)
    have H := mul_le_mul huq hLE (mul_nonneg hL0 hE0) hse
    nlinarith only [H]
  have H4 : 32 * Real.sqrt u * (μ * Real.exp ((-μ / 4 + 1 / 2) * L)) ≤ 256 * Real.sqrt ε := by
    have H := mul_le_mul hsu hcross (by positivity) hse
    nlinarith only [H]
  nlinarith only [H1, H2, H3, H4, hse]

/-- The weak row retains an exponential margin on the entire long-connection region. -/
theorem connection_weak_cone_size {μ u w L : ℝ} (hμ : 4 ≤ μ) (hu : 0 ≤ u ∧ u ≤ 1)
    (hw : 0 < w) (hL : 256 ≤ L) (hsmall : 40000 * Real.sqrt w ≤ 1) :
    (Real.sqrt w * Real.exp (-L / μ)) *
      (274 * L / μ ^ 2 + 9000 * (1 + L) / μ ^ 2 * Real.sqrt u +
        (1 + 32 / μ) / w * Real.sqrt w) ≤ Real.exp (-L / (2 * μ)) := by
  have hμ0 : 0 < μ := by linarith only [hμ]
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hsu : Real.sqrt u ≤ 1 := Real.sqrt_le_one.mpr hu.2
  have hsw := Real.sqrt_nonneg w
  have hrow : 274 * L / μ ^ 2 + 9000 * (1 + L) / μ ^ 2 * Real.sqrt u ≤
      10000 * (1 + L) / μ ^ 2 := by
    have H := mul_le_mul_of_nonneg_left hsu (show 0 ≤ 9000 * (1 + L) / μ ^ 2 by positivity)
    have HH := div_le_div_of_nonneg_right (show 274 * L ≤ 1000 * (1 + L) by linarith only [hL0]) (sq_nonneg μ)
    calc
      _ ≤ 1000 * (1 + L) / μ ^ 2 + 9000 * (1 + L) / μ ^ 2 := by linarith only [H, HH]
      _ = _ := by ring
  have hsmall' : 10000 * Real.sqrt w ≤ 1 / 4 := by linarith only [hsmall]
  have hcorr : 32 / μ + 10000 * (1 + L) * Real.sqrt w / μ ^ 2 ≤ L / (4 * μ) := by
    have H := mul_le_mul_of_nonneg_left hsmall' (show 0 ≤ 1 + L by positivity)
    apply (le_div_iff₀ (by positivity : 0 < 4 * μ)).mpr
    field_simp
    have Hμ := mul_le_mul_of_nonneg_left hμ hL0
    nlinarith only [H, Hμ, hL, hμ]
  have hid : (Real.sqrt w * Real.exp (-L / μ)) *
      (274 * L / μ ^ 2 + 9000 * (1 + L) / μ ^ 2 * Real.sqrt u +
        (1 + 32 / μ) / w * Real.sqrt w) =
      Real.exp (-L / μ) * (1 + 32 / μ + Real.sqrt w *
        (274 * L / μ ^ 2 + 9000 * (1 + L) / μ ^ 2 * Real.sqrt u)) := by
    calc
      _ = Real.exp (-L / μ) * ((1 + 32 / μ) * ((Real.sqrt w) ^ 2 / w) +
        Real.sqrt w * (274 * L / μ ^ 2 + 9000 * (1 + L) / μ ^ 2 * Real.sqrt u)) := by ring
      _ = _ := by rw [Real.sq_sqrt hw.le, div_self (ne_of_gt hw)]; ring
  rw [hid]
  have Hb : 1 + 32 / μ + Real.sqrt w *
      (274 * L / μ ^ 2 + 9000 * (1 + L) / μ ^ 2 * Real.sqrt u) ≤ 1 + L / (4 * μ) := by
    have H := mul_le_mul_of_nonneg_left hrow hsw
    have HH : Real.sqrt w * (10000 * (1 + L) / μ ^ 2) = 10000 * (1 + L) * Real.sqrt w / μ ^ 2 := by ring
    rw [HH] at H
    linarith only [H, hcorr]
  calc
    _ ≤ Real.exp (-L / μ) * (1 + L / (4 * μ)) := mul_le_mul_of_nonneg_left Hb (Real.exp_pos _).le
    _ ≤ Real.exp (-L / μ) * Real.exp (L / (4 * μ)) :=
      mul_le_mul_of_nonneg_left (by linarith only [Real.add_one_le_exp (L / (4 * μ))]) (Real.exp_pos _).le
    _ = Real.exp (-3 * L / (4 * μ)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-L / (2 * μ)) := Real.exp_le_exp.mpr (by apply (div_le_div_iff₀ (by positivity : 0 < 4 * μ) (by positivity : 0 < 2 * μ)).mpr; nlinarith only [hL0, hμ0])

end BianchiIX
