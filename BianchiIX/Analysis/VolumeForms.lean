import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

noncomputable section

namespace BianchiIX

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι] [DecidableEq ι]

theorem basis_det_zero_of_covector (b : Module.Basis ι ℝ E) {l : E →ₗ[ℝ] ℝ}
    (hl : l ≠ 0) {v : ι → E} (hv : ∀ i, l (v i) = 0) : b.det v = 0 := by
  by_contra hdet
  have hspan := ((b.is_basis_iff_det).mpr (isUnit_iff_ne_zero.mpr hdet)).2
  have hker : Submodule.span ℝ (Set.range v) ≤ LinearMap.ker l :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hv i)
  apply hl
  ext x
  exact hker (by rw [hspan]; trivial)

/-- Contraction to a regular level set is independent of the normalized transverse vector. -/
theorem basis_det_cons_normal_independent {n : ℕ} (b : Module.Basis (Fin (n + 1)) ℝ E)
    {l : E →ₗ[ℝ] ℝ} {X Y : E} {v : Fin n → E}
    (hX : l X = 1) (hY : l Y = 1) (hv : ∀ i, l (v i) = 0) :
    b.det (Fin.cons Y v) = b.det (Fin.cons X v) := by
  have hl : l ≠ 0 := by intro hz; simp [hz] at hX
  have hz : b.det (Fin.cons (Y - X) v) = 0 := by
    apply basis_det_zero_of_covector b hl
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hX, hY]
    · exact hv j
  have H := b.det.map_update_add (Fin.cons X v) 0 (Y - X) X
  simpa only [Fin.update_cons_zero, sub_add_cancel, hz, zero_add] using H

omit [Fintype ι] in
theorem alternating_update_add_multiple (f : E [⋀^ι]→ₗ[ℝ] ℝ) (v : ι → E)
    {i j : ι} (hij : i ≠ j) (c : ℝ) :
    f (Function.update v i (v i + c • v j)) = f v := by
  rw [f.map_update_add, Function.update_eq_self, f.map_update_smul,
    f.map_update_self v hij, smul_zero, add_zero]

/-- Each moving-time contribution repeats the flow vector in an alternating volume. -/
theorem alternating_fin5_add_flow (f : E [⋀^Fin 5]→ₗ[ℝ] ℝ)
    (X F A B C : E) (a b c : ℝ) :
    f ![X, F, A + a • F, B + b • F, C + c • F] = f ![X, F, A, B, C] := by
  have h₂ : f ![X, F, A + a • F, B, C] = f ![X, F, A, B, C] := by
    convert! alternating_update_add_multiple f ![X, F, A, B, C]
      (i := 2) (j := 1) (by decide) a using 1
    congr 1
    ext i
    fin_cases i <;> simp
  have h₃ : f ![X, F, A + a • F, B + b • F, C] = f ![X, F, A + a • F, B, C] := by
    convert! alternating_update_add_multiple f ![X, F, A + a • F, B, C]
      (i := 3) (j := 1) (by decide) b using 1
    congr 1
    ext i
    fin_cases i <;> simp
  have h₄ : f ![X, F, A + a • F, B + b • F, C + c • F] =
      f ![X, F, A + a • F, B + b • F, C] := by
    convert! alternating_update_add_multiple f ![X, F, A + a • F, B + b • F, C]
      (i := 4) (j := 1) (by decide) c using 1
    congr 1
    ext i
    fin_cases i <;> simp
  exact h₄.trans (h₃.trans h₂)

end BianchiIX
