import Metastability.SourceDefinitions
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Finite-particle attention coefficients and the cap-minimum estimate

The vector fields and all coefficients are the literal source definitions.
The final estimate is the algebraic local step in the cap-drift proof
(source equations `eq:eta-derivative-cap`–`eq:cap-internal-nonneg-v7`).
-/

noncomputable section
open Set
open scoped BigOperators RealInnerProductSpace

namespace Metastability.ModelBounds
variable {n d : ℕ}

theorem inner_bounds (x y : Source.Sphere d) : -1 ≤ ⟪x.val, y.val⟫ ∧ ⟪x.val, y.val⟫ ≤ 1 := by
  have h : |⟪x.val, y.val⟫| ≤ 1 := by
    simpa only [x.property, y.property, mul_one] using abs_real_inner_le_norm x.val y.val
  exact abs_le.mp h

theorem kernel_self (β : ℝ) (x : Source.Sphere d) :
    Real.exp (β * (⟪x.val, x.val⟫ - 1)) = 1 := by
  simp only [real_inner_self_eq_norm_sq, x.property, one_pow, sub_self, mul_zero, Real.exp_zero]

theorem normalization_ge_one (β : ℝ) (x : Source.Configuration n d) (i : Fin n) :
    1 ≤ ∑ k, Real.exp (β * (⟪(x i).val, (x k).val⟫ - 1)) := by
  calc
    1 = Real.exp (β * (⟪(x i).val, (x i).val⟫ - 1)) := (kernel_self β (x i)).symm
    _ ≤ _ := Finset.single_le_sum (f := fun k : Fin n =>
      Real.exp (β * (⟪(x i).val, (x k).val⟫ - 1)))
      (fun k _ => (Real.exp_pos _).le) (Finset.mem_univ i)

theorem coefficient_nonneg (model : Source.Model) (β : ℝ)
    (x : Source.Configuration n d) (i j : Fin n) :
    0 ≤ Source.coefficient model β x i j := by
  cases model <;> unfold Source.coefficient <;> positivity

theorem coefficient_le_kernel (model : Source.Model) (β : ℝ)
    (x : Source.Configuration n d) (i j : Fin n) :
    Source.coefficient model β x i j ≤ Real.exp (β * (⟪(x i).val, (x j).val⟫ - 1)) := by
  cases model with
  | usa =>
    exact div_le_self (Real.exp_pos _).le (by exact_mod_cast (show 1 ≤ n from Nat.succ_le_of_lt (Nat.zero_lt_of_lt i.isLt)))
  | sa => exact div_le_self (Real.exp_pos _).le (normalization_ge_one β x i)

theorem coefficient_le_exp_barrier (model : Source.Model) (β L : ℝ) (hβ : 0 ≤ β)
    (x : Source.Configuration n d) (i j : Fin n)
    (hsep : ⟪(x i).val, (x j).val⟫ ≤ 1 - L) :
    Source.coefficient model β x i j ≤ Real.exp (-β * L) := by
  apply (coefficient_le_kernel model β x i j).trans
  apply Real.exp_le_exp.mpr
  nlinarith

theorem row_sum_sa (β : ℝ) (x : Source.Configuration n d) (i : Fin n) :
    ∑ j, Source.coefficient .sa β x i j = 1 := by
  unfold Source.coefficient
  rw [← Finset.sum_div, div_self]
  have h := normalization_ge_one β x i
  linarith

theorem row_sum_le_one (model : Source.Model) (β : ℝ) (hβ : 0 ≤ β)
    (x : Source.Configuration n d) (i : Fin n) :
    ∑ j, Source.coefficient model β x i j ≤ 1 := by
  cases model with
  | sa => exact (row_sum_sa β x i).le
  | usa =>
    have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
    unfold Source.coefficient
    rw [← Finset.sum_div]
    apply (div_le_iff₀ hn).mpr
    calc
      ∑ j, Real.exp (β * (⟪(x i).val, (x j).val⟫ - 1)) ≤ ∑ _ : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        apply Real.exp_le_one_iff.mpr
        exact mul_nonpos_of_nonneg_of_nonpos hβ (sub_nonpos.mpr (inner_bounds _ _).2)
      _ = 1 * n := by simp

/-- Tangency of the literal vector field at every unit state. -/
theorem vectorField_tangent (model : Source.Model) (β : ℝ)
    (x : Source.Configuration n d) (i : Fin n) :
    ⟪(x i).val, Source.vectorField model β x i⟫ = 0 := by
  simp only [Source.vectorField, Source.projectTangent, inner_sub_right,
    inner_smul_right, real_inner_self_eq_norm_sq, (x i).property, one_pow, mul_one, sub_self]

theorem vectorField_coordinate (model : Source.Model) (β : ℝ)
    (x : Source.Configuration n d) (i : Fin n) (w : Source.Sphere d) :
    ⟪Source.vectorField model β x i, w.val⟫ =
      ∑ j, Source.coefficient model β x i j *
        (⟪(x j).val, w.val⟫ - ⟪(x i).val, (x j).val⟫ * ⟪(x i).val, w.val⟫) := by
  simp only [Source.vectorField, Source.projectTangent, inner_sub_left,
    sum_inner, inner_sum, real_inner_smul_left, inner_smul_right,
    Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem projected_coordinate_abs_le_two (u v w : Source.Sphere d) :
    |⟪v.val, w.val⟫ - ⟪u.val, v.val⟫ * ⟪u.val, w.val⟫| ≤ 2 := by
  have huv : |⟪u.val, v.val⟫| ≤ 1 := abs_le.mpr (inner_bounds u v)
  have huw : |⟪u.val, w.val⟫| ≤ 1 := abs_le.mpr (inner_bounds u w)
  have hvw : |⟪v.val, w.val⟫| ≤ 1 := abs_le.mpr (inner_bounds v w)
  calc
    |⟪v.val, w.val⟫ - ⟪u.val, v.val⟫ * ⟪u.val, w.val⟫| ≤
        |⟪v.val, w.val⟫| + |⟪u.val, v.val⟫ * ⟪u.val, w.val⟫| := abs_sub _ _
    _ ≤ 1 + 1 := by
      rw [abs_mul]
      exact add_le_add hvw (by simpa only [one_mul] using mul_le_mul huv huw (abs_nonneg _) zero_le_one)
    _ = 2 := by norm_num

/-- An internal particle cannot lower a positive minimal cap coordinate. -/
theorem internal_coordinate_nonneg (u v w : Source.Sphere d)
    (hpos : 0 ≤ ⟪u.val, w.val⟫) (hmin : ⟪u.val, w.val⟫ ≤ ⟪v.val, w.val⟫) :
    0 ≤ ⟪v.val, w.val⟫ - ⟪u.val, v.val⟫ * ⟪u.val, w.val⟫ := by
  nlinarith [(inner_bounds u v).2]

/-- Source cap-drift local estimate at a minimizing label. The constant 2n
is uniform in beta, the configuration, the cap, and the choice of model. -/
theorem cap_minimum_vectorField_lower (model : Source.Model) (β L : ℝ) (hβ : 0 ≤ β)
    (x : Source.Configuration n d) (A : Source.Block n) (i : Fin n)
    (w : Source.Sphere d) (hpos : 0 ≤ ⟪(x i).val, w.val⟫)
    (hmin : ∀ j ∈ A, ⟪(x i).val, w.val⟫ ≤ ⟪(x j).val, w.val⟫)
    (hsep : ∀ j ∉ A, ⟪(x i).val, (x j).val⟫ ≤ 1 - L) :
    -(2 * n) * Real.exp (-β * L) ≤ ⟪Source.vectorField model β x i, w.val⟫ := by
  rw [vectorField_coordinate]
  have hterm : ∀ j : Fin n, -(2 * Real.exp (-β * L)) ≤
      Source.coefficient model β x i j *
        (⟪(x j).val, w.val⟫ - ⟪(x i).val, (x j).val⟫ * ⟪(x i).val, w.val⟫) := by
    intro j
    have hc := coefficient_nonneg model β x i j
    by_cases hj : j ∈ A
    · have hp := internal_coordinate_nonneg (x i) (x j) w hpos (hmin j hj)
      exact (neg_nonpos.mpr (mul_nonneg (by norm_num) (Real.exp_pos _).le)).trans (mul_nonneg hc hp)
    · have hb := coefficient_le_exp_barrier model β L hβ x i j (hsep j hj)
      have hp := (abs_le.mp (projected_coordinate_abs_le_two (x i) (x j) w)).1
      nlinarith
  calc
    -(2 * n) * Real.exp (-β * L) = ∑ _ : Fin n, -(2 * Real.exp (-β * L)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ _ := Finset.sum_le_sum (fun j _ => hterm j)

/-- With no exterior particles, the minimal positive cap coordinate has
nonnegative velocity, for either attention model. -/
theorem full_cap_minimum_vectorField_nonneg (model : Source.Model) (β : ℝ)
    (x : Source.Configuration n d) (i : Fin n) (w : Source.Sphere d)
    (hpos : 0 ≤ ⟪(x i).val, w.val⟫)
    (hmin : ∀ j, ⟪(x i).val, w.val⟫ ≤ ⟪(x j).val, w.val⟫) :
    0 ≤ ⟪Source.vectorField model β x i, w.val⟫ := by
  rw [vectorField_coordinate]
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (coefficient_nonneg model β x i j)
    (internal_coordinate_nonneg (x i) (x j) w hpos (hmin j)))

end Metastability.ModelBounds
