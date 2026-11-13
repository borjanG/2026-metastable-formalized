import Metastability.ModelBounds

/-!
# Pair correlation deficits from the literal source ODE

Differentiation on the source time domain includes its left endpoint zero.
The symmetric velocity identity is purely algebraic and applies to both
attention models, without a scalar ODE premise or a noncoincidence assumption.
-/

noncomputable section
open Set
open scoped BigOperators RealInnerProductSpace

namespace Metastability.PairDeficit

open Source
variable {n d : ℕ}

/-- The source pair deficit `qᵢⱼ = 1 - ⟪xᵢ,xⱼ⟫`. -/
def deficit (x : Configuration n d) (i j : Fin n) : ℝ :=
  1 - ⟪(x i).val, (x j).val⟫

/-- The derivative supplied by the literal vector field. -/
def velocity (model : Model) (β : ℝ) (x : Configuration n d) (i j : Fin n) : ℝ :=
  -(⟪vectorField model β x i, (x j).val⟫ +
    ⟪(x i).val, vectorField model β x j⟫)

theorem deficit_nonneg (x : Configuration n d) (i j : Fin n) :
    0 ≤ deficit x i j :=
  sub_nonneg.mpr (ModelBounds.inner_bounds (x i) (x j)).2

theorem deficit_le_two (x : Configuration n d) (i j : Fin n) :
    deficit x i j ≤ 2 := by
  unfold deficit
  linarith only [(ModelBounds.inner_bounds (x i) (x j)).1]

theorem deficit_eq_zero_iff (x : Configuration n d) (i j : Fin n) :
    deficit x i j = 0 ↔ x i = x j := by
  rw [deficit, sub_eq_zero]
  constructor
  · intro h
    exact Subtype.ext ((inner_eq_one_iff_of_norm_eq_one (x i).property (x j).property).mp h.symm)
  · intro h
    rw [h, real_inner_self_eq_norm_sq, (x j).property, one_pow]

/-- Differentiation on the actual source half-line, including time zero. -/
theorem hasDerivWithinAt (model : Model) (β : ℝ)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (i j : Fin n) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun u => deficit (X u) i j)
      (velocity model β (X t) i j) (Ici 0) t := by
  simpa only [deficit, velocity, add_comm] using
    ((hX t ht i).inner ℝ (hX t ht j)).const_sub 1

/-- Right differentiation at any nonnegative original time. -/
theorem hasDerivWithinAt_right (model : Model) (β : ℝ)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (i j : Fin n) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun u => deficit (X u) i j)
      (velocity model β (X t) i j) (Ici t) t :=
  (hasDerivWithinAt model β X hX i j t ht).mono (Ici_subset_Ici.mpr ht)

theorem hasDerivAt_pos (model : Model) (β : ℝ)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (i j : Fin n) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun u => deficit (X u) i j)
      (velocity model β (X t) i j) t :=
  (hasDerivWithinAt model β X hX i j t ht.le).hasDerivAt (Ici_mem_nhds ht)

theorem continuousOn (model : Model) (β : ℝ)
    (X : ℝ → Configuration n d) (hX : Solves model β X) (i j : Fin n) :
    ContinuousOn (fun u => deficit (X u) i j) (Ici 0) :=
  fun t ht => (hasDerivWithinAt model β X hX i j t ht).continuousWithinAt

/-- The exact unsymmetrized scalar equation, obtained by expanding the
tangent projections in the source vector field. -/
theorem velocity_eq_sum (model : Model) (β : ℝ)
    (x : Configuration n d) (i j : Fin n) :
    velocity model β x i j = ∑ k,
      (coefficient model β x i k *
        (⟪(x i).val, (x j).val⟫ * ⟪(x i).val, (x k).val⟫ -
          ⟪(x j).val, (x k).val⟫) +
       coefficient model β x j k *
        (⟪(x i).val, (x j).val⟫ * ⟪(x j).val, (x k).val⟫ -
          ⟪(x i).val, (x k).val⟫)) := by
  unfold velocity
  rw [real_inner_comm (vectorField model β x j) (x i).val,
    ModelBounds.vectorField_coordinate, ModelBounds.vectorField_coordinate,
    ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [real_inner_comm (x j).val (x k).val,
    real_inner_comm (x i).val (x k).val, real_inner_comm (x i).val (x j).val]
  ring

/-- Symmetric endpoint algebra for the pair deficit. This separates the
contracting average term from the coefficient-difference term. -/
theorem velocity_eq_symmetric (model : Model) (β : ℝ)
    (x : Configuration n d) (i j : Fin n) :
    velocity model β x i j =
      -(deficit x i j) / 2 * ∑ k,
        (coefficient model β x i k + coefficient model β x j k) *
          (⟪(x i).val, (x k).val⟫ + ⟪(x j).val, (x k).val⟫) +
      (1 + ⟪(x i).val, (x j).val⟫) / 2 * ∑ k,
        (coefficient model β x i k - coefficient model β x j k) *
          (⟪(x i).val, (x k).val⟫ - ⟪(x j).val, (x k).val⟫) := by
  rw [velocity_eq_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  unfold deficit
  ring

/-- Identical particle positions have identical coefficient rows in either model. -/
theorem coefficient_eq_of_eq (model : Model) (β : ℝ)
    (x : Configuration n d) (i j : Fin n) (h : x i = x j) (k : Fin n) :
    coefficient model β x i k = coefficient model β x j k := by
  cases model <;> simp only [coefficient, h]

theorem vectorField_eq_of_eq (model : Model) (β : ℝ)
    (x : Configuration n d) (i j : Fin n) (h : x i = x j) :
    vectorField model β x i = vectorField model β x j := by
  unfold vectorField
  simp only [h, coefficient_eq_of_eq model β x i j h]

theorem velocity_eq_zero_of_eq (model : Model) (β : ℝ)
    (x : Configuration n d) (i j : Fin n) (h : x i = x j) :
    velocity model β x i j = 0 := by
  unfold velocity
  rw [vectorField_eq_of_eq model β x i j h, h,
    real_inner_comm (x j).val (vectorField model β x j),
    ModelBounds.vectorField_tangent]
  ring

theorem velocity_eq_zero_of_deficit_eq_zero (model : Model) (β : ℝ)
    (x : Configuration n d) (i j : Fin n) (h : deficit x i j = 0) :
    velocity model β x i j = 0 :=
  velocity_eq_zero_of_eq model β x i j ((deficit_eq_zero_iff x i j).mp h)

/-- At coincidence the actual source pair deficit has zero right derivative. -/
theorem hasDerivWithinAt_zero_of_deficit_eq_zero (model : Model) (β : ℝ)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (i j : Fin n) (t : ℝ) (ht : 0 ≤ t) (h : deficit (X t) i j = 0) :
    HasDerivWithinAt (fun u => deficit (X u) i j) 0 (Ici t) t := by
  simpa only [velocity_eq_zero_of_deficit_eq_zero model β (X t) i j h] using
    hasDerivWithinAt_right model β X hX i j t ht

end Metastability.PairDeficit
