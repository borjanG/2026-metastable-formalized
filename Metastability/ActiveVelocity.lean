import Metastability.ActiveCoefficients

/-!
# Original-time correlation velocity of two tight blocks

The finite estimates in this file are consequences of the source vector fields.
They do not assume a scalar differential equation or a coefficient expansion.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Metastability.ActiveVelocity
open Source ActiveCoefficients
variable {n d : ℕ}

def projection (x : Configuration n d) (i j k : Fin n) : ℝ :=
  ⟪(x j).val, (x k).val⟫ - ⟪(x i).val, (x j).val⟫ * ⟪(x i).val, (x k).val⟫

def sineSquare (x : Configuration n d) (i j : Fin n) : ℝ :=
  1 - ⟪(x i).val, (x j).val⟫ ^ 2

def rowVelocity (model : Model) (β : ℝ) (x : Configuration n d) (i j : Fin n) : ℝ :=
  ∑ k, coefficient model β x i k * projection x i j k

def rate (model : Model) (B C : Block n) : ℝ :=
  (C.card : ℝ) / blockDenominator model B + (B.card : ℝ) / blockDenominator model C

theorem rate_usa (B C : Block n) :
    rate .usa B C = ((B.card : ℝ) + C.card) / n := by
  dsimp only [rate, blockDenominator]
  ring

theorem rate_sa (B C : Block n) :
    rate .sa B C = (C.card : ℝ) / B.card + (B.card : ℝ) / C.card := rfl

theorem sineSquare_nonneg (x : Configuration n d) (i j : Fin n) :
    0 ≤ sineSquare x i j := by
  have h := ModelBounds.inner_bounds (x i) (x j)
  dsimp only [sineSquare]
  nlinarith only [h.1, h.2]

theorem sineSquare_le_one (x : Configuration n d) (i j : Fin n) :
    sineSquare x i j ≤ 1 := by
  dsimp only [sineSquare]
  nlinarith only [sq_nonneg ⟪(x i).val, (x j).val⟫]

theorem sineSquare_comm (x : Configuration n d) (i j : Fin n) :
    sineSquare x i j = sineSquare x j i := by
  simp only [sineSquare, real_inner_comm]

theorem kernel_comm (β : ℝ) (x : Configuration n d) (i j : Fin n) :
    kernel β x i j = kernel β x j i := by
  simp only [kernel, real_inner_comm]

theorem correlation_velocity_eq (model : Model) (β : ℝ) (x : Configuration n d) (i j : Fin n) :
    -PairDeficit.velocity model β x i j =
      rowVelocity model β x i j + rowVelocity model β x j i := by
  rw [PairDeficit.velocity_eq_sum, ← Finset.sum_neg_distrib]
  dsimp only [rowVelocity]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  dsimp only [projection]
  rw [real_inner_comm (x i).val (x j).val]
  ring

theorem projection_self (x : Configuration n d) (i j : Fin n) :
    projection x i j i = 0 := by
  simp only [projection, real_inner_self_eq_norm_sq, (x i).property, one_pow, mul_one,
    real_inner_comm, sub_self]

theorem projection_other (x : Configuration n d) (i j : Fin n) :
    projection x i j j = sineSquare x i j := by
  simp only [projection, sineSquare, real_inner_self_eq_norm_sq, (x j).property, pow_two, one_mul]

theorem projection_variation (x : Configuration n d) (i j k l : Fin n) :
    |projection x i j k - projection x i j l| ≤ 2 * angularDist (x k) (x l) := by
  have hr : |⟪(x i).val, (x j).val⟫| ≤ 1 := abs_le.mpr (ModelBounds.inner_bounds _ _)
  have h₁ := inner_variation (x j) (x k) (x l)
  have h₂ := inner_variation (x i) (x k) (x l)
  have heq : projection x i j k - projection x i j l =
      (⟪(x j).val, (x k).val⟫ - ⟪(x j).val, (x l).val⟫) -
      ⟪(x i).val, (x j).val⟫ * (⟪(x i).val, (x k).val⟫ - ⟪(x i).val, (x l).val⟫) := by
    dsimp only [projection]
    ring
  rw [heq]
  calc
    _ ≤ |⟪(x j).val, (x k).val⟫ - ⟪(x j).val, (x l).val⟫| +
        |⟪(x i).val, (x j).val⟫ * (⟪(x i).val, (x k).val⟫ - ⟪(x i).val, (x l).val⟫)| := abs_sub _ _
    _ ≤ angularDist (x k) (x l) + angularDist (x k) (x l) := by
      rw [abs_mul]
      exact add_le_add h₁ ((mul_le_mul_of_nonneg_right hr (abs_nonneg _)).trans (by simpa using h₂))
    _ = _ := by ring

theorem projection_abs_le_two (x : Configuration n d) (i j k : Fin n) :
    |projection x i j k| ≤ 2 := by
  simpa only [projection, real_inner_comm, mul_comm] using
    ModelBounds.projected_coordinate_abs_le_two (x i) (x k) (x j)

/-- Replacing all members of the two blocks by their representatives in the
geometric factor costs only the block diameter and the exterior coefficients. -/
theorem row_geometric_error (model : Model) (β δ L : ℝ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ)
    (x : Configuration n d) (B C : Block n) (i j : Fin n)
    (hBclose : ∀ k ∈ B, angularDist (x k) (x i) ≤ δ)
    (hCclose : ∀ k ∈ C, angularDist (x k) (x j) ≤ δ)
    (hsep : ∀ k ∉ B, k ∉ C → L ≤ PairDeficit.deficit x i k) :
    |rowVelocity model β x i j - sineSquare x i j * (∑ k ∈ C, coefficient model β x i k)| ≤
      2 * δ + 2 * n * Real.exp (-β * L) := by
  have hterm : ∀ k : Fin n,
      |coefficient model β x i k *
        (projection x i j k - (if k ∈ C then sineSquare x i j else 0))| ≤
        2 * δ * coefficient model β x i k + 2 * Real.exp (-β * L) := by
    intro k
    have hc := ModelBounds.coefficient_nonneg model β x i k
    rw [abs_mul, abs_of_nonneg hc]
    by_cases hkC : k ∈ C
    · rw [if_pos hkC, ← projection_other]
      have h := mul_le_mul_of_nonneg_left ((projection_variation x i j k j).trans
        (mul_le_mul_of_nonneg_left (hCclose k hkC) (by norm_num))) hc
      nlinarith only [h, (Real.exp_pos (-β * L)).le]
    · rw [if_neg hkC, sub_zero]
      by_cases hkB : k ∈ B
      · have hp : |projection x i j k| ≤ 2 * δ := by
          simpa only [projection_self, sub_zero] using
            (projection_variation x i j k i).trans
              (mul_le_mul_of_nonneg_left (hBclose k hkB) (by norm_num))
        have h := mul_le_mul_of_nonneg_left hp hc
        nlinarith only [h, (Real.exp_pos (-β * L)).le]
      · have hcO := ModelBounds.coefficient_le_exp_barrier model β L hβ x i k (by
          have hh := hsep k hkB hkC
          dsimp only [PairDeficit.deficit] at hh
          linarith only [hh])
        have hp := mul_le_mul (projection_abs_le_two x i j k) hcO hc (by norm_num)
        have hδc := mul_nonneg hδ hc
        nlinarith only [hp, hδc]
  have heq : rowVelocity model β x i j - sineSquare x i j * (∑ k ∈ C, coefficient model β x i k) =
      ∑ k : Fin n, coefficient model β x i k *
        (projection x i j k - (if k ∈ C then sineSquare x i j else 0)) := by
    simp only [mul_sub, Finset.sum_sub_distrib, rowVelocity]
    congr 1
    rw [Finset.mul_sum]
    simp only [mul_ite, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]
    simp only [mul_comm]
  rw [heq]
  calc
    _ ≤ ∑ k : Fin n, |coefficient model β x i k *
        (projection x i j k - (if k ∈ C then sineSquare x i j else 0))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin n, (2 * δ * coefficient model β x i k + 2 * Real.exp (-β * L)) :=
      Finset.sum_le_sum (fun k _ => hterm k)
    _ = 2 * δ * (∑ k : Fin n, coefficient model β x i k) + 2 * n * Real.exp (-β * L) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (ModelBounds.row_sum_le_one model β hβ x i)
        (show 0 ≤ 2 * δ by positivity)
      linarith only [h]

theorem cross_mass_error (model : Model) (β δ L : ℝ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ)
    (x : Configuration n d) (B C : Block n) (hB : B.Nonempty) (i j : Fin n)
    (hBclose : ∀ k ∈ B, angularDist (x i) (x k) ≤ δ)
    (hCclose : ∀ k ∈ C, angularDist (x k) (x j) ≤ δ)
    (hsep : ∀ k ∉ B, k ∉ C → L ≤ PairDeficit.deficit x i k) :
    |(∑ k ∈ C, coefficient model β x i k) - (C.card : ℝ) / blockDenominator model B * kernel β x i j| ≤
      n * kernel β x i j * (kernelError β δ +
        denominatorError n β δ (kernel β x i j) (Real.exp (-β * L))) := by
  let E := kernel β x i j * (kernelError β δ +
    denominatorError n β δ (kernel β x i j) (Real.exp (-β * L)))
  have hE : 0 ≤ E := by
    dsimp only [E, denominatorError]
    have hH := kernelError_nonneg β δ hβ hδ
    have hK : 0 ≤ kernel β x i j := (Real.exp_pos _).le
    positivity
  have heq : (C.card : ℝ) / blockDenominator model B * kernel β x i j =
      ∑ _ ∈ C, kernel β x i j / blockDenominator model B := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [heq, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ C, |coefficient model β x i k - kernel β x i j / blockDenominator model B| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ C, E := Finset.sum_le_sum (fun k hk =>
      coefficient_close model β δ L hβ hδ x B C hB i j hBclose hCclose hsep k hk)
    _ = C.card * E := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ n * E := mul_le_mul_of_nonneg_right (by exact_mod_cast (show C.card ≤ n by simpa only [Fintype.card_fin] using Finset.card_le_univ C)) hE
    _ = _ := by dsimp only [E]; ring

/-- Explicit error in one row, including the literal SA normalization. -/
theorem row_error (model : Model) (β δ L : ℝ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ)
    (x : Configuration n d) (B C : Block n) (hB : B.Nonempty) (i j : Fin n)
    (hBclose : ∀ k ∈ B, angularDist (x k) (x i) ≤ δ)
    (hCclose : ∀ k ∈ C, angularDist (x k) (x j) ≤ δ)
    (hsep : ∀ k ∉ B, k ∉ C → L ≤ PairDeficit.deficit x i k) :
    |rowVelocity model β x i j - (C.card : ℝ) / blockDenominator model B *
      (sineSquare x i j * kernel β x i j)| ≤
      2 * δ + 2 * n * Real.exp (-β * L) +
        n * (sineSquare x i j * kernel β x i j) * (kernelError β δ +
          denominatorError n β δ (kernel β x i j) (Real.exp (-β * L))) := by
  have hg := row_geometric_error model β δ L hβ hδ x B C i j hBclose hCclose hsep
  have hc := cross_mass_error model β δ L hβ hδ x B C hB i j
    (fun k hk => by simpa only [AngularGeometry.angularDist_comm] using hBclose k hk)
    hCclose hsep
  have hs := sineSquare_nonneg x i j
  have heq : rowVelocity model β x i j - (C.card : ℝ) / blockDenominator model B *
      (sineSquare x i j * kernel β x i j) =
      (rowVelocity model β x i j - sineSquare x i j * (∑ k ∈ C, coefficient model β x i k)) +
      sineSquare x i j * ((∑ k ∈ C, coefficient model β x i k) -
        (C.card : ℝ) / blockDenominator model B * kernel β x i j) := by ring
  rw [heq]
  calc
    _ ≤ |rowVelocity model β x i j - sineSquare x i j * (∑ k ∈ C, coefficient model β x i k)| +
        |sineSquare x i j * ((∑ k ∈ C, coefficient model β x i k) -
          (C.card : ℝ) / blockDenominator model B * kernel β x i j)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_of_nonneg hs]
      have h := add_le_add hg (mul_le_mul_of_nonneg_left hc hs)
      convert h using 1; ring

/-- Quantitative two-block law for the literal original-time correlation
velocity. The USA and SA rates are exact cardinality expressions. -/
theorem correlation_error (model : Model) (β δ L : ℝ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ)
    (x : Configuration n d) (B C : Block n) (hB : B.Nonempty) (hC : C.Nonempty)
    (i j : Fin n)
    (hBclose : ∀ k ∈ B, angularDist (x k) (x i) ≤ δ)
    (hCclose : ∀ k ∈ C, angularDist (x k) (x j) ≤ δ)
    (hsepB : ∀ k ∉ B, k ∉ C → L ≤ PairDeficit.deficit x i k)
    (hsepC : ∀ k ∉ C, k ∉ B → L ≤ PairDeficit.deficit x j k) :
    |-PairDeficit.velocity model β x i j - rate model B C *
      (sineSquare x i j * kernel β x i j)| ≤
      4 * δ + 4 * n * Real.exp (-β * L) +
        2 * n * (sineSquare x i j * kernel β x i j) * (kernelError β δ +
          denominatorError n β δ (kernel β x i j) (Real.exp (-β * L))) := by
  have h₁ := row_error model β δ L hβ hδ x B C hB i j hBclose hCclose hsepB
  have h₂ := row_error model β δ L hβ hδ x C B hC j i hCclose hBclose hsepC
  rw [← sineSquare_comm x i j, ← kernel_comm β x i j] at h₂
  rw [correlation_velocity_eq]
  have heq : rowVelocity model β x i j + rowVelocity model β x j i -
      rate model B C * (sineSquare x i j * kernel β x i j) =
      (rowVelocity model β x i j - (C.card : ℝ) / blockDenominator model B * (sineSquare x i j * kernel β x i j)) +
      (rowVelocity model β x j i - (B.card : ℝ) / blockDenominator model C * (sineSquare x i j * kernel β x i j)) := by
    dsimp only [rate]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans (by convert add_le_add h₁ h₂ using 1; ring)

end Metastability.ActiveVelocity
