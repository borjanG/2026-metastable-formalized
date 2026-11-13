import Metastability.ActiveVelocity

/-!
# Two-sided terminal correlation estimates

The SA denominator is bounded only between one and the particle count. In
particular, these estimates do not impose the mesoscopic SA cardinality rate
on the terminal window.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Metastability.ActiveTerminalVelocity
open Source ActiveCoefficients ActiveVelocity
variable {n d : ℕ}

/-- Cross-block mass bounds that do not approximate the SA denominator. -/
theorem cross_mass_bounds (model : Model) (β δ : ℝ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ)
    (hsmall : kernelError β δ ≤ 1 / 2)
    (x : Configuration n d) (C : Block n) (hC : C.Nonempty) (i j : Fin n)
    (hclose : ∀ k ∈ C, angularDist (x k) (x j) ≤ δ) :
    kernel β x i j / (2 * n) ≤ ∑ k ∈ C, coefficient model β x i k ∧
      (∑ k ∈ C, coefficient model β x i k) ≤ 2 * n * kernel β x i j := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  have hK : 0 ≤ kernel β x i j := (Real.exp_pos _).le
  have hpert := mul_le_mul_of_nonneg_left hsmall hK
  have hterm : ∀ k ∈ C, kernel β x i j / (2 * n) ≤ coefficient model β x i k ∧
      coefficient model β x i k ≤ 2 * kernel β x i j := by
    intro k hk
    have h := abs_le.mp (kernel_close β δ hβ hδ x i j k (hclose k hk))
    constructor
    · calc
        _ = (kernel β x i j / 2) / n := by ring
        _ ≤ kernel β x i k / n := div_le_div_of_nonneg_right (by nlinarith only [h.1, hpert]) hn.le
        _ ≤ _ := ContractionPointwise.coefficient_ge_kernel_div_n model β hβ x i k
    · exact (ModelBounds.coefficient_le_kernel model β x i k).trans (by
        change kernel β x i k ≤ 2 * kernel β x i j
        nlinarith only [h.2, hpert, hK])
  constructor
  · obtain ⟨k, hk⟩ := hC
    exact (hterm k hk).1.trans (Finset.single_le_sum (fun l _ =>
      ModelBounds.coefficient_nonneg model β x i l) hk)
  · calc
      _ ≤ ∑ _ ∈ C, 2 * kernel β x i j := Finset.sum_le_sum (fun k hk => (hterm k hk).2)
      _ = C.card * (2 * kernel β x i j) := by simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ n * (2 * kernel β x i j) := mul_le_mul_of_nonneg_right
        (by exact_mod_cast (show C.card ≤ n by simpa only [Fintype.card_fin] using Finset.card_le_univ C))
        (by positivity)
      _ = _ := by ring

/-- Static absorption step for the terminal window. Its explicit numerical
smallness premises are discharged from the cutoff and exponential scales in
the source-facing asymptotic assembly. -/
theorem correlation_comparable (model : Model) (β δ L : ℝ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ)
    (hsmall : kernelError β δ ≤ 1 / 2)
    (x : Configuration n d) (B C : Block n) (hB : B.Nonempty) (hC : C.Nonempty)
    (i j : Fin n)
    (hBclose : ∀ k ∈ B, angularDist (x k) (x i) ≤ δ)
    (hCclose : ∀ k ∈ C, angularDist (x k) (x j) ≤ δ)
    (hsepB : ∀ k ∉ B, k ∉ C → L ≤ PairDeficit.deficit x i k)
    (hsepC : ∀ k ∉ C, k ∉ B → L ≤ PairDeficit.deficit x j k)
    (habsorb : 4 * δ + 4 * n * Real.exp (-β * L) ≤
      (sineSquare x i j * kernel β x i j) / (2 * n)) :
    (sineSquare x i j * kernel β x i j) / (2 * n) ≤
        -PairDeficit.velocity model β x i j ∧
      -PairDeficit.velocity model β x i j ≤
        (4 * n + 1) * (sineSquare x i j * kernel β x i j) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt (Nat.zero_lt_of_lt i.isLt)
  have hS := sineSquare_nonneg x i j
  have hK : 0 ≤ kernel β x i j := (Real.exp_pos _).le
  have hSK := mul_nonneg hS hK
  have h₁ := row_geometric_error model β δ L hβ hδ x B C i j hBclose hCclose hsepB
  have h₂ := row_geometric_error model β δ L hβ hδ x C B j i hCclose hBclose hsepC
  have hm₁ := cross_mass_bounds model β δ hβ hδ hsmall x C hC i j hCclose
  have hm₂ := cross_mass_bounds model β δ hβ hδ hsmall x B hB j i hBclose
  rw [← sineSquare_comm x i j] at h₂
  rw [← kernel_comm β x i j] at hm₂
  have hlo₁ := mul_le_mul_of_nonneg_left hm₁.1 hS
  have hlo₂ := mul_le_mul_of_nonneg_left hm₂.1 hS
  have hhi₁ := mul_le_mul_of_nonneg_left hm₁.2 hS
  have hhi₂ := mul_le_mul_of_nonneg_left hm₂.2 hS
  have hhalf : sineSquare x i j * (kernel β x i j / (2 * n)) =
      (sineSquare x i j * kernel β x i j) / (2 * n) := by ring
  rw [hhalf] at hlo₁ hlo₂
  rw [correlation_velocity_eq]
  constructor
  · linarith only [(abs_le.mp h₁).1, (abs_le.mp h₂).1, hlo₁, hlo₂, habsorb]
  · have hdiv : (sineSquare x i j * kernel β x i j) / (2 * n) ≤
        sineSquare x i j * kernel β x i j := div_le_self hSK (by linarith only [hn1])
    have h₁' := (abs_le.mp h₁).2
    have h₂' := (abs_le.mp h₂).2
    nlinarith only [h₁', h₂', hhi₁, hhi₂, habsorb, hdiv]

end Metastability.ActiveTerminalVelocity
