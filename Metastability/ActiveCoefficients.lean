import Metastability.ContractionPointwise
import Metastability.BlockGeometry

/-!
# Coefficient estimates near two tight blocks

All kernels and row denominators below are the literal source coefficients.
The estimates retain their numerical remainders, so their use does not assume
an approximate scalar equation.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Metastability.ActiveCoefficients
open Source
variable {n d : ℕ}

def kernel (β : ℝ) (x : Configuration n d) (i j : Fin n) : ℝ :=
  Real.exp (β * (⟪(x i).val, (x j).val⟫ - 1))

def denominator (model : Model) (β : ℝ) (x : Configuration n d) (i : Fin n) : ℝ :=
  match model with
  | .usa => n
  | .sa => ∑ k, kernel β x i k

def blockDenominator (model : Model) (B : Block n) : ℝ :=
  match model with
  | .usa => n
  | .sa => B.card

/-- Relative kernel perturbation at angular error delta. -/
def kernelError (β δ : ℝ) : ℝ := β * δ * Real.exp (β * δ)

/-- A common bound on the row-denominator perturbation, valid for both models. -/
def denominatorError (n : ℕ) (β δ K O : ℝ) : ℝ :=
  n * (β * δ + K * (1 + kernelError β δ) + O)

theorem coefficient_eq (model : Model) (β : ℝ) (x : Configuration n d) (i k : Fin n) :
    coefficient model β x i k = kernel β x i k / denominator model β x i := by
  cases model <;> rfl

theorem denominator_ge_one (model : Model) (β : ℝ) (x : Configuration n d) (i : Fin n) :
    1 ≤ denominator model β x i := by
  cases model with
  | usa =>
    change (1 : ℝ) ≤ n
    exact_mod_cast (Nat.succ_le_of_lt (Nat.zero_lt_of_lt i.isLt))
  | sa => exact ModelBounds.normalization_ge_one β x i

theorem blockDenominator_ge_one (model : Model) (B : Block n) (hB : B.Nonempty) :
    1 ≤ blockDenominator model B := by
  cases model with
  | usa =>
    obtain ⟨i, _⟩ := hB
    change (1 : ℝ) ≤ n
    exact_mod_cast (Nat.succ_le_of_lt (Nat.zero_lt_of_lt i.isLt))
  | sa =>
    change (1 : ℝ) ≤ B.card
    exact_mod_cast (Finset.one_le_card.mpr hB)

theorem inner_variation (u v w : Sphere d) :
    |⟪u.val, v.val⟫ - ⟪u.val, w.val⟫| ≤ angularDist v w := by
  rw [← inner_sub_right]
  exact (abs_real_inner_le_norm _ _).trans (by
    simpa only [u.property, one_mul] using AngularGeometry.norm_sub_le_angularDist v w)

theorem kernelError_nonneg (β δ : ℝ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ) :
    0 ≤ kernelError β δ := mul_nonneg (mul_nonneg hβ hδ) (Real.exp_pos _).le

theorem exp_difference_le (a b e : ℝ) (he : 0 ≤ e) (hab : |a - b| ≤ e) :
    |Real.exp a - Real.exp b| ≤ Real.exp b * (e * Real.exp e) := by
  have ha : a ≤ b + e := by linarith only [(abs_le.mp hab).2]
  have hea : Real.exp a ≤ Real.exp b * Real.exp e := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr ha
  have he1 : 1 ≤ Real.exp e := Real.one_le_exp he
  apply abs_le.mpr
  constructor
  · have h := KernelComparison.exp_sub_le_exp_mul_sub b a
    have hb : b - a ≤ e := by linarith only [(abs_le.mp hab).1]
    have h' := mul_le_mul_of_nonneg_left hb (Real.exp_pos b).le
    have h'' := mul_le_mul_of_nonneg_left he1 (mul_nonneg (Real.exp_pos b).le he)
    nlinarith only [h, h', h'']
  · have h := KernelComparison.exp_sub_le_exp_mul_sub a b
    have h' := mul_le_mul_of_nonneg_left (abs_le.mp hab).2 (Real.exp_pos a).le
    have h'' := mul_le_mul_of_nonneg_right hea he
    nlinarith only [h, h', h'']

theorem kernel_close (β δ : ℝ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ)
    (x : Configuration n d) (i j k : Fin n) (hclose : angularDist (x k) (x j) ≤ δ) :
    |kernel β x i k - kernel β x i j| ≤ kernel β x i j * kernelError β δ := by
  apply exp_difference_le _ _ _ (mul_nonneg hβ hδ)
  rw [show β * (⟪(x i).val, (x k).val⟫ - 1) - β * (⟪(x i).val, (x j).val⟫ - 1) =
    β * (⟪(x i).val, (x k).val⟫ - ⟪(x i).val, (x j).val⟫) by ring, abs_mul, abs_of_nonneg hβ]
  exact mul_le_mul_of_nonneg_left ((inner_variation (x i) (x k) (x j)).trans hclose) hβ

theorem kernel_near_self (β δ : ℝ) (hβ : 0 ≤ β)
    (x : Configuration n d) (i k : Fin n) (hclose : angularDist (x i) (x k) ≤ δ) :
    |kernel β x i k - 1| ≤ β * δ := by
  have hk := ContractionPointwise.kernel_le_one β hβ (x i) (x k)
  have hc := inner_variation (x i) (x i) (x k)
  rw [real_inner_self_eq_norm_sq, (x i).property, one_pow] at hc
  have hq : 1 - ⟪(x i).val, (x k).val⟫ ≤ δ :=
    (le_abs_self _).trans (hc.trans hclose)
  have he := Real.add_one_le_exp (β * (⟪(x i).val, (x k).val⟫ - 1))
  dsimp only [kernel]
  rw [abs_of_nonpos (sub_nonpos.mpr hk)]
  nlinarith only [he, mul_le_mul_of_nonneg_left hq hβ]

theorem quotient_difference_le (A K D b h E : ℝ)
    (hK : 0 ≤ K) (hD : 1 ≤ D) (hb : 1 ≤ b)
    (hAK : |A - K| ≤ K * h) (hDb : |D - b| ≤ E) :
    |A / D - K / b| ≤ K * (h + E) := by
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have heq : A / D - K / b = (A - K) / D + K * (b - D) / (D * b) := by
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ |(A - K) / D| + |K * (b - D) / (D * b)| := abs_add_le _ _
    _ = |A - K| / D + K * |D - b| / (D * b) := by
      rw [abs_div, abs_div, abs_mul, abs_of_pos hD0, abs_of_nonneg hK,
        abs_of_pos (mul_pos hD0 hb0), abs_sub_comm b D]
    _ ≤ |A - K| + K * |D - b| :=
      add_le_add (div_le_self (abs_nonneg _) hD)
        (div_le_self (mul_nonneg hK (abs_nonneg _)) (by nlinarith only [hD, hb]))
    _ ≤ K * h + K * E := add_le_add hAK (mul_le_mul_of_nonneg_left hDb hK)
    _ = _ := by ring

theorem denominator_close (model : Model) (β δ L : ℝ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ)
    (x : Configuration n d) (B C : Block n) (i j : Fin n)
    (hBclose : ∀ k ∈ B, angularDist (x i) (x k) ≤ δ)
    (hCclose : ∀ k ∈ C, angularDist (x k) (x j) ≤ δ)
    (hsep : ∀ k ∉ B, k ∉ C → L ≤ PairDeficit.deficit x i k) :
    |denominator model β x i - blockDenominator model B| ≤
      denominatorError n β δ (kernel β x i j) (Real.exp (-β * L)) := by
  have hH := kernelError_nonneg β δ hβ hδ
  have hK : 0 ≤ kernel β x i j := (Real.exp_pos _).le
  have hO : 0 ≤ Real.exp (-β * L) := (Real.exp_pos _).le
  have hβδ := mul_nonneg hβ hδ
  have hR : 0 ≤ β * δ + kernel β x i j * (1 + kernelError β δ) + Real.exp (-β * L) := by positivity
  cases model with
  | usa => simpa only [denominator, blockDenominator, sub_self, abs_zero] using
      mul_nonneg (show (0 : ℝ) ≤ n by positivity) hR
  | sa =>
    have hterm : ∀ k : Fin n,
        |kernel β x i k - (if k ∈ B then 1 else 0)| ≤
          β * δ + kernel β x i j * (1 + kernelError β δ) + Real.exp (-β * L) := by
      intro k
      by_cases hkB : k ∈ B
      · rw [if_pos hkB]
        exact (kernel_near_self β δ hβ x i k (hBclose k hkB)).trans (by
          have hKH : 0 ≤ kernel β x i j * (1 + kernelError β δ) := by positivity
          linarith only [hKH, hO])
      · rw [if_neg hkB, sub_zero, abs_of_pos (show 0 < kernel β x i k from Real.exp_pos _)]
        by_cases hkC : k ∈ C
        · have h := (abs_le.mp (kernel_close β δ hβ hδ x i j k (hCclose k hkC))).2
          nlinarith only [h, hβδ, hO]
        · have h : kernel β x i k ≤ Real.exp (-β * L) := by
            apply Real.exp_le_exp.mpr
            have hh := hsep k hkB hkC
            dsimp only [PairDeficit.deficit] at hh
            nlinarith only [mul_le_mul_of_nonneg_left hh hβ]
          exact h.trans (by
            have hKH : 0 ≤ kernel β x i j * (1 + kernelError β δ) := by positivity
            linarith only [hβδ, hKH])
    have heq : (∑ k : Fin n, (if k ∈ B then (1 : ℝ) else 0)) = B.card := by simp
    change |(∑ k, kernel β x i k) - (B.card : ℝ)| ≤ _
    rw [← heq, ← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ k : Fin n, |kernel β x i k - (if k ∈ B then 1 else 0)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin n, (β * δ + kernel β x i j * (1 + kernelError β δ) + Real.exp (-β * L)) :=
        Finset.sum_le_sum (fun k _ => hterm k)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, denominatorError]

theorem coefficient_close (model : Model) (β δ L : ℝ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ)
    (x : Configuration n d) (B C : Block n) (hB : B.Nonempty) (i j : Fin n)
    (hBclose : ∀ k ∈ B, angularDist (x i) (x k) ≤ δ)
    (hCclose : ∀ k ∈ C, angularDist (x k) (x j) ≤ δ)
    (hsep : ∀ k ∉ B, k ∉ C → L ≤ PairDeficit.deficit x i k)
    (k : Fin n) (hk : k ∈ C) :
    |coefficient model β x i k - kernel β x i j / blockDenominator model B| ≤
      kernel β x i j * (kernelError β δ +
        denominatorError n β δ (kernel β x i j) (Real.exp (-β * L))) := by
  rw [coefficient_eq]
  exact quotient_difference_le _ _ _ _ _ _ (Real.exp_pos _).le
    (denominator_ge_one model β x i) (blockDenominator_ge_one model B hB)
    (kernel_close β δ hβ hδ x i j k (hCclose k hk))
    (denominator_close model β δ L hβ hδ x B C i j hBclose hCclose hsep)

end Metastability.ActiveCoefficients
