import Metastability.ModelBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
Scalar chord interpolation of the literal frozen attention weights. Its
normalized derivative is a variance, so dropping the nonpositive square term
bounds the response without imposing a reduced dynamical equation.
-/
noncomputable section
open Set
open scoped BigOperators RealInnerProductSpace
namespace Metastability.FrozenWeights
variable {n : ℕ}

def kernel (β : ℝ) (a c : Fin n → ℝ) (s : ℝ) (k : Fin n) : ℝ :=
  Real.exp (β * (c k + s * (a k - c k) - 1))

def total (β : ℝ) (a c : Fin n → ℝ) (s : ℝ) : ℝ := ∑ k, kernel β a c s k

def first (β : ℝ) (a c : Fin n → ℝ) (s : ℝ) : ℝ :=
  ∑ k, kernel β a c s k * (a k - c k)

def second (β : ℝ) (a c : Fin n → ℝ) (s : ℝ) : ℝ :=
  ∑ k, kernel β a c s k * (a k - c k) ^ 2

def response (model : Source.Model) (β : ℝ) (a c : Fin n → ℝ) (s : ℝ) : ℝ :=
  match model with
  | .usa => first β a c s / n
  | .sa => first β a c s / total β a c s

def responseDerivative (model : Source.Model) (β : ℝ) (a c : Fin n → ℝ) (s : ℝ) : ℝ :=
  match model with
  | .usa => β * second β a c s / n
  | .sa => β * second β a c s / total β a c s -
      β * (first β a c s) ^ 2 / (total β a c s) ^ 2

theorem kernel_pos (β : ℝ) (a c : Fin n → ℝ) (s : ℝ) (k : Fin n) :
    0 < kernel β a c s k := Real.exp_pos _

theorem total_pos (hn : 0 < n) (β : ℝ) (a c : Fin n → ℝ) (s : ℝ) :
    0 < total β a c s := by
  exact Finset.sum_pos (fun k _ => kernel_pos β a c s k)
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩

theorem kernel_hasDerivAt (β : ℝ) (a c : Fin n → ℝ) (s : ℝ) (k : Fin n) :
    HasDerivAt (fun t => kernel β a c t k)
      (β * (a k - c k) * kernel β a c s k) s := by
  have h := (((hasDerivAt_id s).mul_const (a k - c k)).const_add (c k)).sub_const 1
  convert (h.const_mul β).exp using 1
  dsimp [kernel]
  ring

theorem total_hasDerivAt (β : ℝ) (a c : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (total β a c) (β * first β a c s) s := by
  convert HasDerivAt.fun_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) =>
    kernel_hasDerivAt β a c s k) using 1
  simp only [first, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem first_hasDerivAt (β : ℝ) (a c : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (first β a c) (β * second β a c s) s := by
  convert HasDerivAt.fun_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin n))) =>
    (kernel_hasDerivAt β a c s k).mul_const (a k - c k)) using 1
  simp only [second, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem response_hasDerivAt (hn : 0 < n) (model : Source.Model) (β : ℝ)
    (a c : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (response model β a c) (responseDerivative model β a c s) s := by
  cases model with
  | usa => exact (first_hasDerivAt β a c s).div_const n
  | sa =>
    have hz := (total_pos hn β a c s).ne'
    convert (first_hasDerivAt β a c s).div (total_hasDerivAt β a c s) hz using 1
    dsimp [responseDerivative]
    field_simp

theorem kernel_le_max_endpoints (β : ℝ) (hβ : 0 ≤ β) (a c : Fin n → ℝ)
    {s : ℝ} (hs : s ∈ Icc 0 1) (k : Fin n) :
    kernel β a c s k ≤ max (kernel β a c 1 k) (kernel β a c 0 k) := by
  have hl : c k + s * (a k - c k) ≤ max (a k) (c k) := by
    rcases le_total (a k) (c k) with h | h
    · rw [max_eq_right h]
      nlinarith only [hs.1, h]
    · rw [max_eq_left h]
      nlinarith only [hs.2, h]
  unfold kernel
  simp only [one_mul, zero_mul, add_zero, add_sub_cancel]
  rcases le_total (a k) (c k) with h | h
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (by simpa only [max_eq_right h] using sub_le_sub_right hl 1) hβ)).trans (le_max_right _ _)
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
      (by simpa only [max_eq_left h] using sub_le_sub_right hl 1) hβ)).trans (le_max_left _ _)

theorem second_nonneg (β : ℝ) (a c : Fin n → ℝ) (s : ℝ) :
    0 ≤ second β a c s :=
  Finset.sum_nonneg (fun k _ => mul_nonneg (kernel_pos β a c s k).le (sq_nonneg _))

theorem second_le_endpoints (β : ℝ) (hβ : 0 ≤ β) (a c : Fin n → ℝ)
    {s : ℝ} (hs : s ∈ Icc 0 1) :
    second β a c s ≤ ∑ k, max (kernel β a c 1 k) (kernel β a c 0 k) * (a k - c k) ^ 2 :=
  Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right
    (kernel_le_max_endpoints β hβ a c hs k) (sq_nonneg _))

theorem responseDerivative_le (hn : 0 < n) (model : Source.Model)
    (β : ℝ) (hβ : 0 ≤ β) (a c : Fin n → ℝ) {s : ℝ} (hs : s ∈ Icc 0 1)
    (hz : 1 / 2 ≤ total β a c s) :
    responseDerivative model β a c s ≤
      2 * β * ∑ k, max (kernel β a c 1 k) (kernel β a c 0 k) * (a k - c k) ^ 2 := by
  have hv := second_nonneg β a c s
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnum : 0 ≤ β * second β a c s := mul_nonneg hβ hv
  have hsbd := mul_le_mul_of_nonneg_left (second_le_endpoints β hβ a c hs)
    (show 0 ≤ 2 * β by positivity)
  cases model with
  | usa =>
    dsimp [responseDerivative]
    have hd := div_le_self hnum hn'
    nlinarith only [hd, hsbd, hnum]
  | sa =>
    dsimp [responseDerivative]
    have hd : β * second β a c s / total β a c s ≤ 2 * β * second β a c s := by
      apply (div_le_iff₀ (total_pos hn β a c s)).mpr
      nlinarith only [hz, hnum]
    have hneg : 0 ≤ β * (first β a c s) ^ 2 / (total β a c s) ^ 2 := by positivity
    linarith only [hd, hneg, hsbd]

theorem response_sub_le (hn : 0 < n) (model : Source.Model)
    (β : ℝ) (hβ : 0 ≤ β) (a c : Fin n → ℝ)
    (hz : ∀ s ∈ Icc (0 : ℝ) 1, 1 / 2 ≤ total β a c s) :
    response model β a c 1 - response model β a c 0 ≤
      2 * β * ∑ k, max (kernel β a c 1 k) (kernel β a c 0 k) * (a k - c k) ^ 2 := by
  obtain ⟨s, hs, he⟩ := exists_hasDerivAt_eq_slope (response model β a c)
    (responseDerivative model β a c) (show (0 : ℝ) < 1 by norm_num)
    (fun s _ => (response_hasDerivAt hn model β a c s).continuousAt.continuousWithinAt)
    (fun s _ => response_hasDerivAt hn model β a c s)
  simpa only [sub_zero, div_one, he] using
    responseDerivative_le hn model β hβ a c (Ioo_subset_Icc_self hs)
      (hz s (Ioo_subset_Icc_self hs))


theorem kernel_one (β : ℝ) (a c : Fin n → ℝ) (k : Fin n) :
    kernel β a c 1 k = Real.exp (β * (a k - 1)) := by
  unfold kernel
  congr 1
  ring

theorem kernel_zero (β : ℝ) (a c : Fin n → ℝ) (k : Fin n) :
    kernel β a c 0 k = Real.exp (β * (c k - 1)) := by
  simp only [kernel, zero_mul, add_zero]

theorem kernel_ge_half (β : ℝ) (hβ : 0 ≤ β) (a c : Fin n → ℝ)
    (ε : ℝ) (he : β * ε ^ 2 ≤ 1) (k : Fin n)
    (ha : 1 - a k ≤ ε ^ 2 / 2) (hc : 1 - c k ≤ ε ^ 2 / 2)
    {s : ℝ} (hs : s ∈ Icc 0 1) : 1 / 2 ≤ kernel β a c s k := by
  have hmix : 1 - (c k + s * (a k - c k)) ≤ ε ^ 2 / 2 := by
    have h1 := mul_nonneg hs.1 (sub_nonneg.mpr ha)
    have h2 := mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hc)
    nlinarith only [h1, h2]
  have hb := mul_le_mul_of_nonneg_left hmix hβ
  have hx := Real.add_one_le_exp (β * (c k + s * (a k - c k) - 1))
  change 1 / 2 ≤ Real.exp _
  nlinarith only [hb, he, hx]

theorem coefficient_difference_le {d : ℕ} (hn : 0 < n) (model : Source.Model)
    (β : ℝ) (hβ : 0 ≤ β) (x : Source.Configuration n d) (i j : Fin n)
    (hz : ∀ s ∈ Icc (0 : ℝ) 1,
      1 / 2 ≤ total β (fun k => ⟪(x i).val, (x k).val⟫)
        (fun k => ⟪(x j).val, (x k).val⟫) s) :
    (∑ k, (Source.coefficient model β x i k - Source.coefficient model β x j k) *
      (⟪(x i).val, (x k).val⟫ - ⟪(x j).val, (x k).val⟫)) ≤
      2 * β * ∑ k,
        max (Real.exp (β * (⟪(x i).val, (x k).val⟫ - 1)))
          (Real.exp (β * (⟪(x j).val, (x k).val⟫ - 1))) *
          (⟪(x i).val, (x k).val⟫ - ⟪(x j).val, (x k).val⟫) ^ 2 := by
  have h := response_sub_le hn model β hβ
    (fun k => ⟪(x i).val, (x k).val⟫) (fun k => ⟪(x j).val, (x k).val⟫) hz
  simp only [kernel_one, kernel_zero] at h
  convert h using 1
  cases model <;> simp only [response, first, total, kernel_one, kernel_zero,
    Source.coefficient, Finset.sum_div, ← Finset.sum_sub_distrib]
  all_goals
    apply Finset.sum_congr rfl
    intro k _
    ring

end Metastability.FrozenWeights
