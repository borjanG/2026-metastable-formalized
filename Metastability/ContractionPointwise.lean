import Metastability.PairDeficit
import Metastability.FrozenWeights
import Metastability.KernelComparison
import Metastability.ContractionInteraction

/-!
Pointwise contraction of an arbitrary tight block for both source vector fields.
The proof compares frozen weights along an affine chord; its SA derivative is
a variance. All estimates are derived from the literal particle coefficients.
-/
noncomputable section
open Set
open scoped BigOperators RealInnerProductSpace
namespace Metastability.ContractionPointwise
open Source
variable {n d : ℕ}

theorem kernel_le_one (β : ℝ) (hβ : 0 ≤ β) (u v : Sphere d) :
    Real.exp (β * (⟪u.val, v.val⟫ - 1)) ≤ 1 :=
  Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonneg_of_nonpos hβ (sub_nonpos.mpr (ModelBounds.inner_bounds u v).2))

theorem normalization_le_n (β : ℝ) (hβ : 0 ≤ β) (x : Configuration n d) (i : Fin n) :
    (∑ k, Real.exp (β * (⟪(x i).val, (x k).val⟫ - 1))) ≤ n := by
  calc
    _ ≤ ∑ _ : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun k _ => kernel_le_one β hβ _ _)
    _ = n := by simp

theorem coefficient_ge_kernel_div_n (model : Model) (β : ℝ) (hβ : 0 ≤ β)
    (x : Configuration n d) (i k : Fin n) :
    Real.exp (β * (⟪(x i).val, (x k).val⟫ - 1)) / n ≤ coefficient model β x i k := by
  cases model with
  | usa => rfl
  | sa =>
    unfold coefficient
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le
      (lt_of_lt_of_le zero_lt_one (ModelBounds.normalization_ge_one β x i))
      (normalization_le_n β hβ x i)

theorem coefficient_ge_half_div_n (hn : 0 < n) (model : Model)
    (β : ℝ) (hβ : 0 ≤ β) (ε : ℝ) (he : β * ε ^ 2 ≤ 1)
    (x : Configuration n d) (i k : Fin n)
    (hclose : angularDist (x i) (x k) ≤ ε) :
    1 / (2 * (n : ℝ)) ≤ coefficient model β x i k := by
  have hq := KernelComparison.one_sub_inner_le_sq_half_of_angle_le (x i) (x k) ε hclose
  have hb := mul_le_mul_of_nonneg_left hq hβ
  have he' := Real.add_one_le_exp (β * (⟪(x i).val, (x k).val⟫ - 1))
  have hk : 1 / 2 ≤ Real.exp (β * (⟪(x i).val, (x k).val⟫ - 1)) := by
    nlinarith only [hb, he, he']
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    1 / (2 * (n : ℝ)) = (1 / 2 : ℝ) / n := by ring
    _ ≤ Real.exp (β * (⟪(x i).val, (x k).val⟫ - 1)) / n :=
      div_le_div_of_nonneg_right hk hn'.le
    _ ≤ _ := coefficient_ge_kernel_div_n model β hβ x i k

theorem chord_total_ge_half (β : ℝ) (hβ : 0 ≤ β) (ε : ℝ) (he : β * ε ^ 2 ≤ 1)
    (x : Configuration n d) (D : Block n) (hD : D.Nonempty)
    (hdiam : ∀ a ∈ D, ∀ b ∈ D, angularDist (x a) (x b) ≤ ε)
    (i j : Fin n) (hi : i ∈ D) (hj : j ∈ D) :
    ∀ s ∈ Icc (0 : ℝ) 1,
      1 / 2 ≤ FrozenWeights.total β (fun k => ⟪(x i).val, (x k).val⟫)
        (fun k => ⟪(x j).val, (x k).val⟫) s := by
  obtain ⟨k, hk⟩ := hD
  intro s hs
  apply (FrozenWeights.kernel_ge_half β hβ
    (fun l => ⟪(x i).val, (x l).val⟫) (fun l => ⟪(x j).val, (x l).val⟫) ε he k
    (KernelComparison.one_sub_inner_le_sq_half_of_angle_le _ _ ε (hdiam i hi k hk))
    (KernelComparison.one_sub_inner_le_sq_half_of_angle_le _ _ ε (hdiam j hj k hk)) hs).trans
  exact Finset.single_le_sum (fun l _ => (FrozenWeights.kernel_pos β _ _ s l).le)
    (Finset.mem_univ k)


theorem sum_split (D : Block n) (f : Fin n → ℝ) :
    (∑ k, f k) = (∑ k ∈ D, f k) + ∑ k ∈ Finset.univ \ D, f k := by
  have h := Finset.sum_sdiff (f := f) (Finset.subset_univ D)
  linarith only [h]

theorem kernel_le_interaction (β : ℝ) (hβ : 0 ≤ β) (u v : Sphere d) :
    Real.exp (β * (⟪u.val, v.val⟫ - 1)) ≤ ContractionInteraction.interaction β u v := by
  rw [ContractionInteraction.interaction_eq_inner]
  have ha : ⟪u.val, v.val⟫ ^ 2 ≤ 1 := by
    obtain ⟨hl, hu⟩ := ModelBounds.inner_bounds u v
    nlinarith only [hl, hu]
  exact le_mul_of_one_le_left (Real.exp_pos _).le
    (by nlinarith only [mul_nonneg hβ (sub_nonneg.mpr ha)])

theorem average_sum_lower (hn : 0 < n) (model : Model) (β : ℝ) (hβ : 0 ≤ β)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (he : β * ε ^ 2 ≤ 1)
    (x : Configuration n d) (D : Block n) (hD : D.Nonempty)
    (hdiam : ∀ a ∈ D, ∀ b ∈ D, angularDist (x a) (x b) ≤ ε)
    (i j : Fin n) (hi : i ∈ D) (hj : j ∈ D) :
    1 / (n : ℝ) - 4 * ContractionInteraction.exterior β x D hD ≤
      ∑ k, (coefficient model β x i k + coefficient model β x j k) *
        (⟪(x i).val, (x k).val⟫ + ⟪(x j).val, (x k).val⟫) := by
  let R : Fin n → ℝ := fun k => D.sup' hD
    (fun a => ContractionInteraction.interaction β (x a) (x k))
  let f : Fin n → ℝ := fun k =>
    (coefficient model β x i k + coefficient model β x j k) *
      (⟪(x i).val, (x k).val⟫ + ⟪(x j).val, (x k).val⟫)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hint : ∀ k ∈ D, 1 / (n : ℝ) ≤ f k := by
    intro k hk
    have hci := coefficient_ge_half_div_n hn model β hβ ε he x i k (hdiam i hi k hk)
    have hcj := coefficient_ge_half_div_n hn model β hβ ε he x j k (hdiam j hj k hk)
    have hqik := KernelComparison.one_sub_inner_le_sq_half_of_angle_le _ _ ε (hdiam i hi k hk)
    have hqjk := KernelComparison.one_sub_inner_le_sq_half_of_angle_le _ _ ε (hdiam j hj k hk)
    have hs : 1 ≤ ⟪(x i).val, (x k).val⟫ + ⟪(x j).val, (x k).val⟫ := by
      nlinarith only [hqik, hqjk, hε0, hε1]
    have hcoef : 1 / (n : ℝ) ≤ coefficient model β x i k + coefficient model β x j k := by
      have heq : 1 / (2 * (n : ℝ)) + 1 / (2 * (n : ℝ)) = 1 / n := by ring
      linarith only [hci, hcj, heq]
    exact hcoef.trans (le_mul_of_one_le_right
      (add_nonneg (ModelBounds.coefficient_nonneg model β x i k)
        (ModelBounds.coefficient_nonneg model β x j k)) hs)
  have hout : ∀ k, -4 * R k ≤ f k := by
    intro k
    have hci : coefficient model β x i k ≤ R k :=
      (ModelBounds.coefficient_le_kernel model β x i k).trans
        ((kernel_le_interaction β hβ _ _).trans
          (ContractionInteraction.interaction_le_sup β x D hD hi k))
    have hcj : coefficient model β x j k ≤ R k :=
      (ModelBounds.coefficient_le_kernel model β x j k).trans
        ((kernel_le_interaction β hβ _ _).trans
          (ContractionInteraction.interaction_le_sup β x D hD hj k))
    have hpos := add_nonneg (ModelBounds.coefficient_nonneg model β x i k)
      (ModelBounds.coefficient_nonneg model β x j k)
    have hs : -2 ≤ ⟪(x i).val, (x k).val⟫ + ⟪(x j).val, (x k).val⟫ := by
      linarith only [(ModelBounds.inner_bounds (x i) (x k)).1,
        (ModelBounds.inner_bounds (x j) (x k)).1]
    have hh := mul_le_mul_of_nonneg_left hs hpos
    dsimp [f]
    nlinarith only [hci, hcj, hh]
  have hsint : 1 / (n : ℝ) ≤ ∑ k ∈ D, f k := by
    have hh := Finset.sum_le_sum hint
    have hcard : (1 : ℝ) ≤ D.card := by exact_mod_cast (Finset.card_pos.mpr hD)
    have hcarddiv := div_le_div_of_nonneg_right hcard hn'.le
    simp only [Finset.sum_const, nsmul_eq_mul] at hh
    exact hcarddiv.trans (by simpa only [div_eq_mul_inv, one_mul] using hh)
  have hsout : -4 * ContractionInteraction.exterior β x D hD ≤
      ∑ k ∈ Finset.univ \ D, f k := by
    have hh := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ \ D) => hout k)
    simpa only [← Finset.mul_sum, ContractionInteraction.exterior, R] using hh
  change 1 / (n : ℝ) - 4 * ContractionInteraction.exterior β x D hD ≤ ∑ k, f k
  rw [sum_split D f]
  linarith only [hsint, hsout]



theorem weighted_square_sum_upper (β : ℝ) (hβ : 0 ≤ β) (ε : ℝ) (he : β * ε ^ 2 ≤ 1)
    (x : Configuration n d) (D : Block n) (hD : D.Nonempty)
    (hdiam : ∀ a ∈ D, ∀ b ∈ D, angularDist (x a) (x b) ≤ ε)
    (i j : Fin n) (hi : i ∈ D) (hj : j ∈ D) :
    β * (∑ k,
      max (Real.exp (β * (⟪(x i).val, (x k).val⟫ - 1)))
        (Real.exp (β * (⟪(x j).val, (x k).val⟫ - 1))) *
        (⟪(x i).val, (x k).val⟫ - ⟪(x j).val, (x k).val⟫) ^ 2) ≤
      5 * n * β * PairDeficit.deficit x i j * ε ^ 2 +
        4 * PairDeficit.deficit x i j * ContractionInteraction.exterior β x D hD := by
  let q := PairDeficit.deficit x i j
  let f : Fin n → ℝ := fun k => β *
    max (Real.exp (β * (⟪(x i).val, (x k).val⟫ - 1)))
      (Real.exp (β * (⟪(x j).val, (x k).val⟫ - 1))) *
      (⟪(x i).val, (x k).val⟫ - ⟪(x j).val, (x k).val⟫) ^ 2
  let R : Fin n → ℝ := fun k => D.sup' hD
    (fun a => ContractionInteraction.interaction β (x a) (x k))
  have hq : 0 ≤ q := PairDeficit.deficit_nonneg x i j
  have hqsmall : β * q ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left
      (KernelComparison.one_sub_inner_le_sq_half_of_angle_le _ _ ε (hdiam i hi j hj)) hβ
    change β * (1 - ⟪(x i).val, (x j).val⟫) ≤ 1
    nlinarith only [h, he]
  have hint : ∀ k ∈ D, f k ≤ 5 * β * q * ε ^ 2 := by
    intro k hk
    have hm : max (Real.exp (β * (⟪(x i).val, (x k).val⟫ - 1)))
        (Real.exp (β * (⟪(x j).val, (x k).val⟫ - 1))) ≤ 1 :=
      max_le (kernel_le_one β hβ _ _) (kernel_le_one β hβ _ _)
    have hm' := mul_le_mul_of_nonneg_right hm
      (sq_nonneg (⟪(x i).val, (x k).val⟫ - ⟪(x j).val, (x k).val⟫))
    have hg := KernelComparison.inner_sub_sq_le_of_angles_le (x i) (x j) (x k) ε
      (hdiam i hi j hj) (hdiam i hi k hk)
    have h := mul_le_mul_of_nonneg_left (hm'.trans (by simpa only [one_mul] using hg)) hβ
    dsimp [f, q, PairDeficit.deficit]
    nlinarith only [h]
  have hout : ∀ k, f k ≤ 4 * q * R k := by
    intro k
    have hh := KernelComparison.kernel_weighted_inner_sub_sq_le_max β hβ (x i) (x j) (x k) hqsmall
    rw [← ContractionInteraction.interaction_eq_inner,
      ← ContractionInteraction.interaction_eq_inner] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (ContractionInteraction.max_interaction_le_sup β x D hD hi hj k)
      (mul_nonneg (by norm_num) hq))
  have hsint : (∑ k ∈ D, f k) ≤ 5 * n * β * q * ε ^ 2 := by
    have hh := Finset.sum_le_sum hint
    simp only [Finset.sum_const, nsmul_eq_mul] at hh
    have hc : (D.card : ℝ) ≤ n := by
      exact_mod_cast (show D.card ≤ n by simpa using Finset.card_le_card (Finset.subset_univ D))
    have hm := mul_le_mul_of_nonneg_right hc (show 0 ≤ 5 * β * q * ε ^ 2 by positivity)
    nlinarith only [hh, hm]
  have hsout : (∑ k ∈ Finset.univ \ D, f k) ≤
      4 * q * ContractionInteraction.exterior β x D hD := by
    have hh := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ \ D) => hout k)
    simpa only [← Finset.mul_sum, ContractionInteraction.exterior, R] using hh
  have heq : β * (∑ k,
      max (Real.exp (β * (⟪(x i).val, (x k).val⟫ - 1)))
        (Real.exp (β * (⟪(x j).val, (x k).val⟫ - 1))) *
        (⟪(x i).val, (x k).val⟫ - ⟪(x j).val, (x k).val⟫) ^ 2) = ∑ k, f k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [f]
    ring
  rw [heq, sum_split D f]
  linarith only [hsint, hsout]

/-- The source contraction inequality with explicit constants. No dynamical
or Hessian estimate is assumed: all inputs are the pointwise diameter scale. -/
theorem velocity_le (hn : 0 < n) (model : Model) (β : ℝ) (hβ : 0 ≤ β)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hβε : β * ε ^ 2 ≤ 1 / (40 * (n : ℝ) ^ 2))
    (x : Configuration n d) (D : Block n) (hD : D.Nonempty)
    (hdiam : ∀ a ∈ D, ∀ b ∈ D, angularDist (x a) (x b) ≤ ε)
    (i j : Fin n) (hi : i ∈ D) (hj : j ∈ D) :
    PairDeficit.velocity model β x i j ≤
      (-(1 / (4 * (n : ℝ))) + 10 * ContractionInteraction.exterior β x D hD) *
        PairDeficit.deficit x i j := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he : β * ε ^ 2 ≤ 1 := by
    have hden : (1 : ℝ) ≤ 40 * (n : ℝ) ^ 2 := by nlinarith only [hn1]
    exact hβε.trans ((one_div_le_one_div_of_le zero_lt_one hden).trans_eq (by norm_num))
  let q := PairDeficit.deficit x i j
  let L := ContractionInteraction.exterior β x D hD
  have hq : 0 ≤ q := PairDeficit.deficit_nonneg x i j
  have hL : 0 ≤ L := ContractionInteraction.exterior_nonneg β hβ x D hD
  have havg := average_sum_lower hn model β hβ ε hε0 hε1 he x D hD hdiam i j hi hj
  have hdiff := FrozenWeights.coefficient_difference_le hn model β hβ x i j
    (chord_total_ge_half β hβ ε he x D hD hdiam i j hi hj)
  have hsq := weighted_square_sum_upper β hβ ε he x D hD hdiam i j hi hj
  have hdiff' : (∑ k, (coefficient model β x i k - coefficient model β x j k) *
      (⟪(x i).val, (x k).val⟫ - ⟪(x j).val, (x k).val⟫)) ≤
      10 * n * β * q * ε ^ 2 + 8 * q * L := by
    dsimp [q, L]
    nlinarith only [hdiff, hsq]
  have hf0 : 0 ≤ (1 + ⟪(x i).val, (x j).val⟫) / 2 := by
    linarith only [(ModelBounds.inner_bounds (x i) (x j)).1]
  have hf1 : (1 + ⟪(x i).val, (x j).val⟫) / 2 ≤ 1 := by
    linarith only [(ModelBounds.inner_bounds (x i) (x j)).2]
  have hm : 0 ≤ 10 * (n : ℝ) * β * q * ε ^ 2 + 8 * q * L := by positivity
  have hterm := (mul_le_mul_of_nonneg_left hdiff' hf0).trans
    (mul_le_of_le_one_left hm hf1)
  have hneg := mul_le_mul_of_nonpos_left havg (show -q / 2 ≤ 0 by linarith only [hq])
  have habsorb : 10 * (n : ℝ) * β * ε ^ 2 ≤ 1 / (4 * (n : ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * (n : ℝ))).mpr
    have hh := (le_div_iff₀ (by positivity : 0 < 40 * (n : ℝ) ^ 2)).mp hβε
    nlinarith only [hh]
  have habsorbq := mul_le_mul_of_nonneg_right habsorb hq
  rw [PairDeficit.velocity_eq_symmetric]
  change _ ≤ (-(1 / (4 * (n : ℝ))) + 10 * L) * q
  have hrecip : 1 / (n : ℝ) = 4 * (1 / (4 * (n : ℝ))) := by ring
  rw [hrecip] at hneg
  dsimp [q, L] at hneg hterm habsorbq ⊢
  nlinarith only [hneg, hterm, habsorbq]


end Metastability.ContractionPointwise
