import Metastability.AngularGeometry
import Metastability.ModelBounds

/-!
# Endpoint kernel comparisons for block contraction

These estimates use endpoint inner products and a tangent decomposition.
They supply the kernel error terms in an alternative proof of the source
block-contraction lemma, without assuming a geodesic Hessian bound.
-/

noncomputable section
open scoped RealInnerProductSpace

namespace Metastability.KernelComparison

open Source
variable {d : ℕ}

/-- The tangent-line inequality for the exponential, based at its first argument. -/
theorem exp_sub_le_exp_mul_sub (x y : ℝ) :
    Real.exp x - Real.exp y ≤ Real.exp x * (x - y) := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (y - x))
    (Real.exp_pos x).le
  rw [← Real.exp_add, add_sub_cancel] at h
  nlinarith only [h]

/-- Monotonicity and the endpoint maximum bound for a shifted exponential.
The comparison holds for arbitrary real endpoint values, not just [-1,1]. -/
theorem kernel_difference_bounds (β a c : ℝ) (hβ : 0 ≤ β) :
    0 ≤ (Real.exp (β * (a - 1)) - Real.exp (β * (c - 1))) * (a - c) ∧
      (Real.exp (β * (a - 1)) - Real.exp (β * (c - 1))) * (a - c) ≤
        β * max (Real.exp (β * (a - 1))) (Real.exp (β * (c - 1))) * (a - c) ^ 2 := by
  have hord : ∀ a c : ℝ, c ≤ a →
      0 ≤ (Real.exp (β * (a - 1)) - Real.exp (β * (c - 1))) * (a - c) ∧
        (Real.exp (β * (a - 1)) - Real.exp (β * (c - 1))) * (a - c) ≤
          β * max (Real.exp (β * (a - 1))) (Real.exp (β * (c - 1))) * (a - c) ^ 2 := by
    intro a c hca
    have he : Real.exp (β * (c - 1)) ≤ Real.exp (β * (a - 1)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right hca 1) hβ)
    refine ⟨mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr hca), ?_⟩
    rw [max_eq_left he]
    have h := mul_le_mul_of_nonneg_right
      (exp_sub_le_exp_mul_sub (β * (a - 1)) (β * (c - 1))) (sub_nonneg.mpr hca)
    nlinarith only [h]
  rcases le_total c a with hca | hac
  · exact hord a c hca
  · obtain ⟨hlo, hhi⟩ := hord c a hac
    rw [max_comm] at hhi
    constructor <;> nlinarith only [hlo, hhi]

/-- The unit-vector tangent decomposition controls the difference of two
correlations by the pair deficit and the first endpoint's transverse variance. -/
theorem inner_sub_sq_le (u v w : Sphere d) :
    (⟪u.val, w.val⟫ - ⟪v.val, w.val⟫) ^ 2 ≤
      4 * (1 - ⟪u.val, v.val⟫) * (1 - ⟪u.val, w.val⟫ ^ 2) +
        2 * (1 - ⟪u.val, v.val⟫) ^ 2 := by
  let a : ℝ := ⟪u.val, w.val⟫
  let c : ℝ := ⟪v.val, w.val⟫
  let q : ℝ := 1 - ⟪u.val, v.val⟫
  have huu : ⟪u.val, u.val⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, u.property, one_pow]
  have hvv : ⟪v.val, v.val⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, v.property, one_pow]
  have hww : ⟪w.val, w.val⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, w.property, one_pow]
  have hvu : ⟪v.val, u.val⟫ = ⟪u.val, v.val⟫ := real_inner_comm _ _
  have hwu : ⟪w.val, u.val⟫ = a := real_inner_comm _ _
  have hcs := real_inner_mul_inner_self_le (u.val - v.val) (w.val - a • u.val)
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    huu, hvv, hww, hvu, hwu, mul_one] at hcs
  have ht : (a - c - a * q) ^ 2 ≤ 2 * q * (1 - a ^ 2) := by
    dsimp [a, c, q] at hcs ⊢
    nlinarith only [hcs]
  have ha : a ^ 2 ≤ 1 := by
    obtain ⟨hal, hau⟩ := ModelBounds.inner_bounds u w
    dsimp [a]
    nlinarith only [hal, hau]
  have haq : (a * q) ^ 2 ≤ q ^ 2 := by
    have h := mul_le_mul_of_nonneg_right ha (sq_nonneg q)
    nlinarith only [h]
  have hs := add_sq_le (a := a - c - a * q) (b := a * q)
  change (a - c) ^ 2 ≤ 4 * q * (1 - a ^ 2) + 2 * q ^ 2
  nlinarith only [ht, haq, hs]

/-- The same estimate with the second endpoint's transverse variance. -/
theorem inner_sub_sq_le_symm (u v w : Sphere d) :
    (⟪u.val, w.val⟫ - ⟪v.val, w.val⟫) ^ 2 ≤
      4 * (1 - ⟪u.val, v.val⟫) * (1 - ⟪v.val, w.val⟫ ^ 2) +
        2 * (1 - ⟪u.val, v.val⟫) ^ 2 := by
  have h := inner_sub_sq_le v u w
  rw [real_inner_comm u.val v.val] at h
  nlinarith only [h]

/-- A small angular distance gives the usual quadratic correlation deficit. -/
theorem one_sub_inner_le_sq_half_of_angle_le (u v : Sphere d) (ε : ℝ)
    (hangle : angularDist u v ≤ ε) :
    1 - ⟪u.val, v.val⟫ ≤ ε ^ 2 / 2 := by
  have hangle0 := AngularGeometry.angularDist_nonneg u v
  have hs := (sq_le_sq₀ hangle0 (hangle0.trans hangle)).mpr hangle
  have hc : 1 - angularDist u v ^ 2 / 2 ≤ Real.cos (angularDist u v) :=
    Real.one_sub_sq_div_two_le_cos
  rw [AngularGeometry.cos_angularDist] at hc
  nlinarith only [hs, hc]

/-- Internal particles in a tight block have a correlation-difference bound
that retains the vanishing pair deficit as a factor. -/
theorem inner_sub_sq_le_of_small_deficits (u v w : Sphere d) (ε : ℝ)
    (huv : 1 - ⟪u.val, v.val⟫ ≤ ε ^ 2 / 2)
    (huw : 1 - ⟪u.val, w.val⟫ ≤ ε ^ 2 / 2) :
    (⟪u.val, w.val⟫ - ⟪v.val, w.val⟫) ^ 2 ≤
      5 * (1 - ⟪u.val, v.val⟫) * ε ^ 2 := by
  have hq : 0 ≤ 1 - ⟪u.val, v.val⟫ := sub_nonneg.mpr (ModelBounds.inner_bounds u v).2
  have ha : 1 - ⟪u.val, w.val⟫ ^ 2 ≤ ε ^ 2 := by
    nlinarith only [huw, sq_nonneg (1 - ⟪u.val, w.val⟫)]
  have hqa := mul_le_mul_of_nonneg_left ha hq
  have hqq := mul_le_mul_of_nonneg_left huv hq
  nlinarith only [inner_sub_sq_le u v w, hqa, hqq]

theorem inner_sub_sq_le_of_angles_le (u v w : Sphere d) (ε : ℝ)
    (huv : angularDist u v ≤ ε) (huw : angularDist u w ≤ ε) :
    (⟪u.val, w.val⟫ - ⟪v.val, w.val⟫) ^ 2 ≤
      5 * (1 - ⟪u.val, v.val⟫) * ε ^ 2 :=
  inner_sub_sq_le_of_small_deficits u v w ε
    (one_sub_inner_le_sq_half_of_angle_le u v ε huv)
    (one_sub_inner_le_sq_half_of_angle_le u w ε huw)

/-- At either endpoint, the weighted correlation-difference square is
controlled by the source exterior interaction density at that endpoint. -/
theorem kernel_weighted_inner_sub_sq_le_left (β : ℝ) (hβ : 0 ≤ β)
    (u v w : Sphere d) (hsmall : β * (1 - ⟪u.val, v.val⟫) ≤ 1) :
    β * Real.exp (β * (⟪u.val, w.val⟫ - 1)) *
        (⟪u.val, w.val⟫ - ⟪v.val, w.val⟫) ^ 2 ≤
      4 * (1 - ⟪u.val, v.val⟫) *
        ((1 + β * (1 - ⟪u.val, w.val⟫ ^ 2)) *
          Real.exp (β * (⟪u.val, w.val⟫ - 1))) := by
  let q : ℝ := 1 - ⟪u.val, v.val⟫
  let a : ℝ := ⟪u.val, w.val⟫
  let c : ℝ := ⟪v.val, w.val⟫
  have hq : 0 ≤ q := sub_nonneg.mpr (ModelBounds.inner_bounds u v).2
  have hg : (a - c) ^ 2 ≤ 4 * q * (1 - a ^ 2) + 2 * q ^ 2 :=
    inner_sub_sq_le u v w
  have h₁ := mul_le_mul_of_nonneg_left hg hβ
  have h₂ := mul_le_mul_of_nonneg_right hsmall hq
  have hb : β * (a - c) ^ 2 ≤ 4 * q * (1 + β * (1 - a ^ 2)) := by
    change β * q * q ≤ 1 * q at h₂
    nlinarith only [h₁, h₂, hq]
  have h := mul_le_mul_of_nonneg_right hb (Real.exp_pos (β * (a - 1))).le
  change β * Real.exp (β * (a - 1)) * (a - c) ^ 2 ≤
    4 * q * ((1 + β * (1 - a ^ 2)) * Real.exp (β * (a - 1)))
  nlinarith only [h]

/-- The endpoint maximum of the kernels is controlled by the endpoint maximum
of the complete exterior densities. This is the form used after normalizing SA. -/
theorem kernel_weighted_inner_sub_sq_le_max (β : ℝ) (hβ : 0 ≤ β)
    (u v w : Sphere d) (hsmall : β * (1 - ⟪u.val, v.val⟫) ≤ 1) :
    β * max (Real.exp (β * (⟪u.val, w.val⟫ - 1)))
        (Real.exp (β * (⟪v.val, w.val⟫ - 1))) *
        (⟪u.val, w.val⟫ - ⟪v.val, w.val⟫) ^ 2 ≤
      4 * (1 - ⟪u.val, v.val⟫) *
        max ((1 + β * (1 - ⟪u.val, w.val⟫ ^ 2)) * Real.exp (β * (⟪u.val, w.val⟫ - 1)))
          ((1 + β * (1 - ⟪v.val, w.val⟫ ^ 2)) * Real.exp (β * (⟪v.val, w.val⟫ - 1))) := by
  have hq : 0 ≤ 4 * (1 - ⟪u.val, v.val⟫) :=
    mul_nonneg (by norm_num) (sub_nonneg.mpr (ModelBounds.inner_bounds u v).2)
  rcases le_total (Real.exp (β * (⟪v.val, w.val⟫ - 1)))
      (Real.exp (β * (⟪u.val, w.val⟫ - 1))) with hle | hle
  · rw [max_eq_left hle]
    exact (kernel_weighted_inner_sub_sq_le_left β hβ u v w hsmall).trans
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hq)
  · rw [max_eq_right hle]
    have hs : β * (1 - ⟪v.val, u.val⟫) ≤ 1 := by
      rw [real_inner_comm u.val v.val]
      exact hsmall
    have h := kernel_weighted_inner_sub_sq_le_left β hβ v u w hs
    rw [real_inner_comm u.val v.val] at h
    have hh := h.trans (mul_le_mul_of_nonneg_left (le_max_right
      ((1 + β * (1 - ⟪u.val, w.val⟫ ^ 2)) * Real.exp (β * (⟪u.val, w.val⟫ - 1))) _) hq)
    nlinarith only [hh]

/-- The exact angular version of the preceding endpoint-density estimate. -/
theorem kernel_weighted_inner_sub_sq_le_max_sin (β : ℝ) (hβ : 0 ≤ β)
    (u v w : Sphere d) (hsmall : β * (1 - ⟪u.val, v.val⟫) ≤ 1) :
    β * max (Real.exp (β * (⟪u.val, w.val⟫ - 1)))
        (Real.exp (β * (⟪v.val, w.val⟫ - 1))) *
        (⟪u.val, w.val⟫ - ⟪v.val, w.val⟫) ^ 2 ≤
      4 * (1 - ⟪u.val, v.val⟫) *
        max ((1 + β * Real.sin (angularDist u w) ^ 2) * Real.exp (β * (⟪u.val, w.val⟫ - 1)))
          ((1 + β * Real.sin (angularDist v w) ^ 2) * Real.exp (β * (⟪v.val, w.val⟫ - 1))) := by
  have hsin (x : Sphere d) : Real.sin (angularDist x w) ^ 2 = 1 - ⟪x.val, w.val⟫ ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (angularDist x w)
    rw [AngularGeometry.cos_angularDist] at h
    linarith only [h]
  simp only [hsin]
  exact kernel_weighted_inner_sub_sq_le_max β hβ u v w hsmall

end Metastability.KernelComparison
