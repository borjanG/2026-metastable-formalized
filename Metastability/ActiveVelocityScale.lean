import Metastability.ActiveVelocity
import Metastability.ActiveAngleScale
import Metastability.ActiveScales

/-! Uniform real-temperature absorption of the explicit two-block velocity error. -/
noncomputable section
open Filter Set
open scoped Topology RealInnerProductSpace
namespace Metastability.ActiveVelocityScale
open Source ActiveCoefficients ActiveVelocity ActiveScales

/-- An exponential gap absorbs the inverse sine-square loss in the active law. -/
theorem eventually_exp_relative (a U c : ℝ) (hgap : U < a) (hc : 0 < c) :
    ∀ᶠ β : ℝ in atTop,
      Real.exp (-a * β) ≤ (c / β * Real.exp (-β * U)) * β ^ (-(1 : ℝ) / 3) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    eventually_mul_exp_le_rpow (1 / c) (a - U) 1 (-(1 : ℝ) / 3) (sub_pos.mpr hgap)]
      with β hβ h
  rw [Real.rpow_one] at h
  calc
    Real.exp (-a * β) = (c / β * Real.exp (-β * U)) *
        ((1 / c) * β * Real.exp (-(a - U) * β)) := by
      rw [show (c / β * Real.exp (-β * U)) *
          ((1 / c) * β * Real.exp (-(a - U) * β)) =
          Real.exp (-β * U) * Real.exp (-(a - U) * β) by field_simp]
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

/-- Numerical estimates independent of the configuration and chosen blocks. -/
theorem eventually_parameters (κ U L c : ℝ)
    (hκ : 0 < κ) (hκU : U < κ) (hUL : U < L) (hL : 0 < L) (hc : 0 < c) :
    ∀ᶠ β : ℝ in atTop,
      1 < β ∧ 1 ≤ Real.log β ∧ mesoscopicScale β ≤ 1 ∧
      β * Real.exp (-κ * β) ≤ β ^ (-(1 : ℝ) / 3) ∧
      kernelError β (Real.exp (-κ * β)) ≤ 2 * β ^ (-(1 : ℝ) / 3) ∧
      Real.exp (-β * L) ≤ β ^ (-(1 : ℝ) / 3) ∧
      Real.exp (-κ * β) ≤ (c / β * Real.exp (-β * U)) * β ^ (-(1 : ℝ) / 3) ∧
      Real.exp (-β * L) ≤ (c / β * Real.exp (-β * U)) * β ^ (-(1 : ℝ) / 3) := by
  have ht : Tendsto (fun β : ℝ => β * Real.exp (-κ * β)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 κ hκ
  have he : Tendsto (fun β : ℝ => Real.exp (β * Real.exp (-κ * β))) atTop (𝓝 1) := by
    simpa only [Real.exp_zero] using Real.continuous_exp.continuousAt.tendsto.comp ht
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_mesoscopicScale.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_mul_exp_le_rpow 1 κ 1 (-(1 : ℝ) / 3) hκ,
    he.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)),
    eventually_mul_exp_le_rpow 1 L 0 (-(1 : ℝ) / 3) hL,
    eventually_exp_relative κ U c hκU hc,
    eventually_exp_relative L U c hUL hc] with β hβ hlog hmeso hδ he hL hrelδ hrelL
  simp only [one_mul, Real.rpow_one] at hδ
  simp only [one_mul, Real.rpow_zero] at hL
  rw [show -L * β = -β * L by ring] at hL hrelL
  refine ⟨hβ, hlog, hmeso.le, hδ, ?_, hL, hrelδ, hrelL⟩
  unfold kernelError
  have hm := mul_le_mul hδ he.le (Real.exp_pos _).le
    (Real.rpow_pos_of_pos (zero_lt_one.trans hβ) (-(1 : ℝ) / 3)).le
  nlinarith only [hm]

/-- Absorb the finite-sum error with explicit constant, retaining the actual
correlation velocity of either source model. -/
theorem correlation_error_bound {n d : ℕ} (model : Model) (β κ U L c : ℝ)
    (hβ : 1 < β) (hlog : 1 ≤ Real.log β) (hc : 0 < c)
    (x : Configuration n d) (B C : Block n) (hB : B.Nonempty) (hC : C.Nonempty)
    (i j : Fin n)
    (hBclose : ∀ k ∈ B, angularDist (x k) (x i) ≤ Real.exp (-κ * β))
    (hCclose : ∀ k ∈ C, angularDist (x k) (x j) ≤ Real.exp (-κ * β))
    (hsepB : ∀ k ∉ B, k ∉ C → L ≤ PairDeficit.deficit x i k)
    (hsepC : ∀ k ∉ C, k ∉ B → L ≤ PairDeficit.deficit x j k)
    (hS : c * (Real.log β / β) ≤ sineSquare x i j)
    (hupper : PairDeficit.deficit x i j ≤ U)
    (hK : kernel β x i j ≤ β ^ (-(1 : ℝ) / 3))
    (hδ : β * Real.exp (-κ * β) ≤ β ^ (-(1 : ℝ) / 3))
    (hH : kernelError β (Real.exp (-κ * β)) ≤ 2 * β ^ (-(1 : ℝ) / 3))
    (hO : Real.exp (-β * L) ≤ β ^ (-(1 : ℝ) / 3))
    (hrelδ : Real.exp (-κ * β) ≤ (c / β * Real.exp (-β * U)) * β ^ (-(1 : ℝ) / 3))
    (hrelO : Real.exp (-β * L) ≤ (c / β * Real.exp (-β * U)) * β ^ (-(1 : ℝ) / 3)) :
    |-PairDeficit.velocity model β x i j - rate model B C *
      (sineSquare x i j * kernel β x i j)| ≤
        (4 + 8 * (n : ℝ) + 10 * (n : ℝ) ^ 2) *
          (sineSquare x i j * kernel β x i j) * β ^ (-(1 : ℝ) / 3) := by
  let p := β ^ (-(1 : ℝ) / 3)
  let S := sineSquare x i j * kernel β x i j
  have hp : 0 ≤ p := (Real.rpow_pos_of_pos (zero_lt_one.trans hβ) _).le
  have hp1 : p ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hβ.le (by norm_num)
  have hK0 : 0 ≤ kernel β x i j := (Real.exp_pos _).le
  have hS0 : 0 ≤ S := mul_nonneg (sineSquare_nonneg x i j) hK0
  have hslow : c / β * Real.exp (-β * U) ≤ S := by
    have hs : c / β ≤ sineSquare x i j := by
      have hm := mul_le_mul_of_nonneg_left hlog (div_pos hc (zero_lt_one.trans hβ)).le
      have hid : c / β * Real.log β = c * (Real.log β / β) := by ring
      rw [hid] at hm
      simpa only [mul_one] using hm.trans hS
    have hk : Real.exp (-β * U) ≤ kernel β x i j := by
      apply Real.exp_le_exp.mpr
      dsimp only [PairDeficit.deficit] at hupper
      nlinarith only [mul_le_mul_of_nonneg_left hupper (zero_lt_one.trans hβ).le]
    exact mul_le_mul hs hk (Real.exp_pos _).le (sineSquare_nonneg x i j)
  have hδS : Real.exp (-κ * β) ≤ S * p := hrelδ.trans (mul_le_mul_of_nonneg_right hslow hp)
  have hOS : Real.exp (-β * L) ≤ S * p := hrelO.trans (mul_le_mul_of_nonneg_right hslow hp)
  dsimp only [p, S] at *
  have hH2 : kernelError β (Real.exp (-κ * β)) ≤ 2 := hH.trans (by linarith only [hp1])
  have hKH : kernel β x i j * (1 + kernelError β (Real.exp (-κ * β))) ≤ 3 * p := by
    dsimp only [p]
    have hh := kernelError_nonneg β (Real.exp (-κ * β)) (zero_lt_one.trans hβ).le (Real.exp_pos _).le
    have hm := mul_le_mul hK (by linarith only [hH2] : 1 + kernelError β (Real.exp (-κ * β)) ≤ 3)
      (by linarith only [hh]) hp
    nlinarith only [hm]
  have hD : denominatorError n β (Real.exp (-κ * β)) (kernel β x i j) (Real.exp (-β * L)) ≤
      5 * n * p := by
    unfold denominatorError
    have hm := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hδ hKH) hO)
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    dsimp only [p] at *
    nlinarith only [hm]
  have hraw := correlation_error model β (Real.exp (-κ * β)) L (zero_lt_one.trans hβ).le
    (Real.exp_pos _).le x B C hB hC i j hBclose hCclose hsepB hsepC
  have hrem := mul_le_mul_of_nonneg_left (add_le_add hH hD)
    (show 0 ≤ 2 * (n : ℝ) * S by positivity)
  have ho := mul_le_mul_of_nonneg_left hOS (show (0 : ℝ) ≤ 4 * n by positivity)
  dsimp only [p, S] at *
  calc
    _ ≤ _ := hraw
    _ ≤ _ := by nlinarith only [hδS, ho, hrem]

/-- The original-time scalar law, uniformly over configurations and both
models. All small error estimates are derived from the fixed barrier gaps,
exponential tightness, and the literal mesoscopic angular range. -/
theorem eventually_correlation_error (n d : ℕ) (κ U L : ℝ)
    (hκ : 0 < κ) (hκU : U < κ) (hUL : U < L) (hL : 0 < L) (hU : U < 2) :
    ∀ᶠ β : ℝ in atTop, 1 < β ∧ ∀ (model : Model) (x : Configuration n d)
      (B C : Block n), B.Nonempty → C.Nonempty → ∀ (i j : Fin n),
      (∀ k ∈ B, angularDist (x k) (x i) ≤ Real.exp (-κ * β)) →
      (∀ k ∈ C, angularDist (x k) (x j) ≤ Real.exp (-κ * β)) →
      (∀ k ∉ B, k ∉ C → L ≤ PairDeficit.deficit x i k) →
      (∀ k ∉ C, k ∉ B → L ≤ PairDeficit.deficit x j k) →
      PairDeficit.deficit x i j ≤ U →
      mesoscopicScale β ≤ angularDist (x i) (x j) →
      |-PairDeficit.velocity model β x i j - rate model B C *
        (sineSquare x i j * kernel β x i j)| ≤
        (4 + 8 * (n : ℝ) + 10 * (n : ℝ) ^ 2) *
          (sineSquare x i j * kernel β x i j) * β ^ (-(1 : ℝ) / 3) := by
  have hc : 0 < (2 / 5 : ℝ) * (2 - U) := mul_pos (by norm_num) (sub_pos.mpr hU)
  filter_upwards [eventually_parameters κ U L ((2 / 5 : ℝ) * (2 - U)) hκ hκU hUL hL hc]
    with β h
  obtain ⟨hβ, hlog, hsmall, hδ, hH, hO, hrelδ, hrelO⟩ := h
  refine ⟨hβ, ?_⟩
  intro model x B C hB hC i j hBclose hCclose hsepB hsepC hupper hangle
  exact correlation_error_bound model β κ U L ((2 / 5 : ℝ) * (2 - U)) hβ hlog hc
    x B C hB hC i j hBclose hCclose hsepB hsepC
    (ActiveAngleScale.sine_sq_lower β U hβ hU hsmall (x i) (x j) hangle hupper)
    hupper (ActiveAngleScale.kernel_le_third_power β hβ hsmall (x i) (x j) hangle)
    hδ hH hO hrelδ hrelO

end Metastability.ActiveVelocityScale
