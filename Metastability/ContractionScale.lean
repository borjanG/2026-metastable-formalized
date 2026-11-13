import Metastability.PairDeficit
import Metastability.AngularGeometry
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The visible scale and final diameter conversion for block contraction

All limits use real inverse temperature and the literal source visible scale.
The angular estimates retain the source metric and its exact cosine deficit.
-/

noncomputable section
open Filter Set
open scoped Topology RealInnerProductSpace

namespace Metastability.ContractionScale

open Source

theorem visibleScale_pos {β : ℝ} (hβ : 1 < β) : 0 < visibleScale β := by
  have hβ0 : 0 < β := lt_trans zero_lt_one hβ
  have hlog : 0 < Real.log β := Real.log_pos hβ
  unfold visibleScale
  positivity

theorem visibleScale_eq_sqrt (β : ℝ) :
    visibleScale β = Real.sqrt (1 / (β * Real.log β)) := by
  simp only [visibleScale, one_div, Real.sqrt_inv]

theorem tendsto_visibleScale : Tendsto visibleScale atTop (𝓝 0) := by
  have hp : Tendsto (fun β : ℝ => β * Real.log β) atTop atTop :=
    tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop
  have hi : Tendsto (fun β : ℝ => 1 / (β * Real.log β)) atTop (𝓝 0) := by
    simpa only [one_div] using hp.inv_tendsto_atTop
  change Tendsto (fun β : ℝ => 1 / Real.sqrt (β * Real.log β)) atTop (𝓝 0)
  simpa only [Function.comp_def, visibleScale, one_div, Real.sqrt_inv, Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hi

theorem beta_mul_visibleScale_sq {β : ℝ} (hβ : 1 < β) :
    β * visibleScale β ^ 2 = 1 / Real.log β := by
  have hβ0 : 0 < β := lt_trans zero_lt_one hβ
  have hlog : 0 < Real.log β := Real.log_pos hβ
  unfold visibleScale
  rw [div_pow, one_pow, Real.sq_sqrt (mul_pos hβ0 hlog).le]
  field_simp

theorem tendsto_beta_mul_visibleScale_sq :
    Tendsto (fun β : ℝ => β * visibleScale β ^ 2) atTop (𝓝 0) := by
  have h : Tendsto (fun β : ℝ => 1 / Real.log β) atTop (𝓝 0) := by
    simpa only [one_div] using Real.tendsto_log_atTop.inv_tendsto_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with β hβ
  exact (beta_mul_visibleScale_sq hβ).symm

/-- A uniform sufficiently-low-temperature domain for the static estimate. -/
theorem eventually_visibleScale_small (n : ℕ) (hn : 0 < n) :
    ∀ᶠ β : ℝ in atTop, 1 < β ∧ 0 < visibleScale β ∧ visibleScale β ≤ 1 ∧
      β * visibleScale β ^ 2 ≤ 1 / (40 * (n : ℝ) ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have he := tendsto_visibleScale.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hb := tendsto_beta_mul_visibleScale_sq.eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (40 * (n : ℝ) ^ 2)))
  filter_upwards [eventually_gt_atTop (1 : ℝ), he, hb] with β hβ hε hsmall
  exact ⟨hβ, visibleScale_pos hβ, hε.le, hsmall.le⟩

/-- The exterior source barrier defeats the polynomial prefactor. -/
theorem tendsto_exterior_bound (n : ℕ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun β : ℝ => (n : ℝ) * (1 + β) * Real.exp (-β * b))
      atTop (𝓝 0) := by
  have h0 : Tendsto (fun β : ℝ => Real.exp (-b * β)) atTop (𝓝 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 b hb
  have h1 : Tendsto (fun β : ℝ => β * Real.exp (-b * β)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 b hb
  convert (h0.add h1).const_mul (n : ℝ) using 1
  · ext β
    rw [show -β * b = -b * β by ring]
    ring
  · norm_num

/-- The source time-length condition gives the final exponential diameter
bound. The conclusion also holds for arbitrary real kappa under this condition. -/
theorem eventually_diameter_exponential_bound (c κ C : ℝ)
    (hc : 0 < c) (hC : 8 * κ / c < C) :
    ∀ᶠ β : ℝ in atTop,
      2 * visibleScale β ^ 2 * Real.exp (-c * C * β / 2) ≤ Real.exp (-4 * κ * β) := by
  have hgap : 4 * κ < c * C / 2 := by
    have h := (div_lt_iff₀ hc).mp hC
    nlinarith only [h]
  have he := tendsto_visibleScale.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [eventually_gt_atTop (1 : ℝ), he] with β hβ hε
  have hε0 := (visibleScale_pos hβ).le
  have hcoeff : 2 * visibleScale β ^ 2 ≤ 1 := by
    nlinarith only [hε0, hε]
  have hβ0 : 0 ≤ β := by linarith only [hβ]
  calc
    2 * visibleScale β ^ 2 * Real.exp (-c * C * β / 2) ≤
        1 * Real.exp (-c * C * β / 2) :=
      mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le
    _ ≤ Real.exp (-4 * κ * β) := by
      rw [one_mul]
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_le_mul_of_nonneg_right hgap.le hβ0]

/-- The elementary angular-to-deficit estimate used at the final time. -/
theorem sq_le_four_mul_one_sub_cos {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    θ ^ 2 ≤ 4 * (1 - Real.cos θ) := by
  rcases hθ0.eq_or_lt with hzero | hpos
  · rw [← hzero]
    norm_num
  have hh0 : 0 < θ / 2 := by linarith only [hpos]
  have hh1 : θ / 2 ≤ 1 := by linarith only [hθ1]
  have hsin := (Real.sin_gt_sub_cube hh0 hh1).le
  have hcube : (θ / 2) ^ 3 ≤ θ / 2 := by
    have hs : (θ / 2) ^ 2 ≤ 1 := by nlinarith only [hh0, hh1]
    nlinarith only [mul_le_mul_of_nonneg_right hs hh0.le]
  have hlo : 3 * (θ / 2) / 4 ≤ Real.sin (θ / 2) := by
    linarith only [hsin, hcube]
  have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ 3 * (θ / 2) / 4) hlo 2
  have hhalf := Real.sin_sq_eq_half_sub (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at hhalf
  nlinarith only [hsquare, hhalf, sq_nonneg θ]

variable {n d : ℕ}

theorem angularDist_sq_le_four_mul_deficit (x : Configuration n d) (i j : Fin n)
    (hangle : angularDist (x i) (x j) ≤ 1) :
    angularDist (x i) (x j) ^ 2 ≤ 4 * PairDeficit.deficit x i j := by
  simpa only [PairDeficit.deficit, AngularGeometry.cos_angularDist] using
    sq_le_four_mul_one_sub_cos (AngularGeometry.angularDist_nonneg (x i) (x j)) hangle

theorem deficit_le_half_sq_of_angularDist_le (x : Configuration n d) (i j : Fin n)
    (ε : ℝ) (hangle : angularDist (x i) (x j) ≤ ε) :
    PairDeficit.deficit x i j ≤ ε ^ 2 / 2 := by
  have hθ0 := AngularGeometry.angularDist_nonneg (x i) (x j)
  have hcos : 1 - angularDist (x i) (x j) ^ 2 / 2 ≤
      Real.cos (angularDist (x i) (x j)) := Real.one_sub_sq_div_two_le_cos
  rw [AngularGeometry.cos_angularDist] at hcos
  have hsq := pow_le_pow_left₀ hθ0 hangle 2
  unfold PairDeficit.deficit
  linarith only [hcos, hsq]

theorem angularDist_le_iff_deficit_le (x : Configuration n d) (i j : Fin n)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hεπ : ε ≤ Real.pi) :
    angularDist (x i) (x j) ≤ ε ↔ PairDeficit.deficit x i j ≤ 1 - Real.cos ε := by
  rw [AngularGeometry.angularDist_le_iff_inner (x i) (x j) hε0 hεπ, PairDeficit.deficit]
  exact ⟨fun h => sub_le_sub_left h 1, fun h => (sub_le_sub_iff_left 1).mp h⟩

end Metastability.ContractionScale
