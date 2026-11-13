import Metastability.ContractionScale

/-!
# Quantitative scale comparisons for initial preparation

These estimates supply the strict cap-drift margin on an original-time
interval of length proportional to beta. The visible radius and the
quarter-power cap enlargement are the literal scales from the manuscript.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace Metastability.PreparationScale
open Source ContractionScale

/-- Doubling a small cap radius leaves a quadratic cosine margin. -/
theorem cosine_margin {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ε ^ 2 / 2 ≤ Real.cos ε - Real.cos (2 * ε) := by
  have hq := sq_le_four_mul_one_sub_cos hε0 hε1
  have hc : 1 / 2 ≤ Real.cos ε := by
    have h := Real.one_sub_sq_div_two_le_cos (x := ε)
    nlinarith only [h, hε0, hε1]
  have hcos := Real.cos_le_one ε
  rw [Real.cos_two_mul]
  nlinarith only [hq, hc, hcos, mul_nonneg (sub_nonneg.mpr hcos) (sub_nonneg.mpr hc)]

/-- Exponential suppression defeats the cap's quadratic visible-scale margin. -/
theorem eventually_cap_error_small (K L : ℝ) (hK : 0 ≤ K) (hL : 0 < L) :
    ∀ᶠ β : ℝ in atTop,
      K * β * Real.exp (-β * L) < visibleScale β ^ 2 / 2 := by
  have ht : Tendsto (fun β : ℝ => K * (β ^ 3 * Real.exp (-β * L)))
      atTop (𝓝 0) := by
    have h : Tendsto (fun β : ℝ => K * (β ^ 3 * Real.exp (-L * β)))
        atTop (𝓝 0) := by
      simpa only [Real.rpow_ofNat, mul_zero] using
        (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 3 L hL).const_mul K
    convert h using 1
    ext β
    rw [show -β * L = -L * β by ring]
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with β hβ hsmall
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  have hlog : 0 < Real.log β := Real.log_pos hβ
  have hp : 0 < β * Real.log β := mul_pos hβ0 hlog
  have heq : visibleScale β ^ 2 * (β * Real.log β) = 1 := by
    unfold visibleScale
    rw [div_pow, one_pow, Real.sq_sqrt hp.le]
    exact one_div_mul_cancel hp.ne'
  have hlogle : Real.log β ≤ β := (Real.log_le_sub_one_of_pos hβ0).trans (by linarith)
  have hprod : (K * β * Real.exp (-β * L)) * (β * Real.log β) < 1 / 2 := by
    calc
      _ = (K * β ^ 2 * Real.exp (-β * L)) * Real.log β := by ring
      _ ≤ (K * β ^ 2 * Real.exp (-β * L)) * β :=
        mul_le_mul_of_nonneg_left hlogle (by positivity)
      _ = K * (β ^ 3 * Real.exp (-β * L)) := by ring
      _ < 1 / 2 := hsmall
  apply (mul_lt_mul_iff_left₀ hp).mp
  nlinarith only [hprod, heq]

/-- The initial doubled visible cap fits in the source quarter-power enlargement. -/
theorem eventually_doubled_visible_le_quarter_power :
    ∀ᶠ β : ℝ in atTop, 2 * visibleScale β ≤ β ^ (-(1 : ℝ) / 4) := by
  have hquarter : Tendsto (fun β : ℝ => 2 * β ^ (-(1 : ℝ) / 4)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).const_mul 2 using 1 <;>
      norm_num
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    hquarter.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with β hβ hlog hq
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  have hsqrt : Real.sqrt β ≤ Real.sqrt (β * Real.log β) := by
    apply Real.sqrt_le_sqrt
    nlinarith only [hβ0, hlog]
  have hv : visibleScale β ≤ β ^ (-(1 : ℝ) / 2) := by
    calc
      _ ≤ 1 / Real.sqrt β := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hβ0) hsqrt
      _ = β ^ (-(1 : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hβ0.le]
        congr 1
        norm_num
  have heq : β ^ (-(1 : ℝ) / 2) = β ^ (-(1 : ℝ) / 4) * β ^ (-(1 : ℝ) / 4) := by
    rw [← Real.rpow_add hβ0]
    congr 1
    norm_num
  have hp : 0 ≤ β ^ (-(1 : ℝ) / 4) := Real.rpow_nonneg hβ0.le _
  calc
    2 * visibleScale β ≤ 2 * β ^ (-(1 : ℝ) / 2) := by linarith only [hv]
    _ = (2 * β ^ (-(1 : ℝ) / 4)) * β ^ (-(1 : ℝ) / 4) := by rw [heq]; ring
    _ ≤ 1 * β ^ (-(1 : ℝ) / 4) := mul_le_mul_of_nonneg_right hq.le hp
    _ = _ := one_mul _

/-- All scalar conditions for the simultaneous initial cap argument, with
threshold depending only on particle count, separation and time multiplier. -/
theorem eventually_preparation_parameters (n : ℕ) (g C : ℝ)
    (hg : 0 < g) (hC : 0 < C) :
    ∀ᶠ β : ℝ in atTop,
      1 < β ∧ 0 < visibleScale β ∧ visibleScale β ≤ 1 ∧
      2 * visibleScale β < Real.pi / 2 ∧ 8 * visibleScale β ≤ g ∧
      2 * visibleScale β ≤ β ^ (-(1 : ℝ) / 4) ∧
      2 * (n : ℝ) * (C * β) * Real.exp (-β * (g / 2)) <
        Real.cos (visibleScale β) - Real.cos (2 * visibleScale β) := by
  have he := tendsto_visibleScale.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hg' := tendsto_visibleScale.eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < g / 8))
  have herr := eventually_cap_error_small (2 * n * C) (g / 2) (by positivity) (by positivity)
  filter_upwards [eventually_gt_atTop (1 : ℝ), he, hg',
    eventually_doubled_visible_le_quarter_power, herr] with β hβ he hg' hquarter herr
  have he1 : visibleScale β ≤ 1 := by linarith only [he]
  have he0 := visibleScale_pos hβ
  refine ⟨hβ, he0, he1, ?_, ?_, hquarter, ?_⟩
  · linarith only [he, Real.one_le_pi_div_two]
  · linarith only [hg']
  · convert herr.trans_le (cosine_margin he0.le he1) using 1
    ring

end Metastability.PreparationScale
