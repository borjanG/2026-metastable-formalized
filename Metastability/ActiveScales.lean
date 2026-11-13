import Metastability.ContractionScale
import Mathlib.Analysis.Complex.Exponential

/-! Real-temperature scale comparisons used to identify the active clock. -/

noncomputable section
open Filter Set
open scoped Topology

namespace Metastability.ActiveScales

open Source ContractionScale

/-- The manuscript's mesoscopic angular threshold. -/
def mesoscopicScale (β : ℝ) : ℝ := Real.sqrt (Real.log β / β)

theorem mesoscopicScale_pos {β : ℝ} (hβ : 1 < β) : 0 < mesoscopicScale β :=
  Real.sqrt_pos.mpr (div_pos (Real.log_pos hβ) (zero_lt_one.trans hβ))

theorem mesoscopicScale_sq {β : ℝ} (hβ : 1 < β) :
    mesoscopicScale β ^ 2 = Real.log β / β :=
  Real.sq_sqrt (div_nonneg (Real.log_pos hβ).le (zero_lt_one.trans hβ).le)

theorem mesoscopicScale_eq_log_mul_visible {β : ℝ} (hβ : 1 < β) :
    mesoscopicScale β = Real.log β * visibleScale β := by
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  have hlog : 0 < Real.log β := Real.log_pos hβ
  have hv : visibleScale β ^ 2 = 1 / (β * Real.log β) := by
    unfold visibleScale
    rw [div_pow, one_pow, Real.sq_sqrt (mul_pos hβ0 hlog).le]
  have heq : (Real.log β * visibleScale β) ^ 2 = Real.log β / β := by
    rw [mul_pow, hv]
    field_simp
  nlinarith only [heq, mesoscopicScale_sq hβ, mesoscopicScale_pos hβ,
    mul_pos hlog (visibleScale_pos hβ)]

theorem tendsto_mesoscopicScale : Tendsto mesoscopicScale atTop (𝓝 0) := by
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  simpa only [Real.sqrt_zero] using h

/-- Any fixed polynomial times an exponentially small error is eventually
smaller than any prescribed real power. -/
theorem eventually_mul_exp_le_rpow (K κ p q : ℝ) (hκ : 0 < κ) :
    ∀ᶠ β : ℝ in atTop, K * β ^ p * Real.exp (-κ * β) ≤ β ^ q := by
  have hlim : Tendsto (fun β : ℝ => K * (β ^ (p - q) * Real.exp (-κ * β)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p - q) κ hκ).const_mul K
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with β hβ hsmall
  have hp : β ^ p = β ^ (p - q) * β ^ q := by
    rw [← Real.rpow_add hβ]
    congr 1
    ring
  calc
    K * β ^ p * Real.exp (-κ * β) =
        (K * (β ^ (p - q) * Real.exp (-κ * β))) * β ^ q := by rw [hp]; ring
    _ ≤ 1 * β ^ q := mul_le_mul_of_nonneg_right hsmall.le (Real.rpow_pos_of_pos hβ q).le
    _ = β ^ q := one_mul _

theorem clockCutoff_pos {β : ℝ} (hβ : 1 < β) : 0 < clockCutoff β := by
  exact div_pos (visibleScale_pos hβ) (by norm_num)

theorem inv_four_beta_le_clockCutoff {β : ℝ} (hβ : 1 < β) :
    1 / (4 * β) ≤ clockCutoff β := by
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  have hlog : Real.log β ≤ β := (Real.log_le_sub_one_of_pos hβ0).trans (by linarith)
  have hsqrt : Real.sqrt (β * Real.log β) ≤ β := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hβ0.le, by nlinarith only [mul_le_mul_of_nonneg_left hlog hβ0.le]⟩
  have hspos : 0 < Real.sqrt (β * Real.log β) :=
    Real.sqrt_pos.mpr (mul_pos hβ0 (Real.log_pos hβ))
  have hi := one_div_le_one_div_of_le hspos hsqrt
  change 1 / (4 * β) ≤ (1 / Real.sqrt (β * Real.log β)) / 4
  calc
    1 / (4 * β) = (1 / β) / 4 := by ring
    _ ≤ (1 / Real.sqrt (β * Real.log β)) / 4 := div_le_div_of_nonneg_right hi (by norm_num)

/-- All scalar smallness conditions for the static active clock, uniform in
configuration, stage, dimension, and the selected representatives. -/
theorem eventually_clock_parameters (κ δ : ℝ) (hκ : 0 < κ) (hδ : 0 < δ) :
    ∀ᶠ β : ℝ in atTop,
      1 < β ∧ 1 ≤ Real.log β ∧ Real.exp (-κ * β) ≤ clockCutoff β ∧
      2 * Real.exp (-κ * β) < 5 * δ ∧
      2 * β * Real.exp (-κ * β) ≤ 1 ∧
      4 * β * Real.exp (-κ * β) ≤ β ^ (-(1 / 3 : ℝ)) ∧
      clockCutoff β < mesoscopicScale β - 2 * Real.exp (-κ * β) := by
  have he : Tendsto (fun β : ℝ => Real.exp (-κ * β)) atTop (𝓝 0) := by
    simpa only [Real.rpow_zero, one_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 κ hκ
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_mul_exp_le_rpow 4 κ 1 (-1) hκ,
    eventually_mul_exp_le_rpow 4 κ 1 (-(1 / 3 : ℝ)) hκ,
    he.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 5 * δ / 2))]
      with β hβ hlog hcut herr hgap
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  simp only [Real.rpow_one] at hcut herr
  have hinv : β ^ (-1 : ℝ) = 1 / β := by rw [Real.rpow_neg_one, one_div]
  rw [hinv] at hcut
  have hinvle : 1 / β ≤ 1 := (div_le_one hβ0).mpr hβ.le
  have hcut' : Real.exp (-κ * β) ≤ 1 / (4 * β) := by
    have hβge : 1 ≤ β := hβ.le
    have he0 := (Real.exp_pos (-κ * β)).le
    have hm : 4 * Real.exp (-κ * β) ≤ 4 * β * Real.exp (-κ * β) := by
      nlinarith only [mul_le_mul_of_nonneg_right hβge he0]
    have h := hm.trans hcut
    calc
      Real.exp (-κ * β) ≤ (1 / β) / 4 := by linarith only [h]
      _ = 1 / (4 * β) := by ring
  have hεcut := hcut'.trans (inv_four_beta_le_clockCutoff hβ)
  refine ⟨hβ, hlog, hεcut, by linarith only [hgap], ?_, herr, ?_⟩
  · linarith only [hcut, hinvle, Real.exp_pos (-κ * β), hβ0]
  · have hmeso : 4 * clockCutoff β ≤ mesoscopicScale β := by
      rw [mesoscopicScale_eq_log_mul_visible hβ]
      have h := mul_le_mul_of_nonneg_right hlog (visibleScale_pos hβ).le
      dsimp [clockCutoff]
      linarith only [h]
    linarith only [hmeso, hεcut, clockCutoff_pos hβ]

end Metastability.ActiveScales
