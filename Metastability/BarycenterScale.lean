import Metastability.ActiveTimingScales

/-! Vanishing scales for the perturbed active barycenter differential.
Only the additive exponential remainder incurs the inverse-sine factor. -/
noncomputable section
open Filter Set
open scoped Topology
namespace Metastability.BarycenterScale

theorem inverse_sqrt_le (A β : ℝ) (hA : 0 < A) (hβ : 1 ≤ β) (hlog : 1 ≤ Real.log β) :
    (Real.sqrt (A * (Real.log β / β)))⁻¹ ≤ β / Real.sqrt A := by
  have hβ0 : 0 < β := zero_lt_one.trans_le hβ
  have hlog0 : 0 < Real.log β := zero_lt_one.trans_le hlog
  have hp : 0 < A * (Real.log β / β) := mul_pos hA (div_pos hlog0 hβ0)
  have hs : 0 < Real.sqrt (A * (Real.log β / β)) := Real.sqrt_pos.mpr hp
  have hAs := Real.sqrt_pos.mpr hA
  have hprod : 1 ≤ β * Real.log β := by
    nlinarith only [hβ, hlog, mul_nonneg (sub_nonneg.mpr hβ) (sub_nonneg.mpr hlog)]
  have hm : A ≤ A * (β * Real.log β) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hprod hA.le
  have heq : (β * Real.sqrt (A * (Real.log β / β))) ^ 2 = A * (β * Real.log β) := by
    rw [mul_pow, Real.sq_sqrt hp.le]
    field_simp
  have hroot : Real.sqrt A ≤ β * Real.sqrt (A * (Real.log β / β)) := by
    have hAsq := Real.sq_sqrt hA.le
    have hpos := mul_pos hβ0 hs
    nlinarith only [hm, heq, hAsq, hpos, hAs]
  rw [← one_div]
  exact (div_le_div_iff₀ hs hAs).mpr (by simpa only [one_mul] using hroot)

theorem remainder_tendsto (n : ℕ) (A α γ : ℝ) (hA : 0 < A)
    (hα : 0 < α) (hγ : 0 < γ) :
    Tendsto (fun β : ℝ =>
      (4 * Real.log β * (Real.exp (-α * β) + n * Real.exp (-γ * β))) /
        Real.sqrt (A * (Real.log β / β))) atTop (𝓝 0) := by
  have heα : Tendsto (fun β : ℝ => β ^ 2 * Real.exp (-α * β)) atTop (𝓝 0) := by
    simpa only [Real.rpow_two] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 α hα
  have heγ : Tendsto (fun β : ℝ => β ^ 2 * Real.exp (-γ * β)) atTop (𝓝 0) := by
    simpa only [Real.rpow_two] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 γ hγ
  have hbound : Tendsto (fun β : ℝ => (4 / Real.sqrt A) *
      (β ^ 2 * Real.exp (-α * β) + n * (β ^ 2 * Real.exp (-γ * β)))) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (heα.add (heγ.const_mul (n : ℝ))).const_mul (4 / Real.sqrt A)
  apply squeeze_zero' _ _ hbound
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with β hβ
    have hlog := (Real.log_pos hβ).le
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with β hβ hlog
    have hβ0 : 0 < β := zero_lt_one.trans_le hβ
    have hlog0 : 0 ≤ Real.log β := zero_le_one.trans hlog
    have hinv := inverse_sqrt_le A β hA hβ hlog
    have hlogle : Real.log β ≤ β := (Real.log_le_sub_one_of_pos hβ0).trans (by linarith)
    have hE : 0 ≤ 4 * Real.log β * (Real.exp (-α * β) + n * Real.exp (-γ * β)) := by positivity
    calc
      _ ≤ (4 * Real.log β * (Real.exp (-α * β) + n * Real.exp (-γ * β))) * (β / Real.sqrt A) := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hinv hE
      _ = (4 / Real.sqrt A) * (β * Real.log β) *
          (Real.exp (-α * β) + n * Real.exp (-γ * β)) := by ring
      _ ≤ (4 / Real.sqrt A) * (β * β) *
          (Real.exp (-α * β) + n * Real.exp (-γ * β)) := by
        gcongr
      _ = _ := by ring

theorem active_rate_tendsto (n : ℕ) (κ U L : ℝ)
    (hU : U < 2) (hκ : U < κ) (hL : U < L) :
    Tendsto (fun β : ℝ => 12 *
      (((5 * n + 10 * (n : ℝ) ^ 2) * β ^ (-(1 / 3 : ℝ)) * Real.log β) +
        (4 * Real.log β * (Real.exp (-(κ - U) * β) + n * Real.exp (-(L - U) * β))) /
          Real.sqrt (((2 / 5 : ℝ) * (2 - U)) * (Real.log β / β)))) atTop (𝓝 0) := by
  have hp : 0 < (2 / 5 : ℝ) * (2 - U) := mul_pos (by norm_num) (sub_pos.mpr hU)
  have hm : Tendsto (fun β : ℝ =>
      (5 * n + 10 * (n : ℝ) ^ 2) * β ^ (-(1 / 3 : ℝ)) * Real.log β) atTop (𝓝 0) := by
    convert ActiveTimingScales.tendsto_log_mul_neg_third_power.const_mul
      (5 * n + 10 * (n : ℝ) ^ 2) using 1
    · ext β
      rw [show -(1 : ℝ) / 3 = -(1 / 3 : ℝ) by ring]
      ring
    · simp only [mul_zero]
  simpa only [add_zero, mul_zero] using
    (hm.add (remainder_tendsto n _ (κ - U) (L - U) hp (sub_pos.mpr hκ) (sub_pos.mpr hL))).const_mul 12

end Metastability.BarycenterScale
