import Metastability.ActiveScales
import Metastability.ActiveLogCoordinate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Literal angular thresholds and logarithmic errors for active timing. -/

noncomputable section
open Set Filter
open scoped Topology

namespace Metastability.ActiveTimingScales

def angleLog (θ : ℝ) : ℝ := Real.log (Real.tan (θ / 2))

theorem angleLog_eq_logHalfAngle_cos {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi) :
    angleLog θ = ActiveLogCoordinate.logHalfAngle (Real.cos θ) := by
  have hcos1 := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ)) hθ.2.le hθ.1
  have hcosn := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.1.le (le_refl Real.pi) hθ.2
  rw [Real.cos_zero] at hcos1
  rw [Real.cos_pi] at hcosn
  rw [ActiveLogCoordinate.logHalfAngle_eq_log_tan_arccos ⟨hcosn, hcos1⟩,
    Real.arccos_cos hθ.1.le hθ.2.le]
  rfl

theorem continuousOn_angleLog : ContinuousOn angleLog (Ioo (0 : ℝ) Real.pi) := by
  apply ContinuousOn.congr
    (ActiveLogCoordinate.continuousOn_logHalfAngle.comp Real.continuous_cos.continuousOn ?_)
  · intro θ hθ
    exact angleLog_eq_logHalfAngle_cos hθ
  · intro θ hθ
    have hcos1 := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ)) hθ.2.le hθ.1
    have hcosn := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.1.le (le_refl Real.pi) hθ.2
    simpa only [Real.cos_zero, Real.cos_pi] using And.intro hcosn hcos1

theorem exists_compact_angleLog_bound {lo hi : ℝ} (hlo : 0 < lo) (hhi : hi < Real.pi) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ θ ∈ Icc lo hi, |angleLog θ| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_angleLog.mono (show Icc lo hi ⊆ Ioo (0 : ℝ) Real.pi from
      fun θ hθ => ⟨hlo.trans_le hθ.1, hθ.2.trans_lt hhi⟩))
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro θ hθ
  have hx : |angleLog θ| ≤ B := by simpa only [Real.norm_eq_abs] using hB θ hθ
  exact hx.trans (le_max_left _ _)

/-- On small positive angles the tangent half-angle lies between `θ/2` and
`θ`, retaining the additive constants in its logarithm. -/
theorem small_angleLog_bounds {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    Real.log θ - Real.log 2 ≤ angleLog θ ∧ angleLog θ ≤ Real.log θ := by
  have hh : 0 < θ / 2 := by positivity
  have hhp : θ / 2 < Real.pi / 2 := by linarith only [hθ1, Real.two_le_pi]
  have hlo : θ / 2 ≤ Real.tan (θ / 2) := Real.le_tan hh.le hhp
  have hcos : 1 / 2 ≤ Real.cos (θ / 2) := by
    have h := Real.one_sub_sq_div_two_le_cos (x := θ / 2)
    nlinarith only [h, hθ0, hθ1]
  have hhi : Real.tan (θ / 2) ≤ θ := by
    rw [Real.tan_eq_sin_div_cos]
    apply (div_le_iff₀ (by linarith only [hcos] : 0 < Real.cos (θ / 2))).mpr
    have hs := Real.sin_le hh.le
    have hm := mul_le_mul_of_nonneg_left hcos hθ0.le
    linarith only [hs, hm]
  have hl := Real.log_le_log hh hlo
  rw [Real.log_div hθ0.ne' (by norm_num)] at hl
  exact ⟨hl, Real.log_le_log (hh.trans_le hlo) hhi⟩

theorem log_mesoscopicScale {β : ℝ} (hβ : 1 < β) :
    Real.log (ActiveScales.mesoscopicScale β) =
      (Real.log (Real.log β) - Real.log β) / 2 := by
  unfold ActiveScales.mesoscopicScale
  rw [Real.log_sqrt (div_pos (Real.log_pos hβ) (zero_lt_one.trans hβ)).le,
    Real.log_div (Real.log_pos hβ).ne' (zero_lt_one.trans hβ).ne']

theorem mesoscopic_log_error {β : ℝ} (hβ : 1 < β)
    (hsmall : ActiveScales.mesoscopicScale β ≤ 1) (hloglog : 1 ≤ Real.log (Real.log β)) :
    |angleLog (ActiveScales.mesoscopicScale β) + Real.log β / 2| ≤
      2 * Real.log (Real.log β) := by
  have h := small_angleLog_bounds (ActiveScales.mesoscopicScale_pos hβ) hsmall
  rw [log_mesoscopicScale hβ] at h
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlog2pos := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  apply abs_le.mpr
  constructor <;> linarith only [h.1, h.2, hlog2, hlog2pos, hloglog]

theorem tendsto_loglog_div_log :
    Tendsto (fun β : ℝ => Real.log (Real.log β) / Real.log β) atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop

theorem tendsto_log_mul_neg_third_power :
    Tendsto (fun β : ℝ => Real.log β * β ^ (-(1 : ℝ) / 3)) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
  rw [show -(1 : ℝ) / 3 = -(1 / 3 : ℝ) by ring, Real.rpow_neg hβ.le, div_eq_mul_inv]

theorem eventually_timing_smallness (c B D : ℝ) (hc : 0 < c) :
    ∀ᶠ β : ℝ in atTop,
      1 < β ∧ 1 ≤ Real.log (Real.log β) ∧ ActiveScales.mesoscopicScale β ≤ 1 ∧
      D * β ^ (-(1 : ℝ) / 3) ≤ c / 2 ∧
      (B + 2) * Real.log (Real.log β) ≤ Real.log β / 4 ∧
      β ^ (-(1 : ℝ) / 3) ≤ Real.log (Real.log β) / Real.log β := by
  have hrpow : Tendsto (fun β : ℝ => D * β ^ (-(1 : ℝ) / 3)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul D using 1 <;>
      norm_num
  have hratio : Tendsto (fun β : ℝ => (B + 2) * (Real.log (Real.log β) / Real.log β))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_loglog_div_log.const_mul (B + 2)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually (eventually_ge_atTop (1 : ℝ)),
    ActiveScales.tendsto_mesoscopicScale.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hrpow.eventually (gt_mem_nhds (half_pos hc)),
    hratio.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    tendsto_log_mul_neg_third_power.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with β hβ hloglog hmeso hp he hsmall
  change 1 ≤ Real.log (Real.log β) at hloglog
  have hlog : 0 < Real.log β := Real.log_pos hβ
  refine ⟨hβ, hloglog, hmeso.le, hp.le, ?_, ?_⟩
  · rw [← mul_div_assoc] at he
    have hh := (div_lt_iff₀ hlog).mp he
    linarith only [hh]
  · apply (le_div_iff₀ hlog).mpr
    nlinarith only [hsmall, hloglog]

/-- The terminal logarithmic distance uses the exact half-cutoff `visible/8`.
Its ratio to the mesoscopic threshold is `8 log β`. -/
theorem terminal_log_gap {β : ℝ} (hβ : 1 < β) (hlog : 1 ≤ Real.log β)
    (hsmall : ActiveScales.mesoscopicScale β ≤ 1) (hloglog : 1 ≤ Real.log (Real.log β)) :
    angleLog (ActiveScales.mesoscopicScale β) - angleLog (Source.clockCutoff β / 2) ≤
      5 * Real.log (Real.log β) := by
  have hv : 0 < Source.visibleScale β := ContractionScale.visibleScale_pos hβ
  have hcut : 0 < Source.clockCutoff β / 2 := by
    exact div_pos (ActiveScales.clockCutoff_pos hβ) (by norm_num)
  have hcutle : Source.clockCutoff β / 2 ≤ ActiveScales.mesoscopicScale β := by
    rw [ActiveScales.mesoscopicScale_eq_log_mul_visible hβ]
    dsimp [Source.clockCutoff]
    have h := mul_le_mul_of_nonneg_right hlog hv.le
    linarith only [h, hv]
  have hhi := (small_angleLog_bounds (ActiveScales.mesoscopicScale_pos hβ) hsmall).2
  have hlo := (small_angleLog_bounds hcut (hcutle.trans hsmall)).1
  have hratio : ActiveScales.mesoscopicScale β / (Source.clockCutoff β / 2) =
      8 * Real.log β := by
    rw [ActiveScales.mesoscopicScale_eq_log_mul_visible hβ]
    dsimp [Source.clockCutoff]
    field_simp
    norm_num
  have hlogs : Real.log (ActiveScales.mesoscopicScale β) -
      Real.log (Source.clockCutoff β / 2) + Real.log 2 =
      Real.log (Real.log β) + Real.log 16 := by
    rw [← Real.log_div (ActiveScales.mesoscopicScale_pos hβ).ne' hcut.ne', hratio,
      Real.log_mul (by norm_num) (Real.log_pos hβ).ne']
    have h16 : Real.log (16 : ℝ) = Real.log 8 + Real.log 2 := by
      rw [show (16 : ℝ) = 8 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    rw [h16]
    ring
  have h16 : Real.log (16 : ℝ) ≤ 4 := by
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have hp := Real.log_pow (2 : ℝ) 4
    norm_num only [show (2 : ℝ) ^ 4 = 16 by norm_num, Nat.cast_ofNat] at hp
    linarith only [hp, h2]
  linarith only [hhi, hlo, hlogs, h16, hloglog]

theorem eventually_terminal_log_gap :
    ∀ᶠ β : ℝ in atTop, 1 < β ∧
      angleLog (ActiveScales.mesoscopicScale β) - angleLog (Source.clockCutoff β / 2) ≤
        5 * Real.log (Real.log β) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually (eventually_ge_atTop (1 : ℝ)),
    ActiveScales.tendsto_mesoscopicScale.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with β hβ hlog hloglog hsmall
  exact ⟨hβ, terminal_log_gap hβ hlog hsmall.le hloglog⟩

end Metastability.ActiveTimingScales
