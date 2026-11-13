import Metastability.PilotAsymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# The exact angular cutoff of the two-particle analytic profile

These results concern an explicit profile and its algebraic crossing time.
Identifying this crossing with an actual particle hitting time is a separate
dynamical proof obligation.
-/

namespace Metastability.PilotCutoff

open Filter
open scoped Topology
open PilotAsymptotics

/-- The paper's angular clock cutoff, with real inverse temperature. -/
noncomputable def angularCutoff (β : ℝ) : ℝ :=
  (1 / 4) * Real.sqrt (1 / (β * Real.log β))

/-- The half-angle tangent at the exact angular cutoff. -/
noncomputable def cutoffTangent (β : ℝ) : ℝ := Real.tan (angularCutoff β / 2)

/-- The algebraic time when the uncut half-angle profile equals the cutoff tangent. -/
noncomputable def cutoffTime (a β : ℝ) : ℝ :=
  (Real.log a - Real.log (cutoffTangent β)) / Real.log β

theorem angularCutoff_pos {β : ℝ} (hβ : 1 < β) : 0 < angularCutoff β := by
  have hlog := Real.log_pos hβ
  have hβ' : 0 < β := lt_trans zero_lt_one hβ
  unfold angularCutoff
  positivity

theorem tendsto_angularCutoff : Tendsto angularCutoff atTop (𝓝 0) := by
  have hp : Tendsto (fun β : ℝ => β * Real.log β) atTop atTop :=
    tendsto_id.atTop_mul_atTop₀ Real.tendsto_log_atTop
  have hi : Tendsto (fun β : ℝ => 1 / (β * Real.log β)) atTop (𝓝 0) := by
    simpa only [one_div] using hp.inv_tendsto_atTop
  simpa only [angularCutoff, Real.sqrt_zero, mul_zero] using
    (Real.continuous_sqrt.continuousAt.tendsto.comp hi).const_mul (1 / 4 : ℝ)

theorem eventually_angularCutoff_small :
    ∀ᶠ β : ℝ in atTop, 0 < angularCutoff β ∧ angularCutoff β < Real.pi / 2 := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    tendsto_angularCutoff.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < Real.pi / 2))]
      with β hβ hh
  exact ⟨angularCutoff_pos hβ, hh⟩

theorem eventually_cutoffTangent_pos : ∀ᶠ β : ℝ in atTop, 0 < cutoffTangent β := by
  filter_upwards [eventually_angularCutoff_small] with β hβ
  exact Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith only [hβ.1])
    (by linarith only [hβ.1, hβ.2])

theorem tendsto_cutoffTangent : Tendsto cutoffTangent atTop (𝓝 0) := by
  have ht : ContinuousAt Real.tan (0 : ℝ) :=
    (Real.hasDerivAt_tan (by norm_num : Real.cos (0 : ℝ) ≠ 0)).continuousAt
  have hh : Tendsto (fun β : ℝ => angularCutoff β / 2) atTop (𝓝 0) := by
    simpa only [zero_div] using tendsto_angularCutoff.div_const (2 : ℝ)
  simpa only [cutoffTangent, Real.tan_zero] using ht.tendsto.comp hh

theorem tendsto_cutoffTangent_ratio :
    Tendsto (fun β : ℝ => cutoffTangent β / (angularCutoff β / 2)) atTop (𝓝 1) := by
  have hh : Tendsto (fun β : ℝ => angularCutoff β / 2) atTop (𝓝 0) := by
    simpa only [zero_div] using tendsto_angularCutoff.div_const (2 : ℝ)
  have hs : Tendsto (fun β : ℝ => Real.sinc (angularCutoff β / 2)) atTop (𝓝 1) := by
    simpa only [Real.sinc_zero] using Real.continuous_sinc.continuousAt.tendsto.comp hh
  have hc : Tendsto (fun β : ℝ => Real.cos (angularCutoff β / 2)) atTop (𝓝 1) := by
    simpa only [Real.cos_zero] using Real.continuous_cos.continuousAt.tendsto.comp hh
  have hlim : Tendsto (fun β : ℝ =>
      Real.sinc (angularCutoff β / 2) / Real.cos (angularCutoff β / 2)) atTop (𝓝 1) := by
    simpa only [one_div_one] using hs.div hc (by norm_num : (1 : ℝ) ≠ 0)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with β hβ
  have hhpos := angularCutoff_pos hβ
  rw [Real.sinc_of_ne_zero (by positivity : angularCutoff β / 2 ≠ 0), cutoffTangent, Real.tan_eq_sin_div_cos]
  ring

theorem log_halfCutoff {β : ℝ} (hβ : 1 < β) :
    Real.log (angularCutoff β / 2) =
      Real.log (1 / 4 : ℝ) - (Real.log β + Real.log (Real.log β)) / 2 - Real.log 2 := by
  have hp : 0 < β := lt_trans zero_lt_one hβ
  have hl : 0 < Real.log β := Real.log_pos hβ
  rw [Real.log_div (ne_of_gt (angularCutoff_pos hβ)) (by norm_num : (2 : ℝ) ≠ 0)]
  unfold angularCutoff
  rw [Real.log_mul (by norm_num : (1 / 4 : ℝ) ≠ 0) (by positivity),
    Real.log_sqrt (by positivity), Real.log_div one_ne_zero (mul_ne_zero hp.ne' hl.ne'),
    Real.log_one, Real.log_mul hp.ne' hl.ne']
  ring

theorem tendsto_loglog_div_log :
    Tendsto (fun β : ℝ => Real.log (Real.log β) / Real.log β) atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  exact h.comp Real.tendsto_log_atTop

theorem tendsto_log_halfCutoff_div_log :
    Tendsto (fun β : ℝ => Real.log (angularCutoff β / 2) / Real.log β)
      atTop (𝓝 (-(1 / 2))) := by
  have hc := Real.tendsto_log_atTop.const_div_atTop (Real.log (1 / 4 : ℝ) - Real.log 2)
  have hlim : Tendsto (fun β : ℝ =>
      (Real.log (1 / 4 : ℝ) - Real.log 2) / Real.log β - 1 / 2 -
        (Real.log (Real.log β) / Real.log β) / 2) atTop (𝓝 (-(1 / 2))) := by
    convert (hc.sub_const (1 / 2 : ℝ)).sub (tendsto_loglog_div_log.div_const (2 : ℝ)) using 1
    norm_num
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with β hβ
  rw [log_halfCutoff hβ]
  have hl : Real.log β ≠ 0 := (Real.log_pos hβ).ne'
  field_simp
  ring

theorem tendsto_log_cutoffTangent_div_log :
    Tendsto (fun β : ℝ => Real.log (cutoffTangent β) / Real.log β)
      atTop (𝓝 (-(1 / 2))) := by
  have hr : Tendsto (fun β : ℝ =>
      Real.log (cutoffTangent β / (angularCutoff β / 2))) atTop (𝓝 0) := by
    simpa only [Real.log_one] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp tendsto_cutoffTangent_ratio
  have hzero := hr.div_atTop Real.tendsto_log_atTop
  have hlim : Tendsto (fun β : ℝ =>
      Real.log (cutoffTangent β / (angularCutoff β / 2)) / Real.log β +
      Real.log (angularCutoff β / 2) / Real.log β) atTop (𝓝 (-(1 / 2))) := by
    simpa only [zero_add] using hzero.add tendsto_log_halfCutoff_div_log
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_cutoffTangent_pos] with β hβ hq
  have hhpos := angularCutoff_pos hβ
  rw [Real.log_div hq.ne' (by positivity : angularCutoff β / 2 ≠ 0)]
  ring

/-- The algebraic crossing time tends to the two-particle USA jump time. -/
theorem tendsto_cutoffTime (a : ℝ) :
    Tendsto (cutoffTime a) atTop (𝓝 (1 / 2)) := by
  have h := (Real.tendsto_log_atTop.const_div_atTop (Real.log a)).sub
    tendsto_log_cutoffTangent_div_log
  change Tendsto (fun β : ℝ => (Real.log a - Real.log (cutoffTangent β)) / Real.log β)
    atTop (𝓝 (1 / 2))
  simpa only [sub_div, zero_sub, neg_neg] using h

theorem halfAngle_cutoffTime {a β : ℝ} (ha : 0 < a) (hβ : 1 < β)
    (hq : 0 < cutoffTangent β) :
    halfAngle a β (cutoffTime a β) = cutoffTangent β := by
  rw [halfAngle_eq_exp a β _ (lt_trans zero_lt_one hβ)]
  have hl : Real.log β ≠ 0 := (Real.log_pos hβ).ne'
  have hx : -cutoffTime a β * Real.log β = Real.log (cutoffTangent β) - Real.log a := by
    unfold cutoffTime
    field_simp
    ring
  rw [hx, Real.exp_sub, Real.exp_log hq, Real.exp_log ha]
  field_simp

theorem eventually_cutoffTime_pos (a : ℝ) :
    ∀ᶠ β : ℝ in atTop, 0 < cutoffTime a β :=
  (tendsto_cutoffTime a).eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))

theorem angleProfile_cutoffTime {a β : ℝ} (ha : 0 < a) (hβ : 1 < β)
    (hh : angularCutoff β < Real.pi / 2) :
    2 * Real.arctan (halfAngle a β (cutoffTime a β)) = angularCutoff β := by
  have hpos := angularCutoff_pos hβ
  have hupper : angularCutoff β / 2 < Real.pi / 2 := by linarith only [hpos, hh]
  have hlower : -(Real.pi / 2) < angularCutoff β / 2 := by
    linarith only [hpos, Real.pi_pos]
  have hq : 0 < cutoffTangent β :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith only [hpos]) hupper
  rw [halfAngle_cutoffTime ha hβ hq, cutoffTangent, Real.arctan_tan hlower hupper]
  ring

theorem halfAngle_gt_cutoffTangent_iff {a β t : ℝ} (ha : 0 < a) (hβ : 1 < β)
    (hq : 0 < cutoffTangent β) :
    cutoffTangent β < halfAngle a β t ↔ t < cutoffTime a β := by
  rw [← halfAngle_cutoffTime ha hβ hq]
  unfold halfAngle
  rw [mul_lt_mul_iff_right₀ ha]
  constructor
  · intro h
    by_contra hn
    have ht : -t ≤ -cutoffTime a β := neg_le_neg (le_of_not_gt hn)
    exact (not_lt_of_ge (Real.rpow_le_rpow_of_exponent_le hβ.le ht)) h
  · intro h
    exact Real.rpow_lt_rpow_of_exponent_lt hβ (neg_lt_neg h)

theorem beta_mul_angularCutoff_sq {β : ℝ} (hβ : 1 < β) :
    β * angularCutoff β ^ 2 = 1 / (16 * Real.log β) := by
  have hp : 0 < β := lt_trans zero_lt_one hβ
  have hl : 0 < Real.log β := Real.log_pos hβ
  unfold angularCutoff
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  field_simp
  ring

theorem tendsto_beta_mul_angularCutoff_sq :
    Tendsto (fun β : ℝ => β * angularCutoff β ^ 2) atTop (𝓝 0) := by
  have hlim : Tendsto (fun β : ℝ => 1 / (16 * Real.log β)) atTop (𝓝 0) := by
    simpa only [one_div] using
      (Real.tendsto_log_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 16)).inv_tendsto_atTop
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with β hβ
  exact (beta_mul_angularCutoff_sq hβ).symm

theorem tendsto_beta_mul_cutoffTangent_sq :
    Tendsto (fun β : ℝ => β * cutoffTangent β ^ 2) atTop (𝓝 0) := by
  have hlim : Tendsto (fun β : ℝ =>
      (β * angularCutoff β ^ 2 / 4) *
      (cutoffTangent β / (angularCutoff β / 2)) ^ 2) atTop (𝓝 0) := by
    simpa only [zero_div, one_pow, zero_mul] using
      (tendsto_beta_mul_angularCutoff_sq.div_const (4 : ℝ)).mul (tendsto_cutoffTangent_ratio.pow 2)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with β hβ
  have hh : angularCutoff β ≠ 0 := (angularCutoff_pos hβ).ne'
  field_simp
  ring

theorem tendsto_arrheniusExponent_cutoffTime (a : ℝ) (ha : 0 < a) :
    Tendsto (fun β : ℝ => arrheniusExponent a β (cutoffTime a β)) atTop (𝓝 0) := by
  have hn : Tendsto (fun β : ℝ => 2 * (β * cutoffTangent β ^ 2)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_beta_mul_cutoffTangent_sq.const_mul (2 : ℝ)
  have hd : Tendsto (fun β : ℝ => 1 + cutoffTangent β ^ 2) atTop (𝓝 1) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using
      (tendsto_cutoffTangent.pow 2).const_add (1 : ℝ)
  have hlim : Tendsto (fun β : ℝ =>
      2 * (β * cutoffTangent β ^ 2) / (1 + cutoffTangent β ^ 2)) atTop (𝓝 0) := by
    simpa only [zero_div] using hn.div hd (by norm_num : (1 : ℝ) ≠ 0)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_cutoffTangent_pos] with β hβ hq
  rw [arrheniusExponent, halfAngle_cutoffTime ha hβ hq]
  ring

/-- The analytic energy is asymptotically one already at the exact cutoff. -/
theorem tendsto_analyticEnergy_cutoffTime (a : ℝ) (ha : 0 < a) :
    Tendsto (fun β : ℝ => analyticEnergy a β (cutoffTime a β)) atTop (𝓝 1) := by
  have hx : Tendsto (fun β : ℝ => -arrheniusExponent a β (cutoffTime a β)) atTop (𝓝 0) := by
    simpa only [neg_zero] using (tendsto_arrheniusExponent_cutoffTime a ha).neg
  have he := Real.tendsto_exp_nhds_zero_nhds_one.comp hx
  have hlim := (he.const_add (1 : ℝ)).div_const (2 : ℝ)
  norm_num only [show (1 + 1) / 2 = (1 : ℝ) by norm_num] at hlim
  exact hlim

end Metastability.PilotCutoff
