import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic

/-!
# Analytic profile for the two-particle USA pilot

These are real-parameter analytic helpers. They do not assert that the profile
is the particle trajectory after the clock cutoff.
-/

namespace Metastability.PilotAsymptotics

open Filter
open scoped Topology

/-- The explicit half-angle variable before a clock cutoff. -/
noncomputable def halfAngle (a β t : ℝ) : ℝ := a * β ^ (-t)

/-- The cosine corresponding to the explicit half-angle variable. -/
noncomputable def cosineProfile (a β t : ℝ) : ℝ :=
  (1 - (halfAngle a β t) ^ 2) / (1 + (halfAngle a β t) ^ 2)

/-- The positive Arrhenius exponent in the analytic profile. -/
noncomputable def arrheniusExponent (a β t : ℝ) : ℝ :=
  2 * β * (halfAngle a β t) ^ 2 / (1 + (halfAngle a β t) ^ 2)

/-- The uncut auxiliary energy profile, not the actual post-cutoff dynamics. -/
noncomputable def analyticEnergy (a β t : ℝ) : ℝ :=
  (1 + Real.exp (-arrheniusExponent a β t)) / 2

theorem halfAngle_eq_exp (a β t : ℝ) (hβ : 0 < β) :
    halfAngle a β t = a * Real.exp (-t * Real.log β) := by
  rw [halfAngle, Real.rpow_def_of_pos hβ]
  congr 2
  ring

theorem analyticEnergy_eq_cosine (a β t : ℝ) :
    analyticEnergy a β t = (1 + Real.exp (β * (cosineProfile a β t - 1))) / 2 := by
  have hd : (1 + (halfAngle a β t) ^ 2) ≠ 0 := by positivity
  have hx : -arrheniusExponent a β t = β * (cosineProfile a β t - 1) := by
    unfold arrheniusExponent cosineProfile
    field_simp
    ring
  rw [analyticEnergy, hx]

theorem halfAngle_sq (a β t : ℝ) (hβ : 0 ≤ β) :
    (halfAngle a β t) ^ 2 = a ^ 2 * β ^ (-2 * t) := by
  rw [halfAngle, mul_pow, ← Real.rpow_mul_natCast hβ (-t) 2]
  congr 2
  norm_num
  ring

theorem arrheniusExponent_eq (a β t : ℝ) (hβ : 0 < β) :
    arrheniusExponent a β t =
      2 * a ^ 2 * β ^ (1 - 2 * t) / (1 + a ^ 2 * β ^ (-2 * t)) := by
  rw [arrheniusExponent, halfAngle_sq a β t hβ.le]
  have hpow : β ^ (1 - 2 * t) = β * β ^ (-2 * t) := by
    rw [sub_eq_add_neg, Real.rpow_add hβ, Real.rpow_one]
    congr 2
    ring
  rw [hpow]
  ring

theorem arrheniusExponent_nonneg (a β t : ℝ) (hβ : 0 ≤ β) :
    0 ≤ arrheniusExponent a β t := by
  unfold arrheniusExponent
  positivity

theorem analyticEnergy_bounds (a β t : ℝ) (hβ : 0 ≤ β) :
    1 / 2 ≤ analyticEnergy a β t ∧ analyticEnergy a β t ≤ 1 := by
  have he : 0 < Real.exp (-arrheniusExponent a β t) := Real.exp_pos _
  have he' : Real.exp (-arrheniusExponent a β t) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (arrheniusExponent_nonneg a β t hβ))
  unfold analyticEnergy
  constructor <;> linarith

theorem tendsto_halfAngle_sq (a : ℝ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun β : ℝ => (halfAngle a β t) ^ 2) atTop (𝓝 0) := by
  have h' : Tendsto (fun β : ℝ => a ^ 2 * β ^ (-(2 * t))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (by linarith : 0 < 2 * t)).const_mul (a ^ 2)
  apply h'.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with β hβ
  rw [halfAngle_sq a β t hβ]
  congr 2
  ring

theorem tendsto_cosineProfile (a : ℝ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun β : ℝ => cosineProfile a β t) atTop (𝓝 1) := by
  have hn : Tendsto (fun β : ℝ => 1 - (halfAngle a β t) ^ 2) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub (tendsto_halfAngle_sq a ht)
  have hd : Tendsto (fun β : ℝ => 1 + (halfAngle a β t) ^ 2) atTop (𝓝 1) := by
    simpa only [add_zero] using (tendsto_halfAngle_sq a ht).const_add (1 : ℝ)
  simpa only [one_div_one] using hn.div hd (by norm_num : (1 : ℝ) ≠ 0)

theorem tendsto_arrheniusExponent_atTop (a : ℝ) (ha : 0 < a)
    {t : ℝ} (ht : 0 < t) (ht' : t < 1 / 2) :
    Tendsto (fun β : ℝ => arrheniusExponent a β t) atTop atTop := by
  have hn : Tendsto (fun β : ℝ => 2 * a ^ 2 * β ^ (1 - 2 * t)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < 1 - 2 * t)).const_mul_atTop (by positivity)
  have hd : Tendsto (fun β : ℝ => (1 + (halfAngle a β t) ^ 2)⁻¹) atTop (𝓝 1) := by
    have hs : Tendsto (fun β : ℝ => 1 + (halfAngle a β t) ^ 2) atTop (𝓝 1) := by
      simpa only [add_zero] using (tendsto_halfAngle_sq a ht).const_add (1 : ℝ)
    simpa only [inv_one] using hs.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  apply (hn.atTop_mul_pos (by norm_num : (0 : ℝ) < 1) hd).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
  rw [arrheniusExponent_eq a β t hβ, halfAngle_sq a β t hβ.le, div_eq_mul_inv]

theorem tendsto_arrheniusExponent_zero (a : ℝ) {t : ℝ} (ht : 1 / 2 < t) :
    Tendsto (fun β : ℝ => arrheniusExponent a β t) atTop (𝓝 0) := by
  have hp : Tendsto (fun β : ℝ => β ^ (1 - 2 * t)) atTop (𝓝 0) := by
    rw [show 1 - 2 * t = -(2 * t - 1) by ring]
    exact tendsto_rpow_neg_atTop (by linarith : 0 < 2 * t - 1)
  have hn : Tendsto (fun β : ℝ => 2 * a ^ 2 * β ^ (1 - 2 * t)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hp
  have hd : Tendsto (fun β : ℝ => 1 + (halfAngle a β t) ^ 2) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add (tendsto_halfAngle_sq a (by linarith : 0 < t))
  have hlim : Tendsto (fun β : ℝ =>
      (2 * a ^ 2 * β ^ (1 - 2 * t)) / (1 + (halfAngle a β t) ^ 2)) atTop (𝓝 0) := by
    simpa only [zero_div] using hn.div hd (by norm_num : (1 : ℝ) ≠ 0)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
  rw [arrheniusExponent_eq a β t hβ, halfAngle_sq a β t hβ.le]

theorem tendsto_analyticEnergy_before_of_pos (a : ℝ) (ha : 0 < a)
    {t : ℝ} (ht : 0 < t) (ht' : t < 1 / 2) :
    Tendsto (fun β : ℝ => analyticEnergy a β t) atTop (𝓝 (1 / 2)) := by
  have he := Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp (tendsto_arrheniusExponent_atTop a ha ht ht'))
  simpa only [analyticEnergy, add_zero] using
    (tendsto_const_nhds.add he).div_const (2 : ℝ)

theorem tendsto_analyticEnergy_after (a : ℝ) {t : ℝ} (ht : 1 / 2 < t) :
    Tendsto (fun β : ℝ => analyticEnergy a β t) atTop (𝓝 1) := by
  have he : Tendsto (fun β : ℝ => Real.exp (-arrheniusExponent a β t)) atTop (𝓝 1) := by
    simpa only [neg_zero, Real.exp_zero] using
      Real.continuous_exp.continuousAt.tendsto.comp (tendsto_arrheniusExponent_zero a ht).neg
  have hlim := (he.const_add (1 : ℝ)).div_const (2 : ℝ)
  norm_num only [show (1 + 1) / 2 = (1 : ℝ) by norm_num] at hlim
  exact hlim

theorem tendsto_analyticEnergy_at_zero (a : ℝ) (ha : 0 < a) :
    Tendsto (fun β : ℝ => analyticEnergy a β 0) atTop (𝓝 (1 / 2)) := by
  have hc : 0 < 2 * a ^ 2 / (1 + a ^ 2) := by positivity
  have hx : Tendsto (fun β : ℝ => arrheniusExponent a β 0) atTop atTop := by
    have h := (tendsto_id : Tendsto (fun β : ℝ => β) atTop atTop).const_mul_atTop hc
    convert h using 1
    ext β
    simp only [arrheniusExponent, halfAngle, neg_zero, Real.rpow_zero, mul_one, id_eq]
    ring
  have he := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hx)
  simpa only [analyticEnergy, add_zero] using
    (tendsto_const_nhds.add he).div_const (2 : ℝ)

theorem tendsto_analyticEnergy_before (a : ℝ) (ha : 0 < a)
    {t : ℝ} (ht : 0 ≤ t) (ht' : t < 1 / 2) :
    Tendsto (fun β : ℝ => analyticEnergy a β t) atTop (𝓝 (1 / 2)) := by
  rcases eq_or_lt_of_le ht with h | h
  · subst t
    exact tendsto_analyticEnergy_at_zero a ha
  · exact tendsto_analyticEnergy_before_of_pos a ha h ht'

theorem analyticEnergy_mono_time (a β : ℝ) (hβ : 1 ≤ β) :
    Monotone (analyticEnergy a β) := by
  intro s t hst
  have hβ' : 0 ≤ β := le_trans zero_le_one hβ
  have hq : (halfAngle a β t) ^ 2 ≤ (halfAngle a β s) ^ 2 := by
    rw [halfAngle_sq a β t hβ', halfAngle_sq a β s hβ']
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hβ (by linarith)) (sq_nonneg a)
  have hd₁ : 0 < 1 + (halfAngle a β t) ^ 2 := by positivity
  have hd₂ : 0 < 1 + (halfAngle a β s) ^ 2 := by positivity
  have hx : arrheniusExponent a β t ≤ arrheniusExponent a β s := by
    unfold arrheniusExponent
    apply (div_le_div_iff₀ hd₁ hd₂).mpr
    have hmul := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 2 * β)
    nlinarith only [hmul]
  have he := Real.exp_le_exp.mpr (neg_le_neg hx)
  unfold analyticEnergy
  linarith only [he]

/-- Uniform convergence on every closed nonnegative interval strictly before the jump. -/
theorem analyticEnergy_uniform_before (a : ℝ) (ha : 0 < a)
    {l u : ℝ} (hl : 0 ≤ l) (hlu : l ≤ u) (hu : u < 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ β : ℝ in atTop, ∀ t ∈ Set.Icc l u, |analyticEnergy a β t - 1 / 2| < ε := by
  have hlim := tendsto_analyticEnergy_before a ha (le_trans hl hlu) hu
  have he := (Metric.tendsto_nhds.mp hlim) ε hε
  filter_upwards [he, eventually_ge_atTop (1 : ℝ)] with β hE hβ
  intro t ht
  rw [Real.dist_eq] at hE
  have hlo := (analyticEnergy_bounds a β t (le_trans zero_le_one hβ)).1
  have hhi := analyticEnergy_mono_time a β hβ ht.2
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  exact lt_of_le_of_lt (sub_le_sub_right hhi _) (lt_of_le_of_lt (le_abs_self _) hE)

/-- Uniform convergence on every closed interval strictly after the jump,
for the uncut auxiliary profile. -/
theorem analyticEnergy_uniform_after (a : ℝ)
    {l u : ℝ} (hl : 1 / 2 < l) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ β : ℝ in atTop, ∀ t ∈ Set.Icc l u, |analyticEnergy a β t - 1| < ε := by
  have he := (Metric.tendsto_nhds.mp (tendsto_analyticEnergy_after a hl)) ε hε
  filter_upwards [he, eventually_ge_atTop (1 : ℝ)] with β hE hβ
  intro t ht
  rw [Real.dist_eq] at hE
  have hup := (analyticEnergy_bounds a β t (le_trans zero_le_one hβ)).2
  have hlo := analyticEnergy_mono_time a β hβ ht.1
  rw [abs_of_nonpos (sub_nonpos.mpr hup)]
  have hbound : -(analyticEnergy a β t - 1) ≤ |analyticEnergy a β l - 1| := by
    calc
      -(analyticEnergy a β t - 1) ≤ -(analyticEnergy a β l - 1) := by linarith only [hlo]
      _ ≤ |analyticEnergy a β l - 1| := neg_le_abs _
  exact lt_of_le_of_lt hbound hE

/-- Uniform-on-compact left-plateau limit of the analytic profile. -/
theorem tendstoUniformlyOn_analyticEnergy_before (a : ℝ) (ha : 0 < a)
    {K : Set ℝ} (hK : IsCompact K) (hKsub : K ⊆ Set.Ico 0 (1 / 2)) :
    TendstoUniformlyOn (fun β t : ℝ => analyticEnergy a β t)
      (fun _ => 1 / 2) atTop K := by
  rcases Set.eq_empty_or_nonempty K with h | hne
  · subst K
    exact tendstoUniformlyOn_empty
  have hsup := hKsub (hK.sSup_mem hne)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [analyticEnergy_uniform_before a ha (l := 0) (u := sSup K)
    le_rfl hsup.1 hsup.2 hε] with β hβ
  intro t ht
  have htI : t ∈ Set.Icc 0 (sSup K) := ⟨(hKsub ht).1, le_csSup hK.bddAbove ht⟩
  simpa only [Real.dist_eq, abs_sub_comm] using hβ t htI

/-- Uniform-on-compact right-plateau limit of the uncut analytic profile. -/
theorem tendstoUniformlyOn_analyticEnergy_after (a : ℝ)
    {K : Set ℝ} (hK : IsCompact K) (hKsub : K ⊆ Set.Ioi (1 / 2)) :
    TendstoUniformlyOn (fun β t : ℝ => analyticEnergy a β t)
      (fun _ => 1) atTop K := by
  rcases Set.eq_empty_or_nonempty K with h | hne
  · subst K
    exact tendstoUniformlyOn_empty
  have hinf := hKsub (hK.sInf_mem hne)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [analyticEnergy_uniform_after a (l := sInf K) (u := sSup K) hinf hε] with β hβ
  intro t ht
  have htI : t ∈ Set.Icc (sInf K) (sSup K) :=
    ⟨csInf_le hK.bddBelow ht, le_csSup hK.bddAbove ht⟩
  simpa only [Real.dist_eq, abs_sub_comm] using hβ t htI

end Metastability.PilotAsymptotics
