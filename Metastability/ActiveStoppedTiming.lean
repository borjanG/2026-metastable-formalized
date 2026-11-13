import Metastability.ActiveTiming
import Metastability.ActiveClampedTrajectory

/-!
# First mesoscopic hits for an actual accelerated source trajectory

This is the analytic bridge: its scalar-law premise is discharged by the
source-facing theorem in ActiveCollisionTiming. It proves a finite first hit
using absolute continuity supplied by the actual ODE and clock.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace
namespace Metastability.ActiveStoppedTiming
open Source ActiveScales ActiveLogCoordinate ActiveTimingScales ActiveClampedTrajectory

/-- Uniform scalar-to-source timing bridge. The a.e. law is required only
before a hit, on a finite horizon; no first hitting time is assumed to exist. -/
theorem eventual_actual_first_hit (n d : ℕ) (c B D U : ℝ)
    (hc : 0 < c) (hB : 0 ≤ B) (hD : 0 ≤ D) (hU0 : 0 < U) (hU2 : U < 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ β : ℝ in atTop, 1 < β ∧
      ∀ (model : Model) (X : ℝ → Configuration n d), Solves model β X →
      ∀ (shift : ℝ), 0 ≤ shift → ∀ (clock : ℝ → ℝ), ClockRelation β X shift clock →
      ∀ (a : ℝ), 0 ≤ a → ∀ (i j : Fin n),
        ⟪(accelerated X shift clock a i).val, (accelerated X shift clock a j).val⟫ ∈ Ioo (-1 : ℝ) 1 →
        |logHalfAngle ⟪(accelerated X shift clock a i).val,
          (accelerated X shift clock a j).val⟫| ≤ B →
        (∀ᵐ t ∂volume, t ∈ Ioo a (a + 2 / c) →
          (∀ u ∈ Icc a t, mesoscopicScale β <
            angularDist (accelerated X shift clock u i) (accelerated X shift clock u j)) →
          1 - ⟪(accelerated X shift clock t i).val, (accelerated X shift clock t j).val⟫ ≤ U ∧
          ∃ v : ℝ, HasDerivAt (fun u => logHalfAngle
            ⟪(accelerated X shift clock u i).val, (accelerated X shift clock u j).val⟫) v t ∧
            |v + c * Real.log β| ≤ D * β ^ (-(1 : ℝ) / 3) * Real.log β) →
        ∃ t₁ ∈ Ioc a (a + 2 / c),
          angularDist (accelerated X shift clock t₁ i) (accelerated X shift clock t₁ j) =
            mesoscopicScale β ∧
          (∀ u ∈ Ico a t₁, mesoscopicScale β <
            angularDist (accelerated X shift clock u i) (accelerated X shift clock u j)) ∧
          |t₁ - a - 1 / (2 * c)| ≤ K * (Real.log (Real.log β) / Real.log β) := by
  obtain ⟨K, hK, htiming⟩ := ActiveTiming.eventual_mesoscopic_timing c B D hc hB hD
  have hlim : Tendsto (fun β => mesoscopicScale β ^ 2 / 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0), zero_div] using
      (tendsto_mesoscopicScale.pow 2).div_const (2 : ℝ)
  refine ⟨K, hK, ?_⟩
  filter_upwards [htiming, tendsto_mesoscopicScale.eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)), hlim.eventually (gt_mem_nhds hU0)]
    with β htime hmeso htargetU
  obtain ⟨hβ, htime⟩ := htime
  have hθ : mesoscopicScale β ∈ Ioo (0 : ℝ) Real.pi :=
    ⟨mesoscopicScale_pos hβ, hmeso.trans_le (by linarith only [Real.two_le_pi])⟩
  have htcos : Real.cos (mesoscopicScale β) ∈ Ioo (-1 : ℝ) 1 := by
    have h1 := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ)) hθ.2.le hθ.1
    have hn := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.1.le (le_refl Real.pi) hθ.2
    simpa only [Real.cos_zero, Real.cos_pi] using And.intro hn h1
  have hUt : 1 - Real.cos (mesoscopicScale β) < U := by
    have hh := Real.one_sub_sq_div_two_le_cos (x := mesoscopicScale β)
    linarith only [hh, htargetU]
  refine ⟨hβ, ?_⟩
  intro model X hX shift hshift clock hclock a ha i j hstart hBstart hlaw
  let ρ : ℝ → ℝ := fun t => ⟪(accelerated X shift clock t i).val,
    (accelerated X shift clock t j).val⟫
  obtain ⟨lo, hi, hlo, hhi, hloinit, hhiinit, hloU, hlot, hhit⟩ :=
    exists_clamp hstart htcos hU2 hUt
  let f : ℝ → ℝ := fun t => clampedLogHalfAngle lo hi (ρ t)
  have hfl : ∀ t, angleLog (mesoscopicScale β) < f t ↔
      mesoscopicScale β < angularDist (accelerated X shift clock t i) (accelerated X shift clock t j) := by
    intro t
    rw [angleLog_eq_logHalfAngle_cos hθ]
    exact (clampedLogHalfAngle_gt_iff hlo hhi ⟨hlot, hhit⟩).trans
      (correlation_lt_cos_iff _ _ hθ.1.le hθ.2.le)
  have hac := absolutelyContinuous_clamped model β hβ X hX shift hshift clock hclock i j
    hlo hhi (hlot.trans hhit).le a (a + 2 / c) ha (le_add_of_nonneg_right (by positivity))
  have hinit : |f a| ≤ B := by
    dsimp only [f]
    rw [clampedLogHalfAngle_eq ⟨hloinit.le, hhiinit.le⟩]
    exact hBstart
  have hρAE := (ae_restrict_iff' measurableSet_Ici).mp
    (ActiveTrajectory.ae_accelerated_correlation_hasDerivAt model β X hX shift hshift clock hclock i j)
  obtain ⟨t₁, ht₁, hvalue, hbefore, herr⟩ := htime a f hac hinit (by
    filter_upwards [hlaw, hρAE] with t ht hρ hmem hprefix
    have hpref : ∀ u ∈ Icc a t, mesoscopicScale β <
        angularDist (accelerated X shift clock u i) (accelerated X shift clock u j) :=
      fun u hu => (hfl u).mp (hprefix u hu)
    obtain ⟨hu, v, hd, hv⟩ := ht hmem hpref
    have hρt := hρ (ha.trans hmem.1.le)
    have hcurrent := (clampedLogHalfAngle_gt_iff hlo hhi ⟨hlot, hhit⟩).mp (by
      simpa only [← angleLog_eq_logHalfAngle_cos hθ] using hprefix t ⟨hmem.1.le, le_rfl⟩)
    have hrange : ρ t ∈ Ioo lo hi := ⟨hloU.trans_le (by dsimp only [ρ]; linarith only [hu]),
      hcurrent.trans hhit⟩
    have hdf : HasDerivAt f v t := by
      apply hd.congr_of_eventuallyEq
      filter_upwards [hρt.continuousAt.eventually (Ioo_mem_nhds hrange.1 hrange.2)] with u hu
      exact clampedLogHalfAngle_eq ⟨hu.1.le, hu.2.le⟩
    rwa [hdf.deriv])
  refine ⟨t₁, ht₁, ?_, fun u hu => (hfl u).mp (hbefore u hu), herr⟩
  apply (correlation_eq_cos_iff _ _ hθ.1.le hθ.2.le).mp
  apply (clampedLogHalfAngle_eq_iff hlo hhi ⟨hlot, hhit⟩).mp
  simpa only [angleLog_eq_logHalfAngle_cos hθ] using hvalue

end Metastability.ActiveStoppedTiming
