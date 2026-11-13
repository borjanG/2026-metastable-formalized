import Metastability.ActiveTrajectory
import Metastability.ActiveTiming

/-!
# Change of variables for the literal source clock

The cutoff rate need only be measurable. Absolute continuity and its a.e.
derivative suffice; no classical differentiability at clock switches is used.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace Metastability.PlateauClockSubstitution
open Source
variable {n d : ℕ}

/-- A continuous real primitive is Lipschitz on every compact interval. -/
theorem exists_lipschitzOn_primitive (g : ℝ → ℝ) (hg : Continuous g) (A B : ℝ) :
    ∃ K : NNReal, LipschitzOnWith K (fun u => ∫ v in A..u, g v) (Icc A B) := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨Real.toNNReal (max R 0), ?_⟩
  apply (convex_Icc A B).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f' := g)
    (fun u _ => (intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable A u)
      (hg.stronglyMeasurableAtFilter volume (𝓝 u)) hg.continuousAt).hasDerivWithinAt)
  intro u hu
  apply NNReal.coe_le_coe.mp
  rw [Real.coe_toNNReal _ (le_max_right _ _)]
  exact (hR u hu).trans (le_max_left _ _)

/-- Substitution by any actual source clock, for an original-time integrand
continuous on the nonnegative halfline. Both integrability assertions are
proved together with the equality. -/
theorem integral_substitution (model : Model) (β : ℝ) (hβ : 1 < β)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (shift : ℝ) (hshift : 0 ≤ shift) (clock : ℝ → ℝ) (hc : ClockRelation β X shift clock)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Ici (0 : ℝ))) :
    IntervalIntegrable g volume (shift + clock a) (shift + clock b) ∧
    IntervalIntegrable (fun t => g (shift + clock t) * clockFactor β (accelerated X shift clock t)) volume a b ∧
    (∫ u in (shift + clock a)..(shift + clock b), g u) =
      ∫ t in a..b, g (shift + clock t) * clockFactor β (accelerated X shift clock t) := by
  let σ : ℝ → ℝ := fun t => shift + clock t
  have hσnonneg : ∀ t ∈ Ici (0 : ℝ), 0 ≤ σ t :=
    fun t ht => add_nonneg hshift (hc.1.2.1 t ht)
  have hσmono : MonotoneOn σ (Ici (0 : ℝ)) := by
    intro s hs t ht hst
    exact add_le_add le_rfl (hc.2.1.monotoneOn hs ht hst)
  have hσab : σ a ≤ σ b := hσmono ha (ha.trans hab) hab
  have hσmaps : MapsTo σ (Icc a b) (Icc (σ a) (σ b)) := by
    intro t ht
    exact ⟨hσmono ha (ha.trans ht.1) ht.1,
      hσmono (ha.trans ht.1) (ha.trans hab) ht.2⟩
  have hσlip : LipschitzOnWith
      (Real.toNNReal (max 1 (Real.log β * Real.exp (2 * β)))) σ (Icc a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    simpa only [σ, dist_eq_norm, add_sub_add_left_eq_sub] using
      (ActiveTrajectory.clock_lipschitz model β hβ X hX shift hshift clock hc).dist_le_mul
        s (ha.trans hs.1) t (ha.trans ht.1)
  let gext : ℝ → ℝ := fun u => g (max 0 u)
  have hge : Continuous gext :=
    hg.comp_continuous (continuous_const.max continuous_id) (fun u => le_max_left 0 u)
  have hgeq : ∀ u, 0 ≤ u → gext u = g u := by
    intro u hu
    exact congrArg g (max_eq_right hu)
  let G : ℝ → ℝ := fun u => ∫ v in (σ a)..u, gext v
  have hGd : ∀ u, HasDerivAt G (gext u) u := by
    intro u
    exact intervalIntegral.integral_hasDerivAt_right (hge.intervalIntegrable (σ a) u)
      (hge.stronglyMeasurableAtFilter volume (𝓝 u)) hge.continuousAt
  obtain ⟨K, hK⟩ := exists_lipschitzOn_primitive gext hge (σ a) (σ b)
  have hGlip := hK.comp hσlip hσmaps
  have hGac : AbsolutelyContinuousOnInterval (fun t => G (σ t)) a b := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hab] using hGlip
  have hAE : ∀ᵐ t ∂volume, t ∈ Icc a b →
      deriv (fun u => G (σ u)) t = g (σ t) * clockFactor β (accelerated X shift clock t) := by
    have hclockAE := (ae_restrict_iff' measurableSet_Ici).mp hc.1.2.2.2
    filter_upwards [hclockAE] with t ht hmem
    have ht0 := ha.trans hmem.1
    have hcomp := (hGd (σ t)).comp t ((ht ht0).const_add shift)
    rw [hgeq _ (hσnonneg t ht0)] at hcomp
    exact hcomp.deriv
  have hright : IntervalIntegrable
      (fun t => g (σ t) * clockFactor β (accelerated X shift clock t)) volume a b := by
    apply hGac.intervalIntegrable_deriv.congr_ae
    apply (ae_restrict_iff' measurableSet_uIoc).mpr
    filter_upwards [hAE] with t ht hmem
    rw [uIoc_of_le hab] at hmem
    exact ht ⟨hmem.1.le, hmem.2⟩
  have hleft : IntervalIntegrable g volume (σ a) (σ b) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hσab]
    exact hg.mono (fun _ hu => (hσnonneg a ha).trans hu.1)
  have hFTC : (∫ t in a..b, g (σ t) * clockFactor β (accelerated X shift clock t)) =
      G (σ b) - G (σ a) := by
    rw [← hGac.integral_deriv_eq_sub]
    symm
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hAE] with t ht hmem
    rw [uIoc_of_le hab] at hmem
    exact ht ⟨hmem.1.le, hmem.2⟩
  have hGa : G (σ a) = 0 := intervalIntegral.integral_same
  have hGb : G (σ b) = ∫ u in (σ a)..(σ b), g u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hσab] at hu
    exact hgeq u ((hσnonneg a ha).trans hu.1)
  refine ⟨hleft, hright, ?_⟩
  rw [hGb, hGa, sub_zero] at hFTC
  exact hFTC.symm

end Metastability.PlateauClockSubstitution
