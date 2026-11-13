import Metastability.GeneralClock
import Metastability.PairDeficit
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Actual correlation dynamics under the source clock

The estimates here supply regularity and chain rules from the source ODE and
the literal inverse-integral clock. No reduced scalar equation is assumed.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

namespace Metastability.ActiveTrajectory
open Source
variable {n d : ℕ}

theorem abs_vectorField_coordinate_le_two (model : Model) (β : ℝ) (hβ : 0 ≤ β)
    (x : Configuration n d) (i : Fin n) (w : Sphere d) :
    |⟪vectorField model β x i, w.val⟫| ≤ 2 := by
  rw [ModelBounds.vectorField_coordinate]
  calc
    _ ≤ ∑ j, |coefficient model β x i j *
        (⟪(x j).val, w.val⟫ - ⟪(x i).val, (x j).val⟫ * ⟪(x i).val, w.val⟫)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, coefficient model β x i j * 2 := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (ModelBounds.coefficient_nonneg model β x i j)]
      exact mul_le_mul_of_nonneg_left (ModelBounds.projected_coordinate_abs_le_two _ _ _)
        (ModelBounds.coefficient_nonneg model β x i j)
    _ ≤ 2 := by
      rw [← Finset.sum_mul]
      linarith only [ModelBounds.row_sum_le_one model β hβ x i]

theorem abs_velocity_le_four (model : Model) (β : ℝ) (hβ : 0 ≤ β)
    (x : Configuration n d) (i j : Fin n) :
    |PairDeficit.velocity model β x i j| ≤ 4 := by
  rw [PairDeficit.velocity, abs_neg, real_inner_comm (vectorField model β x j) (x i).val]
  exact (abs_add_le _ _).trans (by
    linarith only [abs_vectorField_coordinate_le_two model β hβ x i (x j),
      abs_vectorField_coordinate_le_two model β hβ x j (x i)])

theorem correlation_hasDerivWithinAt (model : Model) (β : ℝ)
    (X : ℝ → Configuration n d) (hX : Solves model β X) (i j : Fin n)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun u => ⟪(X u i).val, (X u j).val⟫)
      (-PairDeficit.velocity model β (X t) i j) (Ici 0) t := by
  simpa only [PairDeficit.deficit, sub_sub_cancel] using
    (PairDeficit.hasDerivWithinAt model β X hX i j t ht).const_sub 1

theorem correlation_hasDerivAt (model : Model) (β : ℝ)
    (X : ℝ → Configuration n d) (hX : Solves model β X) (i j : Fin n)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun u => ⟪(X u i).val, (X u j).val⟫)
      (-PairDeficit.velocity model β (X t) i j) t :=
  (correlation_hasDerivWithinAt model β X hX i j t ht.le).hasDerivAt (Ici_mem_nhds ht)

theorem correlation_lipschitz (model : Model) (β : ℝ) (hβ : 0 ≤ β)
    (X : ℝ → Configuration n d) (hX : Solves model β X) (i j : Fin n) :
    LipschitzOnWith 4 (fun u => ⟪(X u i).val, (X u j).val⟫) (Ici 0) := by
  apply (convex_Ici (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => correlation_hasDerivWithinAt model β X hX i j t ht)
  intro t _
  exact_mod_cast (by simpa only [norm_neg, Real.norm_eq_abs] using
    abs_velocity_le_four model β hβ (X t) i j :
      ‖-PairDeficit.velocity model β (X t) i j‖ ≤ (4 : ℝ))

/-- Every source clock agrees with the constructed Lipschitz inverse. -/
theorem clock_lipschitz (model : Model) (β : ℝ) (hβ : 1 < β)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (shift : ℝ) (hshift : 0 ≤ shift) (clock : ℝ → ℝ)
    (hc : ClockRelation β X shift clock) :
    LipschitzOnWith (Real.toNNReal (max 1 (Real.log β * Real.exp (2 * β)))) clock (Ici 0) := by
  have heq := GeneralClock.clockRelation_unique_on_nonnegative hc
    (GeneralClock.clockRelation β hβ X hX shift hshift)
  intro s hs t ht
  rw [heq hs, heq ht]
  exact (GeneralClock.boundedRate β hβ X hX shift).clock_lipschitz s t

/-- The original-time argument is positive at positive accelerated times. -/
theorem shifted_clock_pos {β shift : ℝ} {X : ℝ → Configuration n d}
    {clock : ℝ → ℝ} (hc : ClockRelation β X shift clock) (hshift : 0 ≤ shift)
    {t : ℝ} (ht : 0 < t) : 0 < shift + clock t := by
  have hp := hc.2.1 (show (0 : ℝ) ∈ Ici (0 : ℝ) from le_refl (0 : ℝ)) ht.le ht
  rw [hc.1.1] at hp
  exact add_pos_of_nonneg_of_pos hshift hp

/-- Almost-everywhere chain rule with the actual finite-minimum clock rate. -/
theorem ae_accelerated_correlation_hasDerivAt (model : Model) (β : ℝ)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (shift : ℝ) (hshift : 0 ≤ shift) (clock : ℝ → ℝ)
    (hc : ClockRelation β X shift clock) (i j : Fin n) :
    ∀ᵐ t ∂volume.restrict (Ici (0 : ℝ)),
      HasDerivAt (fun u => ⟪(accelerated X shift clock u i).val,
        (accelerated X shift clock u j).val⟫)
        ((-PairDeficit.velocity model β (accelerated X shift clock t) i j) *
          clockFactor β (accelerated X shift clock t)) t := by
  have hne : ∀ᵐ t ∂volume.restrict (Ici (0 : ℝ)), t ≠ 0 :=
    (volume.restrict (Ici (0 : ℝ))).ae_ne 0
  filter_upwards [hc.1.2.2.2, ae_restrict_mem measurableSet_Ici, hne] with t hclock ht hne
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hne)
  have hd := correlation_hasDerivAt model β X hX i j (shift + clock t)
    (shifted_clock_pos hc hshift htpos)
  exact hd.comp t (hclock.const_add shift)

/-- Accelerated correlations are Lipschitz on the whole nonnegative halfline. -/
theorem accelerated_correlation_lipschitz (model : Model) (β : ℝ) (hβ : 1 < β)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (shift : ℝ) (hshift : 0 ≤ shift) (clock : ℝ → ℝ)
    (hc : ClockRelation β X shift clock) (i j : Fin n) :
    LipschitzOnWith (4 * Real.toNNReal (max 1 (Real.log β * Real.exp (2 * β))))
      (fun t => ⟪(accelerated X shift clock t i).val,
        (accelerated X shift clock t j).val⟫) (Ici 0) := by
  have hl := clock_lipschitz model β hβ X hX shift hshift clock hc
  have hs : LipschitzOnWith (Real.toNNReal (max 1 (Real.log β * Real.exp (2 * β))))
      (fun t => shift + clock t) (Ici 0) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    simpa only [dist_eq_norm, add_sub_add_left_eq_sub] using hl.dist_le_mul s hs t ht
  exact (correlation_lipschitz model β (by linarith only [hβ]) X hX i j).comp hs
    (fun t ht => add_nonneg hshift (hc.1.2.1 t ht))

/-- Absolute continuity needed to integrate the almost-everywhere scalar law. -/
theorem accelerated_correlation_absolutelyContinuous (model : Model) (β : ℝ) (hβ : 1 < β)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (shift : ℝ) (hshift : 0 ≤ shift) (clock : ℝ → ℝ)
    (hc : ClockRelation β X shift clock) (i j : Fin n)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval (fun t => ⟪(accelerated X shift clock t i).val,
      (accelerated X shift clock t j).val⟫) a b := by
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  apply (accelerated_correlation_lipschitz model β hβ X hX shift hshift clock hc i j).mono
  rw [uIcc_of_le hab]
  exact fun _ ht => ha.trans ht.1

end Metastability.ActiveTrajectory
