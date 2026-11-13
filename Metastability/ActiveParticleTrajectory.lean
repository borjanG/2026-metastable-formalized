import Metastability.ActiveVectorLaw

/-! Actual accelerated particle regularity and displacement from the source
ODE and its a.e. inverse-integral clock. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace NNReal
namespace Metastability.ActiveParticleTrajectory
open Source ActiveVectorLaw
variable {n d : ℕ}

theorem vectorField_norm_le_two (model : Model) (β : ℝ) (hβ : 0 ≤ β)
    (x : Configuration n d) (i : Fin n) : ‖vectorField model β x i‖ ≤ 2 := by
  rw [vectorField_eq_sum]
  calc
    _ ≤ ∑ k, ‖coefficient model β x i k • projectTangent (x i) (x k).val‖ := norm_sum_le _ _
    _ ≤ ∑ k, coefficient model β x i k * 2 := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ModelBounds.coefficient_nonneg model β x i k)]
      exact mul_le_mul_of_nonneg_left (projection_norm_le_two _ _) (ModelBounds.coefficient_nonneg model β x i k)
    _ ≤ 2 := by
      rw [← Finset.sum_mul]
      linarith only [ModelBounds.row_sum_le_one model β hβ x i]

theorem particle_lipschitz (model : Model) (β : ℝ) (hβ : 0 ≤ β)
    (X : ℝ → Configuration n d) (hX : Solves model β X) (i : Fin n) :
    LipschitzOnWith 2 (fun u => (X u i).val) (Ici 0) := by
  apply (convex_Ici (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => hX t ht i)
  intro t _
  exact_mod_cast vectorField_norm_le_two model β hβ (X t) i

theorem ae_hasDerivAt (model : Model) (β : ℝ)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (shift : ℝ) (hshift : 0 ≤ shift) (clock : ℝ → ℝ)
    (hc : ClockRelation β X shift clock) (i : Fin n) :
    ∀ᵐ t ∂volume.restrict (Ici (0 : ℝ)),
      HasDerivAt (fun u => (accelerated X shift clock u i).val)
        (clockFactor β (accelerated X shift clock t) • vectorField model β (accelerated X shift clock t) i) t := by
  have hne : ∀ᵐ t ∂volume.restrict (Ici (0 : ℝ)), t ≠ 0 :=
    (volume.restrict (Ici (0 : ℝ))).ae_ne 0
  filter_upwards [hc.1.2.2.2, ae_restrict_mem measurableSet_Ici, hne] with t hclock ht hne
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm hne)
  have hu := ActiveTrajectory.shifted_clock_pos hc hshift htpos
  have hd := (hX (shift + clock t) hu.le i).hasDerivAt (Ici_mem_nhds hu)
  exact hd.scomp t (hclock.const_add shift)

theorem accelerated_lipschitz (model : Model) (β : ℝ) (hβ : 1 < β)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (shift : ℝ) (hshift : 0 ≤ shift) (clock : ℝ → ℝ)
    (hc : ClockRelation β X shift clock) (i : Fin n) :
    LipschitzOnWith (2 * Real.toNNReal (max 1 (Real.log β * Real.exp (2 * β))))
      (fun t => (accelerated X shift clock t i).val) (Ici 0) := by
  have hl := ActiveTrajectory.clock_lipschitz model β hβ X hX shift hshift clock hc
  have hs : LipschitzOnWith (Real.toNNReal (max 1 (Real.log β * Real.exp (2 * β))))
      (fun t => shift + clock t) (Ici 0) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    simpa only [dist_eq_norm, add_sub_add_left_eq_sub] using hl.dist_le_mul s hs t ht
  exact (particle_lipschitz model β (zero_lt_one.trans hβ).le X hX i).comp hs
    (fun t ht => add_nonneg hshift (hc.1.2.1 t ht))

theorem absolutelyContinuous (model : Model) (β : ℝ) (hβ : 1 < β)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (shift : ℝ) (hshift : 0 ≤ shift) (clock : ℝ → ℝ)
    (hc : ClockRelation β X shift clock) (i : Fin n)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval (fun t => (accelerated X shift clock t i).val) a b := by
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  apply (accelerated_lipschitz model β hβ X hX shift hshift clock hc i).mono
  rw [uIcc_of_le hab]
  exact fun _ ht => ha.trans ht.1


/-- A vector displacement follows from the scalar absolute-continuity theorem
by testing against the endpoint displacement. -/
theorem norm_sub_le_of_ae_hasDerivAt_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {f : ℝ → E} {a b K : ℝ} {Q : ℝ≥0}
    (hab : a ≤ b) (hK : 0 ≤ K) (hf : LipschitzOnWith Q f (Icc a b))
    (hd : ∀ᵐ t ∂volume, t ∈ Ioo a b → ∃ v, HasDerivAt f v t ∧ ‖v‖ ≤ K) :
    ‖f b - f a‖ ≤ K * (b - a) := by
  let w := f b - f a
  let g : ℝ → ℝ := fun t => ⟪w, f t⟫
  have hglip := (innerSL ℝ w).lipschitz.comp_lipschitzOnWith hf
  have hg : AbsolutelyContinuousOnInterval g a b := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    rw [uIcc_of_le hab]
    exact hglip
  have hbound := ActiveTiming.sub_le_of_ae_deriv_le hab hg (by
    filter_upwards [hd] with t ht hmem
    obtain ⟨v, hv, hvK⟩ := ht hmem
    have hgd : HasDerivAt g ⟪w, v⟫ t := by
      simpa only [inner_zero_left, add_zero] using (hasDerivAt_const t w).inner ℝ hv
    rw [hgd.deriv]
    exact (le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left hvK (norm_nonneg w))))
  have heq : g b - g a = ‖w‖ ^ 2 := by
    dsimp only [g]
    rw [← inner_sub_right]
    exact real_inner_self_eq_norm_sq w
  rw [heq] at hbound
  by_cases hw : ‖w‖ = 0
  · change ‖w‖ ≤ _
    rw [hw]
    exact mul_nonneg hK (sub_nonneg.mpr hab)
  · have hwpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw)
    have hh : ‖w‖ * ‖w‖ ≤ ‖w‖ * (K * (b - a)) := by nlinarith only [hbound]
    exact (mul_le_mul_iff_right₀ hwpos).mp hh

end Metastability.ActiveParticleTrajectory
