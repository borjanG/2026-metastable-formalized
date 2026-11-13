import Metastability.BarycenterRegularity
import Metastability.ActiveParticleTrajectory

/-! Actual-clock barycenter displacement from the checked differential formula.
The explicit velocity-error hypotheses in this internal analytic composition
are supplied by the source vector law in the final stage theorem. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace NNReal
namespace Metastability.BarycenterTrajectory
open Source AngularGeometry BarycenterFormula BarycenterBounds BarycenterRegularity
variable {n d : ℕ}

theorem weight_balance (model : Model) (B C : Block n) (hB : B.Nonempty) (hC : C.Nonempty)
    (r : ℝ) :
    centerWeight model B * ((C.card : ℝ) / ActiveCoefficients.blockDenominator model B * r) =
      centerWeight model C * ((B.card : ℝ) / ActiveCoefficients.blockDenominator model C * r) := by
  have hb : (B.card : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast Finset.card_pos.mpr hB)
  have hc : (C.card : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast Finset.card_pos.mpr hC)
  cases model <;> simp only [centerWeight, ActiveCoefficients.blockDenominator]
  · ring
  · field_simp

/-- Endpoint displacement for an actual accelerated pair. Particle regularity,
unit-sphere tangency and the barycenter's interval regularity are all derived. -/
theorem variation_le (model : Model) (β : ℝ) (hβ : 1 < β)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (shift : ℝ) (hshift : 0 ≤ shift) (clock : ℝ → ℝ)
    (hc : ClockRelation β X shift clock) (i j : Fin n)
    (a b wa wb α γ R E m : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hwa : 0 < wa) (hwb : 0 < wb) (hbalance : wa * α = wb * γ)
    (hR : 0 ≤ R) (hE : 0 ≤ E) (hm : 0 < m)
    (hangle : ∀ t ∈ Icc a b, 0 < angularDist (accelerated X shift clock t i) (accelerated X shift clock t j) ∧
      angularDist (accelerated X shift clock t i) (accelerated X shift clock t j) < Real.pi)
    (hsine : ∀ t ∈ Icc a b, m ≤ Real.sin (angularDist (accelerated X shift clock t i) (accelerated X shift clock t j)))
    (herr : ∀ t ∈ Icc a b,
      let p := accelerated X shift clock t i
      let q := accelerated X shift clock t j
      let v := clockFactor β (accelerated X shift clock t) • vectorField model β (accelerated X shift clock t) i
      let w := clockFactor β (accelerated X shift clock t) • vectorField model β (accelerated X shift clock t) j
      ‖v - α • projectTangent p q.val‖ ≤ R * Real.sin (angularDist p q) + E ∧
      ‖w - γ • projectTangent q p.val‖ ≤ R * Real.sin (angularDist p q) + E) :
    ‖vector (wb / (wa + wb)) (accelerated X shift clock b i).val (accelerated X shift clock b j).val -
      vector (wb / (wa + wb)) (accelerated X shift clock a i).val (accelerated X shift clock a j).val‖ ≤
      (12 * (R + E / m)) * (b - a) := by
  let p : ℝ → Sphere d := fun t => accelerated X shift clock t i
  let q : ℝ → Sphere d := fun t => accelerated X shift clock t j
  have hp := (ActiveParticleTrajectory.accelerated_lipschitz model β hβ X hX shift hshift clock hc i).mono
    (show Icc a b ⊆ Ici 0 from fun _ ht => ha.trans ht.1)
  have hq := (ActiveParticleTrajectory.accelerated_lipschitz model β hβ X hX shift hshift clock hc j).mono
    (show Icc a b ⊆ Ici 0 from fun _ ht => ha.trans ht.1)
  have hneq : ∀ t ∈ Icc a b, p t ≠ q t := by
    intro t ht he
    have hz := (hangle t ht).1
    change 0 < angularDist (p t) (q t) at hz
    rw [he, angularDist_self] at hz
    exact lt_irrefl 0 hz
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_vector (wb / (wa + wb)) p q a b hp hq hneq
    (fun t ht => (hangle t ht).2)
  have hdi := ActiveParticleTrajectory.ae_hasDerivAt model β X hX shift hshift clock hc i
  have hdj := ActiveParticleTrajectory.ae_hasDerivAt model β X hX shift hshift clock hc j
  rw [ae_restrict_iff' measurableSet_Ici] at hdi hdj
  apply ActiveParticleTrajectory.norm_sub_le_of_ae_hasDerivAt_bound hab (by positivity) hK
  filter_upwards [hdi, hdj] with t hit hjt ht
  have htcc : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
  have ht0 : t ∈ Ici 0 := ha.trans ht.1.le
  have hpi := hit ht0
  have hqj := hjt ht0
  have hρlo : -1 < ⟪(p t).val, (q t).val⟫ := Real.arccos_lt_pi.mp (hangle t htcc).2
  have hρhi : ⟪(p t).val, (q t).val⟫ < 1 := Real.arccos_pos.mp (hangle t htcc).1
  refine ⟨_, hasDerivAt_vector (wb / (wa + wb)) (fun t => (p t).val) (fun t => (q t).val) _ _ t hpi hqj hρlo hρhi, ?_⟩
  have hd := norm_differential_le_error wa wb hwa hwb (p t) (q t) _ _ α γ R E hbalance
    (derivative_tangent p _ t hpi) (derivative_tangent q _ t hqj)
    (hneq t htcc) (hangle t htcc).2 (herr t htcc).1 (herr t htcc).2
  have hdiv : E / Real.sin (angularDist (p t) (q t)) ≤ E / m :=
    div_le_div_of_nonneg_left hE hm (hsine t htcc)
  exact hd.trans (by linarith only [hdiv])

end Metastability.BarycenterTrajectory
