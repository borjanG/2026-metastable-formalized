import Metastability.ContractionComparison
import Metastability.ContractionInteraction
import Metastability.ContractionScale
import Metastability.ContractionPointwise

/-!
# Original-time block contraction from the source dynamics

The source ODE supplies the actual pair-deficit derivatives. Scalar comparison
integrates their bounds, and a finite-maximum argument proves visible-diameter
confinement from a conditional exterior-separation assumption.
-/

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace

namespace Metastability.ContractionDynamics

open Source
variable {n d : ℕ}

theorem gronwall_of_velocity_le (model : Model) (β : ℝ)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (D : Block n) (hD : D.Nonempty) (i j : Fin n)
    {a b c C : ℝ} (ha : 0 ≤ a)
    (hv : ∀ u ∈ Ico a b,
      PairDeficit.velocity model β (X u) i j ≤
        (-c + C * ContractionInteraction.exterior β (X u) D hD) *
          PairDeficit.deficit (X u) i j)
    {t : ℝ} (ht : t ∈ Icc a b) :
    PairDeficit.deficit (X t) i j ≤ PairDeficit.deficit (X a) i j *
      Real.exp (-c * (t - a) + C * ∫ u in a..t, ContractionInteraction.exterior β (X u) D hD) := by
  apply ContractionComparison.contraction_bound
    (fun u => PairDeficit.deficit (X u) i j)
    (fun u => PairDeficit.velocity model β (X u) i j)
    (fun u => ContractionInteraction.exterior β (X u) D hD)
  · exact (PairDeficit.continuousOn model β X hX i j).mono (fun u hu => ha.trans hu.1)
  · exact (ContractionInteraction.continuousOn_exterior_of_solves model β X hX D hD).mono
      (fun u hu => ha.trans hu.1)
  · intro u hu
    exact PairDeficit.hasDerivWithinAt_right model β X hX i j u (ha.trans hu.1)
  · exact hv
  · exact ht

theorem diameter_invariant_of_confined_decay (model : Model) (β : ℝ)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (D : Block n) (hD : D.Nonempty) {a b ε c : ℝ}
    (ha : 0 ≤ a) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hc : 0 < c)
    (hstart : ∀ i ∈ D, ∀ j ∈ D, angularDist (X a i) (X a j) ≤ ε)
    (hv : ∀ u ∈ Ico a b,
      (∀ i ∈ D, ∀ j ∈ D, angularDist (X u i) (X u j) ≤ ε) →
      ∀ i ∈ D, ∀ j ∈ D,
        PairDeficit.velocity model β (X u) i j ≤ -c * PairDeficit.deficit (X u) i j)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ∀ i ∈ D, ∀ j ∈ D, angularDist (X t i) (X t j) ≤ ε := by
  have hεπ : ε ≤ Real.pi := hε1.trans (by linarith only [Real.two_le_pi])
  have hR : 0 < 1 - Real.cos ε := by
    have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 0) hεπ hε0
    rw [Real.cos_zero] at hcos
    exact sub_pos.mpr hcos
  have hbound := ContractionComparison.finite_maximum_le_of_strict_boundary
    (D.product D) (hD.product hD)
    (fun p u => PairDeficit.deficit (X u) p.1 p.2)
    (fun p u => PairDeficit.velocity model β (X u) p.1 p.2)
    (a := a) (b := b) (R := 1 - Real.cos ε)
    (fun p _ => (PairDeficit.continuousOn model β X hX p.1 p.2).mono
      (fun u hu => ha.trans hu.1))
    (fun u hu p _ => PairDeficit.hasDerivWithinAt_right model β X hX p.1 p.2 u (ha.trans hu.1))
    (fun p hp => (ContractionScale.angularDist_le_iff_deficit_le (X a) p.1 p.2 hε0.le hεπ).mp
      (hstart p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2))
    (by
      intro u hu hconf p hp hboundary
      have hdiam : ∀ i ∈ D, ∀ j ∈ D, angularDist (X u i) (X u j) ≤ ε := by
        intro i hi j hj
        apply (ContractionScale.angularDist_le_iff_deficit_le (X u) i j hε0.le hεπ).mpr
        exact hconf (i, j) (Finset.mem_product.mpr ⟨hi, hj⟩)
      have h := hv u hu hdiam p.1 (Finset.mem_product.mp hp).1
        p.2 (Finset.mem_product.mp hp).2
      change PairDeficit.deficit (X u) p.1 p.2 = 1 - Real.cos ε at hboundary
      rw [hboundary] at h
      exact h.trans_lt (mul_neg_of_neg_of_pos (neg_neg_of_pos hc) hR)) ht
  intro i hi j hj
  apply (ContractionScale.angularDist_le_iff_deficit_le (X t) i j hε0.le hεπ).mpr
  exact hbound (i, j) (Finset.mem_product.mpr ⟨hi, hj⟩)

theorem decay_of_velocity_le (model : Model) (β : ℝ)
    (X : ℝ → Configuration n d) (hX : Solves model β X) (i j : Fin n)
    {a b c : ℝ} (ha : 0 ≤ a)
    (hv : ∀ u ∈ Ico a b,
      PairDeficit.velocity model β (X u) i j ≤ -c * PairDeficit.deficit (X u) i j)
    {t : ℝ} (ht : t ∈ Icc a b) :
    PairDeficit.deficit (X t) i j ≤ PairDeficit.deficit (X a) i j * Real.exp (-c * (t - a)) := by
  have h := ContractionComparison.contraction_bound
    (fun u => PairDeficit.deficit (X u) i j)
    (fun u => PairDeficit.velocity model β (X u) i j) (fun _ => 0)
    (c := c) (C := 0)
    ((PairDeficit.continuousOn model β X hX i j).mono (fun u hu => ha.trans hu.1))
    continuousOn_const
    (fun u hu => PairDeficit.hasDerivWithinAt_right model β X hX i j u (ha.trans hu.1))
    (fun u hu => by simpa only [zero_mul, add_zero] using hv u hu) ht
  simpa only [zero_mul, add_zero] using h

/-- The source ODE and the small block diameter imply the literal original-time
Gronwall estimate, with the source exterior interaction inside the integral. -/
theorem interval_gronwall (hn : 0 < n) (model : Model) (β : ℝ) (hβ : 0 ≤ β)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hβε : β * ε ^ 2 ≤ 1 / (40 * (n : ℝ) ^ 2))
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (D : Block n) (hD : D.Nonempty) {a b : ℝ} (ha : 0 ≤ a)
    (hdiam : ∀ u ∈ Icc a b, ∀ i ∈ D, ∀ j ∈ D,
      angularDist (X u i) (X u j) ≤ ε)
    (i j : Fin n) (hi : i ∈ D) (hj : j ∈ D)
    {t : ℝ} (ht : t ∈ Icc a b) :
    PairDeficit.deficit (X t) i j ≤ PairDeficit.deficit (X a) i j *
      Real.exp (-(1 / (4 * (n : ℝ))) * (t - a) +
        10 * ∫ u in a..t, ContractionInteraction.exterior β (X u) D hD) := by
  apply gronwall_of_velocity_le model β X hX D hD i j ha
  · intro u hu
    exact ContractionPointwise.velocity_le hn model β hβ ε hε0 hε1 hβε
      (X u) D hD (hdiam u ⟨hu.1, hu.2.le⟩) i j hi hj
  · exact ht

/-- Conditional exterior separation implies confinement and exponential
pair-deficit decay. Separation is used only at configurations already satisfying
the visible-diameter bound; the conclusion supplies that bound at every time. -/
theorem confinement_and_decay (hn : 0 < n) (model : Model) (β : ℝ) (hβ : 0 ≤ β)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hβε : β * ε ^ 2 ≤ 1 / (40 * (n : ℝ) ^ 2))
    (bstar : ℝ)
    (hext : 10 * ((n : ℝ) * (1 + β) * Real.exp (-β * bstar)) ≤
      (1 / (4 * (n : ℝ))) / 2)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (D : Block n) (hD : D.Nonempty) {a b : ℝ} (ha : 0 ≤ a)
    (hstart : ∀ i ∈ D, ∀ j ∈ D, angularDist (X a i) (X a j) ≤ ε)
    (hsep : ∀ u ∈ Icc a b,
      (∀ i ∈ D, ∀ j ∈ D, angularDist (X u i) (X u j) ≤ ε) →
      ∀ i ∈ D, ∀ k ∉ D, bstar ≤ PairDeficit.deficit (X u) i k) :
    ∀ t ∈ Icc a b,
      (∀ i ∈ D, ∀ j ∈ D, angularDist (X t i) (X t j) ≤ ε) ∧
      ∀ i ∈ D, ∀ j ∈ D,
        PairDeficit.deficit (X t) i j ≤ PairDeficit.deficit (X a) i j *
          Real.exp (-((1 / (4 * (n : ℝ))) / 2) * (t - a)) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hc : 0 < (1 / (4 * (n : ℝ))) / 2 := by positivity
  have hv : ∀ u ∈ Ico a b,
      (∀ i ∈ D, ∀ j ∈ D, angularDist (X u i) (X u j) ≤ ε) →
      ∀ i ∈ D, ∀ j ∈ D,
        PairDeficit.velocity model β (X u) i j ≤
          -((1 / (4 * (n : ℝ))) / 2) * PairDeficit.deficit (X u) i j := by
    intro u hu hdiam i hi j hj
    have hpoint := ContractionPointwise.velocity_le hn model β hβ ε hε0.le hε1 hβε
      (X u) D hD hdiam i j hi hj
    have hextu := ContractionInteraction.exterior_le_of_barrier β bstar hβ (X u) D hD
      (hsep u ⟨hu.1, hu.2.le⟩ hdiam)
    have hcoef : -(1 / (4 * (n : ℝ))) +
        10 * ContractionInteraction.exterior β (X u) D hD ≤
        -((1 / (4 * (n : ℝ))) / 2) := by
      linarith only [hext, hextu]
    exact hpoint.trans (mul_le_mul_of_nonneg_right hcoef (PairDeficit.deficit_nonneg (X u) i j))
  have hconf : ∀ t ∈ Icc a b, ∀ i ∈ D, ∀ j ∈ D,
      angularDist (X t i) (X t j) ≤ ε := by
    intro t ht
    exact diameter_invariant_of_confined_decay model β X hX D hD ha hε0 hε1 hc hstart hv ht
  intro t ht
  refine ⟨hconf t ht, ?_⟩
  intro i hi j hj
  apply decay_of_velocity_le model β X hX i j ha
  · intro u hu
    exact hv u hu (hconf u ⟨hu.1, hu.2.le⟩) i hi j hj
  · exact ht

end Metastability.ContractionDynamics
