import Metastability.ContractionScale
import Metastability.ContractionDynamics
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms

/-!
# Source block contraction for both attention models

The shared constants and inverse-temperature thresholds are chosen before
the dimension, model, trajectory, time interval, and block. Auxiliary numeric
smallness conditions are derived from the literal source visible scale.
-/

noncomputable section
open Filter Set MeasureTheory
open scoped Topology RealInnerProductSpace

namespace Metastability.BlockContraction

open Source

theorem contraction_constant_pos (n : ℕ) (hn : 0 < n) :
    0 < 1 / (4 * (n : ℝ)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

theorem exists_scale_threshold (n : ℕ) (hn : 0 < n) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      1 < β ∧ 0 < visibleScale β ∧ visibleScale β ≤ 1 ∧
        β * visibleScale β ^ 2 ≤ 1 / (40 * (n : ℝ) ^ 2) := by
  obtain ⟨B, hB⟩ := eventually_atTop.mp (ContractionScale.eventually_visibleScale_small n hn)
  refine ⟨max B 2, lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro β hβ
  exact hB β ((le_max_left _ _).trans hβ)

theorem eventually_tightening_parameters (n : ℕ) (hn : 0 < n)
    (b κ C : ℝ) (hb : 0 < b) (hC : 8 * κ / (1 / (4 * (n : ℝ))) < C) :
    ∀ᶠ β : ℝ in atTop,
      10 * ((n : ℝ) * (1 + β) * Real.exp (-β * b)) ≤ (1 / (4 * (n : ℝ))) / 2 ∧
      2 * visibleScale β ^ 2 * Real.exp (-(1 / (4 * (n : ℝ))) * C * β / 2) ≤
        Real.exp (-4 * κ * β) := by
  have hc := contraction_constant_pos n hn
  have hd : Tendsto (fun β : ℝ => 10 * ((n : ℝ) * (1 + β) * Real.exp (-β * b)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (ContractionScale.tendsto_exterior_bound n b hb).const_mul (10 : ℝ)
  filter_upwards [hd.eventually (gt_mem_nhds (half_pos hc)),
    ContractionScale.eventually_diameter_exponential_bound (1 / (4 * (n : ℝ))) κ C hc hC]
      with β hext hfinal
  exact ⟨hext.le, hfinal⟩

variable {n d : ℕ}

/-- Conversion of a source-derived velocity estimate to the manuscript's
ordinary derivative inequality almost everywhere, including intervals at zero. -/
theorem ae_derivative_bound (model : Model) (β : ℝ)
    (X : ℝ → Configuration n d) (hX : Solves model β X) (i j : Fin n)
    {a b : ℝ} (ha : 0 ≤ a) (F : ℝ → ℝ)
    (hbound : ∀ t ∈ Icc a b, PairDeficit.velocity model β (X t) i j ≤ F t) :
    ∀ᵐ t ∂volume.restrict (Icc a b),
      deriv (fun u => PairDeficit.deficit (X u) i j) t ≤ F t := by
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc,
    (volume.restrict (Icc a b)).ae_ne 0] with t ht hne
  have ht0 : 0 < t := lt_of_le_of_ne (ha.trans ht.1) (Ne.symm hne)
  rw [(PairDeficit.hasDerivAt_pos model β X hX i j t ht0).deriv]
  exact hbound t ht

/-- The interval conclusions with all numeric hypotheses exposed, for use
inside the source-facing theorem where the visible scale supplies them. -/
theorem interval_estimates (hn : 0 < n) (model : Model) (β : ℝ) (hβ : 0 ≤ β)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hβε : β * ε ^ 2 ≤ 1 / (40 * (n : ℝ) ^ 2))
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (D : Block n) (hD : D.Nonempty) {a b : ℝ} (ha : 0 ≤ a)
    (hdiam : ∀ t ∈ Icc a b, ∀ i ∈ D, ∀ j ∈ D, angularDist (X t i) (X t j) ≤ ε)
    (i j : Fin n) (hi : i ∈ D) (hj : j ∈ D) :
    (∀ t ∈ Icc a b,
      HasDerivWithinAt (fun u => PairDeficit.deficit (X u) i j)
        (PairDeficit.velocity model β (X t) i j) (Ici t) t ∧
      PairDeficit.velocity model β (X t) i j ≤
        (-(1 / (4 * (n : ℝ))) + 10 * ContractionInteraction.exterior β (X t) D hD) *
          PairDeficit.deficit (X t) i j) ∧
    (∀ᵐ t ∂volume.restrict (Icc a b),
      deriv (fun u => PairDeficit.deficit (X u) i j) t ≤
        (-(1 / (4 * (n : ℝ))) + 10 * ContractionInteraction.exterior β (X t) D hD) *
          PairDeficit.deficit (X t) i j) ∧
    (∀ t ∈ Icc a b, PairDeficit.deficit (X t) i j ≤ PairDeficit.deficit (X a) i j *
      Real.exp (-(1 / (4 * (n : ℝ))) * (t - a) +
        10 * ∫ u in a..t, ContractionInteraction.exterior β (X u) D hD)) := by
  have hv : ∀ t ∈ Icc a b, PairDeficit.velocity model β (X t) i j ≤
      (-(1 / (4 * (n : ℝ))) + 10 * ContractionInteraction.exterior β (X t) D hD) *
        PairDeficit.deficit (X t) i j := fun t ht =>
    ContractionPointwise.velocity_le hn model β hβ ε hε0 hε1 hβε (X t) D hD
      (hdiam t ht) i j hi hj
  refine ⟨fun t ht => ⟨PairDeficit.hasDerivWithinAt_right model β X hX i j t
    (ha.trans ht.1), hv t ht⟩, ae_derivative_bound model β X hX i j ha _ hv, ?_⟩
  intro t ht
  exact ContractionDynamics.interval_gronwall hn model β hβ ε hε0 hε1 hβε X hX D hD
    ha hdiam i j hi hj ht

/-- The complete source block-contraction lemma. The constants may be chosen
as `c₀ = 1/(4n)` and `C₀ = 10`, for both models. Its second temperature
threshold depends only on the displayed scalar parameters and `n`.

The first conjunct includes the source almost-everywhere ordinary derivative
inequality and the stronger right-derivative formulation at every interval
point. The second conjunct assumes exterior separation only while the block
is within the visible diameter, and proves that confinement as a conclusion.
This is an ordinary proved source export, not a frozen graph anchor. -/
theorem block_contraction (n : ℕ) (hn : 0 < n) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∃ β₀ : ℝ, 1 < β₀ ∧
      (∀ (d : ℕ) (model : Model) (β : ℝ), β₀ ≤ β →
        ∀ (X : ℝ → Configuration n d), Solves model β X →
        ∀ (a b : ℝ), 0 ≤ a → a ≤ b →
        ∀ (D : Block n) (hD : D.Nonempty),
          (∀ t ∈ Icc a b, ∀ i ∈ D, ∀ j ∈ D,
            angularDist (X t i) (X t j) ≤ visibleScale β) →
          ∀ i ∈ D, ∀ j ∈ D,
            (∀ t ∈ Icc a b,
              HasDerivWithinAt (fun u => PairDeficit.deficit (X u) i j)
                (PairDeficit.velocity model β (X t) i j) (Ici t) t ∧
              PairDeficit.velocity model β (X t) i j ≤
                (-c₀ + C₀ * ContractionInteraction.exterior β (X t) D hD) *
                  PairDeficit.deficit (X t) i j) ∧
            (∀ᵐ t ∂volume.restrict (Icc a b),
              deriv (fun u => PairDeficit.deficit (X u) i j) t ≤
                (-c₀ + C₀ * ContractionInteraction.exterior β (X t) D hD) *
                  PairDeficit.deficit (X t) i j) ∧
            (∀ t ∈ Icc a b, PairDeficit.deficit (X t) i j ≤ PairDeficit.deficit (X a) i j *
              Real.exp (-c₀ * (t - a) +
                C₀ * ∫ u in a..t, ContractionInteraction.exterior β (X u) D hD))) ∧
      (∀ (bStar κ CStar : ℝ), 0 < bStar → 0 < κ → 8 * κ / c₀ < CStar →
        ∃ β₁ : ℝ, β₀ ≤ β₁ ∧
          ∀ (d : ℕ) (model : Model) (β : ℝ), β₁ ≤ β →
          ∀ (X : ℝ → Configuration n d), Solves model β X →
          ∀ (a : ℝ), 0 ≤ a → ∀ (D : Block n) (_hD : D.Nonempty),
            (∀ i ∈ D, ∀ j ∈ D, angularDist (X a i) (X a j) ≤ visibleScale β) →
            (∀ t ∈ Icc a (a + CStar * β),
              (∀ i ∈ D, ∀ j ∈ D, angularDist (X t i) (X t j) ≤ visibleScale β) →
              ∀ i ∈ D, ∀ k ∉ D,
                bStar ≤ 1 - Real.cos (angularDist (X t i) (X t k))) →
            (∀ t ∈ Icc a (a + CStar * β), ∀ i ∈ D, ∀ j ∈ D,
              angularDist (X t i) (X t j) ≤ visibleScale β) ∧
            (∀ i ∈ D, ∀ j ∈ D,
              angularDist (X (a + CStar * β) i) (X (a + CStar * β) j) ≤
                Real.exp (-2 * κ * β))) := by
  have hc := contraction_constant_pos n hn
  obtain ⟨β₀, hβ₀, hscale⟩ := exists_scale_threshold n hn
  refine ⟨1 / (4 * (n : ℝ)), hc, 10, by norm_num, β₀, hβ₀, ?_, ?_⟩
  · intro d model β hβ X hX a b ha _hab D hD hdiam i hi j hj
    obtain ⟨hβ1, hε0, hε1, hβε⟩ := hscale β hβ
    exact interval_estimates hn model β (by linarith only [hβ1])
      (visibleScale β) hε0.le hε1 hβε X hX D hD ha hdiam i j hi hj
  · intro bStar κ CStar hbStar hκ hCStar
    obtain ⟨B, hB⟩ := eventually_atTop.mp
      (eventually_tightening_parameters n hn bStar κ CStar hbStar hCStar)
    refine ⟨max β₀ B, le_max_left _ _, ?_⟩
    intro d model β hβ X hX a ha D hD hstart hsep
    obtain ⟨hβ1, hε0, hε1, hβε⟩ := hscale β ((le_max_left _ _).trans hβ)
    obtain ⟨hext, hfinal⟩ := hB β ((le_max_right _ _).trans hβ)
    have hβ0 : 0 ≤ β := by linarith only [hβ1]
    have hC0 : 0 < CStar := (div_pos (mul_pos (by norm_num) hκ) hc).trans hCStar
    have htime : a + CStar * β ∈ Icc a (a + CStar * β) :=
      ⟨le_add_of_nonneg_right (mul_nonneg hC0.le hβ0), le_rfl⟩
    have hsep' : ∀ t ∈ Icc a (a + CStar * β),
        (∀ i ∈ D, ∀ j ∈ D, angularDist (X t i) (X t j) ≤ visibleScale β) →
        ∀ i ∈ D, ∀ k ∉ D, bStar ≤ PairDeficit.deficit (X t) i k := by
      simpa only [PairDeficit.deficit, AngularGeometry.cos_angularDist] using hsep
    have hdecay := ContractionDynamics.confinement_and_decay hn model β hβ0
      (visibleScale β) hε0 hε1 hβε bStar hext X hX D hD ha hstart hsep'
    refine ⟨fun t ht => (hdecay t ht).1, ?_⟩
    intro i hi j hj
    have hangle := (hdecay _ htime).1 i hi j hj
    have hq := (hdecay _ htime).2 i hi j hj
    have hinit := ContractionScale.deficit_le_half_sq_of_angularDist_le
      (X a) i j (visibleScale β) (hstart i hi j hj)
    have hanglesq := ContractionScale.angularDist_sq_le_four_mul_deficit
      (X (a + CStar * β)) i j (hangle.trans hε1)
    have hexponent : -(1 / (4 * (n : ℝ)) / 2) * (a + CStar * β - a) =
        -(1 / (4 * (n : ℝ))) * CStar * β / 2 := by ring
    rw [hexponent] at hq
    have hmul := mul_le_mul_of_nonneg_right hinit
      (Real.exp_pos (-(1 / (4 * (n : ℝ))) * CStar * β / 2)).le
    have hsq : angularDist (X (a + CStar * β) i) (X (a + CStar * β) j) ^ 2 ≤
        Real.exp (-4 * κ * β) := by
      nlinarith only [hanglesq, hq, hmul, hfinal]
    have hexp : Real.exp (-2 * κ * β) ^ 2 = Real.exp (-4 * κ * β) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    nlinarith only [hsq, hexp, Real.exp_pos (-2 * κ * β),
      AngularGeometry.angularDist_nonneg (X (a + CStar * β) i) (X (a + CStar * β) j)]

end Metastability.BlockContraction
