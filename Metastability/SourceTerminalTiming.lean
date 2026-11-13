import Metastability.TerminalTrajectory

/-!
# Source terminal completion time

The source ODE, literal inverse clock, and H1/H2/H3 before completion imply
an actual first completed parent in a finite accelerated-time horizon. Neither
an existing hitting time nor continued terminal confinement is assumed.
-/
noncomputable section
open Filter Set MeasureTheory
open scoped Topology RealInnerProductSpace
namespace Metastability.SourceTerminalTiming
open Source ActiveScales ActiveVelocity ActiveTimingScales CapEnlargement
variable {n N d : ℕ}

/-- The literal finite collection of parent angular constraints is closed.
Consequently, nonempty finite-horizon completion has a first time. -/
theorem exists_first_parent_completion (D : Block n) (β : ℝ)
    (Y : ℝ → Configuration n d) (a b : ℝ)
    (hc : ∀ p q, ContinuousOn (fun t => angularDist (Y t p) (Y t q)) (Icc a b))
    (hstart : ¬ ∀ p ∈ D, ∀ q ∈ D, angularDist (Y a p) (Y a q) ≤ clockCutoff β)
    (hex : ∃ t ∈ Icc a b, ∀ p ∈ D, ∀ q ∈ D, angularDist (Y t p) (Y t q) ≤ clockCutoff β) :
    ∃ U ∈ Ioc a b,
      (∀ p ∈ D, ∀ q ∈ D, angularDist (Y U p) (Y U q) ≤ clockCutoff β) ∧
      ∀ t ∈ Ico a U, ¬ ∀ p ∈ D, ∀ q ∈ D, angularDist (Y t p) (Y t q) ≤ clockCutoff β := by
  let Z : Set ℝ := Icc a b ∩ {t | ∀ p ∈ D, ∀ q ∈ D, angularDist (Y t p) (Y t q) ≤ clockCutoff β}
  have hZeq : Z = Icc a b ∩ ⋂ p ∈ D, ⋂ q ∈ D,
      (Icc a b ∩ {t | angularDist (Y t p) (Y t q) ≤ clockCutoff β}) := by
    ext t
    simp only [Z, mem_inter_iff, mem_iInter, mem_setOf_eq]
    constructor
    · intro h
      exact ⟨h.1, fun p hp q hq => ⟨h.1, h.2 p hp q hq⟩⟩
    · intro h
      exact ⟨h.1, fun p hp q hq => (h.2 p hp q hq).2⟩
  have hZ : IsClosed Z := by
    rw [hZeq]
    apply isClosed_Icc.inter
    exact isClosed_iInter fun p => isClosed_iInter fun _ =>
      isClosed_iInter fun q => isClosed_iInter fun _ =>
        (hc p q).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hZne : Z.Nonempty := by
    obtain ⟨t, ht, hcomplete⟩ := hex
    exact ⟨t, ht, hcomplete⟩
  obtain ⟨U, hU⟩ := (isCompact_Icc.of_isClosed_subset hZ inter_subset_left).exists_isLeast hZne
  have hUa : a < U := by
    apply lt_of_le_of_ne hU.1.1.1
    intro heq
    have hh := hU.1.2
    rw [← heq] at hh
    exact hstart hh
  refine ⟨U, ⟨hUa, hU.1.1.2⟩, hU.1.2, ?_⟩
  intro t ht hcomplete
  exact (not_le.mpr ht.2) (hU.2 ⟨⟨ht.1, ht.2.le.trans hU.1.1.2⟩, hcomplete⟩)

/-- Uniform source terminal-window bound. The constant is `20*n`; beta is
chosen before the model, clock, time interval, stage, and representatives.
H1/H2/H3 are required only as long as the parent has not completed. -/
theorem terminal_completion (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 0 < κ) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5), ∀ (l : Fin N) (model : Model)
      (X : ℝ → Configuration n d), Solves model β X →
      ∀ (shift : ℝ), 0 ≤ shift → ∀ (clock : ℝ → ℝ), ClockRelation β X shift clock →
      ∀ (a : ℝ), 0 ≤ a → ∀ (i j : Fin n), i ∈ T.left l → j ∈ T.right l →
      angularDist (accelerated X shift clock a i) (accelerated X shift clock a j) = mesoscopicScale β →
      (∀ t ∈ Icc a (a + 20 * n * (Real.log (Real.log β) / Real.log β)),
        (∀ u ∈ Icc a t, ¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
          angularDist (accelerated X shift clock u p) (accelerated X shift clock u q) ≤ clockCutoff β) →
        (∀ D ∈ T.partition l.castSucc, ∀ p ∈ D, ∀ q ∈ D,
          angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ≤ Real.exp (-κ * β)) ∧
        (∀ (D : Block n) (hD : D ∈ T.partition l.castSucc), D ≠ T.left l → D ≠ T.right l →
          ∀ p ∈ D, angularDist (accelerated X shift clock t p) (C (T.currentNode l D hD)).center ≤
            (C (T.currentNode l D hD)).radius + M * enlargementScale β) ∧
        (∀ hp : T.parent l ≠ Finset.univ, ∀ p ∈ T.parent l,
          angularDist (accelerated X shift clock t p) (C (T.parentNode l hp)).center ≤
            (C (T.parentNode l hp)).radius + M * enlargementScale β)) →
      ∃ U ∈ Ioc a (a + 20 * n * (Real.log (Real.log β) / Real.log β)),
        (∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
          angularDist (accelerated X shift clock U p) (accelerated X shift clock U q) ≤ clockCutoff β) ∧
        (∀ t ∈ Ico a U, ¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
          angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ≤ clockCutoff β) ∧
        (∀ t ∈ Ico a U,
          angularDist (accelerated X shift clock t i) (accelerated X shift clock t j) ≤ mesoscopicScale β) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast TreeDynamics.particle_pos T
  obtain ⟨V, hV, hstatic⟩ := SourceTerminalEstimates.source_terminal_estimates T hN C hC κ hκ
  obtain ⟨S, hS⟩ := eventually_atTop.mp (show ∀ᶠ β : ℝ in atTop,
      1 ≤ Real.log β ∧ 1 ≤ Real.log (Real.log β) ∧
        angleLog (mesoscopicScale β) - angleLog (clockCutoff β / 2) ≤ 5 * Real.log (Real.log β) by
    filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually (eventually_ge_atTop (1 : ℝ)),
      eventually_terminal_log_gap] with β hlog hloglog hgap
    exact ⟨hlog, hloglog, hgap.2⟩)
  refine ⟨max V S, hV.trans_le (le_max_left _ _), ?_⟩
  intro β hβ M hM l model X hX shift hshift clock hc a ha i j hi hj hstart hgeometry
  have hβ1 : 1 < β := hV.trans_le ((le_max_left _ _).trans hβ)
  have hlog := Real.log_pos hβ1
  obtain ⟨hsmall, _, hpoint⟩ := hstatic β ((le_max_left _ _).trans hβ)
  obtain ⟨hlog1, hloglog, hgap⟩ := hS β ((le_max_right _ _).trans hβ)
  let b := a + 20 * n * (Real.log (Real.log β) / Real.log β)
  let Y := accelerated X shift clock
  have hab : a ≤ b := by
    dsimp only [b]
    apply le_add_of_nonneg_right
    have hh : 0 ≤ Real.log (Real.log β) := by linarith only [hloglog]
    positivity
  have hmesocut : clockCutoff β < mesoscopicScale β := by
    rw [mesoscopicScale_eq_log_mul_visible hβ1]
    have hv := ContractionScale.visibleScale_pos hβ1
    have hh := mul_le_mul_of_nonneg_right hlog1 hv.le
    change visibleScale β / 4 < _
    linarith only [hh, hv]
  have hnotstart : ¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
      angularDist (Y a p) (Y a q) ≤ clockCutoff β := by
    intro hh
    have hij := hh i (Finset.mem_union_left _ hi) j (Finset.mem_union_right _ hj)
    rw [hstart] at hij
    exact (not_le.mpr hmesocut) hij
  have hpoint' : ∀ t ∈ Icc a b,
      (∀ u ∈ Icc a t, ¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l, angularDist (Y u p) (Y u q) ≤ clockCutoff β) →
      angularDist (Y t i) (Y t j) ≤ 2 * mesoscopicScale β →
      clockCutoff β / 2 < angularDist (Y t i) (Y t j) ∧
      0 < -PairDeficit.velocity model β (Y t) i j ∧
      (angularDist (Y t i) (Y t j) ≤ mesoscopicScale β →
        Real.log β / (4 * n) * sineSquare (Y t) i j ≤
          (-PairDeficit.velocity model β (Y t) i j) * clockFactor β (Y t)) := by
    intro t ht hprefix hangle
    obtain ⟨htight, hother, hparent⟩ := hgeometry t ht hprefix
    exact hpoint M hM l model (Y t) htight hother hparent i j hi hj
      (hprefix t ⟨ht.1, le_rfl⟩) hangle
  have hex : ∃ t ∈ Icc a b,
      ∀ p ∈ T.parent l, ∀ q ∈ T.parent l, angularDist (Y t p) (Y t q) ≤ clockCutoff β := by
    by_contra hno
    have hnc : ∀ t ∈ Icc a b, ¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
        angularDist (Y t p) (Y t q) ≤ clockCutoff β := by
      intro t ht hh
      exact hno ⟨t, ht, hh⟩
    apply TerminalTrajectory.impossible_terminal_interval model β hβ1 X hX shift hshift clock hc
      i j a b ha hab hsmall hstart (fun t ht => hpoint' t ht (fun u hu => hnc u ⟨hu.1, hu.2.trans ht.2⟩))
    have hbudget : (Real.log β / (4 * n)) * (b - a) = 5 * Real.log (Real.log β) := by
      dsimp only [b]
      field_simp
      ring
    rwa [hbudget]
  have hcont : ∀ p q, ContinuousOn (fun t => angularDist (Y t p) (Y t q)) (Icc a b) := by
    intro p q
    exact Real.continuous_arccos.comp_continuousOn
      (((ActiveTrajectory.accelerated_correlation_lipschitz model β hβ1 X hX shift hshift clock hc p q).mono
        (show Icc a b ⊆ Ici (0 : ℝ) from fun _ ht => ha.trans ht.1)).continuousOn)
  obtain ⟨U, hU, hcomplete, hbefore⟩ := exists_first_parent_completion (T.parent l) β Y a b hcont hnotstart hex
  refine ⟨U, hU, hcomplete, hbefore, ?_⟩
  intro t ht
  apply TerminalTrajectory.no_upward_exit model β hβ1 X hX shift hshift clock hc i j a t ha ht.1 hsmall hstart
    (fun s hs hangle => (hpoint' s ⟨hs.1.le, hs.2.le.trans (ht.2.le.trans hU.2)⟩
      (fun u hu => hbefore u ⟨hu.1, hu.2.trans_lt (hs.2.trans ht.2)⟩) hangle).2.1) t ⟨ht.1, le_rfl⟩

/-- The same bound applies to every truncated interval before completion,
without assuming that a first completion time has already been constructed. -/
theorem terminal_duration_before_completion (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 0 < κ) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5), ∀ (l : Fin N) (model : Model)
      (X : ℝ → Configuration n d), Solves model β X →
      ∀ (shift : ℝ), 0 ≤ shift → ∀ (clock : ℝ → ℝ), ClockRelation β X shift clock →
      ∀ (a : ℝ), 0 ≤ a → ∀ (i j : Fin n), i ∈ T.left l → j ∈ T.right l →
      angularDist (accelerated X shift clock a i) (accelerated X shift clock a j) = mesoscopicScale β →
      ∀ b ≥ a,
      (∀ t ∈ Ico a b,
        (¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
          angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ≤ clockCutoff β) ∧
        (∀ D ∈ T.partition l.castSucc, ∀ p ∈ D, ∀ q ∈ D,
          angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ≤ Real.exp (-κ * β)) ∧
        (∀ (D : Block n) (hD : D ∈ T.partition l.castSucc), D ≠ T.left l → D ≠ T.right l →
          ∀ p ∈ D, angularDist (accelerated X shift clock t p) (C (T.currentNode l D hD)).center ≤
            (C (T.currentNode l D hD)).radius + M * enlargementScale β) ∧
        (∀ hp : T.parent l ≠ Finset.univ, ∀ p ∈ T.parent l,
          angularDist (accelerated X shift clock t p) (C (T.parentNode l hp)).center ≤
            (C (T.parentNode l hp)).radius + M * enlargementScale β)) →
      b - a ≤ 20 * n * (Real.log (Real.log β) / Real.log β) := by
  obtain ⟨β₀, hβ₀, hcomplete⟩ := terminal_completion T hN C hC κ hκ
  refine ⟨β₀, hβ₀, ?_⟩
  intro β hβ M hM l model X hX shift hshift clock hc a ha i j hi hj hstart b _hab hbefore
  by_contra hnot
  have hH : a + 20 * n * (Real.log (Real.log β) / Real.log β) < b := by
    linarith only [lt_of_not_ge hnot]
  obtain ⟨U, hU, hdone, _⟩ := hcomplete β hβ M hM l model X hX shift hshift clock hc
    a ha i j hi hj hstart (by
      intro t ht _hprefix
      exact (hbefore t ⟨ht.1, ht.2.trans_lt hH⟩).2)
  exact (hbefore U ⟨hU.1.le, hU.2.trans_lt hH⟩).1 hdone

end Metastability.SourceTerminalTiming
