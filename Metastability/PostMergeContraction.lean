import Metastability.BlockContraction
import Metastability.PostMergeClock

/-!
# Post-merge tightening at the literal clock cutoff

Both attention models preserve cutoff confinement, including equality at
entry, while separated blocks tighten exponentially. The next accelerated
time is produced from the actual inverse clock. Separation is the explicit
conditional hypothesis of the source post-merge corollary.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

namespace Metastability.PostMergeContraction
open Source

/-- One admissible original-time multiplier, chosen only from n and kappa. -/
def tighteningConstant (n : ℕ) (κ : ℝ) : ℝ := 64 * n * (κ + 1)

theorem tighteningConstant_pos (n : ℕ) (hn : 0 < n) (κ : ℝ) (hκ : 0 < κ) :
    0 < tighteningConstant n κ := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  unfold tighteningConstant
  positivity

theorem tighteningConstant_margin (n : ℕ) (hn : 0 < n) (κ : ℝ) (hκ : 0 < κ) :
    8 * κ / (1 / (4 * (n : ℝ))) < tighteningConstant n κ := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  simp only [one_div, div_inv_eq_mul]
  unfold tighteningConstant
  nlinarith only [hnR, mul_pos hnR hκ]

/-- Numeric low-temperature conditions, including the exact quarter-scale
cutoff. They are derived before the geometry or solution is chosen. -/
theorem eventually_parameters (n : ℕ) (hn : 0 < n) (b κ CStar : ℝ)
    (hb : 0 < b) (hC : 8 * κ / (1 / (4 * (n : ℝ))) < CStar) :
    ∀ᶠ β : ℝ in atTop,
      1 < β ∧ 0 < clockCutoff β ∧ clockCutoff β ≤ 1 ∧
      β * clockCutoff β ^ 2 ≤ 1 / (40 * (n : ℝ) ^ 2) ∧
      clockCutoff β < b ∧
      10 * ((n : ℝ) * (1 + β) * Real.exp (-β * b)) ≤ (1 / (4 * (n : ℝ))) / 2 ∧
      2 * visibleScale β ^ 2 * Real.exp (-(1 / (4 * (n : ℝ))) * CStar * β / 2) ≤
        Real.exp (-4 * κ * β) := by
  filter_upwards [ContractionScale.eventually_visibleScale_small n hn,
    BlockContraction.eventually_tightening_parameters n hn b κ CStar hb hC,
    ContractionScale.tendsto_visibleScale.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 4 * b))]
    with β hscale htight hsmall
  obtain ⟨hβ, hε, hε1, hβε⟩ := hscale
  have hcut0 : 0 < clockCutoff β := div_pos hε (by norm_num)
  have hcut : clockCutoff β ≤ visibleScale β := by unfold clockCutoff; linarith only [hε]
  have hsquare := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hcut0.le hcut 2)
    (zero_lt_one.trans hβ).le
  refine ⟨hβ, hcut0, hcut.trans hε1, hsquare.trans hβε, ?_, htight⟩
  unfold clockCutoff
  linarith only [hsmall]

/-- Original-time cutoff confinement and tightening from the literal vector
field. The conditional separation assumption is used even at the endpoints;
no confinement or derivative estimate is assumed. -/
theorem cutoff_confinement_and_tightening (n : ℕ) (hn : 0 < n)
    (b κ CStar : ℝ) (hb : 0 < b) (hκ : 0 < κ)
    (hC : 8 * κ / (1 / (4 * (n : ℝ))) < CStar) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀, ∀ (d : ℕ) (model : Model)
      (X : ℝ → Configuration n d), Solves model β X →
      ∀ a : ℝ, 0 ≤ a → ∀ (D : Block n) (_hD : D.Nonempty),
      (∀ i ∈ D, ∀ j ∈ D, angularDist (X a i) (X a j) ≤ clockCutoff β) →
      (∀ u ∈ Icc a (a + CStar * β), ∀ i ∈ D, ∀ j ∉ D,
        b ≤ 1 - ⟪(X u i).val, (X u j).val⟫) →
      (∀ u ∈ Icc a (a + CStar * β), ∀ i ∈ D, ∀ j ∈ D,
        angularDist (X u i) (X u j) ≤ clockCutoff β) ∧
      (∀ i ∈ D, ∀ j ∈ D,
        angularDist (X (a + CStar * β) i) (X (a + CStar * β) j) ≤
          Real.exp (-2 * κ * β)) := by
  obtain ⟨B, hB⟩ := eventually_atTop.mp (eventually_parameters n hn b κ CStar hb hC)
  refine ⟨max B 2, lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro β hβ d model X hX a ha D hD hstart hsep
  obtain ⟨hβ1, hcut0, hcut1, hβcut, _, hext, hfinal⟩ := hB β ((le_max_left _ _).trans hβ)
  have hβ0 : 0 ≤ β := (zero_lt_one.trans hβ1).le
  have hc := BlockContraction.contraction_constant_pos n hn
  have hC0 : 0 < CStar := (div_pos (mul_pos (by norm_num) hκ) hc).trans hC
  have htime : a + CStar * β ∈ Icc a (a + CStar * β) :=
    ⟨le_add_of_nonneg_right (mul_nonneg hC0.le hβ0), le_rfl⟩
  have hdecay := ContractionDynamics.confinement_and_decay hn model β hβ0
    (clockCutoff β) hcut0 hcut1 hβcut b hext X hX D hD ha hstart
    (fun u hu _ i hi j hj => hsep u hu i hi j hj)
  refine ⟨fun u hu => (hdecay u hu).1, ?_⟩
  intro i hi j hj
  have hangle := (hdecay _ htime).1 i hi j hj
  have hq := (hdecay _ htime).2 i hi j hj
  have hvisible : clockCutoff β ≤ visibleScale β := by
    unfold clockCutoff
    linarith only [ContractionScale.visibleScale_pos hβ1]
  have hinit := ContractionScale.deficit_le_half_sq_of_angularDist_le (X a) i j
    (visibleScale β) ((hstart i hi j hj).trans hvisible)
  have hanglesq := ContractionScale.angularDist_sq_le_four_mul_deficit
    (X (a + CStar * β)) i j (hangle.trans hcut1)
  rw [show -(1 / (4 * (n : ℝ)) / 2) * (a + CStar * β - a) =
    -(1 / (4 * (n : ℝ))) * CStar * β / 2 by ring] at hq
  have hmul := mul_le_mul_of_nonneg_right hinit
    (Real.exp_pos (-(1 / (4 * (n : ℝ))) * CStar * β / 2)).le
  have hsq : angularDist (X (a + CStar * β) i) (X (a + CStar * β) j) ^ 2 ≤
      Real.exp (-4 * κ * β) := by nlinarith only [hanglesq, hq, hmul, hfinal]
  have hexp : Real.exp (-2 * κ * β) ^ 2 = Real.exp (-4 * κ * β) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  nlinarith only [hsq, hexp, Real.exp_pos (-2 * κ * β),
    AngularGeometry.angularDist_nonneg (X (a + CStar * β) i) (X (a + CStar * β) j)]

/-- The complete conditional post-merge corollary for both source models.
A nonterminal current partition supplies at least two blocks. The exact next
accelerated time, cutoff confinement, exponential tightness, and quantitative
duration are all conclusions. The threshold precedes dimension, tree,
stage, model, trajectory, shift, clock, and entry time. -/
theorem post_merge_tightening (n : ℕ) (hn : 0 < n) (b κ CStar : ℝ)
    (hb : 0 < b) (hκ : 0 < κ)
    (hC : 8 * κ / (1 / (4 * (n : ℝ))) < CStar) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀, ∀ (N d : ℕ) (T : CollisionTree n N)
      (k : Fin N) (model : Model) (X : ℝ → Configuration n d), Solves model β X →
      ∀ shift : ℝ, 0 ≤ shift → ∀ clock : ℝ → ℝ, ClockRelation β X shift clock →
      ∀ t₀ : ℝ, 0 ≤ t₀ →
      (∀ D ∈ T.partition k.castSucc, ∀ i ∈ D, ∀ j ∈ D,
        angularDist (accelerated X shift clock t₀ i) (accelerated X shift clock t₀ j) ≤ clockCutoff β) →
      (∀ u ∈ Icc (shift + clock t₀) (shift + clock t₀ + CStar * β),
        ∀ D ∈ T.partition k.castSucc, ∀ i ∈ D, ∀ j ∉ D,
          b ≤ 1 - ⟪(X u i).val, (X u j).val⟫) →
      (∀ u ∈ Icc (shift + clock t₀) (shift + clock t₀ + CStar * β),
        ∀ D ∈ T.partition k.castSucc, ∀ i ∈ D, ∀ j ∈ D,
          angularDist (X u i) (X u j) ≤ clockCutoff β) ∧
      ∃ t₁ : ℝ, t₀ ≤ t₁ ∧
        t₁ = originalClockTime β X shift (clock t₀ + CStar * β) ∧
        clock t₁ = clock t₀ + CStar * β ∧
        t₁ - t₀ ≤ CStar * β / Real.log β * Real.exp (-β * b) ∧
        t₁ - t₀ ≤ Real.log (Real.log β) / Real.log β ∧
        ∀ D ∈ T.partition k.castSucc, ∀ i ∈ D, ∀ j ∈ D,
          angularDist (accelerated X shift clock t₁ i) (accelerated X shift clock t₁ j) ≤
            Real.exp (-2 * κ * β) := by
  obtain ⟨B, hB, hcontract⟩ := cutoff_confinement_and_tightening n hn b κ CStar hb hκ hC
  obtain ⟨S, hS⟩ := eventually_atTop.mp
    ((eventually_parameters n hn b κ CStar hb hC).and
      (PostMergeClock.eventually_duration_le_logRatio CStar b hb))
  refine ⟨max B S, hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ N d T k model X hX shift hshift clock hc t₀ ht₀ hentry hsep
  have hβB := (le_max_left _ _).trans hβ
  obtain ⟨⟨hβ1, _, _, _, hcut, _, _⟩, hratio⟩ := hS β ((le_max_right _ _).trans hβ)
  have hc0 := BlockContraction.contraction_constant_pos n hn
  have hC0 : 0 < CStar := (div_pos (mul_pos (by norm_num) hκ) hc0).trans hC
  have htime : 0 ≤ CStar * β := mul_nonneg hC0.le (zero_lt_one.trans hβ1).le
  have hτ0 : 0 ≤ shift + clock t₀ := add_nonneg hshift (hc.1.2.1 t₀ ht₀)
  have hblocks : ∀ (D : Block n) (hD : D ∈ T.partition k.castSucc),
      (∀ u ∈ Icc (shift + clock t₀) (shift + clock t₀ + CStar * β), ∀ i ∈ D, ∀ j ∈ D,
        angularDist (X u i) (X u j) ≤ clockCutoff β) ∧
      (∀ i ∈ D, ∀ j ∈ D,
        angularDist (X (shift + clock t₀ + CStar * β) i)
          (X (shift + clock t₀ + CStar * β) j) ≤ Real.exp (-2 * κ * β)) := by
    intro D hD
    exact hcontract β hβB d model X hX (shift + clock t₀) hτ0 D
      (T.block_nonempty _ _ hD) (hentry D hD) (fun u hu => hsep u hu D hD)
  have hconf : ∀ u ∈ Icc (shift + clock t₀) (shift + clock t₀ + CStar * β),
      ∀ D ∈ T.partition k.castSucc, ∀ i ∈ D, ∀ j ∈ D,
        angularDist (X u i) (X u j) ≤ clockCutoff β :=
    fun u hu D hD => (hblocks D hD).1 u hu
  obtain ⟨t₁, hle, hdef, heq, hlength⟩ := PostMergeClock.exists_next_time model β hβ1
    X hX shift hshift clock hc t₀ (CStar * β) b ht₀ htime
    (fun u hu => PostMergeClock.clockFactor_lower T k β b hβ1 hcut (X u)
      (hconf u hu) (hsep u hu))
  refine ⟨hconf, t₁, hle, hdef, heq, hlength, hlength.trans hratio, ?_⟩
  intro D hD i hi j hj
  dsimp only [accelerated]
  rw [heq, ← add_assoc]
  exact (hblocks D hD).2 i hi j hj

end Metastability.PostMergeContraction
