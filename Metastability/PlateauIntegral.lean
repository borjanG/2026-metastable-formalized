import Metastability.PlateauInteraction
import Metastability.PlateauScalar
import Metastability.PlateauClockSubstitution

/-!
# Uniform exterior integral on a stopped active plateau

The constant is chosen before kappa. The original-time integral is obtained
from the actual cutoff clock and the source scalar law, rather than assumed.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

namespace Metastability.PlateauIntegral
open Source ActiveScales ActiveVelocity ActiveSourceLaw CapEnlargement
open ContractionInteraction PlateauScalar
variable {n N d : ℕ}

/-- A dimension-independent constant for the source exterior integral. -/
def diameterConstant (n : ℕ) : ℝ := 128 * ((n : ℝ) + 1) ^ 2

theorem diameterConstant_pos (n : ℕ) : 0 < diameterConstant n := by
  unfold diameterConstant
  positivity

theorem eventually_residual_le_one (n : ℕ) (Δ : ℝ) (hΔ : 0 < Δ) :
    ∀ᶠ β : ℝ in atTop,
      2 * n * (1 + β) * Real.log β * Real.exp (-5 * Δ * β) ≤ 1 := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_mul_exp_le_rpow (4 * n) (5 * Δ) 2 0 (by positivity)] with β hβ hs
  rw [Real.rpow_ofNat, Real.rpow_zero] at hs
  have hβ0 : 0 ≤ β := by linarith only [hβ]
  have hlog0 := (Real.log_pos hβ).le
  have hlog := Real.log_le_self hβ0
  have h1 : 1 + β ≤ 2 * β := by linarith only [hβ]
  calc
    _ ≤ 2 * n * (2 * β) * β * Real.exp (-5 * Δ * β) := by
      gcongr
    _ = (4 * n) * β ^ 2 * Real.exp (-(5 * Δ) * β) := by
      rw [show -(5 * Δ) * β = -5 * Δ * β by ring]
      ring
    _ ≤ 1 := hs

/-- Uniform integral bound for every current block on a stopped stage interval.
The allowed interval length also covers the preliminary horizon used to produce
the active first hit. -/
theorem exterior_integral_bound (T : CollisionTree n N) (hN : 0 < N) (C : TreeCaps T d)
    (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 4 < κ) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5), ∀ (model : Model) (l : Fin N)
      (X : ℝ → Configuration n d), Solves model β X →
      ∀ shift : ℝ, 0 ≤ shift → ∀ clock : ℝ → ℝ, ClockRelation β X shift clock →
      ∀ i j : Fin n, i ∈ T.left l → j ∈ T.right l →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a ≤ 2 * ((n : ℝ) + 1) →
      (∀ t ∈ Icc a b, StageHyp T C β κ M l (accelerated X shift clock t)) →
      (∀ t ∈ Icc a b, 1 - correlation X shift clock i j t ≤
        upperBarrier C l + 2 * treeMargin hN C) →
      (∀ t ∈ Icc a b, mesoscopicScale β ≤
        angularDist (accelerated X shift clock t i) (accelerated X shift clock t j)) →
      ∀ (D : Block n) (hD : D ∈ T.partition l.castSucc),
        (∫ u in (shift + clock a)..(shift + clock b),
          exterior β (X u) D (T.block_nonempty _ _ hD)) ≤ diameterConstant n * β := by
  obtain ⟨B, hB, hpoint⟩ := PlateauInteraction.source_weighted_exterior T hN C hC κ
    (by linarith only [hκ])
  obtain ⟨S, hS, hscalar⟩ := interval_bounds T hN C hC κ hκ
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    (eventually_residual_le_one n (treeMargin hN C) (treeMargin_pos hN C hC))
  refine ⟨max B (max S R), hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ M hM model l X hX shift hshift clock hc i j hi hj a b ha hab hlen hstage hupper hangle D hD
  have hβB : B ≤ β := (le_max_left _ _).trans hβ
  have hβS : S ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβR : R ≤ β := (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  have hβ1 := hB.trans_le hβB
  have hβ0 : 0 ≤ β := by linarith only [hβ1]
  obtain ⟨_, _, _, hw, _, _, hiw⟩ := hscalar β hβS M hM model l X hX shift hshift clock hc
    i j hi hj a b ha hab hstage hupper hangle
  obtain ⟨_, hf, heq⟩ := PlateauClockSubstitution.integral_substitution model β hβ1
    X hX shift hshift clock hc a b ha hab
    (fun u => exterior β (X u) D (T.block_nonempty _ _ hD))
    (continuousOn_exterior_of_solves model β X hX D (T.block_nonempty _ _ hD))
  rw [heq]
  have hconst : IntervalIntegrable (fun _ : ℝ => 8 * n * Real.log β) volume a b := intervalIntegrable_const
  have hone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume a b := intervalIntegrable_const
  have hmajor : IntervalIntegrable
      (fun t => 8 * n * Real.log β + 8 * n * (β * activeWeight β X shift clock i j t) + 1)
      volume a b := (hconst.add (hw.const_mul (8 * n))).add hone
  have hint := intervalIntegral.integral_mono_on hab hf hmajor (fun t ht => by
    have hp := hpoint β hβB M hM l (accelerated X shift clock t) (hstage t ht)
      i j hi hj (hupper t ht) (hangle t ht) D hD
    have hr := hR β hβR
    change exterior β (accelerated X shift clock t) D _ * clockFactor β (accelerated X shift clock t) ≤ _
    dsimp only [activeWeight]
    nlinarith only [hp, hr])
  have hrate := TreeDynamics.stageRate_pos T model l
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (TreeDynamics.particle_pos T)
  have hr : 4 / stageRate model T l ≤ 4 * n := by
    have hl := (stageRate_bounds model T l).1
    have hl' : 1 ≤ stageRate model T l * n := (div_le_iff₀ hn).mp hl
    apply (div_le_iff₀ hrate).mpr
    nlinarith only [hl']
  have hiw' : (∫ t in a..b, β * activeWeight β X shift clock i j t) ≤ 4 * n * β :=
    hiw.trans (mul_le_mul_of_nonneg_right hr hβ0)
  have hieq : (∫ t in a..b,
      8 * n * Real.log β + 8 * n * (β * activeWeight β X shift clock i j t) + 1) =
      (b - a) * (8 * n * Real.log β) +
        8 * n * (∫ t in a..b, β * activeWeight β X shift clock i j t) + (b - a) := by
    rw [intervalIntegral.integral_add (hconst.add (hw.const_mul (8 * n))) hone,
      intervalIntegral.integral_add hconst (hw.const_mul (8 * n)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, intervalIntegral.integral_const]
    rw [intervalIntegral.integral_const_mul]
    simp only [smul_eq_mul, mul_one]
    ring
  rw [hieq] at hint
  have hfirst : (b - a) * (8 * n * Real.log β) ≤ 16 * n * (n + 1) * β := by
    calc
      _ ≤ (2 * (n + 1)) * (8 * n * β) := by
        gcongr
        · exact mul_nonneg (by positivity) (Real.log_pos hβ1).le
        · exact Real.log_le_self hβ0
      _ = _ := by ring
  have hlast : b - a ≤ 2 * (n + 1) * β :=
    hlen.trans (le_mul_of_one_le_right (by positivity) hβ1.le)
  have hmiddle := mul_le_mul_of_nonneg_left hiw' (show 0 ≤ 8 * (n : ℝ) by positivity)
  have hconstant : 16 * n * (n + 1) + 32 * n ^ 2 + 2 * (n + 1) ≤ diameterConstant n := by
    unfold diameterConstant
    nlinarith only [sq_nonneg (n : ℝ), hn]
  have hfinish := mul_le_mul_of_nonneg_right hconstant hβ0
  nlinarith only [hint, hfirst, hmiddle, hlast, hfinish]

end Metastability.PlateauIntegral
