import Metastability.CompletionInteraction
import Metastability.PlateauIntegral

/-! The original-time exterior integral stays within the same n-only bound
through the whole uncompleted collision stage. Completion is allowed at the
right endpoint. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace
namespace Metastability.CompletionIntegral
open Source ActiveScales ActiveVelocity ActiveSourceLaw CapEnlargement
open ContractionInteraction PlateauScalar PlateauIntegral
variable {n N d : ℕ}

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
      (∀ t ∈ Ico a b, ¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
        angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ≤ clockCutoff β) →
      ∀ (D : Block n) (hD : D ∈ T.partition l.castSucc),
        (∫ u in (shift + clock a)..(shift + clock b),
          exterior β (X u) D (T.block_nonempty _ _ hD)) ≤ diameterConstant n * β := by
  obtain ⟨B, hB, hpoint⟩ := CompletionInteraction.source_weighted_exterior T hN C hC κ hκ
  obtain ⟨S, hS, hscalar⟩ := CompletionScalar.interval_bounds T hN C hC κ hκ
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    (eventually_residual_le_one n (treeMargin hN C) (treeMargin_pos hN C hC))
  refine ⟨max B (max S R), hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ M hM model l X hX shift hshift clock hc i j hi hj a b ha hab hlen hstage hupper hnoncomplete D hD
  have hβB : B ≤ β := (le_max_left _ _).trans hβ
  have hβS : S ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβR : R ≤ β := (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  have hβ1 := hB.trans_le hβB
  have hβ0 : 0 ≤ β := by linarith only [hβ1]
  obtain ⟨_, _, _, hw, _, _, hiw⟩ := hscalar β hβS M hM model l X hX shift hshift clock hc
    i j hi hj a b ha hab hstage hupper hnoncomplete
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
  have hint := intervalIntegral.integral_mono_on_of_le_Ioo hab hf hmajor (fun t ht => by
    have hp := hpoint β hβB M hM l (accelerated X shift clock t) (hstage t ⟨ht.1.le, ht.2.le⟩)
      i j hi hj (hupper t ⟨ht.1.le, ht.2.le⟩) (hnoncomplete t ⟨ht.1.le, ht.2⟩) D hD
    have hr := hR β hβR
    change exterior β (accelerated X shift clock t) D _ * clockFactor β (accelerated X shift clock t) ≤ _
    dsimp only [activeWeight]
    nlinarith only [hp, hr])
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (TreeDynamics.particle_pos T)
  have hiw' : (∫ t in a..b, β * activeWeight β X shift clock i j t) ≤ 8 * n * β := hiw
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
  have hconstant : 16 * n * (n + 1) + 64 * n ^ 2 + 2 * (n + 1) ≤ diameterConstant n := by
    unfold diameterConstant
    nlinarith only [sq_nonneg (n : ℝ), hn]
  have hfinish := mul_le_mul_of_nonneg_right hconstant hβ0
  nlinarith only [hint, hfirst, hmiddle, hlast, hfinish]


end Metastability.CompletionIntegral
