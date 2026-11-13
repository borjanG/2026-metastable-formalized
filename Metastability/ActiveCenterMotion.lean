import Metastability.ActiveParticleTrajectory
import Metastability.PostMergeCenter

/-! Inactive motion and terminal confinement from actual source dynamics. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace NNReal
namespace Metastability.ActiveCenterMotion
open Source ActiveScales ActiveCoefficients ActiveSourceLaw CapEnlargement
variable {n N d : ℕ}

/-- Clock multiplication of an explicit finite-sum geometric remainder. -/
theorem scaled_geometric_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (β κ U L F : ℝ) (v : E) (hF : 0 ≤ F)
    (hFU : F ≤ 2 * Real.log β * Real.exp (β * U))
    (hv : ‖v‖ ≤ 2 * Real.exp (-κ * β) + 2 * n * Real.exp (-β * L)) :
    ‖F • v‖ ≤ 4 * Real.log β *
      (Real.exp (-(κ - U) * β) + n * Real.exp (-(L - U) * β)) := by
  have hh := mul_le_mul hv hFU hF (show 0 ≤ 2 * Real.exp (-κ * β) + 2 * n * Real.exp (-β * L) by positivity)
  have heκ : Real.exp (β * U) * Real.exp (-κ * β) = Real.exp (-(κ - U) * β) := by
    rw [← Real.exp_add]; congr 1; ring
  have heL : Real.exp (β * U) * Real.exp (-β * L) = Real.exp (-(L - U) * β) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hF]
  calc
    _ ≤ (2 * Real.log β * Real.exp (β * U)) *
        (2 * Real.exp (-κ * β) + 2 * n * Real.exp (-β * L)) := by nlinarith only [hh]
    _ = 4 * Real.log β * (Real.exp (β * U) * Real.exp (-κ * β) +
        n * (Real.exp (β * U) * Real.exp (-β * L))) := by ring
    _ = _ := by rw [heκ, heL]

/-- Every particle of an inactive block has exponentially small accelerated
velocity throughout the uncompleted stage, including the terminal window. -/
theorem inactive_velocity (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 4 < κ) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5), ∀ (model : Model) (l : Fin N)
      (x : Configuration n d), StageHyp T C β κ M l x →
      ∀ i j : Fin n, i ∈ T.left l → j ∈ T.right l →
      1 - ⟪(x i).val, (x j).val⟫ ≤ upperBarrier C l + 2 * treeMargin hN C →
      (¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l, angularDist (x p) (x q) ≤ clockCutoff β) →
      ∀ D ∈ T.partition l.castSucc, D ≠ T.left l → D ≠ T.right l → ∀ p ∈ D,
      ‖clockFactor β x • vectorField model β x p‖ ≤
        4 * Real.log β * (Real.exp (-(κ - (upperBarrier C l + 2 * treeMargin hN C)) * β) +
          n * Real.exp (-(5 * treeMargin hN C) * β)) := by
  obtain ⟨B, hB, hclock⟩ := CompletionScalar.clock_bounds T hN C hC κ (by linarith only [hκ])
  obtain ⟨G, hG, hgeo⟩ := ActiveGeometry.stage_barriers T hN C hC
  refine ⟨max B G, hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ M hM model l x hs i j hi hj hu hnc D hD hDl hDr p hp
  have hβB := (le_max_left _ _).trans hβ
  have hβG := (le_max_right _ _).trans hβ
  have hβ1 := hB.trans_le hβB
  have hF0 : 0 ≤ clockFactor β x :=
    (le_min zero_le_one (Real.log_pos hβ1).le).trans (GeneralClock.clockFactor_bounds β hβ1 x).1
  have hFU := (hclock β hβB M hM l x hs i j hi hj hu hnc).2.2
  have hsep := PlateauCapGeometry.inactive_barrier_of_nonactive_pairs T l x _
    (hgeo β hβG M hM l x hs.2.1 hs.2.2).2 D hD hDl hDr
  have hraw := ActiveVectorLaw.geometric_error model β (Real.exp (-κ * β))
    (upperBarrier C l + 7 * treeMargin hN C) (zero_lt_one.trans hβ1).le (Real.exp_pos _).le
    x D ∅ p p (fun k hk => hs.1 D hD k hk p hp) (by intro k hk; exact False.elim (Finset.notMem_empty k hk))
    (fun k hk _ => hsep p hp k hk)
  simp only [Finset.sum_empty, zero_smul, sub_zero] at hraw
  have hh := scaled_geometric_bound β κ (upperBarrier C l + 2 * treeMargin hN C)
    (upperBarrier C l + 7 * treeMargin hN C) (clockFactor β x)
    (vectorField model β x p) hF0 hFU hraw
  simpa only [show (upperBarrier C l + 7 * treeMargin hN C) -
    (upperBarrier C l + 2 * treeMargin hN C) = 5 * treeMargin hN C by ring] using hh

/-- Actual inactive particles stay exponentially close to their entry positions.
Completion at the right endpoint is allowed. -/
theorem inactive_displacement (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 4 < κ) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5), ∀ (model : Model) (l : Fin N)
      (X : ℝ → Configuration n d), Solves model β X →
      ∀ shift : ℝ, 0 ≤ shift → ∀ clock : ℝ → ℝ, ClockRelation β X shift clock →
      ∀ i j : Fin n, i ∈ T.left l → j ∈ T.right l →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      (∀ t ∈ Icc a b, StageHyp T C β κ M l (accelerated X shift clock t)) →
      (∀ t ∈ Icc a b, 1 - ⟪(accelerated X shift clock t i).val, (accelerated X shift clock t j).val⟫ ≤
        upperBarrier C l + 2 * treeMargin hN C) →
      (∀ t ∈ Ico a b, ¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
        angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ≤ clockCutoff β) →
      ∀ t ∈ Icc a b, ∀ D ∈ T.partition l.castSucc, D ≠ T.left l → D ≠ T.right l → ∀ p ∈ D,
      ‖(accelerated X shift clock t p).val - (accelerated X shift clock a p).val‖ ≤
        (4 * Real.log β * (Real.exp (-(κ - (upperBarrier C l + 2 * treeMargin hN C)) * β) +
          n * Real.exp (-(5 * treeMargin hN C) * β))) * (t - a) := by
  obtain ⟨B, hB, hstatic⟩ := inactive_velocity T hN C hC κ hκ
  refine ⟨B, hB, ?_⟩
  intro β hβ M hM model l X hX shift hshift clock hc i j hi hj a b ha hab hs hu hnc t ht D hD hDl hDr p hp
  have hβ1 := hB.trans_le hβ
  have hAE := (ae_restrict_iff' measurableSet_Ici).mp
    (ActiveParticleTrajectory.ae_hasDerivAt model β X hX shift hshift clock hc p)
  apply ActiveParticleTrajectory.norm_sub_le_of_ae_hasDerivAt_bound ht.1
    (by have hlog := (Real.log_pos hβ1).le; positivity)
    ((ActiveParticleTrajectory.accelerated_lipschitz model β hβ1 X hX shift hshift clock hc p).mono
      (fun u hu => ha.trans hu.1))
  filter_upwards [hAE] with u hdu humem
  have hub : u ∈ Icc a b := ⟨humem.1.le, humem.2.le.trans ht.2⟩
  exact ⟨_, hdu (ha.trans humem.1.le), hstatic β hβ M hM model l
    (accelerated X shift clock u) (hs u hub) i j hi hj (hu u hub)
      (hnc u ⟨humem.1.le, humem.2.trans_le ht.2⟩) D hD hDl hDr p hp⟩

end Metastability.ActiveCenterMotion
