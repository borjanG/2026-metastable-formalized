import Metastability.PlateauInteraction
import Metastability.CompletionScalar

/-! Actual exterior interaction bounds throughout an uncompleted stage,
including the interval below the mesoscopic angle. -/
noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Metastability.CompletionInteraction
open Source ActiveCoefficients ActiveVelocity ContractionInteraction CapEnlargement
variable {n N d : ℕ}

theorem source_weighted_exterior (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 4 < κ) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀, ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5),
      ∀ (l : Fin N) (x : Configuration n d), ActiveSourceLaw.StageHyp T C β κ M l x →
      ∀ (i j : Fin n), i ∈ T.left l → j ∈ T.right l →
      1 - ⟪(x i).val, (x j).val⟫ ≤ upperBarrier C l + 2 * CapEnlargement.treeMargin hN C →
      (¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l, angularDist (x p) (x q) ≤ clockCutoff β) →
      ∀ (D : Block n) (hD : D ∈ T.partition l.castSucc),
      exterior β x D (T.block_nonempty _ _ hD) * clockFactor β x ≤
        8 * n * (1 + β * sineSquare x i j) * Real.log β +
          2 * n * (1 + β) * Real.log β * Real.exp (-5 * CapEnlargement.treeMargin hN C * β) := by
  obtain ⟨G, hG, hgeometry⟩ := ActiveGeometry.stage_barriers T hN C hC
  obtain ⟨B, hB, hclock⟩ := CompletionScalar.clock_bounds T hN C hC κ (by linarith only [hκ])
  obtain ⟨S, hS⟩ := eventually_atTop.mp (ActiveScales.eventually_mul_exp_le_rpow 4 κ 1 0 (by linarith only [hκ]))
  refine ⟨max G (max B S), hG.trans_le (le_max_left _ _), ?_⟩
  intro β hβ M hM l x hstage i j hi hj hupper hnoncomplete D hD
  have hβG : G ≤ β := (le_max_left _ _).trans hβ
  have hβB : B ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβS : S ≤ β := (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  have hβ1 := hB.trans_le hβB
  have hβ0 := zero_lt_one.trans hβ1
  have hlog := Real.log_pos hβ1
  have hs := sineSquare_nonneg x i j
  have hsm := hS β hβS
  simp only [Real.rpow_one, Real.rpow_zero] at hsm
  have hsmall : β * Real.exp (-κ * β) ≤ 1 / 4 := by linarith only [hsm]
  obtain ⟨hext, hpair⟩ := hgeometry β hβG M hM l x hstage.2.1 hstage.2.2
  have hraw := PlateauInteraction.exterior_le_of_stage T C β κ M _ hβ0.le hsmall l x hstage hext hpair i j hi hj D hD
  obtain ⟨_, hKF, hFU⟩ := hclock β hβB M hM l x hstage i j hi hj hupper hnoncomplete
  have hF0 : 0 ≤ clockFactor β x :=
    (le_min zero_le_one hlog.le).trans (GeneralClock.clockFactor_bounds β hβ1 x).1
  have hactive := mul_le_mul_of_nonneg_left hKF (show 0 ≤ 4 * n * (1 + β * sineSquare x i j) by positivity)
  have houtside := mul_le_mul_of_nonneg_left hFU (show 0 ≤ n * (1 + β) *
    Real.exp (-β * (upperBarrier C l + 7 * CapEnlargement.treeMargin hN C)) by positivity)
  have hexp : Real.exp (-β * (upperBarrier C l + 7 * CapEnlargement.treeMargin hN C)) *
      Real.exp (β * (upperBarrier C l + 2 * CapEnlargement.treeMargin hN C)) =
        Real.exp (-5 * CapEnlargement.treeMargin hN C * β) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ (4 * n * (1 + β * sineSquare x i j) * kernel β x i j +
        n * (1 + β) * Real.exp (-β * (upperBarrier C l + 7 * CapEnlargement.treeMargin hN C))) * clockFactor β x :=
      mul_le_mul_of_nonneg_right hraw hF0
    _ ≤ 8 * n * (1 + β * sineSquare x i j) * Real.log β +
        (2 * n * (1 + β) * Real.log β) *
          (Real.exp (-β * (upperBarrier C l + 7 * CapEnlargement.treeMargin hN C)) *
            Real.exp (β * (upperBarrier C l + 2 * CapEnlargement.treeMargin hN C))) := by
      nlinarith only [hactive, houtside]
    _ = _ := by rw [hexp]


end Metastability.CompletionInteraction
