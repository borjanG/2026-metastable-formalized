import Metastability.ActiveSourceLaw
import Metastability.ContractionInteraction
import Metastability.PlateauCapGeometry

/-!
# Exterior interaction estimates on a stopped plateau

The source exterior density is the sum of genuine finite maxima. Active-child
interactions retain their sine-squared factor; exterior terms retain the
prepared-tree barrier. No bound on that density is assumed.
-/
noncomputable section
open Filter Set
open scoped Topology BigOperators RealInnerProductSpace
namespace Metastability.PlateauInteraction
open Source ActiveCoefficients ActiveVelocity ContractionInteraction
variable {n N d : ℕ}

/-- A current block diameter error controls the full source density across
its partner block, including the sine-squared prefactor. -/
theorem active_pair_interaction_le (β δ : ℝ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ)
    (hsmall : β * δ ≤ 1 / 4) (x : Configuration n d) (a k i j : Fin n)
    (ha : angularDist (x a) (x i) ≤ δ) (hk : angularDist (x k) (x j) ≤ δ) :
    interaction β (x a) (x k) ≤ 4 * (1 + β * sineSquare x i j) * kernel β x i j := by
  have hnear : |⟪(x a).val, (x k).val⟫ - ⟪(x i).val, (x j).val⟫| ≤ 2 * δ := by
    exact (BlockGeometry.abs_inner_sub_inner_le (x a) (x k) (x i) (x j)).trans
      ((add_le_add ((AngularGeometry.norm_sub_le_angularDist _ _).trans ha)
        ((AngularGeometry.norm_sub_le_angularDist _ _).trans hk)).trans_eq (by ring))
  have habs₁ : |⟪(x a).val, (x k).val⟫| ≤ 1 := abs_le.mpr (ModelBounds.inner_bounds _ _)
  have habs₂ : |⟪(x i).val, (x j).val⟫| ≤ 1 := abs_le.mpr (ModelBounds.inner_bounds _ _)
  have hsquares : |⟪(x a).val, (x k).val⟫ ^ 2 - ⟪(x i).val, (x j).val⟫ ^ 2| ≤ 4 * δ := by
    rw [show ⟪(x a).val, (x k).val⟫ ^ 2 - ⟪(x i).val, (x j).val⟫ ^ 2 =
      (⟪(x a).val, (x k).val⟫ - ⟪(x i).val, (x j).val⟫) *
        (⟪(x a).val, (x k).val⟫ + ⟪(x i).val, (x j).val⟫) by ring, abs_mul]
    have hsum := (abs_add_le _ _).trans (add_le_add habs₁ habs₂)
    have hh := mul_le_mul hnear hsum (abs_nonneg _) (by positivity : 0 ≤ 2 * δ)
    nlinarith only [hh]
  have hs := sineSquare_nonneg x i j
  have hfactor : 1 + β * (1 - ⟪(x a).val, (x k).val⟫ ^ 2) ≤
      2 * (1 + β * sineSquare x i j) := by
    have hh := mul_le_mul_of_nonneg_left (abs_le.mp hsquares).1 hβ
    dsimp only [sineSquare] at *
    nlinarith only [hh, hsmall, mul_nonneg hβ hs]
  have hβδ := mul_nonneg hβ hδ
  have he : Real.exp (2 * β * δ) ≤ 2 := by
    have hh := Real.abs_exp_sub_one_le (show |2 * β * δ| ≤ 1 by
      rw [abs_of_nonneg (by positivity)]
      nlinarith only [hsmall])
    rw [abs_of_nonneg (show 0 ≤ 2 * β * δ by positivity)] at hh
    have hu := (abs_le.mp hh).2
    nlinarith only [hu, hsmall]
  have hkernel : kernel β x a k ≤ 2 * kernel β x i j := by
    calc
      _ ≤ Real.exp (β * (⟪(x i).val, (x j).val⟫ - 1) + 2 * β * δ) := by
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left (abs_le.mp hnear).2 hβ
        nlinarith only [hh]
      _ = kernel β x i j * Real.exp (2 * β * δ) := Real.exp_add _ _
      _ ≤ kernel β x i j * 2 := mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
      _ = _ := mul_comm _ _
  rw [interaction_eq_inner]
  have hh := mul_le_mul hfactor hkernel (Real.exp_pos _).le (by positivity : 0 ≤ 2 * (1 + β * sineSquare x i j))
  change (1 + β * (1 - ⟪(x a).val, (x k).val⟫ ^ 2)) * kernel β x a k ≤ _
  nlinarith only [hh]

/-- Active-child exterior bound directly from the literal sum of finite maxima. -/
theorem active_exterior_le (β δ L : ℝ) (hβ : 0 ≤ β) (hδ : 0 ≤ δ)
    (hsmall : β * δ ≤ 1 / 4) (x : Configuration n d)
    (B C : Block n) (hB : B.Nonempty) (i j : Fin n)
    (hBclose : ∀ a ∈ B, angularDist (x a) (x i) ≤ δ)
    (hCclose : ∀ k ∈ C, angularDist (x k) (x j) ≤ δ)
    (hsep : ∀ a ∈ B, ∀ k ∉ B, k ∉ C → L ≤ 1 - ⟪(x a).val, (x k).val⟫) :
    exterior β x B hB ≤ 4 * n * (1 + β * sineSquare x i j) * kernel β x i j +
      n * (1 + β) * Real.exp (-β * L) := by
  let P := 4 * (1 + β * sineSquare x i j) * kernel β x i j
  let E := (1 + β) * Real.exp (-β * L)
  have hP : 0 ≤ P := by
    have hs := sineSquare_nonneg x i j
    have hk : 0 ≤ kernel β x i j := (Real.exp_pos _).le
    dsimp only [P]
    positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hterm : ∀ k ∈ Finset.univ \ B,
      B.sup' hB (fun a => interaction β (x a) (x k)) ≤ P + E := by
    intro k hk
    apply Finset.sup'_le hB
    intro a ha
    by_cases hkC : k ∈ C
    · exact (active_pair_interaction_le β δ hβ hδ hsmall x a k i j (hBclose a ha) (hCclose k hkC)).trans
        (le_add_of_nonneg_right hE)
    · exact (interaction_le_of_barrier β L hβ (x a) (x k)
        (hsep a ha k (Finset.mem_sdiff.mp hk).2 hkC)).trans (le_add_of_nonneg_left hP)
  calc
    exterior β x B hB ≤ ∑ _ ∈ Finset.univ \ B, (P + E) := Finset.sum_le_sum hterm
    _ = ((Finset.univ \ B).card : ℝ) * (P + E) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ n * (P + E) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (show (Finset.univ \ B).card ≤ n by
        simpa only [Fintype.card_fin] using Finset.card_le_univ (Finset.univ \ B))) (add_nonneg hP hE)
    _ = _ := by dsimp only [P, E]; ring

/-- The source geometry yields a common density bound for every current
block. The active term is harmlessly retained also for inactive blocks. -/
theorem exterior_le_of_stage (T : CollisionTree n N) (C : TreeCaps T d)
    (β κ M L : ℝ) (hβ : 0 ≤ β) (hsmall : β * Real.exp (-κ * β) ≤ 1 / 4)
    (l : Fin N) (x : Configuration n d) (hstage : ActiveSourceLaw.StageHyp T C β κ M l x)
    (hext : ∀ a ∈ T.parent l, ∀ k ∉ T.parent l, L ≤ 1 - ⟪(x a).val, (x k).val⟫)
    (hpair : ∀ a k, T.blockOf l.castSucc a ≠ T.blockOf l.castSucc k →
      ¬ ActiveGeometry.IsActiveCross T l a k → L ≤ 1 - ⟪(x a).val, (x k).val⟫)
    (i j : Fin n) (hi : i ∈ T.left l) (hj : j ∈ T.right l)
    (D : Block n) (hD : D ∈ T.partition l.castSucc) :
    exterior β x D (T.block_nonempty _ _ hD) ≤
      4 * n * (1 + β * sineSquare x i j) * kernel β x i j +
        n * (1 + β) * Real.exp (-β * L) := by
  by_cases hDl : D = T.left l
  · subst D
    exact active_exterior_le β _ L hβ (Real.exp_pos _).le hsmall x _ _ _ i j
      (fun a ha => hstage.1 _ (T.left_mem l) a ha i hi)
      (fun k hk => hstage.1 _ (T.right_mem l) k hk j hj)
      (fun a ha k hkB hkC => hext a (Finset.mem_union_left _ ha) k (by
        simpa only [CollisionTree.parent, Finset.mem_union, not_or] using And.intro hkB hkC))
  by_cases hDr : D = T.right l
  · subst D
    have hh := active_exterior_le β _ L hβ (Real.exp_pos _).le hsmall x _ _
      (T.block_nonempty _ _ hD) j i
      (fun a ha => hstage.1 _ (T.right_mem l) a ha j hj)
      (fun k hk => hstage.1 _ (T.left_mem l) k hk i hi)
      (fun a ha k hkC hkB => hext a (Finset.mem_union_right _ ha) k (by
        simpa only [CollisionTree.parent, Finset.mem_union, not_or] using And.intro hkB hkC))
    simpa only [sineSquare_comm x j i, kernel_comm β x j i] using hh
  · have hh := exterior_le_of_barrier β L hβ x D (T.block_nonempty _ _ hD)
      (PlateauCapGeometry.inactive_barrier_of_nonactive_pairs T l x L hpair D hD hDl hDr)
    have hs := sineSquare_nonneg x i j
    have hk : 0 ≤ kernel β x i j := (Real.exp_pos _).le
    exact hh.trans (le_add_of_nonneg_left (by positivity))

/-- Multiplication by the literal source clock preserves the active sine
factor and exposes the fixed exterior gap. All numerical smallness is produced. -/
theorem source_weighted_exterior (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 0 < κ) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀, ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5),
      ∀ (l : Fin N) (x : Configuration n d), ActiveSourceLaw.StageHyp T C β κ M l x →
      ∀ (i j : Fin n), i ∈ T.left l → j ∈ T.right l →
      1 - ⟪(x i).val, (x j).val⟫ ≤ upperBarrier C l + 2 * CapEnlargement.treeMargin hN C →
      ActiveScales.mesoscopicScale β ≤ angularDist (x i) (x j) →
      ∀ (D : Block n) (hD : D ∈ T.partition l.castSucc),
      exterior β x D (T.block_nonempty _ _ hD) * clockFactor β x ≤
        8 * n * (1 + β * sineSquare x i j) * Real.log β +
          2 * n * (1 + β) * Real.log β * Real.exp (-5 * CapEnlargement.treeMargin hN C * β) := by
  obtain ⟨G, hG, hgeometry⟩ := ActiveGeometry.stage_barriers T hN C hC
  obtain ⟨B, hB, hclock⟩ := ActiveClock.active_clock T hN C hC κ hκ
  obtain ⟨S, hS⟩ := eventually_atTop.mp (ActiveScales.eventually_mul_exp_le_rpow 4 κ 1 0 hκ)
  refine ⟨max G (max B S), hG.trans_le (le_max_left _ _), ?_⟩
  intro β hβ M hM l x hstage i j hi hj hupper hangle D hD
  have hβG : G ≤ β := (le_max_left _ _).trans hβ
  have hβB : B ≤ β := (le_max_left _ _).trans ((le_max_right _ _).trans hβ)
  have hβS : S ≤ β := (le_max_right _ _).trans ((le_max_right _ _).trans hβ)
  have hβ1 := hB.trans_le hβB
  have hβ0 := zero_lt_one.trans hβ1
  have hlog := Real.log_pos hβ1
  have hs := sineSquare_nonneg x i j
  have hK := Real.exp_pos (β * (⟪(x i).val, (x j).val⟫ - 1))
  have hsm := hS β hβS
  simp only [Real.rpow_one, Real.rpow_zero] at hsm
  have hsmall : β * Real.exp (-κ * β) ≤ 1 / 4 := by linarith only [hsm]
  obtain ⟨hext, hpair⟩ := hgeometry β hβG M hM l x hstage.2.1 hstage.2.2
  have hraw := exterior_le_of_stage T C β κ M _ hβ0.le hsmall l x hstage hext hpair i j hi hj D hD
  have hc := (hclock β hβB M hM l x hstage.1 hstage.2.1 hstage.2.2 i j hi hj hupper hangle).2.2
  have hp : β ^ (-(1 / 3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hβ1.le (by norm_num)
  have hden : 0 < Real.log β * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫)) := by positivity
  have hratio : clockFactor β x / (Real.log β * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫))) ≤ 2 := by
    linarith only [(abs_le.mp hc).2, hp]
  have hF : clockFactor β x ≤ 2 * (Real.log β * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫))) :=
    (div_le_iff₀ hden).mp hratio
  have hF0 : 0 ≤ clockFactor β x :=
    (le_min zero_le_one hlog.le).trans (GeneralClock.clockFactor_bounds β hβ1 x).1
  have hKF : kernel β x i j * clockFactor β x ≤ 2 * Real.log β := by
    have hh := mul_le_mul_of_nonneg_left hF hK.le
    have he : kernel β x i j * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫)) = 1 := by
      rw [kernel, ← Real.exp_add, show β * (⟪(x i).val, (x j).val⟫ - 1) +
        β * (1 - ⟪(x i).val, (x j).val⟫) = 0 by ring, Real.exp_zero]
    calc
      _ ≤ kernel β x i j * (2 * (Real.log β * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫)))) := hh
      _ = (2 * Real.log β) * (kernel β x i j * Real.exp (β * (1 - ⟪(x i).val, (x j).val⟫))) := by ring
      _ = _ := by rw [he, mul_one]
  have hFU : clockFactor β x ≤ 2 * Real.log β * Real.exp (β * (upperBarrier C l + 2 * CapEnlargement.treeMargin hN C)) := by
    apply hF.trans
    have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hupper hβ0.le)) (show 0 ≤ 2 * Real.log β by positivity)
    convert hh using 1
    ring
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

end Metastability.PlateauInteraction
