import Metastability.PostMergeCenter
import Metastability.PostMergeContraction
import Metastability.PlateauClockTransfer

/-! Post-merge tightening from prescribed entry caps and cutoff diameters.
The interblock separation required by the conditional contraction corollary
is derived on its whole original-time interval. -/
noncomputable section
open Set
open scoped RealInnerProductSpace
namespace Metastability.PostMergeStep
open Source CapEnlargement
variable {n N d : ℕ}

theorem tightening_from_caps (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (k : Fin N)
    (κ CStar : ℝ) (hκ : 0 < κ)
    (hCStar : 8 * κ / (1 / (4 * (n : ℝ))) < CStar) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 4),
      ∀ (model : Model) (X : ℝ → Configuration n d), Solves model β X →
      ∀ shift : ℝ, 0 ≤ shift → ∀ clock : ℝ → ℝ, ClockRelation β X shift clock →
      ∀ t₀ : ℝ, 0 ≤ t₀ →
      (∀ D ∈ T.partition k.castSucc, ∀ p ∈ D, ∀ q ∈ D,
        angularDist (accelerated X shift clock t₀ p) (accelerated X shift clock t₀ q) ≤ clockCutoff β) →
      (∀ (D : Block n) (hD : D ∈ T.partition k.castSucc), ∀ p ∈ D,
        angularDist (accelerated X shift clock t₀ p) (C (T.currentNode k D hD)).center ≤
          (C (T.currentNode k D hD)).radius + M * enlargementScale β) →
      ∃ t₁ : ℝ, t₀ ≤ t₁ ∧
        t₁ = originalClockTime β X shift (clock t₀ + CStar * β) ∧
        clock t₁ = clock t₀ + CStar * β ∧
        t₁ - t₀ ≤ CStar * β / Real.log β * Real.exp (-β * (lowerBarrier C k - treeMargin hN C)) ∧
        t₁ - t₀ ≤ Real.log (Real.log β) / Real.log β ∧
        (∀ t ∈ Icc t₀ t₁,
          (∀ (D : Block n) (hD : D ∈ T.partition k.castSucc), ∀ p ∈ D,
            angularDist (accelerated X shift clock t p) (C (T.currentNode k D hD)).center <
              (C (T.currentNode k D hD)).radius + (M + 1) * enlargementScale β) ∧
          (∀ D ∈ T.partition k.castSucc, ∀ p ∈ D, ∀ q ∈ D,
            angularDist (accelerated X shift clock t p) (accelerated X shift clock t q) ≤ clockCutoff β)) ∧
        (∀ D ∈ T.partition k.castSucc, ∀ p ∈ D, ∀ q ∈ D,
          angularDist (accelerated X shift clock t₁ p) (accelerated X shift clock t₁ q) ≤
            Real.exp (-2 * κ * β)) ∧
        (∀ (D : Block n) (hD : D ∈ T.partition k.castSucc),
          let hne := T.block_nonempty _ _ hD
          BlockGeometry.blockMean D hne (accelerated X shift clock t₀) ≠ 0 ∧ ∃ z₀ : Sphere d,
            z₀.val = ‖BlockGeometry.blockMean D hne (accelerated X shift clock t₀)‖⁻¹ •
              BlockGeometry.blockMean D hne (accelerated X shift clock t₀) ∧
            ∀ t ∈ Icc t₀ t₁,
              BlockGeometry.blockMean D hne (accelerated X shift clock t) ≠ 0 ∧ ∃ z : Sphere d,
                z.val = ‖BlockGeometry.blockMean D hne (accelerated X shift clock t)‖⁻¹ •
                  BlockGeometry.blockMean D hne (accelerated X shift clock t) ∧
                angularDist z z₀ ≤ 4 * clockCutoff β) := by
  have hn := TreeDynamics.particle_pos T
  have hcpos := BlockContraction.contraction_constant_pos n hn
  have hC0 : 0 < CStar := (div_pos (mul_pos (by norm_num) hκ) hcpos).trans hCStar
  have hb := PostMergeGeometry.post_barrier_pos T hN C hC k
  obtain ⟨P, hP, hcaps⟩ := PostMergeCaps.post_merge_caps T hN C hC CStar hC0
  obtain ⟨D, hD, htight⟩ := PostMergeContraction.post_merge_tightening n hn
    (lowerBarrier C k - treeMargin hN C) κ CStar hb hκ hCStar
  obtain ⟨Z, hZ, hcenters⟩ := PostMergeCenter.post_merge_centers T hN C hC CStar hC0
  refine ⟨max P (max D Z), hP.trans_le (le_max_left _ _), ?_⟩
  intro β hβ M hM model X hX shift hshift clock hc t₀ ht₀ hd0 hc0
  have hβP := (le_max_left P (max D Z)).trans hβ
  have hβD := (le_max_left D Z).trans ((le_max_right P (max D Z)).trans hβ)
  have hβZ := (le_max_right D Z).trans ((le_max_right P (max D Z)).trans hβ)
  have hτ0 : 0 ≤ shift + clock t₀ := add_nonneg hshift (hc.1.2.1 t₀ ht₀)
  have hgeometry := (hcaps β hβP M hM model k X hX (shift + clock t₀) hτ0 hc0).2
  obtain ⟨hconf, t₁, hle, hdef, heq, hlength, hratio, hfinal⟩ :=
    htight β hβD N d T k model X hX shift hshift clock hc t₀ ht₀ hd0
      (fun u hu => (hgeometry u hu).2)
  have himage : ∀ t ∈ Icc t₀ t₁,
      shift + clock t ∈ Icc (shift + clock t₀) (shift + clock t₀ + CStar * β) := by
    intro t ht
    have hh := PlateauClockTransfer.shifted_clock_mem_Icc hc ht₀ ht
    rwa [heq, ← add_assoc] at hh
  refine ⟨t₁, hle, hdef, heq, hlength, hratio, ?_, hfinal, ?_⟩
  · intro t ht
    exact ⟨(hgeometry _ (himage t ht)).1, hconf _ (himage t ht)⟩
  · intro D hD
    obtain ⟨hm₀, z₀, hz₀, hzall⟩ := hcenters β hβZ M hM model k X hX
      (shift + clock t₀) hτ0 hc0 hd0 D hD
    refine ⟨hm₀, z₀, hz₀, ?_⟩
    intro t ht
    exact (hzall _ (himage t ht)).2

end Metastability.PostMergeStep
