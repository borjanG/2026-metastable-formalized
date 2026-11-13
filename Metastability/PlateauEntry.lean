import Metastability.PlateauCapGeometry
import Metastability.PlateauRegion

/-! Entry preparation implies the closed plateau region, including active
parent containment and the representative upper barrier. -/

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace Metastability.PlateauEntry
open Source CapEnlargement ActiveSourceLaw
variable {n N d : ℕ}

theorem conditions (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 4), ∀ κ : ℝ, 0 < κ →
      ∀ (l : Fin N) (x : Configuration n d),
      (∀ D ∈ T.partition l.castSucc, ∀ p ∈ D, ∀ q ∈ D,
        angularDist (x p) (x q) ≤ Real.exp (-2 * κ * β)) →
      (∀ (D : Block n) (hD : D ∈ T.partition l.castSucc), ∀ p ∈ D,
        angularDist (x p) (C (T.currentNode l D hD)).center ≤
          (C (T.currentNode l D hD)).radius + M * enlargementScale β) →
      StageHyp T C β κ (M + 1) l x ∧
      ∀ i j, i ∈ T.left l → j ∈ T.right l →
        1 - ⟪(x i).val, (x j).val⟫ ≤ upperBarrier C l + treeMargin hN C := by
  obtain ⟨β₀, hβ₀, hgeom⟩ := PlateauCapGeometry.entry_cap_geometry T hN C hC
  refine ⟨β₀, hβ₀, ?_⟩
  intro β hβ M hM κ hκ l x hd hc
  have hβpos : 0 < β := zero_lt_one.trans (hβ₀.trans_le hβ)
  have hM' : M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5) := ⟨hM.1, by linarith only [hM.2]⟩
  obtain ⟨hp, hu⟩ := (hgeom β hβ M hM').2 l x hc
  have hγ := (enlargementScale_pos hβpos).le
  have hexp : Real.exp (-2 * κ * β) ≤ Real.exp (-κ * β) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_pos hκ hβpos]
  refine ⟨⟨fun D hD p hp q hq => (hd D hD p hp q hq).trans hexp, ?_, ?_⟩, hu⟩
  · intro D hD _ _ p hp
    have hh := hc D hD p hp
    nlinarith only [hh, hγ]
  · intro hP p hp'
    have hh := hp hP p hp'
    nlinarith only [hh, hγ]

end Metastability.PlateauEntry
