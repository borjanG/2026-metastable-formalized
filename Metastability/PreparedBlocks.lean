import Metastability.CapNoExit
import Metastability.BlockContraction
import Metastability.PreparationScale
import Metastability.PreparationGeometry
import Metastability.GeneralClock

/-!
# Simultaneous preparation of blocks with separated centers

This intermediate theorem uses an explicit static separation of the centers.
The tree-facing theorem derives that separation from strict preparation.
No dynamical confinement or contraction estimate is an input.
-/

noncomputable section
open Filter Set
open scoped Topology RealInnerProductSpace

namespace Metastability.PreparedBlocks
open Source

/-- Visible blocks around separated centers become exponentially tight after
one common original-time shift. The normalized means and clock are produced. -/
theorem prepare_separated_blocks (n : ℕ) (hn : 0 < n) (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (ι : Type*) [Fintype ι]
      (A : ι → Block n) (hA : ∀ α, (A α).Nonempty) (w : ι → Sphere d),
      (∀ i : Fin n, ∃ α, i ∈ A α) →
      ∀ (g : ℝ), 0 < g →
      (∀ α γ, α ≠ γ → g ≤ 1 - ⟪(w α).val, (w γ).val⟫) →
      ∀ᶠ β : ℝ in atTop, 1 < β ∧
      ∀ (model : Model) (X : ℝ → Configuration n d), Solves model β X →
      (∀ α, ∀ i ∈ A α, angularDist (X 0 i) (w α) ≤ visibleScale β) →
      (∀ α, ∀ i ∈ A α, ∀ j ∈ A α,
        angularDist (X 0 i) (X 0 j) ≤ visibleScale β) →
      (∀ t ∈ Icc 0 (C * β), ∀ α, ∀ i ∈ A α,
        angularDist (X t i) (w α) ≤ 2 * visibleScale β) ∧
      (∀ α, ∀ i ∈ A α, ∀ j ∈ A α,
        angularDist (X (C * β) i) (X (C * β) j) ≤ Real.exp (-2 * κ * β)) ∧
      (∀ α, BlockGeometry.blockMean (A α) (hA α) (X (C * β)) ≠ 0 ∧
        ∃ z : Sphere d,
          z.val = ‖BlockGeometry.blockMean (A α) (hA α) (X (C * β))‖⁻¹ •
            BlockGeometry.blockMean (A α) (hA α) (X (C * β)) ∧
          angularDist z (w α) ≤ 2 * visibleScale β) ∧
      ∃ clock : ℝ → ℝ, ClockRelation β X (C * β) clock := by
  obtain ⟨c₀, hc₀, C₀, _hC₀, β₀, _hβ₀, _hfirst, hsecond⟩ :=
    BlockContraction.block_contraction n hn
  let C : ℝ := 8 * κ / c₀ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hCmargin : 8 * κ / c₀ < C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro d ι _ A hA w hcover g hg hgap
  obtain ⟨β₁, _hβ₁, hcontract⟩ := hsecond (g / 2) κ C (by positivity) hκ hCmargin
  filter_upwards [eventually_ge_atTop β₁,
    PreparationScale.eventually_preparation_parameters n g C hg hC] with β hβ₁ hparam
  obtain ⟨hβ, hε, _hε1, hεπ, hεg, _hquarter, herr⟩ := hparam
  refine ⟨hβ, ?_⟩
  intro model X hX hstart hdiam
  have hβ0 : 0 ≤ β := by linarith only [hβ]
  have htime : 0 ≤ C * β := mul_nonneg hC.le hβ0
  have hsep : ∀ x : Configuration n d,
      (∀ α, ∀ i ∈ A α, angularDist (x i) (w α) ≤ 2 * visibleScale β) →
      ∀ α, ∀ i ∈ A α, ∀ k ∉ A α,
        g / 2 ≤ 1 - ⟪(x i).val, (x k).val⟫ := by
    intro x hx
    exact PreparationGeometry.exterior_barrier_of_center_separation A w hcover
      g (2 * visibleScale β) hgap (by linarith only [hεg]) x hx
  have hconf : ∀ t ∈ Icc 0 (C * β), ∀ α, ∀ i ∈ A α,
      angularDist (X t i) (w α) ≤ 2 * visibleScale β := by
    have h := CapNoExit.simultaneous_cap_no_exit model β hβ0 X hX A hA w
      0 (C * β) (visibleScale β) (2 * visibleScale β) (g / 2)
      (le_refl 0) htime hε.le (by linarith only [hε]) hεπ hstart
      (fun u _ hu => hsep (X u) hu) (by simpa only [sub_zero] using herr)
    intro t ht α i hi
    exact (h t ht α i hi).1
  refine ⟨hconf, ?_, ?_, GeneralClock.exists_clockRelation β hβ X hX (C * β) htime⟩
  · intro α
    have h := hcontract d model β hβ₁ X hX 0 (le_refl 0) (A α) (hA α)
      (hdiam α) (by
        intro t ht _ i hi k hk
        rw [AngularGeometry.cos_angularDist]
        apply hsep (X t) (hconf t (by simpa only [zero_add] using ht)) α i hi k hk)
    simpa only [zero_add] using h.2
  · intro α
    exact PreparationGeometry.exists_mean_near_center (A α) (hA α) (X (C * β))
      (w α) (2 * visibleScale β) (by positivity) hεπ
      (hconf (C * β) ⟨htime, le_refl _⟩ α)

end Metastability.PreparedBlocks
