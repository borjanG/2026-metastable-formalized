import Metastability.BlockGeometry

/-! Static geometry used to prepare all initial blocks simultaneously. -/

noncomputable section
open scoped RealInnerProductSpace

namespace Metastability.PreparationGeometry
open Source AngularGeometry
variable {n d : ℕ} {ι : Type*}

/-- Small neighborhoods of separated centers give a particlewise exterior
barrier. The blocks need only cover the particles. -/
theorem exterior_barrier_of_center_separation
    (A : ι → Block n) (w : ι → Sphere d)
    (hcover : ∀ i : Fin n, ∃ α, i ∈ A α)
    (g R : ℝ)
    (hgap : ∀ α γ, α ≠ γ → g ≤ 1 - ⟪(w α).val, (w γ).val⟫)
    (hR : 4 * R ≤ g) (x : Configuration n d)
    (hcap : ∀ α, ∀ i ∈ A α, angularDist (x i) (w α) ≤ R) :
    ∀ α, ∀ i ∈ A α, ∀ k ∉ A α,
      g / 2 ≤ 1 - ⟪(x i).val, (x k).val⟫ := by
  intro α i hi k hk
  obtain ⟨γ, hγ⟩ := hcover k
  have hne : α ≠ γ := by
    intro heq
    exact hk (heq ▸ hγ)
  have hpair := hgap α γ hne
  have hpert := BlockGeometry.abs_inner_sub_inner_le (x i) (x k) (w α) (w γ)
  have hi' := (norm_sub_le_angularDist (x i) (w α)).trans (hcap α i hi)
  have hk' := (norm_sub_le_angularDist (x k) (w γ)).trans (hcap γ k hγ)
  have hd := le_abs_self (⟪(x i).val, (x k).val⟫ - ⟪(w α).val, (w γ).val⟫)
  linarith only [hpair, hpert, hi', hk', hd, hR]

/-- A small cap produces its literal normalized mean and controls its center. -/
theorem exists_mean_near_center (A : Block n) (hA : A.Nonempty)
    (x : Configuration n d) (w : Sphere d) (R : ℝ)
    (hR0 : 0 ≤ R) (hRπ : R < Real.pi / 2)
    (hcap : ∀ i ∈ A, angularDist (x i) w ≤ R) :
    BlockGeometry.blockMean A hA x ≠ 0 ∧ ∃ z : Sphere d,
      z.val = ‖BlockGeometry.blockMean A hA x‖⁻¹ • BlockGeometry.blockMean A hA x ∧
      angularDist z w ≤ R := by
  let C : SphericalCap d := ⟨w, R, hR0, hRπ⟩
  have hc : ∀ i ∈ A, x i ∈ C.carrier := hcap
  exact ⟨BlockGeometry.blockMean_ne_zero A hA x C hc,
    BlockGeometry.normalizedMean A hA x C hc, rfl,
    BlockGeometry.normalizedMean_mem_cap A hA x C hc⟩

end Metastability.PreparationGeometry
