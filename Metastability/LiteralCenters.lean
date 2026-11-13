import Metastability.BlockGeometry
import Metastability.PreparationGeometry

/-! Estimates for explicitly normalized arithmetic means, independent of the
containing cap used to establish their nonvanishing. -/
noncomputable section
namespace Metastability.LiteralCenters
open Source AngularGeometry BlockGeometry
variable {n d : ℕ}

theorem particle_to_mean (D : Block n) (hne : D.Nonempty) (x : Configuration n d)
    (z : Sphere d) (hz : z.val = ‖blockMean D hne x‖⁻¹ • blockMean D hne x)
    (ε : ℝ) (hε : ε < Real.pi / 2)
    (hdiam : ∀ p ∈ D, ∀ q ∈ D, angularDist (x p) (x q) ≤ ε)
    (p : Fin n) (hp : p ∈ D) : angularDist (x p) z ≤ ε := by
  obtain ⟨C, _, hC⟩ := exists_cap_of_diameter D hne x hε hdiam
  have heq : z = normalizedMean D hne x C hC := Subtype.ext hz
  rw [heq]
  exact angularDist_normalizedMean_le_of_diameter D hne x C hC hε hdiam hp

theorem mean_in_cap (D : Block n) (hne : D.Nonempty) (x : Configuration n d)
    (z w : Sphere d) (hz : z.val = ‖blockMean D hne x‖⁻¹ • blockMean D hne x)
    (r : ℝ) (hr0 : 0 ≤ r) (hrπ : r < Real.pi / 2)
    (hcap : ∀ p ∈ D, angularDist (x p) w ≤ r) : angularDist z w ≤ r := by
  let C : SphericalCap d := ⟨w, r, hr0, hrπ⟩
  have heq : z = normalizedMean D hne x C hcap := Subtype.ext hz
  rw [heq]
  exact normalizedMean_mem_cap D hne x C hcap

/-- Two small block diameters and a center displacement control every particle. -/
theorem particle_displacement (D : Block n) (hne : D.Nonempty)
    (x y : Configuration n d) (z w : Sphere d)
    (hz : z.val = ‖blockMean D hne x‖⁻¹ • blockMean D hne x)
    (hw : w.val = ‖blockMean D hne y‖⁻¹ • blockMean D hne y)
    (ε r : ℝ) (hε : ε < Real.pi / 2)
    (hx : ∀ p ∈ D, ∀ q ∈ D, angularDist (x p) (x q) ≤ ε)
    (hy : ∀ p ∈ D, ∀ q ∈ D, angularDist (y p) (y q) ≤ ε)
    (hmove : angularDist z w ≤ r) (p q : Fin n) (hp : p ∈ D) (hq : q ∈ D) :
    angularDist (x p) (y q) ≤ 2 * ε + r := by
  have hxz := particle_to_mean D hne x z hz ε hε hx p hp
  have hyw := particle_to_mean D hne y w hw ε hε hy q hq
  have htri := angularDist_triangle (x p) z (y q)
  have htri' := angularDist_triangle z w (y q)
  rw [angularDist_comm w (y q)] at htri'
  linarith only [hxz, hyw, hmove, htri, htri']

end Metastability.LiteralCenters
