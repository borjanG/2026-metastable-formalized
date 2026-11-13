import Metastability.BlockGeometry

/-!
# The source tight-block geometry lemma with uniform explicit constants

The constants are chosen before the dimension, configuration, blocks, and
diameter scale. Both centers are literal normalized Euclidean means. Containing
caps and nonvanishing are derived from diameter; neither is a premise.
-/

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace Metastability.TightGeometry

open Source BlockGeometry

/-- The conclusions of source Lemma `tight-geometry`, including its outer
existential constants and both single-block and two-block estimates.
The proof uses the universal choices `ε₀ = 1/2` and `C = 2`.

The existential sphere points are fully specified by the displayed literal
normalized-mean equations. The second-block disjointness hypothesis is retained
from the source, although the geometric estimates do not need it. -/
theorem tight_geometry (n : ℕ) :
    ∃ ε₀ : ℝ, ε₀ ∈ Ioo 0 1 ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ (d : ℕ) (x : Configuration n d) (A : Block n) (hA : A.Nonempty) (ε : ℝ),
        (∀ i ∈ A, ∀ j ∈ A, angularDist (x i) (x j) ≤ ε) → ε ≤ ε₀ →
        blockMean A hA x ≠ 0 ∧ ∃ zA : Sphere d,
          zA.val = ‖blockMean A hA x‖⁻¹ • blockMean A hA x ∧
          (∀ i ∈ A,
            ‖(x i).val - zA.val‖ ≤ C * ε ∧
            1 - ⟪(x i).val, zA.val⟫ ≤ C * ε ^ 2) ∧
          |‖blockMean A hA x‖ - 1| ≤ C * ε ^ 2 ∧
          ∀ (D : Block n) (hD : D.Nonempty), Disjoint A D →
            (∀ i ∈ D, ∀ j ∈ D, angularDist (x i) (x j) ≤ ε) →
            blockMean D hD x ≠ 0 ∧ ∃ zD : Sphere d,
              zD.val = ‖blockMean D hD x‖⁻¹ • blockMean D hD x ∧
              ∀ i ∈ A, ∀ j ∈ D,
                |⟪(x i).val, (x j).val⟫ - ⟪zA.val, zD.val⟫| ≤ C * ε ∧
                ‖projectTangent (x i) zD.val - projectTangent zA zD.val‖ ≤ C * ε := by
  refine ⟨1 / 2, by norm_num, 2, by norm_num, ?_⟩
  intro d x A hA ε hdiamA hε
  have hεπ : ε < Real.pi / 2 := by
    linarith only [hε, Real.one_le_pi_div_two]
  obtain ⟨C, _, hC⟩ := exists_cap_of_diameter A hA x hεπ hdiamA
  let zA := normalizedMean A hA x C hC
  have hε0 : 0 ≤ ε := by
    obtain ⟨i, hi⟩ := hA
    simpa only [AngularGeometry.angularDist_self] using hdiamA i hi i hi
  have hlinear : ε ≤ 2 * ε := by linarith only [hε0]
  have hquadratic : ε ^ 2 / 2 ≤ 2 * ε ^ 2 := by nlinarith only [sq_nonneg ε]
  refine ⟨blockMean_ne_zero A hA x C hC, zA, rfl, ?_, ?_, ?_⟩
  · intro i hi
    exact ⟨(norm_sub_normalizedMean_le_of_diameter A hA x C hC hεπ hdiamA hi).trans hlinear,
      (one_sub_inner_normalizedMean_le_of_diameter A hA x C hC hεπ hdiamA hi).trans hquadratic⟩
  · exact (abs_norm_blockMean_sub_one_le_of_diameter A hA x hεπ hdiamA).trans hquadratic
  · intro D hD _hdisjoint hdiamD
    obtain ⟨F, _, hF⟩ := exists_cap_of_diameter D hD x hεπ hdiamD
    let zD := normalizedMean D hD x F hF
    refine ⟨blockMean_ne_zero D hD x F hF, zD, rfl, ?_⟩
    intro i hi j hj
    exact ⟨abs_inner_sub_blockCenters_le_of_diameter A D hA hD x C F hC hF
      hεπ hdiamA hdiamD hi hj,
      norm_projectTangent_sub_blockCenter_le_of_diameter A hA x C hC hεπ hdiamA hi zD⟩

end Metastability.TightGeometry
