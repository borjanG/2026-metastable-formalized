import Metastability.PostMergeCaps
import Metastability.PreparationGeometry
import Metastability.PreparationScale

/-! Normalized block centers move by at most four clock cutoffs during tightening. -/

noncomputable section
open Filter Set
open scoped Topology RealInnerProductSpace

namespace Metastability.PostMergeCenter
open Source CapEnlargement
variable {n N d : ℕ}

/-- A particlewise exterior barrier suffices to retain a small cap about the
initial normalized mean. Nonvanishing of every later mean is a conclusion. -/
theorem center_displacement_of_separation
    (model : Model) (β : ℝ) (hβ : 1 < β)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (A : Block n) (hA : A.Nonempty) (a b L : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hsmall : visibleScale β < Real.pi / 2) (hscale : visibleScale β ≤ 1)
    (hdiam : ∀ i ∈ A, ∀ j ∈ A, angularDist (X a i) (X a j) ≤ clockCutoff β)
    (hsep : ∀ t ∈ Ico a b, ∀ i ∈ A, ∀ j ∉ A,
      L ≤ 1 - ⟪(X t i).val, (X t j).val⟫)
    (herror : (2 * n) * (b - a) * Real.exp (-β * L) < visibleScale β ^ 2 / 8) :
    BlockGeometry.blockMean A hA (X a) ≠ 0 ∧ ∃ z₀ : Sphere d,
      z₀.val = ‖BlockGeometry.blockMean A hA (X a)‖⁻¹ • BlockGeometry.blockMean A hA (X a) ∧
      ∀ t ∈ Icc a b,
        (∀ i ∈ A, angularDist (X t i) z₀ < 4 * clockCutoff β) ∧
        BlockGeometry.blockMean A hA (X t) ≠ 0 ∧ ∃ z : Sphere d,
          z.val = ‖BlockGeometry.blockMean A hA (X t)‖⁻¹ • BlockGeometry.blockMean A hA (X t) ∧
          angularDist z z₀ ≤ 4 * clockCutoff β := by
  have hh : 0 < clockCutoff β := ActiveScales.clockCutoff_pos hβ
  have hfour : 4 * clockCutoff β = visibleScale β := by unfold clockCutoff; ring
  have hhπ : clockCutoff β < Real.pi / 2 := by linarith only [hsmall, hfour, hh]
  obtain ⟨E, _, hE⟩ := BlockGeometry.exists_cap_of_diameter A hA (X a) hhπ hdiam
  let z₀ := BlockGeometry.normalizedMean A hA (X a) E hE
  have hinitial : ∀ i ∈ A, angularDist (X a i) z₀ ≤ 2 * clockCutoff β := by
    intro i hi
    exact (BlockGeometry.angularDist_normalizedMean_le_of_diameter
      A hA (X a) E hE hhπ hdiam hi).trans (by linarith only [hh])
  have hgap := PreparationScale.cosine_margin (show 0 ≤ 2 * clockCutoff β by positivity)
    (show 2 * clockCutoff β ≤ 1 by linarith only [hscale, hfour, hh])
  have hmargin : visibleScale β ^ 2 / 8 ≤
      Real.cos (2 * clockCutoff β) - Real.cos (4 * clockCutoff β) := by
    convert hgap using 1
    · rw [← hfour]
      ring
    · congr 1
      congr 1
      ring
  have hconf := PostMergeCaps.variable_caps_no_exit model β (zero_lt_one.trans hβ).le X hX
    (fun _ : Unit => A) (fun _ => hA) (fun _ => z₀)
    (fun _ => 2 * clockCutoff β) (fun _ => 4 * clockCutoff β) a b L ha hab
    (fun _ => by positivity) (fun _ => by linarith only [hh])
    (fun _ => by rwa [hfour]) (fun _ => hinitial)
    (fun t ht _ _ => hsep t ht) (fun _ => herror.trans_le hmargin)
  refine ⟨BlockGeometry.blockMean_ne_zero_of_diameter A hA (X a) hhπ hdiam, z₀, rfl, ?_⟩
  intro t ht
  have htcap : ∀ i ∈ A, angularDist (X t i) z₀ < 4 * clockCutoff β := hconf t ht ()
  exact ⟨htcap, PreparationGeometry.exists_mean_near_center A hA (X t) z₀
    (4 * clockCutoff β) (by positivity) (by rwa [hfour]) (fun i hi => (htcap i hi).le)⟩

/-- The exponentially small exterior drift fits the shrinking center cap,
uniformly over all current stages. -/
theorem eventually_center_parameters (n : ℕ) (CStar δ : ℝ)
    (hCStar : 0 < CStar) (hδ : 0 < δ) :
    ∀ᶠ β : ℝ in atTop, 1 < β ∧ visibleScale β < Real.pi / 2 ∧ visibleScale β ≤ 1 ∧
      2 * n * CStar * β * Real.exp (-β * (7 * δ)) < visibleScale β ^ 2 / 8 := by
  have he := PreparationScale.eventually_cap_error_small (8 * n * CStar) (7 * δ)
    (by positivity) (by positivity)
  filter_upwards [eventually_gt_atTop (1 : ℝ), he,
    ContractionScale.tendsto_visibleScale.eventually (gt_mem_nhds (half_pos Real.pi_pos)),
    ContractionScale.tendsto_visibleScale.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with β hβ herr hπ hone
  refine ⟨hβ, hπ, hone.le, ?_⟩
  nlinarith only [herr]

/-- Source post-merge center displacement. Entry caps produce all exterior
barriers, and entry cutoff diameters produce the literal initial normalized
means. The estimate holds at every point of the closed original-time interval. -/
theorem post_merge_centers (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (CStar : ℝ) (hCStar : 0 < CStar) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 4),
      ∀ (model : Model) (k : Fin N) (X : ℝ → Configuration n d), Solves model β X →
      ∀ a : ℝ, 0 ≤ a →
      (∀ (D : Block n) (hD : D ∈ T.partition k.castSucc), ∀ i ∈ D,
        angularDist (X a i) (C (T.currentNode k D hD)).center ≤
          (C (T.currentNode k D hD)).radius + M * enlargementScale β) →
      (∀ D ∈ T.partition k.castSucc, ∀ i ∈ D, ∀ j ∈ D,
        angularDist (X a i) (X a j) ≤ clockCutoff β) →
      ∀ (D : Block n) (hD : D ∈ T.partition k.castSucc),
        let hne := T.block_nonempty _ _ hD
        BlockGeometry.blockMean D hne (X a) ≠ 0 ∧ ∃ z₀ : Sphere d,
          z₀.val = ‖BlockGeometry.blockMean D hne (X a)‖⁻¹ • BlockGeometry.blockMean D hne (X a) ∧
          ∀ t ∈ Icc a (a + CStar * β),
            (∀ i ∈ D, angularDist (X t i) z₀ < 4 * clockCutoff β) ∧
            BlockGeometry.blockMean D hne (X t) ≠ 0 ∧ ∃ z : Sphere d,
              z.val = ‖BlockGeometry.blockMean D hne (X t)‖⁻¹ • BlockGeometry.blockMean D hne (X t) ∧
              angularDist z z₀ ≤ 4 * clockCutoff β := by
  obtain ⟨G, hG, hcaps⟩ := PostMergeCaps.post_merge_caps T hN C hC CStar hCStar
  obtain ⟨S, hS⟩ := eventually_atTop.mp
    (eventually_center_parameters n CStar (treeMargin hN C) hCStar (treeMargin_pos hN C hC))
  refine ⟨max G S, hG.trans_le (le_max_left _ _), ?_⟩
  intro β hβ M hM model k X hX a ha hentry hdiam D hD
  obtain ⟨hβ1, hsmall, hscale, herror⟩ := hS β ((le_max_right _ _).trans hβ)
  have hβ0 := zero_lt_one.trans hβ1
  have hall := (hcaps β ((le_max_left _ _).trans hβ) M hM model k X hX a ha hentry).2
  let L := lowerBarrier C k - treeMargin hN C
  have hL := PostMergeGeometry.post_barrier_lower T hN C hC k
  have hExp : Real.exp (-β * L) ≤ Real.exp (-β * (7 * treeMargin hN C)) := by
    apply Real.exp_le_exp.mpr
    dsimp only [L]
    nlinarith only [mul_le_mul_of_nonneg_left hL hβ0.le]
  have herror' : (2 * n) * (a + CStar * β - a) * Real.exp (-β * L) < visibleScale β ^ 2 / 8 := by
    have hh := mul_le_mul_of_nonneg_left hExp
      (show (0 : ℝ) ≤ 2 * n * CStar * β by positivity)
    have heq : (2 * n) * (a + CStar * β - a) * Real.exp (-β * L) =
        2 * n * CStar * β * Real.exp (-β * L) := by ring
    rw [heq]
    exact hh.trans_lt herror
  exact center_displacement_of_separation model β hβ1 X hX D (T.block_nonempty _ _ hD)
    a (a + CStar * β) L ha (le_add_of_nonneg_right (mul_pos hCStar hβ0).le)
    hsmall hscale (hdiam D hD)
    (fun t ht => (hall t ⟨ht.1, ht.2.le⟩).2 D hD) herror'

end Metastability.PostMergeCenter
