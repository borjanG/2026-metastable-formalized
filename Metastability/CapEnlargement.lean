import Metastability.CapDistances
import Metastability.GeodesicBarycenter
import Metastability.ContractionScale

/-!
# Angular cap enlargements and perturbations of source barriers

The enlarged cap has its literal enlarged radius. A point in it is within the
enlargement distance of an original-cap point, proved using the source spherical
interpolation. This argument includes one-dimensional ambient spaces and
zero-radius caps; it does not assume a connected sphere.
-/

noncomputable section
open Filter Set
open scoped Topology RealInnerProductSpace

namespace Metastability.CapEnlargement

open Source AngularGeometry
variable {d : ℕ}

theorem abs_angularDist_sub_le (x y x₀ y₀ : Sphere d) :
    |angularDist x y - angularDist x₀ y₀| ≤ angularDist x x₀ + angularDist y y₀ := by
  have h₁ := angularDist_triangle x x₀ y
  have h₂ := angularDist_triangle x₀ y₀ y
  have h₃ := angularDist_triangle x₀ x y₀
  have h₄ := angularDist_triangle x y y₀
  rw [angularDist_comm y₀ y] at h₂
  rw [angularDist_comm x₀ x] at h₃
  exact abs_le.mpr ⟨by linarith only [h₃, h₄], by linarith only [h₁, h₂]⟩

/-- The source cosine deficit is one-Lipschitz in the sum of endpoint
angular displacements. -/
theorem abs_deficit_sub_le (x y x₀ y₀ : Sphere d) :
    |(1 - Real.cos (angularDist x y)) - (1 - Real.cos (angularDist x₀ y₀))| ≤
      angularDist x x₀ + angularDist y y₀ := by
  rw [show (1 - Real.cos (angularDist x y)) - (1 - Real.cos (angularDist x₀ y₀)) =
    -(Real.cos (angularDist x y) - Real.cos (angularDist x₀ y₀)) by ring, abs_neg]
  exact (Real.abs_cos_sub_cos_le _ _).trans (abs_angularDist_sub_le x y x₀ y₀)

theorem abs_inner_deficit_sub_le (x y x₀ y₀ : Sphere d) :
    |(1 - ⟪x.val, y.val⟫) - (1 - ⟪x₀.val, y₀.val⟫)| ≤
      angularDist x x₀ + angularDist y y₀ := by
  simpa only [cos_angularDist] using abs_deficit_sub_le x y x₀ y₀

/-- Useful for points within twice the visible scale of their cap centers. -/
theorem abs_deficit_sub_le_four_mul (x y x₀ y₀ : Sphere d) (ε : ℝ)
    (hx : angularDist x x₀ ≤ 2 * ε) (hy : angularDist y y₀ ≤ 2 * ε) :
    |(1 - Real.cos (angularDist x y)) - (1 - Real.cos (angularDist x₀ y₀))| ≤ 4 * ε :=
  (abs_deficit_sub_le x y x₀ y₀).trans (by linarith only [hx, hy])

theorem min_barrier_le_deficit (C D : SphericalCap d) (x y : Sphere d)
    (hx : x ∈ C.carrier) (hy : y ∈ D.carrier) :
    1 - Real.cos (capMinDistance C D) ≤ 1 - Real.cos (angularDist x y) := by
  exact sub_le_sub_left (Real.cos_le_cos_of_nonneg_of_le_pi
    (CapDistances.capMinDistance_nonneg C D) (angularDist_le_pi x y)
    (CapDistances.capMinDistance_le_angle C D x y hx hy)) 1

theorem deficit_le_max_barrier (C D : SphericalCap d) (x y : Sphere d)
    (hx : x ∈ C.carrier) (hy : y ∈ D.carrier) :
    1 - Real.cos (angularDist x y) ≤ 1 - Real.cos (capMaxDistance C D) := by
  exact sub_le_sub_left (Real.cos_le_cos_of_nonneg_of_le_pi
    (angularDist_nonneg x y) (CapDistances.capMaxDistance_le_pi C D)
    (CapDistances.angle_le_capMaxDistance C D x y hx hy)) 1

/-- The exact supremum appearing in the manuscript is bounded by the
cosine deficit at the maximum angular cap distance. -/
theorem sup_deficits_le_max_barrier (C D : SphericalCap d) :
    sSup {z : ℝ | ∃ x ∈ C.carrier, ∃ y ∈ D.carrier,
      z = 1 - Real.cos (angularDist x y)} ≤ 1 - Real.cos (capMaxDistance C D) := by
  have hnonempty : ({z : ℝ | ∃ x ∈ C.carrier, ∃ y ∈ D.carrier,
      z = 1 - Real.cos (angularDist x y)} : Set ℝ).Nonempty :=
    ⟨1 - Real.cos (angularDist C.center D.center),
      C.center, cap_center_mem C, D.center, cap_center_mem D, rfl⟩
  apply csSup_le hnonempty
  rintro z ⟨x, hx, y, hy, rfl⟩
  exact deficit_le_max_barrier C D x y hx hy

/-- Literal enlargement, defined when its radius is still below a hemisphere. -/
def enlarge (C : SphericalCap d) (η : ℝ) (hη : 0 ≤ η)
    (hsmall : C.radius + η < Real.pi / 2) : SphericalCap d :=
  ⟨C.center, C.radius + η, add_nonneg C.radius_nonneg hη, hsmall⟩

theorem mem_enlarge_iff (C : SphericalCap d) (η : ℝ) (hη : 0 ≤ η)
    (hsmall : C.radius + η < Real.pi / 2) (x : Sphere d) :
    x ∈ (enlarge C η hη hsmall).carrier ↔ angularDist x C.center ≤ C.radius + η := Iff.rfl

theorem carrier_subset_enlarge (C : SphericalCap d) (η : ℝ) (hη : 0 ≤ η)
    (hsmall : C.radius + η < Real.pi / 2) :
    C.carrier ⊆ (enlarge C η hη hsmall).carrier := by
  intro x hx
  exact (show angularDist x C.center ≤ C.radius from hx).trans (le_add_of_nonneg_right hη)

/-- Radial retraction to the original cap. The zero-radius case is explicit;
positive radii use interpolation only between points with angle below pi. -/
theorem exists_near_original (C : SphericalCap d) (η : ℝ) (hη : 0 ≤ η)
    (hsmall : C.radius + η < Real.pi / 2) (x : Sphere d)
    (hx : x ∈ (enlarge C η hη hsmall).carrier) :
    ∃ x₀ ∈ C.carrier, angularDist x x₀ ≤ η := by
  by_cases hmem : x ∈ C.carrier
  · exact ⟨x, hmem, by simpa only [angularDist_self] using hη⟩
  change angularDist x C.center ≤ C.radius + η at hx
  by_cases hr : C.radius = 0
  · exact ⟨C.center, cap_center_mem C, by simpa only [hr, zero_add] using hx⟩
  have hr0 : 0 < C.radius := lt_of_le_of_ne C.radius_nonneg (Ne.symm hr)
  have hθr : C.radius < angularDist C.center x := by
    rw [angularDist_comm C.center x]
    exact lt_of_not_ge hmem
  have hθ0 : 0 < angularDist C.center x := hr0.trans hθr
  have hθπ : angularDist C.center x < Real.pi := by
    rw [angularDist_comm C.center x]
    linarith only [hx, hsmall, Real.pi_pos]
  let z := GeodesicBarycenter.point (angularDist C.center x - C.radius) C.radius
    (sub_pos.mpr hθr) hr0 C.center x hθπ
  have hsum : angularDist C.center x - C.radius + C.radius = angularDist C.center x := by ring
  have hleft : angularDist C.center z = C.radius := by
    rw [GeodesicBarycenter.angularDist_point_left, hsum]
    exact div_mul_cancel₀ C.radius hθ0.ne'
  have hright : angularDist z x = angularDist C.center x - C.radius := by
    rw [GeodesicBarycenter.angularDist_point_right, hsum]
    exact div_mul_cancel₀ _ hθ0.ne'
  refine ⟨z, ?_, ?_⟩
  · change angularDist z C.center ≤ C.radius
    rw [angularDist_comm z C.center, hleft]
  · rw [angularDist_comm x z, hright, angularDist_comm C.center x]
    linarith only [hx]

theorem capMinDistance_enlarge_le (C D : SphericalCap d) (η : ℝ) (hη : 0 ≤ η)
    (hC : C.radius + η < Real.pi / 2) (hD : D.radius + η < Real.pi / 2) :
    capMinDistance (enlarge C η hη hC) (enlarge D η hη hD) ≤ capMinDistance C D := by
  apply le_csInf (CapDistances.values_nonempty C D)
  rintro r ⟨x, hx, y, hy, rfl⟩
  exact CapDistances.capMinDistance_le_angle _ _ x y
    (carrier_subset_enlarge C η hη hC hx) (carrier_subset_enlarge D η hη hD hy)

theorem capMinDistance_sub_le_enlarge (C D : SphericalCap d) (η : ℝ) (hη : 0 ≤ η)
    (hC : C.radius + η < Real.pi / 2) (hD : D.radius + η < Real.pi / 2) :
    capMinDistance C D - 2 * η ≤ capMinDistance (enlarge C η hη hC) (enlarge D η hη hD) := by
  apply le_csInf (CapDistances.values_nonempty _ _)
  rintro r ⟨x, hx, y, hy, rfl⟩
  obtain ⟨x₀, hx₀, hxx₀⟩ := exists_near_original C η hη hC x hx
  obtain ⟨y₀, hy₀, hyy₀⟩ := exists_near_original D η hη hD y hy
  have hmin := CapDistances.capMinDistance_le_angle C D x₀ y₀ hx₀ hy₀
  have hpert := (abs_le.mp (abs_angularDist_sub_le x y x₀ y₀)).1
  linarith only [hmin, hpert, hxx₀, hyy₀]

theorem capMaxDistance_le_enlarge (C D : SphericalCap d) (η : ℝ) (hη : 0 ≤ η)
    (hC : C.radius + η < Real.pi / 2) (hD : D.radius + η < Real.pi / 2) :
    capMaxDistance C D ≤ capMaxDistance (enlarge C η hη hC) (enlarge D η hη hD) := by
  apply csSup_le (CapDistances.values_nonempty C D)
  rintro r ⟨x, hx, y, hy, rfl⟩
  exact CapDistances.angle_le_capMaxDistance _ _ x y
    (carrier_subset_enlarge C η hη hC hx) (carrier_subset_enlarge D η hη hD hy)

theorem capMaxDistance_enlarge_le_add (C D : SphericalCap d) (η : ℝ) (hη : 0 ≤ η)
    (hC : C.radius + η < Real.pi / 2) (hD : D.radius + η < Real.pi / 2) :
    capMaxDistance (enlarge C η hη hC) (enlarge D η hη hD) ≤ capMaxDistance C D + 2 * η := by
  apply csSup_le (CapDistances.values_nonempty _ _)
  rintro r ⟨x, hx, y, hy, rfl⟩
  obtain ⟨x₀, hx₀, hxx₀⟩ := exists_near_original C η hη hC x hx
  obtain ⟨y₀, hy₀, hyy₀⟩ := exists_near_original D η hη hD y hy
  have hmax := CapDistances.angle_le_capMaxDistance C D x₀ y₀ hx₀ hy₀
  have hpert := (abs_le.mp (abs_angularDist_sub_le x y x₀ y₀)).2
  linarith only [hmax, hpert, hxx₀, hyy₀]

theorem min_barrier_enlarge_lower (C D : SphericalCap d) (η : ℝ) (hη : 0 ≤ η)
    (hC : C.radius + η < Real.pi / 2) (hD : D.radius + η < Real.pi / 2) :
    1 - Real.cos (capMinDistance C D) - 2 * η ≤
      1 - Real.cos (capMinDistance (enlarge C η hη hC) (enlarge D η hη hD)) := by
  have hmin := capMinDistance_enlarge_le C D η hη hC hD
  have hnear := capMinDistance_sub_le_enlarge C D η hη hC hD
  have hcos := Real.abs_cos_sub_cos_le
    (capMinDistance (enlarge C η hη hC) (enlarge D η hη hD)) (capMinDistance C D)
  rw [abs_of_nonpos (sub_nonpos.mpr hmin)] at hcos
  have hc := (abs_le.mp hcos).2
  linarith only [hnear, hc]

theorem max_barrier_enlarge_upper (C D : SphericalCap d) (η : ℝ) (hη : 0 ≤ η)
    (hC : C.radius + η < Real.pi / 2) (hD : D.radius + η < Real.pi / 2) :
    1 - Real.cos (capMaxDistance (enlarge C η hη hC) (enlarge D η hη hD)) ≤
      1 - Real.cos (capMaxDistance C D) + 2 * η := by
  have hmax := capMaxDistance_le_enlarge C D η hη hC hD
  have hnear := capMaxDistance_enlarge_le_add C D η hη hC hD
  have hcos := Real.abs_cos_sub_cos_le
    (capMaxDistance (enlarge C η hη hC) (enlarge D η hη hD)) (capMaxDistance C D)
  rw [abs_of_nonneg (sub_nonneg.mpr hmax)] at hcos
  have hc := (abs_le.mp hcos).1
  linarith only [hnear, hc]

/-- The literal real-temperature enlargement scale beta to the minus quarter. -/
def enlargementScale (β : ℝ) : ℝ := β ^ (-(1 / 4 : ℝ))

/-- A uniform source geometric constant for all M in [0,2N+5]. -/
def geometryConstant (N : ℕ) : ℝ := 2 * (2 * (N : ℝ) + 5)

theorem geometryConstant_pos (N : ℕ) : 0 < geometryConstant N := by
  unfold geometryConstant
  positivity

theorem enlargement_error_le (N : ℕ) {β M : ℝ} (hβ : 0 < β)
    (hM : M ≤ 2 * (N : ℝ) + 5) :
    2 * (M * enlargementScale β) ≤ geometryConstant N * enlargementScale β := by
  have h := mul_le_mul_of_nonneg_right hM (Real.rpow_pos_of_pos hβ (-(1 / 4 : ℝ))).le
  change M * enlargementScale β ≤ (2 * (N : ℝ) + 5) * enlargementScale β at h
  unfold geometryConstant
  linarith only [h]

theorem enlargementScale_pos {β : ℝ} (hβ : 0 < β) : 0 < enlargementScale β :=
  Real.rpow_pos_of_pos hβ _

theorem tendsto_enlargementScale : Tendsto enlargementScale atTop (𝓝 0) := by
  exact tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)

variable {n N : ℕ} {T : CollisionTree n N}

/-- The smaller of the two source separation gaps at one collision stage. -/
def stageGap (C : TreeCaps T d) (l : Fin N) : ℝ :=
  min (lowerBarrier C l - previousUpperBarrier C l) (outsideBarrier C l - upperBarrier C l)

/-- The source Delta_tree: one eighth of the minimum of both gaps over all
collision stages. Nonemptiness is supplied by the source assumption N > 0. -/
def treeMargin (hN : 0 < N) (C : TreeCaps T d) : ℝ :=
  (Finset.univ.image (stageGap C)).min'
    (Finset.Nonempty.image ⟨⟨0, hN⟩, Finset.mem_univ _⟩ (stageGap C)) / 8

theorem treeMargin_pos (hN : 0 < N) (C : TreeCaps T d) (hC : StrictlyPrepared C) :
    0 < treeMargin hN C := by
  have hmin : 0 < (Finset.univ.image (stageGap C)).min'
      (Finset.Nonempty.image ⟨⟨0, hN⟩, Finset.mem_univ _⟩ (stageGap C)) := by
    obtain ⟨l, _, heq⟩ := Finset.mem_image.mp (Finset.min'_mem
      (Finset.univ.image (stageGap C))
      (Finset.Nonempty.image ⟨⟨0, hN⟩, Finset.mem_univ _⟩ (stageGap C)))
    rw [← heq]
    obtain ⟨_, _, _, hprevious, _, houtside⟩ := hC.2 l
    exact lt_min (sub_pos.mpr hprevious) (sub_pos.mpr houtside)
  exact div_pos hmin (by norm_num)

theorem treeMargin_gaps (hN : 0 < N) (C : TreeCaps T d) (l : Fin N) :
    previousUpperBarrier C l + 8 * treeMargin hN C ≤ lowerBarrier C l ∧
      upperBarrier C l + 8 * treeMargin hN C ≤ outsideBarrier C l := by
  have hb : (Finset.univ.image (stageGap C)).min'
      (Finset.Nonempty.image ⟨⟨0, hN⟩, Finset.mem_univ _⟩ (stageGap C)) ≤ stageGap C l :=
    Finset.min'_le _ _ (Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩)
  have hl := hb.trans (min_le_left _ _)
  have hr := hb.trans (min_le_right _ _)
  unfold treeMargin
  constructor <;> linarith only [hl, hr]

/-- A simultaneous literal enlargement of proper-node caps. Root caps are
neither introduced nor needed. -/
def enlargeFamily (C : TreeCaps T d) (η : ℝ) (hη : 0 ≤ η)
    (hsmall : ∀ A, (C A).radius + η < Real.pi / 2) : TreeCaps T d :=
  fun A => enlarge (C A) η hη (hsmall A)

/-- Uniform radius and barrier-error control over all proper nodes and all
source enlargement parameters 0 <= M <= 2N+5. -/
theorem eventually_uniform_enlargement (C : TreeCaps T d) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ β : ℝ in atTop, 1 < β ∧ ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5),
      0 ≤ M * enlargementScale β ∧
      (∀ A, (C A).radius + M * enlargementScale β < Real.pi / 2) ∧
      2 * (M * enlargementScale β) ≤ δ := by
  classical
  letI : Fintype T.ProperNode := Fintype.ofFinite T.ProperNode
  have hlim : Tendsto (fun β : ℝ => (2 * (N : ℝ) + 5) * enlargementScale β)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_enlargementScale.const_mul (2 * (N : ℝ) + 5)
  have hcaps : ∀ᶠ β : ℝ in atTop, ∀ A : T.ProperNode,
      (2 * (N : ℝ) + 5) * enlargementScale β < Real.pi / 2 - (C A).radius := by
    apply eventually_all.mpr
    intro A
    exact hlim.eventually (gt_mem_nhds (sub_pos.mpr (C A).radius_lt_half_pi))
  have herr : ∀ᶠ β : ℝ in atTop,
      (2 * (N : ℝ) + 5) * enlargementScale β < δ / 2 :=
    hlim.eventually (gt_mem_nhds (half_pos hδ))
  filter_upwards [eventually_gt_atTop (1 : ℝ), hcaps, herr] with β hβ hc he
  refine ⟨hβ, ?_⟩
  intro M hM
  have hscale := (enlargementScale_pos (lt_trans zero_lt_one hβ)).le
  have hMbound := mul_le_mul_of_nonneg_right hM.2 hscale
  refine ⟨mul_nonneg hM.1 hscale, ?_, ?_⟩
  · intro A
    linarith only [hMbound, hc A]
  · linarith only [hMbound, he]

/-- A uniformly enlarged proper-node family with its exact centers and radii,
and simultaneous source barrier estimates for every pair of proper nodes. -/
theorem exists_uniform_enlarged_family (C : TreeCaps T d) (δ : ℝ) (hδ : 0 < δ) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀, ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5),
      ∃ E : TreeCaps T d,
        (∀ A, (E A).center = (C A).center ∧
          (E A).radius = (C A).radius + M * enlargementScale β) ∧
        2 * (M * enlargementScale β) ≤ δ ∧
        ∀ A B,
          1 - Real.cos (capMinDistance (C A) (C B)) - 2 * (M * enlargementScale β) ≤
            1 - Real.cos (capMinDistance (E A) (E B)) ∧
          1 - Real.cos (capMaxDistance (E A) (E B)) ≤
            1 - Real.cos (capMaxDistance (C A) (C B)) + 2 * (M * enlargementScale β) := by
  obtain ⟨B, hB⟩ := eventually_atTop.mp (eventually_uniform_enlargement C δ hδ)
  refine ⟨max B 2, lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro β hβ M hM
  obtain ⟨hη, hsmall, herr⟩ := (hB β ((le_max_left _ _).trans hβ)).2 M hM
  refine ⟨enlargeFamily C (M * enlargementScale β) hη hsmall,
    fun A => ⟨rfl, rfl⟩, herr, ?_⟩
  intro A D
  have hmin := min_barrier_enlarge_lower (C A) (C D) (M * enlargementScale β)
    hη (hsmall A) (hsmall D)
  have hmax := max_barrier_enlarge_upper (C A) (C D) (M * enlargementScale β)
    hη (hsmall A) (hsmall D)
  exact ⟨hmin, hmax⟩

end Metastability.CapEnlargement
