import Metastability.BarycenterTrajectory
import Metastability.BarycenterScale

/-! Uniform active-collision motion of the actual representative barycenter.
All velocity estimates and clock regularity come from the literal source ODE;
no invariant, error equation, or regularity is assumed in the source export. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace NNReal
namespace Metastability.ActiveBarycenter
open Source AngularGeometry BarycenterFormula BarycenterTrajectory
open ActiveScales ActiveSourceLaw CapEnlargement
variable {n N d : ℕ}

/-- Ambient value of the source weighted spherical barycenter. Its equality to
the literal source construction is given below on the non-antipodal domain. -/
def representativeCenter (model : Model) (T : CollisionTree n N) (l : Fin N)
    (x : Configuration n d) (i j : Fin n) : Vector d :=
  vector (centerWeight model (T.right l) /
    (centerWeight model (T.left l) + centerWeight model (T.right l))) (x i).val (x j).val

theorem representativeCenter_eq_source (model : Model) (T : CollisionTree n N) (l : Fin N)
    (x : Configuration n d) (i j : Fin n) (hθ : angularDist (x i) (x j) < Real.pi) :
    representativeCenter model T l x i j =
      geodesicBarycenter (centerWeight model (T.left l)) (centerWeight model (T.right l))
        (centerWeight_pos model _ (T.block_nonempty _ _ (T.left_mem l)))
        (centerWeight_pos model _ (T.block_nonempty _ _ (T.right_mem l))) (x i) (x j) hθ :=
  vector_eq_source _ _ _ _ _ _ hθ

def motionRate (n : ℕ) (κ U L β : ℝ) : ℝ := 12 *
  (((5 * n + 10 * (n : ℝ) ^ 2) * β ^ (-(1 / 3 : ℝ)) * Real.log β) +
    (4 * Real.log β * (Real.exp (-(κ - U) * β) + n * Real.exp (-(L - U) * β))) /
      Real.sqrt (((2 / 5 : ℝ) * (2 - U)) * (Real.log β / β)))

theorem motionRate_nonneg (n : ℕ) (κ U L β : ℝ) (hβ : 1 < β) :
    0 ≤ motionRate n κ U L β := by
  have hlog := (Real.log_pos hβ).le
  have hp := (Real.rpow_pos_of_pos (zero_lt_one.trans hβ) (-(1 / 3 : ℝ))).le
  unfold motionRate
  positivity

theorem motionRate_tendsto (n : ℕ) (κ U L : ℝ)
    (hU : U < 2) (hκ : U < κ) (hL : U < L) :
    Tendsto (motionRate n κ U L) atTop (𝓝 0) :=
  BarycenterScale.active_rate_tendsto n κ U L hU hκ hL

/-- The sine bound is produced by the mesoscopic lower angle and upper barrier. -/
theorem active_angle_bounds (β U : ℝ) (hβ : 1 < β) (hU : U < 2)
    (hsmall : mesoscopicScale β ≤ 1) (p q : Sphere d)
    (hangle : mesoscopicScale β ≤ angularDist p q)
    (hupper : 1 - ⟪p.val, q.val⟫ ≤ U) :
    (0 < angularDist p q ∧ angularDist p q < Real.pi) ∧
    0 < Real.sqrt (((2 / 5 : ℝ) * (2 - U)) * (Real.log β / β)) ∧
    Real.sqrt (((2 / 5 : ℝ) * (2 - U)) * (Real.log β / β)) ≤ Real.sin (angularDist p q) := by
  have hβ0 : 0 < β := zero_lt_one.trans hβ
  have hlog := Real.log_pos hβ
  have hm : 0 < mesoscopicScale β := Real.sqrt_pos.mpr (div_pos hlog hβ0)
  have hpos := hm.trans_le hangle
  have hpi : angularDist p q < Real.pi := Real.arccos_lt_pi.mpr (by linarith only [hupper, hU])
  have hspos : 0 < Real.sin (angularDist p q) := Real.sin_pos_of_pos_of_lt_pi hpos hpi
  have hA : 0 < ((2 / 5 : ℝ) * (2 - U)) * (Real.log β / β) :=
    mul_pos (mul_pos (by norm_num) (sub_pos.mpr hU)) (div_pos hlog hβ0)
  have hsq := ActiveAngleScale.sine_sq_lower β U hβ hU hsmall p q hangle hupper
  rw [BarycenterDifferential.sine_sq p q] at hsq
  refine ⟨⟨hpos, hpi⟩, Real.sqrt_pos.mpr hA, ?_⟩
  exact (Real.sqrt_le_iff).mpr ⟨hspos.le, hsq⟩

/-- Quantitative endpoint variation along every closed active subinterval. -/
theorem interval_variation (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 4 < κ) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5), ∀ (model : Model) (l : Fin N)
      (X : ℝ → Configuration n d), Solves model β X →
      ∀ (shift : ℝ), 0 ≤ shift → ∀ (clock : ℝ → ℝ), ClockRelation β X shift clock →
      ∀ (i j : Fin n), i ∈ T.left l → j ∈ T.right l →
      ∀ (a b : ℝ), 0 ≤ a → a ≤ b →
      (∀ t ∈ Icc a b, StageHyp T C β κ M l (accelerated X shift clock t)) →
      (∀ t ∈ Icc a b, 1 - ⟪(accelerated X shift clock t i).val, (accelerated X shift clock t j).val⟫ ≤
        upperBarrier C l + 2 * treeMargin hN C) →
      (∀ t ∈ Icc a b, mesoscopicScale β ≤ angularDist (accelerated X shift clock t i) (accelerated X shift clock t j)) →
      ‖representativeCenter model T l (accelerated X shift clock b) i j -
        representativeCenter model T l (accelerated X shift clock a) i j‖ ≤
        motionRate n κ (upperBarrier C l + 2 * treeMargin hN C)
          (upperBarrier C l + 7 * treeMargin hN C) β * (b - a) := by
  obtain ⟨B, hB, hlaw⟩ := ActiveVectorLaw.static_reduced_pair T hN C hC κ hκ
  have hsmall : ∀ᶠ β : ℝ in atTop, mesoscopicScale β ≤ 1 :=
    (tendsto_mesoscopicScale.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
      (fun _ h => h.le)
  obtain ⟨V, hV⟩ := eventually_atTop.mp hsmall
  refine ⟨max B V, hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ M hM model l X hX shift hshift clock hc i j hi hj a b ha hab hstage hupper hangle
  have hβB := (le_max_left B V).trans hβ
  have hβ1 := hB.trans_le hβB
  have hmeso := hV β ((le_max_right B V).trans hβ)
  obtain ⟨_, _, _, _, hU⟩ := source_barrier_parameters T hN C hC κ hκ l
  let U := upperBarrier C l + 2 * treeMargin hN C
  let L := upperBarrier C l + 7 * treeMargin hN C
  let R := (5 * n + 10 * (n : ℝ) ^ 2) * β ^ (-(1 / 3 : ℝ)) * Real.log β
  let E := 4 * Real.log β * (Real.exp (-(κ - U) * β) + n * Real.exp (-(L - U) * β))
  let m := Real.sqrt (((2 / 5 : ℝ) * (2 - U)) * (Real.log β / β))
  have hgeom := fun t ht => active_angle_bounds β U hβ1 hU hmeso
    (accelerated X shift clock t i) (accelerated X shift clock t j) (hangle t ht) (hupper t ht)
  have hBne := T.block_nonempty _ _ (T.left_mem l)
  have hCne := T.block_nonempty _ _ (T.right_mem l)
  have hlog := (Real.log_pos hβ1).le
  have hp := (Real.rpow_pos_of_pos (zero_lt_one.trans hβ1) (-(1 / 3 : ℝ))).le
  apply variation_le model β hβ1 X hX shift hshift clock hc i j a b
    (centerWeight model (T.left l)) (centerWeight model (T.right l))
    (((T.right l).card : ℝ) / ActiveCoefficients.blockDenominator model (T.left l) * Real.log β)
    (((T.left l).card : ℝ) / ActiveCoefficients.blockDenominator model (T.right l) * Real.log β)
    R E m ha hab (centerWeight_pos model _ hBne) (centerWeight_pos model _ hCne)
    (weight_balance model _ _ hBne hCne (Real.log β))
    (by dsimp only [R]; positivity) (by dsimp only [E]; positivity)
    (hgeom a ⟨le_rfl, hab⟩).2.1 (fun t ht => (hgeom t ht).1) (fun t ht => (hgeom t ht).2.2)
  intro t ht
  have hh := hlaw β hβB M hM model l (accelerated X shift clock t) (hstage t ht) i j hi hj
    (hupper t ht) (hangle t ht)
  simpa only [norm_projectTangent, angularDist_comm (accelerated X shift clock t j)
    (accelerated X shift clock t i)] using hh

/-- Uniform vanishing center motion over the source's bounded active stage.
The threshold is chosen before the model, stage, trajectory, representatives,
and time interval. -/
theorem uniformly_small_variation (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 4 < κ)
    (H : ℝ) (hH : 0 < H) (ε : ℝ) (hε : 0 < ε) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5), ∀ (model : Model) (l : Fin N)
      (X : ℝ → Configuration n d), Solves model β X →
      ∀ (shift : ℝ), 0 ≤ shift → ∀ (clock : ℝ → ℝ), ClockRelation β X shift clock →
      ∀ (i j : Fin n), i ∈ T.left l → j ∈ T.right l →
      ∀ (a b : ℝ), 0 ≤ a → a ≤ b → b - a ≤ H →
      (∀ t ∈ Icc a b, StageHyp T C β κ M l (accelerated X shift clock t)) →
      (∀ t ∈ Icc a b, 1 - ⟪(accelerated X shift clock t i).val, (accelerated X shift clock t j).val⟫ ≤
        upperBarrier C l + 2 * treeMargin hN C) →
      (∀ t ∈ Icc a b, mesoscopicScale β ≤ angularDist (accelerated X shift clock t i) (accelerated X shift clock t j)) →
      ∀ t ∈ Icc a b,
      ‖representativeCenter model T l (accelerated X shift clock t) i j -
        representativeCenter model T l (accelerated X shift clock a) i j‖ < ε := by
  have hevent : ∀ᶠ β : ℝ in atTop, ∀ l : Fin N,
      motionRate n κ (upperBarrier C l + 2 * treeMargin hN C)
        (upperBarrier C l + 7 * treeMargin hN C) β < ε / (H) := by
    apply eventually_all.mpr
    intro l
    obtain ⟨_, hκU, hUL, _, hU⟩ := source_barrier_parameters T hN C hC κ hκ l
    exact (motionRate_tendsto n κ _ _ hU hκU hUL).eventually
      (gt_mem_nhds (div_pos hε hH))
  obtain ⟨V, hV⟩ := eventually_atTop.mp hevent
  obtain ⟨B, hB, hbound⟩ := interval_variation T hN C hC κ hκ
  refine ⟨max B V, hB.trans_le (le_max_left _ _), ?_⟩
  intro β hβ M hM model l X hX shift hshift clock hc i j hi hj a b ha hab hlength hstage hupper hangle t ht
  have hβB := (le_max_left B V).trans hβ
  have hβ1 := hB.trans_le hβB
  have hsub : Icc a t ⊆ Icc a b := fun u hu => ⟨hu.1, hu.2.trans ht.2⟩
  have hh := hbound β hβB M hM model l X hX shift hshift clock hc i j hi hj a t ha ht.1
    (fun u hu => hstage u (hsub hu)) (fun u hu => hupper u (hsub hu)) (fun u hu => hangle u (hsub hu))
  have hrate := hV β ((le_max_right B V).trans hβ) l
  have hr0 := motionRate_nonneg n κ (upperBarrier C l + 2 * treeMargin hN C)
    (upperBarrier C l + 7 * treeMargin hN C) β hβ1
  have htime : t - a ≤ H := by linarith only [ht.2, hlength]
  apply hh.trans_lt
  calc
    _ ≤ _ * (H) := mul_le_mul_of_nonneg_left htime hr0
    _ < (ε / (H)) * (H) := mul_lt_mul_of_pos_right hrate hH
    _ = ε := div_mul_cancel₀ ε hH.ne'

end Metastability.ActiveBarycenter
