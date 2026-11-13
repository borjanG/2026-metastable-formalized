import Metastability.BarycenterFormula
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Continuity of the literal geodesic barycenter, including the diagonal.
Uniform continuity holds on every fixed region away from antipodal pairs. -/
noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Metastability.BarycenterContinuity
open Source AngularGeometry BarycenterFormula
variable {d : ℕ}

theorem norm_vector_sub_left_le (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (p q : Sphere d) (hθ : angularDist p q < Real.pi) :
    ‖vector (b / (a + b)) p.val q.val - p.val‖ ≤ angularDist p q := by
  rw [vector_eq_point a b ha hb p q hθ]
  have hfrac : b / (a + b) ≤ 1 := (div_le_one (add_pos ha hb)).mpr (by linarith only [ha])
  calc
    _ ≤ angularDist (GeodesicBarycenter.point a b ha hb p q hθ) p := norm_sub_le_angularDist _ _
    _ = b / (a + b) * angularDist p q := by
      rw [angularDist_comm, GeodesicBarycenter.angularDist_point_left]
    _ ≤ angularDist p q := mul_le_of_le_one_left (angularDist_nonneg p q) hfrac

/-- The ambient formula is continuous along unit pairs even at coincidence. -/
theorem continuousOn_vector (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ContinuousOn (fun z : Sphere d × Sphere d => vector (b / (a + b)) z.1.val z.2.val)
      {z | angularDist z.1 z.2 < Real.pi} := by
  intro z hz
  by_cases he : z.1 = z.2
  · have hzero : angularDist z.1 z.2 = 0 := by rw [← he, angularDist_self]
    have hvzero : vector (b / (a + b)) z.1.val z.2.val = z.1.val := by
      rw [vector_eq_point a b ha hb z.1 z.2 hz]
      simpa only [← he] using congrArg Subtype.val (GeodesicBarycenter.point_self a b ha hb z.1 (by rw [angularDist_self]; exact Real.pi_pos))
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [hvzero]
    have hlim : Tendsto (fun w : Sphere d × Sphere d =>
        angularDist w.1 w.2 + ‖w.1.val - z.1.val‖)
        (𝓝[{w | angularDist w.1 w.2 < Real.pi}] z) (𝓝 0) := by
      have hcoord : Continuous (fun w : Sphere d × Sphere d => w.1.val) :=
        continuous_subtype_val.comp continuous_fst
      have hh : ContinuousAt (fun w : Sphere d × Sphere d =>
          angularDist w.1 w.2 + ‖w.1.val - z.1.val‖) z :=
        continuous_angularDist.continuousAt.add
          ((hcoord.continuousAt.sub continuousAt_const).norm)
      have hval : angularDist z.1 z.2 + ‖z.1.val - z.1.val‖ = 0 := by rw [hzero, sub_self, norm_zero, add_zero]
      have hht := hh.tendsto
      simp only [hval] at hht
      exact hht.mono_left inf_le_left
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hlim
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (norm_sub_le_norm_sub_add_norm_sub (vector (b / (a + b)) w.1.val w.2.val) w.1.val z.1.val).trans
      (add_le_add (norm_vector_sub_left_le a b ha hb w.1 w.2 hw) le_rfl)
  · have hsin := GeodesicBarycenter.sin_angularDist_ne_zero he hz
    have hρ : Continuous (fun w : Sphere d × Sphere d => ⟪w.1.val, w.2.val⟫) :=
      (continuous_subtype_val.comp continuous_fst).inner (continuous_subtype_val.comp continuous_snd)
    have hθ : ContinuousAt (fun w : Sphere d × Sphere d => angularDist w.1 w.2) z :=
      continuous_angularDist.continuousAt
    have hcos : ContinuousAt (fun w : Sphere d × Sphere d => Real.cos (b / (a + b) * angularDist w.1 w.2)) z :=
      Real.continuous_cos.continuousAt.comp (hθ.const_mul _)
    have hrat : ContinuousAt (fun w : Sphere d × Sphere d =>
        Real.sin (b / (a + b) * angularDist w.1 w.2) / Real.sin (angularDist w.1 w.2)) z :=
      (Real.continuous_sin.continuousAt.comp (hθ.const_mul _)).div
        (Real.continuous_sin.continuousAt.comp hθ) hsin
    have horth : ContinuousAt (fun w : Sphere d × Sphere d =>
        w.2.val - ⟪w.1.val, w.2.val⟫ • w.1.val) z :=
      (continuous_subtype_val.comp continuous_snd).continuousAt.sub
      (hρ.continuousAt.smul (continuous_subtype_val.comp continuous_fst).continuousAt)
    exact ((hcos.smul (continuous_subtype_val.comp continuous_fst).continuousAt).add
      (hrat.smul horth)).continuousWithinAt

/-- The closed angular region is compact; no positive lower angle is needed. -/
theorem isCompact_angle_le (R : ℝ) :
    IsCompact {z : Sphere d × Sphere d | angularDist z.1 z.2 ≤ R} := by
  have hsphere : IsCompact {p : Vector d | ‖p‖ = 1} := by
    simpa only [Metric.sphere, dist_zero_right] using isCompact_sphere (0 : Vector d) 1
  letI : CompactSpace (Sphere d) := isCompact_iff_compactSpace.mp hsphere
  exact (isClosed_le continuous_angularDist continuous_const).isCompact

/-- Fixed positive weights give uniform continuity on every closed region
strictly below the antipodal angle. This includes all coincident pairs. -/
theorem uniformContinuousOn_vector (a b R : ℝ) (ha : 0 < a) (hb : 0 < b) (hR : R < Real.pi) :
    UniformContinuousOn (fun z : Sphere d × Sphere d => vector (b / (a + b)) z.1.val z.2.val)
      {z | angularDist z.1 z.2 ≤ R} :=
  (isCompact_angle_le R).uniformContinuousOn_of_continuous
    ((continuousOn_vector a b ha hb).mono (fun _ hz => lt_of_le_of_lt hz hR))

end Metastability.BarycenterContinuity
