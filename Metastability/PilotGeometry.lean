import Metastability.SourceDefinitions
import Metastability.PilotCutoff
import Metastability.ScalarClock
import Metastability.TwoParticle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Angular and scalar coordinates for the two-particle pilot

These identities connect the source angular cutoff, the half-angle profile,
and the scalar odds. They do not assert existence of a hitting time.
-/

noncomputable section
open scoped RealInnerProductSpace

namespace Metastability.PilotGeometry

/-- The two literal forms of the source cutoff agree (including their totalized values). -/
theorem clockCutoff_eq_angularCutoff (β : ℝ) :
    Source.clockCutoff β = PilotCutoff.angularCutoff β := by
  simp only [Source.clockCutoff, Source.visibleScale, PilotCutoff.angularCutoff,
    one_div, Real.sqrt_inv]
  ring

/-- Angular threshold comparisons reverse their scalar-product comparisons. -/
theorem lt_arccos_iff {ρ h : ℝ} (hρl : -1 ≤ ρ) (hρu : ρ ≤ 1)
    (hh0 : 0 ≤ h) (hhπ : h ≤ Real.pi) :
    h < Real.arccos ρ ↔ ρ < Real.cos h := by
  constructor
  · intro hlt
    simpa only [Real.cos_arccos hρl hρu] using
      Real.cos_lt_cos_of_nonneg_of_le_pi hh0 (Real.arccos_le_pi ρ) hlt
  · intro hlt
    by_contra hn
    have hc := Real.cos_le_cos_of_nonneg_of_le_pi (Real.arccos_nonneg ρ) hhπ
      (le_of_not_gt hn)
    rw [Real.cos_arccos hρl hρu] at hc
    exact (not_lt_of_ge hc) hlt

/-- Exact inversion at a threshold in the principal angular range. -/
theorem arccos_eq_iff {ρ h : ℝ} (hρl : -1 ≤ ρ) (hρu : ρ ≤ 1)
    (hh0 : 0 ≤ h) (hhπ : h ≤ Real.pi) :
    Real.arccos ρ = h ↔ ρ = Real.cos h := by
  constructor
  · intro he
    rw [← he, Real.cos_arccos hρl hρu]
  · intro he
    rw [he, Real.arccos_cos hh0 hhπ]

/-- The squared half-angle tangent equals the scalar odds below the antipode. -/
theorem odds_cos_eq_tan_half_sq {h : ℝ} (hh0 : 0 ≤ h) (hhπ : h < Real.pi) :
    ScalarClock.odds (Real.cos h) = Real.tan (h / 2) ^ 2 := by
  have hc : -1 < Real.cos h := by
    simpa only [Real.cos_pi] using
      Real.cos_lt_cos_of_nonneg_of_le_pi hh0 le_rfl hhπ
  have hf := Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq h (by linarith)
  have hf' := (eq_div_iff (by positivity : (1 : ℝ) + Real.tan (h / 2) ^ 2 ≠ 0)).mp hf
  unfold ScalarClock.odds
  apply (div_eq_iff (by linarith : 1 + Real.cos h ≠ 0)).mpr
  nlinarith [hf']

/-- The half-angle parameter is strictly positive for any angle strictly between zero and pi. -/
theorem tan_half_pos {h : ℝ} (hh0 : 0 < h) (hhπ : h < Real.pi) :
    0 < Real.tan (h / 2) :=
  Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith)

/-- The scalar initial condition used by the pilot, derived from the initial correlation. -/
theorem odds_eq_tan_arccos_half_sq {ρ : ℝ} (hρl : -1 < ρ) (hρu : ρ ≤ 1) :
    ScalarClock.odds ρ = Real.tan (Real.arccos ρ / 2) ^ 2 := by
  have he := odds_cos_eq_tan_half_sq (Real.arccos_nonneg ρ) (Real.arccos_lt_pi.mpr hρl)
  simpa only [Real.cos_arccos hρl.le hρu] using he

theorem tan_arccos_half_pos {ρ : ℝ} (hρl : -1 < ρ) (hρu : ρ < 1) :
    0 < Real.tan (Real.arccos ρ / 2) :=
  tan_half_pos (Real.arccos_pos.mpr hρu) (Real.arccos_lt_pi.mpr hρl)

/-- Non-antipodal distinct unit vectors give the positive half-angle parameter
and its exact initial-odds identity without any dynamical premise. -/
theorem initial_halfAngle_spec {d : ℕ} (x y : Source.Sphere d)
    (hne : x ≠ y) (hanti : x.val ≠ -y.val) :
    0 < Real.tan (Source.angularDist x y / 2) ∧
      ScalarClock.odds ⟪x.val, y.val⟫ = Real.tan (Source.angularDist x y / 2) ^ 2 := by
  have hrle := neg_one_le_real_inner_of_norm_eq_one x.property y.property
  have hrne : ⟪x.val, y.val⟫ ≠ -1 := by
    intro he
    exact hanti ((inner_eq_neg_one_iff_of_norm_eq_one x.property y.property).mp he)
  have hrl : -1 < ⟪x.val, y.val⟫ := lt_of_le_of_ne hrle (Ne.symm hrne)
  have hru : ⟪x.val, y.val⟫ < 1 :=
    (inner_lt_one_iff_real_of_norm_eq_one x.property y.property).mpr
      (fun he => hne (Subtype.ext he))
  exact ⟨tan_arccos_half_pos hrl hru, odds_eq_tan_arccos_half_sq hrl hru.le⟩

/-- Source angular eligibility in the scalar correlation coordinate. -/
theorem cutoff_lt_angularDist_iff {d : ℕ} (β : ℝ) (x y : Source.Sphere d)
    (hh0 : 0 ≤ Source.clockCutoff β) (hhπ : Source.clockCutoff β ≤ Real.pi) :
    Source.clockCutoff β < Source.angularDist x y ↔
      ⟪x.val, y.val⟫ < Real.cos (Source.clockCutoff β) :=
  lt_arccos_iff (neg_one_le_real_inner_of_norm_eq_one x.property y.property)
    (real_inner_le_one_of_norm_eq_one x.property y.property) hh0 hhπ

/-- The exact source cutoff also has the profile's cutoff odds. -/
theorem odds_cos_clockCutoff {β : ℝ} (hβ : 1 < β)
    (hhπ : Source.clockCutoff β < Real.pi) :
    ScalarClock.odds (Real.cos (Source.clockCutoff β)) =
      PilotCutoff.cutoffTangent β ^ 2 := by
  rw [clockCutoff_eq_angularCutoff] at hhπ ⊢
  exact odds_cos_eq_tan_half_sq (PilotCutoff.angularCutoff_pos hβ).le hhπ

/-- The odds recover the squared half-angle from the rational profile exactly. -/
theorem odds_cosineProfile (a β t : ℝ) :
    ScalarClock.odds (PilotAsymptotics.cosineProfile a β t) =
      PilotAsymptotics.halfAngle a β t ^ 2 := by
  unfold ScalarClock.odds PilotAsymptotics.cosineProfile
  have hp : (1 : ℝ) + PilotAsymptotics.halfAngle a β t ^ 2 ≠ 0 := by positivity
  have hd : 1 + (1 - PilotAsymptotics.halfAngle a β t ^ 2) /
      (1 + PilotAsymptotics.halfAngle a β t ^ 2) ≠ 0 := by
    field_simp [hp]
    norm_num
    exact hp
  apply (div_eq_iff hd).mpr
  field_simp
  ring

/-- At the algebraic crossing time, the correlation profile has the exact source cutoff. -/
theorem cosineProfile_cutoffTime {a β : ℝ} (ha : 0 < a) (hβ : 1 < β)
    (hhπ : Source.clockCutoff β < Real.pi) :
    PilotAsymptotics.cosineProfile a β (PilotCutoff.cutoffTime a β) =
      Real.cos (Source.clockCutoff β) := by
  rw [clockCutoff_eq_angularCutoff] at hhπ ⊢
  have hp := PilotCutoff.angularCutoff_pos hβ
  have hq : 0 < PilotCutoff.cutoffTangent β := tan_half_pos hp hhπ
  have hc : -1 < Real.cos (PilotCutoff.angularCutoff β) := by
    simpa only [Real.cos_pi] using
      Real.cos_lt_cos_of_nonneg_of_le_pi hp.le le_rfl hhπ
  rw [PilotAsymptotics.cosineProfile, PilotCutoff.halfAngle_cutoffTime ha hβ hq]
  exact (Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq _ (by linarith)).symm

/-- Equality with the cutoff identifies the unique algebraic profile time. -/
theorem cosineProfile_eq_cos_clockCutoff_iff {a β t : ℝ} (ha : 0 < a) (hβ : 1 < β)
    (hhπ : Source.clockCutoff β < Real.pi) :
    PilotAsymptotics.cosineProfile a β t = Real.cos (Source.clockCutoff β) ↔
      t = PilotCutoff.cutoffTime a β := by
  have hb : 0 < β := lt_trans zero_lt_one hβ
  have hq : 0 < PilotCutoff.cutoffTangent β := by
    apply tan_half_pos (PilotCutoff.angularCutoff_pos hβ)
    simpa only [clockCutoff_eq_angularCutoff] using hhπ
  constructor
  · intro he
    have ho := congrArg ScalarClock.odds he
    rw [odds_cosineProfile, odds_cos_clockCutoff hβ hhπ] at ho
    have hp : 0 < PilotAsymptotics.halfAngle a β t :=
      mul_pos ha (Real.rpow_pos_of_pos hb _)
    have heq : PilotAsymptotics.halfAngle a β t = PilotCutoff.cutoffTangent β := by
      nlinarith [ho]
    rw [← PilotCutoff.halfAngle_cutoffTime ha hβ hq] at heq
    simp only [PilotAsymptotics.halfAngle, mul_right_inj' ha.ne'] at heq
    have he := (Real.rpow_right_inj hb (ne_of_gt hβ)).mp heq
    linarith
  · rintro rfl
    exact cosineProfile_cutoffTime ha hβ hhπ

/-- The full source energy specialized to two labels is exactly the four-term pilot energy. -/
theorem source_energy_eq_twoParticleEnergy {d : ℕ} (β : ℝ)
    (x : Source.Configuration 2 d) :
    Source.energy β x = TwoParticle.twoParticleEnergy β (x 0).val (x 1).val := by
  simp only [Source.energy, Fin.sum_univ_two, TwoParticle.twoParticleEnergy]
  norm_num
  ring

end Metastability.PilotGeometry
