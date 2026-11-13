import Metastability.PlateauClockTransfer
import Metastability.PlateauCapGeometry
import Metastability.PlateauCapScale
import Metastability.PlateauScalar
import Metastability.CapNoExit

/-! Strict improvement of stopped plateau cap bounds from the actual source
ODE, source clock, and literal prepared-tree geometry. -/

noncomputable section
open Filter Set
open scoped Topology RealInnerProductSpace

namespace Metastability.PlateauCaps
open Source CapEnlargement ActiveSourceLaw
variable {n N d : ℕ}

theorem accelerated_cap_drift (model : Model) (β : ℝ) (hβ : 0 ≤ β)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (shift : ℝ) (hshift : 0 ≤ shift) (clock : ℝ → ℝ) (hc : ClockRelation β X shift clock)
    (D : Block n) (hD : D.Nonempty) (w : Sphere d)
    (a b r R L : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hr0 : 0 ≤ r)
    (hrR : r ≤ R) (hRπ : R < Real.pi / 2)
    (hentry : ∀ i ∈ D, angularDist (accelerated X shift clock a i) w ≤ r)
    (hcap : ∀ t ∈ Ico a b, ∀ i ∈ D, angularDist (accelerated X shift clock t i) w ≤ R)
    (hsep : ∀ t ∈ Ico a b, ∀ i ∈ D, ∀ j ∉ D,
      L ≤ 1 - ⟪(accelerated X shift clock t i).val, (accelerated X shift clock t j).val⟫) :
    ∀ t ∈ Icc a b, ∀ i ∈ D,
      Real.cos r - (2 * n) * (clock t - clock a) * Real.exp (-β * L) ≤
        ⟪(accelerated X shift clock t i).val, w.val⟫ := by
  have ha0 : 0 ≤ shift + clock a := add_nonneg hshift (hc.1.2.1 a ha)
  have hR0 := hr0.trans hrR
  have hRpi : R ≤ Real.pi := by linarith only [hRπ, Real.pi_pos]
  have hrpi := hrR.trans hRpi
  have hcos : 0 < Real.cos R := Real.cos_pos_of_mem_Ioo
    ⟨by linarith only [hR0, Real.pi_pos], hRπ⟩
  have hpositive : ∀ u ∈ Ico (shift + clock a) (shift + clock b), ∀ i ∈ D,
      0 ≤ ⟪(X u i).val, w.val⟫ := by
    intro u hu i hi
    obtain ⟨t, ht, heq⟩ := PlateauClockTransfer.exists_time_Ico hc ha hab hu
    have hh := (AngularGeometry.angularDist_le_iff_inner _ _ hR0 hRpi).mp (hcap t ht i hi)
    rw [heq]
    exact hcos.le.trans hh
  have hsep' : ∀ u ∈ Ico (shift + clock a) (shift + clock b), ∀ i ∈ D, ∀ j ∉ D,
      ⟪(X u i).val, (X u j).val⟫ ≤ 1 - L := by
    intro u hu i hi j hj
    obtain ⟨t, ht, heq⟩ := PlateauClockTransfer.exists_time_Ico hc ha hab hu
    have hh := hsep t ht i hi j hj
    rw [heq]
    change ⟪(accelerated X shift clock t i).val, (accelerated X shift clock t j).val⟫ ≤ 1 - L
    linarith only [hh]
  intro t ht i hi
  have hh := CapDrift.cap_drift_on_interval X hX hβ D hD w
    (shift + clock a) (shift + clock b) r L ha0 hr0 hrpi hentry hpositive hsep'
    (PlateauClockTransfer.shifted_clock_mem_Icc hc ha ht) i hi
  simpa only [show shift + clock t - (shift + clock a) = clock t - clock a by ring] using hh

theorem cap_margin_of_clock_length (model : Model) (β : ℝ) (hβ : 1 < β)
    (X : ℝ → Configuration n d) (hX : Solves model β X)
    (shift : ℝ) (hshift : 0 ≤ shift) (clock : ℝ → ℝ) (hc : ClockRelation β X shift clock)
    (D : Block n) (hD : D.Nonempty) (C : SphericalCap d)
    (a b M U δ : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hM : 0 ≤ M)
    (hsmall : C.radius + (M + 1) * enlargementScale β < Real.pi / 2)
    (hscale : enlargementScale β ≤ 1)
    (herror : 8 * n * (n + 1) * Real.log β * Real.exp (-5 * δ * β) ≤
      (1 / 5 : ℝ) * enlargementScale β ^ 2)
    (hlength : clock b - clock a ≤ 4 * (n + 1) * Real.log β * Real.exp (β * U))
    (hentry : ∀ i ∈ D, angularDist (accelerated X shift clock a i) C.center ≤
      C.radius + M * enlargementScale β)
    (hcap : ∀ t ∈ Ico a b, ∀ i ∈ D,
      angularDist (accelerated X shift clock t i) C.center ≤ C.radius + (M + 1) * enlargementScale β)
    (hsep : ∀ t ∈ Ico a b, ∀ i ∈ D, ∀ j ∉ D,
      U + 5 * δ ≤ 1 - ⟪(accelerated X shift clock t i).val, (accelerated X shift clock t j).val⟫) :
    ∀ t ∈ Icc a b, ∀ i ∈ D,
      (Real.cos (C.radius + M * enlargementScale β) +
        Real.cos (C.radius + (M + 1) * enlargementScale β)) / 2 ≤
          ⟪(accelerated X shift clock t i).val, C.center.val⟫ ∧
      Real.cos (C.radius + (M + 1) * enlargementScale β) <
          ⟪(accelerated X shift clock t i).val, C.center.val⟫ := by
  have hγ := enlargementScale_pos (zero_lt_one.trans hβ)
  have hr : 0 ≤ C.radius + M * enlargementScale β := add_nonneg C.radius_nonneg (mul_nonneg hM hγ.le)
  have hrr : C.radius + M * enlargementScale β ≤ C.radius + (M + 1) * enlargementScale β := by
    nlinarith only [hγ.le]
  have hgap := PlateauCapScale.cosine_gap_lower (C.radius + M * enlargementScale β)
    (enlargementScale β) hr hγ.le hscale (by nlinarith only [hsmall.le])
  rw [show C.radius + M * enlargementScale β + enlargementScale β =
      C.radius + (M + 1) * enlargementScale β by ring] at hgap
  have hdrift := accelerated_cap_drift model β (zero_lt_one.trans hβ).le X hX shift hshift clock hc
    D hD C.center a b _ _ (U + 5 * δ) ha hab hr hrr hsmall hentry hcap hsep
  intro t ht i hi
  have htime := hc.2.1.monotoneOn (ha.trans ht.1) (ha.trans hab) ht.2
  have htlength : clock t - clock a ≤ 4 * (n + 1) * Real.log β * Real.exp (β * U) := by
    linarith only [htime, hlength]
  have hbound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left htlength (show (0 : ℝ) ≤ 2 * n by positivity))
    (Real.exp_pos (-β * (U + 5 * δ))).le
  have hexp : Real.exp (β * U) * Real.exp (-β * (U + 5 * δ)) = Real.exp (-5 * δ * β) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have herr : (2 * n) * (clock t - clock a) * Real.exp (-β * (U + 5 * δ)) ≤
      (1 / 5 : ℝ) * enlargementScale β ^ 2 := by
    calc
      _ ≤ (2 * n) * (4 * (n + 1) * Real.log β * Real.exp (β * U)) *
          Real.exp (-β * (U + 5 * δ)) := hbound
      _ = 8 * n * (n + 1) * Real.log β * Real.exp (-5 * δ * β) := by
        calc
          _ = (8 * n * (n + 1) * Real.log β) *
              (Real.exp (β * U) * Real.exp (-β * (U + 5 * δ))) := by ring
          _ = _ := by rw [hexp]
      _ ≤ _ := herror
  have hh := hdrift t ht i hi
  have hsquare : 0 < enlargementScale β ^ 2 := sq_pos_of_pos hγ
  constructor <;> nlinarith only [hh, herr, hgap, hsquare]

theorem angularDist_lt_of_cos_lt (x w : Sphere d) (R : ℝ) (hR : 0 ≤ R)
    (hinner : Real.cos R < ⟪x.val, w.val⟫) : angularDist x w < R := by
  by_contra hh
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hR
    (AngularGeometry.angularDist_le_pi x w) (le_of_not_gt hh)
  rw [AngularGeometry.cos_angularDist] at hcos
  exact (not_lt_of_ge hcos) hinner

/-- The source plateau cap improvement. The temperature threshold is chosen
before the interval, model, clock, stage, multiplier, or representatives.
Only the stopped stage geometry and range are assumed; the clock-length and
exterior-error estimates are derived in the proof. -/
theorem plateau_cap_margin (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 4 < κ) :
    ∃ β₀ : ℝ, 1 < β₀ ∧ ∀ β ≥ β₀,
      ∀ M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 4),
        (∀ A, (C A).radius + (M + 1) * enlargementScale β < Real.pi / 2) ∧
      ∀ (model : Model) (l : Fin N) (X : ℝ → Configuration n d), Solves model β X →
      ∀ shift : ℝ, 0 ≤ shift → ∀ clock : ℝ → ℝ, ClockRelation β X shift clock →
      ∀ i j : Fin n, i ∈ T.left l → j ∈ T.right l →
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a ≤ 2 * ((n : ℝ) + 1) →
      (∀ (D : Block n) (hD : D ∈ T.partition l.castSucc), ∀ k ∈ D,
        angularDist (accelerated X shift clock a k) (C (T.currentNode l D hD)).center ≤
          (C (T.currentNode l D hD)).radius + M * enlargementScale β) →
      (∀ t ∈ Icc a b, StageHyp T C β κ (M + 1) l (accelerated X shift clock t)) →
      (∀ t ∈ Icc a b,
        1 - ⟪(accelerated X shift clock t i).val, (accelerated X shift clock t j).val⟫ ≤
          upperBarrier C l + 2 * treeMargin hN C) →
      (∀ t ∈ Icc a b, ActiveScales.mesoscopicScale β ≤
        angularDist (accelerated X shift clock t i) (accelerated X shift clock t j)) →
      ∀ t ∈ Icc a b,
        (∀ (D : Block n) (hD : D ∈ T.partition l.castSucc), D ≠ T.left l → D ≠ T.right l →
          ∀ k ∈ D,
            angularDist (accelerated X shift clock t k) (C (T.currentNode l D hD)).center <
              (C (T.currentNode l D hD)).radius + (M + 1) * enlargementScale β) ∧
        (∀ hp : T.parent l ≠ Finset.univ, ∀ k ∈ T.parent l,
          angularDist (accelerated X shift clock t k) (C (T.parentNode l hp)).center <
            (C (T.parentNode l hp)).radius + (M + 1) * enlargementScale β) := by
  obtain ⟨E, hE, hentryGeometry⟩ := PlateauCapGeometry.entry_cap_geometry T hN C hC
  obtain ⟨G, hG, hgeometry⟩ := ActiveGeometry.stage_barriers T hN C hC
  obtain ⟨S, hS, hscalar⟩ := PlateauScalar.interval_bounds T hN C hC κ hκ
  obtain ⟨P, hP⟩ := eventually_atTop.mp
    (PlateauCapScale.eventually_cap_error n (treeMargin hN C) (treeMargin_pos hN C hC))
  refine ⟨max (max E G) (max S P), hE.trans_le ((le_max_left E G).trans (le_max_left _ _)), ?_⟩
  intro β hβ M hM
  have hβE := (le_max_left E G).trans ((le_max_left _ _).trans hβ)
  have hβG := (le_max_right E G).trans ((le_max_left _ _).trans hβ)
  have hβS := (le_max_left S P).trans ((le_max_right _ _).trans hβ)
  have hβP := (le_max_right S P).trans ((le_max_right _ _).trans hβ)
  obtain ⟨hβ1, hscale, herror⟩ := hP β hβP
  have hM0 : M ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5) := ⟨hM.1, by linarith only [hM.2]⟩
  have hM1 : M + 1 ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5) :=
    ⟨by linarith only [hM.1], by linarith only [hM.2]⟩
  have hsmall := (hentryGeometry β hβE (M + 1) hM1).1
  refine ⟨hsmall, ?_⟩
  intro model l X hX shift hshift clock hc i j hi hj a b ha hab htime hentry hstage hupper hangle
  have hclock := (hscalar β hβS (M + 1) hM1 model l X hX shift hshift clock hc
    i j hi hj a b ha hab hstage hupper hangle).2.1
  have hlength : clock b - clock a ≤ 4 * ((n : ℝ) + 1) * Real.log β *
      Real.exp (β * (upperBarrier C l + 2 * treeMargin hN C)) := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htime (by norm_num : (0 : ℝ) ≤ 2))
        (Real.log_pos hβ1).le)
      (Real.exp_pos (β * (upperBarrier C l + 2 * treeMargin hN C))).le
    nlinarith only [hclock, hh]
  have hext : ∀ t ∈ Icc a b,
      (∀ p ∈ T.parent l, ∀ q ∉ T.parent l,
        upperBarrier C l + 7 * treeMargin hN C ≤
          1 - ⟪(accelerated X shift clock t p).val, (accelerated X shift clock t q).val⟫) ∧
      (∀ p q, T.blockOf l.castSucc p ≠ T.blockOf l.castSucc q →
        ¬ ActiveGeometry.IsActiveCross T l p q →
        upperBarrier C l + 7 * treeMargin hN C ≤
          1 - ⟪(accelerated X shift clock t p).val, (accelerated X shift clock t q).val⟫) := by
    intro t ht
    exact hgeometry β hβG (M + 1) hM1 l (accelerated X shift clock t)
      (hstage t ht).2.1 (hstage t ht).2.2
  have hparentEntry := ((hentryGeometry β hβE M hM0).2 l
    (accelerated X shift clock a) hentry).1
  have hγ := enlargementScale_pos (zero_lt_one.trans hβ1)
  have hpositiveR : ∀ A, 0 ≤ (C A).radius + (M + 1) * enlargementScale β :=
    fun A => add_nonneg (C A).radius_nonneg (mul_nonneg hM1.1 hγ.le)
  intro t ht
  constructor
  · intro D hD hDl hDr k hk
    have hmargin := cap_margin_of_clock_length model β hβ1 X hX shift hshift clock hc
      D (T.block_nonempty _ _ hD) (C (T.currentNode l D hD)) a b M
      (upperBarrier C l + 2 * treeMargin hN C) (treeMargin hN C)
      ha hab hM.1 (hsmall _) hscale herror hlength (hentry D hD)
      (fun u hu => (hstage u ⟨hu.1, hu.2.le⟩).2.1 D hD hDl hDr) (by
        intro u hu p hp q hq
        have hh := PlateauCapGeometry.inactive_barrier_of_nonactive_pairs T l
          (accelerated X shift clock u) _ (hext u ⟨hu.1, hu.2.le⟩).2 D hD hDl hDr p hp q hq
        linarith only [hh]) t ht k hk
    exact angularDist_lt_of_cos_lt _ _ _ (hpositiveR _) hmargin.2
  · intro hp k hk
    have hA : (T.parent l).Nonempty :=
      (T.block_nonempty _ _ (T.left_mem l)).mono (Finset.subset_union_left)
    have hmargin := cap_margin_of_clock_length model β hβ1 X hX shift hshift clock hc
      (T.parent l) hA (C (T.parentNode l hp)) a b M
      (upperBarrier C l + 2 * treeMargin hN C) (treeMargin hN C)
      ha hab hM.1 (hsmall _) hscale herror hlength (hparentEntry hp)
      (fun u hu => (hstage u ⟨hu.1, hu.2.le⟩).2.2 hp) (by
        intro u hu p hp' q hq
        have hh := (hext u ⟨hu.1, hu.2.le⟩).1 p hp' q hq
        linarith only [hh]) t ht k hk
    exact angularDist_lt_of_cos_lt _ _ _ (hpositiveR _) hmargin.2

end Metastability.PlateauCaps
