import Metastability.CascadeFamilyData
import Metastability.CenterLimits
import Metastability.StageCenterPropagation
import Metastability.StageAngleLimit
import Metastability.CenterTransport
import Metastability.CompactStages
import Metastability.TerminalCompletion

/-! The empirical measure limit from the proved geometric cascade and its
entry-center convergence. The latter is an explicit intermediate input,
discharged by the finite center induction in the source theorem. -/
noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Metastability.GlobalMeasure
open Source ActiveSourceLaw ActiveScales CapEnlargement CascadeStep AngularGeometry
variable {n N d : ℕ}

/-- On an interior compact set, the next partition is already the measure
limit, while the energy still records the current partition. -/
theorem stage_measure_limit_of_cascade (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 4 < κ)
    (model : Model) (CStar : ℝ) (hCStar : 0 ≤ CStar)
    (X : ℝ → ℝ → Configuration n d)
    (hX : ∀ β : ℝ, 1 < β → Solves model β (X β))
    (data : CascadeFamilyData T hN C κ model CStar X)
    (z : NodeCenters T d) (hz : IsDeterministicCenters model hN C z)
    (hentry : ∀ r : Fin (N + 1), ∀ ε : ℝ, 0 < ε → ∀ᶠ β : ℝ in atTop,
      ∀ (D : Block n) (hD : D ∈ T.partition r), ∀ p ∈ D,
        angularDist (accelerated (X β) (CStar * β) (data.clock β) (data.s β r) p)
          (z D ⟨r, hD⟩) < ε)
    (l : Fin N) (K : Set ℝ) (hK : IsCompact K)
    (hsub : K ⊆ Ioo (jumpTime model T l.castSucc) (jumpTime model T l.succ)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ β : ℝ in atTop, ∀ t ∈ K,
      empiricalWasserstein (TreeDynamics.particle_pos T)
        (accelerated (X β) (CStar * β) (data.clock β) t)
        (partitionConfiguration T z l.succ) < ε := by
  let H := jumpTime model T l.succ - jumpTime model T l.castSucc + 1
  have hH : 0 < H := by
    have hh := TreeDynamics.jumpTime_strictMono T model (Fin.castSucc_lt_succ (i := l))
    dsimp only [H]
    linarith only [hh]
  have hlen : ∀ᶠ β : ℝ in atTop, data.complete β l - data.s β l.castSucc ≤ H :=
    ((data.complete_tendsto l).sub (data.entry_tendsto l.castSucc) |>.eventually
      (gt_mem_nhds (show jumpTime model T l.succ - jumpTime model T l.castSucc < H by
        dsimp only [H]; linarith))).mono (fun _ h => h.le)
  obtain ⟨η, hη, hgap⟩ := CompactStages.exists_eventually_gap hK
    (fun _ ht => (hsub ht).1) (data.entry_tendsto l.castSucc)
  have hhit := CompactStages.eventually_above_compact hK
    (fun _ ht => (hsub ht).2) (data.hit_tendsto l)
  have hM : entryMultiplier l + 1 ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5) := by
    have hh := entryMultiplier_bounds l
    constructor <;> linarith only [hh.1, hh.2]
  have hΔ := treeMargin_pos hN C hC
  intro ε hε
  have heps : 0 < ε / 4 := by positivity
  obtain ⟨B, _, hprop⟩ := StageCenterPropagation.source_propagation T hN C hC κ hκ H hH
    (ε / 4) heps
  have hG := CenterLimits.entry_barycenter_close T hN C model z hz l
    (fun β => accelerated (X β) (CStar * β) (data.clock β) (data.s β l.castSucc))
    (data.i l) (data.j l)
    (fun e he => (hentry l.castSucc e he).mono
      (fun _ hh => hh _ (T.left_mem l) _ (data.i_mem l)))
    (fun e he => (hentry l.castSucc e he).mono
      (fun _ hh => hh _ (T.right_mem l) _ (data.j_mem l))) (ε / 4) heps
  filter_upwards [eventually_ge_atTop B, eventually_gt_atTop (1 : ℝ), hlen, hgap, hhit,
    data.entry_nonneg, data.entry_geometry, data.stage_times, data.stage_geometry, data.prehit_angle,
    data.terminal_angle, data.noncompletion, hG, hentry l.castSucc (ε / 4) heps,
    StageAngleLimit.eventual_angle_small T hN C hC κ hκ model l η (ε / 4) hη heps]
    with β hβB hβ hlen hgap hhit hnonneg hentrygeom htimes hgeometry hpre hpost hnc hG hentryβ hangle
  let Y := accelerated (X β) (CStar * β) (data.clock β)
  have hc := data.clock_relation β hβ
  have hshift : 0 ≤ CStar * β := mul_nonneg hCStar (zero_lt_one.trans hβ).le
  have ha := hnonneg l.castSucc
  have hupper : ∀ t ∈ Icc (data.s β l.castSucc) (data.complete β l),
      1 - ⟪(Y t (data.i l)).val, (Y t (data.j l)).val⟫ ≤ upperBarrier C l + 2 * treeMargin hN C := by
    intro t ht
    have hh := (hgeometry l t ht).2
    linarith only [hh, hΔ]
  obtain ⟨G, hformula, hactive, _, hinactive⟩ := hprop β hβB (entryMultiplier l + 1) hM
    model l (X β) (hX β hβ) (CStar * β) hshift (data.clock β) hc
    (data.i l) (data.j l) (data.i_mem l) (data.j_mem l)
    (data.s β l.castSucc) (data.hit β l) (data.complete β l) ha
    (htimes l).1 (htimes l).2.1 hlen (fun t ht => (hgeometry l t ht).1)
    hupper (hnc l) (hpre l) (hpost l)
  have hGnear := hG G hformula
  intro t ht
  have hat : data.s β l.castSucc ≤ t := by have := hgap t ht; linarith only [this, hη]
  have hth : t ≤ data.hit β l := (hhit t ht).le
  have htc : t ≤ data.complete β l := hth.trans (htimes l).2.1
  have hleft : angularDist (Y (data.s β l.castSucc) (data.i l)) (C (T.leftNode l)).center ≤
      (C (T.leftNode l)).radius + (entryMultiplier l + 1) * enlargementScale β :=
    (hentrygeom l).2 _ (T.left_mem l) _ (data.i_mem l) |>.trans (by
      change (C (T.leftNode l)).radius + entryMultiplier l * enlargementScale β ≤
        (C (T.leftNode l)).radius + (entryMultiplier l + 1) * enlargementScale β
      have hg : 0 ≤ enlargementScale β := by unfold enlargementScale; positivity
      nlinarith only [hg])
  have hright : angularDist (Y (data.s β l.castSucc) (data.j l)) (C (T.rightNode l)).center ≤
      (C (T.rightNode l)).radius + (entryMultiplier l + 1) * enlargementScale β :=
    (hentrygeom l).2 _ (T.right_mem l) _ (data.j_mem l) |>.trans (by
      change (C (T.rightNode l)).radius + entryMultiplier l * enlargementScale β ≤
        (C (T.rightNode l)).radius + (entryMultiplier l + 1) * enlargementScale β
      have hg : 0 ≤ enlargementScale β := by unfold enlargementScale; positivity
      nlinarith only [hg])
  have hν := hangle.2 (entryMultiplier l + 1) hM (X β) (hX β hβ) (CStar * β)
    hshift (data.clock β) hc (data.i l) (data.j l) (data.i_mem l) (data.j_mem l)
    (data.s β l.castSucc) t ha (hgap t ht) hleft hright
    (fun u hu => (hgeometry l u ⟨hu.1, hu.2.trans htc⟩).1)
    (fun u hu => hupper u ⟨hu.1, hu.2.trans htc⟩)
    (fun u hu => hpre l u ⟨hu.1, hu.2.trans hth⟩)
  apply (CenterTransport.empirical_next_le T (TreeDynamics.particle_pos T) z l (Y t)
    (3 * ε / 4) ?_ ?_).trans_lt (by linarith only [hε])
  · intro p hp
    have hh := (angularDist_triangle (Y t p) G _).trans
      (add_le_add (hactive t ⟨hat, hth⟩ p hp) hGnear.le)
    linarith only [hh, hν]
  · intro D hD hDl hDr p hp
    have hd := hinactive t ⟨hat, htc⟩ D hD hDl hDr p hp
    have hz' := hentryβ D hD p hp
    have hh := angularDist_triangle (Y t p) (Y (data.s β l.castSucc) p) (z D ⟨l.castSucc, hD⟩)
    linarith only [hh, hd, hz', hε]

/-- After the last limiting jump, final cap invariance gives convergence to
the deterministic root on every interior compact set. -/
theorem terminal_measure_limit_of_cascade (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (κ : ℝ) (model : Model) (CStar : ℝ) (hCStar : 0 ≤ CStar)
    (X : ℝ → ℝ → Configuration n d)
    (hX : ∀ β : ℝ, 1 < β → Solves model β (X β))
    (data : CascadeFamilyData T hN C κ model CStar X)
    (z : NodeCenters T d)
    (hentry : ∀ ε : ℝ, 0 < ε → ∀ᶠ β : ℝ in atTop,
      ∀ (D : Block n) (hD : D ∈ T.partition (Fin.last N)), ∀ p ∈ D,
        angularDist (accelerated (X β) (CStar * β) (data.clock β) (data.s β (Fin.last N)) p)
          (z D ⟨Fin.last N, hD⟩) < ε)
    (K : Set ℝ) (hK : IsCompact K)
    (hsub : K ⊆ Ioi (jumpTime model T (Fin.last N))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ β : ℝ in atTop, ∀ t ∈ K,
      empiricalWasserstein (TreeDynamics.particle_pos T)
        (accelerated (X β) (CStar * β) (data.clock β) t)
        (partitionConfiguration T z (Fin.last N)) < ε := by
  have hwindow := CompactStages.eventually_below_compact hK hsub (data.entry_tendsto (Fin.last N))
  have hcut : Tendsto clockCutoff atTop (𝓝 0) := by
    simpa only [clockCutoff, zero_div] using ContractionScale.tendsto_visibleScale.div_const 4
  have hroot : Finset.univ ∈ T.partition (Fin.last N) := by
    rw [T.final_partition]
    exact Finset.mem_singleton_self _
  let zr := z Finset.univ ⟨Fin.last N, hroot⟩
  let j : Fin n := ⟨0, TreeDynamics.particle_pos T⟩
  intro ε hε
  filter_upwards [eventually_gt_atTop (1 : ℝ), hwindow, data.entry_nonneg, data.final_cutoff,
    hcut.eventually (gt_mem_nhds (half_pos Real.pi_pos)),
    hcut.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity)),
    hentry (ε / 2) (by positivity)] with β hβ hw hnonneg hcomplete hsmall hεcut he
  have hc := data.clock_relation β hβ
  have hshift : 0 ≤ CStar * β := mul_nonneg hCStar (zero_lt_one.trans hβ).le
  have hnear := he Finset.univ hroot j (Finset.mem_univ j)
  intro t ht
  have hh := (TerminalCompletion.after_completion (TreeDynamics.particle_pos T)
    model β hβ hsmall (X β) (hX β hβ) (CStar * β) hshift (data.clock β) hc
    (data.s β (Fin.last N)) (hnonneg (Fin.last N)) hcomplete t (hw t ht).le).2.2 zr j
  rw [CenterTransport.partitionConfiguration_final T z]
  exact hh.trans_lt (by linarith only [hεcut, hnear])

/-- Both literal source measure limits. The only remaining intermediate input
is entry-particle convergence, proved by `CenterCascade.entry_centers`. -/
theorem measure_limit_of_cascade (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 4 < κ)
    (model : Model) (CStar : ℝ) (hCStar : 0 ≤ CStar)
    (X : ℝ → ℝ → Configuration n d)
    (hX : ∀ β : ℝ, 1 < β → Solves model β (X β))
    (data : CascadeFamilyData T hN C κ model CStar X)
    (z : NodeCenters T d) (hz : IsDeterministicCenters model hN C z)
    (hentry : ∀ r : Fin (N + 1), ∀ ε : ℝ, 0 < ε → ∀ᶠ β : ℝ in atTop,
      ∀ (D : Block n) (hD : D ∈ T.partition r), ∀ p ∈ D,
        angularDist (accelerated (X β) (CStar * β) (data.clock β) (data.s β r) p)
          (z D ⟨r, hD⟩) < ε) :
    (∀ l : Fin N, ∀ K : Set ℝ, IsCompact K →
      K ⊆ Ioo (jumpTime model T l.castSucc) (jumpTime model T l.succ) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ β : ℝ in atTop, ∀ t ∈ K,
        empiricalWasserstein (TreeDynamics.particle_pos T)
          (accelerated (X β) (CStar * β) (data.clock β) t)
          (partitionConfiguration T z l.succ) < ε) ∧
    (∀ K : Set ℝ, IsCompact K → K ⊆ Ioi (jumpTime model T (Fin.last N)) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ β : ℝ in atTop, ∀ t ∈ K,
        empiricalWasserstein (TreeDynamics.particle_pos T)
          (accelerated (X β) (CStar * β) (data.clock β) t)
          (partitionConfiguration T z (Fin.last N)) < ε) := by
  exact ⟨stage_measure_limit_of_cascade T hN C hC κ hκ model CStar hCStar X hX data z hz hentry,
    terminal_measure_limit_of_cascade T hN C κ model CStar hCStar X hX data z (hentry (Fin.last N))⟩

end Metastability.GlobalMeasure
