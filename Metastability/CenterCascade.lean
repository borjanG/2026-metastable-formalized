import Metastability.CenterLimits
import Metastability.CascadeFamilyData
import Metastability.StageCenterPropagation

/-! Finite deterministic-center induction along the produced actual cascade.
The intermediate record is derived from source data; the final source theorem
constructs it rather than assuming any of its geometric conclusions. -/
noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace Metastability.CenterCascade
open Source AngularGeometry ActiveScales ActiveSourceLaw CapEnlargement CascadeStep
variable {n N d : ℕ}

/-- The proved geometric cascade supplies every hypothesis of the actual
particle propagation theorem on each complete active stage. -/
theorem stage_propagation (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 4 < κ)
    (model : Model) (CStar : ℝ) (hCStar : 0 ≤ CStar)
    (X : ℝ → ℝ → Configuration n d) (hX : ∀ β, 1 < β → Solves model β (X β))
    (data : CascadeFamilyData T hN C κ model CStar X) (l : Fin N) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ β : ℝ in atTop, ∃ G : Sphere d,
      (∃ hπ : angularDist (accelerated (X β) (CStar * β) (data.clock β) (data.s β l.castSucc) (data.i l))
          (accelerated (X β) (CStar * β) (data.clock β) (data.s β l.castSucc) (data.j l)) < Real.pi,
        G.val = geodesicBarycenter (centerWeight model (T.left l)) (centerWeight model (T.right l))
          (centerWeight_pos model _ (T.block_nonempty _ _ (T.left_mem l)))
          (centerWeight_pos model _ (T.block_nonempty _ _ (T.right_mem l)))
          (accelerated (X β) (CStar * β) (data.clock β) (data.s β l.castSucc) (data.i l))
          (accelerated (X β) (CStar * β) (data.clock β) (data.s β l.castSucc) (data.j l)) hπ) ∧
      (∀ t ∈ Icc (data.s β l.castSucc) (data.hit β l), ∀ p ∈ T.parent l,
        angularDist (accelerated (X β) (CStar * β) (data.clock β) t p) G ≤
          angularDist (accelerated (X β) (CStar * β) (data.clock β) t (data.i l))
            (accelerated (X β) (CStar * β) (data.clock β) t (data.j l)) + ε) ∧
      (∀ t ∈ Icc (data.hit β l) (data.complete β l), ∀ p ∈ T.parent l,
        angularDist (accelerated (X β) (CStar * β) (data.clock β) t p) G < ε) ∧
      (∀ t ∈ Icc (data.s β l.castSucc) (data.complete β l), ∀ D ∈ T.partition l.castSucc,
        D ≠ T.left l → D ≠ T.right l → ∀ p ∈ D,
        angularDist (accelerated (X β) (CStar * β) (data.clock β) t p)
          (accelerated (X β) (CStar * β) (data.clock β) (data.s β l.castSucc) p) < ε) := by
  let H := |jumpTime model T l.succ - jumpTime model T l.castSucc| + 1
  have hH : 0 < H := by dsimp [H]; positivity
  have hlen : ∀ᶠ β : ℝ in atTop, data.complete β l - data.s β l.castSucc ≤ H := by
    have ht := (data.complete_tendsto l).sub (data.entry_tendsto l.castSucc)
    have hh : jumpTime model T l.succ - jumpTime model T l.castSucc < H := by
      dsimp [H]
      linarith only [le_abs_self (jumpTime model T l.succ - jumpTime model T l.castSucc)]
    exact (ht.eventually (gt_mem_nhds hh)).mono (fun _ h => h.le)
  obtain ⟨B, hB, hprop⟩ := StageCenterPropagation.source_propagation T hN C hC κ hκ H hH ε hε
  filter_upwards [eventually_ge_atTop B, data.entry_nonneg, data.stage_times,
    data.stage_geometry, data.noncompletion, data.prehit_angle, data.terminal_angle, hlen]
      with β hb hn ht hg hnc hpre hpost hlength
  have hβ := hB.trans_le hb
  have hM := entryMultiplier_bounds l
  have hM' : entryMultiplier l + 1 ∈ Icc (0 : ℝ) (2 * (N : ℝ) + 5) := by
    constructor <;> linarith only [hM.1, hM.2]
  exact hprop β hb _ hM' model l (X β) (hX β hβ) (CStar * β)
    (mul_nonneg hCStar (zero_lt_one.trans hβ).le) (data.clock β) (data.clock_relation β hβ)
    (data.i l) (data.j l) (data.i_mem l) (data.j_mem l)
    (data.s β l.castSucc) (data.hit β l) (data.complete β l) (hn _) (ht l).1 (ht l).2.1 hlength
    (fun t ht => (hg l t ht).1)
    (fun t ht => (hg l t ht).2.trans (by linarith only [treeMargin_pos hN C hC]))
    (hnc l) (hpre l) (hpost l)

/-- Every particle in every entry block converges to that block's literal
recursive deterministic center, including the final root entry. -/
theorem entry_centers (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ) (hκ : 4 < κ)
    (model : Model) (CStar : ℝ)
    (hCStar : 8 * κ / (1 / (4 * (n : ℝ))) < CStar)
    (X : ℝ → ℝ → Configuration n d) (hX : ∀ β, 1 < β → Solves model β (X β))
    (hvisible : ∀ β, 1 < β → VisiblePrepared hN C β (X β 0))
    (data : CascadeFamilyData T hN C κ model CStar X)
    (z : NodeCenters T d) (hz : IsDeterministicCenters model hN C z) :
    ∀ r : Fin (N + 1), ∀ ε : ℝ, 0 < ε → ∀ᶠ β : ℝ in atTop,
      ∀ (D : Block n) (hD : D ∈ T.partition r), ∀ p ∈ D,
        angularDist (accelerated (X β) (CStar * β) (data.clock β) (data.s β r) p)
          (z D ⟨r, hD⟩) < ε := by
  have hκ0 : 0 < κ := by linarith only [hκ]
  have hCs : 0 < CStar := (div_pos (mul_pos (by norm_num) hκ0)
    (BlockContraction.contraction_constant_pos n (TreeDynamics.particle_pos T))).trans hCStar
  intro r
  induction r using Fin.induction with
  | zero =>
    intro ε hε
    filter_upwards [data.entry_zero,
      CenterLimits.initial_particles T hN C hC κ CStar hκ0 hCStar ε hε] with β hztime hinit
    intro D hD p hp
    rw [hztime, hz.1 D hD]
    exact hinit.2 model (X β) (hX β hinit.1) (hvisible β hinit.1)
      (data.clock β) (data.clock_relation β hinit.1) D hD p hp
  | succ l ih =>
    intro ε hε
    have hquarter : 0 < ε / 4 := by positivity
    have hleft : ∀ η : ℝ, 0 < η → ∀ᶠ β : ℝ in atTop,
        angularDist (accelerated (X β) (CStar * β) (data.clock β) (data.s β l.castSucc) (data.i l))
          (z (T.left l) (T.left_node l)) < η := by
      intro η hη
      exact (ih η hη).mono (fun β hb => hb _ (T.left_mem l) _ (data.i_mem l))
    have hright : ∀ η : ℝ, 0 < η → ∀ᶠ β : ℝ in atTop,
        angularDist (accelerated (X β) (CStar * β) (data.clock β) (data.s β l.castSucc) (data.j l))
          (z (T.right l) (T.right_node l)) < η := by
      intro η hη
      exact (ih η hη).mono (fun β hb => hb _ (T.right_mem l) _ (data.j_mem l))
    have hnear := CenterLimits.entry_barycenter_close T hN C model z hz l
      (fun β => accelerated (X β) (CStar * β) (data.clock β) (data.s β l.castSucc))
      (data.i l) (data.j l) hleft hright (ε / 4) hquarter
    have hcut : ∀ᶠ β : ℝ in atTop, 6 * clockCutoff β < ε / 4 := by
      have hl : Tendsto (fun β : ℝ => 6 * clockCutoff β) atTop (𝓝 0) := by
        simpa only [clockCutoff, zero_div, mul_zero] using
          (ContractionScale.tendsto_visibleScale.div_const 4).const_mul 6
      exact hl.eventually (gt_mem_nhds hquarter)
    filter_upwards [stage_propagation T hN C hC κ hκ model CStar hCs.le X hX data l (ε / 4) hquarter,
      hnear, ih (ε / 4) hquarter, data.stage_times, data.post_motion, hcut]
        with β hprop hnear hentry htime hpost hcut
    obtain ⟨G, hG, _, hparent, hinactive⟩ := hprop
    have hGclose := hnear G hG
    intro D hD p hp
    have hmove := hpost l (data.s β l.succ) ⟨(htime l).2.2, le_rfl⟩ D hD p hp p hp
    have hD' := hD
    rw [T.merge l] at hD'
    rcases Finset.mem_insert.mp hD' with heq | hold
    · subst D
      have hend := hparent (data.complete β l) ⟨(htime l).2.1, le_rfl⟩ p hp
      have htri := angularDist_triangle
        (accelerated (X β) (CStar * β) (data.clock β) (data.complete β l) p) G
        (z (T.parent l) (T.parent_node l))
      have htri' := angularDist_triangle
        (accelerated (X β) (CStar * β) (data.clock β) (data.s β l.succ) p)
        (accelerated (X β) (CStar * β) (data.clock β) (data.complete β l) p)
        (z (T.parent l) (T.parent_node l))
      change angularDist (accelerated (X β) (CStar * β) (data.clock β) (data.s β l.succ) p)
        (z (T.parent l) (T.parent_node l)) < ε
      linarith only [hmove, hcut, hend, hGclose, htri, htri', hε]
    · obtain ⟨hDr, hold⟩ := Finset.mem_erase.mp hold
      obtain ⟨hDl, hold⟩ := Finset.mem_erase.mp hold
      have hm := hinactive (data.complete β l) ⟨(htime l).1.trans (htime l).2.1, le_rfl⟩
        D hold hDl hDr p hp
      have he := hentry D hold p hp
      have htri := angularDist_triangle
        (accelerated (X β) (CStar * β) (data.clock β) (data.complete β l) p)
        (accelerated (X β) (CStar * β) (data.clock β) (data.s β l.castSucc) p) (z D ⟨l.castSucc, hold⟩)
      have htri' := angularDist_triangle
        (accelerated (X β) (CStar * β) (data.clock β) (data.s β l.succ) p)
        (accelerated (X β) (CStar * β) (data.clock β) (data.complete β l) p) (z D ⟨l.castSucc, hold⟩)
      linarith only [hmove, hcut, hm, he, htri, htri', hε]

end Metastability.CenterCascade
