import Metastability.GeometricCascadeFamily

/-! Derived geometric family data, produced from the actual visible source problem.
The fields expose conclusions; `exists_data` discharges them all. -/
noncomputable section
open Filter Set
open scoped Topology RealInnerProductSpace
namespace Metastability
open Source CapEnlargement ActiveScales ActiveSourceLaw CascadeStep

structure CascadeFamilyData {n N d : ℕ} (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (κ : ℝ) (model : Model) (CStar : ℝ)
    (X : ℝ → ℝ → Configuration n d) where
  i : Fin N → Fin n
  j : Fin N → Fin n
  i_mem : ∀ l, i l ∈ T.left l
  j_mem : ∀ l, j l ∈ T.right l
  clock : ℝ → ℝ → ℝ
  clock_relation : ∀ β : ℝ, 1 < β → ClockRelation β (X β) (CStar * β) (clock β)
  s : ℝ → Fin (N + 1) → ℝ
  hit : ℝ → Fin N → ℝ
  complete : ℝ → Fin N → ℝ
  entry_tendsto : ∀ r, Tendsto (fun β => s β r) atTop (𝓝 (jumpTime model T r))
  hit_tendsto : ∀ l, Tendsto (fun β => hit β l) atTop (𝓝 (jumpTime model T l.succ))
  complete_tendsto : ∀ l, Tendsto (fun β => complete β l) atTop (𝓝 (jumpTime model T l.succ))
  entry_zero : ∀ᶠ β : ℝ in atTop, s β 0 = 0
  entry_nonneg : ∀ᶠ β : ℝ in atTop, ∀ r, 0 ≤ s β r
  entry_geometry : ∀ᶠ β : ℝ in atTop, ∀ l,
    EntryGeometry T C β κ l (accelerated (X β) (CStar * β) (clock β) (s β l.castSucc))
  stage_times : ∀ᶠ β : ℝ in atTop, ∀ l,
    s β l.castSucc ≤ hit β l ∧ hit β l ≤ complete β l ∧ complete β l ≤ s β l.succ
  stage_windows : ∀ᶠ β : ℝ in atTop, ∀ l,
    hit β l ∈ Ioo (s β l.castSucc) (s β l.castSucc + (1 + 1 / (2 * stageRate model T l))) ∧
    complete β l ∈ Ioc (hit β l) (hit β l + 20 * n * (Real.log (Real.log β) / Real.log β))
  hit_least : ∀ᶠ β : ℝ in atTop, ∀ l,
    IsLeast {t : ℝ | s β l.castSucc ≤ t ∧
      angularDist (accelerated (X β) (CStar * β) (clock β) t (i l))
        (accelerated (X β) (CStar * β) (clock β) t (j l)) = mesoscopicScale β} (hit β l)
  complete_least : ∀ᶠ β : ℝ in atTop, ∀ l,
    IsLeast {t : ℝ | s β l.castSucc ≤ t ∧ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
      angularDist (accelerated (X β) (CStar * β) (clock β) t p)
        (accelerated (X β) (CStar * β) (clock β) t q) ≤ clockCutoff β} (complete β l)
  stage_geometry : ∀ᶠ β : ℝ in atTop, ∀ l, ∀ t ∈ Icc (s β l.castSucc) (complete β l),
    StageHyp T C β κ (entryMultiplier l + 1) l (accelerated (X β) (CStar * β) (clock β) t) ∧
    1 - ⟪(accelerated (X β) (CStar * β) (clock β) t (i l)).val,
      (accelerated (X β) (CStar * β) (clock β) t (j l)).val⟫ ≤ upperBarrier C l + treeMargin hN C
  prehit_angle : ∀ᶠ β : ℝ in atTop, ∀ l, ∀ t ∈ Icc (s β l.castSucc) (hit β l),
    mesoscopicScale β ≤ angularDist (accelerated (X β) (CStar * β) (clock β) t (i l))
      (accelerated (X β) (CStar * β) (clock β) t (j l))
  terminal_angle : ∀ᶠ β : ℝ in atTop, ∀ l, ∀ t ∈ Icc (hit β l) (complete β l),
    angularDist (accelerated (X β) (CStar * β) (clock β) t (i l))
      (accelerated (X β) (CStar * β) (clock β) t (j l)) ≤ mesoscopicScale β
  noncompletion : ∀ᶠ β : ℝ in atTop, ∀ l, ∀ t ∈ Ico (s β l.castSucc) (complete β l),
    ¬ ∀ p ∈ T.parent l, ∀ q ∈ T.parent l,
      angularDist (accelerated (X β) (CStar * β) (clock β) t p)
        (accelerated (X β) (CStar * β) (clock β) t q) ≤ clockCutoff β
  future_separation : ∀ᶠ β : ℝ in atTop, ∀ l, ∀ t ∈ Icc (s β l.castSucc) (complete β l),
    ∀ m : Fin N, l < m → ∃ p ∈ T.parent m, ∃ q ∈ T.parent m,
      7 * treeMargin hN C ≤ angularDist (accelerated (X β) (CStar * β) (clock β) t p)
        (accelerated (X β) (CStar * β) (clock β) t q) ∧
      visibleScale β < angularDist (accelerated (X β) (CStar * β) (clock β) t p)
        (accelerated (X β) (CStar * β) (clock β) t q)
  final_completion : ∀ᶠ β : ℝ in atTop, ∀ l, l.val + 1 = N → s β l.succ = complete β l
  post_clock : ∀ᶠ β : ℝ in atTop, ∀ l k : Fin N, k.castSucc = l.succ →
    s β l.succ = originalClockTime β (X β) (CStar * β) (clock β (complete β l) + CStar * β) ∧
    clock β (s β l.succ) = clock β (complete β l) + CStar * β ∧
    s β l.succ - complete β l ≤ CStar * β / Real.log β *
      Real.exp (-β * (lowerBarrier C k - treeMargin hN C))
  post_geometry : ∀ᶠ β : ℝ in atTop, ∀ l k : Fin N, k.castSucc = l.succ →
    ∀ t ∈ Icc (complete β l) (s β l.succ),
      (∀ (D : Block n) (hD : D ∈ T.partition k.castSucc), ∀ p ∈ D,
        angularDist (accelerated (X β) (CStar * β) (clock β) t p) (C (T.currentNode k D hD)).center <
          (C (T.currentNode k D hD)).radius + entryMultiplier k * enlargementScale β) ∧
      (∀ D ∈ T.partition k.castSucc, ∀ p ∈ D, ∀ q ∈ D,
        angularDist (accelerated (X β) (CStar * β) (clock β) t p)
          (accelerated (X β) (CStar * β) (clock β) t q) ≤ clockCutoff β)
  post_motion : ∀ᶠ β : ℝ in atTop, ∀ l, ∀ t ∈ Icc (complete β l) (s β l.succ),
    ∀ D ∈ T.partition l.succ, ∀ p ∈ D, ∀ q ∈ D,
      angularDist (accelerated (X β) (CStar * β) (clock β) t p)
        (accelerated (X β) (CStar * β) (clock β) (complete β l) q) ≤ 6 * clockCutoff β
  final_cutoff : ∀ᶠ β : ℝ in atTop, ∀ p q : Fin n,
    angularDist (accelerated (X β) (CStar * β) (clock β) (s β (Fin.last N)) p)
      (accelerated (X β) (CStar * β) (clock β) (s β (Fin.last N)) q) ≤ clockCutoff β
  initial_centers : ∀ᶠ β : ℝ in atTop, ∀ (D : Block n) (hD : D ∈ T.partition 0),
    let hne := T.block_nonempty 0 D hD
    let x := accelerated (X β) (CStar * β) (clock β) 0
    BlockGeometry.blockMean D hne x ≠ 0 ∧ ∃ z : Sphere d,
      z.val = ‖BlockGeometry.blockMean D hne x‖⁻¹ • BlockGeometry.blockMean D hne x ∧
      angularDist z (C (T.currentNode ⟨0, hN⟩ D hD)).center ≤ 2 * visibleScale β
  timing_error : ∃ K : ℝ, 0 < K ∧ ∀ᶠ β : ℝ in atTop,
    (∀ r, |s β r - jumpTime model T r| ≤ K * (Real.log (Real.log β) / Real.log β)) ∧
    ∀ l, |hit β l - jumpTime model T l.succ| ≤ K * (Real.log (Real.log β) / Real.log β) ∧
      |complete β l - jumpTime model T l.succ| ≤ K * (Real.log (Real.log β) / Real.log β)

namespace CascadeFamilyData
variable {n N d : ℕ}

/-- Every field of the compact data record is derived from actual source
solutions and visible preparation; no geometric estimate is assumed. -/
theorem exists_data (T : CollisionTree n N) (hN : 0 < N)
    (C : TreeCaps T d) (hC : StrictlyPrepared C) (κ : ℝ)
    (hκ : PlateauStability.kappaThreshold n < κ) (model : Model) (CStar : ℝ)
    (hCStar : 8 * κ / (1 / (4 * (n : ℝ))) < CStar)
    (X : ℝ → ℝ → Configuration n d)
    (hX : ∀ β : ℝ, 1 < β → Solves model β (X β))
    (hvisible : ∀ β : ℝ, 1 < β → VisiblePrepared hN C β (X β 0)) :
    Nonempty (CascadeFamilyData T hN C κ model CStar X) := by
  classical
  choose i hi using fun l : Fin N => T.block_nonempty _ _ (T.left_mem l)
  choose j hj using fun l : Fin N => T.block_nonempty _ _ (T.right_mem l)
  obtain ⟨K, hK, B, _, hfamily⟩ :=
    GeometricCascadeFamily.geometric_cascade_family T hN C hC κ hκ model CStar hCStar
  obtain ⟨clock, hc, s, hit, complete, hprops, hs, hh, ht⟩ := hfamily X hX hvisible i j hi hj
  have he := (eventually_ge_atTop B).mono (fun β hb => hprops β hb)
  have hκ0 : 0 < κ := (by norm_num : (0 : ℝ) < 4).trans
    ((PlateauStability.kappaThreshold_gt_four n).trans hκ)
  refine ⟨{
    i := i
    j := j
    i_mem := hi
    j_mem := hj
    clock := clock
    clock_relation := hc
    s := s
    hit := hit
    complete := complete
    entry_tendsto := hs
    hit_tendsto := hh
    complete_tendsto := ht
    entry_zero := he.mono (fun _ h => h.1)
    entry_nonneg := he.mono (fun _ h => h.2.1)
    entry_geometry := he.mono (fun _ h => h.2.2.1)
    stage_times := ?_
    stage_windows := ?_
    hit_least := ?_
    complete_least := ?_
    stage_geometry := ?_
    prehit_angle := ?_
    terminal_angle := ?_
    noncompletion := ?_
    future_separation := ?_
    final_completion := ?_
    post_clock := ?_
    post_geometry := ?_
    post_motion := ?_
    final_cutoff := he.mono (fun _ h => h.2.2.2.2.2)
    initial_centers := ?_
    timing_error := ?_ }⟩
  · filter_upwards [he] with β h l
    obtain ⟨h1, h2, h3, _⟩ := h.2.2.2.2.1 l
    exact ⟨h1.1.le, h2.1.le, h3⟩
  · filter_upwards [he] with β h l
    obtain ⟨h1, h2, _⟩ := h.2.2.2.2.1 l
    exact ⟨h1, h2⟩
  · filter_upwards [he] with β h l
    exact (h.2.2.2.2.1 l).2.2.2.1
  · filter_upwards [he] with β h l
    exact (h.2.2.2.2.1 l).2.2.2.2.1
  · filter_upwards [he] with β h l
    exact (h.2.2.2.2.1 l).2.2.2.2.2.2.2.1
  · filter_upwards [he] with β h l
    exact (h.2.2.2.2.1 l).2.2.2.2.2.2.2.2.1
  · filter_upwards [he] with β h l
    exact (h.2.2.2.2.1 l).2.2.2.2.2.2.2.2.2.1
  · filter_upwards [he] with β h l t ht hcomplete
    exact (not_le.mpr ht.2) ((h.2.2.2.2.1 l).2.2.2.2.1.2 ⟨ht.1, hcomplete⟩)
  · filter_upwards [he] with β h l
    exact (h.2.2.2.2.1 l).2.2.2.2.2.2.2.2.2.2.1
  · filter_upwards [he] with β h l
    exact (h.2.2.2.2.1 l).2.2.2.2.2.2.2.2.2.2.2.1
  · filter_upwards [he] with β h l k hk
    obtain ⟨h1, h2, h3, _⟩ := (h.2.2.2.2.1 l).2.2.2.2.2.2.2.2.2.2.2.2 k hk
    exact ⟨h1, h2, h3⟩
  · filter_upwards [he] with β h l k hk
    exact ((h.2.2.2.2.1 l).2.2.2.2.2.2.2.2.2.2.2.2 k hk).2.2.2.1
  · filter_upwards [he, eventually_gt_atTop (1 : ℝ)] with β h hβ l t ht D hD p hp q hq
    by_cases hn : l.val + 1 < N
    · let k : Fin N := ⟨l.val + 1, hn⟩
      have hk : k.castSucc = l.succ := rfl
      exact ((h.2.2.2.2.1 l).2.2.2.2.2.2.2.2.2.2.2.2 k hk).2.2.2.2
        t ht D (by rwa [hk]) p hp q hq
    · have hl : l.val + 1 = N := by have := l.isLt; omega
      have heq := (h.2.2.2.2.1 l).2.2.2.2.2.2.2.2.2.2.2.1 hl
      have htt : t = complete β l := le_antisymm (heq ▸ ht.2) ht.1
      subst t
      have hroot := GeometricCascade.last_parent T l hl
      have hpq := (h.2.2.2.2.1 l).2.2.2.2.1.1.2
        p (hroot.symm ▸ Finset.mem_univ p) q (hroot.symm ▸ Finset.mem_univ q)
      have hcut := ActiveScales.clockCutoff_pos hβ
      linarith only [hpq, hcut]
  · filter_upwards [CascadePreparation.initial_at_multiplier T hN C hC κ CStar hκ0 hCStar]
      with β hprep D hD
    have hinit := (hprep.2 model (X β) (hX β hprep.1) (hvisible β hprep.1)).1
    simpa only [accelerated, (hc β hprep.1).1.1, add_zero] using (hinit D hD).2.2
  · refine ⟨K, hK, ?_⟩
    filter_upwards [he] with β h
    refine ⟨h.2.2.2.1, ?_⟩
    intro l
    obtain ⟨_, _, _, _, _, hhit, hcomplete, _⟩ := h.2.2.2.2.1 l
    exact ⟨hhit, hcomplete⟩

end CascadeFamilyData
end Metastability
