import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-! Finite dependent choice with explicitly retained transition witnesses. -/
noncomputable section
namespace Metastability.FiniteChain

theorem exists_chain {N : ℕ} {α γ : Type*}
    (P : Fin (N + 1) → α → Prop)
    (R : Fin N → α → γ → α → Prop)
    (a₀ : α) (ha₀ : P 0 a₀)
    (hstep : ∀ l : Fin N, ∀ a, P l.castSucc a →
      ∃ o b, P l.succ b ∧ R l a o b) :
    ∃ a : Fin (N + 1) → α, ∃ o : Fin N → γ,
      a 0 = a₀ ∧ (∀ l, P l (a l)) ∧ ∀ l, R l (a l.castSucc) (o l) (a l.succ) := by
  classical
  let output (l : Fin N) (a : {a // P l.castSucc a}) : γ :=
    Classical.choose (hstep l a.val a.property)
  let next (l : Fin N) (a : {a // P l.castSucc a}) : {b // P l.succ b} :=
    ⟨Classical.choose (Classical.choose_spec (hstep l a.val a.property)),
      (Classical.choose_spec (Classical.choose_spec (hstep l a.val a.property))).1⟩
  let chain : (l : Fin (N + 1)) → {a // P l a} := Fin.induction ⟨a₀, ha₀⟩ next
  refine ⟨fun l => (chain l).val, fun l => output l (chain l.castSucc), rfl,
    fun l => (chain l).property, ?_⟩
  intro l
  exact (Classical.choose_spec (Classical.choose_spec
    (hstep l (chain l.castSucc).val (chain l.castSucc).property))).2

end Metastability.FiniteChain
