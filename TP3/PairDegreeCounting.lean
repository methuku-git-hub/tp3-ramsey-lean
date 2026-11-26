module

public import TP3.PairCompletions

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem triple_pairs_at_vertex {f : Finset V} (hf : f.card=3) (v : V) :
    ((f.powersetCard 2).filter (fun e => v ∈ e)).card = if v ∈ f then 2 else 0 := by
  by_cases hv : v ∈ f
  · rw [ite_eq_left hv]
    have hh := Finset.card_filter_powersetCard_subset ({v} : Finset V) f 2
      (Finset.singleton_subset_iff.mpr hv) (by simp)
    simpa [hf] using hh
  · rw [ite_eq_right hv]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨heP,hve⟩ := Finset.mem_filter.mp he
    exact hv ((Finset.mem_powersetCard.mp heP).1 hve)

theorem sum_completions_at_vertex {H : Finset (Finset V)} (hH : IsTripleSystem H) (v : V) :
    ∑ e ∈ (allPairs V).filter (fun e => v ∈ e), (completions H e).card = 2*degree H v := by
  let E := (allPairs V).filter (fun e => v ∈ e)
  calc
    _ = ∑ e ∈ E, (H.filter (fun f => e ⊆ f)).card :=
      Finset.sum_congr rfl (fun e he => completions_card hH e
        (mem_allPairs.mp (Finset.mem_filter.mp he).1))
    _ = ∑ e ∈ E, ∑ f ∈ H, if e ⊆ f then 1 else 0 := by simp
    _ = ∑ f ∈ H, ∑ e ∈ E, if e ⊆ f then 1 else 0 := Finset.sum_comm
    _ = ∑ f ∈ H, ((f.powersetCard 2).filter (fun e => v ∈ e)).card := by
      apply Finset.sum_congr rfl
      intro f hf
      have heq : E.filter (fun e => e ⊆ f) =
          (f.powersetCard 2).filter (fun e => v ∈ e) := by
        ext e
        simp only [E,Finset.mem_filter,mem_allPairs,Finset.mem_powersetCard]
        tauto
      rw [← Finset.sum_filter,← Finset.card_eq_sum_ones,heq]
    _ = ∑ f ∈ H, if v ∈ f then 2 else 0 :=
      Finset.sum_congr rfl (fun f hf => triple_pairs_at_vertex (hH f hf) v)
    _ = _ := by rw [← Finset.sum_filter]; simp [degree,Nat.mul_comm]

/-- Restricting to pairs of codegree at least a bounds their graph degree. -/
theorem high_pair_graph_degree {H G : Finset (Finset V)} (hH : IsTripleSystem H)
    (hG : IsPairSystem G) (a : ℝ)
    (hhigh : ∀ e ∈ G, a ≤ ((completions H e).card : ℝ)) (v : V) :
    a*(degree G v : ℝ) ≤ 2*degree H v := by
  calc
    _ = ∑ _e ∈ G.filter (fun e => v ∈ e), a := by simp [degree,mul_comm]
    _ ≤ ∑ e ∈ G.filter (fun e => v ∈ e), ((completions H e).card : ℝ) :=
      Finset.sum_le_sum (fun e he => hhigh e (Finset.mem_filter.mp he).1)
    _ ≤ ∑ e ∈ (allPairs V).filter (fun e => v ∈ e), ((completions H e).card : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        obtain ⟨heG,hev⟩ := Finset.mem_filter.mp he
        exact Finset.mem_filter.mpr ⟨mem_allPairs.mpr (hG e heG),hev⟩
      · intro e he hn
        exact Nat.cast_nonneg _
    _ = _ := by exact_mod_cast sum_completions_at_vertex hH v

end TP3
