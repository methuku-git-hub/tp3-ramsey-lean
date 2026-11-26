module

public import TP3.PairDegreeCounting

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem pair_eq_pair_of_mem {e : Finset V} (he : e.card=2) {a : V} (ha : a ∈ e) :
    ∃ b, b ≠ a ∧ e={a,b} := by
  obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp he
  rcases Finset.mem_insert.mp ha with hax | hay
  · subst a
    exact ⟨y,hxy.symm,rfl⟩
  · have hay' := Finset.mem_singleton.mp hay
    subst a
    exact ⟨x,hxy,by ext z; simp [or_comm]⟩

noncomputable def mediumPairs (H : Finset (Finset V)) (a s : ℝ) : Finset (Finset V) :=
  (allPairs V).filter (fun e => a ≤ ((completions H e).card : ℝ) ∧
    ((completions H e).card : ℝ) ≤ s)

theorem mediumPairs_isPairSystem (H : Finset (Finset V)) (a s : ℝ) :
    IsPairSystem (mediumPairs H a s) :=
  fun e he => mem_allPairs.mp (Finset.mem_filter.mp he).1

theorem mediumPairs_degree_bound {H : Finset (Finset V)} (hH : IsTripleSystem H)
    (a s : ℝ) (v : V) : a*(degree (mediumPairs H a s) v : ℝ) ≤ 2*degree H v :=
  high_pair_graph_degree hH (mediumPairs_isPairSystem H a s) a
    (fun e he => (Finset.mem_filter.mp he).2.1) v

theorem medium_completions_disjoint {H : Finset (Finset V)} (hH : IsTripleSystem H)
    (hfree : ¬ HasTightPath H) {a s : ℝ} (ha : 2 < a) (v : V) :
    (((mediumPairs H a s).filter (fun e => v ∈ e)) : Set (Finset V)).PairwiseDisjoint
      (completions H) := by
  intro e he f hf hef
  obtain ⟨heG,hve⟩ := Finset.mem_filter.mp he
  obtain ⟨hfG,hvf⟩ := Finset.mem_filter.mp hf
  obtain ⟨x,hx,rfl⟩ := pair_eq_pair_of_mem (mediumPairs_isPairSystem H a s e heG) hve
  obtain ⟨y,hy,rfl⟩ := pair_eq_pair_of_mem (mediumPairs_isPairSystem H a s f hfG) hvf
  have hxy : x ≠ y := by intro hh; subst y; exact hef rfl
  have hhigh := (Finset.mem_filter.mp heG).2.1
  have hnat : 3 ≤ (completions H {v,x}).card := by
    by_contra! hh
    have hn : (completions H {v,x}).card ≤ 2 := by omega
    have : ((completions H {v,x}).card : ℝ) ≤ 2 := by exact_mod_cast hn
    linarith
  change Disjoint (completions H {v,x}) (completions H {v,y})
  simp only [completions_pair] at hnat ⊢
  exact pairNeighbors_disjoint hH hfree hnat hxy

namespace DenseDecomposition

variable {H : Finset (Finset V)} {a s : ℝ}

noncomputable def pairLists (P : DenseDecomposition (mediumPairs H a s) s a)
    (e : Finset V) (c : ℝ) : Finset (DenseBlock V) :=
  if e ∈ mediumPairs H a s then intersectionList P.blocks Prod.fst (completions H e) c else ∅

theorem block_incidence_le (P : DenseDecomposition (mediumPairs H a s) s a)
    (ha : 0 < a) (g : ℝ) (hdeg : ∀ v, (degree (mediumPairs H a s) v : ℝ) ≤ g)
    (v : V) : ((P.blocks.filter (fun b => v ∈ b.1)).card : ℝ) ≤ g/a := by
  apply (le_div_iff₀ ha).mpr
  have hh := (P.incidence_bound v).trans (hdeg v)
  simpa only [mul_comm] using hh

theorem pairLists_card_bound (P : DenseDecomposition (mediumPairs H a s) s a)
    (ha : 0 < a) (hs : 0 ≤ s) (c g : ℝ) (hc : 0 < c) (hg : 0 ≤ g)
    (hdeg : ∀ v, (degree (mediumPairs H a s) v : ℝ) ≤ g) (e : Finset V) :
    ((P.pairLists e c).card : ℝ) ≤ (g/a)*s/c := by
  by_cases he : e ∈ mediumPairs H a s
  · rw [pairLists,ite_eq_left he]
    have hh := intersectionList_bound P.blocks Prod.fst (completions H e) c (g/a)
      (fun x _ => P.block_incidence_le ha g hdeg x)
    apply (le_div_iff₀ hc).mpr
    have hsN := (Finset.mem_filter.mp he).2.2
    have hb := mul_le_mul_of_nonneg_left hsN (div_nonneg hg ha.le)
    simpa only [mul_comm c] using hh.trans hb
  · rw [pairLists,ite_eq_right he,Finset.card_empty,Nat.cast_zero]
    positivity

theorem pairLists_local_bound (P : DenseDecomposition (mediumPairs H a s) s a)
    (hH : IsTripleSystem H) (hfree : ¬ HasTightPath H) (ha : 2 < a)
    (c : ℝ) (hc : 0 < c) {b : DenseBlock V} (hb : b ∈ P.blocks) (v : V) :
    (((mediumPairs H a s).filter (fun e => v ∈ e ∧ b ∈ P.pairLists e c)).card : ℝ) ≤ s/c := by
  let I := (mediumPairs H a s).filter (fun e => v ∈ e)
  have heq : (mediumPairs H a s).filter (fun e => v ∈ e ∧ b ∈ P.pairLists e c) =
      I.filter (fun e => c ≤ ((completions H e ∩ b.1).card : ℝ)) := by
    ext e
    simp only [Finset.mem_filter,I]
    by_cases he : e ∈ mediumPairs H a s
    · simp [pairLists,intersectionList,he,hb]
    · simp [he]
  rw [heq]
  apply (le_div_iff₀ hc).mpr
  have hh := disjoint_neighborhood_list_bound I (completions H) b.1 c
    (medium_completions_disjoint hH hfree ha v)
  have hsB := (P.valid b hb).2.1
  simpa only [mul_comm c] using hh.trans hsB

end DenseDecomposition
end TP3
