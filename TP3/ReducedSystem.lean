module

public import TP3.MediumPairLists

@[expose] public section

namespace TP3.DenseDecomposition

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : Finset (Finset V)} {a s : ℝ}
variable (P : DenseDecomposition (mediumPairs H a s) s a)

/-- Delete triples with a large pair, and triples whose completion vertex
lies in a block listed by one of their medium pairs. -/
noncomputable def reducedSystem (c : ℝ) : Finset (Finset V) :=
  H.filter (fun f =>
    (∀ e ∈ f.powersetCard 2, ((completions H e).card : ℝ) ≤ s) ∧
    ∀ e ∈ f.powersetCard 2, ∀ b ∈ P.pairLists e c, Disjoint (f \ e) b.1)

theorem reducedSystem_subset (c : ℝ) : P.reducedSystem c ⊆ H := Finset.filter_subset _ _

theorem reducedSystem_triples (hH : IsTripleSystem H) (c : ℝ) :
    IsTripleSystem (P.reducedSystem c) := fun f hf => hH f (P.reducedSystem_subset c hf)

theorem reduced_pair_original_bound (c : ℝ) {e : Finset V} (he : e.card=2)
    (hne : (completions (P.reducedSystem c) e).Nonempty) :
    ((completions H e).card : ℝ) ≤ s := by
  obtain ⟨x,hx⟩ := hne
  obtain ⟨hxE,hf⟩ := mem_completions.mp hx
  exact (Finset.mem_filter.mp hf).2.1 e
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_insert _ _,he⟩)

theorem reduced_pair_bound (c : ℝ) (hs : 0 ≤ s) {e : Finset V} (he : e.card=2) :
    ((completions (P.reducedSystem c) e).card : ℝ) ≤ s := by
  by_cases hn : (completions (P.reducedSystem c) e).Nonempty
  · exact (show ((completions (P.reducedSystem c) e).card : ℝ) ≤ (completions H e).card by
      exact_mod_cast Finset.card_le_card (completions_mono (P.reducedSystem_subset c) e)).trans
      (P.reduced_pair_original_bound c he hn)
  · have heq := Finset.not_nonempty_iff_eq_empty.mp hn
    simpa only [heq,Finset.card_empty,Nat.cast_zero] using hs

theorem reduced_completions_avoid_list (c : ℝ) {e : Finset V} (he : e.card=2)
    {b : DenseBlock V} (hb : b ∈ P.pairLists e c) :
    Disjoint (completions (P.reducedSystem c) e) b.1 := by
  apply Finset.disjoint_left.mpr
  intro x hx hxB
  obtain ⟨hxE,hf⟩ := mem_completions.mp hx
  have hdis := (Finset.mem_filter.mp hf).2.2 e
    (Finset.mem_powersetCard.mpr ⟨Finset.subset_insert _ _,he⟩) b hb
  exact Finset.disjoint_left.mp hdis (Finset.mem_sdiff.mpr ⟨by simp,hxE⟩) hxB

theorem reduced_completions_small_intersection (c : ℝ) (hc : 0 ≤ c)
    {e : Finset V} (he : e ∈ mediumPairs H a s) {b : DenseBlock V} (hb : b ∈ P.blocks) :
    ((completions (P.reducedSystem c) e ∩ b.1).card : ℝ) ≤ c := by
  by_cases hl : b ∈ P.pairLists e c
  · have hh := Finset.disjoint_iff_inter_eq_empty.mp
      (P.reduced_completions_avoid_list c (mediumPairs_isPairSystem H a s e he) hl)
    simpa only [hh,Finset.card_empty,Nat.cast_zero] using hc
  · have hsmall : ((completions H e ∩ b.1).card : ℝ) < c := by
      simpa [pairLists,intersectionList,he,hb] using hl
    apply le_trans _ hsmall.le
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter
      (completions_mono (P.reducedSystem_subset c) e) (Finset.Subset.refl b.1))

theorem reduced_nonmedium_bound (c : ℝ) (ha : 0 ≤ a) {e : Finset V} (he : e.card=2)
    (hnot : e ∉ mediumPairs H a s) :
    ((completions (P.reducedSystem c) e).card : ℝ) ≤ a := by
  by_cases hn : (completions (P.reducedSystem c) e).Nonempty
  · have hsN := P.reduced_pair_original_bound c he hn
    have hlow : ((completions H e).card : ℝ) < a := by
      by_contra! hhigh
      exact hnot (Finset.mem_filter.mpr ⟨mem_allPairs.mpr he,hhigh,hsN⟩)
    apply le_trans _ hlow.le
    exact_mod_cast Finset.card_le_card (completions_mono (P.reducedSystem_subset c) e)
  · have heq := Finset.not_nonempty_iff_eq_empty.mp hn
    simpa only [heq,Finset.card_empty,Nat.cast_zero] using ha

theorem reduced_medium_density (ha : 0 ≤ a) (hs : 0 ≤ s) (c r : ℝ) (hc : 0 ≤ c)
    (hr : ∀ x, ((P.blocks.filter (fun b => x ∈ b.1)).card : ℝ) ≤ r)
    {e : Finset V} (he : e ∈ mediumPairs H a s) :
    ((induced (mediumPairs H a s) (completions (P.reducedSystem c) e)).card : ℝ) ≤
      (a+c*r)*(completions (P.reducedSystem c) e).card := by
  apply P.induced_edge_bound (mediumPairs_isPairSystem H a s) ha _
    (P.reduced_pair_bound c hs (mediumPairs_isPairSystem H a s e he)) c r hc
  · exact fun b hb => P.reduced_completions_small_intersection c hc he hb
  · exact fun x _ => hr x

end TP3.DenseDecomposition
