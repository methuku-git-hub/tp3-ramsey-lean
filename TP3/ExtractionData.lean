module

public import TP3.PairGraph
public import TP3.FDeletion

@[expose] public section

namespace TP3.DenseDecomposition

attribute [local instance] Classical.propDecidable
open DependentSample
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : Finset (Finset V)} {a s : ℝ}
variable (P : DenseDecomposition (mediumPairs H a s) s a)

/-- Block occurrences, including occurrences with the same vertex set,
have separate marks. Unused indices have empty sets and never occur in
a list. This uses a fixed finite index type for the sampling law. -/
noncomputable def extractionData (c : ℝ) (R : ℕ) (colour : V → Fin R)
    (b : ℕ) (hb : ∀ e, (P.pairLists e c).card ≤ b) : Data V (DenseBlock V) where
  classes := R
  classOf := colour
  graph := pairGraph (mediumPairs H a s)
  triples := H
  sets B := if B ∈ P.blocks then B.1 else ∅
  lists x y := P.pairLists {x,y} c
  listBound := b
  list_card x y := hb {x,y}

variable (c : ℝ) (R : ℕ) (colour : V → Fin R) (b : ℕ)
variable (hb : ∀ e, (P.pairLists e c).card ≤ b)

theorem extraction_lists_symm (x y : V) :
    (P.extractionData c R colour b hb).lists x y =
      (P.extractionData c R colour b hb).lists y x := by
  simp only [extractionData,Finset.pair_comm]

theorem extraction_neighbors_card (v : V) :
    ((P.extractionData c R colour b hb).neighbors v).card = degree (mediumPairs H a s) v :=
  pairGraph_neighbors_card (mediumPairs_isPairSystem H a s) v

theorem pairLists_subset (e : Finset V) : P.pairLists e c ⊆ P.blocks := by
  unfold pairLists
  split
  · exact Finset.filter_subset _ _
  · exact Finset.empty_subset _

theorem extraction_setIncidences (v : V) :
    (P.extractionData c R colour b hb).setIncidences v =
      P.blocks.filter (fun B => v ∈ B.1) := by
  ext B
  unfold Data.setIncidences
  rw [Finset.mem_filter,Finset.mem_filter]
  simp only [Finset.mem_univ,true_and]
  change (v ∈ (if B ∈ P.blocks then B.1 else ∅)) ↔ B ∈ P.blocks ∧ v ∈ B.1
  by_cases hB : B ∈ P.blocks <;> simp [hB]

theorem extraction_listing_card (v : V) (B : DenseBlock V) :
    ((P.extractionData c R colour b hb).listing v B).card =
      ((mediumPairs H a s).filter (fun e => v ∈ e ∧ B ∈ P.pairLists e c)).card := by
  unfold Data.listing Data.neighbors
  rw [Finset.filter_filter]
  convert pairGraph_filtered_neighbors_card (mediumPairs_isPairSystem H a s) v
    (fun e => B ∈ P.pairLists e c) using 1 <;> congr 3

theorem extraction_listing_bound (hH : IsTripleSystem H) (hfree : ¬ HasTightPath H)
    (ha : 2 < a) (hc : 0 < c) (h : ℕ) (hh : s/c ≤ h) (v : V) (B : DenseBlock V) :
    ((P.extractionData c R colour b hb).listing v B).card ≤ h := by
  rw [P.extraction_listing_card c R colour b hb]
  by_cases hB : B ∈ P.blocks
  · exact_mod_cast (P.pairLists_local_bound hH hfree ha c hc hB v).trans hh
  · have heq : (mediumPairs H a s).filter (fun e => v ∈ e ∧ B ∈ P.pairLists e c)=∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro e he hvB
      exact hB (P.pairLists_subset c e hvB.2)
    rw [heq,Finset.card_empty]
    exact Nat.zero_le _

/-- Once all large pairs are absent, the selected induced hypergraph
is exactly the induced reduced system. Its listed completions have
already been removed by the shared marks. -/
theorem extraction_induced_eq (S : Finset V)
    (hlarge : ∀ e ∈ allPairs V, e ⊆ S → ((completions H e).card : ℝ) ≤ s)
    (hexclude : ∀ x ∈ S, ∀ y ∈ S, (pairGraph (mediumPairs H a s)).Adj x y →
      ∀ B ∈ P.pairLists {x,y} c, Disjoint S B.1) :
    induced H S = induced (P.reducedSystem c) S := by
  apply Finset.Subset.antisymm
  · intro f hf
    obtain ⟨hfH,hfS⟩ := Finset.mem_filter.mp hf
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hfH,?_,?_⟩,hfS⟩
    · intro e he
      obtain ⟨hef,hecard⟩ := Finset.mem_powersetCard.mp he
      exact hlarge e (mem_allPairs.mpr hecard) (hef.trans hfS)
    · intro e he B hB
      obtain ⟨hef,hecard⟩ := Finset.mem_powersetCard.mp he
      have heG : e ∈ mediumPairs H a s := by
        by_contra hh
        simpa [pairLists,hh] using hB
      obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp hecard
      have hxyS : ({x,y} : Finset V) ⊆ S := hef.trans hfS
      have hd := hexclude x (hxyS (by simp)) y (hxyS (by simp)) ⟨hxy,heG⟩ B hB
      exact Finset.disjoint_left.mpr (fun z hz =>
        Finset.disjoint_left.mp hd (hfS (Finset.mem_sdiff.mp hz).1))
  · exact fun f hf => Finset.mem_filter.mpr
      ⟨P.reducedSystem_subset c (Finset.mem_filter.mp hf).1,(Finset.mem_filter.mp hf).2⟩

theorem extraction_finalSet_exclusion (n : ℕ)
    (ξ : History (ClassNoise V (DenseBlock V)
      (P.extractionData c R colour b hb).maxListSize) n)
    {x y : V}
    (hx : x ∈ (P.extractionData c R colour b hb).finalSet n ξ)
    (hy : y ∈ (P.extractionData c R colour b hb).finalSet n ξ)
    (hxy : (pairGraph (mediumPairs H a s)).Adj x y)
    {B : DenseBlock V} (hB : B ∈ P.pairLists {x,y} c) :
    Disjoint ((P.extractionData c R colour b hb).finalSet n ξ) B.1 := by
  have hh := (P.extractionData c R colour b hb).finalSet_exclusion
    (P.extraction_lists_symm c R colour b hb) n ξ hx hy hxy hB
  simpa only [extractionData,ite_eq_left (P.pairLists_subset c {x,y} hB)] using hh

end TP3.DenseDecomposition
