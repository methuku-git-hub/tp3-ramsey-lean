module

public import TP3.PairSystems

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A recorded set together with the edges charged to that occurrence.
Keeping the charge explicit makes all incidence bounds auditable. -/
abbrev DenseBlock (V : Type*) := Finset V × Finset (Finset V)

def ValidDenseBlock (G : Finset (Finset V)) (s a : ℝ) (b : DenseBlock V) : Prop :=
  b.1.Nonempty ∧ (b.1.card : ℝ) ≤ s ∧ b.2.Nonempty ∧ b.2 ⊆ induced G b.1 ∧
    ∀ v ∈ b.1, a ≤ (degree b.2 v : ℝ)

noncomputable def removedEdges (P : Finset (DenseBlock V)) : Finset (Finset V) :=
  P.biUnion Prod.snd

noncomputable def residualEdges (G : Finset (Finset V)) (P : Finset (DenseBlock V)) :
    Finset (Finset V) := G \ removedEdges P

/-- The output of graph peeling. Blocks are indexed occurrences of vertex
sets; their charged edges are pairwise disjoint. -/
structure DenseDecomposition (G : Finset (Finset V)) (s a : ℝ) where
  blocks : Finset (DenseBlock V)
  valid : ∀ b ∈ blocks, ValidDenseBlock G s a b
  disjoint : (blocks : Set (DenseBlock V)).PairwiseDisjoint Prod.snd
  residual_low : ∀ X : Finset V, (X.card : ℝ) ≤ s → X.Nonempty →
    ∃ v ∈ X, (degree (induced (residualEdges G blocks) X) v : ℝ) < a

theorem residual_disjoint_block (G : Finset (Finset V)) (P : Finset (DenseBlock V))
    (X : Finset V) {b : DenseBlock V} (hb : b ∈ P) :
    Disjoint (induced (residualEdges G P) X) b.2 := by
  apply Finset.disjoint_left.mpr
  intro e he hbE
  have hnot := (Finset.mem_sdiff.mp (Finset.mem_filter.mp he).1).2
  exact hnot (Finset.mem_biUnion.mpr ⟨b,hb,hbE⟩)

/-- Existence of the dense sets and a locally sparse residual graph.
Maximizing a finite packing is equivalent to continuing peeling until
no further dense set can be removed. -/
theorem exists_denseDecomposition (G : Finset (Finset V)) (s a : ℝ) (ha : 0 < a) :
    Nonempty (DenseDecomposition G s a) := by
  classical
  let candidates : Finset (DenseBlock V) := Finset.univ.filter (ValidDenseBlock G s a)
  let packs := candidates.powerset.filter
    (fun P : Finset (DenseBlock V) => (P : Set (DenseBlock V)).PairwiseDisjoint Prod.snd)
  have hnonempty : packs.Nonempty := by
    refine ⟨∅,?_⟩
    simp [packs]
  obtain ⟨P,hP,hmax⟩ := packs.exists_max_image Finset.card hnonempty
  obtain ⟨hPc,hdis⟩ := Finset.mem_filter.mp hP
  have hvalid : ∀ b ∈ P, ValidDenseBlock G s a b := by
    intro b hb
    exact (Finset.mem_filter.mp ((Finset.mem_powerset.mp hPc) hb)).2
  refine ⟨⟨P,hvalid,hdis,?_⟩⟩
  intro X hs hX
  by_contra! hbad
  let E := induced (residualEdges G P) X
  let b : DenseBlock V := (X,E)
  have hE : E.Nonempty := by
    obtain ⟨v,hv⟩ := hX
    have hvdeg := hbad v hv
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    change a ≤ (degree E v : ℝ) at hvdeg
    simp [he,degree] at hvdeg
    linarith
  have hES : E ⊆ induced G X := by
    intro e he
    obtain ⟨heR,heX⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp heR).1,heX⟩
  have hbvalid : ValidDenseBlock G s a b := ⟨hX,hs,hE,hES,hbad⟩
  have hbnew : b ∉ P := by
    intro hb
    have hh := residual_disjoint_block G P X hb
    have he : Disjoint E E := hh
    obtain ⟨e,heE⟩ := hE
    exact Finset.disjoint_left.mp he heE heE
  have hinsert : insert b P ∈ packs := by
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powerset.mpr
      exact Finset.insert_subset_iff.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hbvalid⟩,Finset.mem_powerset.mp hPc⟩
    · intro c hc d hd hcd
      rcases Finset.mem_insert.mp hc with rfl | hc <;>
        rcases Finset.mem_insert.mp hd with rfl | hd
      · exact False.elim (hcd rfl)
      · exact residual_disjoint_block G P X hd
      · exact (residual_disjoint_block G P X hc).symm
      · exact hdis hc hd hcd
  have hh := hmax (insert b P) hinsert
  rw [Finset.card_insert_of_notMem hbnew] at hh
  omega

theorem DenseDecomposition.residual_sparse {G : Finset (Finset V)} {s a : ℝ}
    (P : DenseDecomposition G s a) (hG : ∀ e ∈ G, e.Nonempty) (ha : 0 ≤ a)
    (Y : Finset V) (hY : (Y.card : ℝ) ≤ s) :
    ((induced (residualEdges G P.blocks) Y).card : ℝ) ≤ a*Y.card := by
  apply induced_edges_le_of_low_degree _ (fun e he => hG e (Finset.mem_sdiff.mp he).1) a ha Y
  intro X hXY hX
  apply P.residual_low X _ hX
  exact (show (X.card : ℝ) ≤ Y.card by exact_mod_cast Finset.card_le_card hXY).trans hY

/-- Each block containing v charges at least a distinct incident edges.
Their total cannot exceed v's original degree. -/
theorem DenseDecomposition.incidence_bound {G : Finset (Finset V)} {s a : ℝ}
    (P : DenseDecomposition G s a) (v : V) :
    a * ((P.blocks.filter (fun b => v ∈ b.1)).card : ℝ) ≤ degree G v := by
  let I := P.blocks.filter (fun b => v ∈ b.1)
  let E := fun b : DenseBlock V => b.2.filter (fun e => v ∈ e)
  have hdis : (I : Set (DenseBlock V)).PairwiseDisjoint E := by
    intro b hb c hc hbc
    exact (P.disjoint (Finset.mem_filter.mp hb).1 (Finset.mem_filter.mp hc).1 hbc).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hsub : I.biUnion E ⊆ G.filter (fun e => v ∈ e) := by
    intro e he
    obtain ⟨b,hb,he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨heB,hev⟩ := Finset.mem_filter.mp he
    have hbvalid := P.valid b (Finset.mem_filter.mp hb).1
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (hbvalid.2.2.2.1 heB)).1,hev⟩
  calc
    _ = ∑ _b ∈ I, a := by simp [I,mul_comm]
    _ ≤ ∑ b ∈ I, ((E b).card : ℝ) := by
      apply Finset.sum_le_sum
      intro b hb
      exact (P.valid b (Finset.mem_filter.mp hb).1).2.2.2.2 v (Finset.mem_filter.mp hb).2
    _ = ((I.biUnion E).card : ℝ) := by rw [Finset.card_biUnion hdis,Nat.cast_sum]
    _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub

end TP3
