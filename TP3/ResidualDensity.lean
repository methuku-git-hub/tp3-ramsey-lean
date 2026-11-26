module

public import TP3.ListIncidences
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem induced_pairs_card_le_square {G : Finset (Finset V)} (hG : IsPairSystem G)
    (Y : Finset V) : (induced G Y).card ≤ Y.card^2 := by
  calc
    _ ≤ (Y.powersetCard 2).card := by
      apply Finset.card_le_card
      intro e he
      obtain ⟨heG,heY⟩ := Finset.mem_filter.mp he
      exact Finset.mem_powersetCard.mpr ⟨heY,hG e heG⟩
    _ = Y.card.choose 2 := Finset.card_powersetCard _ _
    _ ≤ _ := Nat.choose_le_pow _ _

theorem DenseDecomposition.induced_covered {G : Finset (Finset V)} {s a : ℝ}
    (P : DenseDecomposition G s a) (Y : Finset V) :
    induced G Y ⊆ induced (residualEdges G P.blocks) Y ∪
      P.blocks.biUnion (fun b => induced b.2 (Y ∩ b.1)) := by
  intro e he
  obtain ⟨heG,heY⟩ := Finset.mem_filter.mp he
  by_cases heR : e ∈ removedEdges P.blocks
  · obtain ⟨b,hb,heB⟩ := Finset.mem_biUnion.mp heR
    have heU := (Finset.mem_filter.mp ((P.valid b hb).2.2.2.1 heB)).2
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨b,hb,Finset.mem_filter.mpr ⟨heB,Finset.subset_inter heY heU⟩⟩)
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨heG,heR⟩,heY⟩)

/-- After excluding listed blocks, only the sparse remainder and small
intersections with the other blocks contribute edges in a neighbourhood. -/
theorem DenseDecomposition.induced_edge_bound {G : Finset (Finset V)} {s a : ℝ}
    (P : DenseDecomposition G s a) (hG : IsPairSystem G) (ha : 0 ≤ a)
    (Y : Finset V) (hY : (Y.card : ℝ) ≤ s) (c r : ℝ) (hc : 0 ≤ c)
    (hsmall : ∀ b ∈ P.blocks, ((Y ∩ b.1).card : ℝ) ≤ c)
    (hr : ∀ x ∈ Y, ((P.blocks.filter (fun b => x ∈ b.1)).card : ℝ) ≤ r) :
    ((induced G Y).card : ℝ) ≤ (a+c*r)*Y.card := by
  have hnonempty : ∀ e ∈ G, e.Nonempty := by
    intro e he
    apply Finset.card_pos.mp
    rw [hG e he]
    decide
  have hres := P.residual_sparse hnonempty ha Y hY
  have hsquare := unlisted_intersection_square_sum P.blocks Prod.fst Y c r hc hsmall hr
  have hblocks :
      ((P.blocks.biUnion (fun b => induced b.2 (Y ∩ b.1))).card : ℝ) ≤
        ∑ b ∈ P.blocks, ((Y ∩ b.1).card : ℝ)^2 := by
    calc
      _ ≤ ∑ b ∈ P.blocks, ((induced b.2 (Y ∩ b.1)).card : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := P.blocks)
          (t := fun b => induced b.2 (Y ∩ b.1)))
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro b hb
        have hbG : IsPairSystem b.2 := fun e he =>
          hG e (Finset.mem_filter.mp ((P.valid b hb).2.2.2.1 he)).1
        exact_mod_cast induced_pairs_card_le_square hbG (Y ∩ b.1)
  have hcover : ((induced G Y).card : ℝ) ≤
      (induced (residualEdges G P.blocks) Y).card +
      (P.blocks.biUnion (fun b => induced b.2 (Y ∩ b.1))).card := by
    exact_mod_cast (Finset.card_le_card (P.induced_covered Y)).trans (Finset.card_union_le _ _)
  nlinarith

end TP3
