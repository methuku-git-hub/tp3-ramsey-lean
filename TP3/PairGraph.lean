module

public import TP3.MediumPairLists
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The simple graph represented by a family of unordered pairs. -/
def pairGraph (G : Finset (Finset V)) : SimpleGraph V where
  Adj x y := x ≠ y ∧ {x,y} ∈ G
  symm := by constructor; intro x y h; exact ⟨h.1.symm,by simpa only [Finset.pair_comm] using h.2⟩
  loopless := by constructor; intro x h; exact h.1 rfl

theorem pair_image_injective (x : V) : Function.Injective (fun y : V => ({x,y} : Finset V)) := by
  intro y z h
  have hy : y=x ∨ y=z := by
    have := (Finset.ext_iff.mp h y).mp (by simp)
    simpa only [Finset.mem_insert,Finset.mem_singleton] using this
  have hz : z=x ∨ z=y := by
    have := (Finset.ext_iff.mp h z).mpr (by simp)
    simpa only [Finset.mem_insert,Finset.mem_singleton] using this
  rcases hy with rfl | hy
  · rcases hz with hz | hz <;> exact hz.symm
  · exact hy

/-- Identifying a neighbour with its incident unordered edge preserves
cardinality, also after imposing any property of that edge. -/
theorem pairGraph_filtered_neighbors_card {G : Finset (Finset V)}
    (hG : IsPairSystem G) (x : V) (P : Finset V → Prop) :
    (Finset.univ.filter (fun y => (pairGraph G).Adj x y ∧ P {x,y})).card =
      (G.filter (fun e => x ∈ e ∧ P e)).card := by
  have heq : (Finset.univ.filter (fun y => (pairGraph G).Adj x y ∧ P {x,y})).image
      (fun y => ({x,y} : Finset V)) = G.filter (fun e => x ∈ e ∧ P e) := by
    ext e
    constructor
    · intro he
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp he
      obtain ⟨_,⟨hne,hG⟩,hP⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨hG,by simp,hP⟩
    · intro he
      obtain ⟨heG,hxe,hP⟩ := Finset.mem_filter.mp he
      obtain ⟨y,hy,rfl⟩ := pair_eq_pair_of_mem (hG e heG) hxe
      exact Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,⟨hy.symm,heG⟩,hP⟩,rfl⟩
  rw [← heq,Finset.card_image_of_injective _ (pair_image_injective x)]

theorem pairGraph_neighbors_card {G : Finset (Finset V)} (hG : IsPairSystem G) (x : V) :
    (Finset.univ.filter (fun y => (pairGraph G).Adj x y)).card = degree G x := by
  simpa only [and_true,degree] using pairGraph_filtered_neighbors_card hG x (fun _ => True)

end TP3
