module

public import TP3.Links

@[expose] public section

namespace TP3

variable {V : Type*} [DecidableEq V]

/-- The five-vertex configuration eliminated by the dependent sample. -/
def HasF (H : Finset (Finset V)) : Prop :=
  ∃ a b x y z : V, [a,b,x,y,z].Pairwise (· ≠ ·) ∧
    {a,b,x} ∈ H ∧ {a,b,y} ∈ H ∧ {x,y,z} ∈ H

/-- Three distinct triples on four vertices, with their common vertex first. -/
def HasThreeOnFour (H : Finset (Finset V)) : Prop :=
  ∃ v a b c : V, [v,a,b,c].Pairwise (· ≠ ·) ∧
    {v,a,b} ∈ H ∧ {v,a,c} ∈ H ∧ {v,b,c} ∈ H

/-- A triple containing a specified pair has a third vertex different
from both endpoints. -/
theorem third_vertex {e : Finset V} {x y : V} (hcard : e.card = 3)
    (hxy : x ≠ y) (hp : ({x,y} : Finset V) ⊆ e) :
    ∃ z : V, z ≠ x ∧ z ≠ y ∧ e = {x,y,z} := by
  have htwo : ({x,y} : Finset V).card = 2 := by simp [hxy]
  have hdiff : (e \ {x,y}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hp, hcard, htwo]
  obtain ⟨z,hz⟩ := Finset.card_eq_one.mp hdiff
  have hzm : z ∈ e \ {x,y} := by rw [hz]; simp
  obtain ⟨hze,hznot⟩ := Finset.mem_sdiff.mp hzm
  have hzx : z ≠ x := by intro h; apply hznot; simp [h]
  have hzy : z ≠ y := by intro h; apply hznot; simp [h]
  refine ⟨z,hzx,hzy,?_⟩
  have heq := Finset.sdiff_union_of_subset hp
  rw [hz] at heq
  rw [← heq]
  ext a
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- Excluding the two configurations gives exactly the independent
pair-neighbourhood property used in the last step. -/
theorem independent_pair_neighborhoods_of_exclusions
    {H : Finset (Finset V)} (hH : IsTripleSystem H)
    (hF : ¬ HasF H) (h4 : ¬ HasThreeOnFour H) :
    IndependentPairNeighborhoods H := by
  intro a b x y hxy habx haby e he hsub
  obtain ⟨hab,hax,hbx⟩ := edge_distinct hH habx
  obtain ⟨_,hay,hby⟩ := edge_distinct hH haby
  obtain ⟨z,hzx,hzy,rfl⟩ := third_vertex (hH e he) hxy hsub
  by_cases hza : z = a
  · subst z
    apply h4
    refine ⟨a,b,x,y,?_,habx,haby,?_⟩
    · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, forall_eq_or_imp]
      aesop
    · rwa [triple_rotate x y a] at he
  by_cases hzb : z = b
  · subst z
    apply h4
    refine ⟨b,a,x,y,?_,?_,?_,?_⟩
    · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, forall_eq_or_imp]
      aesop
    · simpa [Finset.insert_comm] using habx
    · simpa [Finset.insert_comm] using haby
    · rwa [triple_rotate x y b] at he
  apply hF
  refine ⟨a,b,x,y,z,?_,habx,haby,he⟩
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, forall_eq_or_imp]
  aesop

end TP3
