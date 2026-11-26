module

public import TP3.Structure
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace TP3

variable {V : Type*} [DecidableEq V]

/-- The link of v, retaining v as an isolated vertex in the ambient type. -/
def link (H : Finset (Finset V)) (v : V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ v ≠ x ∧ v ≠ y ∧ {v,x,y} ∈ H
  symm := by
    constructor
    intro x y h
    exact ⟨h.1.symm,h.2.2.1,h.2.1,by
      rw [← triple_swap_last v x y]
      exact h.2.2.2⟩
  loopless := by
    constructor
    intro x h
    exact h.1 rfl

instance (H : Finset (Finset V)) (v : V) : DecidableRel (link H v).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ _ ≠ _ ∧ _ ≠ _ ∧ _ ∈ H))

/-- No link of a tight-path-free triple system has a path with three edges. -/
theorem link_no_three_edge_path {H : Finset (Finset V)}
    (hfree : ¬ HasTightPath H) (v a b c d : V)
    (hd : [a,b,c,d].Pairwise (· ≠ ·))
    (hab : (link H v).Adj a b) (hbc : (link H v).Adj b c)
    (hcd : (link H v).Adj c d) : False := by
  apply hfree
  refine ⟨a,b,v,c,d,?_,?_,?_,hcd.2.2.2⟩
  · simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
      forall_eq_or_imp] at hd ⊢
    obtain ⟨hab',hva,hvb,heab⟩ := hab
    obtain ⟨hbc',hvb',hvc,hebc⟩ := hbc
    obtain ⟨hcd',hvc',hvd,hecd⟩ := hcd
    aesop
  · simpa only [← triple_rotate a b v] using hab.2.2.2
  · rw [Finset.insert_comm b v]
    exact hbc.2.2.2

/-- The property produced by deleting F and the configurations on four
vertices: no edge contains two distinct completions of the same pair. -/
def IndependentPairNeighborhoods (H : Finset (Finset V)) : Prop :=
  ∀ a b x y : V, x ≠ y → {a,b,x} ∈ H → {a,b,y} ∈ H →
    ∀ e ∈ H, ¬ ({x,y} : Finset V) ⊆ e

/-- Two leaves with the same chosen centre in a link lie in no common triple. -/
theorem link_leaves_in_no_triple {H : Finset (Finset V)}
    (hind : IndependentPairNeighborhoods H) {v c x y : V}
    (hcx : (link H v).Adj c x) (hcy : (link H v).Adj c y) (hxy : x ≠ y) :
    ∀ e ∈ H, ¬ ({x,y} : Finset V) ⊆ e :=
  hind v c x y hxy hcx.2.2.2 hcy.2.2.2

/-- The independent-pair-neighbourhood property also excludes link triangles. -/
theorem link_no_triangle {H : Finset (Finset V)}
    (hind : IndependentPairNeighborhoods H) {v a b c : V}
    (hab : (link H v).Adj a b) (hac : (link H v).Adj a c)
    (hbc : (link H v).Adj b c) : False := by
  apply hind v a b c hbc.1 hab.2.2.2 hac.2.2.2 {v,b,c} hbc.2.2.2
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  tauto

/-- An edge of a triangle-free graph with no three-edge path has an
endpoint of degree one. Thus each nontrivial component is a star. -/
theorem link_edge_has_leaf {H : Finset (Finset V)}
    (hfree : ¬ HasTightPath H) (hind : IndependentPairNeighborhoods H)
    {v x y : V} (hxy : (link H v).Adj x y) :
    (∀ z, (link H v).Adj x z → z = y) ∨
      (∀ z, (link H v).Adj y z → z = x) := by
  classical
  by_cases hx : ∀ z, (link H v).Adj x z → z = y
  · exact Or.inl hx
  right
  push Not at hx
  obtain ⟨z,hxz,hzy⟩ := hx
  intro w hyw
  by_contra hwx
  by_cases hwz : w = z
  · subst w
    exact link_no_triangle hind hxy hxz hyw
  apply link_no_three_edge_path hfree v z x y w _ hxz.symm hxy hyw
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, forall_eq_or_imp]
  have hzx := hxz.ne.symm
  have hyw' := hyw.ne
  have hxy' := hxy.ne
  aesop

end TP3
