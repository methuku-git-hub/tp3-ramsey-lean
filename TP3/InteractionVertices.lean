module

public import TP3.StarOrientation

@[expose] public section

namespace TP3.StarOrientation

attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : Finset (Finset V)} {v : V} (O : StarOrientation (link H v))

theorem interacting_centres_distinct (hind : IndependentPairNeighborhoods H)
    {x y : V} (hx : x ∈ O.leaves) (hy : y ∈ O.leaves) (hxy : x ≠ y)
    {e : Finset V} (he : e ∈ H) (hpair : ({x,y} : Finset V) ⊆ e) :
    O.centre x ≠ O.centre y := by
  intro hh
  have hcx := (O.leaf_adj x hx).symm
  have hcy := (O.leaf_adj y hy).symm
  rw [← hh] at hcy
  exact link_leaves_in_no_triple hind hcx hcy hxy e he hpair

theorem interaction_four_distinct (hind : IndependentPairNeighborhoods H)
    {x y : V} (hx : x ∈ O.leaves) (hy : y ∈ O.leaves) (hxy : x ≠ y)
    {e : Finset V} (he : e ∈ H) (hpair : ({x,y} : Finset V) ⊆ e) :
    [x,y,O.centre x,O.centre y].Pairwise (· ≠ ·) := by
  have hc := O.interacting_centres_distinct hind hx hy hxy he hpair
  have hxx := O.leaf_ne_centre hx hx
  have hxyc := O.leaf_ne_centre hx hy
  have hyxc := O.leaf_ne_centre hy hx
  have hyy := O.leaf_ne_centre hy hy
  simp only [List.pairwise_cons,List.mem_cons,List.not_mem_nil,forall_eq_or_imp]
  aesop

/-- The third vertex of an interacting triple cannot be either centre:
otherwise independent pair neighbourhoods would forbid a link edge. -/
theorem interaction_third_ne_centre (hind : IndependentPairNeighborhoods H)
    {x y z : V} (hx : x ∈ O.leaves) (hy : y ∈ O.leaves)
    (he : ({x,y,z} : Finset V) ∈ H) : z ≠ O.centre x := by
  intro hz
  subst z
  have hcx : ({O.centre x,x,v} : Finset V) ∈ H := by
    rw [triple_rotate (O.centre x) x v]
    exact (O.leaf_adj x hx).symm.2.2.2
  have hcxy : ({O.centre x,x,y} : Finset V) ∈ H := by
    rwa [← triple_rotate x y (O.centre x)]
  have hyedge := (O.leaf_adj y hy).2.2.2
  exact hind (O.centre x) x v y (O.leaves_ne_vertex hy).symm hcx hcxy
    {v,y,O.centre y} hyedge (by simp)

theorem interaction_five_distinct (hH : IsTripleSystem H) (hind : IndependentPairNeighborhoods H)
    {x y z : V} (hx : x ∈ O.leaves) (hy : y ∈ O.leaves)
    (he : ({x,y,z} : Finset V) ∈ H) :
    [x,y,O.centre x,O.centre y,z].Pairwise (· ≠ ·) := by
  obtain ⟨hxy,hxz,hyz⟩ := edge_distinct hH he
  have hfour := O.interaction_four_distinct hind hx hy hxy he (by simp)
  have hzx := O.interaction_third_ne_centre hind hx hy he
  have hzy := O.interaction_third_ne_centre hind hy hx
    (show ({y,x,z} : Finset V) ∈ H by simpa only [Finset.insert_comm] using he)
  simp only [List.pairwise_cons,List.mem_cons,List.not_mem_nil,forall_eq_or_imp] at hfour ⊢
  aesop

end TP3.StarOrientation
