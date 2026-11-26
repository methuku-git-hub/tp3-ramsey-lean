module

public import TP3.LinkTriangles

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The edge xy is oriented from a leaf x towards its centre y.
The fixed rank breaks ties only for components consisting of one edge. -/
def OrientedLeaf (G : SimpleGraph V) (rank : V → ℕ) (x y : V) : Prop :=
  G.Adj x y ∧ (∀ z, G.Adj x z → z=y) ∧
    (¬ (∀ z, G.Adj y z → z=x) ∨ rank y < rank x)

theorem orientedLeaf_unique {G : SimpleGraph V} {rank : V → ℕ} {x y z : V}
    (hxy : OrientedLeaf G rank x y) (hxz : OrientedLeaf G rank x z) : y=z :=
  (hxy.2.1 z hxz.1).symm

theorem orientedLeaf_asymm {G : SimpleGraph V} {rank : V → ℕ} {x y : V}
    (hxy : OrientedLeaf G rank x y) (hyx : OrientedLeaf G rank y x) : False := by
  have hylt := hxy.2.2.resolve_left (not_not.mpr hyx.2.1)
  have hxlt := hyx.2.2.resolve_left (not_not.mpr hxy.2.1)
  omega

theorem edge_oriented {G : SimpleGraph V} {rank : V → ℕ}
    (hinj : Function.Injective rank) {x y : V} (hxy : G.Adj x y)
    (hleaf : (∀ z, G.Adj x z → z=y) ∨ (∀ z, G.Adj y z → z=x)) :
    OrientedLeaf G rank x y ∨ OrientedLeaf G rank y x := by
  by_cases hx : ∀ z, G.Adj x z → z=y
  · by_cases hy : ∀ z, G.Adj y z → z=x
    · have hne : rank x ≠ rank y := fun hh => hxy.ne (hinj hh)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inr ⟨hxy.symm,hy,Or.inr hlt⟩
      · exact Or.inl ⟨hxy,hx,Or.inr hgt⟩
    · exact Or.inl ⟨hxy,hx,Or.inl hy⟩
  · exact Or.inr ⟨hxy.symm,hleaf.resolve_left hx,Or.inl hx⟩

/-- Explicit disjoint sets of centres and leaves, with one centre for
each leaf and one leaf for each graph edge. -/
structure StarOrientation (G : SimpleGraph V) where
  leaves : Finset V
  centres : Finset V
  centre : V → V
  disjoint : Disjoint leaves centres
  centre_mem : ∀ x ∈ leaves, centre x ∈ centres
  leaf_adj : ∀ x ∈ leaves, G.Adj x (centre x)
  leaf_unique : ∀ x ∈ leaves, ∀ y, G.Adj x y → y=centre x
  edge_covered : ∀ x y, G.Adj x y →
    (x ∈ leaves ∧ centre x=y) ∨ (y ∈ leaves ∧ centre y=x)

theorem exists_starOrientation (G : SimpleGraph V) (v₀ : V)
    (hleaf : ∀ x y, G.Adj x y →
      (∀ z, G.Adj x z → z=y) ∨ (∀ z, G.Adj y z → z=x)) :
    Nonempty (StarOrientation G) := by
  let rank : V → ℕ := fun x => (Fintype.equivFin V x).val
  have hinj : Function.Injective rank := fun x y hh =>
    (Fintype.equivFin V).injective (Fin.ext hh)
  let A := Finset.univ.filter (fun x => ∃ y, OrientedLeaf G rank x y)
  let π : V → V := fun x => if hx : ∃ y, OrientedLeaf G rank x y then hx.choose else v₀
  have hπ : ∀ x ∈ A, OrientedLeaf G rank x (π x) := by
    intro x hx
    have hh := (Finset.mem_filter.mp hx).2
    simp only [π,dif_pos hh]
    exact hh.choose_spec
  have horient (x y : V) (hxy : OrientedLeaf G rank x y) : x ∈ A ∧ π x=y := by
    have hx : x ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,y,hxy⟩
    exact ⟨hx,orientedLeaf_unique (hπ x hx) hxy⟩
  refine ⟨⟨A,A.image π,π,?_,?_,?_,?_,?_⟩⟩
  · apply Finset.disjoint_left.mpr
    intro x hx hxC
    obtain ⟨y,hy,hyx⟩ := Finset.mem_image.mp hxC
    have hyx' : OrientedLeaf G rank y x := hyx ▸ hπ y hy
    have hxy := hπ x hx
    have hπx : π x=y := (hxy.2.1 y hyx'.1.symm).symm
    exact orientedLeaf_asymm (hπx ▸ hxy) hyx'
  · exact fun x hx => Finset.mem_image.mpr ⟨x,hx,rfl⟩
  · exact fun x hx => (hπ x hx).1
  · exact fun x hx => (hπ x hx).2.1
  · intro x y hxy
    exact (edge_oriented hinj hxy (hleaf x y hxy)).imp (horient x y) (horient y x)

theorem link_starOrientation {H : Finset (Finset V)} (hfree : ¬ HasTightPath H)
    (hind : IndependentPairNeighborhoods H) (v : V) :
    Nonempty (StarOrientation (link H v)) :=
  exists_starOrientation (link H v) v (fun _ _ hxy => link_edge_has_leaf hfree hind hxy)

namespace StarOrientation

variable {H : Finset (Finset V)} {v : V} (O : StarOrientation (link H v))

theorem leaf_ne_centre {x y : V} (hx : x ∈ O.leaves) (hy : y ∈ O.leaves) :
    x ≠ O.centre y := by
  intro hh
  exact Finset.disjoint_left.mp O.disjoint hx (hh.symm ▸ O.centre_mem y hy)

theorem leaves_card_le (hH : IsTripleSystem H) : O.leaves.card ≤ degree H v := by
  rw [← linkPairs_card hH]
  apply Finset.card_le_card_of_injOn (fun x => ({x,O.centre x} : Finset V))
  · intro x hx
    have ha := O.leaf_adj x hx
    exact Finset.mem_filter.mpr ⟨mem_allPairs.mpr (by simp [ha.ne]),
      by simp [ha.2.1,ha.2.2.1],ha.2.2.2⟩
  · intro x hx y hy heq
    have hmem := (Finset.ext_iff.mp heq x).mp (by simp)
    exact (Finset.mem_insert.mp hmem).resolve_right
      (fun hh => O.leaf_ne_centre hx hy (Finset.mem_singleton.mp hh))

theorem leaves_ne_vertex {x : V} (hx : x ∈ O.leaves) : x ≠ v :=
  (O.leaf_adj x hx).2.1.symm

theorem centre_ne_vertex {x : V} (hx : x ∈ O.leaves) : O.centre x ≠ v :=
  (O.leaf_adj x hx).2.2.1.symm

end StarOrientation
end TP3
