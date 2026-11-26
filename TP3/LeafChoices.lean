module

public import TP3.Structure

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable

variable {V : Type*} [DecidableEq V]

/-- If each forbidden set uses at most one unrevealed vertex, compatibility
can be checked one unrevealed vertex at a time. This applies to the forbidden
pairs and triples after the outside choices and the centres have been fixed. -/
theorem independent_union_iff_individual
    {F : Finset (Finset V)} {O U S : Finset V}
    (hO : Independent F O) (hSU : S ⊆ U)
    (hone : ∀ e ∈ F, e ⊆ O ∪ U →
      ∀ x ∈ e, x ∈ U → ∀ y ∈ e, y ∈ U → x = y) :
    Independent F (O ∪ S) ↔ ∀ x ∈ S, Independent F (O ∪ {x}) := by
  constructor
  · intro h x hx
    exact independent_mono h (Finset.union_subset_union_right
      (Finset.singleton_subset_iff.mpr hx))
  · intro hind e he hsub
    have hnot : ¬ e ⊆ O := hO e he
    obtain ⟨x,hxe,hxo⟩ := Finset.not_subset.mp hnot
    have hxS : x ∈ S := (Finset.mem_union.mp (hsub hxe)).resolve_left hxo
    apply hind x hxS e he
    intro y hye
    rcases Finset.mem_union.mp (hsub hye) with hyO | hyS
    · exact Finset.mem_union_left _ hyO
    · have hxy := hone e he
        (hsub.trans (Finset.union_subset_union_right hSU))
        x hxe (hSU hxS) y hye (hSU hyS)
      exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hxy.symm)

/-- The individually available leaves form the set of all choices. -/
theorem independent_union_iff_subset_available
    {F : Finset (Finset V)} {O U S : Finset V}
    (hO : Independent F O) (hSU : S ⊆ U)
    (hone : ∀ e ∈ F, e ⊆ O ∪ U →
      ∀ x ∈ e, x ∈ U → ∀ y ∈ e, y ∈ U → x = y) :
    Independent F (O ∪ S) ↔
      S ⊆ U.filter (fun x => Independent F (O ∪ {x})) := by
  classical
  rw [independent_union_iff_individual hO hSU hone]
  constructor
  · intro h x hx
    exact Finset.mem_filter.mpr ⟨hSU hx, h x hx⟩
  · intro h x hx
    exact (Finset.mem_filter.mp (h hx)).2

/-- There are exactly 2^|M| possible completions after fixing the outside
choices, where M consists of the individually available leaves. -/
theorem number_of_leaf_choices
    {F : Finset (Finset V)} {O U : Finset V}
    (hO : Independent F O)
    (hone : ∀ e ∈ F, e ⊆ O ∪ U →
      ∀ x ∈ e, x ∈ U → ∀ y ∈ e, y ∈ U → x = y) :
    (U.powerset.filter (fun S => Independent F (O ∪ S))).card =
      2 ^ (U.filter (fun x => Independent F (O ∪ {x}))).card := by
  classical
  have heq : U.powerset.filter (fun S => Independent F (O ∪ S)) =
      (U.filter (fun x => Independent F (O ∪ {x}))).powerset := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hSU, hS⟩
      exact (independent_union_iff_subset_available hO hSU hone).mp hS
    · intro hSM
      have hSU := hSM.trans (Finset.filter_subset _ _)
      exact ⟨hSU, (independent_union_iff_subset_available hO hSU hone).mpr hSM⟩
  rw [heq, Finset.card_powerset]

end TP3
