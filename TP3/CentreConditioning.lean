module

public import TP3.StarOrientation
public import TP3.LeafConditioning

@[expose] public section

namespace TP3.StarOrientation

attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : Finset (Finset V)} {v : V} (O : StarOrientation (link H v))

noncomputable def activeLeaves (X C : Finset V) : Finset V :=
  O.leaves.filter (fun x => x ∈ X ∧ O.centre x ∈ C)

theorem activeLeaves_disjoint (X C : Finset V) : Disjoint (O.activeLeaves X C) O.centres :=
  O.disjoint.mono_left (Finset.filter_subset _ _)

noncomputable def observation (X I : Finset V) : Finset V × Finset V :=
  (I ∩ O.centres,I \ O.activeLeaves X (I ∩ O.centres))

/-- Revealing the chosen centres first adds no hidden condition to the
outside fibre. Conversely, the outside set records all chosen centres,
because the unrevealed vertices are leaves. -/
theorem observation_eq_iff_outside (X I I₀ : Finset V) :
    O.observation X I = O.observation X I₀ ↔
      I \ O.activeLeaves X (I₀ ∩ O.centres)=I₀ \ O.activeLeaves X (I₀ ∩ O.centres) := by
  constructor
  · intro h
    have hc := congrArg Prod.fst h
    have ho := congrArg Prod.snd h
    change I ∩ O.centres=I₀ ∩ O.centres at hc
    change I\O.activeLeaves X (I∩O.centres)=I₀\O.activeLeaves X (I₀∩O.centres) at ho
    rwa [hc] at ho
  · intro h
    have hc : I ∩ O.centres=I₀ ∩ O.centres := by
      ext x
      have hx := Finset.ext_iff.mp h x
      have hd : x ∈ O.centres → x ∉ O.activeLeaves X (I₀ ∩ O.centres) := by
        intro hxc hxu
        exact Finset.disjoint_left.mp (O.activeLeaves_disjoint X _) hxu hxc
      simp only [Finset.mem_sdiff] at hx
      simp only [Finset.mem_inter]
      tauto
    apply Prod.ext
    · exact hc
    · change I\O.activeLeaves X (I∩O.centres)=I₀\O.activeLeaves X (I₀∩O.centres)
      rwa [hc]

theorem observation_fiber (F : Finset (Finset V)) (X I₀ : Finset V) :
    (allowedSubsets F X).filter (fun I => O.observation X I=O.observation X I₀) =
      outsideFiber F X (O.activeLeaves X (I₀∩O.centres))
        (I₀\O.activeLeaves X (I₀∩O.centres)) := by
  ext I
  simp only [outsideFiber,Finset.mem_filter,O.observation_eq_iff_outside]

/-- The preceding fibre identity together with the absence of any
forbidden set containing two unrevealed leaves gives the exact family
of equally likely choices. -/
theorem observation_fiber_eq_image (F : Finset (Finset V)) (X I₀ : Finset V)
    (hI : I₀ ∈ allowedSubsets F X)
    (hone : let U := O.activeLeaves X (I₀∩O.centres)
      let A := I₀\U
      ∀ e ∈ F, e ⊆ A∪U → ∀ x ∈ e, x ∈ U → ∀ y ∈ e, y ∈ U → x=y) :
    let U := O.activeLeaves X (I₀∩O.centres)
    let A := I₀\U
    (allowedSubsets F X).filter (fun I => O.observation X I=O.observation X I₀) =
      (U.filter (fun x => Independent F (A∪{x}))).powerset.image (fun S => A∪S) := by
  dsimp only
  rw [O.observation_fiber]
  obtain ⟨hIX,hind⟩ := Finset.mem_filter.mp hI
  have hIX' := Finset.mem_powerset.mp hIX
  apply outsideFiber_eq_image
  · exact Finset.sdiff_subset.trans hIX'
  · intro x hx
    exact (Finset.mem_filter.mp hx).2.1
  · exact Finset.disjoint_left.mpr (fun x hx hxu => (Finset.mem_sdiff.mp hx).2 hxu)
  · exact independent_mono hind Finset.sdiff_subset
  · exact hone

noncomputable def chosenLeaves (I : Finset V) : Finset V :=
  O.leaves.filter (fun x => x ∈ I ∧ O.centre x ∈ I)

theorem leaf_pair_injective : Set.InjOn (fun x => ({x,O.centre x} : Finset V)) O.leaves := by
  intro x hx y hy heq
  have hmem := (Finset.ext_iff.mp heq x).mp (by simp)
  exact (Finset.mem_insert.mp hmem).resolve_right
    (fun hh => O.leaf_ne_centre hx hy (Finset.mem_singleton.mp hh))

theorem chosenLeaves_image (I : Finset V) :
    (O.chosenLeaves I).image (fun x => ({x,O.centre x} : Finset V)) =
      induced (linkPairs H v) I := by
  ext e
  constructor
  · intro he
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hxA,hxI,hcI⟩ := Finset.mem_filter.mp hx
    have ha := O.leaf_adj x hxA
    refine Finset.mem_filter.mpr ⟨?_,Finset.insert_subset_iff.mpr ⟨hxI,Finset.singleton_subset_iff.mpr hcI⟩⟩
    exact Finset.mem_filter.mpr ⟨mem_allPairs.mpr (by simp [ha.ne]),
      by simp [ha.2.1,ha.2.2.1],ha.2.2.2⟩
  · intro he
    obtain ⟨heL,heI⟩ := Finset.mem_filter.mp he
    obtain ⟨hecard,hvE,heH⟩ := Finset.mem_filter.mp heL
    obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp (mem_allPairs.mp hecard)
    have ha : (link H v).Adj x y := ⟨hxy,by simpa using fun hh => hvE (by simp [hh]),
      by simpa using fun hh => hvE (by simp [hh]),heH⟩
    rcases O.edge_covered x y ha with ⟨hx,hπ⟩ | ⟨hy,hπ⟩
    · refine Finset.mem_image.mpr ⟨x,?_,by rw [hπ]⟩
      exact Finset.mem_filter.mpr ⟨hx,heI (by simp),by rw [hπ]; exact heI (by simp)⟩
    · refine Finset.mem_image.mpr ⟨y,?_,by rw [hπ,Finset.pair_comm]⟩
      exact Finset.mem_filter.mpr ⟨hy,heI (by simp),by rw [hπ]; exact heI (by simp)⟩

theorem chosenLeaves_count (I : Finset V) :
    (O.chosenLeaves I).card=(induced (linkPairs H v) I).card := by
  rw [← O.chosenLeaves_image I]
  symm
  exact Finset.card_image_of_injOn (O.leaf_pair_injective.mono
    (show O.chosenLeaves I ⊆ O.leaves from Finset.filter_subset _ _))

theorem chosenLeaves_eq_inter {I X : Finset V} (hIX : I ⊆ X) :
    O.chosenLeaves I=I ∩ O.activeLeaves X (I∩O.centres) := by
  ext x
  simp only [chosenLeaves,activeLeaves,Finset.mem_inter,Finset.mem_filter]
  constructor
  · rintro ⟨hxA,hxI,hcI⟩
    exact ⟨hxI,hxA,hIX hxI,hcI,O.centre_mem x hxA⟩
  · rintro ⟨hxI,hxA,_hxX,hcI,_hcC⟩
    exact ⟨hxA,hxI,hcI⟩

end TP3.StarOrientation
