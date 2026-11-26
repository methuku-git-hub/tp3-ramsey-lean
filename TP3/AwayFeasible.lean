module

public import TP3.GoodInteractions

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def sampledVertices (ω : RestrictionData V) : Finset V :=
  Finset.univ.filter (fun x => ω.1 x=true)

@[simp] theorem mem_sampledVertices {ω : RestrictionData V} {x : V} :
    x ∈ sampledVertices ω ↔ ω.1 x=true := by simp [sampledVertices]

noncomputable def forbiddenFamily (H : Finset (Finset V)) (ω : RestrictionData V) :
    Finset (Finset V) := H ∪ (allPairs V).filter (fun e => ω.2 e=false)

theorem feasibleFamily_eq_allowedSubsets (H : Finset (Finset V)) (ω : RestrictionData V) :
    feasibleFamily H ω = allowedSubsets (forbiddenFamily H ω) (sampledVertices ω) := by
  ext S
  simp only [feasibleFamily,allowedSubsets,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_powerset]
  constructor
  · rintro ⟨hind,hvertices,hpairs⟩
    refine ⟨fun x hx => mem_sampledVertices.mpr (hvertices x hx),?_⟩
    intro e he heS
    rcases Finset.mem_union.mp he with heH | heP
    · exact hind e heH heS
    · obtain ⟨heP,hfalse⟩ := Finset.mem_filter.mp heP
      have htrue := hpairs e (Finset.mem_powersetCard.mpr ⟨heS,mem_allPairs.mp heP⟩)
      rw [htrue] at hfalse
      contradiction
  · rintro ⟨hSX,hind⟩
    refine ⟨fun e he => hind e (Finset.mem_union_left _ he),
      fun x hx => mem_sampledVertices.mp (hSX hx),?_⟩
    intro e he
    by_contra hh
    have hf : ω.2 e=false := by simpa using hh
    obtain ⟨heS,hecard⟩ := Finset.mem_powersetCard.mp he
    exact hind e (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨mem_allPairs.mpr hecard,hf⟩)) heS

/-- The family used when v is removed. Pair decisions still use the
original codegrees, including triples containing v. -/
noncomputable def awayFamily (H : Finset (Finset V)) (ω : RestrictionData V) (v : V) :
    Finset (Finset V) := allowedSubsets (forbiddenFamily H ω) ((sampledVertices ω).erase v)

theorem awayFamily_nonempty {H : Finset (Finset V)} (hH : IsTripleSystem H)
    (ω : RestrictionData V) (v : V) : (awayFamily H ω v).Nonempty := by
  refine ⟨∅,Finset.mem_filter.mpr ⟨by simp,?_⟩⟩
  intro e he heE
  have heq := Finset.subset_empty.mp heE
  rcases Finset.mem_union.mp he with heH | heP
  · have hc := hH e heH
    simp [heq] at hc
  · have hc := mem_allPairs.mp (Finset.mem_filter.mp heP).1
    simp [heq] at hc

namespace StarOrientation

variable {H : Finset (Finset V)} {v : V} (O : StarOrientation (link H v))

theorem interactionSupport_subset {X C e : Finset V}
    (he : e ⊆ O.activeLeaves X C) (hC : C ⊆ X) : O.interactionSupport e ⊆ X := by
  intro z hz
  rcases Finset.mem_union.mp hz with hze | hzim
  · exact (Finset.mem_filter.mp (he hze)).2.1
  · obtain ⟨x,hxe,rfl⟩ := Finset.mem_image.mp hzim
    exact hC (Finset.mem_filter.mp (he hxe)).2.2

/-- On the good event every relevant forbidden pair or triple meets
the active leaves in at most one vertex. This supplies the hypothesis
of the already proved uniform-fibre lemma. -/
theorem goodInteractions_one_leaf (hH : IsTripleSystem H) (ω : RestrictionData V)
    (hgood : O.GoodInteractions ω) {C : Finset V} (hC : C ⊆ (sampledVertices ω).erase v)
    {e : Finset V} (he : e ∈ forbiddenFamily H ω) (heX : e ⊆ (sampledVertices ω).erase v)
    {x y : V} (hx : x ∈ e) (hxU : x ∈ O.activeLeaves ((sampledVertices ω).erase v) C)
    (hy : y ∈ e) (hyU : y ∈ O.activeLeaves ((sampledVertices ω).erase v) C) : x=y := by
  by_contra hxy
  have hpU : ({x,y} : Finset V) ⊆ O.activeLeaves ((sampledVertices ω).erase v) C := by
    simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
    exact ⟨hxU,hyU⟩
  have hpA : ({x,y} : Finset V) ∈ O.leaves.powersetCard 2 := Finset.mem_powersetCard.mpr
    ⟨hpU.trans (Finset.filter_subset _ _),by simp [hxy]⟩
  have hsupport := O.interactionSupport_subset hpU hC
  have hmask : ∀ w ∈ O.interactionSupport {x,y}, ω.1 w=true := by
    intro w hw
    exact mem_sampledVertices.mp (Finset.mem_erase.mp (hsupport hw)).2
  have hpe : ({x,y} : Finset V) ⊆ e := Finset.insert_subset_iff.mpr ⟨hx,Finset.singleton_subset_iff.mpr hy⟩
  rcases Finset.mem_union.mp he with heH | heP
  · obtain ⟨z,hzx,hzy,heq⟩ := third_vertex (hH e heH) hxy hpe
    have hzX : z ∈ (sampledVertices ω).erase v := heX (by simp [heq])
    apply hgood.2
    refine ⟨{x,y},hpA,z,?_,(Finset.mem_erase.mp hzX).1,?_⟩
    · apply mem_completions.mpr
      refine ⟨by simp [hzx,hzy],?_⟩
      rw [← triple_rotate x y z,← heq]
      exact heH
    · intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact mem_sampledVertices.mp (Finset.mem_erase.mp hzX).2
      · exact hmask w hw
  · obtain ⟨heP,hfalse⟩ := Finset.mem_filter.mp heP
    have hecard := mem_allPairs.mp heP
    have hpeq : ({x,y} : Finset V)=e := Finset.eq_of_subset_of_card_le hpe (by simp [hxy,hecard])
    apply hgood.1
    exact ⟨{x,y},hpA,hmask,hpeq.symm ▸ hfalse⟩

theorem away_observation_fiber (hH : IsTripleSystem H) (ω : RestrictionData V)
    (hgood : O.GoodInteractions ω) (I₀ : Finset V) (hI : I₀ ∈ awayFamily H ω v) :
    let X := (sampledVertices ω).erase v
    let U := O.activeLeaves X (I₀∩O.centres)
    let A := I₀\U
    (awayFamily H ω v).filter (fun I => O.observation X I=O.observation X I₀) =
      (U.filter (fun x => Independent (forbiddenFamily H ω) (A∪{x}))).powerset.image (fun S => A∪S) := by
  dsimp only
  apply O.observation_fiber_eq_image _ _ I₀ hI
  have hIX := Finset.mem_powerset.mp (Finset.mem_filter.mp hI).1
  dsimp only
  intro e he heAU x hx hxU y hy hyU
  apply O.goodInteractions_one_leaf hH ω hgood (Finset.inter_subset_left.trans hIX) he _ hx hxU hy hyU
  apply heAU.trans
  apply Finset.union_subset (Finset.sdiff_subset.trans hIX)
  intro z hz
  exact (Finset.mem_filter.mp hz).2.1

end StarOrientation
end TP3
