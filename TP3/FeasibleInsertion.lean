module

public import TP3.AwayFeasible
public import TP3.Insertion

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mem_awayFamily {H : Finset (Finset V)} {ω : RestrictionData V} {v : V} {S : Finset V} :
    S ∈ awayFamily H ω v ↔ S ∈ feasibleFamily H ω ∧ v ∉ S := by
  rw [feasibleFamily_eq_allowedSubsets]
  simp only [awayFamily,allowedSubsets,Finset.mem_filter,Finset.mem_powerset,Finset.subset_erase]
  tauto

theorem feasibleFamily_downward {H : Finset (Finset V)} {ω : RestrictionData V} {S T : Finset V}
    (hT : T ∈ feasibleFamily H ω) (hST : S ⊆ T) : S ∈ feasibleFamily H ω := by
  rw [feasibleFamily_eq_allowedSubsets] at hT ⊢
  obtain ⟨hTX,hind⟩ := Finset.mem_filter.mp hT
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (hST.trans (Finset.mem_powerset.mp hTX)),
    independent_mono hind hST⟩

theorem awayFamily_eq_of_absent (H : Finset (Finset V)) (ω : RestrictionData V) (v : V)
    (hv : ω.1 v=false) : awayFamily H ω v=feasibleFamily H ω := by
  ext S
  rw [mem_awayFamily]
  constructor
  · exact And.left
  · intro hS
    refine ⟨hS,?_⟩
    intro hvS
    have hh := (Finset.mem_filter.mp hS).2.2.1 v hvS
    rw [hv] at hh
    contradiction

noncomputable def extendibleFamily (H : Finset (Finset V)) (ω : RestrictionData V) (v : V) :
    Finset (Finset V) := (awayFamily H ω v).filter (fun S => insert v S ∈ feasibleFamily H ω)

theorem feasibleFamily_eq_inserted (H : Finset (Finset V)) (ω : RestrictionData V) (v : V) :
    feasibleFamily H ω=insertedFamily (awayFamily H ω v) (extendibleFamily H ω v) v := by
  ext S
  constructor
  · intro hS
    by_cases hv : v ∈ S
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨S.erase v,Finset.mem_filter.mpr ⟨?_,?_⟩,Finset.insert_erase hv⟩
      · exact mem_awayFamily.mpr ⟨feasibleFamily_downward hS (Finset.erase_subset _ _),Finset.notMem_erase _ _⟩
      · rwa [Finset.insert_erase hv]
    · exact Finset.mem_union_left _ (mem_awayFamily.mpr ⟨hS,hv⟩)
  · intro hS
    rcases Finset.mem_union.mp hS with hS | hS
    · exact (mem_awayFamily.mp hS).1
    · obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hS
      exact (Finset.mem_filter.mp hT).2

theorem independent_insert_iff_linkCount_zero {H : Finset (Finset V)} (hH : IsTripleSystem H)
    {S : Finset V} (hS : Independent H S) {v : V} (hv : v ∉ S) :
    Independent H (insert v S) ↔ linkCount H v S=0 := by
  have hzero : linkCount H v S=0 ↔ ∀ e ∈ linkPairs H v, ¬ e ⊆ S := by
    unfold linkCount
    rw [Nat.cast_eq_zero,Finset.card_eq_zero,Finset.eq_empty_iff_forall_notMem]
    simp only [induced,Finset.mem_filter,not_and]
  rw [hzero]
  constructor
  · intro hind e he heS
    obtain ⟨_,_,heH⟩ := Finset.mem_filter.mp he
    exact hind (insert v e) heH (Finset.insert_subset_insert v heS)
  · intro hlink e he heS
    by_cases hve : v ∈ e
    · have hep : e.erase v ∈ linkPairs H v := by
        refine Finset.mem_filter.mpr ⟨mem_allPairs.mpr ?_,Finset.notMem_erase _ _,?_⟩
        · rw [Finset.card_erase_of_mem hve,hH e he]
        · rwa [Finset.insert_erase hve]
      apply hlink (e.erase v) hep
      intro x hx
      have hxin := heS (Finset.mem_erase.mp hx).2
      exact (Finset.mem_insert.mp hxin).resolve_left (Finset.mem_erase.mp hx).1
    · apply hS e he
      intro x hx
      exact (Finset.mem_insert.mp (heS hx)).resolve_left (fun hh => hve (hh ▸ hx))

theorem feasible_insert_iff {H : Finset (Finset V)} (hH : IsTripleSystem H)
    (ω : RestrictionData V) (v : V) {S : Finset V} (hS : S ∈ awayFamily H ω v) :
    insert v S ∈ feasibleFamily H ω ↔ ω.1 v=true ∧ linkCount H v S=0 ∧
      ∀ x ∈ S, ω.2 {v,x}=true := by
  obtain ⟨hfull,hvS⟩ := mem_awayFamily.mp hS
  obtain ⟨hind,hvertices,hpairs⟩ := (Finset.mem_filter.mp hfull).2
  simp only [feasibleFamily,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [independent_insert_iff_linkCount_zero hH hind hvS]
  constructor
  · rintro ⟨hlink,hvert,hpair⟩
    refine ⟨hvert v (by simp),hlink,?_⟩
    intro x hx
    apply hpair {v,x}
    apply Finset.mem_powersetCard.mpr
    exact ⟨by simp [hx],by simp [show v ≠ x from fun hh => hvS (hh.symm ▸ hx)]⟩
  · rintro ⟨hvert,hlink,hpair⟩
    refine ⟨hlink,?_,?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hvert
      · exact hvertices x hx
    · intro e he
      obtain ⟨heS,hecard⟩ := Finset.mem_powersetCard.mp he
      by_cases hve : v ∈ e
      · obtain ⟨x,hxv,rfl⟩ := pair_eq_pair_of_mem hecard hve
        apply hpair x
        exact (Finset.mem_insert.mp (heS (by simp))).resolve_left hxv
      · apply hpairs e
        refine Finset.mem_powersetCard.mpr ⟨?_,hecard⟩
        intro x hx
        exact (Finset.mem_insert.mp (heS hx)).resolve_left (fun hh => hve (hh ▸ hx))

theorem feasible_uniform_insertion (H : Finset (Finset V)) (hH : IsTripleSystem H)
    (ω : RestrictionData V) (v : V) :
    (((extendibleFamily H ω v).card : ℝ)/(awayFamily H ω v).card)/2 ≤
      (FiniteLaw.uniform (feasibleFamily H ω) (feasibleFamily_nonempty hH ω)).event (fun I => v ∈ I) := by
  have hh := uniform_insert_lower_bound (awayFamily H ω v) (extendibleFamily H ω v) v
    (awayFamily_nonempty hH ω v) (Finset.filter_subset _ _) (fun S hS => (mem_awayFamily.mp hS).2)
  simpa only [← feasibleFamily_eq_inserted] using hh

end TP3
