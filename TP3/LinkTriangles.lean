module

public import TP3.FDeletion
public import TP3.PairGraph

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def linkPairs (H : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  (allPairs V).filter (fun e => v ∉ e ∧ insert v e ∈ H)

theorem linkPairs_card (hH : IsTripleSystem H) (v : V) :
    (linkPairs H v).card = degree H v := by
  have heq : (linkPairs H v).image (insert v) = H.filter (fun e => v ∈ e) := by
    ext e
    constructor
    · intro he
      obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hf).2.2,by simp⟩
    · intro he
      obtain ⟨heH,hve⟩ := Finset.mem_filter.mp he
      refine Finset.mem_image.mpr ⟨e.erase v,?_,Finset.insert_erase hve⟩
      apply Finset.mem_filter.mpr
      refine ⟨mem_allPairs.mpr ?_,Finset.notMem_erase _ _,?_⟩
      · rw [Finset.card_erase_of_mem hve,hH e heH]
      · rwa [Finset.insert_erase hve]
  have hinj : Set.InjOn (insert v) (linkPairs H v : Set (Finset V)) := by
    intro e he f hf hef
    have he' := (Finset.mem_filter.mp he).2.1
    have hf' := (Finset.mem_filter.mp hf).2.1
    have := congrArg (fun S : Finset V => S.erase v) hef
    simpa [Finset.erase_insert,he',hf'] using this
  rw [degree,← heq,Finset.card_image_of_injOn hinj]

noncomputable def linkTriangles (H : Finset (Finset V)) (v : V) : Finset (Finset V) :=
  (Finset.univ.powersetCard 3).filter
    (fun T => ∀ x ∈ T, ∀ y ∈ T, x ≠ y → (link H v).Adj x y)

theorem linkTriangle_pair {H : Finset (Finset V)} {v : V} {T e : Finset V}
    (hT : T ∈ linkTriangles H v) (he : e ∈ T.powersetCard 2) : e ∈ linkPairs H v := by
  obtain ⟨heT,hecard⟩ := Finset.mem_powersetCard.mp he
  obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp hecard
  have hh := (Finset.mem_filter.mp hT).2 x (heT (by simp)) y (heT (by simp)) hxy
  exact Finset.mem_filter.mpr ⟨mem_allPairs.mpr (by simp [hxy]),by simp [hh.2.1,hh.2.2.1],hh.2.2.2⟩

/-- Two different triangles sharing an edge yield a three-edge path
in the link. Thus a link edge belongs to at most one triangle. -/
theorem linkTriangles_same_of_shared_pair {H : Finset (Finset V)}
    (hfree : ¬ HasTightPath H) {v : V} {T U e : Finset V}
    (hT : T ∈ linkTriangles H v) (hU : U ∈ linkTriangles H v)
    (heT : e ∈ T.powersetCard 2) (heU : e ∈ U.powersetCard 2) : T=U := by
  obtain ⟨heT,hecard⟩ := Finset.mem_powersetCard.mp heT
  obtain ⟨heU,_⟩ := Finset.mem_powersetCard.mp heU
  have hTc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2
  have hUc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hU).1).2
  obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp hecard
  obtain ⟨z,hzx,hzy,hTeq⟩ := third_vertex hTc hxy heT
  obtain ⟨w,hwx,hwy,hUeq⟩ := third_vertex hUc hxy heU
  by_cases hzw : z=w
  · simpa [hzw,hTeq,hUeq]
  · exfalso
    have hzx' := (Finset.mem_filter.mp hT).2 z (by simp [hTeq]) x (by simp [hTeq]) hzx
    have hxy' := (Finset.mem_filter.mp hT).2 x (by simp [hTeq]) y (by simp [hTeq]) hxy
    have hyw := (Finset.mem_filter.mp hU).2 y (by simp [hUeq]) w (by simp [hUeq]) hwy.symm
    apply link_no_three_edge_path hfree v z x y w _ hzx' hxy' hyw
    simp only [List.pairwise_cons,List.mem_cons,List.not_mem_nil,forall_eq_or_imp]
    aesop

theorem linkTriangles_card_le {H : Finset (Finset V)}
    (hH : IsTripleSystem H) (hfree : ¬ HasTightPath H) (v : V) :
    (linkTriangles H v).card ≤ degree H v := by
  have hnonempty : ∀ T ∈ linkTriangles H v, (T.powersetCard 2).Nonempty := by
    intro T hT
    have hc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2
    apply Finset.card_pos.mp
    rw [Finset.card_powersetCard,hc]
    decide
  let pick : Finset V → Finset V := fun T =>
    if h : T ∈ linkTriangles H v then (hnonempty T h).choose else ∅
  have hpick : ∀ T ∈ linkTriangles H v, pick T ∈ T.powersetCard 2 := by
    intro T hT
    simp only [pick,dif_pos hT]
    exact (hnonempty T hT).choose_spec
  rw [← linkPairs_card hH]
  apply Finset.card_le_card_of_injOn pick
  · intro T hT
    exact linkTriangle_pair hT (hpick T hT)
  · intro T hT U hU hTU
    exact linkTriangles_same_of_shared_pair hfree hT hU (hpick T hT) (hTU.symm ▸ hpick U hU)

noncomputable def triangleInstances (H : Finset (Finset V)) : Finset (V × Finset V) :=
  Finset.univ.biUnion (fun v => (linkTriangles H v).image (fun T => (v,T)))

@[simp] theorem mem_triangleInstances {H : Finset (Finset V)} {v : V} {T : Finset V} :
    (v,T) ∈ triangleInstances H ↔ T ∈ linkTriangles H v := by simp [triangleInstances]

def triangleSupport (j : V × Finset V) := insert j.1 j.2

theorem triangleSupport_card {H : Finset (Finset V)} {j : V × Finset V}
    (hj : j ∈ triangleInstances H) : (triangleSupport j).card=4 := by
  rcases j with ⟨v,T⟩
  have hT := mem_triangleInstances.mp hj
  have hc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2
  have hv : v ∉ T := by
    intro hvT
    have hn : (T.erase v).Nonempty := Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hvT,hc]; omega)
    obtain ⟨x,hx⟩ := hn
    have hh := (Finset.mem_filter.mp hT).2 v hvT x (Finset.mem_erase.mp hx).2 (Finset.mem_erase.mp hx).1.symm
    exact hh.2.1 rfl
  simp [triangleSupport,hv,hc]

theorem triangleInstances_card_le {H : Finset (Finset V)}
    (hH : IsTripleSystem H) (hfree : ¬ HasTightPath H) :
    (triangleInstances H).card ≤ 3*H.card := by
  calc
    _ ≤ ∑ v : V, ((linkTriangles H v).image (fun T => (v,T))).card := Finset.card_biUnion_le
    _ ≤ ∑ v : V, (linkTriangles H v).card := Finset.sum_le_sum (fun _ _ => Finset.card_image_le)
    _ ≤ ∑ v : V, degree H v := Finset.sum_le_sum (fun v _ => linkTriangles_card_le hH hfree v)
    _ = _ := sum_degree_triples hH

end TP3
