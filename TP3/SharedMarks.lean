module

public import TP3.CoarseSampling
public import TP3.FourVertexProperty

@[expose] public section

namespace TP3.DependentSample.Data

attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

variable (d : Data V U)

/-- A retained pair sharing a mark must use distinct supporting vertices,
at least one of which lies outside the specified configuration. -/
theorem retained_overlap_external (W C A : Finset V) (i : ℕ)
    (hW : FourVertexProperty d.triples W)
    (hC : ∀ u ∈ C, (d.classOf u).val < i)
    (hA : ∀ x ∈ A, (d.classOf x).val = i)
    {x y : V} (hxW : x ∈ W) (hyW : y ∈ W) (hxy : x ≠ y)
    (hx : x ∈ d.retained C A) (hy : y ∈ d.retained C A)
    (hoverlap : ¬ Disjoint (d.required C x) (d.required C y)) :
    ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ (u ∉ W ∨ v ∉ W) ∧
      d.graph.Adj x u ∧ d.graph.Adj y v ∧
      (d.lists x u ∩ d.lists y v).Nonempty := by
  classical
  obtain ⟨M,hMx,hMy⟩ := Finset.not_disjoint_iff.mp hoverlap
  obtain ⟨u,hu,hMu⟩ := Finset.mem_biUnion.mp hMx
  obtain ⟨v,hv,hMv⟩ := Finset.mem_biUnion.mp hMy
  have hMC : (d.lists x u ∩ d.lists y v).Nonempty :=
    ⟨M,Finset.mem_inter.mpr ⟨hMu,hMv⟩⟩
  have huC : u ∈ C := (Finset.mem_filter.mp hu).1
  have hvC : v ∈ C := (Finset.mem_filter.mp hv).1
  have huv : u ≠ v := by
    intro heq
    exact d.retained_no_conflict C A hx hy
      ⟨hxy,u,hu,v,hv,hMC,Or.inl heq⟩
  have houtside : u ∉ W ∨ v ∉ W := by
    by_contra! hin
    have hxi := hA x (d.retained_subset C A hx)
    have hyi := hA y (d.retained_subset C A hy)
    have hui := hC u huC
    have hvi := hC v hvC
    have hxu : x ≠ u := by intro hh; subst u; omega
    have hxv : x ≠ v := by intro hh; subst v; omega
    have hyu : y ≠ u := by intro hh; subst u; omega
    have hyv : y ≠ v := by intro hh; subst v; omega
    have hd : [x,u,y,v].Pairwise (· ≠ ·) := by
      simp only [List.pairwise_cons,List.mem_cons,List.not_mem_nil,forall_eq_or_imp]
      aesop
    have hc : ({x,u,y,v} : Finset V).card=4 := by
      simpa using List.toFinset_card_of_nodup hd
    have hsub : ({x,u,y,v} : Finset V) ⊆ W := by
      simp only [Finset.insert_subset_iff,Finset.singleton_subset_iff]
      exact ⟨hxW,hin.1,hyW,hin.2⟩
    obtain ⟨e,he,hes⟩ := hW _ hsub hc
    exact d.retained_no_conflict C A hx hy
      ⟨hxy,u,hu,v,hv,hMC,Or.inr ⟨e,he,hes⟩⟩
  exact ⟨u,huC,v,hvC,huv,houtside,
    (Finset.mem_filter.mp hu).2,(Finset.mem_filter.mp hv).2,hMC⟩

/-- A witness used in the union bound. The second supporting vertex is
outside W, so at least one additional q-coin must have succeeded. -/
def ExternalWitness (W C : Finset V) : Prop :=
  ∃ x ∈ W, ∃ y ∈ W, x ≠ y ∧
    ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ v ∉ W ∧
      d.graph.Adj x u ∧ d.graph.Adj y v ∧
      (d.lists x u ∩ d.lists y v).Nonempty

theorem externalWitness_mono {W C C' : Finset V} (hCC : C ⊆ C')
    (h : d.ExternalWitness W C) : d.ExternalWitness W C' := by
  obtain ⟨x,hx,y,hy,hxy,u,hu,v,hv,huv,hvW,hxu,hyv,hM⟩ := h
  exact ⟨x,hx,y,hy,hxy,u,hCC hu,v,hCC hv,huv,hvW,hxu,hyv,hM⟩

theorem retained_overlap_witness (W C A : Finset V) (i : ℕ)
    (hW : FourVertexProperty d.triples W)
    (hC : ∀ u ∈ C, (d.classOf u).val < i)
    (hA : ∀ x ∈ A, (d.classOf x).val = i)
    {x y : V} (hxW : x ∈ W) (hyW : y ∈ W) (hxy : x ≠ y)
    (hx : x ∈ d.retained C A) (hy : y ∈ d.retained C A)
    (hoverlap : ¬ Disjoint (d.required C x) (d.required C y)) :
    d.ExternalWitness W C := by
  obtain ⟨u,hu,v,hv,huv,hout,hxu,hyv,hM⟩ :=
    d.retained_overlap_external W C A i hW hC hA hxW hyW hxy hx hy hoverlap
  rcases hout with huW | hvW
  · exact ⟨y,hyW,x,hxW,hxy.symm,v,hv,u,hu,huv.symm,huW,hyv,hxu,by
      simpa only [Finset.inter_comm] using hM⟩
  · exact ⟨x,hxW,y,hyW,hxy,u,hu,v,hv,huv,hvW,hxu,hyv,hM⟩

end TP3.DependentSample.Data
