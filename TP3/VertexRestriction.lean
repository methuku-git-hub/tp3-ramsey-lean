module

public import TP3.StructuredIndependence

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The induced hypergraph whose ambient vertex type is the selected set.
Unlike `induced`, this removes the unselected vertices from the type. -/
noncomputable def vertexRestriction (H : Finset (Finset V)) (T : Finset V) :
    Finset (Finset T) := Finset.univ.filter (fun e => e.image Subtype.val ∈ H)

@[simp] theorem mem_vertexRestriction (H : Finset (Finset V)) (T : Finset V)
    (e : Finset T) : e ∈ vertexRestriction H T ↔ e.image Subtype.val ∈ H := by
  simp [vertexRestriction]

theorem vertex_image_subset (T : Finset V) (e : Finset T) : e.image Subtype.val ⊆ T := by
  intro x hx
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  exact y.property

theorem vertex_image_injective (T : Finset V) :
    Function.Injective (fun e : Finset T => e.image Subtype.val) :=
  Finset.image_injective Subtype.val_injective

theorem vertexRestriction_triples {H : Finset (Finset V)} (hH : IsTripleSystem H)
    (T : Finset V) : IsTripleSystem (vertexRestriction H T) := by
  intro e he
  have hh := hH _ (mem_vertexRestriction H T e |>.mp he)
  simpa only [Finset.card_image_of_injective _ Subtype.val_injective] using hh

theorem vertexRestriction_pathFree {H : Finset (Finset V)} (hfree : ¬ HasTightPath H)
    (T : Finset V) : ¬ HasTightPath (vertexRestriction H T) := by
  rintro ⟨a,b,c,d,e,hd,h₁,h₂,h₃⟩
  apply hfree
  refine ⟨a.val,b.val,c.val,d.val,e.val,?_,?_,?_,?_⟩
  · simp only [List.pairwise_cons,List.mem_cons,List.not_mem_nil,forall_eq_or_imp] at hd ⊢
    have hi := @Subtype.val_injective V (fun x => x ∈ T)
    aesop
  · simpa using (mem_vertexRestriction H T _).mp h₁
  · simpa using (mem_vertexRestriction H T _).mp h₂
  · simpa using (mem_vertexRestriction H T _).mp h₃

theorem vertexRestriction_independentPairs {H : Finset (Finset V)} (T : Finset V)
    (hind : IndependentPairNeighborhoods (induced H T)) :
    IndependentPairNeighborhoods (vertexRestriction H T) := by
  intro a b x y hxy hx hy e he hsub
  have hmem (f : Finset T) (hf : f ∈ vertexRestriction H T) :
      f.image Subtype.val ∈ induced H T :=
    Finset.mem_filter.mpr ⟨(mem_vertexRestriction H T f).mp hf,vertex_image_subset T f⟩
  apply hind a.val b.val x.val y.val (fun hh => hxy (Subtype.ext hh))
    (by simpa using hmem _ hx) (by simpa using hmem _ hy)
    (e.image Subtype.val) (hmem e he)
  simpa using Finset.image_subset_image hsub

theorem vertexRestriction_degree (H : Finset (Finset V)) (T : Finset V) (x : T) :
    degree (vertexRestriction H T) x ≤ degree (induced H T) x.val := by
  apply Finset.card_le_card_of_injOn (fun e : Finset T => e.image Subtype.val)
  · intro e he
    obtain ⟨he,hx⟩ := Finset.mem_filter.mp he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨(mem_vertexRestriction H T e).mp he,vertex_image_subset T e⟩,?_⟩
    exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
  · intro e he f hf hh
    exact vertex_image_injective T hh

theorem vertexRestriction_independent {H : Finset (Finset V)} {T : Finset V}
    {I : Finset T} (hI : Independent (vertexRestriction H T) I) :
    Independent H (I.image Subtype.val) := by
  intro e he hes
  let f : Finset T := e.subtype (fun x => x ∈ T)
  have hf : f.image Subtype.val=e := by
    ext x
    constructor
    · intro hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_subtype.mp hy
    · intro hx
      have hxT := vertex_image_subset T I (hes hx)
      exact Finset.mem_image.mpr ⟨⟨x,hxT⟩,Finset.mem_subtype.mpr hx,rfl⟩
  apply hI f ((mem_vertexRestriction H T f).mpr (hf.symm ▸ he))
  intro x hx
  have hxI := hes (Finset.mem_subtype.mp hx)
  obtain ⟨y,hy,hxy⟩ := Finset.mem_image.mp hxI
  have hyx : y=x := Subtype.ext hxy
  simpa [hyx] using hy

/-- Apply the proved structured bound on the extracted vertex set itself. -/
theorem structured_independence_on_set (H : Finset (Finset V)) (hH : IsTripleSystem H)
    (hfree : ¬ HasTightPath H) (T : Finset V) (hT : T.Nonempty)
    (hind : IndependentPairNeighborhoods (induced H T))
    (L : ℝ) (hL : 100 ≤ L)
    (hdegree : ∀ x, (degree (induced H T) x : ℝ) ≤ Real.exp (12*L)) :
    ∃ I ⊆ T, Independent H I ∧
      (T.card : ℝ)*Real.sqrt L*Real.exp (-6*L)/100 ≤ I.card := by
  have hN : 0 < Fintype.card T := by simpa using Finset.card_pos.mpr hT
  obtain ⟨I,hI,hsize⟩ := structured_independence_exponential (vertexRestriction H T)
    (vertexRestriction_triples hH T) (vertexRestriction_pathFree hfree T)
    (vertexRestriction_independentPairs T hind) hN L hL (fun x =>
      (by exact_mod_cast vertexRestriction_degree H T x :
        (degree (vertexRestriction H T) x : ℝ) ≤ degree (induced H T) x.val).trans (hdegree x.val))
  refine ⟨I.image Subtype.val,vertex_image_subset T I,vertexRestriction_independent hI,?_⟩
  simpa only [Fintype.card_coe,Finset.card_image_of_injective _ Subtype.val_injective] using hsize

end TP3
