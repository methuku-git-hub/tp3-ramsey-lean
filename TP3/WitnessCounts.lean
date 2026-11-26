module

public import TP3.CollisionWitness
public import TP3.FiniteCounting

@[expose] public section

namespace TP3.DependentSample.Data

attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
variable (d : Data V U)

abbrev WitnessIndex (V U : Type*) := V × V × V × U × V

noncomputable def neighbors (x : V) : Finset V :=
  Finset.univ.filter (fun u => d.graph.Adj x u)

noncomputable def listing (y : V) (M : U) : Finset V :=
  (d.neighbors y).filter (fun v => M ∈ d.lists y v)

noncomputable def smallIndices (W : Finset V) : Finset (WitnessIndex V U) :=
  (W.product W).biUnion (fun xy => W.biUnion (fun u =>
    (d.lists xy.1 u).biUnion (fun M =>
      ((d.listing xy.2 M).filter (fun v => v ∉ W)).image
        (fun v => (xy.1,xy.2,u,M,v)))))

noncomputable def largeIndices (W : Finset V) : Finset (WitnessIndex V U) :=
  (W.product W).biUnion (fun xy =>
    ((d.neighbors xy.1).filter (fun u => u ∉ W)).biUnion (fun u =>
      (d.lists xy.1 u).biUnion (fun M =>
        ((d.listing xy.2 M).filter (fun v => v ∉ W ∧ v ≠ u)).image
          (fun v => (xy.1,xy.2,u,M,v)))))

def smallSupport (W : Finset V) (j : WitnessIndex V U) : Finset V := insert j.2.2.2.2 W

def largeSupport (W : Finset V) (j : WitnessIndex V U) : Finset V :=
  insert j.2.2.1 (insert j.2.2.2.2 W)

theorem small_support_card (W : Finset V) (j : WitnessIndex V U)
    (hj : j ∈ d.smallIndices W) : (smallSupport W j).card = W.card+1 := by
  obtain ⟨xy,hxy,hj⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨u,hu,hj⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨M,hM,hj⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hj
  have hvW := (Finset.mem_filter.mp hv).2
  simp [smallSupport,hvW]

theorem large_support_card (W : Finset V) (j : WitnessIndex V U)
    (hj : j ∈ d.largeIndices W) : (largeSupport W j).card = W.card+2 := by
  obtain ⟨xy,hxy,hj⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨u,hu,hj⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨M,hM,hj⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hj
  have huW := (Finset.mem_filter.mp hu).2
  obtain ⟨hvW,hvu⟩ := (Finset.mem_filter.mp hv).2
  simp [largeSupport,huW,hvW,hvu.symm,Nat.add_assoc]

theorem small_indices_card (W : Finset V) (h : ℕ)
    (hinc : ∀ y M, (d.listing y M).card ≤ h) :
    (d.smallIndices W).card ≤ W.card^3*d.listBound*h := by
  have hinner (x y u : V) :
      ((d.lists x u).biUnion (fun M =>
        ((d.listing y M).filter (fun v => v ∉ W)).image
          (fun v => (x,y,u,M,v)))).card ≤ d.listBound*h := by
    calc
      _ ≤ (d.lists x u).card*h := card_biUnion_le_mul _ _ h (by
        intro M hM
        exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans (hinc y M)))
      _ ≤ _ := Nat.mul_le_mul_right h (d.list_card x u)
  calc
    _ ≤ (W.product W).card*(W.card*(d.listBound*h)) := by
      apply card_biUnion_le_mul
      intro xy hxy
      exact card_biUnion_le_mul _ _ _ (fun u _ => hinner xy.1 xy.2 u)
    _ = _ := by rw [Finset.product_eq_sprod,Finset.card_product]; ring

theorem large_indices_card (W : Finset V) (h : ℕ) (g : ℝ)
    (hinc : ∀ y M, (d.listing y M).card ≤ h)
    (hdeg : ∀ x, ((d.neighbors x).card : ℝ) ≤ g) :
    ((d.largeIndices W).card : ℝ) ≤ (W.card : ℝ)^2*g*d.listBound*h := by
  have hinner (x y u : V) :
      ((d.lists x u).biUnion (fun M =>
        ((d.listing y M).filter (fun v => v ∉ W ∧ v ≠ u)).image
          (fun v => (x,y,u,M,v)))).card ≤ d.listBound*h := by
    calc
      _ ≤ (d.lists x u).card*h := card_biUnion_le_mul _ _ h (by
        intro M hM
        exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans (hinc y M)))
      _ ≤ _ := Nat.mul_le_mul_right h (d.list_card x u)
  have hmid (xy : V × V) :
      ((((d.neighbors xy.1).filter (fun u => u ∉ W)).biUnion (fun u =>
        (d.lists xy.1 u).biUnion (fun M =>
          ((d.listing xy.2 M).filter (fun v => v ∉ W ∧ v ≠ u)).image
            (fun v => (xy.1,xy.2,u,M,v))))).card : ℝ) ≤ g*(d.listBound*h) := by
    calc
      _ ≤ (((d.neighbors xy.1).filter (fun u => u ∉ W)).card : ℝ)*(d.listBound*h) := by
        apply card_biUnion_le_mul_real
        intro u hu
        exact_mod_cast hinner xy.1 xy.2 u
      _ ≤ _ := by
        have hf : (((d.neighbors xy.1).filter (fun u => u ∉ W)).card : ℝ) ≤
            ((d.neighbors xy.1).card : ℝ) := by
          exact_mod_cast Finset.card_filter_le (d.neighbors xy.1) (fun u => u ∉ W)
        exact mul_le_mul_of_nonneg_right (hf.trans (hdeg xy.1)) (by positivity)
  calc
    _ ≤ ((W.product W).card : ℝ)*(g*(d.listBound*h)) :=
      card_biUnion_le_mul_real _ _ _ (fun xy _ => hmid xy)
    _ = _ := by simp only [Finset.product_eq_sprod,Finset.card_product,Nat.cast_mul]; ring

theorem witness_has_support (W C : Finset V) (hWC : W ⊆ C)
    (hw : d.ExternalWitness W C) :
    (∃ j ∈ d.smallIndices W, smallSupport W j ⊆ C) ∨
      (∃ j ∈ d.largeIndices W, largeSupport W j ⊆ C) := by
  obtain ⟨x,hx,y,hy,hxy,u,hu,v,hv,huv,hvW,hxu,hyv,M,hM⟩ := hw
  obtain ⟨hMx,hMy⟩ := Finset.mem_inter.mp hM
  have hvlist : v ∈ d.listing y M := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hyv⟩,hMy⟩
  by_cases huW : u ∈ W
  · left
    refine ⟨(x,y,u,M,v),?_,?_⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,?_⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨u,huW,?_⟩
      apply Finset.mem_biUnion.mpr
      exact ⟨M,hMx,Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨hvlist,hvW⟩,rfl⟩⟩
    · exact Finset.insert_subset_iff.mpr ⟨hv,hWC⟩
  · right
    refine ⟨(x,y,u,M,v),?_,?_⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,?_⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨u,Finset.mem_filter.mpr ⟨?_,huW⟩,?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxu⟩
      · apply Finset.mem_biUnion.mpr
        exact ⟨M,hMx,Finset.mem_image.mpr
          ⟨v,Finset.mem_filter.mpr ⟨hvlist,hvW,huv.symm⟩,rfl⟩⟩
    · exact Finset.insert_subset_iff.mpr ⟨hu,Finset.insert_subset_iff.mpr ⟨hv,hWC⟩⟩

end TP3.DependentSample.Data
