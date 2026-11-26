module

public import TP3.ConflictDeletion
public import TP3.SupportCounting

@[expose] public section

namespace TP3.DependentSample.Data

attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
variable (d : Data V U)

abbrev ThreeIndex (V U : Type*) := V × V × U × V
abbrev FourIndex (V U : Type*) := Finset V × V × V × V × U × V

noncomputable def threeIndices : Finset (ThreeIndex V U) :=
  Finset.univ.biUnion (fun x => (d.neighbors x).biUnion (fun u =>
    (d.lists x u).biUnion (fun M =>
      ((d.listing u M).filter (fun y => y ≠ x)).image (fun y => (x,u,M,y)))))

def threeSupport (j : ThreeIndex V U) : Finset V := {j.1,j.2.1,j.2.2.2}

noncomputable def fourIndices : Finset (FourIndex V U) :=
  d.triples.biUnion (fun e => e.biUnion (fun a => e.biUnion (fun b =>
    e.biUnion (fun c => (d.lists a b).biUnion (fun M =>
      ((d.listing c M).filter (fun z => z ∉ e)).image (fun z => (e,a,b,c,M,z)))))))

def fourSupport (j : FourIndex V U) : Finset V := insert j.2.2.2.2.2 j.1

theorem three_support_card (j : ThreeIndex V U) (hj : j ∈ d.threeIndices) :
    (threeSupport j).card=3 := by
  obtain ⟨x,hx,hj⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨u,hu,hj⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨M,hM,hj⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hj
  have hxu := (Finset.mem_filter.mp hu).2
  have huy := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).1).2
  have hyx := (Finset.mem_filter.mp hy).2
  simp [threeSupport,hxu.ne,huy.ne,hyx.symm]

theorem four_support_card (hH : IsTripleSystem d.triples)
    (j : FourIndex V U) (hj : j ∈ d.fourIndices) : (fourSupport j).card=4 := by
  obtain ⟨e,he,hj⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨a,ha,hj⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨b,hb,hj⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨c,hc,hj⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨M,hM,hj⟩ := Finset.mem_biUnion.mp hj
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hj
  simp [fourSupport,(Finset.mem_filter.mp hz).2,hH e he]

theorem three_indices_card (h : ℕ) (g : ℝ)
    (hinc : ∀ y M, (d.listing y M).card ≤ h)
    (hdeg : ∀ x, ((d.neighbors x).card : ℝ) ≤ g) :
    ((d.threeIndices).card : ℝ) ≤ (Fintype.card V : ℝ)*g*d.listBound*h := by
  have hi (x u : V) :
      ((d.lists x u).biUnion (fun M =>
        ((d.listing u M).filter (fun y => y ≠ x)).image (fun y => (x,u,M,y)))).card ≤
      d.listBound*h := by
    calc
      _ ≤ (d.lists x u).card*h := card_biUnion_le_mul _ _ h (by
        intro M hM
        exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans (hinc u M)))
      _ ≤ _ := Nat.mul_le_mul_right h (d.list_card x u)
  calc
    _ ≤ (Fintype.card V : ℝ)*(g*(d.listBound*h)) := by
      apply le_trans (card_biUnion_le_mul_real _ _ (g*(d.listBound*h)) ?_) (by simp)
      intro x hx
      calc
        _ ≤ ((d.neighbors x).card : ℝ)*(d.listBound*h) := by
          apply card_biUnion_le_mul_real
          intro u hu
          exact_mod_cast hi x u
        _ ≤ _ := mul_le_mul_of_nonneg_right (hdeg x) (by positivity)
    _ = _ := by ring

theorem four_indices_card (hH : IsTripleSystem d.triples) (h : ℕ)
    (hinc : ∀ y M, (d.listing y M).card ≤ h) :
    (d.fourIndices).card ≤ 27*d.triples.card*d.listBound*h := by
  have hi (e : Finset V) (a b c : V) :
      ((d.lists a b).biUnion (fun M =>
        ((d.listing c M).filter (fun z => z ∉ e)).image (fun z => (e,a,b,c,M,z)))).card ≤
      d.listBound*h := by
    calc
      _ ≤ (d.lists a b).card*h := card_biUnion_le_mul _ _ h (by
        intro M hM
        exact Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans (hinc c M)))
      _ ≤ _ := Nat.mul_le_mul_right h (d.list_card a b)
  calc
    _ ≤ d.triples.card*(27*(d.listBound*h)) := by
      apply card_biUnion_le_mul
      intro e he
      have hh := card_biUnion_le_mul e
        (fun a => e.biUnion (fun b => e.biUnion (fun c =>
          (d.lists a b).biUnion (fun M =>
            ((d.listing c M).filter (fun z => z ∉ e)).image (fun z => (e,a,b,c,M,z))))))
        (e.card*(e.card*(d.listBound*h))) (by
          intro a ha
          apply card_biUnion_le_mul
          intro b hb
          exact card_biUnion_le_mul _ _ _ (fun c hc => hi e a b c))
      simpa [hH e he,← Nat.mul_assoc] using hh
    _ = _ := by ring

theorem mem_threeIndices {x u y : V} {M : U}
    (hxu : d.graph.Adj x u) (huy : d.graph.Adj u y)
    (hyx : y ≠ x) (hM₁ : M ∈ d.lists x u) (hM₂ : M ∈ d.lists u y) :
    (x,u,M,y) ∈ d.threeIndices := by
  apply Finset.mem_biUnion.mpr
  refine ⟨x,Finset.mem_univ _,?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨u,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxu⟩,?_⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨M,hM₁,Finset.mem_image.mpr ⟨y,?_,rfl⟩⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,huy⟩,hM₂⟩,hyx⟩

theorem mem_fourIndices {e : Finset V} {a b c z : V} {M : U}
    (he : e ∈ d.triples) (ha : a ∈ e) (hb : b ∈ e) (hc : c ∈ e)
    (hcz : d.graph.Adj c z) (hz : z ∉ e)
    (hM₁ : M ∈ d.lists a b) (hM₂ : M ∈ d.lists c z) :
    (e,a,b,c,M,z) ∈ d.fourIndices := by
  apply Finset.mem_biUnion.mpr
  refine ⟨e,he,Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_biUnion.mpr
    ⟨b,hb,Finset.mem_biUnion.mpr ⟨c,hc,Finset.mem_biUnion.mpr
      ⟨M,hM₁,Finset.mem_image.mpr ⟨z,?_,rfl⟩⟩⟩⟩⟩⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcz⟩,hM₂⟩,hz⟩

/-- A triple contained in two disjoint pairs contains a full pair and one
endpoint of the other. Encoding all ordered choices costs only a constant. -/
theorem four_witness_of_triple (hH : IsTripleSystem d.triples)
    (hsym : ∀ a b, d.lists a b = d.lists b a)
    {x u y v : V} {M : U}
    (hd : [x,u,y,v].Pairwise (· ≠ ·))
    (hxu : d.graph.Adj x u) (hyv : d.graph.Adj y v)
    (hMx : M ∈ d.lists x u) (hMy : M ∈ d.lists y v)
    {e : Finset V} (he : e ∈ d.triples) (hes : e ⊆ {x,u,y,v}) :
    ∃ j ∈ d.fourIndices, fourSupport j = {x,u,y,v} := by
  have hcard : ({x,u,y,v} : Finset V).card=4 := by
    simpa using List.toFinset_card_of_nodup hd
  have hdiff : (({x,u,y,v} : Finset V) \ e).card=1 := by
    rw [Finset.card_sdiff_of_subset hes,hcard,hH e he]
  obtain ⟨w,hw⟩ := Finset.card_eq_one.mp hdiff
  have hwmem : w ∈ ({x,u,y,v} : Finset V) := by
    have hh : w ∈ ({x,u,y,v} : Finset V) \ e := by rw [hw]; simp
    exact (Finset.mem_sdiff.mp hh).1
  have hwout : w ∉ e := by
    have hh : w ∈ ({x,u,y,v} : Finset V) \ e := by rw [hw]; simp
    exact (Finset.mem_sdiff.mp hh).2
  have hcover : insert w e = ({x,u,y,v} : Finset V) := by
    have hh := Finset.sdiff_union_of_subset hes
    rw [hw] at hh
    simpa only [Finset.singleton_union] using hh
  have hkeep {z : V} (hz : z ∈ ({x,u,y,v} : Finset V)) (hzw : z ≠ w) : z ∈ e := by
    by_contra hnot
    have hh : z ∈ ({x,u,y,v} : Finset V) \ e := Finset.mem_sdiff.mpr ⟨hz,hnot⟩
    rw [hw,Finset.mem_singleton] at hh
    exact hzw hh
  simp only [List.pairwise_cons,List.mem_cons,List.not_mem_nil,forall_eq_or_imp] at hd
  simp only [Finset.mem_insert,Finset.mem_singleton] at hwmem
  rcases hwmem with hwx | hwu | hwy | hwv <;> subst w
  · refine ⟨(e,y,v,u,M,x),?_,hcover⟩
    exact d.mem_fourIndices he (hkeep (by simp) (by aesop)) (hkeep (by simp) (by aesop))
      (hkeep (by simp) (by aesop)) hxu.symm hwout hMy (by simpa only [hsym u x] using hMx)
  · refine ⟨(e,y,v,x,M,u),?_,hcover⟩
    exact d.mem_fourIndices he (hkeep (by simp) (by aesop)) (hkeep (by simp) (by aesop))
      (hkeep (by simp) (by aesop)) hxu hwout hMy hMx
  · refine ⟨(e,x,u,v,M,y),?_,hcover⟩
    exact d.mem_fourIndices he (hkeep (by simp) (by aesop)) (hkeep (by simp) (by aesop))
      (hkeep (by simp) (by aesop)) hyv.symm hwout hMx (by simpa only [hsym v y] using hMy)
  · refine ⟨(e,x,u,y,M,v),?_,hcover⟩
    exact d.mem_fourIndices he (hkeep (by simp) (by aesop)) (hkeep (by simp) (by aesop))
      (hkeep (by simp) (by aesop)) hyv hwout hMx hMy

end TP3.DependentSample.Data
