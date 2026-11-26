module

public import TP3.ExtractionData
public import TP3.ProductSplit

@[expose] public section

namespace TP3.FiniteLaw

attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β]

theorem event_singleton (μ : FiniteLaw β) (b : β) : μ.event (fun x => x=b)=μ.prob b := by
  classical
  unfold event
  rw [Finset.sum_filter]
  rw [Finset.sum_eq_single b]
  · simp
  · intro a ha hab
    simp [hab]
  · simp

theorem product_required_value (μ : ι → FiniteLaw β) (A : Finset ι) (b : β) :
    (product μ).event (fun ω => ∀ i ∈ A, ω i=b)=∏ i ∈ A, (μ i).prob b := by
  rw [product_event _ (fun i x => i ∈ A → x=b)]
  have hi (i : ι) : (μ i).event (fun x => i ∈ A → x=b)=if i ∈ A then (μ i).prob b else 1 := by
    by_cases h : i ∈ A
    · simp only [h,true_implies,ite_true,event_singleton]
    · simp only [h,false_implies,ite_false]
      simpa using (μ i).event_const True
  simp_rw [hi]
  exact Finset.prod_ite_mem_eq A (fun i => (μ i).prob b)

theorem colour_pair_probability (R : ℕ) (hR : 0 < R) (x y : ι) (hxy : x ≠ y) :
    (product (fun _ : ι => uniform (Finset.univ : Finset (Fin R))
      (Finset.card_pos.mp (by simpa using hR)))).event (fun ω => ω x=ω y)=1/(R:ℝ) := by
  let ν := uniform (Finset.univ : Finset (Fin R)) (Finset.card_pos.mp (by simpa using hR))
  let μ := product (fun _ : ι => ν)
  have hc (b : Fin R) : μ.event (fun ω => ω x=b ∧ ω y=b)=1/(R:ℝ)^2 := by
    have hh := product_required_value (fun _ : ι => ν) {x,y} b
    simp only [Finset.mem_insert,Finset.mem_singleton,forall_eq_or_imp,forall_eq] at hh
    have hν : ν.prob b=1/(R:ℝ) := by simp [ν,uniform]
    rw [hν] at hh
    simp [hxy] at hh
    convert hh using 1 <;> ring
  have hsplit (ω : ι → Fin R) : (if ω x=ω y then (1:ℝ) else 0)=
      ∑ b : Fin R, if ω x=b ∧ ω y=b then 1 else 0 := by
    by_cases hh : ω x=ω y
    · simp [hh]
    · have hn (b : Fin R) : ¬ (ω x=b ∧ ω y=b) := fun h => hh (h.1.trans h.2.symm)
      simp [hh,hn]
  change μ.event (fun ω => ω x=ω y)=_
  rw [← μ.mean_indicator]
  simp_rw [hsplit]
  rw [μ.mean_sum]
  simp_rw [μ.mean_indicator,hc]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hR0 : (R:ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  field_simp

end TP3.FiniteLaw

namespace TP3

attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def monochromaticPairs {R : ℕ} (G : Finset (Finset V)) (colour : V → Fin R) :
    Finset (Finset V) := G.filter (fun e => ∀ x ∈ e, ∀ y ∈ e, colour x=colour y)

/-- A partition into R classes with at most a 1/R fraction of the
graph edges inside classes. The expectation is computed under the
independent uniform colouring and then attained by an outcome. -/
theorem exists_class_partition {G : Finset (Finset V)} (hG : IsPairSystem G)
    (R : ℕ) (hR : 0 < R) :
    ∃ colour : V → Fin R, ((monochromaticPairs G colour).card : ℝ) ≤ (G.card : ℝ)/R := by
  let ν := FiniteLaw.uniform (Finset.univ : Finset (Fin R)) (Finset.card_pos.mp (by simpa using hR))
  let μ := FiniteLaw.product (fun _ : V => ν)
  have hp (e : Finset V) (he : e ∈ G) :
      μ.event (fun colour => ∀ x ∈ e, ∀ y ∈ e, colour x=colour y)=1/(R:ℝ) := by
    obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp (hG e he)
    have heq : (fun colour : V → Fin R => ∀ a ∈ ({x,y} : Finset V), ∀ b ∈ ({x,y} : Finset V), colour a=colour b)=
        (fun colour => colour x=colour y) := by
      funext colour
      apply propext
      constructor
      · intro hh
        exact hh x (by simp) y (by simp)
      · intro hh a ha b hb
        simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all
    rw [heq]
    exact FiniteLaw.colour_pair_probability R hR x y hxy
  have hmean : μ.mean (fun colour => ((monochromaticPairs G colour).card : ℝ))=(G.card : ℝ)/R := by
    have hh := μ.mean_filter_card G
      (fun (e : Finset V) (colour : V → Fin R) => ∀ x ∈ e, ∀ y ∈ e, colour x=colour y)
    calc
      _ = ∑ e ∈ G, μ.event (fun colour => ∀ x ∈ e, ∀ y ∈ e, colour x=colour y) := by
        convert hh using 1
        congr 1
        funext colour
        congr 1
        congr 1
        ext e
        simp [monochromaticPairs]
      _ = ∑ _e ∈ G, 1/(R:ℝ) := Finset.sum_congr rfl hp
      _ = _ := by simp; ring
  obtain ⟨colour,_,hh⟩ := μ.exists_support_ge_mean (fun colour => -((monochromaticPairs G colour).card : ℝ))
  have hn : μ.mean (fun colour => -((monochromaticPairs G colour).card : ℝ))=
      -μ.mean (fun colour => ((monochromaticPairs G colour).card : ℝ)) := by
    simpa only [neg_one_mul] using μ.mean_mul_const (-1) (fun colour => ((monochromaticPairs G colour).card : ℝ))
  rw [hn,hmean] at hh
  exact ⟨colour,by linarith⟩

theorem pairSystem_edge_bound {G : Finset (Finset V)} (hG : IsPairSystem G)
    (g : ℝ) (hdegree : ∀ v, (degree G v : ℝ) ≤ g) :
    (G.card : ℝ) ≤ (Fintype.card V : ℝ)*g/2 := by
  have hh := sum_degree_eq_sum_card G
  have hs : ∑ v : V, degree G v = 2*G.card := by
    rw [hh]
    calc
      _ = ∑ _e ∈ G, 2 := Finset.sum_congr rfl hG
      _ = _ := by simp [Nat.mul_comm]
  have hs' : ∑ v : V, (degree G v : ℝ) = 2*(G.card : ℝ) := by exact_mod_cast hs
  have hb := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun v _ => hdegree v)
  rw [hs'] at hb
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hb
  linarith

namespace DenseDecomposition

variable {H : Finset (Finset V)} {a s : ℝ}
variable (P : DenseDecomposition (mediumPairs H a s) s a)

theorem extraction_withinClassPairs (c : ℝ) (R : ℕ) (colour : V → Fin R)
    (b : ℕ) (hb : ∀ e, (P.pairLists e c).card ≤ b) :
    (P.extractionData c R colour b hb).withinClassPairs =
      monochromaticPairs (mediumPairs H a s) colour := by
  ext e
  constructor
  · intro he
    obtain ⟨he2,x,hx,y,hy,hxy,hcolour⟩ := Finset.mem_filter.mp he
    have hcard := (Finset.mem_powersetCard.mp he2).2
    have hxy' : x ≠ y ∧ {x,y} ∈ mediumPairs H a s := hxy
    have heq : ({x,y} : Finset V)=e := Finset.eq_of_subset_of_card_le
      (Finset.insert_subset_iff.mpr ⟨hx,Finset.singleton_subset_iff.mpr hy⟩)
      (by simpa [hxy'.1] using hcard.le)
    apply Finset.mem_filter.mpr
    refine ⟨heq ▸ hxy'.2,?_⟩
    intro u hu v hv
    rw [← heq] at hu hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> first | exact hcolour | exact hcolour.symm | rfl
  · intro he
    obtain ⟨heG,hmono⟩ := Finset.mem_filter.mp he
    obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp (mediumPairs_isPairSystem H a s e heG)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,by simp [hxy]⟩,
      x,by simp,y,by simp,?_,hmono x (by simp) y (by simp)⟩
    exact ⟨hxy,heG⟩

end DenseDecomposition

end TP3
