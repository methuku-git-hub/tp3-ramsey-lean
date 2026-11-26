module

public import TP3.ReducedFCount
public import TP3.SamplingLemma

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem mem_fInstances {H : Finset (Finset V)} {e f : Finset V} {z : V} :
    (e,f,z) ∈ fInstances H ↔ e.card=2 ∧ f ⊆ completions H e ∧ f.card=2 ∧
      z ∈ completions H f ∧ z ∉ e := by
  simp [fInstances, Finset.mem_powersetCard, and_assoc]

theorem fInstance_vertices {H : Finset (Finset V)} {j : FIndex V}
    (hj : j ∈ fInstances H) :
    ∃ a b x y z : V, [a,b,x,y,z].Pairwise (· ≠ ·) ∧
      {a,b,x} ∈ H ∧ {a,b,y} ∈ H ∧ {x,y,z} ∈ H ∧
        fSupport j={a,b,x,y,z} := by
  rcases j with ⟨e,f,z⟩
  obtain ⟨he,hfe,hf,hz,hze⟩ := mem_fInstances.mp hj
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp he
  obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp hf
  have hx := mem_completions.mp (hfe (Finset.mem_insert_self x {y}))
  have hy := mem_completions.mp (hfe (show y ∈ ({x,y} : Finset V) by simp))
  have hz' := mem_completions.mp hz
  refine ⟨a,b,x,y,z,?_,?_,?_,?_,?_⟩
  · simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hx hy hz' hze
    simp only [List.pairwise_cons,List.mem_cons,List.not_mem_nil,forall_eq_or_imp]
    aesop
  · rw [triple_rotate a b x]; exact hx.2
  · rw [triple_rotate a b y]; exact hy.2
  · rw [triple_rotate x y z]; exact hz'.2
  · ext w
    simp [fSupport]
    tauto

theorem fSupport_card {H : Finset (Finset V)} {j : FIndex V}
    (hj : j ∈ fInstances H) : (fSupport j).card=5 := by
  obtain ⟨a,b,x,y,z,hd,_,_,_,heq⟩ := fInstance_vertices hj
  rw [heq]
  simpa using List.toFinset_card_of_nodup hd

theorem fSupport_fourVertex {H : Finset (Finset V)} {j : FIndex V}
    (hj : j ∈ fInstances H) : FourVertexProperty H (fSupport j) := by
  obtain ⟨a,b,x,y,z,hd,h1,h2,h3,heq⟩ := fInstance_vertices hj
  rw [heq]
  exact fourVertexProperty_F hd h1 h2 h3

theorem hasF_induced_iff (H : Finset (Finset V)) (S : Finset V) :
    HasF (induced H S) ↔ ∃ j ∈ fInstances H, fSupport j ⊆ S := by
  constructor
  · rintro ⟨a,b,x,y,z,hd,h1,h2,h3⟩
    obtain ⟨h1,h1S⟩ := Finset.mem_filter.mp h1
    obtain ⟨h2,h2S⟩ := Finset.mem_filter.mp h2
    obtain ⟨h3,h3S⟩ := Finset.mem_filter.mp h3
    simp only [List.pairwise_cons,List.mem_cons,List.not_mem_nil,forall_eq_or_imp] at hd
    refine ⟨({a,b},{x,y},z),?_,?_⟩
    · rw [mem_fInstances]
      refine ⟨by simp [hd.1.1],?_,by simp [hd.2.2.1.1],?_,?_⟩
      · intro w hw
        simp only [Finset.mem_insert,Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact mem_completions.mpr ⟨by simp; aesop,by rwa [← triple_rotate a b w]⟩
        · exact mem_completions.mpr ⟨by simp; aesop,by rwa [← triple_rotate a b w]⟩
      · exact mem_completions.mpr ⟨by simp; aesop,by rwa [← triple_rotate x y z]⟩
      · simp; aesop
    · intro w hw
      simp only [fSupport,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hw
      rcases hw with (rfl | rfl) | rfl | rfl | rfl
      · exact h1S (by simp)
      · exact h1S (by simp)
      · exact h3S (by simp)
      · exact h1S (by simp)
      · exact h2S (by simp)
  · rintro ⟨j,hj,hjS⟩
    obtain ⟨a,b,x,y,z,hd,h1,h2,h3,heq⟩ := fInstance_vertices hj
    rw [heq] at hjS
    refine ⟨a,b,x,y,z,hd,?_,?_,?_⟩
    · exact Finset.mem_filter.mpr ⟨h1,Finset.Subset.trans (show ({a,b,x} : Finset V) ⊆ {a,b,x,y,z} by simp) hjS⟩
    · exact Finset.mem_filter.mpr ⟨h2,Finset.Subset.trans (show ({a,b,y} : Finset V) ⊆ {a,b,x,y,z} by simp) hjS⟩
    · exact Finset.mem_filter.mpr ⟨h3,Finset.Subset.trans (show ({x,y,z} : Finset V) ⊆ {a,b,x,y,z} by intro w hw; simp only [Finset.mem_insert,Finset.mem_singleton] at hw ⊢; tauto) hjS⟩

/-- One deletion for each present instance eliminates every copy of F.
The family of supports may identify several instances, which only reduces
the number of deletions. -/
theorem delete_present_F (H : Finset (Finset V)) (S : Finset V) :
    ∃ T ⊆ S, ¬ HasF (induced H T) ∧
      S.card ≤ T.card + ((fInstances H).filter (fun j => fSupport j ⊆ S)).card := by
  let J := (fInstances H).filter (fun j => fSupport j ⊆ S)
  let E := J.image fSupport
  have hE : ∀ e ∈ E, e.Nonempty := by
    intro e he
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp he
    exact Finset.card_pos.mp (by rw [fSupport_card (Finset.mem_filter.mp hj).1]; omega)
  refine ⟨deleteForbidden E hE S,deleteForbidden_subset E hE S,?_,?_⟩
  · intro hF
    obtain ⟨j,hj,hjT⟩ := (hasF_induced_iff H _).mp hF
    have hjS := hjT.trans (deleteForbidden_subset E hE S)
    have hjE : fSupport j ∈ E := Finset.mem_image.mpr
      ⟨j,Finset.mem_filter.mpr ⟨hj,hjS⟩,rfl⟩
    exact deleteForbidden_independent E hE S _ hjE hjT
  · exact (deleteForbidden_size E hE S).trans
      (Nat.add_le_add_left Finset.card_image_le _)

namespace DependentSample.Data

variable {U : Type*} [Fintype U] [DecidableEq U] (d : Data V U)

/-- The five factors in the survival estimate are justified by the
actual dependent law; the remaining terms account for shared marks. -/
theorem mean_F_instances {K : Finset (Finset V)} (hK : K ⊆ d.triples)
    (h : ℕ) (g : ℝ)
    (hinc : ∀ y M, (d.listing y M).card ≤ h)
    (hdeg : ∀ x, ((d.neighbors x).card : ℝ) ≤ g)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) d.classes).mean
      (fun ξ => (((fInstances K).filter
        (fun j => fSupport j ⊆ d.finalSet d.classes ξ)).card : ℝ)) ≤
    (fInstances K).card * ((q*τ^d.maxListSize)^5 +
      25*(5*d.listBound*h*q^6 + g*d.listBound*h*q^7)) := by
  let μ := historyLaw (finiteClassLaw (V := V) (U := U) d.maxListSize q τ hq hq1 hτ hτ1) d.classes
  have hm := μ.mean_filter_card (fInstances K)
    (fun (j : FIndex V) (ξ : History (ClassNoise V U d.maxListSize) d.classes) =>
      fSupport j ⊆ d.finalSet d.classes ξ)
  calc
    _ = ∑ j ∈ fInstances K, μ.event (fun ξ => fSupport j ⊆ d.finalSet d.classes ξ) := by
      convert hm using 1
      congr 1
      funext ξ
      congr 1
      congr 1
      ext j
      simp
    _ ≤ ∑ _j ∈ fInstances K, ((q*τ^d.maxListSize)^5 +
        25*(5*d.listBound*h*q^6 + g*d.listBound*h*q^7)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hf : FourVertexProperty d.triples (fSupport j) := by
        intro T hT hcard
        obtain ⟨e,he,heT⟩ := fSupport_fourVertex hj T hT hcard
        exact ⟨e,hK he,heT⟩
      have hp := d.chosen_probability (fSupport j) hf h g hinc hdeg q τ hq hq1 hτ hτ1
      apply le_trans (μ.event_mono (fun ξ hξ =>
        hξ.trans (d.finalSet_subset_chosen d.classes ξ)))
      norm_num only [fSupport_card hj,Nat.cast_ofNat] at hp
      exact hp
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]

end DependentSample.Data
end TP3
