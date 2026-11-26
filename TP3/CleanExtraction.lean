module

public import TP3.DeletionEstimates

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem hasF_mono {H K : Finset (Finset V)} (hHK : H ⊆ K) (hF : HasF H) : HasF K := by
  obtain ⟨a,b,x,y,z,hd,h1,h2,h3⟩ := hF
  exact ⟨a,b,x,y,z,hd,hHK h1,hHK h2,hHK h3⟩

theorem hasThreeOnFour_mono {H K : Finset (Finset V)} (hHK : H ⊆ K)
    (h4 : HasThreeOnFour H) : HasThreeOnFour K := by
  obtain ⟨v,a,b,c,hd,h1,h2,h3⟩ := h4
  exact ⟨v,a,b,c,hd,hHK h1,hHK h2,hHK h3⟩

theorem present_instances_mono {I : Type*} [DecidableEq I] (E : Finset I)
    (support : I → Finset V) {S T : Finset V} (hST : S ⊆ T) :
    (E.filter (fun j => support j ⊆ S)).card ≤
      (E.filter (fun j => support j ⊆ T)).card := by
  apply Finset.card_le_card
  intro j hj
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1,(Finset.mem_filter.mp hj).2.trans hST⟩

namespace DenseDecomposition

variable {H : Finset (Finset V)} {a s : ℝ}
variable (P : DenseDecomposition (mediumPairs H a s) s a)

/-- The deterministic part of extraction. All losses are measured on
the original selected set S, so their expectations can be estimated
directly under the dependent law. -/
theorem clean_extraction (hH : IsTripleSystem H) (c : ℝ) (S : Finset V)
    (hexclude : ∀ x ∈ S, ∀ y ∈ S, (pairGraph (mediumPairs H a s)).Adj x y →
      ∀ B ∈ P.pairLists {x,y} c, Disjoint S B.1)
    (D : ℝ) (hD : 0 < D) :
    ∃ T ⊆ S, ¬ HasF (induced H T) ∧ ¬ HasThreeOnFour (induced H T) ∧
      IndependentPairNeighborhoods (induced H T) ∧
      (∀ v, (degree (induced H T) v : ℝ) ≤ D) ∧
      (S.card : ℝ) ≤ T.card + ((largePairs H s).filter (fun e => e ⊆ S)).card +
        ((fInstances (P.reducedSystem c)).filter (fun j => fSupport j ⊆ S)).card +
        ((triangleInstances H).filter (fun j => triangleSupport j ⊆ S)).card +
        3*(induced H S).card/D := by
  obtain ⟨S₁,h₁,hlarge,hsize₁⟩ := delete_largePairs H s S
  have heq (X : Finset V) (hX : X ⊆ S₁) : induced H X=induced (P.reducedSystem c) X := by
    apply P.extraction_induced_eq c X
    · intro e he heX
      exact hlarge e he (heX.trans hX)
    · intro x hx y hy hxy B hB
      have hd := hexclude x (h₁ (hX hx)) y (h₁ (hX hy)) hxy B hB
      exact Finset.disjoint_left.mpr (fun z hz => Finset.disjoint_left.mp hd (h₁ (hX hz)))
  obtain ⟨S₂,h₂,hF,hsize₂⟩ := delete_present_F (P.reducedSystem c) S₁
  have hF₂ : ¬ HasF (induced H S₂) := by rwa [heq S₂ h₂]
  obtain ⟨S₃,h₃,h4,hsize₃⟩ := delete_present_triangles H S₂
  obtain ⟨T,hT,hdegree,hsizeT⟩ := delete_high_degree hH S₃ D hD
  have hTS := hT.trans (h₃.trans (h₂.trans h₁))
  have hFT : ¬ HasF (induced H T) := fun h =>
    hF₂ (hasF_mono (induced_mono_vertices H (hT.trans h₃)) h)
  have h4T : ¬ HasThreeOnFour (induced H T) := fun h =>
    h4 (hasThreeOnFour_mono (induced_mono_vertices H hT) h)
  refine ⟨T,hTS,hFT,h4T,independent_pair_neighborhoods_of_exclusions
    (induced_isTripleSystem hH T) hFT h4T,hdegree,?_⟩
  have hfcount := present_instances_mono (fInstances (P.reducedSystem c)) fSupport h₁
  have htcount := present_instances_mono (triangleInstances H) triangleSupport (h₂.trans h₁)
  have hedge : ((induced H S₃).card : ℝ) ≤ (induced H S).card := by
    exact_mod_cast Finset.card_le_card (induced_mono_vertices H (h₃.trans (h₂.trans h₁)))
  have hdcount : 3*((induced H S₃).card : ℝ)/D ≤ 3*(induced H S).card/D :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hedge (by norm_num)) hD.le
  have hs₁ : (S.card : ℝ) ≤ S₁.card + ((largePairs H s).filter (fun e => e ⊆ S)).card := by
    exact_mod_cast hsize₁
  have hs₂ : (S₁.card : ℝ) ≤ S₂.card +
      ((fInstances (P.reducedSystem c)).filter (fun j => fSupport j ⊆ S)).card := by
    exact_mod_cast hsize₂.trans (Nat.add_le_add_left hfcount _)
  have hs₃ : (S₂.card : ℝ) ≤ S₃.card +
      ((triangleInstances H).filter (fun j => triangleSupport j ⊆ S)).card := by
    exact_mod_cast hsize₃.trans (Nat.add_le_add_left htcount _)
  linarith

end DenseDecomposition
end TP3
