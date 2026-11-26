module

public import TP3.FiniteExtraction
public import TP3.RandomClasses

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

def inclusionFormula (b R h : ℕ) (g q τ : ℝ) (j : ℕ) : ℝ :=
  (q*τ^(b*R))^j + (j:ℝ)^2*((j:ℝ)*b*h*q^(j+1)+g*b*h*q^(j+2))

noncomputable def extractionFraction (d a s c g : ℝ) (b R h r : ℕ) (q τ D : ℝ) : ℝ :=
  let φ := q*τ^(b*R)
  φ*(1-g*φ/R) - 3*g*b*h*q^3 - 54*d*b*h*q^4 -
    r*(R*τ*φ+h*φ^2) - g/(2*R)*inclusionFormula b R h g q τ 2 -
    d/s*inclusionFormula b R h g q τ 2 -
    s*(2*a+c*r)*d*inclusionFormula b R h g q τ 5 - d*q^4 -
    d*inclusionFormula b R h g q τ 3/D

theorem inclusionFormula_nonneg (b R h : ℕ) {g q τ : ℝ}
    (hg : 0 ≤ g) (hq : 0 ≤ q) (hτ : 0 ≤ τ) (j : ℕ) :
    0 ≤ inclusionFormula b R h g q τ j := by unfold inclusionFormula; positivity

theorem tripleSystem_edge_bound {H : Finset (Finset V)} (hH : IsTripleSystem H)
    (d : ℝ) (hdegree : ∀ v, (degree H v : ℝ) ≤ d) :
    3*(H.card : ℝ) ≤ (Fintype.card V : ℝ)*d := by
  have hs : ∑ v : V, (degree H v : ℝ)=3*(H.card : ℝ) := by
    exact_mod_cast sum_degree_triples hH
  have hb := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun v _ => hdegree v)
  rw [hs] at hb
  simpa using hb

/-- The extraction estimate after constructing the lists and choosing a
partition. Every remaining hypothesis concerns only numerical parameters. -/
theorem quantitative_extraction (H : Finset (Finset V)) (hH : IsTripleSystem H)
    (hfree : ¬ HasTightPath H) (d a s c g : ℝ) (b R h r : ℕ) (q τ D : ℝ)
    (hd : 0 ≤ d) (hdegree : ∀ v, (degree H v : ℝ) ≤ d)
    (ha : 2 < a) (hs : 0 < s) (hc : 0 < c) (hg : 0 ≤ g)
    (hg_bound : 2*d/a ≤ g) (hb_bound : (g/a)*s/c ≤ b)
    (hr_bound : g/a ≤ r) (hh_bound : s/c ≤ h) (hR : 0 < R)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hD : 0 < D) :
    ∃ T : Finset V, ¬ HasF (induced H T) ∧ ¬ HasThreeOnFour (induced H T) ∧
      IndependentPairNeighborhoods (induced H T) ∧
      (∀ v, (degree (induced H T) v : ℝ) ≤ D) ∧
      (Fintype.card V : ℝ)*extractionFraction d a s c g b R h r q τ D ≤ T.card := by
  have ha0 : 0 < a := by linarith
  let G := mediumPairs H a s
  have hG := mediumPairs_isPairSystem H a s
  have hGdeg (v : V) : (degree G v : ℝ) ≤ g := by
    apply le_trans _ hg_bound
    apply (le_div_iff₀ ha0).mpr
    have hh := mediumPairs_degree_bound hH a s v
    have hv := hdegree v
    dsimp only [G]
    nlinarith
  obtain ⟨P⟩ := exists_denseDecomposition G s a ha0
  have hb (e : Finset V) : (P.pairLists e c).card ≤ b := by
    exact_mod_cast (P.pairLists_card_bound ha0 hs.le c g hc hg hGdeg e).trans hb_bound
  obtain ⟨colour,hcolour⟩ := exists_class_partition hG R hR
  let data := P.extractionData c R colour b hb
  have hinc (v : V) (M : DenseBlock V) : (data.listing v M).card ≤ h :=
    P.extraction_listing_bound c R colour b hb hH hfree ha hc h hh_bound v M
  have hr (v : V) : (data.setIncidences v).card ≤ r := by
    rw [P.extraction_setIncidences c R colour b hb]
    exact_mod_cast (P.block_incidence_le ha0 g hGdeg v).trans hr_bound
  have hdeg (v : V) : ((data.neighbors v).card : ℝ) ≤ g := by
    rw [P.extraction_neighbors_card c R colour b hb]
    exact hGdeg v
  obtain ⟨T,hF,h4,hind,hTdegree,hsize⟩ := P.finite_extraction hH c R colour b hb hR
    h r g hinc hr hdeg q τ hq hq1 hτ hτ1 D hD
  refine ⟨T,hF,h4,hind,hTdegree,le_trans ?_ hsize⟩
  let N : ℝ := Fintype.card V
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hE : 3*(H.card : ℝ) ≤ N*d := tripleSystem_edge_bound hH d hdegree
  have hR0 : 0 < (R:ℝ) := by exact_mod_cast hR
  have hclass : (data.withinClassPairs.card : ℝ) ≤ N*g/(2*R) := by
    rw [P.extraction_withinClassPairs c R colour b hb]
    apply hcolour.trans
    have hh := div_le_div_of_nonneg_right (pairSystem_edge_bound hG g hGdeg) hR0.le
    convert hh using 1 <;> ring
  have hlarge : ((largePairs H s).card : ℝ) ≤ N*d/s := by
    apply (le_div_iff₀ hs).mpr
    have hh := (largePairs_card_bound hH s).trans hE
    nlinarith
  have hFcount : ((fInstances (P.reducedSystem c)).card : ℝ) ≤ s*(2*a+c*r)*(N*d) := by
    apply (P.reduced_f_count hH ha0.le hs.le c r hc.le (Nat.cast_nonneg _)
      (fun x => (P.block_incidence_le ha0 g hGdeg x).trans hr_bound)).trans
    exact mul_le_mul_of_nonneg_left hE (by positivity)
  have htriangle : ((triangleInstances H).card : ℝ) ≤ N*d :=
    (by exact_mod_cast triangleInstances_card_le hH hfree :
      ((triangleInstances H).card : ℝ) ≤ 3*(H.card : ℝ)).trans hE
  have hPB (j : ℕ) : 0 ≤ inclusionFormula b R h g q τ j :=
    inclusionFormula_nonneg b R h hg hq hτ j
  have hcost1 := mul_le_mul_of_nonneg_right hclass (hPB 2)
  have hcost2 := mul_le_mul_of_nonneg_right hlarge (hPB 2)
  have hcost3 := mul_le_mul_of_nonneg_right hFcount (hPB 5)
  have hcost4 := mul_le_mul_of_nonneg_right htriangle (pow_nonneg hq 4)
  have hcost5 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hE (hPB 3)) hD.le
  have hcost6 := mul_le_mul_of_nonneg_right hE
    (show 0 ≤ 54*(b:ℝ)*h*q^4 by positivity)
  change N*extractionFraction d a s c g b R h r q τ D ≤
    data.sizeBound h r g q τ - _ - _ - _ - _
  have hPB_eq (j : ℕ) : data.pointBound h g q τ j=inclusionFormula b R h g q τ j := rfl
  simp only [DependentSample.Data.sizeBound,hPB_eq]
  change N*extractionFraction d a s c g b R h r q τ D ≤
    N*(q*τ^(b*R))*(1-g*(q*τ^(b*R))/R) -
    (3*N*g*b*h*q^3+162*(H.card:ℝ)*b*h*q^4) -
    N*r*(R*τ*(q*τ^(b*R))+h*(q*τ^(b*R))^2) -
    (data.withinClassPairs.card:ℝ)*inclusionFormula b R h g q τ 2 -
    (largePairs H s).card*inclusionFormula b R h g q τ 2 -
    (fInstances (P.reducedSystem c)).card*inclusionFormula b R h g q τ 5 -
    (triangleInstances H).card*q^4 -
    3*((H.card:ℝ)*inclusionFormula b R h g q τ 3)/D
  unfold extractionFraction
  linear_combination hcost1+hcost2+hcost3+hcost4+hcost5+hcost6

end TP3
