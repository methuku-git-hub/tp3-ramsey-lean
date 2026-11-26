module

public import TP3.CleanExtraction
public import TP3.FiniteMeanAlgebra

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable

namespace DependentSample.Data

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

/-- The inclusion upper bound, including collisions of shared marks. -/
def pointBound (d : Data V U) (h : ℕ) (g q τ : ℝ) (m : ℕ) : ℝ :=
  (q*τ^d.maxListSize)^m + (m : ℝ)^2*
    ((m : ℝ)*d.listBound*h*q^(m+1) + g*d.listBound*h*q^(m+2))

noncomputable def sizeBound (d : Data V U) (h r : ℕ) (g q τ : ℝ) : ℝ :=
  let φ := q*τ^d.maxListSize
  (Fintype.card V : ℝ)*φ*(1-g*φ/d.classes) -
    (3*(Fintype.card V : ℝ)*g*d.listBound*h*q^3 +
      162*(d.triples.card : ℝ)*d.listBound*h*q^4) -
    (Fintype.card V : ℝ)*r*(d.classes*τ*φ + h*φ^2) -
    (d.withinClassPairs.card : ℝ)*d.pointBound h g q τ 2

end DependentSample.Data

namespace DenseDecomposition

open DependentSample
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : Finset (Finset V)} {a s : ℝ}
variable (P : DenseDecomposition (mediumPairs H a s) s a)

/-- A finite, quantitative extraction statement for the constructed
dependent law. No independent-sampling assumption occurs here. Choosing
the numerical parameters is separate from this probability calculation. -/
theorem finite_extraction (hH : IsTripleSystem H)
    (c : ℝ) (R : ℕ) (colour : V → Fin R) (b : ℕ)
    (hb : ∀ e, (P.pairLists e c).card ≤ b) (hR : 0 < R)
    (h r : ℕ) (g : ℝ)
    (hinc : ∀ y M, ((P.extractionData c R colour b hb).listing y M).card ≤ h)
    (hr : ∀ x, ((P.extractionData c R colour b hb).setIncidences x).card ≤ r)
    (hdeg : ∀ x, (((P.extractionData c R colour b hb).neighbors x).card : ℝ) ≤ g)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (D : ℝ) (hD : 0 < D) :
    let d := P.extractionData c R colour b hb
    ∃ T : Finset V, ¬ HasF (induced H T) ∧ ¬ HasThreeOnFour (induced H T) ∧
      IndependentPairNeighborhoods (induced H T) ∧
      (∀ v, (degree (induced H T) v : ℝ) ≤ D) ∧
      d.sizeBound h r g q τ -
        (largePairs H s).card*d.pointBound h g q τ 2 -
        (fInstances (P.reducedSystem c)).card*d.pointBound h g q τ 5 -
        (triangleInstances H).card*q^4 -
        3*((H.card : ℝ)*d.pointBound h g q τ 3)/D ≤ T.card := by
  let d := P.extractionData c R colour b hb
  let μ := historyLaw (finiteClassLaw (V := V) (U := DenseBlock V) d.maxListSize q τ hq hq1 hτ hτ1) R
  let S := fun ξ => d.finalSet R ξ
  let L := fun ξ => (((largePairs H s).filter (fun e => e ⊆ S ξ)).card : ℝ)
  let F := fun ξ => (((fInstances (P.reducedSystem c)).filter (fun j => fSupport j ⊆ S ξ)).card : ℝ)
  let A := fun ξ => (((triangleInstances H).filter (fun j => triangleSupport j ⊆ S ξ)).card : ℝ)
  let E := fun ξ => ((induced H (S ξ)).card : ℝ)
  let score := fun ξ => ((S ξ).card : ℝ) - L ξ - F ξ - A ξ - 3*E ξ/D
  have hsize : d.sizeBound h r g q τ ≤ μ.mean (fun ξ => ((S ξ).card : ℝ)) := by
    have hh := d.mean_finalSet_size hH (P.extraction_lists_symm c R colour b hb)
      hR h r g hinc hr hdeg q τ hq hq1 hτ hτ1
    convert hh using 1
    · dsimp only [Data.sizeBound,Data.pointBound]
      norm_num
    · congr 1
  have hL : μ.mean L ≤ (largePairs H s).card*d.pointBound h g q τ 2 :=
    d.mean_present_small_sets (largePairs H s) 2 (by omega)
      (fun e he => mem_allPairs.mp (Finset.mem_filter.mp he).1)
      h g hinc hdeg q τ hq hq1 hτ hτ1
  have hF : μ.mean F ≤ (fInstances (P.reducedSystem c)).card*d.pointBound h g q τ 5 := by
    have hh := d.mean_F_instances (P.reducedSystem_subset c) h g hinc hdeg q τ hq hq1 hτ hτ1
    convert hh using 1
    · congr 1
    · simp only [Data.pointBound,Nat.cast_ofNat,Nat.reduceAdd]
      norm_num
  have hA : μ.mean A ≤ (triangleInstances H).card*q^4 :=
    d.mean_triangle_instances q τ hq hq1 hτ hτ1
  have hE : μ.mean E ≤ (H.card : ℝ)*d.pointBound h g q τ 3 :=
    d.mean_present_small_sets H 3 (by omega) hH h g hinc hdeg q τ hq hq1 hτ hτ1
  have hscore : μ.mean score = μ.mean (fun ξ => ((S ξ).card : ℝ)) - μ.mean L -
      μ.mean F - μ.mean A - 3*μ.mean E/D := by
    dsimp only [score]
    rw [μ.mean_sub,μ.mean_sub,μ.mean_sub,μ.mean_sub,μ.mean_div,μ.mean_mul_const]
  obtain ⟨ξ,_hξ,hξ⟩ := μ.exists_support_ge_mean score
  obtain ⟨T,_hTS,hFT,h4T,hind,hdegree,hcard⟩ := P.clean_extraction hH c (S ξ)
    (fun x hx y hy hxy B hB => P.extraction_finalSet_exclusion c R colour b hb R ξ hx hy hxy hB) D hD
  refine ⟨T,hFT,h4T,hind,hdegree,?_⟩
  have hE' : 3*μ.mean E/D ≤ 3*((H.card : ℝ)*d.pointBound h g q τ 3)/D :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by norm_num)) hD.le
  change ((S ξ).card : ℝ) ≤ T.card+L ξ+F ξ+A ξ+3*E ξ/D at hcard
  change μ.mean score ≤ ((S ξ).card : ℝ)-L ξ-F ξ-A ξ-3*E ξ/D at hξ
  change d.sizeBound h r g q τ - _ - _ - _ - _ ≤ _
  linarith

end DenseDecomposition
end TP3
