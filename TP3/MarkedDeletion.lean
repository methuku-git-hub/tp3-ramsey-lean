module

public import TP3.ChosenMarks

@[expose] public section

namespace TP3.DependentSample.Data

attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
variable (d : Data V U)

noncomputable def setIncidences (x : V) : Finset U :=
  Finset.univ.filter (fun M => x ∈ d.sets M)

noncomputable def markedVertices (n : ℕ)
    (ξ : History (ClassNoise V U d.maxListSize) n) : Finset V :=
  (d.run n ξ).chosen.filter (fun x => ∃ M ∈ (d.run n ξ).marked, x ∈ d.sets M)

noncomputable def unmarked (n : ℕ)
    (ξ : History (ClassNoise V U d.maxListSize) n) : Finset V :=
  (d.run n ξ).chosen \ d.markedVertices n ξ

theorem unmarked_subset (n : ℕ) (ξ : History (ClassNoise V U d.maxListSize) n) :
    d.unmarked n ξ ⊆ (d.run n ξ).chosen := Finset.sdiff_subset

theorem unmarked_avoids (n : ℕ) (ξ : History (ClassNoise V U d.maxListSize) n)
    {x : V} (hx : x ∈ d.unmarked n ξ) {M : U} (hM : M ∈ (d.run n ξ).marked) :
    x ∉ d.sets M := by
  intro hxM
  obtain ⟨hxC,hnot⟩ := Finset.mem_sdiff.mp hx
  exact hnot (Finset.mem_filter.mpr ⟨hxC,M,hM,hxM⟩)

theorem marked_vertex_probability (x : V) (n : ℕ) (h r : ℕ)
    (hinc : ∀ M, (d.listing x M).card ≤ h)
    (hr : (d.setIncidences x).card ≤ r)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) n).event
      (fun ξ => x ∈ d.markedVertices n ξ) ≤
        r*(n*τ*(q*τ^d.maxListSize) + h*(q*τ^d.maxListSize)^2) := by
  let μ := historyLaw (finiteClassLaw (V := V) (U := U) d.maxListSize q τ hq hq1 hτ hτ1) n
  calc
    _ ≤ μ.event (fun ξ => ∃ M ∈ d.setIncidences x,
        x ∈ (d.run n ξ).chosen ∧ M ∈ (d.run n ξ).marked) := by
      apply μ.event_mono
      intro ξ hx
      obtain ⟨hxC,M,hM,hxM⟩ := Finset.mem_filter.mp hx
      exact ⟨M,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxM⟩,hxC,hM⟩
    _ ≤ ∑ M ∈ d.setIncidences x,
        μ.event (fun ξ => x ∈ (d.run n ξ).chosen ∧ M ∈ (d.run n ξ).marked) :=
      μ.event_exists_finset_le_sum _ _
    _ ≤ ∑ _M ∈ d.setIncidences x,
        (n*τ*(q*τ^d.maxListSize) + h*(q*τ^d.maxListSize)^2) :=
      Finset.sum_le_sum (fun M _ => d.chosen_joint_mark x M n h (hinc M) q τ hq hq1 hτ hτ1)
    _ = (d.setIncidences x).card *
        (n*τ*(q*τ^d.maxListSize) + h*(q*τ^d.maxListSize)^2) := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hr) (by positivity)

theorem mean_marked_vertices (n : ℕ) (h r : ℕ)
    (hinc : ∀ x M, (d.listing x M).card ≤ h)
    (hr : ∀ x, (d.setIncidences x).card ≤ r)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) n).mean
      (fun ξ => ((d.markedVertices n ξ).card : ℝ)) ≤
        (Fintype.card V : ℝ)*r*(n*τ*(q*τ^d.maxListSize) + h*(q*τ^d.maxListSize)^2) := by
  rw [FiniteLaw.mean_card]
  calc
    _ ≤ ∑ _x : V, (r : ℝ)*(n*τ*(q*τ^d.maxListSize) + h*(q*τ^d.maxListSize)^2) :=
      Finset.sum_le_sum (fun x _ => d.marked_vertex_probability x n h r (hinc x) (hr x)
        q τ hq hq1 hτ hτ1)
    _ = _ := by simp; ring

theorem unmarked_size (n : ℕ) (ξ : History (ClassNoise V U d.maxListSize) n) :
    (d.run n ξ).chosen.card = (d.unmarked n ξ).card + (d.markedVertices n ξ).card := by
  exact (Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)).symm

end TP3.DependentSample.Data
