module

public import TP3.ExtractionData
public import TP3.TriangleDeletion

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def largePairs (H : Finset (Finset V)) (s : ℝ) : Finset (Finset V) :=
  (allPairs V).filter (fun e => s < ((completions H e).card : ℝ))

theorem largePairs_card_bound {H : Finset (Finset V)} (hH : IsTripleSystem H) (s : ℝ) :
    s*(largePairs H s).card ≤ 3*(H.card : ℝ) := by
  calc
    _ = ∑ _e ∈ largePairs H s, s := by simp [mul_comm]
    _ ≤ ∑ e ∈ largePairs H s, ((completions H e).card : ℝ) :=
      Finset.sum_le_sum (fun e he => (Finset.mem_filter.mp he).2.le)
    _ ≤ ∑ e ∈ allPairs V, ((completions H e).card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
    _ = _ := by exact_mod_cast sum_completions hH

theorem delete_largePairs (H : Finset (Finset V)) (s : ℝ) (S : Finset V) :
    ∃ T ⊆ S, (∀ e ∈ allPairs V, e ⊆ T → ((completions H e).card : ℝ) ≤ s) ∧
      S.card ≤ T.card + ((largePairs H s).filter (fun e => e ⊆ S)).card := by
  have hn : ∀ e ∈ largePairs H s, e.Nonempty := by
    intro e he
    have hc := mem_allPairs.mp (Finset.mem_filter.mp he).1
    exact Finset.card_pos.mp (by omega)
  obtain ⟨T,hTS,hind,hsize⟩ := delete_present_forbidden hn S
  refine ⟨T,hTS,?_,hsize⟩
  intro e he heT
  by_contra! hh
  exact hind e (Finset.mem_filter.mpr ⟨he,hh⟩) heT

/-- Removing all vertices of degree above D costs at most the sum of
the degrees divided by D. The degree bound is then inherited by every
remaining vertex. -/
theorem delete_high_degree {H : Finset (Finset V)} (hH : IsTripleSystem H)
    (S : Finset V) (D : ℝ) (hD : 0 < D) :
    ∃ T ⊆ S, (∀ v, (degree (induced H T) v : ℝ) ≤ D) ∧
      (S.card : ℝ) ≤ T.card + 3*(induced H S).card/D := by
  let K := induced H S
  let B := S.filter (fun v => D < (degree K v : ℝ))
  have hcount : D*(B.card : ℝ) ≤ 3*(K.card : ℝ) := by
    calc
      _ = ∑ _v ∈ B, D := by simp [mul_comm]
      _ ≤ ∑ v ∈ B, (degree K v : ℝ) :=
        Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2.le)
      _ ≤ ∑ v : V, (degree K v : ℝ) :=
        Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.cast_nonneg _)
      _ = _ := by
        exact_mod_cast sum_degree_triples (fun e he => hH e (Finset.mem_filter.mp he).1)
  refine ⟨S\B,Finset.sdiff_subset,?_,?_⟩
  · intro v
    by_cases hv : v ∈ S\B
    · have hlow : (degree K v : ℝ) ≤ D := by
        obtain ⟨hvS,hvB⟩ := Finset.mem_sdiff.mp hv
        simpa only [B,Finset.mem_filter,hvS,true_and,not_lt] using hvB
      apply le_trans _ hlow
      exact_mod_cast degree_mono (induced_mono_vertices H Finset.sdiff_subset) v
    · have hz : degree (induced H (S\B)) v=0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.filter_eq_empty_iff.mpr
        intro e he hve
        exact hv ((Finset.mem_filter.mp he).2 hve)
      simpa only [hz,Nat.cast_zero] using hD.le
  · have hB : B ⊆ S := Finset.filter_subset _ _
    have hc : ((S\B).card : ℝ)+B.card=S.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hB
    have hb : (B.card : ℝ) ≤ 3*(K.card : ℝ)/D := by
      apply (le_div_iff₀ hD).mpr
      simpa only [mul_comm] using hcount
    change (S.card : ℝ) ≤ (S\B).card+3*(K.card : ℝ)/D
    linarith

namespace DependentSample.Data

variable {U : Type*} [Fintype U] [DecidableEq U] (d : Data V U)

/-- One inclusion estimate for any family of pairs or triples. -/
theorem mean_present_small_sets (E : Finset (Finset V)) (m : ℕ) (hm : m ≤ 3)
    (hE : ∀ e ∈ E, e.card=m) (h : ℕ) (g : ℝ)
    (hinc : ∀ y M, (d.listing y M).card ≤ h)
    (hdeg : ∀ x, ((d.neighbors x).card : ℝ) ≤ g)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) d.classes).mean
      (fun ξ => ((E.filter (fun e => e ⊆ d.finalSet d.classes ξ)).card : ℝ)) ≤
    E.card * ((q*τ^d.maxListSize)^m + (m : ℝ)^2*
      ((m : ℝ)*d.listBound*h*q^(m+1) + g*d.listBound*h*q^(m+2))) := by
  let μ := historyLaw (finiteClassLaw (V := V) (U := U) d.maxListSize q τ hq hq1 hτ hτ1) d.classes
  have hh := μ.mean_filter_card E
    (fun (e : Finset V) (ξ : History (ClassNoise V U d.maxListSize) d.classes) =>
      e ⊆ d.finalSet d.classes ξ)
  calc
    _ = ∑ e ∈ E, μ.event (fun ξ => e ⊆ d.finalSet d.classes ξ) := by
      convert hh using 1
      congr 1
      funext ξ
      congr 1
      congr 1
      ext e
      simp
    _ ≤ ∑ _e ∈ E, ((q*τ^d.maxListSize)^m + (m : ℝ)^2*
      ((m : ℝ)*d.listBound*h*q^(m+1) + g*d.listBound*h*q^(m+2))) := by
      apply Finset.sum_le_sum
      intro e he
      have hp := d.finalSet_probability e
        (fourVertexProperty_small d.triples e (by rw [hE e he]; exact hm))
        h g hinc hdeg q τ hq hq1 hτ hτ1
      rwa [hE e he] at hp
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]

end DependentSample.Data
end TP3
