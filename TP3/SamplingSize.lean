module

public import TP3.PointwiseSampling
public import TP3.FiniteCardinality

@[expose] public section

namespace TP3.DependentSample.Data

attribute [local instance] Classical.propDecidable

open scoped BigOperators

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
variable (d : Data V U)

/-- Eligibility depends only on the earlier choices. Summing their marginal
bounds controls its failure probability without an independence assumption. -/
theorem mean_earlier_neighbors (x : V) (n : ℕ)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) n).mean
      (fun ξ => ((d.earlierNeighbors (d.run n ξ).chosen x).card : ℝ)) ≤
        (d.neighbors x).card * (q*τ^d.maxListSize) := by
  let μ := historyLaw (finiteClassLaw (V := V) (U := U) d.maxListSize q τ hq hq1 hτ hτ1) n
  have heq (ξ : History (ClassNoise V U d.maxListSize) n) :
      d.earlierNeighbors (d.run n ξ).chosen x =
        (d.neighbors x).filter (fun y => y ∈ (d.run n ξ).chosen) := by
    ext y
    simp only [earlierNeighbors, neighbors, Finset.mem_filter, Finset.mem_univ,
      true_and, and_comm]
  simp_rw [heq]
  have hmean := μ.mean_filter_card (d.neighbors x)
    (fun (y : V) (ξ : History (ClassNoise V U d.maxListSize) n) => y ∈ (d.run n ξ).chosen)
  calc
    _ = ∑ y ∈ d.neighbors x, μ.event (fun ξ => y ∈ (d.run n ξ).chosen) := by
      convert hmean using 1
      congr 1
      funext ξ
      congr 1
      congr 1
      ext y
      simp
    _ ≤ _ := ?_
  calc
    _ ≤ ∑ _y ∈ d.neighbors x, q*τ^d.maxListSize :=
      Finset.sum_le_sum (fun y _ => d.chosen_vertex_probability y n q τ hq hq1 hτ hτ1)
    _ = _ := by simp

theorem eligible_probability (x : V) (n : ℕ) (hR : 0 < d.classes)
    (g : ℝ) (hdeg : ((d.neighbors x).card : ℝ) ≤ g)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    1 - g*(q*τ^d.maxListSize)/d.classes ≤
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) n).event
      (fun ξ => d.Eligible (d.run n ξ).chosen x) := by
  let μ := historyLaw (finiteClassLaw (V := V) (U := U) d.maxListSize q τ hq hq1 hτ hτ1) n
  have hbad : μ.event (fun ξ => ¬ d.Eligible (d.run n ξ).chosen x) ≤
      g*(q*τ^d.maxListSize)/d.classes := by
    calc
      _ ≤ μ.event (fun ξ => (d.classes : ℝ) ≤
          (d.earlierNeighbors (d.run n ξ).chosen x).card) := by
        apply μ.event_mono
        intro ξ h
        have hh : d.classes < (d.earlierNeighbors (d.run n ξ).chosen x).card :=
          Nat.lt_of_not_ge h
        exact_mod_cast hh.le
      _ ≤ μ.mean (fun ξ => ((d.earlierNeighbors (d.run n ξ).chosen x).card : ℝ)) /
          d.classes := μ.event_ge_le (fun _ => Nat.cast_nonneg _) (by exact_mod_cast hR)
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        exact (d.mean_earlier_neighbors x n q τ hq hq1 hτ hτ1).trans
          (mul_le_mul_of_nonneg_right hdeg (by positivity))
  rw [μ.event_not] at hbad
  linarith

/-- An eligible vertex is selected with probability exactly φ. The earlier
history is fixed throughout this calculation. -/
theorem tentative_vertex_conditional (i : ℕ) (C : Finset V) (x : V)
    (hx : x ∈ d.classVertices i)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1).event
      (fun ω => x ∈ d.tentative i C ω) =
        if d.Eligible C x then q*τ^d.maxListSize else 0 := by
  classical
  by_cases he : d.Eligible C x
  · simp only [ite_eq_left he]
    have hp := finiteClassPass_disjoint d.maxListSize (d.required C) {x}
      q τ hq hq1 hτ hτ1
      (fun y hy => by simpa only [Finset.mem_singleton.mp hy] using d.required_card_le he)
      (by simp)
    simpa only [tentative, Finset.mem_filter, hx, he, true_and,
      Finset.mem_singleton, forall_eq, Finset.card_singleton, pow_one] using hp
  · have hfalse : (fun ω => x ∈ d.tentative i C ω) = fun _ => False := by
      funext ω
      simp [tentative,he]
    rw [hfalse,FiniteLaw.event_false,ite_eq_right he]

theorem tentative_vertex_probability (i : ℕ) (x : V)
    (hx : x ∈ d.classVertices i)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) (i+1)).event
      (fun ξ => x ∈ d.tentative i (d.run i ξ.1).chosen ξ.2) =
      (q*τ^d.maxListSize) *
        (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) i).event
          (fun ξ => d.Eligible (d.run i ξ).chosen x) := by
  change ((historyLaw _ i).staged (fun _ => _)).event _ = _
  rw [FiniteLaw.staged_event]
  simp_rw [d.tentative_vertex_conditional i _ x hx q τ hq hq1 hτ hτ1]
  rw [← FiniteLaw.mean_indicator, ← FiniteLaw.mean_mul_const]
  congr 1
  funext ξ
  split <;> simp

theorem mean_tentative_class (i : ℕ) (hR : 0 < d.classes)
    (g : ℝ) (hdeg : ∀ x, ((d.neighbors x).card : ℝ) ≤ g)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (d.classVertices i).card * ((q*τ^d.maxListSize) *
      (1-g*(q*τ^d.maxListSize)/d.classes)) ≤
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) (i+1)).mean
      (fun ξ => ((d.tentative i (d.run i ξ.1).chosen ξ.2).card : ℝ)) := by
  let μ := historyLaw (finiteClassLaw (V := V) (U := U) d.maxListSize q τ hq hq1 hτ hτ1) (i+1)
  rw [μ.mean_card]
  calc
    _ = ∑ _x ∈ d.classVertices i, (q*τ^d.maxListSize) *
        (1-g*(q*τ^d.maxListSize)/d.classes) := by simp
    _ ≤ ∑ x ∈ d.classVertices i,
        μ.event (fun ξ => x ∈ d.tentative i (d.run i ξ.1).chosen ξ.2) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [d.tentative_vertex_probability i x hx q τ hq hq1 hτ hτ1]
      exact mul_le_mul_of_nonneg_left
        (d.eligible_probability x i hR g (hdeg x) q τ hq hq1 hτ hτ1) (by positivity)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => μ.event_nonneg _)

theorem tentative_disjoint_past (i : ℕ)
    (ξ : History (ClassNoise V U d.maxListSize) i)
    (ω : ClassNoise V U d.maxListSize) :
    Disjoint (d.run i ξ).tentative (d.tentative i (d.run i ξ).chosen ω) := by
  apply Finset.disjoint_left.mpr
  intro x hp hn
  have hp' := d.run_tentative_class_lt i ξ x hp
  have hn' := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
  omega

theorem mean_tentative_succ (i : ℕ)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) (i+1)).mean
      (fun ξ => ((d.run (i+1) ξ).tentative.card : ℝ)) =
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) i).mean
      (fun ξ => ((d.run i ξ).tentative.card : ℝ)) +
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) (i+1)).mean
      (fun ξ => ((d.tentative i (d.run i ξ.1).chosen ξ.2).card : ℝ)) := by
  have hc (ξ : History (ClassNoise V U d.maxListSize) (i+1)) :
      ((d.run (i+1) ξ).tentative.card : ℝ) =
        (d.run i ξ.1).tentative.card + (d.tentative i (d.run i ξ.1).chosen ξ.2).card := by
    change (((d.run i ξ.1).tentative ∪ d.tentative i (d.run i ξ.1).chosen ξ.2).card : ℝ) = _
    rw [Finset.card_union_of_disjoint (d.tentative_disjoint_past i ξ.1 ξ.2),Nat.cast_add]
  simp_rw [hc]
  rw [FiniteLaw.mean_add]
  congr 1
  change ((historyLaw _ i).staged (fun _ => _)).mean _ = _
  rw [FiniteLaw.staged_mean]
  simp_rw [FiniteLaw.mean_const]

/-- The expected number of tentative choices in all classes. This estimate
is for the adaptive process itself, before charging conflict deletions. -/
theorem mean_tentative_until (n : ℕ) (hR : 0 < d.classes)
    (g : ℝ) (hdeg : ∀ x, ((d.neighbors x).card : ℝ) ≤ g)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (∑ i ∈ Finset.range n, ((d.classVertices i).card : ℝ)) *
      ((q*τ^d.maxListSize) * (1-g*(q*τ^d.maxListSize)/d.classes)) ≤
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) n).mean
      (fun ξ => ((d.run n ξ).tentative.card : ℝ)) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero,Finset.sum_empty,zero_mul]
    exact FiniteLaw.mean_nonneg _ (fun _ => Nat.cast_nonneg _)
  | succ n ih =>
    rw [Finset.sum_range_succ,add_mul,d.mean_tentative_succ]
    exact add_le_add ih (d.mean_tentative_class n hR g hdeg q τ hq hq1 hτ hτ1)

theorem mean_tentative_all (hR : 0 < d.classes)
    (g : ℝ) (hdeg : ∀ x, ((d.neighbors x).card : ℝ) ≤ g)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (Fintype.card V : ℝ) *
      ((q*τ^d.maxListSize) * (1-g*(q*τ^d.maxListSize)/d.classes)) ≤
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) d.classes).mean
      (fun ξ => ((d.run d.classes ξ).tentative.card : ℝ)) := by
  have hc : (∑ i ∈ Finset.range d.classes, ((d.classVertices i).card : ℝ)) =
      Fintype.card V := by
    have hh := d.slice_card_sum Finset.univ d.classes
    rw [d.processed_all,Finset.card_univ] at hh
    exact_mod_cast hh
  simpa only [hc] using d.mean_tentative_until d.classes hR g hdeg q τ hq hq1 hτ hτ1

end TP3.DependentSample.Data
