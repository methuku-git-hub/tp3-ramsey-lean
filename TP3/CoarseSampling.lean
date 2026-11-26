module

public import TP3.SamplingBounds

@[expose] public section

namespace TP3.DependentSample.Data

attribute [local instance] Classical.propDecidable

open scoped BigOperators

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

variable (d : Data V U)

/-- A new class cannot supply any previously missing vertex from an
earlier class. This separates the old and new requirements exactly. -/
theorem processed_subset_union_iff (W P A : Finset V) (i : ℕ)
    (hP : ∀ x ∈ P, (d.classOf x).val < i)
    (hA : ∀ x ∈ A, (d.classOf x).val = i) :
    d.processed W (i+1) ⊆ P ∪ A ↔ d.processed W i ⊆ P ∧ d.slice W i ⊆ A := by
  constructor
  · intro h
    constructor
    · intro x hx
      obtain ⟨hxW,hxi⟩ := Finset.mem_filter.mp hx
      have hxnext : x ∈ d.processed W (i+1) :=
        Finset.mem_filter.mpr ⟨hxW,Nat.lt_succ_of_lt hxi⟩
      rcases Finset.mem_union.mp (h hxnext) with hp | ha
      · exact hp
      · have := hA x ha
        omega
    · intro x hx
      obtain ⟨hxW,hxi⟩ := Finset.mem_filter.mp hx
      have hxnext : x ∈ d.processed W (i+1) := Finset.mem_filter.mpr ⟨hxW,by omega⟩
      rcases Finset.mem_union.mp (h hxnext) with hp | ha
      · have := hP x hp
        omega
      · exact ha
  · rintro ⟨hp,ha⟩ x hx
    obtain ⟨hxW,hxi⟩ := Finset.mem_filter.mp hx
    by_cases hlt : (d.classOf x).val < i
    · exact Finset.mem_union_left _ (hp (Finset.mem_filter.mpr ⟨hxW,hlt⟩))
    · exact Finset.mem_union_right _ (ha (Finset.mem_filter.mpr ⟨hxW,by omega⟩))

theorem tentative_step_bound (W : Finset V)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (i : ℕ) (h : History (ClassNoise V U d.maxListSize) i) :
    (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1).event
      (fun ω => d.processed W (i+1) ⊆ (d.run (i+1) (h,ω)).tentative) ≤
      if d.processed W i ⊆ (d.run i h).tentative then q^(d.slice W i).card else 0 := by
  classical
  let μ := finiteClassLaw (V := V) (U := U) d.maxListSize q τ hq hq1 hτ hτ1
  have hiff (ω : ClassNoise V U d.maxListSize) :
      d.processed W (i+1) ⊆ (d.run (i+1) (h,ω)).tentative ↔
      d.processed W i ⊆ (d.run i h).tentative ∧
        d.slice W i ⊆ d.tentative i (d.run i h).chosen ω := by
    apply d.processed_subset_union_iff _ _ _ _ (d.run_tentative_class_lt i h)
    intro x hx
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
  by_cases hp : d.processed W i ⊆ (d.run i h).tentative
  · rw [ite_eq_left hp]
    calc
      _ ≤ μ.event (fun ω => ∀ x ∈ d.slice W i, ω.2.1 x = true) := by
        apply FiniteLaw.event_mono
        intro ω hnew x hx
        have ht := (hiff ω).mp hnew
        exact (Finset.mem_filter.mp (ht.2 hx)).2.2.2.1
      _ = _ := finiteClass_envelope_probability _ _ _ _ hq hq1 hτ hτ1
  · rw [ite_eq_right hp]
    have heq :
        (fun ω => d.processed W (i+1) ⊆ (d.run (i+1) (h,ω)).tentative) =
        fun _ => False := by
      funext ω
      exact propext ⟨fun hn => hp ((hiff ω).mp hn).1,False.elim⟩
    rw [heq, FiniteLaw.event_false]

/-- The coarse inclusion bound is valid for the complete adaptive
algorithm, not just for one class or fixed deterministic lists. -/
theorem tentative_probability (W : Finset V)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) d.classes).event
      (fun h => W ⊆ (d.run d.classes h).tentative) ≤ q^W.card := by
  have hh := history_event_bound
    (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1)
    (fun n h => d.processed W n ⊆ (d.run n h).tentative)
    (fun i => q^(d.slice W i).card) (fun _ => pow_nonneg hq _)
    (fun i h => by
      have hh := d.tentative_step_bound W q τ hq hq1 hτ hτ1 i h
      by_cases hp : d.processed W i ⊆ (d.run i h).tentative
      · simpa only [ite_eq_left hp] using hh
      · simpa only [ite_eq_right hp] using hh) d.classes
  rw [Finset.prod_pow_eq_pow_sum, d.slice_card_sum, d.processed_all] at hh
  exact hh

theorem chosen_coarse_probability (W : Finset V)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) d.classes).event
      (fun h => W ⊆ (d.run d.classes h).chosen) ≤ q^W.card := by
  apply le_trans (FiniteLaw.event_mono _ ?_) (d.tentative_probability W q τ hq hq1 hτ hτ1)
  intro h hW
  exact hW.trans (d.run_chosen_subset_tentative d.classes h)

end TP3.DependentSample.Data
