module

public import TP3.DependentSampling

@[expose] public section

namespace TP3.DependentSample.Data

attribute [local instance] Classical.propDecidable

open scoped BigOperators

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

variable (d : Data V U)

noncomputable def slice (W : Finset V) (i : ℕ) : Finset V :=
  W.filter (fun x => (d.classOf x).val = i)

noncomputable def processed (W : Finset V) (i : ℕ) : Finset V :=
  W.filter (fun x => (d.classOf x).val < i)

theorem slice_card_sum (W : Finset V) (n : ℕ) :
    (∑ i ∈ Finset.range n, (d.slice W i).card) = (d.processed W n).card := by
  simpa [slice,processed] using
    Finset.sum_card_fiberwise_eq_card_filter W (Finset.range n) (fun x => (d.classOf x).val)

theorem processed_all (W : Finset V) : d.processed W d.classes = W := by
  ext x
  simp [processed,(d.classOf x).isLt]

/-- All tested vertices have survived, with disjoint required lists
within each processed class. The earlier history fixes those lists. -/
noncomputable def Good (W : Finset V) :
    (n : ℕ) → History (ClassNoise V U d.maxListSize) n → Prop
  | 0, _ => True
  | n+1, h =>
    Good W n h.1 ∧
      (d.slice W n : Set V).PairwiseDisjoint (d.required (d.run n h.1).chosen) ∧
      d.slice W n ⊆ d.retained (d.run n h.1).chosen
        (d.tentative n (d.run n h.1).chosen h.2)

theorem good_step_bound (W : Finset V)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (i : ℕ) (h : History (ClassNoise V U d.maxListSize) i) :
    (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1).event
      (fun ω => d.Good W (i+1) (h,ω)) ≤
      if d.Good W i h then (q*τ^d.maxListSize)^(d.slice W i).card else 0 := by
  classical
  let μ := finiteClassLaw (V := V) (U := U) d.maxListSize q τ hq hq1 hτ hτ1
  let C := (d.run i h).chosen
  have hφ : 0 ≤ (q*τ^d.maxListSize)^(d.slice W i).card := by positivity
  by_cases hpast : d.Good W i h
  · rw [ite_eq_left hpast]
    by_cases hok : (d.slice W i : Set V).PairwiseDisjoint (d.required C) ∧
        ∀ x ∈ d.slice W i, d.Eligible C x
    · calc
        _ ≤ μ.event (fun ω => ∀ x ∈ d.slice W i,
            finiteClassPass d.maxListSize (d.required C) x ω) := by
          apply FiniteLaw.event_mono
          intro ω hg x hx
          have ht := d.retained_subset C _ (hg.2.2 hx)
          exact (Finset.mem_filter.mp ht).2.2
        _ = _ := finiteClassPass_disjoint _ _ _ _ _ hq hq1 hτ hτ1
          (fun x hx => d.required_card_le (hok.2 x hx)) hok.1
    · have hnone : ∀ ω, ¬ d.Good W (i+1) (h,ω) := by
        intro ω hg
        apply hok
        refine ⟨hg.2.1,?_⟩
        intro x hx
        exact (Finset.mem_filter.mp (d.retained_subset C _ (hg.2.2 hx))).2.1
      have heq : (fun ω => d.Good W (i+1) (h,ω)) = fun _ => False := by
        funext ω
        exact propext ⟨fun hh => hnone ω hh,False.elim⟩
      rw [heq, FiniteLaw.event_false]
      exact hφ
  · rw [ite_eq_right hpast]
    have heq : (fun ω => d.Good W (i+1) (h,ω)) = fun _ => False := by
      funext ω
      exact propext ⟨fun hh => hpast hh.1,False.elim⟩
    rw [heq, FiniteLaw.event_false]

theorem good_probability_until (W : Finset V) (n : ℕ)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) n).event
      (d.Good W n) ≤ (q*τ^d.maxListSize)^(d.processed W n).card := by
  have hh := history_event_bound
    (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) (d.Good W)
    (fun i => (q*τ^d.maxListSize)^(d.slice W i).card)
    (fun _ => by positivity) (d.good_step_bound W q τ hq hq1 hτ hτ1) n
  rw [Finset.prod_pow_eq_pow_sum, d.slice_card_sum] at hh
  exact hh

/-- Across the entire adaptive experiment the no-shared-mark event has
probability at most φ^|W|. No independence of the chosen classes is assumed. -/
theorem good_probability (W : Finset V)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) d.classes).event
      (d.Good W d.classes) ≤ (q*τ^d.maxListSize)^W.card := by
  simpa only [d.processed_all] using
    d.good_probability_until W d.classes q τ hq hq1 hτ hτ1

end TP3.DependentSample.Data
