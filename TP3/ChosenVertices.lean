module

public import TP3.CoarseSampling

@[expose] public section

namespace TP3.DependentSample.Data

attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
variable (d : Data V U)

theorem processed_chosen_step_iff (W : Finset V) (i : ℕ)
    (h : History (ClassNoise V U d.maxListSize) i)
    (ω : ClassNoise V U d.maxListSize) :
    d.processed W (i+1) ⊆ (d.run (i+1) (h,ω)).chosen ↔
      d.processed W i ⊆ (d.run i h).chosen ∧
        d.slice W i ⊆ d.retained (d.run i h).chosen
          (d.tentative i (d.run i h).chosen ω) := by
  apply d.processed_subset_union_iff _ _ _ _ (d.run_chosen_class_lt i h)
  intro x hx
  have ht := d.retained_subset _ _ hx
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2

theorem good_of_disjoint_lists (W : Finset V)
    (hdis : ∀ i C, (d.slice W i : Set V).PairwiseDisjoint (d.required C))
    (n : ℕ) (h : History (ClassNoise V U d.maxListSize) n)
    (hW : d.processed W n ⊆ (d.run n h).chosen) : d.Good W n h := by
  induction n with
  | zero => trivial
  | succ n ih =>
    have hh := (d.processed_chosen_step_iff W n h.1 h.2).mp hW
    exact ⟨ih h.1 hh.1,hdis n _,hh.2⟩

/-- Every chosen vertex has marginal probability at most φ at every
stage. This includes the dependence introduced by conflict deletions. -/
theorem chosen_vertex_probability (x : V) (n : ℕ)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) n).event
      (fun h => x ∈ (d.run n h).chosen) ≤ q*τ^d.maxListSize := by
  classical
  let μ := historyLaw (finiteClassLaw (V := V) (U := U) d.maxListSize q τ hq hq1 hτ hτ1) n
  by_cases hx : (d.classOf x).val < n
  · have hsingle : d.processed {x} n = {x} := by simp [processed,hx]
    have hgood : ∀ h, x ∈ (d.run n h).chosen → d.Good {x} n h := by
      intro h hchosen
      refine d.good_of_disjoint_lists {x} ?_ n h ?_
      · intro i C y hy z hz hyz
        have hyx : y=x := Finset.mem_singleton.mp (Finset.mem_filter.mp hy).1
        have hzx : z=x := Finset.mem_singleton.mp (Finset.mem_filter.mp hz).1
        exact False.elim (hyz (hyx.trans hzx.symm))
      · rw [hsingle]
        exact Finset.singleton_subset_iff.mpr hchosen
    calc
      _ ≤ μ.event (d.Good {x} n) := FiniteLaw.event_mono _ hgood
      _ ≤ (q*τ^d.maxListSize)^(d.processed {x} n).card :=
        d.good_probability_until {x} n q τ hq hq1 hτ hτ1
      _ = _ := by simp [hsingle]
  · have heq : (fun h => x ∈ (d.run n h).chosen) = fun _ => False := by
      funext h
      exact propext ⟨fun hm => hx (d.run_chosen_class_lt n h x hm),False.elim⟩
    rw [heq,FiniteLaw.event_false]
    positivity

end TP3.DependentSample.Data
