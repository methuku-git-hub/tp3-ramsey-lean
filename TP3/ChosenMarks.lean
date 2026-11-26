module

public import TP3.MarkHistory

@[expose] public section

namespace TP3.DependentSample.Data

attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
variable (d : Data V U)

/-- A chosen vertex and a set marked in any processed class. Only the
vertex's own class contributes the extra term hφ²; other classes cost τφ. -/
theorem chosen_joint_mark (x : V) (M : U) (n : ℕ) (h : ℕ)
    (hinc : (d.listing x M).card ≤ h)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) n).event
      (fun ξ => x ∈ (d.run n ξ).chosen ∧ M ∈ (d.run n ξ).marked) ≤
        n*τ*(q*τ^d.maxListSize) + h*(q*τ^d.maxListSize)^2 := by
  induction n with
  | zero => simp [run,processState,initial]; positivity
  | succ n ih =>
    let μ := historyLaw (finiteClassLaw (V := V) (U := U) d.maxListSize q τ hq hq1 hτ hτ1) n
    let ν := finiteClassLaw (V := V) (U := U) d.maxListSize q τ hq hq1 hτ hτ1
    change (μ.staged (fun _ => ν)).event _ ≤ _
    by_cases hxclass : (d.classOf x).val=n
    · have hx : x ∈ d.classVertices n := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxclass⟩
      have hselected (ξ : History (ClassNoise V U d.maxListSize) (n+1))
          (hchosen : x ∈ (d.run (n+1) ξ).chosen) :
          x ∈ d.tentative n (d.run n ξ.1).chosen ξ.2 := by
        change x ∈ (d.run n ξ.1).chosen ∪ _ at hchosen
        rcases Finset.mem_union.mp hchosen with hp | hn
        · have hh := d.run_chosen_class_lt n ξ.1 x hp
          omega
        · exact d.retained_subset _ _ hn
      have hpast : (μ.staged (fun _ => ν)).event
          (fun ξ => M ∈ (d.run n ξ.1).marked ∧ x ∈ d.tentative n (d.run n ξ.1).chosen ξ.2) ≤
          (q*τ^d.maxListSize)*(n*τ) := by
        apply le_trans (d.tentative_past_event n x hx
          (fun ξ => M ∈ (d.run n ξ).marked) q τ hq hq1 hτ hτ1)
        exact mul_le_mul_of_nonneg_left (d.marked_probability M n q τ hq hq1 hτ hτ1)
          (by positivity : 0 ≤ q*τ^d.maxListSize)
      calc
        _ ≤ (μ.staged (fun _ => ν)).event (fun ξ =>
            (M ∈ (d.run n ξ.1).marked ∧ x ∈ d.tentative n (d.run n ξ.1).chosen ξ.2) ∨
            (x ∈ d.tentative n (d.run n ξ.1).chosen ξ.2 ∧ ξ.2.1 M=true)) := by
          apply FiniteLaw.event_mono
          intro ξ hh
          rcases (d.run_marked_succ n ξ.1 ξ.2 M).mp hh.2 with hp | hn
          · exact Or.inl ⟨hp,hselected ξ hh.1⟩
          · exact Or.inr ⟨hselected ξ hh.1,hn⟩
        _ ≤ (μ.staged (fun _ => ν)).event
            (fun ξ => M ∈ (d.run n ξ.1).marked ∧ x ∈ d.tentative n (d.run n ξ.1).chosen ξ.2) +
            (μ.staged (fun _ => ν)).event
            (fun ξ => x ∈ d.tentative n (d.run n ξ.1).chosen ξ.2 ∧ ξ.2.1 M=true) :=
          FiniteLaw.event_or_le _ _ _
        _ ≤ (q*τ^d.maxListSize)*(n*τ) +
            (τ*(q*τ^d.maxListSize) + h*(q*τ^d.maxListSize)^2) :=
          add_le_add hpast (d.tentative_joint_mark n x M h hinc q τ hq hq1 hτ hτ1)
        _ = _ := by push_cast; ring
    · have hselected (ξ : History (ClassNoise V U d.maxListSize) (n+1))
          (hchosen : x ∈ (d.run (n+1) ξ).chosen) : x ∈ (d.run n ξ.1).chosen := by
        change x ∈ (d.run n ξ.1).chosen ∪ _ at hchosen
        rcases Finset.mem_union.mp hchosen with hp | hn
        · exact hp
        · have ht := d.retained_subset _ _ hn
          exact False.elim (hxclass (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2)
      have hfresh : (μ.staged (fun _ => ν)).event
          (fun ξ => x ∈ (d.run n ξ.1).chosen ∧ ξ.2.1 M=true) ≤ (q*τ^d.maxListSize)*τ := by
        rw [FiniteLaw.independent_events _ _
          (fun ξ : History (ClassNoise V U d.maxListSize) n => x ∈ (d.run n ξ).chosen)
          (fun ω : ClassNoise V U d.maxListSize => ω.1 M=true),finiteClass_mark_probability]
        exact mul_le_mul_of_nonneg_right (d.chosen_vertex_probability x n q τ hq hq1 hτ hτ1) hτ
      calc
        _ ≤ (μ.staged (fun _ => ν)).event (fun ξ =>
            (x ∈ (d.run n ξ.1).chosen ∧ M ∈ (d.run n ξ.1).marked) ∨
            (x ∈ (d.run n ξ.1).chosen ∧ ξ.2.1 M=true)) := by
          apply FiniteLaw.event_mono
          intro ξ hh
          rcases (d.run_marked_succ n ξ.1 ξ.2 M).mp hh.2 with hp | hn
          · exact Or.inl ⟨hselected ξ hh.1,hp⟩
          · exact Or.inr ⟨hselected ξ hh.1,hn⟩
        _ ≤ (μ.staged (fun _ => ν)).event
            (fun ξ => x ∈ (d.run n ξ.1).chosen ∧ M ∈ (d.run n ξ.1).marked) +
            (μ.staged (fun _ => ν)).event
            (fun ξ => x ∈ (d.run n ξ.1).chosen ∧ ξ.2.1 M=true) := FiniteLaw.event_or_le _ _ _
        _ = μ.event (fun ξ => x ∈ (d.run n ξ).chosen ∧ M ∈ (d.run n ξ).marked) +
            (μ.staged (fun _ => ν)).event
            (fun ξ => x ∈ (d.run n ξ.1).chosen ∧ ξ.2.1 M=true) := by
          rw [FiniteLaw.staged_event_first _ _
            (fun ξ : History (ClassNoise V U d.maxListSize) n =>
              x ∈ (d.run n ξ).chosen ∧ M ∈ (d.run n ξ).marked)]
        _ ≤ (n*τ*(q*τ^d.maxListSize) + h*(q*τ^d.maxListSize)^2) +
            (q*τ^d.maxListSize)*τ := add_le_add ih hfresh
        _ = _ := by push_cast; ring

end TP3.DependentSample.Data
