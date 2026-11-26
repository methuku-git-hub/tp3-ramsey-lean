module

public import TP3.SamplingSize

@[expose] public section

namespace TP3.DependentSample.Data

attribute [local instance] Classical.propDecidable

open scoped BigOperators

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
variable (d : Data V U)

/-- All conflict pairs encountered up to a given stage. A pair occurs in
only one class, so their union counts the full deletion allowance. -/
noncomputable def allConflicts :
    (n : ℕ) → History (ClassNoise V U d.maxListSize) n → Finset (Finset V)
  | 0, _ => ∅
  | n+1, ξ => allConflicts n ξ.1 ∪
      d.conflicts (d.run n ξ.1).chosen (d.tentative n (d.run n ξ.1).chosen ξ.2)

theorem conflicts_class (i : ℕ) (C : Finset V) (ω : ClassNoise V U d.maxListSize)
    {e : Finset V} (he : e ∈ d.conflicts C (d.tentative i C ω)) :
    ∀ x ∈ e, (d.classOf x).val = i := by
  intro x hx
  have ht := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).1 hx
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).2

theorem allConflicts_class_lt (n : ℕ)
    (ξ : History (ClassNoise V U d.maxListSize) n)
    {e : Finset V} (he : e ∈ d.allConflicts n ξ) :
    e.Nonempty ∧ ∀ x ∈ e, (d.classOf x).val < n := by
  induction n with
  | zero => simpa [allConflicts] using he
  | succ n ih =>
    rcases Finset.mem_union.mp he with hp | hn
    · have hh := ih ξ.1 hp
      exact ⟨hh.1,fun x hx => Nat.lt_succ_of_lt (hh.2 x hx)⟩
    · exact ⟨d.conflicts_nonempty _ _ e hn,
        fun x hx => by rw [d.conflicts_class n _ _ hn x hx]; omega⟩

theorem allConflicts_disjoint_new (n : ℕ)
    (ξ : History (ClassNoise V U d.maxListSize) n)
    (ω : ClassNoise V U d.maxListSize) :
    Disjoint (d.allConflicts n ξ)
      (d.conflicts (d.run n ξ).chosen (d.tentative n (d.run n ξ).chosen ω)) := by
  apply Finset.disjoint_left.mpr
  intro e hp hn
  obtain ⟨hne,hlt⟩ := d.allConflicts_class_lt n ξ hp
  obtain ⟨x,hx⟩ := hne
  have h₁ := hlt x hx
  have h₂ := d.conflicts_class n _ _ hn x hx
  omega

theorem chosen_disjoint_new (n : ℕ)
    (ξ : History (ClassNoise V U d.maxListSize) n)
    (ω : ClassNoise V U d.maxListSize) :
    Disjoint (d.run n ξ).chosen
      (d.retained (d.run n ξ).chosen (d.tentative n (d.run n ξ).chosen ω)) := by
  exact (d.tentative_disjoint_past n ξ ω).mono
    (d.run_chosen_subset_tentative n ξ) (d.retained_subset _ _)

/-- Each deletion is charged to a conflict pair from the same class.
This is a deterministic inequality for every complete history. -/
theorem run_size_loss (n : ℕ)
    (ξ : History (ClassNoise V U d.maxListSize) n) :
    (d.run n ξ).tentative.card ≤
      (d.run n ξ).chosen.card + (d.allConflicts n ξ).card := by
  induction n with
  | zero => simp [run,processState,initial,allConflicts]
  | succ n ih =>
    change ((d.run n ξ.1).tentative ∪ d.tentative n (d.run n ξ.1).chosen ξ.2).card ≤
      ((d.run n ξ.1).chosen ∪ d.retained (d.run n ξ.1).chosen
        (d.tentative n (d.run n ξ.1).chosen ξ.2)).card +
      (d.allConflicts n ξ.1 ∪ d.conflicts (d.run n ξ.1).chosen
        (d.tentative n (d.run n ξ.1).chosen ξ.2)).card
    rw [Finset.card_union_of_disjoint (d.tentative_disjoint_past n ξ.1 ξ.2),
      Finset.card_union_of_disjoint (d.chosen_disjoint_new n ξ.1 ξ.2),
      Finset.card_union_of_disjoint (d.allConflicts_disjoint_new n ξ.1 ξ.2)]
    have hp := ih ξ.1
    have hn := d.retained_size (d.run n ξ.1).chosen (d.tentative n (d.run n ξ.1).chosen ξ.2)
    omega

theorem mean_chosen_lower_bound (hR : 0 < d.classes)
    (g : ℝ) (hdeg : ∀ x, ((d.neighbors x).card : ℝ) ≤ g)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (Fintype.card V : ℝ) *
      ((q*τ^d.maxListSize) * (1-g*(q*τ^d.maxListSize)/d.classes)) ≤
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) d.classes).mean
      (fun ξ => ((d.run d.classes ξ).chosen.card : ℝ)) +
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) d.classes).mean
      (fun ξ => ((d.allConflicts d.classes ξ).card : ℝ)) := by
  apply le_trans (d.mean_tentative_all hR g hdeg q τ hq hq1 hτ hτ1)
  rw [← FiniteLaw.mean_add]
  apply FiniteLaw.mean_mono
  intro ξ
  exact_mod_cast d.run_size_loss d.classes ξ

end TP3.DependentSample.Data
