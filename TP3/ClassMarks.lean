module

public import TP3.ExpectedConflictLoss

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable

variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem finiteClass_mark_probability (m : ℕ) (M : U)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (finiteClassLaw (V := V) m q τ hq hq1 hτ hτ1).event
      (fun ω => ω.1 M = true) = τ := by
  unfold finiteClassLaw
  rw [FiniteLaw.staged_event_first _ _ (fun ω : U → Bool => ω M = true)]
  have hh := FiniteLaw.bernoulli_required (fun _ : U => τ)
    (fun _ => hτ) (fun _ => hτ1) {M}
  simpa using hh

/-- An extra mark costs a factor τ unless it is already required by the
vertex. The compensation for all the required marks remains exact. -/
theorem finiteClassPass_joint_mark (m : ℕ) (L : V → Finset U) (x : V) (M : U)
    (hL : (L x).card ≤ m)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (finiteClassLaw m q τ hq hq1 hτ hτ1).event
      (fun ω => finiteClassPass m L x ω ∧ ω.1 M = true) =
        if M ∈ L x then q*τ^m else τ*(q*τ^m) := by
  classical
  have heq :
      (fun ω : ClassNoise V U m => finiteClassPass m L x ω ∧ ω.1 M = true) =
      fun ω => (∀ u ∈ insert M (L x), ω.1 u = true) ∧
        (ω.2.1 x = true ∧ ∀ j ∈ auxiliaryIndices m (L x).card, ω.2.2 x j = true) := by
    funext ω
    apply propext
    simp only [finiteClassPass,Finset.mem_insert,forall_eq_or_imp]
    tauto
  rw [heq]
  unfold finiteClassLaw
  rw [FiniteLaw.independent_events _ _
    (fun ω : U → Bool => ∀ u ∈ insert M (L x), ω u = true)
    (fun ω : (V → Bool) × (V → Fin (m+1) → Bool) =>
      ω.1 x = true ∧ ∀ j ∈ auxiliaryIndices m (L x).card, ω.2 x j = true)]
  rw [FiniteLaw.independent_events _ _
    (fun ω : V → Bool => ω x = true)
    (fun ω : V → Fin (m+1) → Bool =>
      ∀ j ∈ auxiliaryIndices m (L x).card, ω x j = true)]
  have hqevent := FiniteLaw.bernoulli_required (fun _ : V => q)
    (fun _ => hq) (fun _ => hq1) {x}
  simp only [Finset.mem_singleton,forall_eq,Finset.prod_singleton] at hqevent
  have ha := auxiliary_success_probability m L {x} τ hτ hτ1
  simp only [Finset.mem_singleton,forall_eq,Finset.prod_singleton] at ha
  rw [FiniteLaw.bernoulli_required,hqevent,ha]
  simp only [Finset.prod_const]
  have hpow : τ^(L x).card * τ^(m-(L x).card) = τ^m := by
    rw [← pow_add,Nat.add_sub_of_le hL]
  by_cases hm : M ∈ L x
  · rw [ite_eq_left hm,Finset.insert_eq_of_mem hm]
    calc
      _ = q*(τ^(L x).card * τ^(m-(L x).card)) := by ring
      _ = _ := by rw [hpow]
  · rw [ite_eq_right hm,Finset.card_insert_of_notMem hm,pow_succ]
    calc
      _ = τ*q*(τ^(L x).card * τ^(m-(L x).card)) := by ring
      _ = _ := by rw [hpow]; ring

namespace DependentSample.Data

variable (d : Data V U)

theorem required_mark_probability (x : V) (M : U) (n : ℕ) (h : ℕ)
    (hinc : (d.listing x M).card ≤ h)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) n).event
      (fun ξ => M ∈ d.required (d.run n ξ).chosen x) ≤
        h*(q*τ^d.maxListSize) := by
  let μ := historyLaw (finiteClassLaw (V := V) (U := U) d.maxListSize q τ hq hq1 hτ hτ1) n
  calc
    _ ≤ μ.event (fun ξ => ∃ y ∈ d.listing x M, y ∈ (d.run n ξ).chosen) := by
      apply μ.event_mono
      intro ξ hm
      obtain ⟨y,hy,hM⟩ := Finset.mem_biUnion.mp hm
      obtain ⟨hyC,hxy⟩ := Finset.mem_filter.mp hy
      exact ⟨y,Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxy⟩,hM⟩,hyC⟩
    _ ≤ ∑ y ∈ d.listing x M, μ.event (fun ξ => y ∈ (d.run n ξ).chosen) :=
      μ.event_exists_finset_le_sum _ _
    _ ≤ ∑ _y ∈ d.listing x M, q*τ^d.maxListSize :=
      Finset.sum_le_sum (fun y _ => d.chosen_vertex_probability y n q τ hq hq1 hτ hτ1)
    _ = (d.listing x M).card*(q*τ^d.maxListSize) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hinc) (by positivity)

theorem tentative_joint_mark_conditional (i : ℕ) (C : Finset V) (x : V) (M : U)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1).event
      (fun ω => x ∈ d.tentative i C ω ∧ ω.1 M = true) ≤
        τ*(q*τ^d.maxListSize) +
          (q*τ^d.maxListSize)*(if M ∈ d.required C x then 1 else 0) := by
  by_cases he : d.Eligible C x
  · have hh := finiteClassPass_joint_mark d.maxListSize (d.required C) x M
      (d.required_card_le he) q τ hq hq1 hτ hτ1
    refine le_trans (FiniteLaw.event_mono _
      (Q := fun ω => finiteClassPass d.maxListSize (d.required C) x ω ∧ ω.1 M = true) ?_) ?_
    · intro ω hω
      exact ⟨(Finset.mem_filter.mp hω.1).2.2,hω.2⟩
    · rw [hh]
      split <;> simp <;> positivity
  · have hfalse :
        (fun ω => x ∈ d.tentative i C ω ∧ ω.1 M = true) = fun _ => False := by
      funext ω
      simp [tentative,he]
    rw [hfalse,FiniteLaw.event_false]
    positivity

theorem tentative_joint_mark (i : ℕ) (x : V) (M : U) (h : ℕ)
    (hinc : (d.listing x M).card ≤ h)
    (q τ : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    (historyLaw (finiteClassLaw d.maxListSize q τ hq hq1 hτ hτ1) (i+1)).event
      (fun ξ => x ∈ d.tentative i (d.run i ξ.1).chosen ξ.2 ∧ ξ.2.1 M = true) ≤
        τ*(q*τ^d.maxListSize) + h*(q*τ^d.maxListSize)^2 := by
  let μ := historyLaw (finiteClassLaw (V := V) (U := U) d.maxListSize q τ hq hq1 hτ hτ1) i
  change (μ.staged (fun _ => _)).event _ ≤ _
  rw [FiniteLaw.staged_event]
  calc
    _ ≤ μ.mean (fun ξ => τ*(q*τ^d.maxListSize) +
        (q*τ^d.maxListSize)*(if M ∈ d.required (d.run i ξ).chosen x then 1 else 0)) :=
      μ.mean_mono (fun ξ => d.tentative_joint_mark_conditional i _ x M q τ hq hq1 hτ hτ1)
    _ = τ*(q*τ^d.maxListSize) + (q*τ^d.maxListSize)*
        μ.event (fun ξ => M ∈ d.required (d.run i ξ).chosen x) := by
      rw [μ.mean_add,μ.mean_const,μ.mean_mul_const,μ.mean_indicator]
    _ ≤ τ*(q*τ^d.maxListSize) + (q*τ^d.maxListSize)*(h*(q*τ^d.maxListSize)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (d.required_mark_probability x M i h hinc q τ hq hq1 hτ hτ1)
        (by positivity : 0 ≤ q*τ^d.maxListSize))
    _ = _ := by ring

end DependentSample.Data
end TP3
