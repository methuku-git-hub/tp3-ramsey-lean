module

public import TP3.RestrictionLaw
public import TP3.Conditioning
public import TP3.FiniteCounting

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem restriction_vertices_required (c : Finset V → ℝ) (hc : ∀ e, 0 ≤ c e)
    (p δ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 ≤ δ) (S : Finset V) :
    (restrictionDataLaw c hc p δ hp hp1 hδ).event (fun ω => ∀ x ∈ S, ω.1 x=true) = p^S.card := by
  rw [restrictionDataLaw,FiniteLaw.staged_event_first _ _
    (fun ω : V → Bool => ∀ x ∈ S, ω x=true),FiniteLaw.bernoulli_required]
  simp

theorem restriction_forbidden_pair (c : Finset V → ℝ) (hc : ∀ e, 0 ≤ c e)
    (p δ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 ≤ δ) (S e : Finset V) :
    (restrictionDataLaw c hc p δ hp hp1 hδ).event
      (fun ω => (∀ x ∈ S, ω.1 x=true) ∧ ω.2 e=false) =
      p^S.card*(1-Real.exp (-δ*c e)) := by
  unfold restrictionDataLaw
  rw [FiniteLaw.independent_events _ _ (fun ω : V → Bool => ∀ x ∈ S, ω x=true)
    (fun ω : Finset V → Bool => ω e=false)]
  have hvertex : (FiniteLaw.product fun _ : V => FiniteLaw.bernoulli p hp hp1).event
      (fun ω => ∀ x ∈ S, ω x=true)=p^S.card := by
    rw [FiniteLaw.bernoulli_required]
    simp
  rw [hvertex]
  congr 1
  have hevent := FiniteLaw.bernoulli_required
    (fun f : Finset V => Real.exp (-δ*c f)) (fun _ => (Real.exp_pos _).le)
    (fun f => Real.exp_le_one_iff.mpr (by nlinarith [hc f])) {e}
  simp only [Finset.mem_singleton,forall_eq,Finset.prod_singleton] at hevent
  have hpred : (fun ω : Finset V → Bool => ω e=false)=(fun ω => ¬ ω e=true) := by
    funext ω
    simp
  rw [hpred,FiniteLaw.event_not,hevent]

theorem one_sub_exp_neg_le (t : ℝ) : 1-Real.exp (-t) ≤ t := by
  have hh := Real.add_one_le_exp (-t)
  linarith

end TP3
