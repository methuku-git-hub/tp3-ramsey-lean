module

public import TP3.AwayFeasible

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem mem_awayFamily_explicit {H : Finset (Finset V)} {ω : RestrictionData V} {v : V} {S : Finset V} :
    S ∈ awayFamily H ω v ↔ Independent H S ∧ v ∉ S ∧
      (∀ x ∈ S, ω.1 x=true) ∧ (∀ e ∈ S.powersetCard 2, ω.2 e=true) := by
  have heq : awayFamily H ω v=(feasibleFamily H ω).filter (fun S => v ∉ S) := by
    rw [feasibleFamily_eq_allowedSubsets]
    ext S
    simp only [awayFamily,allowedSubsets,Finset.mem_filter,Finset.mem_powerset,Finset.subset_erase]
    tauto
  rw [heq]
  simp only [Finset.mem_filter,feasibleFamily,Finset.mem_univ,true_and]
  tauto

/-- The family omitting v depends on neither the vertex decision at v
nor any of the pair decisions at v. -/
theorem awayFamily_congr (H : Finset (Finset V)) (v : V) (ω ω' : RestrictionData V)
    (hvertices : ∀ x, x ≠ v → ω.1 x=ω'.1 x)
    (hpairs : ∀ e, v ∉ e → ω.2 e=ω'.2 e) : awayFamily H ω v=awayFamily H ω' v := by
  ext S
  simp only [mem_awayFamily_explicit]
  by_cases hvS : v ∈ S
  · simp [hvS]
  · have hx (x) (hxs : x ∈ S) : x ≠ v := fun hh => hvS (hh ▸ hxs)
    have he (e) (heS : e ∈ S.powersetCard 2) : v ∉ e :=
      fun hve => hvS ((Finset.mem_powersetCard.mp heS).1 hve)
    constructor
    · rintro ⟨hind,hv,hvert,hpair⟩
      exact ⟨hind,hv,fun x hxs => by rw [← hvertices x (hx x hxs)]; exact hvert x hxs,
        fun e heS => by rw [← hpairs e (he e heS)]; exact hpair e heS⟩
    · rintro ⟨hind,hv,hvert,hpair⟩
      exact ⟨hind,hv,fun x hxs => by rw [hvertices x (hx x hxs)]; exact hvert x hxs,
        fun e heS => by rw [hpairs e (he e heS)]; exact hpair e heS⟩

noncomputable def awayLaw (H : Finset (Finset V)) (hH : IsTripleSystem H)
    (c : Finset V → ℝ) (hc : ∀ e, 0 ≤ c e)
    (p δ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 ≤ δ) (v : V) : FiniteLaw (Finset V) :=
  (restrictionDataLaw c hc p δ hp hp1 hδ).bind
    (fun ω => FiniteLaw.uniform (awayFamily H ω v) (awayFamily_nonempty hH ω v))

end TP3
