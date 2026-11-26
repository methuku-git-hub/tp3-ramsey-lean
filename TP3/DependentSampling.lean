module

public import TP3.FiniteClassNoise
public import TP3.FiniteProcess
public import TP3.Deletion
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

namespace TP3.DependentSample

attribute [local instance] Classical.propDecidable

open scoped BigOperators

variable (V U : Type*) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

/-- Deterministic data fixed before making any choices. The incidence
bounds needed for the collision count will be proved for the lists made
by the graph-peeling argument; they are not built into the probability law. -/
structure Data where
  classes : ℕ
  classOf : V → Fin classes
  graph : SimpleGraph V
  triples : Finset (Finset V)
  sets : U → Finset V
  lists : V → V → Finset U
  listBound : ℕ
  list_card : ∀ x y, (lists x y).card ≤ listBound

variable {V U}

namespace Data

variable (d : Data V U)

def maxListSize : ℕ := d.listBound*d.classes

noncomputable def earlierNeighbors (C : Finset V) (x : V) : Finset V :=
  C.filter (fun y => d.graph.Adj x y)

noncomputable def required (C : Finset V) (x : V) : Finset U :=
  (d.earlierNeighbors C x).biUnion (d.lists x)

def Eligible (C : Finset V) (x : V) : Prop :=
  (d.earlierNeighbors C x).card ≤ d.classes

theorem required_card_le {C : Finset V} {x : V} (hx : d.Eligible C x) :
    (d.required C x).card ≤ d.maxListSize := by
  calc
    _ ≤ ∑ y ∈ d.earlierNeighbors C x, (d.lists x y).card := Finset.card_biUnion_le
    _ ≤ ∑ _y ∈ d.earlierNeighbors C x, d.listBound :=
      Finset.sum_le_sum (fun y _ => d.list_card x y)
    _ = (d.earlierNeighbors C x).card*d.listBound := by simp
    _ ≤ d.classes*d.listBound := Nat.mul_le_mul_right d.listBound hx
    _ = d.maxListSize := by simp [maxListSize, Nat.mul_comm]

noncomputable def classVertices (i : ℕ) : Finset V :=
  Finset.univ.filter (fun x => (d.classOf x).val = i)

noncomputable def tentative (i : ℕ) (C : Finset V)
    (ω : ClassNoise V U d.maxListSize) : Finset V :=
  (d.classVertices i).filter (fun x => d.Eligible C x ∧
    finiteClassPass d.maxListSize (d.required C) x ω)

/-- A shared mark requires deletion precisely for the two types of
supporting pairs whose overlap would leave no extra selected vertex. -/
def Conflict (C : Finset V) (x y : V) : Prop :=
  x ≠ y ∧ ∃ u ∈ d.earlierNeighbors C x, ∃ v ∈ d.earlierNeighbors C y,
    (d.lists x u ∩ d.lists y v).Nonempty ∧
      (u=v ∨ ∃ e ∈ d.triples, e ⊆ ({x,u,y,v} : Finset V))

noncomputable def conflicts (C A : Finset V) : Finset (Finset V) :=
  (A.powersetCard 2).filter (fun e => ∃ x ∈ e, ∃ y ∈ e, d.Conflict C x y)

theorem conflicts_nonempty (C A : Finset V) : ∀ e ∈ d.conflicts C A, e.Nonempty := by
  intro e he
  have hc := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2
  exact Finset.card_pos.mp (by omega)

noncomputable def retained (C A : Finset V) : Finset V :=
  deleteForbidden (d.conflicts C A) (d.conflicts_nonempty C A) A

theorem retained_subset (C A : Finset V) : d.retained C A ⊆ A :=
  deleteForbidden_subset _ _ _

theorem retained_size (C A : Finset V) :
    A.card ≤ (d.retained C A).card + (d.conflicts C A).card :=
  deleteForbidden_size _ _ _

theorem retained_no_conflict (C A : Finset V) {x y : V}
    (hx : x ∈ d.retained C A) (hy : y ∈ d.retained C A) :
    ¬ d.Conflict C x y := by
  intro hcon
  have hxy := hcon.1
  have hpair : ({x,y} : Finset V) ∈ d.conflicts C A := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powersetCard.mpr ⟨?_,by simp [hxy]⟩,?_⟩
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact d.retained_subset C A hx
      · have := Finset.mem_singleton.mp hz
        subst z
        exact d.retained_subset C A hy
    · exact ⟨x,by simp,y,by simp,hcon⟩
  apply deleteForbidden_independent (d.conflicts C A) (d.conflicts_nonempty C A)
    A {x,y} hpair
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
  exact ⟨hx,hy⟩

end Data

/-- The retained vertices, tentative vertices, and union of marked sets
are recorded separately, so their different deletion costs remain visible. -/
structure State where
  chosen : Finset V
  tentative : Finset V
  marked : Finset U

namespace Data

variable (d : Data V U)

def initial (_d : Data V U) : State (V := V) (U := U) := ⟨∅,∅,∅⟩

noncomputable def step (i : ℕ) (s : State (V := V) (U := U))
    (ω : ClassNoise V U d.maxListSize) : State (V := V) (U := U) :=
  let A := d.tentative i s.chosen ω
  { chosen := s.chosen ∪ d.retained s.chosen A
    tentative := s.tentative ∪ A
    marked := s.marked ∪ Finset.univ.filter (fun u => ω.1 u = true) }

noncomputable def run (n : ℕ) (h : History (ClassNoise V U d.maxListSize) n) :
    State (V := V) (U := U) := processState d.initial d.step n h

theorem run_chosen_subset_tentative (n : ℕ)
    (h : History (ClassNoise V U d.maxListSize) n) :
    (d.run n h).chosen ⊆ (d.run n h).tentative := by
  induction n with
  | zero => exact Finset.Subset.refl _
  | succ n ih =>
    change (d.run n h.1).chosen ∪ _ ⊆ (d.run n h.1).tentative ∪ _
    exact Finset.union_subset_union (ih h.1) (d.retained_subset _ _)

theorem run_tentative_class_lt (n : ℕ)
    (h : History (ClassNoise V U d.maxListSize) n) :
    ∀ x ∈ (d.run n h).tentative, (d.classOf x).val < n := by
  induction n with
  | zero => simp [run,processState,initial]
  | succ n ih =>
    intro x hx
    change x ∈ (d.run n h.1).tentative ∪ d.tentative n (d.run n h.1).chosen h.2 at hx
    rcases Finset.mem_union.mp hx with hp | hn
    · exact Nat.lt_succ_of_lt (ih h.1 x hp)
    · have hc := (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
      omega

theorem run_chosen_class_lt (n : ℕ)
    (h : History (ClassNoise V U d.maxListSize) n) :
    ∀ x ∈ (d.run n h).chosen, (d.classOf x).val < n :=
  fun x hx => d.run_tentative_class_lt n h x (d.run_chosen_subset_tentative n h hx)

end Data

end TP3.DependentSample
