module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.Pairwise
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

@[expose] public section

namespace TP3

variable {V : Type*} [DecidableEq V]

/-- A triple system is a family of three-element subsets of its vertex set. -/
def IsTripleSystem (H : Finset (Finset V)) : Prop :=
  ∀ e ∈ H, e.card = 3

/-- The three-edge tight path consists of abc, bcd, and cde
on five distinct vertices. Additional edges are permitted. -/
def HasTightPath (H : Finset (Finset V)) : Prop :=
  ∃ a b c d e : V, [a, b, c, d, e].Pairwise (· ≠ ·) ∧
    {a, b, c} ∈ H ∧ {b, c, d} ∈ H ∧ {c, d, e} ∈ H

/-- A set is independent when it contains no edge of the triple system. -/
def Independent (H : Finset (Finset V)) (S : Finset V) : Prop :=
  ∀ e ∈ H, ¬ e ⊆ S

/-- The vertices completing a pair to an edge. The two endpoints are excluded. -/
def pairNeighbors [Fintype V] (H : Finset (Finset V)) (a b : V) : Finset V :=
  Finset.univ.filter fun x => x ≠ a ∧ x ≠ b ∧ {a, b, x} ∈ H

/-- The number of vertices completing a pair. -/
def codegree [Fintype V] (H : Finset (Finset V)) (a b : V) : ℕ :=
  (pairNeighbors H a b).card

/-- The number of hyperedges containing a vertex. -/
def degree (H : Finset (Finset V)) (v : V) : ℕ :=
  (H.filter fun e => v ∈ e).card

/-- Restrict the vertex set while keeping every edge contained in it. -/
def induced (H : Finset (Finset V)) (S : Finset V) : Finset (Finset V) :=
  H.filter fun e => e ⊆ S

end TP3
