module

public import TP3.Structure
public import TP3.FiniteCounting

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
open scoped BigOperators

variable {V : Type*} [DecidableEq V]

/-- A graph represented by its unordered two-element edges. -/
def IsPairSystem (G : Finset (Finset V)) : Prop := ∀ e ∈ G, e.card=2

theorem degree_mono {G K : Finset (Finset V)} (hGK : G ⊆ K) (v : V) :
    degree G v ≤ degree K v :=
  Finset.card_le_card (Finset.filter_subset_filter _ hGK)

theorem induced_mono_vertices (G : Finset (Finset V)) {X Y : Finset V}
    (hXY : X ⊆ Y) : induced G X ⊆ induced G Y := by
  intro e he
  obtain ⟨heG,heX⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨heG,heX.trans hXY⟩

theorem induced_induced (G : Finset (Finset V)) {X Y : Finset V}
    (hXY : X ⊆ Y) : induced (induced G Y) X = induced G X := by
  ext e
  simp only [induced,Finset.mem_filter]
  exact ⟨fun hh => ⟨hh.1.1,hh.2⟩,fun hh => ⟨⟨hh.1,hh.2.trans hXY⟩,hh.2⟩⟩

theorem degree_induced_le (G : Finset (Finset V)) (X : Finset V) (v : V) :
    degree (induced G X) v ≤ degree G v := degree_mono (Finset.filter_subset _ _) v

theorem induced_erase_partition (G : Finset (Finset V)) (Y : Finset V) (v : V) :
    (induced G Y).card = (induced G (Y.erase v)).card + degree (induced G Y) v := by
  have heq : induced G (Y.erase v) = (induced G Y).filter (fun e => v ∉ e) := by
    ext e
    simp only [induced,Finset.mem_filter,Finset.subset_erase]
    tauto
  rw [heq]
  simpa only [degree,not_not] using
    (Finset.card_filter_add_card_filter_not (s := induced G Y) (p := fun e : Finset V => v ∉ e)).symm

/-- A graph in which every nonempty induced subgraph has a vertex of
degree below a has at most a times its number of vertices edges. -/
theorem induced_edges_le_of_low_degree (G : Finset (Finset V))
    (hG : ∀ e ∈ G, e.Nonempty) (a : ℝ) (ha : 0 ≤ a)
    (Y : Finset V)
    (hlow : ∀ X ⊆ Y, X.Nonempty → ∃ v ∈ X, (degree (induced G X) v : ℝ) < a) :
    ((induced G Y).card : ℝ) ≤ a*Y.card := by
  induction Y using Finset.strongInductionOn with
  | _ Y ih =>
    by_cases hy : Y=∅
    · subst Y
      have he : induced G ∅=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro e he
        obtain ⟨heG,heE⟩ := Finset.mem_filter.mp he
        exact (hG e heG).ne_empty (Finset.subset_empty.mp heE)
      simp [he]
    · obtain ⟨v,hv,hdeg⟩ := hlow Y (Finset.Subset.refl _) (Finset.nonempty_iff_ne_empty.mpr hy)
      have heY := Finset.erase_ssubset hv
      have hrest := ih (Y.erase v) heY (fun X hXY hX =>
        hlow X (hXY.trans (Finset.erase_subset _ _)) hX)
      have hcount := induced_erase_partition G Y v
      have hsize := Finset.card_erase_add_one hv
      have hc : ((induced G Y).card : ℝ) =
          (induced G (Y.erase v)).card + degree (induced G Y) v := by exact_mod_cast hcount
      have hs : ((Y.erase v).card : ℝ)+1=Y.card := by exact_mod_cast hsize
      nlinarith

variable [Fintype V]

/-- Count incidences by vertices or by edges, for an arbitrary finite
hypergraph. This is later applied to pairs and triples. -/
theorem sum_degree_eq_sum_card (H : Finset (Finset V)) :
    ∑ v : V, degree H v = ∑ e ∈ H, e.card := by
  have hd (v : V) : degree H v = ∑ e ∈ H, if v ∈ e then 1 else 0 := by
    simp [degree,← Finset.sum_filter]
  simp_rw [hd]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  simp

theorem sum_degree_triples {H : Finset (Finset V)} (hH : IsTripleSystem H) :
    ∑ v : V, degree H v = 3*H.card := by
  rw [sum_degree_eq_sum_card]
  calc
    _ = ∑ _e ∈ H, 3 := Finset.sum_congr rfl hH
    _ = _ := by simp [Nat.mul_comm]

end TP3
