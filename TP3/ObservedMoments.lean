module

public import TP3.AwayFeasible
public import TP3.FibreMoments
public import TP3.UniformFibres

@[expose] public section

namespace TP3.StarOrientation

attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : Finset (Finset V)} {v : V} (O : StarOrientation (link H v))

noncomputable def availableLeaves (F : Finset (Finset V)) (X I : Finset V) : Finset V :=
  (O.activeLeaves X (O.observation X I).1).filter
    (fun x => Independent F ((O.observation X I).2∪{x}))

theorem availableLeaves_congr (F : Finset (Finset V)) {X I I₀ : Finset V}
    (hobs : O.observation X I=O.observation X I₀) :
    O.availableLeaves F X I=O.availableLeaves F X I₀ := by
  simp only [availableLeaves,hobs]

theorem exp_leaf_weight (m : ℕ) (δ w : ℝ) :
    Real.exp (-(m:ℝ)*Real.log 2-δ*w)=Real.exp (-δ*w)/(2:ℝ)^m := by
  rw [show -(m:ℝ)*Real.log 2-δ*w=(-δ*w)-(m:ℝ)*Real.log 2 by ring,
    Real.exp_sub,Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]

theorem observed_link_mean (hH : IsTripleSystem H) (ω : RestrictionData V)
    (hgood : O.GoodInteractions ω) (I₀ : Finset V) (hI : I₀ ∈ awayFamily H ω v) :
    let X := (sampledVertices ω).erase v
    let B := (awayFamily H ω v).filter (fun I => O.observation X I=O.observation X I₀)
    (FiniteLaw.uniform B ⟨I₀,Finset.mem_filter.mpr ⟨hI,rfl⟩⟩).mean (linkCount H v) =
      ((O.availableLeaves (forbiddenFamily H ω) X I₀).card : ℝ)/2 := by
  let X := (sampledVertices ω).erase v
  let U := O.activeLeaves X (I₀∩O.centres)
  let A := I₀\U
  let M := O.availableLeaves (forbiddenFamily H ω) X I₀
  let B := (awayFamily H ω v).filter (fun I => O.observation X I=O.observation X I₀)
  have hB : B.Nonempty := ⟨I₀,by simp [B,hI]⟩
  have heq : B=M.powerset.image (fun S => A∪S) := O.away_observation_fiber hH ω hgood I₀ hI
  have hMU : M ⊆ U := Finset.filter_subset _ _
  have hAU : Disjoint A U := Finset.disjoint_left.mpr (fun x hx hxu => (Finset.mem_sdiff.mp hx).2 hxu)
  change (FiniteLaw.uniform B hB).mean (linkCount H v)=(M.card:ℝ)/2
  calc
    _ = (FiniteLaw.uniform B hB).mean (fun I => ((I∩U).card : ℝ)) := by
      apply FiniteLaw.uniform_mean_congr_on
      intro I hIB
      obtain ⟨hIF,hobs⟩ := Finset.mem_filter.mp hIB
      exact O.linkCount_in_fiber (Finset.mem_powerset.mp (Finset.mem_filter.mp hIF).1) hobs
    _ = (FiniteLaw.uniform (M.powerset.image (fun S => A∪S))
        ((show M.powerset.Nonempty from ⟨∅,by simp⟩).image _)).mean
        (fun I => ((I∩U).card : ℝ)) := by
      rw [FiniteLaw.uniform_mean,FiniteLaw.uniform_mean,heq]
    _ = _ := union_powerset_mean_inter A U M hAU hMU

theorem observed_empty_mean (hH : IsTripleSystem H) (ω : RestrictionData V)
    (hgood : O.GoodInteractions ω) (I₀ : Finset V) (hI : I₀ ∈ awayFamily H ω v) (δ : ℝ) :
    let X := (sampledVertices ω).erase v
    let B := (awayFamily H ω v).filter (fun I => O.observation X I=O.observation X I₀)
    (FiniteLaw.uniform B ⟨I₀,Finset.mem_filter.mpr ⟨hI,rfl⟩⟩).mean
      (fun I => if linkCount H v I=0 then Real.exp (-δ*incidentCost H v I) else 0) =
      Real.exp (-((O.availableLeaves (forbiddenFamily H ω) X I₀).card : ℝ)*Real.log 2-
        δ*incidentCost H v (O.observation X I₀).2) := by
  let X := (sampledVertices ω).erase v
  let U := O.activeLeaves X (I₀∩O.centres)
  let A := I₀\U
  let M := O.availableLeaves (forbiddenFamily H ω) X I₀
  let B := (awayFamily H ω v).filter (fun I => O.observation X I=O.observation X I₀)
  have hB : B.Nonempty := ⟨I₀,by simp [B,hI]⟩
  have heq : B=M.powerset.image (fun S => A∪S) := O.away_observation_fiber hH ω hgood I₀ hI
  have hMU : M ⊆ U := Finset.filter_subset _ _
  have hAU : Disjoint A U := Finset.disjoint_left.mpr (fun x hx hxu => (Finset.mem_sdiff.mp hx).2 hxu)
  change (FiniteLaw.uniform B hB).mean _=Real.exp (-(M.card:ℝ)*Real.log 2-δ*incidentCost H v A)
  rw [exp_leaf_weight]
  calc
    _ = (FiniteLaw.uniform B hB).mean (fun I => if I∩U=∅ then Real.exp (-δ*incidentCost H v I) else 0) := by
      apply FiniteLaw.uniform_mean_congr_on
      intro I hIB
      obtain ⟨hIF,hobs⟩ := Finset.mem_filter.mp hIB
      rw [O.linkCount_in_fiber (Finset.mem_powerset.mp (Finset.mem_filter.mp hIF).1) hobs]
      simp only [Nat.cast_eq_zero,Finset.card_eq_zero]
      congr 1
    _ = (FiniteLaw.uniform (M.powerset.image (fun S => A∪S))
        ((show M.powerset.Nonempty from ⟨∅,by simp⟩).image _)).mean
        (fun I => if I∩U=∅ then Real.exp (-δ*incidentCost H v I) else 0) := by
      rw [FiniteLaw.uniform_mean,FiniteLaw.uniform_mean,heq]
    _ = _ := union_powerset_mean_empty A U M hAU hMU (fun I => Real.exp (-δ*incidentCost H v I))

end TP3.StarOrientation
