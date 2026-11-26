module

public import TP3.ObservedMoments
public import TP3.FiniteMeanAlgebra

@[expose] public section

namespace TP3.StarOrientation

attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : Finset (Finset V)} {v : V} (O : StarOrientation (link H v))

/-- Average the conditional leaf count over all centre/outside
observations, for a fixed good restriction outcome. -/
theorem away_mean_available (hH : IsTripleSystem H) (ω : RestrictionData V)
    (hgood : O.GoodInteractions ω) :
    (FiniteLaw.uniform (awayFamily H ω v) (awayFamily_nonempty hH ω v)).mean
      (fun I => ((O.availableLeaves (forbiddenFamily H ω) ((sampledVertices ω).erase v) I).card : ℝ)) =
      2*(FiniteLaw.uniform (awayFamily H ω v) (awayFamily_nonempty hH ω v)).mean (linkCount H v) := by
  let X := (sampledVertices ω).erase v
  let f := fun I => ((O.availableLeaves (forbiddenFamily H ω) X I).card : ℝ)
  have hh := FiniteLaw.uniform_mean_eq_of_fiber_means (awayFamily H ω v)
    (awayFamily_nonempty hH ω v) (O.observation X) f (fun I => 2*linkCount H v I) (by
      intro I₀ hI
      let B := (awayFamily H ω v).filter (fun I => O.observation X I=O.observation X I₀)
      have hB : B.Nonempty := ⟨I₀,Finset.mem_filter.mpr ⟨hI,rfl⟩⟩
      have hc : (FiniteLaw.uniform B hB).mean f=f I₀ := by
        calc
          _ = (FiniteLaw.uniform B hB).mean (fun _ => f I₀) := by
            apply FiniteLaw.uniform_mean_congr_on
            intro I hIB
            exact congrArg (fun M : Finset V => (M.card:ℝ))
              (O.availableLeaves_congr _ (Finset.mem_filter.mp hIB).2)
          _ = _ := FiniteLaw.mean_const _ _
      change (FiniteLaw.uniform B hB).mean f=(FiniteLaw.uniform B hB).mean _
      rw [hc,FiniteLaw.mean_mul_const]
      have hm := O.observed_link_mean hH ω hgood I₀ hI
      change (FiniteLaw.uniform B hB).mean (linkCount H v)=f I₀/2 at hm
      rw [hm]
      ring)
  rwa [FiniteLaw.mean_mul_const] at hh

noncomputable def observationCost (ω : RestrictionData V) (δ : ℝ) (I : Finset V) : ℝ :=
  ((O.availableLeaves (forbiddenFamily H ω) ((sampledVertices ω).erase v) I).card : ℝ)*Real.log 2+
    δ*incidentCost H v (O.observation ((sampledVertices ω).erase v) I).2

/-- The exponential after revealing centres and outside choices has
the same mean as the weighted probability of no chosen link edge. -/
theorem away_mean_empty (hH : IsTripleSystem H) (ω : RestrictionData V)
    (hgood : O.GoodInteractions ω) (δ : ℝ) :
    (FiniteLaw.uniform (awayFamily H ω v) (awayFamily_nonempty hH ω v)).mean
      (fun I => if linkCount H v I=0 then Real.exp (-δ*incidentCost H v I) else 0) =
    (FiniteLaw.uniform (awayFamily H ω v) (awayFamily_nonempty hH ω v)).mean
      (fun I => Real.exp (-O.observationCost ω δ I)) := by
  let X := (sampledVertices ω).erase v
  apply FiniteLaw.uniform_mean_eq_of_fiber_means _ _ (O.observation X)
  intro I₀ hI
  let B := (awayFamily H ω v).filter (fun I => O.observation X I=O.observation X I₀)
  have hB : B.Nonempty := ⟨I₀,Finset.mem_filter.mpr ⟨hI,rfl⟩⟩
  have hc : (FiniteLaw.uniform B hB).mean (fun I => Real.exp (-O.observationCost ω δ I)) =
      Real.exp (-O.observationCost ω δ I₀) := by
    calc
      _ = (FiniteLaw.uniform B hB).mean (fun _ => Real.exp (-O.observationCost ω δ I₀)) := by
        apply FiniteLaw.uniform_mean_congr_on
        intro I hIB
        have hobs := (Finset.mem_filter.mp hIB).2
        dsimp only [X] at hobs
        simp only [observationCost,O.availableLeaves_congr _ hobs,hobs]
      _ = _ := FiniteLaw.mean_const _ _
  change (FiniteLaw.uniform B hB).mean _=(FiniteLaw.uniform B hB).mean _
  rw [hc]
  have hm := O.observed_empty_mean hH ω hgood I₀ hI δ
  convert hm using 1
  dsimp only [observationCost]
  congr 1
  ring

theorem observationCost_nonneg (ω : RestrictionData V) (δ : ℝ) (hδ : 0 ≤ δ) (I : Finset V) :
    0 ≤ O.observationCost ω δ I := by
  apply add_nonneg
  · exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  · exact mul_nonneg hδ (incidentCost_nonneg _ _ _)

theorem away_mean_observationCost (hH : IsTripleSystem H) (ω : RestrictionData V)
    (hgood : O.GoodInteractions ω) (δ : ℝ) (hδ : 0 ≤ δ) :
    (FiniteLaw.uniform (awayFamily H ω v) (awayFamily_nonempty hH ω v)).mean (O.observationCost ω δ) ≤
      2*Real.log 2*(FiniteLaw.uniform (awayFamily H ω v) (awayFamily_nonempty hH ω v)).mean (linkCount H v)+
        δ*(FiniteLaw.uniform (awayFamily H ω v) (awayFamily_nonempty hH ω v)).mean (incidentCost H v) := by
  let μ := FiniteLaw.uniform (awayFamily H ω v) (awayFamily_nonempty hH ω v)
  have hpoint (I : Finset V) : O.observationCost ω δ I ≤
      Real.log 2*((O.availableLeaves (forbiddenFamily H ω) ((sampledVertices ω).erase v) I).card : ℝ)+
        δ*incidentCost H v I := by
    have hh := mul_le_mul_of_nonneg_left
      (incidentCost_mono H v (show (O.observation ((sampledVertices ω).erase v) I).2 ⊆ I from Finset.sdiff_subset)) hδ
    dsimp only [observationCost]
    linarith
  have hh := μ.mean_mono hpoint
  rw [μ.mean_add,μ.mean_mul_const,μ.mean_mul_const,O.away_mean_available hH ω hgood] at hh
  nlinarith only [hh]

end TP3.StarOrientation
