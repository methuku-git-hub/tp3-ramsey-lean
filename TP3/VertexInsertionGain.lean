module

public import TP3.ConditionalAverages
public import TP3.ExtensionWeights
public import TP3.GoodEventJensen

@[expose] public section

namespace TP3.StarOrientation

attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : Finset (Finset V)} {v : V} (O : StarOrientation (link H v))

include O

/-- The insertion gain for one vertex, derived from the constructed
restriction law, the centres-first fibres, and the good-event estimate. -/
theorem vertex_insertion_gain (hH : IsTripleSystem H) (hind : IndependentPairNeighborhoods H)
    (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ x, (degree H x : ℝ) ≤ D)
    (p δ : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hδ : 0 ≤ δ)
    (hbad : D^2*(δ*p^4+p^5) ≤ 1/2) :
    let ν := awayLaw H hH (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1 hδ v
    (p/4)*Real.exp (-4*Real.log 2*ν.mean (linkCount H v)-2*δ*ν.mean (incidentCost H v)) ≤
      (restrictedLaw H hH (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1 hδ).event (fun I => v ∈ I) := by
  let μ := restrictionDataLaw (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1 hδ
  let κ := fun ω => FiniteLaw.uniform (awayFamily H ω v) (awayFamily_nonempty hH ω v)
  let ν := awayLaw H hH (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1 hδ v
  let η := μ.staged κ
  let G := fun ξ : RestrictionData V × Finset V => O.GoodInteractions ξ.1
  let X := fun ξ : RestrictionData V × Finset V => O.observationCost ξ.1 δ ξ.2
  let C := 2*Real.log 2*ν.mean (linkCount H v)+δ*ν.mean (incidentCost H v)
  have hB0 (I : Finset V) : 0 ≤ linkCount H v I := Nat.cast_nonneg _
  have hW0 (I : Finset V) : 0 ≤ incidentCost H v I := incidentCost_nonneg _ _ _
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hC : 0 ≤ C := add_nonneg (mul_nonneg (by positivity) (ν.mean_nonneg hB0))
    (mul_nonneg hδ (ν.mean_nonneg hW0))
  have hg : (1:ℝ)/2 ≤ η.event G := by
    have hh := O.goodInteractions_probability hH hind D hD0 hD p δ hp hp1 hδ
    change (1:ℝ)/2 ≤ (μ.staged κ).event (fun ξ => O.GoodInteractions ξ.1)
    rw [FiniteLaw.staged_event_first μ κ O.GoodInteractions]
    linarith
  have hm : η.mean (fun ξ => if G ξ then X ξ else 0) ≤ C := by
    rw [FiniteLaw.staged_mean]
    have hpoint (ω : RestrictionData V) :
        (κ ω).mean (fun I => if O.GoodInteractions ω then O.observationCost ω δ I else 0) ≤
        2*Real.log 2*(κ ω).mean (linkCount H v)+δ*(κ ω).mean (incidentCost H v) := by
      by_cases hgood : O.GoodInteractions ω
      · simp only [if_pos hgood]
        exact O.away_mean_observationCost hH ω hgood δ hδ
      · simp only [if_neg hgood,FiniteLaw.mean_const]
        exact add_nonneg (mul_nonneg (by positivity) ((κ ω).mean_nonneg hB0))
          (mul_nonneg hδ ((κ ω).mean_nonneg hW0))
    have hh := μ.mean_mono hpoint
    rw [μ.mean_add,μ.mean_mul_const,μ.mean_mul_const] at hh
    dsimp only [C,ν,awayLaw]
    rw [FiniteLaw.bind_mean,FiniteLaw.bind_mean]
    convert hh using 1 <;> congr 3
  have hj := η.good_event_exp_lower G X hg C hC hm
  have hretained : η.mean (fun ξ => if G ξ then Real.exp (-X ξ) else 0) ≤
      ν.mean (fun I => if linkCount H v I=0 then Real.exp (-δ*incidentCost H v I) else 0) := by
    change (μ.staged κ).mean _ ≤ (μ.bind κ).mean _
    rw [FiniteLaw.staged_mean,FiniteLaw.bind_mean]
    apply μ.mean_mono
    intro ω
    by_cases hgood : O.GoodInteractions ω
    · simp only [G,X,if_pos hgood]
      exact (O.away_mean_empty hH ω hgood δ).symm.le
    · simp only [G,if_neg hgood,FiniteLaw.mean_const]
      apply FiniteLaw.mean_nonneg
      intro I
      split <;> positivity
  have hinsert := away_insert_bound H hH p δ hp hp1 hδ v
  have hgain := (mul_le_mul_of_nonneg_left (hj.trans hretained) (show 0 ≤ p/2 by positivity)).trans hinsert
  change (p/4)*Real.exp (-4*Real.log 2*ν.mean (linkCount H v)-2*δ*ν.mean (incidentCost H v)) ≤ _
  convert hgain using 1
  dsimp only [C]
  ring_nf

end TP3.StarOrientation
