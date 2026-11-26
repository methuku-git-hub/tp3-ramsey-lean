module

public import TP3.AveragedDensity
public import TP3.ParameterChoice

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The final independent-set lemma, with D=exp(12L). The random
restriction estimates, including the averaged inequality, are derived
above rather than supplied as extra hypotheses. -/
theorem structured_independence_exponential (H : Finset (Finset V)) (hH : IsTripleSystem H)
    (hfree : ¬ HasTightPath H) (hind : IndependentPairNeighborhoods H)
    (hN : 0 < Fintype.card V) (L : ℝ) (hL : 100 ≤ L)
    (hdegree : ∀ x, (degree H x : ℝ) ≤ Real.exp (12*L)) :
    ∃ I : Finset V, Independent H I ∧
      (Fintype.card V : ℝ)*Real.sqrt L*Real.exp (-6*L)/100 ≤ I.card := by
  let D := Real.exp (12*L)
  let p := Real.exp (-5*L)
  let δ := Real.sqrt L*Real.exp (-6*L)
  obtain ⟨hp,hp_small,hδ,hD,hLpos,hscale,hsmall,hlog_upper,hlog_lower,hbad⟩ := parameter_choice L hL
  change 0 < p at hp
  change p ≤ 1/4 at hp_small
  change 0 < δ at hδ
  change 0 < D at hD
  change δ^2*D=L at hscale
  change δ/100 ≤ p at hsmall
  change Real.log (100*Real.exp 1*p/δ) ≤ 2*L at hlog_upper
  change L/5 < Real.log (25*p/δ) at hlog_lower
  change D^2*(δ*p^4+p^5) ≤ 1/2 at hbad
  have hp1 : p < 1 := by linarith
  let μ := restrictedLaw H hH (codegreeCost H) (codegreeCost_nonneg H) p δ hp.le hp1.le hδ.le
  let N : ℝ := Fintype.card V
  let ρ := μ.mean (fun I => (I.card : ℝ))/N
  let w := μ.mean (pairCost (codegreeCost H))/N
  have hN0 : 0 < N := by change 0 < (Fintype.card V : ℝ); exact_mod_cast hN
  have haverage := averaged_density_bound H hH hfree hind hN D hD.le hdegree p δ hp hp1 hδ.le hbad
  change 0 < ρ ∧ Real.log (p/(4*ρ)) ≤ 4*Real.log 2/(1-p)*w+4*δ*D*ρ/(1-p) at haverage
  have hw : 0 ≤ w := div_nonneg
    (μ.mean_nonneg (fun I => Finset.sum_nonneg (fun e _ => codegreeCost_nonneg H e))) hN0.le
  have hdensity : μ.mean (fun I => (I.card : ℝ))=N*ρ := by dsimp only [ρ]; field_simp
  have hcharge := restrictedLaw_charge H hH (codegreeCost H) (codegreeCost_nonneg H)
    p δ hp hp1.le hδ.le haverage.1 hdensity
  have hcharge' : δ*w ≤ ρ*Real.log (Real.exp 1*p/ρ) := by
    change δ*(μ.mean (pairCost (codegreeCost H))/N) ≤ _
    rw [← mul_div_assoc,div_le_iff₀ hN0]
    convert hcharge using 1 <;> ring
  have hgain := density_gain_of_estimates hp hp_small hδ hD hLpos hscale hsmall
    haverage.1 hw hcharge' haverage.2 hlog_upper hlog_lower
  obtain ⟨I,hI,hsize⟩ := μ.exists_support_ge_mean (fun I => (I.card : ℝ))
  refine ⟨I,restrictedLaw_independent H hH (codegreeCost H) (codegreeCost_nonneg H)
    p δ hp.le hp1.le hδ.le I hI,?_⟩
  have hh := mul_le_mul_of_nonneg_left hgain.le hN0.le
  rw [← hdensity] at hh
  have hb := hh.trans hsize
  change N*Real.sqrt L*Real.exp (-6*L)/100 ≤ _
  convert hb using 1
  dsimp only [δ]
  ring

end TP3
