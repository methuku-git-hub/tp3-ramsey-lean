module

public import TP3.VertexInsertionGain
public import TP3.RemovedCosts
public import TP3.FiniteCardinality

@[expose] public section

namespace TP3

attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem sum_away_linkCount_le (H : Finset (Finset V)) (hH : IsTripleSystem H)
    (p δ : ℝ) (hp : 0 ≤ p) (hp1 : p < 1) (hδ : 0 ≤ δ) :
    (∑ v : V, (awayLaw H hH (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1.le hδ v).mean
      (linkCount H v)) ≤
    (restrictedLaw H hH (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1.le hδ).mean
      (pairCost (codegreeCost H))/(1-p) := by
  let μ := restrictedLaw H hH (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1.le hδ
  calc
    _ ≤ ∑ v : V, μ.mean (linkCount H v)/(1-p) :=
      Finset.sum_le_sum (fun v _ => away_linkCount_le H hH p δ hp hp1 hδ v)
    _ = μ.mean (fun I => ∑ v : V, linkCount H v I)/(1-p) := by
      rw [μ.mean_sum,Finset.sum_div]
    _ = _ := by simp only [linkCount_sum]; congr 1

theorem sum_away_incidentCost_le (H : Finset (Finset V)) (hH : IsTripleSystem H)
    (D : ℝ) (hD : ∀ x, (degree H x : ℝ) ≤ D)
    (p δ : ℝ) (hp : 0 ≤ p) (hp1 : p < 1) (hδ : 0 ≤ δ) :
    (∑ v : V, (awayLaw H hH (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1.le hδ v).mean
      (incidentCost H v)) ≤
    2*D*(restrictedLaw H hH (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1.le hδ).mean
      (fun I => (I.card : ℝ))/(1-p) := by
  let μ := restrictedLaw H hH (codegreeCost H) (codegreeCost_nonneg H) p δ hp hp1.le hδ
  calc
    _ ≤ ∑ v : V, μ.mean (incidentCost H v)/(1-p) :=
      Finset.sum_le_sum (fun v _ => away_incidentCost_le H hH p δ hp hp1 hδ v)
    _ = μ.mean (fun I => ∑ v : V, incidentCost H v I)/(1-p) := by
      rw [μ.mean_sum,Finset.sum_div]
    _ ≤ μ.mean (fun I => 2*D*I.card)/(1-p) :=
      div_le_div_of_nonneg_right (μ.mean_mono (incidentCost_sum_le hH D hD)) (sub_pos.mpr hp1).le
    _ = _ := by rw [μ.mean_mul_const]

/-- The averaged logarithmic inequality, proved from the actual random
restriction experiment. Its hypotheses are precisely the structural
properties and the numerical good-event bound used in the manuscript. -/
theorem averaged_density_bound (H : Finset (Finset V)) (hH : IsTripleSystem H)
    (hfree : ¬ HasTightPath H) (hind : IndependentPairNeighborhoods H)
    (hN : 0 < Fintype.card V) (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ x, (degree H x : ℝ) ≤ D)
    (p δ : ℝ) (hp : 0 < p) (hp1 : p < 1) (hδ : 0 ≤ δ)
    (hbad : D^2*(δ*p^4+p^5) ≤ 1/2) :
    let μ := restrictedLaw H hH (codegreeCost H) (codegreeCost_nonneg H) p δ hp.le hp1.le hδ
    let ρ := μ.mean (fun I => (I.card : ℝ))/(Fintype.card V : ℝ)
    let w := μ.mean (pairCost (codegreeCost H))/(Fintype.card V : ℝ)
    0 < ρ ∧ Real.log (p/(4*ρ)) ≤ 4*Real.log 2/(1-p)*w+4*δ*D*ρ/(1-p) := by
  let μ := restrictedLaw H hH (codegreeCost H) (codegreeCost_nonneg H) p δ hp.le hp1.le hδ
  let ν := fun v => awayLaw H hH (codegreeCost H) (codegreeCost_nonneg H) p δ hp.le hp1.le hδ v
  let N : ℝ := Fintype.card V
  let ρ := μ.mean (fun I => (I.card : ℝ))/N
  let w := μ.mean (pairCost (codegreeCost H))/N
  have hN0 : 0 < N := by change 0 < (Fintype.card V : ℝ); exact_mod_cast hN
  have hV : (Finset.univ : Finset V).Nonempty := Finset.card_pos.mp (by simpa using hN)
  let η := FiniteLaw.uniform (Finset.univ : Finset V) hV
  let B := fun v => (ν v).mean (linkCount H v)
  let W := fun v => (ν v).mean (incidentCost H v)
  let C := 4*Real.log 2*η.mean B+2*δ*η.mean W
  have hb : η.mean B ≤ w/(1-p) := by
    have hh := div_le_div_of_nonneg_right (sum_away_linkCount_le H hH p δ hp.le hp1 hδ) hN0.le
    rw [FiniteLaw.uniform_mean,Finset.card_univ]
    convert hh using 1 <;> dsimp only [w,N] <;> ring
  have hw : η.mean W ≤ 2*D*ρ/(1-p) := by
    have hh := div_le_div_of_nonneg_right (sum_away_incidentCost_le H hH D hD p δ hp.le hp1 hδ) hN0.le
    rw [FiniteLaw.uniform_mean,Finset.card_univ]
    convert hh using 1 <;> dsimp only [ρ,N] <;> ring
  have hρmean : η.mean (fun v => μ.event (fun I => v ∈ I))=ρ := by
    rw [FiniteLaw.uniform_mean,Finset.card_univ,← μ.mean_card (fun I : Finset V => I)]
  have hinsert (v : V) : (p/4)*Real.exp (-4*Real.log 2*B v-2*δ*W v) ≤ μ.event (fun I => v ∈ I) := by
    obtain ⟨O⟩ := link_starOrientation hfree hind v
    exact O.vertex_insertion_gain hH hind D hD0 hD p δ hp.le hp1.le hδ hbad
  have hmean := η.mean_mono hinsert
  rw [η.mean_mul_const,hρmean] at hmean
  have hj := η.exp_mean_le (fun v => -4*Real.log 2*B v-2*δ*W v)
  have hz : η.mean (fun v => -4*Real.log 2*B v-2*δ*W v) = -C := by
    rw [η.mean_sub,η.mean_mul_const,η.mean_mul_const]
    dsimp only [C]
    ring
  rw [hz] at hj
  have hρbound : (p/4)*Real.exp (-C) ≤ ρ :=
    (mul_le_mul_of_nonneg_left hj (by positivity : 0 ≤ p/4)).trans hmean
  have hρpos : 0 < ρ := lt_of_lt_of_le (mul_pos (by positivity) (Real.exp_pos _)) hρbound
  have hlog : Real.log (p/(4*ρ)) ≤ C := by
    have hh := Real.log_le_log (mul_pos (show 0 < p/4 by positivity) (Real.exp_pos (-C))) hρbound
    rw [Real.log_mul (div_ne_zero hp.ne' (by norm_num)) (Real.exp_ne_zero _),
      Real.log_div hp.ne' (by norm_num : (4:ℝ) ≠ 0),Real.log_exp] at hh
    rw [Real.log_div hp.ne' (mul_ne_zero (by norm_num) hρpos.ne'),
      Real.log_mul (by norm_num : (4:ℝ) ≠ 0) hρpos.ne']
    linarith
  refine ⟨hρpos,hlog.trans ?_⟩
  have hb' := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ 4*Real.log 2 by positivity)
  have hw' := mul_le_mul_of_nonneg_left hw (show 0 ≤ 2*δ by positivity)
  change C ≤ 4*Real.log 2/(1-p)*w+4*δ*D*ρ/(1-p)
  dsimp only [C]
  calc
    _ ≤ 4*Real.log 2*(w/(1-p))+2*δ*(2*D*ρ/(1-p)) := add_le_add hb' hw'
    _ = _ := by ring

end TP3
