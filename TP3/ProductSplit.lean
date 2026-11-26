module

public import TP3.Conditioning
public import Mathlib.Logic.Equiv.Prod

@[expose] public section

namespace TP3.FiniteLaw

attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]

/-- Split independent coordinates into two groups. This identity is
used to expose the decisions at one vertex separately from the remaining
vertex and pair decisions, with no conditioning on their outcomes. -/
theorem product_split_mean (μ : ι → FiniteLaw β) (P : ι → Prop) [DecidablePred P]
    (F : (ι → β) → ℝ) :
    (product μ).mean F =
      ((product fun i : {i // P i} => μ i).staged
        (fun _ => product fun i : {i // ¬ P i} => μ i)).mean
        (fun ω => F ((Equiv.piEquivPiSubtypeProd P (fun _ => β)).symm ω)) := by
  let e := Equiv.piEquivPiSubtypeProd P (fun _ => β)
  unfold mean
  apply Fintype.sum_equiv e
  intro ω
  have hprob : (product μ).prob ω =
      ((product fun i : {i // P i} => μ i).staged
        (fun _ => product fun i : {i // ¬ P i} => μ i)).prob (e ω) := by
    change (∏ i, (μ i).prob (ω i)) =
      (∏ i : {i // P i}, (μ i).prob (ω i)) * ∏ i : {i // ¬ P i}, (μ i).prob (ω i)
    exact (Fintype.prod_subtype_mul_prod_subtype P (fun i => (μ i).prob (ω i))).symm
  rw [hprob]
  congr 1
  exact congrArg F (e.symm_apply_apply ω).symm

/-- If F depends only on the second group and G only on the first,
their weighted expectations factor exactly. -/
theorem product_disjoint_mean (μ : ι → FiniteLaw β) (P : ι → Prop) [DecidablePred P]
    (F G : (ι → β) → ℝ)
    (hF : ∀ ω ω', (∀ i, ¬ P i → ω i=ω' i) → F ω=F ω')
    (hG : ∀ ω ω', (∀ i, P i → ω i=ω' i) → G ω=G ω') :
    (product μ).mean (fun ω => F ω*G ω) = (product μ).mean F*(product μ).mean G := by
  obtain ⟨ω₀,_⟩ := (product μ).exists_positive_mass
  let e := Equiv.piEquivPiSubtypeProd P (fun _ => β)
  let A := product fun i : {i // P i} => μ i
  let B := product fun i : {i // ¬ P i} => μ i
  let f := fun b => F (e.symm ((e ω₀).1,b))
  let g := fun a => G (e.symm (a,(e ω₀).2))
  have hf (a) (b) : F (e.symm (a,b))=f b := by
    apply hF
    intro i hi
    simp [e,Equiv.piEquivPiSubtypeProd,hi]
  have hg (a) (b) : G (e.symm (a,b))=g a := by
    apply hG
    intro i hi
    simp [e,Equiv.piEquivPiSubtypeProd,hi]
  rw [product_split_mean μ P,product_split_mean μ P F,product_split_mean μ P G]
  change (A.staged (fun _ => B)).mean (fun ω => F (e.symm ω)*G (e.symm ω)) =
    (A.staged (fun _ => B)).mean (fun ω => F (e.symm ω)) *
      (A.staged (fun _ => B)).mean (fun ω => G (e.symm ω))
  simp_rw [staged_mean,hf,hg]
  have hfg (a) : B.mean (fun b => f b*g a) = g a*B.mean f := by
    simpa only [mul_comm] using B.mean_mul_const (g a) f
  simp_rw [hfg,B.mean_const,A.mean_const]
  simpa only [mul_comm] using A.mean_mul_const (B.mean f) g

end TP3.FiniteLaw
