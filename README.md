# On the Ramsey number of a tight path of length 3 versus a clique

This repository contains a Lean 4 and Mathlib formalization of the main theorem of
*On the Ramsey number of a tight path of length 3 versus a clique*, by
Abhishek Dhawan and Abhishek Methuku. The proved declaration is `TP3.ramsey_bound`.

## Abstract

Let $r(P_s,t)$ denote the Ramsey number of the 3-uniform tight path with
$s$ edges versus a clique on $t$ vertices. Results of Phelps and Rödl give
$r(P_2,t)=\Theta(t^2/\log t)$. In 2013, Cooper and Mubayi proved that
$r(P_s,t)=\Theta(t^2)$ for every fixed $s\ge4$. For the remaining case
$s=3$, they asked for the order of $r(P_3,t)$, a question later reiterated
by Bohman, Mubayi and Picollelli. Together, these results give a lower bound
of $\Omega(t^2/\log t)$ and an upper bound of $O(t^2)$ for $r(P_3,t)$.
We improve the upper bound to $O(t^2/\log\log t)$, making progress towards
a conjecture of Mattheus, Mubayi, Nie and Verstraëte.

## The mathematical statement

**Main theorem.** For the 3-uniform tight path $P$ with three edges,

$$
r(P,t)=O\!\left(\frac{t^2}{\log\log t}\right).
$$

All logarithms in the formalization are natural. The tight path has five distinct
vertices and edges $abc,bcd,cde$; additional edges are allowed. The theorem makes
no regularity or codegree assumption on the input hypergraph.

### Exact Lean statement

```lean
theorem ramsey_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ t₀ : ℕ, 3 ≤ t₀ ∧
      ∀ t : ℕ, t₀ ≤ t →
        ∃ N : ℕ, (N : ℝ) ≤ C * (t : ℝ) ^ 2 / Real.log (Real.log (t : ℝ)) ∧
          ∀ H : Finset (Finset (Fin N)), IsTripleSystem H →
            HasTightPath H ∨
              ∃ S : Finset (Fin N), S.card = t ∧ Independent H S
```

Here `IsTripleSystem H` says every member of `H` has cardinality three,
`HasTightPath H` specifies the five distinct vertices and three required edges,
and `Independent H S` says that no edge of `H` is contained in `S`.
Regard `H` as the red triples and its complement as the blue triples. The statement
then gives exactly the claimed Ramsey upper bound, with constants independent of
the coloring and an independent set of exactly $t$ vertices.

[`Challenge.lean`](Challenge.lean) states this target independently.
[`Solution.lean`](Solution.lean) imports the unconditional proof in
[`TP3/MainRamsey.lean`](TP3/MainRamsey.lean). The Challenge's deliberate placeholder
is excluded from the proof dependency closure. There are no proof holes or extra
axioms in the Solution. The optimal conjectured order $t^2/\log t$ and historical
lower bounds are not claimed as formalized results here.

## Proof structure

The proof first obtains an induced hypergraph with independent pair
neighbourhoods and controlled degree. A second random choice gives an independent
set larger than the elementary square-root bound. The main formal steps are:

| Step | Entry point | Result |
| --- | --- | --- |
| Structure | [`Structure`](TP3/Structure.lean), [`GeneralDegree`](TP3/GeneralDegree.lean) | Private pairs at high codegree, disjoint pair neighbourhoods, and maximum degree at most $3n$ |
| Blocks and lists | [`GraphPeeling`](TP3/GraphPeeling.lean), [`MediumPairLists`](TP3/MediumPairLists.lean), [`ReducedFCount`](TP3/ReducedFCount.lean) | Construct the block occurrences, prove incidence bounds, and count the forbidden configurations |
| Dependent sampling | [`SamplingLemma`](TP3/SamplingLemma.lean), [`PointwiseSampling`](TP3/PointwiseSampling.lean) | Prove the joint inclusion bounds, including every shared-mark correction, for the actual sequential law |
| Extraction | [`ExtractionTheorem`](TP3/ExtractionTheorem.lean) | Retain at least $kn/(2x)$ vertices, degree at most $100k^2$, and independent pair neighbourhoods when the original degree is at most $x^2$ |
| Conditional averaging | [`AveragedDensity`](TP3/AveragedDensity.lean) | Derive the averaged density inequality from the random pair restrictions and conditional uniform choices |
| Independent set | [`StructuredIndependence`](TP3/StructuredIndependence.lean), [`VertexRestriction`](TP3/VertexRestriction.lean) | Obtain the structured independent-set bound and apply it on the extracted vertex type |
| Final bound | [`MainIndependence`](TP3/MainIndependence.lean), [`RamseyReduction`](TP3/RamseyReduction.lean) | Prove $\alpha(H)\ge \sqrt{n\log\log n}/480000$ for sufficiently large $n$, then convert it to the Ramsey statement |

The final theorem has no assumed extraction lemma, averaged inequality, or
independence bound. These intermediate statements are proved in this repository.

### Implementation details and fidelity

The finite class experiment uses independent Bernoulli trials in place of
continuous uniform vertex numbers. If $m=bR$ and $\varphi=q\tau^m$, an eligible
vertex requiring $l$ shared marks additionally requires its independent $q$ trial
and $m-l$ independent $\tau$ trials. Joint probabilities, including shared marks,
are proved for this experiment; they are not deduced from marginal probabilities.

Conflict deletion chooses one fixed endpoint per conflicting pair. The proof
uses the larger conflict-loss constants $3$ and $162$ and checks their numerical
specialization. Dense blocks are indexed by occurrences with disjoint charged
edge sets, so repeated vertex sets are counted with their multiplicities.
The general degree bound used is the sufficient estimate $\Delta(H)\le3n$.
The final integer scale is maximal subject to $\exp(k^{60})\le x$, where
$x=\sqrt{3n}$. Its next threshold bounds $\log\log n$ by $144\log k$.
These choices change constants and thresholds, not the theorem's hypotheses or
asymptotic conclusion.

## Building and verification

The project uses Lean `v4.35.0` and Mathlib pinned in
[`lake-manifest.json`](lake-manifest.json). With Git and Elan installed:

```bash
git clone https://github.com/methuku-git-hub/tp3-ramsey-lean.git
cd tp3-ramsey-lean
lake exe cache get
lake build TP3 +Challenge:olean +Solution:olean +AxiomAudit:olean
lake comparator --config comparator.json
```

The [local Comparator run](verification/comparator-main.log) matched the exact
Challenge and Solution theorem and accepted the exported proof with Lean's kernel
and NanoDa. The [axiom audit](verification/main-theorem-probe.log) records only
`propext`, `Classical.choice`, and `Quot.sound` for the main theorem. The complete
development audit checked all 838 exported `TP3` declarations.

The local macOS Comparator invocation used `--inadvisably-no-sandbox` because
Bubblewrap is unavailable there. This local run is separate from Palomar's
required Linux mechanical preflight. Neither a local pass nor preflight is a
claim of registry acceptance or independent human review.

## Sources and attribution

The mathematical source is the main theorem, labelled `thm:ramsey`, in the
25 November 2026 manuscript by Abhishek Dhawan and Abhishek Methuku. Its LaTeX
source SHA-256 is
`efebeaa7f3753f411d1eb1ab11b543e474b5f13e00a447edc103f03db0a20024`.
The manuscript is unchanged by this formalization task.

The initial generic finite-law infrastructure in
[`TP3/FiniteProbability.lean`](TP3/FiniteProbability.lean) was adapted from the
[locally Ramsey project](https://github.com/methuku-git-hub/locally-ramsey-lean).
The reused source had SHA-256
`77b70967a9c2bec0bb1ff4953b1e7287433078aa0d71ff151fb60bb9538c2403`.
There is no path dependency on that project.

Abhishek Methuku is the formalization author and responsible maintainer.
OpenAI Codex developed and checked the Lean proofs under his direction.
No independent human review of the formalization is claimed.

## License

The repository uses [Apache 2.0](LICENSE), following the author's other Lean
formalization repositories. See [`formalization.yaml`](formalization.yaml) for
provenance, automation and scope, and [`comparator.json`](comparator.json) for
the comparison target.
