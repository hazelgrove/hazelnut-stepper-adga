# Filtered Stepper Calculus — Agda Mechanization

This repository contains the Agda mechanization of the *Filtered Stepper
Calculus* described in the paper *Practical Algebraic Stepping with Scoped
Filters*. The calculus extends the simply-typed lambda calculus with natural
numbers, addition, and a fixpoint operator with two new expression forms — a
user-written `filter` and an internal `residue` — that together let the
stepper hide or show small-step reductions based on lightweight pattern
matching.

## Requirements

We have tested against:

- **Agda 2.6.4.3**
- **agda-stdlib 2.1**

Other recent Agda versions should also work; nothing here is version-specific.

## Checking the development

From the repository root, run:

```
agda Progress.agda
agda Preservation.agda
agda Simulation.agda
agda Determinism.agda
```

Each invocation type-checks the corresponding module and all of its
dependencies. There are no holes, no postulates, and no `--rewriting`
extensions; a clean exit code means every theorem stated below has been
fully verified.

## Repository layout

| File | Contents |
|---|---|
| `Base.agda` | Syntax of expressions, patterns, values, actions (`⊳` for *step*, `∥` for *skip*), gases (`𝟙` for *one*, `⋆` for *all*), and the `value?` decision procedure. |
| `Substitution.agda` | Variable insertion/shifting, capture-avoiding substitution `applyₑ`, and the `patternize` coercion from expressions to patterns. |
| `Match.agda` | The `strip` operation and the structural pattern-matching judgment `_matches_`, with its decision procedure. Uses de Bruijn indices, so `α`-equivalence is built in. |
| `Statics.agda` | Type grammar (`` `ℕ ``, `_`→_`) and typing judgments for expressions (`_⊢[_]∶_`), patterns (`_⊢<_>∶_`), and evaluation contexts (`_⊢⟨_⟩∶_`). |
| `Dynamics.agda` | Evaluation contexts `Ctx`, the instruction transition `_—→_`, decomposition `_⇒_`, composition `_⇐_`, action selection `_⊢_⊣_`, instrumentation `_⊢_⇝_`, optimization `_⇴_`, the `decay` function, and finally the filtered stepping relation `_⊢_⇥_` (and the underlying unfiltered step `_↦_`, with reflexive–transitive closure `_↦*_`). |
| `Preservation.agda` | Preservation for the filtered stepping relation. |
| `Progress.agda` | Progress for the underlying step relation, and single-iteration progress for the filtered stepping pipeline. |
| `Simulation.agda` | The similarity relation `_∼_` and the simulation theorem: every filtered step is simulated by a multi-step trace in the underlying calculus. |
| `Determinism.agda` | Determinism of instrumentation, decomposition, composition, optimization, instruction transition, and filtered stepping. |
| `Eq.agda` | Decidable equality of expressions, used by the matching decision procedure. |

## Theorems

The paper's metatheoretic results map to the following names in the
development:

| Paper | Statement | Agda name | Location |
|---|---|---|---|
| Theorem 1 (Preservation) | If `Γ ⊢ e : τ` and `e ⇥ e′`, then `Γ ⊢ e′ : τ`. | `preserve` | `Preservation.agda:206` |
| Theorem 2 (Progress) | If `∅ ⊢ e : τ`, then `e` is a value or `∃ e′. e ↦ e′`. | `↦-progress` | `Progress.agda:136` |
| Theorem 3 (Simulation) | If `e ⇥ e′`, then `strip e ↦* strip e′`. | `sim` | `Simulation.agda:239` |
| Theorem 4 (Single-Iteration Progress) | If `∅ ⊢ e : τ`, then `e` is a value or one full filtered pipeline iteration exists. | `filter-iteration` | `Progress.agda:184` |

The simulation theorem is stated in terms of a similarity relation `_∼_`
(`Simulation.agda:14`) and packaged as a `Leg` (`Simulation.agda:150`)
witnessing both the similarity of the targets and the multi-step trace; the
strip-based formulation in the paper follows by `strip-∼` and `∼-strip`.

In addition, `Determinism.agda` proves determinism of every intermediate
relation used by the stepper (`⇝`, `⇒`, `⇐`, `⇴`, `→`, and `⇥`).

## Notation: paper → Agda

| Paper | Agda |
|---|---|
| Lambda abstraction `λx.e` | `ƛ e` (de Bruijn) |
| Application `e₁(e₂)` | `e₁ `· e₂` |
| Natural literal `n` | `# n` |
| Addition `e₁ + e₂` | `e₁ `+ e₂` |
| Fixpoint `μx.e` | `μ e` (de Bruijn) |
| Filter `debug f in e` | `φ f e` where `f : Filter = Pat × Act × Gas` |
| Residue ⟨r⟩ e | `δ r e` where `r : Residue = Act × Gas × ℕ` |
| Action `step` / `skip` | `∥` / `⊳` |
| Gas `one` / `all` | `𝟙` / `⋆` |
| Pattern wildcards `$e` / `$v` | `$e` / `$v` |
| `Strip(e)` | `strip e` |
| `Decay(𝓔)` | `decay ε` |
| Instrumentation `(p,a,g,l) ⊢ e ↝ e′` | `(p , a , g , l) ⊢ e ⇝ e′` |
| Optimization `e ↝_opt e′` | `e ⇴ e′` |
| Decomposition `e ⇒ 𝓔{e₀}` | `e ⇒ ε ⟨ e₀ ⟩` |
| Composition `e ⇐ 𝓔{e₀}` | `e ⇐ ε ⟨ e₀ ⟩` |
| Action selection `(a,l) ⊢ 𝓔 ⊣ a′` | `(a , l) ⊢ ε ⊣ a′` |
| Instruction transition `e → e′` | `e —→ e′` |
| Filtered step `e ⇉ⁿ e′` | `(p , a , g , l) ⊢ e ⇥ e′` |
| Underlying step `e ↦ e′` | `e ↦ e′` |
| Multi-step `e ↦* e′` | `e ↦* e′` |
| Typing `Γ ⊢ e : τ` | `Γ ⊢[ e ]∶ τ` (expressions) / `Γ ⊢< p >∶ τ` (patterns) |

## A note on representation

The development uses **de Bruijn indices** throughout. As a result,
`α`-equivalence holds definitionally: the pattern-matching rule `M-Lam` in
the paper (`λx₁.e₁ ▷ λx₂.e₂` when `strip e₁ ≡ strip e₂`) is implemented in
Agda as `(ƛ eₚ) matches (ƛ eₑ) when strip eₚ ≡ strip eₑ`, with no separate
α-conversion. Substitution and pattern coercion are fused into the single
function `applyₑ`/`applyₚ` to avoid intermediate ill-formed states (e.g.,
shifting down a free variable). Termination of `instr` and `optimize` is
established by well-founded recursion on expression size.
