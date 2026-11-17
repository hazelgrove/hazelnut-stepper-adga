# Filtered Stepper Calculus — Agda Mechanization

This repository contains the Agda mechanization of the *Filtered Stepper
Calculus* described in the paper *Practical Algebraic Stepping with Scoped
Filters*. The calculus extends the simply-typed lambda calculus with natural
numbers, addition, and a fixpoint operator with two new expression forms — a
user-written `filter` and an internal `residue` — that together let the
stepper hide or show small-step reductions based on lightweight pattern
matching.

## Requirements

The development has been checked with the following versions.

- **Agda 2.6.4.1**
- **agda-stdlib 2.0**

## Checking the development

From the repository root, run

```sh
agda --safe All.agda
```

`All.agda` imports every module listed below. To check an individual proof
and its dependencies, replace `All.agda` with its module filename.

## Repository layout

| File | Contents |
|---|---|
| `Base.agda` | Expressions, patterns, filters, residues, and the value judgment. |
| `Substitution.agda` | Shifting, substitution, and the coercion `patternize` from expressions to patterns. |
| `Match.agda` | Stripping filters and residues, structural pattern matching, and its decision procedure. |
| `Ctx.agda` | Evaluation contexts and the function `compose` that fills the hole. |
| `Decompose.agda` | Filter lookup and decomposition into a candidate redex and its context, with an action and level. |
| `Recompose.agda` | Filling a candidate context with its redex recovers the input up to residues. |
| `Transition.agda` | Reduction of a redex. |
| `Step.agda` | The initial state `top` and the filtered stepping judgment. |
| `Statics.agda` | Types and typing judgments for expressions and patterns. |
| `Preservation.agda` | Type preservation for filtered steps. |
| `Progress.agda` | Decomposition progress, finality of values, and transition progress. |
| `Simulation.agda` | The unfiltered step relation and simulation of filtered steps. |
| `Patternize.agda` | A pattern obtained by `patternize` matches exactly those expressions equal to its source after stripping. |
| `All.agda` | Entry point for checking the full development. |

## Theorems

| Paper | Statement | Agda name | Location |
|---|---|---|---|
| Preservation | If `∅ ⊢ e : τ` and `e ⇥ e′`, then `∅ ⊢ e′ : τ`. | `⇥-preserve` | [Preservation.agda](Preservation.agda#L191) |
| Decomposition Progress | A well-typed closed expression is a value or admits a decomposition. Values admit no decomposition. | `progress`, `value-final` | [Progress.agda](Progress.agda#L21) |
| Transition Progress | Every redex obtained by decomposing a well-typed closed expression admits a transition. | `⇛-progress` | [Progress.agda](Progress.agda#L55) |
| Simulation | If `e ⇥ e′`, then `strip e ↦* strip e′`. | `sim` | [Simulation.agda](Simulation.agda#L188) |

## Notation: paper → Agda

| Paper | Agda |
|---|---|
| Lambda abstraction `λx.e` | `ƛ e` (de Bruijn) |
| Application `e₁(e₂)` | `` e₁ `· e₂ `` |
| Natural literal `n` | `# n` |
| Addition `e₁ + e₂` | `` e₁ `+ e₂ `` |
| Fixpoint `μx.e` | `μ e` (de Bruijn) |
| Filter `debug f in e` | `φ f e` where `f : Filter = Pat × Act × Gas` |
| Residue with action `a` and level `l` around `e` | `δ (a , l) e` |
| Action `step` / `skip` | `∥` / `⊳` |
| Gas `one` / `all` | `𝟙` / `⋆` |
| Pattern wildcards `$e` / `$v` | `$e` / `$v` |
| State `(a, lₐ, lᵣ, E)` | `state a lₐ lᵣ C` |
| Action selection `lookup(Φ, e, s)` | `lookup Φ e s` |
| Context–redex pair `E{r}` | `C ⟨ r ⟩` |
| Decomposition | `(Φ , s) ⊢ e ⇛ C ⟨ r ⟩ ⊣ t` |
| Filling a context `E[e]` | `compose C e` |
| Instruction transition | `e —→ e′` |
| Filtered step | `e ⇥ e′` |
| Unfiltered step and its reflexive–transitive closure | `e ↦ e′` and `e ↦* e′` |
| Typing | `Γ ⊢[ e ]∶ τ` (expressions) and `Γ ⊢< p >∶ τ` (patterns) |

## A note on representation

The development uses **de Bruijn indices** for both expressions and
patterns, so matching under a binder handles α-equivalence directly.
The wildcard `$v` follows the same value judgment inside a binder body
as elsewhere. The substitution functions `applyₑ` and `applyₚ` remove
the substituted binder as they traverse an expression or pattern.
