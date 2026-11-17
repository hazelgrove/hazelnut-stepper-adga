# Agda mechanization

Mechanization of the stepper's core calculus, following the notation and
conventions of the earlier `hazelnut-stepper-agda` development: de Bruijn
indices, `ƛ_`/`` `_ ``/`φ`/`δ`/`μ`, `$e`/`$v`, and `M-*` rule names.

A pattern lambda has a *pattern* body, so `$e` and `$v` can appear under a
binder. The value wildcard `$v` matches only values, ignoring filter and
residue wrappers; it
does not match variables, including parameters in a function body. Matching
needs no binder context: de Bruijn indices retain alpha-equivalence for
structural variable patterns.

Decomposition threads a `State` record with fields `act`, `act-lvl`,
`ins-lvl`, and `ctx`. The filter stack `Φ` stays separate, and
`lookup : Filters → Exp → State → State` updates this state when searching
the filters. The record carries no proof obligations or restrictions on
its fields; `bump` and `keep` remain separate helpers.
`bump` compares two action-priority pairs and keeps the first pair when
their priorities are equal.
Decomposition rules and their metatheorems quantify over states directly,
using field projections and record updates as the traversal descends.

| Module         | Contents                                                        |
|----------------|-----------------------------------------------------------------|
| `Base`         | Syntax of expressions, patterns, filters, residues; values      |
| `Substitution` | Shifting, `patternize`, substitution, `applyₑ`                 |
| `Ctx`          | Evaluation contexts, read hole-first; `compose`                 |
| `Match`        | `strip`, `strip-δ`, `p matches e`, matching decision             |
| `Decompose`    | `State`, `lookup`; `(Φ , s) ⊢ e ⇛ C′ ⟨ r ⟩ ⊣ t`                 |
| `Recompose`    | `C ⟨ r ⟩` recomposes to the expression, up to residues          |
| `Transition`   | `e —→ e′`, the paper's T rules; none for a mismatched operand   |
| `Step`         | `e ⇥ e′`, the paper's S rules: skip silently, then one step     |
| `Statics`      | Types; `Γ ⊢[ e ]∶ τ` and `Γ ⊢< p >∶ τ`, as in the appendix      |
| `Progress`     | well-typed closed: a value or decomposes, and the redex steps   |
| `Preservation` | a run keeps the type of a well-typed closed program             |
| `Simulation`   | a step, stripped, is steps of evaluation ignoring filters       |
| `Patternize`   | `patternize e₁ matches e₂ ⇔ strip e₁ ≡ strip e₂`                |

Check everything with:

```sh
agda --safe All.agda
```

Tested with Agda 2.6.4.1 and agda-stdlib 2.0.
