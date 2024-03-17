## Propositions as Types

Actually the project currently contains more about lambda calculus and simple type theory than about logic.

**Currently the files IPL-implic-frag.agda and props-as-types.agda do not compile**.

Currently only the implicational fragment is considered.

Lambda-calculus.agda defines lambda terms (currently `var`, `lam`, and `app`) and substitution, the reducibility relations, normal and stringly normalising terms, and it contains:
1. inverses to one step reduction rules,
2. a proof of the Church-Rosser diamond property,
3. an exact enumeration of one step reductions from a given term,
4. the decidability of beta-equivalence for strongly normalising terms.

simpleTT.agda defines types, typing judgements, context morphisms (=typed  renaming of variables, not sure why I picked this name) and typed substitutions,
and it proves:
1. admissibility of weakening and substitution,
2. subject reduction and progress,
3. strong normalisation for typed terms, via reducibility candidates as in Girard's "Proofs and types",
4. consistency.

The other files contain auxiliary material for the metatheory.
