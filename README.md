## Propositions as Types

Currently, the working part of the project is that on lambda calculus and simple type theory. The logic part needs to be updated (it used to work).

Lambda-calculus.agda defines lambda terms (currently `var`, `lam`, and `app`) and substitution, the reduction relations and beta-equivalence, normal and strongly normalising terms, and it contains:
1. inverses to one step reduction rules,
2. a proof of the Church-Rosser diamond property,
3. an exact enumeration of one step reductions from a given term,
4. the decidability of beta-equivalence for strongly normalising terms.

simpleTT.agda defines types, typing judgements, context morphisms (=typed  renaming of variables, not sure why I picked this name) and typed substitutions, and it proves:
1. admissibility of weakening and substitution,
2. subject reduction and progress,
3. strong normalisation for typed terms, via Girard's reducibility candidates,
4. consistency.

The other files contain auxiliary material for the metatheory.
