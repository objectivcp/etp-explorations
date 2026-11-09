# Attribute exploration of ETP laws

Results of attribute exploration, a method of formal concept analysis, on families of laws of the [Equational Theories Project](https://github.com/teorth/equational_theories) (ETP). For each family, the exploration decides which implications between sets of its laws hold. An implication can have several premises and several conclusions, for example `E28, E43 => E2`. The exploration gives two things:

- **Rules.** Every implication that holds follows from these. The rules are proved in Lean.
- **Magmas.** Every implication that does not follow from the rules fails in one of these magmas. Each magma's facts are proved in Lean.

Laws are numbered and written as in the ETP. Numbers above 4694 follow the ETP's scheme (`scripts/find_equation_id.py`). The code that ran the explorations, and checks these results, is in [conceptual-exploration](https://github.com/objectivcp/conceptual-exploration).

## Case studies

| Case study | Laws | Assumed | Rules | New to the ETP | Magmas |
|---|---|---|---|---|---|
| `Order2` | 24 | — | 69 | 49 | 30 |
| `OneVariable` | 31 | — | 99 | 92 | 1,672 finite, 3,858 free |
| `Semigroup4` | 248 | associativity (E4512) | 621 | 349 | 77 |
| `CommutativeSemigroup5` | 160 | associativity, commutativity (E4512, E43) | 201 | 190 | 17 |
| `Semigroup5` | 388 | associativity (E4512) | 1,701 | 1,607 | 216 |

Rules are counted with their duals.

- **`Order2`:** laws of order at most 2. Equivalent laws are grouped into classes, and one law per class is kept. The set is closed under duality.
- **`OneVariable`:** all one-variable laws of order at most 4.
- **`Semigroup4`:** laws of order at most 4, up to equivalence for semigroups. The set has three parts:
  - the first law of each ETP class of the 653 right-associated laws;
  - their reversals;
  - associativity.
- **`CommutativeSemigroup5`:** laws of order at most 5 in commutative form.
  - Order at most 4: one law per class of laws equivalent for commutative semigroups, the classes coming from `Semigroup4`.
  - Order 5: all of them.
- **`Semigroup5`:** one law from each of the 380 classes of the 3,284 semigroup laws of order at most 5. The set is closed under reversal.

The order of a law is its number of operations.

**When a law is assumed,** the implications are about the magmas that satisfy it. So the rules of the semigroup case studies hold in all semigroups, and their magmas are semigroups. Under associativity, the dual of a law is its reversal.

**For `CommutativeSemigroup5`,** every law is equivalent to its dual, so its rules come without duals.

## Contents

```
data/<case study>/
  laws.txt              the laws: "N: law"
  implications.txt      the rules, one per line
  implications.json     the same, as {name, premise, conclusion, source, origin, new}
  magmas.txt            the magmas: Table, Satisfies, Refutes
  free_magmas.json      OneVariable and CommutativeSemigroup5 only
ExplorationLaws.lean    the 2,630 laws the ETP does not declare: equation N := ...
<CaseStudy>.lean, <CaseStudy>/
                        one Lean library per case study, in its own namespace
lakefile.toml           the ETP as a dependency, at commit 1aec8a7
```

## The rules

The rules form the canonical basis relative to the background, simplified. The background is closed under duality, and the basis is given up to duality.

- **Premises:** each premise is cut to the laws that the rest of it does not entail.
- **Conclusions:** each conclusion is cut to the laws that do not follow from the background, the other rules and their duals.

**Format.** Each rule is followed by its dual, unless the dual coincides with it:

```
[B3] E3: x = x ◇ x => E23: x = (x ◇ x) ◇ x   (background: ETP)
[B3^op] E3: x = x ◇ x => E8: x = x ◇ (x ◇ x)   (dual of B3)
[19] E28: x = (y ◇ x) ◇ x, E43: x ◇ y = y ◇ x => E2: x = y   (proved, new)
[19^op] E9: x = x ◇ (x ◇ y), E43: x ◇ y = y ◇ x => E2: x = y   (dual of 19, new)
```

**Background rules** were given to the exploration from the start. Each is labelled with its origin:

| Label | Case studies | Origin |
|---|---|---|
| `ETP` | `Order2`, `Semigroup4` | the ETP's implications between two laws |
| `equational reasoning` | `OneVariable` | derivations through laws of bounded order |
| `Semigroup4` | `CommutativeSemigroup5`, `Semigroup5` | the result of `Semigroup4` |

**`and reversal`** is added when a background rule also needs the reversals of these implications. The background is closed under the duality, which for semigroups is reversal. For example, the ETP has `E10 => E3322` (`x = xyx` gives `xy = xyzy`). Reversing it gives `E10 => E3326` (`xy = xzxy`), which holds in semigroups but not in all magmas. So `Semigroup4` has:

```
[B5] E10: … => E8: …, E432: …, E3326: …, E4269: …   (background: ETP and reversal)
```

The Lean files prove the background rules like all the other rules.

**`new`** marks a rule that the ETP's implications do not give. That is, some law of its conclusion does not follow from any single law of its premise, nor from an assumed law, by chains of the ETP's implications and their duals (reversals, for semigroups). The chains can pass through any ETP law, not just the explored ones.

- **Several premises.** The ETP studies implications from one law, so rules with several premises are usually new.
- **Semigroups.** Associativity counts as a premise of every rule. So does commutativity in `CommutativeSemigroup5`.
- **Proved rules need not be new.** Nine proved rules of `Semigroup4` follow from ETP implications chained through laws outside the exploration, which its background did not include.

## Lean

```
lake exe cache get
lake build Order2 OneVariable Semigroup4 CommutativeSemigroup5
lake build Semigroup5
```

**Files in each library:**

| File | Contents |
|---|---|
| `Implications*.lean` | One theorem per implication with a single law as its conclusion, for example `Equation434_4512_implies_Equation437`. The proofs are chains of `rw`, made from Vampire's proofs, without automation. |
| `MagmaTables.lean`, `SemigroupTables.lean` | The magmas, as `finOpTable`. |
| `Magmas*.lean`, `Semigroups*.lean` | Their `Facts`, by `decideFin!`. Each lists the refuted laws, and enough satisfied laws for the implications to give the rest. |
| `SemigroupParts*.lean` | The laws satisfied in the larger semigroups, proved one value of the first variable at a time. |

**The rules and the Lean files.** The implications in the Lean files entail all the rules. Together with the facts, they give exactly the result: for every set of laws, the laws it implies are those satisfied in every magma that satisfies it.

That the Lean statements give exactly the result is checked by `verify.py --lean` in conceptual-exploration.

**Axioms:**
- The implication theorems use no axioms.
- The facts use `propext`, `Classical.choice` and `Quot.sound`.
- Nothing uses `sorryAx`, `Lean.ofReduceBool` or `Lean.trustCompiler`.

**Build cost.** `Semigroup5` takes far longer to build than the other four libraries together, most of it in `SemigroupParts*`. These decide, in parts, the laws of the larger semigroups that are too costly to decide at once. Lake runs one Lean process per core, and each may need up to about 5 GB of memory. With less memory, build those modules a few at a time, such as `lake build Semigroup5.SemigroupParts0 Semigroup5.SemigroupParts1`.

## Free magmas

**`OneVariable`.** Besides the finite magmas, the exploration used 3,858 infinite ones: the free magmas over the premises of its questions. The finite magmas alone do not refute every implication that fails.

- Each free magma is listed in `free_magmas.json` with its premise, its row and a convergent rewrite system. A law holds in the free magma if and only if its two sides have the same normal form.
- These rows are not in Lean.

**`CommutativeSemigroup5`.** The exploration used one infinite magma: the free commutative semigroup satisfying E53858. In its place, the magmas include a finite stand-in with the same row on all 160 laws:

- It is the free object of that variety on two generators, truncated: the monomials of degree at most 3 with no cube, plus a zero, 8 elements in all.
- It is in Lean like the other magmas.

## License

[Apache 2.0](LICENSE), as the ETP.
