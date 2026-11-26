# Open order-3 questions

Implications between laws of order at most 3 that attribute exploration could not decide. The exploration covers 149 laws, which represent the 146 ETP classes of laws of order at most 3: one law per class, and both a law and its dual for the three classes that contain the duals of their laws but no law equal to its own dual (E14 and E29, E66 and E281, E332 and E387). The list comes from its fourth run, in reject mode, seeded with what the first three found: a question that the provers and model finders could not decide was rejected tentatively, and the run went on without assuming the implication.

74 questions in all, 39 up to duality, the dual of each listed question being open too. Each is listed with a minimal premise; the premise's other laws follow from it. 30 have in their premise, or imply, a law that needed a dedicated construction in the ETP, or its dual; the headings name them. Laws are numbered and written as in the ETP.

Together with the proved implications, the listed questions give every open implication. Those with a single law as conclusion, 2,870 in all (1,436 up to duality), have 155 different premises (80 up to duality) once closed under the proved implications. [`order3_open_implications.md`](order3_open_implications.md) lists each of these premises, up to duality, with all its open laws, and [`order3_open_implications.json`](order3_open_implications.json) lists all of them. The run asked each of these implications with its closed premise; 193 more that it left open fail in finite magmas found after it. Refuting a question here can bring in weaker ones that it gave, while that list only shrinks as implications are proved or refuted. So the number of theories, the sets of these laws that are exactly the laws some magma satisfies, is at least 3,712, the sets closed under the proved implications in which every other law fails in a known magma satisfying the set, and at most 3,867, all the sets closed under the proved implications.

Tried on every question, for each law r of the conclusion, without a proof or a countermodel, the exploration's expert, with the premise closed under the proved implications: Vampire 10 s to prove r and 60 s for a model violating it, E 2 s and Prover9 5 s to prove r, and Mace4 120 s for a model violating a law of the question's conclusion.

On the laws not marked *new* (32 questions without a new law), also:

- Mace4 on the premise and not r, sizes 2 to 24, 300 s (marked **24** where it exhausted all sizes);
- Vampire 5.1.0 `--mode casc`, 60 s on 8 cores (not on the laws of 4 questions new to the second or third run); E 3.2.5 and Prover9, 120 s each;
- Knuth–Bendix completion of the premise, 120 s, on most of them (it failed on all);
- linear and affine models x◇y = ax + by + c mod n, n ≤ 100;
- Vampire `--mode casc` 600 s, Vampire `--schedule casc_sat` 300 s and E `--auto-schedule` 300 s, one core each.

Then on every question, for each law r of the conclusion, with the premise closed under the proved implications, one core each: Vampire `--mode casc` 1 h, Mace4 1 h on sizes 2 to 100 (from 25 where it had exhausted sizes 2 to 24; marked **100** where it exhausted all sizes), E `--auto-schedule` 30 min and Vampire `--schedule casc_sat` 30 min. Mace4 found a magma of size 25 satisfying exactly the laws that E75, E167 and E264 imply, which settled one more question. Knuth–Bendix completion, with the Knuth–Bendix order and two lexicographic path orders, 600 s each, then completed none of the 157 premises with an open law.

A second run of the same exploration, on a server with 32 cores, asked the same questions and proved the same implications. Its model searches found a magma of size 16 satisfying exactly the laws that E222 and E280 imply, where this run had found none. This settled one more question; weaker questions that it gave are listed in its place. The searches of the previous paragraph, run on these too, found nothing.

Then Mace4, 1 h on sizes 2 to 100, on each of the other 41 premises up to duality of [`order3_open_implications.md`](order3_open_implications.md), those of no question, for each of its open laws that the premise and its other open laws do not imply, 46 searches in all: a magma of the premise that violates an open law violates one of these. It found nothing, and exhausted all sizes in 6 of the searches, marked **100** there.

The proved implications and the finite magmas are in Lean, in the library `Order3` of etp-explorations. The refutations that need a free magma or a refutation in the ETP are not: they are certified by rewrite systems or come from the ETP.


## Premise implies E65 (Asterix), or its dual E261

1. E48: `x = x ◇ (x ◇ (x ◇ y))`; E261: `x = ((x ◇ y) ◇ x) ◇ y` ⇒ E102: `x = x ◇ ((x ◇ y) ◇ y)`
2. E49: `x = x ◇ (x ◇ (y ◇ x))`; E65: `x = y ◇ (x ◇ (y ◇ x))` ⇒ E39: `x ◇ x = y ◇ x` **100**
3. E53: `x = x ◇ (y ◇ (x ◇ y))`; E55: `x = x ◇ (y ◇ (y ◇ x))`; E261: `x = ((x ◇ y) ◇ x) ◇ y` ⇒ E159: `x = (x ◇ y) ◇ (y ◇ x)`
4. E53: `x = x ◇ (y ◇ (x ◇ y))`; E206: `x = (x ◇ (x ◇ y)) ◇ y`; E261: `x = ((x ◇ y) ◇ x) ◇ y` ⇒ E4: `x = x ◇ y` *new*
5. E55: `x = x ◇ (y ◇ (y ◇ x))`; E159: `x = (x ◇ y) ◇ (y ◇ x)`; E261: `x = ((x ◇ y) ◇ x) ◇ y` ⇒ E53: `x = x ◇ (y ◇ (x ◇ y))`
6. E65: `x = y ◇ (x ◇ (y ◇ x))`; E124: `x = y ◇ ((y ◇ x) ◇ x)`; E159: `x = (x ◇ y) ◇ (y ◇ x)` ⇒ E5: `x = y ◇ x` **24**
7. E65: `x = y ◇ (x ◇ (y ◇ x))`; E167: `x = (y ◇ x) ◇ (x ◇ y)` ⇒ E26: `x = (x ◇ y) ◇ y`
8. E65: `x = y ◇ (x ◇ (y ◇ x))`; E228: `x = (y ◇ (y ◇ x)) ◇ x` ⇒ E270: `x = ((y ◇ x) ◇ x) ◇ x`
9. E65: `x = y ◇ (x ◇ (y ◇ x))`; E261: `x = ((x ◇ y) ◇ x) ◇ y` ⇒ E43: `x ◇ y = y ◇ x`
10. E65: `x = y ◇ (x ◇ (y ◇ x))`; E264: `x = ((x ◇ y) ◇ y) ◇ y` ⇒ E117: `x = y ◇ ((x ◇ y) ◇ x)`
11. E65: `x = y ◇ (x ◇ (y ◇ x))`; E364: `x ◇ x = (y ◇ x) ◇ x` ⇒ E55: `x = x ◇ (y ◇ (y ◇ x))`
12. E65: `x = y ◇ (x ◇ (y ◇ x))`; E385: `x ◇ y = (y ◇ x) ◇ y` ⇒ E375: `x ◇ y = (x ◇ x) ◇ y` **24**

## Premise implies E118, E124 (greedy constructions), or their duals E229, E206

13. E75: `x = y ◇ (y ◇ (y ◇ x))`; E274: `x = ((y ◇ x) ◇ y) ◇ y`; E280: `x = ((y ◇ y) ◇ x) ◇ x` ⇒ E43: `x ◇ y = y ◇ x` *new*
14. E75: `x = y ◇ (y ◇ (y ◇ x))`; E274: `x = ((y ◇ x) ◇ y) ◇ y`; E375: `x ◇ y = (x ◇ x) ◇ y` ⇒ E43: `x ◇ y = y ◇ x` *new*
15. E101: `x = x ◇ ((x ◇ y) ◇ x)`; E206: `x = (x ◇ (x ◇ y)) ◇ y` ⇒ E4: `x = x ◇ y`
16. E105: `x = x ◇ ((y ◇ x) ◇ y)`; E159: `x = (x ◇ y) ◇ (y ◇ x)`; E206: `x = (x ◇ (x ◇ y)) ◇ y` ⇒ E53: `x = x ◇ (y ◇ (x ◇ y))`
17. E105: `x = x ◇ ((y ◇ x) ◇ y)`; E206: `x = (x ◇ (x ◇ y)) ◇ y`; E209: `x = (x ◇ (y ◇ x)) ◇ y` ⇒ E4: `x = x ◇ y` **24**
18. E118: `x = y ◇ ((x ◇ y) ◇ y)`; E151: `x = (x ◇ x) ◇ (x ◇ x)` ⇒ E222: `x = (y ◇ (x ◇ y)) ◇ y`
19. E118: `x = y ◇ ((x ◇ y) ◇ y)`; E280: `x = ((y ◇ y) ◇ x) ◇ x` ⇒ E222: `x = (y ◇ (x ◇ y)) ◇ y` *new* **100**
20. E124: `x = y ◇ ((y ◇ x) ◇ x)`; E153: `x = (x ◇ x) ◇ (y ◇ x)` ⇒ E10: `x = x ◇ (y ◇ x)` **100**
21. E124: `x = y ◇ ((y ◇ x) ◇ x)`; E167: `x = (y ◇ x) ◇ (x ◇ y)` ⇒ E206: `x = (x ◇ (x ◇ y)) ◇ y`
22. E124: `x = y ◇ ((y ◇ x) ◇ x)`; E385: `x ◇ y = (y ◇ x) ◇ y` ⇒ E10: `x = x ◇ (y ◇ x)`
23. E125: `x = y ◇ ((y ◇ x) ◇ y)`; E283: `x = ((y ◇ y) ◇ y) ◇ x` ⇒ E212: `x = (x ◇ (y ◇ y)) ◇ y` *new*; E264: `x = ((x ◇ y) ◇ y) ◇ y` *new*

## Premise implies E63, E73 (proved by hand), or their duals E271, E274

24. E50: `x = x ◇ (x ◇ (y ◇ y))`; E63: `x = y ◇ (x ◇ (x ◇ y))` ⇒ E53: `x = x ◇ (y ◇ (x ◇ y))`
25. E56: `x = x ◇ (y ◇ (y ◇ y))`; E63: `x = y ◇ (x ◇ (x ◇ y))` ⇒ E26: `x = (x ◇ y) ◇ y`
26. E63: `x = y ◇ (x ◇ (x ◇ y))`; E167: `x = (y ◇ x) ◇ (x ◇ y)` ⇒ E2: `x = y` **24**
27. E63: `x = y ◇ (x ◇ (x ◇ y))`; E271: `x = ((y ◇ x) ◇ x) ◇ y` ⇒ E43: `x ◇ y = y ◇ x`
28. E73: `x = y ◇ (y ◇ (x ◇ y))`; E99: `x = x ◇ ((x ◇ x) ◇ x)` ⇒ E125: `x = y ◇ ((y ◇ x) ◇ y)`
29. E73: `x = y ◇ (y ◇ (x ◇ y))`; E151: `x = (x ◇ x) ◇ (x ◇ x)` ⇒ E125: `x = y ◇ ((y ◇ x) ◇ y)`
30. E73: `x = y ◇ (y ◇ (x ◇ y))`; E203: `x = (x ◇ (x ◇ x)) ◇ x` ⇒ E125: `x = y ◇ ((y ◇ x) ◇ y)`

## Other premises

31. E49: `x = x ◇ (x ◇ (y ◇ x))`; E260: `x = ((x ◇ y) ◇ x) ◇ x` ⇒ E10: `x = x ◇ (y ◇ x)`
32. E55: `x = x ◇ (y ◇ (y ◇ x))`; E102: `x = x ◇ ((x ◇ y) ◇ y)`; E325: `x ◇ y = x ◇ (y ◇ x)` ⇒ E105: `x = x ◇ ((y ◇ x) ◇ y)` *new*
33. E55: `x = x ◇ (y ◇ (y ◇ x))`; E159: `x = (x ◇ y) ◇ (y ◇ x)`; E209: `x = (x ◇ (y ◇ x)) ◇ y` ⇒ E26: `x = (x ◇ y) ◇ y`
34. E75: `x = y ◇ (y ◇ (y ◇ x))`; E209: `x = (x ◇ (y ◇ x)) ◇ y` ⇒ E261: `x = ((x ◇ y) ◇ x) ◇ y`
35. E75: `x = y ◇ (y ◇ (y ◇ x))`; E212: `x = (x ◇ (y ◇ y)) ◇ y` ⇒ E99: `x = x ◇ ((x ◇ x) ◇ x)`
36. E102: `x = x ◇ ((x ◇ y) ◇ y)`; E105: `x = x ◇ ((y ◇ x) ◇ y)`; E325: `x ◇ y = x ◇ (y ◇ x)` ⇒ E55: `x = x ◇ (y ◇ (y ◇ x))` *new*
37. E105: `x = x ◇ ((y ◇ x) ◇ y)`; E159: `x = (x ◇ y) ◇ (y ◇ x)`; E209: `x = (x ◇ (y ◇ x)) ◇ y` ⇒ E26: `x = (x ◇ y) ◇ y`
38. E105: `x = x ◇ ((y ◇ x) ◇ y)`; E167: `x = (y ◇ x) ◇ (x ◇ y)` ⇒ E127: `x = y ◇ ((y ◇ y) ◇ x)`
39. E212: `x = (x ◇ (y ◇ y)) ◇ y`; E281: `x = ((y ◇ y) ◇ x) ◇ y`; E283: `x = ((y ◇ y) ◇ y) ◇ x` ⇒ E73: `x = y ◇ (y ◇ (x ◇ y))`

