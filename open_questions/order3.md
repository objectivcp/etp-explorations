# Open order-3 questions

Implications between laws of order at most 3 that the attribute exploration of the 149 laws of order at most 3 (one per ETP class) could not decide, after a third run seeded with what the first two found and the countermodel found after the second: 73 in all, 44 up to duality, the dual of each listed question being open too. Each is listed with a minimal premise; the premise's other laws follow from it. 33 have in their premise, or imply, a law that needed a dedicated construction in the ETP, or its dual; the headings name them. Laws are numbered and written as in the ETP.

Tried on every question, for each law r of the conclusion, without a proof or a countermodel, the exploration's expert: Vampire 10 s to prove and 60 s for a model, Mace4 120 s, E 2 s, Prover9 5 s.

Also, on every law r:

- Mace4 on the premise and not r, sizes 2 to 24, 300 s (marked **24** where it exhausted all sizes);
- Vampire 5.1.0 `--mode casc`, 60 s on 8 cores (not on the laws of 8 questions new to the second or third run); E 3.2.5 and Prover9, 120 s each;
- Knuth–Bendix completion of the premise, 120 s, on most of them (it failed on all);
- linear and affine models x◇y = ax + by + c mod n, n ≤ 100;
- Vampire `--mode casc` 600 s, Vampire `--schedule casc_sat` 300 s and E `--auto-schedule` 300 s, one core each.

These results are from automated tools and are not checked in Lean.


## Premise implies E65 (Asterix), or its dual E261

1. E48: `x = x ◇ (x ◇ (x ◇ y))`; E261: `x = ((x ◇ y) ◇ x) ◇ y` ⇒ E102: `x = x ◇ ((x ◇ y) ◇ y)`
2. E49: `x = x ◇ (x ◇ (y ◇ x))`; E65: `x = y ◇ (x ◇ (y ◇ x))` ⇒ E39: `x ◇ x = y ◇ x` **24**
3. E53: `x = x ◇ (y ◇ (x ◇ y))`; E55: `x = x ◇ (y ◇ (y ◇ x))`; E261: `x = ((x ◇ y) ◇ x) ◇ y` ⇒ E159: `x = (x ◇ y) ◇ (y ◇ x)`
4. E55: `x = x ◇ (y ◇ (y ◇ x))`; E159: `x = (x ◇ y) ◇ (y ◇ x)`; E261: `x = ((x ◇ y) ◇ x) ◇ y` ⇒ E53: `x = x ◇ (y ◇ (x ◇ y))`
5. E65: `x = y ◇ (x ◇ (y ◇ x))`; E124: `x = y ◇ ((y ◇ x) ◇ x)`; E159: `x = (x ◇ y) ◇ (y ◇ x)` ⇒ E5: `x = y ◇ x` **24**
6. E65: `x = y ◇ (x ◇ (y ◇ x))`; E167: `x = (y ◇ x) ◇ (x ◇ y)` ⇒ E26: `x = (x ◇ y) ◇ y`
7. E65: `x = y ◇ (x ◇ (y ◇ x))`; E228: `x = (y ◇ (y ◇ x)) ◇ x` ⇒ E270: `x = ((y ◇ x) ◇ x) ◇ x`
8. E65: `x = y ◇ (x ◇ (y ◇ x))`; E261: `x = ((x ◇ y) ◇ x) ◇ y` ⇒ E43: `x ◇ y = y ◇ x`
9. E65: `x = y ◇ (x ◇ (y ◇ x))`; E264: `x = ((x ◇ y) ◇ y) ◇ y` ⇒ E117: `x = y ◇ ((x ◇ y) ◇ x)`
10. E65: `x = y ◇ (x ◇ (y ◇ x))`; E364: `x ◇ x = (y ◇ x) ◇ x` ⇒ E55: `x = x ◇ (y ◇ (y ◇ x))`
11. E65: `x = y ◇ (x ◇ (y ◇ x))`; E385: `x ◇ y = (y ◇ x) ◇ y` ⇒ E375: `x ◇ y = (x ◇ x) ◇ y` **24**
12. E261: `x = ((x ◇ y) ◇ x) ◇ y`; E308: `x ◇ x = x ◇ (x ◇ y)` ⇒ E258: `x = ((x ◇ x) ◇ y) ◇ y`

## Premise implies E118, E124 (greedy constructions), or their duals E229, E206

13. E53: `x = x ◇ (y ◇ (x ◇ y))`; E206: `x = (x ◇ (x ◇ y)) ◇ y` ⇒ E105: `x = x ◇ ((y ◇ x) ◇ y)`; E159: `x = (x ◇ y) ◇ (y ◇ x)`
14. E75: `x = y ◇ (y ◇ (y ◇ x))`; E222: `x = (y ◇ (x ◇ y)) ◇ y` ⇒ E43: `x ◇ y = y ◇ x`
15. E101: `x = x ◇ ((x ◇ y) ◇ x)`; E206: `x = (x ◇ (x ◇ y)) ◇ y` ⇒ E4: `x = x ◇ y`
16. E105: `x = x ◇ ((y ◇ x) ◇ y)`; E159: `x = (x ◇ y) ◇ (y ◇ x)`; E206: `x = (x ◇ (x ◇ y)) ◇ y` ⇒ E53: `x = x ◇ (y ◇ (x ◇ y))`
17. E105: `x = x ◇ ((y ◇ x) ◇ y)`; E206: `x = (x ◇ (x ◇ y)) ◇ y`; E209: `x = (x ◇ (y ◇ x)) ◇ y` ⇒ E4: `x = x ◇ y` **24**
18. E118: `x = y ◇ ((x ◇ y) ◇ y)`; E151: `x = (x ◇ x) ◇ (x ◇ x)` ⇒ E222: `x = (y ◇ (x ◇ y)) ◇ y`
19. E118: `x = y ◇ ((x ◇ y) ◇ y)`; E280: `x = ((y ◇ y) ◇ x) ◇ x` ⇒ E43: `x ◇ y = y ◇ x`
20. E124: `x = y ◇ ((y ◇ x) ◇ x)`; E153: `x = (x ◇ x) ◇ (y ◇ x)` ⇒ E10: `x = x ◇ (y ◇ x)` **24**
21. E124: `x = y ◇ ((y ◇ x) ◇ x)`; E167: `x = (y ◇ x) ◇ (x ◇ y)` ⇒ E206: `x = (x ◇ (x ◇ y)) ◇ y`
22. E124: `x = y ◇ ((y ◇ x) ◇ x)`; E385: `x ◇ y = (y ◇ x) ◇ y` ⇒ E10: `x = x ◇ (y ◇ x)`
23. E125: `x = y ◇ ((y ◇ x) ◇ y)`; E283: `x = ((y ◇ y) ◇ y) ◇ x` ⇒ E66: `x = y ◇ (x ◇ (y ◇ y))`
24. E156: `x = (x ◇ y) ◇ (x ◇ x)`; E206: `x = (x ◇ (x ◇ y)) ◇ y` ⇒ E24: `x = (x ◇ x) ◇ y` **24**
25. E206: `x = (x ◇ (x ◇ y)) ◇ y`; E325: `x ◇ y = x ◇ (y ◇ x)` ⇒ E24: `x = (x ◇ x) ◇ y`
26. E222: `x = (y ◇ (x ◇ y)) ◇ y`; E283: `x = ((y ◇ y) ◇ y) ◇ x` ⇒ E66: `x = y ◇ (x ◇ (y ◇ y))`

## Premise implies E63, E73 (proved by hand), or their duals E271, E274

27. E50: `x = x ◇ (x ◇ (y ◇ y))`; E63: `x = y ◇ (x ◇ (x ◇ y))` ⇒ E53: `x = x ◇ (y ◇ (x ◇ y))`
28. E56: `x = x ◇ (y ◇ (y ◇ y))`; E63: `x = y ◇ (x ◇ (x ◇ y))` ⇒ E26: `x = (x ◇ y) ◇ y`
29. E63: `x = y ◇ (x ◇ (x ◇ y))`; E167: `x = (y ◇ x) ◇ (x ◇ y)` ⇒ E2: `x = y` **24**
30. E63: `x = y ◇ (x ◇ (x ◇ y))`; E271: `x = ((y ◇ x) ◇ x) ◇ y` ⇒ E43: `x ◇ y = y ◇ x`
31. E73: `x = y ◇ (y ◇ (x ◇ y))`; E99: `x = x ◇ ((x ◇ x) ◇ x)` ⇒ E125: `x = y ◇ ((y ◇ x) ◇ y)`
32. E73: `x = y ◇ (y ◇ (x ◇ y))`; E151: `x = (x ◇ x) ◇ (x ◇ x)` ⇒ E125: `x = y ◇ ((y ◇ x) ◇ y)`
33. E73: `x = y ◇ (y ◇ (x ◇ y))`; E203: `x = (x ◇ (x ◇ x)) ◇ x` ⇒ E125: `x = y ◇ ((y ◇ x) ◇ y)`

## Other premises

34. E49: `x = x ◇ (x ◇ (y ◇ x))`; E260: `x = ((x ◇ y) ◇ x) ◇ x` ⇒ E10: `x = x ◇ (y ◇ x)`
35. E55: `x = x ◇ (y ◇ (y ◇ x))`; E159: `x = (x ◇ y) ◇ (y ◇ x)`; E209: `x = (x ◇ (y ◇ x)) ◇ y` ⇒ E26: `x = (x ◇ y) ◇ y`
36. E55: `x = x ◇ (y ◇ (y ◇ x))`; E325: `x ◇ y = x ◇ (y ◇ x)` ⇒ E26: `x = (x ◇ y) ◇ y`
37. E75: `x = y ◇ (y ◇ (y ◇ x))`; E167: `x = (y ◇ x) ◇ (x ◇ y)`; E264: `x = ((x ◇ y) ◇ y) ◇ y` ⇒ E2: `x = y`
38. E75: `x = y ◇ (y ◇ (y ◇ x))`; E209: `x = (x ◇ (y ◇ x)) ◇ y` ⇒ E261: `x = ((x ◇ y) ◇ x) ◇ y`
39. E75: `x = y ◇ (y ◇ (y ◇ x))`; E212: `x = (x ◇ (y ◇ y)) ◇ y` ⇒ E99: `x = x ◇ ((x ◇ x) ◇ x)`
40. E105: `x = x ◇ ((y ◇ x) ◇ y)`; E159: `x = (x ◇ y) ◇ (y ◇ x)`; E209: `x = (x ◇ (y ◇ x)) ◇ y` ⇒ E26: `x = (x ◇ y) ◇ y`
41. E105: `x = x ◇ ((y ◇ x) ◇ y)`; E167: `x = (y ◇ x) ◇ (x ◇ y)` ⇒ E127: `x = y ◇ ((y ◇ y) ◇ x)`
42. E105: `x = x ◇ ((y ◇ x) ◇ y)`; E325: `x ◇ y = x ◇ (y ◇ x)` ⇒ E26: `x = (x ◇ y) ◇ y`
43. E127: `x = y ◇ ((y ◇ y) ◇ x)`; E264: `x = ((x ◇ y) ◇ y) ◇ y` ⇒ E47: `x = x ◇ (x ◇ (x ◇ x))`
44. E212: `x = (x ◇ (y ◇ y)) ◇ y`; E281: `x = ((y ◇ y) ◇ x) ◇ y`; E283: `x = ((y ◇ y) ◇ y) ◇ x` ⇒ E75: `x = y ◇ (y ◇ (y ◇ x))`

