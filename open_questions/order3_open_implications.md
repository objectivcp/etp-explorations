# All open order-3 implications

Every implication between the 149 laws of order at most 3 with a single law as conclusion that the exploration left open, neither proved nor refuted: 2,930 in all, 1,466 up to duality. Closed under the proved implications, their premises are 157 sets of laws, 81 up to duality. Each is listed here once up to duality, with a minimal premise, whose other laws follow from it, and all its open laws: the implication from the premise to each of them is open. The dual of each listed premise is open for the duals of its laws; a premise equal to its own dual is listed with all its open laws. The run asked each of these implications with its closed premise; [`order3.md`](order3.md) says what was tried.

This list only shrinks. A countermodel removes each law it violates under each premise it satisfies. A proof of A ⇒ r removes r under each premise that implies A by the proved implications, and with it whatever then follows. Nothing ever needs to be added.

A premise marked with a question number is that of the question of [`order3.md`](order3.md); with the proved implications, those questions give all the implications here. Open laws are given by number; all the laws are listed at the end, numbered and written as in the ETP. These results are from automated tools and are not checked in Lean.


## Premise implies E65 (Asterix), or its dual E261

1. E48: `x = x ◇ (x ◇ (x ◇ y))`; E53: `x = x ◇ (y ◇ (x ◇ y))`; E261: `x = ((x ◇ y) ◇ x) ◇ y` ⇒ E102
2. E48: `x = x ◇ (x ◇ (x ◇ y))`; E261: `x = ((x ◇ y) ◇ x) ◇ y` (question 1) ⇒ E102
3. E49: `x = x ◇ (x ◇ (y ◇ x))`; E65: `x = y ◇ (x ◇ (y ◇ x))` (question 2) ⇒ E39, E52, E55, E58, E62, E72, E75, E359, E361, E364, E367, E370, E375, E378, E381, E385, E395
4. E49: `x = x ◇ (x ◇ (y ◇ x))`; E65: `x = y ◇ (x ◇ (y ◇ x))`; E359: `x ◇ x = (x ◇ x) ◇ x` ⇒ E39, E52, E55, E58, E62, E72, E75, E361, E364, E367, E370, E375, E378, E381, E385, E395
5. E53: `x = x ◇ (y ◇ (x ◇ y))`; E55: `x = x ◇ (y ◇ (y ◇ x))`; E261: `x = ((x ◇ y) ◇ x) ◇ y` (question 3) ⇒ E159
6. E53: `x = x ◇ (y ◇ (x ◇ y))`; E102: `x = x ◇ ((x ◇ y) ◇ y)`; E261: `x = ((x ◇ y) ◇ x) ◇ y` ⇒ E48
7. E53: `x = x ◇ (y ◇ (x ◇ y))`; E206: `x = (x ◇ (x ◇ y)) ◇ y`; E261: `x = ((x ◇ y) ◇ x) ◇ y` (question 4) ⇒ E4, E9, E10, E11, E24, E25, E26, E38, E48, E49, E50, E52, E55, E56, E58, E100, E101, E102, E103, E104, E105, E106, E107, E108, E109, E111, E152, E153, E156, E159, E162, E205, E208, E209, E211, E212, E215, E256, E257, E258, E260, E263, E264, E266, E308, E309, E310, E311, E323, E325, E327, E329, E360, E361, E362, E363, E374, E377, E378, E379, E381
8. E55: `x = x ◇ (y ◇ (y ◇ x))`; E159: `x = (x ◇ y) ◇ (y ◇ x)`; E261: `x = ((x ◇ y) ◇ x) ◇ y` (question 5) ⇒ E53
9. E65: `x = y ◇ (x ◇ (y ◇ x))`; E73: `x = y ◇ (y ◇ (x ◇ y))` ⇒ E26, E102, E117, E125, E167, E212, E229, E258, E263, E335, E362
10. E65: `x = y ◇ (x ◇ (y ◇ x))`; E124: `x = y ◇ ((y ◇ x) ◇ x)`; E159: `x = (x ◇ y) ◇ (y ◇ x)` (question 6) ⇒ E5, E10, E13, E16, E25, E28, E31, E39, E49, E52, E55, E58, E62, E72, E75, E101, E104, E107, E117, E127, E138, E153, E156, E162, E166, E205, E208, E211, E218, E221, E224, E228, E231, E238, E242, E246, E257, E260, E263, E266, E270, E273, E280, E283, E309, E312, E315, E318, E323, E329, E333, E336, E343, E361, E364, E367, E370, E378, E381, E385, E395
11. E65: `x = y ◇ (x ◇ (y ◇ x))`; E167: `x = (y ◇ x) ◇ (x ◇ y)` (question 7) ⇒ E26, E73, E102, E117, E125, E212, E229, E258, E263, E335, E362
12. E65: `x = y ◇ (x ◇ (y ◇ x))`; E228: `x = (y ◇ (y ◇ x)) ◇ x` (question 8) ⇒ E270
13. E65: `x = y ◇ (x ◇ (y ◇ x))`; E261: `x = ((x ◇ y) ◇ x) ◇ y` (question 9) ⇒ E43, E63, E117, E124, E206, E209, E271, E332, E387
14. E65: `x = y ◇ (x ◇ (y ◇ x))`; E264: `x = ((x ◇ y) ◇ y) ◇ y` (question 10) ⇒ E117
15. E65: `x = y ◇ (x ◇ (y ◇ x))`; E326: `x ◇ y = x ◇ (y ◇ y)`; E364: `x ◇ x = (y ◇ x) ◇ x` ⇒ E16, E55, E72, E127, E208, E228, E315, E333
16. E65: `x = y ◇ (x ◇ (y ◇ x))`; E364: `x ◇ x = (y ◇ x) ◇ x` (question 11) ⇒ E55, E72
17. E65: `x = y ◇ (x ◇ (y ◇ x))`; E364: `x ◇ x = (y ◇ x) ◇ x`; E375: `x ◇ y = (x ◇ x) ◇ y` ⇒ E55, E72
18. E65: `x = y ◇ (x ◇ (y ◇ x))`; E385: `x ◇ y = (y ◇ x) ◇ y` (question 12) ⇒ E375

## Premise implies E118, E124 (greedy constructions), or their duals E229, E206

19. E73: `x = y ◇ (y ◇ (x ◇ y))`; E124: `x = y ◇ ((y ◇ x) ◇ x)` ⇒ E2, E4, E5, E9, E10, E11, E13, E14, E16, E24, E25, E26, E28, E29, E31, E38, E39, E40, E41, E43, E48, E49, E50, E52, E53, E55, E56, E58, E62, E63, E65, E66, E72, E75, E100, E101, E102, E103, E104, E105, E106, E107, E108, E109, E111, E115, E117, E118, E125, E127, E138, E152, E153, E156, E159, E162, E166, E167, E168, E205, E206, E208, E209, E211, E212, E215, E218, E219, E221, E222, E224, E228, E229, E231, E238, E242, E246, E256, E257, E258, E260, E261, E263, E264, E266, E270, E271, E273, E274, E280, E281, E283, E308, E309, E310, E311, E312, E313, E314, E315, E316, E317, E318, E319, E323, E325, E327, E329, E332, E333, E335, E336, E343, E360, E361, E362, E363, E364, E365, E366, E367, E368, E370, E371, E372, E374, E377, E378, E379, E381, E384, E385, E387, E395
20. E75: `x = y ◇ (y ◇ (y ◇ x))`; E274: `x = ((y ◇ x) ◇ y) ◇ y`; E280: `x = ((y ◇ y) ◇ x) ◇ x` ⇒ E43, E73, E125, E229, E264
21. E75: `x = y ◇ (y ◇ (y ◇ x))`; E274: `x = ((y ◇ x) ◇ y) ◇ y`; E283: `x = ((y ◇ y) ◇ y) ◇ x` ⇒ E127
22. E75: `x = y ◇ (y ◇ (y ◇ x))`; E274: `x = ((y ◇ x) ◇ y) ◇ y`; E375: `x ◇ y = (x ◇ x) ◇ y` (question 13) ⇒ E43, E73, E125, E229, E264, E332, E387
23. E101: `x = x ◇ ((x ◇ y) ◇ x)`; E105: `x = x ◇ ((y ◇ x) ◇ y)`; E159: `x = (x ◇ y) ◇ (y ◇ x)`; E206: `x = (x ◇ (x ◇ y)) ◇ y` ⇒ E4, E9, E10, E11, E24, E25, E26, E38, E48, E49, E50, E52, E53, E55, E56, E58, E100, E102, E103, E104, E106, E107, E108, E109, E111, E152, E153, E156, E162, E205, E208, E209, E211, E212, E215, E256, E257, E258, E260, E261, E263, E264, E266, E308, E309, E310, E311, E323, E325, E327, E329, E360, E361, E362, E363, E374, E377, E378, E379, E381
24. E101: `x = x ◇ ((x ◇ y) ◇ x)`; E105: `x = x ◇ ((y ◇ x) ◇ y)`; E206: `x = (x ◇ (x ◇ y)) ◇ y` ⇒ E4, E9, E10, E11, E24, E25, E26, E38, E48, E49, E50, E52, E53, E55, E56, E58, E100, E102, E103, E104, E106, E107, E108, E109, E111, E152, E153, E156, E159, E162, E205, E208, E209, E211, E212, E215, E256, E257, E258, E260, E261, E263, E264, E266, E308, E309, E310, E311, E323, E325, E327, E329, E360, E361, E362, E363, E374, E377, E378, E379, E381
25. E101: `x = x ◇ ((x ◇ y) ◇ x)`; E159: `x = (x ◇ y) ◇ (y ◇ x)`; E206: `x = (x ◇ (x ◇ y)) ◇ y` ⇒ E4, E9, E10, E11, E24, E25, E26, E38, E48, E49, E50, E52, E53, E55, E56, E58, E100, E102, E103, E104, E105, E106, E107, E108, E109, E111, E152, E153, E156, E162, E205, E208, E209, E211, E212, E215, E256, E257, E258, E260, E261, E263, E264, E266, E308, E309, E310, E311, E323, E325, E327, E329, E360, E361, E362, E363, E374, E377, E378, E379, E381
26. E101: `x = x ◇ ((x ◇ y) ◇ x)`; E206: `x = (x ◇ (x ◇ y)) ◇ y` (question 14) ⇒ E4, E9, E10, E11, E24, E25, E26, E38, E48, E49, E50, E52, E53, E55, E56, E58, E100, E102, E103, E104, E105, E106, E107, E108, E109, E111, E152, E153, E156, E159, E162, E205, E208, E209, E211, E212, E215, E256, E257, E258, E260, E261, E263, E264, E266, E308, E309, E310, E311, E323, E325, E327, E329, E360, E361, E362, E363, E374, E377, E378, E379, E381
27. E105: `x = x ◇ ((y ◇ x) ◇ y)`; E159: `x = (x ◇ y) ◇ (y ◇ x)`; E206: `x = (x ◇ (x ◇ y)) ◇ y` (question 15) ⇒ E53
28. E105: `x = x ◇ ((y ◇ x) ◇ y)`; E206: `x = (x ◇ (x ◇ y)) ◇ y`; E209: `x = (x ◇ (y ◇ x)) ◇ y` (question 16) ⇒ E4, E9, E10, E11, E24, E25, E26, E38, E48, E49, E50, E52, E53, E55, E56, E58, E100, E101, E102, E103, E104, E106, E107, E108, E109, E111, E152, E153, E156, E159, E162, E205, E208, E211, E212, E215, E256, E257, E258, E260, E261, E263, E264, E266, E308, E309, E310, E311, E323, E325, E327, E329, E360, E361, E362, E363, E374, E377, E378, E379, E381
29. E105: `x = x ◇ ((y ◇ x) ◇ y)`; E206: `x = (x ◇ (x ◇ y)) ◇ y`; E325: `x ◇ y = x ◇ (y ◇ x)` ⇒ E4, E9, E10, E11, E24, E25, E26, E38, E48, E49, E50, E52, E53, E55, E56, E58, E100, E101, E102, E103, E104, E106, E107, E108, E109, E111, E152, E153, E156, E159, E162, E205, E208, E209, E211, E212, E215, E256, E257, E258, E260, E261, E263, E264, E266, E308, E309, E310, E311, E323, E327, E329, E360, E361, E362, E363, E374, E377, E378, E379, E381
30. E118: `x = y ◇ ((x ◇ y) ◇ y)`; E151: `x = (x ◇ x) ◇ (x ◇ x)` (question 17) ⇒ E222, E274
31. E118: `x = y ◇ ((x ◇ y) ◇ y)`; E280: `x = ((y ◇ y) ◇ x) ◇ x` (question 18) ⇒ E43, E73, E75, E125, E222, E229, E264, E274
32. E118: `x = y ◇ ((x ◇ y) ◇ y)`; E283: `x = ((y ◇ y) ◇ y) ◇ x` ⇒ E75, E127, E222, E274
33. E118: `x = y ◇ ((x ◇ y) ◇ y)`; E375: `x ◇ y = (x ◇ x) ◇ y` ⇒ E222, E274
34. E124: `x = y ◇ ((y ◇ x) ◇ x)`; E153: `x = (x ◇ x) ◇ (y ◇ x)` (question 19) ⇒ E10, E13, E16, E39, E101, E104, E107, E117, E127, E138, E156, E159, E162, E166, E361, E364, E367, E370, E375, E378, E381, E385, E395
35. E124: `x = y ◇ ((y ◇ x) ◇ x)`; E153: `x = (x ◇ x) ◇ (y ◇ x)`; E159: `x = (x ◇ y) ◇ (y ◇ x)` ⇒ E10, E13, E16, E39, E101, E104, E107, E117, E127, E138, E156, E162, E166, E361, E364, E367, E370, E375, E378, E381, E385, E395
36. E124: `x = y ◇ ((y ◇ x) ◇ x)`; E167: `x = (y ◇ x) ◇ (x ◇ y)` (question 20) ⇒ E206
37. E124: `x = y ◇ ((y ◇ x) ◇ x)`; E326: `x ◇ y = x ◇ (y ◇ y)`; E385: `x ◇ y = (y ◇ x) ◇ y` ⇒ E5, E10, E13, E16, E25, E28, E31, E39, E49, E52, E55, E58, E62, E65, E72, E75, E101, E104, E107, E117, E127, E138, E153, E156, E159, E162, E166, E205, E208, E211, E218, E221, E224, E228, E231, E238, E242, E246, E257, E260, E263, E266, E270, E273, E280, E283, E309, E312, E315, E318, E323, E329, E333, E336, E343, E361, E364, E367, E370, E378, E381, E395
38. E124: `x = y ◇ ((y ◇ x) ◇ x)`; E375: `x ◇ y = (x ◇ x) ◇ y`; E385: `x ◇ y = (y ◇ x) ◇ y` ⇒ E10, E13, E16, E39, E101, E104, E107, E117, E127, E138, E153, E156, E159, E162, E166, E361, E364, E367, E370, E378, E381, E395
39. E124: `x = y ◇ ((y ◇ x) ◇ x)`; E385: `x ◇ y = (y ◇ x) ◇ y` (question 21) ⇒ E10, E13, E16, E39, E101, E104, E107, E117, E127, E138, E153, E156, E159, E162, E166, E361, E364, E367, E370, E375, E378, E381, E395
40. E125: `x = y ◇ ((y ◇ x) ◇ y)`; E280: `x = ((y ◇ y) ◇ x) ◇ x` ⇒ E43, E75, E118, E222, E264, E274
41. E125: `x = y ◇ ((y ◇ x) ◇ y)`; E283: `x = ((y ◇ y) ◇ y) ◇ x` (question 22) ⇒ E212, E264
42. E127: `x = y ◇ ((y ◇ y) ◇ x)`; E274: `x = ((y ◇ x) ◇ y) ◇ y`; E283: `x = ((y ◇ y) ◇ y) ◇ x` ⇒ E75
43. E264: `x = ((x ◇ y) ◇ y) ◇ y`; E274: `x = ((y ◇ x) ◇ y) ◇ y`; E283: `x = ((y ◇ y) ◇ y) ◇ x` ⇒ E66, E127, E212, E281

## Premise implies E63, E73 (proved by hand), or their duals E271, E274

44. E47: `x = x ◇ (x ◇ (x ◇ x))`; E151: `x = (x ◇ x) ◇ (x ◇ x)`; E274: `x = ((y ◇ x) ◇ y) ◇ y` ⇒ E118, E222
45. E47: `x = x ◇ (x ◇ (x ◇ x))`; E274: `x = ((y ◇ x) ◇ y) ◇ y` ⇒ E118, E222
46. E50: `x = x ◇ (x ◇ (y ◇ y))`; E63: `x = y ◇ (x ◇ (x ◇ y))` (question 23) ⇒ E26, E53, E75
47. E50: `x = x ◇ (x ◇ (y ◇ y))`; E63: `x = y ◇ (x ◇ (x ◇ y))`; E75: `x = y ◇ (y ◇ (y ◇ x))` ⇒ E53
48. E50: `x = x ◇ (x ◇ (y ◇ y))`; E274: `x = ((y ◇ x) ◇ y) ◇ y` ⇒ E43, E73, E75, E118, E125, E222, E229, E264
49. E56: `x = x ◇ (y ◇ (y ◇ y))`; E63: `x = y ◇ (x ◇ (x ◇ y))` (question 24) ⇒ E26, E75
50. E63: `x = y ◇ (x ◇ (x ◇ y))`; E167: `x = (y ◇ x) ◇ (x ◇ y)` (question 25) ⇒ E2, E4, E5, E9, E10, E11, E13, E14, E16, E24, E25, E26, E28, E29, E31, E38, E39, E40, E41, E43, E48, E49, E50, E52, E53, E55, E56, E58, E62, E65, E66, E72, E73, E75, E100, E101, E102, E103, E104, E105, E106, E107, E108, E109, E111, E115, E117, E118, E124, E125, E127, E138, E152, E153, E156, E159, E162, E166, E168, E205, E206, E208, E209, E211, E212, E215, E218, E219, E221, E222, E224, E228, E229, E231, E238, E242, E246, E256, E257, E258, E260, E261, E263, E264, E266, E270, E271, E273, E274, E280, E281, E283, E308, E309, E310, E311, E312, E313, E314, E315, E316, E317, E318, E319, E323, E325, E327, E329, E332, E333, E335, E336, E343, E360, E361, E362, E363, E364, E365, E366, E367, E368, E370, E371, E372, E374, E377, E378, E379, E381, E384, E385, E387, E395
51. E63: `x = y ◇ (x ◇ (x ◇ y))`; E271: `x = ((y ◇ x) ◇ x) ◇ y` (question 26) ⇒ E43, E65, E117, E124, E206, E209, E261, E332, E387
52. E73: `x = y ◇ (y ◇ (x ◇ y))`; E99: `x = x ◇ ((x ◇ x) ◇ x)` (question 27) ⇒ E125, E203, E229, E255
53. E73: `x = y ◇ (y ◇ (x ◇ y))`; E99: `x = x ◇ ((x ◇ x) ◇ x)`; E151: `x = (x ◇ x) ◇ (x ◇ x)` ⇒ E125, E203, E229, E255
54. E73: `x = y ◇ (y ◇ (x ◇ y))`; E99: `x = x ◇ ((x ◇ x) ◇ x)`; E151: `x = (x ◇ x) ◇ (x ◇ x)`; E203: `x = (x ◇ (x ◇ x)) ◇ x` ⇒ E125, E229, E255
55. E73: `x = y ◇ (y ◇ (x ◇ y))`; E99: `x = x ◇ ((x ◇ x) ◇ x)`; E203: `x = (x ◇ (x ◇ x)) ◇ x` ⇒ E125, E229, E255
56. E73: `x = y ◇ (y ◇ (x ◇ y))`; E107: `x = x ◇ ((y ◇ y) ◇ x)` ⇒ E43, E75, E118, E125, E203, E211, E222, E229, E255, E264, E274, E280
57. E73: `x = y ◇ (y ◇ (x ◇ y))`; E108: `x = x ◇ ((y ◇ y) ◇ y)` ⇒ E56, E125, E151, E203, E212, E229, E231, E255, E264, E283
58. E73: `x = y ◇ (y ◇ (x ◇ y))`; E108: `x = x ◇ ((y ◇ y) ◇ y)`; E151: `x = (x ◇ x) ◇ (x ◇ x)` ⇒ E125, E203, E212, E229, E231, E255, E264, E283
59. E73: `x = y ◇ (y ◇ (x ◇ y))`; E108: `x = x ◇ ((y ◇ y) ◇ y)`; E203: `x = (x ◇ (x ◇ x)) ◇ x` ⇒ E56, E125, E151, E212, E229, E231, E255, E264, E283
60. E73: `x = y ◇ (y ◇ (x ◇ y))`; E151: `x = (x ◇ x) ◇ (x ◇ x)` (question 28) ⇒ E99, E125, E203, E229, E255
61. E73: `x = y ◇ (y ◇ (x ◇ y))`; E151: `x = (x ◇ x) ◇ (x ◇ x)`; E203: `x = (x ◇ (x ◇ x)) ◇ x` ⇒ E99, E125, E229, E255
62. E73: `x = y ◇ (y ◇ (x ◇ y))`; E159: `x = (x ◇ y) ◇ (y ◇ x)` ⇒ E125, E229, E271
63. E73: `x = y ◇ (y ◇ (x ◇ y))`; E203: `x = (x ◇ (x ◇ x)) ◇ x` (question 29) ⇒ E99, E125, E229, E255
64. E73: `x = y ◇ (y ◇ (x ◇ y))`; E211: `x = (x ◇ (y ◇ y)) ◇ x` ⇒ E43, E75, E118, E125, E222, E229, E255, E264, E274, E280
65. E73: `x = y ◇ (y ◇ (x ◇ y))`; E283: `x = ((y ◇ y) ◇ y) ◇ x` ⇒ E125, E212, E229, E264
66. E73: `x = y ◇ (y ◇ (x ◇ y))`; E375: `x ◇ y = (x ◇ x) ◇ y` ⇒ E125, E229

## Other premises

67. E49: `x = x ◇ (x ◇ (y ◇ x))`; E260: `x = ((x ◇ y) ◇ x) ◇ x` (question 30) ⇒ E10, E25, E52, E55, E101, E104, E107, E153, E156, E205, E208, E211, E257, E263, E309, E323, E361, E378
68. E55: `x = x ◇ (y ◇ (y ◇ x))`; E102: `x = x ◇ ((x ◇ y) ◇ y)`; E105: `x = x ◇ ((y ◇ x) ◇ y)`; E159: `x = (x ◇ y) ◇ (y ◇ x)`; E209: `x = (x ◇ (y ◇ x)) ◇ y` ⇒ E26, E212, E258, E263, E325, E362
69. E55: `x = x ◇ (y ◇ (y ◇ x))`; E102: `x = x ◇ ((x ◇ y) ◇ y)`; E159: `x = (x ◇ y) ◇ (y ◇ x)`; E209: `x = (x ◇ (y ◇ x)) ◇ y` ⇒ E26, E105, E212, E258, E263, E325, E362
70. E55: `x = x ◇ (y ◇ (y ◇ x))`; E102: `x = x ◇ ((x ◇ y) ◇ y)`; E325: `x ◇ y = x ◇ (y ◇ x)` (question 31) ⇒ E105
71. E55: `x = x ◇ (y ◇ (y ◇ x))`; E105: `x = x ◇ ((y ◇ x) ◇ y)`; E159: `x = (x ◇ y) ◇ (y ◇ x)`; E209: `x = (x ◇ (y ◇ x)) ◇ y` ⇒ E26, E102, E212, E258, E263, E325, E362
72. E55: `x = x ◇ (y ◇ (y ◇ x))`; E159: `x = (x ◇ y) ◇ (y ◇ x)`; E209: `x = (x ◇ (y ◇ x)) ◇ y` (question 32) ⇒ E26, E102, E105, E212, E258, E263, E325, E362
73. E75: `x = y ◇ (y ◇ (y ◇ x))`; E117: `x = y ◇ ((x ◇ y) ◇ x)`; E264: `x = ((x ◇ y) ◇ y) ◇ y` ⇒ E2, E4, E5, E9, E10, E11, E13, E14, E16, E24, E25, E26, E28, E29, E31, E38, E39, E40, E41, E43, E48, E49, E50, E52, E53, E55, E56, E58, E62, E63, E65, E66, E72, E73, E100, E101, E102, E103, E104, E105, E106, E107, E108, E109, E111, E115, E118, E124, E125, E127, E138, E152, E153, E156, E159, E162, E166, E167, E168, E205, E206, E208, E209, E211, E212, E215, E218, E219, E221, E222, E224, E228, E229, E231, E238, E242, E246, E256, E257, E258, E260, E261, E263, E266, E270, E271, E273, E274, E280, E281, E283, E308, E309, E310, E311, E312, E313, E314, E315, E316, E317, E318, E319, E323, E325, E327, E329, E332, E333, E335, E336, E343, E360, E361, E362, E363, E364, E365, E366, E367, E368, E370, E371, E372, E374, E377, E378, E379, E381, E384, E385, E387, E395
74. E75: `x = y ◇ (y ◇ (y ◇ x))`; E167: `x = (y ◇ x) ◇ (x ◇ y)`; E209: `x = (x ◇ (y ◇ x)) ◇ y` ⇒ E2, E4, E5, E9, E10, E11, E13, E14, E16, E24, E25, E26, E28, E29, E31, E38, E39, E40, E41, E43, E48, E49, E50, E52, E53, E55, E56, E58, E62, E63, E65, E66, E72, E73, E100, E101, E102, E103, E104, E105, E106, E107, E108, E109, E111, E115, E117, E118, E124, E125, E127, E138, E152, E153, E156, E159, E162, E166, E168, E205, E206, E208, E211, E212, E215, E218, E219, E221, E222, E224, E228, E229, E231, E238, E242, E246, E256, E257, E258, E260, E261, E263, E264, E266, E270, E271, E273, E274, E280, E281, E283, E308, E309, E310, E311, E312, E313, E314, E315, E316, E317, E318, E319, E323, E325, E327, E329, E332, E333, E335, E336, E343, E360, E361, E362, E363, E364, E365, E366, E367, E368, E370, E371, E372, E374, E377, E378, E379, E381, E384, E385, E387, E395
75. E75: `x = y ◇ (y ◇ (y ◇ x))`; E209: `x = (x ◇ (y ◇ x)) ◇ y` (question 33) ⇒ E261
76. E75: `x = y ◇ (y ◇ (y ◇ x))`; E212: `x = (x ◇ (y ◇ y)) ◇ y` (question 34) ⇒ E99, E255
77. E102: `x = x ◇ ((x ◇ y) ◇ y)`; E105: `x = x ◇ ((y ◇ x) ◇ y)`; E159: `x = (x ◇ y) ◇ (y ◇ x)`; E209: `x = (x ◇ (y ◇ x)) ◇ y` ⇒ E26, E55, E212, E258, E263, E325, E362
78. E102: `x = x ◇ ((x ◇ y) ◇ y)`; E105: `x = x ◇ ((y ◇ x) ◇ y)`; E325: `x ◇ y = x ◇ (y ◇ x)` (question 35) ⇒ E55
79. E105: `x = x ◇ ((y ◇ x) ◇ y)`; E159: `x = (x ◇ y) ◇ (y ◇ x)`; E209: `x = (x ◇ (y ◇ x)) ◇ y` (question 36) ⇒ E26, E55, E102, E212, E258, E263, E325, E362
80. E105: `x = x ◇ ((y ◇ x) ◇ y)`; E167: `x = (y ◇ x) ◇ (x ◇ y)` (question 37) ⇒ E127
81. E212: `x = (x ◇ (y ◇ y)) ◇ y`; E281: `x = ((y ◇ y) ◇ x) ◇ y`; E283: `x = ((y ◇ y) ◇ y) ◇ x` (question 38) ⇒ E73, E75, E118, E125, E222, E229, E264, E274

## Laws

- E1: `x = x`
- E2: `x = y`
- E3: `x = x ◇ x`
- E4: `x = x ◇ y`
- E5: `x = y ◇ x`
- E8: `x = x ◇ (x ◇ x)`
- E9: `x = x ◇ (x ◇ y)`
- E10: `x = x ◇ (y ◇ x)`
- E11: `x = x ◇ (y ◇ y)`
- E13: `x = y ◇ (x ◇ x)`
- E14: `x = y ◇ (x ◇ y)`
- E16: `x = y ◇ (y ◇ x)`
- E23: `x = (x ◇ x) ◇ x`
- E24: `x = (x ◇ x) ◇ y`
- E25: `x = (x ◇ y) ◇ x`
- E26: `x = (x ◇ y) ◇ y`
- E28: `x = (y ◇ x) ◇ x`
- E29: `x = (y ◇ x) ◇ y`
- E31: `x = (y ◇ y) ◇ x`
- E38: `x ◇ x = x ◇ y`
- E39: `x ◇ x = y ◇ x`
- E40: `x ◇ x = y ◇ y`
- E41: `x ◇ x = y ◇ z`
- E43: `x ◇ y = y ◇ x`
- E47: `x = x ◇ (x ◇ (x ◇ x))`
- E48: `x = x ◇ (x ◇ (x ◇ y))`
- E49: `x = x ◇ (x ◇ (y ◇ x))`
- E50: `x = x ◇ (x ◇ (y ◇ y))`
- E52: `x = x ◇ (y ◇ (x ◇ x))`
- E53: `x = x ◇ (y ◇ (x ◇ y))`
- E55: `x = x ◇ (y ◇ (y ◇ x))`
- E56: `x = x ◇ (y ◇ (y ◇ y))`
- E58: `x = x ◇ (y ◇ (z ◇ x))`
- E62: `x = y ◇ (x ◇ (x ◇ x))`
- E63: `x = y ◇ (x ◇ (x ◇ y))`
- E65: `x = y ◇ (x ◇ (y ◇ x))`
- E66: `x = y ◇ (x ◇ (y ◇ y))`
- E72: `x = y ◇ (y ◇ (x ◇ x))`
- E73: `x = y ◇ (y ◇ (x ◇ y))`
- E75: `x = y ◇ (y ◇ (y ◇ x))`
- E99: `x = x ◇ ((x ◇ x) ◇ x)`
- E100: `x = x ◇ ((x ◇ x) ◇ y)`
- E101: `x = x ◇ ((x ◇ y) ◇ x)`
- E102: `x = x ◇ ((x ◇ y) ◇ y)`
- E103: `x = x ◇ ((x ◇ y) ◇ z)`
- E104: `x = x ◇ ((y ◇ x) ◇ x)`
- E105: `x = x ◇ ((y ◇ x) ◇ y)`
- E106: `x = x ◇ ((y ◇ x) ◇ z)`
- E107: `x = x ◇ ((y ◇ y) ◇ x)`
- E108: `x = x ◇ ((y ◇ y) ◇ y)`
- E109: `x = x ◇ ((y ◇ y) ◇ z)`
- E111: `x = x ◇ ((y ◇ z) ◇ y)`
- E115: `x = y ◇ ((x ◇ x) ◇ y)`
- E117: `x = y ◇ ((x ◇ y) ◇ x)`
- E118: `x = y ◇ ((x ◇ y) ◇ y)`
- E124: `x = y ◇ ((y ◇ x) ◇ x)`
- E125: `x = y ◇ ((y ◇ x) ◇ y)`
- E127: `x = y ◇ ((y ◇ y) ◇ x)`
- E138: `x = y ◇ ((z ◇ y) ◇ x)`
- E151: `x = (x ◇ x) ◇ (x ◇ x)`
- E152: `x = (x ◇ x) ◇ (x ◇ y)`
- E153: `x = (x ◇ x) ◇ (y ◇ x)`
- E156: `x = (x ◇ y) ◇ (x ◇ x)`
- E159: `x = (x ◇ y) ◇ (y ◇ x)`
- E162: `x = (x ◇ y) ◇ (z ◇ x)`
- E166: `x = (y ◇ x) ◇ (x ◇ x)`
- E167: `x = (y ◇ x) ◇ (x ◇ y)`
- E168: `x = (y ◇ x) ◇ (x ◇ z)`
- E203: `x = (x ◇ (x ◇ x)) ◇ x`
- E205: `x = (x ◇ (x ◇ y)) ◇ x`
- E206: `x = (x ◇ (x ◇ y)) ◇ y`
- E208: `x = (x ◇ (y ◇ x)) ◇ x`
- E209: `x = (x ◇ (y ◇ x)) ◇ y`
- E211: `x = (x ◇ (y ◇ y)) ◇ x`
- E212: `x = (x ◇ (y ◇ y)) ◇ y`
- E215: `x = (x ◇ (y ◇ z)) ◇ y`
- E218: `x = (y ◇ (x ◇ x)) ◇ x`
- E219: `x = (y ◇ (x ◇ x)) ◇ y`
- E221: `x = (y ◇ (x ◇ y)) ◇ x`
- E222: `x = (y ◇ (x ◇ y)) ◇ y`
- E224: `x = (y ◇ (x ◇ z)) ◇ x`
- E228: `x = (y ◇ (y ◇ x)) ◇ x`
- E229: `x = (y ◇ (y ◇ x)) ◇ y`
- E231: `x = (y ◇ (y ◇ y)) ◇ x`
- E238: `x = (y ◇ (z ◇ x)) ◇ x`
- E242: `x = (y ◇ (z ◇ y)) ◇ x`
- E246: `x = (y ◇ (z ◇ z)) ◇ x`
- E255: `x = ((x ◇ x) ◇ x) ◇ x`
- E256: `x = ((x ◇ x) ◇ x) ◇ y`
- E257: `x = ((x ◇ x) ◇ y) ◇ x`
- E258: `x = ((x ◇ x) ◇ y) ◇ y`
- E260: `x = ((x ◇ y) ◇ x) ◇ x`
- E261: `x = ((x ◇ y) ◇ x) ◇ y`
- E263: `x = ((x ◇ y) ◇ y) ◇ x`
- E264: `x = ((x ◇ y) ◇ y) ◇ y`
- E266: `x = ((x ◇ y) ◇ z) ◇ x`
- E270: `x = ((y ◇ x) ◇ x) ◇ x`
- E271: `x = ((y ◇ x) ◇ x) ◇ y`
- E273: `x = ((y ◇ x) ◇ y) ◇ x`
- E274: `x = ((y ◇ x) ◇ y) ◇ y`
- E280: `x = ((y ◇ y) ◇ x) ◇ x`
- E281: `x = ((y ◇ y) ◇ x) ◇ y`
- E283: `x = ((y ◇ y) ◇ y) ◇ x`
- E307: `x ◇ x = x ◇ (x ◇ x)`
- E308: `x ◇ x = x ◇ (x ◇ y)`
- E309: `x ◇ x = x ◇ (y ◇ x)`
- E310: `x ◇ x = x ◇ (y ◇ y)`
- E311: `x ◇ x = x ◇ (y ◇ z)`
- E312: `x ◇ x = y ◇ (x ◇ x)`
- E313: `x ◇ x = y ◇ (x ◇ y)`
- E314: `x ◇ x = y ◇ (x ◇ z)`
- E315: `x ◇ x = y ◇ (y ◇ x)`
- E316: `x ◇ x = y ◇ (y ◇ y)`
- E317: `x ◇ x = y ◇ (y ◇ z)`
- E318: `x ◇ x = y ◇ (z ◇ x)`
- E319: `x ◇ x = y ◇ (z ◇ y)`
- E323: `x ◇ y = x ◇ (x ◇ y)`
- E325: `x ◇ y = x ◇ (y ◇ x)`
- E326: `x ◇ y = x ◇ (y ◇ y)`
- E327: `x ◇ y = x ◇ (y ◇ z)`
- E329: `x ◇ y = x ◇ (z ◇ y)`
- E332: `x ◇ y = y ◇ (x ◇ x)`
- E333: `x ◇ y = y ◇ (x ◇ y)`
- E335: `x ◇ y = y ◇ (y ◇ x)`
- E336: `x ◇ y = y ◇ (y ◇ y)`
- E343: `x ◇ y = z ◇ (x ◇ y)`
- E359: `x ◇ x = (x ◇ x) ◇ x`
- E360: `x ◇ x = (x ◇ x) ◇ y`
- E361: `x ◇ x = (x ◇ y) ◇ x`
- E362: `x ◇ x = (x ◇ y) ◇ y`
- E363: `x ◇ x = (x ◇ y) ◇ z`
- E364: `x ◇ x = (y ◇ x) ◇ x`
- E365: `x ◇ x = (y ◇ x) ◇ y`
- E366: `x ◇ x = (y ◇ x) ◇ z`
- E367: `x ◇ x = (y ◇ y) ◇ x`
- E368: `x ◇ x = (y ◇ y) ◇ y`
- E370: `x ◇ x = (y ◇ z) ◇ x`
- E371: `x ◇ x = (y ◇ z) ◇ y`
- E372: `x ◇ x = (y ◇ z) ◇ z`
- E374: `x ◇ y = (x ◇ x) ◇ x`
- E375: `x ◇ y = (x ◇ x) ◇ y`
- E377: `x ◇ y = (x ◇ y) ◇ x`
- E378: `x ◇ y = (x ◇ y) ◇ y`
- E379: `x ◇ y = (x ◇ y) ◇ z`
- E381: `x ◇ y = (x ◇ z) ◇ y`
- E384: `x ◇ y = (y ◇ x) ◇ x`
- E385: `x ◇ y = (y ◇ x) ◇ y`
- E387: `x ◇ y = (y ◇ y) ◇ x`
- E395: `x ◇ y = (z ◇ x) ◇ y`

