import Mathlib.Data.Finite.Prod
import ExplorationLaws
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import equational_theories.EquationalResult
import Order2.MagmaTables
import Order2.MagmaParts0

set_option linter.unusedVariables false

namespace Order2

/-! M1 of Order2: 4 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M1» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [4] [2, 5, 13, 14, 16, 28, 29, 31, 39, 40, 41, 43] :=
    ⟨Fin 2, «Order2 M1», Finite.of_fintype _,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!)⟩

/-! M1^op of Order2: 5 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M1^op» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [5] [2, 4, 9, 11, 14, 24, 26, 29, 38, 40, 41, 43] :=
    ⟨Fin 2, «Order2 M1^op», Finite.of_fintype _,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!)⟩

/-! M2 of Order2: 38, 39 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M2» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [38, 39] [2, 3, 4, 5, 8, 9, 10, 11, 13, 14, 16, 23, 24, 25, 26, 28, 29, 31] :=
    ⟨Fin 2, «Order2 M2», Finite.of_fintype _,
      by decideFin!,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!)⟩

/-! M3 of Order2: 11, 14, 16 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M3» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [11, 14, 16] [2, 3, 4, 5, 9, 10, 13, 24, 25, 28, 38, 39, 41] :=
    ⟨Fin 2, «Order2 M3», Finite.of_fintype _,
      by decideFin!,
      by decideFin!,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!)⟩

/-! M4 of Order2: 3, 43 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M4» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3, 43] [2, 4, 5, 9, 10, 11, 13, 14, 16, 24, 25, 26, 28, 29, 31, 38, 39, 40, 41] :=
    ⟨Fin 2, «Order2 M4», Finite.of_fintype _,
      by decideFin!,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 1) (by decideFin!)⟩

/-! M5 of Order2: 25, 40 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M5» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [25, 40] [2, 3, 4, 5, 8, 9, 10, 11, 13, 14, 16, 24, 26, 28, 29, 38, 39, 41, 43] :=
    ⟨Fin 2, «Order2 M5», Finite.of_fintype _,
      by decideFin!,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!)⟩

/-! M5^op of Order2: 10, 40 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M5^op» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [10, 40] [2, 3, 4, 5, 9, 13, 14, 16, 23, 24, 25, 26, 28, 29, 31, 38, 39, 41, 43] :=
    ⟨Fin 2, «Order2 M5^op», Finite.of_fintype _,
      by decideFin!,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!)⟩

/-! M6 of Order2: 24 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M6» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [24] [2, 3, 4, 5, 8, 9, 10, 11, 13, 14, 16, 28, 29, 31, 39, 40, 41, 43] :=
    ⟨Fin 2, «Order2 M6», Finite.of_fintype _,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!)⟩

/-! M6^op of Order2: 13 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M6^op» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [13] [2, 3, 4, 5, 9, 11, 14, 23, 24, 25, 26, 28, 29, 31, 38, 40, 41, 43] :=
    ⟨Fin 2, «Order2 M6^op», Finite.of_fintype _,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!)⟩

/-! M7 of Order2: 26, 31 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M7» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [26, 31] [2, 3, 4, 5, 8, 9, 10, 11, 13, 14, 16, 24, 25, 28, 29, 38, 39, 41, 43] :=
    ⟨Fin 3, «Order2 M7», Finite.of_fintype _,
      by decideFin!,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!)⟩

/-! M7^op of Order2: 11, 16 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M7^op» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [11, 16] [2, 3, 4, 5, 9, 10, 13, 14, 23, 24, 25, 26, 28, 29, 31, 38, 39, 41, 43] :=
    ⟨Fin 3, «Order2 M7^op», Finite.of_fintype _,
      by decideFin!,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!)⟩

/-! M8 of Order2: 31, 43 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M8» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [31, 43] [2, 3, 4, 5, 9, 10, 13, 14, 16, 24, 25, 26, 28, 29, 38, 39, 41] :=
    ⟨Fin 3, «Order2 M8», Finite.of_fintype _,
      by decideFin!,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!)⟩

/-! M9 of Order2: 8, 26 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M9» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [8, 26] [2, 3, 4, 5, 9, 10, 11, 13, 14, 16, 24, 25, 28, 29, 31, 38, 39, 40, 41, 43] :=
    ⟨Fin 3, «Order2 M9», Finite.of_fintype _,
      by decideFin!,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 2) (by decideFin!),
      fun h => absurd (h 1 2) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 2) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 1 2) (by decideFin!)⟩

/-! M9^op of Order2: 16, 23 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M9^op» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [16, 23] [2, 3, 4, 5, 9, 10, 11, 13, 14, 24, 25, 26, 28, 29, 31, 38, 39, 40, 41, 43] :=
    ⟨Fin 3, «Order2 M9^op», Finite.of_fintype _,
      by decideFin!,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 2) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 2) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 2) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 1 2) (by decideFin!)⟩

/-! M10 of Order2: 14, 16 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M10» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [14, 16] [2, 3, 4, 5, 9, 10, 11, 13, 24, 25, 28, 31, 38, 39, 40, 41] :=
    ⟨Fin 3, «Order2 M10», Finite.of_fintype _,
      by decideFin!,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!)⟩

/-! M11 of Order2: 3, 25 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M11» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3, 25] [2, 4, 5, 9, 10, 11, 13, 14, 16, 24, 26, 28, 29, 31, 38, 39, 40, 41, 43] :=
    ⟨Fin 3, «Order2 M11», Finite.of_fintype _,
      by decideFin!,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!)⟩

/-! M11^op of Order2: 3, 10 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M11^op» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3, 10] [2, 4, 5, 9, 11, 13, 14, 16, 24, 25, 26, 28, 29, 31, 38, 39, 40, 41, 43] :=
    ⟨Fin 3, «Order2 M11^op», Finite.of_fintype _,
      by decideFin!,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!)⟩

/-! M12 of Order2: 3, 14 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M12» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3, 14] [2, 4, 5, 9, 10, 11, 13, 16, 24, 25, 26, 28, 31, 38, 39, 40, 41, 43] :=
    ⟨Fin 4, «Order2 M12», Finite.of_fintype _,
      by decideFin!,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!)⟩

/-! M13 of Order2: 11, 14 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M13» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [11, 14] [2, 3, 4, 5, 9, 10, 13, 16, 24, 25, 26, 28, 38, 39, 41, 43] :=
    ⟨Fin 5, «Order2 M13», Finite.of_fintype _,
      by decideFin!,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!)⟩

/-! M14 of Order2: 8, 26, 31 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M14» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [8, 26, 31] [2, 3, 4, 5, 9, 10, 13, 14, 16, 24, 25, 28, 29, 38, 39, 41, 43] :=
    ⟨Fin 3, «Order2 M14», Finite.of_fintype _,
      by decideFin!,
      by decideFin!,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 2) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!)⟩

/-! M14^op of Order2: 11, 16, 23 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M14^op» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [11, 16, 23] [2, 3, 4, 5, 9, 10, 13, 14, 24, 25, 26, 28, 29, 38, 39, 41, 43] :=
    ⟨Fin 3, «Order2 M14^op», Finite.of_fintype _,
      by decideFin!,
      by decideFin!,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 2) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!)⟩

/-! M15 of Order2: 28 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M15» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [28] [2, 4, 5, 9, 10, 11, 13, 14, 16, 24, 25, 26, 29, 31, 38, 39, 40, 41, 43] :=
    ⟨Fin 3, «Order2 M15», Finite.of_fintype _,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 2) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 2) (by decideFin!)⟩

/-! M15^op of Order2: 9 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M15^op» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [9] [2, 4, 5, 10, 11, 13, 14, 16, 24, 25, 26, 28, 29, 31, 38, 39, 40, 41, 43] :=
    ⟨Fin 3, «Order2 M15^op», Finite.of_fintype _,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 2) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 2) (by decideFin!)⟩

/-! M16 of Order2: 3, 26 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M16» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3, 26] [2, 4, 5, 9, 10, 11, 13, 14, 16, 24, 25, 28, 29, 31, 38, 39, 40, 41, 43] :=
    ⟨Fin 3, «Order2 M16», Finite.of_fintype _,
      by decideFin!,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!)⟩

/-! M16^op of Order2: 3, 16 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M16^op» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3, 16] [2, 4, 5, 9, 10, 11, 13, 14, 24, 25, 26, 28, 29, 31, 38, 39, 40, 41, 43] :=
    ⟨Fin 3, «Order2 M16^op», Finite.of_fintype _,
      by decideFin!,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!)⟩

/-! M17 of Order2: 25, 28 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M17» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [25, 28] [2, 4, 5, 9, 10, 11, 13, 14, 16, 24, 26, 29, 31, 38, 39, 40, 41, 43] :=
    ⟨Fin 3, «Order2 M17», Finite.of_fintype _,
      by decideFin!,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 2) (by decideFin!)⟩

/-! M17^op of Order2: 9, 10 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M17^op» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [9, 10] [2, 4, 5, 11, 13, 14, 16, 24, 25, 26, 28, 29, 31, 38, 39, 40, 41, 43] :=
    ⟨Fin 3, «Order2 M17^op», Finite.of_fintype _,
      by decideFin!,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 2) (by decideFin!)⟩

/-! M18 of Order2: 16, 28 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M18» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [16, 28] [2, 4, 5, 9, 10, 11, 13, 14, 24, 25, 26, 29, 31, 38, 39, 40, 41, 43] :=
    ⟨Fin 3, «Order2 M18», Finite.of_fintype _,
      by decideFin!,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!)⟩

/-! M18^op of Order2: 9, 26 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M18^op» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [9, 26] [2, 4, 5, 10, 11, 13, 14, 16, 24, 25, 28, 29, 31, 38, 39, 40, 41, 43] :=
    ⟨Fin 3, «Order2 M18^op», Finite.of_fintype _,
      by decideFin!,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!)⟩

/-! M19 of Order2: 3, 14, 16 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Order2 M19» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3, 14, 16] [2, 4, 5, 9, 10, 11, 13, 24, 25, 28, 31, 38, 39, 40, 41] :=
    ⟨Fin 3, «Order2 M19», Finite.of_fintype _,
      by decideFin!,
      by decideFin!,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!)⟩

end Order2
