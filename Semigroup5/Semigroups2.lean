import Mathlib.Data.Finite.Prod
import ExplorationLaws
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import equational_theories.EquationalResult
import Semigroup5.SemigroupTables
import Semigroup5.SemigroupParts0
import Semigroup5.SemigroupParts1
import Semigroup5.SemigroupParts2
import Semigroup5.SemigroupParts3
import Semigroup5.SemigroupParts4
import Semigroup5.SemigroupParts5
import Semigroup5.SemigroupParts6
import Semigroup5.SemigroupParts7
import Semigroup5.SemigroupParts8
import Semigroup5.SemigroupParts9
import Semigroup5.SemigroupParts10
import Semigroup5.SemigroupParts11
import Semigroup5.SemigroupParts12
import Semigroup5.SemigroupParts13
import Semigroup5.SemigroupParts14
import Semigroup5.SemigroupParts15
import Semigroup5.SemigroupParts16
import Semigroup5.SemigroupParts17
import Semigroup5.SemigroupParts18
import Semigroup5.SemigroupParts19
import Semigroup5.SemigroupParts20
import Semigroup5.SemigroupParts21
import Semigroup5.SemigroupParts22
import Semigroup5.SemigroupParts23
import Semigroup5.SemigroupParts24
import Semigroup5.SemigroupParts25
import Semigroup5.SemigroupParts26
import Semigroup5.SemigroupParts27
import Semigroup5.SemigroupParts28
import Semigroup5.SemigroupParts29
import Semigroup5.SemigroupParts30
import Semigroup5.SemigroupParts31
import Semigroup5.SemigroupParts32
import Semigroup5.SemigroupParts33

set_option linter.unusedVariables false

namespace Semigroup5

/-! M55 of Semigroup5: 40, 43, 307, 4512 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Semigroup5 M55» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [40, 43, 307, 4512] [2, 3, 4, 5, 8, 10, 11, 14, 16, 38, 39, 41, 47, 56, 66, 73, 75, 311, 314, 318, 323, 325, 326, 327, 329, 333, 343, 411, 419, 429, 436, 440, 477, 504, 511, 513, 3267, 3300, 3304, 3306, 3308, 3309, 3315, 3316, 3319, 3322, 3323, 3326, 3331, 3334, 3342, 3345, 3346, 3353, 3355, 3370, 3388, 3414, 4271, 4274, 4278, 4300, 4339, 4360, 4695, 4798, 4949, 5097, 5099, 41580, 41671, 41726, 41733, 41735, 41743, 41745, 41769, 41773, 41783, 41790, 41799, 41833, 41849, 41883, 41887, 41897, 41931, 41933, 41999, 42197, 42223, 53821, 53854, 53858, 53878, 53892, 53905, 53946, 53985, 54029, 54037, 54113, 54140, 54160, 54180, 54188, 54194, 54287, 54291, 54318, 54331, 54335, 54337, 54338, 54339, 54340, 54343, 54350, 54351, 54352, 54370, 54395, 54398, 54408, 54472, 54485, 54550] :=
    ⟨Fin 32, «Semigroup5 M55», Finite.of_fintype _,
      by decideFin!,
      by decideFin!,
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
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 0 1 2) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 1 2 3 4) (by decideFin!),
      fun h => absurd (h 0 1 2 3 4) (by decideFin!),
      fun h => absurd (h 0 1 2 3 4) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 0 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2 0) (by decideFin!),
      fun h => absurd (h 0 1 2 0) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2 0) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2 0) (by decideFin!)⟩

section
attribute [local instance] «Semigroup5 M56»

theorem «Semigroup5 M56 satisfies 3267» : Equation3267 (Fin 26) :=
  fun x0 => match x0 with
    | ⟨0, _⟩ =>
      «Semigroup5 M56 satisfies 3267 at 0»
    | ⟨1, _⟩ =>
      «Semigroup5 M56 satisfies 3267 at 1»
    | ⟨2, _⟩ =>
      «Semigroup5 M56 satisfies 3267 at 2»
    | ⟨3, _⟩ =>
      «Semigroup5 M56 satisfies 3267 at 3»
    | ⟨4, _⟩ =>
      «Semigroup5 M56 satisfies 3267 at 4»
    | ⟨5, _⟩ =>
      «Semigroup5 M56 satisfies 3267 at 5»
    | ⟨6, _⟩ =>
      «Semigroup5 M56 satisfies 3267 at 6»
    | ⟨7, _⟩ =>
      «Semigroup5 M56 satisfies 3267 at 7»
    | ⟨8, _⟩ =>
      «Semigroup5 M56 satisfies 3267 at 8»
    | ⟨9, _⟩ =>
      «Semigroup5 M56 satisfies 3267 at 9»
    | ⟨10, _⟩ =>
      «Semigroup5 M56 satisfies 3267 at 10»
    | ⟨11, _⟩ =>
      «Semigroup5 M56 satisfies 3267 at 11»
    | ⟨12, _⟩ =>
      «Semigroup5 M56 satisfies 3267 at 12»
    | ⟨13, _⟩ =>
      «Semigroup5 M56 satisfies 3267 at 13»
    | ⟨14, _⟩ =>
      «Semigroup5 M56 satisfies 3267 at 14»
    | ⟨15, _⟩ =>
      «Semigroup5 M56 satisfies 3267 at 15»
    | ⟨16, _⟩ =>
      «Semigroup5 M56 satisfies 3267 at 16»
    | ⟨17, _⟩ =>
      «Semigroup5 M56 satisfies 3267 at 17»
    | ⟨18, _⟩ =>
      «Semigroup5 M56 satisfies 3267 at 18»
    | ⟨19, _⟩ =>
      «Semigroup5 M56 satisfies 3267 at 19»
    | ⟨20, _⟩ =>
      «Semigroup5 M56 satisfies 3267 at 20»
    | ⟨21, _⟩ =>
      «Semigroup5 M56 satisfies 3267 at 21»
    | ⟨22, _⟩ =>
      «Semigroup5 M56 satisfies 3267 at 22»
    | ⟨23, _⟩ =>
      «Semigroup5 M56 satisfies 3267 at 23»
    | ⟨24, _⟩ =>
      «Semigroup5 M56 satisfies 3267 at 24»
    | ⟨25, _⟩ =>
      «Semigroup5 M56 satisfies 3267 at 25»
    | ⟨_ + 26, h⟩ =>
      absurd h (by omega)

end
/-! M56 of Semigroup5: 43, 3267, 4512 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Semigroup5 M56» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [3267, 43, 4512] [2, 3, 4, 5, 8, 10, 11, 14, 16, 38, 39, 41, 47, 56, 66, 73, 75, 311, 314, 318, 323, 325, 326, 327, 329, 333, 343, 411, 419, 429, 436, 440, 477, 504, 511, 513, 3306, 3308, 3309, 3315, 3316, 3319, 3322, 3323, 3326, 3331, 3334, 3342, 3345, 3346, 3353, 3355, 3370, 3388, 3414, 4271, 4274, 4278, 4300, 4339, 4360, 4695, 4798, 4949, 5097, 5099, 41733, 41735, 41743, 41745, 41769, 41773, 41783, 41790, 41799, 41833, 41849, 41883, 41887, 41897, 41931, 41933, 41999, 42197, 42223, 54318, 54331, 54335, 54337, 54338, 54339, 54340, 54343, 54350, 54351, 54352, 54370, 54395, 54398, 54408, 54472, 54485, 54550] :=
    ⟨Fin 26, «Semigroup5 M56», Finite.of_fintype _,
      «Semigroup5 M56 satisfies 3267»,
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
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
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
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 0 1 2) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
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
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2 0) (by decideFin!),
      fun h => absurd (h 0 1 2 0) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2 0) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2 0) (by decideFin!)⟩

section
attribute [local instance] «Semigroup5 M57»

theorem «Semigroup5 M57 satisfies 41580» : Equation41580 (Fin 31) :=
  fun x0 => match x0 with
    | ⟨0, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 0 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨1, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 1 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨2, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 2 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨3, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 3 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨4, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 4 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨5, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 5 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨6, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 6 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨7, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 7 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨8, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 8 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨9, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 9 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨10, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 10 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨11, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 11 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨12, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 12 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨13, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 13 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨14, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 14 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨15, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 15 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨16, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 16 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨17, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 17 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨18, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 18 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨19, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 19 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨20, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 20 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨21, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 21 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨22, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 22 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨23, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 23 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨24, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 24 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨25, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 25 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨26, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 26 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨27, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 27 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨28, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 28 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨29, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 29 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨30, _⟩ =>
      fun x1 => match x1 with
        | ⟨0, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 0»
        | ⟨1, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 1»
        | ⟨2, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 2»
        | ⟨3, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 3»
        | ⟨4, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 4»
        | ⟨5, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 5»
        | ⟨6, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 6»
        | ⟨7, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 7»
        | ⟨8, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 8»
        | ⟨9, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 9»
        | ⟨10, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 10»
        | ⟨11, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 11»
        | ⟨12, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 12»
        | ⟨13, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 13»
        | ⟨14, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 14»
        | ⟨15, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 15»
        | ⟨16, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 16»
        | ⟨17, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 17»
        | ⟨18, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 18»
        | ⟨19, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 19»
        | ⟨20, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 20»
        | ⟨21, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 21»
        | ⟨22, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 22»
        | ⟨23, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 23»
        | ⟨24, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 24»
        | ⟨25, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 25»
        | ⟨26, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 26»
        | ⟨27, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 27»
        | ⟨28, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 28»
        | ⟨29, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 29»
        | ⟨30, _⟩ =>
          «Semigroup5 M57 satisfies 41580 at 30 30»
        | ⟨_ + 31, h⟩ =>
          absurd h (by omega)
    | ⟨_ + 31, h⟩ =>
      absurd h (by omega)

end
/-! M57 of Semigroup5: 43, 4512, 41580 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Semigroup5 M57» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [41580, 43, 4512] [2, 3, 4, 5, 8, 10, 11, 14, 16, 38, 39, 41, 47, 56, 66, 73, 75, 311, 314, 318, 323, 325, 326, 327, 329, 333, 343, 411, 419, 429, 436, 440, 477, 504, 511, 513, 3267, 3300, 3304, 3306, 3308, 3309, 3315, 3316, 3319, 3322, 3323, 3326, 3331, 3334, 3342, 3345, 3346, 3353, 3355, 3370, 3388, 3414, 4271, 4274, 4278, 4300, 4339, 4360, 4695, 4798, 4949, 5097, 5099, 41733, 41735, 41743, 41745, 41769, 41773, 41783, 41790, 41799, 41833, 41849, 41883, 41887, 41897, 41931, 41933, 41999, 42197, 42223, 53821, 53854, 53858, 53878, 53892, 53905, 53946, 53985, 54029, 54037, 54113, 54140, 54160, 54180, 54188, 54194, 54287, 54291, 54318, 54331, 54335, 54337, 54338, 54339, 54340, 54343, 54350, 54351, 54352, 54370, 54395, 54398, 54408, 54472, 54485, 54550] :=
    ⟨Fin 31, «Semigroup5 M57», Finite.of_fintype _,
      «Semigroup5 M57 satisfies 41580»,
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
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 0 1 2) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
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
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 0 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2 3) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2 0) (by decideFin!),
      fun h => absurd (h 0 1 2 0) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2 0) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2) (by decideFin!),
      fun h => absurd (h 0 1 2 0) (by decideFin!)⟩

/-! M58 of Semigroup5: 43, 4271, 4512 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Semigroup5 M58» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [43, 4271, 4512] [2, 3, 4, 5, 8, 10, 11, 14, 16, 38, 39, 40, 41, 47, 56, 66, 73, 75, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 318, 323, 325, 326, 327, 329, 333, 343, 411, 419, 429, 436, 440, 477, 504, 511, 513, 3253, 3255, 3256, 3258, 3259, 3260, 3261, 3264, 3265, 3267, 3271, 3273, 3274, 3278, 3290, 3292, 3300, 3301, 3304, 3306, 3308, 3309, 3315, 3316, 3319, 3322, 3323, 3326, 3331, 3334, 3342, 3345, 3346, 3353, 3355, 3370, 3388, 3414, 4695, 4798, 4949, 5097, 5099, 41529, 41534, 41538, 41547, 41548, 41550, 41551, 41553, 41557, 41565, 41566, 41567, 41568, 41571, 41576, 41577, 41578, 41580, 41585, 41592, 41597, 41600, 41602, 41604, 41605, 41607, 41608, 41613, 41619, 41621, 41628, 41659, 41661, 41667, 41668, 41671, 41674, 41684, 41685, 41708, 41709, 41711, 41716, 41726, 41733, 41735, 41743, 41745, 41769, 41773, 41783, 41790, 41799, 41833, 41849, 41883, 41887, 41897, 41931, 41933, 41999, 42197, 42223] :=
    ⟨Fin 28, «Semigroup5 M58», Finite.of_fintype _,
      by decideFin!,
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
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!),
      fun h => absurd (h 0 0 0) (by decideFin!)⟩

/-! M59 of Semigroup5: 43, 311, 4512 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Semigroup5 M59» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [43, 311, 4512] [2, 3, 4, 5, 8, 10, 11, 14, 16, 38, 39, 41, 47, 56, 66, 73, 75, 323, 325, 326, 327, 329, 333, 343, 411, 419, 429, 436, 440, 477, 504, 511, 513, 3306, 3308, 3309, 3315, 3316, 3319, 3322, 3323, 3326, 3331, 3334, 3342, 3345, 3346, 3353, 3355, 3370, 3388, 3414, 4695, 4798, 4949, 5097, 5099, 41733, 41735, 41743, 41745, 41769, 41773, 41783, 41790, 41799, 41833, 41849, 41883, 41887, 41897, 41931, 41933, 41999, 42197, 42223] :=
    ⟨Fin 22, «Semigroup5 M59», Finite.of_fintype _,
      by decideFin!,
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
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
      fun h => absurd (h 0 0) (by decideFin!),
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
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0) (by decideFin!),
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
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!)⟩

/-! M60 of Semigroup5: 56, 75, 4512 hold, and the others of its row follow -/
set_option maxRecDepth 10000 in
@[equational_result]
theorem «Facts from Semigroup5 M60» :
  ∃ (G : Type) (_ : Magma G) (_: Finite G), Facts G [56, 75, 4512] [2, 3, 4, 5, 8, 10, 11, 14, 16, 38, 39, 40, 41, 43, 66, 73, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 318, 323, 325, 326, 327, 329, 333, 343, 411, 419, 429, 436, 440, 477, 504, 511, 513, 3253, 3255, 3256, 3258, 3259, 3260, 3261, 3264, 3265, 3267, 3271, 3273, 3274, 3278, 3290, 3292, 3300, 3301, 3304, 3306, 3308, 3309, 3315, 3316, 3319, 3322, 3323, 3326, 3331, 3334, 3342, 3345, 3346, 3353, 3355, 3370, 3388, 3414, 4268, 4269, 4270, 4271, 4272, 4273, 4274, 4275, 4277, 4278, 4279, 4280, 4283, 4284, 4286, 4288, 4290, 4291, 4293, 4296, 4297, 4299, 4300, 4301, 4304, 4305, 4314, 4318, 4320, 4321, 4325, 4327, 4331, 4339, 4343, 4358, 4360, 4362, 4364, 4369, 4695, 4798, 4949, 5097, 5099, 41534, 41547, 41548, 41550, 41551, 41553, 41565, 41566, 41567, 41568, 41571, 41576, 41577, 41578, 41580, 41585, 41597, 41600, 41602, 41604, 41605, 41607, 41608, 41613, 41619, 41621, 41659, 41661, 41667, 41668, 41671, 41674, 41684, 41685, 41708, 41709, 41711, 41716, 41726, 41735, 41743, 41745, 41773, 41790, 41833, 41883, 41887, 41897, 41933, 41999, 42197, 53807, 53808, 53809, 53810, 53811, 53812, 53813, 53814, 53815, 53816, 53817, 53818, 53819, 53820, 53821, 53822, 53823, 53824, 53825, 53826, 53827, 53828, 53830, 53832, 53833, 53834, 53835, 53836, 53838, 53840, 53842, 53844, 53846, 53848, 53850, 53854, 53855, 53858, 53860, 53862, 53863, 53864, 53866, 53869, 53870, 53871, 53872, 53873, 53874, 53875, 53876, 53877, 53878, 53879, 53880, 53881, 53884, 53885, 53888, 53892, 53896, 53897, 53899, 53900, 53901, 53902, 53903, 53904, 53905, 53906, 53907, 53913, 53917, 53921, 53922, 53934, 53938, 53939, 53942, 53943, 53946, 53951, 53959, 53963, 53968, 53985, 54011, 54013, 54014, 54017, 54018, 54020, 54021, 54022, 54023, 54024, 54025, 54026, 54027, 54028, 54029, 54031, 54034, 54035, 54037, 54039, 54047, 54048, 54050, 54053, 54055, 54057, 54060, 54063, 54067, 54071, 54075, 54087, 54088, 54105, 54113, 54118, 54119, 54122, 54133, 54140, 54160, 54162, 54164, 54165, 54166, 54167, 54168, 54171, 54172, 54173, 54174, 54175, 54176, 54177, 54178, 54179, 54180, 54181, 54182, 54183, 54184, 54185, 54186, 54187, 54188, 54190, 54194, 54199, 54201, 54202, 54208, 54209, 54211, 54215, 54219, 54222, 54236, 54239, 54240, 54241, 54243, 54244, 54253, 54261, 54270, 54273, 54275, 54287, 54291, 54318, 54331, 54335, 54337, 54338, 54339, 54340, 54343, 54350, 54351, 54352, 54370, 54395, 54398, 54408, 54472, 54485, 54550] :=
    ⟨Fin 27, «Semigroup5 M60», Finite.of_fintype _,
      by decideFin!,
      by decideFin!,
      by decideFin!,
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 3 9) (by decideFin!),
      fun h => absurd (h 3 9) (by decideFin!),
      fun h => absurd (h 3 9) (by decideFin!),
      fun h => absurd (h 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 3 9) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 3 9) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 3 9) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 3 9) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 3 9 0) (by decideFin!),
      fun h => absurd (h 3 0 9) (by decideFin!),
      fun h => absurd (h 0 3 9) (by decideFin!),
      fun h => absurd (h 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 3 9) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 0 1) (by decideFin!),
      fun h => absurd (h 3 9) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 3 9) (by decideFin!),
      fun h => absurd (h 3 9) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 0 1) (by decideFin!),
      fun h => absurd (h 3 9) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 3 9) (by decideFin!),
      fun h => absurd (h 3 9) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 3 9) (by decideFin!),
      fun h => absurd (h 3 9) (by decideFin!),
      fun h => absurd (h 3 9 0) (by decideFin!),
      fun h => absurd (h 3 0 9) (by decideFin!),
      fun h => absurd (h 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 1 0) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 1 0 0) (by decideFin!),
      fun h => absurd (h 1 0 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 1 0 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 1 0 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 1 0) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 1) (by decideFin!),
      fun h => absurd (h 0 0 0 1) (by decideFin!)⟩

end Semigroup5
