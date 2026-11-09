import Mathlib.Data.Finite.Prod
import ExplorationLaws
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import equational_theories.EquationalResult
import CommutativeSemigroup5.SemigroupTables

set_option linter.unusedVariables false

namespace CommutativeSemigroup5

section
attribute [local instance] «CommutativeSemigroup5 M12»

theorem «CommutativeSemigroup5 M12 satisfies 41580 at 15» : ∀ y z w u : Fin 16, ((15 : Fin 16) ◇ (15 : Fin 16)) = ((15 : Fin 16) ◇ (y ◇ (z ◇ (w ◇ u)))) := by decideFin!

end

end CommutativeSemigroup5
