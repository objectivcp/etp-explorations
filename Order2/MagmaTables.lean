import Mathlib.Data.Finite.Prod
import ExplorationLaws
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import equational_theories.EquationalResult

set_option linter.unusedVariables false

namespace Order2

@[implicit_reducible]
def «Order2 M1» : Magma (Fin 2) where
  op := finOpTable "[[0,0],[1,1]]"

@[implicit_reducible]
def «Order2 M1^op» : Magma (Fin 2) where
  op := finOpTable "[[0,1],[0,1]]"

@[implicit_reducible]
def «Order2 M2» : Magma (Fin 2) where
  op := finOpTable "[[0,0],[0,0]]"

@[implicit_reducible]
def «Order2 M3» : Magma (Fin 2) where
  op := finOpTable "[[0,1],[1,0]]"

@[implicit_reducible]
def «Order2 M4» : Magma (Fin 2) where
  op := finOpTable "[[0,0],[0,1]]"

@[implicit_reducible]
def «Order2 M5» : Magma (Fin 2) where
  op := finOpTable "[[1,1],[0,1]]"

@[implicit_reducible]
def «Order2 M5^op» : Magma (Fin 2) where
  op := finOpTable "[[1,0],[1,1]]"

@[implicit_reducible]
def «Order2 M6» : Magma (Fin 2) where
  op := finOpTable "[[1,1],[0,0]]"

@[implicit_reducible]
def «Order2 M6^op» : Magma (Fin 2) where
  op := finOpTable "[[1,0],[1,0]]"

@[implicit_reducible]
def «Order2 M7» : Magma (Fin 3) where
  op := finOpTable "[[2,0,1],[1,2,0],[0,1,2]]"

@[implicit_reducible]
def «Order2 M7^op» : Magma (Fin 3) where
  op := finOpTable "[[2,1,0],[0,2,1],[1,0,2]]"

@[implicit_reducible]
def «Order2 M8» : Magma (Fin 3) where
  op := finOpTable "[[2,1,0],[1,2,1],[0,1,2]]"

@[implicit_reducible]
def «Order2 M9» : Magma (Fin 3) where
  op := finOpTable "[[2,1,0],[1,0,1],[0,2,2]]"

@[implicit_reducible]
def «Order2 M9^op» : Magma (Fin 3) where
  op := finOpTable "[[2,1,0],[1,0,2],[0,1,2]]"

@[implicit_reducible]
def «Order2 M10» : Magma (Fin 3) where
  op := finOpTable "[[2,1,0],[1,0,2],[0,2,1]]"

@[implicit_reducible]
def «Order2 M11» : Magma (Fin 3) where
  op := finOpTable "[[0,0,2],[2,1,2],[0,1,2]]"

@[implicit_reducible]
def «Order2 M11^op» : Magma (Fin 3) where
  op := finOpTable "[[0,2,0],[0,1,1],[2,2,2]]"

@[implicit_reducible]
def «Order2 M12» : Magma (Fin 4) where
  op := finOpTable "[[0,3,1,2],[2,1,3,0],[3,0,2,1],[1,2,0,3]]"

@[implicit_reducible]
def «Order2 M13» : Magma (Fin 5) where
  op := finOpTable "[[4,3,1,2,0],[2,4,3,0,1],[3,0,4,1,2],[1,2,0,4,3],[0,1,2,3,4]]"

@[implicit_reducible]
def «Order2 M14» : Magma (Fin 3) where
  op := finOpTable "[[2,0,0],[1,2,1],[0,1,2]]"

@[implicit_reducible]
def «Order2 M14^op» : Magma (Fin 3) where
  op := finOpTable "[[2,1,0],[0,2,1],[0,1,2]]"

@[implicit_reducible]
def «Order2 M15» : Magma (Fin 3) where
  op := finOpTable "[[0,2,1],[2,1,2],[0,1,2]]"

@[implicit_reducible]
def «Order2 M15^op» : Magma (Fin 3) where
  op := finOpTable "[[0,2,0],[2,1,1],[1,2,2]]"

@[implicit_reducible]
def «Order2 M16» : Magma (Fin 3) where
  op := finOpTable "[[0,0,1],[2,1,0],[1,2,2]]"

@[implicit_reducible]
def «Order2 M16^op» : Magma (Fin 3) where
  op := finOpTable "[[0,2,1],[0,1,2],[1,0,2]]"

@[implicit_reducible]
def «Order2 M17» : Magma (Fin 3) where
  op := finOpTable "[[0,2,2],[2,1,2],[0,1,2]]"

@[implicit_reducible]
def «Order2 M17^op» : Magma (Fin 3) where
  op := finOpTable "[[0,2,0],[2,1,1],[2,2,2]]"

@[implicit_reducible]
def «Order2 M18» : Magma (Fin 3) where
  op := finOpTable "[[0,1,2],[2,1,0],[0,1,2]]"

@[implicit_reducible]
def «Order2 M18^op» : Magma (Fin 3) where
  op := finOpTable "[[0,2,0],[1,1,1],[2,0,2]]"

@[implicit_reducible]
def «Order2 M19» : Magma (Fin 3) where
  op := finOpTable "[[0,2,1],[2,1,0],[1,0,2]]"

end Order2
