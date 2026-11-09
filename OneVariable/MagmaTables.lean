import Mathlib.Data.Finite.Prod
import ExplorationLaws
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import equational_theories.EquationalResult

set_option linter.unusedVariables false

namespace OneVariable

@[implicit_reducible]
def «OneVariable M1» : Magma (Fin 2) where
  op := finOpTable "[[0,0],[0,0]]"

@[implicit_reducible]
def «OneVariable M2» : Magma (Fin 2) where
  op := finOpTable "[[0,1],[1,0]]"

@[implicit_reducible]
def «OneVariable M3» : Magma (Fin 2) where
  op := finOpTable "[[1,1],[1,0]]"

@[implicit_reducible]
def «OneVariable M4» : Magma (Fin 2) where
  op := finOpTable "[[1,1],[0,1]]"

@[implicit_reducible]
def «OneVariable M4^op» : Magma (Fin 2) where
  op := finOpTable "[[1,0],[1,1]]"

@[implicit_reducible]
def «OneVariable M5» : Magma (Fin 3) where
  op := finOpTable "[[0,1,2],[1,2,0],[2,0,1]]"

@[implicit_reducible]
def «OneVariable M11» : Magma (Fin 2) where
  op := finOpTable "[[1,1],[0,0]]"

@[implicit_reducible]
def «OneVariable M11^op» : Magma (Fin 2) where
  op := finOpTable "[[1,0],[1,0]]"

@[implicit_reducible]
def «OneVariable M28» : Magma (Fin 3) where
  op := finOpTable "[[1,1,0],[2,1,0],[0,1,2]]"

@[implicit_reducible]
def «OneVariable M28^op» : Magma (Fin 3) where
  op := finOpTable "[[1,2,0],[1,1,1],[0,0,2]]"

@[implicit_reducible]
def «OneVariable M35» : Magma (Fin 3) where
  op := finOpTable "[[2,1,0],[1,0,1],[0,2,2]]"

@[implicit_reducible]
def «OneVariable M35^op» : Magma (Fin 3) where
  op := finOpTable "[[2,1,0],[1,0,2],[0,1,2]]"

@[implicit_reducible]
def «OneVariable M39» : Magma (Fin 4) where
  op := finOpTable "[[2,0,3,2],[0,3,0,1],[3,1,2,2],[1,1,0,3]]"

@[implicit_reducible]
def «OneVariable M39^op» : Magma (Fin 4) where
  op := finOpTable "[[2,0,3,1],[0,3,1,1],[3,0,2,0],[2,1,2,3]]"

@[implicit_reducible]
def «OneVariable M141» : Magma (Fin 3) where
  op := finOpTable "[[0,1,1],[2,1,2],[2,0,0]]"

@[implicit_reducible]
def «OneVariable M141^op» : Magma (Fin 3) where
  op := finOpTable "[[0,2,2],[1,1,0],[1,2,0]]"

@[implicit_reducible]
def «OneVariable M145» : Magma (Fin 3) where
  op := finOpTable "[[2,2,1],[2,1,0],[1,2,2]]"

@[implicit_reducible]
def «OneVariable M145^op» : Magma (Fin 3) where
  op := finOpTable "[[2,2,1],[2,1,2],[1,0,2]]"

@[implicit_reducible]
def «OneVariable M149» : Magma (Fin 3) where
  op := finOpTable "[[0,2,0],[1,0,0],[1,0,2]]"

@[implicit_reducible]
def «OneVariable M149^op» : Magma (Fin 3) where
  op := finOpTable "[[0,1,1],[2,0,0],[0,0,2]]"

@[implicit_reducible]
def «OneVariable M151» : Magma (Fin 3) where
  op := finOpTable "[[0,2,1],[0,0,0],[1,0,2]]"

@[implicit_reducible]
def «OneVariable M151^op» : Magma (Fin 3) where
  op := finOpTable "[[0,0,1],[2,0,0],[1,0,2]]"

@[implicit_reducible]
def «OneVariable M175» : Magma (Fin 4) where
  op := finOpTable "[[1,1,1,0],[2,1,0,0],[3,0,2,0],[0,1,3,3]]"

@[implicit_reducible]
def «OneVariable M175^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[1,1,0,1],[1,0,2,3],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M177» : Magma (Fin 3) where
  op := finOpTable "[[1,1,0],[2,1,1],[0,0,2]]"

@[implicit_reducible]
def «OneVariable M177^op» : Magma (Fin 3) where
  op := finOpTable "[[1,2,0],[1,1,0],[0,1,2]]"

@[implicit_reducible]
def «OneVariable M178» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,0],[2,1,0,0],[3,0,2,0],[0,2,0,3]]"

@[implicit_reducible]
def «OneVariable M178^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[2,1,0,2],[0,0,2,0],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M188» : Magma (Fin 3) where
  op := finOpTable "[[1,1,1],[2,1,1],[0,0,2]]"

@[implicit_reducible]
def «OneVariable M188^op» : Magma (Fin 3) where
  op := finOpTable "[[1,2,0],[1,1,0],[1,1,2]]"

@[implicit_reducible]
def «OneVariable M204» : Magma (Fin 4) where
  op := finOpTable "[[0,2,2,3],[2,1,3,2],[2,0,0,1],[3,2,3,2]]"

@[implicit_reducible]
def «OneVariable M204^op» : Magma (Fin 4) where
  op := finOpTable "[[0,2,2,3],[2,1,0,2],[2,3,0,3],[3,2,1,2]]"

@[implicit_reducible]
def «OneVariable M209» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[2,3,0,1],[3,0,2,1],[0,1,2,3]]"

@[implicit_reducible]
def «OneVariable M225» : Magma (Fin 4) where
  op := finOpTable "[[1,2,1,0],[2,3,2,1],[3,0,2,1],[0,1,1,3]]"

@[implicit_reducible]
def «OneVariable M225^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[2,3,0,1],[1,2,2,1],[0,1,1,3]]"

@[implicit_reducible]
def «OneVariable M231» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,2],[3,0,0,2],[0,1,2,3],[1,0,2,3]]"

@[implicit_reducible]
def «OneVariable M231^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,1],[3,0,1,0],[0,0,2,2],[2,2,3,3]]"

@[implicit_reducible]
def «OneVariable M236» : Magma (Fin 4) where
  op := finOpTable "[[1,0,1,3],[0,1,3,2],[0,3,2,1],[0,2,0,1]]"

@[implicit_reducible]
def «OneVariable M236^op» : Magma (Fin 4) where
  op := finOpTable "[[1,0,0,0],[0,1,3,2],[1,3,2,0],[3,2,1,1]]"

@[implicit_reducible]
def «OneVariable M240» : Magma (Fin 4) where
  op := finOpTable "[[1,1,0,2],[3,1,1,0],[0,1,2,0],[2,0,1,3]]"

@[implicit_reducible]
def «OneVariable M240^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,2],[1,1,1,0],[0,1,2,1],[2,0,0,3]]"

@[implicit_reducible]
def «OneVariable M243» : Magma (Fin 4) where
  op := finOpTable "[[2,2,0,1],[2,3,1,1],[0,1,2,1],[3,0,2,3]]"

@[implicit_reducible]
def «OneVariable M243^op» : Magma (Fin 4) where
  op := finOpTable "[[2,2,0,3],[2,3,1,0],[0,1,2,2],[1,1,1,3]]"

@[implicit_reducible]
def «OneVariable M256» : Magma (Fin 4) where
  op := finOpTable "[[1,0,3,0],[2,3,2,1],[1,0,3,2],[0,1,2,3]]"

@[implicit_reducible]
def «OneVariable M256^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,1,0],[0,3,0,1],[3,2,3,2],[0,1,2,3]]"

@[implicit_reducible]
def «OneVariable M269» : Magma (Fin 4) where
  op := finOpTable "[[0,1,0,3],[1,3,0,2],[0,0,2,1],[3,2,3,0]]"

@[implicit_reducible]
def «OneVariable M269^op» : Magma (Fin 4) where
  op := finOpTable "[[0,1,0,3],[1,3,0,2],[0,0,2,3],[3,2,1,0]]"

@[implicit_reducible]
def «OneVariable M285» : Magma (Fin 5) where
  op := finOpTable "[[2,2,3,1,2],[0,1,2,3,1],[4,1,0,0,1],[2,1,0,3,4],[2,1,0,3,4]]"

@[implicit_reducible]
def «OneVariable M285^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,4,2,2],[2,1,1,1,1],[3,2,0,0,0],[1,3,0,3,3],[2,1,1,4,4]]"

@[implicit_reducible]
def «OneVariable M319» : Magma (Fin 4) where
  op := finOpTable "[[3,2,0,1],[2,1,2,0],[0,2,1,2],[1,1,2,3]]"

@[implicit_reducible]
def «OneVariable M319^op» : Magma (Fin 4) where
  op := finOpTable "[[3,2,0,1],[2,1,2,1],[0,2,1,2],[1,0,2,3]]"

@[implicit_reducible]
def «OneVariable M334» : Magma (Fin 3) where
  op := finOpTable "[[0,1,1],[2,0,0],[1,0,2]]"

@[implicit_reducible]
def «OneVariable M334^op» : Magma (Fin 3) where
  op := finOpTable "[[0,2,1],[1,0,0],[1,0,2]]"

@[implicit_reducible]
def «OneVariable M341» : Magma (Fin 3) where
  op := finOpTable "[[2,2,1],[2,1,0],[0,2,2]]"

@[implicit_reducible]
def «OneVariable M341^op» : Magma (Fin 3) where
  op := finOpTable "[[2,2,0],[2,1,2],[1,0,2]]"

@[implicit_reducible]
def «OneVariable M351» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,2],[2,1,0,0],[0,1,2,3],[1,0,2,3]]"

@[implicit_reducible]
def «OneVariable M351^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,1],[3,1,1,0],[0,0,2,2],[2,0,3,3]]"

@[implicit_reducible]
def «OneVariable M355» : Magma (Fin 4) where
  op := finOpTable "[[2,1,0,2],[1,2,3,0],[0,1,2,2],[3,2,1,3]]"

@[implicit_reducible]
def «OneVariable M355^op» : Magma (Fin 4) where
  op := finOpTable "[[2,1,0,3],[1,2,1,2],[0,3,2,1],[2,0,2,3]]"

@[implicit_reducible]
def «OneVariable M407» : Magma (Fin 5) where
  op := finOpTable "[[2,1,3,2,1],[0,1,2,3,4],[4,1,0,1,0],[2,1,0,3,4],[2,1,0,3,4]]"

@[implicit_reducible]
def «OneVariable M407^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,4,2,2],[1,1,1,1,1],[3,2,0,0,0],[2,3,1,3,3],[1,4,0,4,4]]"

@[implicit_reducible]
def «OneVariable M434» : Magma (Fin 5) where
  op := finOpTable "[[3,3,3,0,4],[1,1,4,3,0],[2,4,2,3,1],[0,4,4,3,2],[4,2,3,0,2]]"

@[implicit_reducible]
def «OneVariable M434^op» : Magma (Fin 5) where
  op := finOpTable "[[3,1,2,0,4],[3,1,4,4,2],[3,4,2,4,3],[0,3,3,3,0],[4,0,1,2,2]]"

@[implicit_reducible]
def «OneVariable M474» : Magma (Fin 3) where
  op := finOpTable "[[1,1,1],[2,1,0],[0,1,2]]"

@[implicit_reducible]
def «OneVariable M474^op» : Magma (Fin 3) where
  op := finOpTable "[[1,2,0],[1,1,1],[1,0,2]]"

@[implicit_reducible]
def «OneVariable M477» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,1],[3,1,1,0],[0,1,2,2],[2,3,3,3]]"

@[implicit_reducible]
def «OneVariable M477^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,2],[3,1,1,3],[0,1,2,3],[1,0,2,3]]"

@[implicit_reducible]
def «OneVariable M481» : Magma (Fin 4) where
  op := finOpTable "[[1,0,3,0],[2,3,0,1],[3,0,2,0],[0,1,0,3]]"

@[implicit_reducible]
def «OneVariable M481^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[0,3,0,1],[3,0,2,0],[0,1,0,3]]"

@[implicit_reducible]
def «OneVariable M489» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,1],[3,2,1,0],[0,1,2,3],[2,1,3,2]]"

@[implicit_reducible]
def «OneVariable M489^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,2],[3,2,1,1],[0,1,2,3],[1,0,3,2]]"

@[implicit_reducible]
def «OneVariable M511» : Magma (Fin 3) where
  op := finOpTable "[[0,2,1],[2,1,0],[1,0,0]]"

@[implicit_reducible]
def «OneVariable M517» : Magma (Fin 4) where
  op := finOpTable "[[1,0,1,0],[2,1,0,1],[3,0,2,2],[0,1,3,3]]"

@[implicit_reducible]
def «OneVariable M517^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[0,1,0,1],[1,0,2,3],[0,1,2,3]]"

@[implicit_reducible]
def «OneVariable M523» : Magma (Fin 4) where
  op := finOpTable "[[1,0,1,3],[2,1,0,1],[3,0,3,2],[0,1,2,3]]"

@[implicit_reducible]
def «OneVariable M523^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[0,1,0,1],[1,0,3,2],[3,1,2,3]]"

@[implicit_reducible]
def «OneVariable M528» : Magma (Fin 3) where
  op := finOpTable "[[1,1,0],[2,1,0],[0,0,2]]"

@[implicit_reducible]
def «OneVariable M528^op» : Magma (Fin 3) where
  op := finOpTable "[[1,2,0],[1,1,0],[0,0,2]]"

@[implicit_reducible]
def «OneVariable M531» : Magma (Fin 3) where
  op := finOpTable "[[1,1,1],[2,1,0],[0,0,2]]"

@[implicit_reducible]
def «OneVariable M531^op» : Magma (Fin 3) where
  op := finOpTable "[[1,2,0],[1,1,0],[1,0,2]]"

@[implicit_reducible]
def «OneVariable M537» : Magma (Fin 4) where
  op := finOpTable "[[1,2,1,0],[2,1,0,1],[3,0,3,2],[0,1,2,3]]"

@[implicit_reducible]
def «OneVariable M537^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[2,1,0,1],[1,0,3,2],[0,1,2,3]]"

@[implicit_reducible]
def «OneVariable M540» : Magma (Fin 4) where
  op := finOpTable "[[1,2,1,3],[2,1,0,2],[3,0,3,2],[0,0,2,3]]"

@[implicit_reducible]
def «OneVariable M540^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[2,1,0,0],[1,0,3,2],[3,2,2,3]]"

@[implicit_reducible]
def «OneVariable M548» : Magma (Fin 4) where
  op := finOpTable "[[1,0,0,1],[3,2,1,0],[0,1,2,2],[1,0,3,3]]"

@[implicit_reducible]
def «OneVariable M548^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,1],[0,2,1,0],[0,1,2,3],[1,0,2,3]]"

@[implicit_reducible]
def «OneVariable M553» : Magma (Fin 4) where
  op := finOpTable "[[2,3,0,1],[1,0,1,0],[0,1,2,2],[1,2,3,3]]"

@[implicit_reducible]
def «OneVariable M553^op» : Magma (Fin 4) where
  op := finOpTable "[[2,1,0,1],[3,0,1,2],[0,1,2,3],[1,0,2,3]]"

@[implicit_reducible]
def «OneVariable M556» : Magma (Fin 4) where
  op := finOpTable "[[1,2,1,0],[2,3,0,1],[3,0,3,2],[0,1,2,3]]"

@[implicit_reducible]
def «OneVariable M556^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[2,3,0,1],[1,0,3,2],[0,1,2,3]]"

@[implicit_reducible]
def «OneVariable M572» : Magma (Fin 3) where
  op := finOpTable "[[1,0,2],[2,1,0],[0,0,2]]"

@[implicit_reducible]
def «OneVariable M572^op» : Magma (Fin 3) where
  op := finOpTable "[[1,2,0],[0,1,0],[2,0,2]]"

@[implicit_reducible]
def «OneVariable M573» : Magma (Fin 4) where
  op := finOpTable "[[1,0,3,1],[2,1,0,3],[1,0,2,0],[0,3,2,1]]"

@[implicit_reducible]
def «OneVariable M573^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,1,0],[0,1,0,3],[3,0,2,2],[1,3,0,1]]"

@[implicit_reducible]
def «OneVariable M580» : Magma (Fin 5) where
  op := finOpTable "[[2,0,0,0,3],[0,1,2,3,4],[0,2,2,4,1],[4,3,4,3,2],[3,4,1,0,3]]"

@[implicit_reducible]
def «OneVariable M580^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,0,4,3],[0,1,2,3,4],[0,2,2,4,1],[0,3,4,3,0],[3,4,1,2,3]]"

@[implicit_reducible]
def «OneVariable M581» : Magma (Fin 3) where
  op := finOpTable "[[1,1,2],[2,1,0],[0,0,2]]"

@[implicit_reducible]
def «OneVariable M581^op» : Magma (Fin 3) where
  op := finOpTable "[[1,2,0],[1,1,0],[2,0,2]]"

@[implicit_reducible]
def «OneVariable M590» : Magma (Fin 4) where
  op := finOpTable "[[1,2,2,0],[3,1,0,0],[0,0,2,0],[1,0,2,3]]"

@[implicit_reducible]
def «OneVariable M590^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,1],[2,1,0,0],[2,0,2,2],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M690» : Magma (Fin 5) where
  op := finOpTable "[[3,0,1,4,3],[0,1,2,3,2],[3,1,2,0,3],[2,3,0,1,0],[3,3,2,0,4]]"

@[implicit_reducible]
def «OneVariable M690^op» : Magma (Fin 5) where
  op := finOpTable "[[3,0,3,2,3],[0,1,1,3,3],[1,2,2,0,2],[4,3,0,1,0],[3,2,3,0,4]]"

@[implicit_reducible]
def «OneVariable M698» : Magma (Fin 5) where
  op := finOpTable "[[3,3,4,0,2],[2,1,2,3,4],[4,1,2,4,0],[0,4,4,3,2],[2,1,3,1,2]]"

@[implicit_reducible]
def «OneVariable M698^op» : Magma (Fin 5) where
  op := finOpTable "[[3,2,4,0,2],[3,1,1,4,1],[4,2,2,4,3],[0,3,4,3,1],[2,4,0,2,2]]"

@[implicit_reducible]
def «OneVariable M882» : Magma (Fin 4) where
  op := finOpTable "[[2,1,0,1],[3,0,1,0],[0,1,2,2],[1,2,2,3]]"

@[implicit_reducible]
def «OneVariable M882^op» : Magma (Fin 4) where
  op := finOpTable "[[2,3,0,1],[1,0,1,2],[0,1,2,2],[1,0,2,3]]"

@[implicit_reducible]
def «OneVariable M901» : Magma (Fin 4) where
  op := finOpTable "[[1,3,1,0],[2,1,3,0],[1,0,2,0],[1,0,0,3]]"

@[implicit_reducible]
def «OneVariable M901^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,1,1],[3,1,0,0],[1,3,2,0],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M905» : Magma (Fin 4) where
  op := finOpTable "[[2,3,0,1],[3,3,3,0],[0,3,0,1],[1,2,1,1]]"

@[implicit_reducible]
def «OneVariable M908» : Magma (Fin 4) where
  op := finOpTable "[[2,2,3,2],[2,1,0,3],[1,1,2,0],[0,2,0,3]]"

@[implicit_reducible]
def «OneVariable M908^op» : Magma (Fin 4) where
  op := finOpTable "[[2,2,1,0],[2,1,1,2],[3,0,2,0],[2,3,0,3]]"

@[implicit_reducible]
def «OneVariable M910» : Magma (Fin 4) where
  op := finOpTable "[[1,3,1,1],[2,1,0,0],[1,0,2,0],[1,0,0,3]]"

@[implicit_reducible]
def «OneVariable M911» : Magma (Fin 4) where
  op := finOpTable "[[1,3,1,1],[2,1,3,0],[1,0,2,0],[1,0,0,3]]"

@[implicit_reducible]
def «OneVariable M911^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,1,1],[3,1,0,0],[1,3,2,0],[1,0,0,3]]"

@[implicit_reducible]
def «OneVariable M916» : Magma (Fin 5) where
  op := finOpTable "[[1,3,1,1,0],[2,1,1,0,2],[4,0,2,4,4],[1,0,4,3,2],[0,0,4,2,2]]"

@[implicit_reducible]
def «OneVariable M916^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,1,0],[3,1,0,0,0],[1,1,2,4,4],[1,0,4,3,2],[0,2,4,2,2]]"

@[implicit_reducible]
def «OneVariable M934» : Magma (Fin 5) where
  op := finOpTable "[[1,3,1,1,0],[2,4,2,0,1],[1,0,3,2,3],[4,0,2,3,2],[0,1,0,4,4]]"

@[implicit_reducible]
def «OneVariable M934^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,4,0],[3,4,0,0,1],[1,2,3,2,0],[1,0,2,3,4],[0,1,3,2,4]]"

@[implicit_reducible]
def «OneVariable M943» : Magma (Fin 5) where
  op := finOpTable "[[1,0,4,1,3],[0,1,4,0,2],[4,4,2,3,0],[1,0,3,2,4],[3,2,1,4,2]]"

@[implicit_reducible]
def «OneVariable M943^op» : Magma (Fin 5) where
  op := finOpTable "[[1,0,4,1,3],[0,1,4,0,2],[4,4,2,3,1],[1,0,3,2,4],[3,2,0,4,2]]"

@[implicit_reducible]
def «OneVariable M961» : Magma (Fin 5) where
  op := finOpTable "[[0,1,2,3,4],[1,0,3,2,2],[2,4,1,0,0],[2,2,0,3,4],[1,2,1,4,3]]"

@[implicit_reducible]
def «OneVariable M961^op» : Magma (Fin 5) where
  op := finOpTable "[[0,1,2,2,1],[1,0,4,2,2],[2,3,1,0,1],[3,2,0,3,4],[4,2,0,4,3]]"

@[implicit_reducible]
def «OneVariable M974» : Magma (Fin 5) where
  op := finOpTable "[[1,0,4,2,1],[0,1,2,3,4],[3,2,0,1,1],[2,1,0,3,4],[2,2,1,4,3]]"

@[implicit_reducible]
def «OneVariable M974^op» : Magma (Fin 5) where
  op := finOpTable "[[1,0,3,2,2],[0,1,2,1,2],[4,2,0,0,1],[2,3,1,3,4],[1,4,1,4,3]]"

@[implicit_reducible]
def «OneVariable M980» : Magma (Fin 4) where
  op := finOpTable "[[2,3,0,0],[3,3,1,0],[0,1,2,3],[1,0,3,2]]"

@[implicit_reducible]
def «OneVariable M980^op» : Magma (Fin 4) where
  op := finOpTable "[[2,3,0,1],[3,3,1,0],[0,1,2,3],[0,0,3,2]]"

@[implicit_reducible]
def «OneVariable M989» : Magma (Fin 5) where
  op := finOpTable "[[1,0,4,3,3],[0,1,4,0,2],[4,4,2,3,0],[2,2,3,2,4],[2,2,1,3,2]]"

@[implicit_reducible]
def «OneVariable M989^op» : Magma (Fin 5) where
  op := finOpTable "[[1,0,4,2,2],[0,1,4,2,2],[4,4,2,3,1],[3,0,3,2,3],[3,2,0,4,2]]"

@[implicit_reducible]
def «OneVariable M1037» : Magma (Fin 4) where
  op := finOpTable "[[3,1,0,0],[1,2,3,2],[0,1,2,1],[0,0,1,3]]"

@[implicit_reducible]
def «OneVariable M1037^op» : Magma (Fin 4) where
  op := finOpTable "[[3,1,0,0],[1,2,1,0],[0,3,2,1],[0,2,1,3]]"

@[implicit_reducible]
def «OneVariable M1048» : Magma (Fin 5) where
  op := finOpTable "[[1,4,1,2,1],[2,1,0,2,0],[1,0,2,3,3],[0,2,3,2,2],[3,0,3,2,4]]"

@[implicit_reducible]
def «OneVariable M1048^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,0,3],[4,1,0,2,0],[1,0,2,3,3],[2,2,3,2,2],[1,0,3,2,4]]"

@[implicit_reducible]
def «OneVariable M1052» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,1,1],[2,1,0,0,0],[1,0,2,4,3],[0,4,4,3,4],[1,0,3,4,3]]"

@[implicit_reducible]
def «OneVariable M1052^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,0,1],[4,1,0,4,0],[3,0,2,4,3],[1,0,4,3,4],[1,0,3,4,3]]"

@[implicit_reducible]
def «OneVariable M1148» : Magma (Fin 5) where
  op := finOpTable "[[2,3,0,1,1],[4,0,1,0,0],[0,1,2,1,2],[1,2,1,3,3],[0,2,1,1,4]]"

@[implicit_reducible]
def «OneVariable M1148^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,0,1,0],[3,0,1,2,2],[0,1,2,1,1],[1,0,1,3,1],[1,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M1159» : Magma (Fin 4) where
  op := finOpTable "[[1,0,1,0],[2,3,2,1],[3,0,2,2],[0,1,3,3]]"

@[implicit_reducible]
def «OneVariable M1159^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[0,3,0,1],[1,2,2,3],[0,1,2,3]]"

@[implicit_reducible]
def «OneVariable M1167» : Magma (Fin 5) where
  op := finOpTable "[[1,0,3,3,0],[2,1,0,0,4],[4,0,2,3,1],[0,1,2,3,1],[0,4,2,3,1]]"

@[implicit_reducible]
def «OneVariable M1167^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,0,0],[0,1,0,1,4],[3,0,2,2,2],[3,0,3,3,3],[0,4,1,1,1]]"

@[implicit_reducible]
def «OneVariable M1178» : Magma (Fin 4) where
  op := finOpTable "[[2,2,0,1],[3,2,1,2],[0,1,2,3],[3,2,3,0]]"

@[implicit_reducible]
def «OneVariable M1178^op» : Magma (Fin 4) where
  op := finOpTable "[[2,3,0,3],[2,2,1,2],[0,1,2,3],[1,2,3,0]]"

@[implicit_reducible]
def «OneVariable M1331» : Magma (Fin 5) where
  op := finOpTable "[[1,0,4,4,1],[0,1,4,3,4],[0,3,2,4,0],[1,3,4,1,1],[2,4,3,1,2]]"

@[implicit_reducible]
def «OneVariable M1331^op» : Magma (Fin 5) where
  op := finOpTable "[[1,0,0,1,2],[0,1,3,3,4],[4,4,2,4,3],[4,3,4,1,1],[1,4,0,1,2]]"

@[implicit_reducible]
def «OneVariable M1332» : Magma (Fin 5) where
  op := finOpTable "[[2,2,0,1,1],[2,3,1,0,3],[0,1,2,1,1],[2,4,1,3,1],[2,2,2,1,4]]"

@[implicit_reducible]
def «OneVariable M1332^op» : Magma (Fin 5) where
  op := finOpTable "[[2,2,0,2,2],[2,3,1,4,2],[0,1,2,1,2],[1,0,1,3,1],[1,3,1,1,4]]"

@[implicit_reducible]
def «OneVariable M1369» : Magma (Fin 4) where
  op := finOpTable "[[1,0,1,0],[2,3,0,1],[3,2,2,2],[0,1,3,3]]"

@[implicit_reducible]
def «OneVariable M1369^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[0,3,2,1],[1,0,2,3],[0,1,2,3]]"

@[implicit_reducible]
def «OneVariable M1372» : Magma (Fin 4) where
  op := finOpTable "[[1,0,3,0],[2,1,0,1],[3,1,2,3],[0,0,3,2]]"

@[implicit_reducible]
def «OneVariable M1372^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[0,1,1,0],[3,0,2,3],[0,1,3,2]]"

@[implicit_reducible]
def «OneVariable M1383» : Magma (Fin 4) where
  op := finOpTable "[[1,0,3,0],[2,3,0,1],[3,1,2,2],[0,1,2,3]]"

@[implicit_reducible]
def «OneVariable M1383^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[0,3,1,1],[3,0,2,2],[0,1,2,3]]"

@[implicit_reducible]
def «OneVariable M1441» : Magma (Fin 5) where
  op := finOpTable "[[1,0,2,2,3],[0,1,3,2,2],[2,4,1,1,0],[2,2,0,3,4],[1,0,0,4,3]]"

@[implicit_reducible]
def «OneVariable M1441^op» : Magma (Fin 5) where
  op := finOpTable "[[1,0,2,2,1],[0,1,4,2,0],[2,3,1,0,0],[2,2,1,3,4],[3,2,0,4,3]]"

@[implicit_reducible]
def «OneVariable M1457» : Magma (Fin 5) where
  op := finOpTable "[[2,1,3,1,0],[0,1,0,4,2],[3,4,2,0,4],[4,4,0,3,1],[0,2,4,1,3]]"

@[implicit_reducible]
def «OneVariable M1457^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,3,4,0],[1,1,4,4,2],[3,0,2,0,4],[1,4,0,3,1],[0,2,4,1,3]]"

@[implicit_reducible]
def «OneVariable M1467» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,1,0],[3,1,0,0,0],[1,0,2,2,4],[4,3,3,3,4],[0,2,4,4,2]]"

@[implicit_reducible]
def «OneVariable M1467^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,1,4,0],[2,1,0,3,2],[1,0,2,3,4],[1,0,2,3,4],[0,0,4,4,2]]"

@[implicit_reducible]
def «OneVariable M1469» : Magma (Fin 5) where
  op := finOpTable "[[0,2,1,2,1],[4,0,0,1,0],[3,3,3,2,2],[2,1,2,3,2],[1,3,2,2,4]]"

@[implicit_reducible]
def «OneVariable M1469^op» : Magma (Fin 5) where
  op := finOpTable "[[0,4,3,2,1],[2,0,3,1,3],[1,0,3,2,2],[2,1,2,3,2],[1,0,2,2,4]]"

@[implicit_reducible]
def «OneVariable M1470» : Magma (Fin 5) where
  op := finOpTable "[[0,4,2,1,0],[3,3,3,0,1],[2,4,0,1,1],[3,2,1,3,1],[4,1,1,1,4]]"

@[implicit_reducible]
def «OneVariable M1470^op» : Magma (Fin 5) where
  op := finOpTable "[[0,3,2,3,4],[4,3,4,2,1],[2,3,0,1,1],[1,0,1,3,1],[0,1,1,1,4]]"

@[implicit_reducible]
def «OneVariable M1486» : Magma (Fin 5) where
  op := finOpTable "[[2,4,0,3,3],[4,1,4,0,2],[0,3,2,3,3],[2,0,3,2,4],[1,0,3,4,1]]"

@[implicit_reducible]
def «OneVariable M1486^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,0,2,1],[4,1,3,0,0],[0,4,2,3,3],[3,0,3,2,4],[3,2,3,4,1]]"

@[implicit_reducible]
def «OneVariable M1509» : Magma (Fin 5) where
  op := finOpTable "[[1,0,3,2,3],[0,1,4,2,2],[4,4,3,0,2],[4,2,1,3,4],[2,1,2,4,3]]"

@[implicit_reducible]
def «OneVariable M1509^op» : Magma (Fin 5) where
  op := finOpTable "[[1,0,4,4,2],[0,1,4,2,1],[3,4,3,1,2],[2,2,0,3,4],[3,2,2,4,3]]"

@[implicit_reducible]
def «OneVariable M1513» : Magma (Fin 5) where
  op := finOpTable "[[0,4,3,4,1],[4,1,3,4,2],[3,3,2,1,4],[4,4,0,2,3],[1,2,4,3,0]]"

@[implicit_reducible]
def «OneVariable M1516» : Magma (Fin 5) where
  op := finOpTable "[[1,0,1,0,1],[0,1,2,3,2],[1,2,4,1,3],[1,3,1,1,2],[2,2,0,2,4]]"

@[implicit_reducible]
def «OneVariable M1516^op» : Magma (Fin 5) where
  op := finOpTable "[[1,0,1,1,2],[0,1,2,3,2],[1,2,4,1,0],[0,3,1,1,2],[1,2,3,2,4]]"

@[implicit_reducible]
def «OneVariable M1538» : Magma (Fin 5) where
  op := finOpTable "[[1,0,4,1,1],[0,1,3,3,4],[4,4,2,0,0],[1,3,4,1,1],[1,4,3,2,2]]"

@[implicit_reducible]
def «OneVariable M1538^op» : Magma (Fin 5) where
  op := finOpTable "[[1,0,4,1,1],[0,1,4,3,4],[4,3,2,4,3],[1,3,0,1,2],[1,4,0,1,2]]"

@[implicit_reducible]
def «OneVariable M1575» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,3,0],[4,1,0,5,0,2],[3,0,2,1,1,5],[0,5,5,3,0,1],[5,0,0,3,4,1],[5,2,5,1,0,3]]"

@[implicit_reducible]
def «OneVariable M1575^op» : Magma (Fin 6) where
  op := finOpTable "[[1,4,3,0,5,5],[2,1,0,5,0,2],[3,0,2,5,0,5],[0,5,1,3,3,1],[3,0,1,0,4,0],[0,2,5,1,1,3]]"

@[implicit_reducible]
def «OneVariable M1579» : Magma (Fin 5) where
  op := finOpTable "[[2,0,4,1,1],[0,1,2,3,4],[3,2,1,0,4],[1,3,0,1,0],[2,4,0,0,1]]"

@[implicit_reducible]
def «OneVariable M1579^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,3,1,2],[0,1,2,3,4],[4,2,1,0,0],[1,3,0,1,0],[1,4,4,0,1]]"

@[implicit_reducible]
def «OneVariable M1583» : Magma (Fin 5) where
  op := finOpTable "[[2,3,0,1,1],[3,1,2,2,2],[0,2,2,3,4],[4,2,3,0,2],[3,0,4,2,2]]"

@[implicit_reducible]
def «OneVariable M1583^op» : Magma (Fin 5) where
  op := finOpTable "[[2,3,0,4,3],[3,1,2,2,0],[0,2,2,3,4],[1,2,3,0,2],[1,2,4,2,2]]"

@[implicit_reducible]
def «OneVariable M1637» : Magma (Fin 5) where
  op := finOpTable "[[0,4,4,1,2],[3,3,3,2,1],[4,4,2,1,3],[3,0,1,3,4],[2,1,0,4,0]]"

@[implicit_reducible]
def «OneVariable M1637^op» : Magma (Fin 5) where
  op := finOpTable "[[0,3,4,3,2],[4,3,4,0,1],[4,3,2,1,0],[1,2,1,3,4],[2,1,3,4,0]]"

@[implicit_reducible]
def «OneVariable M1639» : Magma (Fin 5) where
  op := finOpTable "[[0,2,1,1,1],[4,0,0,1,0],[1,3,3,2,2],[1,1,2,3,0],[0,3,2,1,4]]"

@[implicit_reducible]
def «OneVariable M1639^op» : Magma (Fin 5) where
  op := finOpTable "[[0,4,1,1,0],[2,0,3,1,3],[1,0,3,2,2],[1,1,2,3,1],[1,0,2,0,4]]"

@[implicit_reducible]
def «OneVariable M1652» : Magma (Fin 5) where
  op := finOpTable "[[2,2,1,0,2],[2,1,0,3,4],[4,0,3,2,4],[0,3,2,3,4],[3,2,0,4,3]]"

@[implicit_reducible]
def «OneVariable M1652^op» : Magma (Fin 5) where
  op := finOpTable "[[2,2,4,0,3],[2,1,0,3,2],[1,0,3,2,0],[0,3,2,3,4],[2,4,4,4,3]]"

@[implicit_reducible]
def «OneVariable M1684» : Magma (Fin 5) where
  op := finOpTable "[[1,0,3,1,4],[0,1,4,3,0],[4,4,2,4,1],[2,3,0,1,2],[4,2,3,0,2]]"

@[implicit_reducible]
def «OneVariable M1684^op» : Magma (Fin 5) where
  op := finOpTable "[[1,0,4,2,4],[0,1,4,3,2],[3,4,2,0,3],[1,3,4,1,0],[4,0,1,2,2]]"

@[implicit_reducible]
def «OneVariable M1757» : Magma (Fin 6) where
  op := finOpTable "[[1,2,1,1,0,1],[5,1,0,2,3,0],[3,0,2,3,5,3],[0,4,3,4,1,5],[0,3,5,1,4,2],[4,0,4,5,2,4]]"

@[implicit_reducible]
def «OneVariable M1757^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,0,0,4],[2,1,0,4,3,0],[1,0,2,3,5,4],[1,2,3,4,1,5],[0,3,5,1,4,2],[1,0,3,5,2,4]]"

@[implicit_reducible]
def «OneVariable M1766» : Magma (Fin 5) where
  op := finOpTable "[[2,3,0,2,1],[4,0,1,0,0],[0,1,2,1,1],[1,2,3,3,3],[1,2,1,3,4]]"

@[implicit_reducible]
def «OneVariable M1766^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,0,1,1],[3,0,1,2,2],[0,1,2,3,1],[2,0,1,3,3],[1,0,1,3,4]]"

@[implicit_reducible]
def «OneVariable M1770» : Magma (Fin 5) where
  op := finOpTable "[[2,2,1,4,0],[2,4,0,4,1],[3,0,2,4,1],[4,3,0,3,1],[0,1,3,0,4]]"

@[implicit_reducible]
def «OneVariable M1770^op» : Magma (Fin 5) where
  op := finOpTable "[[2,2,3,4,0],[2,4,0,3,1],[1,0,2,0,3],[4,4,4,3,0],[0,1,1,1,4]]"

@[implicit_reducible]
def «OneVariable M1780» : Magma (Fin 5) where
  op := finOpTable "[[2,4,0,0,3],[4,1,4,4,2],[0,4,2,3,3],[2,4,3,2,4],[1,0,3,4,1]]"

@[implicit_reducible]
def «OneVariable M1780^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,0,2,1],[4,1,4,4,0],[0,4,2,3,3],[0,4,3,2,4],[3,2,3,4,1]]"

@[implicit_reducible]
def «OneVariable M1781» : Magma (Fin 5) where
  op := finOpTable "[[3,2,0,4,3],[2,1,2,0,0],[0,2,1,2,1],[1,1,2,3,0],[2,4,4,0,4]]"

@[implicit_reducible]
def «OneVariable M1781^op» : Magma (Fin 5) where
  op := finOpTable "[[3,2,0,1,2],[2,1,2,1,4],[0,2,1,2,4],[4,0,2,3,0],[3,0,1,0,4]]"

@[implicit_reducible]
def «OneVariable M1783» : Magma (Fin 6) where
  op := finOpTable "[[0,1,5,1,1,1],[3,5,1,2,5,4],[1,1,2,1,1,5],[1,2,1,3,1,1],[1,0,2,1,4,1],[1,3,2,1,1,5]]"

@[implicit_reducible]
def «OneVariable M1783^op» : Magma (Fin 6) where
  op := finOpTable "[[0,3,1,1,1,1],[1,5,1,2,0,3],[5,1,2,1,2,2],[1,2,1,3,1,1],[1,5,1,1,4,1],[1,4,5,1,1,5]]"

@[implicit_reducible]
def «OneVariable M1787» : Magma (Fin 5) where
  op := finOpTable "[[0,3,4,1,2],[3,3,4,0,1],[3,4,4,1,2],[1,2,2,4,3],[2,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M1787^op» : Magma (Fin 5) where
  op := finOpTable "[[0,3,3,1,2],[3,3,4,2,1],[4,4,4,2,2],[1,0,1,4,3],[2,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M1790» : Magma (Fin 5) where
  op := finOpTable "[[1,3,4,1,0],[2,4,3,0,1],[4,0,3,2,3],[4,0,2,3,4],[0,1,2,4,4]]"

@[implicit_reducible]
def «OneVariable M1790^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,4,0],[3,4,0,0,1],[4,3,3,2,2],[1,0,2,3,4],[0,1,3,4,4]]"

@[implicit_reducible]
def «OneVariable M1811» : Magma (Fin 5) where
  op := finOpTable "[[1,3,4,4,0],[2,1,3,0,4],[4,0,2,4,1],[4,0,4,3,2],[0,4,1,2,3]]"

@[implicit_reducible]
def «OneVariable M1811^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,4,0],[3,1,0,0,4],[4,3,2,4,1],[4,0,4,3,2],[0,4,1,2,3]]"

@[implicit_reducible]
def «OneVariable M1815» : Magma (Fin 5) where
  op := finOpTable "[[2,3,4,0,3],[3,4,0,1,1],[1,2,3,2,0],[0,1,2,3,4],[3,1,0,4,3]]"

@[implicit_reducible]
def «OneVariable M1815^op» : Magma (Fin 5) where
  op := finOpTable "[[2,3,1,0,3],[3,4,2,1,1],[4,0,3,2,0],[0,1,2,3,4],[3,1,0,4,3]]"

@[implicit_reducible]
def «OneVariable M1844» : Magma (Fin 5) where
  op := finOpTable "[[1,3,1,1,0],[2,1,0,0,2],[4,0,2,4,4],[1,2,4,3,0],[0,1,4,4,2]]"

@[implicit_reducible]
def «OneVariable M1844^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,1,0],[3,1,0,2,1],[1,0,2,4,4],[1,0,4,3,4],[0,2,4,0,2]]"

@[implicit_reducible]
def «OneVariable M1855» : Magma (Fin 5) where
  op := finOpTable "[[2,2,1,4,0],[4,1,3,0,4],[3,0,2,0,4],[4,3,0,3,1],[0,2,4,2,2]]"

@[implicit_reducible]
def «OneVariable M1855^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,4,0],[2,1,0,3,2],[1,3,2,0,4],[4,0,0,3,2],[0,4,4,1,2]]"

@[implicit_reducible]
def «OneVariable M1894» : Magma (Fin 5) where
  op := finOpTable "[[0,1,2,2,2],[1,3,3,2,0],[2,3,0,1,2],[2,4,1,3,1],[2,0,3,4,4]]"

@[implicit_reducible]
def «OneVariable M1894^op» : Magma (Fin 5) where
  op := finOpTable "[[0,1,2,2,2],[1,3,3,4,0],[2,3,0,1,3],[2,2,1,3,4],[2,0,2,1,4]]"

@[implicit_reducible]
def «OneVariable M1905» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,0,1],[2,3,0,1,0],[3,3,4,2,2],[0,1,1,3,3],[1,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M1905^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,1],[4,3,3,1,0],[3,0,4,1,2],[0,1,2,3,3],[1,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M1917» : Magma (Fin 5) where
  op := finOpTable "[[0,3,2,1,4],[2,3,1,0,2],[2,1,2,3,4],[1,4,3,2,1],[4,2,4,2,2]]"

@[implicit_reducible]
def «OneVariable M1917^op» : Magma (Fin 5) where
  op := finOpTable "[[0,2,2,1,4],[3,3,1,4,2],[2,1,2,3,4],[1,0,3,2,2],[4,2,4,1,2]]"

@[implicit_reducible]
def «OneVariable M1921» : Magma (Fin 5) where
  op := finOpTable "[[2,2,1,2,0],[2,3,0,1,2],[3,0,2,0,3],[4,1,0,3,3],[0,2,1,4,4]]"

@[implicit_reducible]
def «OneVariable M1921^op» : Magma (Fin 5) where
  op := finOpTable "[[2,2,3,4,0],[2,3,0,1,2],[1,0,2,0,1],[2,1,0,3,4],[0,2,3,3,4]]"

@[implicit_reducible]
def «OneVariable M1936» : Magma (Fin 5) where
  op := finOpTable "[[1,3,3,1,0],[2,1,0,0,1],[4,0,2,4,4],[0,0,3,3,3],[0,1,2,2,4]]"

@[implicit_reducible]
def «OneVariable M1936^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,0,0],[3,1,0,0,1],[3,0,2,3,2],[1,0,4,3,2],[0,1,4,3,4]]"

@[implicit_reducible]
def «OneVariable M1937» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,3,0,1],[2,1,0,3,2,0],[4,0,2,1,4,3],[0,3,0,5,5,4],[0,4,4,5,2,3],[1,0,3,2,3,5]]"

@[implicit_reducible]
def «OneVariable M1937^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,4,0,0,1],[5,1,0,3,4,0],[3,0,2,0,4,3],[3,3,1,5,5,2],[0,2,4,5,2,3],[1,0,3,4,3,5]]"

@[implicit_reducible]
def «OneVariable M1938» : Magma (Fin 6) where
  op := finOpTable "[[0,3,3,1,4,1],[5,0,1,2,1,0],[3,1,2,4,5,2],[1,4,4,3,4,5],[1,0,0,4,3,4],[1,2,0,5,4,3]]"

@[implicit_reducible]
def «OneVariable M1938^op» : Magma (Fin 6) where
  op := finOpTable "[[0,5,3,1,1,1],[3,0,1,4,0,2],[3,1,2,4,0,0],[1,2,4,3,4,5],[4,1,5,4,3,4],[1,0,2,5,4,3]]"

@[implicit_reducible]
def «OneVariable M1949» : Magma (Fin 5) where
  op := finOpTable "[[2,4,0,3,2],[4,1,3,4,0],[0,3,2,1,4],[2,4,0,3,1],[1,3,4,2,1]]"

@[implicit_reducible]
def «OneVariable M1950» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,1,1,0],[4,1,0,3,0,5],[1,0,2,5,3,3],[0,3,4,2,1,2],[5,0,3,2,4,4],[0,5,3,1,4,1]]"

@[implicit_reducible]
def «OneVariable M1950^op» : Magma (Fin 6) where
  op := finOpTable "[[1,4,1,0,5,0],[2,1,0,3,0,5],[3,0,2,4,3,3],[1,3,5,2,2,1],[1,0,3,1,4,4],[0,5,3,2,4,1]]"

@[implicit_reducible]
def «OneVariable M1952» : Magma (Fin 5) where
  op := finOpTable "[[1,4,1,0,3],[2,1,0,4,0],[3,0,2,4,4],[0,3,4,3,3],[3,0,2,1,4]]"

@[implicit_reducible]
def «OneVariable M1952^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,3],[4,1,0,3,0],[1,0,2,4,2],[0,4,4,3,1],[3,0,4,3,4]]"

@[implicit_reducible]
def «OneVariable M2014» : Magma (Fin 4) where
  op := finOpTable "[[2,2,1,0],[3,1,0,1],[0,3,2,2],[0,3,0,3]]"

@[implicit_reducible]
def «OneVariable M2014^op» : Magma (Fin 4) where
  op := finOpTable "[[2,3,0,0],[2,1,3,3],[1,0,2,0],[0,1,2,3]]"

@[implicit_reducible]
def «OneVariable M2015» : Magma (Fin 5) where
  op := finOpTable "[[0,4,0,4,1],[4,1,1,4,0],[2,4,2,2,3],[4,4,3,3,4],[3,2,1,4,1]]"

@[implicit_reducible]
def «OneVariable M2015^op» : Magma (Fin 5) where
  op := finOpTable "[[0,4,2,4,3],[4,1,4,4,2],[0,1,2,3,1],[4,4,2,3,4],[1,0,3,4,1]]"

@[implicit_reducible]
def «OneVariable M2020» : Magma (Fin 5) where
  op := finOpTable "[[2,2,0,0,1],[4,4,1,4,0],[0,1,2,1,1],[0,4,2,3,1],[1,3,2,3,4]]"

@[implicit_reducible]
def «OneVariable M2020^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,0,0,1],[2,4,1,4,3],[0,1,2,2,2],[0,4,1,3,3],[1,0,1,1,4]]"

@[implicit_reducible]
def «OneVariable M2066» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,0,1],[4,3,0,1,0],[3,1,2,3,4],[0,1,2,3,4],[1,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M2066^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,0,1],[2,3,1,1,0],[1,0,2,2,2],[0,1,3,3,3],[1,0,4,4,4]]"

@[implicit_reducible]
def «OneVariable M2083» : Magma (Fin 5) where
  op := finOpTable "[[2,2,1,2,0],[4,1,0,4,4],[3,0,2,0,4],[2,1,0,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M2083^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,2,0],[2,1,0,1,1],[1,0,2,0,2],[2,4,0,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M2085» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,1,0],[3,1,2,0,4],[4,0,2,3,4],[1,0,2,3,4],[0,4,2,3,4]]"

@[implicit_reducible]
def «OneVariable M2085^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,4,1,0],[2,1,0,0,4],[1,2,2,2,2],[1,0,3,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M2091» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,0,1],[4,3,3,1,0],[3,0,4,3,2],[0,1,3,3,3],[1,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M2091^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,0,1],[2,3,0,1,0],[1,3,4,3,2],[0,1,3,3,3],[1,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M2112» : Magma (Fin 5) where
  op := finOpTable "[[1,0,2,4,3],[0,1,2,4,2],[2,2,2,3,4],[4,4,3,2,0],[2,2,4,1,3]]"

@[implicit_reducible]
def «OneVariable M2112^op» : Magma (Fin 5) where
  op := finOpTable "[[1,0,2,4,2],[0,1,2,4,2],[2,2,2,3,4],[4,4,3,2,1],[3,2,4,0,3]]"

@[implicit_reducible]
def «OneVariable M2113» : Magma (Fin 5) where
  op := finOpTable "[[2,4,0,3,1],[3,4,3,1,2],[0,3,2,2,1],[0,1,2,3,4],[1,0,2,4,3]]"

@[implicit_reducible]
def «OneVariable M2113^op» : Magma (Fin 5) where
  op := finOpTable "[[2,3,0,0,1],[4,4,3,1,0],[0,3,2,2,2],[3,1,2,3,4],[1,2,1,4,3]]"

@[implicit_reducible]
def «OneVariable M2117» : Magma (Fin 4) where
  op := finOpTable "[[1,2,1,0],[0,1,0,1],[3,3,2,0],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M2117^op» : Magma (Fin 4) where
  op := finOpTable "[[1,0,3,0],[2,1,3,0],[1,0,2,0],[0,1,0,3]]"

@[implicit_reducible]
def «OneVariable M2127» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,1,0],[3,1,0,0,4],[4,2,2,3,2],[1,0,3,3,3],[0,4,0,0,1]]"

@[implicit_reducible]
def «OneVariable M2127^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,4,1,0],[2,1,2,0,4],[1,0,2,3,0],[1,0,3,3,0],[0,4,2,3,1]]"

@[implicit_reducible]
def «OneVariable M2213» : Magma (Fin 5) where
  op := finOpTable "[[2,2,1,4,0],[4,1,0,1,0],[3,0,4,3,2],[2,0,0,3,1],[0,2,2,4,4]]"

@[implicit_reducible]
def «OneVariable M2213^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,2,0],[2,1,0,0,2],[1,0,4,0,2],[4,1,3,3,4],[0,0,2,1,4]]"

@[implicit_reducible]
def «OneVariable M2237» : Magma (Fin 5) where
  op := finOpTable "[[2,4,1,4,0],[4,4,0,2,1],[3,0,4,2,2],[2,4,0,4,3],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M2237^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,2,0],[4,4,0,4,1],[1,0,4,0,2],[4,2,2,4,3],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M2289» : Magma (Fin 5) where
  op := finOpTable "[[2,4,0,1,0],[3,3,3,0,1],[0,4,2,1,2],[1,2,1,3,4],[0,1,4,4,3]]"

@[implicit_reducible]
def «OneVariable M2289^op» : Magma (Fin 5) where
  op := finOpTable "[[2,3,0,1,0],[4,3,4,2,1],[0,3,2,1,4],[1,0,1,3,4],[0,1,2,4,3]]"

@[implicit_reducible]
def «OneVariable M2290» : Magma (Fin 6) where
  op := finOpTable "[[1,4,1,4,1,0],[2,1,0,1,0,0],[3,0,2,5,2,3],[0,2,5,2,3,2],[5,0,2,3,4,5],[0,5,3,4,4,5]]"

@[implicit_reducible]
def «OneVariable M2290^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,5,0],[4,1,0,2,0,5],[1,0,2,5,2,3],[4,1,5,2,3,4],[1,0,2,3,4,4],[0,0,3,2,5,5]]"

@[implicit_reducible]
def «OneVariable M2299» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,0,1],[2,3,0,1,0],[1,0,3,2,4],[0,1,2,3,4],[3,0,4,1,4]]"

@[implicit_reducible]
def «OneVariable M2306» : Magma (Fin 6) where
  op := finOpTable "[[1,4,3,1,1,0],[2,1,0,5,0,5],[1,0,2,3,2,0],[0,5,3,2,3,1],[5,0,2,4,4,1],[0,5,3,1,1,1]]"

@[implicit_reducible]
def «OneVariable M2306^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,1,0,5,0],[4,1,0,5,0,5],[3,0,2,3,2,3],[1,5,3,2,4,1],[1,0,2,3,4,1],[0,5,0,1,1,1]]"

@[implicit_reducible]
def «OneVariable M2318» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,3,1,0],[4,1,0,5,0,5],[5,0,3,2,3,0],[0,5,2,3,4,0],[1,0,4,4,4,0],[0,5,0,0,0,1]]"

@[implicit_reducible]
def «OneVariable M2318^op» : Magma (Fin 6) where
  op := finOpTable "[[1,4,5,0,1,0],[2,1,0,5,0,5],[3,0,3,2,4,0],[3,5,2,3,4,0],[1,0,3,4,4,0],[0,5,0,0,0,1]]"

@[implicit_reducible]
def «OneVariable M2320» : Magma (Fin 6) where
  op := finOpTable "[[1,4,1,4,5,0],[2,1,0,5,0,5],[3,0,2,4,1,1],[0,0,4,3,4,5],[5,0,3,4,3,1],[0,5,0,3,3,1]]"

@[implicit_reducible]
def «OneVariable M2320^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,5,0],[4,1,0,0,0,5],[1,0,2,4,3,0],[4,5,4,3,4,3],[5,0,1,4,3,3],[0,5,1,5,1,1]]"

@[implicit_reducible]
def «OneVariable M2321» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,3,1,0],[4,1,0,1,0,1],[5,0,2,3,3,3],[0,2,3,2,3,2],[5,0,3,3,4,5],[0,1,3,4,4,5]]"

@[implicit_reducible]
def «OneVariable M2321^op» : Magma (Fin 6) where
  op := finOpTable "[[1,4,5,0,5,0],[2,1,0,2,0,1],[3,0,2,3,3,3],[3,1,3,2,3,4],[1,0,3,3,4,4],[0,1,3,2,5,5]]"

@[implicit_reducible]
def «OneVariable M2324» : Magma (Fin 5) where
  op := finOpTable "[[2,2,0,3,1],[2,4,1,4,0],[0,1,2,4,4],[3,4,3,3,1],[1,3,4,1,2]]"

@[implicit_reducible]
def «OneVariable M2324^op» : Magma (Fin 5) where
  op := finOpTable "[[2,2,0,3,1],[2,4,1,4,3],[0,1,2,3,4],[3,4,4,3,1],[1,0,4,1,2]]"

@[implicit_reducible]
def «OneVariable M2328» : Magma (Fin 6) where
  op := finOpTable "[[2,5,1,4,2,0],[5,1,0,4,2,1],[3,0,2,0,4,5],[2,4,0,3,5,4],[0,2,4,1,3,2],[0,1,5,4,3,2]]"

@[implicit_reducible]
def «OneVariable M2328^op» : Magma (Fin 6) where
  op := finOpTable "[[2,5,3,2,0,0],[5,1,0,4,2,1],[1,0,2,0,4,5],[4,4,0,3,1,4],[2,2,4,5,3,3],[0,1,5,4,2,2]]"

@[implicit_reducible]
def «OneVariable M2333» : Magma (Fin 5) where
  op := finOpTable "[[3,1,3,0,2],[1,0,3,1,2],[3,3,4,2,0],[0,1,2,3,4],[2,2,1,4,3]]"

@[implicit_reducible]
def «OneVariable M2334» : Magma (Fin 6) where
  op := finOpTable "[[2,5,0,1,1,1],[4,0,1,1,2,2],[0,1,2,3,4,5],[1,2,3,5,2,4],[1,3,4,2,2,3],[1,2,5,4,3,2]]"

@[implicit_reducible]
def «OneVariable M2334^op» : Magma (Fin 6) where
  op := finOpTable "[[2,4,0,1,1,1],[5,0,1,2,3,2],[0,1,2,3,4,5],[1,1,3,5,2,4],[1,2,4,2,2,3],[1,2,5,4,3,2]]"

@[implicit_reducible]
def «OneVariable M2402» : Magma (Fin 6) where
  op := finOpTable "[[1,2,4,0,0,1],[5,1,0,3,4,0],[3,0,2,3,2,2],[1,3,2,1,1,1],[0,4,0,0,1,1],[4,0,0,5,5,5]]"

@[implicit_reducible]
def «OneVariable M2402^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,1,0,4],[2,1,0,3,4,0],[4,0,2,2,0,0],[0,3,3,1,0,5],[0,4,2,1,1,5],[1,0,2,1,1,5]]"

@[implicit_reducible]
def «OneVariable M2405» : Magma (Fin 6) where
  op := finOpTable "[[1,2,4,0,0,4],[5,1,0,3,4,0],[3,0,2,5,2,3],[1,3,5,1,1,4],[0,4,4,1,1,5],[4,0,3,4,5,2]]"

@[implicit_reducible]
def «OneVariable M2405^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,1,0,4],[2,1,0,3,4,0],[4,0,2,5,4,3],[0,3,5,1,1,4],[0,4,2,1,1,5],[4,0,3,4,5,2]]"

@[implicit_reducible]
def «OneVariable M2415» : Magma (Fin 6) where
  op := finOpTable "[[1,2,1,0,1,0],[4,1,0,5,0,5],[3,0,4,3,2,0],[1,5,4,3,4,1],[5,0,2,2,4,1],[0,5,1,3,4,1]]"

@[implicit_reducible]
def «OneVariable M2415^op» : Magma (Fin 6) where
  op := finOpTable "[[1,4,3,1,5,0],[2,1,0,5,0,5],[1,0,4,4,2,1],[0,5,3,3,2,3],[1,0,2,4,4,4],[0,5,0,1,1,1]]"

@[implicit_reducible]
def «OneVariable M2419» : Magma (Fin 6) where
  op := finOpTable "[[1,4,1,0,1,0],[2,1,0,1,0,5],[3,0,2,5,2,3],[2,2,5,2,3,2],[5,0,2,3,4,0],[0,5,3,4,1,1]]"

@[implicit_reducible]
def «OneVariable M2419^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,2,5,0],[4,1,0,2,0,5],[1,0,2,5,2,3],[0,1,5,2,3,4],[1,0,2,3,4,1],[0,5,3,2,0,1]]"

@[implicit_reducible]
def «OneVariable M2426» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,3,0,1],[2,1,0,3,3,0],[4,0,2,1,3,5],[0,3,0,4,5,4],[0,3,3,2,4,3],[4,0,5,1,3,2]]"

@[implicit_reducible]
def «OneVariable M2426^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,4,0,0,4],[5,1,0,3,3,0],[3,0,2,0,3,5],[3,3,1,4,2,1],[0,3,3,5,4,3],[1,0,5,4,3,2]]"

@[implicit_reducible]
def «OneVariable M2430» : Magma (Fin 6) where
  op := finOpTable "[[1,4,1,0,5,0],[2,1,0,3,0,5],[3,0,2,5,5,3],[2,1,5,4,3,1],[5,0,5,3,4,1],[0,5,4,2,1,2]]"

@[implicit_reducible]
def «OneVariable M2430^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,2,5,0],[4,1,0,1,0,5],[1,0,2,5,5,4],[0,3,5,4,3,2],[5,0,5,3,4,1],[0,5,3,1,1,2]]"

@[implicit_reducible]
def «OneVariable M2431» : Magma (Fin 6) where
  op := finOpTable "[[1,2,4,0,0,1],[5,4,0,4,1,0],[3,0,5,0,3,2],[3,1,4,4,3,5],[0,1,3,3,4,5],[4,0,2,1,5,5]]"

@[implicit_reducible]
def «OneVariable M2431^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,3,0,4],[2,4,0,1,1,0],[4,0,5,4,3,2],[0,4,0,4,3,1],[0,1,3,3,4,5],[1,0,2,5,5,5]]"

@[implicit_reducible]
def «OneVariable M2433» : Magma (Fin 6) where
  op := finOpTable "[[1,5,1,0,0,4],[2,4,0,1,1,0],[3,0,3,2,3,5],[3,3,2,3,1,1],[0,1,2,0,4,5],[4,0,2,1,4,5]]"

@[implicit_reducible]
def «OneVariable M2433^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,3,0,4],[5,4,0,3,1,0],[1,0,3,2,2,2],[0,1,2,3,0,1],[0,1,3,1,4,4],[4,0,5,1,5,5]]"

@[implicit_reducible]
def «OneVariable M2512» : Magma (Fin 4) where
  op := finOpTable "[[1,2,1,0],[2,3,0,1],[1,0,1,2],[0,1,2,3]]"

@[implicit_reducible]
def «OneVariable M2516» : Magma (Fin 5) where
  op := finOpTable "[[1,0,1,3,0],[2,4,0,3,1],[3,0,2,3,4],[0,3,2,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M2516^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,0],[0,4,0,3,1],[1,0,2,2,2],[3,3,3,3,3],[0,1,4,4,4]]"

@[implicit_reducible]
def «OneVariable M2518» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,0,1],[4,3,0,1,0],[1,1,2,3,4],[0,1,2,3,4],[3,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M2518^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,1,0,3],[2,3,1,1,0],[1,0,2,2,2],[0,1,3,3,3],[1,0,4,4,4]]"

@[implicit_reducible]
def «OneVariable M2523» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,3,0],[2,4,0,3,1],[3,0,2,3,4],[0,3,2,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M2523^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,0],[2,4,0,3,1],[1,0,2,2,2],[3,3,3,3,3],[0,1,4,4,4]]"

@[implicit_reducible]
def «OneVariable M2527» : Magma (Fin 5) where
  op := finOpTable "[[1,0,3,3,0],[2,4,0,3,1],[1,0,2,3,4],[0,3,2,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M2527^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,0,0],[0,4,0,3,1],[3,0,2,2,2],[3,3,3,3,3],[0,1,4,4,4]]"

@[implicit_reducible]
def «OneVariable M2528» : Magma (Fin 5) where
  op := finOpTable "[[1,0,4,3,0],[2,4,0,3,1],[3,0,2,3,4],[0,4,2,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M2528^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,0],[0,4,0,4,1],[4,0,2,2,2],[3,3,3,3,3],[0,1,4,4,4]]"

@[implicit_reducible]
def «OneVariable M2529» : Magma (Fin 5) where
  op := finOpTable "[[1,0,3,3,0],[2,4,0,3,1],[4,0,2,3,4],[0,3,2,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M2529^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,0,0],[0,4,0,3,1],[3,0,2,2,2],[3,3,3,3,3],[0,1,4,4,4]]"

@[implicit_reducible]
def «OneVariable M2543» : Magma (Fin 4) where
  op := finOpTable "[[1,2,1,0],[0,3,3,1],[3,0,3,2],[0,1,2,3]]"

@[implicit_reducible]
def «OneVariable M2543^op» : Magma (Fin 4) where
  op := finOpTable "[[1,0,3,0],[2,3,0,1],[1,3,3,2],[0,1,2,3]]"

@[implicit_reducible]
def «OneVariable M2548» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,1,0],[3,4,0,0,1],[4,0,2,2,4],[4,0,2,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M2548^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,4,4,0],[2,4,0,0,1],[1,0,2,2,2],[1,0,2,3,3],[0,1,4,4,4]]"

@[implicit_reducible]
def «OneVariable M2555» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,0,1],[4,3,2,1,0],[3,0,3,2,3],[0,1,2,3,3],[3,0,4,3,4]]"

@[implicit_reducible]
def «OneVariable M2555^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,0,3],[2,3,0,1,0],[1,2,3,2,4],[0,1,2,3,3],[1,0,3,3,4]]"

@[implicit_reducible]
def «OneVariable M2564» : Magma (Fin 5) where
  op := finOpTable "[[2,0,4,1,2],[0,1,2,3,4],[3,2,1,0,4],[2,3,0,3,4],[1,2,0,3,4]]"

@[implicit_reducible]
def «OneVariable M2564^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,3,2,1],[0,1,2,3,2],[4,2,1,0,0],[1,3,0,3,3],[2,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M2567» : Magma (Fin 5) where
  op := finOpTable "[[2,2,0,1,0],[3,3,1,0,2],[0,1,2,3,4],[2,4,3,2,1],[3,2,2,1,4]]"

@[implicit_reducible]
def «OneVariable M2567^op» : Magma (Fin 5) where
  op := finOpTable "[[2,3,0,2,3],[2,3,1,4,2],[0,1,2,3,2],[1,0,3,2,1],[0,2,4,1,4]]"

@[implicit_reducible]
def «OneVariable M2579» : Magma (Fin 3) where
  op := finOpTable "[[1,0,2],[0,1,2],[2,2,0]]"

@[implicit_reducible]
def «OneVariable M2580» : Magma (Fin 5) where
  op := finOpTable "[[2,4,0,3,1],[4,3,1,1,0],[0,1,2,3,4],[4,1,3,3,0],[3,0,4,2,0]]"

@[implicit_reducible]
def «OneVariable M2580^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,0,4,3],[4,3,1,1,0],[0,1,2,3,4],[3,1,3,3,2],[1,0,4,0,0]]"

@[implicit_reducible]
def «OneVariable M2590» : Magma (Fin 6) where
  op := finOpTable "[[2,2,0,0,3,1],[4,5,3,4,1,0],[0,1,3,2,5,1],[0,5,2,3,2,1],[3,1,0,2,4,5],[1,3,2,1,5,4]]"

@[implicit_reducible]
def «OneVariable M2590^op» : Magma (Fin 6) where
  op := finOpTable "[[2,4,0,0,3,1],[2,5,1,5,1,3],[0,3,3,2,0,2],[0,4,2,3,2,1],[3,1,5,2,4,5],[1,0,1,1,5,4]]"

@[implicit_reducible]
def «OneVariable M2617» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,3,0],[2,4,0,0,1],[1,0,2,3,4],[0,4,2,3,3],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M2617^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,0,0],[2,4,0,4,1],[3,0,2,2,2],[3,0,3,3,3],[0,1,4,3,4]]"

@[implicit_reducible]
def «OneVariable M2633» : Magma (Fin 5) where
  op := finOpTable "[[1,3,1,1,0],[2,4,1,0,1],[1,0,2,3,4],[1,0,3,3,1],[0,1,4,1,4]]"

@[implicit_reducible]
def «OneVariable M2633^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,1,0],[3,4,0,0,1],[1,1,2,3,4],[1,0,3,3,1],[0,1,4,1,4]]"

@[implicit_reducible]
def «OneVariable M2639» : Magma (Fin 6) where
  op := finOpTable "[[1,2,1,3,0,1],[5,4,0,0,1,0],[3,0,2,3,4,5],[0,3,2,3,4,5],[0,1,2,3,4,4],[1,0,5,5,5,5]]"

@[implicit_reducible]
def «OneVariable M2639^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,0,0,1],[2,4,0,3,1,0],[1,0,2,2,2,5],[3,0,3,3,3,5],[0,1,4,4,4,5],[1,0,5,5,4,5]]"

@[implicit_reducible]
def «OneVariable M2654» : Magma (Fin 6) where
  op := finOpTable "[[1,2,1,3,0,4],[5,4,0,0,1,0],[3,0,2,3,4,5],[0,3,2,3,4,5],[0,1,2,3,4,4],[1,0,5,5,5,5]]"

@[implicit_reducible]
def «OneVariable M2654^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,0,0,1],[2,4,0,3,1,0],[1,0,2,2,2,5],[3,0,3,3,3,5],[0,1,4,4,4,5],[4,0,5,5,4,5]]"

@[implicit_reducible]
def «OneVariable M2660» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,3,0,1],[5,4,0,0,1,0],[1,0,2,3,4,5],[0,3,2,3,4,5],[0,1,2,3,4,4],[1,0,5,5,5,5]]"

@[implicit_reducible]
def «OneVariable M2660^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,1,0,0,1],[2,4,0,3,1,0],[3,0,2,2,2,5],[3,0,3,3,3,5],[0,1,4,4,4,5],[1,0,5,5,4,5]]"

@[implicit_reducible]
def «OneVariable M2662» : Magma (Fin 5) where
  op := finOpTable "[[4,3,4,2,0],[3,1,2,0,4],[3,2,1,4,4],[1,4,0,0,3],[0,4,4,3,4]]"

@[implicit_reducible]
def «OneVariable M2662^op» : Magma (Fin 5) where
  op := finOpTable "[[4,3,3,1,0],[3,1,2,4,4],[4,2,1,0,4],[2,0,4,0,3],[0,4,4,3,4]]"

@[implicit_reducible]
def «OneVariable M2664» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,3,0,1],[5,4,0,0,1,0],[1,0,2,3,4,5],[0,3,2,3,4,5],[0,1,2,3,4,4],[4,0,5,5,5,5]]"

@[implicit_reducible]
def «OneVariable M2664^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,1,0,0,4],[2,4,0,3,1,0],[3,0,2,2,2,5],[3,0,3,3,3,5],[0,1,4,4,4,5],[1,0,5,5,4,5]]"

@[implicit_reducible]
def «OneVariable M2666» : Magma (Fin 6) where
  op := finOpTable "[[1,2,4,3,0,1],[5,4,0,0,1,0],[3,0,2,3,4,5],[0,3,2,3,4,5],[0,1,2,3,4,4],[1,0,5,5,5,5]]"

@[implicit_reducible]
def «OneVariable M2666^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,0,0,1],[2,4,0,3,1,0],[4,0,2,2,2,5],[3,0,3,3,3,5],[0,1,4,4,4,5],[1,0,5,5,4,5]]"

@[implicit_reducible]
def «OneVariable M2677» : Magma (Fin 5) where
  op := finOpTable "[[3,2,1,0,2],[2,3,3,1,4],[4,3,0,2,0],[0,1,2,3,4],[4,4,0,4,1]]"

@[implicit_reducible]
def «OneVariable M2677^op» : Magma (Fin 5) where
  op := finOpTable "[[3,2,4,0,4],[2,3,3,1,4],[1,3,0,2,0],[0,1,2,3,4],[2,4,0,4,1]]"

@[implicit_reducible]
def «OneVariable M2690» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,1,0],[3,4,0,0,1],[1,0,2,3,1],[1,0,2,3,3],[0,1,1,4,4]]"

@[implicit_reducible]
def «OneVariable M2692» : Magma (Fin 5) where
  op := finOpTable "[[0,3,4,1,4],[3,3,1,0,3],[2,1,2,3,3],[1,4,3,2,1],[4,2,0,1,0]]"

@[implicit_reducible]
def «OneVariable M2692^op» : Magma (Fin 5) where
  op := finOpTable "[[0,3,2,1,4],[3,3,1,4,2],[4,1,2,3,0],[1,0,3,2,1],[4,3,3,1,0]]"

@[implicit_reducible]
def «OneVariable M2695» : Magma (Fin 6) where
  op := finOpTable "[[1,4,1,2,1,0],[2,5,0,0,0,1],[3,0,4,3,2,5],[0,2,3,2,3,5],[1,0,2,3,4,5],[0,1,3,4,4,5]]"

@[implicit_reducible]
def «OneVariable M2695^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,1,0],[4,5,0,2,0,1],[1,0,4,3,2,3],[2,0,3,2,3,4],[1,0,2,3,4,4],[0,1,5,5,5,5]]"

@[implicit_reducible]
def «OneVariable M2701» : Magma (Fin 6) where
  op := finOpTable "[[1,4,3,3,1,0],[2,5,0,0,0,1],[1,0,4,4,2,2],[0,3,4,3,2,5],[1,0,2,2,5,4],[0,1,2,4,4,5]]"

@[implicit_reducible]
def «OneVariable M2701^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,1,0,1,0],[4,5,0,3,0,1],[3,0,4,4,2,2],[3,0,4,3,2,4],[1,0,2,2,5,4],[0,1,2,5,4,5]]"

@[implicit_reducible]
def «OneVariable M2715» : Magma (Fin 6) where
  op := finOpTable "[[1,4,1,3,5,0],[2,5,0,0,0,1],[3,0,2,3,4,5],[0,3,2,3,4,5],[1,0,2,3,4,5],[0,1,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M2715^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,1,0],[4,5,0,3,0,1],[1,0,2,2,2,2],[3,0,3,3,3,3],[5,0,4,4,4,4],[0,1,5,5,5,5]]"

@[implicit_reducible]
def «OneVariable M2718» : Magma (Fin 6) where
  op := finOpTable "[[1,4,1,3,5,0],[2,5,0,0,0,1],[3,0,2,3,4,5],[0,3,2,3,4,5],[5,0,2,3,4,5],[0,1,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M2718^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,5,0],[4,5,0,3,0,1],[1,0,2,2,2,2],[3,0,3,3,3,3],[5,0,4,4,4,4],[0,1,5,5,5,5]]"

@[implicit_reducible]
def «OneVariable M2762» : Magma (Fin 6) where
  op := finOpTable "[[2,3,0,4,2,1],[5,5,5,1,1,2],[0,4,2,3,4,1],[4,5,3,2,0,5],[3,1,4,0,3,5],[1,0,1,5,5,4]]"

@[implicit_reducible]
def «OneVariable M2762^op» : Magma (Fin 6) where
  op := finOpTable "[[2,5,0,4,3,1],[3,5,4,5,1,0],[0,5,2,3,4,1],[4,1,3,2,0,5],[2,1,4,0,3,5],[1,2,1,5,5,4]]"

@[implicit_reducible]
def «OneVariable M2776» : Magma (Fin 5) where
  op := finOpTable "[[1,4,1,0,3],[2,3,2,1,0],[3,0,2,2,4],[0,1,3,3,4],[3,0,4,3,4]]"

@[implicit_reducible]
def «OneVariable M2776^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,3],[4,3,0,1,0],[1,2,2,3,4],[0,1,2,3,3],[3,0,4,4,4]]"

@[implicit_reducible]
def «OneVariable M2798» : Magma (Fin 5) where
  op := finOpTable "[[2,3,0,3,1],[4,4,4,1,0],[0,3,2,3,3],[3,1,3,3,4],[1,2,1,4,3]]"

@[implicit_reducible]
def «OneVariable M2798^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,0,3,1],[3,4,3,1,2],[0,4,2,3,1],[3,1,3,3,4],[1,0,3,4,3]]"

@[implicit_reducible]
def «OneVariable M2805» : Magma (Fin 5) where
  op := finOpTable "[[1,4,1,0,3],[2,3,0,1,0],[3,2,2,2,4],[0,1,2,3,2],[1,0,4,2,2]]"

@[implicit_reducible]
def «OneVariable M2805^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,1],[4,3,2,1,0],[1,0,2,2,4],[0,1,2,3,2],[3,0,4,2,2]]"

@[implicit_reducible]
def «OneVariable M2813» : Magma (Fin 6) where
  op := finOpTable "[[1,2,1,2,1,0],[4,5,0,2,0,1],[3,0,2,3,4,5],[0,4,3,4,5,4],[5,0,4,5,2,3],[0,1,4,2,3,5]]"

@[implicit_reducible]
def «OneVariable M2813^op» : Magma (Fin 6) where
  op := finOpTable "[[1,4,3,0,5,0],[2,5,0,4,0,1],[1,0,2,3,4,4],[2,2,3,4,5,2],[1,0,4,5,2,3],[0,1,5,4,3,5]]"

@[implicit_reducible]
def «OneVariable M2817» : Magma (Fin 6) where
  op := finOpTable "[[0,1,2,3,0,5],[1,5,0,1,5,4],[2,3,0,3,3,1],[3,2,3,2,2,3],[0,5,2,2,4,1],[5,2,1,3,1,0]]"

@[implicit_reducible]
def «OneVariable M2817^op» : Magma (Fin 6) where
  op := finOpTable "[[0,1,2,3,0,5],[1,5,3,2,5,2],[2,0,0,3,2,1],[3,1,3,2,2,3],[0,5,3,2,4,1],[5,4,1,3,1,0]]"

@[implicit_reducible]
def «OneVariable M2818» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,2,0,1],[2,4,0,3,1,0],[4,0,4,3,2,3],[0,5,3,2,3,3],[0,1,2,3,4,5],[1,0,3,5,5,4]]"

@[implicit_reducible]
def «OneVariable M2818^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,4,0,0,1],[5,4,0,5,1,0],[3,0,4,3,2,3],[2,3,3,2,3,5],[0,1,2,3,4,5],[1,0,3,3,5,4]]"

@[implicit_reducible]
def «OneVariable M2819» : Magma (Fin 6) where
  op := finOpTable "[[1,0,1,3,0,4],[0,4,5,2,1,2],[2,3,1,1,2,4],[3,2,4,5,1,3],[0,1,2,4,4,2],[4,2,0,3,5,5]]"

@[implicit_reducible]
def «OneVariable M2819^op» : Magma (Fin 6) where
  op := finOpTable "[[1,0,2,3,0,4],[0,4,3,2,1,2],[1,5,1,4,2,0],[3,2,1,5,4,3],[0,1,2,1,4,5],[4,2,4,3,2,5]]"

@[implicit_reducible]
def «OneVariable M2820» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,0,2,1],[2,3,0,1,1,0],[3,0,2,1,4,5],[0,1,1,4,3,3],[0,1,4,3,5,4],[4,0,5,3,4,2]]"

@[implicit_reducible]
def «OneVariable M2820^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,0,4],[5,3,0,1,1,0],[3,0,2,1,4,5],[0,1,1,4,3,3],[2,1,4,3,5,4],[1,0,5,3,4,2]]"

@[implicit_reducible]
def «OneVariable M2821» : Magma (Fin 6) where
  op := finOpTable "[[1,4,3,2,1,0],[2,5,0,3,0,1],[5,0,5,3,3,2],[0,1,3,2,3,3],[5,0,3,4,5,4],[0,1,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M2821^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,5,0,5,0],[4,5,0,1,0,1],[3,0,5,3,3,2],[2,3,3,2,4,3],[1,0,3,3,5,4],[0,1,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M2823» : Magma (Fin 6) where
  op := finOpTable "[[1,4,5,0,5,0],[2,5,0,5,0,1],[3,0,5,0,3,2],[3,5,5,4,3,3],[1,0,3,3,5,4],[0,1,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M2823^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,3,1,0],[4,5,0,5,0,1],[5,0,5,5,3,2],[0,5,0,4,3,3],[5,0,3,3,5,4],[0,1,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M2824» : Magma (Fin 6) where
  op := finOpTable "[[1,4,5,0,5,0],[2,5,0,0,0,1],[3,0,2,3,4,5],[3,4,3,4,5,2],[5,0,4,5,2,3],[0,1,4,2,3,5]]"

@[implicit_reducible]
def «OneVariable M2824^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,3,5,0],[4,5,0,4,0,1],[5,0,2,3,4,4],[0,0,3,4,5,2],[5,0,4,5,2,3],[0,1,5,2,3,5]]"

@[implicit_reducible]
def «OneVariable M2838» : Magma (Fin 6) where
  op := finOpTable "[[1,4,1,3,1,0],[2,5,0,3,0,1],[3,0,2,3,4,5],[0,3,2,3,4,5],[5,0,2,3,4,5],[0,1,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M2838^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,5,0],[4,5,0,3,0,1],[1,0,2,2,2,2],[3,3,3,3,3,3],[1,0,4,4,4,4],[0,1,5,5,5,5]]"

@[implicit_reducible]
def «OneVariable M2841» : Magma (Fin 6) where
  op := finOpTable "[[1,2,1,0,0,1],[5,4,0,1,1,0],[3,0,2,2,4,5],[4,4,2,4,3,1],[0,1,2,3,4,1],[4,0,2,1,4,5]]"

@[implicit_reducible]
def «OneVariable M2841^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,4,0,4],[2,4,0,4,1,0],[1,0,2,2,2,2],[0,1,2,4,3,1],[0,1,4,3,4,4],[1,0,5,1,1,5]]"

@[implicit_reducible]
def «OneVariable M2842» : Magma (Fin 6) where
  op := finOpTable "[[1,2,1,0,0,4],[5,4,0,1,1,0],[3,0,2,2,4,5],[3,4,2,4,3,1],[0,1,2,3,4,1],[4,0,2,1,4,5]]"

@[implicit_reducible]
def «OneVariable M2842^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,3,0,4],[2,4,0,4,1,0],[1,0,2,2,2,2],[0,1,2,4,3,1],[0,1,4,3,4,4],[4,0,5,1,1,5]]"

@[implicit_reducible]
def «OneVariable M2844» : Magma (Fin 6) where
  op := finOpTable "[[2,4,0,1,4,0],[3,3,5,0,1,1],[0,3,5,1,2,2],[1,2,1,5,4,3],[4,5,2,4,3,4],[0,1,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M2844^op» : Magma (Fin 6) where
  op := finOpTable "[[2,3,0,1,4,0],[4,3,3,2,5,1],[0,5,5,1,2,2],[1,0,1,5,4,3],[4,1,2,4,3,4],[0,1,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M2846» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,3,0],[2,4,0,1,1],[4,0,3,2,4],[0,1,2,3,4],[0,1,3,4,3]]"

@[implicit_reducible]
def «OneVariable M2846^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,0,0],[2,4,0,1,1],[3,0,3,2,3],[3,1,2,3,4],[0,1,4,4,3]]"

@[implicit_reducible]
def «OneVariable M2863» : Magma (Fin 5) where
  op := finOpTable "[[1,0,4,3,0],[2,1,0,0,4],[3,0,2,3,1],[0,1,2,3,1],[0,4,2,3,1]]"

@[implicit_reducible]
def «OneVariable M2863^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,0],[0,1,0,1,4],[4,0,2,2,2],[3,0,3,3,3],[0,4,1,1,1]]"

@[implicit_reducible]
def «OneVariable M2935» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,1,0],[2,1,0,3,0],[3,0,2,1,4],[0,4,2,3,0],[0,4,4,0,2]]"

@[implicit_reducible]
def «OneVariable M2935^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,0],[2,1,0,4,4],[4,0,2,2,4],[1,3,1,3,0],[0,0,4,0,2]]"

@[implicit_reducible]
def «OneVariable M2982» : Magma (Fin 5) where
  op := finOpTable "[[2,4,0,2,3],[4,1,3,0,2],[0,4,2,3,1],[2,3,3,2,4],[1,0,3,4,1]]"

@[implicit_reducible]
def «OneVariable M2982^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,0,2,1],[4,1,4,3,0],[0,3,2,3,3],[2,0,3,2,4],[3,2,1,4,1]]"

@[implicit_reducible]
def «OneVariable M3027» : Magma (Fin 5) where
  op := finOpTable "[[2,4,0,2,1],[4,1,4,4,0],[0,4,2,3,4],[2,4,3,2,2],[2,3,4,1,1]]"

@[implicit_reducible]
def «OneVariable M3029» : Magma (Fin 6) where
  op := finOpTable "[[1,4,5,3,1,0],[2,5,0,5,0,1],[3,0,2,3,4,5],[0,5,2,3,4,5],[1,0,2,3,4,5],[0,1,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M3029^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,1,0],[4,5,0,5,0,1],[5,0,2,2,2,2],[3,5,3,3,3,3],[1,0,4,4,4,4],[0,1,5,5,5,5]]"

@[implicit_reducible]
def «OneVariable M3031» : Magma (Fin 5) where
  op := finOpTable "[[1,3,4,1,0],[2,1,0,0,1],[3,0,2,4,4],[0,0,3,3,2],[0,1,2,0,4]]"

@[implicit_reducible]
def «OneVariable M3031^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,0],[3,1,0,0,1],[4,0,2,3,2],[1,0,4,3,0],[0,1,4,2,4]]"

@[implicit_reducible]
def «OneVariable M3032» : Magma (Fin 6) where
  op := finOpTable "[[1,4,5,3,1,0],[2,1,0,0,0,3],[3,0,2,5,4,3],[0,4,5,5,3,2],[1,0,4,3,2,5],[0,3,3,1,5,5]]"

@[implicit_reducible]
def «OneVariable M3032^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,1,0],[4,1,0,4,0,3],[5,0,2,5,4,3],[3,0,5,5,3,1],[1,0,4,3,2,5],[0,3,3,2,5,5]]"

@[implicit_reducible]
def «OneVariable M3034» : Magma (Fin 6) where
  op := finOpTable "[[1,2,1,3,0,4],[5,1,0,3,3,0],[3,0,2,0,4,3],[0,3,5,5,1,2],[0,4,4,5,2,3],[1,0,3,4,3,5]]"

@[implicit_reducible]
def «OneVariable M3034^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,0,0,1],[2,1,0,3,4,0],[1,0,2,5,4,3],[3,3,0,5,5,4],[0,3,4,1,2,3],[4,0,3,2,3,5]]"

@[implicit_reducible]
def «OneVariable M3067» : Magma (Fin 4) where
  op := finOpTable "[[1,0,3,0],[2,1,0,0],[3,0,2,3],[0,0,3,2]]"

@[implicit_reducible]
def «OneVariable M3067^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[0,1,0,0],[3,0,2,3],[0,0,3,2]]"

@[implicit_reducible]
def «OneVariable M3084» : Magma (Fin 6) where
  op := finOpTable "[[1,2,5,3,5,0],[4,5,0,3,0,1],[3,0,5,3,4,2],[0,5,2,3,4,5],[5,0,1,3,4,5],[0,1,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M3084^op» : Magma (Fin 6) where
  op := finOpTable "[[1,4,3,0,5,0],[2,5,0,5,0,1],[5,0,5,2,1,2],[3,3,3,3,3,3],[5,0,4,4,4,4],[0,1,2,5,5,5]]"

@[implicit_reducible]
def «OneVariable M3109» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,0,0,1],[2,1,0,3,3,0],[4,0,2,1,4,3],[3,3,0,5,5,4],[0,2,4,5,2,3],[1,0,3,2,3,5]]"

@[implicit_reducible]
def «OneVariable M3109^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,4,3,0,1],[5,1,0,3,2,0],[3,0,2,0,4,3],[0,3,1,5,5,2],[0,3,4,5,2,3],[1,0,3,4,3,5]]"

@[implicit_reducible]
def «OneVariable M3110» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,0,0,1],[2,1,0,2,3,0],[4,0,2,3,4,5],[3,4,3,4,1,0],[0,3,2,5,4,3],[4,0,5,2,3,2]]"

@[implicit_reducible]
def «OneVariable M3110^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,4,3,0,4],[5,1,0,4,3,0],[3,0,2,3,2,5],[0,2,3,4,5,2],[0,3,4,1,4,3],[1,0,5,0,3,2]]"

@[implicit_reducible]
def «OneVariable M3113» : Magma (Fin 6) where
  op := finOpTable "[[1,4,3,0,5,0],[2,1,0,3,0,2],[5,0,2,3,4,4],[3,1,4,3,5,3],[1,0,4,2,2,3],[0,1,2,4,0,5]]"

@[implicit_reducible]
def «OneVariable M3113^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,5,3,1,0],[4,1,0,1,0,1],[3,0,2,4,4,2],[0,3,3,3,2,4],[5,0,4,5,2,0],[0,2,4,3,3,5]]"

@[implicit_reducible]
def «OneVariable M3115» : Magma (Fin 6) where
  op := finOpTable "[[2,5,0,1,5,5],[2,3,1,4,5,1],[0,2,2,5,4,3],[1,0,5,3,1,0],[0,5,4,1,2,4],[5,1,3,0,4,2]]"

@[implicit_reducible]
def «OneVariable M3115^op» : Magma (Fin 6) where
  op := finOpTable "[[2,2,0,1,0,5],[5,3,2,0,5,1],[0,1,2,5,4,3],[1,4,5,3,1,0],[5,5,4,1,2,4],[5,1,3,0,4,2]]"

@[implicit_reducible]
def «OneVariable M3116» : Magma (Fin 6) where
  op := finOpTable "[[1,4,3,0,5,0],[2,5,0,5,0,1],[5,0,2,0,4,0],[4,4,2,3,4,5],[1,0,2,4,3,5],[0,1,2,1,4,5]]"

@[implicit_reducible]
def «OneVariable M3116^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,5,4,1,0],[4,5,0,4,0,1],[3,0,2,2,2,2],[0,5,0,3,4,1],[5,0,4,4,3,4],[0,1,0,5,5,5]]"

@[implicit_reducible]
def «OneVariable M3134» : Magma (Fin 6) where
  op := finOpTable "[[1,4,5,3,1,0],[2,1,0,3,0,0],[3,0,5,1,3,2],[0,3,4,4,2,1],[5,0,3,5,4,3],[0,1,2,0,3,5]]"

@[implicit_reducible]
def «OneVariable M3134^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,5,0],[4,1,0,3,0,1],[5,0,5,4,3,2],[3,3,1,4,5,0],[1,0,3,2,4,3],[0,0,2,1,3,5]]"

@[implicit_reducible]
def «OneVariable M3165» : Magma (Fin 6) where
  op := finOpTable "[[1,5,4,1,0,1],[2,4,0,1,1,0],[3,0,4,2,2,5],[0,1,2,3,4,5],[0,1,2,4,3,5],[4,0,5,4,5,2]]"

@[implicit_reducible]
def «OneVariable M3165^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,0,4],[5,4,0,1,1,0],[4,0,4,2,2,5],[1,1,2,3,4,4],[0,1,2,4,3,5],[1,0,5,5,5,2]]"

@[implicit_reducible]
def «OneVariable M3206» : Magma (Fin 6) where
  op := finOpTable "[[1,4,1,3,5,0],[2,1,0,5,0,3],[3,0,2,3,4,2],[0,2,3,5,5,1],[1,0,4,2,2,3],[0,3,4,4,3,5]]"

@[implicit_reducible]
def «OneVariable M3206^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,1,0],[4,1,0,2,0,3],[1,0,2,3,4,4],[3,5,3,5,2,4],[5,0,4,5,2,3],[0,3,2,1,3,5]]"

@[implicit_reducible]
def «OneVariable M3234» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,5,0],[4,1,0,3,0,3],[5,0,2,4,0,2],[3,3,2,1,0,0],[5,0,0,3,5,4],[0,0,0,0,4,5]]"

@[implicit_reducible]
def «OneVariable M3234^op» : Magma (Fin 6) where
  op := finOpTable "[[1,4,5,3,5,0],[2,1,0,3,0,0],[3,0,2,2,0,0],[0,3,4,1,3,0],[5,0,0,0,5,4],[0,3,2,0,4,5]]"

@[implicit_reducible]
def «OneVariable M3237» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,0,1],[5,4,0,0,1,0],[4,0,2,3,2,5],[3,4,3,3,2,5],[0,1,0,2,4,5],[4,0,2,3,5,5]]"

@[implicit_reducible]
def «OneVariable M3237^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,4,3,0,4],[2,4,0,4,1,0],[3,0,2,3,0,2],[0,0,3,3,2,3],[0,1,2,2,4,5],[1,0,5,5,5,5]]"

@[implicit_reducible]
def «OneVariable M3238» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,0,1],[5,1,0,5,3,0],[4,0,5,5,3,2],[3,4,0,4,2,3],[0,3,3,1,4,2],[4,0,2,3,3,5]]"

@[implicit_reducible]
def «OneVariable M3238^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,4,3,0,4],[2,1,0,4,3,0],[3,0,5,0,3,2],[0,5,5,4,1,3],[0,3,3,2,4,3],[1,0,2,3,2,5]]"

@[implicit_reducible]
def «OneVariable M3245» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,5,0],[4,5,0,5,0,1],[5,0,5,5,3,2],[2,1,5,4,2,3],[5,0,3,2,5,4],[0,1,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M3245^op» : Magma (Fin 6) where
  op := finOpTable "[[1,4,5,2,5,0],[2,5,0,1,0,1],[3,0,5,5,3,2],[0,5,5,4,2,3],[5,0,3,2,5,4],[0,1,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M3246» : Magma (Fin 5) where
  op := finOpTable "[[1,0,3,2,3],[0,1,2,3,1],[3,2,1,4,3],[1,3,0,2,2],[3,1,3,1,4]]"

@[implicit_reducible]
def «OneVariable M3247» : Magma (Fin 4) where
  op := finOpTable "[[3,0,1,2],[0,1,2,0],[1,2,1,0],[2,3,0,3]]"

@[implicit_reducible]
def «OneVariable M3251» : Magma (Fin 5) where
  op := finOpTable "[[2,2,0,1,4],[4,3,1,0,1],[0,1,2,3,4],[1,0,3,2,3],[4,0,4,0,0]]"

@[implicit_reducible]
def «OneVariable M3251^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,0,1,4],[2,3,1,0,0],[0,1,2,3,4],[1,0,3,2,0],[4,1,4,3,0]]"

@[implicit_reducible]
def «OneVariable M3255» : Magma (Fin 3) where
  op := finOpTable "[[2,0,2],[0,0,1],[2,1,1]]"

@[implicit_reducible]
def «OneVariable M3271» : Magma (Fin 4) where
  op := finOpTable "[[2,0,1,0],[3,1,0,3],[2,0,2,3],[0,1,2,3]]"

@[implicit_reducible]
def «OneVariable M3271^op» : Magma (Fin 4) where
  op := finOpTable "[[2,3,2,0],[0,1,0,1],[1,0,2,2],[0,3,3,3]]"

@[implicit_reducible]
def «OneVariable M3274» : Magma (Fin 4) where
  op := finOpTable "[[3,3,0,1],[2,1,2,0],[0,2,2,3],[3,1,2,3]]"

@[implicit_reducible]
def «OneVariable M3274^op» : Magma (Fin 4) where
  op := finOpTable "[[3,2,0,3],[3,1,2,1],[0,2,2,2],[1,0,3,3]]"

@[implicit_reducible]
def «OneVariable M3277» : Magma (Fin 4) where
  op := finOpTable "[[3,1,0,0],[0,2,1,1],[2,2,0,3],[3,3,2,1]]"

@[implicit_reducible]
def «OneVariable M3277^op» : Magma (Fin 4) where
  op := finOpTable "[[3,0,2,3],[1,2,2,3],[0,1,0,2],[0,1,3,1]]"

@[implicit_reducible]
def «OneVariable M3296» : Magma (Fin 3) where
  op := finOpTable "[[1,2,1],[1,1,0],[1,2,2]]"

@[implicit_reducible]
def «OneVariable M3296^op» : Magma (Fin 3) where
  op := finOpTable "[[1,1,1],[2,1,2],[1,0,2]]"

@[implicit_reducible]
def «OneVariable M3314» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[1,1,0,1],[3,1,2,2],[0,0,3,3]]"

@[implicit_reducible]
def «OneVariable M3314^op» : Magma (Fin 4) where
  op := finOpTable "[[1,1,3,0],[2,1,1,0],[3,0,2,3],[0,1,2,3]]"

@[implicit_reducible]
def «OneVariable M3324» : Magma (Fin 4) where
  op := finOpTable "[[2,2,1,3],[3,1,0,1],[2,0,2,0],[0,1,2,3]]"

@[implicit_reducible]
def «OneVariable M3324^op» : Magma (Fin 4) where
  op := finOpTable "[[2,3,2,0],[2,1,0,1],[1,0,2,2],[3,1,0,3]]"

@[implicit_reducible]
def «OneVariable M3329» : Magma (Fin 6) where
  op := finOpTable "[[3,0,1,4,3,5],[2,0,0,3,5,1],[1,1,2,3,4,3],[3,1,5,5,0,2],[0,5,2,0,4,5],[0,4,3,5,1,1]]"

@[implicit_reducible]
def «OneVariable M3329^op» : Magma (Fin 6) where
  op := finOpTable "[[3,2,1,3,0,0],[0,0,1,1,5,4],[1,0,2,5,2,3],[4,3,3,5,0,5],[3,5,4,0,4,1],[5,1,3,2,5,1]]"

@[implicit_reducible]
def «OneVariable M3331» : Magma (Fin 6) where
  op := finOpTable "[[3,1,3,2,5,0],[0,5,5,1,3,2],[3,5,2,0,2,1],[3,4,0,1,1,5],[5,3,4,1,4,0],[4,5,1,3,0,0]]"

@[implicit_reducible]
def «OneVariable M3331^op» : Magma (Fin 6) where
  op := finOpTable "[[3,0,3,3,5,4],[1,5,5,4,3,5],[3,5,2,0,4,1],[2,1,0,1,1,3],[5,3,2,1,4,0],[0,2,1,5,0,0]]"

@[implicit_reducible]
def «OneVariable M3335» : Magma (Fin 4) where
  op := finOpTable "[[2,3,1,3],[2,1,0,0],[2,0,2,2],[0,1,3,3]]"

@[implicit_reducible]
def «OneVariable M3335^op» : Magma (Fin 4) where
  op := finOpTable "[[2,2,2,0],[3,1,0,1],[1,0,2,3],[3,0,2,3]]"

@[implicit_reducible]
def «OneVariable M3347» : Magma (Fin 4) where
  op := finOpTable "[[2,3,1,0],[3,1,0,1],[2,3,2,1],[0,3,3,3]]"

@[implicit_reducible]
def «OneVariable M3347^op» : Magma (Fin 4) where
  op := finOpTable "[[2,3,2,0],[3,1,3,3],[1,0,2,3],[0,1,1,3]]"

@[implicit_reducible]
def «OneVariable M3363» : Magma (Fin 4) where
  op := finOpTable "[[2,2,1,0],[3,1,2,3],[2,0,2,3],[0,2,2,3]]"

@[implicit_reducible]
def «OneVariable M3363^op» : Magma (Fin 4) where
  op := finOpTable "[[2,3,2,0],[2,1,0,2],[1,2,2,2],[0,3,3,3]]"

@[implicit_reducible]
def «OneVariable M3376» : Magma (Fin 4) where
  op := finOpTable "[[3,3,0,1],[2,1,3,0],[0,1,2,2],[3,0,3,3]]"

@[implicit_reducible]
def «OneVariable M3376^op» : Magma (Fin 4) where
  op := finOpTable "[[3,2,0,3],[3,1,1,0],[0,3,2,3],[1,0,2,3]]"

@[implicit_reducible]
def «OneVariable M3377» : Magma (Fin 4) where
  op := finOpTable "[[2,2,1,0],[3,1,0,1],[2,0,2,2],[3,3,2,3]]"

@[implicit_reducible]
def «OneVariable M3377^op» : Magma (Fin 4) where
  op := finOpTable "[[2,3,2,3],[2,1,0,3],[1,0,2,2],[0,1,2,3]]"

@[implicit_reducible]
def «OneVariable M3384» : Magma (Fin 7) where
  op := finOpTable "[[4,4,5,0,1,0,6],[3,1,0,3,0,6,3],[5,0,2,2,3,3,4],[0,3,1,3,4,5,6],[4,0,6,4,6,5,2],[2,6,0,5,4,0,5],[0,5,4,6,6,1,5]]"

@[implicit_reducible]
def «OneVariable M3384^op» : Magma (Fin 7) where
  op := finOpTable "[[4,3,5,0,4,2,0],[4,1,0,3,0,6,5],[5,0,2,1,6,0,4],[0,3,2,3,4,5,6],[1,0,3,4,6,4,6],[0,6,3,5,5,0,1],[6,3,4,6,2,5,5]]"

@[implicit_reducible]
def «OneVariable M3386» : Magma (Fin 5) where
  op := finOpTable "[[2,3,1,1,0],[4,1,0,2,0],[2,0,2,3,3],[0,1,2,3,3],[0,1,2,0,4]]"

@[implicit_reducible]
def «OneVariable M3386^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,2,0,0],[3,1,0,1,1],[1,0,2,2,2],[1,2,3,3,0],[0,0,3,3,4]]"

@[implicit_reducible]
def «OneVariable M3414» : Magma (Fin 5) where
  op := finOpTable "[[4,0,2,0,0],[1,0,1,3,1],[2,2,1,2,4],[0,3,3,2,3],[4,1,4,4,3]]"

@[implicit_reducible]
def «OneVariable M3414^op» : Magma (Fin 5) where
  op := finOpTable "[[4,1,2,0,4],[0,0,2,3,1],[2,1,1,3,4],[0,3,2,2,4],[0,1,4,3,3]]"

@[implicit_reducible]
def «OneVariable M3422» : Magma (Fin 8) where
  op := finOpTable "[[3,0,2,5,0,3,3,7],[0,2,5,1,1,2,2,2],[2,2,4,3,6,5,4,4],[3,6,3,1,4,1,1,1],[7,1,4,4,0,5,6,0],[1,4,1,0,3,5,6,7],[4,3,0,2,2,5,6,7],[4,3,1,0,3,5,6,7]]"

@[implicit_reducible]
def «OneVariable M3422^op» : Magma (Fin 8) where
  op := finOpTable "[[3,0,2,3,7,1,4,4],[0,2,2,6,1,4,3,3],[2,5,4,3,4,1,0,1],[5,1,3,1,4,0,2,0],[0,1,6,4,0,3,2,3],[3,2,5,1,5,5,5,5],[3,2,4,1,6,6,6,6],[7,2,4,1,0,7,7,7]]"

@[implicit_reducible]
def «OneVariable M3442» : Magma (Fin 8) where
  op := finOpTable "[[0,0,4,7,0,6,5,0],[1,1,4,1,3,6,2,5],[4,6,4,2,0,5,2,6],[7,4,2,7,3,3,7,0],[2,3,4,1,3,4,6,4],[6,7,5,3,0,6,0,5],[5,2,1,7,6,6,2,7],[3,5,7,7,4,1,7,5]]"

@[implicit_reducible]
def «OneVariable M3442^op» : Magma (Fin 8) where
  op := finOpTable "[[0,1,4,7,2,6,5,3],[0,1,6,4,3,7,2,5],[4,4,4,2,4,5,1,7],[7,1,2,7,1,3,7,7],[0,3,0,3,3,0,6,4],[6,6,5,3,4,6,6,1],[5,2,2,7,6,0,2,7],[0,5,6,0,4,5,7,5]]"

@[implicit_reducible]
def «OneVariable M3445» : Magma (Fin 8) where
  op := finOpTable "[[7,1,7,0,0,3,2,2],[1,3,1,6,2,5,3,6],[4,4,1,2,1,2,6,5],[5,3,2,0,5,0,1,3],[0,7,3,6,6,4,3,4],[6,5,7,7,4,2,5,2],[5,0,6,4,6,0,5,7],[7,4,0,3,1,1,7,4]]"

@[implicit_reducible]
def «OneVariable M3445^op» : Magma (Fin 8) where
  op := finOpTable "[[7,1,4,5,0,6,5,7],[1,3,4,3,7,5,0,4],[7,1,1,2,3,7,6,0],[0,6,2,0,6,7,4,3],[0,2,1,5,6,4,6,1],[3,5,2,0,4,2,0,1],[2,3,6,1,3,5,5,7],[2,6,5,3,4,2,7,4]]"

@[implicit_reducible]
def «OneVariable M3458» : Magma (Fin 6) where
  op := finOpTable "[[0,1,5,5,1,2],[5,1,2,5,4,3],[5,1,3,4,3,2],[2,5,3,5,2,1],[0,1,3,2,4,2],[2,3,0,5,3,2]]"

@[implicit_reducible]
def «OneVariable M3458^op» : Magma (Fin 6) where
  op := finOpTable "[[0,5,5,2,0,2],[1,1,1,5,1,3],[5,2,3,3,3,0],[5,5,4,5,2,5],[1,4,3,2,4,3],[2,3,2,1,2,2]]"

@[implicit_reducible]
def «OneVariable M3463» : Magma (Fin 8) where
  op := finOpTable "[[2,0,7,1,0,5,6,0],[3,0,1,1,4,1,1,5],[2,1,4,3,6,2,2,0],[1,0,3,3,5,4,3,3],[0,4,4,4,5,3,2,4],[5,7,2,4,5,1,6,5],[6,1,4,7,2,6,6,6],[2,5,0,7,4,1,0,7]]"

@[implicit_reducible]
def «OneVariable M3463^op» : Magma (Fin 8) where
  op := finOpTable "[[2,3,2,1,0,5,6,2],[0,0,1,0,4,7,1,5],[7,1,4,3,4,2,4,0],[1,1,3,3,4,4,7,7],[0,4,6,5,5,5,2,4],[5,1,2,4,3,1,6,1],[6,1,2,3,2,6,6,0],[0,5,0,3,4,5,6,7]]"

@[implicit_reducible]
def «OneVariable M3466» : Magma (Fin 8) where
  op := finOpTable "[[7,3,0,0,4,5,7,6],[3,1,7,0,5,4,7,2],[0,7,5,2,2,6,5,2],[1,0,2,0,3,5,4,3],[4,5,2,6,3,4,3,4],[5,4,5,5,1,4,2,7],[7,6,5,4,3,2,6,0],[7,2,1,3,4,7,0,2]]"

@[implicit_reducible]
def «OneVariable M3466^op» : Magma (Fin 8) where
  op := finOpTable "[[7,3,0,1,4,5,7,7],[3,1,7,0,5,4,6,2],[0,7,5,2,2,5,5,1],[0,0,2,0,6,5,4,3],[4,5,2,3,3,1,3,4],[5,4,6,5,4,4,2,7],[7,7,5,4,3,2,6,0],[6,2,2,3,4,7,0,2]]"

@[implicit_reducible]
def «OneVariable M3468» : Magma (Fin 8) where
  op := finOpTable "[[7,3,7,0,0,5,6,2],[3,1,5,7,2,4,2,0],[4,7,2,5,4,0,6,0],[1,0,5,0,4,3,3,3],[0,5,4,4,5,1,7,4],[5,4,3,2,5,3,5,7],[7,7,2,0,7,7,6,5],[7,0,0,3,6,7,4,4]]"

@[implicit_reducible]
def «OneVariable M3468^op» : Magma (Fin 8) where
  op := finOpTable "[[7,3,4,1,0,5,7,7],[3,1,7,0,5,4,7,0],[7,5,2,5,4,3,2,0],[0,7,5,0,4,2,0,3],[0,2,4,4,5,5,7,6],[5,4,0,3,1,3,7,7],[6,2,6,3,7,5,6,4],[2,0,0,3,4,7,5,4]]"

@[implicit_reducible]
def «OneVariable M3469» : Magma (Fin 8) where
  op := finOpTable "[[1,2,1,3,7,0,6,0],[1,5,0,1,5,4,3,7],[3,0,2,5,0,6,0,6],[0,1,5,6,6,3,4,3],[7,6,4,0,4,1,3,1],[0,5,3,2,1,3,5,2],[6,1,7,6,3,5,7,2],[4,7,6,3,0,7,7,0]]"

@[implicit_reducible]
def «OneVariable M3469^op» : Magma (Fin 8) where
  op := finOpTable "[[1,1,3,0,7,0,6,4],[2,5,0,1,6,5,1,7],[1,0,2,5,4,3,7,6],[3,1,5,6,0,2,6,3],[7,5,0,6,4,1,3,0],[0,4,6,3,1,3,5,7],[6,3,0,4,3,5,7,7],[0,7,6,3,1,2,2,0]]"

@[implicit_reducible]
def «OneVariable M3474» : Magma (Fin 8) where
  op := finOpTable "[[5,4,3,0,0,2,2,7],[4,1,0,7,0,5,6,3],[5,0,2,1,7,0,7,4],[0,4,3,7,3,3,5,1],[1,5,7,3,0,4,2,4],[5,3,0,6,4,3,7,5],[6,6,1,5,0,3,6,5],[7,3,0,7,2,5,7,4]]"

@[implicit_reducible]
def «OneVariable M3474^op» : Magma (Fin 8) where
  op := finOpTable "[[5,4,5,0,1,5,6,7],[4,1,0,4,5,3,6,3],[3,0,2,3,7,0,1,0],[0,7,1,7,3,6,5,7],[0,0,7,3,0,4,0,2],[2,5,0,3,4,3,3,5],[2,6,7,5,2,7,6,7],[7,3,4,1,4,5,5,4]]"

@[implicit_reducible]
def «OneVariable M3475» : Magma (Fin 8) where
  op := finOpTable "[[1,2,3,4,4,0,7,0],[1,5,0,1,1,6,4,7],[1,0,2,5,7,3,6,4],[0,1,5,4,6,3,7,3],[4,1,0,4,7,5,3,2],[0,5,4,2,5,3,1,7],[7,5,6,4,3,1,6,0],[6,7,4,3,7,0,5,0]]"

@[implicit_reducible]
def «OneVariable M3475^op» : Magma (Fin 8) where
  op := finOpTable "[[1,1,1,0,4,0,7,6],[2,5,0,1,1,5,5,7],[3,0,2,5,0,4,6,4],[4,1,5,4,4,2,4,3],[4,1,7,6,7,5,3,7],[0,6,3,3,5,3,1,0],[7,4,6,7,3,1,6,5],[0,7,4,3,2,7,0,0]]"

@[implicit_reducible]
def «OneVariable M3476» : Magma (Fin 8) where
  op := finOpTable "[[6,5,7,3,7,0,1,0],[5,1,5,0,7,3,0,3],[7,5,3,4,7,2,6,2],[3,0,3,7,2,5,6,1],[7,2,7,2,4,6,2,5],[0,3,1,5,6,2,5,7],[6,0,6,6,3,4,5,7],[4,3,2,7,6,7,7,0]]"

@[implicit_reducible]
def «OneVariable M3476^op» : Magma (Fin 8) where
  op := finOpTable "[[6,5,7,3,7,0,6,4],[5,1,5,0,2,3,0,3],[7,5,3,3,7,1,6,2],[3,0,4,7,2,5,6,7],[7,7,7,2,4,6,3,6],[0,3,2,5,6,2,4,7],[1,0,6,6,2,5,5,7],[0,3,2,1,5,7,7,0]]"

@[implicit_reducible]
def «OneVariable M3496» : Magma (Fin 6) where
  op := finOpTable "[[1,5,0,2,0,1],[1,2,4,1,2,0],[3,2,0,0,1,2],[2,1,5,3,4,5],[0,3,1,3,4,5],[4,0,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M3496^op» : Magma (Fin 6) where
  op := finOpTable "[[1,1,3,2,0,4],[5,2,2,1,3,0],[0,4,0,5,1,2],[2,1,0,3,3,3],[0,2,1,4,4,4],[1,0,2,5,5,5]]"

@[implicit_reducible]
def «OneVariable M3497» : Magma (Fin 8) where
  op := finOpTable "[[1,2,1,0,3,0,6,7],[1,5,0,3,5,4,6,1],[3,0,2,6,0,6,0,5],[4,3,6,0,0,2,3,7],[3,0,4,6,4,1,7,0],[0,5,7,5,1,7,5,2],[6,6,3,2,7,5,3,6],[7,1,5,7,6,7,4,6]]"

@[implicit_reducible]
def «OneVariable M3497^op» : Magma (Fin 8) where
  op := finOpTable "[[1,1,3,4,3,0,6,7],[2,5,0,3,0,5,6,1],[1,0,2,6,4,7,3,5],[0,3,6,0,6,5,2,7],[3,5,0,0,4,1,7,6],[0,4,6,2,1,7,5,7],[6,6,0,3,7,5,3,4],[7,1,5,7,0,2,6,6]]"

@[implicit_reducible]
def «OneVariable M3499» : Magma (Fin 6) where
  op := finOpTable "[[0,2,3,3,1,5],[2,4,1,1,0,3],[3,1,2,4,5,4],[3,5,4,1,3,0],[1,4,5,2,3,4],[5,3,0,0,4,5]]"

@[implicit_reducible]
def «OneVariable M3499^op» : Magma (Fin 6) where
  op := finOpTable "[[0,2,3,3,1,5],[2,4,1,5,4,3],[3,1,2,4,5,0],[3,1,4,1,2,0],[1,0,5,3,3,4],[5,3,4,0,4,5]]"

@[implicit_reducible]
def «OneVariable M3502» : Magma (Fin 8) where
  op := finOpTable "[[1,2,3,3,7,5,0,0],[1,6,0,4,5,1,4,7],[6,0,2,2,4,4,4,5],[0,4,0,3,3,6,7,5],[7,5,2,1,4,5,1,1],[5,1,0,6,5,7,5,2],[0,6,6,7,1,3,5,6],[4,7,5,7,1,7,6,0]]"

@[implicit_reducible]
def «OneVariable M3502^op» : Magma (Fin 8) where
  op := finOpTable "[[1,1,6,0,7,5,0,4],[2,6,0,4,5,1,6,7],[3,0,2,0,2,0,6,5],[3,4,2,3,1,6,7,7],[7,5,4,3,4,5,1,1],[5,1,4,6,5,7,3,7],[0,4,4,7,1,5,5,6],[0,7,5,5,1,2,6,0]]"

@[implicit_reducible]
def «OneVariable M3512» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[1,1,3,2],[1,0,2,0],[0,2,0,3]]"

@[implicit_reducible]
def «OneVariable M3512^op» : Magma (Fin 4) where
  op := finOpTable "[[1,1,1,0],[2,1,0,2],[3,3,2,0],[0,2,0,3]]"

@[implicit_reducible]
def «OneVariable M3517» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[1,1,0,3],[1,2,2,3],[0,1,2,3]]"

@[implicit_reducible]
def «OneVariable M3517^op» : Magma (Fin 4) where
  op := finOpTable "[[1,1,1,0],[2,1,2,1],[3,0,2,2],[0,3,3,3]]"

@[implicit_reducible]
def «OneVariable M3521» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,4,0],[1,1,0,0,0],[3,0,2,2,2],[0,0,0,3,3],[0,0,0,0,4]]"

@[implicit_reducible]
def «OneVariable M3521^op» : Magma (Fin 5) where
  op := finOpTable "[[1,1,3,0,0],[2,1,0,0,0],[4,0,2,0,0],[4,0,2,3,0],[0,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M3525» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[1,1,0,1],[1,0,2,3],[3,1,2,3]]"

@[implicit_reducible]
def «OneVariable M3525^op» : Magma (Fin 4) where
  op := finOpTable "[[1,1,1,3],[2,1,0,1],[3,0,2,2],[0,1,3,3]]"

@[implicit_reducible]
def «OneVariable M3530» : Magma (Fin 7) where
  op := finOpTable "[[1,6,2,0,5,0,3],[1,2,4,1,3,5,0],[0,2,5,6,1,3,2],[0,1,5,3,3,2,6],[5,2,1,0,4,0,4],[4,1,5,2,6,0,5],[1,0,2,6,0,5,6]]"

@[implicit_reducible]
def «OneVariable M3530^op» : Magma (Fin 7) where
  op := finOpTable "[[1,1,0,0,5,4,1],[6,2,2,1,2,1,0],[2,4,5,5,1,5,2],[0,1,6,3,0,2,6],[5,3,1,3,4,6,0],[0,5,3,2,0,0,5],[3,0,2,6,4,5,6]]"

@[implicit_reducible]
def «OneVariable M3534» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,0],[1,1,0,3,4],[4,0,2,3,4],[3,1,2,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M3534^op» : Magma (Fin 5) where
  op := finOpTable "[[1,1,4,3,0],[2,1,0,1,1],[3,0,2,2,2],[0,3,3,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M3537» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,0,0],[1,1,0,0,0],[3,0,2,2,2],[4,0,0,3,3],[0,0,0,0,4]]"

@[implicit_reducible]
def «OneVariable M3537^op» : Magma (Fin 5) where
  op := finOpTable "[[1,1,3,4,0],[2,1,0,0,0],[4,0,2,0,0],[0,0,2,3,0],[0,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M3541» : Magma (Fin 7) where
  op := finOpTable "[[1,3,2,6,5,0,0],[1,2,4,0,6,5,1],[0,2,5,6,1,3,2],[6,0,6,3,6,2,3],[5,6,1,3,4,6,4],[4,1,5,2,6,0,5],[0,1,2,2,6,5,6]]"

@[implicit_reducible]
def «OneVariable M3541^op» : Magma (Fin 7) where
  op := finOpTable "[[1,1,0,6,5,4,0],[3,2,2,0,6,1,1],[2,4,5,6,1,5,2],[6,0,6,3,3,2,2],[5,6,1,6,4,6,6],[0,5,3,2,6,0,5],[0,1,2,3,4,5,6]]"

@[implicit_reducible]
def «OneVariable M3547» : Magma (Fin 8) where
  op := finOpTable "[[1,2,5,3,4,0,6,0],[1,5,1,6,4,3,1,7],[1,0,2,3,7,6,5,4],[7,5,3,3,6,1,4,0],[4,4,0,4,7,5,4,2],[0,5,4,5,5,6,2,7],[6,1,0,0,3,6,4,6],[3,7,1,1,7,7,6,0]]"

@[implicit_reducible]
def «OneVariable M3547^op» : Magma (Fin 8) where
  op := finOpTable "[[1,1,1,7,4,0,6,3],[2,5,0,5,4,5,1,7],[5,1,2,3,0,4,0,1],[3,6,3,3,4,5,0,1],[4,4,7,6,7,5,3,7],[0,3,6,1,5,6,6,7],[6,1,5,4,4,2,4,6],[0,7,4,0,2,7,6,0]]"

@[implicit_reducible]
def «OneVariable M3553» : Magma (Fin 8) where
  op := finOpTable "[[1,2,5,7,4,0,3,0],[1,5,0,2,6,4,1,7],[1,3,4,2,5,7,6,2],[6,4,1,2,3,5,3,0],[4,5,4,3,7,2,0,6],[0,5,4,5,1,6,7,3],[2,1,6,0,7,6,3,5],[3,7,2,1,7,6,4,0]]"

@[implicit_reducible]
def «OneVariable M3553^op» : Magma (Fin 8) where
  op := finOpTable "[[1,1,1,6,4,0,2,3],[2,5,3,4,5,5,1,7],[5,0,4,1,4,4,6,2],[7,2,2,2,3,5,0,1],[4,6,5,3,7,1,7,7],[0,4,7,5,2,6,6,6],[3,1,6,3,0,7,3,4],[0,7,2,0,6,3,5,0]]"

@[implicit_reducible]
def «OneVariable M3557» : Magma (Fin 8) where
  op := finOpTable "[[1,2,3,0,3,7,0,7],[1,6,0,3,5,1,4,7],[1,0,2,7,2,6,5,3],[4,3,7,0,1,5,1,3],[3,6,3,0,4,7,1,5],[6,1,6,5,6,7,5,4],[0,6,7,3,1,2,5,6],[7,7,0,2,5,7,6,3]]"

@[implicit_reducible]
def «OneVariable M3557^op» : Magma (Fin 8) where
  op := finOpTable "[[1,1,1,4,3,6,0,7],[2,6,0,3,6,1,6,7],[3,0,2,7,3,6,7,0],[0,3,7,0,0,5,3,2],[3,5,2,1,4,6,1,5],[7,1,6,5,7,7,2,7],[0,4,5,1,1,5,5,6],[7,7,3,3,5,4,6,3]]"

@[implicit_reducible]
def «OneVariable M3559» : Magma (Fin 6) where
  op := finOpTable "[[1,5,0,2,0,4],[1,2,4,1,3,0],[3,2,0,5,1,2],[2,1,0,3,4,5],[0,2,1,3,4,5],[1,0,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M3559^op» : Magma (Fin 6) where
  op := finOpTable "[[1,1,3,2,0,1],[5,2,2,1,2,0],[0,4,0,0,1,2],[2,1,5,3,3,3],[0,3,1,4,4,4],[4,0,2,5,5,5]]"

@[implicit_reducible]
def «OneVariable M3561» : Magma (Fin 8) where
  op := finOpTable "[[1,2,6,3,4,0,0,5],[1,6,0,1,1,5,7,4],[3,0,2,6,0,4,4,5],[0,1,6,4,7,3,3,5],[4,1,0,4,5,2,6,3],[7,5,4,3,5,0,6,1],[0,6,5,2,6,6,3,1],[5,4,5,0,3,1,1,7]]"

@[implicit_reducible]
def «OneVariable M3561^op» : Magma (Fin 8) where
  op := finOpTable "[[1,1,3,0,4,7,0,5],[2,6,0,1,1,5,6,4],[6,0,2,6,0,4,5,5],[3,1,6,4,4,3,2,0],[4,1,0,7,5,5,6,3],[0,5,4,3,2,0,6,1],[0,7,4,3,6,6,3,1],[5,4,5,5,3,1,1,7]]"

@[implicit_reducible]
def «OneVariable M3564» : Magma (Fin 8) where
  op := finOpTable "[[1,2,4,3,0,5,0,7],[1,4,1,5,3,1,6,7],[4,0,2,0,6,4,7,0],[6,5,3,3,1,0,1,5],[0,4,6,4,5,2,4,4],[5,1,5,0,5,7,5,3],[3,6,0,1,4,5,0,6],[7,7,0,7,4,7,2,6]]"

@[implicit_reducible]
def «OneVariable M3564^op» : Magma (Fin 8) where
  op := finOpTable "[[1,1,4,6,0,5,3,7],[2,4,0,5,4,1,6,7],[4,1,2,3,6,5,0,0],[3,5,0,3,4,0,1,7],[0,3,6,1,5,5,4,4],[5,1,4,0,2,7,5,7],[0,6,7,1,4,5,0,2],[7,7,0,5,4,3,6,6]]"

@[implicit_reducible]
def «OneVariable M3567» : Magma (Fin 8) where
  op := finOpTable "[[1,2,5,7,4,0,7,0],[1,5,0,4,1,3,1,7],[5,3,2,0,0,4,7,2],[7,6,3,3,0,0,7,1],[4,1,0,6,7,5,4,2],[0,5,4,1,5,6,2,7],[7,1,5,7,3,6,4,6],[3,7,4,5,7,7,6,0]]"

@[implicit_reducible]
def «OneVariable M3567^op» : Magma (Fin 8) where
  op := finOpTable "[[1,1,5,7,4,0,7,3],[2,5,3,6,1,5,1,7],[5,0,2,3,0,4,5,4],[7,4,0,3,6,1,7,5],[4,1,0,0,7,5,3,7],[0,3,4,0,5,6,6,7],[7,1,7,7,4,2,4,6],[0,7,2,1,2,7,6,0]]"

@[implicit_reducible]
def «OneVariable M3569» : Magma (Fin 8) where
  op := finOpTable "[[1,2,3,0,0,5,7,0],[1,4,0,6,3,1,1,7],[4,0,2,2,3,0,2,5],[3,5,3,3,1,2,0,3],[0,4,4,1,5,6,7,4],[5,1,0,5,5,7,4,2],[7,7,4,0,7,4,6,1],[6,7,5,3,4,7,5,0]]"

@[implicit_reducible]
def «OneVariable M3569^op» : Magma (Fin 8) where
  op := finOpTable "[[1,1,4,3,0,5,7,6],[2,4,0,5,4,1,7,7],[3,0,2,3,4,0,4,5],[0,6,2,3,1,5,0,3],[0,3,3,1,5,5,7,4],[5,1,0,2,6,7,4,7],[7,1,2,0,7,4,6,5],[0,7,5,3,4,2,1,0]]"

@[implicit_reducible]
def «OneVariable M3571» : Magma (Fin 8) where
  op := finOpTable "[[1,2,4,0,0,6,0,7],[1,4,0,1,5,3,6,7],[3,0,2,4,7,5,7,0],[1,1,4,7,3,6,3,5],[0,4,7,2,3,1,4,4],[6,3,5,4,1,5,7,3],[5,6,7,3,4,1,0,6],[7,7,0,7,4,3,2,6]]"

@[implicit_reducible]
def «OneVariable M3571^op» : Magma (Fin 8) where
  op := finOpTable "[[1,1,3,1,0,6,5,7],[2,4,0,1,4,3,6,7],[4,0,2,4,7,5,7,0],[0,1,4,7,2,4,3,7],[0,5,7,3,3,1,4,4],[6,3,5,6,1,5,1,3],[0,6,7,3,4,7,0,2],[7,7,0,5,4,3,6,6]]"

@[implicit_reducible]
def «OneVariable M3572» : Magma (Fin 4) where
  op := finOpTable "[[1,1,1,2],[1,2,2,1],[0,2,3,3],[0,1,3,1]]"

@[implicit_reducible]
def «OneVariable M3572^op» : Magma (Fin 4) where
  op := finOpTable "[[1,1,0,0],[1,2,2,1],[1,2,3,3],[2,1,3,1]]"

@[implicit_reducible]
def «OneVariable M3593» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,1],[3,0,0,2],[1,1,2,2],[0,0,3,3]]"

@[implicit_reducible]
def «OneVariable M3593^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,1,0],[2,0,1,0],[3,0,2,3],[1,2,2,3]]"

@[implicit_reducible]
def «OneVariable M3607» : Magma (Fin 4) where
  op := finOpTable "[[1,2,1,3],[3,0,2,0],[1,1,2,2],[0,0,2,3]]"

@[implicit_reducible]
def «OneVariable M3607^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,1,0],[2,0,1,0],[1,2,2,2],[3,0,2,3]]"

@[implicit_reducible]
def «OneVariable M3608» : Magma (Fin 4) where
  op := finOpTable "[[1,2,1,1],[3,0,0,0],[1,1,2,2],[0,0,3,3]]"

@[implicit_reducible]
def «OneVariable M3608^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,1,0],[2,0,1,0],[1,0,2,3],[1,0,2,3]]"

@[implicit_reducible]
def «OneVariable M3645» : Magma (Fin 3) where
  op := finOpTable "[[1,2,1],[2,1,0],[0,0,2]]"

@[implicit_reducible]
def «OneVariable M3645^op» : Magma (Fin 3) where
  op := finOpTable "[[1,2,0],[2,1,0],[1,0,2]]"

@[implicit_reducible]
def «OneVariable M3727» : Magma (Fin 3) where
  op := finOpTable "[[1,0,1],[2,1,0],[0,0,2]]"

@[implicit_reducible]
def «OneVariable M3727^op» : Magma (Fin 3) where
  op := finOpTable "[[1,2,0],[0,1,0],[1,0,2]]"

@[implicit_reducible]
def «OneVariable M3776» : Magma (Fin 6) where
  op := finOpTable "[[4,4,2,5,0,3],[0,1,2,2,0,4],[0,3,3,2,5,4],[3,2,1,0,4,0],[1,0,4,3,2,2],[3,1,4,3,4,5]]"

@[implicit_reducible]
def «OneVariable M3776^op» : Magma (Fin 6) where
  op := finOpTable "[[4,0,0,3,1,3],[4,1,3,2,0,1],[2,2,3,1,4,4],[5,2,2,0,3,3],[0,0,5,4,2,4],[3,4,4,0,2,5]]"

@[implicit_reducible]
def «OneVariable M3783» : Magma (Fin 6) where
  op := finOpTable "[[2,4,2,2,1,5],[0,0,2,5,0,3],[3,1,5,0,5,5],[0,5,0,3,4,5],[1,1,2,5,4,2],[0,1,4,1,2,1]]"

@[implicit_reducible]
def «OneVariable M3783^op» : Magma (Fin 6) where
  op := finOpTable "[[2,0,3,0,1,0],[4,0,1,5,1,1],[2,2,5,0,2,4],[2,5,0,3,5,1],[1,0,5,4,4,2],[5,3,5,5,2,1]]"

@[implicit_reducible]
def «OneVariable M3815» : Magma (Fin 3) where
  op := finOpTable "[[1,0,1],[2,1,0],[0,1,2]]"

@[implicit_reducible]
def «OneVariable M3815^op» : Magma (Fin 3) where
  op := finOpTable "[[1,2,0],[0,1,1],[1,0,2]]"

@[implicit_reducible]
def «OneVariable M3842» : Magma (Fin 4) where
  op := finOpTable "[[2,3,1,0],[3,1,0,1],[3,0,2,0],[0,3,3,3]]"

@[implicit_reducible]
def «OneVariable M3842^op» : Magma (Fin 4) where
  op := finOpTable "[[2,3,3,0],[3,1,0,3],[1,0,2,3],[0,1,0,3]]"

@[implicit_reducible]
def «OneVariable M3884» : Magma (Fin 4) where
  op := finOpTable "[[2,3,1,0],[3,1,0,1],[3,0,2,0],[0,3,0,3]]"

@[implicit_reducible]
def «OneVariable M3884^op» : Magma (Fin 4) where
  op := finOpTable "[[2,3,3,0],[3,1,0,3],[1,0,2,0],[0,1,0,3]]"

@[implicit_reducible]
def «OneVariable M3899» : Magma (Fin 4) where
  op := finOpTable "[[1,2,1,1],[3,0,0,0],[3,1,2,2],[0,2,3,3]]"

@[implicit_reducible]
def «OneVariable M3899^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,3,0],[2,0,1,2],[1,0,2,3],[1,0,2,3]]"

@[implicit_reducible]
def «OneVariable M3940» : Magma (Fin 4) where
  op := finOpTable "[[1,3,1,1],[2,1,1,0],[0,0,2,0],[1,0,0,3]]"

@[implicit_reducible]
def «OneVariable M3940^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,1],[3,1,0,0],[1,1,2,0],[1,0,0,3]]"

@[implicit_reducible]
def «OneVariable M3947» : Magma (Fin 6) where
  op := finOpTable "[[5,5,2,4,3,1],[0,1,2,4,2,0],[0,4,4,5,1,3],[4,3,5,3,4,5],[3,2,1,0,0,5],[1,0,3,2,4,2]]"

@[implicit_reducible]
def «OneVariable M3947^op» : Magma (Fin 6) where
  op := finOpTable "[[5,0,0,4,3,1],[5,1,4,3,2,0],[2,2,4,5,1,3],[4,4,5,3,0,2],[3,2,1,4,0,4],[1,0,3,5,5,2]]"

@[implicit_reducible]
def «OneVariable M4072» : Magma (Fin 4) where
  op := finOpTable "[[1,2,1,1],[3,1,0,0],[3,0,2,2],[0,0,3,3]]"

@[implicit_reducible]
def «OneVariable M4072^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,3,0],[2,1,0,0],[1,0,2,3],[1,0,2,3]]"

@[implicit_reducible]
def «OneVariable M4166» : Magma (Fin 4) where
  op := finOpTable "[[2,2,1,2],[2,1,0,3],[3,0,2,0],[0,3,0,3]]"

@[implicit_reducible]
def «OneVariable M4166^op» : Magma (Fin 4) where
  op := finOpTable "[[2,2,3,0],[2,1,0,3],[1,0,2,0],[2,3,0,3]]"

@[implicit_reducible]
def «OneVariable M4170» : Magma (Fin 4) where
  op := finOpTable "[[2,2,1,2],[2,1,0,2],[3,0,2,0],[0,2,1,3]]"

@[implicit_reducible]
def «OneVariable M4170^op» : Magma (Fin 4) where
  op := finOpTable "[[2,2,3,0],[2,1,0,2],[1,0,2,1],[2,2,0,3]]"

@[implicit_reducible]
def «OneVariable M4215» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,3],[3,1,0,0],[1,0,2,0],[0,0,3,3]]"

@[implicit_reducible]
def «OneVariable M4215^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,1,0],[2,1,0,0],[0,0,2,3],[3,0,0,3]]"

@[implicit_reducible]
def «OneVariable M4217» : Magma (Fin 4) where
  op := finOpTable "[[2,0,1,2],[2,1,0,3],[3,0,2,0],[0,3,0,3]]"

@[implicit_reducible]
def «OneVariable M4219» : Magma (Fin 4) where
  op := finOpTable "[[2,2,1,0],[2,1,0,3],[3,0,2,0],[0,2,0,3]]"

@[implicit_reducible]
def «OneVariable M4219^op» : Magma (Fin 4) where
  op := finOpTable "[[2,2,3,0],[2,1,0,2],[1,0,2,0],[0,3,0,3]]"

@[implicit_reducible]
def «OneVariable M4233» : Magma (Fin 8) where
  op := finOpTable "[[0,6,3,2,5,0,6,0],[6,2,5,3,2,2,0,6],[3,4,3,0,1,1,6,3],[2,1,7,6,6,6,4,2],[1,1,1,6,4,5,3,7],[0,2,1,3,4,5,3,4],[1,7,2,5,3,3,1,1],[5,6,2,2,4,0,1,7]]"

@[implicit_reducible]
def «OneVariable M4233^op» : Magma (Fin 8) where
  op := finOpTable "[[0,6,3,2,1,0,1,5],[6,2,4,1,1,2,7,6],[3,5,3,7,1,1,2,2],[2,3,0,6,6,3,5,2],[5,2,1,6,4,4,3,4],[0,2,1,6,5,5,3,0],[6,0,6,4,3,3,1,1],[0,6,3,2,7,4,1,7]]"

@[implicit_reducible]
def «OneVariable M4240» : Magma (Fin 4) where
  op := finOpTable "[[2,1,3,2],[0,1,0,1],[1,0,2,0],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M4240^op» : Magma (Fin 4) where
  op := finOpTable "[[2,0,1,0],[1,1,0,0],[3,0,2,0],[2,1,0,3]]"

@[implicit_reducible]
def «OneVariable M4242» : Magma (Fin 4) where
  op := finOpTable "[[3,3,2,1],[3,1,3,0],[0,1,2,0],[2,0,0,3]]"

@[implicit_reducible]
def «OneVariable M4242^op» : Magma (Fin 4) where
  op := finOpTable "[[3,3,0,2],[3,1,1,0],[2,3,2,0],[1,0,0,3]]"

@[implicit_reducible]
def «OneVariable M4254» : Magma (Fin 4) where
  op := finOpTable "[[2,1,1,2],[0,1,0,1],[3,0,2,0],[0,3,0,3]]"

@[implicit_reducible]
def «OneVariable M4254^op» : Magma (Fin 4) where
  op := finOpTable "[[2,0,3,0],[1,1,0,3],[1,0,2,0],[2,1,0,3]]"

@[implicit_reducible]
def «OneVariable M4256» : Magma (Fin 4) where
  op := finOpTable "[[3,2,3,1],[3,1,2,0],[0,0,2,0],[2,0,0,3]]"

@[implicit_reducible]
def «OneVariable M4256^op» : Magma (Fin 4) where
  op := finOpTable "[[3,3,0,2],[2,1,0,0],[3,2,2,0],[1,0,0,3]]"

@[implicit_reducible]
def «OneVariable M4279» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,1,0],[3,0,0,0,1],[4,1,2,4,2],[0,4,2,3,3],[0,1,3,4,4]]"

@[implicit_reducible]
def «OneVariable M4279^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,4,0,0],[2,0,1,4,1],[1,0,2,2,3],[1,0,4,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M4292» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,3,0],[3,0,4,0,1],[4,1,2,0,3],[0,4,2,3,2],[0,1,4,4,4]]"

@[implicit_reducible]
def «OneVariable M4292^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,4,0,0],[2,0,1,4,1],[1,4,2,2,4],[3,0,0,3,4],[0,1,3,2,4]]"

@[implicit_reducible]
def «OneVariable M4297» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[3,0,1,2],[3,1,2,2],[0,2,1,3]]"

@[implicit_reducible]
def «OneVariable M4297^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,3,0],[2,0,1,2],[3,1,2,1],[0,2,2,3]]"

@[implicit_reducible]
def «OneVariable M4303» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,1],[4,0,0,1,3],[3,1,2,2,2],[0,1,4,3,3],[0,3,4,4,4]]"

@[implicit_reducible]
def «OneVariable M4303^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,0,0],[2,0,1,1,3],[3,0,2,4,4],[0,1,2,3,4],[1,3,2,3,4]]"

@[implicit_reducible]
def «OneVariable M4372» : Magma (Fin 4) where
  op := finOpTable "[[2,2,1,0],[3,1,0,0],[3,0,2,2],[0,3,0,3]]"

@[implicit_reducible]
def «OneVariable M4372^op» : Magma (Fin 4) where
  op := finOpTable "[[2,3,3,0],[2,1,0,3],[1,0,2,0],[0,0,2,3]]"

@[implicit_reducible]
def «OneVariable M4409» : Magma (Fin 4) where
  op := finOpTable "[[2,2,1,0],[3,1,0,3],[3,1,2,0],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M4409^op» : Magma (Fin 4) where
  op := finOpTable "[[2,3,3,0],[2,1,1,0],[1,0,2,0],[0,3,0,3]]"

@[implicit_reducible]
def «OneVariable M4410» : Magma (Fin 5) where
  op := finOpTable "[[2,2,1,4,0],[4,1,0,3,4],[3,2,2,0,2],[0,1,0,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M4410^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,0,0],[2,1,2,1,4],[1,0,2,0,4],[4,3,0,3,4],[0,4,2,3,4]]"

@[implicit_reducible]
def «OneVariable M4485» : Magma (Fin 6) where
  op := finOpTable "[[0,2,2,5,4,3],[2,4,0,1,4,0],[2,1,1,5,5,4],[5,1,5,3,1,5],[1,3,2,1,2,4],[5,1,4,5,4,5]]"

@[implicit_reducible]
def «OneVariable M4485^op» : Magma (Fin 6) where
  op := finOpTable "[[0,2,2,5,1,5],[2,4,1,1,3,1],[2,0,1,5,2,4],[5,1,5,3,1,5],[4,4,5,1,2,4],[3,0,4,5,4,5]]"

@[implicit_reducible]
def «OneVariable M4498» : Magma (Fin 5) where
  op := finOpTable "[[2,2,1,4,0],[4,1,4,4,3],[3,0,2,0,0],[0,4,0,3,3],[0,3,0,3,4]]"

@[implicit_reducible]
def «OneVariable M4498^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,0,0],[2,1,0,4,3],[1,4,2,0,0],[4,4,0,3,3],[0,3,0,3,4]]"

@[implicit_reducible]
def «OneVariable M4563» : Magma (Fin 5) where
  op := finOpTable "[[2,2,1,2,0],[4,1,0,1,4],[3,2,2,0,2],[0,2,0,3,1],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M4563^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,0,0],[2,1,2,2,4],[1,0,2,0,4],[2,1,0,3,4],[0,4,2,1,4]]"

@[implicit_reducible]
def «OneVariable M4582» : Magma (Fin 5) where
  op := finOpTable "[[4,2,0,4,1],[2,1,0,3,0],[0,0,2,3,4],[0,2,4,3,0],[3,2,4,0,4]]"

@[implicit_reducible]
def «OneVariable M4582^op» : Magma (Fin 5) where
  op := finOpTable "[[4,2,0,0,3],[2,1,0,2,2],[0,0,2,4,4],[4,3,3,3,0],[1,0,4,0,4]]"

@[implicit_reducible]
def «OneVariable M4600» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,0,1],[4,1,0,0,3],[3,0,2,0,0],[0,0,1,3,3],[0,0,1,0,4]]"

@[implicit_reducible]
def «OneVariable M4600^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,0,0],[2,1,0,0,0],[1,0,2,1,1],[0,0,0,3,0],[1,3,0,3,4]]"

@[implicit_reducible]
def «OneVariable M4656» : Magma (Fin 5) where
  op := finOpTable "[[2,2,1,4,0],[4,1,0,1,4],[3,0,2,4,2],[0,4,0,3,1],[0,2,0,4,4]]"

@[implicit_reducible]
def «OneVariable M4656^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,0,0],[2,1,0,4,2],[1,0,2,0,0],[4,1,4,3,4],[0,4,2,1,4]]"

@[implicit_reducible]
def «OneVariable M4682» : Magma (Fin 4) where
  op := finOpTable "[[3,3,0,1],[2,1,2,0],[0,3,2,2],[2,0,0,3]]"

@[implicit_reducible]
def «OneVariable M4682^op» : Magma (Fin 4) where
  op := finOpTable "[[3,2,0,2],[3,1,3,0],[0,2,2,0],[1,0,2,3]]"

@[implicit_reducible]
def «OneVariable M4756» : Magma (Fin 5) where
  op := finOpTable "[[2,4,1,2,0],[4,1,0,3,2],[3,0,2,3,4],[0,1,0,3,3],[0,2,4,3,4]]"

@[implicit_reducible]
def «OneVariable M4756^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,0,0],[4,1,0,1,2],[1,0,2,0,4],[2,3,3,3,3],[0,2,4,3,4]]"

@[implicit_reducible]
def «OneVariable M4771» : Magma (Fin 5) where
  op := finOpTable "[[2,2,1,2,0],[4,1,1,2,0],[3,0,2,0,2],[0,3,0,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M4771^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,0,0],[2,1,0,3,4],[1,1,2,0,4],[2,2,0,3,4],[0,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M4803» : Magma (Fin 5) where
  op := finOpTable "[[2,4,1,3,0],[4,1,0,2,4],[3,0,2,0,4],[0,0,0,3,0],[0,3,0,0,4]]"

@[implicit_reducible]
def «OneVariable M4803^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,0,0],[4,1,0,0,3],[1,0,2,0,0],[3,2,0,3,0],[0,4,4,0,4]]"

@[implicit_reducible]
def «OneVariable M4811» : Magma (Fin 5) where
  op := finOpTable "[[2,0,1,2,0],[4,1,1,3,2],[3,0,2,0,0],[0,3,0,3,3],[0,2,4,0,4]]"

@[implicit_reducible]
def «OneVariable M4811^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,0,0],[0,1,0,3,2],[1,1,2,0,4],[2,3,0,3,0],[0,2,0,3,4]]"

@[implicit_reducible]
def «OneVariable M4832» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,1,0],[3,1,0,0,1],[4,0,2,0,3],[0,0,0,3,4],[0,3,2,1,4]]"

@[implicit_reducible]
def «OneVariable M4832^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,4,0,0],[2,1,0,0,3],[3,0,2,0,2],[1,0,0,3,1],[0,1,3,4,4]]"

@[implicit_reducible]
def «OneVariable M4833» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[3,1,0,0],[3,3,2,0],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M4833^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,3,0],[2,1,3,0],[3,0,2,0],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M4834» : Magma (Fin 5) where
  op := finOpTable "[[2,4,1,2,0],[4,1,2,3,2],[3,0,2,0,4],[0,1,0,3,3],[0,2,4,3,4]]"

@[implicit_reducible]
def «OneVariable M4834^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,0,0],[4,1,0,1,2],[1,2,2,0,4],[2,3,0,3,3],[0,2,4,3,4]]"

@[implicit_reducible]
def «OneVariable M4853» : Magma (Fin 5) where
  op := finOpTable "[[2,2,1,2,0],[4,1,0,4,2],[3,0,2,0,4],[0,3,3,3,3],[0,2,4,4,4]]"

@[implicit_reducible]
def «OneVariable M4853^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,0,0],[2,1,0,3,2],[1,0,2,3,4],[2,4,0,3,4],[0,2,4,3,4]]"

@[implicit_reducible]
def «OneVariable M4872» : Magma (Fin 5) where
  op := finOpTable "[[2,2,1,4,0],[4,1,0,4,3],[3,0,2,0,4],[0,2,3,3,1],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M4872^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,0,0],[2,1,0,2,4],[1,0,2,3,4],[4,4,0,3,4],[0,3,4,1,4]]"

@[implicit_reducible]
def «OneVariable M4873» : Magma (Fin 5) where
  op := finOpTable "[[2,2,1,3,0],[4,1,0,1,2],[3,0,2,0,4],[0,4,0,3,3],[0,2,2,0,4]]"

@[implicit_reducible]
def «OneVariable M4873^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,0,0],[2,1,0,4,2],[1,0,2,0,2],[3,1,0,3,0],[0,2,4,3,4]]"

@[implicit_reducible]
def «OneVariable M4879» : Magma (Fin 5) where
  op := finOpTable "[[2,4,1,2,0],[4,1,0,3,0],[3,0,2,0,4],[0,3,3,3,3],[0,2,4,4,4]]"

@[implicit_reducible]
def «OneVariable M4879^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,0,0],[4,1,0,3,2],[1,0,2,3,4],[2,3,0,3,4],[0,0,4,3,4]]"

@[implicit_reducible]
def «OneVariable M4892» : Magma (Fin 4) where
  op := finOpTable "[[2,2,1,0],[3,1,0,1],[3,0,2,0],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M4892^op» : Magma (Fin 4) where
  op := finOpTable "[[2,3,3,0],[2,1,0,0],[1,0,2,0],[0,1,0,3]]"

@[implicit_reducible]
def «OneVariable M4895» : Magma (Fin 5) where
  op := finOpTable "[[4,4,4,0,1],[3,1,2,3,0],[0,2,2,2,0],[1,2,3,3,1],[2,0,0,4,4]]"

@[implicit_reducible]
def «OneVariable M4895^op» : Magma (Fin 5) where
  op := finOpTable "[[4,3,0,1,2],[4,1,2,2,0],[4,2,2,3,0],[0,3,2,3,4],[1,0,0,1,4]]"

@[implicit_reducible]
def «OneVariable M4899» : Magma (Fin 5) where
  op := finOpTable "[[3,3,3,2,0],[0,1,2,0,0],[4,0,2,0,4],[1,0,0,3,1],[0,1,2,4,4]]"

@[implicit_reducible]
def «OneVariable M4899^op» : Magma (Fin 5) where
  op := finOpTable "[[3,0,4,1,0],[3,1,0,0,1],[3,2,2,0,2],[2,0,0,3,4],[0,0,4,1,4]]"

@[implicit_reducible]
def «OneVariable M4904» : Magma (Fin 8) where
  op := finOpTable "[[6,6,0,3,7,4,1,4],[2,1,7,3,3,3,0,2],[0,0,2,1,3,1,0,2],[0,3,4,4,2,6,5,6],[5,3,3,1,0,0,6,4],[4,3,6,6,7,5,6,2],[2,0,0,7,4,6,3,3],[4,5,2,6,4,2,5,7]]"

@[implicit_reducible]
def «OneVariable M4904^op» : Magma (Fin 8) where
  op := finOpTable "[[6,2,0,0,5,4,2,4],[6,1,0,3,3,3,0,5],[0,7,2,4,3,6,0,2],[3,3,1,4,1,6,7,6],[7,3,3,2,0,7,4,4],[4,3,1,6,0,5,6,2],[1,0,0,5,6,6,3,5],[4,2,2,6,4,2,3,7]]"

@[implicit_reducible]
def «OneVariable M4911» : Magma (Fin 9) where
  op := finOpTable "[[0,8,2,3,1,5,5,3,0],[4,4,4,3,0,7,7,6,1],[5,1,2,6,1,5,6,3,8],[7,1,7,7,5,4,3,2,4],[1,2,1,8,3,3,4,7,3],[5,7,7,4,4,5,5,8,6],[8,7,4,3,4,6,6,7,0],[3,5,3,0,4,1,1,1,7],[0,1,1,4,6,5,8,7,8]]"

@[implicit_reducible]
def «OneVariable M4911^op» : Magma (Fin 9) where
  op := finOpTable "[[0,4,5,7,1,5,8,3,0],[8,4,1,1,2,7,7,5,1],[2,4,2,7,1,7,4,3,1],[3,3,6,7,8,4,3,0,4],[1,0,1,5,3,4,4,4,6],[5,7,5,4,3,5,6,1,5],[5,7,6,3,4,5,6,1,8],[3,6,3,2,7,8,7,1,7],[0,1,8,4,3,6,0,7,8]]"

@[implicit_reducible]
def «OneVariable M5085» : Magma (Fin 8) where
  op := finOpTable "[[6,7,0,1,4,6,0,0],[3,1,1,3,3,5,6,6],[7,7,2,4,4,5,7,4],[3,0,0,0,2,5,3,7],[4,3,3,4,3,7,6,5],[0,3,2,4,7,5,0,7],[5,7,2,3,6,3,7,6],[0,1,2,7,7,4,1,4]]"

@[implicit_reducible]
def «OneVariable M5085^op» : Magma (Fin 8) where
  op := finOpTable "[[6,3,7,3,4,0,5,0],[7,1,7,0,3,3,7,1],[0,1,2,0,3,2,2,2],[1,3,4,0,4,4,3,7],[4,3,4,2,3,7,6,7],[6,5,5,5,7,5,3,4],[0,6,7,3,6,0,7,1],[0,6,4,7,5,7,6,4]]"

@[implicit_reducible]
def «OneVariable M5125» : Magma (Fin 8) where
  op := finOpTable "[[1,1,1,3,0,5,7,6],[2,4,0,4,4,1,6,7],[0,2,2,3,4,5,6,2],[3,1,3,3,6,3,0,7],[0,3,5,1,5,5,5,4],[5,1,7,3,6,7,4,7],[1,6,6,1,4,5,6,7],[0,7,5,5,4,2,0,0]]"

@[implicit_reducible]
def «OneVariable M5125^op» : Magma (Fin 8) where
  op := finOpTable "[[1,2,0,3,0,5,1,0],[1,4,2,1,3,1,6,7],[1,0,2,3,5,7,6,5],[3,4,3,3,1,3,1,5],[0,4,4,6,5,6,4,4],[5,1,5,3,5,7,5,2],[7,6,6,0,5,4,6,0],[6,7,2,7,4,7,7,0]]"

@[implicit_reducible]
def «OneVariable M5158» : Magma (Fin 6) where
  op := finOpTable "[[1,1,0,5,1,3],[4,2,2,2,0,1],[2,3,5,1,5,5],[5,1,1,3,3,5],[0,0,2,4,4,2],[0,5,4,0,2,0]]"

@[implicit_reducible]
def «OneVariable M5158^op» : Magma (Fin 6) where
  op := finOpTable "[[1,4,2,5,0,0],[1,2,3,1,0,5],[0,2,5,1,2,4],[5,2,1,3,4,0],[1,0,5,3,4,2],[3,1,5,5,2,0]]"

@[implicit_reducible]
def «OneVariable M5167» : Magma (Fin 8) where
  op := finOpTable "[[0,1,6,3,6,3,6,1],[1,1,2,4,4,3,2,7],[0,6,6,3,2,7,2,5],[5,4,3,5,1,3,6,7],[6,3,2,4,3,4,0,7],[3,1,5,0,4,2,5,2],[4,2,1,6,6,5,4,7],[0,1,5,3,4,5,6,7]]"

@[implicit_reducible]
def «OneVariable M5167^op» : Magma (Fin 8) where
  op := finOpTable "[[0,1,0,5,6,3,4,0],[1,1,6,4,3,1,2,1],[6,2,6,3,2,5,1,5],[3,4,3,5,4,0,6,3],[6,4,2,1,3,4,6,4],[3,3,7,3,4,2,5,5],[6,2,2,6,0,5,4,6],[1,7,5,7,7,2,7,7]]"

@[implicit_reducible]
def «OneVariable M5176» : Magma (Fin 8) where
  op := finOpTable "[[1,1,2,0,5,4,6,7],[2,3,0,3,4,5,0,1],[0,0,2,3,4,7,6,7],[0,6,4,7,4,3,1,7],[5,4,2,3,4,5,6,3],[0,5,7,3,4,0,2,2],[6,1,6,1,0,7,6,7],[7,1,2,4,3,5,0,5]]"

@[implicit_reducible]
def «OneVariable M5176^op» : Magma (Fin 8) where
  op := finOpTable "[[1,2,0,0,5,0,6,7],[1,3,0,6,4,5,1,1],[2,0,2,4,2,7,6,2],[0,3,3,7,3,3,1,4],[5,4,4,4,4,4,0,3],[4,5,7,3,5,0,7,5],[6,0,6,1,6,2,6,0],[7,1,7,7,3,2,7,5]]"

@[implicit_reducible]
def «OneVariable M5208» : Magma (Fin 8) where
  op := finOpTable "[[2,0,0,2,7,5,6,4],[0,5,6,3,5,1,2,1],[3,2,1,0,4,2,1,7],[0,6,7,6,3,5,3,2],[4,1,4,3,0,6,5,0],[7,4,2,5,1,7,6,5],[6,3,2,1,6,4,4,7],[5,1,3,7,4,0,7,3]]"

@[implicit_reducible]
def «OneVariable M5208^op» : Magma (Fin 8) where
  op := finOpTable "[[2,0,3,0,4,7,6,5],[0,5,2,6,1,4,3,1],[0,6,1,7,4,2,2,3],[2,3,0,6,3,5,1,7],[7,5,4,3,0,1,6,4],[5,1,2,5,6,7,4,0],[6,2,1,3,5,6,4,7],[4,1,7,2,0,5,7,3]]"

@[implicit_reducible]
def «OneVariable M5237» : Magma (Fin 8) where
  op := finOpTable "[[5,7,2,2,4,1,4,0],[0,1,7,3,3,0,6,7],[0,7,3,0,2,5,6,1],[2,6,0,4,1,5,3,7],[0,3,2,1,6,4,0,4],[1,0,5,5,4,7,6,6],[4,6,6,3,0,5,7,5],[0,3,1,7,4,6,5,2]]"

@[implicit_reducible]
def «OneVariable M5237^op» : Magma (Fin 8) where
  op := finOpTable "[[5,0,0,2,0,1,4,0],[7,1,7,6,3,0,6,3],[2,7,3,0,2,5,6,1],[2,3,0,4,1,5,3,7],[4,3,2,1,6,4,0,4],[1,0,5,5,4,7,5,6],[4,6,6,3,0,6,7,5],[0,7,1,7,4,6,5,2]]"

@[implicit_reducible]
def «OneVariable M5261» : Magma (Fin 8) where
  op := finOpTable "[[5,1,0,3,7,0,0,4],[0,1,2,2,7,0,6,3],[0,4,3,2,2,7,2,5],[3,2,1,4,3,5,7,5],[4,1,2,6,0,4,3,7],[1,0,5,5,4,2,5,7],[0,6,5,3,3,1,6,5],[4,0,5,3,4,5,5,7]]"

@[implicit_reducible]
def «OneVariable M5261^op» : Magma (Fin 8) where
  op := finOpTable "[[5,0,0,3,4,1,0,4],[1,1,4,2,1,0,6,0],[0,2,3,1,2,5,5,5],[3,2,2,4,6,5,3,3],[7,7,2,3,0,4,3,4],[0,0,7,5,4,2,1,5],[0,6,2,7,3,5,6,5],[4,3,5,5,7,7,5,7]]"

@[implicit_reducible]
def «OneVariable M5296» : Magma (Fin 8) where
  op := finOpTable "[[0,1,3,7,0,6,1,6],[2,2,0,3,5,4,6,1],[1,0,7,7,4,1,2,3],[6,3,2,3,6,3,6,7],[0,5,4,6,1,1,3,7],[0,2,2,2,4,5,6,7],[5,6,2,4,3,7,4,5],[3,1,3,2,7,6,5,6]]"

@[implicit_reducible]
def «OneVariable M5296^op» : Magma (Fin 8) where
  op := finOpTable "[[0,2,1,6,0,0,5,3],[1,2,0,3,5,2,6,1],[3,0,7,2,4,2,2,3],[7,3,7,3,6,2,4,2],[0,5,4,6,1,4,3,7],[6,4,1,3,1,5,7,6],[1,6,2,6,3,6,4,5],[6,1,3,7,7,7,5,6]]"

@[implicit_reducible]
def «OneVariable M5335» : Magma (Fin 6) where
  op := finOpTable "[[0,1,2,1,3,2],[3,3,1,0,5,4],[5,2,5,4,3,0],[1,0,4,2,2,3],[1,5,3,3,4,5],[2,4,0,5,1,1]]"

@[implicit_reducible]
def «OneVariable M5335^op» : Magma (Fin 6) where
  op := finOpTable "[[0,3,5,1,1,2],[1,3,2,0,5,4],[2,1,5,4,3,0],[1,0,4,2,3,5],[3,5,3,2,4,1],[2,4,0,3,5,1]]"

@[implicit_reducible]
def «OneVariable M5355» : Magma (Fin 8) where
  op := finOpTable "[[7,6,7,3,0,6,1,2],[6,1,2,3,7,5,6,7],[0,7,2,3,5,6,3,0],[3,1,6,6,5,4,2,7],[0,7,7,5,3,3,4,1],[5,1,2,4,4,5,6,7],[1,0,3,2,4,0,0,6],[2,4,0,7,1,0,6,4]]"

@[implicit_reducible]
def «OneVariable M5355^op» : Magma (Fin 8) where
  op := finOpTable "[[7,6,0,3,0,5,1,2],[6,1,7,1,7,1,0,4],[7,2,2,6,7,2,3,0],[3,3,3,6,5,4,2,7],[0,7,5,5,3,4,4,1],[6,5,6,4,3,5,0,0],[1,6,3,2,4,6,0,6],[2,7,0,7,1,7,6,4]]"

@[implicit_reducible]
def «OneVariable M5356» : Magma (Fin 8) where
  op := finOpTable "[[0,3,2,2,1,5,5,0],[1,1,6,3,3,5,6,0],[3,6,3,0,2,5,1,3],[2,4,7,4,1,3,6,7],[5,3,2,1,5,7,4,5],[6,3,5,3,7,6,0,4],[5,2,1,6,4,0,2,2],[7,0,2,2,4,4,6,7]]"

@[implicit_reducible]
def «OneVariable M5356^op» : Magma (Fin 8) where
  op := finOpTable "[[0,1,3,2,5,6,5,7],[3,1,6,4,3,3,2,0],[2,6,3,7,2,5,1,2],[2,3,0,4,1,3,6,2],[1,3,2,1,5,7,4,4],[5,5,5,3,7,6,0,4],[5,6,1,6,4,0,2,6],[0,0,3,7,5,4,2,7]]"

@[implicit_reducible]
def «OneVariable M5519» : Magma (Fin 8) where
  op := finOpTable "[[0,4,5,4,4,5,0,7],[1,1,2,3,2,6,6,3],[5,4,4,2,7,0,6,4],[4,3,2,6,0,3,7,6],[3,2,1,0,3,5,4,2],[2,6,0,3,5,2,1,6],[1,5,6,7,4,1,5,3],[7,3,2,3,2,6,3,7]]"

@[implicit_reducible]
def «OneVariable M5519^op» : Magma (Fin 8) where
  op := finOpTable "[[0,1,5,4,3,2,1,7],[4,1,4,3,2,6,5,3],[5,2,4,2,1,0,6,2],[4,3,2,6,0,3,7,3],[4,2,7,0,3,5,4,2],[5,6,0,3,5,2,1,6],[0,6,6,7,4,1,5,3],[7,3,4,6,2,6,3,7]]"

@[implicit_reducible]
def «OneVariable M5583» : Magma (Fin 8) where
  op := finOpTable "[[4,4,7,4,3,2,0,2],[0,1,6,4,0,5,6,0],[5,6,0,6,2,0,1,0],[4,4,6,3,0,0,2,5],[1,0,4,0,6,6,5,6],[2,5,0,6,6,5,4,1],[6,2,3,2,7,4,2,4],[2,5,2,5,4,1,4,7]]"

@[implicit_reducible]
def «OneVariable M5583^op» : Magma (Fin 8) where
  op := finOpTable "[[4,0,5,4,1,2,6,2],[4,1,6,4,0,5,2,5],[7,6,0,6,4,0,3,2],[4,4,6,3,0,6,2,5],[3,0,2,0,6,6,7,4],[2,5,0,0,6,5,4,1],[0,6,1,2,5,4,2,4],[2,0,0,5,6,1,4,7]]"

@[implicit_reducible]
def «OneVariable M5698» : Magma (Fin 6) where
  op := finOpTable "[[1,1,0,5,0,3],[4,2,2,1,0,1],[2,5,3,3,2,1],[0,3,4,0,2,3],[0,0,2,2,4,2],[3,1,1,3,2,5]]"

@[implicit_reducible]
def «OneVariable M5698^op» : Magma (Fin 6) where
  op := finOpTable "[[1,4,2,0,0,3],[1,2,5,3,0,1],[0,2,3,4,2,1],[5,1,3,0,2,3],[0,0,2,2,4,2],[3,1,1,3,2,5]]"

@[implicit_reducible]
def «OneVariable M5960» : Magma (Fin 8) where
  op := finOpTable "[[4,0,3,6,5,4,3,0],[0,1,0,7,0,1,0,5],[3,1,2,6,4,7,7,4],[2,7,0,0,3,7,3,5],[1,0,4,4,7,0,7,6],[1,6,5,7,0,5,5,7],[3,1,6,3,2,6,6,4],[7,3,4,1,2,7,4,3]]"

@[implicit_reducible]
def «OneVariable M5960^op» : Magma (Fin 8) where
  op := finOpTable "[[4,0,3,2,1,1,3,7],[0,1,1,7,0,6,1,3],[3,0,2,0,4,5,6,4],[6,7,6,0,4,7,3,1],[5,0,4,3,7,0,2,2],[4,1,7,7,0,5,6,7],[3,0,7,3,7,5,6,4],[0,5,4,5,6,7,4,3]]"

@[implicit_reducible]
def «OneVariable M5962» : Magma (Fin 9) where
  op := finOpTable "[[0,7,7,8,4,5,5,1,4],[1,1,4,1,7,3,5,1,4],[7,6,2,6,6,8,7,2,8],[8,5,7,3,6,5,6,2,8],[8,8,6,6,8,4,3,4,1],[6,6,8,5,5,6,1,8,2],[5,5,4,4,2,0,4,6,6],[2,7,2,6,4,8,6,7,3],[4,4,5,8,0,7,8,5,5]]"

@[implicit_reducible]
def «OneVariable M5962^op» : Magma (Fin 9) where
  op := finOpTable "[[0,1,7,8,8,6,5,2,4],[7,1,6,5,8,6,5,7,4],[7,4,2,7,6,8,4,2,5],[8,1,6,3,6,5,4,6,8],[4,7,6,6,8,5,2,4,0],[5,3,8,5,4,6,0,8,7],[5,5,7,6,3,1,4,6,8],[1,1,2,2,4,8,6,7,5],[4,4,8,8,1,2,6,3,5]]"

@[implicit_reducible]
def «OneVariable M5969» : Magma (Fin 8) where
  op := finOpTable "[[4,3,6,0,1,6,5,0],[3,1,0,5,0,7,7,3],[6,0,2,7,4,7,5,4],[0,5,3,3,0,7,7,7],[3,0,4,0,7,2,4,5],[6,1,6,1,2,5,6,4],[2,7,5,7,6,6,0,3],[7,3,4,7,2,4,1,6]]"

@[implicit_reducible]
def «OneVariable M5969^op» : Magma (Fin 8) where
  op := finOpTable "[[4,3,6,0,3,6,2,7],[3,1,0,5,0,1,7,3],[6,0,2,3,4,6,5,4],[0,5,7,3,0,1,7,7],[1,0,4,0,7,2,6,2],[6,7,7,7,2,5,6,4],[5,7,5,7,4,6,0,1],[0,3,4,7,5,4,3,6]]"

@[implicit_reducible]
def «OneVariable M6011» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,4,0],[3,0,4,4,1],[1,1,2,3,3],[0,0,0,3,4],[0,1,4,3,4]]"

@[implicit_reducible]
def «OneVariable M6011^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,1,0,0],[2,0,1,0,1],[4,4,2,0,4],[4,4,3,3,3],[0,1,3,4,4]]"

@[implicit_reducible]
def «OneVariable M6012» : Magma (Fin 4) where
  op := finOpTable "[[1,0,0,2],[3,1,1,0],[0,2,2,0],[0,0,3,3]]"

@[implicit_reducible]
def «OneVariable M6012^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,0],[0,1,2,0],[0,1,2,3],[2,0,0,3]]"

@[implicit_reducible]
def «OneVariable M6013» : Magma (Fin 4) where
  op := finOpTable "[[3,2,0,0],[0,1,1,0],[0,0,2,2],[1,1,0,3]]"

@[implicit_reducible]
def «OneVariable M6013^op» : Magma (Fin 4) where
  op := finOpTable "[[3,0,0,1],[2,1,0,1],[0,1,2,0],[0,0,2,3]]"

@[implicit_reducible]
def «OneVariable M6016» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,0,3],[4,0,3,1,0],[1,1,2,3,4],[0,1,2,3,4],[0,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M6016^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,1,0,0],[2,0,1,1,0],[1,3,2,2,2],[0,1,3,3,3],[3,0,4,4,4]]"

@[implicit_reducible]
def «OneVariable M6111» : Magma (Fin 4) where
  op := finOpTable "[[1,0,3,0],[2,1,0,1],[0,2,2,3],[0,1,2,3]]"

@[implicit_reducible]
def «OneVariable M6111^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,0],[0,1,2,1],[3,0,2,2],[0,1,3,3]]"

@[implicit_reducible]
def «OneVariable M6144» : Magma (Fin 6) where
  op := finOpTable "[[4,5,0,2,4,1],[0,0,4,1,2,3],[0,4,2,3,4,2],[0,1,5,3,0,3],[3,1,5,0,1,4],[1,1,2,2,4,5]]"

@[implicit_reducible]
def «OneVariable M6144^op» : Magma (Fin 6) where
  op := finOpTable "[[4,0,0,0,3,1],[5,0,4,1,1,1],[0,4,2,5,5,2],[2,1,3,3,0,2],[4,2,4,0,1,4],[1,3,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M6146» : Magma (Fin 7) where
  op := finOpTable "[[0,0,0,3,5,5,3],[0,1,6,3,4,6,6],[3,6,2,4,4,5,6],[1,3,4,6,2,5,3],[5,4,1,4,3,0,6],[2,6,5,3,5,4,1],[3,2,6,0,4,6,5]]"

@[implicit_reducible]
def «OneVariable M6146^op» : Magma (Fin 7) where
  op := finOpTable "[[0,0,3,1,5,2,3],[0,1,6,3,4,6,2],[0,6,2,4,1,5,6],[3,3,4,6,4,3,0],[5,4,4,2,3,5,4],[5,6,5,5,0,4,6],[3,6,6,3,6,1,5]]"

@[implicit_reducible]
def «OneVariable M6152» : Magma (Fin 5) where
  op := finOpTable "[[3,2,0,4,2],[0,1,2,0,4],[0,2,2,3,1],[1,0,4,3,0],[3,2,4,3,4]]"

@[implicit_reducible]
def «OneVariable M6152^op» : Magma (Fin 5) where
  op := finOpTable "[[3,0,0,1,3],[2,1,2,0,2],[0,2,2,4,4],[4,0,3,3,3],[2,4,1,0,4]]"

@[implicit_reducible]
def «OneVariable M6186» : Magma (Fin 7) where
  op := finOpTable "[[0,1,4,3,4,4,3],[5,1,2,3,6,4,6],[4,2,3,5,0,1,6],[1,3,5,6,4,2,0],[5,6,0,3,2,4,1],[6,1,2,2,4,5,6],[3,5,2,0,1,6,4]]"

@[implicit_reducible]
def «OneVariable M6186^op» : Magma (Fin 7) where
  op := finOpTable "[[0,5,4,1,5,6,3],[1,1,2,3,6,1,5],[4,2,3,5,0,2,2],[3,3,5,6,3,2,0],[4,6,0,4,2,4,1],[4,4,1,2,4,5,6],[3,6,6,0,1,6,4]]"

@[implicit_reducible]
def «OneVariable M6258» : Magma (Fin 5) where
  op := finOpTable "[[4,2,0,4,3],[0,1,4,4,0],[0,1,2,0,4],[4,1,4,3,0],[1,4,1,0,4]]"

@[implicit_reducible]
def «OneVariable M6258^op» : Magma (Fin 5) where
  op := finOpTable "[[4,0,0,4,1],[2,1,1,1,4],[0,4,2,4,1],[4,4,0,3,0],[3,0,4,0,4]]"

@[implicit_reducible]
def «OneVariable M6260» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,0,1],[2,1,0,3,0],[0,0,2,3,4],[4,1,2,3,3],[1,0,0,3,4]]"

@[implicit_reducible]
def «OneVariable M6260^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,0,4,1],[4,1,0,1,0],[3,0,2,2,0],[0,3,3,3,3],[1,0,4,3,4]]"

@[implicit_reducible]
def «OneVariable M6340» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,2,0],[0,1,0,3,0],[1,0,2,0,4],[1,1,0,3,2],[0,0,0,3,4]]"

@[implicit_reducible]
def «OneVariable M6340^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,1,1,0],[4,1,0,1,0],[3,0,2,0,0],[2,3,0,3,3],[0,0,4,2,4]]"

@[implicit_reducible]
def «OneVariable M6357» : Magma (Fin 5) where
  op := finOpTable "[[2,3,4,0,3],[0,1,0,3,4],[1,1,2,2,0],[0,2,4,3,4],[2,1,0,3,4]]"

@[implicit_reducible]
def «OneVariable M6357^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,1,0,2],[3,1,1,2,1],[4,0,2,4,0],[0,3,2,3,3],[3,4,0,4,4]]"

@[implicit_reducible]
def «OneVariable M6406» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,2,0],[0,1,0,0,1],[1,0,2,0,4],[2,1,3,3,0],[0,1,0,3,4]]"

@[implicit_reducible]
def «OneVariable M6406^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,1,2,0],[4,1,0,1,1],[3,0,2,3,0],[2,0,0,3,3],[0,1,4,0,4]]"

@[implicit_reducible]
def «OneVariable M6424» : Magma (Fin 5) where
  op := finOpTable "[[2,3,4,0,3],[0,1,0,4,4],[1,0,2,4,0],[0,2,4,3,0],[3,1,4,2,4]]"

@[implicit_reducible]
def «OneVariable M6424^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,1,0,3],[3,1,0,2,1],[4,0,2,4,4],[0,4,4,3,2],[3,4,0,0,4]]"

@[implicit_reducible]
def «OneVariable M6442» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,0,3],[4,1,0,4,0],[0,0,2,2,0],[0,3,3,3,3],[0,4,4,3,4]]"

@[implicit_reducible]
def «OneVariable M6442^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,0,0,0],[2,1,0,3,4],[1,0,2,3,4],[0,4,2,3,3],[3,0,0,3,4]]"

@[implicit_reducible]
def «OneVariable M6443» : Magma (Fin 5) where
  op := finOpTable "[[3,2,0,4,3],[0,1,1,1,4],[0,2,2,4,3],[1,0,3,3,0],[3,1,4,0,4]]"

@[implicit_reducible]
def «OneVariable M6443^op» : Magma (Fin 5) where
  op := finOpTable "[[3,0,0,1,3],[2,1,2,0,1],[0,1,2,3,4],[4,1,4,3,0],[3,4,3,0,4]]"

@[implicit_reducible]
def «OneVariable M6477» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,0,3],[4,1,0,0,0],[0,0,2,0,3],[0,3,3,3,0],[0,0,4,4,4]]"

@[implicit_reducible]
def «OneVariable M6477^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,0,0,0],[2,1,0,3,0],[1,0,2,3,4],[0,0,0,3,4],[3,0,3,0,4]]"

@[implicit_reducible]
def «OneVariable M6478» : Magma (Fin 5) where
  op := finOpTable "[[4,3,4,0,2],[0,1,1,0,0],[4,2,2,3,0],[0,2,3,3,4],[1,0,0,4,4]]"

@[implicit_reducible]
def «OneVariable M6478^op» : Magma (Fin 5) where
  op := finOpTable "[[4,0,4,0,1],[3,1,2,2,0],[4,1,2,3,0],[0,0,3,3,4],[2,0,0,4,4]]"

@[implicit_reducible]
def «OneVariable M6482» : Magma (Fin 9) where
  op := finOpTable "[[7,1,6,5,3,3,0,8,7],[0,3,3,2,7,7,8,4,1],[0,3,2,1,0,5,1,0,2],[4,6,1,0,0,8,1,7,3],[3,7,0,0,4,5,6,7,5],[3,7,1,3,4,5,6,1,4],[0,1,1,1,2,6,6,7,1],[2,5,0,3,6,1,7,1,0],[7,1,3,3,5,8,1,0,8]]"

@[implicit_reducible]
def «OneVariable M6482^op» : Magma (Fin 9) where
  op := finOpTable "[[7,0,0,4,3,3,0,2,7],[1,3,3,6,7,7,1,5,1],[6,3,2,1,0,1,1,0,3],[5,2,1,0,0,3,1,3,3],[3,7,0,0,4,4,2,6,5],[3,7,5,8,5,5,6,1,8],[0,8,1,1,6,6,6,7,1],[8,4,0,7,7,1,7,1,0],[7,1,2,3,5,4,1,0,8]]"

@[implicit_reducible]
def «OneVariable M6490» : Magma (Fin 5) where
  op := finOpTable "[[2,3,4,0,3],[0,1,0,3,4],[1,0,2,3,0],[0,4,2,3,4],[2,1,0,3,4]]"

@[implicit_reducible]
def «OneVariable M6490^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,1,0,2],[3,1,0,4,1],[4,0,2,2,0],[0,3,3,3,3],[3,4,0,4,4]]"

@[implicit_reducible]
def «OneVariable M6491» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,1,0],[0,1,0,3,4],[1,0,2,0,4],[2,1,0,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M6491^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,1,2,0],[4,1,0,1,1],[3,0,2,0,2],[1,3,0,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M6493» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,4,0],[0,1,0,3,4],[1,0,2,0,4],[1,1,0,3,4],[0,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M6493^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,1,1,0],[4,1,0,1,0],[3,0,2,0,2],[4,3,0,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M6600» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,4,0],[0,1,0,3,4],[1,0,2,3,4],[4,1,0,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M6600^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,1,4,0],[4,1,0,1,1],[3,0,2,0,2],[4,3,3,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M6655» : Magma (Fin 6) where
  op := finOpTable "[[1,4,3,0,1,0],[2,1,0,4,0,1],[0,0,2,5,3,1],[3,0,4,3,0,0],[5,0,3,0,4,5],[0,1,3,0,4,5]]"

@[implicit_reducible]
def «OneVariable M6655^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,0,3,5,0],[4,1,0,0,0,1],[3,0,2,4,3,3],[0,4,5,3,0,0],[1,0,3,0,4,4],[0,1,1,0,5,5]]"

@[implicit_reducible]
def «OneVariable M6735» : Magma (Fin 9) where
  op := finOpTable "[[0,1,2,8,2,8,6,1,8],[6,7,2,4,8,7,1,5,4],[3,1,4,2,5,4,7,8,7],[8,4,2,3,6,0,3,7,8],[2,3,0,1,1,2,4,7,6],[5,6,3,6,2,5,6,1,0],[8,1,7,6,4,5,6,3,3],[1,0,6,7,4,1,2,2,3],[0,4,7,3,4,8,0,7,8]]"

@[implicit_reducible]
def «OneVariable M6735^op» : Magma (Fin 9) where
  op := finOpTable "[[0,6,3,8,2,5,8,1,0],[1,7,1,4,3,6,1,0,4],[2,2,4,2,0,3,7,6,7],[8,4,2,3,1,6,6,7,3],[2,8,5,6,1,2,4,4,4],[8,7,4,0,2,5,5,1,8],[6,1,7,3,4,6,6,2,0],[1,5,8,7,7,1,3,2,7],[8,4,7,8,6,0,3,3,8]]"

@[implicit_reducible]
def «OneVariable M6737» : Magma (Fin 5) where
  op := finOpTable "[[1,2,0,4,0],[3,1,0,0,4],[2,0,2,3,4],[0,0,2,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M6737^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,2,0,0],[2,1,0,0,1],[0,0,2,2,2],[4,0,3,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M6738» : Magma (Fin 6) where
  op := finOpTable "[[1,2,1,0,0,4],[5,1,0,1,4,0],[3,0,2,2,4,5],[3,2,2,3,4,5],[0,2,2,5,4,5],[0,0,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M6738^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,3,0,0],[2,1,0,2,2,0],[1,0,2,2,2,2],[0,1,2,3,5,3],[0,4,4,4,4,4],[4,0,5,5,5,5]]"

@[implicit_reducible]
def «OneVariable M6739» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,2,0],[0,1,0,3,4],[1,0,2,0,4],[4,1,0,3,4],[0,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M6739^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,1,4,0],[4,1,0,1,0],[3,0,2,0,2],[2,3,0,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M6746» : Magma (Fin 6) where
  op := finOpTable "[[1,2,5,0,5,0],[4,1,0,3,0,2],[3,0,2,4,0,5],[4,2,2,3,0,5],[0,0,2,3,4,5],[0,3,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M6746^op» : Magma (Fin 6) where
  op := finOpTable "[[1,4,3,4,0,0],[2,1,0,2,0,3],[5,0,2,2,2,2],[0,3,4,3,3,3],[5,0,0,0,4,4],[0,2,5,5,5,5]]"

@[implicit_reducible]
def «OneVariable M6747» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,4,0],[3,1,0,0,4],[4,0,2,3,4],[0,0,2,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M6747^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,4,0,0],[2,1,0,0,1],[3,0,2,2,2],[4,0,3,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M6771» : Magma (Fin 8) where
  op := finOpTable "[[1,0,3,0,4,5,7,4],[2,3,7,1,1,4,6,7],[0,0,5,6,4,2,2,1],[0,5,2,4,3,2,7,3],[2,1,4,6,7,5,5,4],[5,1,3,1,0,6,5,7],[6,6,2,3,3,4,0,1],[6,5,7,3,0,7,6,2]]"

@[implicit_reducible]
def «OneVariable M6771^op» : Magma (Fin 8) where
  op := finOpTable "[[1,2,0,0,2,5,6,6],[0,3,0,5,1,1,6,5],[3,7,5,2,4,3,2,7],[0,1,6,4,6,1,3,3],[4,1,4,3,7,0,3,0],[5,4,2,2,5,6,4,7],[7,6,2,7,5,5,0,6],[4,7,1,3,4,7,1,2]]"

@[implicit_reducible]
def «OneVariable M6822» : Magma (Fin 8) where
  op := finOpTable "[[0,1,1,4,4,5,0,5],[5,2,0,6,4,1,1,5],[0,0,5,3,4,6,7,2],[3,6,3,1,0,3,5,7],[2,4,4,0,3,5,6,6],[4,1,6,3,5,7,4,0],[2,3,2,3,7,2,6,7],[7,0,2,7,6,0,3,4]]"

@[implicit_reducible]
def «OneVariable M6822^op» : Magma (Fin 8) where
  op := finOpTable "[[0,5,0,3,2,4,2,7],[1,2,0,6,4,1,3,0],[1,0,5,3,4,6,2,2],[4,6,3,1,0,3,3,7],[4,4,4,0,3,5,7,6],[5,1,6,3,5,7,2,0],[0,1,7,5,6,4,6,3],[5,5,2,7,6,0,7,4]]"

@[implicit_reducible]
def «OneVariable M6845» : Magma (Fin 8) where
  op := finOpTable "[[1,1,3,0,0,6,5,7],[2,4,0,7,4,5,1,1],[0,0,2,3,4,3,6,4],[1,1,3,3,1,7,6,7],[0,3,5,1,7,4,2,7],[0,5,5,7,4,0,2,3],[5,4,6,6,0,5,6,6],[7,1,4,0,2,5,6,5]]"

@[implicit_reducible]
def «OneVariable M6845^op» : Magma (Fin 8) where
  op := finOpTable "[[1,2,0,1,0,0,5,7],[1,4,0,1,3,5,4,1],[3,0,2,3,5,5,6,4],[0,7,3,3,1,7,6,0],[0,4,4,1,7,4,0,2],[6,5,3,7,4,0,5,5],[5,1,6,6,2,2,6,6],[7,1,4,7,7,3,6,5]]"

@[implicit_reducible]
def «OneVariable M6848» : Magma (Fin 7) where
  op := finOpTable "[[1,1,0,5,6,3,0],[4,2,2,6,0,1,1],[2,3,5,1,6,5,2],[5,1,1,3,0,5,6],[0,0,2,4,4,2,4],[0,5,4,6,2,0,5],[0,1,2,0,0,5,6]]"

@[implicit_reducible]
def «OneVariable M6848^op» : Magma (Fin 7) where
  op := finOpTable "[[1,4,2,5,0,0,0],[1,2,3,1,0,5,1],[0,2,5,1,2,4,2],[5,6,1,3,4,6,0],[6,0,6,0,4,2,0],[3,1,5,5,2,0,5],[0,1,2,6,4,5,6]]"

@[implicit_reducible]
def «OneVariable M6850» : Magma (Fin 8) where
  op := finOpTable "[[5,6,3,0,4,0,1,3],[6,1,7,3,3,5,6,0],[0,3,2,3,2,0,2,2],[0,6,5,4,3,7,3,5],[4,3,5,1,6,5,4,0],[2,0,0,5,5,3,6,4],[6,5,2,3,7,6,0,4],[1,7,0,5,4,5,4,7]]"

@[implicit_reducible]
def «OneVariable M6850^op» : Magma (Fin 8) where
  op := finOpTable "[[5,6,0,0,4,2,6,1],[6,1,3,6,3,0,5,7],[3,7,2,5,5,0,2,0],[0,3,3,4,1,5,3,5],[4,3,2,3,6,5,7,4],[0,5,0,7,5,3,6,5],[1,6,2,3,4,6,0,4],[3,0,2,5,0,4,4,7]]"

@[implicit_reducible]
def «OneVariable M6856» : Magma (Fin 7) where
  op := finOpTable "[[1,4,0,6,5,0,3],[4,2,3,5,0,1,1],[2,3,6,1,5,2,4],[6,1,1,3,6,5,6],[0,0,2,0,4,2,2],[0,1,2,5,2,5,6],[3,6,4,5,2,6,0]]"

@[implicit_reducible]
def «OneVariable M6856^op» : Magma (Fin 7) where
  op := finOpTable "[[1,4,2,6,0,0,3],[4,2,3,1,0,1,6],[0,3,6,1,2,2,4],[6,5,1,3,0,5,5],[5,0,5,6,4,2,2],[0,1,2,5,2,5,6],[3,1,4,6,2,6,0]]"

@[implicit_reducible]
def «OneVariable M6869» : Magma (Fin 8) where
  op := finOpTable "[[1,0,5,7,4,0,6,3],[2,5,0,4,1,1,6,7],[0,1,2,6,5,5,6,3],[6,1,0,3,4,0,6,7],[4,1,5,0,6,2,4,4],[0,3,6,1,5,4,5,7],[6,6,0,4,3,5,7,6],[7,7,6,5,4,7,2,0]]"

@[implicit_reducible]
def «OneVariable M6869^op» : Magma (Fin 8) where
  op := finOpTable "[[1,2,0,6,4,0,6,7],[0,5,1,1,1,3,6,7],[5,0,2,0,5,6,0,6],[7,4,6,3,0,1,4,5],[4,1,5,4,6,5,3,4],[0,1,5,0,2,4,5,7],[6,6,6,6,4,5,7,2],[3,7,3,7,4,7,6,0]]"

@[implicit_reducible]
def «OneVariable M6876» : Magma (Fin 8) where
  op := finOpTable "[[1,2,6,5,6,3,0,7],[4,6,3,7,0,5,3,1],[0,0,2,3,4,7,6,6],[5,1,4,3,7,5,1,3],[0,0,2,3,4,7,1,7],[3,5,7,1,7,0,6,4],[0,3,5,1,1,6,7,2],[7,1,6,3,0,4,2,5]]"

@[implicit_reducible]
def «OneVariable M6876^op» : Magma (Fin 8) where
  op := finOpTable "[[1,4,0,5,0,3,0,7],[2,6,0,1,0,5,3,1],[6,3,2,4,2,7,5,6],[5,7,3,3,3,1,1,3],[6,0,4,7,4,7,1,0],[3,5,7,5,7,0,6,4],[0,3,6,1,1,6,7,2],[7,1,6,3,7,4,2,5]]"

@[implicit_reducible]
def «OneVariable M6981» : Magma (Fin 8) where
  op := finOpTable "[[1,2,3,0,0,7,6,5],[2,4,0,6,3,5,1,7],[0,0,2,0,4,5,4,0],[3,1,5,3,1,5,6,6],[0,3,7,1,6,2,2,4],[7,4,5,7,2,5,5,7],[6,1,4,0,2,5,7,3],[5,7,0,6,4,1,3,0]]"

@[implicit_reducible]
def «OneVariable M6981^op» : Magma (Fin 8) where
  op := finOpTable "[[1,2,0,3,0,7,6,5],[2,4,0,1,3,4,1,7],[3,0,2,5,7,5,4,0],[0,6,0,3,1,7,0,6],[0,3,4,1,6,2,2,4],[7,5,5,5,2,5,5,1],[6,1,4,6,2,5,7,3],[5,7,0,6,4,7,3,0]]"

@[implicit_reducible]
def «OneVariable M7010» : Magma (Fin 8) where
  op := finOpTable "[[3,4,6,2,1,1,0,7],[0,1,0,3,4,5,6,7],[0,4,2,3,2,2,6,7],[2,0,0,6,4,7,5,3],[1,3,7,4,0,0,6,2],[7,5,0,3,1,5,0,5],[0,4,3,5,6,3,7,1],[7,6,0,3,2,5,1,4]]"

@[implicit_reducible]
def «OneVariable M7010^op» : Magma (Fin 8) where
  op := finOpTable "[[3,0,0,2,1,7,0,7],[4,1,4,0,3,5,4,6],[6,0,2,0,7,0,3,0],[2,3,3,6,4,3,5,3],[1,4,2,4,0,1,6,2],[1,5,2,7,0,5,3,5],[0,6,6,5,6,0,7,1],[7,7,7,3,2,5,1,4]]"

@[implicit_reducible]
def «OneVariable M7031» : Magma (Fin 8) where
  op := finOpTable "[[2,1,3,6,5,4,0,6],[1,4,2,5,3,1,7,6],[7,2,6,0,4,1,5,0],[0,1,1,3,1,0,6,0],[5,3,4,1,0,7,6,4],[4,1,2,0,4,5,2,7],[0,7,5,6,6,2,1,3],[0,6,0,0,4,7,6,7]]"

@[implicit_reducible]
def «OneVariable M7031^op» : Magma (Fin 8) where
  op := finOpTable "[[2,1,7,0,5,4,0,0],[1,4,2,1,3,1,7,6],[3,2,6,1,4,2,5,0],[6,5,0,3,1,0,6,0],[5,3,4,1,0,4,6,4],[4,1,1,0,7,5,2,7],[0,7,5,6,6,2,1,6],[6,6,0,0,4,7,3,7]]"

@[implicit_reducible]
def «OneVariable M7049» : Magma (Fin 8) where
  op := finOpTable "[[1,5,3,0,7,3,6,4],[2,3,0,4,6,0,1,7],[0,2,2,6,2,1,6,6],[0,4,5,6,1,7,5,3],[7,1,2,1,4,1,6,7],[0,0,2,3,1,5,3,5],[6,1,4,5,6,3,7,2],[4,7,6,3,1,5,2,0]]"

@[implicit_reducible]
def «OneVariable M7049^op» : Magma (Fin 8) where
  op := finOpTable "[[1,2,0,0,7,0,6,4],[5,3,2,4,1,0,1,7],[3,0,2,5,2,2,4,6],[0,4,6,6,1,3,5,3],[7,6,2,1,4,1,6,1],[3,0,1,7,1,5,3,5],[6,1,6,5,6,3,7,2],[4,7,6,3,7,5,2,0]]"

@[implicit_reducible]
def «OneVariable M7061» : Magma (Fin 9) where
  op := finOpTable "[[0,8,0,7,5,4,6,3,8],[2,1,3,3,4,7,1,5,6],[2,3,2,7,4,4,0,7,8],[7,3,7,4,8,3,1,2,4],[5,4,1,6,5,0,3,4,3],[4,7,4,5,2,7,5,1,6],[8,6,1,3,3,5,6,7,3],[3,5,6,0,7,8,7,3,5],[7,2,4,4,3,5,1,5,8]]"

@[implicit_reducible]
def «OneVariable M7061^op» : Magma (Fin 9) where
  op := finOpTable "[[0,2,2,7,5,4,8,3,7],[8,1,3,3,4,7,6,5,2],[0,3,2,7,1,4,1,6,4],[7,3,7,4,6,5,3,0,4],[5,4,4,8,5,2,3,7,3],[4,7,4,3,0,7,5,8,5],[6,1,0,1,3,5,6,7,1],[3,5,7,2,4,1,7,3,5],[8,6,8,4,3,6,3,5,8]]"

@[implicit_reducible]
def «OneVariable M7246» : Magma (Fin 9) where
  op := finOpTable "[[5,5,3,0,8,1,8,0,4],[3,1,3,3,1,0,5,7,7],[0,3,2,2,3,0,2,3,7],[0,1,3,3,0,5,4,7,8],[8,4,3,3,4,3,3,5,8],[2,0,0,5,7,7,3,4,5],[8,3,6,4,3,5,6,5,3],[7,3,8,7,5,6,5,8,2],[6,7,7,8,3,8,0,1,0]]"

@[implicit_reducible]
def «OneVariable M7246^op» : Magma (Fin 9) where
  op := finOpTable "[[5,3,0,0,8,2,8,7,6],[5,1,3,1,4,0,3,3,7],[3,3,2,3,3,0,6,8,7],[0,3,2,3,3,5,4,7,8],[8,1,3,0,4,7,3,5,3],[1,0,0,5,3,7,5,6,8],[8,5,2,4,3,3,6,5,0],[0,7,3,7,5,4,5,8,1],[4,7,7,8,8,5,3,2,0]]"

@[implicit_reducible]
def «OneVariable M7280» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,1,0],[3,0,0,4,1],[1,1,2,3,4],[0,0,4,3,0],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M7280^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,1,0,0],[2,0,1,0,1],[4,0,2,4,2],[1,4,3,3,3],[0,1,4,0,4]]"

@[implicit_reducible]
def «OneVariable M7287» : Magma (Fin 5) where
  op := finOpTable "[[1,3,2,4,0],[2,0,4,3,1],[0,0,2,3,4],[1,1,2,3,1],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M7287^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,0,1,0],[3,0,0,1,1],[2,4,2,2,2],[4,3,3,3,3],[0,1,4,1,4]]"

@[implicit_reducible]
def «OneVariable M7297» : Magma (Fin 5) where
  op := finOpTable "[[3,2,0,1,3],[3,1,2,0,2],[0,1,2,2,4],[4,2,4,3,0],[0,4,4,0,4]]"

@[implicit_reducible]
def «OneVariable M7297^op» : Magma (Fin 5) where
  op := finOpTable "[[3,3,0,4,0],[2,1,1,2,4],[0,2,2,4,4],[1,0,2,3,0],[3,2,4,0,4]]"

@[implicit_reducible]
def «OneVariable M7313» : Magma (Fin 5) where
  op := finOpTable "[[2,4,1,2,0],[2,1,0,1,1],[3,0,2,1,0],[0,3,0,3,3],[0,4,4,3,4]]"

@[implicit_reducible]
def «OneVariable M7313^op» : Magma (Fin 5) where
  op := finOpTable "[[2,2,3,0,0],[4,1,0,3,4],[1,0,2,0,4],[2,1,1,3,3],[0,1,0,3,4]]"

@[implicit_reducible]
def «OneVariable M7427» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,1],[4,0,0,1,3],[1,1,2,4,0],[1,2,2,3,2],[0,0,2,2,4]]"

@[implicit_reducible]
def «OneVariable M7427^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,1,1,0],[2,0,1,2,0],[3,0,2,2,2],[0,1,4,3,2],[1,3,0,2,4]]"

@[implicit_reducible]
def «OneVariable M7535» : Magma (Fin 4) where
  op := finOpTable "[[2,3,1,0],[2,1,0,1],[3,0,2,0],[0,2,0,3]]"

@[implicit_reducible]
def «OneVariable M7535^op» : Magma (Fin 4) where
  op := finOpTable "[[2,2,3,0],[3,1,0,2],[1,0,2,0],[0,1,0,3]]"

@[implicit_reducible]
def «OneVariable M7550» : Magma (Fin 5) where
  op := finOpTable "[[2,3,1,0,2],[2,1,1,1,1],[4,0,2,0,0],[0,3,4,3,3],[0,4,0,3,4]]"

@[implicit_reducible]
def «OneVariable M7550^op» : Magma (Fin 5) where
  op := finOpTable "[[2,2,4,0,0],[3,1,0,3,4],[1,1,2,4,0],[0,1,0,3,3],[2,1,0,3,4]]"

@[implicit_reducible]
def «OneVariable M7578» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,1,0],[3,1,0,0,2],[0,0,2,1,2],[0,3,3,3,3],[0,4,4,3,4]]"

@[implicit_reducible]
def «OneVariable M7578^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,0,0,0],[2,1,0,3,4],[4,0,2,3,4],[1,0,1,3,3],[0,2,2,3,4]]"

@[implicit_reducible]
def «OneVariable M7580» : Magma (Fin 5) where
  op := finOpTable "[[3,4,3,1,0],[3,1,0,0,4],[0,4,2,3,4],[2,0,0,3,2],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M7580^op» : Magma (Fin 5) where
  op := finOpTable "[[3,3,0,2,0],[4,1,4,0,1],[3,0,2,0,2],[1,0,3,3,3],[0,4,4,2,4]]"

@[implicit_reducible]
def «OneVariable M7598» : Magma (Fin 5) where
  op := finOpTable "[[2,4,1,2,0],[2,1,0,4,4],[3,0,2,0,1],[0,1,0,3,0],[1,0,0,3,4]]"

@[implicit_reducible]
def «OneVariable M7598^op» : Magma (Fin 5) where
  op := finOpTable "[[2,2,3,0,1],[4,1,0,1,0],[1,0,2,0,0],[2,4,0,3,3],[0,4,1,0,4]]"

@[implicit_reducible]
def «OneVariable M7601» : Magma (Fin 8) where
  op := finOpTable "[[6,7,4,4,3,5,1,0],[6,1,5,3,5,4,0,3],[4,5,2,7,0,6,5,7],[4,1,2,3,4,6,6,7],[2,5,3,4,0,7,6,5],[0,7,6,6,1,4,3,5],[7,0,3,6,4,2,5,0],[0,3,6,3,5,5,0,7]]"

@[implicit_reducible]
def «OneVariable M7601^op» : Magma (Fin 8) where
  op := finOpTable "[[6,6,4,4,2,0,7,0],[7,1,5,1,5,7,0,3],[4,5,2,2,3,6,3,6],[4,3,7,3,4,6,6,3],[3,5,0,4,0,1,4,5],[5,4,6,6,7,4,2,5],[1,0,5,6,6,3,5,0],[0,3,7,7,5,5,0,7]]"

@[implicit_reducible]
def «OneVariable M7616» : Magma (Fin 5) where
  op := finOpTable "[[1,3,1,4,0],[2,1,0,0,0],[0,0,2,2,2],[0,0,3,3,3],[0,0,4,3,4]]"

@[implicit_reducible]
def «OneVariable M7616^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,0,0,0],[3,1,0,0,0],[1,0,2,3,4],[4,0,2,3,3],[0,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M7617» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,1,0],[3,1,0,0,0],[1,0,2,4,4],[0,0,0,3,0],[0,0,0,3,4]]"

@[implicit_reducible]
def «OneVariable M7617^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,1,0,0],[2,1,0,0,0],[4,0,2,0,0],[1,0,4,3,3],[0,0,4,0,4]]"

@[implicit_reducible]
def «OneVariable M7619» : Magma (Fin 5) where
  op := finOpTable "[[4,3,4,0,1],[2,1,2,1,0],[0,2,2,4,0],[0,3,4,3,0],[2,0,0,3,4]]"

@[implicit_reducible]
def «OneVariable M7619^op» : Magma (Fin 5) where
  op := finOpTable "[[4,2,0,0,2],[3,1,2,3,0],[4,2,2,4,0],[0,1,4,3,3],[1,0,0,0,4]]"

@[implicit_reducible]
def «OneVariable M7622» : Magma (Fin 9) where
  op := finOpTable "[[0,8,2,4,6,6,5,8,1],[8,6,8,4,1,5,3,6,2],[1,8,2,0,7,6,6,8,8],[3,6,7,3,4,5,1,7,5],[1,1,3,8,4,8,6,1,5],[6,1,6,8,7,8,2,5,4],[4,7,5,1,6,0,5,1,8],[8,1,8,7,7,5,1,7,8],[7,0,1,5,5,3,6,8,1]]"

@[implicit_reducible]
def «OneVariable M7622^op» : Magma (Fin 9) where
  op := finOpTable "[[0,8,1,3,1,6,4,8,7],[8,6,8,6,1,1,7,1,0],[2,8,2,7,3,6,5,8,1],[4,4,0,3,8,8,1,7,5],[6,1,7,4,4,7,6,7,5],[6,5,6,5,8,8,0,5,3],[5,3,6,1,6,2,5,1,6],[8,6,8,7,1,5,1,7,8],[1,2,8,5,5,4,8,8,1]]"

@[implicit_reducible]
def «OneVariable M7624» : Magma (Fin 5) where
  op := finOpTable "[[2,4,1,3,0],[2,1,0,2,4],[3,0,2,0,4],[0,1,0,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M7624^op» : Magma (Fin 5) where
  op := finOpTable "[[2,2,3,0,0],[4,1,0,1,1],[1,0,2,0,2],[3,2,0,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M7775» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,0],[4,1,0,2,0],[4,0,2,0,0],[4,0,0,3,0],[0,0,0,0,4]]"

@[implicit_reducible]
def «OneVariable M7775^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,4,4,0],[2,1,0,0,0],[3,0,2,0,0],[0,2,0,3,0],[0,0,0,0,4]]"

@[implicit_reducible]
def «OneVariable M7782» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,5,0],[4,1,0,0,0,1],[5,0,2,0,0,0],[4,0,0,3,0,0],[0,0,0,0,4,0],[0,0,0,0,0,5]]"

@[implicit_reducible]
def «OneVariable M7782^op» : Magma (Fin 6) where
  op := finOpTable "[[1,4,5,4,0,0],[2,1,0,0,0,0],[3,0,2,0,0,0],[0,0,0,3,0,0],[5,0,0,0,4,0],[0,1,0,0,0,5]]"

@[implicit_reducible]
def «OneVariable M7796» : Magma (Fin 6) where
  op := finOpTable "[[2,3,1,0,2,0],[5,1,0,1,0,1],[4,0,2,0,0,0],[2,1,3,3,4,5],[0,5,0,0,4,1],[0,1,5,3,4,5]]"

@[implicit_reducible]
def «OneVariable M7796^op» : Magma (Fin 6) where
  op := finOpTable "[[2,5,4,2,0,0],[3,1,0,1,5,1],[1,0,2,3,0,5],[0,1,0,3,0,3],[2,0,0,4,4,4],[0,1,0,5,1,5]]"

@[implicit_reducible]
def «OneVariable M7811» : Magma (Fin 8) where
  op := finOpTable "[[0,6,6,5,7,5,6,3],[6,7,1,6,4,2,0,5],[7,1,2,5,5,0,4,1],[2,6,5,3,7,0,0,7],[7,1,5,7,6,4,2,3],[2,2,3,4,4,5,4,1],[6,3,4,0,5,4,1,7],[3,2,1,7,0,1,6,4]]"

@[implicit_reducible]
def «OneVariable M7811^op» : Magma (Fin 8) where
  op := finOpTable "[[0,6,7,2,7,2,6,3],[6,7,1,6,1,2,3,2],[6,1,2,5,5,3,4,1],[5,6,5,3,7,4,0,7],[7,4,5,7,6,4,5,0],[5,2,0,0,4,5,4,1],[6,0,4,0,2,4,1,6],[3,5,1,7,3,1,7,4]]"

@[implicit_reducible]
def «OneVariable M7816» : Magma (Fin 9) where
  op := finOpTable "[[0,5,3,3,8,1,8,8,4],[0,1,4,3,6,4,7,7,2],[3,4,8,0,2,3,8,7,1],[2,3,5,2,7,1,7,6,8],[5,6,2,7,4,7,4,1,8],[1,1,3,1,2,5,8,8,8],[8,1,2,7,6,6,6,7,2],[8,7,2,4,1,8,3,3,5],[4,2,6,3,8,7,2,0,7]]"

@[implicit_reducible]
def «OneVariable M7816^op» : Magma (Fin 9) where
  op := finOpTable "[[0,0,3,2,5,1,8,8,4],[5,1,4,3,6,1,1,7,2],[3,4,8,5,2,3,2,2,6],[3,3,0,2,7,1,7,4,3],[8,6,2,7,4,2,6,1,8],[1,4,3,1,7,5,6,8,7],[8,7,8,7,4,8,6,3,2],[8,7,7,6,1,8,7,3,0],[4,2,1,8,8,8,2,5,7]]"

@[implicit_reducible]
def «OneVariable M7821» : Magma (Fin 6) where
  op := finOpTable "[[1,2,4,0,0,1],[5,1,0,3,3,0],[3,0,2,3,4,5],[3,0,2,3,4,5],[0,1,2,1,4,5],[0,0,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M7821^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,3,0,0],[2,1,0,0,1,0],[4,0,2,2,2,2],[0,3,3,3,1,3],[0,3,4,4,4,4],[1,0,5,5,5,5]]"

@[implicit_reducible]
def «OneVariable M7822» : Magma (Fin 5) where
  op := finOpTable "[[4,2,0,4,1],[2,1,0,3,0],[0,3,2,3,4],[0,1,2,3,0],[3,0,2,0,4]]"

@[implicit_reducible]
def «OneVariable M7822^op» : Magma (Fin 5) where
  op := finOpTable "[[4,2,0,0,3],[2,1,3,1,0],[0,0,2,2,2],[4,3,3,3,0],[1,0,4,0,4]]"

@[implicit_reducible]
def «OneVariable M7824» : Magma (Fin 10) where
  op := finOpTable "[[1,2,4,0,0,8,6,1,9,8],[7,4,0,1,5,3,1,0,8,4],[3,0,2,4,6,7,6,6,6,2],[3,1,4,6,7,6,9,4,3,8],[0,9,6,2,3,1,4,3,1,1],[8,6,2,3,1,5,3,3,1,3],[6,9,8,5,4,3,8,0,7,3],[0,0,2,4,4,2,0,7,6,2],[5,8,6,3,1,1,2,6,0,0],[8,1,9,0,1,7,3,2,8,9]]"

@[implicit_reducible]
def «OneVariable M7824^op» : Magma (Fin 10) where
  op := finOpTable "[[1,7,3,3,0,8,6,0,5,8],[2,4,0,1,9,6,9,0,8,1],[4,0,2,4,6,2,8,2,6,9],[0,1,4,6,2,3,5,4,3,0],[0,5,6,7,3,1,4,4,1,1],[8,3,7,6,1,5,3,2,1,7],[6,1,6,9,4,3,8,0,2,3],[1,0,6,4,3,3,0,7,6,2],[9,8,6,3,1,1,7,6,0,8],[8,4,2,8,1,3,3,2,0,9]]"

@[implicit_reducible]
def «OneVariable M8104» : Magma (Fin 8) where
  op := finOpTable "[[3,2,1,4,5,0,0,2],[2,1,2,6,4,4,3,1],[7,2,0,2,6,6,5,1],[5,7,3,6,0,0,1,3],[3,6,6,0,4,6,2,3],[0,3,6,0,3,5,6,7],[6,3,4,7,5,6,2,3],[2,3,0,3,3,7,3,7]]"

@[implicit_reducible]
def «OneVariable M8104^op» : Magma (Fin 8) where
  op := finOpTable "[[3,2,7,5,3,0,6,2],[2,1,2,7,6,3,3,3],[1,2,0,3,6,6,4,0],[4,6,2,6,0,0,7,3],[5,4,6,0,4,3,5,3],[0,4,6,0,6,5,6,7],[0,3,5,1,2,6,2,3],[2,1,1,3,3,7,3,7]]"

@[implicit_reducible]
def «OneVariable M8106» : Magma (Fin 9) where
  op := finOpTable "[[0,0,1,3,4,5,3,0,8],[0,1,0,4,4,6,5,4,5],[7,0,2,4,3,6,6,5,8],[6,4,4,6,1,3,8,3,7],[4,3,0,2,3,7,4,5,5],[5,6,6,5,8,4,2,4,0],[3,7,5,0,6,1,5,6,3],[3,7,0,3,5,5,6,7,5],[8,0,8,6,5,4,3,6,8]]"

@[implicit_reducible]
def «OneVariable M8106^op» : Magma (Fin 9) where
  op := finOpTable "[[0,0,7,6,4,5,3,3,8],[0,1,0,4,3,6,7,7,0],[1,0,2,4,0,6,5,0,8],[3,4,4,6,2,5,0,3,6],[4,4,3,1,3,8,6,5,5],[5,6,6,3,7,4,1,5,4],[3,5,6,8,4,2,5,6,3],[0,4,5,3,5,4,6,7,6],[8,5,8,7,5,0,3,5,8]]"

@[implicit_reducible]
def «OneVariable M8220» : Magma (Fin 10) where
  op := finOpTable "[[2,9,1,6,2,6,5,7,2,0],[9,1,3,3,9,8,7,7,8,9],[8,0,9,4,2,9,6,9,0,3],[9,3,4,3,6,1,2,3,0,9],[0,9,2,6,7,7,4,3,9,1],[6,5,2,1,4,5,6,4,1,2],[3,7,6,2,4,0,0,1,7,9],[7,6,2,4,5,4,8,6,0,9],[0,8,0,0,8,7,1,0,8,6],[0,4,5,2,8,2,9,9,6,4]]"

@[implicit_reducible]
def «OneVariable M8220^op» : Magma (Fin 10) where
  op := finOpTable "[[2,9,8,9,0,6,3,7,0,0],[9,1,0,3,9,5,7,6,8,4],[1,3,9,4,2,2,6,2,0,5],[6,3,4,3,6,1,2,4,0,2],[2,9,2,6,7,4,4,5,8,8],[6,8,9,1,7,5,0,4,7,2],[5,7,6,2,4,6,0,8,1,9],[7,7,9,3,3,4,1,6,0,9],[2,8,0,0,9,1,7,0,8,6],[0,9,3,9,1,2,9,9,6,4]]"

@[implicit_reducible]
def «OneVariable M8236» : Magma (Fin 10) where
  op := finOpTable "[[2,2,8,9,9,5,6,0,7,3],[0,1,1,4,1,0,6,7,1,5],[1,0,7,5,7,2,2,3,0,9],[9,5,6,3,4,3,6,2,2,9],[9,4,2,4,4,6,0,4,3,2],[5,0,2,6,6,9,3,7,9,1],[6,7,2,5,0,4,5,1,7,6],[0,6,4,2,2,7,8,6,5,7],[7,1,0,2,3,5,7,5,8,5],[4,5,9,0,2,8,6,7,5,0]]"

@[implicit_reducible]
def «OneVariable M8236^op» : Magma (Fin 10) where
  op := finOpTable "[[2,0,1,9,9,5,6,0,7,4],[2,1,0,5,4,0,7,6,1,5],[8,1,7,6,2,2,2,4,0,9],[9,4,5,3,4,6,5,2,2,0],[9,1,7,4,4,6,0,2,3,2],[5,0,2,3,6,9,4,7,5,8],[6,6,2,6,0,3,5,8,7,6],[0,7,3,2,4,7,1,6,5,7],[7,1,0,2,3,9,7,5,8,5],[3,5,9,9,2,1,6,7,5,0]]"

@[implicit_reducible]
def «OneVariable M8258» : Magma (Fin 9) where
  op := finOpTable "[[0,8,0,7,0,4,3,6,8],[8,3,4,2,1,3,1,8,0],[2,4,2,1,7,8,6,4,6],[7,5,1,6,6,1,0,3,3],[0,1,7,3,4,8,3,7,8],[4,1,8,1,4,5,7,5,6],[3,6,8,4,3,7,8,6,5],[0,8,4,3,2,7,6,7,4],[1,7,6,8,8,6,2,4,1]]"

@[implicit_reducible]
def «OneVariable M8258^op» : Magma (Fin 9) where
  op := finOpTable "[[0,8,2,7,0,4,3,0,1],[8,3,4,5,1,1,6,8,7],[0,4,2,1,7,8,8,4,6],[7,2,1,6,3,1,4,3,8],[0,1,7,6,4,4,3,2,8],[4,3,8,1,8,5,7,7,6],[3,1,6,0,3,7,8,6,2],[6,8,4,3,7,5,6,7,4],[8,0,6,3,8,6,5,4,1]]"

@[implicit_reducible]
def «OneVariable M8296» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,0,0,4],[2,1,0,4,0,0],[0,0,2,0,0,0],[4,0,0,3,0,0],[0,0,0,0,4,0],[4,0,0,0,0,5]]"

@[implicit_reducible]
def «OneVariable M8296^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,0,4,0,4],[5,1,0,0,0,0],[3,0,2,0,0,0],[0,4,0,3,0,0],[0,0,0,0,4,0],[4,0,0,0,0,5]]"

@[implicit_reducible]
def «OneVariable M8320» : Magma (Fin 5) where
  op := finOpTable "[[3,4,4,1,0],[3,1,2,0,3],[0,4,2,0,3],[2,1,0,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M8320^op» : Magma (Fin 5) where
  op := finOpTable "[[3,3,0,2,0],[4,1,4,1,1],[4,2,2,0,2],[1,0,0,3,3],[0,3,3,4,4]]"

@[implicit_reducible]
def «OneVariable M8400» : Magma (Fin 5) where
  op := finOpTable "[[3,4,4,1,0],[3,1,2,0,4],[0,4,2,3,3],[2,0,0,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M8400^op» : Magma (Fin 5) where
  op := finOpTable "[[3,3,0,2,0],[4,1,4,0,1],[4,2,2,0,2],[1,0,3,3,3],[0,4,3,4,4]]"

@[implicit_reducible]
def «OneVariable M8415» : Magma (Fin 6) where
  op := finOpTable "[[2,3,1,0,5,0],[2,1,0,1,1,1],[4,0,2,3,0,1],[2,1,0,3,4,5],[0,1,0,3,4,5],[0,3,3,3,4,5]]"

@[implicit_reducible]
def «OneVariable M8415^op» : Magma (Fin 6) where
  op := finOpTable "[[2,2,4,2,0,0],[3,1,0,1,1,3],[1,0,2,0,0,3],[0,1,3,3,3,3],[5,1,0,4,4,4],[0,1,1,5,5,5]]"

@[implicit_reducible]
def «OneVariable M8418» : Magma (Fin 9) where
  op := finOpTable "[[0,7,2,6,8,0,6,7,8],[7,8,7,5,4,1,5,0,6],[2,7,2,2,8,0,6,1,4],[2,1,6,3,7,5,0,4,1],[8,1,8,6,7,6,4,3,0],[2,1,6,3,4,5,2,4,8],[8,8,6,3,4,2,6,7,1],[6,2,6,4,5,4,7,1,8],[5,3,5,1,2,8,1,7,4]]"

@[implicit_reducible]
def «OneVariable M8418^op» : Magma (Fin 9) where
  op := finOpTable "[[0,7,2,2,8,2,8,6,5],[7,8,7,1,1,1,8,2,3],[2,7,2,6,8,6,6,6,5],[6,5,2,3,6,3,3,4,1],[8,4,8,7,7,4,4,5,2],[0,1,0,5,6,5,2,4,8],[6,5,6,0,4,2,6,7,1],[7,0,1,4,3,4,7,1,7],[8,6,4,1,0,8,1,8,4]]"

@[implicit_reducible]
def «OneVariable M8421» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,0,0,4],[2,1,0,3,3,0],[0,0,2,3,4,5],[4,1,2,3,4,5],[0,1,2,3,4,5],[1,0,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M8421^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,0,4,0,1],[5,1,0,1,1,0],[3,0,2,2,2,2],[0,3,3,3,3,3],[0,3,4,4,4,4],[4,0,5,5,5,5]]"

@[implicit_reducible]
def «OneVariable M8479» : Magma (Fin 5) where
  op := finOpTable "[[1,3,4,4,0],[2,1,2,0,4],[0,0,2,3,4],[4,0,2,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M8479^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,0,4,0],[3,1,0,0,1],[4,2,2,2,2],[4,0,3,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M8497» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,0,3],[2,1,0,1,0],[0,1,2,0,0],[0,0,0,3,0],[3,0,0,0,4]]"

@[implicit_reducible]
def «OneVariable M8497^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,0,0,3],[4,1,1,0,0],[3,0,2,0,0],[0,1,0,3,0],[3,0,0,0,4]]"

@[implicit_reducible]
def «OneVariable M8513» : Magma (Fin 9) where
  op := finOpTable "[[3,7,2,6,0,7,4,5,4],[7,1,2,3,6,6,8,4,6],[0,2,7,4,3,3,1,6,1],[8,3,5,2,1,1,0,7,0],[0,6,3,3,4,6,5,7,4],[7,3,3,1,6,5,6,7,1],[4,4,1,0,5,6,6,2,5],[1,4,8,3,7,4,2,0,2],[0,6,2,0,4,6,6,2,8]]"

@[implicit_reducible]
def «OneVariable M8513^op» : Magma (Fin 9) where
  op := finOpTable "[[3,7,0,8,0,7,4,1,0],[7,1,2,3,6,3,4,4,6],[2,2,7,5,3,3,1,8,2],[6,3,4,2,3,1,0,3,0],[0,6,3,1,4,6,5,7,4],[7,6,3,1,6,5,6,4,6],[4,8,1,0,5,6,6,2,6],[5,4,6,7,7,7,2,0,2],[4,6,1,0,4,1,5,2,8]]"

@[implicit_reducible]
def «OneVariable M8516» : Magma (Fin 10) where
  op := finOpTable "[[1,4,3,0,5,0,6,8,7,8],[2,5,0,1,0,7,3,3,8,3],[0,0,2,5,0,6,0,7,6,9],[3,1,5,6,5,4,7,8,3,0],[5,0,0,5,4,5,6,7,6,0],[0,9,6,2,6,3,5,1,1,1],[6,3,0,9,0,5,8,3,2,3],[8,3,7,8,0,1,3,7,8,2],[9,8,6,3,6,1,4,1,0,1],[8,1,7,3,0,1,3,2,1,9]]"

@[implicit_reducible]
def «OneVariable M8516^op» : Magma (Fin 10) where
  op := finOpTable "[[1,2,0,3,5,0,6,8,9,8],[4,5,0,1,0,9,3,3,8,1],[3,0,2,5,0,6,0,7,6,7],[0,1,5,6,5,2,9,8,3,3],[5,0,0,5,4,6,0,0,6,0],[0,7,6,4,5,3,5,1,1,1],[6,3,0,7,6,5,8,3,4,3],[8,3,7,8,7,1,3,7,1,2],[7,8,6,3,6,1,2,8,0,1],[8,3,9,0,0,1,3,2,1,9]]"

@[implicit_reducible]
def «OneVariable M8517» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,0,3],[2,1,0,3,0],[0,0,2,3,4],[0,0,2,3,4],[3,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M8517^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,0,0,3],[4,1,0,0,0],[3,0,2,2,2],[0,3,3,3,3],[3,0,4,4,4]]"

@[implicit_reducible]
def «OneVariable M8518» : Magma (Fin 10) where
  op := finOpTable "[[1,2,6,0,4,7,0,8,7,6],[9,6,0,8,1,8,3,7,1,0],[3,0,2,9,6,0,6,4,8,3],[3,8,9,3,0,5,1,4,0,0],[4,1,6,0,7,5,2,3,6,0],[7,1,4,3,5,5,1,1,0,9],[0,5,7,1,8,1,4,6,7,8],[5,7,4,4,9,1,6,0,1,4],[7,1,2,0,6,9,7,7,8,5],[0,0,3,3,4,5,1,4,2,9]]"

@[implicit_reducible]
def «OneVariable M8518^op» : Magma (Fin 10) where
  op := finOpTable "[[1,9,3,3,4,7,0,5,7,0],[2,6,0,8,1,1,5,7,1,0],[6,0,2,9,6,4,7,4,2,3],[0,8,9,3,0,3,1,4,0,3],[4,1,6,0,7,5,8,9,6,4],[7,8,0,5,5,5,1,1,9,5],[0,3,6,1,2,1,4,6,7,1],[8,7,4,4,3,1,6,0,7,4],[7,1,8,0,6,0,7,1,8,2],[6,0,3,0,0,9,8,4,5,9]]"

@[implicit_reducible]
def «OneVariable M8629» : Magma (Fin 10) where
  op := finOpTable "[[1,2,6,3,4,6,0,8,9,8],[5,6,0,1,3,0,7,3,8,3],[3,0,2,6,0,7,6,2,4,9],[0,1,6,4,7,6,2,8,3,8],[4,9,0,9,8,0,6,3,2,3],[0,0,6,6,4,5,4,2,4,0],[0,9,4,5,6,4,3,1,8,1],[8,9,2,0,3,2,1,7,1,7],[7,8,4,3,5,4,0,1,0,1],[8,1,9,3,3,0,1,3,8,9]]"

@[implicit_reducible]
def «OneVariable M8629^op» : Magma (Fin 10) where
  op := finOpTable "[[1,5,3,0,4,0,0,8,7,8],[2,6,0,1,9,0,9,9,8,1],[6,0,2,6,0,6,4,2,4,9],[3,1,6,4,9,6,5,0,3,3],[4,3,0,7,8,4,6,3,5,3],[6,0,7,6,0,5,4,2,4,0],[0,7,6,2,6,4,3,1,0,1],[8,3,2,8,3,2,1,7,1,3],[9,8,4,3,2,4,8,1,0,8],[8,3,9,8,3,0,1,7,1,9]]"

@[implicit_reducible]
def «OneVariable M8630» : Magma (Fin 9) where
  op := finOpTable "[[3,7,5,1,0,2,2,0,7],[3,1,4,0,2,1,7,7,0],[6,4,0,2,8,7,7,2,4],[8,0,3,4,7,6,3,6,0],[4,6,1,5,2,3,4,3,6],[2,6,2,3,3,5,6,7,4],[2,0,0,3,4,6,6,2,2],[0,7,2,4,3,7,2,7,6],[0,8,4,0,4,1,2,6,8]]"

@[implicit_reducible]
def «OneVariable M8630^op» : Magma (Fin 9) where
  op := finOpTable "[[3,3,6,8,4,2,2,0,0],[7,1,4,0,6,6,0,7,8],[5,4,0,3,1,2,0,2,4],[1,0,2,4,5,3,3,4,0],[0,2,8,7,2,3,4,3,4],[2,1,7,6,3,5,6,7,1],[2,7,7,3,4,6,6,2,2],[0,7,2,6,3,7,2,7,6],[7,0,4,0,6,4,2,6,8]]"

@[implicit_reducible]
def «OneVariable M8639» : Magma (Fin 10) where
  op := finOpTable "[[1,2,4,6,0,5,2,8,7,4],[9,4,3,5,5,6,1,7,6,0],[4,0,5,9,7,4,6,2,7,3],[7,5,1,2,4,3,8,1,6,5],[0,8,7,4,6,2,7,3,1,3],[5,6,8,3,1,7,0,6,2,0],[2,1,6,0,9,0,3,5,2,4],[3,7,2,1,3,9,4,0,1,5],[7,1,2,6,1,2,6,7,8,9],[0,0,3,3,4,5,4,5,9,9]]"

@[implicit_reducible]
def «OneVariable M8639^op» : Magma (Fin 10) where
  op := finOpTable "[[1,9,4,7,0,5,2,3,7,0],[2,4,0,5,8,6,1,7,1,0],[4,3,5,1,7,8,6,2,2,3],[6,5,9,2,4,3,0,1,6,3],[0,5,7,4,6,1,9,3,1,4],[5,6,4,3,2,7,0,9,2,5],[2,1,6,8,7,0,3,4,6,4],[8,7,2,1,3,6,5,0,7,5],[7,6,7,6,1,2,2,1,8,9],[4,0,3,5,3,0,4,5,9,9]]"

@[implicit_reducible]
def «OneVariable M8672» : Magma (Fin 10) where
  op := finOpTable "[[2,6,3,7,4,8,9,0,0,6],[8,1,4,2,1,5,5,1,1,4],[5,9,7,0,2,0,6,1,4,2],[7,5,1,3,4,3,4,7,8,0],[4,5,2,0,6,7,8,5,0,7],[0,2,0,5,7,5,6,7,0,0],[1,5,6,4,3,6,0,7,4,2],[0,2,8,7,9,3,7,4,2,6],[0,2,2,0,0,0,4,2,8,3],[6,7,2,0,2,0,6,6,0,9]]"

@[implicit_reducible]
def «OneVariable M8672^op» : Magma (Fin 10) where
  op := finOpTable "[[2,8,5,7,4,0,1,0,0,6],[6,1,9,5,5,2,5,2,2,7],[3,4,7,1,2,0,6,8,2,2],[7,2,0,3,0,5,4,7,0,0],[4,1,2,4,6,7,3,9,0,2],[8,5,0,3,7,5,6,3,0,0],[9,5,6,4,8,6,0,7,4,6],[0,1,1,7,5,7,7,4,2,6],[0,1,4,8,0,0,4,2,8,0],[6,4,2,0,7,0,2,6,3,9]]"

@[implicit_reducible]
def «OneVariable M8680» : Magma (Fin 10) where
  op := finOpTable "[[2,6,8,4,0,5,1,6,4,9],[2,1,2,6,4,3,6,1,3,9],[3,9,4,0,7,9,6,9,0,2],[0,1,4,3,4,5,3,3,6,3],[0,2,1,5,9,4,5,2,5,8],[5,9,9,0,4,6,8,9,0,1],[7,2,6,5,5,3,0,2,5,9],[6,7,9,3,2,9,2,7,5,0],[4,3,0,6,5,0,5,0,8,4],[9,6,2,4,3,7,9,0,4,5]]"

@[implicit_reducible]
def «OneVariable M8680^op» : Magma (Fin 10) where
  op := finOpTable "[[2,2,3,0,0,5,7,6,4,9],[6,1,9,1,2,9,2,7,3,6],[8,2,4,4,1,9,6,9,0,2],[4,6,0,3,5,0,5,3,6,4],[0,4,7,4,9,4,5,2,5,3],[5,3,9,5,4,6,3,9,0,7],[1,6,6,3,5,8,0,2,5,9],[6,1,9,3,2,9,2,7,0,0],[4,3,0,6,5,0,5,5,8,4],[9,9,2,3,8,1,9,0,4,5]]"

@[implicit_reducible]
def «OneVariable M8688» : Magma (Fin 10) where
  op := finOpTable "[[1,2,3,0,0,9,9,4,8,6],[7,4,0,8,3,5,8,0,1,9],[4,0,2,3,2,6,6,0,0,8],[3,8,2,3,1,3,0,7,8,8],[0,6,2,1,8,9,1,9,7,4],[9,5,1,3,4,5,9,7,4,1],[9,1,2,2,1,0,6,0,0,9],[0,0,5,7,9,7,0,7,4,8],[8,1,0,0,5,4,0,4,9,2],[5,9,8,8,4,1,1,7,3,0]]"

@[implicit_reducible]
def «OneVariable M8688^op» : Magma (Fin 10) where
  op := finOpTable "[[1,7,4,3,0,9,9,0,8,5],[2,4,0,8,6,5,1,0,1,9],[3,0,2,2,2,1,2,5,0,8],[0,8,3,3,1,3,2,7,0,8],[0,3,2,1,8,4,1,9,5,4],[9,5,6,3,9,5,0,7,4,1],[9,8,6,0,1,9,6,0,0,1],[4,0,0,7,9,7,0,7,4,7],[8,1,0,8,7,4,0,4,9,3],[6,9,8,8,4,1,9,8,2,0]]"

@[implicit_reducible]
def «OneVariable M8692» : Magma (Fin 9) where
  op := finOpTable "[[6,2,1,8,1,8,3,0,0],[4,0,5,7,5,1,1,8,7],[1,1,2,3,6,3,8,6,2],[8,7,5,3,7,8,0,5,5],[1,5,5,1,4,4,6,6,1],[0,1,4,5,5,5,0,7,5],[5,6,8,0,8,0,7,2,6],[7,3,6,5,6,7,4,1,5],[0,7,2,2,6,8,6,7,8]]"

@[implicit_reducible]
def «OneVariable M8692^op» : Magma (Fin 9) where
  op := finOpTable "[[6,4,1,8,1,0,5,7,0],[2,0,1,7,5,1,6,3,7],[1,5,2,5,5,4,8,6,2],[8,7,3,3,1,5,0,5,2],[1,5,6,7,4,5,8,6,6],[8,1,3,8,4,5,0,7,8],[3,1,8,0,6,0,7,4,6],[0,8,6,5,6,7,2,1,7],[0,7,2,5,1,5,6,5,8]]"

@[implicit_reducible]
def «OneVariable M8693» : Magma (Fin 8) where
  op := finOpTable "[[1,1,1,3,6,0,1,7],[2,5,3,1,4,5,0,5],[0,0,2,3,3,0,6,7],[3,1,4,4,4,6,1,7],[0,4,2,2,0,5,0,7],[0,7,2,3,5,3,3,7],[4,4,4,5,4,5,6,7],[4,1,2,5,3,1,6,7]]"

@[implicit_reducible]
def «OneVariable M8693^op» : Magma (Fin 8) where
  op := finOpTable "[[1,2,0,3,0,0,4,4],[1,5,0,1,4,7,4,1],[1,3,2,4,2,2,4,2],[3,1,3,4,2,3,5,5],[6,4,3,4,0,5,4,3],[0,5,0,6,5,3,5,1],[1,0,6,1,0,3,6,6],[7,5,7,7,7,7,7,7]]"

@[implicit_reducible]
def «OneVariable M8695» : Magma (Fin 4) where
  op := finOpTable "[[1,1,3,0],[2,1,1,2],[0,0,2,0],[0,1,0,3]]"

@[implicit_reducible]
def «OneVariable M8695^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,0],[1,1,0,1],[3,1,2,0],[0,2,0,3]]"

@[implicit_reducible]
def «OneVariable M8696» : Magma (Fin 4) where
  op := finOpTable "[[2,3,2,0],[0,1,3,3],[1,0,2,3],[0,2,0,3]]"

@[implicit_reducible]
def «OneVariable M8696^op» : Magma (Fin 4) where
  op := finOpTable "[[2,0,1,0],[3,1,0,2],[2,3,2,0],[0,3,3,3]]"

@[implicit_reducible]
def «OneVariable M8697» : Magma (Fin 4) where
  op := finOpTable "[[1,1,3,0],[2,1,0,1],[0,0,2,0],[2,0,0,3]]"

@[implicit_reducible]
def «OneVariable M8697^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,2],[1,1,0,0],[3,0,2,0],[0,1,0,3]]"

@[implicit_reducible]
def «OneVariable M8701» : Magma (Fin 8) where
  op := finOpTable "[[6,0,2,3,1,5,6,5],[0,2,2,2,0,7,3,1],[2,5,7,2,3,1,6,7],[6,6,2,3,7,7,6,7],[0,3,2,3,4,7,0,2],[7,1,1,0,4,5,6,7],[4,1,6,2,4,7,1,7],[0,1,4,3,3,6,7,0]]"

@[implicit_reducible]
def «OneVariable M8701^op» : Magma (Fin 8) where
  op := finOpTable "[[6,0,2,6,0,7,4,0],[0,2,5,6,3,1,1,1],[2,2,7,2,2,1,6,4],[3,2,2,3,3,0,2,3],[1,0,3,7,4,4,4,3],[5,7,1,7,7,5,7,6],[6,3,6,6,0,6,1,7],[5,1,7,7,2,7,7,0]]"

@[implicit_reducible]
def «OneVariable M8702» : Magma (Fin 8) where
  op := finOpTable "[[1,1,4,7,0,5,6,3],[2,4,0,6,4,5,1,7],[0,2,2,3,4,5,0,3],[3,1,3,3,0,3,6,7],[0,3,5,1,6,4,6,7],[5,5,0,6,4,7,3,7],[6,1,4,0,2,5,5,6],[0,7,5,4,7,2,6,0]]"

@[implicit_reducible]
def «OneVariable M8702^op» : Magma (Fin 8) where
  op := finOpTable "[[1,2,0,3,0,5,6,0],[1,4,2,1,3,5,1,7],[4,0,2,3,5,0,4,5],[7,6,3,3,1,6,0,4],[0,4,4,0,6,4,2,7],[5,5,5,3,4,7,5,2],[6,1,0,6,6,3,5,6],[3,7,3,7,7,7,6,0]]"

@[implicit_reducible]
def «OneVariable M8703» : Magma (Fin 8) where
  op := finOpTable "[[4,3,6,0,4,5,2,3],[0,1,0,3,0,3,7,7],[6,3,2,2,4,5,6,2],[0,6,2,5,7,5,3,4],[1,0,7,3,3,4,6,5],[5,3,7,1,4,6,6,0],[0,1,4,3,6,7,0,5],[0,0,2,4,4,5,5,7]]"

@[implicit_reducible]
def «OneVariable M8703^op» : Magma (Fin 8) where
  op := finOpTable "[[4,0,6,0,1,5,0,0],[3,1,3,6,0,3,1,0],[6,0,2,2,7,7,4,2],[0,3,2,5,3,1,3,4],[4,0,4,7,3,4,6,4],[5,3,5,5,4,6,7,5],[2,7,6,3,6,6,0,5],[3,7,2,4,5,0,5,7]]"

@[implicit_reducible]
def «OneVariable M8739» : Magma (Fin 3) where
  op := finOpTable "[[1,2,1],[1,1,1],[0,0,2]]"

@[implicit_reducible]
def «OneVariable M8739^op» : Magma (Fin 3) where
  op := finOpTable "[[1,1,0],[2,1,0],[1,1,2]]"

@[implicit_reducible]
def «OneVariable M8740» : Magma (Fin 3) where
  op := finOpTable "[[1,2,1],[0,1,1],[0,0,2]]"

@[implicit_reducible]
def «OneVariable M8740^op» : Magma (Fin 3) where
  op := finOpTable "[[1,0,0],[2,1,0],[1,1,2]]"

@[implicit_reducible]
def «OneVariable M8743» : Magma (Fin 3) where
  op := finOpTable "[[0,1,1],[1,2,0],[2,1,2]]"

@[implicit_reducible]
def «OneVariable M8743^op» : Magma (Fin 3) where
  op := finOpTable "[[0,1,2],[1,2,1],[1,0,2]]"

@[implicit_reducible]
def «OneVariable M8802» : Magma (Fin 4) where
  op := finOpTable "[[0,3,1,1],[3,1,3,0],[3,0,2,3],[2,0,0,0]]"

@[implicit_reducible]
def «OneVariable M8802^op» : Magma (Fin 4) where
  op := finOpTable "[[0,3,3,2],[3,1,0,0],[1,3,2,0],[1,0,3,0]]"

@[implicit_reducible]
def «OneVariable M8834» : Magma (Fin 4) where
  op := finOpTable "[[2,2,3,2],[3,1,0,3],[1,0,2,0],[0,3,0,3]]"

@[implicit_reducible]
def «OneVariable M8834^op» : Magma (Fin 4) where
  op := finOpTable "[[2,3,1,0],[2,1,0,3],[3,0,2,0],[2,3,0,3]]"

@[implicit_reducible]
def «OneVariable M8889» : Magma (Fin 3) where
  op := finOpTable "[[1,2,0],[0,1,0],[0,0,2]]"

@[implicit_reducible]
def «OneVariable M8889^op» : Magma (Fin 3) where
  op := finOpTable "[[1,0,0],[2,1,0],[0,0,2]]"

@[implicit_reducible]
def «OneVariable M8890» : Magma (Fin 3) where
  op := finOpTable "[[1,2,1],[0,1,0],[0,2,2]]"

@[implicit_reducible]
def «OneVariable M8890^op» : Magma (Fin 3) where
  op := finOpTable "[[1,0,0],[2,1,2],[1,0,2]]"

@[implicit_reducible]
def «OneVariable M8949» : Magma (Fin 3) where
  op := finOpTable "[[1,2,1],[1,1,0],[0,0,2]]"

@[implicit_reducible]
def «OneVariable M8949^op» : Magma (Fin 3) where
  op := finOpTable "[[1,1,0],[2,1,0],[1,0,2]]"

@[implicit_reducible]
def «OneVariable M8950» : Magma (Fin 3) where
  op := finOpTable "[[1,2,1],[0,1,0],[0,0,2]]"

@[implicit_reducible]
def «OneVariable M8950^op» : Magma (Fin 3) where
  op := finOpTable "[[1,0,0],[2,1,0],[1,0,2]]"

@[implicit_reducible]
def «OneVariable M8964» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,1],[2,1,0,0],[1,0,2,0],[0,0,2,3]]"

@[implicit_reducible]
def «OneVariable M9029» : Magma (Fin 4) where
  op := finOpTable "[[0,3,1,1],[2,0,0,0],[3,1,2,0],[1,0,1,3]]"

@[implicit_reducible]
def «OneVariable M9029^op» : Magma (Fin 4) where
  op := finOpTable "[[0,2,3,1],[3,0,1,0],[1,0,2,1],[1,0,0,3]]"

@[implicit_reducible]
def «OneVariable M9088» : Magma (Fin 4) where
  op := finOpTable "[[1,2,2,1],[3,1,0,0],[0,0,2,3],[1,0,2,3]]"

@[implicit_reducible]
def «OneVariable M9088^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,1],[2,1,0,0],[2,0,2,2],[1,0,3,3]]"

@[implicit_reducible]
def «OneVariable M9092» : Magma (Fin 4) where
  op := finOpTable "[[0,0,3,3],[0,1,3,2],[3,3,2,1],[2,2,0,2]]"

@[implicit_reducible]
def «OneVariable M9092^op» : Magma (Fin 4) where
  op := finOpTable "[[0,0,3,2],[0,1,3,2],[3,3,2,0],[3,2,1,2]]"

@[implicit_reducible]
def «OneVariable M9101» : Magma (Fin 8) where
  op := finOpTable "[[0,4,2,3,7,3,5,4],[4,1,2,4,3,7,6,5],[0,1,2,4,4,5,6,5],[5,4,4,5,1,0,5,7],[7,3,3,2,3,5,7,0],[3,7,7,6,4,7,3,2],[6,1,2,5,7,3,6,7],[4,5,5,3,6,1,4,4]]"

@[implicit_reducible]
def «OneVariable M9101^op» : Magma (Fin 8) where
  op := finOpTable "[[0,4,0,5,7,3,6,4],[4,1,1,4,3,7,1,5],[2,2,2,4,3,7,2,5],[3,4,4,5,2,6,5,3],[7,3,4,1,3,4,7,6],[3,7,5,0,5,7,3,1],[5,6,6,5,7,3,6,4],[4,5,5,7,0,2,7,4]]"

@[implicit_reducible]
def «OneVariable M9108» : Magma (Fin 4) where
  op := finOpTable "[[2,2,1,1],[0,1,0,3],[3,0,2,0],[2,1,0,3]]"

@[implicit_reducible]
def «OneVariable M9108^op» : Magma (Fin 4) where
  op := finOpTable "[[2,0,3,2],[2,1,0,1],[1,0,2,0],[1,3,0,3]]"

@[implicit_reducible]
def «OneVariable M9134» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,1],[2,0,0,1],[2,1,2,0],[0,3,3,3]]"

@[implicit_reducible]
def «OneVariable M9134^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,2,0],[3,0,1,3],[0,0,2,3],[1,1,0,3]]"

@[implicit_reducible]
def «OneVariable M9191» : Magma (Fin 5) where
  op := finOpTable "[[1,3,4,3,0],[2,1,0,0,2],[4,0,2,0,0],[0,0,2,3,2],[0,0,2,0,4]]"

@[implicit_reducible]
def «OneVariable M9191^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,0,0],[3,1,0,0,0],[4,0,2,2,2],[3,0,0,3,0],[0,2,0,2,4]]"

@[implicit_reducible]
def «OneVariable M9272» : Magma (Fin 5) where
  op := finOpTable "[[1,3,0,1,1],[4,0,1,0,0],[1,3,2,0,0],[0,2,3,3,3],[2,1,4,0,4]]"

@[implicit_reducible]
def «OneVariable M9272^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,1,0,2],[3,0,3,2,1],[0,1,2,3,4],[1,0,0,3,0],[1,0,0,3,4]]"

@[implicit_reducible]
def «OneVariable M9275» : Magma (Fin 5) where
  op := finOpTable "[[1,3,1,1,0],[2,0,0,0,1],[4,1,2,2,2],[0,4,3,3,3],[0,1,4,4,4]]"

@[implicit_reducible]
def «OneVariable M9275^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,0,0],[3,0,1,4,1],[1,0,2,3,4],[1,0,2,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M9285» : Magma (Fin 5) where
  op := finOpTable "[[1,3,3,1,0],[2,0,0,2,1],[4,1,2,2,2],[0,4,3,3,3],[0,1,4,4,4]]"

@[implicit_reducible]
def «OneVariable M9285^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,0,0],[3,0,1,4,1],[3,0,2,3,4],[1,2,2,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M9337» : Magma (Fin 5) where
  op := finOpTable "[[4,4,4,0,2],[3,1,1,4,4],[0,3,2,1,0],[0,4,4,3,0],[1,0,0,2,4]]"

@[implicit_reducible]
def «OneVariable M9337^op» : Magma (Fin 5) where
  op := finOpTable "[[4,3,0,0,1],[4,1,3,4,0],[4,1,2,4,0],[0,4,1,3,2],[2,4,0,0,4]]"

@[implicit_reducible]
def «OneVariable M9372» : Magma (Fin 5) where
  op := finOpTable "[[2,0,3,2,0],[4,1,0,0,4],[1,0,2,3,4],[0,1,0,3,4],[0,3,2,3,4]]"

@[implicit_reducible]
def «OneVariable M9372^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,1,0,0],[0,1,0,1,3],[3,0,2,0,2],[2,0,3,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M9374» : Magma (Fin 5) where
  op := finOpTable "[[4,4,0,4,3],[2,1,1,1,0],[0,2,2,2,3],[0,1,3,3,0],[1,0,3,4,4]]"

@[implicit_reducible]
def «OneVariable M9374^op» : Magma (Fin 5) where
  op := finOpTable "[[4,2,0,0,1],[4,1,2,1,0],[0,1,2,3,3],[4,1,2,3,4],[3,0,3,0,4]]"

@[implicit_reducible]
def «OneVariable M9424» : Magma (Fin 5) where
  op := finOpTable "[[1,3,1,3,0],[2,0,4,0,1],[4,1,2,0,0],[0,4,0,3,0],[0,1,0,0,4]]"

@[implicit_reducible]
def «OneVariable M9424^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,0,0],[3,0,1,4,1],[1,4,2,0,0],[3,0,0,3,0],[0,1,0,0,4]]"

@[implicit_reducible]
def «OneVariable M9442» : Magma (Fin 5) where
  op := finOpTable "[[2,0,3,2,0],[4,1,0,2,4],[1,1,2,0,1],[0,1,0,3,3],[0,3,4,3,4]]"

@[implicit_reducible]
def «OneVariable M9442^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,1,0,0],[0,1,1,1,3],[3,0,2,0,4],[2,2,0,3,3],[0,4,1,3,4]]"

@[implicit_reducible]
def «OneVariable M9493» : Magma (Fin 5) where
  op := finOpTable "[[2,3,4,0,2],[3,1,4,0,3],[1,0,2,2,0],[0,0,2,3,1],[0,0,0,4,4]]"

@[implicit_reducible]
def «OneVariable M9493^op» : Magma (Fin 5) where
  op := finOpTable "[[2,3,1,0,0],[3,1,0,0,0],[4,4,2,2,0],[0,0,2,3,4],[2,3,0,1,4]]"

@[implicit_reducible]
def «OneVariable M9522» : Magma (Fin 5) where
  op := finOpTable "[[4,4,0,4,3],[2,1,1,1,0],[0,2,2,2,3],[0,4,3,3,0],[1,4,4,0,4]]"

@[implicit_reducible]
def «OneVariable M9522^op» : Magma (Fin 5) where
  op := finOpTable "[[4,2,0,0,1],[4,1,2,4,4],[0,1,2,3,4],[4,1,2,3,0],[3,0,3,0,4]]"

@[implicit_reducible]
def «OneVariable M9587» : Magma (Fin 5) where
  op := finOpTable "[[3,3,0,4,3],[2,1,1,0,3],[0,2,2,4,3],[1,0,2,3,0],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M9587^op» : Magma (Fin 5) where
  op := finOpTable "[[3,2,0,1,0],[3,1,2,0,4],[0,1,2,2,4],[4,0,4,3,4],[3,3,3,0,4]]"

@[implicit_reducible]
def «OneVariable M9640» : Magma (Fin 5) where
  op := finOpTable "[[3,3,4,2,0],[4,1,4,4,0],[0,2,2,0,3],[1,0,0,3,3],[0,2,4,4,4]]"

@[implicit_reducible]
def «OneVariable M9640^op» : Magma (Fin 5) where
  op := finOpTable "[[3,4,0,1,0],[3,1,2,0,2],[4,4,2,0,4],[2,4,0,3,4],[0,0,3,3,4]]"

@[implicit_reducible]
def «OneVariable M9649» : Magma (Fin 5) where
  op := finOpTable "[[4,4,0,4,3],[2,1,0,4,0],[1,1,2,4,2],[0,3,0,3,0],[1,0,4,0,4]]"

@[implicit_reducible]
def «OneVariable M9649^op» : Magma (Fin 5) where
  op := finOpTable "[[4,2,1,0,1],[4,1,1,3,0],[0,0,2,0,4],[4,4,4,3,0],[3,0,2,0,4]]"

@[implicit_reducible]
def «OneVariable M9651» : Magma (Fin 5) where
  op := finOpTable "[[1,2,2,0,1],[4,1,0,1,0],[0,0,2,2,0],[0,2,3,3,4],[3,0,4,3,4]]"

@[implicit_reducible]
def «OneVariable M9651^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,0,0,3],[2,1,0,2,0],[2,0,2,3,4],[0,1,2,3,3],[1,0,0,4,4]]"

@[implicit_reducible]
def «OneVariable M9652» : Magma (Fin 5) where
  op := finOpTable "[[1,3,1,1,0],[2,1,0,0,4],[4,0,2,1,4],[0,0,0,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M9652^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,0,0],[3,1,0,0,1],[1,0,2,0,2],[1,0,1,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M9663» : Magma (Fin 9) where
  op := finOpTable "[[0,5,2,5,4,4,5,6,2],[1,1,7,3,3,1,8,5,8],[8,7,8,7,2,8,6,1,0],[3,1,7,3,0,4,8,7,4],[4,5,2,4,4,1,6,6,8],[4,4,4,4,4,5,6,7,2],[7,8,2,8,7,6,7,4,3],[6,2,3,2,6,7,0,2,8],[2,6,5,6,8,2,1,7,6]]"

@[implicit_reducible]
def «OneVariable M9663^op» : Magma (Fin 9) where
  op := finOpTable "[[0,1,8,3,4,4,7,6,2],[5,1,7,1,5,4,8,2,6],[2,7,8,7,2,4,2,3,5],[5,3,7,3,4,4,8,2,6],[4,3,2,0,4,4,7,6,8],[4,1,8,4,1,5,6,7,2],[5,8,6,8,6,6,7,0,1],[6,5,1,7,6,7,4,2,7],[2,8,0,4,8,2,3,8,6]]"

@[implicit_reducible]
def «OneVariable M9756» : Magma (Fin 8) where
  op := finOpTable "[[1,2,1,3,4,5,0,0],[0,6,1,1,4,5,7,6],[0,0,2,6,2,5,6,7],[3,1,0,4,5,4,6,7],[7,4,2,3,0,5,6,0],[4,1,3,3,3,5,1,5],[0,1,3,2,6,6,3,1],[4,1,7,7,4,2,1,7]]"

@[implicit_reducible]
def «OneVariable M9756^op» : Magma (Fin 8) where
  op := finOpTable "[[1,0,0,3,7,4,0,4],[2,6,0,1,4,1,1,1],[1,1,2,0,2,3,3,7],[3,1,6,4,3,3,2,7],[4,4,2,5,0,3,6,4],[5,5,5,4,5,5,6,2],[0,7,6,6,6,1,3,1],[0,6,7,7,0,5,1,7]]"

@[implicit_reducible]
def «OneVariable M9775» : Magma (Fin 8) where
  op := finOpTable "[[2,0,3,2,7,0,6,7],[0,5,7,5,4,3,1,5],[3,7,1,7,4,2,2,1],[0,1,0,3,6,1,6,7],[7,2,4,0,0,5,3,0],[0,3,2,3,5,6,7,6],[6,1,2,4,3,7,4,2],[4,2,2,7,4,5,5,7]]"

@[implicit_reducible]
def «OneVariable M9775^op» : Magma (Fin 8) where
  op := finOpTable "[[2,0,3,0,7,0,6,4],[0,5,7,1,2,3,1,2],[3,7,1,0,4,2,2,2],[2,5,7,3,0,3,4,7],[7,4,4,6,0,5,3,4],[0,3,2,1,5,6,7,5],[6,1,2,6,3,7,4,5],[7,5,1,7,0,6,2,7]]"

@[implicit_reducible]
def «OneVariable M9945» : Magma (Fin 8) where
  op := finOpTable "[[3,1,2,5,7,3,0,7],[1,7,7,3,4,5,5,2],[4,1,4,3,0,2,6,6],[0,6,3,6,4,0,1,7],[2,4,2,5,5,3,6,7],[0,6,2,4,4,1,1,5],[0,3,7,3,6,5,2,2],[4,1,1,7,0,5,6,0]]"

@[implicit_reducible]
def «OneVariable M9945^op» : Magma (Fin 8) where
  op := finOpTable "[[3,1,4,0,2,0,0,4],[1,7,1,6,4,6,3,1],[2,7,4,3,2,2,7,1],[5,3,3,6,5,4,3,7],[7,4,0,4,5,4,6,0],[3,5,2,0,3,1,5,5],[0,5,6,1,6,1,2,6],[7,2,6,7,7,5,2,0]]"

@[implicit_reducible]
def «OneVariable M10000» : Magma (Fin 6) where
  op := finOpTable "[[0,5,5,3,3,5],[5,3,2,4,3,1],[1,4,2,3,5,3],[2,3,5,5,1,2],[4,1,5,1,4,3],[1,0,3,5,3,1]]"

@[implicit_reducible]
def «OneVariable M10000^op» : Magma (Fin 6) where
  op := finOpTable "[[0,5,1,2,4,1],[5,3,4,3,1,0],[5,2,2,5,5,3],[3,4,3,5,1,5],[3,3,5,1,4,3],[5,1,3,2,3,1]]"

@[implicit_reducible]
def «OneVariable M10003» : Magma (Fin 6) where
  op := finOpTable "[[0,1,4,5,1,5],[4,4,3,3,0,1],[0,3,2,3,4,4],[5,2,1,1,3,5],[1,1,5,4,5,2],[3,5,4,0,4,3]]"

@[implicit_reducible]
def «OneVariable M10003^op» : Magma (Fin 6) where
  op := finOpTable "[[0,4,0,5,1,3],[1,4,3,2,1,5],[4,3,2,1,5,4],[5,3,3,1,4,0],[1,0,4,3,5,4],[5,1,4,5,2,3]]"

@[implicit_reducible]
def «OneVariable M10012» : Magma (Fin 8) where
  op := finOpTable "[[1,2,1,6,4,0,6,7],[0,5,0,5,1,3,6,7],[0,0,2,5,5,5,7,7],[6,1,0,3,4,1,6,4],[7,1,5,7,7,5,4,3],[0,1,4,1,2,4,6,5],[3,6,7,0,4,6,0,7],[7,7,6,4,4,5,2,6]]"

@[implicit_reducible]
def «OneVariable M10012^op» : Magma (Fin 8) where
  op := finOpTable "[[1,0,0,6,7,0,3,7],[2,5,0,1,1,1,6,7],[1,0,2,0,5,4,7,6],[6,5,5,3,7,1,0,4],[4,1,5,4,7,2,4,4],[0,3,5,1,5,4,6,5],[6,6,7,6,4,6,0,2],[7,7,7,4,3,5,7,6]]"

@[implicit_reducible]
def «OneVariable M10087» : Magma (Fin 8) where
  op := finOpTable "[[1,3,1,1,7,5,0,4],[2,6,0,0,6,1,4,7],[0,0,2,6,1,5,6,5],[0,3,3,3,0,6,6,0],[7,1,4,0,4,5,1,7],[5,1,7,6,5,7,3,2],[0,4,4,5,1,3,5,6],[4,7,5,0,0,2,6,0]]"

@[implicit_reducible]
def «OneVariable M10087^op» : Magma (Fin 8) where
  op := finOpTable "[[1,2,0,0,7,5,0,4],[3,6,0,3,1,1,4,7],[1,0,2,3,4,7,4,5],[1,0,6,3,0,6,5,0],[7,6,1,0,4,5,1,0],[5,1,5,6,5,7,3,2],[0,4,6,6,1,3,5,6],[4,7,5,0,7,2,6,0]]"

@[implicit_reducible]
def «OneVariable M10145» : Magma (Fin 8) where
  op := finOpTable "[[5,0,4,5,2,3,5,2],[1,2,6,2,5,4,2,5],[7,3,0,1,0,2,1,0],[0,2,1,3,4,0,6,5],[2,5,0,3,4,1,6,7],[6,7,5,0,1,1,0,1],[5,1,1,3,4,0,6,7],[2,5,2,6,4,5,6,7]]"

@[implicit_reducible]
def «OneVariable M10145^op» : Magma (Fin 8) where
  op := finOpTable "[[5,1,7,0,2,6,5,2],[0,2,3,2,5,7,1,5],[4,6,0,1,0,5,1,2],[5,2,1,3,3,0,3,6],[2,5,0,4,4,1,4,4],[3,4,2,0,1,1,0,5],[5,2,1,6,6,0,6,6],[2,5,0,5,7,1,7,7]]"

@[implicit_reducible]
def «OneVariable M10530» : Magma (Fin 9) where
  op := finOpTable "[[0,1,7,3,0,4,6,7,3],[1,3,3,2,6,6,5,3,1],[4,1,2,1,5,5,8,2,8],[8,7,1,8,3,8,3,1,0],[4,6,5,3,4,4,6,4,8],[4,6,5,4,5,5,0,7,3],[6,4,8,6,1,1,1,8,7],[7,0,2,1,5,1,8,7,4],[3,8,6,5,8,3,2,6,6]]"

@[implicit_reducible]
def «OneVariable M10530^op» : Magma (Fin 9) where
  op := finOpTable "[[0,1,4,8,4,4,6,7,3],[1,3,1,7,6,6,4,0,8],[7,3,2,1,5,5,8,2,6],[3,2,1,8,3,4,6,1,5],[0,6,5,3,4,5,1,5,8],[4,6,5,8,4,5,1,1,3],[6,5,8,3,6,0,1,8,2],[7,3,2,1,4,7,8,7,6],[3,1,8,0,8,3,7,4,6]]"

@[implicit_reducible]
def «OneVariable M10543» : Magma (Fin 5) where
  op := finOpTable "[[1,3,4,1,0],[2,0,0,4,1],[1,1,2,4,2],[0,0,3,3,3],[3,3,3,4,4]]"

@[implicit_reducible]
def «OneVariable M10543^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,0,3],[3,0,1,0,3],[4,0,2,3,3],[1,4,4,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M10549» : Magma (Fin 5) where
  op := finOpTable "[[1,3,4,1,0],[2,0,0,4,1],[1,1,2,2,2],[0,0,3,3,3],[0,1,4,3,4]]"

@[implicit_reducible]
def «OneVariable M10549^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,0,0],[3,0,1,0,1],[4,0,2,3,4],[1,4,2,3,3],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M10562» : Magma (Fin 5) where
  op := finOpTable "[[1,3,4,3,0],[2,0,2,4,1],[1,1,2,3,4],[0,0,2,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M10562^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,0,0],[3,0,1,0,1],[4,2,2,2,2],[3,4,3,3,3],[0,1,4,4,4]]"

@[implicit_reducible]
def «OneVariable M10593» : Magma (Fin 5) where
  op := finOpTable "[[2,3,4,0,2],[2,1,1,1,4],[1,0,2,3,0],[0,3,2,3,3],[0,1,0,3,4]]"

@[implicit_reducible]
def «OneVariable M10593^op» : Magma (Fin 5) where
  op := finOpTable "[[2,2,1,0,0],[3,1,0,3,1],[4,1,2,2,0],[0,1,3,3,3],[2,4,0,3,4]]"

@[implicit_reducible]
def «OneVariable M10647» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,4,0],[3,1,1,0,1],[0,0,2,0,2],[4,0,3,3,3],[0,0,4,4,4]]"

@[implicit_reducible]
def «OneVariable M10647^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,0,4,0],[2,1,0,0,0],[1,1,2,3,4],[4,0,0,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M10724» : Magma (Fin 5) where
  op := finOpTable "[[3,2,0,4,3],[3,1,3,0,1],[0,1,2,0,4],[1,0,0,3,3],[0,2,2,0,4]]"

@[implicit_reducible]
def «OneVariable M10724^op» : Magma (Fin 5) where
  op := finOpTable "[[3,3,0,1,0],[2,1,1,0,2],[0,3,2,0,2],[4,0,0,3,0],[3,1,4,3,4]]"

@[implicit_reducible]
def «OneVariable M10790» : Magma (Fin 5) where
  op := finOpTable "[[2,3,4,0,2],[2,1,0,4,1],[1,4,2,0,0],[0,0,0,3,1],[0,4,0,4,4]]"

@[implicit_reducible]
def «OneVariable M10790^op» : Magma (Fin 5) where
  op := finOpTable "[[2,2,1,0,0],[3,1,4,0,4],[4,0,2,0,0],[0,4,0,3,4],[2,1,0,1,4]]"

@[implicit_reducible]
def «OneVariable M10826» : Magma (Fin 5) where
  op := finOpTable "[[1,3,4,1,0],[2,1,2,0,4],[4,0,2,3,4],[0,0,2,3,4],[0,4,2,3,4]]"

@[implicit_reducible]
def «OneVariable M10826^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,0,0],[3,1,0,0,4],[4,2,2,2,2],[1,0,3,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M10876» : Magma (Fin 5) where
  op := finOpTable "[[3,4,3,2,0],[3,1,0,0,4],[0,0,2,4,4],[1,0,0,3,3],[0,0,2,4,4]]"

@[implicit_reducible]
def «OneVariable M10876^op» : Magma (Fin 5) where
  op := finOpTable "[[3,3,0,1,0],[4,1,0,0,0],[3,0,2,0,2],[2,0,4,3,4],[0,4,4,3,4]]"

@[implicit_reducible]
def «OneVariable M10909» : Magma (Fin 5) where
  op := finOpTable "[[4,2,0,4,3],[4,1,0,2,0],[0,0,2,4,4],[0,4,2,3,0],[1,0,2,0,4]]"

@[implicit_reducible]
def «OneVariable M10909^op» : Magma (Fin 5) where
  op := finOpTable "[[4,4,0,0,1],[2,1,0,4,0],[0,0,2,2,2],[4,2,4,3,0],[3,0,4,0,4]]"

@[implicit_reducible]
def «OneVariable M10910» : Magma (Fin 5) where
  op := finOpTable "[[2,3,4,0,2],[2,1,0,3,4],[1,0,2,3,0],[3,1,0,3,0],[0,1,0,3,4]]"

@[implicit_reducible]
def «OneVariable M10910^op» : Magma (Fin 5) where
  op := finOpTable "[[2,2,1,3,0],[3,1,0,1,1],[4,0,2,0,0],[0,3,3,3,3],[2,4,0,0,4]]"

@[implicit_reducible]
def «OneVariable M10924» : Magma (Fin 9) where
  op := finOpTable "[[1,2,1,0,3,5,7,6,6],[4,5,0,1,0,7,6,5,3],[0,0,2,3,8,5,5,7,3],[0,1,3,3,2,5,6,2,1],[1,0,5,3,4,6,5,7,2],[0,8,6,5,3,6,2,1,1],[8,1,5,6,5,4,0,3,0],[6,1,7,2,4,1,0,7,2],[6,5,7,1,2,1,6,4,8]]"

@[implicit_reducible]
def «OneVariable M10924^op» : Magma (Fin 9) where
  op := finOpTable "[[1,4,0,0,1,0,8,6,6],[2,5,0,1,0,8,1,1,5],[1,0,2,3,5,6,5,7,7],[0,1,3,3,3,5,6,2,1],[3,0,8,2,4,3,5,4,2],[5,7,5,5,6,6,4,1,1],[7,6,5,6,5,2,0,0,6],[6,5,7,2,7,1,3,7,4],[6,3,3,1,2,1,0,2,8]]"

@[implicit_reducible]
def «OneVariable M10929» : Magma (Fin 5) where
  op := finOpTable "[[4,3,3,0,2],[4,1,1,3,0],[0,2,2,1,0],[0,1,2,3,0],[1,0,0,3,4]]"

@[implicit_reducible]
def «OneVariable M10929^op» : Magma (Fin 5) where
  op := finOpTable "[[4,4,0,0,1],[3,1,2,1,0],[3,1,2,2,0],[0,3,1,3,3],[2,0,0,0,4]]"

@[implicit_reducible]
def «OneVariable M10930» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,3,0],[2,1,0,3,4],[1,0,2,0,4],[0,1,0,3,4],[0,2,2,3,4]]"

@[implicit_reducible]
def «OneVariable M10930^op» : Magma (Fin 5) where
  op := finOpTable "[[2,2,1,0,0],[4,1,0,1,2],[3,0,2,0,2],[3,3,0,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M11104» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,0,0],[2,1,0,0,0],[4,0,2,0,0],[4,0,0,3,0],[0,0,0,0,4]]"

@[implicit_reducible]
def «OneVariable M11104^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,4,0],[4,1,0,0,0],[3,0,2,0,0],[0,0,0,3,0],[0,0,0,0,4]]"

@[implicit_reducible]
def «OneVariable M11111» : Magma (Fin 6) where
  op := finOpTable "[[1,4,5,0,1,0],[2,1,0,1,0,1],[3,0,2,0,0,2],[3,0,0,3,3,3],[0,0,4,0,4,4],[0,5,5,0,0,5]]"

@[implicit_reducible]
def «OneVariable M11111^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,3,0,0],[4,1,0,0,0,5],[5,0,2,0,4,5],[0,1,0,3,0,0],[1,0,0,3,4,0],[0,1,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M11124» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,4,0],[3,1,0,0,4],[0,2,2,3,4],[4,0,2,3,4],[0,4,2,3,4]]"

@[implicit_reducible]
def «OneVariable M11124^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,0,4,0],[2,1,2,0,4],[1,0,2,2,2],[4,0,3,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M11138» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,2,0],[4,1,0,1,4],[1,0,2,0,3],[0,0,0,3,4],[0,4,0,4,4]]"

@[implicit_reducible]
def «OneVariable M11138^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,1,0,0],[4,1,0,0,4],[3,0,2,0,0],[2,1,0,3,4],[0,4,3,4,4]]"

@[implicit_reducible]
def «OneVariable M11139» : Magma (Fin 6) where
  op := finOpTable "[[2,3,4,0,2,0],[5,1,0,1,1,4],[1,0,2,2,0,0],[3,1,0,3,0,3],[0,1,0,4,4,1],[0,0,5,3,1,5]]"

@[implicit_reducible]
def «OneVariable M11139^op» : Magma (Fin 6) where
  op := finOpTable "[[2,5,1,3,0,0],[3,1,0,1,1,0],[4,0,2,0,0,5],[0,1,2,3,4,3],[2,1,0,0,4,1],[0,4,0,3,1,5]]"

@[implicit_reducible]
def «OneVariable M11144» : Magma (Fin 9) where
  op := finOpTable "[[3,4,5,7,0,8,6,3,5],[4,1,0,0,4,6,2,1,7],[5,0,2,3,8,5,6,2,8],[1,0,3,6,6,5,4,0,2],[0,4,1,3,4,5,3,8,4],[2,6,0,3,5,0,1,6,4],[0,2,6,8,3,7,5,5,3],[0,1,7,0,8,6,6,7,1],[5,0,2,2,4,4,3,1,8]]"

@[implicit_reducible]
def «OneVariable M11144^op» : Magma (Fin 9) where
  op := finOpTable "[[3,4,5,1,0,2,0,0,5],[4,1,0,0,4,6,2,1,0],[5,0,2,3,1,0,6,7,2],[7,0,3,6,3,3,8,0,2],[0,4,8,6,4,5,3,8,4],[8,6,5,5,5,0,7,6,4],[6,2,6,4,3,1,5,6,3],[3,1,2,0,8,6,5,7,1],[5,7,8,2,4,4,3,1,8]]"

@[implicit_reducible]
def «OneVariable M11147» : Magma (Fin 10) where
  op := finOpTable "[[1,9,6,0,4,7,0,5,5,1],[2,6,0,1,9,5,8,3,6,0],[3,0,2,6,4,4,4,9,9,9],[3,1,6,4,7,3,2,4,5,6],[4,2,5,8,5,2,6,3,3,0],[8,5,4,3,9,0,0,1,0,4],[0,7,4,9,6,9,3,1,1,3],[5,3,9,3,3,1,1,7,7,2],[5,1,9,0,3,5,1,7,8,9],[0,0,9,6,0,4,6,2,9,9]]"

@[implicit_reducible]
def «OneVariable M11147^op» : Magma (Fin 10) where
  op := finOpTable "[[1,2,3,3,4,8,0,5,5,0],[9,6,0,1,2,5,7,3,1,0],[6,0,2,6,5,4,4,9,9,9],[0,1,6,4,8,3,9,3,0,6],[4,9,4,7,5,9,6,3,3,0],[7,5,4,3,2,0,9,1,5,4],[0,8,4,2,6,0,3,1,1,6],[5,3,9,4,3,1,1,7,7,2],[5,6,9,5,3,0,1,7,8,9],[1,0,9,6,0,4,3,2,9,9]]"

@[implicit_reducible]
def «OneVariable M11353» : Magma (Fin 8) where
  op := finOpTable "[[3,6,6,1,5,4,0,7],[0,1,6,0,7,7,6,7],[0,6,7,3,2,4,1,5],[1,0,3,6,4,7,5,3],[5,7,2,4,0,3,3,1],[4,5,2,3,4,5,3,2],[0,7,1,5,4,3,2,6],[7,0,5,3,1,2,6,4]]"

@[implicit_reducible]
def «OneVariable M11353^op» : Magma (Fin 8) where
  op := finOpTable "[[3,0,0,1,5,4,0,7],[6,1,6,0,7,5,7,0],[6,6,7,3,2,2,1,5],[1,0,3,6,4,3,5,3],[5,7,2,4,0,4,4,1],[4,7,4,7,3,5,3,2],[0,6,1,5,3,3,2,6],[7,7,5,3,1,2,6,4]]"

@[implicit_reducible]
def «OneVariable M11429» : Magma (Fin 9) where
  op := finOpTable "[[0,1,2,0,7,2,8,7,6],[0,1,5,2,1,2,6,1,6],[5,3,5,2,8,0,2,8,7],[3,8,2,3,2,6,5,6,8],[7,4,8,4,4,5,6,4,8],[2,2,1,4,5,6,7,6,5],[4,8,6,5,6,3,8,5,1],[4,1,8,6,7,5,5,7,2],[6,6,4,8,2,8,0,3,2]]"

@[implicit_reducible]
def «OneVariable M11429^op» : Magma (Fin 9) where
  op := finOpTable "[[0,0,5,3,7,2,4,4,6],[1,1,3,8,4,2,8,1,6],[2,5,5,2,8,1,6,8,4],[0,2,2,3,4,4,5,6,8],[7,1,8,2,4,5,6,7,2],[2,2,0,6,5,6,3,5,8],[8,6,2,5,6,7,8,5,0],[7,1,8,6,4,6,5,7,3],[6,6,7,8,8,5,1,2,2]]"

@[implicit_reducible]
def «OneVariable M11577» : Magma (Fin 10) where
  op := finOpTable "[[1,2,1,0,4,9,6,3,9,8],[7,3,0,5,1,3,0,0,4,9],[0,2,2,6,3,5,6,9,9,9],[0,8,6,4,7,1,3,4,1,9],[4,1,3,2,6,0,8,3,6,4],[9,1,5,9,0,5,4,9,9,9],[6,0,9,3,5,4,9,0,4,2],[3,0,8,3,0,9,0,7,2,6],[9,4,9,1,4,9,6,8,8,3],[5,9,6,9,4,0,7,6,1,0]]"

@[implicit_reducible]
def «OneVariable M11577^op» : Magma (Fin 10) where
  op := finOpTable "[[1,7,0,0,4,9,6,3,9,5],[2,3,2,8,1,1,0,0,4,9],[1,0,2,6,3,5,9,8,9,6],[0,5,6,4,2,9,3,3,1,9],[4,1,3,7,6,0,5,0,4,4],[9,3,5,1,0,5,4,9,9,0],[6,0,6,3,8,4,9,0,6,7],[3,0,9,4,3,9,0,7,8,6],[9,4,9,1,6,9,4,2,8,1],[8,9,9,9,4,9,2,6,3,0]]"

@[implicit_reducible]
def «OneVariable M11590» : Magma (Fin 10) where
  op := finOpTable "[[1,8,4,9,0,5,9,2,1,3],[2,4,0,5,6,7,4,1,0,9],[4,3,5,1,9,6,5,7,3,2],[7,5,8,2,4,3,7,0,2,1],[0,5,9,4,7,1,1,8,7,3],[5,7,4,3,2,9,2,0,9,8],[9,1,2,7,1,2,6,7,2,9],[2,1,7,6,9,0,3,3,4,4],[0,0,3,3,4,5,2,4,8,5],[6,9,2,1,3,7,0,5,5,0]]"

@[implicit_reducible]
def «OneVariable M11590^op» : Magma (Fin 10) where
  op := finOpTable "[[1,2,4,7,0,5,9,2,0,6],[8,4,3,5,5,7,1,1,0,9],[4,0,5,8,9,4,2,7,3,2],[9,5,1,2,4,3,7,6,3,1],[0,6,9,4,7,2,1,9,4,3],[5,7,6,3,1,9,2,0,5,7],[9,4,5,7,1,2,6,3,2,0],[2,1,7,0,8,0,7,3,4,5],[1,0,3,2,7,9,2,4,8,5],[3,9,2,1,3,8,9,4,5,0]]"

@[implicit_reducible]
def «OneVariable M11602» : Magma (Fin 9) where
  op := finOpTable "[[7,2,0,4,3,7,3,5,0],[2,1,6,8,5,5,7,0,8],[0,2,2,3,1,2,8,7,7],[6,8,3,0,2,8,0,3,5],[3,5,2,2,4,5,7,6,7],[0,3,5,8,7,5,7,0,6],[3,4,7,3,7,8,6,7,8],[1,0,8,7,6,0,7,8,2],[8,3,7,1,7,6,8,4,3]]"

@[implicit_reducible]
def «OneVariable M11602^op» : Magma (Fin 9) where
  op := finOpTable "[[7,2,0,6,3,0,3,1,8],[2,1,2,8,5,3,4,0,3],[0,6,2,3,2,5,7,8,7],[4,8,3,0,2,8,3,7,1],[3,5,1,2,4,7,7,6,7],[7,5,2,8,5,5,8,0,6],[3,7,8,0,7,7,6,7,8],[5,0,7,3,6,0,7,8,4],[0,8,7,5,7,6,8,2,3]]"

@[implicit_reducible]
def «OneVariable M11610» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,2],[1,1,2,2],[0,3,2,3],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M11610^op» : Magma (Fin 4) where
  op := finOpTable "[[1,1,0,0],[3,1,3,0],[0,2,2,0],[2,2,3,3]]"

@[implicit_reducible]
def «OneVariable M11644» : Magma (Fin 5) where
  op := finOpTable "[[1,4,1,0,3],[2,0,3,1,0],[1,1,2,3,4],[2,2,2,3,0],[0,0,2,0,4]]"

@[implicit_reducible]
def «OneVariable M11644^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,2,0],[4,0,1,2,0],[1,3,2,2,2],[0,1,3,3,0],[3,0,4,0,4]]"

@[implicit_reducible]
def «OneVariable M11645» : Magma (Fin 5) where
  op := finOpTable "[[2,4,1,2,0],[0,1,0,1,4],[3,0,2,2,0],[4,0,0,3,3],[0,2,4,3,4]]"

@[implicit_reducible]
def «OneVariable M11645^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,3,4,0],[4,1,0,0,2],[1,0,2,0,4],[2,1,2,3,3],[0,4,0,3,4]]"

@[implicit_reducible]
def «OneVariable M11650» : Magma (Fin 4) where
  op := finOpTable "[[2,3,1,0],[0,1,0,3],[0,0,2,3],[0,2,3,3]]"

@[implicit_reducible]
def «OneVariable M11650^op» : Magma (Fin 4) where
  op := finOpTable "[[2,0,0,0],[3,1,0,2],[1,0,2,3],[0,3,3,3]]"

@[implicit_reducible]
def «OneVariable M11651» : Magma (Fin 4) where
  op := finOpTable "[[2,3,1,0],[0,1,0,2],[0,2,2,2],[0,1,3,3]]"

@[implicit_reducible]
def «OneVariable M11651^op» : Magma (Fin 4) where
  op := finOpTable "[[2,0,0,0],[3,1,2,1],[1,0,2,3],[0,2,2,3]]"

@[implicit_reducible]
def «OneVariable M11653» : Magma (Fin 5) where
  op := finOpTable "[[1,4,1,0,3],[2,0,3,1,0],[1,1,2,2,4],[0,1,2,3,3],[0,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M11653^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,0,0],[4,0,1,1,0],[1,3,2,2,2],[0,1,2,3,3],[3,0,4,3,4]]"

@[implicit_reducible]
def «OneVariable M11675» : Magma (Fin 5) where
  op := finOpTable "[[4,3,4,0,1],[0,1,4,3,0],[4,1,2,3,0],[0,2,4,3,0],[2,2,0,0,4]]"

@[implicit_reducible]
def «OneVariable M11675^op» : Magma (Fin 5) where
  op := finOpTable "[[4,0,4,0,2],[3,1,1,2,2],[4,4,2,4,0],[0,3,3,3,0],[1,0,0,0,4]]"

@[implicit_reducible]
def «OneVariable M11678» : Magma (Fin 5) where
  op := finOpTable "[[2,4,1,2,0],[0,1,0,0,4],[3,2,2,0,1],[4,3,0,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M11678^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,3,4,0],[4,1,2,3,1],[1,0,2,0,2],[2,0,0,3,3],[0,4,1,4,4]]"

@[implicit_reducible]
def «OneVariable M11738» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[3,1,0,0],[0,0,2,3],[1,0,2,3]]"

@[implicit_reducible]
def «OneVariable M11738^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,1],[2,1,0,0],[3,0,2,2],[0,0,3,3]]"

@[implicit_reducible]
def «OneVariable M11750» : Magma (Fin 5) where
  op := finOpTable "[[2,3,1,0,3],[0,1,0,3,4],[4,4,2,3,0],[0,1,2,3,4],[2,4,0,3,4]]"

@[implicit_reducible]
def «OneVariable M11750^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,4,0,2],[3,1,4,1,4],[1,0,2,2,0],[0,3,3,3,3],[3,4,0,4,4]]"

@[implicit_reducible]
def «OneVariable M11778» : Magma (Fin 4) where
  op := finOpTable "[[2,3,1,0],[0,1,1,3],[0,0,2,3],[0,3,1,3]]"

@[implicit_reducible]
def «OneVariable M11778^op» : Magma (Fin 4) where
  op := finOpTable "[[2,0,0,0],[3,1,0,3],[1,1,2,1],[0,3,3,3]]"

@[implicit_reducible]
def «OneVariable M11782» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[1,1,0,1],[0,3,2,0],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M11782^op» : Magma (Fin 4) where
  op := finOpTable "[[1,1,0,0],[2,1,3,0],[3,0,2,0],[0,1,0,3]]"

@[implicit_reducible]
def «OneVariable M11807» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[0,1,0,3],[0,0,2,2],[3,1,3,3]]"

@[implicit_reducible]
def «OneVariable M11807^op» : Magma (Fin 4) where
  op := finOpTable "[[1,0,0,3],[2,1,0,1],[3,0,2,3],[0,3,2,3]]"

@[implicit_reducible]
def «OneVariable M11838» : Magma (Fin 5) where
  op := finOpTable "[[2,4,1,2,0],[0,1,0,0,4],[3,0,2,4,4],[2,2,0,3,0],[0,4,2,3,4]]"

@[implicit_reducible]
def «OneVariable M11838^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,3,2,0],[4,1,0,2,4],[1,0,2,0,2],[2,0,4,3,3],[0,4,4,0,4]]"

@[implicit_reducible]
def «OneVariable M11848» : Magma (Fin 8) where
  op := finOpTable "[[1,5,2,7,0,4,6,3],[2,4,0,6,3,0,1,7],[0,0,2,3,4,3,6,6],[7,1,3,3,1,2,6,7],[0,3,0,1,6,7,5,4],[0,0,5,2,4,5,4,7],[6,1,0,3,5,4,7,2],[3,7,6,1,4,5,2,0]]"

@[implicit_reducible]
def «OneVariable M11848^op» : Magma (Fin 8) where
  op := finOpTable "[[1,2,0,7,0,0,6,3],[5,4,0,1,3,0,1,7],[2,0,2,3,0,5,0,6],[7,6,3,3,1,2,3,1],[0,3,4,1,6,4,5,4],[4,0,3,2,7,5,4,5],[6,1,6,6,5,4,7,2],[3,7,6,7,4,7,2,0]]"

@[implicit_reducible]
def «OneVariable M11887» : Magma (Fin 5) where
  op := finOpTable "[[2,4,1,2,0],[0,1,2,3,4],[3,0,2,0,4],[2,2,0,3,0],[0,0,2,4,4]]"

@[implicit_reducible]
def «OneVariable M11887^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,3,2,0],[4,1,0,2,0],[1,2,2,0,2],[2,3,0,3,4],[0,4,4,0,4]]"

@[implicit_reducible]
def «OneVariable M11909» : Magma (Fin 5) where
  op := finOpTable "[[2,4,1,2,0],[0,1,0,4,4],[3,0,2,0,1],[2,4,0,3,1],[0,2,1,4,4]]"

@[implicit_reducible]
def «OneVariable M11909^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,3,2,0],[4,1,0,4,2],[1,0,2,0,1],[2,4,0,3,4],[0,4,1,1,4]]"

@[implicit_reducible]
def «OneVariable M11920» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,1],[4,1,0,0,0],[0,0,2,3,4],[3,0,2,3,3],[1,0,4,3,4]]"

@[implicit_reducible]
def «OneVariable M11920^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,0,3,1],[2,1,0,0,0],[3,0,2,2,4],[0,0,3,3,3],[1,0,4,3,4]]"

@[implicit_reducible]
def «OneVariable M11934» : Magma (Fin 5) where
  op := finOpTable "[[2,4,1,4,0],[0,1,0,4,4],[3,0,2,0,4],[4,1,0,3,4],[0,1,0,3,4]]"

@[implicit_reducible]
def «OneVariable M11934^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,3,4,0],[4,1,0,1,1],[1,0,2,0,0],[4,4,0,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M11943» : Magma (Fin 5) where
  op := finOpTable "[[1,3,1,4,0],[2,1,0,0,1],[3,0,2,3,4],[0,0,2,3,3],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M11943^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,0],[3,1,0,0,1],[1,0,2,2,2],[4,0,3,3,3],[0,1,4,3,4]]"

@[implicit_reducible]
def «OneVariable M11947» : Magma (Fin 9) where
  op := finOpTable "[[0,1,2,6,4,1,3,8,8],[5,1,3,7,6,0,8,7,6],[2,2,2,3,2,4,6,8,7],[6,7,3,6,2,7,4,5,8],[7,0,2,3,4,1,3,7,8],[3,5,7,7,4,5,6,3,6],[3,8,6,0,3,2,8,7,5],[8,4,8,1,7,3,6,3,2],[4,6,7,3,8,6,1,0,7]]"

@[implicit_reducible]
def «OneVariable M11947^op» : Magma (Fin 9) where
  op := finOpTable "[[0,5,2,6,7,3,3,8,4],[1,1,2,7,0,5,8,4,6],[2,3,2,3,2,7,6,8,7],[6,7,3,6,3,7,0,1,3],[4,6,2,2,4,4,3,7,8],[1,0,4,7,1,5,2,3,6],[3,8,6,4,3,6,8,6,1],[8,7,8,5,7,3,7,3,0],[8,6,7,8,8,6,5,2,7]]"

@[implicit_reducible]
def «OneVariable M11950» : Magma (Fin 5) where
  op := finOpTable "[[2,4,1,1,0],[0,1,0,3,4],[3,0,2,0,4],[2,1,0,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M11950^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,3,2,0],[4,1,0,1,1],[1,0,2,0,2],[1,3,0,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M12086» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,5,0],[4,1,0,3,0,4],[0,0,2,0,0,0],[4,0,0,3,0,0],[5,0,0,0,4,0],[0,0,0,0,0,5]]"

@[implicit_reducible]
def «OneVariable M12086^op» : Magma (Fin 6) where
  op := finOpTable "[[1,4,0,4,5,0],[2,1,0,0,0,0],[3,0,2,0,0,0],[0,3,0,3,0,0],[5,0,0,0,4,0],[0,4,0,0,0,5]]"

@[implicit_reducible]
def «OneVariable M12153» : Magma (Fin 6) where
  op := finOpTable "[[1,4,1,0,5,0],[2,1,0,1,0,1],[3,0,2,2,2,2],[3,3,3,3,3,0],[0,0,4,0,4,0],[0,0,0,0,0,5]]"

@[implicit_reducible]
def «OneVariable M12153^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,3,0,0],[4,1,0,3,0,0],[1,0,2,3,4,0],[0,1,2,3,0,0],[5,0,2,3,4,0],[0,1,2,0,0,5]]"

@[implicit_reducible]
def «OneVariable M12168» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,1,0],[3,1,0,0,4],[0,2,2,3,4],[4,0,2,3,4],[0,4,2,3,4]]"

@[implicit_reducible]
def «OneVariable M12168^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,0,4,0],[2,1,2,0,4],[4,0,2,2,2],[1,0,3,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M12190» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,1,0],[4,1,0,3,0,1],[0,0,2,2,4,5],[3,0,2,3,4,5],[5,0,2,3,4,4],[0,0,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M12190^op» : Magma (Fin 6) where
  op := finOpTable "[[1,4,0,3,5,0],[2,1,0,0,0,0],[3,0,2,2,2,2],[0,3,2,3,3,3],[1,0,4,4,4,4],[0,1,5,5,4,5]]"

@[implicit_reducible]
def «OneVariable M12195» : Magma (Fin 9) where
  op := finOpTable "[[0,1,3,7,3,3,1,7,1],[6,8,4,3,2,8,1,2,0],[3,7,1,0,1,3,2,6,8],[2,1,5,2,8,7,8,3,6],[5,2,6,8,4,0,6,5,8],[7,6,3,3,5,5,4,7,1],[0,1,2,8,6,7,6,4,7],[6,2,2,3,8,6,5,7,8],[1,5,2,4,7,1,3,8,3]]"

@[implicit_reducible]
def «OneVariable M12195^op» : Magma (Fin 9) where
  op := finOpTable "[[0,6,3,2,5,7,0,6,1],[1,8,7,1,2,6,1,2,5],[3,4,1,5,6,3,2,2,2],[7,3,0,2,8,3,8,3,4],[3,2,1,8,4,5,6,8,7],[3,8,3,7,0,5,7,6,1],[1,1,2,8,6,4,6,5,3],[7,2,6,3,5,7,4,7,8],[1,0,8,6,8,1,7,8,3]]"

@[implicit_reducible]
def «OneVariable M12198» : Magma (Fin 5) where
  op := finOpTable "[[1,3,3,4,0],[2,1,0,0,4],[4,0,2,3,4],[0,0,2,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M12198^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,0,0],[3,1,0,0,1],[3,0,2,2,2],[4,0,3,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M12202» : Magma (Fin 5) where
  op := finOpTable "[[3,4,3,1,0],[0,1,4,0,4],[4,2,2,0,4],[2,0,0,3,4],[0,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M12202^op» : Magma (Fin 5) where
  op := finOpTable "[[3,0,4,2,0],[4,1,2,0,0],[3,4,2,0,2],[1,0,0,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M12254» : Magma (Fin 8) where
  op := finOpTable "[[1,2,7,3,3,5,6,0],[0,7,4,1,4,3,6,5],[0,0,5,3,4,7,2,6],[2,1,3,4,0,5,5,7],[6,5,1,3,2,4,6,7],[5,1,2,0,4,6,3,1],[4,6,2,7,1,5,0,7],[0,1,2,6,7,2,4,3]]"

@[implicit_reducible]
def «OneVariable M12254^op» : Magma (Fin 8) where
  op := finOpTable "[[1,0,0,2,6,5,4,0],[2,7,0,1,5,1,6,1],[7,4,5,3,1,2,2,2],[3,1,3,4,3,0,7,6],[3,4,4,0,2,4,1,7],[5,3,7,5,4,6,5,2],[6,6,2,5,6,3,0,4],[0,5,6,7,7,1,7,3]]"

@[implicit_reducible]
def «OneVariable M12344» : Magma (Fin 8) where
  op := finOpTable "[[3,1,2,4,6,5,0,1],[7,0,2,1,4,2,6,3],[2,5,1,3,4,0,4,7],[0,1,5,6,0,3,2,7],[0,4,6,7,2,5,1,7],[4,6,2,3,5,7,6,0],[0,7,3,3,4,1,5,6],[5,1,7,2,3,5,6,4]]"

@[implicit_reducible]
def «OneVariable M12344^op» : Magma (Fin 8) where
  op := finOpTable "[[3,7,2,0,0,4,0,5],[1,0,5,1,4,6,7,1],[2,2,1,5,6,2,3,7],[4,1,3,6,7,3,3,2],[6,4,4,0,2,5,4,3],[5,2,0,3,5,7,1,5],[0,6,4,2,1,6,5,6],[1,3,7,7,7,0,6,4]]"

@[implicit_reducible]
def «OneVariable M12384» : Magma (Fin 8) where
  op := finOpTable "[[6,1,3,3,4,0,7,5],[1,1,1,2,5,5,7,1],[3,1,2,3,4,6,6,7],[2,3,6,0,4,5,3,4],[4,5,4,7,3,5,6,0],[0,7,6,5,1,4,6,5],[0,4,4,3,6,2,5,0],[0,1,7,4,4,5,0,7]]"

@[implicit_reducible]
def «OneVariable M12384^op» : Magma (Fin 8) where
  op := finOpTable "[[6,1,3,2,4,0,0,0],[1,1,1,3,5,7,4,1],[3,1,2,6,4,6,4,7],[3,2,3,0,7,5,3,4],[4,5,4,4,3,1,6,4],[0,5,6,5,5,4,2,5],[7,7,6,3,6,6,5,0],[5,1,7,4,0,5,0,7]]"

@[implicit_reducible]
def «OneVariable M12386» : Magma (Fin 8) where
  op := finOpTable "[[1,2,3,0,4,0,7,7],[0,5,0,4,1,3,6,7],[0,0,2,0,5,5,6,0],[4,1,0,3,4,1,6,4],[4,1,5,0,7,5,6,3],[0,1,7,1,2,4,1,5],[7,6,3,3,6,4,6,7],[6,7,0,4,4,5,1,0]]"

@[implicit_reducible]
def «OneVariable M12386^op» : Magma (Fin 8) where
  op := finOpTable "[[1,0,0,4,4,0,7,6],[2,5,0,1,1,1,6,7],[3,0,2,0,5,7,3,0],[0,4,0,3,0,1,3,4],[4,1,5,4,7,2,6,4],[0,3,5,1,5,4,4,5],[7,6,6,6,6,1,6,1],[7,7,0,4,3,5,7,0]]"

@[implicit_reducible]
def «OneVariable M12389» : Magma (Fin 6) where
  op := finOpTable "[[3,5,0,1,2,0],[0,1,2,0,4,4],[4,2,0,2,1,3],[3,0,5,2,3,4],[2,4,2,3,4,4],[0,5,3,3,4,5]]"

@[implicit_reducible]
def «OneVariable M12389^op» : Magma (Fin 6) where
  op := finOpTable "[[3,0,4,3,2,0],[5,1,2,0,4,5],[0,2,0,5,2,3],[1,0,2,2,3,3],[2,4,1,3,4,4],[0,4,3,4,4,5]]"

@[implicit_reducible]
def «OneVariable M12391» : Magma (Fin 7) where
  op := finOpTable "[[1,4,0,5,6,5,0],[0,2,3,6,0,1,1],[2,1,5,1,6,4,2],[5,1,1,3,0,5,2],[0,0,2,0,4,2,6],[3,5,2,6,2,0,5],[0,1,2,2,6,5,6]]"

@[implicit_reducible]
def «OneVariable M12391^op» : Magma (Fin 7) where
  op := finOpTable "[[1,0,2,5,0,3,0],[4,2,1,1,0,5,1],[0,3,5,1,2,2,2],[5,6,1,3,0,6,2],[6,0,6,0,4,2,6],[5,1,4,5,2,0,5],[0,1,2,2,6,5,6]]"

@[implicit_reducible]
def «OneVariable M12466» : Magma (Fin 9) where
  op := finOpTable "[[0,2,1,3,3,4,5,6,7],[2,3,0,7,1,3,2,8,1],[1,6,1,2,5,4,8,4,2],[8,5,3,4,0,1,4,1,3],[3,4,7,6,2,2,3,8,4],[6,3,4,1,2,5,7,7,8],[5,2,2,4,3,6,6,5,1],[7,1,4,1,4,7,5,7,8],[8,1,2,3,4,4,5,8,8]]"

@[implicit_reducible]
def «OneVariable M12466^op» : Magma (Fin 9) where
  op := finOpTable "[[0,2,1,8,3,6,5,7,8],[2,3,6,5,4,3,2,1,1],[1,0,1,3,7,4,2,4,2],[3,7,2,4,6,1,4,1,3],[3,1,5,0,2,2,3,4,4],[4,3,4,1,2,5,6,7,4],[5,2,8,4,3,7,6,5,5],[6,8,4,1,8,7,5,7,8],[7,1,2,3,4,8,1,8,8]]"

@[implicit_reducible]
def «OneVariable M12701» : Magma (Fin 9) where
  op := finOpTable "[[0,0,6,0,8,2,0,8,3],[0,1,4,5,4,5,0,4,5],[5,4,5,6,7,3,2,4,2],[3,5,2,3,4,2,8,8,8],[8,3,1,4,2,4,8,2,0],[2,6,0,2,5,8,5,8,1],[0,1,2,8,8,5,6,8,8],[3,6,4,8,3,6,8,7,5],[4,5,8,8,6,7,3,5,4]]"

@[implicit_reducible]
def «OneVariable M12701^op» : Magma (Fin 9) where
  op := finOpTable "[[0,0,5,3,8,2,0,3,4],[0,1,4,5,3,6,1,6,5],[6,4,5,2,1,0,2,4,8],[0,5,6,3,4,2,8,8,8],[8,4,7,4,2,5,8,3,6],[2,5,3,2,4,8,5,6,7],[0,0,2,8,8,5,6,8,3],[8,4,4,8,2,8,8,7,5],[3,5,2,8,0,1,8,5,4]]"

@[implicit_reducible]
def «OneVariable M12804» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,0,3],[2,1,2,3,0],[1,0,2,3,0],[0,0,2,3,4],[0,0,3,3,4]]"

@[implicit_reducible]
def «OneVariable M12804^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,0,0],[4,1,0,0,0],[3,2,2,2,3],[0,3,3,3,3],[3,0,0,4,4]]"

@[implicit_reducible]
def «OneVariable M12863» : Magma (Fin 5) where
  op := finOpTable "[[2,4,1,4,0],[0,1,2,3,4],[3,0,2,0,0],[2,1,0,3,0],[0,2,2,3,4]]"

@[implicit_reducible]
def «OneVariable M12863^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,3,2,0],[4,1,0,1,2],[1,2,2,0,2],[4,3,0,3,3],[0,4,0,0,4]]"

@[implicit_reducible]
def «OneVariable M12887» : Magma (Fin 5) where
  op := finOpTable "[[1,3,4,4,0],[2,1,0,0,4],[1,1,2,3,4],[0,0,2,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M12887^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,0,0],[3,1,1,0,1],[4,0,2,2,2],[4,0,3,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M12892» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,0,4],[5,1,0,3,3,0],[0,0,2,3,4,5],[1,0,2,3,4,5],[0,0,2,3,4,5],[1,0,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M12892^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,0,1,0,1],[2,1,0,0,0,0],[3,0,2,2,2,2],[0,3,3,3,3,3],[0,3,4,4,4,4],[4,0,5,5,5,5]]"

@[implicit_reducible]
def «OneVariable M12894» : Magma (Fin 5) where
  op := finOpTable "[[1,3,4,4,0],[2,1,0,0,4],[3,0,2,3,4],[0,0,2,3,0],[0,1,3,3,4]]"

@[implicit_reducible]
def «OneVariable M12894^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,0],[3,1,0,0,1],[4,0,2,2,3],[4,0,3,3,3],[0,4,4,0,4]]"

@[implicit_reducible]
def «OneVariable M12896» : Magma (Fin 9) where
  op := finOpTable "[[0,1,6,3,7,5,0,7,8],[1,1,6,3,4,4,5,3,1],[1,6,2,5,4,3,8,7,6],[3,0,5,7,4,2,0,1,5],[7,2,4,3,5,1,2,8,7],[5,4,0,8,6,3,4,7,0],[0,5,6,7,5,4,6,3,5],[2,3,7,6,0,5,3,4,2],[6,6,6,5,7,5,6,4,8]]"

@[implicit_reducible]
def «OneVariable M12896^op» : Magma (Fin 9) where
  op := finOpTable "[[0,1,1,3,7,5,0,2,6],[1,1,6,0,2,4,5,3,6],[6,6,2,5,4,0,6,7,6],[3,3,5,7,3,8,7,6,5],[7,4,4,4,5,6,5,0,7],[5,4,3,2,1,3,4,5,5],[0,5,8,0,2,4,6,3,6],[7,3,7,1,8,7,3,4,4],[8,1,6,5,7,0,5,2,8]]"

@[implicit_reducible]
def «OneVariable M12900» : Magma (Fin 6) where
  op := finOpTable "[[1,4,3,0,5,0],[2,1,0,3,0,0],[1,0,2,3,4,5],[4,1,2,3,4,5],[0,0,2,3,4,5],[0,0,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M12900^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,1,4,0,0],[4,1,0,1,0,0],[3,0,2,2,2,2],[0,3,3,3,3,3],[5,0,4,4,4,4],[0,0,5,5,5,5]]"

@[implicit_reducible]
def «OneVariable M12902» : Magma (Fin 10) where
  op := finOpTable "[[1,8,3,0,9,0,4,7,5,4],[2,5,0,1,4,6,3,7,0,3],[1,0,2,5,7,5,9,7,4,2],[3,1,5,7,3,8,4,6,5,0],[6,4,7,3,0,4,5,8,7,1],[0,9,7,2,4,3,1,5,7,1],[4,1,6,3,4,1,6,3,0,0],[7,4,0,9,2,5,3,4,0,3],[0,0,4,5,7,3,0,4,8,4],[4,5,4,7,0,1,0,3,4,9]]"

@[implicit_reducible]
def «OneVariable M12902^op» : Magma (Fin 10) where
  op := finOpTable "[[1,2,1,3,6,0,4,7,0,4],[8,5,0,1,4,9,1,4,0,5],[3,0,2,5,7,7,6,0,4,4],[0,1,5,7,3,2,3,9,5,7],[9,4,7,3,0,4,4,2,7,0],[0,6,5,8,4,3,1,5,3,1],[4,3,9,4,5,1,6,3,0,0],[7,7,7,6,8,5,3,4,4,3],[5,0,4,5,7,7,0,0,8,4],[4,3,2,0,1,1,0,3,4,9]]"

@[implicit_reducible]
def «OneVariable M12961» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,3],[4,1,2,3,0],[0,0,2,3,0],[0,2,4,3,4],[3,0,0,3,4]]"

@[implicit_reducible]
def «OneVariable M12961^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,0,0,3],[2,1,0,2,0],[3,2,2,4,0],[0,3,3,3,3],[3,0,0,4,4]]"

@[implicit_reducible]
def «OneVariable M12998» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,0,3],[2,1,2,3,0],[3,0,2,3,4],[0,1,2,3,4],[0,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M12998^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,0],[4,1,0,1,0],[3,2,2,2,2],[0,3,3,3,3],[3,0,4,4,4]]"

@[implicit_reducible]
def «OneVariable M13010» : Magma (Fin 6) where
  op := finOpTable "[[1,4,3,0,5,0],[2,1,0,4,0,1],[5,0,2,0,0,0],[4,0,0,3,0,0],[0,0,0,0,4,0],[0,0,0,0,0,5]]"

@[implicit_reducible]
def «OneVariable M13010^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,5,4,0,0],[4,1,0,0,0,0],[3,0,2,0,0,0],[0,4,0,3,0,0],[5,0,0,0,4,0],[0,1,0,0,0,5]]"

@[implicit_reducible]
def «OneVariable M13013» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,4,0],[3,1,0,0,4],[0,1,2,3,4],[4,0,2,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M13013^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,0,4,0],[2,1,1,0,1],[4,0,2,2,2],[4,0,3,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M13019» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,0,3],[2,1,0,3,0],[3,1,2,3,4],[0,1,2,3,4],[0,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M13019^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,0],[4,1,1,1,0],[3,0,2,2,2],[0,3,3,3,3],[3,0,4,4,4]]"

@[implicit_reducible]
def «OneVariable M13026» : Magma (Fin 9) where
  op := finOpTable "[[0,1,4,4,4,0,4,2,1],[6,8,2,6,7,7,1,4,0],[4,1,7,4,2,8,8,3,5],[4,6,2,3,6,2,4,2,1],[5,7,2,5,4,0,4,6,8],[4,7,8,3,3,5,4,7,4],[4,1,8,3,3,6,6,7,8],[2,5,0,2,6,6,7,1,8],[1,3,6,1,8,4,4,7,2]]"

@[implicit_reducible]
def «OneVariable M13026^op» : Magma (Fin 9) where
  op := finOpTable "[[0,6,4,4,5,4,4,2,1],[1,8,1,6,7,7,1,5,3],[4,2,7,2,2,8,8,0,6],[4,6,4,3,5,3,3,2,1],[4,7,2,6,4,3,3,6,8],[0,7,8,2,0,5,6,6,4],[4,1,8,4,4,4,6,7,4],[2,4,3,2,6,7,7,1,7],[1,0,5,1,8,4,8,8,2]]"

@[implicit_reducible]
def «OneVariable M13032» : Magma (Fin 6) where
  op := finOpTable "[[1,4,5,0,5,0],[2,1,0,3,0,0],[3,0,2,0,4,5],[4,0,2,3,4,5],[0,0,2,2,4,5],[0,0,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M13032^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,4,0,0],[4,1,0,0,0,0],[5,0,2,2,2,2],[0,3,0,3,2,3],[5,0,4,4,4,4],[0,0,5,5,5,5]]"

@[implicit_reducible]
def «OneVariable M13114» : Magma (Fin 8) where
  op := finOpTable "[[2,3,7,0,4,6,5,3],[0,1,0,3,3,1,7,1],[1,3,3,5,2,4,6,0],[0,6,5,4,1,2,3,5],[4,3,2,1,6,5,7,0],[6,1,2,2,5,5,6,4],[5,3,6,3,7,2,0,4],[0,1,0,0,4,0,4,7]]"

@[implicit_reducible]
def «OneVariable M13114^op» : Magma (Fin 8) where
  op := finOpTable "[[2,0,1,0,4,6,5,0],[3,1,3,6,3,1,3,1],[7,0,3,5,2,2,6,0],[0,3,5,4,1,2,3,0],[4,3,2,1,6,5,7,4],[6,1,4,2,5,5,2,0],[5,7,6,3,7,6,0,4],[3,1,0,5,0,4,4,7]]"

@[implicit_reducible]
def «OneVariable M13118» : Magma (Fin 10) where
  op := finOpTable "[[1,6,5,7,4,0,5,4,8,9],[2,5,2,3,8,4,0,7,1,8],[1,0,2,3,4,0,6,8,8,0],[7,3,2,3,4,5,4,7,5,7],[7,1,2,4,4,1,3,0,8,9],[0,9,7,7,1,8,7,5,3,9],[0,0,2,4,4,8,6,7,5,0],[3,7,8,1,1,5,7,0,9,3],[8,1,0,5,8,6,6,2,7,0],[9,5,2,7,4,1,2,8,7,9]]"

@[implicit_reducible]
def «OneVariable M13118^op» : Magma (Fin 10) where
  op := finOpTable "[[1,2,1,7,7,0,0,3,8,9],[6,5,0,3,1,9,0,7,1,5],[5,2,2,2,2,7,2,8,0,2],[7,3,3,3,4,7,4,1,5,7],[4,8,4,4,4,1,4,1,8,4],[0,4,0,5,1,8,8,5,6,1],[5,0,6,4,3,7,6,7,6,2],[4,7,8,7,0,5,7,0,2,8],[8,1,8,5,8,3,5,9,7,7],[9,8,0,7,9,9,0,3,0,9]]"

@[implicit_reducible]
def «OneVariable M13143» : Magma (Fin 10) where
  op := finOpTable "[[1,2,3,0,6,7,8,3,6,9],[7,3,0,8,5,1,6,0,5,6],[0,2,2,3,4,5,6,7,0,9],[0,4,9,5,1,2,1,9,1,3],[6,3,4,1,4,9,6,0,8,5],[6,1,3,7,6,9,5,3,6,8],[4,6,9,9,1,5,0,9,1,7],[1,0,7,5,0,3,9,7,2,6],[6,1,9,8,8,5,0,2,8,8],[9,3,0,3,5,4,2,0,5,6]]"

@[implicit_reducible]
def «OneVariable M13143^op» : Magma (Fin 10) where
  op := finOpTable "[[1,7,0,0,6,6,4,1,6,9],[2,3,2,4,3,1,6,0,1,3],[3,0,2,9,4,3,9,7,9,0],[0,8,3,5,1,7,9,5,8,3],[6,5,4,1,4,6,1,0,8,5],[7,1,5,2,9,9,5,3,5,4],[8,6,6,1,6,5,0,9,0,2],[3,0,7,9,0,3,9,7,2,0],[6,5,0,1,8,6,1,2,8,5],[9,6,9,3,5,8,7,6,8,6]]"

@[implicit_reducible]
def «OneVariable M13146» : Magma (Fin 10) where
  op := finOpTable "[[2,4,8,3,0,5,7,6,4,6],[2,1,3,3,1,3,3,6,9,1],[1,0,4,2,5,3,6,3,0,9],[3,0,2,6,9,0,1,0,4,4],[0,1,7,8,3,2,4,2,6,6],[5,1,2,6,2,5,0,7,8,0],[9,3,6,5,4,3,0,2,8,2],[6,6,4,9,7,7,0,7,8,0],[0,4,0,4,4,8,8,7,8,9],[6,2,9,4,3,0,6,0,0,9]]"

@[implicit_reducible]
def «OneVariable M13146^op» : Magma (Fin 10) where
  op := finOpTable "[[2,2,1,3,0,5,9,6,0,6],[4,1,0,0,1,1,3,6,4,2],[8,3,4,2,7,2,6,4,0,9],[3,3,2,6,8,6,5,9,4,4],[0,1,5,9,3,2,4,7,4,3],[5,3,3,0,2,5,3,7,8,0],[7,3,6,1,4,0,0,0,8,6],[6,6,3,0,2,7,2,7,7,0],[4,9,0,4,6,8,8,8,8,0],[6,1,9,4,6,0,2,0,9,9]]"

@[implicit_reducible]
def «OneVariable M13168» : Magma (Fin 9) where
  op := finOpTable "[[4,7,6,0,2,7,0,1,6],[7,1,1,4,4,5,0,0,8],[0,3,2,3,0,5,1,3,6],[3,4,8,7,5,4,8,2,3],[8,6,0,1,3,6,4,4,0],[7,8,5,4,3,5,2,7,6],[0,2,6,7,4,2,6,3,5],[5,8,3,6,7,8,3,0,7],[4,6,1,3,0,1,8,7,8]]"

@[implicit_reducible]
def «OneVariable M13168^op» : Magma (Fin 9) where
  op := finOpTable "[[4,7,0,3,8,7,0,5,4],[7,1,3,4,6,8,2,8,6],[6,1,2,8,0,5,6,3,1],[0,4,3,7,1,4,7,6,3],[2,4,0,5,3,3,4,7,0],[7,5,5,4,6,5,2,8,1],[0,0,1,8,4,2,6,3,8],[1,0,3,2,4,7,3,0,7],[6,8,6,3,0,6,5,7,8]]"

@[implicit_reducible]
def «OneVariable M13254» : Magma (Fin 9) where
  op := finOpTable "[[4,5,7,5,1,0,0,2,2],[0,1,6,0,0,0,6,0,1],[8,6,0,6,2,2,3,5,5],[5,0,6,3,0,3,7,0,8],[3,0,4,0,6,7,5,4,7],[0,0,2,3,4,5,4,7,5],[6,7,1,7,8,4,2,6,4],[2,0,5,7,4,5,6,7,4],[2,1,2,4,7,0,4,0,8]]"

@[implicit_reducible]
def «OneVariable M13254^op» : Magma (Fin 9) where
  op := finOpTable "[[4,0,8,5,3,0,6,2,2],[5,1,6,0,0,0,7,0,1],[7,6,0,6,4,2,1,5,2],[5,0,6,3,0,3,7,7,4],[1,0,2,0,6,4,8,4,7],[0,0,2,3,7,5,4,5,0],[0,6,3,7,5,4,2,6,4],[2,0,5,0,4,7,6,7,0],[2,1,5,8,7,5,4,4,8]]"

@[implicit_reducible]
def «OneVariable M13258» : Magma (Fin 3) where
  op := finOpTable "[[1,2,1],[1,1,0],[0,1,2]]"

@[implicit_reducible]
def «OneVariable M13258^op» : Magma (Fin 3) where
  op := finOpTable "[[1,1,0],[2,1,1],[1,0,2]]"

@[implicit_reducible]
def «OneVariable M13261» : Magma (Fin 3) where
  op := finOpTable "[[1,2,2],[1,1,0],[0,0,2]]"

@[implicit_reducible]
def «OneVariable M13261^op» : Magma (Fin 3) where
  op := finOpTable "[[1,1,0],[2,1,0],[2,0,2]]"

@[implicit_reducible]
def «OneVariable M13268» : Magma (Fin 8) where
  op := finOpTable "[[6,7,2,0,0,6,5,0],[3,1,2,3,6,1,6,1],[2,1,3,5,2,3,6,3],[1,0,3,0,4,0,3,0],[0,1,7,4,2,5,4,2],[0,1,2,2,4,5,0,7],[6,4,6,3,1,5,4,7],[3,1,4,2,4,0,0,7]]"

@[implicit_reducible]
def «OneVariable M13268^op» : Magma (Fin 8) where
  op := finOpTable "[[6,3,2,1,0,0,6,3],[7,1,1,0,1,1,4,1],[2,2,3,3,7,2,6,4],[0,3,5,0,4,2,3,2],[0,6,2,4,2,4,1,4],[6,1,3,0,5,5,5,0],[5,6,6,3,4,0,4,0],[0,1,3,0,2,7,7,7]]"

@[implicit_reducible]
def «OneVariable M13272» : Magma (Fin 8) where
  op := finOpTable "[[2,2,1,0,7,5,7,0],[0,1,2,3,0,1,5,7],[2,0,3,6,0,2,3,7],[0,5,3,5,3,1,2,3],[4,0,4,7,4,5,5,7],[5,3,2,5,7,7,1,4],[6,0,2,3,6,6,6,7],[6,1,7,3,5,7,0,0]]"

@[implicit_reducible]
def «OneVariable M13272^op» : Magma (Fin 8) where
  op := finOpTable "[[2,0,2,0,4,5,6,6],[2,1,0,5,0,3,0,1],[1,2,3,3,4,2,2,7],[0,3,6,5,7,5,3,3],[7,0,0,3,4,7,6,5],[5,1,2,1,5,7,6,7],[7,5,3,2,5,1,6,0],[0,7,7,3,7,4,7,0]]"

@[implicit_reducible]
def «OneVariable M13276» : Magma (Fin 8) where
  op := finOpTable "[[3,3,0,1,1,0,6,5],[0,1,7,0,1,1,1,1],[0,2,6,2,3,2,7,6],[3,0,4,2,2,5,3,7],[4,7,3,3,4,6,6,4],[7,1,2,5,6,0,5,0],[6,4,6,3,5,4,5,2],[5,1,2,7,0,5,2,7]]"

@[implicit_reducible]
def «OneVariable M13276^op» : Magma (Fin 8) where
  op := finOpTable "[[3,0,0,3,4,7,6,5],[3,1,2,0,7,1,4,1],[0,7,6,4,3,2,6,2],[1,0,2,2,3,5,3,7],[1,1,3,2,4,6,5,0],[0,1,2,5,6,0,4,5],[6,1,7,3,6,5,5,2],[5,1,6,7,4,0,2,7]]"

@[implicit_reducible]
def «OneVariable M13278» : Magma (Fin 8) where
  op := finOpTable "[[7,5,3,0,4,0,4,2],[5,1,5,3,3,5,7,1],[0,6,2,3,2,6,6,0],[0,5,3,4,1,3,7,3],[4,3,5,4,5,6,0,7],[1,7,5,3,5,0,4,5],[2,4,0,7,4,4,6,7],[7,0,0,6,7,5,6,3]]"

@[implicit_reducible]
def «OneVariable M13278^op» : Magma (Fin 8) where
  op := finOpTable "[[7,5,0,0,4,1,2,7],[5,1,6,5,3,7,4,0],[3,5,2,3,5,5,0,0],[0,3,3,4,4,3,7,6],[4,3,2,1,5,5,4,7],[0,5,6,3,6,0,4,5],[4,7,6,7,0,4,6,6],[2,1,0,3,7,5,7,3]]"

@[implicit_reducible]
def «OneVariable M13283» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[1,1,0,0],[0,0,2,0],[1,1,0,3]]"

@[implicit_reducible]
def «OneVariable M13283^op» : Magma (Fin 4) where
  op := finOpTable "[[1,1,0,1],[2,1,0,1],[3,0,2,0],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M13288» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[1,1,0,3],[0,0,2,1],[0,3,1,3]]"

@[implicit_reducible]
def «OneVariable M13288^op» : Magma (Fin 4) where
  op := finOpTable "[[1,1,0,0],[2,1,0,3],[3,0,2,1],[0,3,1,3]]"

@[implicit_reducible]
def «OneVariable M13289» : Magma (Fin 7) where
  op := finOpTable "[[0,2,4,3,4,0,6],[1,1,2,2,6,3,6],[4,5,3,1,2,2,6],[3,2,3,6,4,0,5],[5,6,0,3,2,4,4],[0,5,2,3,4,5,3],[6,0,2,6,1,3,4]]"

@[implicit_reducible]
def «OneVariable M13289^op» : Magma (Fin 7) where
  op := finOpTable "[[0,1,4,3,5,0,6],[2,1,5,2,6,5,0],[4,2,3,3,0,2,2],[3,2,1,6,3,3,6],[4,6,2,4,2,4,1],[0,3,2,0,4,5,3],[6,6,6,5,4,3,4]]"

@[implicit_reducible]
def «OneVariable M13293» : Magma (Fin 8) where
  op := finOpTable "[[3,0,1,2,0,0,6,0],[0,1,5,3,3,3,6,6],[0,2,2,0,0,7,0,0],[3,6,1,4,1,1,3,7],[0,7,7,4,6,7,5,4],[7,7,7,3,4,5,4,7],[6,0,1,3,6,7,7,1],[5,7,7,7,4,3,7,0]]"

@[implicit_reducible]
def «OneVariable M13293^op» : Magma (Fin 8) where
  op := finOpTable "[[3,0,0,3,0,7,6,5],[0,1,2,6,7,7,0,7],[1,5,2,1,7,7,1,7],[2,3,0,4,4,3,3,7],[0,3,0,1,6,4,6,4],[0,3,7,1,7,5,7,3],[6,6,0,3,5,4,7,7],[0,6,0,7,4,7,1,0]]"

@[implicit_reducible]
def «OneVariable M13294» : Magma (Fin 8) where
  op := finOpTable "[[7,0,1,3,0,0,4,6],[2,0,7,1,4,1,3,1],[2,1,2,2,4,5,2,7],[3,6,4,1,3,5,0,0],[0,4,1,2,3,4,5,7],[0,6,7,5,6,4,3,5],[0,1,6,3,6,5,6,2],[7,1,4,3,7,2,0,5]]"

@[implicit_reducible]
def «OneVariable M13294^op» : Magma (Fin 8) where
  op := finOpTable "[[7,2,2,3,0,0,0,7],[0,0,1,6,4,6,1,1],[1,7,2,4,1,7,6,4],[3,1,2,1,2,5,3,3],[0,4,4,3,3,6,6,7],[0,1,5,5,4,4,5,2],[4,3,2,0,5,3,6,0],[6,1,7,0,7,5,2,5]]"

@[implicit_reducible]
def «OneVariable M13295» : Magma (Fin 8) where
  op := finOpTable "[[2,5,1,0,0,0,4,7],[0,1,0,3,4,5,0,3],[2,0,3,5,4,0,1,2],[0,2,3,7,3,2,6,1],[6,4,4,3,0,7,1,4],[0,4,2,2,7,5,7,7],[4,3,7,6,4,6,6,7],[7,3,2,7,5,0,0,4]]"

@[implicit_reducible]
def «OneVariable M13295^op» : Magma (Fin 8) where
  op := finOpTable "[[2,0,2,0,6,0,4,7],[5,1,0,2,4,4,3,3],[1,0,3,3,4,2,7,2],[0,3,5,7,3,2,6,7],[0,4,4,3,0,7,4,5],[0,5,0,2,7,5,6,0],[4,0,1,6,1,7,6,0],[7,3,2,1,4,7,7,4]]"

@[implicit_reducible]
def «OneVariable M13296» : Magma (Fin 8) where
  op := finOpTable "[[5,1,3,0,7,4,0,0],[1,3,7,4,0,0,6,1],[3,7,2,3,2,5,5,7],[2,3,5,0,1,3,6,7],[0,1,4,1,4,0,6,6],[5,0,7,3,0,6,2,5],[0,6,5,1,1,6,7,4],[0,2,3,7,6,5,7,1]]"

@[implicit_reducible]
def «OneVariable M13296^op» : Magma (Fin 8) where
  op := finOpTable "[[5,1,3,2,0,5,0,0],[1,3,7,3,1,0,6,2],[3,7,2,5,4,7,5,3],[0,4,3,0,1,3,1,7],[7,0,2,1,4,0,1,6],[4,0,5,3,0,6,6,5],[0,6,5,6,6,2,7,7],[0,1,7,7,6,5,4,1]]"

@[implicit_reducible]
def «OneVariable M13298» : Magma (Fin 3) where
  op := finOpTable "[[0,1,1],[2,2,0],[2,0,2]]"

@[implicit_reducible]
def «OneVariable M13298^op» : Magma (Fin 3) where
  op := finOpTable "[[0,2,2],[1,2,0],[1,0,2]]"

@[implicit_reducible]
def «OneVariable M13299» : Magma (Fin 3) where
  op := finOpTable "[[0,1,2],[2,2,0],[1,0,2]]"

@[implicit_reducible]
def «OneVariable M13299^op» : Magma (Fin 3) where
  op := finOpTable "[[0,2,1],[1,2,0],[2,0,2]]"

@[implicit_reducible]
def «OneVariable M13305» : Magma (Fin 4) where
  op := finOpTable "[[0,3,1,0],[2,0,0,0],[1,1,2,2],[1,1,3,3]]"

@[implicit_reducible]
def «OneVariable M13305^op» : Magma (Fin 4) where
  op := finOpTable "[[0,2,1,1],[3,0,1,1],[1,0,2,3],[0,0,2,3]]"

@[implicit_reducible]
def «OneVariable M13309» : Magma (Fin 3) where
  op := finOpTable "[[2,1,1],[0,1,0],[1,0,2]]"

@[implicit_reducible]
def «OneVariable M13309^op» : Magma (Fin 3) where
  op := finOpTable "[[2,0,1],[1,1,0],[1,0,2]]"

@[implicit_reducible]
def «OneVariable M13346» : Magma (Fin 4) where
  op := finOpTable "[[0,2,1,0],[3,0,0,0],[1,1,2,2],[1,1,3,3]]"

@[implicit_reducible]
def «OneVariable M13346^op» : Magma (Fin 4) where
  op := finOpTable "[[0,3,1,1],[2,0,1,1],[1,0,2,3],[0,0,2,3]]"

@[implicit_reducible]
def «OneVariable M13368» : Magma (Fin 4) where
  op := finOpTable "[[1,2,1,1],[3,1,0,0],[0,1,2,1],[0,0,1,3]]"

@[implicit_reducible]
def «OneVariable M13368^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,0],[2,1,1,0],[1,0,2,1],[1,0,1,3]]"

@[implicit_reducible]
def «OneVariable M13374» : Magma (Fin 4) where
  op := finOpTable "[[1,3,1,1],[2,1,0,0],[0,1,2,1],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M13374^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,0],[3,1,1,0],[1,0,2,0],[1,0,1,3]]"

@[implicit_reducible]
def «OneVariable M13380» : Magma (Fin 4) where
  op := finOpTable "[[1,2,1,1],[3,1,0,0],[0,0,2,2],[0,0,3,3]]"

@[implicit_reducible]
def «OneVariable M13380^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,0],[2,1,0,0],[1,0,2,3],[1,0,2,3]]"

@[implicit_reducible]
def «OneVariable M13424» : Magma (Fin 8) where
  op := finOpTable "[[1,2,1,0,4,1,7,6],[5,3,1,7,1,0,6,3],[0,0,2,3,3,3,2,2],[0,7,4,4,2,5,3,1],[4,1,3,2,6,6,5,2],[0,0,3,5,4,5,4,0],[7,6,2,3,5,4,0,0],[6,1,2,1,2,0,6,7]]"

@[implicit_reducible]
def «OneVariable M13424^op» : Magma (Fin 8) where
  op := finOpTable "[[1,5,0,0,4,0,7,6],[2,3,0,7,1,0,6,1],[1,1,2,4,3,3,2,2],[0,7,3,4,2,5,3,1],[4,1,3,2,6,4,5,2],[1,0,3,5,6,5,4,0],[7,6,2,3,5,4,0,6],[6,3,2,1,2,0,0,7]]"

@[implicit_reducible]
def «OneVariable M13451» : Magma (Fin 8) where
  op := finOpTable "[[1,6,1,0,4,7,1,5],[2,3,0,5,1,3,0,7],[0,2,2,0,4,2,6,4],[0,5,0,4,6,1,4,3],[4,1,7,6,7,6,3,2],[7,1,5,1,6,5,5,7],[0,0,6,3,3,6,6,6],[5,7,4,3,2,0,6,0]]"

@[implicit_reducible]
def «OneVariable M13451^op» : Magma (Fin 8) where
  op := finOpTable "[[1,2,0,0,4,7,0,5],[6,3,2,5,1,1,0,7],[1,0,2,0,7,5,6,4],[0,5,0,4,6,1,3,3],[4,1,4,6,7,6,3,2],[7,3,2,1,6,5,6,0],[1,0,6,4,3,5,6,6],[5,7,4,3,2,7,6,0]]"

@[implicit_reducible]
def «OneVariable M13462» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,0,3],[4,0,3,1,0],[0,1,2,2,2],[0,1,3,3,3],[0,1,4,4,4]]"

@[implicit_reducible]
def «OneVariable M13462^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,0,0,0],[2,0,1,1,1],[1,3,2,3,4],[0,1,2,3,4],[3,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M13468» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[2,1,1,3],[0,0,2,0],[0,2,0,3]]"

@[implicit_reducible]
def «OneVariable M13468^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,0],[2,1,0,2],[3,1,2,0],[0,3,0,3]]"

@[implicit_reducible]
def «OneVariable M13489» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[2,1,0,3],[0,1,2,0],[0,3,0,3]]"

@[implicit_reducible]
def «OneVariable M13489^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,0],[2,1,1,3],[3,0,2,0],[0,3,0,3]]"

@[implicit_reducible]
def «OneVariable M13496» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,2,0],[0,1,0,0,1],[1,0,2,2,4],[0,0,0,3,3],[0,2,4,3,4]]"

@[implicit_reducible]
def «OneVariable M13496^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,1,0,0],[4,1,0,0,2],[3,0,2,0,4],[2,0,2,3,3],[0,1,4,3,4]]"

@[implicit_reducible]
def «OneVariable M13521» : Magma (Fin 5) where
  op := finOpTable "[[1,3,4,1,0],[2,1,1,0,0],[0,0,2,3,2],[0,0,4,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M13521^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,0,0,0],[3,1,0,0,1],[4,1,2,4,2],[1,0,3,3,3],[0,0,2,4,4]]"

@[implicit_reducible]
def «OneVariable M13530» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,4,0],[3,1,0,0,0],[0,1,2,3,0],[0,0,2,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M13530^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,0,0,0],[2,1,1,0,1],[1,0,2,2,2],[4,0,3,3,3],[0,0,0,4,4]]"

@[implicit_reducible]
def «OneVariable M13541» : Magma (Fin 5) where
  op := finOpTable "[[3,2,0,4,1],[0,1,2,0,2],[0,3,4,2,1],[1,0,2,3,0],[0,2,1,0,4]]"

@[implicit_reducible]
def «OneVariable M13541^op» : Magma (Fin 5) where
  op := finOpTable "[[3,0,0,1,0],[2,1,3,0,2],[0,2,4,2,1],[4,0,2,3,0],[1,2,1,0,4]]"

@[implicit_reducible]
def «OneVariable M13543» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,0,1],[2,1,0,3,0],[0,0,2,3,4],[3,1,2,3,4],[0,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M13543^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,0,3,0],[4,1,0,1,0],[3,0,2,2,2],[0,3,3,3,3],[1,0,4,4,4]]"

@[implicit_reducible]
def «OneVariable M13546» : Magma (Fin 9) where
  op := finOpTable "[[7,8,3,4,3,7,6,5,0],[0,1,7,6,0,0,6,0,0],[3,0,2,3,5,2,7,7,1],[2,6,0,0,5,3,1,7,6],[3,0,6,3,4,5,7,7,8],[0,0,6,3,1,5,6,0,5],[0,5,7,8,7,6,3,4,3],[1,0,6,3,8,0,2,6,7],[0,0,2,6,1,5,6,7,8]]"

@[implicit_reducible]
def «OneVariable M13546^op» : Magma (Fin 9) where
  op := finOpTable "[[7,0,3,2,3,0,0,1,0],[8,1,0,6,0,0,5,0,0],[3,7,2,0,6,6,7,6,2],[4,6,3,0,3,3,8,3,6],[3,0,5,5,4,1,7,8,1],[7,0,2,3,5,5,6,0,5],[6,6,7,1,7,6,3,2,6],[5,0,7,7,7,0,4,6,7],[0,0,1,6,8,5,3,7,8]]"

@[implicit_reducible]
def «OneVariable M13609» : Magma (Fin 9) where
  op := finOpTable "[[0,1,2,1,1,5,0,7,1],[3,3,1,0,5,7,8,5,1],[2,2,5,4,3,6,5,3,0],[1,6,7,2,8,3,1,2,3],[2,5,3,3,4,5,3,7,4],[5,4,8,5,1,1,2,0,2],[6,1,2,1,8,2,6,4,3],[7,5,3,3,4,5,6,7,2],[4,1,2,3,8,2,4,7,8]]"

@[implicit_reducible]
def «OneVariable M13609^op» : Magma (Fin 9) where
  op := finOpTable "[[0,3,2,1,2,5,6,7,4],[1,3,2,6,5,4,1,5,1],[2,1,5,7,3,8,2,3,2],[1,0,4,2,3,5,1,3,3],[1,5,3,8,4,1,8,4,8],[5,7,6,3,5,1,2,5,2],[0,8,5,1,3,2,6,6,4],[7,5,3,2,7,0,4,7,7],[1,1,0,3,4,2,3,2,8]]"

@[implicit_reducible]
def «OneVariable M13611» : Magma (Fin 8) where
  op := finOpTable "[[0,1,1,6,4,5,4,6],[0,2,0,7,1,4,6,3],[1,5,4,3,7,1,2,6],[6,7,3,1,4,6,5,2],[3,1,7,4,6,2,0,2],[5,1,1,6,2,5,6,7],[4,6,2,5,0,1,3,0],[6,3,2,3,2,1,0,7]]"

@[implicit_reducible]
def «OneVariable M13611^op» : Magma (Fin 8) where
  op := finOpTable "[[0,0,1,6,3,5,4,6],[1,2,5,7,1,1,6,3],[1,0,4,3,7,1,2,2],[6,7,3,1,4,6,5,3],[4,1,7,4,6,2,0,2],[5,4,1,6,2,5,1,1],[4,6,2,5,0,6,3,0],[6,3,6,2,2,7,0,7]]"

@[implicit_reducible]
def «OneVariable M13612» : Magma (Fin 5) where
  op := finOpTable "[[1,3,0,2,1],[4,0,1,0,2],[2,2,2,4,0],[0,1,4,3,2],[0,1,2,2,4]]"

@[implicit_reducible]
def «OneVariable M13612^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,2,0,0],[3,0,2,1,1],[0,1,2,4,2],[2,0,4,3,2],[1,2,0,2,4]]"

@[implicit_reducible]
def «OneVariable M13615» : Magma (Fin 5) where
  op := finOpTable "[[1,3,0,2,1],[4,0,1,0,2],[0,1,2,2,2],[0,1,1,3,3],[0,1,4,4,4]]"

@[implicit_reducible]
def «OneVariable M13615^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,0,0,0],[3,0,1,1,1],[0,1,2,1,4],[2,0,2,3,4],[1,2,2,3,4]]"

@[implicit_reducible]
def «OneVariable M13635» : Magma (Fin 5) where
  op := finOpTable "[[2,4,1,2,0],[0,1,0,0,1],[3,0,2,3,2],[0,3,0,3,0],[0,2,0,0,4]]"

@[implicit_reducible]
def «OneVariable M13635^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,3,0,0],[4,1,0,3,2],[1,0,2,0,0],[2,0,3,3,0],[0,1,2,0,4]]"

@[implicit_reducible]
def «OneVariable M13640» : Magma (Fin 5) where
  op := finOpTable "[[2,3,1,0,2],[0,1,0,2,4],[4,1,2,1,0],[0,2,0,3,3],[0,2,0,3,4]]"

@[implicit_reducible]
def «OneVariable M13640^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,4,0,0],[3,1,1,2,2],[1,0,2,0,0],[0,2,1,3,3],[2,4,0,3,4]]"

@[implicit_reducible]
def «OneVariable M13652» : Magma (Fin 5) where
  op := finOpTable "[[2,4,1,2,0],[0,1,3,3,4],[3,0,2,0,0],[0,4,0,3,3],[0,2,4,3,4]]"

@[implicit_reducible]
def «OneVariable M13652^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,3,0,0],[4,1,0,4,2],[1,3,2,0,4],[2,3,0,3,3],[0,4,0,3,4]]"

@[implicit_reducible]
def «OneVariable M13655» : Magma (Fin 5) where
  op := finOpTable "[[2,4,1,3,0],[0,1,0,4,4],[3,0,2,0,4],[0,3,0,3,4],[0,4,2,4,4]]"

@[implicit_reducible]
def «OneVariable M13655^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,3,0,0],[4,1,0,3,4],[1,0,2,0,2],[3,4,0,3,4],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M13695» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,1],[4,1,0,0,0],[0,0,2,2,1],[3,3,3,3,3],[0,0,4,3,4]]"

@[implicit_reducible]
def «OneVariable M13695^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,0,3,0],[2,1,0,3,0],[3,0,2,3,4],[0,0,2,3,3],[1,0,1,3,4]]"

@[implicit_reducible]
def «OneVariable M13713» : Magma (Fin 9) where
  op := finOpTable "[[0,1,4,8,4,3,6,7,8],[1,6,7,6,4,0,5,2,2],[4,8,1,2,0,4,6,1,3],[0,1,2,3,4,6,1,8,8],[2,1,5,4,2,3,8,6,6],[0,1,4,3,4,5,1,5,4],[6,3,2,1,7,1,4,0,4],[1,2,2,3,6,6,6,7,8],[3,2,2,2,6,4,6,8,8]]"

@[implicit_reducible]
def «OneVariable M13713^op» : Magma (Fin 9) where
  op := finOpTable "[[0,1,4,0,2,0,6,1,3],[1,6,8,1,1,1,3,2,2],[4,7,1,2,5,4,2,2,2],[8,6,2,3,4,3,1,3,2],[4,4,0,4,2,4,7,6,6],[3,0,4,6,3,5,1,6,4],[6,5,6,1,8,1,4,6,6],[7,2,1,8,6,5,0,7,8],[8,2,3,8,6,4,4,8,8]]"

@[implicit_reducible]
def «OneVariable M13778» : Magma (Fin 9) where
  op := finOpTable "[[3,2,5,6,3,2,7,0,0],[2,1,2,3,6,4,6,7,3],[1,7,0,2,8,0,8,2,6],[4,8,3,8,0,3,0,5,7],[0,6,8,0,4,4,0,2,8],[2,7,2,3,5,5,1,1,8],[0,4,8,0,0,7,6,6,8],[0,6,2,3,8,1,7,7,3],[8,3,4,1,5,8,2,3,2]]"

@[implicit_reducible]
def «OneVariable M13778^op» : Magma (Fin 9) where
  op := finOpTable "[[3,2,1,4,0,2,0,0,8],[2,1,7,8,6,7,4,6,3],[5,2,0,3,8,2,8,2,4],[6,3,2,8,0,3,0,3,1],[3,6,8,0,4,5,0,8,5],[2,4,0,3,4,5,7,1,8],[7,6,8,0,0,1,6,7,2],[0,7,2,5,2,1,6,7,3],[0,3,6,7,8,8,8,3,2]]"

@[implicit_reducible]
def «OneVariable M13807» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,4,0],[3,1,2,0,4],[0,0,2,3,4],[0,0,2,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M13807^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,0,0,0],[2,1,0,0,1],[4,2,2,2,2],[4,0,3,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M13809» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,5,0],[4,1,0,4,0,1],[0,0,2,0,0,0],[4,0,0,3,0,0],[0,0,0,0,4,0],[0,0,0,0,0,5]]"

@[implicit_reducible]
def «OneVariable M13809^op» : Magma (Fin 6) where
  op := finOpTable "[[1,4,0,4,0,0],[2,1,0,0,0,0],[3,0,2,0,0,0],[0,4,0,3,0,0],[5,0,0,0,4,0],[0,1,0,0,0,5]]"

@[implicit_reducible]
def «OneVariable M13811» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[2,1,0,0],[0,0,2,1],[3,0,1,3]]"

@[implicit_reducible]
def «OneVariable M13811^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,3],[2,1,0,0],[3,0,2,1],[0,0,1,3]]"

@[implicit_reducible]
def «OneVariable M13818» : Magma (Fin 5) where
  op := finOpTable "[[1,3,4,4,0],[2,1,2,0,4],[0,0,2,3,4],[0,0,2,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M13818^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,0,0,0],[3,1,0,0,1],[4,2,2,2,2],[4,0,3,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M13821» : Magma (Fin 6) where
  op := finOpTable "[[1,4,3,0,5,0],[2,1,0,1,0,1],[0,0,2,0,0,0],[4,0,0,3,0,0],[0,0,0,0,4,0],[0,0,0,0,0,5]]"

@[implicit_reducible]
def «OneVariable M13821^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,0,4,0,0],[4,1,0,0,0,0],[3,0,2,0,0,0],[0,1,0,3,0,0],[5,0,0,0,4,0],[0,1,0,0,0,5]]"

@[implicit_reducible]
def «OneVariable M13825» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,4,0],[3,1,0,0,4],[0,1,2,3,4],[0,0,2,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M13825^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,0,0,0],[2,1,1,0,1],[4,0,2,2,2],[4,0,3,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M13828» : Magma (Fin 5) where
  op := finOpTable "[[1,3,4,4,0],[2,1,0,0,4],[0,1,2,3,4],[0,0,2,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M13828^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,0,0,0],[3,1,1,0,1],[4,0,2,2,2],[4,0,3,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M13835» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,4,0],[3,1,0,0,4],[0,0,2,3,4],[0,0,2,3,4],[0,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M13835^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,0,0,0],[2,1,0,0,0],[4,0,2,2,2],[4,0,3,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M13851» : Magma (Fin 9) where
  op := finOpTable "[[1,5,3,0,8,6,0,7,4],[2,6,0,7,6,0,3,1,8],[0,0,2,5,4,2,4,3,2],[1,1,2,3,4,8,1,7,7],[8,1,7,1,6,2,2,4,8],[0,0,5,8,0,5,6,6,7],[0,3,4,1,2,8,7,5,6],[7,1,0,0,4,6,5,8,3],[4,8,2,7,1,7,6,3,0]]"

@[implicit_reducible]
def «OneVariable M13851^op» : Magma (Fin 9) where
  op := finOpTable "[[1,2,0,1,8,0,0,7,4],[5,6,0,1,1,0,3,1,8],[3,0,2,2,7,5,4,0,2],[0,7,5,3,1,8,1,0,7],[8,6,4,4,6,0,2,4,1],[6,0,2,8,2,5,8,6,7],[0,3,4,1,2,6,7,5,6],[7,1,3,7,4,6,5,8,3],[4,8,2,7,8,7,6,3,0]]"

@[implicit_reducible]
def «OneVariable M13853» : Magma (Fin 8) where
  op := finOpTable "[[0,1,1,3,3,5,6,7],[6,2,0,3,5,4,1,6],[1,7,6,2,4,3,5,1],[1,3,2,4,0,5,7,6],[3,5,4,0,1,2,6,2],[5,4,2,5,4,5,2,0],[4,1,5,7,6,2,3,4],[7,1,1,6,4,0,6,7]]"

@[implicit_reducible]
def «OneVariable M13853^op» : Magma (Fin 8) where
  op := finOpTable "[[0,6,1,1,3,5,4,7],[1,2,7,3,5,4,1,1],[1,0,6,2,4,2,5,1],[3,3,2,4,0,5,7,6],[3,5,4,0,1,4,6,4],[5,4,3,5,2,5,2,0],[6,1,5,7,6,2,3,6],[7,6,1,6,2,0,4,7]]"

@[implicit_reducible]
def «OneVariable M13854» : Magma (Fin 9) where
  op := finOpTable "[[1,2,3,0,4,0,7,6,5],[8,5,0,3,6,4,1,7,0],[0,0,2,3,3,5,5,0,8],[3,0,7,4,2,5,8,3,6],[4,1,3,2,7,1,6,8,0],[0,4,3,5,1,6,2,5,3],[7,1,5,8,6,2,3,7,4],[6,7,0,3,8,5,1,0,4],[0,0,8,6,4,2,6,4,8]]"

@[implicit_reducible]
def «OneVariable M13854^op» : Magma (Fin 9) where
  op := finOpTable "[[1,8,0,3,4,0,7,6,0],[2,5,0,0,1,4,1,7,0],[3,0,2,7,3,3,5,0,8],[0,3,3,4,2,5,8,3,6],[4,6,3,2,7,1,6,8,4],[0,4,5,5,1,6,2,5,2],[7,1,5,8,6,2,3,1,6],[6,7,0,3,8,5,7,0,4],[5,0,8,6,0,3,4,4,8]]"

@[implicit_reducible]
def «OneVariable M13867» : Magma (Fin 4) where
  op := finOpTable "[[3,1,3,2],[0,1,2,3],[1,1,2,1],[2,2,0,0]]"

@[implicit_reducible]
def «OneVariable M13867^op» : Magma (Fin 4) where
  op := finOpTable "[[3,0,1,2],[1,1,1,2],[3,2,2,0],[2,3,1,0]]"

@[implicit_reducible]
def «OneVariable M13883» : Magma (Fin 5) where
  op := finOpTable "[[4,4,2,4,3],[2,1,2,0,0],[0,2,2,3,4],[4,1,1,3,2],[1,0,1,0,0]]"

@[implicit_reducible]
def «OneVariable M13883^op» : Magma (Fin 5) where
  op := finOpTable "[[4,2,0,4,1],[4,1,2,1,0],[2,2,2,1,1],[4,0,3,3,0],[3,0,4,2,0]]"

@[implicit_reducible]
def «OneVariable M13884» : Magma (Fin 5) where
  op := finOpTable "[[4,3,4,4,3],[0,1,2,2,4],[4,2,2,3,1],[1,1,3,3,0],[2,3,0,0,0]]"

@[implicit_reducible]
def «OneVariable M13884^op» : Magma (Fin 5) where
  op := finOpTable "[[4,0,4,1,2],[3,1,2,1,3],[4,2,2,3,0],[4,2,3,3,0],[3,4,1,0,0]]"

@[implicit_reducible]
def «OneVariable M13887» : Magma (Fin 4) where
  op := finOpTable "[[3,2,0,1],[2,1,1,2],[0,2,2,3],[1,2,3,0]]"

@[implicit_reducible]
def «OneVariable M13889» : Magma (Fin 5) where
  op := finOpTable "[[2,3,3,1,0],[0,1,2,3,4],[3,2,0,1,1],[4,3,1,4,2],[0,4,1,2,3]]"

@[implicit_reducible]
def «OneVariable M13889^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,3,4,0],[3,1,2,3,4],[3,2,0,1,1],[1,3,1,4,2],[0,4,1,2,3]]"

@[implicit_reducible]
def «OneVariable M13896» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,4,0],[3,0,4,4,1],[4,4,3,0,2],[4,4,0,2,3],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M13906» : Magma (Fin 5) where
  op := finOpTable "[[0,3,4,4,1],[3,1,1,3,4],[3,1,2,1,3],[1,3,1,4,0],[1,4,1,2,3]]"

@[implicit_reducible]
def «OneVariable M13906^op» : Magma (Fin 5) where
  op := finOpTable "[[0,3,3,1,1],[3,1,1,3,4],[4,1,2,1,1],[4,3,1,4,2],[1,4,3,0,3]]"

@[implicit_reducible]
def «OneVariable M13908» : Magma (Fin 6) where
  op := finOpTable "[[2,5,3,4,4,0],[5,1,0,5,1,4],[1,4,0,4,2,3],[2,4,4,5,3,1],[0,1,2,3,4,5],[0,4,4,2,5,3]]"

@[implicit_reducible]
def «OneVariable M13908^op» : Magma (Fin 6) where
  op := finOpTable "[[2,5,1,2,0,0],[5,1,4,4,1,4],[3,0,0,4,2,4],[4,5,4,5,3,2],[4,1,2,3,4,5],[0,4,3,1,5,3]]"

@[implicit_reducible]
def «OneVariable M13910» : Magma (Fin 4) where
  op := finOpTable "[[2,0,3,2],[0,1,2,3],[3,2,0,0],[1,3,1,3]]"

@[implicit_reducible]
def «OneVariable M13910^op» : Magma (Fin 4) where
  op := finOpTable "[[2,0,3,1],[0,1,2,3],[3,2,0,1],[2,3,0,3]]"

@[implicit_reducible]
def «OneVariable M13916» : Magma (Fin 5) where
  op := finOpTable "[[3,3,0,1,2],[2,1,1,2,1],[0,2,2,3,1],[4,2,3,0,0],[2,2,1,2,4]]"

@[implicit_reducible]
def «OneVariable M13916^op» : Magma (Fin 5) where
  op := finOpTable "[[3,2,0,4,2],[3,1,2,2,2],[0,1,2,3,1],[1,2,3,0,2],[2,1,1,0,4]]"

@[implicit_reducible]
def «OneVariable M13917» : Magma (Fin 6) where
  op := finOpTable "[[1,4,3,0,1,3],[2,0,0,1,3,1],[3,3,5,2,5,4],[0,1,2,3,5,5],[3,5,3,2,4,3],[2,3,0,5,3,2]]"

@[implicit_reducible]
def «OneVariable M13917^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,3,2],[4,0,3,1,5,3],[3,0,5,2,3,0],[0,1,2,3,2,5],[1,3,5,5,4,3],[3,1,4,5,3,2]]"

@[implicit_reducible]
def «OneVariable M13918» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,0,5,1],[2,0,0,4,1,4],[3,4,2,4,2,4],[0,5,4,5,3,1],[0,1,4,3,4,5],[4,4,3,2,5,3]]"

@[implicit_reducible]
def «OneVariable M13918^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,0,4],[5,0,4,5,1,4],[3,0,2,4,4,3],[0,4,4,5,3,2],[5,1,2,3,4,5],[1,4,4,1,5,3]]"

@[implicit_reducible]
def «OneVariable M13922» : Magma (Fin 5) where
  op := finOpTable "[[4,4,3,0,1],[4,1,0,2,3],[3,3,2,2,0],[0,2,2,3,4],[2,3,0,4,0]]"

@[implicit_reducible]
def «OneVariable M13922^op» : Magma (Fin 5) where
  op := finOpTable "[[4,4,3,0,2],[4,1,3,2,3],[3,0,2,2,0],[0,2,2,3,4],[1,3,0,4,0]]"

@[implicit_reducible]
def «OneVariable M13924» : Magma (Fin 6) where
  op := finOpTable "[[1,4,3,3,1,0],[2,0,0,1,3,4],[5,0,2,2,5,3],[0,1,0,3,4,5],[1,3,5,4,5,2],[0,4,3,5,1,4]]"

@[implicit_reducible]
def «OneVariable M13924^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,5,0,1,0],[4,0,0,1,3,4],[3,0,2,0,5,3],[3,1,2,3,4,5],[1,3,5,4,5,1],[0,4,3,5,2,4]]"

@[implicit_reducible]
def «OneVariable M13929» : Magma (Fin 5) where
  op := finOpTable "[[4,0,4,1,3],[0,1,2,3,4],[1,2,2,2,0],[4,1,2,3,1],[2,4,1,0,0]]"

@[implicit_reducible]
def «OneVariable M13931» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,3,0,1],[5,0,0,1,3,3],[1,3,2,4,0,3],[0,1,0,3,2,2],[0,4,3,2,4,2],[4,0,4,5,1,5]]"

@[implicit_reducible]
def «OneVariable M13931^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,1,0,0,4],[2,0,3,1,4,0],[3,0,2,0,3,4],[3,1,4,3,2,5],[0,3,0,2,4,1],[1,3,3,2,2,5]]"

@[implicit_reducible]
def «OneVariable M13932» : Magma (Fin 5) where
  op := finOpTable "[[0,1,2,3,0],[1,3,3,4,3],[3,0,2,0,3],[3,2,1,1,1],[0,0,0,0,4]]"

@[implicit_reducible]
def «OneVariable M13932^op» : Magma (Fin 5) where
  op := finOpTable "[[0,1,3,3,0],[1,3,0,2,0],[2,3,2,1,0],[3,4,0,1,0],[0,3,3,1,4]]"

@[implicit_reducible]
def «OneVariable M13933» : Magma (Fin 6) where
  op := finOpTable "[[1,2,1,0,0,1],[5,0,0,3,1,0],[3,4,2,1,2,4],[0,3,5,5,4,2],[1,1,4,3,4,5],[4,4,3,2,5,3]]"

@[implicit_reducible]
def «OneVariable M13933^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,0,1,4],[2,0,4,3,1,4],[1,0,2,5,4,3],[0,3,1,5,3,2],[0,1,2,4,4,5],[1,0,4,2,5,3]]"

@[implicit_reducible]
def «OneVariable M13935» : Magma (Fin 6) where
  op := finOpTable "[[1,2,1,2,0,1],[5,0,0,1,4,0],[3,3,2,2,1,3],[0,1,3,3,3,5],[0,4,5,5,5,2],[4,3,4,5,2,4]]"

@[implicit_reducible]
def «OneVariable M13935^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,0,0,4],[2,0,3,1,4,3],[1,0,2,3,5,4],[2,1,2,3,5,5],[0,4,1,3,5,2],[1,0,3,5,2,4]]"

@[implicit_reducible]
def «OneVariable M13936» : Magma (Fin 5) where
  op := finOpTable "[[4,4,4,0,2],[3,1,2,3,0],[4,1,2,4,3],[0,0,4,3,4],[1,0,0,4,0]]"

@[implicit_reducible]
def «OneVariable M13936^op» : Magma (Fin 5) where
  op := finOpTable "[[4,3,4,0,1],[4,1,1,0,0],[4,2,2,4,0],[0,3,4,3,4],[2,0,3,4,0]]"

@[implicit_reducible]
def «OneVariable M13943» : Magma (Fin 6) where
  op := finOpTable "[[0,3,5,5,4,4],[3,5,3,1,1,2],[3,4,2,5,0,4],[1,1,5,4,2,3],[4,5,0,2,3,5],[4,0,4,3,5,1]]"

@[implicit_reducible]
def «OneVariable M13943^op» : Magma (Fin 6) where
  op := finOpTable "[[0,3,3,1,4,4],[3,5,4,1,5,0],[5,3,2,5,0,4],[5,1,5,4,2,3],[4,1,0,2,3,5],[4,2,4,3,5,1]]"

@[implicit_reducible]
def «OneVariable M13956» : Magma (Fin 5) where
  op := finOpTable "[[0,1,2,3,4],[1,1,0,4,0],[0,2,2,0,3],[3,0,4,4,2],[4,3,0,1,3]]"

@[implicit_reducible]
def «OneVariable M13958» : Magma (Fin 6) where
  op := finOpTable "[[1,4,3,3,1,0],[2,0,0,3,3,1],[1,5,2,4,4,5],[0,1,2,3,2,4],[5,0,3,2,4,5],[0,1,5,2,5,5]]"

@[implicit_reducible]
def «OneVariable M13958^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,1,0,5,0],[4,0,5,1,0,1],[3,0,2,2,3,5],[3,3,4,3,2,2],[1,3,4,2,4,5],[0,1,5,4,5,5]]"

@[implicit_reducible]
def «OneVariable M13963» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,5,1],[5,0,0,4,1,4],[3,4,2,4,4,4],[0,5,4,5,3,2],[0,1,2,3,4,5],[4,4,3,1,5,3]]"

@[implicit_reducible]
def «OneVariable M13963^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,0,0,4],[2,0,4,5,1,4],[3,0,2,4,2,3],[0,4,4,5,3,1],[5,1,4,3,4,5],[1,4,4,2,5,3]]"

@[implicit_reducible]
def «OneVariable M13965» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,3,0,1],[5,0,0,5,1,4],[4,0,2,4,4,3],[0,5,4,5,3,2],[0,1,0,3,4,5],[1,4,3,1,5,3]]"

@[implicit_reducible]
def «OneVariable M13965^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,4,0,0,1],[2,0,0,5,1,4],[3,0,2,4,0,3],[3,5,4,5,3,1],[0,1,4,3,4,5],[1,4,3,2,5,3]]"

@[implicit_reducible]
def «OneVariable M13967» : Magma (Fin 6) where
  op := finOpTable "[[1,4,1,2,1,0],[2,0,0,1,0,5],[3,3,4,4,3,2],[0,1,5,3,5,5],[5,3,3,2,2,4],[0,5,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M13967^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,5,0],[4,0,3,1,3,5],[1,0,4,5,3,2],[2,1,4,3,2,3],[1,0,3,5,2,4],[0,5,2,5,4,5]]"

@[implicit_reducible]
def «OneVariable M13968» : Magma (Fin 5) where
  op := finOpTable "[[1,4,0,1,1],[3,0,1,0,0],[0,1,2,3,2],[1,2,2,3,3],[2,0,4,1,4]]"

@[implicit_reducible]
def «OneVariable M13968^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,0,1,2],[4,0,1,2,0],[0,1,2,2,4],[1,0,3,3,1],[1,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M13969» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,0,0],[3,0,1,0,1],[3,4,2,1,0],[4,4,4,3,3],[0,1,0,4,4]]"

@[implicit_reducible]
def «OneVariable M13969^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,3,4,0],[2,0,4,4,1],[1,1,2,4,0],[0,0,1,3,4],[0,1,0,3,4]]"

@[implicit_reducible]
def «OneVariable M13970» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,4,0,1],[2,0,0,4,1,4],[4,4,2,4,5,4],[0,5,4,5,3,1],[0,1,0,3,4,5],[4,4,3,2,5,3]]"

@[implicit_reducible]
def «OneVariable M13970^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,4,0,0,4],[5,0,4,5,1,4],[3,0,2,4,0,3],[4,4,4,5,3,2],[0,1,5,3,4,5],[1,4,4,1,5,3]]"

@[implicit_reducible]
def «OneVariable M13971» : Magma (Fin 6) where
  op := finOpTable "[[1,2,1,0,0,4],[5,0,3,1,3,0],[3,3,4,2,5,4],[1,1,2,3,4,4],[0,2,1,4,2,3],[4,3,3,4,3,5]]"

@[implicit_reducible]
def «OneVariable M13971^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,1,0,4],[2,0,3,1,2,3],[1,3,4,2,1,3],[0,1,2,3,4,4],[0,3,5,4,2,3],[4,0,4,4,3,5]]"

@[implicit_reducible]
def «OneVariable M13972» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,0,1],[5,0,0,4,1,4],[4,4,2,4,3,4],[0,5,4,5,3,2],[4,1,4,3,4,5],[3,4,3,1,5,3]]"

@[implicit_reducible]
def «OneVariable M13972^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,4,0,4,3],[2,0,4,5,1,4],[3,0,2,4,4,3],[0,4,4,5,3,1],[0,1,3,3,4,5],[1,4,4,2,5,3]]"

@[implicit_reducible]
def «OneVariable M13973» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,3,0,1],[5,0,0,4,1,4],[4,4,2,4,4,4],[0,5,0,5,3,2],[0,1,2,3,4,5],[4,4,3,1,5,3]]"

@[implicit_reducible]
def «OneVariable M13973^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,4,0,0,4],[2,0,4,5,1,4],[3,0,2,0,2,3],[3,4,4,5,3,1],[0,1,4,3,4,5],[1,4,4,2,5,3]]"

@[implicit_reducible]
def «OneVariable M13974» : Magma (Fin 6) where
  op := finOpTable "[[1,2,1,0,1,0],[4,0,0,1,0,0],[3,3,2,3,3,3],[3,1,4,3,4,5],[5,3,5,4,5,2],[0,4,4,5,2,4]]"

@[implicit_reducible]
def «OneVariable M13974^op» : Magma (Fin 6) where
  op := finOpTable "[[1,4,3,3,5,0],[2,0,3,1,3,4],[1,0,2,4,5,4],[0,1,3,3,4,5],[1,0,3,4,5,2],[0,0,3,5,2,4]]"

@[implicit_reducible]
def «OneVariable M13976» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,2,0],[2,0,4,4,1],[3,4,3,1,2],[0,4,1,2,3],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M13976^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,0],[2,0,4,4,1],[4,4,3,1,2],[2,4,1,2,3],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M13985» : Magma (Fin 6) where
  op := finOpTable "[[1,2,4,3,0,4],[5,0,3,1,4,3],[3,0,2,4,5,5],[0,1,0,3,1,1],[0,5,3,5,4,4],[1,3,5,3,0,5]]"

@[implicit_reducible]
def «OneVariable M13985^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,0,0,1],[2,0,0,1,5,3],[4,3,2,0,3,5],[3,1,4,3,5,3],[0,4,5,1,4,0],[4,3,5,1,4,5]]"

@[implicit_reducible]
def «OneVariable M13991» : Magma (Fin 6) where
  op := finOpTable "[[1,4,5,2,1,0],[2,0,0,1,3,4],[3,0,2,2,5,3],[0,1,0,3,4,5],[1,3,5,4,5,2],[0,4,3,5,1,4]]"

@[implicit_reducible]
def «OneVariable M13991^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,1,0],[4,0,0,1,3,4],[5,0,2,0,5,3],[2,1,2,3,4,5],[1,3,5,4,5,1],[0,4,3,5,2,4]]"

@[implicit_reducible]
def «OneVariable M13993» : Magma (Fin 6) where
  op := finOpTable "[[1,2,1,3,0,4],[5,0,3,1,3,0],[3,0,2,4,0,2],[0,1,4,3,0,2],[0,1,2,3,4,3],[1,4,0,4,3,5]]"

@[implicit_reducible]
def «OneVariable M13993^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,0,0,1],[2,0,0,1,1,4],[1,3,2,4,2,0],[3,1,4,3,3,4],[0,3,0,0,4,3],[4,0,2,2,3,5]]"

@[implicit_reducible]
def «OneVariable M13994» : Magma (Fin 6) where
  op := finOpTable "[[4,5,4,0,1,0],[5,2,4,1,3,3],[2,5,1,2,0,3],[3,1,2,3,4,4],[1,3,3,4,0,3],[0,3,3,5,3,5]]"

@[implicit_reducible]
def «OneVariable M13994^op» : Magma (Fin 6) where
  op := finOpTable "[[4,5,2,3,1,0],[5,2,5,1,3,3],[4,4,1,2,3,3],[0,1,2,3,4,5],[1,3,0,4,0,3],[0,3,3,4,3,5]]"

@[implicit_reducible]
def «OneVariable M13995» : Magma (Fin 6) where
  op := finOpTable "[[0,4,3,4,4,0],[5,3,5,2,1,1],[5,5,2,4,0,3],[4,0,4,1,3,5],[4,4,0,3,5,2],[3,1,3,5,2,4]]"

@[implicit_reducible]
def «OneVariable M13995^op» : Magma (Fin 6) where
  op := finOpTable "[[0,5,5,4,4,3],[4,3,5,0,4,1],[3,5,2,4,0,3],[4,2,4,1,3,5],[4,1,0,3,5,2],[0,1,3,5,2,4]]"

@[implicit_reducible]
def «OneVariable M13997» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,0,0,4],[2,0,4,5,1,4],[4,0,2,4,3,3],[3,4,4,5,3,1],[0,1,3,3,4,5],[1,4,4,2,5,3]]"

@[implicit_reducible]
def «OneVariable M13997^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,4,3,0,1],[5,0,0,4,1,4],[3,4,2,4,3,4],[0,5,4,5,3,2],[0,1,3,3,4,5],[4,4,3,1,5,3]]"

@[implicit_reducible]
def «OneVariable M13998» : Magma (Fin 6) where
  op := finOpTable "[[1,4,3,0,1,0],[2,0,0,1,3,4],[5,0,2,2,5,3],[4,1,0,3,4,5],[1,3,5,4,5,2],[0,4,3,5,1,4]]"

@[implicit_reducible]
def «OneVariable M13998^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,5,4,1,0],[4,0,0,1,3,4],[3,0,2,0,5,3],[0,1,2,3,4,5],[1,3,5,4,5,1],[0,4,3,5,2,4]]"

@[implicit_reducible]
def «OneVariable M14000» : Magma (Fin 6) where
  op := finOpTable "[[1,4,5,2,1,0],[2,0,0,1,3,3],[3,3,2,0,3,3],[0,1,4,3,4,5],[5,3,5,4,5,2],[0,4,3,5,1,4]]"

@[implicit_reducible]
def «OneVariable M14000^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,5,0],[4,0,3,1,3,4],[5,0,2,4,5,3],[2,1,0,3,4,5],[1,3,3,4,5,1],[0,3,3,5,2,4]]"

@[implicit_reducible]
def «OneVariable M14008» : Magma (Fin 6) where
  op := finOpTable "[[1,5,1,4,0,4],[2,0,3,1,0,0],[3,0,2,2,3,4],[0,1,2,3,0,5],[0,5,5,2,4,0],[1,3,3,5,2,5]]"

@[implicit_reducible]
def «OneVariable M14008^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,0,1],[5,0,0,1,5,3],[1,3,2,2,5,3],[4,1,2,3,2,5],[0,0,3,0,4,2],[4,0,4,5,0,5]]"

@[implicit_reducible]
def «OneVariable M14009» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,5,0],[4,0,5,1,3,1],[5,5,2,3,3,3],[4,3,3,3,4,5],[5,5,3,4,5,2],[0,1,3,5,2,4]]"

@[implicit_reducible]
def «OneVariable M14009^op» : Magma (Fin 6) where
  op := finOpTable "[[1,4,5,4,5,0],[2,0,5,3,5,1],[3,5,2,3,3,3],[0,1,3,3,4,5],[5,3,3,4,5,2],[0,1,3,5,2,4]]"

@[implicit_reducible]
def «OneVariable M14010» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,0,1],[5,0,0,1,4,3],[4,3,2,4,3,2],[2,1,0,3,0,3],[0,3,3,4,4,4],[4,3,0,5,2,5]]"

@[implicit_reducible]
def «OneVariable M14010^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,4,2,0,4],[2,0,3,1,3,3],[3,0,2,0,3,0],[0,1,4,3,4,5],[0,4,3,0,4,2],[1,3,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M14016» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,1,0],[3,0,0,4,1],[4,1,2,2,2],[0,4,3,3,3],[0,1,4,4,4]]"

@[implicit_reducible]
def «OneVariable M14016^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,4,0,0],[2,0,1,4,1],[3,0,2,3,4],[1,4,2,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M14017» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,0,1],[4,0,0,1,0],[3,1,2,2,2],[3,3,3,3,3],[0,3,4,4,4]]"

@[implicit_reducible]
def «OneVariable M14017^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,3,0],[2,0,1,3,3],[1,0,2,3,4],[0,1,2,3,4],[1,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M14021» : Magma (Fin 4) where
  op := finOpTable "[[2,3,1,0],[0,1,2,2],[1,3,0,2],[0,2,2,3]]"

@[implicit_reducible]
def «OneVariable M14021^op» : Magma (Fin 4) where
  op := finOpTable "[[2,0,1,0],[3,1,3,2],[1,2,0,2],[0,2,2,3]]"

@[implicit_reducible]
def «OneVariable M14025» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,4,0],[3,0,4,4,1],[1,1,2,3,4],[0,0,2,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M14025^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,1,0,0],[2,0,1,0,1],[3,4,2,2,2],[4,4,3,3,3],[0,1,4,4,4]]"

@[implicit_reducible]
def «OneVariable M14028» : Magma (Fin 5) where
  op := finOpTable "[[4,4,3,0,1],[2,1,2,3,4],[0,2,2,4,1],[0,3,4,3,4],[2,3,0,4,0]]"

@[implicit_reducible]
def «OneVariable M14028^op» : Magma (Fin 5) where
  op := finOpTable "[[4,2,0,0,2],[4,1,2,3,3],[3,2,2,4,0],[0,3,4,3,4],[1,4,1,4,0]]"

@[implicit_reducible]
def «OneVariable M14029» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,0,1],[2,0,0,1,3],[0,0,2,3,4],[3,0,2,3,3],[1,1,4,3,4]]"

@[implicit_reducible]
def «OneVariable M14029^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,0,3,1],[4,0,0,0,1],[3,0,2,2,4],[0,1,3,3,3],[1,3,4,3,4]]"

@[implicit_reducible]
def «OneVariable M14034» : Magma (Fin 5) where
  op := finOpTable "[[4,3,3,0,2],[0,1,2,2,3],[3,1,2,1,4],[0,2,3,3,4],[1,3,3,4,0]]"

@[implicit_reducible]
def «OneVariable M14034^op» : Magma (Fin 5) where
  op := finOpTable "[[4,0,3,0,1],[3,1,1,2,3],[3,2,2,3,3],[0,2,1,3,4],[2,3,4,4,0]]"

@[implicit_reducible]
def «OneVariable M14036» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,4,0],[3,0,4,4,1],[4,1,2,0,0],[0,4,4,3,2],[0,1,2,1,4]]"

@[implicit_reducible]
def «OneVariable M14036^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,4,0,0],[2,0,1,4,1],[3,4,2,4,2],[4,4,0,3,1],[0,1,0,2,4]]"

@[implicit_reducible]
def «OneVariable M14037» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,0,0,4],[2,0,3,1,1,3],[0,4,2,4,3,4],[3,1,5,3,2,5],[0,1,0,2,4,1],[4,1,0,4,1,5]]"

@[implicit_reducible]
def «OneVariable M14037^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,0,3,0,4],[5,0,4,1,1,1],[3,3,2,5,0,0],[0,1,4,3,2,4],[0,1,3,2,4,1],[4,3,4,5,1,5]]"

@[implicit_reducible]
def «OneVariable M14040» : Magma (Fin 5) where
  op := finOpTable "[[4,4,3,0,1],[3,1,1,1,4],[0,2,2,0,3],[0,3,4,3,4],[2,3,0,4,0]]"

@[implicit_reducible]
def «OneVariable M14040^op» : Magma (Fin 5) where
  op := finOpTable "[[4,3,0,0,2],[4,1,2,3,3],[3,1,2,4,0],[0,1,0,3,4],[1,4,3,4,0]]"

@[implicit_reducible]
def «OneVariable M14041» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,0,0,1],[2,0,0,1,1,3],[0,4,2,2,2,2],[3,3,3,3,3,3],[0,1,4,4,4,4],[4,1,5,5,5,5]]"

@[implicit_reducible]
def «OneVariable M14041^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,0,3,0,4],[5,0,4,3,1,1],[3,0,2,3,4,5],[0,1,2,3,4,5],[0,1,2,3,4,5],[1,3,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M14042» : Magma (Fin 6) where
  op := finOpTable "[[1,2,1,0,0,4],[5,0,3,1,0,0],[3,1,2,2,2,2],[3,1,3,3,0,3],[0,4,4,0,4,4],[0,3,5,5,5,5]]"

@[implicit_reducible]
def «OneVariable M14042^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,3,0,0],[2,0,1,1,4,3],[1,3,2,3,4,5],[0,1,2,3,0,5],[0,0,2,0,4,5],[4,0,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M14047» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,1,0],[3,0,0,4,1],[3,1,2,2,2],[0,2,3,3,3],[0,1,4,4,4]]"

@[implicit_reducible]
def «OneVariable M14047^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,3,0,0],[2,0,1,2,1],[4,0,2,3,4],[1,4,2,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M14049» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,0],[4,0,1,1,3],[4,1,2,0,1],[3,2,1,3,1],[0,2,1,2,4]]"

@[implicit_reducible]
def «OneVariable M14049^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,4,3,0],[2,0,1,2,2],[3,1,2,1,1],[0,1,0,3,2],[0,3,1,1,4]]"

@[implicit_reducible]
def «OneVariable M14051» : Magma (Fin 5) where
  op := finOpTable "[[1,3,2,4,0],[2,0,4,3,1],[0,4,2,0,0],[4,1,4,3,2],[0,1,2,1,4]]"

@[implicit_reducible]
def «OneVariable M14051^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,0,4,0],[3,0,4,1,1],[2,4,2,4,2],[4,3,0,3,1],[0,1,0,2,4]]"

@[implicit_reducible]
def «OneVariable M14053» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,0,0],[4,0,1,2,2],[3,1,2,0,1],[3,2,1,3,1],[0,2,3,2,4]]"

@[implicit_reducible]
def «OneVariable M14053^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,3,0],[2,0,1,2,2],[4,1,2,1,3],[0,2,0,3,2],[0,2,1,1,4]]"

@[implicit_reducible]
def «OneVariable M14056» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,0,1],[5,0,0,1,1,4],[4,1,2,2,0,0],[3,1,3,3,0,0],[0,4,4,4,4,4],[0,3,5,5,5,5]]"

@[implicit_reducible]
def «OneVariable M14056^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,4,3,0,0],[2,0,1,1,4,3],[3,0,2,3,4,5],[0,1,2,3,4,5],[0,1,0,0,4,5],[1,4,0,0,4,5]]"

@[implicit_reducible]
def «OneVariable M14057» : Magma (Fin 6) where
  op := finOpTable "[[1,2,4,0,0,1],[5,0,0,1,3,3],[3,1,2,2,2,2],[3,1,3,3,3,0],[0,4,4,4,4,4],[0,3,5,5,5,5]]"

@[implicit_reducible]
def «OneVariable M14057^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,3,0,0],[2,0,1,1,4,3],[4,0,2,3,4,5],[0,1,2,3,4,5],[0,3,2,3,4,5],[1,3,2,0,4,5]]"

@[implicit_reducible]
def «OneVariable M14058» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[2,0,3,1],[0,1,2,0],[3,0,0,3]]"

@[implicit_reducible]
def «OneVariable M14058^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,3],[2,0,1,0],[3,3,2,0],[0,1,0,3]]"

@[implicit_reducible]
def «OneVariable M14061» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,4,0],[0,1,4,2,4],[1,4,0,4,2],[1,0,2,3,2],[0,1,2,1,4]]"

@[implicit_reducible]
def «OneVariable M14061^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,1,1,0],[4,1,4,0,1],[3,4,0,2,2],[4,2,4,3,1],[0,4,2,2,4]]"

@[implicit_reducible]
def «OneVariable M14064» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,5,0],[4,0,3,1,3,3],[1,1,2,3,5,0],[3,1,5,3,5,3],[0,0,3,5,4,0],[0,0,3,4,4,5]]"

@[implicit_reducible]
def «OneVariable M14064^op» : Magma (Fin 6) where
  op := finOpTable "[[1,4,1,3,0,0],[2,0,1,1,0,0],[3,3,2,5,3,3],[0,1,3,3,5,4],[5,3,5,5,4,4],[0,3,0,3,0,5]]"

@[implicit_reducible]
def «OneVariable M14065» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,0,0,4],[2,0,4,3,1,4],[0,0,2,3,4,5],[2,4,0,3,4,5],[0,1,0,3,4,0],[1,1,0,3,0,5]]"

@[implicit_reducible]
def «OneVariable M14065^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,0,2,0,1],[5,0,0,4,1,1],[3,4,2,0,0,0],[0,3,3,3,3,3],[0,1,4,4,4,0],[4,4,5,5,0,5]]"

@[implicit_reducible]
def «OneVariable M14069» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,5,0],[4,0,3,1,3,5],[5,1,2,4,3,5],[4,1,0,3,1,0],[0,3,1,0,4,1],[0,2,0,4,1,5]]"

@[implicit_reducible]
def «OneVariable M14069^op» : Magma (Fin 6) where
  op := finOpTable "[[1,4,5,4,0,0],[2,0,1,1,3,2],[3,3,2,0,1,0],[0,1,4,3,0,4],[5,3,3,1,4,1],[0,5,5,0,1,5]]"

@[implicit_reducible]
def «OneVariable M14071» : Magma (Fin 6) where
  op := finOpTable "[[1,2,5,0,5,0],[4,0,3,1,3,5],[3,1,2,5,0,0],[4,1,0,3,1,5],[0,3,0,1,4,3],[0,4,4,4,1,5]]"

@[implicit_reducible]
def «OneVariable M14071^op» : Magma (Fin 6) where
  op := finOpTable "[[1,4,3,4,0,0],[2,0,1,1,3,4],[5,3,2,0,0,4],[0,1,5,3,1,4],[5,3,0,1,4,1],[0,5,0,5,3,5]]"

@[implicit_reducible]
def «OneVariable M14072» : Magma (Fin 4) where
  op := finOpTable "[[3,2,2,3],[2,2,3,2],[1,0,1,1],[0,1,1,0]]"

@[implicit_reducible]
def «OneVariable M14072^op» : Magma (Fin 4) where
  op := finOpTable "[[3,2,1,0],[2,2,0,1],[2,3,1,1],[3,2,1,0]]"

@[implicit_reducible]
def «OneVariable M14078» : Magma (Fin 5) where
  op := finOpTable "[[3,1,4,1,0],[0,1,2,4,4],[4,1,2,3,2],[2,4,2,0,3],[0,1,0,3,4]]"

@[implicit_reducible]
def «OneVariable M14078^op» : Magma (Fin 5) where
  op := finOpTable "[[3,0,4,2,0],[1,1,1,4,1],[4,2,2,2,0],[1,4,3,0,3],[0,4,2,3,4]]"

@[implicit_reducible]
def «OneVariable M14082» : Magma (Fin 5) where
  op := finOpTable "[[3,3,4,1,0],[0,1,1,4,1],[1,4,2,3,4],[2,4,0,0,3],[0,1,1,3,4]]"

@[implicit_reducible]
def «OneVariable M14082^op» : Magma (Fin 5) where
  op := finOpTable "[[3,0,1,2,0],[3,1,4,4,1],[4,1,2,0,1],[1,4,3,0,3],[0,1,4,3,4]]"

@[implicit_reducible]
def «OneVariable M14085» : Magma (Fin 5) where
  op := finOpTable "[[1,4,4,0,0],[2,0,1,2,2],[3,1,2,0,0],[3,2,1,3,2],[0,2,3,0,4]]"

@[implicit_reducible]
def «OneVariable M14085^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,3,0],[4,0,1,2,2],[4,1,2,1,3],[0,2,0,3,0],[0,2,0,2,4]]"

@[implicit_reducible]
def «OneVariable M14090» : Magma (Fin 5) where
  op := finOpTable "[[3,3,4,1,0],[0,1,1,4,1],[4,2,2,3,2],[2,4,0,0,3],[0,4,4,3,4]]"

@[implicit_reducible]
def «OneVariable M14090^op» : Magma (Fin 5) where
  op := finOpTable "[[3,0,4,2,0],[3,1,2,4,4],[4,1,2,0,4],[1,4,3,0,3],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M14091» : Magma (Fin 6) where
  op := finOpTable "[[1,5,3,0,0,1],[2,0,0,1,3,3],[4,1,2,0,0,4],[3,1,2,3,3,5],[0,3,2,0,4,3],[0,3,3,5,3,5]]"

@[implicit_reducible]
def «OneVariable M14091^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,4,3,0,0],[5,0,1,1,3,3],[3,0,2,2,2,3],[0,1,0,3,0,5],[0,3,0,3,4,3],[1,3,4,5,3,5]]"

@[implicit_reducible]
def «OneVariable M14092» : Magma (Fin 6) where
  op := finOpTable "[[1,4,5,0,1,0],[2,0,0,1,3,0],[3,1,2,0,0,2],[3,1,3,3,3,3],[0,3,4,0,4,4],[0,5,5,5,5,5]]"

@[implicit_reducible]
def «OneVariable M14092^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,3,0,0],[4,0,1,1,3,5],[5,0,2,3,4,5],[0,1,0,3,0,5],[1,3,0,3,4,5],[0,0,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M14098» : Magma (Fin 5) where
  op := finOpTable "[[3,4,1,1,0],[0,1,2,4,4],[4,1,2,3,1],[2,2,4,0,3],[0,2,4,3,4]]"

@[implicit_reducible]
def «OneVariable M14098^op» : Magma (Fin 5) where
  op := finOpTable "[[3,0,4,2,0],[4,1,1,2,2],[1,2,2,4,4],[1,4,3,0,3],[0,4,1,3,4]]"

@[implicit_reducible]
def «OneVariable M14102» : Magma (Fin 5) where
  op := finOpTable "[[3,3,4,2,0],[2,1,1,3,4],[0,4,2,4,2],[1,4,0,0,3],[0,4,2,3,4]]"

@[implicit_reducible]
def «OneVariable M14102^op» : Magma (Fin 5) where
  op := finOpTable "[[3,2,0,1,0],[3,1,4,4,4],[4,1,2,0,2],[2,3,4,0,3],[0,4,2,3,4]]"

@[implicit_reducible]
def «OneVariable M14108» : Magma (Fin 5) where
  op := finOpTable "[[3,3,4,2,0],[4,1,1,3,4],[0,2,2,4,4],[1,4,0,0,3],[0,4,4,3,4]]"

@[implicit_reducible]
def «OneVariable M14108^op» : Magma (Fin 5) where
  op := finOpTable "[[3,4,0,1,0],[3,1,2,4,4],[4,1,2,0,4],[2,3,4,0,3],[0,4,4,3,4]]"

@[implicit_reducible]
def «OneVariable M14109» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,1,0],[4,0,0,1,5,1],[0,3,2,4,5,2],[3,1,4,3,0,2],[5,1,2,3,4,5],[0,5,2,1,1,5]]"

@[implicit_reducible]
def «OneVariable M14109^op» : Magma (Fin 6) where
  op := finOpTable "[[1,4,0,3,5,0],[2,0,3,1,1,5],[3,0,2,4,2,2],[0,1,4,3,3,1],[1,5,5,0,4,1],[0,1,2,2,5,5]]"

@[implicit_reducible]
def «OneVariable M14110» : Magma (Fin 6) where
  op := finOpTable "[[1,5,1,0,0,4],[2,0,3,1,1,0],[3,1,2,2,2,2],[3,1,0,3,3,3],[0,4,0,4,4,4],[0,4,0,5,5,5]]"

@[implicit_reducible]
def «OneVariable M14110^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,3,0,0],[5,0,1,1,4,4],[1,3,2,0,0,0],[0,1,2,3,4,5],[0,1,2,3,4,5],[4,0,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M14115» : Magma (Fin 5) where
  op := finOpTable "[[4,3,3,0,1],[0,1,3,2,2],[1,3,2,2,4],[0,0,2,3,4],[2,3,3,4,0]]"

@[implicit_reducible]
def «OneVariable M14115^op» : Magma (Fin 5) where
  op := finOpTable "[[4,0,1,0,2],[3,1,3,0,3],[3,3,2,2,3],[0,2,2,3,4],[1,2,4,4,0]]"

@[implicit_reducible]
def «OneVariable M14120» : Magma (Fin 5) where
  op := finOpTable "[[3,4,4,2,0],[3,1,2,3,4],[0,4,2,0,2],[1,4,4,0,3],[0,4,2,3,4]]"

@[implicit_reducible]
def «OneVariable M14120^op» : Magma (Fin 5) where
  op := finOpTable "[[3,3,0,1,0],[4,1,4,4,4],[4,2,2,4,2],[2,3,0,0,3],[0,4,2,3,4]]"

@[implicit_reducible]
def «OneVariable M14121» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,5,0],[4,0,3,1,5,1],[0,0,2,3,4,5],[2,1,0,3,4,5],[1,1,0,3,4,4],[0,0,1,3,4,5]]"

@[implicit_reducible]
def «OneVariable M14121^op» : Magma (Fin 6) where
  op := finOpTable "[[1,4,0,2,1,0],[2,0,0,1,1,0],[3,3,2,0,0,1],[0,1,3,3,3,3],[5,5,4,4,4,4],[0,1,5,5,4,5]]"

@[implicit_reducible]
def «OneVariable M14122» : Magma (Fin 6) where
  op := finOpTable "[[1,4,3,0,5,0],[2,0,5,1,3,1],[1,1,2,3,0,5],[2,4,0,3,0,5],[0,0,2,3,4,5],[0,1,2,3,4,5]]"

@[implicit_reducible]
def «OneVariable M14122^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,1,2,0,0],[4,0,1,4,0,1],[3,5,2,0,2,2],[0,1,3,3,3,3],[5,3,0,0,4,4],[0,1,5,5,5,5]]"

@[implicit_reducible]
def «OneVariable M14124» : Magma (Fin 5) where
  op := finOpTable "[[4,3,3,0,2],[3,1,0,2,4],[0,1,2,1,3],[0,4,1,3,4],[1,3,3,4,0]]"

@[implicit_reducible]
def «OneVariable M14124^op» : Magma (Fin 5) where
  op := finOpTable "[[4,3,0,0,1],[3,1,1,4,3],[3,0,2,1,3],[0,2,1,3,4],[2,4,3,4,0]]"

@[implicit_reducible]
def «OneVariable M14127» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,5,0],[4,0,3,1,3,5],[0,3,2,1,3,3],[4,1,0,3,1,5],[5,1,5,1,4,3],[0,0,0,4,1,5]]"

@[implicit_reducible]
def «OneVariable M14127^op» : Magma (Fin 6) where
  op := finOpTable "[[1,4,0,4,5,0],[2,0,3,1,1,0],[3,3,2,0,5,0],[0,1,1,3,1,4],[5,3,3,1,4,1],[0,5,3,5,3,5]]"

@[implicit_reducible]
def «OneVariable M14129» : Magma (Fin 6) where
  op := finOpTable "[[1,4,3,0,5,0],[2,0,3,1,3,5],[5,1,2,4,3,5],[4,1,0,3,5,1],[0,3,0,2,4,1],[0,4,4,4,1,5]]"

@[implicit_reducible]
def «OneVariable M14129^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,5,4,0,0],[4,0,1,1,3,4],[3,3,2,0,0,4],[0,1,4,3,2,4],[5,3,3,5,4,1],[0,5,5,1,1,5]]"

@[implicit_reducible]
def «OneVariable M14130» : Magma (Fin 6) where
  op := finOpTable "[[1,4,5,0,5,0],[2,0,3,1,3,1],[3,1,2,0,3,1],[3,1,0,3,1,1],[0,5,0,0,4,1],[0,2,1,2,3,5]]"

@[implicit_reducible]
def «OneVariable M14130^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,3,0,0],[4,0,1,1,5,2],[5,3,2,0,0,1],[0,1,0,3,0,2],[5,3,3,1,4,3],[0,1,1,1,1,5]]"

@[implicit_reducible]
def «OneVariable M14131» : Magma (Fin 3) where
  op := finOpTable "[[1,2,2],[2,0,2],[0,1,2]]"

@[implicit_reducible]
def «OneVariable M14131^op» : Magma (Fin 3) where
  op := finOpTable "[[1,2,0],[2,0,1],[2,2,2]]"

@[implicit_reducible]
def «OneVariable M14133» : Magma (Fin 3) where
  op := finOpTable "[[1,2,1],[2,0,0],[0,1,2]]"

@[implicit_reducible]
def «OneVariable M14133^op» : Magma (Fin 3) where
  op := finOpTable "[[1,2,0],[2,0,1],[1,0,2]]"

@[implicit_reducible]
def «OneVariable M14134» : Magma (Fin 4) where
  op := finOpTable "[[1,3,3,1],[2,0,0,3],[0,1,2,0],[0,1,0,3]]"

@[implicit_reducible]
def «OneVariable M14134^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,0],[3,0,1,1],[3,0,2,0],[1,3,0,3]]"

@[implicit_reducible]
def «OneVariable M14135» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,1],[3,0,0,2],[0,1,2,0],[0,1,0,3]]"

@[implicit_reducible]
def «OneVariable M14135^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,0],[2,0,1,1],[3,0,2,0],[1,2,0,3]]"

@[implicit_reducible]
def «OneVariable M14136» : Magma (Fin 4) where
  op := finOpTable "[[1,2,1,1],[3,0,0,0],[0,1,2,3],[0,1,1,3]]"

@[implicit_reducible]
def «OneVariable M14136^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,0],[2,0,1,1],[1,0,2,1],[1,0,3,3]]"

@[implicit_reducible]
def «OneVariable M14138» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,4,0],[3,0,4,2,1],[0,1,2,3,4],[0,1,3,3,2],[0,1,1,2,4]]"

@[implicit_reducible]
def «OneVariable M14138^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,0,0,0],[2,0,1,1,1],[3,4,2,3,1],[4,2,3,3,2],[0,1,4,2,4]]"

@[implicit_reducible]
def «OneVariable M14139» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,0,1],[2,0,0,1,3],[0,1,2,2,2],[2,3,3,3,3],[0,1,4,4,4]]"

@[implicit_reducible]
def «OneVariable M14139^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,0,2,0],[4,0,1,3,1],[3,0,2,3,4],[0,1,2,3,4],[1,3,2,3,4]]"

@[implicit_reducible]
def «OneVariable M14141» : Magma (Fin 5) where
  op := finOpTable "[[1,3,2,4,0],[2,0,4,3,1],[0,1,2,3,4],[0,1,2,3,2],[0,1,4,2,4]]"

@[implicit_reducible]
def «OneVariable M14141^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,0,0,0],[3,0,1,1,1],[2,4,2,2,4],[4,3,3,3,2],[0,1,4,2,4]]"

@[implicit_reducible]
def «OneVariable M14143» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,3],[4,0,3,1,3],[0,1,2,4,2],[0,1,2,3,4],[0,1,2,4,4]]"

@[implicit_reducible]
def «OneVariable M14143^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,0,0,0],[2,0,1,1,1],[3,3,2,2,2],[0,1,4,3,4],[3,3,2,4,4]]"

@[implicit_reducible]
def «OneVariable M14144» : Magma (Fin 6) where
  op := finOpTable "[[1,2,3,0,5,0],[4,0,3,1,3,5],[0,1,2,5,3,3],[4,1,4,3,1,5],[0,1,0,2,4,0],[0,4,4,4,3,5]]"

@[implicit_reducible]
def «OneVariable M14144^op» : Magma (Fin 6) where
  op := finOpTable "[[1,4,0,4,0,0],[2,0,1,1,1,4],[3,3,2,4,0,4],[0,1,5,3,2,4],[5,3,3,1,4,3],[0,5,3,5,0,5]]"

@[implicit_reducible]
def «OneVariable M14145» : Magma (Fin 6) where
  op := finOpTable "[[1,4,3,0,5,0],[2,0,3,1,3,5],[0,1,2,4,0,1],[4,1,4,3,2,5],[0,1,1,0,4,1],[0,2,0,4,3,5]]"

@[implicit_reducible]
def «OneVariable M14145^op» : Magma (Fin 6) where
  op := finOpTable "[[1,2,0,4,0,0],[4,0,1,1,1,2],[3,3,2,4,1,0],[0,1,4,3,0,4],[5,3,0,2,4,3],[0,5,1,5,1,5]]"

@[implicit_reducible]
def «OneVariable M14156» : Magma (Fin 3) where
  op := finOpTable "[[1,0,0],[2,1,1],[0,0,2]]"

@[implicit_reducible]
def «OneVariable M14156^op» : Magma (Fin 3) where
  op := finOpTable "[[1,2,0],[0,1,0],[0,1,2]]"

@[implicit_reducible]
def «OneVariable M14161» : Magma (Fin 4) where
  op := finOpTable "[[1,2,1,0],[3,0,1,0],[1,1,2,2],[0,0,1,3]]"

@[implicit_reducible]
def «OneVariable M14161^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,1,0],[2,0,1,0],[1,1,2,1],[0,0,2,3]]"

@[implicit_reducible]
def «OneVariable M14171» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,3,0],[4,1,0,3,0],[3,0,2,3,2],[0,1,2,3,4],[0,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M14171^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,0,0],[2,1,0,1,0],[1,0,2,2,2],[3,3,3,3,3],[0,0,2,4,4]]"

@[implicit_reducible]
def «OneVariable M14172» : Magma (Fin 6) where
  op := finOpTable "[[0,4,5,5,4,5],[4,5,1,3,0,1],[5,1,2,3,3,1],[5,1,3,4,3,0],[4,4,3,2,1,5],[5,2,1,5,4,3]]"

@[implicit_reducible]
def «OneVariable M14172^op» : Magma (Fin 6) where
  op := finOpTable "[[0,4,5,5,4,5],[4,5,1,1,4,2],[5,1,2,3,3,1],[5,3,3,4,2,5],[4,0,3,3,1,4],[5,1,1,0,5,3]]"

@[implicit_reducible]
def «OneVariable M14198» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[3,1,0,3],[3,0,2,1],[0,0,2,3]]"

@[implicit_reducible]
def «OneVariable M14198^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,3,0],[2,1,0,0],[3,0,2,2],[0,3,1,3]]"

@[implicit_reducible]
def «OneVariable M14202» : Magma (Fin 4) where
  op := finOpTable "[[0,2,1,1],[3,0,1,0],[3,1,2,2],[1,0,3,3]]"

@[implicit_reducible]
def «OneVariable M14202^op» : Magma (Fin 4) where
  op := finOpTable "[[0,3,3,1],[2,0,1,0],[1,1,2,3],[1,0,2,3]]"

@[implicit_reducible]
def «OneVariable M14209» : Magma (Fin 4) where
  op := finOpTable "[[2,2,1,0],[2,1,0,0],[3,0,2,1],[0,2,0,3]]"

@[implicit_reducible]
def «OneVariable M14209^op» : Magma (Fin 4) where
  op := finOpTable "[[2,2,3,0],[2,1,0,2],[1,0,2,0],[0,0,1,3]]"

@[implicit_reducible]
def «OneVariable M14224» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,1,0],[4,1,0,3,0],[1,0,2,4,0],[0,0,0,3,0],[0,0,0,3,4]]"

@[implicit_reducible]
def «OneVariable M14224^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,1,0,0],[2,1,0,0,0],[3,0,2,0,0],[1,3,4,3,3],[0,0,0,0,4]]"

@[implicit_reducible]
def «OneVariable M14227» : Magma (Fin 4) where
  op := finOpTable "[[1,2,1,0],[3,1,0,0],[1,3,2,0],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M14227^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,1,0],[2,1,3,0],[1,0,2,0],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M14229» : Magma (Fin 4) where
  op := finOpTable "[[1,2,1,0],[3,1,0,0],[3,3,2,0],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M14229^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,3,0],[2,1,3,0],[1,0,2,0],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M14234» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[3,1,0,0],[1,3,2,0],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M14234^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,1,0],[2,1,3,0],[3,0,2,0],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M14247» : Magma (Fin 8) where
  op := finOpTable "[[0,3,7,3,4,5,5,7],[7,1,7,3,4,6,5,2],[7,7,5,5,2,3,6,0],[0,4,5,3,4,2,6,6],[0,1,2,3,4,2,7,6],[5,6,4,2,2,6,1,7],[5,5,2,6,7,0,7,4],[7,2,1,6,6,5,3,2]]"

@[implicit_reducible]
def «OneVariable M14247^op» : Magma (Fin 8) where
  op := finOpTable "[[0,7,7,0,0,5,5,7],[3,1,7,4,1,6,5,2],[7,7,5,5,2,4,2,1],[3,3,5,3,3,2,6,6],[4,4,2,4,4,2,7,6],[5,6,3,2,2,6,0,5],[5,5,6,6,7,1,7,3],[7,2,0,6,6,7,4,2]]"

@[implicit_reducible]
def «OneVariable M14259» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,0,0],[4,1,0,0,0],[3,0,2,0,0],[4,0,0,3,2],[0,0,0,0,4]]"

@[implicit_reducible]
def «OneVariable M14259^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,4,0],[2,1,0,0,0],[4,0,2,0,0],[0,0,0,3,0],[0,0,0,2,4]]"

@[implicit_reducible]
def «OneVariable M14276» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,0,0],[4,1,0,4,0],[3,0,2,2,3],[3,0,2,3,3],[0,0,3,4,4]]"

@[implicit_reducible]
def «OneVariable M14276^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,3,0],[2,1,0,0,0],[1,0,2,2,3],[0,4,2,3,4],[0,0,3,3,4]]"

@[implicit_reducible]
def «OneVariable M14278» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,3,0],[4,1,0,3,0],[4,0,2,3,4],[0,1,2,3,4],[0,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M14278^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,4,0,0],[2,1,0,1,0],[3,0,2,2,2],[3,3,3,3,3],[0,0,4,4,4]]"

@[implicit_reducible]
def «OneVariable M14283» : Magma (Fin 8) where
  op := finOpTable "[[4,0,2,3,0,6,6,0],[0,2,1,1,3,1,1,3],[2,6,5,2,4,2,2,3],[3,4,2,3,4,2,6,4],[7,4,4,4,1,5,6,4],[5,1,3,3,5,0,5,3],[5,1,1,1,0,5,6,4],[0,4,1,3,0,2,6,7]]"

@[implicit_reducible]
def «OneVariable M14283^op» : Magma (Fin 8) where
  op := finOpTable "[[4,0,2,3,7,5,5,0],[0,2,6,4,4,1,1,4],[2,1,5,2,4,3,1,1],[3,1,2,3,4,3,1,3],[0,3,4,4,1,5,0,0],[6,1,2,2,5,0,5,2],[6,1,2,6,6,5,6,6],[0,3,3,4,4,3,4,7]]"

@[implicit_reducible]
def «OneVariable M14289» : Magma (Fin 8) where
  op := finOpTable "[[2,0,2,0,7,5,0,1],[0,1,0,4,4,6,6,3],[1,2,6,2,4,2,6,5],[0,6,2,3,5,5,2,7],[0,3,4,3,0,3,6,4],[5,1,2,5,4,4,1,7],[0,6,3,6,6,5,5,3],[4,2,0,7,4,7,4,7]]"

@[implicit_reducible]
def «OneVariable M14289^op» : Magma (Fin 8) where
  op := finOpTable "[[2,0,1,0,0,5,0,4],[0,1,2,6,3,1,6,2],[2,0,6,2,4,2,3,0],[0,4,2,3,3,5,6,7],[7,4,4,5,0,4,6,4],[5,6,2,5,3,4,5,7],[0,6,6,2,6,1,5,4],[1,3,5,7,4,7,3,7]]"

@[implicit_reducible]
def «OneVariable M14346» : Magma (Fin 8) where
  op := finOpTable "[[0,1,2,3,4,2,7,3],[5,1,2,3,6,5,6,7],[2,3,5,1,4,2,6,2],[4,3,3,2,0,3,6,7],[4,4,4,4,3,5,7,6],[2,5,0,3,5,7,6,5],[0,1,2,3,2,6,6,7],[0,5,2,7,7,1,7,4]]"

@[implicit_reducible]
def «OneVariable M14346^op» : Magma (Fin 8) where
  op := finOpTable "[[0,5,2,4,4,2,0,0],[1,1,3,3,4,5,1,5],[2,2,5,3,4,0,2,2],[3,3,1,2,4,3,3,7],[4,6,4,0,3,5,2,7],[2,5,2,3,5,7,6,1],[7,6,6,6,7,6,6,7],[3,7,2,7,6,5,7,4]]"

@[implicit_reducible]
def «OneVariable M14361» : Magma (Fin 8) where
  op := finOpTable "[[5,1,0,4,3,0,3,0],[1,4,1,6,1,0,3,7],[0,1,2,7,1,0,7,7],[4,6,5,3,4,5,6,5],[4,2,1,4,0,4,6,0],[2,0,0,5,4,7,5,5],[3,6,7,6,6,5,1,2],[0,7,7,5,7,3,7,6]]"

@[implicit_reducible]
def «OneVariable M14361^op» : Magma (Fin 8) where
  op := finOpTable "[[5,1,0,4,4,2,3,0],[1,4,1,6,2,0,6,7],[0,1,2,5,1,0,7,7],[4,6,7,3,4,5,6,5],[3,1,1,4,0,4,6,7],[0,0,0,5,4,7,5,3],[3,3,7,6,6,5,1,7],[0,7,7,5,0,5,2,6]]"

@[implicit_reducible]
def «OneVariable M14428» : Magma (Fin 8) where
  op := finOpTable "[[7,4,7,0,1,0,1,2],[6,0,3,5,1,3,0,1],[7,3,2,1,4,5,6,0],[3,2,1,1,7,3,7,6],[1,1,2,7,4,5,6,3],[0,3,2,3,4,5,6,0],[1,0,2,7,4,2,6,7],[5,7,0,4,3,0,7,3]]"

@[implicit_reducible]
def «OneVariable M14428^op» : Magma (Fin 8) where
  op := finOpTable "[[7,6,7,3,1,0,1,5],[4,0,3,2,1,3,0,7],[7,3,2,1,2,2,2,0],[0,5,1,1,7,3,7,4],[1,1,4,7,4,4,4,3],[0,3,5,3,5,5,2,0],[1,0,6,7,6,6,6,7],[2,1,0,6,3,0,7,3]]"

@[implicit_reducible]
def «OneVariable M14460» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[3,1,1,0],[3,0,2,2],[0,0,2,3]]"

@[implicit_reducible]
def «OneVariable M14460^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,3,0],[2,1,0,0],[3,1,2,2],[0,0,2,3]]"

@[implicit_reducible]
def «OneVariable M14461» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[3,1,3,0],[1,0,2,0],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M14461^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,1,0],[2,1,0,0],[3,3,2,0],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M14467» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,0],[4,1,0,1,0],[1,0,2,4,0],[2,1,2,3,2],[0,0,2,2,4]]"

@[implicit_reducible]
def «OneVariable M14467^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,1,2,0],[2,1,0,1,0],[3,0,2,2,2],[0,1,4,3,2],[0,0,0,2,4]]"

@[implicit_reducible]
def «OneVariable M14468» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,2],[2,1,3,0],[0,0,2,0],[1,0,0,3]]"

@[implicit_reducible]
def «OneVariable M14468^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,1],[3,1,0,0],[0,3,2,0],[2,0,0,3]]"

@[implicit_reducible]
def «OneVariable M14518» : Magma (Fin 8) where
  op := finOpTable "[[0,0,2,3,4,0,6,7],[0,1,2,3,4,7,6,7],[2,3,4,1,4,7,6,2],[3,3,2,2,3,6,5,7],[2,4,0,3,7,5,4,7],[0,1,1,0,5,5,6,7],[7,6,6,3,4,6,3,0],[7,4,2,7,1,7,6,6]]"

@[implicit_reducible]
def «OneVariable M14518^op» : Magma (Fin 8) where
  op := finOpTable "[[0,0,2,3,2,0,7,7],[0,1,3,3,4,1,6,4],[2,2,4,2,0,1,6,2],[3,3,1,2,3,0,3,7],[4,4,4,3,7,5,4,1],[0,7,7,6,5,5,6,7],[6,6,6,5,4,6,3,6],[7,7,2,7,7,7,0,6]]"

@[implicit_reducible]
def «OneVariable M14519» : Magma (Fin 8) where
  op := finOpTable "[[2,4,2,0,1,0,0,7],[4,1,6,3,4,5,1,3],[6,0,3,3,4,2,0,2],[0,3,5,7,3,2,2,7],[0,4,4,3,0,4,7,6],[0,0,2,2,4,5,1,4],[0,1,0,0,7,5,6,7],[7,3,2,1,4,5,7,4]]"

@[implicit_reducible]
def «OneVariable M14519^op» : Magma (Fin 8) where
  op := finOpTable "[[2,4,6,0,0,0,0,7],[4,1,0,3,4,0,1,3],[2,6,3,5,4,2,0,2],[0,3,3,7,3,2,0,1],[1,4,4,3,0,4,7,4],[0,5,2,2,4,5,5,5],[0,1,0,2,7,1,6,7],[7,3,2,7,6,4,7,4]]"

@[implicit_reducible]
def «OneVariable M14521» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,1],[2,0,0,1],[1,1,2,3],[0,0,3,3]]"

@[implicit_reducible]
def «OneVariable M14573» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,0],[3,1,1,0],[0,0,2,0],[1,0,0,3]]"

@[implicit_reducible]
def «OneVariable M14573^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,1],[2,1,0,0],[0,1,2,0],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M14574» : Magma (Fin 4) where
  op := finOpTable "[[2,0,3,2],[2,1,0,1],[1,0,2,2],[0,1,0,3]]"

@[implicit_reducible]
def «OneVariable M14574^op» : Magma (Fin 4) where
  op := finOpTable "[[2,2,1,0],[0,1,0,1],[3,0,2,0],[2,1,2,3]]"

@[implicit_reducible]
def «OneVariable M14603» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,1],[2,1,3,0],[1,0,2,2],[0,0,1,3]]"

@[implicit_reducible]
def «OneVariable M14603^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,1,0],[3,1,0,0],[0,3,2,1],[1,0,2,3]]"

@[implicit_reducible]
def «OneVariable M14636» : Magma (Fin 8) where
  op := finOpTable "[[0,4,6,4,4,6,2,0],[4,1,6,4,3,2,6,7],[6,6,4,3,7,2,0,4],[4,4,2,6,1,6,5,3],[3,4,5,0,3,2,6,2],[5,1,4,3,2,5,3,5],[6,2,1,7,4,3,2,3],[0,1,2,6,2,5,3,7]]"

@[implicit_reducible]
def «OneVariable M14636^op» : Magma (Fin 8) where
  op := finOpTable "[[0,4,6,4,3,5,6,0],[4,1,6,4,4,1,2,1],[6,6,4,2,5,4,1,2],[4,4,3,6,0,3,7,6],[4,3,7,1,3,2,4,2],[6,2,2,6,2,5,3,5],[2,6,0,5,6,3,2,3],[0,7,4,3,2,5,3,7]]"

@[implicit_reducible]
def «OneVariable M14643» : Magma (Fin 5) where
  op := finOpTable "[[1,3,0,1,0],[2,0,0,1,1],[4,1,2,1,2],[0,4,1,3,3],[0,1,4,4,4]]"

@[implicit_reducible]
def «OneVariable M14643^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,0,0],[3,0,1,4,1],[0,0,2,1,4],[1,1,1,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M14687» : Magma (Fin 5) where
  op := finOpTable "[[4,0,0,2,3],[2,1,2,4,0],[0,2,2,2,0],[0,1,4,3,0],[1,0,4,4,4]]"

@[implicit_reducible]
def «OneVariable M14687^op» : Magma (Fin 5) where
  op := finOpTable "[[4,2,0,0,1],[0,1,2,1,0],[0,2,2,4,4],[2,4,2,3,4],[3,0,0,0,4]]"

@[implicit_reducible]
def «OneVariable M14718» : Magma (Fin 5) where
  op := finOpTable "[[4,0,0,2,3],[2,1,2,2,0],[0,1,2,4,4],[0,1,2,3,0],[1,1,0,0,4]]"

@[implicit_reducible]
def «OneVariable M14718^op» : Magma (Fin 5) where
  op := finOpTable "[[4,2,0,0,1],[0,1,1,1,1],[0,2,2,2,0],[2,2,4,3,0],[3,0,4,0,4]]"

@[implicit_reducible]
def «OneVariable M14719» : Magma (Fin 5) where
  op := finOpTable "[[2,0,3,3,0],[4,1,0,4,2],[1,0,2,0,1],[0,4,0,3,0],[0,4,4,0,4]]"

@[implicit_reducible]
def «OneVariable M14719^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,1,0,0],[0,1,0,4,4],[3,0,2,0,4],[3,4,0,3,0],[0,2,1,0,4]]"

@[implicit_reducible]
def «OneVariable M14723» : Magma (Fin 5) where
  op := finOpTable "[[3,0,3,2,0],[4,1,1,0,4],[0,2,2,4,2],[1,0,0,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M14723^op» : Magma (Fin 5) where
  op := finOpTable "[[3,4,0,1,0],[0,1,2,0,4],[3,1,2,0,4],[2,0,4,3,4],[0,4,2,3,4]]"

@[implicit_reducible]
def «OneVariable M14734» : Magma (Fin 4) where
  op := finOpTable "[[2,0,3,0],[3,1,0,2],[1,0,2,0],[0,3,0,3]]"

@[implicit_reducible]
def «OneVariable M14734^op» : Magma (Fin 4) where
  op := finOpTable "[[2,3,1,0],[0,1,0,3],[3,0,2,0],[0,2,0,3]]"

@[implicit_reducible]
def «OneVariable M14736» : Magma (Fin 5) where
  op := finOpTable "[[4,0,0,4,3],[2,1,1,1,3],[0,2,2,0,0],[0,4,3,3,0],[1,0,4,0,4]]"

@[implicit_reducible]
def «OneVariable M14736^op» : Magma (Fin 5) where
  op := finOpTable "[[4,2,0,0,1],[0,1,2,4,0],[0,1,2,3,4],[4,1,0,3,0],[3,3,0,0,4]]"

@[implicit_reducible]
def «OneVariable M14742» : Magma (Fin 5) where
  op := finOpTable "[[3,0,0,4,3],[2,1,2,0,3],[0,2,2,2,3],[1,0,4,3,0],[0,1,4,0,4]]"

@[implicit_reducible]
def «OneVariable M14742^op» : Magma (Fin 5) where
  op := finOpTable "[[3,2,0,1,0],[0,1,2,0,1],[0,2,2,4,4],[4,0,2,3,0],[3,3,3,0,4]]"

@[implicit_reducible]
def «OneVariable M14744» : Magma (Fin 8) where
  op := finOpTable "[[4,0,7,3,6,7,0,5],[6,1,0,6,0,0,1,3],[7,5,2,4,5,4,4,7],[0,3,4,7,2,4,3,6],[1,0,4,5,3,4,0,7],[7,2,0,4,4,5,4,2],[0,6,4,3,0,0,6,3],[2,3,7,1,4,7,3,0]]"

@[implicit_reducible]
def «OneVariable M14744^op» : Magma (Fin 8) where
  op := finOpTable "[[4,6,7,0,1,7,0,2],[0,1,5,3,0,2,6,3],[7,0,2,4,4,0,4,7],[3,6,4,7,5,4,3,1],[6,0,5,2,3,4,0,4],[7,0,4,4,4,5,0,7],[0,1,4,3,0,4,6,3],[5,3,7,6,7,2,3,0]]"

@[implicit_reducible]
def «OneVariable M14746» : Magma (Fin 9) where
  op := finOpTable "[[2,8,4,8,2,0,6,0,3],[8,1,7,2,4,7,2,5,8],[5,2,6,6,0,0,3,2,8],[8,3,2,3,5,6,2,7,4],[0,1,0,5,4,3,6,6,8],[7,1,0,5,4,5,4,3,6],[0,2,1,2,6,6,8,8,7],[0,0,2,3,1,7,6,7,6],[1,0,2,8,8,6,5,6,0]]"

@[implicit_reducible]
def «OneVariable M14746^op» : Magma (Fin 9) where
  op := finOpTable "[[2,8,5,8,0,7,0,0,1],[8,1,2,3,1,1,2,0,0],[4,7,6,2,0,0,1,2,2],[8,2,6,3,5,5,2,3,8],[2,4,0,5,4,4,6,1,8],[0,7,0,6,3,5,6,7,6],[6,2,3,2,6,4,8,6,5],[0,5,2,7,6,3,8,7,6],[3,8,8,4,8,6,7,6,0]]"

@[implicit_reducible]
def «OneVariable M14823» : Magma (Fin 8) where
  op := finOpTable "[[5,3,2,1,0,4,0,7],[3,0,4,1,2,1,6,7],[2,4,1,7,2,0,6,3],[1,1,7,3,4,5,5,7],[0,2,2,3,4,0,6,6],[4,1,0,5,0,6,3,5],[0,6,6,5,6,3,7,4],[7,7,3,7,6,5,4,2]]"

@[implicit_reducible]
def «OneVariable M14838» : Magma (Fin 8) where
  op := finOpTable "[[0,0,2,4,2,5,6,5],[2,1,2,3,2,3,4,1],[2,2,4,2,0,5,7,6],[5,3,2,5,6,1,4,3],[2,2,1,6,3,4,4,7],[5,3,5,1,4,7,6,0],[6,4,7,4,4,6,6,7],[5,1,6,3,7,0,7,2]]"

@[implicit_reducible]
def «OneVariable M14915» : Magma (Fin 8) where
  op := finOpTable "[[7,0,3,2,0,0,3,5],[5,1,6,4,4,2,3,0],[3,3,2,6,7,4,2,6],[6,4,3,0,5,4,3,3],[4,4,7,1,3,4,7,2],[0,5,5,4,1,5,2,0],[3,3,6,3,7,2,6,7],[1,0,7,7,6,0,7,4]]"

@[implicit_reducible]
def «OneVariable M14915^op» : Magma (Fin 8) where
  op := finOpTable "[[7,5,3,6,4,0,3,1],[0,1,3,4,4,5,3,0],[3,6,2,3,7,5,6,7],[2,4,6,0,1,4,3,7],[0,4,7,5,3,1,7,6],[0,2,4,4,4,5,2,0],[3,3,2,3,7,2,6,7],[5,0,6,3,2,0,7,4]]"

@[implicit_reducible]
def «OneVariable M14917» : Magma (Fin 9) where
  op := finOpTable "[[6,5,0,1,6,1,4,0,0],[3,0,8,0,1,1,1,8,2],[0,8,2,7,4,4,6,2,4],[1,1,7,3,1,2,6,3,6],[0,1,4,1,4,4,0,5,8],[1,4,5,4,5,5,2,3,6],[7,6,6,8,0,6,8,0,3],[2,8,2,7,2,2,0,7,8],[8,7,8,6,8,6,5,1,1]]"

@[implicit_reducible]
def «OneVariable M14917^op» : Magma (Fin 9) where
  op := finOpTable "[[6,3,0,1,0,1,7,2,8],[5,0,8,1,1,4,6,8,7],[0,8,2,7,4,5,6,2,8],[1,0,7,3,1,4,8,7,6],[6,1,4,1,4,5,0,2,8],[1,1,4,2,4,5,6,2,6],[4,1,6,6,0,2,8,0,5],[0,8,2,3,5,3,0,7,1],[0,2,4,6,8,6,3,8,1]]"

@[implicit_reducible]
def «OneVariable M14944» : Magma (Fin 5) where
  op := finOpTable "[[4,3,0,0,1],[0,1,2,4,0],[1,4,2,4,0],[0,4,0,3,0],[2,0,0,3,4]]"

@[implicit_reducible]
def «OneVariable M14944^op» : Magma (Fin 5) where
  op := finOpTable "[[4,0,1,0,2],[3,1,4,4,0],[0,2,2,0,0],[0,4,4,3,3],[1,0,0,0,4]]"

@[implicit_reducible]
def «OneVariable M14967» : Magma (Fin 5) where
  op := finOpTable "[[2,4,1,0,0],[0,1,0,3,1],[3,0,2,0,4],[4,1,0,3,4],[0,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M14968» : Magma (Fin 9) where
  op := finOpTable "[[2,0,6,4,5,4,1,0,8],[0,1,2,3,8,3,0,1,6],[7,2,8,2,4,1,0,0,5],[4,1,1,3,4,3,1,8,2],[3,8,2,6,0,4,4,8,1],[4,7,2,5,6,5,6,1,2],[0,8,0,4,4,5,6,6,8],[1,7,0,8,8,1,6,7,8],[0,8,3,2,7,2,8,6,4]]"

@[implicit_reducible]
def «OneVariable M14968^op» : Magma (Fin 9) where
  op := finOpTable "[[2,0,7,4,3,4,0,1,0],[0,1,2,1,8,7,8,7,8],[6,2,8,1,2,2,0,0,3],[4,3,2,3,6,5,4,8,2],[5,8,4,4,0,6,4,8,7],[4,3,1,3,4,5,5,1,2],[1,0,0,1,4,6,6,6,8],[0,1,0,8,8,1,6,7,6],[8,6,5,2,1,2,8,8,4]]"

@[implicit_reducible]
def «OneVariable M14979» : Magma (Fin 3) where
  op := finOpTable "[[1,2,0],[2,1,0],[0,0,2]]"

@[implicit_reducible]
def «OneVariable M14988» : Magma (Fin 4) where
  op := finOpTable "[[1,2,2,0],[3,1,0,0],[0,0,2,1],[0,0,1,3]]"

@[implicit_reducible]
def «OneVariable M14988^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,0],[2,1,0,0],[2,0,2,1],[0,0,1,3]]"

@[implicit_reducible]
def «OneVariable M14992» : Magma (Fin 4) where
  op := finOpTable "[[0,1,2,3],[2,2,0,1],[2,3,1,1],[1,1,2,3]]"

@[implicit_reducible]
def «OneVariable M14992^op» : Magma (Fin 4) where
  op := finOpTable "[[0,2,2,1],[1,2,3,1],[2,0,1,2],[3,1,1,3]]"

@[implicit_reducible]
def «OneVariable M15002» : Magma (Fin 4) where
  op := finOpTable "[[1,2,1,0],[3,1,2,0],[0,0,2,1],[0,0,1,3]]"

@[implicit_reducible]
def «OneVariable M15002^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,0],[2,1,0,0],[1,2,2,1],[0,0,1,3]]"

@[implicit_reducible]
def «OneVariable M15016» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,1],[2,1,3,0],[0,0,2,2],[0,0,3,3]]"

@[implicit_reducible]
def «OneVariable M15016^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,0],[3,1,0,0],[0,3,2,3],[1,0,2,3]]"

@[implicit_reducible]
def «OneVariable M15024» : Magma (Fin 3) where
  op := finOpTable "[[1,2,0],[2,1,0],[0,1,2]]"

@[implicit_reducible]
def «OneVariable M15024^op» : Magma (Fin 3) where
  op := finOpTable "[[1,2,0],[2,1,1],[0,0,2]]"

@[implicit_reducible]
def «OneVariable M15028» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[3,1,0,0],[0,3,2,3],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M15028^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,0],[2,1,3,0],[3,0,2,0],[0,0,3,3]]"

@[implicit_reducible]
def «OneVariable M15031» : Magma (Fin 4) where
  op := finOpTable "[[0,3,1,1],[2,0,0,1],[1,1,2,0],[1,1,1,3]]"

@[implicit_reducible]
def «OneVariable M15031^op» : Magma (Fin 4) where
  op := finOpTable "[[0,2,1,1],[3,0,1,1],[1,0,2,1],[1,1,0,3]]"

@[implicit_reducible]
def «OneVariable M15032» : Magma (Fin 4) where
  op := finOpTable "[[1,2,1,0],[3,1,0,0],[0,2,2,1],[0,0,1,3]]"

@[implicit_reducible]
def «OneVariable M15032^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,0],[2,1,2,0],[1,0,2,1],[0,0,1,3]]"

@[implicit_reducible]
def «OneVariable M15041» : Magma (Fin 8) where
  op := finOpTable "[[5,4,4,3,2,6,5,0],[4,1,6,5,4,5,6,7],[4,7,2,5,4,5,6,6],[0,5,5,4,7,1,3,4],[1,0,4,6,0,5,3,3],[7,5,3,2,4,3,0,0],[0,7,2,3,3,0,6,4],[0,4,6,3,3,0,4,7]]"

@[implicit_reducible]
def «OneVariable M15041^op» : Magma (Fin 8) where
  op := finOpTable "[[5,4,4,0,1,7,0,0],[4,1,7,5,0,5,7,4],[4,6,2,5,4,3,2,6],[3,5,5,4,6,2,3,3],[2,4,4,7,0,4,3,3],[6,5,5,1,5,3,0,0],[5,6,6,3,3,0,6,4],[0,7,6,4,3,0,4,7]]"

@[implicit_reducible]
def «OneVariable M15054» : Magma (Fin 8) where
  op := finOpTable "[[1,3,0,0,0,5,4,7],[3,2,4,1,1,1,6,7],[0,4,5,2,4,3,2,7],[0,0,2,3,0,2,5,7],[6,1,1,6,4,0,6,7],[5,1,3,3,4,6,7,5],[4,6,2,3,6,7,0,3],[7,0,2,3,4,5,5,7]]"

@[implicit_reducible]
def «OneVariable M15054^op» : Magma (Fin 8) where
  op := finOpTable "[[1,3,0,0,6,5,4,7],[3,2,4,0,1,1,6,0],[0,4,5,2,1,3,2,2],[0,1,2,3,6,3,3,3],[0,1,4,0,4,4,6,4],[5,1,3,2,0,6,7,5],[4,6,2,5,6,7,0,5],[7,7,7,7,7,5,3,7]]"

@[implicit_reducible]
def «OneVariable M15068» : Magma (Fin 8) where
  op := finOpTable "[[0,1,7,2,4,5,6,7],[1,3,2,6,5,4,1,1],[7,2,5,3,0,6,2,0],[1,0,3,7,3,5,1,4],[7,5,7,3,4,5,0,3],[4,4,6,5,5,1,2,7],[6,1,2,1,0,2,6,0],[7,1,0,4,3,7,0,2]]"

@[implicit_reducible]
def «OneVariable M15068^op» : Magma (Fin 8) where
  op := finOpTable "[[0,1,7,1,7,4,6,7],[1,3,2,0,5,4,1,1],[7,2,5,3,7,6,2,0],[2,6,3,7,3,5,1,4],[4,5,0,3,4,5,0,3],[5,4,6,5,5,1,2,7],[6,1,2,1,0,2,6,0],[7,1,0,4,3,7,0,2]]"

@[implicit_reducible]
def «OneVariable M15091» : Magma (Fin 8) where
  op := finOpTable "[[6,2,1,0,0,1,7,6],[5,0,1,7,3,0,1,3],[1,1,2,6,7,6,6,5],[3,4,6,1,1,6,2,3],[0,3,7,3,4,4,0,6],[1,1,4,6,2,5,6,5],[4,6,6,5,0,3,3,0],[0,3,7,3,0,0,0,7]]"

@[implicit_reducible]
def «OneVariable M15091^op» : Magma (Fin 8) where
  op := finOpTable "[[6,5,1,3,0,1,4,0],[2,0,1,4,3,1,6,3],[1,1,2,6,7,4,6,7],[0,7,6,1,3,6,5,3],[0,3,7,1,4,2,0,0],[1,0,6,6,4,5,3,0],[7,1,6,2,0,6,3,0],[6,3,5,3,6,5,0,7]]"

@[implicit_reducible]
def «OneVariable M15105» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[3,1,3,0],[0,0,2,1],[0,0,1,3]]"

@[implicit_reducible]
def «OneVariable M15105^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,0],[2,1,0,0],[3,3,2,1],[0,0,1,3]]"

@[implicit_reducible]
def «OneVariable M15113» : Magma (Fin 4) where
  op := finOpTable "[[2,3,1,0],[0,1,0,3],[3,0,2,3],[0,3,0,3]]"

@[implicit_reducible]
def «OneVariable M15113^op» : Magma (Fin 4) where
  op := finOpTable "[[2,0,3,0],[3,1,0,3],[1,0,2,0],[0,3,3,3]]"

@[implicit_reducible]
def «OneVariable M15117» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,0],[4,1,0,0,0],[0,0,2,0,0],[3,0,0,3,0],[0,0,0,0,4]]"

@[implicit_reducible]
def «OneVariable M15117^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,0,3,0],[2,1,0,0,0],[3,0,2,0,0],[0,0,0,3,0],[0,0,0,0,4]]"

@[implicit_reducible]
def «OneVariable M15121» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,2],[2,1,0,0],[0,1,2,0],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M15121^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,0],[3,1,1,0],[0,0,2,0],[2,0,0,3]]"

@[implicit_reducible]
def «OneVariable M15151» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[3,0,1,2],[0,1,2,3],[0,1,2,3]]"

@[implicit_reducible]
def «OneVariable M15151^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,0],[2,0,1,1],[3,1,2,2],[0,2,3,3]]"

@[implicit_reducible]
def «OneVariable M15154» : Magma (Fin 4) where
  op := finOpTable "[[2,0,3,1],[0,1,0,0],[1,3,0,2],[2,1,2,3]]"

@[implicit_reducible]
def «OneVariable M15154^op» : Magma (Fin 4) where
  op := finOpTable "[[2,0,1,2],[0,1,3,1],[3,0,0,2],[1,0,2,3]]"

@[implicit_reducible]
def «OneVariable M15155» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,3,0],[4,0,1,3,2],[1,1,2,3,4],[0,0,2,3,4],[0,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M15155^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,1,0,0],[2,0,1,0,0],[3,1,2,2,2],[3,3,3,3,3],[0,2,4,4,4]]"

@[implicit_reducible]
def «OneVariable M15156» : Magma (Fin 4) where
  op := finOpTable "[[3,3,0,1],[2,1,0,3],[0,2,2,1],[2,3,0,0]]"

@[implicit_reducible]
def «OneVariable M15156^op» : Magma (Fin 4) where
  op := finOpTable "[[3,2,0,2],[3,1,2,3],[0,0,2,0],[1,3,1,0]]"

@[implicit_reducible]
def «OneVariable M15157» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,2,0],[4,0,1,0,0],[3,1,2,2,0],[0,1,3,3,3],[0,3,0,4,4]]"

@[implicit_reducible]
def «OneVariable M15157^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,0,0],[2,0,1,1,3],[1,1,2,3,0],[2,0,2,3,4],[0,0,0,3,4]]"

@[implicit_reducible]
def «OneVariable M15158» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,0,0],[4,0,1,0,0],[3,1,2,2,3],[3,3,3,3,2],[0,2,4,2,4]]"

@[implicit_reducible]
def «OneVariable M15158^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,3,0],[2,0,1,3,2],[1,1,2,3,4],[0,0,2,3,2],[0,0,3,2,4]]"

@[implicit_reducible]
def «OneVariable M15159» : Magma (Fin 5) where
  op := finOpTable "[[1,2,4,3,0],[4,0,1,3,2],[3,1,2,1,4],[0,3,1,3,2],[0,2,1,2,4]]"

@[implicit_reducible]
def «OneVariable M15159^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,0,0],[2,0,1,3,2],[4,1,2,1,1],[3,3,1,3,2],[0,2,4,2,4]]"

@[implicit_reducible]
def «OneVariable M15160» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,0],[4,0,1,4,2],[1,1,2,1,3],[1,3,1,3,2],[0,0,4,2,4]]"

@[implicit_reducible]
def «OneVariable M15160^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,1,1,0],[2,0,1,3,0],[3,1,2,1,4],[0,4,1,3,2],[0,2,3,2,4]]"

@[implicit_reducible]
def «OneVariable M15162» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,1],[2,0,0,1],[3,1,2,1],[0,2,1,3]]"

@[implicit_reducible]
def «OneVariable M15162^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[3,0,1,2],[0,0,2,1],[1,1,1,3]]"

@[implicit_reducible]
def «OneVariable M15164» : Magma (Fin 5) where
  op := finOpTable "[[4,1,0,0,1],[0,1,4,1,3],[3,0,2,1,4],[0,0,1,3,4],[2,4,2,4,0]]"

@[implicit_reducible]
def «OneVariable M15164^op» : Magma (Fin 5) where
  op := finOpTable "[[4,0,3,0,2],[1,1,0,0,4],[0,4,2,1,2],[0,1,1,3,4],[1,3,4,4,0]]"

@[implicit_reducible]
def «OneVariable M15165» : Magma (Fin 5) where
  op := finOpTable "[[4,0,3,0,2],[3,1,1,1,4],[0,3,2,2,1],[0,1,3,3,4],[1,3,4,4,0]]"

@[implicit_reducible]
def «OneVariable M15165^op» : Magma (Fin 5) where
  op := finOpTable "[[4,3,0,0,1],[0,1,3,1,3],[3,1,2,3,4],[0,1,2,3,4],[2,4,1,4,0]]"

@[implicit_reducible]
def «OneVariable M15166» : Magma (Fin 5) where
  op := finOpTable "[[4,0,3,0,2],[3,1,3,3,4],[0,0,2,0,3],[0,2,1,3,4],[1,3,4,4,0]]"

@[implicit_reducible]
def «OneVariable M15167» : Magma (Fin 4) where
  op := finOpTable "[[1,2,2,0],[3,0,1,2],[0,1,2,3],[0,1,2,3]]"

@[implicit_reducible]
def «OneVariable M15167^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,0],[2,0,1,1],[2,1,2,2],[0,2,3,3]]"

@[implicit_reducible]
def «OneVariable M15168» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,0,0],[4,0,1,0,2],[0,1,2,3,3],[1,0,3,3,4],[0,1,3,4,4]]"

@[implicit_reducible]
def «OneVariable M15168^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,0,1,0],[2,0,1,0,1],[3,1,2,3,3],[0,0,3,3,4],[0,2,3,4,4]]"

@[implicit_reducible]
def «OneVariable M15169» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,1],[3,0,0,1],[1,1,2,2],[0,0,2,3]]"

@[implicit_reducible]
def «OneVariable M15207» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,1],[3,1,1,0],[1,0,2,2],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M15207^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,1,0],[2,1,0,0],[0,1,2,0],[1,0,2,3]]"

@[implicit_reducible]
def «OneVariable M15263» : Magma (Fin 4) where
  op := finOpTable "[[2,0,1,2],[2,1,0,1],[3,0,2,2],[0,1,0,3]]"

@[implicit_reducible]
def «OneVariable M15263^op» : Magma (Fin 4) where
  op := finOpTable "[[2,2,3,0],[0,1,0,1],[1,0,2,0],[2,1,2,3]]"

@[implicit_reducible]
def «OneVariable M15297» : Magma (Fin 4) where
  op := finOpTable "[[1,3,1,0],[2,1,0,0],[0,0,2,1],[2,0,1,3]]"

@[implicit_reducible]
def «OneVariable M15297^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,2],[3,1,0,0],[1,0,2,1],[0,0,1,3]]"

@[implicit_reducible]
def «OneVariable M15299» : Magma (Fin 8) where
  op := finOpTable "[[5,0,5,7,7,1,6,3],[5,1,6,3,5,0,7,6],[0,4,2,4,2,0,6,6],[7,3,4,3,1,6,5,7],[7,7,2,2,4,5,5,0],[2,0,0,5,6,6,3,7],[0,6,7,5,5,4,7,1],[4,6,6,0,7,5,2,0]]"

@[implicit_reducible]
def «OneVariable M15299^op» : Magma (Fin 8) where
  op := finOpTable "[[5,5,0,7,7,2,0,4],[0,1,4,3,7,0,6,6],[5,6,2,4,2,0,7,6],[7,3,4,3,2,5,5,0],[7,5,2,1,4,6,5,7],[1,0,0,6,5,6,4,5],[6,7,6,5,5,3,7,2],[3,6,6,7,0,7,1,0]]"

@[implicit_reducible]
def «OneVariable M15301» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,0],[2,0,1,1],[0,3,2,1],[2,1,3,3]]"

@[implicit_reducible]
def «OneVariable M15301^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,2],[3,0,3,1],[0,1,2,3],[0,1,1,3]]"

@[implicit_reducible]
def «OneVariable M15303» : Magma (Fin 5) where
  op := finOpTable "[[1,2,0,1,0],[3,0,0,1,1],[4,1,2,2,0],[0,4,1,3,3],[0,1,3,4,4]]"

@[implicit_reducible]
def «OneVariable M15303^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,4,0,0],[2,0,1,4,1],[0,0,2,1,3],[1,1,2,3,4],[0,1,0,3,4]]"

@[implicit_reducible]
def «OneVariable M15306» : Magma (Fin 5) where
  op := finOpTable "[[1,2,0,3,0],[3,0,2,1,1],[4,1,2,1,3],[0,4,1,3,2],[0,1,1,2,4]]"

@[implicit_reducible]
def «OneVariable M15306^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,4,0,0],[2,0,1,4,1],[0,2,2,1,1],[3,1,1,3,2],[0,1,3,2,4]]"

@[implicit_reducible]
def «OneVariable M15338» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,0],[3,1,2,0],[3,0,2,1],[0,0,1,3]]"

@[implicit_reducible]
def «OneVariable M15338^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,3,0],[2,1,0,0],[0,2,2,1],[0,0,1,3]]"

@[implicit_reducible]
def «OneVariable M15347» : Magma (Fin 5) where
  op := finOpTable "[[1,2,0,0,3],[4,1,3,1,0],[3,0,2,0,0],[0,0,0,3,0],[0,0,0,0,4]]"

@[implicit_reducible]
def «OneVariable M15347^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,0,0],[2,1,0,0,0],[0,3,2,0,0],[0,1,0,3,0],[3,0,0,0,4]]"

@[implicit_reducible]
def «OneVariable M15372» : Magma (Fin 5) where
  op := finOpTable "[[3,0,0,1,3],[2,1,4,0,3],[0,4,2,0,3],[4,2,0,3,0],[0,4,4,0,4]]"

@[implicit_reducible]
def «OneVariable M15372^op» : Magma (Fin 5) where
  op := finOpTable "[[3,2,0,4,0],[0,1,4,2,4],[0,4,2,0,4],[1,0,0,3,0],[3,3,3,0,4]]"

@[implicit_reducible]
def «OneVariable M15403» : Magma (Fin 5) where
  op := finOpTable "[[4,0,4,0,1],[3,1,1,0,0],[0,0,2,2,0],[0,4,0,3,0],[2,0,1,4,4]]"

@[implicit_reducible]
def «OneVariable M15403^op» : Magma (Fin 5) where
  op := finOpTable "[[4,3,0,0,2],[0,1,0,4,0],[4,1,2,0,1],[0,0,2,3,4],[1,0,0,0,4]]"

@[implicit_reducible]
def «OneVariable M15426» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,0],[2,1,0,0],[0,0,2,1],[2,0,1,3]]"

@[implicit_reducible]
def «OneVariable M15426^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,2],[3,1,0,0],[0,0,2,1],[0,0,1,3]]"

@[implicit_reducible]
def «OneVariable M15427» : Magma (Fin 5) where
  op := finOpTable "[[4,0,0,4,1],[2,1,2,3,0],[0,2,2,4,1],[0,2,4,3,0],[3,0,0,0,4]]"

@[implicit_reducible]
def «OneVariable M15427^op» : Magma (Fin 5) where
  op := finOpTable "[[4,2,0,0,3],[0,1,2,2,0],[0,2,2,4,0],[4,3,4,3,0],[1,0,1,0,4]]"

@[implicit_reducible]
def «OneVariable M15428» : Magma (Fin 5) where
  op := finOpTable "[[2,0,1,2,0],[4,1,0,0,2],[3,0,2,0,4],[0,3,2,3,3],[0,4,2,3,4]]"

@[implicit_reducible]
def «OneVariable M15428^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,0,0],[0,1,0,3,4],[1,0,2,2,2],[2,0,0,3,3],[0,2,4,3,4]]"

@[implicit_reducible]
def «OneVariable M15434» : Magma (Fin 8) where
  op := finOpTable "[[0,1,3,5,6,5,6,5],[4,1,7,4,4,7,2,5],[3,2,6,5,4,3,1,2],[3,4,0,2,1,3,6,4],[6,4,2,7,3,6,0,4],[5,7,3,3,6,5,0,5],[6,2,7,3,5,6,4,2],[5,5,2,4,1,0,2,7]]"

@[implicit_reducible]
def «OneVariable M15434^op» : Magma (Fin 8) where
  op := finOpTable "[[0,4,3,3,6,5,6,5],[1,1,2,4,4,7,2,5],[3,7,6,0,2,3,7,2],[5,4,5,2,7,3,3,4],[6,4,4,1,3,6,5,1],[5,7,3,3,6,5,6,0],[6,2,1,6,0,0,4,2],[5,5,2,4,4,5,2,7]]"

@[implicit_reducible]
def «OneVariable M15436» : Magma (Fin 9) where
  op := finOpTable "[[7,0,2,0,8,7,8,1,6],[3,1,2,3,0,0,7,0,2],[0,8,8,7,7,2,2,4,5],[0,3,7,3,3,2,6,6,8],[8,0,7,3,4,1,3,7,3],[0,0,6,2,5,5,6,0,2],[8,5,2,6,6,6,6,7,8],[5,0,3,7,2,0,7,2,8],[4,2,1,8,8,2,0,7,0]]"

@[implicit_reducible]
def «OneVariable M15436^op» : Magma (Fin 9) where
  op := finOpTable "[[7,3,0,0,8,0,8,5,4],[0,1,8,3,0,0,5,0,2],[2,2,8,7,7,6,2,3,1],[0,3,7,3,3,2,6,7,8],[8,0,7,3,4,5,6,2,8],[7,0,2,2,1,5,6,0,2],[8,7,2,6,3,6,6,7,0],[1,0,4,6,7,0,7,2,7],[6,2,5,8,3,2,8,8,0]]"

@[implicit_reducible]
def «OneVariable M15606» : Magma (Fin 8) where
  op := finOpTable "[[0,1,3,3,6,6,5,1],[1,7,5,1,1,2,2,4],[3,6,1,0,3,2,2,2],[3,3,4,2,3,7,7,5],[4,0,3,0,4,0,7,1],[2,2,2,7,1,5,5,7],[5,2,5,7,7,0,6,5],[1,0,7,6,1,7,7,3]]"

@[implicit_reducible]
def «OneVariable M15606^op» : Magma (Fin 8) where
  op := finOpTable "[[0,1,3,3,4,2,5,1],[1,7,6,3,0,2,2,0],[3,5,1,4,3,2,5,7],[3,1,0,2,0,7,7,6],[6,1,3,3,4,1,7,1],[6,2,2,7,0,5,0,7],[5,2,2,7,7,5,6,7],[1,4,2,5,1,7,5,3]]"

@[implicit_reducible]
def «OneVariable M15608» : Magma (Fin 9) where
  op := finOpTable "[[0,0,1,3,8,6,8,3,2],[0,1,1,4,6,2,0,2,7],[6,6,2,4,4,5,0,7,8],[7,4,4,7,2,3,3,5,3],[8,4,3,1,3,8,4,4,5],[3,3,5,6,8,5,0,3,8],[6,0,0,3,4,2,6,7,7],[3,7,7,0,7,3,8,8,1],[8,7,8,8,0,4,7,6,4]]"

@[implicit_reducible]
def «OneVariable M15608^op» : Magma (Fin 9) where
  op := finOpTable "[[0,0,6,7,8,3,6,3,8],[0,1,6,4,4,3,0,7,7],[1,1,2,4,3,5,0,7,8],[3,4,4,7,1,6,3,0,8],[8,6,4,2,3,8,4,7,0],[6,2,5,3,8,5,2,3,4],[8,0,0,3,4,0,6,8,7],[3,2,7,5,4,3,7,8,6],[2,7,8,3,5,8,7,1,4]]"

@[implicit_reducible]
def «OneVariable M15646» : Magma (Fin 5) where
  op := finOpTable "[[2,3,4,0,0],[0,1,0,4,4],[1,0,2,4,0],[0,4,1,3,0],[3,2,0,4,4]]"

@[implicit_reducible]
def «OneVariable M15647» : Magma (Fin 5) where
  op := finOpTable "[[2,4,3,0,0],[0,1,0,2,4],[1,0,2,0,4],[1,1,0,3,4],[0,1,4,3,4]]"

@[implicit_reducible]
def «OneVariable M15647^op» : Magma (Fin 5) where
  op := finOpTable "[[2,0,1,1,0],[4,1,0,1,1],[3,0,2,0,4],[0,2,0,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M15675» : Magma (Fin 5) where
  op := finOpTable "[[1,3,4,0,0],[2,1,2,0,4],[0,0,2,3,4],[4,0,2,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «OneVariable M15675^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,0,4,0],[3,1,0,0,1],[4,2,2,2,2],[0,0,3,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «OneVariable M15684» : Magma (Fin 9) where
  op := finOpTable "[[0,8,4,3,4,5,3,7,0],[1,1,2,3,6,0,7,7,0],[4,2,3,7,0,1,6,2,4],[1,3,5,6,4,2,8,2,3],[7,6,8,3,2,6,5,4,4],[5,0,2,2,6,5,6,0,8],[3,6,2,0,1,7,4,6,3],[7,1,1,2,4,0,6,7,0],[8,0,4,1,7,5,3,0,8]]"

@[implicit_reducible]
def «OneVariable M15684^op» : Magma (Fin 9) where
  op := finOpTable "[[0,1,4,1,7,5,3,7,8],[8,1,2,3,6,0,6,1,0],[4,2,3,5,8,2,2,1,4],[3,3,7,6,3,2,0,2,1],[4,6,0,4,2,6,1,4,7],[5,0,1,2,6,5,7,0,5],[3,7,6,8,5,6,4,6,3],[7,7,2,2,4,0,6,7,0],[0,0,4,3,4,8,3,0,8]]"

@[implicit_reducible]
def «OneVariable M15695» : Magma (Fin 4) where
  op := finOpTable "[[0,3,3,2],[3,1,3,3],[3,2,2,3],[1,3,0,0]]"

@[implicit_reducible]
def «OneVariable M15695^op» : Magma (Fin 4) where
  op := finOpTable "[[0,3,3,1],[3,1,2,3],[3,3,2,0],[2,3,3,0]]"

@[implicit_reducible]
def «OneVariable M15718» : Magma (Fin 4) where
  op := finOpTable "[[1,3,2,0],[2,1,0,0],[0,0,2,1],[0,0,1,3]]"

@[implicit_reducible]
def «OneVariable M15718^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,0],[3,1,0,0],[2,0,2,1],[0,0,1,3]]"

@[implicit_reducible]
def «OneVariable M15721» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,1],[3,1,1,0],[0,0,2,0],[0,0,3,3]]"

@[implicit_reducible]
def «OneVariable M15721^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,0],[2,1,0,0],[0,1,2,3],[1,0,0,3]]"

@[implicit_reducible]
def «OneVariable M15726» : Magma (Fin 4) where
  op := finOpTable "[[1,3,1,0],[2,0,1,0],[0,1,2,2],[0,1,3,3]]"

@[implicit_reducible]
def «OneVariable M15726^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,0],[3,0,1,1],[1,1,2,3],[0,0,2,3]]"

@[implicit_reducible]
def «OneVariable M15741» : Magma (Fin 4) where
  op := finOpTable "[[1,3,1,0],[2,1,2,0],[0,0,2,1],[0,0,1,3]]"

@[implicit_reducible]
def «OneVariable M15741^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,0],[3,1,0,0],[1,2,2,1],[0,0,1,3]]"

@[implicit_reducible]
def «OneVariable M15751» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,1],[3,1,0,0],[0,3,2,1],[0,0,1,3]]"

@[implicit_reducible]
def «OneVariable M15751^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,0],[2,1,3,0],[0,0,2,1],[1,0,1,3]]"

@[implicit_reducible]
def «OneVariable M15755» : Magma (Fin 4) where
  op := finOpTable "[[1,3,1,0],[2,1,0,0],[0,1,2,2],[0,0,3,3]]"

@[implicit_reducible]
def «OneVariable M15755^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,0],[3,1,1,0],[1,0,2,3],[0,0,2,3]]"

@[implicit_reducible]
def «OneVariable M15759» : Magma (Fin 8) where
  op := finOpTable "[[0,1,3,3,4,3,1,4],[6,6,1,7,4,7,2,5],[0,1,2,4,4,6,1,4],[7,7,2,3,6,5,6,7],[7,1,4,6,7,6,5,2],[3,7,3,5,6,5,6,7],[1,0,1,6,3,4,4,7],[4,3,4,7,0,1,6,1]]"

@[implicit_reducible]
def «OneVariable M15759^op» : Magma (Fin 8) where
  op := finOpTable "[[0,6,0,7,7,3,1,4],[1,6,1,7,1,7,0,3],[3,1,2,2,4,3,1,4],[3,7,4,3,6,5,6,7],[4,4,4,6,7,6,3,0],[3,7,6,5,6,5,4,1],[1,2,1,6,5,6,4,6],[4,5,4,7,2,7,7,1]]"

@[implicit_reducible]
def «OneVariable M15809» : Magma (Fin 8) where
  op := finOpTable "[[5,0,5,4,3,1,3,0],[0,1,1,7,4,0,0,7],[0,3,2,7,0,0,2,7],[6,7,7,0,0,3,3,2],[3,4,0,3,4,5,5,5],[2,0,0,5,5,7,7,4],[3,0,1,3,7,5,6,5],[7,7,3,1,5,6,5,3]]"

@[implicit_reducible]
def «OneVariable M15809^op» : Magma (Fin 8) where
  op := finOpTable "[[5,0,0,6,3,2,3,7],[0,1,3,7,4,0,0,7],[5,1,2,7,0,0,1,3],[4,7,7,0,3,5,3,1],[3,4,0,0,4,5,7,5],[1,0,0,3,5,7,5,6],[3,0,2,3,5,7,6,5],[0,7,7,2,5,4,5,3]]"

@[implicit_reducible]
def «OneVariable M15813» : Magma (Fin 4) where
  op := finOpTable "[[1,3,3,0],[2,1,3,0],[0,0,2,0],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M15813^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,0],[3,1,0,0],[3,3,2,0],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M15819» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,2],[3,1,1,0],[0,0,2,0],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M15819^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,0],[2,1,0,0],[0,1,2,0],[2,0,0,3]]"

@[implicit_reducible]
def «OneVariable M15838» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,2],[3,1,0,0],[0,1,2,0],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M15838^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,0],[2,1,1,0],[0,0,2,0],[2,0,0,3]]"

@[implicit_reducible]
def «OneVariable M15841» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,0,0],[2,1,0,3,0],[0,0,2,3,4],[3,4,2,3,4],[0,0,2,3,4]]"

@[implicit_reducible]
def «OneVariable M15841^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,0,3,0],[4,1,0,4,0],[3,0,2,2,2],[0,3,3,3,3],[0,0,4,4,4]]"

@[implicit_reducible]
def «OneVariable M15869» : Magma (Fin 4) where
  op := finOpTable "[[1,3,2,0],[2,0,1,3],[0,0,2,1],[1,1,1,3]]"

@[implicit_reducible]
def «OneVariable M15869^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,1],[3,0,0,1],[2,1,2,1],[0,3,1,3]]"

@[implicit_reducible]
def «OneVariable M15870» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,1],[3,0,0,1],[3,1,2,0],[0,2,0,3]]"

@[implicit_reducible]
def «OneVariable M15870^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,3,0],[2,0,1,2],[0,0,2,0],[1,1,0,3]]"

@[implicit_reducible]
def «OneVariable M15871» : Magma (Fin 5) where
  op := finOpTable "[[3,4,0,2,0],[0,1,2,4,0],[1,2,2,3,0],[1,3,4,0,3],[0,4,4,3,4]]"

@[implicit_reducible]
def «OneVariable M15871^op» : Magma (Fin 5) where
  op := finOpTable "[[3,0,1,1,0],[4,1,2,3,4],[0,2,2,4,4],[2,4,3,0,3],[0,0,0,3,4]]"

@[implicit_reducible]
def «OneVariable M15872» : Magma (Fin 5) where
  op := finOpTable "[[3,0,4,1,0],[4,1,2,3,2],[0,0,2,4,2],[2,4,3,0,3],[0,4,4,3,4]]"

@[implicit_reducible]
def «OneVariable M15873» : Magma (Fin 4) where
  op := finOpTable "[[1,3,2,0],[2,0,1,3],[0,1,2,3],[0,1,2,3]]"

@[implicit_reducible]
def «OneVariable M15873^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,0],[3,0,1,1],[2,1,2,2],[0,3,3,3]]"

@[implicit_reducible]
def «OneVariable M15874» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,0,0],[2,0,1,0,2],[0,1,2,1,0],[1,0,1,3,0],[0,1,3,0,4]]"

@[implicit_reducible]
def «OneVariable M15874^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,0,1,0],[4,0,1,0,1],[3,1,2,1,3],[0,0,1,3,0],[0,2,0,0,4]]"

@[implicit_reducible]
def «OneVariable M15876» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,0],[3,1,0,0],[0,0,2,0],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M15878» : Magma (Fin 6) where
  op := finOpTable "[[1,4,2,5,0,3],[4,2,3,1,0,5],[0,3,5,1,2,4],[5,1,1,3,2,5],[0,0,2,2,4,2],[3,1,4,5,2,0]]"

@[implicit_reducible]
def «OneVariable M15878^op» : Magma (Fin 6) where
  op := finOpTable "[[1,4,0,5,0,3],[4,2,3,1,0,1],[2,3,5,1,2,4],[5,1,1,3,2,5],[0,0,2,2,4,2],[3,5,4,5,2,0]]"

@[implicit_reducible]
def «OneVariable M15880» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,0],[3,1,2,0],[0,0,2,1],[0,0,1,3]]"

@[implicit_reducible]
def «OneVariable M15880^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,0],[2,1,0,0],[0,2,2,1],[0,0,1,3]]"

@[implicit_reducible]
def «OneVariable M15884» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,0],[2,1,2,0],[0,0,2,1],[0,0,1,3]]"

@[implicit_reducible]
def «OneVariable M15884^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,0],[3,1,0,0],[0,2,2,1],[0,0,1,3]]"

@[implicit_reducible]
def «OneVariable M15890» : Magma (Fin 8) where
  op := finOpTable "[[1,5,0,6,0,0,3,7],[2,4,1,1,3,0,6,1],[0,0,2,0,4,5,7,7],[6,1,7,3,1,1,6,4],[0,3,7,1,7,4,4,5],[0,0,5,1,4,5,6,4],[3,6,7,6,4,6,0,2],[7,1,7,4,5,4,2,6]]"

@[implicit_reducible]
def «OneVariable M15890^op» : Magma (Fin 8) where
  op := finOpTable "[[1,2,0,6,0,0,3,7],[5,4,0,1,3,0,6,1],[0,1,2,7,7,5,7,7],[6,1,0,3,1,1,6,4],[0,3,4,1,7,4,4,5],[0,0,5,1,4,5,6,4],[3,6,7,6,4,6,0,2],[7,1,7,4,5,4,2,6]]"

@[implicit_reducible]
def «OneVariable M15891» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,0],[3,0,1,1],[0,1,2,3],[0,1,3,3]]"

@[implicit_reducible]
def «OneVariable M15892» : Magma (Fin 4) where
  op := finOpTable "[[1,2,1,0],[0,3,2,1],[1,0,2,0],[0,1,2,3]]"

@[implicit_reducible]
def «OneVariable M15892^op» : Magma (Fin 4) where
  op := finOpTable "[[1,0,1,0],[2,3,0,1],[1,2,2,2],[0,1,0,3]]"

@[implicit_reducible]
def «OneVariable M15894» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[0,1,0,1],[1,3,2,0],[0,0,0,3]]"

@[implicit_reducible]
def «OneVariable M15894^op» : Magma (Fin 4) where
  op := finOpTable "[[1,0,1,0],[2,1,3,0],[3,0,2,0],[0,1,0,3]]"

end OneVariable
