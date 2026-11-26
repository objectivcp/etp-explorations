import Mathlib.Data.Finite.Prod
import ExplorationLaws
import equational_theories.FactsSyntax
import equational_theories.MemoFinOp
import equational_theories.DecideBang
import equational_theories.EquationalResult

set_option linter.unusedVariables false

namespace Order3

@[implicit_reducible]
def «Order3 M1» : Magma (Fin 9) where
  op := finOpTable "[[0,2,3,4,1,6,7,8,5],[5,1,7,8,2,3,4,6,0],[8,3,2,6,7,1,5,0,4],[7,6,4,3,5,8,0,1,2],[6,8,5,1,4,0,2,3,7],[3,4,0,7,8,5,1,2,6],[2,0,8,5,3,7,6,4,1],[1,5,6,2,0,4,8,7,3],[4,7,1,0,6,2,3,5,8]]"

@[implicit_reducible]
def «Order3 M2» : Magma (Fin 5) where
  op := finOpTable "[[0,2,3,0,0],[4,1,4,4,1],[2,2,2,2,2],[3,3,3,3,3],[4,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M2^op» : Magma (Fin 5) where
  op := finOpTable "[[0,4,2,3,4],[2,1,2,3,4],[3,4,2,3,4],[0,4,2,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «Order3 M3» : Magma (Fin 3) where
  op := finOpTable "[[0,1,1],[0,1,2],[0,1,0]]"

@[implicit_reducible]
def «Order3 M3^op» : Magma (Fin 3) where
  op := finOpTable "[[0,0,0],[1,1,1],[1,2,0]]"

@[implicit_reducible]
def «Order3 M4» : Magma (Fin 3) where
  op := finOpTable "[[0,0,0],[2,2,1],[1,2,1]]"

@[implicit_reducible]
def «Order3 M4^op» : Magma (Fin 3) where
  op := finOpTable "[[0,2,1],[0,2,2],[0,1,1]]"

@[implicit_reducible]
def «Order3 M5» : Magma (Fin 3) where
  op := finOpTable "[[0,1,2],[0,0,2],[0,0,1]]"

@[implicit_reducible]
def «Order3 M5^op» : Magma (Fin 3) where
  op := finOpTable "[[0,0,0],[1,0,0],[2,2,1]]"

@[implicit_reducible]
def «Order3 M6» : Magma (Fin 3) where
  op := finOpTable "[[0,0,2],[0,0,2],[0,1,2]]"

@[implicit_reducible]
def «Order3 M6^op» : Magma (Fin 3) where
  op := finOpTable "[[0,0,0],[0,0,1],[2,2,2]]"

@[implicit_reducible]
def «Order3 M8» : Magma (Fin 3) where
  op := finOpTable "[[0,0,0],[2,0,2],[1,1,0]]"

@[implicit_reducible]
def «Order3 M8^op» : Magma (Fin 3) where
  op := finOpTable "[[0,2,1],[0,0,1],[0,2,0]]"

@[implicit_reducible]
def «Order3 M9» : Magma (Fin 3) where
  op := finOpTable "[[0,0,0],[0,0,0],[2,0,2]]"

@[implicit_reducible]
def «Order3 M9^op» : Magma (Fin 3) where
  op := finOpTable "[[0,0,2],[0,0,0],[0,0,2]]"

@[implicit_reducible]
def «Order3 M11» : Magma (Fin 3) where
  op := finOpTable "[[0,0,0],[0,0,1],[0,1,0]]"

@[implicit_reducible]
def «Order3 M12» : Magma (Fin 3) where
  op := finOpTable "[[0,0,2],[0,0,2],[0,2,2]]"

@[implicit_reducible]
def «Order3 M12^op» : Magma (Fin 3) where
  op := finOpTable "[[0,0,0],[0,0,2],[2,2,2]]"

@[implicit_reducible]
def «Order3 M15» : Magma (Fin 3) where
  op := finOpTable "[[0,2,1],[2,1,0],[1,0,2]]"

@[implicit_reducible]
def «Order3 M17» : Magma (Fin 4) where
  op := finOpTable "[[3,3,2,3],[3,2,2,3],[2,2,2,3],[3,3,2,3]]"

@[implicit_reducible]
def «Order3 M17^op» : Magma (Fin 4) where
  op := finOpTable "[[3,3,2,3],[3,2,2,3],[2,2,2,2],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M18» : Magma (Fin 4) where
  op := finOpTable "[[0,1,3,1],[3,2,3,1],[2,0,1,0],[2,0,2,3]]"

@[implicit_reducible]
def «Order3 M19» : Magma (Fin 4) where
  op := finOpTable "[[3,3,2,1],[3,3,2,0],[0,1,3,2],[2,2,0,3]]"

@[implicit_reducible]
def «Order3 M19^op» : Magma (Fin 4) where
  op := finOpTable "[[3,3,0,2],[3,3,1,2],[2,2,3,0],[1,0,2,3]]"

@[implicit_reducible]
def «Order3 M20» : Magma (Fin 4) where
  op := finOpTable "[[3,3,1,3],[3,3,3,3],[2,2,2,2],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M20^op» : Magma (Fin 4) where
  op := finOpTable "[[3,3,2,3],[3,3,2,3],[1,3,2,3],[3,3,2,3]]"

@[implicit_reducible]
def «Order3 M21» : Magma (Fin 4) where
  op := finOpTable "[[0,2,3,1],[2,0,1,3],[3,1,0,2],[1,3,2,0]]"

@[implicit_reducible]
def «Order3 M22» : Magma (Fin 4) where
  op := finOpTable "[[3,0,3,3],[3,3,3,3],[2,2,3,3],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M22^op» : Magma (Fin 4) where
  op := finOpTable "[[3,3,2,3],[0,3,2,3],[3,3,3,3],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M23» : Magma (Fin 4) where
  op := finOpTable "[[2,0,1,1],[3,0,3,1],[2,0,3,0],[2,2,3,1]]"

@[implicit_reducible]
def «Order3 M23^op» : Magma (Fin 4) where
  op := finOpTable "[[2,3,2,2],[0,0,0,2],[1,3,3,3],[1,1,0,1]]"

@[implicit_reducible]
def «Order3 M26» : Magma (Fin 5) where
  op := finOpTable "[[4,3,0,1,0],[2,4,0,1,1],[2,3,4,1,2],[2,3,0,4,3],[4,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M26^op» : Magma (Fin 5) where
  op := finOpTable "[[4,2,2,2,4],[3,4,3,3,4],[0,0,4,0,4],[1,1,1,4,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «Order3 M28» : Magma (Fin 5) where
  op := finOpTable "[[0,0,4,0,0],[2,2,2,2,2],[3,3,3,3,3],[1,1,1,1,1],[4,4,0,4,4]]"

@[implicit_reducible]
def «Order3 M28^op» : Magma (Fin 5) where
  op := finOpTable "[[0,2,3,1,4],[0,2,3,1,4],[4,2,3,1,0],[0,2,3,1,4],[0,2,3,1,4]]"

@[implicit_reducible]
def «Order3 M29» : Magma (Fin 5) where
  op := finOpTable "[[4,2,4,2,4],[3,4,3,4,4],[2,2,2,2,2],[3,3,3,3,3],[4,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M29^op» : Magma (Fin 5) where
  op := finOpTable "[[4,3,2,3,4],[2,4,2,3,4],[4,3,2,3,4],[2,4,2,3,4],[4,4,2,3,4]]"

@[implicit_reducible]
def «Order3 M30» : Magma (Fin 7) where
  op := finOpTable "[[0,2,5,6,3,1,4],[2,1,3,0,6,4,5],[5,3,2,4,1,6,0],[6,0,4,3,5,2,1],[3,6,1,5,4,0,2],[1,4,6,2,0,5,3],[4,5,0,1,2,3,6]]"

@[implicit_reducible]
def «Order3 M32» : Magma (Fin 5) where
  op := finOpTable "[[3,2,3,3,3],[1,4,1,1,4],[2,3,2,2,0],[0,0,0,0,2],[4,1,4,4,1]]"

@[implicit_reducible]
def «Order3 M32^op» : Magma (Fin 5) where
  op := finOpTable "[[3,1,2,0,4],[2,4,3,0,1],[3,1,2,0,4],[3,1,2,0,4],[3,4,0,2,1]]"

@[implicit_reducible]
def «Order3 M33» : Magma (Fin 3) where
  op := finOpTable "[[0,0,1],[0,2,2],[1,1,1]]"

@[implicit_reducible]
def «Order3 M33^op» : Magma (Fin 3) where
  op := finOpTable "[[0,0,1],[0,2,1],[1,2,1]]"

@[implicit_reducible]
def «Order3 M34» : Magma (Fin 4) where
  op := finOpTable "[[0,1,2,3],[0,1,2,3],[1,2,3,0],[3,0,1,2]]"

@[implicit_reducible]
def «Order3 M34^op» : Magma (Fin 4) where
  op := finOpTable "[[0,0,1,3],[1,1,2,0],[2,2,3,1],[3,3,0,2]]"

@[implicit_reducible]
def «Order3 M35» : Magma (Fin 4) where
  op := finOpTable "[[3,3,0,0],[3,3,1,1],[2,2,0,2],[3,3,3,2]]"

@[implicit_reducible]
def «Order3 M35^op» : Magma (Fin 4) where
  op := finOpTable "[[3,3,2,3],[3,3,2,3],[0,1,0,3],[0,1,2,2]]"

@[implicit_reducible]
def «Order3 M37» : Magma (Fin 4) where
  op := finOpTable "[[0,1,2,3],[0,1,2,3],[0,1,2,3],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M37^op» : Magma (Fin 4) where
  op := finOpTable "[[0,0,0,0],[1,1,1,1],[2,2,2,2],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M38» : Magma (Fin 4) where
  op := finOpTable "[[0,0,2,1],[3,1,0,3],[2,2,3,0],[1,3,1,2]]"

@[implicit_reducible]
def «Order3 M38^op» : Magma (Fin 4) where
  op := finOpTable "[[0,3,2,1],[0,1,2,3],[2,0,3,1],[1,3,0,2]]"

@[implicit_reducible]
def «Order3 M39» : Magma (Fin 4) where
  op := finOpTable "[[0,3,0,3],[3,1,1,3],[0,1,0,3],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M40» : Magma (Fin 4) where
  op := finOpTable "[[3,3,0,3],[3,3,1,3],[2,2,3,3],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M40^op» : Magma (Fin 4) where
  op := finOpTable "[[3,3,2,3],[3,3,2,3],[0,1,3,3],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M41» : Magma (Fin 4) where
  op := finOpTable "[[3,2,3,3],[3,2,2,2],[1,1,1,0],[0,0,1,0]]"

@[implicit_reducible]
def «Order3 M41^op» : Magma (Fin 4) where
  op := finOpTable "[[3,3,1,0],[2,2,1,0],[3,2,1,1],[3,2,0,0]]"

@[implicit_reducible]
def «Order3 M43» : Magma (Fin 4) where
  op := finOpTable "[[3,3,1,3],[3,3,1,3],[1,1,1,1],[3,3,0,3]]"

@[implicit_reducible]
def «Order3 M43^op» : Magma (Fin 4) where
  op := finOpTable "[[3,3,1,3],[3,3,1,3],[1,1,1,0],[3,3,1,3]]"

@[implicit_reducible]
def «Order3 M44» : Magma (Fin 2) where
  op := finOpTable "[[1,0],[1,1]]"

@[implicit_reducible]
def «Order3 M44^op» : Magma (Fin 2) where
  op := finOpTable "[[1,1],[0,1]]"

@[implicit_reducible]
def «Order3 M45» : Magma (Fin 3) where
  op := finOpTable "[[1,2,0],[2,0,1],[0,1,2]]"

@[implicit_reducible]
def «Order3 M47» : Magma (Fin 4) where
  op := finOpTable "[[1,0,3,2],[3,2,1,0],[2,3,0,1],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M47^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,2,0],[0,2,3,1],[3,1,0,2],[2,0,1,3]]"

@[implicit_reducible]
def «Order3 M48» : Magma (Fin 2) where
  op := finOpTable "[[1,1],[1,0]]"

@[implicit_reducible]
def «Order3 M49» : Magma (Fin 5) where
  op := finOpTable "[[0,4,1,2,3],[4,1,3,0,2],[1,3,2,4,0],[2,0,4,3,1],[3,2,0,1,4]]"

@[implicit_reducible]
def «Order3 M50» : Magma (Fin 5) where
  op := finOpTable "[[0,4,1,2,3],[3,1,0,4,2],[4,3,2,0,1],[1,2,4,3,0],[2,0,3,1,4]]"

@[implicit_reducible]
def «Order3 M50^op» : Magma (Fin 5) where
  op := finOpTable "[[0,3,4,1,2],[4,1,3,2,0],[1,0,2,4,3],[2,4,0,3,1],[3,2,1,0,4]]"

@[implicit_reducible]
def «Order3 M51» : Magma (Fin 5) where
  op := finOpTable "[[0,3,3,3,4],[2,1,2,4,4],[0,1,2,3,4],[4,1,2,3,4],[0,2,2,3,4]]"

@[implicit_reducible]
def «Order3 M51^op» : Magma (Fin 5) where
  op := finOpTable "[[0,2,0,4,0],[3,1,1,1,2],[3,2,2,2,2],[3,4,3,3,3],[4,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M52» : Magma (Fin 5) where
  op := finOpTable "[[4,4,4,2,4],[3,4,4,4,4],[4,4,4,4,4],[4,4,4,4,4],[4,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M52^op» : Magma (Fin 5) where
  op := finOpTable "[[4,3,4,4,4],[4,4,4,4,4],[4,4,4,4,4],[2,4,4,4,4],[4,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M53» : Magma (Fin 9) where
  op := finOpTable "[[2,3,3,3,2,2,5,5,5],[8,8,7,7,8,7,6,6,6],[4,4,0,0,4,0,5,5,5],[2,3,3,3,2,2,1,1,1],[4,4,0,0,4,0,1,1,1],[8,8,7,7,8,7,6,6,6],[8,8,7,7,8,7,6,6,6],[2,3,3,3,2,2,5,5,5],[4,4,0,0,4,0,1,1,1]]"

@[implicit_reducible]
def «Order3 M54» : Magma (Fin 3) where
  op := finOpTable "[[2,0,1],[1,2,0],[0,1,2]]"

@[implicit_reducible]
def «Order3 M54^op» : Magma (Fin 3) where
  op := finOpTable "[[2,1,0],[0,2,1],[1,0,2]]"

@[implicit_reducible]
def «Order3 M56» : Magma (Fin 3) where
  op := finOpTable "[[2,1,0],[1,2,1],[0,1,2]]"

@[implicit_reducible]
def «Order3 M57» : Magma (Fin 4) where
  op := finOpTable "[[0,3,1,2],[2,1,3,0],[3,0,2,1],[1,2,0,3]]"

@[implicit_reducible]
def «Order3 M58» : Magma (Fin 5) where
  op := finOpTable "[[4,3,1,2,0],[2,4,3,0,1],[3,0,4,1,2],[1,2,0,4,3],[0,1,2,3,4]]"

@[implicit_reducible]
def «Order3 M59» : Magma (Fin 3) where
  op := finOpTable "[[2,0,0],[1,2,1],[0,1,2]]"

@[implicit_reducible]
def «Order3 M59^op» : Magma (Fin 3) where
  op := finOpTable "[[2,1,0],[0,2,1],[0,1,2]]"

@[implicit_reducible]
def «Order3 M61» : Magma (Fin 3) where
  op := finOpTable "[[0,2,2],[2,1,2],[0,1,2]]"

@[implicit_reducible]
def «Order3 M61^op» : Magma (Fin 3) where
  op := finOpTable "[[0,2,0],[2,1,1],[2,2,2]]"

@[implicit_reducible]
def «Order3 M63» : Magma (Fin 3) where
  op := finOpTable "[[0,1,2],[2,1,0],[0,1,2]]"

@[implicit_reducible]
def «Order3 M63^op» : Magma (Fin 3) where
  op := finOpTable "[[0,2,0],[1,1,1],[2,0,2]]"

@[implicit_reducible]
def «Order3 M65» : Magma (Fin 3) where
  op := finOpTable "[[2,2,2],[0,0,0],[1,1,1]]"

@[implicit_reducible]
def «Order3 M65^op» : Magma (Fin 3) where
  op := finOpTable "[[2,0,1],[2,0,1],[2,0,1]]"

@[implicit_reducible]
def «Order3 M67» : Magma (Fin 3) where
  op := finOpTable "[[1,1,0],[1,2,2],[0,2,0]]"

@[implicit_reducible]
def «Order3 M68» : Magma (Fin 4) where
  op := finOpTable "[[0,1,2,3],[0,3,1,0],[0,0,1,2],[0,3,0,2]]"

@[implicit_reducible]
def «Order3 M68^op» : Magma (Fin 4) where
  op := finOpTable "[[0,0,0,0],[1,3,0,3],[2,1,1,0],[3,0,2,2]]"

@[implicit_reducible]
def «Order3 M70» : Magma (Fin 3) where
  op := finOpTable "[[1,2,2],[2,1,0],[0,0,1]]"

@[implicit_reducible]
def «Order3 M70^op» : Magma (Fin 3) where
  op := finOpTable "[[1,2,0],[2,1,0],[2,0,1]]"

@[implicit_reducible]
def «Order3 M72» : Magma (Fin 3) where
  op := finOpTable "[[1,2,1],[2,0,0],[0,1,2]]"

@[implicit_reducible]
def «Order3 M72^op» : Magma (Fin 3) where
  op := finOpTable "[[1,2,0],[2,0,1],[1,0,2]]"

@[implicit_reducible]
def «Order3 M74» : Magma (Fin 4) where
  op := finOpTable "[[2,0,1,3],[1,3,2,0],[3,1,0,2],[0,2,3,1]]"

@[implicit_reducible]
def «Order3 M75» : Magma (Fin 5) where
  op := finOpTable "[[4,0,0,1,4],[0,1,2,3,4],[2,2,3,3,1],[0,3,1,0,3],[1,4,2,4,2]]"

@[implicit_reducible]
def «Order3 M75^op» : Magma (Fin 5) where
  op := finOpTable "[[4,0,2,0,1],[0,1,2,3,4],[0,2,3,1,2],[1,3,3,0,4],[4,4,1,3,2]]"

@[implicit_reducible]
def «Order3 M77» : Magma (Fin 3) where
  op := finOpTable "[[2,1,1],[0,2,2],[0,1,2]]"

@[implicit_reducible]
def «Order3 M77^op» : Magma (Fin 3) where
  op := finOpTable "[[2,0,0],[1,2,1],[1,2,2]]"

@[implicit_reducible]
def «Order3 M79» : Magma (Fin 4) where
  op := finOpTable "[[2,1,1,2],[0,3,3,0],[3,0,0,3],[1,2,2,1]]"

@[implicit_reducible]
def «Order3 M79^op» : Magma (Fin 4) where
  op := finOpTable "[[2,0,3,1],[1,3,0,2],[1,3,0,2],[2,0,3,1]]"

@[implicit_reducible]
def «Order3 M81» : Magma (Fin 5) where
  op := finOpTable "[[2,0,4,1,3],[1,3,0,4,2],[3,4,1,2,0],[4,2,3,0,1],[0,1,2,3,4]]"

@[implicit_reducible]
def «Order3 M81^op» : Magma (Fin 5) where
  op := finOpTable "[[2,1,3,4,0],[0,3,4,2,1],[4,0,1,3,2],[1,4,2,0,3],[3,2,0,1,4]]"

@[implicit_reducible]
def «Order3 M83» : Magma (Fin 3) where
  op := finOpTable "[[1,2,2],[2,0,2],[0,1,2]]"

@[implicit_reducible]
def «Order3 M83^op» : Magma (Fin 3) where
  op := finOpTable "[[1,2,0],[2,0,1],[2,2,2]]"

@[implicit_reducible]
def «Order3 M85» : Magma (Fin 5) where
  op := finOpTable "[[0,1,2,3,4],[1,4,2,0,1],[2,1,3,2,0],[3,3,0,1,4],[4,0,4,3,2]]"

@[implicit_reducible]
def «Order3 M85^op» : Magma (Fin 5) where
  op := finOpTable "[[0,1,2,3,4],[1,4,1,3,0],[2,2,3,0,4],[3,0,2,1,3],[4,1,0,4,2]]"

@[implicit_reducible]
def «Order3 M87» : Magma (Fin 4) where
  op := finOpTable "[[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,1,0]]"

@[implicit_reducible]
def «Order3 M88» : Magma (Fin 4) where
  op := finOpTable "[[0,0,0,0],[0,0,0,2],[2,2,2,2],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M88^op» : Magma (Fin 4) where
  op := finOpTable "[[0,0,2,3],[0,0,2,3],[0,0,2,3],[0,2,2,3]]"

@[implicit_reducible]
def «Order3 M90» : Magma (Fin 4) where
  op := finOpTable "[[0,1,2,3],[1,0,3,2],[2,3,0,1],[3,2,1,0]]"

@[implicit_reducible]
def «Order3 M91» : Magma (Fin 4) where
  op := finOpTable "[[0,0,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]]"

@[implicit_reducible]
def «Order3 M92» : Magma (Fin 4) where
  op := finOpTable "[[0,0,0,0],[0,1,1,1],[0,1,2,1],[0,1,1,3]]"

@[implicit_reducible]
def «Order3 M93» : Magma (Fin 27) where
  op := finOpTable "[[2,6,3,0,7,8,9,10,11,1,4,5,20,17,16,12,19,18,13,14,15,24,25,22,26,23,21],[4,12,5,1,14,17,13,15,19,16,18,20,3,23,0,22,24,2,26,25,21,11,7,6,9,8,10],[3,9,0,2,10,11,1,4,5,6,7,8,15,18,19,20,14,13,17,16,12,26,23,25,21,22,24],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26],[5,13,1,4,15,19,16,18,20,12,14,17,21,2,24,3,25,26,23,0,22,9,8,7,10,6,11],[1,16,4,5,18,20,12,14,17,13,15,19,22,26,25,21,0,23,2,24,3,10,6,8,11,7,9],[7,20,8,6,16,18,17,12,14,19,13,15,0,22,2,25,26,3,21,23,24,5,10,9,1,11,4],[8,17,6,7,12,14,19,13,15,20,16,18,24,3,26,0,23,21,22,2,25,1,11,10,4,9,5],[6,19,7,8,13,15,20,16,18,17,12,14,25,21,23,24,2,22,3,26,0,4,9,11,5,10,1],[10,15,11,9,19,13,18,20,16,14,17,12,2,25,3,23,21,0,24,22,26,8,4,1,6,5,7],[11,18,9,10,20,16,14,17,12,15,19,13,26,0,21,2,22,24,25,3,23,6,5,4,7,1,8],[9,14,10,11,17,12,15,19,13,18,20,16,23,24,22,26,3,25,0,21,2,7,1,5,8,4,6],[14,3,17,12,0,2,23,22,25,24,26,21,1,6,4,7,9,5,10,8,11,20,15,13,16,19,18],[15,21,19,13,24,26,2,3,0,25,23,22,4,7,5,8,10,1,11,6,9,17,18,16,12,20,14],[17,23,12,14,22,25,24,26,21,3,0,2,11,5,9,1,8,10,6,4,7,16,19,15,18,13,20],[19,2,13,15,3,0,25,23,22,21,24,26,9,1,10,4,6,11,7,5,8,12,20,18,14,16,17],[18,22,20,16,25,23,26,21,24,0,2,3,5,8,1,6,11,4,9,7,10,19,14,12,13,17,15],[12,24,14,17,26,21,3,0,2,23,22,25,7,10,8,11,4,6,5,9,1,18,13,19,20,15,16],[20,26,16,18,21,24,0,2,3,22,25,23,10,4,11,5,7,9,8,1,6,13,17,14,15,12,19],[13,25,15,19,23,22,21,24,26,2,3,0,8,11,6,9,5,7,1,10,4,14,16,20,17,18,12],[16,0,18,20,2,3,22,25,23,26,21,24,6,9,7,10,1,8,4,11,5,15,12,17,19,14,13],[24,4,26,21,5,1,7,8,6,10,11,9,13,16,15,18,12,19,14,20,17,22,3,2,25,0,23],[25,5,23,22,1,4,8,6,7,11,9,10,16,12,18,14,13,20,15,17,19,3,21,26,0,24,2],[22,11,25,23,9,10,5,1,4,8,6,7,14,15,17,19,18,12,20,13,16,2,26,24,3,21,0],[26,7,21,24,8,6,10,11,9,4,5,1,17,19,12,13,20,14,16,15,18,25,0,3,23,2,22],[23,8,22,25,6,7,11,9,10,5,1,4,19,20,13,16,17,15,12,18,14,0,24,21,2,26,3],[21,10,24,26,11,9,4,5,1,7,8,6,18,14,20,17,15,16,19,12,13,23,2,0,22,3,25]]"

@[implicit_reducible]
def «Order3 M94» : Magma (Fin 15) where
  op := finOpTable "[[14,4,5,6,14,14,14,10,11,12,14,14,14,14,14],[4,14,7,8,14,10,11,14,14,13,14,14,14,14,14],[5,7,14,9,10,14,12,14,13,14,14,14,14,14,14],[6,8,9,14,11,12,14,13,14,14,14,14,14,14,14],[14,14,10,11,14,14,14,14,14,14,14,14,14,14,14],[14,10,14,12,14,14,14,14,14,14,14,14,14,14,14],[14,11,12,14,14,14,14,14,14,14,14,14,14,14,14],[10,14,14,13,14,14,14,14,14,14,14,14,14,14,14],[11,14,13,14,14,14,14,14,14,14,14,14,14,14,14],[12,13,14,14,14,14,14,14,14,14,14,14,14,14,14],[14,14,14,14,14,14,14,14,14,14,14,14,14,14,14],[14,14,14,14,14,14,14,14,14,14,14,14,14,14,14],[14,14,14,14,14,14,14,14,14,14,14,14,14,14,14],[14,14,14,14,14,14,14,14,14,14,14,14,14,14,14],[14,14,14,14,14,14,14,14,14,14,14,14,14,14,14]]"

@[implicit_reducible]
def «Order3 M95» : Magma (Fin 16) where
  op := finOpTable "[[15,5,6,7,8,15,15,15,15,15,15,15,15,15,15,15],[5,15,9,10,11,15,15,15,15,15,15,15,15,15,15,15],[6,9,15,12,13,15,15,15,15,15,15,15,15,15,15,15],[7,10,12,15,14,15,15,15,15,15,15,15,15,15,15,15],[8,11,13,14,15,15,15,15,15,15,15,15,15,15,15,15],[15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15],[15,15,15,15,15,15,15,15,15,15,15,15,15,15,15,15]]"

@[implicit_reducible]
def «Order3 M96» : Magma (Fin 7) where
  op := finOpTable "[[0,3,4,6,5,2,1],[2,1,6,5,3,4,0],[1,5,2,4,6,0,3],[4,0,5,3,1,6,2],[3,6,0,2,4,1,5],[6,2,3,1,0,5,4],[5,4,1,0,2,3,6]]"

@[implicit_reducible]
def «Order3 M96^op» : Magma (Fin 7) where
  op := finOpTable "[[0,2,1,4,3,6,5],[3,1,5,0,6,2,4],[4,6,2,5,0,3,1],[6,5,4,3,2,1,0],[5,3,6,1,4,0,2],[2,4,0,6,1,5,3],[1,0,3,2,5,4,6]]"

@[implicit_reducible]
def «Order3 M98» : Magma (Fin 8) where
  op := finOpTable "[[0,4,5,6,7,1,2,3],[2,1,3,7,6,4,0,5],[3,6,2,4,1,7,5,0],[4,0,7,3,5,2,1,6],[5,7,0,1,4,6,3,2],[6,3,1,0,2,5,7,4],[7,5,4,2,0,3,6,1],[1,2,6,5,3,0,4,7]]"

@[implicit_reducible]
def «Order3 M98^op» : Magma (Fin 8) where
  op := finOpTable "[[0,2,3,4,5,6,7,1],[4,1,6,0,7,3,5,2],[5,3,2,7,0,1,4,6],[6,7,4,3,1,0,2,5],[7,6,1,5,4,2,0,3],[1,4,7,2,6,5,3,0],[2,0,5,1,3,7,6,4],[3,5,0,6,2,4,1,7]]"

@[implicit_reducible]
def «Order3 M101» : Magma (Fin 3) where
  op := finOpTable "[[0,0,1],[1,1,1],[1,2,0]]"

@[implicit_reducible]
def «Order3 M101^op» : Magma (Fin 3) where
  op := finOpTable "[[0,1,1],[0,1,2],[1,1,0]]"

@[implicit_reducible]
def «Order3 M102» : Magma (Fin 3) where
  op := finOpTable "[[0,0,0],[0,0,2],[0,0,0]]"

@[implicit_reducible]
def «Order3 M102^op» : Magma (Fin 3) where
  op := finOpTable "[[0,0,0],[0,0,0],[0,2,0]]"

@[implicit_reducible]
def «Order3 M104» : Magma (Fin 3) where
  op := finOpTable "[[0,1,2],[0,1,2],[0,0,2]]"

@[implicit_reducible]
def «Order3 M104^op» : Magma (Fin 3) where
  op := finOpTable "[[0,0,0],[1,1,0],[2,2,2]]"

@[implicit_reducible]
def «Order3 M105» : Magma (Fin 3) where
  op := finOpTable "[[0,2,1],[0,1,1],[0,2,2]]"

@[implicit_reducible]
def «Order3 M105^op» : Magma (Fin 3) where
  op := finOpTable "[[0,0,0],[2,1,2],[1,1,2]]"

@[implicit_reducible]
def «Order3 M110» : Magma (Fin 3) where
  op := finOpTable "[[0,1,2],[0,0,1],[0,0,0]]"

@[implicit_reducible]
def «Order3 M110^op» : Magma (Fin 3) where
  op := finOpTable "[[0,0,0],[1,0,0],[2,1,0]]"

@[implicit_reducible]
def «Order3 M112» : Magma (Fin 4) where
  op := finOpTable "[[3,3,2,3],[0,0,2,0],[0,1,2,3],[1,1,2,1]]"

@[implicit_reducible]
def «Order3 M112^op» : Magma (Fin 4) where
  op := finOpTable "[[3,0,0,1],[3,0,1,1],[2,2,2,2],[3,0,3,1]]"

@[implicit_reducible]
def «Order3 M113» : Magma (Fin 4) where
  op := finOpTable "[[0,2,3,1],[2,0,1,3],[1,3,2,0],[3,1,0,2]]"

@[implicit_reducible]
def «Order3 M113^op» : Magma (Fin 4) where
  op := finOpTable "[[0,2,1,3],[2,0,3,1],[3,1,2,0],[1,3,0,2]]"

@[implicit_reducible]
def «Order3 M114» : Magma (Fin 4) where
  op := finOpTable "[[3,3,2,3],[0,3,3,3],[3,1,3,3],[1,2,0,3]]"

@[implicit_reducible]
def «Order3 M114^op» : Magma (Fin 4) where
  op := finOpTable "[[3,0,3,1],[3,3,1,2],[2,3,3,0],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M115» : Magma (Fin 4) where
  op := finOpTable "[[0,1,2,3],[0,1,3,2],[3,1,2,0],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M115^op» : Magma (Fin 4) where
  op := finOpTable "[[0,0,3,0],[1,1,1,1],[2,3,2,2],[3,2,0,3]]"

@[implicit_reducible]
def «Order3 M116» : Magma (Fin 4) where
  op := finOpTable "[[2,3,2,3],[2,3,2,3],[2,2,2,2],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M116^op» : Magma (Fin 4) where
  op := finOpTable "[[2,2,2,3],[3,3,2,3],[2,2,2,3],[3,3,2,3]]"

@[implicit_reducible]
def «Order3 M118» : Magma (Fin 4) where
  op := finOpTable "[[1,1,2,1],[0,1,2,3],[0,1,2,3],[1,1,2,2]]"

@[implicit_reducible]
def «Order3 M118^op» : Magma (Fin 4) where
  op := finOpTable "[[1,0,0,1],[1,1,1,1],[2,2,2,2],[1,3,3,2]]"

@[implicit_reducible]
def «Order3 M119» : Magma (Fin 4) where
  op := finOpTable "[[3,3,1,3],[1,3,1,3],[3,3,3,3],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M119^op» : Magma (Fin 4) where
  op := finOpTable "[[3,1,3,3],[3,3,3,3],[1,1,3,3],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M120» : Magma (Fin 4) where
  op := finOpTable "[[3,3,1,3],[1,1,1,1],[3,1,1,1],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M120^op» : Magma (Fin 4) where
  op := finOpTable "[[3,1,3,3],[3,1,1,3],[1,1,1,3],[3,1,1,3]]"

@[implicit_reducible]
def «Order3 M121» : Magma (Fin 4) where
  op := finOpTable "[[0,1,1,0],[3,1,1,3],[3,2,2,3],[3,2,2,3]]"

@[implicit_reducible]
def «Order3 M121^op» : Magma (Fin 4) where
  op := finOpTable "[[0,3,3,3],[1,1,2,2],[1,1,2,2],[0,3,3,3]]"

@[implicit_reducible]
def «Order3 M122» : Magma (Fin 4) where
  op := finOpTable "[[3,1,1,3],[1,1,3,3],[1,1,1,3],[1,1,1,3]]"

@[implicit_reducible]
def «Order3 M122^op» : Magma (Fin 4) where
  op := finOpTable "[[3,1,1,1],[1,1,1,1],[1,3,1,1],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M124» : Magma (Fin 4) where
  op := finOpTable "[[3,2,2,2],[2,3,3,3],[0,0,1,0],[1,1,0,1]]"

@[implicit_reducible]
def «Order3 M124^op» : Magma (Fin 4) where
  op := finOpTable "[[3,2,0,1],[2,3,0,1],[2,3,1,0],[2,3,0,1]]"

@[implicit_reducible]
def «Order3 M125» : Magma (Fin 4) where
  op := finOpTable "[[0,0,0,1],[1,1,1,2],[2,2,2,0],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M125^op» : Magma (Fin 4) where
  op := finOpTable "[[0,1,2,3],[0,1,2,3],[0,1,2,3],[1,2,0,3]]"

@[implicit_reducible]
def «Order3 M134» : Magma (Fin 4) where
  op := finOpTable "[[3,1,2,0],[0,2,1,3],[3,2,1,0],[3,1,2,0]]"

@[implicit_reducible]
def «Order3 M134^op» : Magma (Fin 4) where
  op := finOpTable "[[3,0,3,3],[1,2,2,1],[2,1,1,2],[0,3,0,0]]"

@[implicit_reducible]
def «Order3 M137» : Magma (Fin 6) where
  op := finOpTable "[[2,3,0,3,0,2],[2,1,5,1,5,2],[2,1,0,1,0,2],[4,3,0,3,0,4],[4,3,5,3,5,4],[4,1,5,1,5,4]]"

@[implicit_reducible]
def «Order3 M137^op» : Magma (Fin 6) where
  op := finOpTable "[[2,2,2,4,4,4],[3,1,1,3,3,1],[0,5,0,0,5,5],[3,1,1,3,3,1],[0,5,0,0,5,5],[2,2,2,4,4,4]]"

@[implicit_reducible]
def «Order3 M138» : Magma (Fin 5) where
  op := finOpTable "[[2,4,0,1,4],[2,3,4,1,4],[2,3,0,4,4],[4,3,0,1,4],[2,3,0,1,4]]"

@[implicit_reducible]
def «Order3 M138^op» : Magma (Fin 5) where
  op := finOpTable "[[2,2,2,4,2],[4,3,3,3,3],[0,4,0,0,0],[1,1,4,1,1],[4,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M141» : Magma (Fin 5) where
  op := finOpTable "[[1,2,1,1,0],[4,4,4,1,1],[3,3,3,0,2],[4,3,4,4,3],[4,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M141^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,3,4,4],[2,4,3,3,4],[1,4,3,4,4],[1,1,0,4,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «Order3 M142» : Magma (Fin 5) where
  op := finOpTable "[[0,3,2,1,4],[2,3,4,1,0],[0,3,2,1,4],[4,3,0,1,2],[0,3,2,1,4]]"

@[implicit_reducible]
def «Order3 M142^op» : Magma (Fin 5) where
  op := finOpTable "[[0,2,0,4,0],[3,3,3,3,3],[2,4,2,0,2],[1,1,1,1,1],[4,0,4,2,4]]"

@[implicit_reducible]
def «Order3 M144» : Magma (Fin 5) where
  op := finOpTable "[[4,4,4,4,4],[2,4,2,2,4],[3,1,4,3,4],[4,2,2,4,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «Order3 M144^op» : Magma (Fin 5) where
  op := finOpTable "[[4,2,3,4,0],[4,4,1,2,1],[4,2,4,2,2],[4,2,3,4,3],[4,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M146» : Magma (Fin 7) where
  op := finOpTable "[[1,2,3,4,5,0,6],[5,4,2,6,0,3,1],[6,3,0,2,1,5,4],[3,1,6,5,2,4,0],[0,6,4,1,3,2,5],[2,5,1,0,4,6,3],[4,0,5,3,6,1,2]]"

@[implicit_reducible]
def «Order3 M146^op» : Magma (Fin 7) where
  op := finOpTable "[[1,5,6,3,0,2,4],[2,4,3,1,6,5,0],[3,2,0,6,4,1,5],[4,6,2,5,1,0,3],[5,0,1,2,3,4,6],[0,3,5,4,2,6,1],[6,1,4,0,5,3,2]]"

@[implicit_reducible]
def «Order3 M148» : Magma (Fin 3) where
  op := finOpTable "[[0,1,0],[0,1,1],[2,2,2]]"

@[implicit_reducible]
def «Order3 M148^op» : Magma (Fin 3) where
  op := finOpTable "[[0,0,2],[1,1,2],[0,1,2]]"

@[implicit_reducible]
def «Order3 M152» : Magma (Fin 4) where
  op := finOpTable "[[3,3,0,3],[3,3,0,3],[2,2,2,2],[3,3,0,3]]"

@[implicit_reducible]
def «Order3 M152^op» : Magma (Fin 4) where
  op := finOpTable "[[3,3,2,3],[3,3,2,3],[0,0,2,0],[3,3,2,3]]"

@[implicit_reducible]
def «Order3 M154» : Magma (Fin 4) where
  op := finOpTable "[[3,3,3,3],[3,3,1,3],[1,3,3,3],[1,3,1,3]]"

@[implicit_reducible]
def «Order3 M154^op» : Magma (Fin 4) where
  op := finOpTable "[[3,3,1,1],[3,3,3,3],[3,1,3,1],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M155» : Magma (Fin 4) where
  op := finOpTable "[[2,2,2,2],[3,3,3,3],[0,0,0,0],[1,1,1,1]]"

@[implicit_reducible]
def «Order3 M155^op» : Magma (Fin 4) where
  op := finOpTable "[[2,3,0,1],[2,3,0,1],[2,3,0,1],[2,3,0,1]]"

@[implicit_reducible]
def «Order3 M157» : Magma (Fin 4) where
  op := finOpTable "[[0,3,0,0],[1,1,3,1],[3,2,2,2],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M157^op» : Magma (Fin 4) where
  op := finOpTable "[[0,1,3,3],[3,1,2,3],[0,3,2,3],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M158» : Magma (Fin 4) where
  op := finOpTable "[[1,2,1,1],[0,1,2,3],[0,1,2,3],[1,2,2,1]]"

@[implicit_reducible]
def «Order3 M158^op» : Magma (Fin 4) where
  op := finOpTable "[[1,0,0,1],[2,1,1,2],[1,2,2,2],[1,3,3,1]]"

@[implicit_reducible]
def «Order3 M178» : Magma (Fin 4) where
  op := finOpTable "[[2,1,2,3],[3,2,2,3],[2,2,2,2],[1,1,2,2]]"

@[implicit_reducible]
def «Order3 M178^op» : Magma (Fin 4) where
  op := finOpTable "[[2,3,2,1],[1,2,2,1],[2,2,2,2],[3,3,2,2]]"

@[implicit_reducible]
def «Order3 M180» : Magma (Fin 4) where
  op := finOpTable "[[3,3,2,3],[3,3,2,3],[1,0,3,3],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M180^op» : Magma (Fin 4) where
  op := finOpTable "[[3,3,1,3],[3,3,0,3],[2,2,3,3],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M182» : Magma (Fin 4) where
  op := finOpTable "[[1,1,1,1],[1,1,1,1],[3,2,2,2],[2,3,3,3]]"

@[implicit_reducible]
def «Order3 M182^op» : Magma (Fin 4) where
  op := finOpTable "[[1,1,3,2],[1,1,2,3],[1,1,2,3],[1,1,2,3]]"

@[implicit_reducible]
def «Order3 M184» : Magma (Fin 3) where
  op := finOpTable "[[0,2,2],[1,2,2],[1,2,2]]"

@[implicit_reducible]
def «Order3 M184^op» : Magma (Fin 3) where
  op := finOpTable "[[0,1,1],[2,2,2],[2,2,2]]"

@[implicit_reducible]
def «Order3 M186» : Magma (Fin 5) where
  op := finOpTable "[[4,3,1,2,4],[2,4,3,0,4],[3,0,4,1,4],[1,2,0,4,4],[4,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M187» : Magma (Fin 6) where
  op := finOpTable "[[5,3,4,1,2,5],[4,5,3,2,0,5],[1,0,5,4,3,5],[2,4,0,5,1,5],[3,2,1,0,5,5],[5,5,5,5,5,5]]"

@[implicit_reducible]
def «Order3 M187^op» : Magma (Fin 6) where
  op := finOpTable "[[5,4,1,2,3,5],[3,5,0,4,2,5],[4,3,5,0,1,5],[1,2,4,5,0,5],[2,0,3,1,5,5],[5,5,5,5,5,5]]"

@[implicit_reducible]
def «Order3 M189» : Magma (Fin 3) where
  op := finOpTable "[[0,2,2],[1,2,2],[0,2,2]]"

@[implicit_reducible]
def «Order3 M189^op» : Magma (Fin 3) where
  op := finOpTable "[[0,1,0],[2,2,2],[2,2,2]]"

@[implicit_reducible]
def «Order3 M191» : Magma (Fin 4) where
  op := finOpTable "[[3,0,3,3],[2,2,2,2],[2,2,2,2],[3,0,3,3]]"

@[implicit_reducible]
def «Order3 M191^op» : Magma (Fin 4) where
  op := finOpTable "[[3,2,2,3],[0,2,2,0],[3,2,2,3],[3,2,2,3]]"

@[implicit_reducible]
def «Order3 M193» : Magma (Fin 4) where
  op := finOpTable "[[0,2,2,1],[0,2,2,3],[0,2,2,3],[2,2,2,3]]"

@[implicit_reducible]
def «Order3 M193^op» : Magma (Fin 4) where
  op := finOpTable "[[0,0,0,2],[2,2,2,2],[2,2,2,2],[1,3,3,3]]"

@[implicit_reducible]
def «Order3 M195» : Magma (Fin 5) where
  op := finOpTable "[[0,2,2,4,4],[2,3,2,3,4],[0,3,2,3,4],[2,3,2,3,4],[0,3,2,3,4]]"

@[implicit_reducible]
def «Order3 M195^op» : Magma (Fin 5) where
  op := finOpTable "[[0,2,0,2,0],[2,3,3,3,3],[2,2,2,2,2],[4,3,3,3,3],[4,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M197» : Magma (Fin 3) where
  op := finOpTable "[[0,2,0],[0,1,2],[0,2,2]]"

@[implicit_reducible]
def «Order3 M197^op» : Magma (Fin 3) where
  op := finOpTable "[[0,0,0],[2,1,2],[0,2,2]]"

@[implicit_reducible]
def «Order3 M199» : Magma (Fin 5) where
  op := finOpTable "[[2,3,2,4,4],[2,1,2,4,4],[2,1,2,4,4],[3,3,3,4,4],[2,1,2,4,4]]"

@[implicit_reducible]
def «Order3 M199^op» : Magma (Fin 5) where
  op := finOpTable "[[2,2,2,3,2],[3,1,1,3,1],[2,2,2,3,2],[4,4,4,4,4],[4,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M201» : Magma (Fin 5) where
  op := finOpTable "[[1,1,4,2,2],[1,1,4,2,2],[4,4,2,1,1],[2,2,0,4,4],[2,2,1,4,4]]"

@[implicit_reducible]
def «Order3 M201^op» : Magma (Fin 5) where
  op := finOpTable "[[1,1,4,2,2],[1,1,4,2,2],[4,4,2,0,1],[2,2,1,4,4],[2,2,1,4,4]]"

@[implicit_reducible]
def «Order3 M203» : Magma (Fin 5) where
  op := finOpTable "[[0,0,0,0,0],[1,1,1,1,1],[1,1,1,1,3],[2,1,1,1,1],[4,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M203^op» : Magma (Fin 5) where
  op := finOpTable "[[0,1,1,2,4],[0,1,1,1,4],[0,1,1,1,4],[0,1,1,1,4],[0,1,3,1,4]]"

@[implicit_reducible]
def «Order3 M205» : Magma (Fin 4) where
  op := finOpTable "[[3,1,1,3],[3,3,2,3],[3,3,3,3],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M205^op» : Magma (Fin 4) where
  op := finOpTable "[[3,3,3,3],[1,3,3,3],[1,2,3,3],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M207» : Magma (Fin 4) where
  op := finOpTable "[[3,2,2,3],[1,1,1,1],[3,3,3,3],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M207^op» : Magma (Fin 4) where
  op := finOpTable "[[3,1,3,3],[2,1,3,3],[2,1,3,3],[3,1,3,3]]"

@[implicit_reducible]
def «Order3 M209» : Magma (Fin 4) where
  op := finOpTable "[[0,2,2,0],[3,3,3,3],[0,2,2,2],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M209^op» : Magma (Fin 4) where
  op := finOpTable "[[0,3,0,3],[2,3,2,3],[2,3,2,3],[0,3,2,3]]"

@[implicit_reducible]
def «Order3 M211» : Magma (Fin 4) where
  op := finOpTable "[[0,2,2,0],[3,3,3,3],[0,2,2,0],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M211^op» : Magma (Fin 4) where
  op := finOpTable "[[0,3,0,3],[2,3,2,3],[2,3,2,3],[0,3,0,3]]"

@[implicit_reducible]
def «Order3 M213» : Magma (Fin 4) where
  op := finOpTable "[[0,1,3,3],[1,1,1,3],[1,1,1,3],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M213^op» : Magma (Fin 4) where
  op := finOpTable "[[0,1,1,3],[1,1,1,3],[3,1,1,3],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M215» : Magma (Fin 5) where
  op := finOpTable "[[0,4,3,3,4],[2,4,2,2,4],[3,4,3,3,4],[0,4,3,3,4],[0,4,3,3,4]]"

@[implicit_reducible]
def «Order3 M215^op» : Magma (Fin 5) where
  op := finOpTable "[[0,2,3,0,0],[4,4,4,4,4],[3,2,3,3,3],[3,2,3,3,3],[4,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M217» : Magma (Fin 4) where
  op := finOpTable "[[0,0,0,3],[0,1,3,3],[0,0,2,3],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M218» : Magma (Fin 4) where
  op := finOpTable "[[2,2,2,2],[0,3,0,3],[2,2,2,2],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M218^op» : Magma (Fin 4) where
  op := finOpTable "[[2,0,2,3],[2,3,2,3],[2,0,2,3],[2,3,2,3]]"

@[implicit_reducible]
def «Order3 M220» : Magma (Fin 5) where
  op := finOpTable "[[0,1,2,3,4],[0,1,2,3,4],[3,1,2,0,4],[0,4,2,3,1],[0,1,2,3,4]]"

@[implicit_reducible]
def «Order3 M220^op» : Magma (Fin 5) where
  op := finOpTable "[[0,0,3,0,0],[1,1,1,4,1],[2,2,2,2,2],[3,3,0,3,3],[4,4,4,1,4]]"

@[implicit_reducible]
def «Order3 M222» : Magma (Fin 5) where
  op := finOpTable "[[3,4,4,3,2],[4,2,2,4,3],[3,2,2,3,4],[3,2,2,3,4],[3,2,2,3,4]]"

@[implicit_reducible]
def «Order3 M222^op» : Magma (Fin 5) where
  op := finOpTable "[[3,4,3,3,3],[4,2,2,2,2],[4,2,2,2,2],[3,4,3,3,3],[2,3,4,4,4]]"

@[implicit_reducible]
def «Order3 M224» : Magma (Fin 5) where
  op := finOpTable "[[4,1,1,3,4],[4,1,3,3,4],[1,1,3,3,4],[1,1,3,3,4],[4,1,1,3,4]]"

@[implicit_reducible]
def «Order3 M224^op» : Magma (Fin 5) where
  op := finOpTable "[[4,4,1,1,4],[1,1,1,1,1],[1,3,3,3,1],[3,3,3,3,3],[4,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M226» : Magma (Fin 5) where
  op := finOpTable "[[3,3,2,3,4],[3,3,2,3,4],[4,3,2,3,4],[3,3,2,3,4],[3,2,2,3,4]]"

@[implicit_reducible]
def «Order3 M226^op» : Magma (Fin 5) where
  op := finOpTable "[[3,3,4,3,3],[3,3,3,3,2],[2,2,2,2,2],[3,3,3,3,3],[4,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M228» : Magma (Fin 5) where
  op := finOpTable "[[2,1,2,4,4],[3,4,2,3,4],[2,4,2,4,4],[2,1,2,4,4],[2,4,2,4,4]]"

@[implicit_reducible]
def «Order3 M228^op» : Magma (Fin 5) where
  op := finOpTable "[[2,3,2,2,2],[1,4,4,1,4],[2,2,2,2,2],[4,3,4,4,4],[4,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M230» : Magma (Fin 4) where
  op := finOpTable "[[1,1,0,1],[1,1,0,1],[2,3,3,3],[2,3,3,3]]"

@[implicit_reducible]
def «Order3 M230^op» : Magma (Fin 4) where
  op := finOpTable "[[1,1,2,2],[1,1,3,3],[0,0,3,3],[1,1,3,3]]"

@[implicit_reducible]
def «Order3 M232» : Magma (Fin 4) where
  op := finOpTable "[[0,2,2,0],[3,3,3,3],[0,0,2,2],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M232^op» : Magma (Fin 4) where
  op := finOpTable "[[0,3,0,3],[2,3,0,3],[2,3,2,3],[0,3,2,3]]"

@[implicit_reducible]
def «Order3 M234» : Magma (Fin 5) where
  op := finOpTable "[[0,4,0,0,4],[2,1,3,3,1],[3,1,3,3,3],[3,1,3,3,3],[0,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M235» : Magma (Fin 6) where
  op := finOpTable "[[0,0,0,3,3,3],[1,1,4,4,4,1],[2,5,2,5,2,5],[0,0,0,3,3,3],[1,1,4,4,4,1],[2,5,2,5,2,5]]"

@[implicit_reducible]
def «Order3 M235^op» : Magma (Fin 6) where
  op := finOpTable "[[0,1,2,0,1,2],[0,1,5,0,1,5],[0,4,2,0,4,2],[3,4,5,3,4,5],[3,4,2,3,4,2],[3,1,5,3,1,5]]"

@[implicit_reducible]
def «Order3 M237» : Magma (Fin 6) where
  op := finOpTable "[[0,5,4,0,4,5],[3,5,2,3,2,5],[3,5,4,3,4,5],[0,5,4,0,4,5],[0,5,4,0,4,5],[0,5,4,0,4,5]]"

@[implicit_reducible]
def «Order3 M237^op» : Magma (Fin 6) where
  op := finOpTable "[[0,3,3,0,0,0],[5,5,5,5,5,5],[4,2,4,4,4,4],[0,3,3,0,0,0],[4,2,4,4,4,4],[5,5,5,5,5,5]]"

@[implicit_reducible]
def «Order3 M239» : Magma (Fin 5) where
  op := finOpTable "[[3,3,3,3,3],[3,3,3,3,0],[4,3,3,3,3],[3,3,3,3,3],[3,3,3,3,3]]"

@[implicit_reducible]
def «Order3 M239^op» : Magma (Fin 5) where
  op := finOpTable "[[3,3,4,3,3],[3,3,3,3,3],[3,3,3,3,3],[3,3,3,3,3],[3,0,3,3,3]]"

@[implicit_reducible]
def «Order3 M241» : Magma (Fin 5) where
  op := finOpTable "[[0,2,2,0,2],[2,3,2,3,3],[2,2,2,2,2],[0,4,4,4,4],[1,1,1,1,1]]"

@[implicit_reducible]
def «Order3 M241^op» : Magma (Fin 5) where
  op := finOpTable "[[0,2,2,0,1],[2,3,2,4,1],[2,2,2,4,1],[0,3,2,4,1],[2,3,2,4,1]]"

@[implicit_reducible]
def «Order3 M243» : Magma (Fin 5) where
  op := finOpTable "[[2,1,2,2,4],[2,1,2,2,2],[3,1,2,4,0],[0,1,2,2,2],[2,1,2,3,2]]"

@[implicit_reducible]
def «Order3 M243^op» : Magma (Fin 5) where
  op := finOpTable "[[2,2,3,0,2],[1,1,1,1,1],[2,2,2,2,2],[2,2,4,2,3],[4,2,0,2,2]]"

@[implicit_reducible]
def «Order3 M245» : Magma (Fin 4) where
  op := finOpTable "[[3,3,3,3],[3,3,3,3],[0,1,0,0],[2,2,2,2]]"

@[implicit_reducible]
def «Order3 M245^op» : Magma (Fin 4) where
  op := finOpTable "[[3,3,0,2],[3,3,1,2],[3,3,0,2],[3,3,0,2]]"

@[implicit_reducible]
def «Order3 M247» : Magma (Fin 4) where
  op := finOpTable "[[2,3,2,3],[0,0,3,3],[3,1,1,3],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M247^op» : Magma (Fin 4) where
  op := finOpTable "[[2,0,3,0],[3,0,1,1],[2,3,1,2],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M249» : Magma (Fin 5) where
  op := finOpTable "[[0,1,3,2,4],[0,1,4,3,2],[1,0,2,3,4],[4,1,2,3,0],[0,3,2,1,4]]"

@[implicit_reducible]
def «Order3 M249^op» : Magma (Fin 5) where
  op := finOpTable "[[0,0,1,4,0],[1,1,0,1,3],[3,4,2,2,2],[2,3,3,3,1],[4,2,4,0,4]]"

@[implicit_reducible]
def «Order3 M251» : Magma (Fin 6) where
  op := finOpTable "[[0,0,3,0,0,0],[1,2,2,1,1,2],[2,5,5,2,2,5],[3,3,4,3,3,3],[4,4,0,4,4,4],[5,1,1,5,5,1]]"

@[implicit_reducible]
def «Order3 M251^op» : Magma (Fin 6) where
  op := finOpTable "[[0,1,2,3,4,5],[0,2,5,3,4,1],[3,2,5,4,0,1],[0,1,2,3,4,5],[0,1,2,3,4,5],[0,2,5,3,4,1]]"

@[implicit_reducible]
def «Order3 M253» : Magma (Fin 5) where
  op := finOpTable "[[1,1,2,1,2],[3,3,3,3,3],[3,3,3,3,3],[0,0,4,0,4],[1,1,2,1,1]]"

@[implicit_reducible]
def «Order3 M253^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,3,0,1],[1,3,3,0,1],[2,3,3,4,2],[1,3,3,0,1],[2,3,3,4,1]]"

@[implicit_reducible]
def «Order3 M255» : Magma (Fin 6) where
  op := finOpTable "[[1,1,2,1,1,1],[4,4,4,4,4,4],[4,4,4,4,4,4],[3,3,5,3,3,3],[0,0,0,0,0,0],[5,5,3,5,5,5]]"

@[implicit_reducible]
def «Order3 M255^op» : Magma (Fin 6) where
  op := finOpTable "[[1,4,4,3,0,5],[1,4,4,3,0,5],[2,4,4,5,0,3],[1,4,4,3,0,5],[1,4,4,3,0,5],[1,4,4,3,0,5]]"

@[implicit_reducible]
def «Order3 M257» : Magma (Fin 9) where
  op := finOpTable "[[2,6,2,6,6,2,6,2,2],[4,2,2,2,4,2,4,2,4],[5,3,5,3,3,5,5,5,8],[1,1,7,7,1,7,1,7,7],[3,3,5,3,5,5,5,5,5],[0,1,7,0,7,7,7,7,1],[5,8,5,5,5,5,5,5,8],[2,2,2,2,4,2,6,2,2],[0,0,7,0,0,7,0,7,7]]"

@[implicit_reducible]
def «Order3 M257^op» : Magma (Fin 9) where
  op := finOpTable "[[2,4,5,1,3,0,5,2,0],[6,2,3,1,3,1,8,2,0],[2,2,5,7,5,7,5,2,7],[6,2,3,7,3,0,5,2,0],[6,4,3,1,5,7,5,4,0],[2,2,5,7,5,7,5,2,7],[6,4,5,1,5,7,5,6,0],[2,2,5,7,5,7,5,2,7],[2,4,8,7,5,1,8,2,7]]"

@[implicit_reducible]
def «Order3 M259» : Magma (Fin 10) where
  op := finOpTable "[[5,1,6,5,5,5,6,5,6,1],[2,4,2,4,4,4,4,4,4,9],[3,3,3,3,3,3,7,7,3,3],[5,1,1,5,5,5,6,5,8,5],[0,3,0,3,3,3,3,7,3,3],[4,4,2,4,4,4,4,4,2,9],[4,4,4,4,4,4,4,9,4,9],[1,1,1,5,5,5,8,5,8,8],[2,4,2,4,4,4,4,4,4,4],[0,3,3,3,3,3,3,3,0,3]]"

@[implicit_reducible]
def «Order3 M259^op» : Magma (Fin 10) where
  op := finOpTable "[[5,2,3,5,0,4,4,1,2,0],[1,4,3,1,3,4,4,1,4,3],[6,2,3,1,0,2,4,1,2,3],[5,4,3,5,3,4,4,5,4,3],[5,4,3,5,3,4,4,5,4,3],[5,4,3,5,3,4,4,5,4,3],[6,4,7,6,3,4,4,8,4,3],[5,4,7,5,7,4,9,5,4,3],[6,4,3,8,3,2,4,8,4,0],[1,9,3,5,3,9,9,8,4,3]]"

@[implicit_reducible]
def «Order3 M261» : Magma (Fin 5) where
  op := finOpTable "[[0,1,2,3,4],[2,2,2,2,2],[0,0,3,3,0],[0,1,0,4,4],[0,2,2,0,2]]"

@[implicit_reducible]
def «Order3 M261^op» : Magma (Fin 5) where
  op := finOpTable "[[0,2,0,0,0],[1,2,0,1,2],[2,2,3,0,2],[3,2,3,4,0],[4,2,0,4,2]]"

@[implicit_reducible]
def «Order3 M263» : Magma (Fin 5) where
  op := finOpTable "[[0,0,0,0,0],[3,1,4,4,1],[1,3,2,2,3],[4,2,3,3,2],[2,4,1,1,4]]"

@[implicit_reducible]
def «Order3 M263^op» : Magma (Fin 5) where
  op := finOpTable "[[0,3,1,4,2],[0,1,3,2,4],[0,4,2,3,1],[0,4,2,3,1],[0,1,3,2,4]]"

@[implicit_reducible]
def «Order3 M265» : Magma (Fin 4) where
  op := finOpTable "[[3,2,2,3],[0,3,0,3],[1,1,3,3],[1,2,0,3]]"

@[implicit_reducible]
def «Order3 M265^op» : Magma (Fin 4) where
  op := finOpTable "[[3,0,1,1],[2,3,1,2],[2,0,3,0],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M267» : Magma (Fin 5) where
  op := finOpTable "[[2,2,2,2,2],[3,3,3,3,3],[4,1,4,4,4],[2,2,2,2,2],[0,3,3,3,3]]"

@[implicit_reducible]
def «Order3 M267^op» : Magma (Fin 5) where
  op := finOpTable "[[2,3,4,2,0],[2,3,1,2,3],[2,3,4,2,3],[2,3,4,2,3],[2,3,4,2,3]]"

@[implicit_reducible]
def «Order3 M269» : Magma (Fin 6) where
  op := finOpTable "[[5,5,1,5,5,5],[3,2,2,2,2,2],[4,4,4,4,4,0],[0,4,0,0,0,0],[1,1,1,5,1,1],[3,3,3,3,2,3]]"

@[implicit_reducible]
def «Order3 M269^op» : Magma (Fin 6) where
  op := finOpTable "[[5,3,4,0,1,3],[5,2,4,4,1,3],[1,2,4,0,1,3],[5,2,4,0,5,3],[5,2,4,0,1,2],[5,2,0,0,1,3]]"

@[implicit_reducible]
def «Order3 M271» : Magma (Fin 4) where
  op := finOpTable "[[1,2,2,2],[3,1,0,2],[3,1,1,3],[0,1,0,1]]"

@[implicit_reducible]
def «Order3 M271^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,3,0],[2,1,1,1],[2,0,1,0],[2,2,3,1]]"

@[implicit_reducible]
def «Order3 M273» : Magma (Fin 7) where
  op := finOpTable "[[2,6,2,2,2,2,6],[3,6,6,3,6,6,6],[5,1,5,5,4,5,5],[2,2,2,2,2,2,6],[0,1,0,3,0,5,0],[0,6,6,3,6,6,6],[4,4,2,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M273^op» : Magma (Fin 7) where
  op := finOpTable "[[2,3,5,2,0,0,4],[6,6,1,2,1,6,4],[2,6,5,2,0,6,2],[2,3,5,2,3,3,4],[2,6,4,2,0,6,4],[2,6,5,2,5,6,4],[6,6,5,6,0,6,4]]"

@[implicit_reducible]
def «Order3 M275» : Magma (Fin 5) where
  op := finOpTable "[[1,1,1,1,1],[2,2,2,2,2],[0,0,0,3,4],[1,1,1,1,4],[1,1,1,1,1]]"

@[implicit_reducible]
def «Order3 M275^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,0,1,1],[1,2,0,1,1],[1,2,0,1,1],[1,2,3,1,1],[1,2,4,4,1]]"

@[implicit_reducible]
def «Order3 M277» : Magma (Fin 5) where
  op := finOpTable "[[3,2,2,3,4],[3,3,4,3,4],[0,1,1,4,4],[4,4,2,2,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «Order3 M277^op» : Magma (Fin 5) where
  op := finOpTable "[[3,3,0,4,0],[2,3,1,4,1],[2,4,1,2,2],[3,3,4,2,3],[4,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M279» : Magma (Fin 13) where
  op := finOpTable "[[3,2,3,3,3,3,3,3,8,3,10,3,3],[4,4,4,4,4,4,4,4,4,4,4,4,4],[3,11,3,3,3,3,3,3,8,3,10,3,3],[11,7,7,7,7,7,7,7,7,7,7,11,12],[6,6,6,6,6,6,6,6,6,6,6,6,6],[3,3,3,3,3,3,3,3,8,3,10,3,3],[9,1,9,9,9,9,9,9,9,9,9,9,9],[0,5,2,5,5,5,5,5,5,5,5,5,5],[7,0,12,7,7,7,7,7,7,7,7,11,12],[4,4,4,4,4,4,4,4,4,4,4,4,4],[7,8,7,7,7,7,7,7,7,7,7,11,12],[0,12,2,5,5,5,5,5,5,5,5,5,5],[0,10,2,5,5,5,5,5,5,5,0,5,5]]"

@[implicit_reducible]
def «Order3 M279^op» : Magma (Fin 13) where
  op := finOpTable "[[3,4,3,11,6,3,9,0,7,4,7,0,0],[2,4,11,7,6,3,1,5,0,4,8,12,10],[3,4,3,7,6,3,9,2,12,4,7,2,2],[3,4,3,7,6,3,9,5,7,4,7,5,5],[3,4,3,7,6,3,9,5,7,4,7,5,5],[3,4,3,7,6,3,9,5,7,4,7,5,5],[3,4,3,7,6,3,9,5,7,4,7,5,5],[3,4,3,7,6,3,9,5,7,4,7,5,5],[8,4,8,7,6,8,9,5,7,4,7,5,5],[3,4,3,7,6,3,9,5,7,4,7,5,5],[10,4,10,7,6,10,9,5,7,4,7,5,0],[3,4,3,11,6,3,9,5,11,4,11,5,5],[3,4,3,12,6,3,9,5,12,4,12,5,5]]"

@[implicit_reducible]
def «Order3 M281» : Magma (Fin 5) where
  op := finOpTable "[[3,2,3,3,4],[0,2,2,4,4],[3,4,3,3,4],[4,1,4,1,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «Order3 M281^op» : Magma (Fin 5) where
  op := finOpTable "[[3,0,3,4,0],[2,2,4,1,1],[3,2,3,4,2],[3,4,3,1,3],[4,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M283» : Magma (Fin 12) where
  op := finOpTable "[[4,2,3,3,4,4,4,4,4,4,10,4],[5,5,5,3,5,5,5,5,5,5,0,10],[11,1,6,6,6,6,6,6,6,6,0,6],[11,7,2,7,7,7,7,7,7,7,7,10],[11,8,8,8,8,8,8,8,8,8,8,11],[7,7,2,7,7,7,7,7,7,7,7,7],[5,5,5,3,5,5,5,5,5,5,5,5],[6,1,6,6,6,6,6,6,6,6,6,6],[0,9,9,9,9,9,9,9,9,9,9,9],[4,4,4,4,4,4,4,4,4,4,10,4],[8,2,8,1,8,8,8,8,8,8,8,11],[0,0,3,1,9,9,9,9,9,9,9,9]]"

@[implicit_reducible]
def «Order3 M283^op» : Magma (Fin 12) where
  op := finOpTable "[[4,5,11,11,11,7,5,6,0,4,8,0],[2,5,1,7,8,7,5,1,9,4,2,0],[3,5,6,2,8,2,5,6,9,4,8,3],[3,3,6,7,8,7,3,6,9,4,1,1],[4,5,6,7,8,7,5,6,9,4,8,9],[4,5,6,7,8,7,5,6,9,4,8,9],[4,5,6,7,8,7,5,6,9,4,8,9],[4,5,6,7,8,7,5,6,9,4,8,9],[4,5,6,7,8,7,5,6,9,4,8,9],[4,5,6,7,8,7,5,6,9,4,8,9],[10,0,0,7,8,7,5,6,9,10,8,9],[4,10,6,10,11,7,5,6,9,4,11,9]]"

@[implicit_reducible]
def «Order3 M285» : Magma (Fin 12) where
  op := finOpTable "[[5,1,5,5,5,5,5,5,5,1,5,11],[8,2,2,2,2,2,2,2,8,9,2,2],[3,3,7,3,7,7,7,7,7,7,7,7],[6,1,6,6,6,6,6,6,11,6,6,11],[5,5,5,5,5,5,5,5,5,5,5,11],[8,10,10,10,10,10,10,10,8,10,10,10],[2,2,2,2,2,2,2,2,2,9,2,2],[6,1,6,6,6,6,6,6,6,6,6,6],[0,3,4,3,4,4,4,4,4,4,4,4],[0,7,7,3,7,7,7,7,7,7,7,0],[0,4,4,0,4,4,4,4,4,4,4,0],[10,10,10,9,10,10,10,10,8,9,10,10]]"

@[implicit_reducible]
def «Order3 M285^op» : Magma (Fin 12) where
  op := finOpTable "[[5,8,3,6,5,8,2,6,0,0,0,10],[1,2,3,1,5,10,2,1,3,7,4,10],[5,2,7,6,5,10,2,6,4,7,4,10],[5,2,3,6,5,10,2,6,3,3,0,9],[5,2,7,6,5,10,2,6,4,7,4,10],[5,2,7,6,5,10,2,6,4,7,4,10],[5,2,7,6,5,10,2,6,4,7,4,10],[5,2,7,6,5,10,2,6,4,7,4,10],[5,8,7,11,5,8,2,6,4,7,4,8],[1,9,7,6,5,10,9,6,4,7,4,9],[5,2,7,6,5,10,2,6,4,7,4,10],[11,2,7,11,11,10,2,6,4,0,0,10]]"

@[implicit_reducible]
def «Order3 M287» : Magma (Fin 4) where
  op := finOpTable "[[1,3,2,3],[1,1,2,2],[1,1,2,2],[0,1,0,2]]"

@[implicit_reducible]
def «Order3 M287^op» : Magma (Fin 4) where
  op := finOpTable "[[1,1,1,0],[3,1,1,1],[2,2,2,0],[3,2,2,2]]"

@[implicit_reducible]
def «Order3 M289» : Magma (Fin 5) where
  op := finOpTable "[[2,0,4,0,2],[1,3,1,4,0],[4,2,0,2,1],[3,4,3,1,3],[0,1,2,3,4]]"

@[implicit_reducible]
def «Order3 M289^op» : Magma (Fin 5) where
  op := finOpTable "[[2,1,4,3,0],[0,3,2,4,1],[4,1,0,3,2],[0,4,2,1,3],[2,0,1,3,4]]"

@[implicit_reducible]
def «Order3 M291» : Magma (Fin 3) where
  op := finOpTable "[[1,2,2],[1,1,2],[0,1,2]]"

@[implicit_reducible]
def «Order3 M291^op» : Magma (Fin 3) where
  op := finOpTable "[[1,1,0],[2,1,1],[2,2,2]]"

@[implicit_reducible]
def «Order3 M293» : Magma (Fin 4) where
  op := finOpTable "[[0,1,2,3],[2,3,2,2],[0,1,2,3],[0,3,2,3]]"

@[implicit_reducible]
def «Order3 M293^op» : Magma (Fin 4) where
  op := finOpTable "[[0,2,0,0],[1,3,1,3],[2,2,2,2],[3,2,3,3]]"

@[implicit_reducible]
def «Order3 M295» : Magma (Fin 4) where
  op := finOpTable "[[3,2,2,2],[3,2,3,3],[0,2,2,3],[3,1,2,3]]"

@[implicit_reducible]
def «Order3 M295^op» : Magma (Fin 4) where
  op := finOpTable "[[3,3,0,3],[2,2,2,1],[2,3,2,2],[2,3,3,3]]"

@[implicit_reducible]
def «Order3 M297» : Magma (Fin 5) where
  op := finOpTable "[[1,4,4,3,0],[4,1,1,0,3],[2,2,2,2,2],[3,0,0,1,4],[0,3,3,4,1]]"

@[implicit_reducible]
def «Order3 M297^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,2,3,0],[4,1,2,0,3],[4,1,2,0,3],[3,0,2,1,4],[0,3,2,4,1]]"

@[implicit_reducible]
def «Order3 M299» : Magma (Fin 4) where
  op := finOpTable "[[2,0,3,3],[3,2,3,3],[3,3,2,3],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M299^op» : Magma (Fin 4) where
  op := finOpTable "[[2,3,3,0],[0,2,3,1],[3,3,2,2],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M301» : Magma (Fin 5) where
  op := finOpTable "[[1,4,0,1,1],[4,0,1,0,0],[2,2,3,4,3],[3,3,4,2,2],[0,1,2,3,4]]"

@[implicit_reducible]
def «Order3 M301^op» : Magma (Fin 5) where
  op := finOpTable "[[1,4,2,3,0],[4,0,2,3,1],[0,1,3,4,2],[1,0,4,2,3],[1,0,3,2,4]]"

@[implicit_reducible]
def «Order3 M303» : Magma (Fin 4) where
  op := finOpTable "[[3,1,3,1],[0,2,0,0],[3,2,2,3],[3,2,2,3]]"

@[implicit_reducible]
def «Order3 M303^op» : Magma (Fin 4) where
  op := finOpTable "[[3,0,3,3],[1,2,2,2],[3,0,2,2],[1,0,3,3]]"

@[implicit_reducible]
def «Order3 M305» : Magma (Fin 4) where
  op := finOpTable "[[3,1,3,1],[0,2,0,0],[2,2,2,2],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M305^op» : Magma (Fin 4) where
  op := finOpTable "[[3,0,2,3],[1,2,2,3],[3,0,2,3],[1,0,2,3]]"

@[implicit_reducible]
def «Order3 M307» : Magma (Fin 4) where
  op := finOpTable "[[2,3,3,3],[3,0,3,3],[3,3,1,3],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M307^op» : Magma (Fin 4) where
  op := finOpTable "[[2,3,3,0],[3,0,3,1],[3,3,1,2],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M309» : Magma (Fin 4) where
  op := finOpTable "[[1,2,2,1],[2,1,1,2],[0,3,3,0],[3,0,0,3]]"

@[implicit_reducible]
def «Order3 M309^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,3],[2,1,3,0],[2,1,3,0],[1,2,0,3]]"

@[implicit_reducible]
def «Order3 M311» : Magma (Fin 6) where
  op := finOpTable "[[3,1,2,5,4,5],[0,2,0,3,5,5],[0,5,4,3,5,5],[5,1,2,0,4,5],[0,5,5,3,2,5],[0,1,2,3,4,5]]"

@[implicit_reducible]
def «Order3 M311^op» : Magma (Fin 6) where
  op := finOpTable "[[3,0,0,5,0,0],[1,2,5,1,5,1],[2,0,4,2,5,2],[5,3,3,0,3,3],[4,5,5,4,2,4],[5,5,5,5,5,5]]"

@[implicit_reducible]
def «Order3 M313» : Magma (Fin 6) where
  op := finOpTable "[[3,1,2,5,4,5],[0,2,5,3,5,5],[0,0,4,3,5,5],[5,1,2,0,4,5],[0,5,5,3,1,5],[0,1,2,3,4,5]]"

@[implicit_reducible]
def «Order3 M313^op» : Magma (Fin 6) where
  op := finOpTable "[[3,0,0,5,0,0],[1,2,0,1,5,1],[2,5,4,2,5,2],[5,3,3,0,3,3],[4,5,5,4,1,4],[5,5,5,5,5,5]]"

@[implicit_reducible]
def «Order3 M315» : Magma (Fin 5) where
  op := finOpTable "[[0,4,4,4,0],[3,1,1,1,2],[1,2,2,2,3],[2,3,3,3,1],[4,0,0,0,4]]"

@[implicit_reducible]
def «Order3 M315^op» : Magma (Fin 5) where
  op := finOpTable "[[0,3,1,2,4],[4,1,2,3,0],[4,1,2,3,0],[4,1,2,3,0],[0,2,3,1,4]]"

@[implicit_reducible]
def «Order3 M317» : Magma (Fin 6) where
  op := finOpTable "[[0,0,1,5,1,0],[1,1,0,1,0,1],[2,2,2,2,5,2],[3,3,3,3,3,3],[4,4,4,4,4,4],[5,5,5,0,2,5]]"

@[implicit_reducible]
def «Order3 M317^op» : Magma (Fin 6) where
  op := finOpTable "[[0,1,2,3,4,5],[0,1,2,3,4,5],[1,0,2,3,4,5],[5,1,2,3,4,0],[1,0,5,3,4,2],[0,1,2,3,4,5]]"

@[implicit_reducible]
def «Order3 M319» : Magma (Fin 16) where
  op := finOpTable "[[0,2,3,4,8,7,1,9,6,10,11,12,5,14,15,13],[3,5,13,9,4,10,2,8,0,7,1,15,14,11,6,12],[4,3,9,5,7,11,0,14,8,12,15,13,2,1,10,6],[8,0,4,7,14,12,6,11,15,13,2,3,1,10,9,5],[6,1,0,8,10,4,12,15,13,14,5,2,11,7,3,9],[9,4,6,15,5,1,13,2,14,3,10,0,7,12,11,8],[2,14,15,3,0,8,11,6,1,4,9,7,13,5,12,10],[10,12,1,6,13,9,7,3,5,15,14,11,0,8,2,4],[1,11,2,0,6,15,10,13,12,8,7,14,9,4,5,3],[11,6,8,14,15,0,5,10,9,2,13,1,12,3,4,7],[12,10,14,13,1,5,15,0,3,11,4,8,6,9,7,2],[5,13,10,11,9,14,3,7,4,0,12,6,15,2,8,1],[7,15,12,10,3,13,14,4,2,9,0,5,8,6,1,11],[15,8,7,12,2,3,9,1,11,5,6,4,10,13,0,14],[13,9,11,1,12,2,4,5,7,6,8,10,3,15,14,0],[14,7,5,2,11,6,8,12,10,1,3,9,4,0,13,15]]"

@[implicit_reducible]
def «Order3 M319^op» : Magma (Fin 16) where
  op := finOpTable "[[0,3,4,8,6,9,2,10,1,11,12,5,7,15,13,14],[2,5,3,0,1,4,14,12,11,6,10,13,15,8,9,7],[3,13,9,4,0,6,15,1,2,8,14,10,12,7,11,5],[4,9,5,7,8,15,3,6,0,14,13,11,10,12,1,2],[8,4,7,14,10,5,0,13,6,15,1,9,3,2,12,11],[7,10,11,12,4,1,8,9,15,0,5,14,13,3,2,6],[1,2,0,6,12,13,11,7,10,5,15,3,14,9,4,8],[9,8,14,11,15,2,6,3,13,10,0,7,4,1,5,12],[6,0,8,15,13,14,1,5,12,9,3,4,2,11,7,10],[10,7,12,13,14,3,4,15,8,2,11,0,9,5,6,1],[11,1,15,2,5,10,9,14,7,13,4,12,0,6,8,3],[12,15,13,3,2,0,7,11,14,1,8,6,5,4,10,9],[5,14,2,1,11,7,13,0,9,12,6,15,8,10,3,4],[14,11,1,10,7,12,5,8,4,3,9,2,6,13,15,0],[15,6,10,9,3,11,12,2,5,4,7,8,1,0,14,13],[13,12,6,5,9,8,10,4,3,7,2,1,11,14,0,15]]"

@[implicit_reducible]
def «Order3 M321» : Magma (Fin 5) where
  op := finOpTable "[[2,1,4,2,4],[2,3,2,4,4],[4,4,0,3,4],[0,4,4,1,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «Order3 M321^op» : Magma (Fin 5) where
  op := finOpTable "[[2,2,4,0,0],[1,3,4,4,1],[4,2,0,4,2],[2,4,3,1,3],[4,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M323» : Magma (Fin 4) where
  op := finOpTable "[[2,1,3,3],[1,3,1,0],[3,2,0,2],[0,0,2,1]]"

@[implicit_reducible]
def «Order3 M323^op» : Magma (Fin 4) where
  op := finOpTable "[[2,1,3,0],[1,3,2,0],[3,1,0,2],[3,0,2,1]]"

@[implicit_reducible]
def «Order3 M327» : Magma (Fin 5) where
  op := finOpTable "[[1,4,2,0,3],[2,0,3,1,4],[3,1,4,2,0],[4,2,0,3,1],[0,3,1,4,2]]"

@[implicit_reducible]
def «Order3 M327^op» : Magma (Fin 5) where
  op := finOpTable "[[1,2,3,4,0],[4,0,1,2,3],[2,3,4,0,1],[0,1,2,3,4],[3,4,0,1,2]]"

@[implicit_reducible]
def «Order3 M329» : Magma (Fin 6) where
  op := finOpTable "[[0,4,5,0,0,0],[4,1,1,1,1,2],[1,2,2,2,2,3],[3,3,0,3,3,1],[2,5,4,4,4,4],[5,0,3,5,5,5]]"

@[implicit_reducible]
def «Order3 M329^op» : Magma (Fin 6) where
  op := finOpTable "[[0,4,1,3,2,5],[4,1,2,3,5,0],[5,1,2,0,4,3],[0,1,2,3,4,5],[0,1,2,3,4,5],[0,2,3,1,4,5]]"

@[implicit_reducible]
def «Order3 M331» : Magma (Fin 5) where
  op := finOpTable "[[2,2,4,3,4],[4,3,0,4,4],[4,4,0,4,4],[0,4,4,1,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «Order3 M331^op» : Magma (Fin 5) where
  op := finOpTable "[[2,4,4,0,0],[2,3,4,4,1],[4,0,0,4,2],[3,4,4,1,3],[4,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M333» : Magma (Fin 13) where
  op := finOpTable "[[0,5,3,9,11,7,8,12,10,6,4,1,2],[2,1,4,6,8,3,9,10,5,12,0,7,11],[8,3,2,10,6,0,12,1,7,5,11,4,9],[10,11,6,3,1,9,7,0,2,4,12,8,5],[7,6,5,2,4,10,0,8,9,11,1,12,3],[3,12,1,11,0,5,2,9,6,8,7,10,4],[11,7,0,12,9,4,6,5,1,10,2,3,8],[9,4,11,5,12,2,10,7,3,1,8,0,6],[1,9,10,0,3,12,4,11,8,2,5,6,7],[4,10,7,8,2,1,11,6,12,9,3,5,0],[5,8,12,4,7,6,3,2,11,0,10,9,1],[12,2,9,7,5,8,1,4,0,3,6,11,10],[6,0,8,1,10,11,5,3,4,7,9,2,12]]"

@[implicit_reducible]
def «Order3 M333^op» : Magma (Fin 13) where
  op := finOpTable "[[0,2,8,10,7,3,11,9,1,4,5,12,6],[5,1,3,11,6,12,7,4,9,10,8,2,0],[3,4,2,6,5,1,0,11,10,7,12,9,8],[9,6,10,3,2,11,12,5,0,8,4,7,1],[11,8,6,1,4,0,9,12,3,2,7,5,10],[7,3,0,9,10,5,4,2,12,1,6,8,11],[8,9,12,7,0,2,6,10,4,11,3,1,5],[12,10,1,0,8,9,5,7,11,6,2,4,3],[10,5,7,2,9,6,1,3,8,12,11,0,4],[6,12,5,4,11,8,10,1,2,9,0,3,7],[4,0,11,12,1,7,2,8,5,3,10,6,9],[1,7,4,8,12,10,3,0,6,5,9,11,2],[2,11,9,5,3,4,8,6,7,0,1,10,12]]"

@[implicit_reducible]
def «Order3 M335» : Magma (Fin 5) where
  op := finOpTable "[[0,1,1,4,0],[3,1,2,1,2],[2,0,2,4,4],[0,0,3,3,2],[3,4,1,3,4]]"

@[implicit_reducible]
def «Order3 M335^op» : Magma (Fin 5) where
  op := finOpTable "[[0,3,2,0,3],[1,1,0,0,4],[1,2,2,3,1],[4,1,4,3,3],[0,2,4,2,4]]"

@[implicit_reducible]
def «Order3 M337» : Magma (Fin 6) where
  op := finOpTable "[[2,0,1,3,0,5],[4,4,2,0,3,5],[3,1,0,2,4,2],[0,2,5,5,4,1],[1,5,2,3,1,4],[0,1,3,4,5,3]]"

@[implicit_reducible]
def «Order3 M337^op» : Magma (Fin 6) where
  op := finOpTable "[[2,4,3,0,1,0],[0,4,1,2,5,1],[1,2,0,5,2,3],[3,0,2,5,3,4],[0,3,4,4,1,5],[5,5,2,1,4,3]]"

@[implicit_reducible]
def «Order3 M339» : Magma (Fin 6) where
  op := finOpTable "[[0,4,0,0,5,1],[5,2,5,3,0,4],[2,3,1,2,2,5],[3,1,3,5,3,2],[1,5,4,4,4,0],[4,0,2,1,1,3]]"

@[implicit_reducible]
def «Order3 M339^op» : Magma (Fin 6) where
  op := finOpTable "[[0,5,2,3,1,4],[4,2,3,1,5,0],[0,5,1,3,4,2],[0,3,2,5,4,1],[5,0,2,3,4,1],[1,4,5,2,0,3]]"

@[implicit_reducible]
def «Order3 M341» : Magma (Fin 4) where
  op := finOpTable "[[0,3,2,3],[2,1,2,3],[0,1,2,1],[0,1,0,3]]"

@[implicit_reducible]
def «Order3 M341^op» : Magma (Fin 4) where
  op := finOpTable "[[0,2,0,0],[3,1,1,1],[2,2,2,0],[3,3,1,3]]"

@[implicit_reducible]
def «Order3 M343» : Magma (Fin 4) where
  op := finOpTable "[[2,1,1,3],[0,1,2,0],[3,1,0,3],[0,2,2,3]]"

@[implicit_reducible]
def «Order3 M343^op» : Magma (Fin 4) where
  op := finOpTable "[[2,0,3,0],[1,1,1,2],[1,2,0,2],[3,0,3,3]]"

@[implicit_reducible]
def «Order3 M345» : Magma (Fin 11) where
  op := finOpTable "[[1,7,2,3,4,10,7,6,8,9,10],[2,0,9,3,4,9,6,7,8,2,10],[3,1,6,0,4,5,5,1,8,8,10],[0,1,2,4,6,5,9,7,9,6,8],[0,1,7,7,3,5,6,2,10,9,5],[4,6,2,3,4,5,6,7,2,9,10],[0,4,8,3,1,5,2,3,8,5,10],[0,3,0,1,4,5,4,9,8,8,10],[0,1,2,2,3,6,6,7,8,9,7],[4,1,3,3,0,5,1,10,8,7,10],[0,1,2,4,0,5,6,7,9,9,10]]"

@[implicit_reducible]
def «Order3 M345^op» : Magma (Fin 11) where
  op := finOpTable "[[1,2,3,0,0,4,0,0,0,4,0],[7,0,1,1,1,6,4,3,1,1,1],[2,9,6,2,7,2,8,0,2,3,2],[3,3,0,4,7,3,3,1,2,3,4],[4,4,4,6,3,4,1,4,3,0,0],[10,9,5,5,5,5,5,5,6,5,5],[7,6,5,9,6,6,2,4,6,1,6],[6,7,1,7,2,7,3,9,7,10,7],[8,8,8,9,10,2,8,8,8,8,9],[9,2,8,6,9,9,5,8,9,7,9],[10,10,10,8,5,10,10,10,7,10,10]]"

@[implicit_reducible]
def «Order3 M347» : Magma (Fin 6) where
  op := finOpTable "[[2,3,2,2,2,4],[1,1,1,1,1,1],[0,4,0,4,0,0],[5,0,5,5,5,5],[4,2,4,0,4,2],[3,5,3,3,3,3]]"

@[implicit_reducible]
def «Order3 M347^op» : Magma (Fin 6) where
  op := finOpTable "[[2,1,0,5,4,3],[3,1,4,0,2,5],[2,1,0,5,4,3],[2,1,4,5,0,3],[2,1,0,5,4,3],[4,1,0,5,2,3]]"

@[implicit_reducible]
def «Order3 M349» : Magma (Fin 4) where
  op := finOpTable "[[1,3,3,3],[2,0,2,2],[1,1,3,1],[0,0,0,2]]"

@[implicit_reducible]
def «Order3 M349^op» : Magma (Fin 4) where
  op := finOpTable "[[1,2,1,0],[3,0,1,0],[3,2,3,0],[3,2,1,2]]"

@[implicit_reducible]
def «Order3 M351» : Magma (Fin 4) where
  op := finOpTable "[[3,2,0,0],[3,2,1,1],[3,3,1,0],[2,2,1,0]]"

@[implicit_reducible]
def «Order3 M351^op» : Magma (Fin 4) where
  op := finOpTable "[[3,3,3,2],[2,2,3,2],[0,1,1,1],[0,1,0,0]]"

@[implicit_reducible]
def «Order3 M353» : Magma (Fin 4) where
  op := finOpTable "[[1,2,2,1],[3,0,0,3],[3,1,3,1],[0,2,0,2]]"

@[implicit_reducible]
def «Order3 M353^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,3,0],[2,0,1,2],[2,0,3,0],[1,3,1,2]]"

@[implicit_reducible]
def «Order3 M355» : Magma (Fin 6) where
  op := finOpTable "[[4,2,4,4,4,4],[3,5,5,5,5,5],[2,4,2,2,2,0],[5,3,3,3,1,3],[0,0,0,0,0,2],[1,1,1,1,3,1]]"

@[implicit_reducible]
def «Order3 M355^op» : Magma (Fin 6) where
  op := finOpTable "[[4,3,2,5,0,1],[2,5,4,3,0,1],[4,5,2,3,0,1],[4,5,2,3,0,1],[4,5,2,1,0,3],[4,5,0,3,2,1]]"

@[implicit_reducible]
def «Order3 M357» : Magma (Fin 9) where
  op := finOpTable "[[6,8,3,6,6,1,8,6,8],[2,5,3,2,4,3,5,7,5],[6,5,3,4,4,3,0,3,0],[2,5,7,2,2,2,2,7,5],[4,5,3,4,4,4,0,3,5],[6,8,1,1,1,1,8,1,8],[7,0,3,0,4,4,0,7,0],[7,5,7,2,2,7,0,7,0],[6,8,1,1,6,1,8,6,8]]"

@[implicit_reducible]
def «Order3 M358» : Magma (Fin 6) where
  op := finOpTable "[[2,2,2,2,1,2],[1,1,1,1,2,0],[0,0,0,0,0,1],[4,3,5,3,3,3],[5,5,3,5,5,5],[3,4,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M358^op» : Magma (Fin 6) where
  op := finOpTable "[[2,1,0,4,5,3],[2,1,0,3,5,4],[2,1,0,5,3,4],[2,1,0,3,5,4],[1,2,0,3,5,4],[2,0,1,3,5,4]]"

@[implicit_reducible]
def «Order3 M360» : Magma (Fin 6) where
  op := finOpTable "[[4,2,3,4,4,4],[1,1,1,1,1,1],[5,0,5,5,5,5],[3,3,4,3,3,0],[0,5,0,0,0,3],[2,4,2,2,2,2]]"

@[implicit_reducible]
def «Order3 M360^op» : Magma (Fin 6) where
  op := finOpTable "[[4,1,5,3,0,2],[2,1,0,3,5,4],[3,1,5,4,0,2],[4,1,5,3,0,2],[4,1,5,3,0,2],[4,1,5,0,3,2]]"

@[implicit_reducible]
def «Order3 M362» : Magma (Fin 4) where
  op := finOpTable "[[1,1,1,1],[0,0,0,2],[1,3,3,3],[2,2,2,2]]"

@[implicit_reducible]
def «Order3 M362^op» : Magma (Fin 4) where
  op := finOpTable "[[1,0,1,2],[1,0,3,2],[1,0,3,2],[1,2,3,2]]"

@[implicit_reducible]
def «Order3 M364» : Magma (Fin 4) where
  op := finOpTable "[[1,1,1,1],[0,0,2,2],[1,1,3,3],[2,2,2,2]]"

@[implicit_reducible]
def «Order3 M364^op» : Magma (Fin 4) where
  op := finOpTable "[[1,0,1,2],[1,0,1,2],[1,2,3,2],[1,2,3,2]]"

@[implicit_reducible]
def «Order3 M366» : Magma (Fin 6) where
  op := finOpTable "[[2,4,4,2,4,2],[4,4,4,5,4,4],[3,0,0,3,0,3],[2,5,2,5,5,5],[0,1,0,1,1,1],[3,3,3,3,1,3]]"

@[implicit_reducible]
def «Order3 M366^op» : Magma (Fin 6) where
  op := finOpTable "[[2,4,3,2,0,3],[4,4,0,5,1,3],[4,4,0,2,0,3],[2,5,3,5,1,3],[4,4,0,5,1,1],[2,4,3,5,1,3]]"

@[implicit_reducible]
def «Order3 M368» : Magma (Fin 5) where
  op := finOpTable "[[2,1,0,1,2],[0,3,0,1,3],[0,0,0,4,4],[1,1,4,1,4],[2,3,4,4,4]]"

@[implicit_reducible]
def «Order3 M369» : Magma (Fin 4) where
  op := finOpTable "[[3,1,0,3],[1,3,2,3],[0,2,3,3],[2,0,1,3]]"

@[implicit_reducible]
def «Order3 M369^op» : Magma (Fin 4) where
  op := finOpTable "[[3,1,0,2],[1,3,2,0],[0,2,3,1],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M371» : Magma (Fin 5) where
  op := finOpTable "[[4,1,4,0,4],[1,2,2,3,2],[1,0,2,1,2],[0,3,2,2,2],[3,3,4,2,4]]"

@[implicit_reducible]
def «Order3 M371^op» : Magma (Fin 5) where
  op := finOpTable "[[4,1,1,0,3],[1,2,0,3,3],[4,2,2,2,4],[0,3,1,2,2],[4,2,2,2,4]]"

@[implicit_reducible]
def «Order3 M373» : Magma (Fin 6) where
  op := finOpTable "[[3,1,2,3,0,5],[2,1,5,3,2,0],[0,1,1,3,4,2],[4,1,5,3,2,0],[0,1,4,3,1,2],[5,1,2,3,3,1]]"

@[implicit_reducible]
def «Order3 M373^op» : Magma (Fin 6) where
  op := finOpTable "[[3,2,0,4,0,5],[1,1,1,1,1,1],[2,5,1,5,4,2],[3,3,3,3,3,3],[0,2,4,2,1,3],[5,0,2,0,2,1]]"

@[implicit_reducible]
def «Order3 M375» : Magma (Fin 4) where
  op := finOpTable "[[2,3,0,0],[1,0,3,1],[3,2,1,2],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M375^op» : Magma (Fin 4) where
  op := finOpTable "[[2,1,3,0],[3,0,2,1],[0,3,1,2],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M377» : Magma (Fin 4) where
  op := finOpTable "[[1,3,2,0],[3,0,3,1],[0,0,1,2],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M377^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,0,0],[3,0,0,1],[2,3,1,2],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M379» : Magma (Fin 5) where
  op := finOpTable "[[1,2,2,0,4],[3,1,4,2,0],[0,0,1,3,2],[0,2,3,1,0],[4,0,2,2,1]]"

@[implicit_reducible]
def «Order3 M379^op» : Magma (Fin 5) where
  op := finOpTable "[[1,3,0,0,4],[2,1,0,2,0],[2,4,1,3,2],[0,2,3,1,2],[4,0,2,0,1]]"

@[implicit_reducible]
def «Order3 M381» : Magma (Fin 4) where
  op := finOpTable "[[1,3,3,0],[3,2,3,1],[3,3,0,2],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M382» : Magma (Fin 4) where
  op := finOpTable "[[0,1,0,0],[1,2,3,1],[2,0,1,2],[3,3,2,3]]"

@[implicit_reducible]
def «Order3 M382^op» : Magma (Fin 4) where
  op := finOpTable "[[0,1,2,3],[1,2,0,3],[0,3,1,2],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M384» : Magma (Fin 4) where
  op := finOpTable "[[1,2,2,0],[3,0,1,3],[2,1,3,1],[0,3,0,2]]"

@[implicit_reducible]
def «Order3 M384^op» : Magma (Fin 4) where
  op := finOpTable "[[1,3,2,0],[2,0,1,3],[2,1,3,0],[0,3,1,2]]"

@[implicit_reducible]
def «Order3 M386» : Magma (Fin 4) where
  op := finOpTable "[[1,2,3,0],[3,0,1,2],[0,3,2,1],[2,1,0,3]]"

@[implicit_reducible]
def «Order3 M387» : Magma (Fin 4) where
  op := finOpTable "[[2,0,3,3],[1,3,2,2],[1,1,0,2],[0,0,3,1]]"

@[implicit_reducible]
def «Order3 M388» : Magma (Fin 6) where
  op := finOpTable "[[3,1,0,3,0,5],[2,1,5,3,5,2],[1,1,3,3,2,2],[4,1,4,3,5,0],[0,1,2,3,1,4],[5,1,5,3,4,3]]"

@[implicit_reducible]
def «Order3 M388^op» : Magma (Fin 6) where
  op := finOpTable "[[3,2,1,4,0,5],[1,1,1,1,1,1],[0,5,3,4,2,5],[3,3,3,3,3,3],[0,5,2,5,1,4],[5,2,2,0,4,3]]"

@[implicit_reducible]
def «Order3 M390» : Magma (Fin 5) where
  op := finOpTable "[[2,1,2,0,0],[1,4,1,3,4],[3,0,2,1,4],[0,3,2,2,2],[3,0,2,1,4]]"

@[implicit_reducible]
def «Order3 M390^op» : Magma (Fin 5) where
  op := finOpTable "[[2,1,3,0,3],[1,4,0,3,0],[2,1,2,2,2],[0,3,1,2,1],[0,4,4,2,4]]"

@[implicit_reducible]
def «Order3 M392» : Magma (Fin 16) where
  op := finOpTable "[[2,5,3,0,4,15,8,9,10,11,6,7,13,14,12,1],[6,8,13,15,9,2,12,4,14,7,3,11,0,5,1,10],[4,12,0,3,2,6,14,13,7,1,15,10,9,8,5,11],[3,7,2,4,0,13,1,6,12,14,9,5,15,11,10,8],[0,10,4,2,3,9,11,15,5,8,13,12,6,1,7,14],[11,9,8,1,14,7,0,10,15,3,5,6,12,4,13,2],[7,4,12,10,5,1,9,14,2,13,11,3,8,6,0,15],[1,13,14,11,8,12,4,5,6,2,10,15,7,0,9,3],[15,11,9,6,13,3,5,0,1,10,2,8,4,12,14,7],[10,0,5,7,12,11,15,8,3,6,1,2,14,13,4,9],[14,6,1,8,11,10,2,7,13,4,12,9,5,3,15,0],[13,1,6,9,15,4,7,2,11,12,0,14,3,10,8,5],[8,15,11,14,1,5,3,12,9,0,7,13,10,2,6,4],[5,3,10,12,7,8,13,11,0,9,14,4,1,15,2,6],[9,14,15,13,6,0,10,3,8,5,4,1,2,7,11,12],[12,2,7,5,10,14,6,1,4,15,8,0,11,9,3,13]]"

@[implicit_reducible]
def «Order3 M392^op» : Magma (Fin 16) where
  op := finOpTable "[[2,6,4,3,0,11,7,1,15,10,14,13,8,5,9,12],[5,8,12,7,10,9,4,13,11,0,6,1,15,3,14,2],[3,13,0,2,4,8,12,14,9,5,1,6,11,10,15,7],[0,15,3,4,2,1,10,11,6,7,8,9,14,12,13,5],[4,9,2,0,3,14,5,8,13,12,11,15,1,7,6,10],[15,2,6,13,9,7,1,12,3,11,10,4,5,8,0,14],[8,12,14,1,11,0,9,4,5,15,2,7,3,13,10,6],[9,4,13,6,15,10,14,5,0,8,7,2,12,11,3,1],[10,14,7,12,5,15,2,6,1,3,13,11,9,0,8,4],[11,7,1,14,8,3,13,2,10,6,4,12,0,9,5,15],[6,3,15,9,13,5,11,10,2,1,12,0,7,14,4,8],[7,11,10,5,12,6,3,15,8,2,9,14,13,4,1,0],[13,0,9,15,6,12,8,7,4,14,5,3,10,1,2,11],[14,5,8,11,1,4,6,0,12,13,3,10,2,15,7,9],[12,1,5,10,7,13,0,9,14,4,15,8,6,2,11,3],[1,10,11,8,14,2,15,3,7,9,0,5,4,6,12,13]]"

@[implicit_reducible]
def «Order3 M394» : Magma (Fin 4) where
  op := finOpTable "[[2,3,3,0],[2,0,1,1],[3,1,0,2],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M394^op» : Magma (Fin 4) where
  op := finOpTable "[[2,2,3,0],[3,0,1,1],[3,1,0,2],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M396» : Magma (Fin 5) where
  op := finOpTable "[[3,0,0,4,0],[1,1,2,1,4],[2,2,4,2,1],[4,3,3,0,3],[0,4,1,3,2]]"

@[implicit_reducible]
def «Order3 M396^op» : Magma (Fin 5) where
  op := finOpTable "[[3,1,2,4,0],[0,1,2,3,4],[0,2,4,3,1],[4,1,2,0,3],[0,4,1,3,2]]"

@[implicit_reducible]
def «Order3 M398» : Magma (Fin 6) where
  op := finOpTable "[[4,0,0,0,3,3],[2,2,3,1,1,1],[5,3,1,2,2,2],[0,1,2,3,4,5],[3,4,4,4,0,4],[1,5,5,5,5,0]]"

@[implicit_reducible]
def «Order3 M398^op» : Magma (Fin 6) where
  op := finOpTable "[[4,2,5,0,3,1],[0,2,3,1,4,5],[0,3,1,2,4,5],[0,1,2,3,4,5],[3,1,2,4,0,5],[3,1,2,5,4,0]]"

@[implicit_reducible]
def «Order3 M400» : Magma (Fin 6) where
  op := finOpTable "[[1,3,0,0,0,0],[3,0,4,1,1,1],[5,4,1,2,2,2],[0,1,3,3,3,3],[2,5,2,4,4,4],[4,2,5,5,5,5]]"

@[implicit_reducible]
def «Order3 M400^op» : Magma (Fin 6) where
  op := finOpTable "[[1,3,5,0,2,4],[3,0,4,1,5,2],[0,4,1,3,2,5],[0,1,2,3,4,5],[0,1,2,3,4,5],[0,1,2,3,4,5]]"

@[implicit_reducible]
def «Order3 M402» : Magma (Fin 5) where
  op := finOpTable "[[0,0,4,2,3],[1,1,1,1,1],[4,2,0,3,2],[2,3,3,0,4],[3,4,2,4,0]]"

@[implicit_reducible]
def «Order3 M402^op» : Magma (Fin 5) where
  op := finOpTable "[[0,1,4,2,3],[0,1,2,3,4],[4,1,0,3,2],[2,1,3,0,4],[3,1,2,4,0]]"

@[implicit_reducible]
def «Order3 M404» : Magma (Fin 7) where
  op := finOpTable "[[1,2,0,0,6,6,6],[3,1,6,2,3,2,0],[2,6,1,3,0,5,2],[0,5,3,1,4,3,5],[4,3,4,4,1,0,3],[5,4,5,5,5,1,4],[6,0,2,6,2,4,1]]"

@[implicit_reducible]
def «Order3 M404^op» : Magma (Fin 7) where
  op := finOpTable "[[1,3,2,0,4,5,6],[2,1,6,5,3,4,0],[0,6,1,3,4,5,2],[0,2,3,1,4,5,6],[6,3,0,4,1,5,2],[6,2,5,3,0,1,4],[6,0,2,5,3,4,1]]"

@[implicit_reducible]
def «Order3 M406» : Magma (Fin 6) where
  op := finOpTable "[[1,2,0,3,4,5],[5,1,2,0,4,3],[2,1,4,3,0,5],[0,5,2,3,1,4],[0,1,3,5,4,2],[0,4,2,1,3,5]]"

@[implicit_reducible]
def «Order3 M406^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,2,0,0,0],[2,1,1,5,1,4],[0,2,4,2,3,2],[3,0,3,3,5,1],[4,4,0,1,4,3],[5,3,5,4,2,5]]"

@[implicit_reducible]
def «Order3 M408» : Magma (Fin 9) where
  op := finOpTable "[[7,3,6,8,0,2,5,4,1],[3,5,0,2,1,4,7,8,6],[1,6,4,5,8,7,0,3,2],[2,4,3,0,5,1,8,6,7],[6,0,8,7,2,3,1,5,4],[4,8,5,1,7,6,2,0,3],[5,7,1,4,6,8,3,2,0],[8,2,7,6,3,0,4,1,5],[0,1,2,3,4,5,6,7,8]]"

@[implicit_reducible]
def «Order3 M408^op» : Magma (Fin 9) where
  op := finOpTable "[[7,3,1,2,6,4,5,8,0],[3,5,6,4,0,8,7,2,1],[6,0,4,3,8,5,1,7,2],[8,2,5,0,7,1,4,6,3],[0,1,8,5,2,7,6,3,4],[2,4,7,1,3,6,8,0,5],[5,7,0,8,1,2,3,4,6],[4,8,3,6,5,0,2,1,7],[1,6,2,7,4,3,0,5,8]]"

@[implicit_reducible]
def «Order3 M410» : Magma (Fin 6) where
  op := finOpTable "[[2,1,4,3,0,5],[1,2,0,4,5,3],[4,3,0,5,2,1],[0,1,2,3,4,5],[0,1,2,3,4,5],[0,1,2,3,4,5]]"

@[implicit_reducible]
def «Order3 M410^op» : Magma (Fin 6) where
  op := finOpTable "[[2,1,4,0,0,0],[1,2,3,1,1,1],[4,0,0,2,2,2],[3,4,5,3,3,3],[0,5,2,4,4,4],[5,3,1,5,5,5]]"

@[implicit_reducible]
def «Order3 M412» : Magma (Fin 8) where
  op := finOpTable "[[4,3,1,2,6,5,0,7],[0,2,5,3,7,1,4,6],[1,5,2,6,4,0,7,3],[2,3,6,4,1,5,0,7],[6,5,2,1,4,3,7,0],[7,1,0,5,3,4,6,2],[0,4,7,3,5,1,2,6],[7,1,3,5,0,2,6,4]]"

@[implicit_reducible]
def «Order3 M412^op» : Magma (Fin 8) where
  op := finOpTable "[[4,0,1,2,6,7,0,7],[3,2,5,3,5,1,4,1],[1,5,2,6,2,0,7,3],[2,3,6,4,1,5,3,5],[6,7,4,1,4,3,5,0],[5,1,0,5,3,4,1,2],[0,4,7,0,7,6,2,6],[7,6,3,7,0,2,6,4]]"

@[implicit_reducible]
def «Order3 M414» : Magma (Fin 15) where
  op := finOpTable "[[5,6,7,12,10,8,11,13,0,3,14,1,9,2,4],[10,2,8,4,6,13,3,5,1,14,12,9,0,7,11],[3,8,1,14,12,11,5,10,2,7,9,6,13,4,0],[11,9,13,7,0,2,12,8,3,10,1,4,14,5,6],[6,10,11,5,9,12,13,1,4,8,7,14,3,0,2],[8,14,12,1,11,0,9,4,5,13,2,7,10,6,3],[12,7,0,11,14,4,10,9,6,1,8,13,2,3,5],[14,0,6,8,2,9,4,3,7,12,13,10,5,11,1],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14],[7,13,3,6,8,14,2,11,9,4,5,0,1,12,10],[13,11,4,2,3,1,8,14,10,0,6,5,7,9,12],[2,4,10,9,13,3,14,6,11,5,0,12,8,1,7],[4,5,14,13,7,6,1,0,12,2,3,8,11,10,9],[1,3,9,0,5,10,7,12,13,11,4,2,6,14,8],[9,12,5,10,1,7,0,2,14,6,11,3,4,8,13]]"

@[implicit_reducible]
def «Order3 M414^op» : Magma (Fin 15) where
  op := finOpTable "[[5,10,3,11,6,8,12,14,0,7,13,2,4,1,9],[6,2,8,9,10,14,7,0,1,13,11,4,5,3,12],[7,8,1,13,11,12,0,6,2,3,4,10,14,9,5],[12,4,14,7,5,1,11,8,3,6,2,9,13,0,10],[10,6,12,0,9,11,14,2,4,8,3,13,7,5,1],[8,13,11,2,12,0,4,9,5,14,1,3,6,10,7],[11,3,5,12,13,9,10,4,6,2,8,14,1,7,0],[13,5,10,8,1,4,9,3,7,11,14,6,0,12,2],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14],[3,14,7,10,8,13,1,12,9,4,0,5,2,11,6],[14,12,9,1,7,2,8,13,10,5,6,0,3,4,11],[1,9,6,4,14,7,13,10,11,0,5,12,8,2,3],[9,0,13,14,3,10,2,5,12,1,7,8,11,6,4],[2,7,4,5,0,6,3,11,13,12,9,1,10,14,8],[4,11,0,6,2,3,5,1,14,10,12,7,9,8,13]]"

@[implicit_reducible]
def «Order3 M416» : Magma (Fin 9) where
  op := finOpTable "[[0,1,2,3,4,5,6,7,8],[1,7,4,8,2,3,5,0,6],[2,6,8,5,3,7,1,4,0],[3,2,7,6,8,1,0,5,4],[4,3,6,1,5,0,8,2,7],[5,8,1,2,0,4,7,6,3],[6,4,5,0,7,2,3,8,1],[7,0,3,4,6,8,2,1,5],[8,5,0,7,1,6,4,3,2]]"

@[implicit_reducible]
def «Order3 M417» : Magma (Fin 9) where
  op := finOpTable "[[5,2,7,1,6,8,3,4,0],[2,6,3,4,5,7,8,0,1],[3,7,4,5,8,1,0,6,2],[1,4,5,7,0,6,2,8,3],[6,5,8,0,2,3,7,1,4],[8,3,1,6,7,0,4,2,5],[7,8,0,2,3,4,1,5,6],[4,0,6,8,1,2,5,3,7],[0,1,2,3,4,5,6,7,8]]"

@[implicit_reducible]
def «Order3 M417^op» : Magma (Fin 9) where
  op := finOpTable "[[5,2,3,1,6,8,7,4,0],[2,6,7,4,5,3,8,0,1],[7,3,4,5,8,1,0,6,2],[1,4,5,7,0,6,2,8,3],[6,5,8,0,2,7,3,1,4],[8,7,1,6,3,0,4,2,5],[3,8,0,2,7,4,1,5,6],[4,0,6,8,1,2,5,3,7],[0,1,2,3,4,5,6,7,8]]"

@[implicit_reducible]
def «Order3 M419» : Magma (Fin 7) where
  op := finOpTable "[[2,4,6,1,5,3,0],[3,5,4,2,0,6,1],[6,3,0,5,1,4,2],[5,0,1,4,6,2,3],[1,2,5,6,3,0,4],[4,6,3,0,2,1,5],[0,1,2,3,4,5,6]]"

@[implicit_reducible]
def «Order3 M420» : Magma (Fin 15) where
  op := finOpTable "[[5,2,8,11,6,14,12,10,1,7,9,13,4,3,0],[9,6,10,4,11,8,14,5,7,12,13,3,0,2,1],[4,3,7,5,10,1,13,14,12,8,0,6,9,11,2],[7,0,4,8,12,13,11,1,14,6,5,9,2,10,3],[11,5,13,10,9,12,3,0,2,14,6,7,1,8,4],[14,13,11,6,2,0,7,3,10,1,12,4,8,9,5],[3,14,0,2,13,4,1,11,9,10,8,12,7,5,6],[6,12,14,13,3,9,8,2,0,11,1,5,10,4,7],[12,10,6,14,1,2,5,9,3,13,4,0,11,7,8],[13,8,5,7,14,10,0,12,11,4,2,1,3,6,9],[8,9,12,1,5,7,2,4,13,3,11,14,6,0,10],[2,7,9,12,8,3,4,13,6,0,14,10,5,1,11],[10,11,1,0,7,6,9,8,4,5,3,2,13,14,12],[1,4,3,9,0,11,10,6,5,2,7,8,14,12,13],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14]]"

@[implicit_reducible]
def «Order3 M421» : Magma (Fin 5) where
  op := finOpTable "[[1,4,4,3,0],[3,0,0,1,4],[3,0,0,2,4],[0,3,3,4,2],[4,1,2,0,3]]"

@[implicit_reducible]
def «Order3 M422» : Magma (Fin 8) where
  op := finOpTable "[[7,5,0,3,4,2,0,6],[7,5,1,3,4,2,1,6],[2,2,4,1,0,5,4,7],[0,1,5,6,6,3,7,3],[0,1,5,2,2,4,7,4],[4,3,2,5,5,1,6,0],[6,6,3,0,1,5,3,7],[3,4,2,7,7,1,6,0]]"

@[implicit_reducible]
def «Order3 M423» : Magma (Fin 3) where
  op := finOpTable "[[1,1,0],[1,1,0],[0,0,0]]"

@[implicit_reducible]
def «Order3 M424» : Magma (Fin 5) where
  op := finOpTable "[[1,2,0,0,4],[2,1,3,4,0],[0,3,1,2,4],[0,4,2,1,3],[4,0,4,3,1]]"

@[implicit_reducible]
def «Order3 M425» : Magma (Fin 5) where
  op := finOpTable "[[2,3,4,4,0],[3,3,0,4,1],[4,0,0,3,2],[4,4,3,1,3],[0,1,2,3,4]]"

@[implicit_reducible]
def «Order3 M426» : Magma (Fin 15) where
  op := finOpTable "[[2,5,0,3,10,12,4,11,7,14,13,9,1,8,6],[9,2,1,6,4,10,14,5,0,7,3,13,11,12,8],[3,4,2,0,1,8,7,6,5,12,11,10,9,14,13],[0,11,3,2,8,6,10,1,9,4,12,14,13,7,5],[7,1,4,12,2,3,8,13,11,10,14,0,6,5,9],[4,6,5,13,14,2,11,3,8,0,9,1,7,10,12],[13,0,6,8,9,4,2,7,12,11,5,3,14,1,10],[5,12,7,14,3,9,6,2,1,13,0,8,10,11,4],[14,13,8,1,7,5,0,10,2,6,4,12,3,9,11],[10,3,9,5,13,11,1,8,14,2,6,4,12,0,7],[1,8,10,7,12,14,13,9,6,3,2,11,5,4,0],[6,9,11,4,5,7,12,14,13,8,10,2,0,3,1],[8,14,12,11,0,13,5,4,10,9,1,7,2,6,3],[11,10,13,9,6,0,3,12,4,1,7,5,8,2,14],[12,7,14,10,11,1,9,0,3,5,8,6,4,13,2]]"

@[implicit_reducible]
def «Order3 M426^op» : Magma (Fin 15) where
  op := finOpTable "[[2,9,3,0,7,4,13,5,14,10,1,6,8,11,12],[5,2,4,11,1,6,0,12,13,3,8,9,14,10,7],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14],[3,6,0,2,12,13,8,14,1,5,7,4,11,9,10],[10,4,1,8,2,14,9,3,7,13,12,5,0,6,11],[12,10,8,6,3,2,4,9,5,11,14,7,13,0,1],[4,14,7,10,8,11,2,6,0,1,13,12,5,3,9],[11,5,6,1,13,3,7,2,10,8,9,14,4,12,0],[7,0,5,9,11,8,12,1,2,14,6,13,10,4,3],[14,7,12,4,10,0,11,13,6,2,3,8,9,1,5],[13,3,11,12,14,9,5,0,4,6,2,10,1,7,8],[9,13,10,14,0,1,3,8,12,4,11,2,7,5,6],[1,11,9,13,6,7,14,10,3,12,5,0,2,8,4],[8,12,14,7,5,10,1,11,9,0,4,3,6,2,13],[6,8,13,5,9,12,10,4,11,7,0,1,3,14,2]]"

@[implicit_reducible]
def «Order3 M428» : Magma (Fin 7) where
  op := finOpTable "[[6,0,2,0,0,2,3],[1,6,1,1,4,1,5],[2,2,6,3,2,3,0],[0,3,3,6,3,0,2],[4,4,4,4,6,5,1],[5,1,5,5,5,6,4],[3,5,0,2,1,4,6]]"

@[implicit_reducible]
def «Order3 M428^op» : Magma (Fin 7) where
  op := finOpTable "[[6,1,2,0,4,5,3],[0,6,2,3,4,1,5],[2,1,6,3,4,5,0],[0,1,3,6,4,5,2],[0,4,2,3,6,5,1],[2,1,3,0,5,6,4],[3,5,0,2,1,4,6]]"

@[implicit_reducible]
def «Order3 M430» : Magma (Fin 7) where
  op := finOpTable "[[6,0,0,3,2,0,4],[1,6,2,1,0,1,5],[2,2,6,2,1,5,1],[3,3,3,6,4,3,0],[0,4,4,4,6,4,3],[5,1,5,5,5,6,2],[4,5,1,0,3,2,6]]"

@[implicit_reducible]
def «Order3 M430^op» : Magma (Fin 7) where
  op := finOpTable "[[6,1,2,3,0,5,4],[0,6,2,3,4,1,5],[0,2,6,3,4,5,1],[3,1,2,6,4,5,0],[2,0,1,4,6,5,3],[0,1,5,3,4,6,2],[4,5,1,0,3,2,6]]"

@[implicit_reducible]
def «Order3 M432» : Magma (Fin 4) where
  op := finOpTable "[[3,1,2,3],[2,3,3,0],[0,1,3,0],[0,3,2,3]]"

@[implicit_reducible]
def «Order3 M432^op» : Magma (Fin 4) where
  op := finOpTable "[[3,2,0,0],[1,3,1,3],[2,3,3,2],[3,0,0,3]]"

@[implicit_reducible]
def «Order3 M434» : Magma (Fin 5) where
  op := finOpTable "[[2,0,4,3,1],[1,2,3,0,4],[3,4,2,1,0],[4,1,0,2,3],[0,3,1,4,2]]"

@[implicit_reducible]
def «Order3 M434^op» : Magma (Fin 5) where
  op := finOpTable "[[2,1,3,4,0],[0,2,4,1,3],[4,3,2,0,1],[3,0,1,2,4],[1,4,0,3,2]]"

@[implicit_reducible]
def «Order3 M436» : Magma (Fin 5) where
  op := finOpTable "[[4,4,4,4,4],[3,4,4,4,4],[3,0,4,3,4],[3,4,2,4,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «Order3 M436^op» : Magma (Fin 5) where
  op := finOpTable "[[4,3,3,3,0],[4,4,0,4,1],[4,4,4,2,2],[4,4,3,4,3],[4,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M438» : Magma (Fin 13) where
  op := finOpTable "[[1,11,3,6,10,7,2,8,5,4,9,0,12],[2,1,12,4,9,8,5,10,6,3,11,7,0],[0,7,1,5,8,10,9,2,11,12,3,4,6],[4,8,5,1,7,12,11,0,3,9,6,10,2],[10,6,11,3,1,0,4,12,2,7,5,8,9],[9,4,0,7,5,1,6,11,10,2,12,3,8],[7,5,9,11,0,6,1,4,8,10,2,12,3],[8,10,6,2,12,4,3,1,9,0,7,11,5],[6,9,4,12,11,5,10,3,1,8,0,2,7],[11,3,7,9,4,2,0,5,12,1,8,6,10],[3,2,10,8,6,9,12,7,0,11,1,5,4],[5,12,8,0,2,3,7,9,4,6,10,1,11],[12,0,2,10,3,11,8,6,7,5,4,9,1]]"

@[implicit_reducible]
def «Order3 M439» : Magma (Fin 13) where
  op := finOpTable "[[4,3,12,7,11,2,9,1,6,8,10,0,5],[2,4,5,10,12,0,6,8,11,3,9,7,1],[9,11,4,2,3,1,10,6,8,12,7,5,0],[5,7,2,4,8,6,0,11,3,10,12,1,9],[11,12,3,8,4,9,1,5,2,7,0,10,6],[6,10,11,1,9,4,8,7,0,5,3,12,2],[3,6,7,9,1,11,4,10,5,0,2,8,12],[8,0,10,12,5,7,2,4,1,9,6,3,11],[12,5,8,3,2,10,11,0,4,6,1,9,7],[1,2,0,11,7,5,3,9,12,4,8,6,10],[10,8,6,5,0,12,7,2,9,1,4,11,3],[0,9,1,6,10,3,5,12,7,2,11,4,8],[7,1,9,0,6,8,12,3,10,11,5,2,4]]"

@[implicit_reducible]
def «Order3 M440» : Magma (Fin 3) where
  op := finOpTable "[[1,1,1],[0,1,2],[0,1,2]]"

@[implicit_reducible]
def «Order3 M440^op» : Magma (Fin 3) where
  op := finOpTable "[[1,0,0],[1,1,1],[1,2,2]]"

@[implicit_reducible]
def «Order3 M442» : Magma (Fin 4) where
  op := finOpTable "[[3,3,3,3],[0,1,0,3],[3,3,2,3],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M442^op» : Magma (Fin 4) where
  op := finOpTable "[[3,0,3,0],[3,1,3,1],[3,0,2,2],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M444» : Magma (Fin 4) where
  op := finOpTable "[[3,1,2,3],[2,3,2,3],[3,1,3,3],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M444^op» : Magma (Fin 4) where
  op := finOpTable "[[3,2,3,0],[1,3,1,1],[2,2,3,2],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M446» : Magma (Fin 3) where
  op := finOpTable "[[2,1,2],[2,1,2],[0,1,2]]"

@[implicit_reducible]
def «Order3 M446^op» : Magma (Fin 3) where
  op := finOpTable "[[2,2,0],[1,1,1],[2,2,2]]"

@[implicit_reducible]
def «Order3 M448» : Magma (Fin 3) where
  op := finOpTable "[[2,2,2],[0,2,2],[0,1,2]]"

@[implicit_reducible]
def «Order3 M448^op» : Magma (Fin 3) where
  op := finOpTable "[[2,0,0],[2,2,1],[2,2,2]]"

@[implicit_reducible]
def «Order3 M450» : Magma (Fin 4) where
  op := finOpTable "[[3,1,0,3],[0,2,2,3],[3,1,3,3],[0,1,2,1]]"

@[implicit_reducible]
def «Order3 M450^op» : Magma (Fin 4) where
  op := finOpTable "[[3,0,3,0],[1,2,1,1],[0,2,3,2],[3,3,3,1]]"

@[implicit_reducible]
def «Order3 M452» : Magma (Fin 3) where
  op := finOpTable "[[1,1,2],[0,0,2],[0,1,2]]"

@[implicit_reducible]
def «Order3 M452^op» : Magma (Fin 3) where
  op := finOpTable "[[1,0,0],[1,0,1],[2,2,2]]"

@[implicit_reducible]
def «Order3 M454» : Magma (Fin 4) where
  op := finOpTable "[[2,1,2,2],[3,3,2,3],[0,0,0,3],[0,1,1,1]]"

@[implicit_reducible]
def «Order3 M454^op» : Magma (Fin 4) where
  op := finOpTable "[[2,3,0,0],[1,3,0,1],[2,2,0,1],[2,3,3,1]]"

@[implicit_reducible]
def «Order3 M456» : Magma (Fin 4) where
  op := finOpTable "[[2,3,2,2],[1,1,1,1],[0,2,0,2],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M456^op» : Magma (Fin 4) where
  op := finOpTable "[[2,1,0,3],[3,1,2,3],[2,1,0,3],[2,1,2,3]]"

@[implicit_reducible]
def «Order3 M458» : Magma (Fin 4) where
  op := finOpTable "[[3,2,3,3],[2,2,2,1],[2,1,1,1],[0,0,3,0]]"

@[implicit_reducible]
def «Order3 M458^op» : Magma (Fin 4) where
  op := finOpTable "[[3,2,2,0],[2,2,1,0],[3,2,1,3],[3,1,1,0]]"

@[implicit_reducible]
def «Order3 M460» : Magma (Fin 11) where
  op := finOpTable "[[0,2,4,5,1,6,3,0,0,0,0],[4,3,0,3,2,7,8,9,10,5,6],[1,4,2,7,0,2,2,8,3,2,2],[6,1,8,1,9,0,5,2,7,10,4],[2,0,1,10,4,4,4,4,4,3,9],[3,9,5,6,5,5,0,1,5,7,5],[5,10,6,0,6,3,6,6,1,6,8],[7,5,3,8,7,9,7,7,2,1,7],[8,6,7,2,8,8,10,3,8,8,1],[9,7,9,4,10,1,9,5,9,9,3],[10,8,10,9,3,10,1,10,6,4,10]]"

@[implicit_reducible]
def «Order3 M460^op» : Magma (Fin 11) where
  op := finOpTable "[[0,4,1,6,2,3,5,7,8,9,10],[2,3,4,1,0,9,10,5,6,7,8],[4,0,2,8,1,5,6,3,7,9,10],[5,3,7,1,10,6,0,8,2,4,9],[1,2,0,9,4,5,6,7,8,10,3],[6,7,2,0,4,5,3,9,8,1,10],[3,8,2,5,4,0,6,7,10,9,1],[0,9,8,2,4,1,6,7,3,5,10],[0,10,3,7,4,5,1,2,8,9,6],[0,5,2,10,3,7,6,1,8,9,4],[0,6,2,4,9,5,8,7,1,3,10]]"

@[implicit_reducible]
def «Order3 M462» : Magma (Fin 4) where
  op := finOpTable "[[0,1,2,0],[0,1,1,0],[0,2,2,3],[3,2,2,3]]"

@[implicit_reducible]
def «Order3 M462^op» : Magma (Fin 4) where
  op := finOpTable "[[0,0,0,3],[1,1,2,2],[2,1,2,2],[0,0,3,3]]"

@[implicit_reducible]
def «Order3 M464» : Magma (Fin 8) where
  op := finOpTable "[[2,6,2,2,6,2,6,2],[3,3,5,3,3,5,3,5],[0,0,0,4,4,0,4,0],[7,1,1,1,1,7,1,7],[2,6,2,6,6,2,6,2],[7,1,7,1,1,7,1,7],[0,4,0,4,4,0,4,0],[5,3,5,3,3,5,3,5]]"

@[implicit_reducible]
def «Order3 M464^op» : Magma (Fin 8) where
  op := finOpTable "[[2,3,0,7,2,7,0,5],[6,3,0,1,6,1,4,3],[2,5,0,1,2,7,0,5],[2,3,4,1,6,1,4,3],[6,3,4,1,6,1,4,3],[2,5,0,7,2,7,0,5],[6,3,4,1,6,1,4,3],[2,5,0,7,2,7,0,5]]"

@[implicit_reducible]
def «Order3 M466» : Magma (Fin 5) where
  op := finOpTable "[[2,4,2,4,2],[1,1,1,1,1],[0,3,0,0,3],[2,2,4,4,4],[3,0,0,3,3]]"

@[implicit_reducible]
def «Order3 M466^op» : Magma (Fin 5) where
  op := finOpTable "[[2,1,0,2,3],[4,1,3,2,0],[2,1,0,4,0],[4,1,0,4,3],[2,1,3,4,3]]"

@[implicit_reducible]
def «Order3 M468» : Magma (Fin 7) where
  op := finOpTable "[[3,2,2,3,3,6,6],[3,2,2,4,4,2,4],[0,1,1,0,6,1,6],[0,5,1,0,0,5,5],[4,1,1,4,4,1,4],[3,5,5,3,3,5,5],[0,2,2,0,6,6,6]]"

@[implicit_reducible]
def «Order3 M468^op» : Magma (Fin 7) where
  op := finOpTable "[[3,3,0,0,4,3,0],[2,2,1,5,1,5,2],[2,2,1,1,1,5,2],[3,4,0,0,4,3,0],[3,4,6,0,4,3,6],[6,2,1,5,1,5,6],[6,4,6,5,4,5,6]]"

@[implicit_reducible]
def «Order3 M470» : Magma (Fin 3) where
  op := finOpTable "[[0,0,0],[2,2,2],[0,1,1]]"

@[implicit_reducible]
def «Order3 M470^op» : Magma (Fin 3) where
  op := finOpTable "[[0,2,0],[0,2,1],[0,2,1]]"

@[implicit_reducible]
def «Order3 M472» : Magma (Fin 6) where
  op := finOpTable "[[4,2,2,4,4,4],[2,3,2,3,2,3],[2,2,2,2,2,2],[5,1,1,1,5,5],[0,0,0,0,0,0],[5,5,5,5,5,5]]"

@[implicit_reducible]
def «Order3 M472^op» : Magma (Fin 6) where
  op := finOpTable "[[4,2,2,5,0,5],[2,3,2,1,0,5],[2,2,2,1,0,5],[4,3,2,1,0,5],[4,2,2,5,0,5],[4,3,2,5,0,5]]"

@[implicit_reducible]
def «Order3 M474» : Magma (Fin 8) where
  op := finOpTable "[[5,2,2,5,5,5,5,5],[6,2,2,2,6,6,6,2],[3,1,1,3,1,3,1,3],[7,2,2,7,7,7,7,7],[6,6,6,6,6,6,6,6],[0,0,0,6,6,0,6,6],[5,1,1,7,4,5,4,7],[6,3,3,3,6,6,6,3]]"

@[implicit_reducible]
def «Order3 M474^op» : Magma (Fin 8) where
  op := finOpTable "[[5,6,3,7,6,0,5,6],[2,2,1,2,6,0,1,3],[2,2,1,2,6,0,1,3],[5,2,3,7,6,6,7,3],[5,6,1,7,6,6,4,6],[5,6,3,7,6,0,5,6],[5,6,1,7,6,6,4,6],[5,2,3,7,6,6,7,3]]"

@[implicit_reducible]
def «Order3 M476» : Magma (Fin 4) where
  op := finOpTable "[[2,1,2,2],[0,3,3,3],[0,0,0,3],[1,1,2,1]]"

@[implicit_reducible]
def «Order3 M476^op» : Magma (Fin 4) where
  op := finOpTable "[[2,0,0,1],[1,3,0,1],[2,3,0,2],[2,3,3,1]]"

@[implicit_reducible]
def «Order3 M478» : Magma (Fin 5) where
  op := finOpTable "[[3,2,2,3,3],[1,1,1,1,1],[0,0,4,4,4],[0,4,0,0,4],[2,3,2,3,2]]"

@[implicit_reducible]
def «Order3 M478^op» : Magma (Fin 5) where
  op := finOpTable "[[3,1,0,0,2],[2,1,0,4,3],[2,1,4,0,2],[3,1,4,0,3],[3,1,4,4,2]]"

@[implicit_reducible]
def «Order3 M480» : Magma (Fin 5) where
  op := finOpTable "[[2,2,2,2,2],[1,1,1,1,1],[0,3,0,0,3],[2,4,4,4,4],[3,3,3,3,3]]"

@[implicit_reducible]
def «Order3 M480^op» : Magma (Fin 5) where
  op := finOpTable "[[2,1,0,2,3],[2,1,3,4,3],[2,1,0,4,3],[2,1,0,4,3],[2,1,3,4,3]]"

@[implicit_reducible]
def «Order3 M482» : Magma (Fin 4) where
  op := finOpTable "[[1,1,1,1],[0,0,0,3],[0,3,3,3],[2,2,2,2]]"

@[implicit_reducible]
def «Order3 M482^op» : Magma (Fin 4) where
  op := finOpTable "[[1,0,0,2],[1,0,3,2],[1,0,3,2],[1,3,3,2]]"

@[implicit_reducible]
def «Order3 M484» : Magma (Fin 4) where
  op := finOpTable "[[2,2,2,0],[3,1,1,1],[0,2,0,0],[3,3,1,3]]"

@[implicit_reducible]
def «Order3 M484^op» : Magma (Fin 4) where
  op := finOpTable "[[2,3,0,3],[2,1,2,3],[2,1,0,1],[0,1,0,3]]"

@[implicit_reducible]
def «Order3 M486» : Magma (Fin 6) where
  op := finOpTable "[[4,1,4,4,4,4],[2,5,0,5,5,5],[3,1,3,3,3,3],[2,2,2,2,2,4],[0,0,0,0,0,3],[1,1,1,5,5,1]]"

@[implicit_reducible]
def «Order3 M486^op» : Magma (Fin 6) where
  op := finOpTable "[[4,2,3,2,0,1],[1,5,1,2,0,1],[4,0,3,2,0,1],[4,5,3,2,0,5],[4,5,3,2,0,5],[4,5,3,4,3,1]]"

@[implicit_reducible]
def «Order3 M488» : Magma (Fin 6) where
  op := finOpTable "[[0,2,0,4,0,0],[5,3,3,3,3,3],[4,4,4,4,4,0],[5,1,1,1,1,1],[2,2,2,2,2,0],[5,5,1,5,3,5]]"

@[implicit_reducible]
def «Order3 M488^op» : Magma (Fin 6) where
  op := finOpTable "[[0,5,4,5,2,5],[2,3,4,1,2,5],[0,3,4,1,2,1],[4,3,4,1,2,5],[0,3,4,1,2,3],[0,3,0,1,0,5]]"

@[implicit_reducible]
def «Order3 M490» : Magma (Fin 4) where
  op := finOpTable "[[1,2,0,3],[0,1,2,3],[0,3,1,2],[3,0,2,1]]"

@[implicit_reducible]
def «Order3 M490^op» : Magma (Fin 4) where
  op := finOpTable "[[1,0,0,3],[2,1,3,0],[0,2,1,2],[3,3,2,1]]"

@[implicit_reducible]
def «Order3 M492» : Magma (Fin 6) where
  op := finOpTable "[[0,1,2,3,4,5],[4,0,2,3,1,5],[0,1,2,3,4,5],[0,1,2,3,4,5],[0,1,2,5,3,4],[0,5,1,3,4,2]]"

@[implicit_reducible]
def «Order3 M492^op» : Magma (Fin 6) where
  op := finOpTable "[[0,4,0,0,0,0],[1,0,1,1,1,5],[2,2,2,2,2,1],[3,3,3,3,5,3],[4,1,4,4,3,4],[5,5,5,5,4,2]]"

@[implicit_reducible]
def «Order3 M494» : Magma (Fin 9) where
  op := finOpTable "[[4,0,6,2,1,5,3,7,8],[0,2,8,3,4,5,6,7,1],[3,1,2,7,4,5,6,0,8],[0,3,8,4,1,5,6,2,7],[0,1,2,3,4,5,6,7,8],[0,1,2,3,4,5,6,7,8],[0,1,2,3,4,5,6,7,8],[2,7,5,6,1,0,8,4,3],[8,1,2,3,4,0,6,7,5]]"

@[implicit_reducible]
def «Order3 M494^op» : Magma (Fin 9) where
  op := finOpTable "[[4,0,3,0,0,0,0,2,8],[0,2,1,3,1,1,1,7,1],[6,8,2,8,2,2,2,5,2],[2,3,7,4,3,3,3,6,3],[1,4,4,1,4,4,4,1,4],[5,5,5,5,5,5,5,0,0],[3,6,6,6,6,6,6,8,6],[7,7,0,2,7,7,7,4,7],[8,1,8,7,8,8,8,3,5]]"

@[implicit_reducible]
def «Order3 M496» : Magma (Fin 4) where
  op := finOpTable "[[3,1,2,3],[0,3,0,3],[0,1,2,3],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M496^op» : Magma (Fin 4) where
  op := finOpTable "[[3,0,0,0],[1,3,1,1],[2,0,2,2],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M498» : Magma (Fin 4) where
  op := finOpTable "[[2,1,2,3],[0,3,0,3],[0,1,2,3],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M498^op» : Magma (Fin 4) where
  op := finOpTable "[[2,0,0,0],[1,3,1,1],[2,0,2,2],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M500» : Magma (Fin 4) where
  op := finOpTable "[[3,1,2,1],[0,2,0,3],[0,1,2,3],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M500^op» : Magma (Fin 4) where
  op := finOpTable "[[3,0,0,0],[1,2,1,1],[2,0,2,2],[1,3,3,3]]"

@[implicit_reducible]
def «Order3 M502» : Magma (Fin 4) where
  op := finOpTable "[[3,2,2,3],[0,1,2,3],[3,1,3,3],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M502^op» : Magma (Fin 4) where
  op := finOpTable "[[3,0,3,0],[2,1,1,1],[2,2,3,2],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M504» : Magma (Fin 4) where
  op := finOpTable "[[3,2,0,2],[2,3,1,2],[0,1,2,3],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M504^op» : Magma (Fin 4) where
  op := finOpTable "[[3,2,0,0],[2,3,1,1],[0,1,2,2],[2,2,3,3]]"

@[implicit_reducible]
def «Order3 M506» : Magma (Fin 5) where
  op := finOpTable "[[3,2,0,2,4],[2,3,0,4,1],[0,1,3,4,2],[0,1,2,3,4],[4,1,2,0,3]]"

@[implicit_reducible]
def «Order3 M506^op» : Magma (Fin 5) where
  op := finOpTable "[[3,2,0,0,4],[2,3,1,1,1],[0,0,3,2,2],[2,4,4,3,0],[4,1,2,4,3]]"

@[implicit_reducible]
def «Order3 M508» : Magma (Fin 6) where
  op := finOpTable "[[0,1,2,3,4,5],[2,4,2,3,5,1],[0,1,2,3,4,5],[0,3,1,2,4,5],[0,1,2,3,4,5],[3,1,2,5,4,0]]"

@[implicit_reducible]
def «Order3 M508^op» : Magma (Fin 6) where
  op := finOpTable "[[0,2,0,0,0,3],[1,4,1,3,1,1],[2,2,2,1,2,2],[3,3,3,2,3,5],[4,5,4,4,4,4],[5,1,5,5,5,0]]"

@[implicit_reducible]
def «Order3 M510» : Magma (Fin 3) where
  op := finOpTable "[[2,0,1],[0,1,2],[0,1,2]]"

@[implicit_reducible]
def «Order3 M510^op» : Magma (Fin 3) where
  op := finOpTable "[[2,0,0],[0,1,1],[1,2,2]]"

@[implicit_reducible]
def «Order3 M512» : Magma (Fin 8) where
  op := finOpTable "[[3,2,7,4,0,5,6,1],[0,1,2,3,4,5,6,7],[3,1,7,4,0,2,6,5],[0,1,2,3,4,5,6,7],[0,1,2,3,7,4,6,5],[5,1,2,3,4,6,0,7],[0,1,2,3,4,5,6,7],[0,1,2,3,4,5,6,7]]"

@[implicit_reducible]
def «Order3 M512^op» : Magma (Fin 8) where
  op := finOpTable "[[3,0,3,0,0,5,0,0],[2,1,1,1,1,1,1,1],[7,2,7,2,2,2,2,2],[4,3,4,3,3,3,3,3],[0,4,0,4,7,4,4,4],[5,5,2,5,4,6,5,5],[6,6,6,6,6,0,6,6],[1,7,5,7,5,7,7,7]]"

@[implicit_reducible]
def «Order3 M514» : Magma (Fin 5) where
  op := finOpTable "[[4,0,1,0,1],[1,4,0,1,0],[3,3,4,2,3],[2,2,3,4,2],[0,1,2,3,4]]"

@[implicit_reducible]
def «Order3 M514^op» : Magma (Fin 5) where
  op := finOpTable "[[4,1,3,2,0],[0,4,3,2,1],[1,0,4,3,2],[0,1,2,4,3],[1,0,3,2,4]]"

@[implicit_reducible]
def «Order3 M516» : Magma (Fin 5) where
  op := finOpTable "[[4,0,0,0,2],[1,4,1,1,3],[2,2,4,2,0],[3,3,3,4,1],[0,1,2,3,4]]"

@[implicit_reducible]
def «Order3 M516^op» : Magma (Fin 5) where
  op := finOpTable "[[4,1,2,3,0],[0,4,2,3,1],[0,1,4,3,2],[0,1,2,4,3],[2,3,0,1,4]]"

@[implicit_reducible]
def «Order3 M518» : Magma (Fin 7) where
  op := finOpTable "[[0,2,2,4,4,0,0],[6,3,3,3,3,6,6],[0,2,2,2,2,5,0],[5,1,1,1,1,5,5],[0,4,4,4,4,0,4],[5,3,2,3,3,5,5],[6,1,1,1,6,6,6]]"

@[implicit_reducible]
def «Order3 M518^op» : Magma (Fin 7) where
  op := finOpTable "[[0,6,0,5,0,5,6],[2,3,2,1,4,3,1],[2,3,2,1,4,2,1],[4,3,2,1,4,3,1],[4,3,2,1,4,3,6],[0,6,5,5,0,5,6],[0,6,0,5,4,5,6]]"

@[implicit_reducible]
def «Order3 M520» : Magma (Fin 8) where
  op := finOpTable "[[2,1,2,1,2,2,2,1],[0,3,0,3,3,3,0,3],[0,0,0,5,0,5,0,5],[1,1,4,1,4,1,4,1],[6,3,6,3,6,3,6,6],[2,7,2,7,2,7,7,7],[4,7,4,4,4,7,4,7],[6,5,5,5,6,5,6,5]]"

@[implicit_reducible]
def «Order3 M520^op» : Magma (Fin 8) where
  op := finOpTable "[[2,0,0,1,6,2,4,6],[1,3,0,1,3,7,7,5],[2,0,0,4,6,2,4,5],[1,3,5,1,3,7,4,5],[2,3,0,4,6,2,4,6],[2,3,5,1,3,7,7,5],[2,0,0,4,6,7,4,6],[1,3,5,1,6,7,7,5]]"

@[implicit_reducible]
def «Order3 M522» : Magma (Fin 5) where
  op := finOpTable "[[4,4,2,4,4],[4,4,3,3,4],[0,4,4,4,4],[4,1,4,4,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «Order3 M522^op» : Magma (Fin 5) where
  op := finOpTable "[[4,4,0,4,0],[4,4,4,1,1],[2,3,4,4,2],[4,3,4,4,3],[4,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M524» : Magma (Fin 4) where
  op := finOpTable "[[0,1,3,3],[2,1,2,3],[3,3,2,3],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M524^op» : Magma (Fin 4) where
  op := finOpTable "[[0,2,3,0],[1,1,3,1],[3,2,2,2],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M526» : Magma (Fin 4) where
  op := finOpTable "[[0,3,2,3],[0,1,2,3],[1,1,2,3],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M526^op» : Magma (Fin 4) where
  op := finOpTable "[[0,0,1,0],[3,1,1,1],[2,2,2,2],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M528» : Magma (Fin 4) where
  op := finOpTable "[[0,1,2,3],[2,1,2,2],[3,1,2,3],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M528^op» : Magma (Fin 4) where
  op := finOpTable "[[0,2,3,0],[1,1,1,1],[2,2,2,2],[3,2,3,3]]"

@[implicit_reducible]
def «Order3 M530» : Magma (Fin 9) where
  op := finOpTable "[[0,2,7,4,0,7,7,4,7],[1,1,1,1,1,1,1,1,1],[5,3,2,5,5,8,8,5,2],[7,6,0,3,7,0,0,3,0],[4,8,3,0,4,3,3,0,3],[8,0,6,8,8,5,5,8,6],[2,4,5,2,2,6,6,2,5],[3,5,4,7,3,4,4,7,4],[6,7,8,6,6,2,2,6,8]]"

@[implicit_reducible]
def «Order3 M530^op» : Magma (Fin 9) where
  op := finOpTable "[[0,1,5,7,4,8,2,3,6],[2,1,3,6,8,0,4,5,7],[7,1,2,0,3,6,5,4,8],[4,1,5,3,0,8,2,7,6],[0,1,5,7,4,8,2,3,6],[7,1,8,0,3,5,6,4,2],[7,1,8,0,3,5,6,4,2],[4,1,5,3,0,8,2,7,6],[7,1,2,0,3,6,5,4,8]]"

@[implicit_reducible]
def «Order3 M532» : Magma (Fin 4) where
  op := finOpTable "[[0,2,2,1],[2,1,2,2],[0,1,2,3],[2,1,2,3]]"

@[implicit_reducible]
def «Order3 M532^op» : Magma (Fin 4) where
  op := finOpTable "[[0,2,0,2],[2,1,1,1],[2,2,2,2],[1,2,3,3]]"

@[implicit_reducible]
def «Order3 M534» : Magma (Fin 4) where
  op := finOpTable "[[0,2,1,3],[3,1,3,3],[3,3,2,3],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M534^op» : Magma (Fin 4) where
  op := finOpTable "[[0,3,3,0],[2,1,3,1],[1,3,2,2],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M536» : Magma (Fin 4) where
  op := finOpTable "[[0,3,1,3],[3,1,0,3],[3,3,2,3],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M536^op» : Magma (Fin 4) where
  op := finOpTable "[[0,3,3,0],[3,1,3,1],[1,0,2,2],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M538» : Magma (Fin 5) where
  op := finOpTable "[[0,4,3,4,4],[2,1,4,3,4],[4,4,2,4,4],[4,1,4,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «Order3 M538^op» : Magma (Fin 5) where
  op := finOpTable "[[0,2,4,4,0],[4,1,4,1,1],[3,4,2,4,2],[4,3,4,3,3],[4,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M540» : Magma (Fin 4) where
  op := finOpTable "[[0,1,3,3],[2,1,2,1],[2,1,2,2],[0,3,3,3]]"

@[implicit_reducible]
def «Order3 M540^op» : Magma (Fin 4) where
  op := finOpTable "[[0,2,2,0],[1,1,1,3],[3,2,2,3],[3,1,2,3]]"

@[implicit_reducible]
def «Order3 M542» : Magma (Fin 5) where
  op := finOpTable "[[0,1,4,1,4],[0,1,2,0,2],[3,1,2,3,1],[2,4,2,3,4],[0,3,0,3,4]]"

@[implicit_reducible]
def «Order3 M542^op» : Magma (Fin 5) where
  op := finOpTable "[[0,0,3,2,0],[1,1,1,4,3],[4,2,2,2,0],[1,0,3,3,3],[4,2,1,4,4]]"

@[implicit_reducible]
def «Order3 M544» : Magma (Fin 5) where
  op := finOpTable "[[0,2,4,4,4],[4,1,4,4,4],[3,4,2,4,4],[4,4,4,3,4],[0,1,2,3,4]]"

@[implicit_reducible]
def «Order3 M544^op» : Magma (Fin 5) where
  op := finOpTable "[[0,4,3,4,0],[2,1,4,4,1],[4,4,2,4,2],[4,4,4,3,3],[4,4,4,4,4]]"

@[implicit_reducible]
def «Order3 M546» : Magma (Fin 6) where
  op := finOpTable "[[0,2,5,4,2,3],[1,1,1,1,1,1],[5,3,2,0,3,4],[4,5,0,3,5,2],[2,4,3,5,4,0],[3,0,4,2,0,5]]"

@[implicit_reducible]
def «Order3 M546^op» : Magma (Fin 6) where
  op := finOpTable "[[0,1,5,4,2,3],[2,1,3,5,4,0],[5,1,2,0,3,4],[4,1,0,3,5,2],[2,1,3,5,4,0],[3,1,4,2,0,5]]"

@[implicit_reducible]
def «Order3 M548» : Magma (Fin 9) where
  op := finOpTable "[[0,2,8,6,2,8,4,4,6],[5,1,6,8,7,6,8,5,7],[3,6,2,4,6,3,0,0,4],[7,4,4,3,5,7,2,2,5],[2,7,7,0,4,2,3,3,0],[8,3,3,7,1,5,7,8,1],[1,8,0,2,8,0,6,1,2],[4,5,5,1,3,4,1,7,3],[6,0,1,5,0,1,5,6,8]]"

@[implicit_reducible]
def «Order3 M548^op» : Magma (Fin 9) where
  op := finOpTable "[[0,5,3,7,2,8,1,4,6],[2,1,6,4,7,3,8,5,0],[8,6,2,4,7,3,0,5,1],[6,8,4,3,0,7,2,1,5],[2,7,6,5,4,1,8,3,0],[8,6,3,7,2,5,0,4,1],[4,8,0,2,3,7,6,1,5],[4,5,0,2,3,8,1,7,6],[6,7,4,5,0,1,2,3,8]]"

@[implicit_reducible]
def «Order3 M550» : Magma (Fin 4) where
  op := finOpTable "[[0,2,3,3],[2,1,1,1],[2,2,2,2],[0,3,3,3]]"

@[implicit_reducible]
def «Order3 M550^op» : Magma (Fin 4) where
  op := finOpTable "[[0,2,2,0],[2,1,2,3],[3,1,2,3],[3,1,2,3]]"

@[implicit_reducible]
def «Order3 M552» : Magma (Fin 9) where
  op := finOpTable "[[0,2,8,4,6,1,7,5,3],[3,1,4,6,8,7,2,0,5],[4,5,2,1,7,0,3,8,6],[7,4,0,3,5,6,8,1,2],[5,7,6,8,4,2,1,3,0],[8,3,7,2,1,5,0,6,4],[1,8,5,0,3,4,6,2,7],[2,6,3,5,0,8,4,7,1],[6,0,1,7,2,3,5,4,8]]"

@[implicit_reducible]
def «Order3 M553» : Magma (Fin 6) where
  op := finOpTable "[[0,4,4,2,0,1],[2,1,1,0,2,4],[1,2,2,4,1,0],[5,5,5,3,5,3],[4,0,0,1,4,2],[3,3,3,5,3,5]]"

@[implicit_reducible]
def «Order3 M553^op» : Magma (Fin 6) where
  op := finOpTable "[[0,2,1,5,4,3],[4,1,2,5,0,3],[4,1,2,5,0,3],[2,0,4,3,1,5],[0,2,1,5,4,3],[1,4,0,3,2,5]]"

@[implicit_reducible]
def «Order3 M555» : Magma (Fin 8) where
  op := finOpTable "[[0,1,4,3,5,2,6,7],[0,1,2,7,4,5,3,6],[7,1,2,0,4,5,6,3],[0,2,5,3,4,1,6,7],[6,1,2,3,4,5,7,0],[3,1,2,6,4,5,0,7],[0,5,2,3,1,4,6,7],[0,4,1,3,2,5,6,7]]"

@[implicit_reducible]
def «Order3 M555^op» : Magma (Fin 8) where
  op := finOpTable "[[0,0,7,0,6,3,0,0],[1,1,1,2,1,1,5,4],[4,2,2,5,2,2,2,1],[3,7,0,3,3,6,3,3],[5,4,4,4,4,4,1,2],[2,5,5,1,5,5,4,5],[6,3,6,6,7,0,6,6],[7,6,3,7,0,7,7,7]]"

@[implicit_reducible]
def «Order3 M557» : Magma (Fin 6) where
  op := finOpTable "[[0,4,2,2,4,5],[2,1,2,3,4,5],[0,1,2,3,1,0],[5,1,2,3,4,5],[0,1,0,3,4,5],[0,1,3,3,4,5]]"

@[implicit_reducible]
def «Order3 M557^op» : Magma (Fin 6) where
  op := finOpTable "[[0,2,0,5,0,0],[4,1,1,1,1,1],[2,2,2,2,0,3],[2,3,3,3,3,3],[4,4,1,4,4,4],[5,5,0,5,5,5]]"

@[implicit_reducible]
def «Order3 M559» : Magma (Fin 6) where
  op := finOpTable "[[0,1,2,3,3,1],[0,1,2,3,0,5],[0,1,2,4,4,5],[0,1,0,3,4,5],[2,5,2,3,4,5],[4,1,2,3,4,5]]"

@[implicit_reducible]
def «Order3 M559^op» : Magma (Fin 6) where
  op := finOpTable "[[0,0,0,0,2,4],[1,1,1,1,5,1],[2,2,2,0,2,2],[3,3,4,3,3,3],[3,0,4,4,4,4],[1,5,5,5,5,5]]"

@[implicit_reducible]
def «Order3 M561» : Magma (Fin 8) where
  op := finOpTable "[[0,5,2,3,4,5,3,4],[6,1,2,3,7,2,6,7],[0,1,2,7,1,6,6,7],[0,1,4,3,4,5,5,0],[0,0,5,3,4,5,6,3],[0,4,3,3,4,5,0,7],[7,1,2,2,4,1,6,7],[1,1,2,6,2,5,6,7]]"

@[implicit_reducible]
def «Order3 M561^op» : Magma (Fin 8) where
  op := finOpTable "[[0,6,0,0,0,0,7,1],[5,1,1,1,0,4,1,1],[2,2,2,4,5,3,2,2],[3,3,7,3,3,3,2,6],[4,7,1,4,4,4,4,2],[5,2,6,5,5,5,1,5],[3,6,6,5,6,0,6,6],[4,7,7,0,3,7,7,7]]"

@[implicit_reducible]
def «Order3 M563» : Magma (Fin 8) where
  op := finOpTable "[[0,6,6,1,0,1,5,5],[5,1,1,7,5,7,0,0],[3,2,2,6,3,6,4,4],[6,4,4,3,6,3,2,2],[4,7,7,2,4,2,3,3],[7,0,0,5,7,5,1,1],[2,3,3,0,2,0,6,6],[1,5,5,4,1,4,7,7]]"

@[implicit_reducible]
def «Order3 M563^op» : Magma (Fin 8) where
  op := finOpTable "[[0,5,3,6,4,7,2,1],[6,1,2,4,7,0,3,5],[6,1,2,4,7,0,3,5],[1,7,6,3,2,5,0,4],[0,5,3,6,4,7,2,1],[1,7,6,3,2,5,0,4],[5,0,4,2,3,1,6,7],[5,0,4,2,3,1,6,7]]"

@[implicit_reducible]
def «Order3 M565» : Magma (Fin 10) where
  op := finOpTable "[[0,4,3,7,3,6,8,4,5,7],[9,1,5,2,5,9,1,1,1,2],[1,9,2,5,2,1,2,9,2,5],[4,0,7,3,7,4,3,0,3,3],[7,3,4,0,4,7,4,3,4,0],[8,2,9,1,9,5,0,2,6,1],[5,6,6,6,6,8,6,6,0,6],[3,7,0,4,0,3,7,7,7,4],[6,8,8,8,8,0,5,8,8,8],[2,5,1,9,1,2,9,5,9,9]]"

@[implicit_reducible]
def «Order3 M565^op» : Magma (Fin 10) where
  op := finOpTable "[[0,9,1,4,7,8,5,3,6,2],[4,1,9,0,3,2,6,7,8,5],[3,5,2,7,4,9,6,0,8,1],[7,2,5,3,0,1,6,4,8,9],[3,5,2,7,4,9,6,0,8,1],[6,9,1,4,7,5,8,3,0,2],[8,1,2,3,4,0,6,7,5,9],[4,1,9,0,3,2,6,7,8,5],[5,1,2,3,4,6,0,7,8,9],[7,2,5,3,0,1,6,4,8,9]]"

@[implicit_reducible]
def «Order3 M567» : Magma (Fin 6) where
  op := finOpTable "[[0,4,2,3,4,5],[3,1,2,3,4,5],[0,1,2,3,5,5],[0,1,2,3,1,4],[0,1,3,0,4,5],[0,1,2,2,4,5]]"

@[implicit_reducible]
def «Order3 M567^op» : Magma (Fin 6) where
  op := finOpTable "[[0,3,0,0,0,0],[4,1,1,1,1,1],[2,2,2,2,3,2],[3,3,3,3,0,2],[4,4,5,1,4,4],[5,5,5,4,5,5]]"

@[implicit_reducible]
def «Order3 M569» : Magma (Fin 9) where
  op := finOpTable "[[0,2,5,8,4,5,6,6,8],[7,1,4,4,4,7,6,7,8],[3,6,2,3,4,5,6,0,8],[4,7,2,3,4,2,6,7,8],[0,1,2,3,4,5,1,1,3],[0,8,2,0,4,5,7,7,8],[0,1,2,3,2,0,6,7,8],[5,1,1,3,3,5,6,7,1],[0,1,2,3,0,5,6,5,8]]"

@[implicit_reducible]
def «Order3 M569^op» : Magma (Fin 9) where
  op := finOpTable "[[0,7,3,4,0,0,0,5,0],[2,1,6,7,1,8,1,1,1],[5,4,2,2,2,2,2,1,2],[8,4,3,3,3,0,3,3,3],[4,4,4,4,4,4,2,3,0],[5,7,5,2,5,5,0,5,5],[6,6,6,6,1,7,6,6,6],[6,7,0,7,1,7,7,7,5],[8,8,8,8,3,8,8,1,8]]"

@[implicit_reducible]
def «Order3 M571» : Magma (Fin 8) where
  op := finOpTable "[[0,3,4,5,6,1,2,7],[5,1,4,0,6,3,2,7],[3,0,2,1,7,5,4,6],[1,5,4,3,6,0,2,7],[3,0,6,1,4,5,7,2],[3,0,2,1,4,5,6,7],[3,0,7,1,2,5,6,4],[0,1,4,3,6,5,2,7]]"

@[implicit_reducible]
def «Order3 M571^op» : Magma (Fin 8) where
  op := finOpTable "[[0,5,3,1,3,3,3,0],[3,1,0,5,0,0,0,1],[4,4,2,4,6,2,7,4],[5,0,1,3,1,1,1,3],[6,6,7,6,4,4,2,6],[1,3,5,0,5,5,5,5],[2,2,4,2,7,6,6,2],[7,7,6,7,2,7,4,7]]"

@[implicit_reducible]
def «Order3 M573» : Magma (Fin 13) where
  op := finOpTable "[[0,2,3,10,5,6,11,12,7,8,1,4,9],[4,1,10,6,7,0,8,5,9,3,12,2,11],[5,9,2,1,3,12,0,8,10,4,11,7,6],[6,4,8,3,12,10,9,1,5,11,2,0,7],[8,10,7,9,4,11,12,0,2,5,6,3,1],[7,11,1,12,10,5,4,3,6,2,8,9,0],[12,7,4,2,8,1,6,11,3,0,9,5,10],[2,12,6,0,9,4,3,7,11,10,5,1,8],[1,5,0,4,11,2,10,9,8,6,7,12,3],[10,0,11,8,1,3,7,2,12,9,4,6,5],[11,3,5,7,0,9,1,6,4,12,10,8,2],[9,8,12,5,6,7,2,10,0,1,3,11,4],[3,6,9,11,2,8,5,4,1,7,0,10,12]]"

@[implicit_reducible]
def «Order3 M573^op» : Magma (Fin 13) where
  op := finOpTable "[[0,4,5,6,8,7,12,2,1,10,11,9,3],[2,1,9,4,10,11,7,12,5,0,3,8,6],[3,10,2,8,7,1,4,6,0,11,5,12,9],[10,6,1,3,9,12,2,0,4,8,7,5,11],[5,7,3,12,4,10,8,9,11,1,0,6,2],[6,0,12,10,11,5,1,4,2,3,9,7,8],[11,8,0,9,12,4,6,3,10,7,1,2,5],[12,5,8,1,0,3,11,7,9,2,6,10,4],[7,9,10,5,2,6,3,11,8,12,4,0,1],[8,3,4,11,5,2,0,10,6,9,12,1,7],[1,12,11,2,6,8,9,5,7,4,10,3,0],[4,2,7,0,3,9,5,1,12,6,8,11,10],[9,11,6,7,1,0,10,8,3,5,2,4,12]]"

@[implicit_reducible]
def «Order3 M575» : Magma (Fin 6) where
  op := finOpTable "[[0,3,0,1,4,5],[2,1,2,5,1,5],[2,1,2,3,2,5],[2,4,2,3,4,3],[0,4,4,3,4,5],[0,1,2,5,4,5]]"

@[implicit_reducible]
def «Order3 M575^op» : Magma (Fin 6) where
  op := finOpTable "[[0,2,2,2,0,0],[3,1,1,4,4,1],[0,2,2,2,4,2],[1,5,3,3,3,5],[4,1,2,4,4,4],[5,5,5,3,5,5]]"

@[implicit_reducible]
def «Order3 M577» : Magma (Fin 7) where
  op := finOpTable "[[0,6,3,6,4,0,6],[2,1,4,3,4,5,1],[5,5,2,2,4,5,1],[4,1,3,3,4,0,6],[0,1,2,3,4,1,3],[5,1,2,2,2,5,6],[0,6,0,3,0,5,6]]"

@[implicit_reducible]
def «Order3 M577^op» : Magma (Fin 7) where
  op := finOpTable "[[0,2,5,4,0,5,0],[6,1,5,1,1,1,6],[3,4,2,3,2,2,0],[6,3,2,3,3,2,3],[4,4,4,4,4,2,0],[0,5,5,0,1,5,5],[6,1,1,6,3,6,6]]"

@[implicit_reducible]
def «Order3 M579» : Magma (Fin 6) where
  op := finOpTable "[[0,5,0,0,0,3],[1,1,1,1,3,1],[2,0,2,2,1,2],[3,3,3,3,2,4],[4,4,4,4,4,0],[5,2,5,5,5,5]]"

@[implicit_reducible]
def «Order3 M579^op» : Magma (Fin 6) where
  op := finOpTable "[[0,1,2,3,4,5],[5,1,0,3,4,2],[0,1,2,3,4,5],[0,1,2,3,4,5],[0,3,1,2,4,5],[3,1,2,4,0,5]]"

@[implicit_reducible]
def «Order3 M581» : Magma (Fin 7) where
  op := finOpTable "[[0,2,3,1,0,0,0],[1,1,1,6,1,1,4],[2,5,2,2,2,2,1],[3,3,4,3,3,4,3],[4,4,0,4,4,6,2],[5,0,5,5,5,5,5],[6,6,6,0,6,3,6]]"

@[implicit_reducible]
def «Order3 M581^op» : Magma (Fin 7) where
  op := finOpTable "[[0,1,2,3,4,5,6],[2,1,5,3,4,0,6],[3,1,2,4,0,5,6],[1,6,2,3,4,5,0],[0,1,2,3,4,5,6],[0,1,2,4,6,5,3],[0,4,1,3,2,5,6]]"

@[implicit_reducible]
def «Order3 M583» : Magma (Fin 6) where
  op := finOpTable "[[0,4,3,0,0,0],[1,1,0,1,1,1],[4,0,2,2,2,2],[3,3,1,3,3,3],[5,2,4,4,4,4],[2,5,5,5,5,5]]"

@[implicit_reducible]
def «Order3 M583^op» : Magma (Fin 6) where
  op := finOpTable "[[0,1,4,3,5,2],[4,1,0,3,2,5],[3,0,2,1,4,5],[0,1,2,3,4,5],[0,1,2,3,4,5],[0,1,2,3,4,5]]"

@[implicit_reducible]
def «Order3 M585» : Magma (Fin 8) where
  op := finOpTable "[[0,2,1,0,0,6,0,0],[6,1,7,1,1,1,1,1],[3,5,2,2,2,2,2,2],[5,6,6,3,3,3,3,3],[1,4,3,4,4,4,4,4],[2,0,5,5,5,5,5,5],[4,7,4,6,6,7,6,6],[7,3,0,7,7,0,7,7]]"

@[implicit_reducible]
def «Order3 M585^op» : Magma (Fin 8) where
  op := finOpTable "[[0,6,3,5,1,2,4,7],[2,1,5,6,4,0,7,3],[1,7,2,6,3,5,4,0],[0,1,2,3,4,5,6,7],[0,1,2,3,4,5,6,7],[6,1,2,3,4,5,7,0],[0,1,2,3,4,5,6,7],[0,1,2,3,4,5,6,7]]"

@[implicit_reducible]
def «Order3 M587» : Magma (Fin 16) where
  op := finOpTable "[[0,4,8,7,14,3,15,5,13,6,11,12,10,2,1,9],[2,1,3,0,6,12,7,4,5,11,9,10,8,15,13,14],[4,6,2,5,12,15,13,11,9,10,8,14,0,1,7,3],[12,7,6,3,13,11,8,15,2,5,4,9,14,10,0,1],[8,2,9,10,4,14,12,0,7,1,13,6,11,3,15,5],[11,8,13,6,0,5,14,10,12,2,15,4,1,9,3,7],[9,3,5,11,2,4,6,8,10,15,7,1,13,14,12,0],[10,0,14,12,5,9,3,7,15,4,1,2,6,8,11,13],[14,12,4,9,15,1,11,3,8,7,0,13,5,6,10,2],[15,13,12,2,11,10,0,1,4,9,14,8,3,7,5,6],[5,14,0,13,3,2,1,9,11,12,10,15,7,4,6,8],[3,15,7,8,1,6,10,14,0,13,5,11,9,12,2,4],[7,5,10,15,9,8,2,13,1,14,6,3,12,0,4,11],[1,11,15,4,10,7,5,6,14,8,3,0,2,13,9,12],[13,9,11,1,8,0,4,2,6,3,12,7,15,5,14,10],[6,10,1,14,7,13,9,12,3,0,2,5,4,11,8,15]]"

@[implicit_reducible]
def «Order3 M587^op» : Magma (Fin 16) where
  op := finOpTable "[[0,2,4,12,8,11,9,10,14,15,5,3,7,1,13,6],[4,1,6,7,2,8,3,0,12,13,14,15,5,11,9,10],[8,3,2,6,9,13,5,14,4,12,0,7,10,15,11,1],[7,0,5,3,10,6,11,12,9,2,13,8,15,4,1,14],[14,6,12,13,4,0,2,5,15,11,3,1,9,10,8,7],[3,12,15,11,14,5,4,9,1,10,2,6,8,7,0,13],[15,7,13,8,12,14,6,3,11,0,1,10,2,5,4,9],[5,4,11,15,0,10,8,7,3,1,9,14,13,6,2,12],[13,5,9,2,7,12,10,15,8,4,11,0,1,14,6,3],[6,11,10,5,1,2,15,4,7,9,12,13,14,8,3,0],[11,9,8,4,13,15,7,1,0,14,10,5,6,3,12,2],[12,10,14,9,6,4,1,2,13,8,15,11,3,0,7,5],[10,8,0,14,11,1,13,6,5,3,7,9,12,2,15,4],[2,15,1,10,3,9,14,8,6,7,4,12,0,13,5,11],[1,13,7,0,15,3,12,11,10,5,6,2,4,9,14,8],[9,14,3,1,5,7,0,13,2,6,8,4,11,12,10,15]]"

@[implicit_reducible]
def «Order3 M589» : Magma (Fin 16) where
  op := finOpTable "[[0,2,3,1,13,7,5,6,4,15,11,14,9,8,10,12],[6,1,4,7,15,12,9,13,10,0,14,5,11,3,8,2],[11,10,2,4,5,3,0,14,12,7,13,6,15,1,9,8],[9,4,12,3,14,8,15,5,7,11,6,0,13,2,1,10],[8,9,6,11,4,14,12,3,13,10,1,7,2,0,15,5],[3,11,13,14,10,5,2,4,15,8,7,12,1,6,0,9],[14,8,1,10,9,4,6,11,2,5,15,13,0,7,12,3],[12,6,9,0,1,15,4,7,11,14,8,10,3,5,2,13],[13,7,10,12,0,2,11,15,8,6,5,9,14,4,3,1],[5,3,14,8,11,10,13,2,1,9,0,15,6,12,7,4],[7,0,11,15,2,13,3,1,9,12,10,4,8,14,5,6],[15,12,8,2,6,1,14,0,3,13,9,11,5,10,4,7],[10,5,0,9,3,11,7,8,6,4,2,1,12,15,13,14],[4,14,15,5,8,9,1,10,0,3,12,2,7,13,6,11],[1,15,7,13,12,6,8,9,5,2,4,3,10,11,14,0],[2,13,5,6,7,0,10,12,14,1,3,8,4,9,11,15]]"

@[implicit_reducible]
def «Order3 M590» : Magma (Fin 8) where
  op := finOpTable "[[0,1,2,5,4,6,3,7],[0,1,4,3,7,5,6,2],[0,5,2,1,4,3,6,7],[4,1,0,3,2,5,6,7],[0,3,2,6,4,5,1,7],[2,1,7,3,4,5,6,0],[7,1,2,3,0,5,6,4],[0,6,2,3,4,1,5,7]]"

@[implicit_reducible]
def «Order3 M590^op» : Magma (Fin 8) where
  op := finOpTable "[[0,0,0,4,0,2,7,0],[1,1,5,1,3,1,1,6],[2,4,2,0,2,7,2,2],[5,3,1,3,6,3,3,3],[4,7,4,2,4,4,0,4],[6,5,3,5,5,5,5,1],[3,6,6,6,1,6,6,5],[7,2,7,7,7,0,4,7]]"

@[implicit_reducible]
def «Order3 M592» : Magma (Fin 10) where
  op := finOpTable "[[0,8,3,2,4,5,6,7,1,9],[2,1,9,0,3,4,6,7,8,5],[9,7,2,3,4,5,6,1,8,0],[4,6,2,3,0,5,1,7,8,9],[0,7,2,5,4,3,6,1,8,9],[0,6,2,3,9,5,1,7,8,4],[0,1,2,7,4,8,6,3,5,9],[0,1,6,3,8,5,2,7,4,9],[6,1,2,3,4,5,0,9,8,7],[0,8,5,3,4,2,6,7,1,9]]"

@[implicit_reducible]
def «Order3 M592^op» : Magma (Fin 10) where
  op := finOpTable "[[0,2,9,4,0,0,0,0,6,0],[8,1,7,6,7,6,1,1,1,8],[3,9,2,2,2,2,2,6,2,5],[2,0,3,3,5,3,7,3,3,3],[4,3,4,0,4,9,4,8,4,4],[5,4,5,5,3,5,8,5,5,2],[6,6,6,1,6,1,6,2,0,6],[7,7,1,7,1,7,3,7,9,7],[1,8,8,8,8,8,5,4,8,1],[9,5,0,9,9,4,9,9,7,9]]"

@[implicit_reducible]
def «Order3 M594» : Magma (Fin 7) where
  op := finOpTable "[[0,4,2,3,1,2,0],[0,1,5,1,4,5,6],[3,0,2,0,2,2,2],[0,3,2,3,4,3,3],[0,1,4,3,4,4,6],[1,6,5,5,5,5,1],[6,1,6,6,4,5,6]]"

@[implicit_reducible]
def «Order3 M594^op» : Magma (Fin 7) where
  op := finOpTable "[[0,0,3,0,0,1,6],[4,1,0,3,1,6,1],[2,5,2,2,4,5,6],[3,1,0,3,3,5,6],[1,4,2,4,4,5,4],[2,5,2,3,4,5,5],[0,6,2,3,6,1,6]]"

@[implicit_reducible]
def «Order3 M596» : Magma (Fin 7) where
  op := finOpTable "[[0,6,3,3,4,0,6],[2,1,5,3,4,2,1],[5,1,2,2,2,5,1],[4,1,3,3,0,0,6],[0,1,4,3,4,4,6],[5,1,2,2,5,5,6],[4,6,0,3,0,5,6]]"

@[implicit_reducible]
def «Order3 M596^op» : Magma (Fin 7) where
  op := finOpTable "[[0,2,5,4,0,5,4],[6,1,1,1,1,1,6],[3,5,2,3,4,2,0],[3,3,2,3,3,2,3],[4,4,2,0,4,5,0],[0,2,5,0,4,5,5],[6,1,1,6,6,6,6]]"

@[implicit_reducible]
def «Order3 M598» : Magma (Fin 4) where
  op := finOpTable "[[0,1,2,3],[2,1,3,3],[0,1,2,3],[2,1,2,3]]"

@[implicit_reducible]
def «Order3 M598^op» : Magma (Fin 4) where
  op := finOpTable "[[0,2,0,2],[1,1,1,1],[2,3,2,2],[3,3,3,3]]"

@[implicit_reducible]
def «Order3 M600» : Magma (Fin 4) where
  op := finOpTable "[[0,1,2,3],[0,1,2,2],[3,1,2,3],[0,1,2,3]]"

@[implicit_reducible]
def «Order3 M600^op» : Magma (Fin 4) where
  op := finOpTable "[[0,0,3,0],[1,1,1,1],[2,2,2,2],[3,2,3,3]]"

@[implicit_reducible]
def «Order3 M602» : Magma (Fin 6) where
  op := finOpTable "[[0,5,2,3,4,1],[3,1,2,0,4,5],[0,1,2,3,5,4],[0,4,2,3,1,5],[0,1,3,2,4,5],[2,1,0,3,4,5]]"

@[implicit_reducible]
def «Order3 M602^op» : Magma (Fin 6) where
  op := finOpTable "[[0,3,0,0,0,2],[5,1,1,4,1,1],[2,2,2,2,3,0],[3,0,3,3,2,3],[4,4,5,1,4,4],[1,5,4,5,5,5]]"

@[implicit_reducible]
def «Order3 M604» : Magma (Fin 10) where
  op := finOpTable "[[0,6,2,3,4,5,9,7,8,1],[2,1,3,4,0,5,6,7,8,9],[0,7,2,3,4,5,1,6,8,9],[0,5,2,3,4,7,6,1,8,9],[0,9,2,3,4,1,6,7,8,5],[0,1,2,8,3,5,6,7,4,9],[8,1,0,3,4,5,6,7,2,9],[0,1,8,2,4,5,6,7,3,9],[0,1,2,3,4,9,7,5,8,6],[4,1,2,3,8,5,6,7,0,9]]"

@[implicit_reducible]
def «Order3 M604^op» : Magma (Fin 10) where
  op := finOpTable "[[0,2,0,0,0,0,8,0,0,4],[6,1,7,5,9,1,1,1,1,1],[2,3,2,2,2,2,0,8,2,2],[3,4,3,3,3,8,3,2,3,3],[4,0,4,4,4,3,4,4,4,8],[5,5,5,7,1,5,5,5,9,5],[9,6,1,6,6,6,6,6,7,6],[7,7,6,1,7,7,7,7,5,7],[8,8,8,8,8,4,2,3,8,0],[1,9,9,9,5,9,9,9,6,9]]"

@[implicit_reducible]
def «Order3 M606» : Magma (Fin 6) where
  op := finOpTable "[[0,5,2,5,4,5],[2,1,3,3,4,5],[0,4,2,3,4,1],[4,1,2,3,1,5],[0,1,2,2,4,3],[0,1,0,3,0,5]]"

@[implicit_reducible]
def «Order3 M606^op» : Magma (Fin 6) where
  op := finOpTable "[[0,2,0,4,0,0],[5,1,4,1,1,1],[2,3,2,2,2,0],[5,3,3,3,2,3],[4,4,4,1,4,0],[5,5,1,5,3,5]]"

@[implicit_reducible]
def «Order3 M608» : Magma (Fin 7) where
  op := finOpTable "[[0,6,2,3,4,5,1],[2,1,3,5,4,0,6],[0,6,2,3,4,5,1],[4,6,2,3,0,5,1],[0,1,5,3,4,2,6],[0,6,2,3,4,5,1],[5,1,0,2,4,3,6]]"

@[implicit_reducible]
def «Order3 M608^op» : Magma (Fin 7) where
  op := finOpTable "[[0,2,0,4,0,0,5],[6,1,6,6,1,6,1],[2,3,2,2,5,2,0],[3,5,3,3,3,3,2],[4,4,4,0,4,4,4],[5,0,5,5,2,5,3],[1,6,1,1,6,1,6]]"

@[implicit_reducible]
def «Order3 M610» : Magma (Fin 6) where
  op := finOpTable "[[0,1,2,3,4,5],[2,1,3,0,4,5],[0,1,2,3,4,5],[0,1,2,3,4,5],[0,1,2,3,4,5],[0,3,2,4,1,5]]"

@[implicit_reducible]
def «Order3 M610^op» : Magma (Fin 6) where
  op := finOpTable "[[0,2,0,0,0,0],[1,1,1,1,1,3],[2,3,2,2,2,2],[3,0,3,3,3,4],[4,4,4,4,4,1],[5,5,5,5,5,5]]"

@[implicit_reducible]
def «Order3 M612» : Magma (Fin 7) where
  op := finOpTable "[[0,1,2,3,5,6,4],[2,1,3,0,4,5,6],[0,1,2,3,4,5,6],[0,1,2,3,4,5,6],[0,1,2,3,4,5,6],[0,1,2,3,4,5,6],[0,1,2,3,4,5,6]]"

@[implicit_reducible]
def «Order3 M612^op» : Magma (Fin 7) where
  op := finOpTable "[[0,2,0,0,0,0,0],[1,1,1,1,1,1,1],[2,3,2,2,2,2,2],[3,0,3,3,3,3,3],[5,4,4,4,4,4,4],[6,5,5,5,5,5,5],[4,6,6,6,6,6,6]]"

@[implicit_reducible]
def «Order3 M614» : Magma (Fin 8) where
  op := finOpTable "[[0,1,2,3,4,5,6,7],[7,1,2,4,6,0,3,5],[3,1,2,5,4,0,6,7],[0,1,2,3,4,5,6,7],[5,1,2,3,4,7,6,0],[0,1,2,3,4,5,6,7],[5,1,2,3,4,7,6,0],[0,1,2,3,4,5,6,7]]"

@[implicit_reducible]
def «Order3 M614^op» : Magma (Fin 8) where
  op := finOpTable "[[0,7,3,0,5,0,5,0],[1,1,1,1,1,1,1,1],[2,2,2,2,2,2,2,2],[3,4,5,3,3,3,3,3],[4,6,4,4,4,4,4,4],[5,0,0,5,7,5,7,5],[6,3,6,6,6,6,6,6],[7,5,7,7,0,7,0,7]]"

@[implicit_reducible]
def «Order3 M616» : Magma (Fin 12) where
  op := finOpTable "[[0,6,2,7,4,1,5,9,8,3,10,11],[2,1,8,3,4,5,6,7,0,9,10,11],[0,3,2,6,4,5,1,7,8,9,10,11],[4,1,10,3,11,5,6,7,2,9,8,0],[0,1,2,6,4,5,7,3,8,9,10,11],[8,1,2,3,4,5,6,7,10,9,0,11],[10,1,0,3,8,5,6,7,11,9,2,4],[8,1,2,3,0,5,6,7,4,9,10,11],[0,5,2,1,4,3,9,6,8,7,10,11],[11,1,2,3,4,5,6,7,0,9,10,8],[0,1,2,5,4,6,3,7,8,9,10,11],[0,1,2,9,4,5,3,7,8,6,10,11]]"

@[implicit_reducible]
def «Order3 M616^op» : Magma (Fin 12) where
  op := finOpTable "[[0,2,0,4,0,8,10,8,0,11,0,0],[6,1,3,1,1,1,1,1,5,1,1,1],[2,8,2,10,2,2,0,2,2,2,2,2],[7,3,6,3,6,3,3,3,1,3,5,9],[4,4,4,11,4,4,8,0,4,4,4,4],[1,5,5,5,5,5,5,5,3,5,6,5],[5,6,1,6,7,6,6,6,9,6,3,3],[9,7,7,7,3,7,7,7,6,7,7,7],[8,0,8,2,8,10,11,4,8,0,8,8],[3,9,9,9,9,9,9,9,7,9,9,6],[10,10,10,8,10,0,2,10,10,10,10,10],[11,11,11,0,11,11,4,11,11,8,11,11]]"

@[implicit_reducible]
def «Order3 M618» : Magma (Fin 12) where
  op := finOpTable "[[0,9,1,3,8,5,6,4,7,2,10,11],[5,1,2,4,7,6,0,3,8,9,10,11],[3,1,2,5,6,0,7,4,8,9,10,11],[0,11,9,3,4,5,6,7,2,8,1,10],[5,10,1,3,4,11,6,7,8,9,2,0],[0,2,8,3,7,5,6,9,1,4,10,11],[0,8,10,3,4,5,6,7,9,1,11,2],[10,2,11,3,4,0,6,7,8,9,5,1],[11,1,2,6,4,3,5,7,8,9,0,10],[6,1,2,0,4,10,3,7,8,9,11,5],[0,1,2,6,3,5,4,8,9,7,10,11],[0,1,2,7,9,5,3,6,4,8,10,11]]"

@[implicit_reducible]
def «Order3 M618^op» : Magma (Fin 12) where
  op := finOpTable "[[0,5,3,0,5,0,0,10,11,6,0,0],[9,1,1,11,10,2,8,2,1,1,1,1],[1,2,2,9,1,8,10,11,2,2,2,2],[3,4,5,3,3,3,3,3,6,0,6,7],[8,7,6,4,4,7,4,4,4,4,3,9],[5,6,0,5,11,5,5,0,3,10,5,5],[6,0,7,6,6,6,6,6,5,3,4,3],[4,3,4,7,7,9,7,7,7,7,8,6],[7,8,8,2,8,1,9,8,8,8,9,4],[2,9,9,8,9,4,1,9,9,9,7,8],[10,10,10,1,2,10,11,5,0,11,10,10],[11,11,11,10,0,11,2,1,10,5,11,11]]"

@[implicit_reducible]
def «Order3 M620» : Magma (Fin 5) where
  op := finOpTable "[[0,4,3,0,0],[1,1,4,1,3],[2,2,2,2,2],[3,3,0,3,1],[4,0,1,4,4]]"

@[implicit_reducible]
def «Order3 M620^op» : Magma (Fin 5) where
  op := finOpTable "[[0,1,2,3,4],[4,1,2,3,0],[3,4,2,0,1],[0,1,2,3,4],[0,3,2,1,4]]"

@[implicit_reducible]
def «Order3 M622» : Magma (Fin 7) where
  op := finOpTable "[[0,2,3,4,0,0,0],[1,1,1,1,1,6,1],[5,0,2,2,5,2,5],[6,5,0,3,3,3,3],[4,4,6,0,4,4,4],[2,3,5,5,2,5,2],[3,6,4,6,6,1,6]]"

@[implicit_reducible]
def «Order3 M622^op» : Magma (Fin 7) where
  op := finOpTable "[[0,1,5,6,4,2,3],[2,1,0,5,4,3,6],[3,1,2,0,6,5,4],[4,1,2,3,0,5,6],[0,1,5,3,4,2,6],[0,6,2,3,4,5,1],[0,1,5,3,4,2,6]]"

@[implicit_reducible]
def «Order3 M624» : Magma (Fin 6) where
  op := finOpTable "[[0,2,2,5,4,5],[4,1,3,3,4,5],[0,5,2,3,0,5],[4,1,2,3,4,1],[0,1,1,3,4,3],[0,1,2,2,0,5]]"

@[implicit_reducible]
def «Order3 M624^op» : Magma (Fin 6) where
  op := finOpTable "[[0,4,0,4,0,0],[2,1,5,1,1,1],[2,3,2,2,1,2],[5,3,3,3,3,2],[4,4,0,4,4,0],[5,5,5,1,3,5]]"

@[implicit_reducible]
def «Order3 M626» : Magma (Fin 6) where
  op := finOpTable "[[0,1,3,3,0,1],[0,1,0,3,1,1],[4,5,2,2,4,5],[0,1,3,3,0,3],[4,4,2,2,4,5],[2,5,2,5,4,5]]"

@[implicit_reducible]
def «Order3 M626^op» : Magma (Fin 6) where
  op := finOpTable "[[0,0,4,0,4,2],[1,1,5,1,4,5],[3,0,2,3,2,2],[3,3,2,3,2,5],[0,1,4,0,4,4],[1,1,5,3,5,5]]"

@[implicit_reducible]
def «Order3 M628» : Magma (Fin 16) where
  op := finOpTable "[[2,7,5,3,9,0,12,11,4,8,6,1,10,14,15,13],[4,14,11,13,15,12,5,3,2,9,1,8,6,7,10,0],[3,6,0,2,1,5,4,13,12,15,7,9,14,10,8,11],[0,15,3,5,14,2,13,4,11,6,8,10,1,9,7,12],[6,5,8,15,13,7,14,1,10,3,2,11,4,12,0,9],[5,8,2,0,10,3,11,12,13,7,15,14,9,1,6,4],[1,13,10,14,5,9,15,7,6,4,11,2,3,0,12,8],[10,12,1,9,0,14,6,8,15,11,4,3,2,5,13,7],[14,4,9,1,3,10,8,6,7,13,12,0,5,2,11,15],[11,1,4,12,7,13,0,2,3,10,14,6,8,15,9,5],[13,10,12,4,6,11,3,5,0,1,9,7,15,8,14,2],[15,3,7,6,4,8,1,14,9,5,0,12,13,11,2,10],[8,0,6,7,12,15,9,10,1,2,3,4,11,13,5,14],[7,2,15,8,11,6,10,9,14,0,5,13,12,4,3,1],[12,9,13,11,8,4,2,0,5,14,10,15,7,6,1,3],[9,11,14,10,2,1,7,15,8,12,13,5,0,3,4,6]]"

@[implicit_reducible]
def «Order3 M629» : Magma (Fin 16) where
  op := finOpTable "[[0,2,4,2,10,4,0,0,10,0,1,1,0,0,0,0],[3,1,3,6,1,1,11,6,1,1,0,0,11,1,1,1],[5,0,2,0,5,14,2,2,2,14,2,2,2,2,3,3],[1,7,1,3,3,3,7,15,3,3,3,3,3,15,2,2],[8,4,0,4,4,0,12,4,12,4,8,4,5,5,4,4],[2,5,9,5,2,5,5,13,5,13,5,5,4,4,9,5],[6,12,6,1,8,6,6,1,7,7,6,12,8,6,6,6],[7,3,7,13,7,9,3,7,6,6,7,7,7,9,7,13],[4,8,8,8,6,8,9,9,8,10,4,8,6,8,10,8],[9,9,5,9,9,7,8,8,14,9,14,9,9,7,5,9],[11,11,10,10,0,10,10,10,0,8,10,14,10,10,8,14],[10,10,11,11,11,11,1,11,11,11,15,11,1,12,15,12],[12,6,12,12,13,13,4,12,4,12,12,6,12,11,12,11],[13,13,13,7,12,12,13,5,13,5,13,15,15,13,13,7],[14,14,15,15,14,2,14,14,9,2,9,10,14,14,14,10],[15,15,14,14,15,15,15,3,15,15,11,13,13,3,11,15]]"

@[implicit_reducible]
def «Order3 M629^op» : Magma (Fin 16) where
  op := finOpTable "[[0,3,5,1,8,2,6,7,4,9,11,10,12,13,14,15],[2,1,0,7,4,5,12,3,8,9,11,10,6,13,14,15],[4,3,2,1,0,9,6,7,8,5,10,11,12,13,15,14],[2,6,0,3,4,5,1,13,8,9,10,11,12,7,15,14],[10,1,5,3,4,2,8,7,6,9,0,11,13,12,14,15],[4,1,14,3,0,5,6,9,8,7,10,11,13,12,2,15],[0,11,2,7,12,5,6,3,9,8,10,1,4,13,14,15],[0,6,2,15,4,13,1,7,9,8,10,11,12,5,14,3],[10,1,2,3,12,5,7,6,8,14,0,11,4,13,9,15],[0,1,14,3,4,13,7,6,10,9,8,11,12,5,2,15],[1,0,2,3,8,5,6,7,4,14,10,15,12,13,9,11],[1,0,2,3,4,5,12,7,8,9,14,11,6,15,10,13],[0,11,2,3,5,4,8,7,6,9,10,1,12,15,14,13],[0,1,2,15,5,4,6,9,8,7,10,12,11,13,14,3],[0,1,3,2,4,9,6,7,10,5,8,15,12,13,14,11],[0,1,3,2,4,5,6,13,8,9,14,12,11,7,10,15]]"

@[implicit_reducible]
def «Order3 M631» : Magma (Fin 16) where
  op := finOpTable "[[0,2,4,9,10,12,0,5,15,8,1,0,13,7,0,3],[3,1,14,6,1,7,13,8,10,1,5,2,11,0,12,1],[5,8,2,0,14,11,4,2,9,13,2,3,2,1,15,6],[12,7,1,3,6,3,9,15,3,11,0,4,14,3,10,2],[8,4,13,2,4,0,5,11,6,4,14,10,3,12,7,4],[15,0,9,5,2,5,10,4,5,7,11,12,6,5,1,14],[6,12,3,10,7,15,6,1,2,5,8,6,4,9,6,13],[1,11,7,14,13,6,3,7,4,0,7,9,7,15,5,8],[7,6,0,8,12,8,15,14,8,10,4,1,9,8,2,11],[2,9,6,7,9,14,12,13,11,9,3,5,0,10,8,9],[13,14,10,15,3,4,1,10,0,6,10,8,10,11,9,5],[11,13,15,12,5,1,11,3,7,2,9,11,8,4,11,10],[4,5,12,1,11,9,8,12,14,3,12,15,12,6,13,0],[9,10,11,13,0,13,2,6,13,14,15,7,1,13,4,12],[14,3,5,4,8,10,14,9,1,12,13,14,15,2,14,7],[10,15,8,11,15,2,7,0,12,15,6,13,5,14,3,15]]"

@[implicit_reducible]
def «Order3 M631^op» : Magma (Fin 16) where
  op := finOpTable "[[0,3,5,12,8,15,6,1,7,2,13,11,4,9,14,10],[2,1,8,7,4,0,12,11,6,9,14,13,5,10,3,15],[4,14,2,1,13,9,3,7,0,6,10,15,12,11,5,8],[9,6,0,3,2,5,10,14,8,7,15,12,1,13,4,11],[10,1,14,6,4,2,7,13,12,9,3,5,11,0,8,15],[12,7,11,3,0,5,15,6,8,14,4,1,9,13,10,2],[0,13,4,9,5,10,6,3,15,12,1,11,8,2,14,7],[5,8,2,15,11,4,1,7,14,13,10,3,12,6,9,0],[15,10,9,3,6,5,2,4,8,11,0,7,14,13,1,12],[8,1,13,11,4,7,5,0,10,9,6,2,3,14,12,15],[1,5,2,0,14,11,8,7,4,3,10,9,12,15,13,6],[0,2,3,4,10,12,6,9,1,5,8,11,15,7,14,13],[13,11,2,14,3,6,4,7,9,0,10,8,12,1,15,5],[7,0,1,3,12,5,9,15,8,10,11,4,6,13,2,14],[0,12,15,10,7,1,6,5,2,8,9,11,13,4,14,3],[3,1,6,2,4,14,13,8,11,9,5,10,0,12,7,15]]"

@[implicit_reducible]
def «Order3 M633» : Magma (Fin 19) where
  op := finOpTable "[[0,13,7,1,14,8,2,15,9,3,16,10,4,17,11,5,18,12,6],[7,1,14,8,2,15,9,3,16,10,4,17,11,5,18,12,6,0,13],[14,8,2,15,9,3,16,10,4,17,11,5,18,12,6,0,13,7,1],[2,15,9,3,16,10,4,17,11,5,18,12,6,0,13,7,1,14,8],[9,3,16,10,4,17,11,5,18,12,6,0,13,7,1,14,8,2,15],[16,10,4,17,11,5,18,12,6,0,13,7,1,14,8,2,15,9,3],[4,17,11,5,18,12,6,0,13,7,1,14,8,2,15,9,3,16,10],[11,5,18,12,6,0,13,7,1,14,8,2,15,9,3,16,10,4,17],[18,12,6,0,13,7,1,14,8,2,15,9,3,16,10,4,17,11,5],[6,0,13,7,1,14,8,2,15,9,3,16,10,4,17,11,5,18,12],[13,7,1,14,8,2,15,9,3,16,10,4,17,11,5,18,12,6,0],[1,14,8,2,15,9,3,16,10,4,17,11,5,18,12,6,0,13,7],[8,2,15,9,3,16,10,4,17,11,5,18,12,6,0,13,7,1,14],[15,9,3,16,10,4,17,11,5,18,12,6,0,13,7,1,14,8,2],[3,16,10,4,17,11,5,18,12,6,0,13,7,1,14,8,2,15,9],[10,4,17,11,5,18,12,6,0,13,7,1,14,8,2,15,9,3,16],[17,11,5,18,12,6,0,13,7,1,14,8,2,15,9,3,16,10,4],[5,18,12,6,0,13,7,1,14,8,2,15,9,3,16,10,4,17,11],[12,6,0,13,7,1,14,8,2,15,9,3,16,10,4,17,11,5,18]]"

@[implicit_reducible]
def «Order3 M633^op» : Magma (Fin 19) where
  op := finOpTable "[[0,7,14,2,9,16,4,11,18,6,13,1,8,15,3,10,17,5,12],[13,1,8,15,3,10,17,5,12,0,7,14,2,9,16,4,11,18,6],[7,14,2,9,16,4,11,18,6,13,1,8,15,3,10,17,5,12,0],[1,8,15,3,10,17,5,12,0,7,14,2,9,16,4,11,18,6,13],[14,2,9,16,4,11,18,6,13,1,8,15,3,10,17,5,12,0,7],[8,15,3,10,17,5,12,0,7,14,2,9,16,4,11,18,6,13,1],[2,9,16,4,11,18,6,13,1,8,15,3,10,17,5,12,0,7,14],[15,3,10,17,5,12,0,7,14,2,9,16,4,11,18,6,13,1,8],[9,16,4,11,18,6,13,1,8,15,3,10,17,5,12,0,7,14,2],[3,10,17,5,12,0,7,14,2,9,16,4,11,18,6,13,1,8,15],[16,4,11,18,6,13,1,8,15,3,10,17,5,12,0,7,14,2,9],[10,17,5,12,0,7,14,2,9,16,4,11,18,6,13,1,8,15,3],[4,11,18,6,13,1,8,15,3,10,17,5,12,0,7,14,2,9,16],[17,5,12,0,7,14,2,9,16,4,11,18,6,13,1,8,15,3,10],[11,18,6,13,1,8,15,3,10,17,5,12,0,7,14,2,9,16,4],[5,12,0,7,14,2,9,16,4,11,18,6,13,1,8,15,3,10,17],[18,6,13,1,8,15,3,10,17,5,12,0,7,14,2,9,16,4,11],[12,0,7,14,2,9,16,4,11,18,6,13,1,8,15,3,10,17,5],[6,13,1,8,15,3,10,17,5,12,0,7,14,2,9,16,4,11,18]]"

@[implicit_reducible]
def «Order3 M635» : Magma (Fin 16) where
  op := finOpTable "[[0,7,1,11,14,10,5,6,12,3,2,13,9,8,15,4],[2,5,3,4,13,11,7,9,14,8,0,1,12,15,6,10],[10,14,6,15,7,0,13,1,5,9,11,8,4,2,3,12],[9,13,12,8,5,2,14,3,7,4,10,15,0,11,1,6],[15,8,11,13,4,3,12,2,9,5,6,10,7,1,0,14],[6,12,10,14,9,1,8,0,4,15,13,11,5,3,2,7],[7,0,9,1,10,14,2,12,15,6,5,4,3,13,8,11],[1,15,0,7,12,6,4,10,8,11,3,2,14,5,13,9],[13,6,14,10,1,9,11,7,3,12,8,0,15,4,5,2],[12,4,2,5,8,7,9,14,0,13,15,3,10,6,11,1],[5,2,4,3,11,15,0,8,10,1,7,14,6,12,9,13],[3,11,15,6,2,5,10,4,13,0,9,12,1,14,7,8],[8,1,7,9,6,12,15,13,2,14,4,5,11,0,10,3],[11,10,13,0,3,4,6,15,1,2,14,7,8,9,12,5],[4,3,5,2,15,8,1,11,6,10,12,9,13,7,14,0],[14,9,8,12,0,13,3,5,11,7,1,6,2,10,4,15]]"

@[implicit_reducible]
def «Order3 M636» : Magma (Fin 18) where
  op := finOpTable "[[0,2,4,6,5,1,8,3,7,0,0,0,0,0,0,0,0,0],[2,3,5,3,0,4,9,10,11,15,16,17,6,7,8,12,13,14],[4,5,2,9,1,0,2,2,2,10,11,3,2,2,2,2,2,2],[6,1,9,1,12,15,7,8,0,11,2,10,14,4,13,17,5,16],[5,0,1,12,4,2,4,4,4,4,4,4,13,14,3,4,4,4],[1,4,0,15,2,5,5,5,5,5,5,5,5,5,5,16,17,3],[8,9,6,7,6,6,6,0,3,12,6,6,15,6,6,1,6,6],[3,10,7,8,7,7,0,7,6,7,13,7,7,16,7,7,1,7],[7,11,8,0,8,8,3,6,8,8,8,14,8,8,17,8,8,1],[9,15,10,11,9,9,12,9,9,9,3,2,1,9,9,6,9,9],[10,16,11,2,10,10,10,13,10,3,10,9,10,1,10,10,7,10],[11,17,3,10,11,11,11,11,14,2,9,11,11,11,1,11,11,8],[12,6,12,14,13,12,15,12,12,1,12,12,12,3,4,9,12,12],[13,7,13,4,14,13,13,16,13,13,1,13,3,13,12,13,10,13],[14,8,14,13,3,14,14,14,17,14,14,1,4,12,14,14,14,11],[15,12,15,17,15,16,1,15,15,6,15,15,9,15,15,15,3,5],[16,13,16,5,16,17,16,1,16,16,7,16,16,10,16,3,16,15],[17,14,17,16,17,3,17,17,1,17,17,8,17,17,11,5,15,17]]"

@[implicit_reducible]
def «Order3 M636^op» : Magma (Fin 18) where
  op := finOpTable "[[0,2,4,6,5,1,8,3,7,9,10,11,12,13,14,15,16,17],[2,3,5,1,0,4,9,10,11,15,16,17,6,7,8,12,13,14],[4,5,2,9,1,0,6,7,8,10,11,3,12,13,14,15,16,17],[6,3,9,1,12,15,7,8,0,11,2,10,14,4,13,17,5,16],[5,0,1,12,4,2,6,7,8,9,10,11,13,14,3,15,16,17],[1,4,0,15,2,5,6,7,8,9,10,11,12,13,14,16,17,3],[8,9,2,7,4,5,6,0,3,12,10,11,15,13,14,1,16,17],[3,10,2,8,4,5,0,7,6,9,13,11,12,16,14,15,1,17],[7,11,2,0,4,5,3,6,8,9,10,14,12,13,17,15,16,1],[0,15,10,11,4,5,12,7,8,9,3,2,1,13,14,6,16,17],[0,16,11,2,4,5,6,13,8,3,10,9,12,1,14,15,7,17],[0,17,3,10,4,5,6,7,14,2,9,11,12,13,1,15,16,8],[0,6,2,14,13,5,15,7,8,1,10,11,12,3,4,9,16,17],[0,7,2,4,14,5,6,16,8,9,1,11,3,13,12,15,10,17],[0,8,2,13,3,5,6,7,17,9,10,1,4,12,14,15,16,11],[0,12,2,17,4,16,1,7,8,6,10,11,9,13,14,15,3,5],[0,13,2,5,4,17,6,1,8,9,7,11,12,10,14,3,16,15],[0,14,2,16,4,3,6,7,1,9,10,8,12,13,11,5,15,17]]"

@[implicit_reducible]
def «Order3 M638» : Magma (Fin 33) where
  op := finOpTable "[[2,5,3,0,9,6,17,14,16,12,21,22,23,20,1,32,19,7,25,30,29,4,15,10,26,8,11,31,27,13,18,28,24],[7,4,6,1,3,15,11,9,21,28,31,27,29,25,32,0,17,18,16,26,30,2,23,24,22,10,13,8,5,14,12,19,20],[3,8,0,2,11,16,19,18,7,22,24,10,15,29,25,4,14,30,6,1,13,26,21,32,12,17,23,28,31,20,5,27,9],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32],[10,3,12,4,1,13,29,31,20,19,5,14,8,9,2,25,18,16,17,0,11,30,24,22,23,28,7,32,26,21,27,15,6],[14,9,17,5,0,11,4,19,24,27,29,3,25,6,22,20,26,10,15,32,1,12,13,31,28,21,2,18,30,16,23,8,7],[1,21,7,6,27,22,10,24,14,26,3,0,13,18,30,9,12,11,32,23,19,31,29,2,20,4,15,5,16,25,8,17,28],[6,15,1,7,28,19,23,12,22,2,20,32,3,14,24,29,10,26,9,25,17,11,31,13,0,5,27,16,8,18,4,30,21],[18,11,19,8,2,23,14,4,9,3,30,28,31,1,26,10,32,21,12,22,7,13,20,27,29,24,6,25,17,5,15,16,0],[21,0,23,9,5,20,26,29,3,8,15,18,1,32,6,30,28,31,13,27,24,16,25,7,19,2,14,4,12,22,10,11,17],[12,13,4,10,19,2,3,27,30,15,6,16,17,11,8,26,31,28,0,29,22,18,7,25,5,20,9,23,21,24,14,32,1],[24,2,15,11,8,3,31,32,13,17,1,5,21,23,28,16,27,20,29,7,26,25,30,14,6,12,18,10,4,9,0,22,19],[4,20,10,12,14,25,28,3,0,16,18,21,7,22,31,17,29,2,27,5,9,32,6,8,30,19,1,15,24,26,13,23,11],[20,19,29,13,10,14,16,6,17,11,32,4,24,27,18,21,5,25,7,8,31,22,26,9,15,30,12,3,2,28,1,0,23],[17,12,5,14,20,4,30,23,26,6,8,13,0,16,15,3,21,32,11,24,25,28,2,29,27,22,10,7,18,19,9,1,31],[11,28,24,15,7,27,9,2,10,30,26,1,18,12,3,14,0,13,31,20,23,17,19,5,25,29,8,22,32,4,6,21,16],[25,17,30,16,18,10,32,26,12,0,13,2,20,7,11,28,22,23,24,9,6,27,3,1,4,15,31,14,19,8,21,5,29],[5,18,14,17,16,26,21,10,11,13,0,29,27,19,12,31,23,24,22,15,8,20,1,4,3,9,28,30,7,6,32,25,2],[19,16,8,18,17,9,12,15,32,31,28,20,2,5,21,13,24,22,23,10,14,29,4,3,1,26,0,6,25,30,11,7,27],[8,10,18,19,13,32,24,25,4,20,2,7,5,30,23,27,15,9,26,21,16,3,0,28,31,11,29,17,6,1,22,14,12],[29,14,13,20,12,18,7,16,19,4,23,9,26,31,5,22,8,6,30,17,28,15,32,21,11,1,24,0,3,27,25,2,10],[23,27,9,21,6,12,0,11,28,1,17,25,32,24,13,18,2,29,20,3,10,19,14,30,8,7,16,26,22,15,31,4,5],[26,23,32,22,24,0,27,28,2,7,25,6,30,15,20,5,3,1,4,13,21,8,16,17,18,31,19,12,10,11,29,9,14],[9,24,21,23,22,28,20,0,29,25,7,8,14,10,27,19,1,4,3,31,32,6,17,18,16,13,5,11,15,12,2,26,30],[15,22,11,24,23,31,2,13,27,5,19,30,6,26,29,7,4,3,1,28,12,14,18,16,17,0,25,21,9,32,20,10,8],[30,26,16,25,31,21,22,5,23,29,27,12,19,8,4,2,9,15,10,11,18,7,28,0,13,32,20,1,14,17,24,6,3],[32,31,22,26,25,29,15,20,6,14,9,17,16,21,10,8,13,0,28,2,4,1,5,19,7,27,30,24,11,23,3,12,18],[31,6,28,27,21,1,25,17,5,24,22,15,10,3,19,23,30,14,8,16,0,9,11,12,32,18,4,13,29,2,7,20,26],[27,7,31,28,15,8,18,30,1,21,12,23,22,2,16,11,25,5,19,14,3,24,9,26,10,6,32,29,20,0,17,13,4],[13,30,20,29,32,17,5,1,25,23,4,26,9,28,7,24,6,8,14,18,27,10,12,11,21,16,22,2,0,31,19,3,15],[16,32,25,30,29,24,8,22,15,10,14,31,28,17,9,6,11,12,21,4,5,0,27,20,2,23,3,19,1,7,26,18,13],[28,25,27,31,26,30,1,8,18,32,11,24,4,0,17,12,7,19,5,6,2,23,10,15,9,14,21,20,13,3,16,29,22],[22,29,26,32,30,7,13,21,31,18,16,19,11,4,0,1,20,27,2,12,15,5,8,6,14,3,17,9,23,10,28,24,25]]"

@[implicit_reducible]
def «Order3 M638^op» : Magma (Fin 33) where
  op := finOpTable "[[2,7,3,0,10,14,1,6,18,21,12,24,4,20,17,11,25,5,19,8,29,23,26,9,15,30,32,31,27,13,16,28,22],[5,4,8,1,3,9,21,15,11,0,13,2,20,19,12,28,17,18,16,10,14,27,23,24,22,26,31,6,7,30,32,25,29],[3,6,0,2,12,17,7,1,19,23,4,15,10,29,5,24,30,14,8,18,13,9,32,21,11,16,22,28,31,20,25,27,26],[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32],[9,3,11,4,1,0,27,28,2,5,19,8,14,10,20,7,18,16,17,13,12,6,24,22,23,31,25,21,15,32,29,26,30],[6,15,16,5,13,11,22,19,23,20,2,3,25,14,4,27,10,26,9,32,18,12,0,28,31,21,29,1,8,17,24,30,7],[17,11,19,6,29,4,10,23,14,26,3,31,28,16,30,9,32,21,12,24,7,0,27,20,2,22,15,25,18,5,8,1,13],[14,9,18,7,31,19,24,12,4,29,27,32,3,6,23,2,26,10,15,25,16,11,28,0,13,5,20,17,30,1,22,8,21],[16,21,7,8,20,24,14,22,9,3,30,13,0,17,26,10,12,11,32,4,19,28,2,29,27,23,6,5,1,25,15,18,31],[12,28,22,9,19,27,26,2,3,8,15,17,16,11,6,30,0,13,31,20,4,1,7,25,5,29,14,24,21,23,10,32,18],[21,31,24,10,5,29,3,20,30,15,6,1,18,32,8,26,13,0,28,2,23,17,25,7,19,27,9,22,12,4,14,11,16],[22,27,10,11,14,3,0,32,28,18,16,5,21,4,13,1,2,29,20,7,9,25,6,8,30,12,17,15,23,26,31,24,19],[23,29,15,12,8,25,13,3,31,1,17,21,7,24,0,18,20,27,2,5,26,32,30,14,6,19,16,10,22,9,28,4,11],[20,25,29,13,9,6,18,14,1,32,11,23,22,27,16,12,7,19,5,30,31,24,15,10,26,8,21,3,2,28,17,0,4],[1,32,25,14,2,22,30,24,26,6,8,28,31,18,15,3,11,12,21,23,5,13,20,27,29,4,10,19,16,7,9,17,0],[32,0,4,15,25,20,9,29,10,30,26,16,17,21,3,14,28,31,13,27,22,18,5,19,7,2,8,23,11,24,6,12,1],[19,17,14,16,18,26,12,10,32,28,31,27,29,5,21,0,22,23,24,15,8,2,3,1,4,9,13,30,25,6,11,7,20],[7,18,30,17,16,10,11,26,21,31,28,20,2,25,32,13,23,24,22,9,6,29,1,4,3,15,0,14,5,8,12,19,27],[25,16,6,18,17,15,32,9,12,13,0,29,27,7,11,31,24,22,23,26,30,20,4,3,1,10,28,8,19,14,21,5,2],[30,26,1,19,0,32,23,25,22,27,29,7,5,8,24,20,9,15,10,21,17,3,13,31,28,11,2,16,14,18,4,6,12],[29,30,13,20,11,1,19,17,7,24,22,26,9,31,25,23,6,8,14,16,28,10,21,32,12,18,4,0,3,27,5,2,15],[4,2,26,21,30,12,31,11,13,16,18,25,32,22,28,17,27,20,29,3,15,19,8,6,14,7,1,9,24,10,0,23,5],[15,23,21,22,24,13,29,31,20,25,7,30,6,26,2,19,3,1,4,0,32,14,16,17,18,28,5,11,9,12,27,10,8],[10,24,32,23,22,31,2,13,27,7,25,14,8,9,29,5,1,4,3,28,21,30,17,18,16,0,19,12,26,11,20,15,6],[26,22,12,24,23,28,20,0,29,19,5,6,30,15,27,25,4,3,1,31,11,8,18,16,17,13,7,32,10,21,2,9,14],[8,10,17,25,28,21,4,5,24,2,20,12,19,30,22,29,15,9,26,11,1,7,31,13,0,32,27,18,6,16,23,14,3],[11,13,23,26,7,2,15,27,6,14,9,18,1,12,10,8,31,28,0,29,24,16,19,5,25,20,30,4,32,22,3,21,17],[31,8,28,27,32,18,5,16,25,4,23,10,15,3,7,22,14,30,6,17,0,26,12,11,21,1,24,13,29,2,19,20,9],[27,5,31,28,26,30,16,8,17,12,21,4,24,2,18,32,19,7,25,6,3,22,10,15,9,14,11,29,20,0,1,13,23],[13,14,20,29,21,16,25,18,5,22,24,9,26,28,19,4,8,6,30,1,27,15,11,12,32,17,23,2,0,31,7,3,10],[18,12,5,30,27,23,8,4,15,10,14,0,13,1,9,6,21,32,11,22,25,31,29,2,20,24,3,7,17,19,26,16,28],[28,19,27,31,15,8,17,30,16,11,32,22,23,0,1,21,5,25,7,14,2,4,9,26,10,6,12,20,13,3,18,29,24],[24,20,9,32,6,7,28,21,0,17,1,19,11,23,31,16,29,2,27,12,10,5,14,30,8,3,18,26,4,15,13,22,25]]"

@[implicit_reducible]
def «Order3 M639» : Magma (Fin 16) where
  op := finOpTable "[[0,2,4,9,1,5,10,3,6,7,8,11,12,13,14,15],[6,1,5,3,2,4,8,14,0,15,10,7,12,9,11,13],[3,4,2,7,5,1,11,0,8,9,13,12,6,15,14,10],[7,1,5,3,2,4,14,9,11,0,10,13,12,8,15,6],[8,5,1,15,4,2,6,7,10,12,0,9,11,13,3,14],[0,2,4,8,1,5,12,10,13,6,14,11,9,3,7,15],[8,5,1,15,4,2,6,7,10,12,0,9,11,13,3,14],[9,5,1,0,4,2,6,7,8,3,11,14,12,13,10,15],[10,4,2,13,5,1,0,7,8,9,6,3,12,11,14,15],[3,4,2,7,5,1,11,0,8,9,13,12,6,15,14,10],[6,1,5,3,2,4,8,14,0,15,10,7,12,9,11,13],[0,2,4,8,1,5,12,10,13,6,14,11,9,3,7,15],[0,1,5,3,2,4,9,7,8,11,10,6,12,13,14,15],[0,5,1,11,4,2,6,7,3,10,15,8,12,13,14,9],[0,4,2,6,5,1,15,11,8,9,7,10,12,13,14,3],[0,2,4,14,1,5,3,7,8,13,9,11,12,10,6,15]]"

@[implicit_reducible]
def «Order3 M639^op» : Magma (Fin 16) where
  op := finOpTable "[[0,6,3,7,8,0,8,9,10,3,6,0,0,0,0,0],[2,1,4,1,5,2,5,5,4,4,1,2,1,5,4,2],[4,5,2,5,1,4,1,1,2,2,5,4,5,1,2,4],[9,3,7,3,15,8,15,0,13,7,3,8,3,11,6,14],[1,2,5,2,4,1,4,4,5,5,2,1,2,4,5,1],[5,4,1,4,2,5,2,2,1,1,4,5,4,2,1,5],[10,8,11,14,6,12,6,6,0,11,8,12,9,6,15,3],[3,14,0,9,7,10,7,7,7,0,14,10,7,7,11,7],[6,0,8,11,10,13,10,8,8,8,0,13,8,3,8,8],[7,15,9,0,12,6,12,3,9,9,15,6,11,10,9,13],[8,10,13,10,0,14,0,11,6,13,10,14,10,15,7,9],[11,7,12,13,9,11,9,14,3,12,7,11,6,8,10,11],[12,12,6,12,11,9,11,12,12,6,12,9,12,12,12,12],[13,9,15,8,13,3,13,13,11,15,9,3,13,13,13,10],[14,11,14,15,3,7,3,10,14,14,11,7,14,14,14,6],[15,13,10,6,14,15,14,15,15,10,13,15,15,9,3,15]]"

@[implicit_reducible]
def «Order3 M640» : Magma (Fin 17) where
  op := finOpTable "[[0,2,8,0,2,8,0,0,15,0,4,0,0,0,15,4,0],[4,1,4,4,7,1,7,12,1,12,1,1,2,1,1,1,2],[5,3,2,5,3,16,2,2,5,2,2,2,1,16,2,2,1],[3,2,8,3,2,8,3,3,15,3,4,3,3,3,15,4,3],[1,6,1,1,4,4,10,6,4,4,0,10,4,4,4,0,4],[2,5,13,2,5,5,8,8,2,5,5,6,5,6,5,5,13],[6,4,6,6,11,7,6,4,7,6,11,5,6,5,6,6,6],[7,9,7,7,1,6,1,7,6,8,7,7,9,7,8,7,7],[14,8,0,14,8,0,5,5,8,7,8,8,8,8,7,14,8],[9,7,9,9,9,9,9,14,14,9,12,12,7,11,11,9,9],[15,10,10,15,15,10,4,10,10,11,10,4,11,10,10,12,12],[11,11,11,11,6,13,13,11,11,10,6,11,10,9,9,11,11],[12,16,16,12,12,12,12,1,12,1,9,9,12,12,12,10,10],[13,13,5,13,13,11,11,13,13,14,13,14,13,13,16,16,5],[8,14,14,8,14,14,14,9,9,13,14,13,14,15,14,8,15],[10,15,15,10,10,15,15,15,0,15,16,15,16,14,0,15,14],[16,12,12,16,16,2,16,16,16,16,15,16,15,2,13,13,16]]"

@[implicit_reducible]
def «Order3 M640^op» : Magma (Fin 17) where
  op := finOpTable "[[0,4,5,3,1,2,6,7,14,9,15,11,12,13,8,10,16],[2,1,3,2,6,5,4,9,8,7,10,11,16,13,14,15,12],[8,4,2,8,1,13,6,7,0,9,10,11,16,5,14,15,12],[0,4,5,3,1,2,6,7,14,9,15,11,12,13,8,10,16],[2,7,3,2,4,5,11,1,8,9,15,6,12,13,14,10,16],[8,1,16,8,4,5,7,6,0,9,10,13,12,11,14,15,2],[0,7,2,3,10,8,6,1,5,9,4,13,12,11,14,15,16],[0,12,2,3,6,8,4,7,5,14,10,11,1,13,9,15,16],[15,1,5,15,4,2,7,6,8,14,10,11,12,13,9,0,16],[0,12,2,3,4,5,6,8,7,9,11,10,1,14,13,15,16],[4,1,2,4,0,5,11,7,8,12,10,6,9,13,14,16,15],[0,1,2,3,10,6,5,7,8,12,4,11,9,14,13,15,16],[0,2,1,3,4,5,6,9,8,7,11,10,12,13,14,16,15],[0,1,16,3,4,6,5,7,8,11,10,9,12,13,15,14,2],[15,1,2,15,4,5,6,8,7,11,10,9,12,16,14,0,13],[4,1,2,4,0,5,6,7,14,9,12,11,10,16,8,15,13],[0,2,1,3,4,13,6,7,8,9,12,11,10,5,15,14,16]]"

@[implicit_reducible]
def «Order3 S1» : Magma (Fin 6) where
  op := finOpTable "[[1,2,2,3,1,1],[5,0,0,0,4,5],[0,1,3,0,3,3],[2,2,4,2,4,5],[5,5,2,3,5,3],[0,1,4,4,1,4]]"

@[implicit_reducible]
def «Order3 S1^op» : Magma (Fin 6) where
  op := finOpTable "[[1,5,0,2,5,0],[2,0,1,2,5,1],[2,0,3,4,2,4],[3,0,0,2,3,4],[1,4,3,4,5,1],[1,5,3,5,3,4]]"

@[implicit_reducible]
def «Order3 S2» : Magma (Fin 10) where
  op := finOpTable "[[2,3,2,5,2,5,5,5,2,2],[3,3,4,3,4,3,4,4,3,3],[0,4,0,0,4,0,4,4,0,0],[5,1,0,1,1,5,5,5,1,1],[2,1,2,1,7,7,7,7,1,7],[0,3,0,3,6,6,6,6,6,0],[5,8,8,5,5,5,5,5,8,8],[9,4,4,9,4,4,4,4,9,9],[9,9,9,9,6,6,6,9,9,9],[8,8,8,8,7,7,8,7,8,8]]"

@[implicit_reducible]
def «Order3 S2^op» : Magma (Fin 10) where
  op := finOpTable "[[2,3,0,5,2,0,5,9,9,8],[3,3,4,1,1,3,8,4,9,8],[2,4,0,0,2,0,8,4,9,8],[5,3,0,1,1,3,5,9,9,8],[2,4,4,1,7,6,5,4,6,7],[5,3,0,5,7,6,5,4,6,7],[5,4,4,5,7,6,5,4,6,8],[5,4,4,5,7,6,5,4,9,7],[2,3,0,1,1,6,8,9,9,8],[2,3,0,1,7,0,8,9,9,8]]"

@[implicit_reducible]
def «Order3 S3» : Magma (Fin 11) where
  op := finOpTable "[[0,2,4,5,7,1,10,8,6,3,9],[4,1,6,7,2,9,3,5,10,8,0],[7,3,2,6,10,8,9,4,1,0,5],[1,5,9,3,8,7,4,10,0,6,2],[8,6,5,0,4,10,2,9,7,1,3],[2,8,1,10,3,5,0,6,9,4,7],[9,7,0,8,5,2,6,3,4,10,1],[6,9,10,2,1,0,8,7,3,5,4],[10,0,3,1,9,4,5,2,8,7,6],[5,10,7,4,6,3,1,0,2,9,8],[3,4,8,9,0,6,7,1,5,2,10]]"

@[implicit_reducible]
def «Order3 S3^op» : Magma (Fin 11) where
  op := finOpTable "[[0,4,7,1,8,2,9,6,10,5,3],[2,1,3,5,6,8,7,9,0,10,4],[4,6,2,9,5,1,0,10,3,7,8],[5,7,6,3,0,10,8,2,1,4,9],[7,2,10,8,4,3,5,1,9,6,0],[1,9,8,7,10,5,2,0,4,3,6],[10,3,9,4,2,0,6,8,5,1,7],[8,5,4,10,9,6,3,7,2,0,1],[6,10,1,0,7,9,4,3,8,2,5],[3,8,0,6,1,4,10,5,7,9,2],[9,0,5,2,3,7,1,4,6,8,10]]"

@[implicit_reducible]
def «Order3 S4» : Magma (Fin 9) where
  op := finOpTable "[[0,2,3,4,6,7,8,1,5],[3,1,5,2,8,6,7,4,0],[4,6,2,7,3,0,5,8,1],[6,5,8,3,1,2,4,0,7],[8,0,7,5,4,1,2,3,6],[1,7,4,8,0,5,3,6,2],[5,4,0,1,7,8,6,2,3],[2,8,1,6,5,3,0,7,4],[7,3,6,0,2,4,1,5,8]]"

@[implicit_reducible]
def «Order3 S4^op» : Magma (Fin 9) where
  op := finOpTable "[[0,3,4,6,8,1,5,2,7],[2,1,6,5,0,7,4,8,3],[3,5,2,8,7,4,0,1,6],[4,2,7,3,5,8,1,6,0],[6,8,3,1,4,0,7,5,2],[7,6,0,2,1,5,8,3,4],[8,7,5,4,2,3,6,0,1],[1,4,8,0,3,6,2,7,5],[5,0,1,7,6,2,3,4,8]]"

@[implicit_reducible]
def «Order3 S5» : Magma (Fin 12) where
  op := finOpTable "[[0,3,5,11,4,8,6,7,2,9,10,1],[2,1,4,3,7,5,8,6,0,9,10,11],[4,10,2,1,6,5,0,7,8,9,3,11],[5,1,0,3,4,6,7,9,8,2,10,11],[0,11,7,3,4,2,6,5,8,9,1,10],[9,1,2,10,0,5,6,7,8,4,11,3],[0,10,8,1,4,5,6,2,7,9,3,11],[0,3,2,11,9,5,4,7,8,6,10,1],[6,11,2,3,4,5,9,7,8,0,1,10],[0,1,2,10,4,7,6,8,5,9,11,3],[0,1,9,3,2,4,5,7,6,8,10,11],[8,1,2,3,5,0,6,4,9,7,10,11]]"

@[implicit_reducible]
def «Order3 S5^op» : Magma (Fin 12) where
  op := finOpTable "[[0,2,4,5,0,9,0,0,6,0,0,8],[3,1,10,1,11,1,10,3,11,1,1,1],[5,4,2,0,7,2,8,2,2,2,9,2],[11,3,1,3,3,10,1,11,3,10,3,3],[4,7,6,4,4,0,4,9,4,4,2,5],[8,5,5,6,2,5,5,5,5,7,4,0],[6,8,0,7,6,6,6,4,9,6,5,6],[7,6,7,9,5,7,2,7,7,8,7,4],[2,0,8,8,8,8,7,8,8,5,6,9],[9,9,9,2,9,4,9,6,0,9,8,7],[10,10,3,10,1,11,3,10,1,11,10,10],[1,11,11,11,10,3,11,1,10,3,11,11]]"

@[implicit_reducible]
def «Order3 S6» : Magma (Fin 7) where
  op := finOpTable "[[0,2,1,4,4,5,6],[3,1,4,0,4,5,6],[3,5,2,0,4,5,6],[6,2,1,3,4,5,6],[0,1,2,3,4,1,0],[0,1,2,3,2,5,6],[0,1,2,3,3,5,6]]"

@[implicit_reducible]
def «Order3 S6^op» : Magma (Fin 7) where
  op := finOpTable "[[0,3,3,6,0,0,0],[2,1,5,2,1,1,1],[1,4,2,1,2,2,2],[4,0,0,3,3,3,3],[4,4,4,4,4,2,3],[5,5,5,5,1,5,5],[6,6,6,6,0,6,6]]"

@[implicit_reducible]
def «Order3 S8» : Magma (Fin 8) where
  op := finOpTable "[[0,2,4,5,4,5,6,7],[3,1,4,4,4,5,6,7],[5,7,2,0,4,5,6,7],[6,6,1,3,4,5,6,7],[0,1,2,3,4,0,1,1],[0,1,2,3,2,5,0,7],[0,1,2,3,3,3,6,7],[0,1,2,3,2,5,6,7]]"

@[implicit_reducible]
def «Order3 S8^op» : Magma (Fin 8) where
  op := finOpTable "[[0,3,5,6,0,0,0,0],[2,1,7,6,1,1,1,1],[4,4,2,1,2,2,2,2],[5,4,0,3,3,3,3,3],[4,4,4,4,4,2,3,2],[5,5,5,5,0,5,3,5],[6,6,6,6,1,0,6,6],[7,7,7,7,1,7,7,7]]"

@[implicit_reducible]
def «Order3 S9» : Magma (Fin 13) where
  op := finOpTable "[[0,3,5,5,4,10,6,7,8,9,3,11,12],[2,1,6,3,4,5,11,7,8,9,10,2,12],[4,4,2,1,8,5,6,7,1,9,10,11,12],[7,1,0,3,4,5,6,9,8,0,10,11,12],[0,1,9,3,4,2,2,7,8,6,10,11,12],[11,1,2,3,0,5,6,0,8,9,10,7,12],[0,12,2,3,1,5,6,7,8,9,10,11,4],[0,1,2,12,4,3,6,7,8,9,10,11,5],[0,1,11,3,4,5,6,7,8,2,10,9,12],[0,1,2,10,12,5,6,7,4,9,8,11,3],[9,1,2,3,4,5,6,7,8,11,10,0,12],[0,8,2,3,4,12,6,7,10,9,5,11,1],[0,1,2,3,4,5,9,11,8,7,10,6,12]]"

@[implicit_reducible]
def «Order3 S9^op» : Magma (Fin 13) where
  op := finOpTable "[[0,2,4,7,0,11,0,0,0,0,9,0,0],[3,1,4,1,1,1,12,1,1,1,1,8,1],[5,6,2,0,9,2,2,2,11,2,2,2,2],[5,3,1,3,3,3,3,12,3,10,3,3,3],[4,4,8,4,4,0,1,4,4,12,4,4,4],[10,5,5,5,2,5,5,3,5,5,5,12,5],[6,11,6,6,2,6,6,6,6,6,6,6,9],[7,7,7,9,7,0,7,7,7,7,7,7,11],[8,8,1,8,8,8,8,8,8,4,8,10,8],[9,9,9,0,6,9,9,9,2,9,11,9,7],[3,10,10,10,10,10,10,10,10,8,10,5,10],[11,2,11,11,11,7,11,11,9,11,0,11,6],[12,12,12,12,12,12,4,5,12,3,12,1,12]]"

@[implicit_reducible]
def «Order3 S10» : Magma (Fin 13) where
  op := finOpTable "[[0,2,1,6,4,5,6,12,8,9,10,9,12],[3,1,4,0,4,7,6,7,8,9,8,11,12],[3,5,2,0,6,5,6,7,10,9,10,11,12],[7,2,1,3,4,5,4,7,8,11,8,11,12],[0,1,8,3,4,1,7,7,8,3,10,11,12],[0,10,2,3,2,5,6,6,8,9,10,11,12],[0,1,2,9,5,5,6,0,2,9,10,11,12],[11,1,2,3,4,4,3,7,8,9,1,11,8],[0,1,1,3,4,5,4,7,8,3,7,11,11],[0,1,2,0,6,5,6,7,10,9,10,12,12],[0,2,2,9,4,5,6,5,12,9,10,11,12],[3,1,2,3,4,5,6,7,8,8,10,11,7],[0,1,2,3,4,5,6,10,9,9,10,0,12]]"

@[implicit_reducible]
def «Order3 S10^op» : Magma (Fin 13) where
  op := finOpTable "[[0,3,3,7,0,0,0,11,0,0,0,3,0],[2,1,5,2,1,10,1,1,1,1,2,1,1],[1,4,2,1,8,2,2,2,1,2,2,2,2],[6,0,0,3,3,3,9,3,3,0,9,3,3],[4,4,6,4,4,2,5,4,4,6,4,4,4],[5,7,5,5,1,5,5,4,5,5,5,5,5],[6,6,6,4,7,6,6,3,4,6,6,6,6],[12,7,7,7,7,6,0,7,7,7,5,7,10],[8,8,10,8,8,8,2,8,8,10,12,8,9],[9,9,9,11,3,9,9,9,3,9,9,8,9],[10,8,10,8,10,10,10,1,7,10,10,10,10],[9,11,11,11,11,11,11,11,11,12,11,11,0],[12,12,12,12,12,12,12,8,11,12,12,7,12]]"

@[implicit_reducible]
def «Order3 S12» : Magma (Fin 11) where
  op := finOpTable "[[0,2,4,7,3,8,9,1,10,5,6],[4,1,6,8,2,0,5,9,7,10,3],[3,5,2,4,9,6,7,10,0,8,1],[1,7,9,3,10,2,0,8,6,4,5],[7,6,8,5,4,10,2,3,9,1,0],[10,4,7,9,0,5,3,6,1,2,8],[5,0,10,1,8,9,6,4,2,3,7],[2,10,1,6,5,3,8,7,4,0,9],[6,9,3,0,1,4,10,5,8,7,2],[8,3,0,10,6,7,1,2,5,9,4],[9,8,5,2,7,1,4,0,3,6,10]]"

@[implicit_reducible]
def «Order3 S12^op» : Magma (Fin 11) where
  op := finOpTable "[[0,4,3,1,7,10,5,2,6,8,9],[2,1,5,7,6,4,0,10,9,3,8],[4,6,2,9,8,7,10,1,3,0,5],[7,8,4,3,5,9,1,6,0,10,2],[3,2,9,10,4,0,8,5,1,6,7],[8,0,6,2,10,5,9,3,4,7,1],[9,5,7,0,2,3,6,8,10,1,4],[1,9,10,8,3,6,4,7,5,2,0],[10,7,0,6,9,1,2,4,8,5,3],[5,10,8,4,1,2,3,0,7,9,6],[6,3,1,5,0,8,7,9,2,4,10]]"

@[implicit_reducible]
def «Order3 S13» : Magma (Fin 12) where
  op := finOpTable "[[0,2,5,6,4,5,10,11,8,9,10,9],[3,1,4,3,4,7,6,7,3,4,10,7],[6,5,2,0,10,8,6,7,8,11,10,11],[7,1,1,3,4,5,4,7,7,1,4,11],[0,1,3,3,4,1,7,7,8,3,7,1],[0,8,9,3,2,5,0,6,10,9,10,11],[11,1,2,9,5,2,6,0,8,9,8,11],[1,1,2,3,4,4,3,7,1,9,3,4],[0,9,2,10,4,6,6,5,8,2,11,11],[0,11,0,8,6,5,6,7,5,9,10,10],[0,1,2,2,11,5,5,8,9,9,10,0],[2,0,2,3,9,5,6,10,8,8,6,11]]"

@[implicit_reducible]
def «Order3 S13^op» : Magma (Fin 12) where
  op := finOpTable "[[0,3,6,7,0,0,11,1,0,0,0,2],[2,1,5,1,1,8,1,1,9,11,1,0],[5,4,2,1,3,9,2,2,2,0,2,2],[6,3,0,3,3,3,9,3,10,8,2,3],[4,4,10,4,4,2,5,4,4,6,11,9],[5,7,8,5,1,5,2,4,6,5,5,5],[10,6,6,4,7,0,6,3,6,6,5,6],[11,7,7,7,7,6,0,7,5,7,8,10],[8,3,8,7,8,10,8,1,8,5,9,8],[9,4,11,1,3,9,9,9,2,9,9,8],[10,10,10,4,7,10,8,3,11,10,10,6],[9,7,11,11,1,11,11,4,11,10,0,11]]"

@[implicit_reducible]
def «Order3 S15» : Magma (Fin 11) where
  op := finOpTable "[[0,3,5,7,4,9,6,1,8,2,10],[2,1,5,3,4,0,6,7,8,9,10],[4,6,2,1,8,5,3,7,0,9,10],[9,1,0,3,4,5,6,7,8,2,10],[0,1,6,3,4,2,5,7,8,9,10],[10,7,2,3,0,5,1,6,8,9,4],[0,1,9,3,10,2,6,7,4,5,8],[5,1,2,3,4,9,6,7,8,0,10],[0,1,9,3,4,5,2,7,8,6,10],[8,1,2,6,4,5,7,3,10,9,0],[0,1,2,3,4,6,9,7,8,5,10]]"

@[implicit_reducible]
def «Order3 S15^op» : Magma (Fin 11) where
  op := finOpTable "[[0,2,4,9,0,10,0,5,0,8,0],[3,1,6,1,1,7,1,1,1,1,1],[5,5,2,0,6,2,9,2,9,2,2],[7,3,1,3,3,3,3,3,3,6,3],[4,4,8,4,4,0,10,4,4,4,4],[9,0,5,5,2,5,2,9,5,5,6],[6,6,3,6,5,1,6,6,2,7,9],[1,7,7,7,7,6,7,7,7,3,7],[8,8,0,8,8,8,4,8,8,10,8],[2,9,9,2,9,9,5,0,6,9,5],[10,10,10,10,10,4,8,10,10,0,10]]"

@[implicit_reducible]
def «Order3 S16» : Magma (Fin 11) where
  op := finOpTable "[[0,6,9,3,4,5,7,1,2,8,10],[2,1,3,0,4,5,6,7,8,9,10],[3,7,2,4,0,1,6,5,8,9,10],[0,5,8,3,4,6,1,7,10,9,2],[0,1,10,3,4,7,5,6,8,2,9],[0,1,4,2,3,5,6,7,8,9,10],[3,1,2,4,0,5,6,7,9,10,8],[4,1,0,3,2,5,6,7,8,9,10],[6,1,2,0,4,5,3,7,8,9,10],[4,1,2,3,6,5,0,7,8,9,10],[0,1,2,6,3,5,4,7,8,9,10]]"

@[implicit_reducible]
def «Order3 S16^op» : Magma (Fin 11) where
  op := finOpTable "[[0,2,3,0,0,0,3,4,6,4,0],[6,1,7,5,1,1,1,1,1,1,1],[9,3,2,8,10,4,2,0,2,2,2],[3,0,4,3,3,2,4,3,0,3,6],[4,4,0,4,4,3,0,2,4,6,3],[5,5,1,6,7,5,5,5,5,5,5],[7,6,6,1,5,6,6,6,3,0,4],[1,7,5,7,6,7,7,7,7,7,7],[2,8,8,10,8,8,9,8,8,8,8],[8,9,9,9,2,9,10,9,9,9,9],[10,10,10,2,9,10,8,10,10,10,10]]"

@[implicit_reducible]
def «Order3 S17» : Magma (Fin 13) where
  op := finOpTable "[[0,9,9,3,4,5,8,7,9,6,10,11,12],[2,1,4,3,8,5,6,7,2,2,10,11,12],[1,3,2,5,4,1,6,7,8,1,10,11,12],[0,1,6,3,2,5,4,7,8,9,10,11,12],[0,7,2,1,4,5,6,3,8,9,12,10,11],[0,1,8,3,4,5,2,7,6,9,10,11,12],[12,1,2,7,4,3,6,5,8,9,0,11,10],[0,1,2,3,6,5,8,7,4,9,10,11,12],[11,5,2,3,4,7,6,1,8,9,10,12,0],[10,0,0,3,4,5,6,7,8,9,11,0,12],[0,1,2,3,6,5,9,7,8,4,10,11,12],[0,1,2,3,9,5,6,7,4,8,10,11,12],[0,1,2,3,8,5,4,7,6,9,10,11,12]]"

@[implicit_reducible]
def «Order3 S17^op» : Magma (Fin 13) where
  op := finOpTable "[[0,2,1,0,0,0,12,0,11,10,0,0,0],[9,1,3,1,7,1,1,1,5,0,1,1,1],[9,4,2,6,2,8,2,2,2,0,2,2,2],[3,3,5,3,1,3,7,3,3,3,3,3,3],[4,8,4,2,4,4,4,6,4,4,6,9,8],[5,5,1,5,5,5,3,5,7,5,5,5,5],[8,6,6,4,6,2,6,8,6,6,9,6,4],[7,7,7,7,3,7,5,7,1,7,7,7,7],[9,2,8,8,8,6,8,4,8,8,8,4,6],[6,2,1,9,9,9,9,9,9,9,4,8,9],[10,10,10,10,12,10,0,10,10,11,10,10,10],[11,11,11,11,10,11,11,11,12,0,11,11,11],[12,12,12,12,11,12,10,12,0,12,12,12,12]]"

@[implicit_reducible]
def «Order3 S18» : Magma (Fin 13) where
  op := finOpTable "[[0,2,11,6,4,5,6,12,6,12,11,11,12],[3,1,4,3,4,7,6,7,8,10,10,11,12],[8,5,2,0,8,5,6,7,8,9,9,5,9],[7,1,1,3,4,5,4,7,8,9,10,10,12],[0,1,10,3,4,1,7,7,7,9,10,3,10],[0,9,2,3,2,5,9,8,8,9,10,8,2],[0,1,2,11,12,12,6,0,11,0,10,11,12],[10,1,2,3,4,4,3,7,10,1,10,11,4],[9,1,2,3,5,5,5,9,8,9,2,2,12],[2,2,2,3,4,5,8,5,8,9,8,11,5],[3,1,1,3,4,5,6,7,4,7,10,4,7],[0,1,12,0,6,6,6,7,0,9,12,11,12],[0,1,0,3,11,11,6,6,8,6,0,11,12]]"

@[implicit_reducible]
def «Order3 S18^op» : Magma (Fin 13) where
  op := finOpTable "[[0,3,8,7,0,0,0,10,9,2,3,0,0],[2,1,5,1,1,9,1,1,1,2,1,1,1],[11,4,2,1,10,2,2,2,2,2,1,12,0],[6,3,0,3,3,3,11,3,3,3,3,0,3],[4,4,8,4,4,2,12,4,5,4,4,6,11],[5,7,5,5,1,5,12,4,5,5,5,6,11],[6,6,6,4,7,9,6,3,5,8,6,6,6],[12,7,7,7,7,8,0,7,9,5,7,7,6],[6,8,8,8,7,8,11,10,8,8,4,0,8],[12,10,9,9,9,9,0,1,9,9,7,9,6],[11,10,9,10,10,10,10,10,2,8,10,12,0],[11,11,5,10,3,8,11,11,2,11,4,11,11],[12,12,9,12,10,2,12,4,12,5,7,12,12]]"

@[implicit_reducible]
def «Order3 S19» : Magma (Fin 6) where
  op := finOpTable "[[0,4,2,0,4,1],[2,1,3,3,1,5],[0,5,2,2,4,4],[3,1,3,3,1,5],[0,4,2,0,4,4],[3,1,0,3,5,5]]"

@[implicit_reducible]
def «Order3 S19^op» : Magma (Fin 6) where
  op := finOpTable "[[0,2,0,3,0,3],[4,1,5,1,4,1],[2,3,2,3,2,0],[0,3,2,3,0,3],[4,1,4,1,4,5],[1,5,4,5,4,5]]"

@[implicit_reducible]
def «Order3 S22» : Magma (Fin 8) where
  op := finOpTable "[[0,3,4,1,4,0,6,7],[2,1,0,6,4,5,6,1],[5,3,2,1,2,5,6,7],[2,7,0,3,4,5,3,7],[0,1,4,3,4,0,4,4],[5,1,2,3,2,5,5,5],[0,1,2,6,6,6,6,1],[0,7,2,3,7,7,3,7]]"

@[implicit_reducible]
def «Order3 S22^op» : Magma (Fin 8) where
  op := finOpTable "[[0,2,5,2,0,5,0,0],[3,1,3,7,1,1,1,7],[4,0,2,0,4,2,2,2],[1,6,1,3,3,3,6,3],[4,4,2,4,4,2,6,7],[0,5,5,5,0,5,6,7],[6,6,6,3,4,5,6,3],[7,1,7,7,4,5,1,7]]"

@[implicit_reducible]
def «Order3 S23» : Magma (Fin 10) where
  op := finOpTable "[[0,3,4,7,4,0,0,7,0,9],[2,1,6,5,1,5,6,1,1,1],[5,7,2,1,2,5,2,7,2,2],[8,9,0,3,4,3,3,3,8,9],[0,4,4,3,4,0,4,4,4,4],[5,1,2,5,2,5,5,5,5,1],[6,1,6,6,6,6,6,1,6,6],[0,7,2,7,7,7,2,7,0,7],[8,8,8,3,8,8,8,3,8,8],[0,9,9,3,9,3,9,9,9,9]]"

@[implicit_reducible]
def «Order3 S24» : Magma (Fin 9) where
  op := finOpTable "[[0,2,4,3,7,5,6,1,8],[3,1,2,4,8,5,6,7,0],[5,1,2,0,4,3,6,7,8],[0,6,1,3,4,5,2,7,8],[6,5,2,3,4,0,1,7,8],[0,1,6,3,2,5,8,7,4],[0,1,2,5,3,7,6,4,8],[8,1,2,3,4,5,0,7,6],[0,7,2,3,4,1,6,5,8]]"

@[implicit_reducible]
def «Order3 S24^op» : Magma (Fin 9) where
  op := finOpTable "[[0,3,5,0,6,0,0,8,0],[2,1,1,6,5,1,1,1,7],[4,2,2,1,2,6,2,2,2],[3,4,0,3,3,3,5,3,3],[7,8,4,4,4,2,3,4,4],[5,5,3,5,0,5,7,5,1],[6,6,6,2,1,8,6,0,6],[1,7,7,7,7,7,4,7,5],[8,0,8,8,8,4,8,6,8]]"

@[implicit_reducible]
def «Order3 S25» : Magma (Fin 14) where
  op := finOpTable "[[0,1,3,4,2,5,6,7,8,9,10,11,12,13],[0,1,2,3,9,4,6,7,8,5,10,11,12,13],[5,1,2,3,4,7,6,0,8,9,10,11,12,13],[6,1,2,3,4,0,5,7,8,9,10,11,12,13],[7,11,2,3,4,5,0,6,8,9,1,10,12,13],[0,10,8,2,4,5,6,7,3,9,12,11,1,13],[0,1,2,8,3,5,6,7,4,9,10,11,12,13],[0,1,4,3,8,5,6,7,2,9,10,11,12,13],[0,1,2,3,4,6,7,5,8,9,10,11,12,13],[0,12,2,3,4,5,6,7,8,9,10,1,11,13],[0,1,2,3,5,13,6,7,8,9,10,11,12,4],[0,1,2,3,13,5,6,7,8,4,10,11,12,9],[0,1,2,3,4,9,6,7,8,13,10,11,12,5],[0,1,2,3,4,5,6,7,8,9,11,12,10,13]]"

@[implicit_reducible]
def «Order3 S25^op» : Magma (Fin 14) where
  op := finOpTable "[[0,0,5,6,7,0,0,0,0,0,0,0,0,0],[1,1,1,1,11,10,1,1,1,12,1,1,1,1],[3,2,2,2,2,8,2,4,2,2,2,2,2,2],[4,3,3,3,3,2,8,3,3,3,3,3,3,3],[2,9,4,4,4,4,3,8,4,4,5,13,4,4],[5,4,7,0,5,5,5,5,6,5,13,5,9,5],[6,6,6,5,0,6,6,6,7,6,6,6,6,6],[7,7,0,7,6,7,7,7,5,7,7,7,7,7],[8,8,8,8,8,3,4,2,8,8,8,8,8,8],[9,5,9,9,9,9,9,9,9,9,9,4,13,9],[10,10,10,10,1,12,10,10,10,10,10,10,10,11],[11,11,11,11,10,11,11,11,11,1,11,11,11,12],[12,12,12,12,12,1,12,12,12,11,12,12,12,10],[13,13,13,13,13,13,13,13,13,13,4,9,5,13]]"

@[implicit_reducible]
def «Order3 S26» : Magma (Fin 16) where
  op := finOpTable "[[0,3,3,6,4,5,9,13,8,1,10,2,12,1,14,2],[2,1,4,2,8,4,6,7,3,0,10,11,12,0,3,15],[1,5,2,1,5,10,6,7,8,9,3,0,3,13,14,0],[7,0,0,3,4,5,12,8,1,9,2,11,2,13,1,15],[0,9,1,3,4,1,5,5,7,6,10,11,6,13,14,7],[0,2,11,3,2,5,4,4,8,9,7,6,12,7,6,15],[11,1,2,14,7,7,6,0,8,4,10,5,4,13,5,15],[15,1,2,10,6,6,3,7,4,9,5,11,12,5,14,4],[0,14,2,14,15,5,6,15,8,1,3,9,12,13,11,11],[13,13,2,3,12,5,12,7,4,9,8,0,10,10,14,15],[0,1,12,12,4,13,6,13,7,11,10,2,9,9,14,15],[15,1,15,3,4,14,14,7,10,6,5,11,12,13,8,8],[0,1,10,10,9,5,9,7,8,13,13,11,12,14,3,14],[9,9,2,3,4,10,6,10,8,12,12,11,15,13,15,0],[0,8,2,8,4,11,11,7,15,9,10,15,6,12,14,12],[11,1,11,3,8,5,6,8,14,9,10,14,13,7,13,15]]"

@[implicit_reducible]
def «Order3 S26^op» : Magma (Fin 16) where
  op := finOpTable "[[0,2,1,7,0,0,11,15,0,13,0,15,0,9,0,11],[3,1,5,0,9,2,1,1,14,13,1,1,1,9,8,1],[3,4,2,0,1,11,2,2,2,2,12,15,10,2,2,11],[6,2,1,3,3,3,14,10,14,3,12,3,10,3,8,3],[4,8,5,4,4,2,7,6,15,12,4,4,9,4,4,8],[5,4,10,5,1,5,7,6,5,5,13,14,5,10,11,5],[9,6,6,12,5,4,6,3,6,12,6,14,9,6,11,6],[13,7,7,8,5,4,0,7,15,7,13,7,7,10,7,8],[8,3,8,1,7,8,8,4,8,4,7,10,8,8,15,14],[1,0,9,9,6,9,4,9,1,9,11,6,13,12,9,9],[10,10,3,2,10,7,10,5,3,8,10,5,13,12,10,10],[2,11,0,11,11,6,5,11,9,0,2,11,11,11,15,14],[12,12,3,2,6,12,4,12,12,10,9,12,12,15,6,13],[1,0,13,13,13,7,13,5,13,10,9,13,14,13,12,7],[14,3,14,1,14,6,5,14,11,14,14,8,3,15,14,13],[2,15,0,15,7,15,15,4,11,15,15,8,14,0,12,15]]"

@[implicit_reducible]
def «Order3 S27» : Magma (Fin 8) where
  op := finOpTable "[[0,2,4,4,0,3,0,0],[3,1,6,1,1,6,1,4],[5,0,2,2,6,2,3,2],[1,3,3,3,7,0,2,3],[4,4,0,0,4,4,5,1],[2,7,5,6,5,5,4,5],[6,6,1,5,2,1,6,6],[7,5,7,7,3,7,7,7]]"

@[implicit_reducible]
def «Order3 S27^op» : Magma (Fin 8) where
  op := finOpTable "[[0,3,5,1,4,2,6,7],[2,1,0,3,4,7,6,5],[4,6,2,3,0,5,1,7],[4,1,2,3,0,6,5,7],[0,1,6,7,4,5,2,3],[3,6,2,0,4,5,1,7],[0,1,3,2,5,4,6,7],[0,4,2,3,1,5,6,7]]"

@[implicit_reducible]
def «Order3 S28» : Magma (Fin 12) where
  op := finOpTable "[[0,2,3,1,4,5,6,7,8,9,10,11],[4,1,2,3,6,5,0,11,8,7,10,9],[5,1,2,3,9,7,6,0,8,10,4,11],[6,1,2,3,4,0,5,7,8,11,9,10],[0,8,1,3,4,5,6,7,2,9,10,11],[0,1,8,2,4,5,6,7,3,9,10,11],[0,3,2,8,4,5,6,7,1,9,10,11],[0,8,1,3,4,5,6,7,2,9,10,11],[0,1,2,3,5,6,4,10,8,9,11,7],[0,2,3,1,4,5,6,7,8,9,10,11],[0,1,8,2,4,5,6,7,3,9,10,11],[0,3,2,8,4,5,6,7,1,9,10,11]]"

@[implicit_reducible]
def «Order3 S28^op» : Magma (Fin 12) where
  op := finOpTable "[[0,4,5,6,0,0,0,0,0,0,0,0],[2,1,1,1,8,1,3,8,1,2,1,3],[3,2,2,2,1,8,2,1,2,3,8,2],[1,3,3,3,3,2,8,3,3,1,2,8],[4,6,9,4,4,4,4,4,5,4,4,4],[5,5,7,0,5,5,5,5,6,5,5,5],[6,0,6,5,6,6,6,6,4,6,6,6],[7,11,0,7,7,7,7,7,10,7,7,7],[8,8,8,8,2,3,1,2,8,8,3,1],[9,7,10,11,9,9,9,9,9,9,9,9],[10,10,4,9,10,10,10,10,11,10,10,10],[11,9,11,10,11,11,11,11,7,11,11,11]]"

@[implicit_reducible]
def «Order3 S29» : Magma (Fin 8) where
  op := finOpTable "[[1,2,3,0,5,0,3,4],[4,0,3,1,5,1,5,5],[0,1,2,0,1,1,5,6],[2,2,6,3,0,1,2,6],[0,1,0,7,4,2,3,6],[4,4,6,7,6,5,4,6],[2,2,4,7,7,7,6,7],[3,3,3,4,5,7,5,7]]"

@[implicit_reducible]
def «Order3 S29^op» : Magma (Fin 8) where
  op := finOpTable "[[1,4,0,2,0,4,2,3],[2,0,1,2,1,4,2,3],[3,3,2,6,0,6,4,3],[0,1,0,3,7,7,7,4],[5,5,1,0,4,6,7,5],[0,1,1,1,2,5,7,7],[3,5,5,2,3,4,6,5],[4,5,6,6,6,6,7,7]]"

@[implicit_reducible]
def «Order3 S30» : Magma (Fin 9) where
  op := finOpTable "[[0,2,8,5,4,5,0,4,8],[3,1,4,1,4,1,6,1,1],[7,5,2,0,2,5,6,7,2],[6,3,1,3,4,3,6,3,3],[0,1,4,3,4,1,0,4,8],[0,5,2,5,2,5,0,5,5],[6,1,2,3,7,3,6,7,6],[6,7,2,7,7,7,6,7,2],[0,8,8,8,4,8,8,0,8]]"

@[implicit_reducible]
def «Order3 S30^op» : Magma (Fin 9) where
  op := finOpTable "[[0,3,7,6,0,0,6,6,0],[2,1,5,3,1,5,1,7,8],[8,4,2,1,4,2,2,2,8],[5,1,0,3,3,5,3,7,8],[4,4,2,4,4,2,7,7,4],[5,1,5,3,1,5,3,7,8],[0,6,6,6,0,0,6,6,8],[4,1,7,3,4,5,7,7,0],[8,1,2,3,8,5,6,2,8]]"

@[implicit_reducible]
def «Order3 S31» : Magma (Fin 16) where
  op := finOpTable "[[0,2,3,1,6,4,5,11,8,13,9,12,7,10,14,15],[4,1,7,2,5,0,6,3,11,8,10,9,14,12,13,15],[6,3,2,7,0,5,4,1,15,9,11,14,12,8,10,13],[5,7,1,3,4,6,0,2,12,15,8,11,10,13,9,14],[5,8,10,3,4,6,0,15,9,1,14,7,12,13,2,11],[6,13,2,8,0,5,4,12,10,9,3,11,15,14,1,7],[4,1,8,9,5,0,6,7,13,14,10,15,11,2,3,12],[4,2,3,1,5,0,6,7,8,13,9,15,11,10,14,12],[0,9,13,10,6,4,5,7,8,11,12,1,3,15,14,2],[6,11,2,14,0,5,4,10,1,9,13,8,12,7,15,3],[4,1,14,12,5,0,6,13,3,7,10,2,8,9,11,15],[6,8,10,3,0,5,4,12,9,1,14,11,15,13,2,7],[5,13,2,8,4,6,0,15,10,9,3,7,12,14,1,11],[5,14,15,3,4,6,0,9,2,10,7,11,1,13,12,8],[0,12,11,15,6,4,5,7,8,3,2,10,13,1,14,9],[0,1,8,9,6,4,5,11,13,14,10,12,7,2,3,15]]"

@[implicit_reducible]
def «Order3 S31^op» : Magma (Fin 16) where
  op := finOpTable "[[0,4,6,5,5,6,4,4,0,6,4,6,5,5,0,0],[2,1,3,7,8,13,1,2,9,11,1,8,13,14,12,1],[3,7,2,1,10,2,8,3,13,2,14,10,2,15,11,8],[1,2,7,3,3,8,9,1,10,14,12,3,8,3,15,9],[6,5,0,4,4,0,5,5,6,0,5,0,4,4,6,6],[4,0,5,6,6,5,0,0,4,5,0,5,6,6,4,4],[5,6,4,0,0,4,6,6,5,4,6,4,0,0,5,5],[11,3,1,2,15,12,7,7,7,10,13,12,15,9,7,11],[8,11,15,12,9,10,13,8,8,1,3,9,10,2,8,13],[13,8,9,15,1,9,14,13,11,9,7,1,9,10,3,14],[9,10,11,8,14,3,10,9,12,13,10,14,3,7,2,10],[12,9,14,11,7,11,15,15,1,8,2,11,7,11,10,12],[7,14,12,10,12,15,11,11,3,12,8,15,12,1,13,7],[10,12,8,13,13,14,2,10,15,7,9,13,14,13,1,2],[14,13,10,9,2,1,3,14,14,15,11,2,1,12,14,3],[15,15,13,14,11,7,12,12,2,3,15,7,11,8,9,15]]"

@[implicit_reducible]
def «Order3 S32» : Magma (Fin 9) where
  op := finOpTable "[[0,2,4,6,4,5,5,7,8],[3,1,2,4,4,2,6,6,8],[5,1,2,0,4,5,1,7,8],[4,8,1,3,4,5,6,7,8],[0,1,2,3,4,0,3,7,1],[0,6,2,3,2,5,6,0,8],[7,1,5,3,0,5,6,7,1],[0,8,2,3,4,6,6,7,8],[0,1,2,3,3,5,7,7,8]]"

@[implicit_reducible]
def «Order3 S32^op» : Magma (Fin 9) where
  op := finOpTable "[[0,3,5,4,0,0,7,0,0],[2,1,1,8,1,6,1,8,1],[4,2,2,1,2,2,5,2,2],[6,4,0,3,3,3,3,3,3],[4,4,4,4,4,2,0,4,3],[5,2,5,5,0,5,5,6,5],[5,6,1,6,3,6,6,6,7],[7,6,7,7,7,0,7,7,7],[8,8,8,8,1,8,1,8,8]]"

@[implicit_reducible]
def «Order3 S33» : Magma (Fin 9) where
  op := finOpTable "[[0,2,3,3,0,5,3,0,0],[4,1,4,1,4,1,1,1,1],[6,5,2,2,2,5,8,7,8],[0,3,3,3,0,3,3,0,0],[4,1,4,1,4,1,6,1,1],[0,5,2,5,0,5,5,0,5],[7,6,4,6,4,6,6,7,6],[7,7,2,2,2,6,6,7,7],[8,8,2,2,2,8,8,8,8]]"

@[implicit_reducible]
def «Order3 S33^op» : Magma (Fin 9) where
  op := finOpTable "[[0,4,6,0,4,0,7,7,8],[2,1,5,3,1,5,6,7,8],[3,4,2,3,4,2,4,2,2],[3,1,2,3,1,5,6,2,2],[0,4,2,0,4,0,4,2,2],[5,1,5,3,1,5,6,6,8],[3,1,8,3,6,5,6,6,8],[0,1,7,0,1,0,7,7,8],[0,1,8,0,1,5,6,7,8]]"

@[implicit_reducible]
def «Order3 S34» : Magma (Fin 8) where
  op := finOpTable "[[0,2,2,2,0,2,0,0],[3,1,1,4,4,5,1,3],[0,2,2,2,0,2,0,7],[5,5,3,3,3,6,6,7],[4,1,1,4,4,5,1,4],[4,1,5,7,4,5,5,4],[6,6,3,3,3,6,6,6],[7,2,2,3,7,1,7,7]]"

@[implicit_reducible]
def «Order3 S34^op» : Magma (Fin 8) where
  op := finOpTable "[[0,3,0,5,4,4,6,7],[2,1,2,5,1,1,6,2],[2,1,2,3,1,5,3,2],[2,4,2,3,4,7,3,3],[0,4,0,3,4,4,3,7],[2,5,2,6,5,5,6,1],[0,1,0,6,1,5,6,7],[0,3,7,7,4,4,6,7]]"

@[implicit_reducible]
def «Order3 S35» : Magma (Fin 11) where
  op := finOpTable "[[0,2,4,6,4,5,4,7,8,5,10],[3,1,5,4,4,5,6,7,6,9,10],[5,7,2,0,4,5,6,7,7,9,10],[9,7,1,3,4,5,5,7,8,4,10],[0,1,2,3,4,0,6,1,0,9,3],[0,1,2,3,2,5,6,1,3,9,0],[8,1,2,8,4,5,6,1,8,0,10],[0,1,2,3,3,2,8,7,8,2,10],[0,7,9,3,6,6,6,7,8,9,10],[10,1,2,10,4,5,3,8,8,9,10],[0,1,2,3,9,9,6,7,8,9,10]]"

@[implicit_reducible]
def «Order3 S35^op» : Magma (Fin 11) where
  op := finOpTable "[[0,3,5,9,0,0,8,0,0,10,0],[2,1,7,7,1,1,1,1,7,1,1],[4,5,2,1,2,2,2,2,9,2,2],[6,4,0,3,3,3,8,3,3,10,3],[4,4,4,4,4,2,4,3,6,4,9],[5,5,5,5,0,5,5,2,6,5,9],[4,6,6,5,6,6,6,8,6,3,6],[7,7,7,7,1,1,1,7,7,8,7],[8,6,7,8,0,3,8,8,8,8,8],[5,9,9,4,9,9,0,2,9,9,9],[10,10,10,10,3,0,10,10,10,10,10]]"

@[implicit_reducible]
def «Order3 S36» : Magma (Fin 9) where
  op := finOpTable "[[0,2,2,6,0,0,2,7,6],[3,1,1,4,4,1,1,7,1],[0,2,2,2,0,0,2,7,2],[5,7,3,3,3,5,6,5,8],[4,1,1,4,4,1,6,4,8],[5,5,3,3,3,5,5,5,5],[7,6,6,3,4,6,6,4,8],[0,1,2,8,7,7,8,7,2],[4,8,8,3,4,8,6,0,8]]"

@[implicit_reducible]
def «Order3 S36^op» : Magma (Fin 9) where
  op := finOpTable "[[0,3,0,5,4,5,7,0,4],[2,1,2,7,1,5,6,1,8],[2,1,2,3,1,3,6,2,8],[6,4,2,3,4,3,3,8,3],[0,4,0,3,4,3,4,7,4],[0,1,0,5,1,5,6,7,8],[2,1,2,6,6,5,6,8,6],[7,7,7,5,4,5,4,7,0],[6,1,2,8,8,5,8,2,8]]"

@[implicit_reducible]
def «Order3 L1» : Magma (Fin 25) where
  op := finOpTable "[[0,2,4,12,1,15,21,8,14,10,16,22,19,24,7,20,9,6,13,3,5,17,23,11,18],[3,1,11,8,5,6,4,19,0,14,7,21,16,18,24,13,23,22,15,10,17,2,20,12,9],[5,6,2,1,7,10,3,12,17,20,0,16,4,21,15,23,18,19,11,8,22,24,9,14,13],[7,14,0,3,10,24,11,2,6,16,21,8,22,12,17,18,20,1,19,15,9,4,13,5,23],[6,9,3,5,4,2,22,23,11,15,19,17,18,7,16,1,21,8,24,20,10,14,0,13,12],[9,22,16,7,0,5,18,10,24,4,3,23,1,20,6,8,19,11,14,2,21,13,12,17,15],[11,0,8,13,23,9,6,14,15,22,18,1,24,16,19,2,3,12,21,7,4,10,5,20,17],[1,12,18,4,24,21,5,7,23,8,11,15,0,19,20,10,14,13,22,17,16,6,2,9,3],[20,7,14,2,12,22,23,16,8,17,4,13,10,15,3,11,1,21,6,5,24,9,19,18,0],[2,18,15,6,13,1,12,21,4,9,14,10,3,8,11,0,17,23,5,24,19,22,7,16,20],[17,15,9,14,16,4,8,24,20,23,10,19,11,3,13,22,5,18,0,12,6,7,1,2,21],[4,24,13,15,21,3,2,22,9,12,1,11,8,6,23,5,7,20,17,14,18,0,16,19,10],[15,8,24,18,20,23,16,3,19,13,9,4,12,10,2,17,22,0,7,1,11,5,6,21,14],[8,16,1,9,17,0,20,6,5,11,22,3,14,13,21,4,2,15,10,23,7,12,18,24,19],[16,20,6,22,15,7,17,13,1,19,12,0,23,5,14,24,11,2,9,18,8,3,21,10,4],[21,17,10,23,18,13,14,1,3,5,20,24,6,9,12,15,4,7,16,0,2,19,11,8,22],[23,21,17,19,3,8,9,0,12,24,2,20,5,11,22,14,16,10,1,4,13,18,15,7,6],[24,10,5,20,9,18,15,4,22,7,13,12,21,1,8,19,0,17,2,6,23,11,14,3,16],[22,4,20,0,14,19,7,9,10,6,24,5,2,17,1,21,13,16,18,11,12,23,3,15,8],[18,11,22,21,6,17,13,15,16,1,8,9,7,4,5,12,10,14,23,19,3,20,24,0,2],[13,3,7,24,8,12,19,11,18,21,23,2,17,14,0,9,6,5,4,16,20,15,10,22,1],[12,13,19,16,22,14,24,18,7,2,5,6,20,23,10,3,15,4,8,9,0,21,17,1,11],[19,23,21,10,11,16,1,20,2,18,17,14,9,0,4,7,24,3,12,13,15,8,22,6,5],[14,5,12,11,19,20,10,17,21,0,15,18,13,2,9,6,8,24,3,22,1,16,4,23,7],[10,19,23,17,2,11,0,5,13,3,6,7,15,22,18,16,12,9,20,21,14,1,8,4,24]]"

@[implicit_reducible]
def «Order3 B1» : Magma (Fin 16) where
  op := finOpTable "[[2,7,3,0,4,14,15,1,9,8,12,13,10,11,5,6],[9,2,5,10,11,1,6,8,7,0,3,4,14,15,12,13],[3,5,2,4,0,6,1,10,12,14,11,7,13,8,15,9],[0,14,4,2,3,15,9,12,10,5,13,8,11,7,6,1],[4,15,0,3,2,9,14,13,11,6,8,12,7,10,1,5],[10,1,6,11,7,2,5,3,14,12,4,0,15,9,13,8],[11,6,1,7,10,5,2,4,15,13,0,3,9,14,8,12],[8,9,10,14,15,12,13,2,0,1,7,11,5,6,3,4],[1,0,12,5,6,3,4,9,2,7,14,15,8,13,10,11],[7,8,14,12,13,10,11,0,1,2,5,6,3,4,9,15],[14,12,11,15,9,13,8,7,5,3,2,10,6,1,4,0],[15,13,7,9,14,8,12,11,6,4,10,2,1,5,0,3],[5,3,13,6,1,4,0,14,8,10,15,9,2,12,11,7],[6,4,8,1,5,0,3,15,13,11,9,14,12,2,7,10],[12,10,15,13,8,11,7,5,3,9,6,1,4,0,2,14],[13,11,9,8,12,7,10,6,4,15,1,5,0,3,14,2]]"

@[implicit_reducible]
def «Order3 B1^op» : Magma (Fin 16) where
  op := finOpTable "[[2,9,3,0,4,10,11,8,1,7,14,15,5,6,12,13],[7,2,5,14,15,1,6,9,0,8,12,13,3,4,10,11],[3,5,2,4,0,6,1,10,12,14,11,7,13,8,15,9],[0,10,4,2,3,11,7,14,5,12,15,9,6,1,13,8],[4,11,0,3,2,7,10,15,6,13,9,14,1,5,8,12],[14,1,6,15,9,2,5,12,3,10,13,8,4,0,11,7],[15,6,1,9,14,5,2,13,4,11,8,12,0,3,7,10],[1,8,10,12,13,3,4,2,9,0,7,11,14,15,5,6],[9,7,12,10,11,14,15,0,2,1,5,6,8,13,3,4],[8,0,14,5,6,12,13,1,7,2,3,4,10,11,9,15],[12,3,11,13,8,4,0,7,14,5,2,10,15,9,6,1],[13,4,7,8,12,0,3,11,15,6,10,2,9,14,1,5],[10,14,13,11,7,15,9,5,8,3,6,1,2,12,4,0],[11,15,8,7,10,9,14,6,13,4,1,5,12,2,0,3],[5,12,15,6,1,13,8,3,10,9,4,0,11,7,2,14],[6,13,9,1,5,8,12,4,11,15,0,3,7,10,14,2]]"

end Order3
