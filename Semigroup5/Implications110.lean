import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_53809_54057_implies_Equation53818 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53809 : Equation53809 G) (h54057 : Equation54057 G) : Equation53818 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54057 (X0 ◇ X1) X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X0 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h54057 X0 X1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54057 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 ((X1 ◇ X2) ◇ (X0 ◇ X0))]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X2 (X0 ◇ X0)]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l1 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X2 X0]
    conv => enter [1]; rw [l3 X0 X1 X2]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l4 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l7 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X2]
  have l10 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53809 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l11 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [h53809 (X1 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h54057 X0 X1]
  have l12 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h53809 (X0 ◇ (X1 ◇ X0)) X0]
    conv => enter [1, 2, 2]; rw [← h53809 X0 X1]
  have l13 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h53809 X0 X1]
  have l14 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l13 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1]; rw [← l9 X0 (X0 ◇ (X1 ◇ X0)) X0]
  have l16 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l11 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))]
  have l17 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l14 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l18 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) (X0 ◇ X0)]
  have l19 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l16 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))]
  have l20 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l17 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l21 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 (X1 ◇ X0) X0]
    conv => enter [1]; rw [← l18 X0 X1]
  have l22 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l19 X1 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ X0) (X0 ◇ (X1 ◇ X0))]
  have l23 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l20 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l24 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l21 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))]
  have l25 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l22 X1 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X0 (X0 ◇ (X1 ◇ X0))]
  have l26 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l24 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X0 ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))]
  have l27 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l25 X1 X0]
    conv => enter [1, 2]; rw [← l23 X0 (X0 ◇ (X0 ◇ (X1 ◇ X0))) X1]
  have l28 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))))) := by
    intro X0 X1
    conv => enter [1]; rw [l26 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X0) (X0 ◇ (X1 ◇ X0))]
  have l29 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l27 X1 X0]
    conv => enter [1, 2, 2]; rw [← l9 X0 X0 (X1 ◇ X0)]
  have l30 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l28 X0 X1]
    conv => enter [1, 2, 2]; rw [← l23 X0 (X1 ◇ X0) (X1 ◇ X0)]
  have l31 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l29 X1 X0]
    conv => enter [1, 2]; rw [← l9 X0 X0 (X1 ◇ X0)]
  have l32 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l30 X0 X1]
    conv => enter [1, 2, 2]; rw [← l10 X0 X0 X1]
  have l33 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l31 X1 X0]
    conv => enter [1, 2]; rw [← l10 X0 X0 X1]
  have l34 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [← l33 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))]
  have l35 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l34 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))]
  have l36 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l35 X1 X0]
    conv => enter [1, 2]; rw [← h54057 (X1 ◇ (X0 ◇ X0)) X0]
  have l37 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l36 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X0) (X0 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l38 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))) := by
    intro X1 X0
    conv => enter [1]; rw [l37 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 (X0 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l39 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) := by
    intro X1 X0
    conv => enter [1]; rw [l38 X1 X0]
    conv => enter [1]; rw [← l9 X0 X1 (X0 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l40 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l39 X1 X0]
    conv => enter [1, 2, 2]; rw [← l10 X0 X1 X0]
  have l41 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l32 X0 X1]
    conv => enter [1]; rw [← l40 X1 X0]
  have l42 : ∀ X0 X2 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X2) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [l41 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X0)) X2]
  have l43 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h54057 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← l41 X0 (X0 ◇ (X0 ◇ X0))]
  have l44 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1 X0]
    conv => enter [1]; rw [← l43 X0 X1]
  have l45 : ∀ X0 X2 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X2)) = (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X2]
    conv => enter [1]; rw [l42 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l46 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l44 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) (X1 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l47 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1, 2]; rw [h4512 X0 X0 X2]
    conv => enter [1]; rw [l45 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X2]
  have l48 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l46 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 (X1 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l49 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l48 X0 X1]
    conv => enter [1, 2]; rw [← l23 X0 (X0 ◇ X0) X1]
  have l50 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l49 X0 X1]
    conv => enter [1]; rw [l5 X0 X0 X0]
  have l51 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X0 X0]
    conv => enter [1]; rw [← l50 X0 X1]
  have l52 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l10 (X1 ◇ (X0 ◇ X0)) X2 X0]
    conv => enter [1, 2, 2, 2]; rw [← l51 X0 X1]
  have l53 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3)) = ((X0 ◇ (X0 ◇ X0)) ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ X0))) X3]
    conv => enter [1, 1]; rw [← l10 X0 X1 X2]
  have l54 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3)) = (X0 ◇ ((X0 ◇ X0) ◇ X3)) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l53 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X3]
  have l55 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l52 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))]
  have l56 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X0))) ◇ X3)) = (X0 ◇ (X0 ◇ (X0 ◇ X3))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l54 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X3]
  have l57 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l55 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))]
  have l58 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X3))) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X0)) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l56 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X0)) X3]
  have l59 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l57 X1 X0 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ X0) (X2 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l60 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X3))) = (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X0) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l58 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ X0) X3]
  have l61 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l59 X1 X0 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X0 (X2 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l62 : ∀ X0 X3 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X3))) = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l60 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 X0 X3]
  have l63 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l61 X1 X0 X2]
    conv => enter [1, 2]; rw [← l23 X0 (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) X1]
  have l64 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l63 X1 X0 X2]
    conv => enter [1]; rw [← l47 X0 (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) X1]
  have l65 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) = (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l64 X1 X0 X2]
    conv => enter [1]; rw [← l9 X0 X0 (X2 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l66 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l65 X1 X0 X1]
    conv => enter [1, 2]; rw [← l62 X0 X0 X1 X0]
  have l67 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = ((X1 ◇ (X0 ◇ X0)) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X0 X0]
    conv => enter [1]; rw [← l66 X1 X0]
  have l68 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ X0) ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l67 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X0) ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))]
  have l69 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l68 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 ((X1 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ X0)))]
  have l70 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l69 X0 X1]
    conv => enter [1, 2]; rw [← h54057 (X1 ◇ (X0 ◇ X0)) X0]
  have l71 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) := by
    intro X0 X1
    conv => enter [1]; rw [l70 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X0) (X0 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l72 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l71 X0 X1]
    conv => enter [1]; rw [← l62 X1 (X0 ◇ X0) (X0 ◇ X0) X0]
  have l73 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l72 X0 X1]
    conv => enter [1, 2]; rw [← h54057 X0 X1]
  have l74 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l73 (X0 ◇ X1) X2]
  have l75 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X2 ◇ (X1 ◇ (X2 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l73 X1 X0]
    conv => enter [1]; rw [l73 X1 X2]
  have l76 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l73 X1 X0]
    conv => enter [1]; rw [l41 X1 X2]
    conv => enter [1, 2]; rw [l73 X1 X0]
  have l77 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l73 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ ((X1 ◇ X2) ◇ X0))]
  have l78 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l77 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X0]
  have l79 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l74 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l80 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l76 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l79 X0 X1 X2]
  have l81 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = (X2 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0))))) := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [h54057 X0 X1]
    conv => enter [1]; rw [l75 X1 (X1 ◇ (X0 ◇ X0)) X2]
  have l82 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = (X2 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ (X1 ◇ (X0 ◇ X0)))))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l81 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X0) (X2 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l83 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l80 X1 (X0 ◇ X0) X1]
    conv => enter [1]; rw [← l82 X1 X0 X1]
  have l84 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l83 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X0) (X0 ◇ (X1 ◇ X0))]
  have l85 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ X0)))) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l84 X1 X0]
    conv => enter [1]; rw [← l62 X1 X0 (X0 ◇ X0) X0]
  have l86 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4512 X0 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l85 X1 X0]
  have l87 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l78 X0 X1 X0]
    conv => enter [1]; rw [l86 X1 X0]
  have l88 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X2 ◇ (X2 ◇ (X2 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l87 X1 X0]
    conv => enter [1]; rw [l87 X1 X2]
  have l89 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) = (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0))))) := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [l87 X0 X2]
    conv => enter [1]; rw [l88 X2 (X2 ◇ (X2 ◇ X0)) X1]
  have l90 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [l9 X2 X1 X0]
    conv => enter [1]; rw [← l89 X2 X0 X1]
  have l91 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ (X0 ◇ X0))) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l9 X0 X2 X0]
    conv => enter [1]; rw [← l90 X1 X2 X0]
  have l92 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l51 X0 X2]
    conv => enter [1]; rw [l91 X0 X2 X1]
  have l93 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ X0) ◇ X0)) = (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54057 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l92 (X0 ◇ X0) X1 X2]
  have l94 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2]
    conv => enter [1]; rw [← l93 X0 X1 X2]
  have l95 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X0 X0]
    conv => enter [1]; rw [← l94 X0 X1 X2]
  have l96 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53809 X0 X0]
    conv => enter [1]; rw [l95 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l96 x y z]

theorem Equation4512_53807_53812_54209_implies_Equation53842 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53807 : Equation53807 G) (h53812 : Equation53812 G) (h54209 : Equation54209 G) : Equation53842 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54209 (X0 ◇ X1) X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = ((X0 ◇ (X1 ◇ X1)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X0 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h54209 X0 X1]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ ((X1 ◇ X1) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l1 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ (X1 ◇ (X1 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l2 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l4 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X2))) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l7 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53812 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 (X0 ◇ X0) X1 X0]
    conv => enter [1, 2, 2]; rw [← h53812 X0 (X0 ◇ X0)]
  have l9 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 (X1 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1]; rw [← l6 X1 X0 (X0 ◇ X0)]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h53807 X0]
    conv => enter [1]; rw [← l10 X0 X1]
  have l12 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l11 X1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 ((X0 ◇ X0) ◇ (X0 ◇ X0))]
  have l13 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l12 X1 X0]
    conv => enter [1]; rw [l3 X0 (X0 ◇ X0) X0]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l13 X1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ (X0 ◇ X0))]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X0 X0]
    conv => enter [1]; rw [← l14 X1 X0]
  have l16 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h53807 X0]
    conv => enter [1]; rw [l15 X0 X1]
  have l17 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X3))) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l3 X3 (X0 ◇ X1) X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l18 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ X3))]
    conv => enter [1]; rw [l17 X0 X1 X2 X3]
  have l19 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) = (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 (X2 ◇ X1)]
    conv => enter [1]; rw [← l18 X0 X1 X2 X1]
  have l20 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h53812 X1 X2]
    conv => enter [1]; rw [← l19 X0 X1 X2]
  have l21 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = (X0 ◇ (X2 ◇ (X1 ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l20 X0 X1 X2]
    conv => enter [1, 2]; rw [← h54209 X2 X1]
  intro x y z
  conv => enter [1]; rw [l16 x y]
  conv => enter [1]; rw [l21 y x z]

theorem Equation4512_53809_53869_implies_Equation53811 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53809 : Equation53809 G) (h53869 : Equation53869 G) : Equation53811 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53869 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h53869 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X0)) X2]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l3 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) X2]
    conv => enter [1]; rw [l3 X0 X1 X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l4 X0 X1 X2]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53809 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h53809 X0 X1]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l7 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l10 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l9 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l11 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l10 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1 X0]
    conv => enter [1, 2]; rw [← h53869 X0 X1]
  have l13 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l12 X0 X2]
    conv => enter [1]; rw [l11 X0 X2 X1]
  have l14 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l13 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 (X0 ◇ X2)]
  have l15 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l14 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X2 (X0 ◇ X0)]
  have l16 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X0 X1 X2]
    conv => enter [1]; rw [l5 X0 X1 X2]
  have l17 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l15 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h53869 X0 X1]
  have l18 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l17 X0 X1 X2]
    conv => enter [1]; rw [← l16 X0 X1 X2]
  have l19 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l18 X0 X1 X2]
    conv => enter [1]; rw [← l0 X0 X1 X2]
  intro x y z
  conv => enter [1]; rw [l19 x y z]

theorem Equation4512_53812_54164_implies_Equation53810 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53812 : Equation53812 G) (h54164 : Equation54164 G) : Equation53810 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l5 sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l6 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l8 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h53812 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l3 sK0 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h53812 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [l7 sK0 (sK0 ◇ sK0)]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h53812 sK0 X0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l10 sK0 X0]
  have l12 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [← h54164 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l13 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l8 sK0]
    conv => enter [1]; rw [← l1 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l14 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l12 sK0]
  have l15 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [← l5 sK0]
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1, 2]; rw [l5 sK0]
  have l16 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l5 sK0]
    conv => enter [1]; rw [l11 sK0 X0]
  have l17 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h53812 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l14 sK0]
  have l18 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l19 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [← l18 sK0]
  have l20 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h54164 (sK0 ◇ sK0) X0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l16 sK0 X0]
    conv => enter [1]; rw [l21 sK0 X0]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l22 sK0 X0]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l20 sK0]
    conv => enter [1]; rw [l23 sK0 X0]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l25 x y]

theorem Equation4512_53809_53900_implies_Equation53832 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53809 : Equation53809 G) (h53900 : Equation53900 G) : Equation53832 G := by
  have l0 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53809 sK0 (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [l0 sK1 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l3 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53809 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l4 sK0 sK1]
  have l6 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h53900 sK1 (sK0 ◇ sK0)]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l7 sK0 sK1]
    conv => enter [1, 2]; rw [← l6 sK1 sK0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l8 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation4512_53812_54175_implies_Equation54186 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53812 : Equation53812 G) (h54175 : Equation54175 G) : Equation54186 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h53812 sK1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h53812 X0 X1]
  have l3 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [h53812 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (sK1 ◇ sK1))]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l5 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l1 sK1]
    conv => enter [1]; rw [← l0 sK1 sK1]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h53812 sK1 X0]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l3 sK1 X0]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l9 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l8 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l10 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l9 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X2]
  have l11 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ sK1) = (sK1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l6 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l12 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← l5 sK1]
    conv => enter [1]; rw [l11 sK1 X0 X1]
  have l13 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1, 2]; rw [l7 sK1 X0]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK1) (X0 ◇ (sK1 ◇ sK1))]
  have l14 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l7 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (X0 ◇ (sK1 ◇ sK1))]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l14 sK0 sK1 X0]
  have l16 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l13 sK2 sK1 X0]
  have l17 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 2]; rw [l16 sK2 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK1)) (X0 ◇ (sK1 ◇ sK1))]
  have l18 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1]; rw [l17 sK0 sK2 sK1 X0]
  have l19 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h54175 X0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
  have l20 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l19 X0 sK1]
    conv => enter [1, 2]; rw [l5 sK1]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l22 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l20 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ sK1) (sK1 ◇ sK1)]
  have l23 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l22 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l24 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l23 sK0 sK2 sK1]
    conv => enter [1]; rw [l18 sK0 sK2 sK1 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l23 sK0 sK2 sK1]
  have l25 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 sK1 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l23 sK0 sK2 sK1]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [l25 sK0 sK1 sK2]
  have l27 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 2]; rw [l24 sK0 sK2 sK1]
    conv => enter [1]; rw [h53812 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 2, 2]; rw [← l24 sK0 sK2 sK1]
  have l28 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l24 sK0 sK2 sK1]
    conv => enter [1]; rw [l27 sK0 sK2 sK1 X0]
  have l29 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l28 sK0 sK2 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← l26 sK0 sK1 sK2]
  have l30 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X0 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1, 2]; rw [l12 sK1 X0 X0]
    conv => enter [1]; rw [← l10 X0 (sK1 ◇ sK1) sK1]
  have l31 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK1
    conv => enter [1]; rw [l20 X0 sK1]
    conv => enter [1]; rw [l30 X0 sK1]
  have l32 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [l31 X0 sK1]
    conv => enter [1]; rw [l10 X0 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← l31 X0 sK1]
  have l33 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [l10 sK0 (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2, 2]; rw [← l31 sK0 sK1]
  have l34 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l33 sK0 sK1 (sK2 ◇ (sK1 ◇ sK1))]
  have l35 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l34 sK0 sK2 sK1]
  have l36 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l35 sK0 sK1 sK2]
    conv => enter [1]; rw [← l29 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l36 x y z]

theorem Equation4512_53809_53860_implies_Equation53866 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53809 : Equation53809 G) (h53860 : Equation53860 G) : Equation53866 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53809 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h53809 sK0 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ sK1) sK0]
  have l2 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l1 sK0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK2 ◇ sK1)) sK0]
  have l3 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ sK0) ◇ X0) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l2 sK0 sK2 sK1]
  have l4 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [l3 sK0 X0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) sK0 X0]
  have l5 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← l4 sK0 X0 sK2 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
  have l6 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ X0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← h53860 sK0 X0]
  have l7 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [h53809 (sK2 ◇ sK1) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK1) ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1)))]
  have l8 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [l7 sK0 sK2 sK1]
  have l9 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [h53809 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
  have l10 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l9 sK2 sK1]
  have l11 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [← l6 sK0 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK2 ◇ sK1) X0]
  have l12 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1]; rw [l11 sK0 sK2 sK1 X0]
  have l13 : ∀ sK0 sK2 sK1 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK1)))))) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1, 2]; rw [l0 (sK0 ◇ (sK2 ◇ sK1)) X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK2 ◇ sK1)) ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK1)))))]
  have l14 : ∀ sK0 sK2 sK1 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1]; rw [l13 sK0 sK2 sK1 X0 X1]
    conv => enter [1]; rw [← l12 sK0 sK2 sK1 (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK1))))]
  have l15 : ∀ sK0 sK2 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK2 ◇ sK1)) ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [l14 sK0 sK2 sK1 X0 X1]
  have l16 : ∀ sK0 sK2 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1]; rw [l12 sK0 sK2 sK1 (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [l15 sK0 sK2 sK1 X0 X1]
  have l17 : ∀ sK0 sK2 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1]; rw [← l6 sK0 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l16 sK0 sK2 sK1 X0 X1]
  have l18 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l17 sK0 sK2 sK1 (sK2 ◇ sK1) (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← h53809 (sK2 ◇ sK1) sK0]
  have l19 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l17 sK0 sK2 sK1 (sK0 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← l8 sK0 sK2 sK1]
  have l20 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l19 sK0 sK2 sK1]
    conv => enter [1]; rw [← l12 sK0 sK2 sK1 ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))]
  have l21 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 1]; rw [l20 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) X0]
  have l22 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l21 sK0 sK2 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK1) (sK2 ◇ sK1) X0]
  have l23 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 1]; rw [l18 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) X0]
  have l24 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ (((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l23 sK0 sK2 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK1) ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)) X0]
  have l25 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l24 sK0 sK2 sK1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 (sK2 ◇ sK1) (sK2 ◇ sK1) X0]
  have l26 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l25 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← l22 sK0 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
  have l27 : ∀ sK0 sK2 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK1) X0 X1]
    conv => enter [1]; rw [← l26 sK0 sK2 sK1 ((sK2 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK1))))]
  have l28 : ∀ sK0 sK2 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1]; rw [l27 sK0 sK2 sK1 X0 X1]
    conv => enter [1]; rw [← l26 sK0 sK2 sK1 (X0 ◇ (X1 ◇ (sK2 ◇ sK1)))]
  have l29 : ∀ sK0 sK2 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1]; rw [l18 sK0 sK2 sK1]
    conv => enter [1]; rw [l28 sK0 sK2 sK1 X0 X1]
  have l30 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l29 sK0 sK2 sK1 sK1 sK1]
    conv => enter [1, 2]; rw [← h53809 sK1 sK2]
  have l31 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l29 sK0 sK2 sK1 (sK2 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l10 sK2 sK1]
  have l32 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l31 sK0 sK2 sK1]
    conv => enter [1]; rw [← l26 sK0 sK2 sK1 (sK1 ◇ sK1)]
  have l33 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 1]; rw [l32 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) (sK1 ◇ sK1) X0]
  have l34 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ X0))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l33 sK0 sK2 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
  have l35 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 1]; rw [l30 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l36 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l35 sK0 sK2 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l37 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ X0)))) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l36 sK0 sK2 sK1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 X0]
  have l38 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l37 sK0 sK2 sK1 X0]
    conv => enter [1]; rw [← l34 sK0 sK2 sK1 (sK1 ◇ X0)]
  have l39 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l38 sK0 sK2 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h53809 sK1 sK0]
  have l40 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l30 sK0 sK2 sK1]
    conv => enter [1]; rw [← l39 sK0 sK2 sK1]
  have l41 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l40 sK0 sK2 sK1]
    conv => enter [1]; rw [← l38 sK0 sK2 sK1 (sK0 ◇ sK1)]
  have l42 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l6 sK0 sK2 sK1 sK1]
    conv => enter [1]; rw [← l41 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l42 x y z]

theorem Equation4512_54162_54186_implies_Equation54190 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54162 : Equation54162 G) (h54186 : Equation54186 G) : Equation54190 G := by
  have l0 : ∀ X0 X2 X1 X3 : G, (X0 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X3)) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := by
    intro X0 X2 X1 X3
    conv => enter [1]; rw [h4512 X0 (X2 ◇ (X1 ◇ X1)) X3]
    conv => enter [1, 1]; rw [← h54186 X0 X1 X2]
  have l1 : ∀ X0 X2 X1 X3 : G, (X0 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X3)) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := by
    intro X0 X2 X1 X3
    conv => enter [1]; rw [l0 X0 X2 X1 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X3]
  have l2 : ∀ X0 X2 X1 X3 : G, (X0 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X2 X1 X3
    conv => enter [1]; rw [l1 X0 X2 X1 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l3 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X0 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l2 X0 X2 X1 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X1 ◇ X1) X3]
  have l4 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X0 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l3 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 X3]
  have l5 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [h54186 X2 X1 X0]
    conv => enter [1, 2]; rw [h54162 X0 X1]
  have l6 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X1)) = (X2 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X2 X1 X0
    conv => enter [1]; rw [l5 X2 X1 X0]
    conv => enter [1]; rw [← l4 X2 X0 X1 X0]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

theorem Equation4512_53866_53873_implies_Equation53888 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53866 : Equation53866 G) (h53873 : Equation53873 G) : Equation53888 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [← h53866 sK0 X0 sK1]
  have l1 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK2 sK1 X0]
    conv => enter [1]; rw [← h53866 sK2 X0 sK1]
  have l2 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [l1 sK2 sK1 X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l0 sK0 sK1 X0]
  have l4 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l2 sK2 sK1 X0]
    conv => enter [1]; rw [h53866 sK2 X0 sK2]
    conv => enter [1, 2]; rw [← l2 sK2 sK1 X0]
  have l5 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ X1)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l2 sK2 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53866 sK2 X1 X0]
  have l6 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X1)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ X1) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l5 sK2 sK1 X0 X1]
    conv => enter [1]; rw [← l2 sK2 sK1 X1]
  have l7 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53866 sK0 X1 X0]
  have l8 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l7 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l3 sK0 sK1 X1]
  have l9 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l2 sK2 sK1 sK1]
    conv => enter [1]; rw [l4 sK2 sK1 sK1]
    conv => enter [1, 2]; rw [l2 sK2 sK1 sK1]
  have l10 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l2 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l4 sK2 sK1 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK2 sK1 (sK2 ◇ sK1)]
  have l11 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l10 sK2 sK1]
    conv => enter [1]; rw [← l2 sK2 sK1 (sK2 ◇ (sK2 ◇ sK1))]
  have l12 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l9 sK2 sK1]
    conv => enter [1]; rw [l11 sK2 sK1]
  have l13 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l12 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ sK1)) (sK2 ◇ (sK2 ◇ sK1))]
  have l14 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 1]; rw [l13 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) (sK2 ◇ (sK2 ◇ sK1)) X0]
  have l15 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l6 sK2 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK1]
  have l16 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK1)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l2 sK2 sK1 sK1]
    conv => enter [1]; rw [l15 sK2 sK1 sK0]
  have l17 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l16 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53873 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l19 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h53873 sK0 (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK2 ◇ sK1)) ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1)))]
  have l20 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ X0))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h53873 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (X0 ◇ X0))]
  have l21 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ X0))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l20 sK0 sK1 X0]
    conv => enter [1]; rw [← h53873 (sK0 ◇ sK1) X0]
  have l22 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l19 sK0 sK2 sK1]
    conv => enter [1]; rw [← l14 sK0 sK2 sK1 (sK2 ◇ (sK2 ◇ sK1))]
  have l23 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK1]
    conv => enter [1]; rw [l18 sK0 sK1]
  have l24 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l21 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ X0)]
  have l25 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l13 sK0 sK2 sK1]
    conv => enter [1]; rw [← l22 sK0 sK2 sK1]
  have l26 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 sK1 sK1]
    conv => enter [1]; rw [l23 sK0 sK1]
  have l27 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l25 sK0 sK2 sK1]
    conv => enter [1]; rw [← l3 sK0 sK1 (sK2 ◇ (sK2 ◇ sK1))]
  have l28 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1, 1]; rw [l27 sK0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK2 ◇ (sK2 ◇ sK1)) X0]
  have l29 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [← l8 sK0 sK1 (sK2 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1]; rw [← l28 sK0 sK2 sK1 X0]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ sK1)]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53866 (sK0 ◇ sK1) sK1 sK1]
    conv => enter [1, 2]; rw [← l26 sK0 sK1]
  have l32 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l24 sK0 sK1 sK1]
    conv => enter [1]; rw [l31 sK0 sK1]
  have l33 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l8 sK0 sK1 sK1 sK1]
    conv => enter [1]; rw [← l30 sK0 sK1]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [l32 sK0 sK1]
  have l35 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 sK1 sK1]
    conv => enter [1]; rw [l33 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l37 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1]; rw [l36 sK0 sK1]
  have l38 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l17 sK0 sK2 sK1]
    conv => enter [1]; rw [← l29 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK2]
  have l39 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [← l38 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l39 x y z]

theorem Equation4512_54174_54186_implies_Equation54181 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54174 : Equation54174 G) (h54186 : Equation54186 G) : Equation54181 G := by
  have l0 : ∀ X0 X2 X1 X3 : G, (X0 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X3)) = ((X0 ◇ (X1 ◇ X1)) ◇ X3) := by
    intro X0 X2 X1 X3
    conv => enter [1]; rw [h4512 X0 (X2 ◇ (X1 ◇ X1)) X3]
    conv => enter [1, 1]; rw [← h54186 X0 X1 X2]
  have l1 : ∀ X0 X2 X1 X3 : G, (X0 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X3)) = (X0 ◇ ((X1 ◇ X1) ◇ X3)) := by
    intro X0 X2 X1 X3
    conv => enter [1]; rw [l0 X0 X2 X1 X3]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X1) X3]
  have l2 : ∀ X0 X2 X1 X3 : G, (X0 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ X3)) = (X0 ◇ (X1 ◇ (X1 ◇ X3))) := by
    intro X0 X2 X1 X3
    conv => enter [1]; rw [l1 X0 X2 X1 X3]
    conv => enter [1, 2]; rw [← h4512 X1 X1 X3]
  have l3 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X0 ◇ (X2 ◇ ((X1 ◇ X1) ◇ X3))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [← l2 X0 X2 X1 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X1 ◇ X1) X3]
  have l4 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ X3))) = (X0 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X3)))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l3 X0 X1 X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 X3]
  have l5 : ∀ X1 sK0 X0 : G, ((X1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) = ((X1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h54174 (X1 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2, 2]; rw [← h54186 X0 sK0 X1]
  have l6 : ∀ sK2 sK0 : G, ((sK2 ◇ sK2) ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h54186 sK2 sK0 sK2]
  have l7 : ∀ X1 sK0 X0 : G, ((X1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l5 X1 sK0 X0]
    conv => enter [1]; rw [← h4512 X1 (sK0 ◇ sK0) (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l8 : ∀ X1 sK0 X0 : G, ((X1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l7 X1 sK0 X0]
    conv => enter [1]; rw [← l4 X1 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l9 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) = ((X1 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro X1 X0 sK0
    conv => enter [1, 2]; rw [h54186 X0 sK0 X0]
    conv => enter [1]; rw [← l8 X1 sK0 X0]
  have l10 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X1 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l9 X1 X0 sK0]
    conv => enter [1]; rw [← h4512 X1 (sK0 ◇ sK0) (X0 ◇ X0)]
  have l11 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [h54186 X1 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l10 X1 X0 sK0]
  have l12 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [l11 X1 X0 sK0]
    conv => enter [1]; rw [← h54186 X1 sK0 X0]
  have l13 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ X0)) = ((sK2 ◇ sK2) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [h54174 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [← h54186 X0 sK2 X0]
  have l14 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h54186 sK0 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l15 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (X0 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h54186 (sK2 ◇ sK2) sK2 X0]
    conv => enter [1]; rw [← l13 sK2 X0]
  have l16 : ∀ sK2 sK0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l12 (sK2 ◇ sK2) sK2 sK0]
  have l17 : ∀ sK2 sK0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l16 sK2 sK0]
    conv => enter [1]; rw [l6 sK2 sK0]
  have l18 : ∀ sK0 sK2 : G, ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l17 sK2 sK0]
  have l19 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h54186 sK0 sK0 sK2]
    conv => enter [1]; rw [← l18 sK0 sK2]
  have l20 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l14 sK0 sK2]
    conv => enter [1]; rw [← l19 sK0 sK2]
  have l21 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h54186 sK0 sK0 sK1]
    conv => enter [1]; rw [← l20 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← l21 x z y]

theorem Equation4512_53866_53897_implies_Equation53913 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53866 : Equation53866 G) (h53897 : Equation53897 G) : Equation53913 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK2 ◇ sK1))]
  have l1 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) X0]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) X0]
    conv => enter [1, 1]; rw [← l0 sK0 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l4 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l3 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0]
  have l5 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [h53866 sK0 X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [← l4 sK0 sK1 sK2 X0]
  have l6 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [← h53866 sK0 X0 sK1]
  have l7 : ∀ sK1 sK2 X0 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK1 (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [← h53866 sK1 X0 (sK2 ◇ sK1)]
  have l8 : ∀ sK0 sK1 sK2 X1 X0 : G, (sK0 ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X1 ◇ X0)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [l5 sK0 ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X1 ◇ X0)) sK1 sK2]
    conv => enter [1, 2]; rw [← h53866 (sK1 ◇ (sK2 ◇ sK1)) X0 X1]
  have l9 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (X1 ◇ X0)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l5 sK0 ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) sK1 sK2]
    conv => enter [1]; rw [← l8 sK0 sK1 sK2 X1 X0]
  have l10 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1]; rw [l7 sK1 sK2 X0]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l6 sK0 sK1 X0]
  have l12 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h53866 X0 sK1 sK2]
    conv => enter [1]; rw [h53866 X0 (sK2 ◇ sK1) sK1]
  have l13 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) = (sK0 ◇ (sK0 ◇ (X1 ◇ X0))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l9 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h53866 sK0 (X1 ◇ X0) (sK1 ◇ (sK2 ◇ sK1))]
  have l14 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l13 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l11 sK0 sK1 (X1 ◇ X0)]
  have l15 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l11 sK0 sK1 ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)]
    conv => enter [1]; rw [l14 sK0 sK1 sK2 X0 X1]
  have l16 : ∀ sK0 X0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X1 ◇ X0)) := by
    intro sK0 X0 sK1 X1
    conv => enter [1]; rw [l5 sK0 X0 sK1 sK0]
    conv => enter [1]; rw [l15 sK0 sK1 sK0 X0 X1]
  have l17 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l11 sK0 sK1 X0]
    conv => enter [1]; rw [l16 sK0 X0 sK1 X1]
  have l18 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l10 sK1 sK2 X0]
    conv => enter [1]; rw [h53866 sK1 X0 sK1]
    conv => enter [1, 2]; rw [← l10 sK1 sK2 X0]
  have l19 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l10 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53866 sK1 X1 X0]
  have l20 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X1) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l19 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l10 sK1 sK2 X1]
  have l21 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l11 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l22 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l10 sK1 sK2 (sK2 ◇ sK1)]
    conv => enter [1]; rw [l18 sK1 sK2 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [l10 sK1 sK2 (sK2 ◇ sK1)]
  have l23 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [← h4512 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [h53897 sK2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [h4512 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
  have l24 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [h53897 sK0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l0 sK0 sK1 sK2]
  have l25 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ (X0 ◇ sK1))) = (sK1 ◇ (X0 ◇ (X0 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l10 sK1 sK2 (X0 ◇ (X0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h53897 X0 sK1]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1 sK2]
    conv => enter [1]; rw [← h53897 (sK1 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l27 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h53866 (sK1 ◇ (sK2 ◇ sK1)) (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [← l26 sK0 sK1 sK2]
  have l28 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ (X0 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h53897 X0 sK1]
    conv => enter [1]; rw [← l25 sK1 sK2 X0]
  have l29 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l24 sK0 sK1 sK2]
    conv => enter [1]; rw [l20 sK1 sK2 (sK0 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK2 ◇ sK1))]
  have l30 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l23 sK2 sK1]
    conv => enter [1]; rw [l20 sK1 sK2 sK2 ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l31 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l22 sK1 sK2]
    conv => enter [1]; rw [h53897 sK1 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l22 sK1 sK2]
  have l32 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l27 sK1 sK2 sK0]
    conv => enter [1]; rw [← l11 sK0 sK1 ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l33 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ sK1)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l28 X0 sK1 sK2]
    conv => enter [1]; rw [l20 sK1 sK2 X0 (X0 ◇ sK1)]
  have l34 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l29 sK0 sK1 sK2]
    conv => enter [1]; rw [l10 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1))]
  have l35 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l20 sK1 sK2 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l30 sK2 sK1]
  have l36 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l32 sK1 sK2 sK0]
    conv => enter [1]; rw [← l5 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1 sK2]
  have l37 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l33 X0 sK1 sK2]
    conv => enter [1]; rw [l20 sK1 sK2 X0 sK1]
  have l38 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l22 sK1 sK2]
    conv => enter [1]; rw [← l34 sK0 sK1 sK2]
  have l39 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l10 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [l35 sK1 sK2]
  have l40 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l36 sK1 sK2 sK0]
  have l41 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l22 sK1 sK2]
    conv => enter [1]; rw [l39 sK1 sK2]
  have l42 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l40 sK0 sK1 sK2]
    conv => enter [1]; rw [← h53866 (sK1 ◇ (sK2 ◇ sK1)) sK1 sK0]
  have l43 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l42 sK0 sK1 sK2]
    conv => enter [1]; rw [l37 (sK1 ◇ (sK2 ◇ sK1)) sK1 sK2]
  have l44 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l31 sK1 sK2]
    conv => enter [1]; rw [← l1 sK2 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l45 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l44 sK2 sK1]
    conv => enter [1]; rw [← h53866 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1)) sK1]
  have l46 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l45 sK2 sK1]
    conv => enter [1]; rw [← l12 (sK2 ◇ sK1) sK1 sK2]
  have l47 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l46 sK2 sK1]
    conv => enter [1]; rw [l37 (sK2 ◇ sK1) sK1 sK2]
  have l48 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l47 sK2 sK1]
    conv => enter [1]; rw [← l43 sK0 sK1 sK2]
  have l49 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [h53897 sK0 sK1]
    conv => enter [1]; rw [← l10 sK1 sK2 (sK0 ◇ (sK0 ◇ sK1))]
  have l50 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h53897 sK0 sK1]
    conv => enter [1]; rw [h53897 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← h53897 sK0 sK1]
  have l51 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1]; rw [← l50 sK1 sK0]
  have l52 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53897 sK0 sK1]
    conv => enter [1]; rw [l49 sK1 sK0 sK2]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53897 sK0 sK1]
    conv => enter [1]; rw [← l51 sK0 sK1]
  have l54 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l52 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l55 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l54 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [l20 sK1 sK2 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l56 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l22 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l57 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h53897 sK1 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l56 sK2 sK1]
  have l58 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l57 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
  have l59 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l58 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l60 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l55 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [l59 sK1 sK2 X0]
  have l61 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l41 sK1 sK2]
    conv => enter [1]; rw [h53897 sK2 ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l41 sK1 sK2]
  have l62 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l61 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1)) (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))]
  have l63 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l62 sK2 sK1]
    conv => enter [1]; rw [← l60 sK0 sK1 (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) sK2]
  have l64 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l63 sK2 sK1 sK0]
    conv => enter [1]; rw [← l17 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) sK2]
  have l65 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l21 sK0 sK1 sK2]
    conv => enter [1]; rw [← l64 sK2 sK1 sK0]
  have l66 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l65 sK0 sK1 sK2]
    conv => enter [1]; rw [l48 sK2 sK1 sK0]
  have l67 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [← l66 sK0 sK1 sK2]
  have l68 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l67 sK0 sK1 sK2]
    conv => enter [1]; rw [← l38 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l68 x y z]

theorem Equation4512_53812_54013_54050_implies_Equation54088 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53812 : Equation53812 G) (h54013 : Equation54013 G) (h54050 : Equation54050 G) : Equation54088 G := by
  have l0 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK1 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) X0]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54050 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54050 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK1 ◇ sK0)]
  have l3 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54050 (sK0 ◇ (sK1 ◇ sK0)) sK2]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ (sK1 ◇ sK0)) (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) (sK1 ◇ sK0) X0]
  have l6 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h53812 (sK1 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK1]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l1 sK1 sK0]
    conv => enter [1]; rw [l6 sK1 sK0 X0]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [l1 sK1 sK0]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l4 sK0 sK1]
  have l10 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l9 sK1 sK0]
  have l11 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [l1 sK1 sK0]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l11 sK1 sK0]
  have l13 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [← l12 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
  have l14 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l13 sK2 sK0 sK1]
  have l15 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l7 sK0 sK1 sK2]
  have l16 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← l15 sK0 sK1 sK2]
  have l17 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l16 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ (sK1 ◇ sK0)) (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l18 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l17 sK2 sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 sK1 sK2]
  have l19 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK2 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l16 sK0 sK1 sK2]
    conv => enter [1]; rw [← l18 sK2 sK0 sK1]
  have l20 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0))]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54013 sK0 sK1]
    conv => enter [1]; rw [← l4 sK0 sK1]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [l12 sK0 sK1]
  have l23 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ (sK1 ◇ sK0)) (sK1 ◇ sK0)]
  have l24 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l23 sK2 sK0 sK1]
    conv => enter [1]; rw [← l14 sK2 sK0 sK1]
  have l25 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l24 sK2 sK0 sK1]
    conv => enter [1]; rw [← l20 sK0 sK1 sK2]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← l25 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l26 x y z]

theorem Equation4512_53809_54020_54021_implies_Equation54022 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53809 : Equation53809 G) (h54020 : Equation54020 G) (h54021 : Equation54021 G) : Equation54022 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK2]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK2 X0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53809 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h53809 X0 X1]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l5 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l7 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h53809 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53809 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [h53809 sK0 sK1]
  have l10 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [h53809 sK0 sK1]
  have l11 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l10 sK0 X0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l8 sK1 sK0]
  have l14 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l11 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0)]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← l14 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0))]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l16 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [← l17 sK0 sK1]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h53809 sK0 sK1]
    conv => enter [1]; rw [l18 sK0 sK1]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l13 sK1 sK0]
  have l21 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l20 sK0 sK1]
  have l22 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l23 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [l22 sK1 sK0]
  have l24 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ sK0) X0]
  have l25 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l24 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
  have l26 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [l25 sK0 sK1 X0]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l23 sK1 sK0]
  have l28 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ (sK1 ◇ sK0))]
    conv => enter [1]; rw [← l27 sK0 sK1]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54020 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54020 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) (sK0 ◇ sK0)]
  have l31 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [← l21 sK0 sK1]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l33 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l31 sK0 sK1]
  have l34 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK0 X0]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1, 2]; rw [← l33 sK0 sK1]
  have l36 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = (((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK0)) (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 1]; rw [← l33 sK0 sK1]
  have l37 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l36 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK0)) sK0 X0]
  have l38 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1, 2]; rw [← l32 sK0 sK1]
  have l39 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l34 sK0 sK1 X0]
    conv => enter [1]; rw [← l37 sK0 sK1 X0]
  have l40 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h53809 sK0 X0]
    conv => enter [1]; rw [← l34 sK0 sK1 (sK0 ◇ (X0 ◇ sK0))]
  have l41 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l40 sK0 sK1 X0]
    conv => enter [1]; rw [← l34 sK0 sK1 (X0 ◇ sK0)]
  have l42 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l34 sK0 sK1 sK2]
  have l43 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l26 sK0 sK1 sK0]
    conv => enter [1]; rw [l41 sK0 sK1 X0]
  have l44 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l39 sK0 sK1 sK0]
    conv => enter [1]; rw [l43 sK0 sK1 X0]
  have l45 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [l44 sK0 sK1 X0]
  have l46 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l45 sK0 sK1 sK2]
    conv => enter [1]; rw [← l1 sK0 sK1 sK2 sK0]
  have l47 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l46 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK0 X0]
  have l48 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l42 sK0 sK1 sK2]
    conv => enter [1]; rw [l39 sK0 sK1 (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [← l42 sK0 sK1 sK2]
  have l49 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54021 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK0]
    conv => enter [1, 2, 2]; rw [← l46 sK0 sK1 sK2]
  have l50 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l47 sK0 sK1 (sK0 ◇ (sK1 ◇ sK0)) sK2]
    conv => enter [1]; rw [← l49 sK0 sK1 sK2]
  have l51 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l50 sK0 sK1 sK2]
    conv => enter [1]; rw [← l47 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) sK2]
  have l52 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l48 sK0 sK1 sK2]
    conv => enter [1]; rw [← l51 sK0 sK1 sK2]
  have l53 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [← l52 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l53 x y z]

theorem Equation4512_53812_54023_implies_Equation54013 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53812 : Equation53812 G) (h54023 : Equation54023 G) : Equation54013 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54023 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X1 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h54023 X0 X1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X2 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l4 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ X0) X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h53812 X0 X1]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l7 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l10 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l9 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l11 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l10 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X2]
  have l12 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h54023 X0 X1]
    conv => enter [1]; rw [← l11 X1 X0 X0]
  have l13 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l6 X0 X1 X2]
    conv => enter [1]; rw [← l11 X1 (X0 ◇ X2) X0]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l12 X0 X1]
    conv => enter [1]; rw [← l3 X1 X0 X0]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X1 X0
    conv => enter [1]; rw [h54023 X1 X0]
    conv => enter [1]; rw [← l14 X1 X0]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l15 X1 X0]
    conv => enter [1]; rw [← l6 X1 X0 (X0 ◇ X1)]
  have l17 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X1]
    conv => enter [1]; rw [l13 X0 X1 X0]
  have l18 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = (X0 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l17 X0 X1]
    conv => enter [1]; rw [l11 X0 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l17 X0 X1]
  intro x y
  conv => enter [1]; rw [l18 x y]

theorem Equation4512_53809_54023_implies_Equation54020 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53809 : Equation53809 G) (h54023 : Equation54023 G) : Equation54020 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54023 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X1 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h54023 X0 X1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X2 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l4 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ X0) X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l7 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53809 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l8 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h54023 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h53809 X0 X1]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h53809 X0 X1]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l11 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 (X0 ◇ (X0 ◇ X0))]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l10 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l13 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l11 X1 X0]
    conv => enter [1, 2]; rw [← h53809 X0 X0]
  have l14 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l12 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [← l13 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 (X0 ◇ (X1 ◇ X0))]
  have l16 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l14 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l17 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l15 X1 X0]
    conv => enter [1]; rw [← l6 X1 X0 X0]
  have l18 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l7 X0 X1 X2]
    conv => enter [1]; rw [← l6 X1 X0 (X2 ◇ X0)]
  have l19 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X1 X1]
    conv => enter [1, 2]; rw [← l17 X0 X1]
  have l20 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0 X0]
    conv => enter [1, 2]; rw [← l6 X0 X0 X1]
  have l21 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [h54023 X1 X0]
    conv => enter [1]; rw [l20 X1 X0]
  have l22 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2]; rw [l18 X0 X1 X1]
    conv => enter [1]; rw [← l3 X1 X0 X1]
  have l23 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0 (X1 ◇ X1)]
    conv => enter [1, 2]; rw [← l19 X0 X1]
  have l24 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) := by
    intro X1 X0
    conv => enter [1]; rw [l21 X1 X0]
    conv => enter [1]; rw [← l23 X1 X0]
  have l25 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l24 X1 X0]
    conv => enter [1]; rw [l22 X1 X0]
  intro x y
  conv => enter [1]; rw [l25 x y]

theorem Equation4512_53812_53860_54023_implies_Equation53870 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53812 : Equation53812 G) (h53860 : Equation53860 G) (h54023 : Equation54023 G) : Equation53870 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h53812 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1 X2]
    conv => enter [1]; rw [← h53860 X0 X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l3 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X2]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0 X0]
    conv => enter [1, 2]; rw [← h54023 X0 X1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation4512_53809_54023_54175_implies_Equation54172 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53809 : Equation53809 G) (h54023 : Equation54023 G) (h54175 : Equation54175 G) : Equation54172 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ (X1 ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X1 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h54023 X0 X1]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l0 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ X0) X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X2))) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l5 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h54023 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h53809 X0 X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0]
    conv => enter [1]; rw [← h54175 (X1 ◇ X0) X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← l6 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 (X0 ◇ (X1 ◇ X0))]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0 X0]
    conv => enter [1]; rw [← l8 X1 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [h54175 X1 X0]
    conv => enter [1]; rw [← l9 X1 X0]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation53812_54020_implies_Equation4269 (G : Type*) [Magma G] (h53812 : Equation53812 G) (h54020 : Equation54020 G) : Equation4269 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53812 sK0 X0]
    conv => enter [1]; rw [← h54020 sK0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation4512_53812_54020_implies_Equation54026 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53812 : Equation53812 G) (h54020 : Equation54020 G) : Equation54026 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h53812 X0 X1]
    conv => enter [1]; rw [← h54020 X0 X1]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X2 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [← l0 X2 (X0 ◇ X1)]
  intro x y z
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1]; rw [← l1 x y z]

theorem Equation4512_53812_54020_implies_Equation54034 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53812 : Equation53812 G) (h54020 : Equation54020 G) : Equation54034 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h53812 X0 X1]
    conv => enter [1]; rw [← h54020 X0 X1]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X2 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [← l0 X2 (X0 ◇ X1)]
  intro x y z
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1]; rw [← l1 x z y]

theorem Equation4512_53812_54020_implies_Equation53818 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53812 : Equation53812 G) (h54020 : Equation54020 G) : Equation53818 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53812 sK0 X0]
    conv => enter [1]; rw [← h54020 sK0 X0]
  have l1 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l0 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation4512_53809_54013_implies_Equation4269 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53809 : Equation53809 G) (h54013 : Equation54013 G) : Equation4269 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53809 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l2 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54013 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

theorem Equation4512_53809_54013_implies_Equation54026 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53809 : Equation53809 G) (h54013 : Equation54013 G) : Equation54026 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h53809 X0 X1]
    conv => enter [1]; rw [← h54013 X0 X1]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X2 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [← l0 X2 (X0 ◇ X1)]
  intro x y z
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1]; rw [← l1 x y z]

theorem Equation4512_53809_54013_implies_Equation54034 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53809 : Equation53809 G) (h54013 : Equation54013 G) : Equation54034 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h53809 X0 X1]
    conv => enter [1]; rw [← h54013 X0 X1]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X2 ◇ X2)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [← l0 X2 (X0 ◇ X1)]
  intro x y z
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1]; rw [← l1 x z y]

theorem Equation53812_53900_implies_Equation53921 (G : Type*) [Magma G] (h53812 : Equation53812 G) (h53900 : Equation53900 G) : Equation53921 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h53812 sK1 X0]
    conv => enter [1]; rw [← h53900 X0 sK1]
  have l1 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h53812 sK1 sK2]
    conv => enter [1]; rw [l0 sK1 X0]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

theorem Equation4512_53809_54164_implies_Equation54167 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53809 : Equation53809 G) (h54164 : Equation54164 G) : Equation54167 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53809 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h53809 sK0 sK1]
    conv => enter [1]; rw [h53809 sK0 sK0]
    conv => enter [1, 2]; rw [h53809 sK0 sK1]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) X0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h53809 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2, 2]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← h54164 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h53809 X0 X1]
    conv => enter [1]; rw [← h54164 X0 X1]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l5 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1]
  have l10 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l6 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l9 sK0 sK1]
  have l11 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l10 X0 sK0 sK1]
    conv => enter [1]; rw [l6 X0 sK2]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK2 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l11 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l12 x z y]

theorem Equation4512_53812_53899_implies_Equation53826 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53812 : Equation53812 G) (h53899 : Equation53899 G) : Equation53826 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK1 ◇ sK1)]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK1 ◇ sK1))]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l4 sK0 sK1]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l7 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l9 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l10 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l9 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1, 2]; rw [← l8 sK0 sK1]
  have l12 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l6 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)]
    conv => enter [1, 2]; rw [l10 sK1 sK0 X0]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53812 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l1 sK0 sK0]
  have l14 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53812 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
  have l15 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1, 2]; rw [← l2 sK0]
  have l16 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l16 sK0]
  have l18 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l17 sK0]
  have l19 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h53812 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l20 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53812 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l21 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 (X0 ◇ (sK0 ◇ sK0)) X1]
    conv => enter [1, 1]; rw [← h53812 sK0 X0]
  have l22 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [← l21 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l23 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l20 sK0]
    conv => enter [1]; rw [h53812 (sK0 ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← l20 sK0]
  have l24 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1]; rw [l23 sK0 X0]
  have l25 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK0) ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l24 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X1]
  have l26 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l25 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l27 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h53812 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK1)]
  have l28 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← h53812 sK1 sK0]
    conv => enter [1]; rw [l7 sK1 (sK1 ◇ sK1)]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h53812 sK1 sK0]
    conv => enter [1]; rw [h53812 sK1 sK1]
    conv => enter [1, 2]; rw [h53812 sK1 sK0]
  have l30 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [← h53812 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l31 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l28 sK1 sK0]
    conv => enter [1]; rw [← l30 sK1 sK0 (sK1 ◇ sK1)]
  have l32 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 sK0]
    conv => enter [1]; rw [← l31 sK1 sK0]
  have l33 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h53812 sK1 sK0]
    conv => enter [1]; rw [l32 sK1 sK0]
  have l34 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1, 2]; rw [← l29 sK1 sK0]
  have l35 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l29 sK1 sK0]
    conv => enter [1]; rw [l7 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l36 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l29 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l37 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l35 sK1 sK0]
    conv => enter [1]; rw [← l30 sK1 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l38 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l33 sK1 sK0]
    conv => enter [1]; rw [l37 sK1 sK0]
  have l39 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l38 sK1 sK0]
    conv => enter [1]; rw [h53812 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 2, 2]; rw [← l38 sK1 sK0]
  have l40 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l38 sK1 sK0]
    conv => enter [1]; rw [l39 sK1 sK0 X0]
  have l41 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [l34 sK0 sK1]
  have l42 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l41 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) X0]
  have l43 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X1)) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X1) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X1]
    conv => enter [1, 1]; rw [← l40 sK1 sK0 X0]
  have l44 : ∀ sK1 sK0 X1 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X1) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X1))) := by
    intro sK1 sK0 X1 X0
    conv => enter [1]; rw [← l43 sK1 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) X1]
  have l45 : ∀ sK0 X0 : G, ((sK0 ◇ X0) ◇ ((sK0 ◇ X0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53899 (sK0 ◇ X0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l1 sK0 X0]
  have l46 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53899 (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [l11 sK0 sK1]
  have l47 : ∀ sK1 X0 : G, ((sK1 ◇ X0) ◇ ((sK1 ◇ X0) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ X0) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)))) := by
    intro sK1 X0
    conv => enter [1]; rw [h53899 (sK1 ◇ X0) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l7 sK1 X0]
  have l48 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53899 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ ((X1 ◇ X2) ◇ X0))]
  have l49 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l48 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 X2 X0]
  have l50 : ∀ sK1 X0 : G, ((sK1 ◇ X0) ◇ ((sK1 ◇ X0) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l47 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))]
  have l51 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l46 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l52 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ X0) ◇ ((sK0 ◇ X0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l26 sK0 X0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← l45 sK0 X0]
  have l53 : ∀ sK1 X0 : G, ((sK1 ◇ X0) ◇ ((sK1 ◇ X0) ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))))) := by
    intro sK1 X0
    conv => enter [1]; rw [l50 sK1 X0]
    conv => enter [1]; rw [l7 sK1 (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)))]
  have l54 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l51 sK1 sK0]
    conv => enter [1]; rw [← l12 sK0 sK1 ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))))]
  have l55 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (X0 ◇ ((sK0 ◇ X0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l52 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 X0 ((sK0 ◇ X0) ◇ (sK0 ◇ sK0))]
  have l56 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ X0) ◇ ((sK1 ◇ X0) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l53 sK1 X0]
    conv => enter [1]; rw [← l30 sK1 sK0 (X0 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)))]
  have l57 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l54 sK1 sK0]
    conv => enter [1]; rw [← l49 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK0) (sK0 ◇ (sK1 ◇ sK1))]
  have l58 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0 (sK0 ◇ X0)]
    conv => enter [1]; rw [← l55 sK0 X0]
  have l59 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ X0) ◇ ((sK1 ◇ X0) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l56 sK1 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l30 sK1 sK0 X0]
  have l60 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l57 sK1 sK0]
    conv => enter [1]; rw [l42 sK0 sK1 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ sK1)))]
  have l61 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ X0) ◇ ((sK1 ◇ X0) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l44 sK1 sK0 X0 X0]
    conv => enter [1]; rw [← l59 sK1 X0 sK0]
  have l62 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l60 sK1 sK0]
  have l63 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (sK1 ◇ (X0 ◇ ((sK1 ◇ X0) ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l61 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 sK1 X0 ((sK1 ◇ X0) ◇ (sK1 ◇ sK1))]
  have l64 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l62 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l65 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l63 sK1 sK0 X0]
    conv => enter [1]; rw [← l27 sK1 X0 (sK1 ◇ X0)]
  have l66 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l64 sK0 sK1]
    conv => enter [1]; rw [← l36 sK1 sK0 ((sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l67 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h53812 sK1 sK0]
    conv => enter [1]; rw [← l65 sK1 sK0 X0]
  have l68 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l66 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK0 ◇ sK0))]
  have l69 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l68 sK0 sK1]
    conv => enter [1]; rw [← l44 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK1]
  have l70 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l67 sK1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l69 sK0 sK1]
  have l71 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l58 sK0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l70 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l71 x y]

theorem Equation4512_53809_54201_implies_Equation53826 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53809 : Equation53809 G) (h54201 : Equation54201 G) : Equation53826 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l6 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l5 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [l6 sK0]
  have l8 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l9 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ X2)) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h53809 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l10 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h53809 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l11 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [h53809 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l4 sK0]
  have l12 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53809 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l13 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h53809 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l3 sK0 (sK0 ◇ sK0)]
  have l14 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = ((X0 ◇ (X0 ◇ X0)) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h53809 X0 X1]
  have l15 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53809 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h53809 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (X0 ◇ sK0))]
  have l17 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h53809 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ sK1)]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h53809 (sK0 ◇ sK0) X0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l18 sK0 X0]
  have l20 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l17 sK1 X0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ sK0)]
  have l22 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l15 sK0 X0]
  have l23 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ ((X0 ◇ X0) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l14 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X2]
  have l24 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [← l1 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))]
  have l25 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l26 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l27 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l28 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53809 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l29 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l19 sK0 X0]
    conv => enter [1]; rw [l8 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l30 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l20 sK1 X0]
  have l31 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l21 sK0 X0]
  have l32 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l22 sK0 X0]
  have l33 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ (X0 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l23 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X2]
  have l34 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1, 2]; rw [← l6 sK0]
    conv => enter [1]; rw [l24 sK0]
    conv => enter [1, 2]; rw [l6 sK0]
  have l35 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l25 sK0]
    conv => enter [1]; rw [← l4 sK0]
  have l36 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l26 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l37 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l27 sK0]
  have l38 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l8 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l29 sK0 X0]
  have l39 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 sK0]
    conv => enter [1]; rw [l31 sK0 X0]
  have l40 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l33 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l41 : ∀ sK0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l34 sK0]
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l42 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l35 sK0]
  have l43 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l36 sK0]
  have l44 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l37 sK0]
  have l45 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l6 sK0]
    conv => enter [1]; rw [l38 sK0 X0]
  have l46 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l39 sK0 X0]
  have l47 : ∀ X0 X2 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l40 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l48 : ∀ sK0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l41 sK0]
  have l49 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l43 sK0]
  have l50 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l45 sK0 X0]
  have l51 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l42 sK0]
    conv => enter [1]; rw [l46 sK0 X0]
  have l52 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l49 sK0]
    conv => enter [1]; rw [l50 sK0 X0]
  have l53 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l42 sK0]
    conv => enter [1]; rw [l52 sK0 X0]
  have l54 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l28 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l55 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l42 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l56 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l44 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l57 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l49 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l58 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l32 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l59 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ sK0) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l51 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (X0 ◇ sK0) X1]
  have l60 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l59 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X1]
  have l61 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ ((X0 ◇ sK1) ◇ X1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (X0 ◇ sK1) X1]
    conv => enter [1, 1]; rw [← l30 sK1 X0]
  have l62 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ ((X0 ◇ sK1) ◇ X1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l61 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X1]
  have l63 : ∀ sK1 X1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ X1))) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [← l62 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK1 X1]
  have l64 : ∀ sK0 X0 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))))) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53809 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l53 sK0 X0]
  have l65 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK0) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l53 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) X1]
  have l66 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l65 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (X0 ◇ (sK0 ◇ sK0)) X1]
  have l67 : ∀ sK0 X0 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l64 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (X0 ◇ (sK0 ◇ sK0)) (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l68 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l66 sK0 X1 X0]
    conv => enter [1]; rw [← l56 sK0 ((X0 ◇ (sK0 ◇ sK0)) ◇ X1)]
  have l69 : ∀ sK0 X0 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l67 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l70 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X1))) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l68 sK0 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) X1]
  have l71 : ∀ sK0 X0 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l69 sK0 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (X0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l72 : ∀ sK0 X0 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l71 sK0 X0]
    conv => enter [1]; rw [← l70 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) X0]
  have l73 : ∀ sK0 X0 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l72 sK0 X0]
    conv => enter [1]; rw [← l57 sK0 ((X0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l74 : ∀ sK0 X0 : G, (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l73 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l75 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l70 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l74 sK0 X0]
  have l76 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l75 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (X0 ◇ (sK0 ◇ sK0)) (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))))]
  have l77 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l76 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK0) (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))))]
  have l78 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l77 sK0 X0]
    conv => enter [1]; rw [← l70 sK0 (((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) X0]
  have l79 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l78 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) (X0 ◇ (sK0 ◇ sK0)) ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l80 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l79 sK0 X0]
    conv => enter [1]; rw [← l57 sK0 ((X0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))))]
  have l81 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((X0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l80 sK0 X0]
    conv => enter [1]; rw [← h54201 (X0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
  have l82 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1]; rw [l81 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l83 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l82 sK0 X0]
    conv => enter [1, 2]; rw [← l48 sK0]
  have l84 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l49 sK0]
    conv => enter [1]; rw [l83 sK0 X0]
    conv => enter [1, 2]; rw [← l49 sK0]
  have l85 : ∀ sK0 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1)) := by
    intro sK0 X1 X0
    conv => enter [1, 1]; rw [l84 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l86 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53809 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l54 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l87 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l86 sK0 X0]
  have l88 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l55 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l87 sK0 X0]
  have l89 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l6 sK0]
    conv => enter [1]; rw [l88 sK0 X0]
  have l90 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l44 sK0]
    conv => enter [1]; rw [l89 sK0 X0]
  have l91 : ∀ X0 sK0 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) = ((X0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h53809 (X0 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l90 sK0 X0]
  have l92 : ∀ X0 sK0 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l91 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) ((X0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l93 : ∀ X0 sK0 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l92 X0 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l94 : ∀ X0 sK0 : G, ((X0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l93 X0 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l44 sK0]
  have l95 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((X0 ◇ (sK0 ◇ sK0)) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1, 2, 2]; rw [l84 sK0 X0]
    conv => enter [1]; rw [← l94 X0 sK0]
  have l96 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((X0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l95 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK0) ((X0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l97 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l96 X0 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (sK0 ◇ sK0) (X0 ◇ (sK0 ◇ sK0))]
  have l98 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l97 X0 sK0]
    conv => enter [1, 2, 2]; rw [← h54201 (sK0 ◇ sK0) X0]
  have l99 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l98 X0 sK0]
    conv => enter [1, 2]; rw [l3 sK0 (X0 ◇ X0)]
  have l100 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l99 X0 sK0]
    conv => enter [1, 2]; rw [← l55 sK0 (X0 ◇ X0)]
  have l101 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l100 X0 sK0]
    conv => enter [1]; rw [← l85 sK0 (X0 ◇ X0) X0]
  have l102 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l44 sK0]
    conv => enter [1]; rw [l101 X0 sK0]
  have l103 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l84 sK0 X0]
    conv => enter [1]; rw [l102 X0 sK0]
  have l104 : ∀ X0 sK0 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [h53809 (X0 ◇ X0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l103 sK0 X0]
  have l105 : ∀ X0 sK0 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l104 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 X0 ((X0 ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l106 : ∀ X0 sK0 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l105 X0 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l107 : ∀ X0 sK0 : G, ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l106 X0 sK0]
    conv => enter [1]; rw [← l47 X0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l108 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0 sK0
    conv => enter [1, 2, 2]; rw [l84 sK0 X0]
    conv => enter [1]; rw [← l107 X0 sK0]
  have l109 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l108 X0 sK0]
    conv => enter [1]; rw [← h4512 X0 X0 ((X0 ◇ X0) ◇ (X0 ◇ X0))]
  have l110 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l9 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← l109 X0 sK0]
  have l111 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l110 X0 sK0]
    conv => enter [1, 2]; rw [← l84 sK0 X0]
  have l112 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l111 X0 sK0]
    conv => enter [1]; rw [← l84 sK0 X0]
  have l113 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l112 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l114 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ X0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 (X0 ◇ (sK0 ◇ X0))]
    conv => enter [1, 2]; rw [← h54201 X0 sK0]
  have l115 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ X0))) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (X0 ◇ (sK1 ◇ X0))]
    conv => enter [1, 2]; rw [← h54201 X0 sK1]
  have l116 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l58 sK0 X0 sK0]
    conv => enter [1]; rw [← l114 sK0 X0]
  have l117 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l63 sK1 X0 X0]
    conv => enter [1]; rw [l115 sK1 X0]
  have l118 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l116 sK0 X0]
    conv => enter [1]; rw [← l60 sK0 X0 X0]
  have l119 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l113 sK0 X0 sK1]
    conv => enter [1]; rw [l117 sK1 X0]
  have l120 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l118 sK0 X0]
    conv => enter [1]; rw [l119 sK0 X0 sK1]
  intro x y
  conv => enter [1]; rw [l120 x y x]

theorem Equation4512_53809_54201_implies_Equation53833 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53809 : Equation53809 G) (h54201 : Equation54201 G) : Equation53833 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) sK1 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 sK1]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK1]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ X0)) = (((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK0)) sK1 X0]
    conv => enter [1, 1]; rw [l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK1) X0]
  have l9 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0
    conv => enter [1]; rw [h53809 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l4 sK0]
  have l10 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53809 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53809 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53809 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l13 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l12 sK0 X0]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l11 sK0 sK1]
  have l15 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l10 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l16 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l9 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l17 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l13 sK0 X0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l14 sK0 sK1]
  have l19 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [← l4 sK0]
  have l20 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l19 sK0]
  have l22 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l20 sK0]
  have l23 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l22 sK0]
  have l24 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [h54201 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h54201 (sK0 ◇ X0) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l1 sK0 X0]
  have l26 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h54201 (sK1 ◇ X0) (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [l8 sK0 sK1 X0]
  have l27 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h54201 (X0 ◇ X1) X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54201 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK0]
  have l29 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54201 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h54201 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l3 sK0 sK1 ((sK0 ◇ sK0) ◇ sK1)]
  have l31 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l30 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK1]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l28 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK1) sK0]
  have l33 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l27 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l34 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK1 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0))))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l26 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0))]
  have l35 : ∀ sK0 X0 : G, ((sK0 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l25 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l36 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l24 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ (X1 ◇ X2)))]
  have l37 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l31 sK1 sK0]
    conv => enter [1]; rw [← h54201 (sK0 ◇ sK1) sK0]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l32 sK0 sK1]
  have l39 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0))))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l34 sK1 X0 sK0]
    conv => enter [1]; rw [l8 sK0 sK1 (X0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)))]
  have l40 : ∀ sK0 X0 : G, ((sK0 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l35 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))]
  have l41 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = (X1 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l36 X2 X0 X1]
    conv => enter [1]; rw [l33 X0 X1 X2]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l29 sK1 sK0]
  have l43 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK1) ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l39 sK1 X0 sK0]
    conv => enter [1]; rw [l33 (sK0 ◇ sK0) (sK0 ◇ sK1) X0]
  have l44 : ∀ sK0 X0 : G, ((sK0 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l40 sK0 X0]
    conv => enter [1]; rw [← h54201 X0 (sK0 ◇ (sK0 ◇ sK0))]
  have l45 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = (X1 ◇ (X2 ◇ (X0 ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l41 X2 X0 X1]
  have l46 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l37 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l47 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l43 sK1 X0 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l48 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l23 sK0]
    conv => enter [1]; rw [← l44 sK0 X0]
  have l49 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ X0))) = (X2 ◇ (X1 ◇ (X0 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h54201 X2 X0]
    conv => enter [1]; rw [l45 X1 X0 X2]
  have l50 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l46 sK0 sK1]
    conv => enter [1, 2]; rw [← l21 sK0]
  have l51 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ X0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l47 sK1 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l21 sK0]
  have l52 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l48 X0 sK0]
    conv => enter [1]; rw [← h4512 sK0 X0 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))]
  have l53 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l51 sK1 X0 sK0]
    conv => enter [1]; rw [← h4512 sK1 X0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l54 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro X0 sK0
    conv => enter [1]; rw [l52 X0 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l55 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l53 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l23 sK0]
  have l56 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l54 X0 sK0]
    conv => enter [1, 2, 2]; rw [← l21 sK0]
  have l57 : ∀ sK0 sK1 : G, (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54201 ((sK0 ◇ sK1) ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [← l18 sK0 sK1]
  have l58 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 ((sK0 ◇ sK1) ◇ sK0) X0]
  have l59 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l58 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l60 : ∀ sK0 sK1 : G, (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK0)) = (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l57 sK0 sK1]
    conv => enter [1]; rw [← l56 ((sK0 ◇ sK1) ◇ sK0) sK0]
  have l61 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (((sK0 ◇ sK1) ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← l60 sK0 sK1]
  have l62 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l61 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 (sK0 ◇ sK0)]
  have l63 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l62 sK0 sK1]
    conv => enter [1]; rw [l49 (sK0 ◇ sK1) sK0 sK0]
  have l64 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l59 sK0 sK0 sK1]
    conv => enter [1]; rw [← l63 sK0 sK1]
  have l65 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l64 sK0 sK1]
    conv => enter [1]; rw [l55 sK0 sK1 sK0]
  have l66 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l65 sK0 sK1]
    conv => enter [1, 2]; rw [← l21 sK0]
  have l67 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l66 sK0 sK1]
  have l68 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0]
    conv => enter [1]; rw [l67 sK0 sK1]
  have l69 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK1)) sK0]
  have l70 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [l69 sK1 sK0]
  have l71 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l42 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK0)]
  have l72 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l71 sK0 sK1]
    conv => enter [1]; rw [l50 sK0 sK1]
  have l73 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l68 sK0 sK1]
    conv => enter [1]; rw [← l72 sK0 sK1]
  have l74 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l73 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK0 ◇ sK1))]
  have l75 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l74 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l76 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l70 sK1 sK0]
  have l77 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l76 sK0 sK1]
    conv => enter [1]; rw [← l75 sK0 sK1 sK1]
  have l78 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53809 sK1 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2, 2]; rw [← l77 sK0 sK1]
  have l79 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l78 sK1 sK0]
    conv => enter [1, 2]; rw [← l68 sK0 sK1]
  have l80 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l68 sK0 sK1]
    conv => enter [1]; rw [← l79 sK1 sK0]
  have l81 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l80 sK0 sK1]
    conv => enter [1]; rw [h53809 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l81 x y]

theorem Equation4512_53812_53897_implies_Equation53934 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53812 : Equation53812 G) (h53897 : Equation53897 G) : Equation53934 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53812 (sK0 ◇ (sK0 ◇ sK1)) sK2]
    conv => enter [1, 2]; rw [h4512 sK2 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h53897 sK0 sK1]
    conv => enter [1]; rw [h53897 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← h53897 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53897 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0]
    conv => enter [1, 2]; rw [← h53897 sK0 sK1]
  have l3 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h53812 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2, 2]; rw [← l2 sK0 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 sK1 X0]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l3 sK2 sK0 sK1]
  have l7 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1, 1]; rw [l3 sK2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
  have l9 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l8 sK0 sK1 sK2]
    conv => enter [1]; rw [h53897 (sK0 ◇ (sK0 ◇ sK1)) (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l8 sK0 sK1 sK2]
  have l10 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l7 sK2 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l9 sK0 sK1 sK2]
  have l11 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [← l10 sK2 sK0 sK1]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l11 sK0 sK1 sK2]
    conv => enter [1]; rw [← l3 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

theorem Equation4512_53812_53897_implies_Equation53832 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53812 : Equation53812 G) (h53897 : Equation53897 G) : Equation53832 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l3 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h53812 sK0 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l4 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [← l2 sK0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l6 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l8 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h53812 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [h53897 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l1 sK0 (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← h53897 X0 (sK0 ◇ sK0)]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0 X0]
    conv => enter [1]; rw [← l10 sK0 X0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 X0]
    conv => enter [1]; rw [← l7 sK0 (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← l12 sK0 X0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l13 sK0 X0]
    conv => enter [1]; rw [← h53897 X0 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l14 x y]

theorem Equation4512_53809_54174_54175_implies_Equation54176 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53809 : Equation53809 G) (h54174 : Equation54174 G) (h54175 : Equation54175 G) : Equation54176 G := by
  have l0 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ sK2) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK2)]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) sK2]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l4 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK2) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h53809 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 sK1]
  have l5 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h53809 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ sK1)]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l5 sK1 X0]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) sK1]
  have l8 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h53809 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l9 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l6 sK1 X0]
  have l10 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l7 sK1 sK2]
  have l11 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l10 sK1 sK2]
  have l12 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l8 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l13 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l12 sK1 X0]
  have l14 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1, 1]; rw [l11 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) sK1 X0]
  have l15 : ∀ sK1 X0 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l14 sK1 X0 sK2]
  have l16 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l9 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l17 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h54174 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l11 sK1 sK2]
  have l18 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ X0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [← h54174 X0 sK1]
  have l19 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (X0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (X0 ◇ X0))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (X0 ◇ (X0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h54174 sK1 X0]
  have l20 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ (X0 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l19 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ X0)]
  have l21 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l15 sK1 (sK1 ◇ sK1) sK2]
    conv => enter [1]; rw [← l17 sK1 sK2]
  have l22 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l16 sK1 X0 X0]
    conv => enter [1]; rw [l20 sK1 X0]
  have l23 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l21 sK1 sK2]
  have l24 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l13 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l23 sK1 sK2]
  have l25 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l8 sK1]
    conv => enter [1]; rw [l24 sK1 sK2]
  have l26 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l25 sK1 sK2]
  have l27 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l8 sK1]
    conv => enter [1]; rw [l26 sK1 sK2]
  have l28 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h54174 sK2 sK1]
  have l29 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l28 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK1)]
  have l30 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [← l29 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2))]
  have l31 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l27 sK1 sK2]
    conv => enter [1]; rw [← l30 sK1 sK2]
  have l32 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l31 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ sK1)]
  have l33 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [h54174 (sK1 ◇ sK2) sK1]
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l34 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1, 2]; rw [← h54174 (sK1 ◇ sK2) sK1]
  have l35 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l34 sK1 sK2]
  have l36 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l33 sK1 sK2]
    conv => enter [1, 2]; rw [← l15 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK2]
  have l37 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l35 sK1 sK2]
    conv => enter [1]; rw [← l15 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK2]
  have l38 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l36 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l39 : ∀ sK1 sK2 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l38 sK1 sK2]
    conv => enter [1]; rw [← l13 sK1 (sK1 ◇ (sK1 ◇ sK2))]
  have l40 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l37 sK1 sK2]
    conv => enter [1]; rw [← l39 sK1 sK2]
  have l41 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l40 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 sK2 (sK1 ◇ sK1)]
  have l42 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l32 sK1 sK2]
    conv => enter [1]; rw [← l41 sK1 sK2]
  have l43 : ∀ sK1 X0 sK2 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1, 1]; rw [l42 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK1) X0]
  have l44 : ∀ sK1 X0 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l43 sK1 X0 sK2]
  have l45 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [← l18 (sK1 ◇ sK2) sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) ((sK1 ◇ sK1) ◇ (sK1 ◇ sK2))]
  have l46 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l44 sK1 (sK1 ◇ sK2) sK2]
    conv => enter [1]; rw [← l45 sK1 sK2]
  have l47 : ∀ sK1 sK2 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l46 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ sK1)]
  have l48 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l42 sK1 sK2]
    conv => enter [1]; rw [← l47 sK1 sK2]
  have l49 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l48 sK1 sK2]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK2)]
  have l50 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l49 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK2))]
  have l51 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l50 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK2))]
  have l52 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l51 sK0 sK1 sK2]
  have l53 : ∀ sK0 sK1 X0 sK2 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l52 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l54 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) sK1 X0]
    conv => enter [1]; rw [l53 sK0 sK1 X0 sK2]
  have l55 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l22 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (X0 ◇ X0)]
  have l56 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l55 sK0 sK1 X0]
  have l57 : ∀ sK0 sK1 X1 X0 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ X1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l56 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK1)) (X0 ◇ X0) X1]
  have l58 : ∀ sK0 sK1 X1 X0 : G, (((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) ◇ X1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l57 sK0 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l59 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) sK1 X1]
    conv => enter [1]; rw [l58 sK0 sK1 X1 X0]
  have l60 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X0))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (X0 ◇ X0)]
    conv => enter [1]; rw [h54175 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l61 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l59 sK0 sK1 X0 X0]
    conv => enter [1]; rw [← l60 sK0 sK1 X0]
  have l62 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l61 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) (X0 ◇ X0)]
  have l63 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l56 sK0 sK1 X0]
    conv => enter [1]; rw [← l62 sK0 sK1 X0]
  have l64 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54175 sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 sK1]
  have l65 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l63 sK0 sK1 ((sK1 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK2) X0]
  have l66 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l64 sK0 sK1]
    conv => enter [1]; rw [l65 sK0 sK1 sK2 X0]
  have l67 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK1)) ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l66 sK0 sK1 sK2 X0]
  have l68 : ∀ sK0 sK1 X1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X1 sK2 X0
    conv => enter [1]; rw [← l67 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) X0 X1]
  have l69 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l54 sK0 sK1 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← l68 sK0 sK1 X1 sK0 X0]
  have l70 : ∀ sK0 sK1 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l63 sK0 sK1 (sK0 ◇ X1)]
    conv => enter [1]; rw [l69 sK0 sK1 sK0 X1]
  have l71 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l64 sK0 sK1]
    conv => enter [1]; rw [l70 sK0 sK1 X1]
  have l72 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l71 sK0 sK1 sK2]
    conv => enter [1]; rw [← l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l72 x y z]

end Semigroup5
