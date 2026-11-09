import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_54291_implies_Equation54180 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54291 : Equation54291 G) : Equation54180 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l1 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l2 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ X0))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← l0 sK2 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l3 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [← l2 sK2 X0]
    conv => enter [1]; rw [← h54291 X0 sK2 sK2 (sK2 ◇ sK2)]
  have l4 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [← l3 sK2 sK2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 sK2]
  have l5 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l4 sK2]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ sK2)]
  have l6 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)))) := by
    intro sK2
    conv => enter [1, 2]; rw [l5 sK2]
    conv => enter [1]; rw [l0 sK2 ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))]
  have l7 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l6 sK2]
    conv => enter [1]; rw [← h54291 (sK2 ◇ sK2) (sK2 ◇ sK2) sK2 (sK2 ◇ sK2)]
  have l8 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [← l3 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← l7 sK2]
  have l9 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l8 sK2]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ sK2)]
  have l10 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) := by
    intro sK2
    conv => enter [1]; rw [l5 sK2]
    conv => enter [1]; rw [← l9 sK2]
  have l11 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l10 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK2) (sK2 ◇ sK2)]
  have l12 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 1]; rw [l10 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
  have l13 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [l12 sK2 X0]
    conv => enter [1]; rw [l3 sK2 X0]
  have l14 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2]
    conv => enter [1]; rw [l11 sK1 sK2]
  have l15 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [l13 sK2 X0]
  have l16 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 ((sK2 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [l15 sK2 X0]
  have l17 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [← l3 sK2 X0]
    conv => enter [1]; rw [l16 sK2 X0]
  have l18 : ∀ sK2 sK1 : G, ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) = (sK2 ◇ ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l17 sK1 sK2]
    conv => enter [1]; rw [l0 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l19 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l17 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l20 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l17 sK1 sK2]
    conv => enter [1]; rw [l19 sK2 sK1]
  have l21 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l15 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l18 sK2 sK1]
  have l22 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l20 sK1 sK2]
    conv => enter [1]; rw [← l21 sK1 sK2]
  have l23 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l22 sK1 sK2]
    conv => enter [1]; rw [← l14 sK1 sK2]
  have l24 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK1 ◇ (sK2 ◇ sK2)) ◇ sK2)) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h54291 (sK2 ◇ sK2) sK2 X0 sK1]
    conv => enter [1, 2]; rw [← l1 sK1 sK2]
  have l25 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [h54291 X0 sK2 X1 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK2 X0]
  have l26 : ∀ X0 sK2 X1 : G, (X0 ◇ (sK2 ◇ sK2)) = (X1 ◇ (sK2 ◇ ((sK2 ◇ sK2) ◇ X0))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [h54291 X0 sK2 X1 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l0 sK2 X0]
  have l27 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ (X1 ◇ X1)) = ((sK3 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [h54291 X0 X1 sK3 sK0]
    conv => enter [1]; rw [h4512 sK3 sK0 (X1 ◇ X0)]
  have l28 : ∀ X0 sK2 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2
    conv => enter [1]; rw [h54291 X0 (sK2 ◇ sK2) X0 sK2]
    conv => enter [1]; rw [← l26 X0 sK2 X0]
  have l29 : ∀ sK2 X0 sK1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l24 sK2 X0 sK1]
    conv => enter [1, 2]; rw [← l23 sK1 sK2]
  have l30 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ (X1 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [← h54291 sK0 sK3 X0 X1]
    conv => enter [1]; rw [l27 sK0 sK3 sK3 sK0]
  have l31 : ∀ sK2 X0 sK1 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [← l0 sK2 sK2]
    conv => enter [1]; rw [l29 sK2 X0 sK1]
  have l32 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [h54291 sK2 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l28 X0 sK2]
  have l33 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [← l15 sK2 sK2]
    conv => enter [1]; rw [l31 sK2 X0 sK1]
  have l34 : ∀ sK1 sK2 : G, (sK1 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l22 sK1 sK2]
    conv => enter [1]; rw [← l32 sK2 (sK1 ◇ (sK2 ◇ sK2))]
  have l35 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l34 sK1 sK2]
    conv => enter [1]; rw [l32 sK2 X0]
  have l36 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l34 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK2) X0]
  have l37 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l36 sK1 sK2 X0]
    conv => enter [1]; rw [← l25 X0 sK2 sK2]
  have l38 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l35 sK1 sK2 X0]
    conv => enter [1]; rw [← l37 sK1 sK2 X0]
  have l39 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l38 sK1 sK2 (sK1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h54291 X0 X1 (sK1 ◇ (sK2 ◇ sK2)) sK1]
  have l40 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK3 ◇ sK0) ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l39 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK3 sK0 sK0]
  have l41 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ sK0) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1, 2]; rw [l40 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK3 ◇ sK0) sK0]
  have l42 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l17 sK1 sK2]
    conv => enter [1]; rw [l41 sK2 sK1 sK3 sK0]
  have l43 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l42 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK3 ◇ sK0)) sK0]
  have l44 : ∀ sK2 sK1 sK3 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ sK0) := by
    intro sK2 sK1 sK3 sK0
    conv => enter [1]; rw [l33 sK2 sK1 sK1]
    conv => enter [1]; rw [l43 sK1 sK2 sK3 sK0]
  have l45 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l34 sK1 sK2]
    conv => enter [1]; rw [l44 sK2 sK1 sK3 sK0]
  have l46 : ∀ sK1 sK2 X0 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1, 1]; rw [l45 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) sK0 X0]
  have l47 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l38 sK1 sK2 X0]
    conv => enter [1]; rw [l46 sK1 sK2 X0 sK3 sK0]
  have l48 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l47 sK1 sK2 sK3 sK0 (sK3 ◇ sK0)]
    conv => enter [1]; rw [l30 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) sK0 sK3 sK0]
  have l49 : ∀ sK1 sK2 X0 sK3 sK0 : G, (sK1 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l48 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l30 X0 sK2 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l49 x y x z w]

@[equational_result]
theorem Equation54291_implies_Equation54222 (G : Type*) [Magma G] (h54291 : Equation54291 G) : Equation54222 G := by
  intro x y z
  conv => enter [1]; rw [h54291 x y y z]

@[equational_result]
theorem Equation54291_implies_Equation54239 (G : Type*) [Magma G] (h54291 : Equation54291 G) : Equation54239 G := by
  intro x y z
  conv => enter [1]; rw [h54291 x y z x]

theorem Equation4512_54291_implies_Equation54187 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54291 : Equation54291 G) : Equation54187 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ X0))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l0 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l1 sK1 X0]
    conv => enter [1]; rw [← h54291 X0 sK1 sK1 (sK1 ◇ sK1)]
  have l3 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l2 sK1 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l4 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l3 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1, 2]; rw [l4 sK1]
    conv => enter [1]; rw [l0 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l6 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1]
    conv => enter [1]; rw [← h54291 (sK1 ◇ sK1) (sK1 ◇ sK1) sK1 (sK1 ◇ sK1)]
  have l7 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l2 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l6 sK1]
  have l8 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l7 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK1)]
  have l9 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l4 sK1]
    conv => enter [1]; rw [← l8 sK1]
  have l10 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l9 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l11 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l10 sK1 X0]
    conv => enter [1]; rw [l2 sK1 X0]
  have l12 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l11 sK1 X0]
  have l13 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [l12 sK1 X0]
  have l14 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [← l2 sK1 X0]
    conv => enter [1]; rw [l13 sK1 X0]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [l16 sK1 sK0]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l12 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l15 sK1 sK0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← l18 sK0 sK1]
  have l20 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [h54291 X0 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK1 X0]
  have l21 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h54291 X0 (sK1 ◇ sK1) X0 sK1]
    conv => enter [1]; rw [← l20 X0 sK1 X0]
  have l22 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h54291 sK1 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l21 X0 sK1]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l22 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l24 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [l22 sK1 sK2]
    conv => enter [1]; rw [h54291 sK2 sK1 X0 sK2]
  have l25 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [l24 sK1 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l25 x y x z]

theorem Equation4512_54291_implies_Equation54241 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54291 : Equation54291 G) : Equation54241 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ X0))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l0 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← l1 sK1 X0]
    conv => enter [1]; rw [← h54291 X0 sK1 sK1 (sK1 ◇ sK1)]
  have l3 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l2 sK1 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l4 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l3 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1, 2]; rw [l4 sK1]
    conv => enter [1]; rw [l0 sK1 ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))]
  have l6 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l5 sK1]
    conv => enter [1]; rw [← h54291 (sK1 ◇ sK1) (sK1 ◇ sK1) sK1 (sK1 ◇ sK1)]
  have l7 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [← l2 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l6 sK1]
  have l8 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l7 sK1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK1)]
  have l9 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [l4 sK1]
    conv => enter [1]; rw [← l8 sK1]
  have l10 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l9 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
  have l11 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l10 sK1 X0]
    conv => enter [1]; rw [l2 sK1 X0]
  have l12 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l11 sK1 X0]
  have l13 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [l12 sK1 X0]
  have l14 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro X0 sK1
    conv => enter [1]; rw [← l2 sK1 X0]
    conv => enter [1]; rw [l13 sK1 X0]
  have l15 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [l16 sK1 sK0]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l12 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l15 sK1 sK0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← l18 sK0 sK1]
  have l20 : ∀ X0 sK1 X1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [h54291 X0 sK1 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l0 sK1 X0]
  have l21 : ∀ X0 sK1 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1
    conv => enter [1]; rw [h54291 X0 (sK1 ◇ sK1) X0 sK1]
    conv => enter [1]; rw [← l20 X0 sK1 X0]
  have l22 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [h54291 sK1 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l21 X0 sK1]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1]
    conv => enter [1]; rw [← l22 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l24 : ∀ sK1 X0 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 X0 sK0 sK2
    conv => enter [1]; rw [l22 sK1 sK2]
    conv => enter [1]; rw [h54291 sK2 sK1 X0 sK0]
  have l25 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l23 sK0 sK1]
    conv => enter [1]; rw [l24 sK1 X0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l25 x y z z]

theorem Equation4512_54291_implies_Equation53858 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54291 : Equation54291 G) : Equation53858 G := by
  have l0 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ X0)]
  have l1 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ sK2) ◇ (sK2 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [l0 sK2 X0]
  have l2 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
    conv => enter [1, 1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l3 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [l2 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ sK2)) X0]
  have l4 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ sK2) := by
    intro sK2
    conv => enter [1, 2]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK2) sK2]
  have l5 : ∀ sK2 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK2) (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l6 : ∀ sK2 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l5 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ (sK2 ◇ sK2))]
  have l7 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X0) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 1]; rw [l4 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK2)) sK2 X0]
  have l8 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1]; rw [l7 sK2 X0]
  have l9 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ X0))) := by
    intro sK2 X0
    conv => enter [1, 2]; rw [l1 sK2 X0]
    conv => enter [1]; rw [l3 sK2 (sK2 ◇ X0)]
  have l10 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ X0))) = ((sK2 ◇ sK2) ◇ (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0))) := by
    intro sK2 X0
    conv => enter [1]; rw [← l3 sK2 ((sK2 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [l3 sK2 X0]
  have l11 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ sK2) ◇ X0))) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [l10 sK2 X0]
    conv => enter [1]; rw [← l1 sK2 ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)]
  have l12 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) = (X0 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [l9 sK2 X0]
    conv => enter [1]; rw [← h54291 X0 sK2 sK2 (sK2 ◇ (sK2 ◇ sK2))]
  have l13 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) = (X0 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [← l11 sK2 X0]
    conv => enter [1]; rw [← h54291 X0 (sK2 ◇ sK2) sK2 (sK2 ◇ (sK2 ◇ sK2))]
  have l14 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) = (X0 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0
    conv => enter [1]; rw [l13 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l15 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2
    conv => enter [1]; rw [← l12 sK2 sK2]
    conv => enter [1, 2]; rw [← l4 sK2]
  have l16 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2
    conv => enter [1]; rw [← l12 sK2 (sK2 ◇ sK2)]
    conv => enter [1, 2]; rw [l6 sK2]
  have l17 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2)) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2
    conv => enter [1]; rw [l16 sK2]
    conv => enter [1]; rw [l3 sK2 (sK2 ◇ (sK2 ◇ sK2))]
  have l18 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l15 sK2]
    conv => enter [1]; rw [← l1 sK2 (sK2 ◇ (sK2 ◇ sK2))]
  have l19 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l17 sK2]
  have l20 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 1]; rw [l18 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK2)) (sK2 ◇ (sK2 ◇ sK2)) X0]
  have l21 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2
    conv => enter [1, 2]; rw [l19 sK2]
    conv => enter [1]; rw [← l1 sK2 ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2)))]
  have l22 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK2 ◇ (((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 1]; rw [l19 sK2]
    conv => enter [1]; rw [← h4512 sK2 ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2))) X0]
  have l23 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0))) := by
    intro sK2 X0
    conv => enter [1]; rw [l22 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK2)) (sK2 ◇ (sK2 ◇ sK2)) X0]
  have l24 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2
    conv => enter [1]; rw [l21 sK2]
    conv => enter [1]; rw [l14 sK2 (sK2 ◇ (sK2 ◇ sK2))]
  have l25 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X0) = (X0 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0
    conv => enter [1]; rw [l23 sK2 X0]
    conv => enter [1]; rw [← h54291 X0 (sK2 ◇ (sK2 ◇ sK2)) sK2 (sK2 ◇ (sK2 ◇ sK2))]
  have l26 : ∀ sK2 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2
    conv => enter [1]; rw [l24 sK2]
    conv => enter [1]; rw [← l8 sK2 (sK2 ◇ (sK2 ◇ sK2))]
  have l27 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X0) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [l25 sK2 X0]
    conv => enter [1, 2]; rw [← l18 sK2]
  have l28 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2
    conv => enter [1]; rw [l19 sK2]
    conv => enter [1]; rw [← l26 sK2]
  have l29 : ∀ sK2 X0 : G, (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK2 ◇ sK2)) X0]
    conv => enter [1]; rw [l27 sK2 X0]
  have l30 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l28 sK2]
    conv => enter [1]; rw [← l1 sK2 (sK2 ◇ (sK2 ◇ sK2))]
  have l31 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l18 sK2]
    conv => enter [1]; rw [← l30 sK2]
  have l32 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1, 2]; rw [l31 sK2]
    conv => enter [1]; rw [h4512 sK2 sK2 (sK2 ◇ (sK2 ◇ sK2))]
  have l33 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1, 1]; rw [l31 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ sK2)) X0]
  have l34 : ∀ sK2 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2
    conv => enter [1]; rw [l31 sK2]
    conv => enter [1]; rw [l32 sK2]
  have l35 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) = (((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1, 2]; rw [l20 sK2 X0]
    conv => enter [1]; rw [l12 sK2 ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)]
  have l36 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [l35 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK2)) X0 (sK2 ◇ sK2)]
  have l37 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [← l12 sK2 X0]
    conv => enter [1]; rw [l36 sK2 X0]
  have l38 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro sK2 X0
    conv => enter [1]; rw [← h4512 sK2 sK2 ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)]
    conv => enter [1, 2]; rw [l29 sK2 X0]
  have l39 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2
    conv => enter [1]; rw [← l12 sK2 X0]
    conv => enter [1]; rw [l38 sK2 X0]
  have l40 : ∀ sK2 X0 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [l33 sK2 X0]
    conv => enter [1]; rw [l29 sK2 X0]
  have l41 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) = (sK2 ◇ (X0 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2
    conv => enter [1]; rw [← l29 sK2 X0]
    conv => enter [1, 2]; rw [l40 sK2 X0]
  have l42 : ∀ X0 sK2 : G, (X0 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2
    conv => enter [1]; rw [l39 X0 sK2]
    conv => enter [1]; rw [← l41 X0 sK2]
  have l43 : ∀ X0 sK2 X1 : G, ((X0 ◇ (sK2 ◇ sK2)) ◇ X1) = (X0 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro X0 sK2 X1
    conv => enter [1, 1]; rw [l42 X0 sK2]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ (sK2 ◇ sK2)) X1]
  have l44 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = (X0 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [h4512 X0 (sK2 ◇ sK2) X1]
    conv => enter [1]; rw [l43 X0 sK2 X1]
  have l45 : ∀ X0 sK2 X1 : G, ((X0 ◇ (sK2 ◇ sK2)) ◇ X1) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ ((X0 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro X0 sK2 X1
    conv => enter [1, 1]; rw [l37 X0 sK2]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK2 ◇ sK2)) (X0 ◇ (sK2 ◇ sK2)) X1]
  have l46 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = ((sK2 ◇ (sK2 ◇ sK2)) ◇ (X0 ◇ ((sK2 ◇ sK2) ◇ X1))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [h4512 X0 (sK2 ◇ sK2) X1]
    conv => enter [1]; rw [l45 X0 sK2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK2 ◇ sK2) X1]
  have l47 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = (X1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l46 X0 sK2 X1]
    conv => enter [1]; rw [← h54291 X1 (sK2 ◇ sK2) (sK2 ◇ (sK2 ◇ sK2)) X0]
  have l48 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = (X1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l47 X0 sK2 X1]
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l49 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK2))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l48 X0 sK2 X1]
    conv => enter [1, 2]; rw [← l31 sK2]
  have l50 : ∀ X0 sK2 X1 : G, (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) = (X1 ◇ (sK2 ◇ sK2)) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l49 X0 sK2 X1]
    conv => enter [1]; rw [← l42 X1 sK2]
  have l51 : ∀ X0 sK2 X1 : G, ((X0 ◇ (sK2 ◇ sK2)) ◇ X1) = (sK2 ◇ ((X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X1)) := by
    intro X0 sK2 X1
    conv => enter [1, 1]; rw [l39 X0 sK2]
    conv => enter [1]; rw [← h4512 sK2 (X0 ◇ (sK2 ◇ (sK2 ◇ sK2))) X1]
  have l52 : ∀ X0 sK2 X1 : G, ((X0 ◇ (sK2 ◇ sK2)) ◇ X1) = (sK2 ◇ (X0 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X1))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l51 X0 sK2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK2 ◇ (sK2 ◇ sK2)) X1]
  have l53 : ∀ X0 sK2 X1 : G, ((X0 ◇ (sK2 ◇ sK2)) ◇ X1) = (X1 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l52 X0 sK2 X1]
    conv => enter [1]; rw [← h54291 X1 (sK2 ◇ (sK2 ◇ sK2)) sK2 X0]
  have l54 : ∀ X0 sK2 X1 : G, ((X0 ◇ (sK2 ◇ sK2)) ◇ X1) = (X1 ◇ ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2)))) := by
    intro X0 sK2 X1
    conv => enter [1]; rw [l53 X0 sK2 X1]
    conv => enter [1]; rw [← l44 X1 sK2 (sK2 ◇ (sK2 ◇ sK2))]
  have l55 : ∀ sK2 X0 X1 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = ((X0 ◇ (sK2 ◇ sK2)) ◇ X1) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← l50 X1 sK2 (sK2 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← l54 X0 sK2 X1]
  have l56 : ∀ sK2 X0 X1 : G, ((sK2 ◇ (sK2 ◇ sK2)) ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l55 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ sK2) X1]
  have l57 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (sK2 ◇ (sK2 ◇ sK2))) = (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [← l6 sK2]
    conv => enter [1]; rw [l56 sK2 X0 X1]
  have l58 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l34 sK2]
    conv => enter [1]; rw [l57 sK2 X0 X1]
  have l59 : ∀ X0 sK0 X1 sK1 : G, (X0 ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro X0 sK0 X1 sK1
    conv => enter [1]; rw [h54291 X0 sK0 X1 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 X0]
  have l60 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l58 sK2 sK2 (X1 ◇ X0)]
    conv => enter [1]; rw [← h54291 X0 X1 sK2 (sK2 ◇ sK2)]
  have l61 : ∀ X0 X1 sK4 sK1 sK0 : G, (X0 ◇ (X1 ◇ X1)) = ((sK4 ◇ (sK1 ◇ sK0)) ◇ (X1 ◇ X0)) := by
    intro X0 X1 sK4 sK1 sK0
    conv => enter [1]; rw [h54291 X0 X1 sK4 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4512 sK4 (sK1 ◇ sK0) (X1 ◇ X0)]
  have l62 : ∀ sK2 X1 sK1 sK0 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X1 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK2 X1 sK1 sK0 X0
    conv => enter [1]; rw [l60 sK2 X0 sK0]
    conv => enter [1]; rw [l59 X0 sK0 X1 sK1]
  have l63 : ∀ X0 X1 sK1 sK0 sK4 : G, (X0 ◇ (X1 ◇ (sK1 ◇ sK0))) = ((sK4 ◇ (sK1 ◇ sK0)) ◇ (sK1 ◇ sK0)) := by
    intro X0 X1 sK1 sK0 sK4
    conv => enter [1]; rw [← h54291 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l61 sK0 sK1 sK4 sK1 sK0]
  have l64 : ∀ sK2 sK4 sK1 sK0 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = ((sK4 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK2 sK4 sK1 sK0 X0
    conv => enter [1]; rw [l62 sK2 sK4 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK4 (sK1 ◇ sK0) X0]
  have l65 : ∀ sK2 X0 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK2 X0 sK4 sK1 sK0
    conv => enter [1]; rw [l64 sK2 sK4 sK1 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l63 X0 sK4 sK1 sK0 sK4]
  intro x y z w u
  conv => enter [1]; rw [l65 x y z w u]

@[equational_result]
theorem Equation54291_implies_Equation54273 (G : Type*) [Magma G] (h54291 : Equation54291 G) : Equation54273 G := by
  intro x y z
  conv => enter [1]; rw [h54291 x y z z]

theorem Equation4512_54291_implies_Equation53821 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54291 : Equation54291 G) : Equation53821 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l1 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l2 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l4 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [l1 sK1 X0]
    conv => enter [1]; rw [l3 sK1 (sK1 ◇ X0)]
  have l6 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = (X0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l5 sK1 X0]
    conv => enter [1]; rw [← h54291 X0 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l7 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← l6 sK1 sK1]
    conv => enter [1, 2]; rw [← l4 sK1]
  have l8 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l7 sK1]
    conv => enter [1]; rw [← l1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l9 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l8 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l10 : ∀ sK0 X0 sK3 X1 X2 : G, ((sK0 ◇ X0) ◇ (sK3 ◇ sK3)) = (X1 ◇ (X2 ◇ ((sK3 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 sK3 X1 X2
    conv => enter [1]; rw [h54291 (sK0 ◇ X0) sK3 X1 X2]
    conv => enter [1, 2, 2]; rw [h4512 sK3 sK0 X0]
  have l11 : ∀ sK1 X0 X1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1, 2]; rw [l8 sK1]
    conv => enter [1]; rw [h54291 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1)) X0 X1]
    conv => enter [1, 2, 2]; rw [← l8 sK1]
  have l12 : ∀ X0 X1 sK1 : G, (X0 ◇ (X1 ◇ X1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X1 ◇ X0)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h54291 X0 X1 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l9 sK1 (X1 ◇ X0)]
  have l13 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l8 sK1]
    conv => enter [1]; rw [l11 sK1 X0 X1]
  have l14 : ∀ sK0 X0 sK3 : G, ((sK0 ◇ X0) ◇ (sK3 ◇ sK3)) = (X0 ◇ ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0))) := by
    intro sK0 X0 sK3
    conv => enter [1]; rw [l10 sK0 X0 sK3 sK0 sK0]
    conv => enter [1]; rw [← h54291 X0 (sK3 ◇ sK0) sK0 sK0]
  have l15 : ∀ X0 X1 sK3 sK0 sK1 : G, (X0 ◇ (X1 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK3 ◇ sK0)) := by
    intro X0 X1 sK3 sK0 sK1
    conv => enter [1]; rw [← h54291 sK0 sK3 X0 X1]
    conv => enter [1]; rw [l12 sK0 sK3 sK1]
  have l16 : ∀ X0 sK3 sK0 : G, (X0 ◇ ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK3 ◇ sK3))) := by
    intro X0 sK3 sK0
    conv => enter [1]; rw [← l14 sK0 X0 sK3]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK3 ◇ sK3)]
  have l17 : ∀ X0 sK3 sK0 : G, (X0 ◇ ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0))) = (sK3 ◇ (sK3 ◇ sK3)) := by
    intro X0 sK3 sK0
    conv => enter [1]; rw [l16 X0 sK3 sK0]
    conv => enter [1]; rw [← h54291 sK3 sK3 sK0 X0]
  have l18 : ∀ X0 sK3 sK0 sK1 : G, (X0 ◇ ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK3 ◇ sK3)) := by
    intro X0 sK3 sK0 sK1
    conv => enter [1]; rw [l17 X0 sK3 sK0]
    conv => enter [1]; rw [l12 sK3 sK3 sK1]
  have l19 : ∀ X0 sK3 sK0 sK1 : G, (X0 ◇ ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK3 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK3 sK0 sK1
    conv => enter [1]; rw [l18 X0 sK3 sK0 sK1]
    conv => enter [1]; rw [l12 (sK1 ◇ (sK1 ◇ sK1)) sK3 sK1]
  have l20 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [l13 sK1 (sK1 ◇ (sK1 ◇ sK1)) sK3]
    conv => enter [1]; rw [← l19 X0 sK3 sK0 sK1]
  have l21 : ∀ sK1 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [l20 sK1 sK1 sK3 sK0]
    conv => enter [1]; rw [l15 sK1 (sK3 ◇ sK0) sK3 sK0 sK1]
  have l22 : ∀ sK1 X0 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK2 ◇ (sK3 ◇ sK0))) := by
    intro sK1 X0 sK2 sK3 sK0
    conv => enter [1]; rw [l21 sK1 sK3 sK0]
    conv => enter [1]; rw [← l15 X0 sK2 sK3 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l22 x x y z w]

theorem Equation4512_54291_implies_Equation53844 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54291 : Equation54291 G) : Equation53844 G := by
  have l0 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK2) (sK0 ◇ sK2)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK2 (sK0 ◇ sK2)]
  have l1 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h54291 (sK2 ◇ (sK0 ◇ sK2)) sK0 X0 sK2]
    conv => enter [1, 2]; rw [← l0 sK2 sK0]
  have l2 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ (X1 ◇ X1)) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ (X1 ◇ X0)) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [h54291 X0 X1 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK2) (X1 ◇ X0)]
  have l3 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l2 sK0 sK0 sK2 sK0]
    conv => enter [1]; rw [l1 sK2 sK0 X0]
  have l4 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0 sK2]
  have l5 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l4 sK0 sK0 sK2]
    conv => enter [1]; rw [← h54291 sK2 sK0 sK0 (sK2 ◇ (sK0 ◇ sK2))]
  have l6 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l5 sK0 sK2]
  have l7 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l6 sK0 sK2]
    conv => enter [1]; rw [h54291 sK2 sK0 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation4512_54291_implies_Equation53819 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54291 : Equation54291 G) : Equation53819 G := by
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
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l1 sK0 X0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ X0)]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [l3 sK0 X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [← h54291 X0 (sK0 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0) sK0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l7 sK0 X0]
    conv => enter [1]; rw [← h54291 X0 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l11 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [← l9 sK0 X0]
    conv => enter [1]; rw [← h54291 X0 (sK0 ◇ sK0) sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l12 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro X0 sK0
    conv => enter [1]; rw [l11 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l10 sK0 sK0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l14 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [← l10 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l6 sK0]
  have l15 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [l3 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l16 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l13 sK0]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l17 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l15 sK0]
    conv => enter [1]; rw [l12 sK0 sK0]
  have l18 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l19 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l18 sK0]
  have l20 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1, 2]; rw [l19 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK0))]
  have l21 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [l16 sK0]
    conv => enter [1]; rw [← l20 sK0]
  have l22 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l21 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l23 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l22 sK0]
    conv => enter [1]; rw [← l19 sK0]
  have l24 : ∀ X0 sK0 X1 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h54291 X0 (sK0 ◇ (sK0 ◇ sK0)) X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l10 sK0 X0]
  have l25 : ∀ X1 X0 sK0 : G, (X1 ◇ (X0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← l24 X0 sK0 X1]
    conv => enter [1, 2]; rw [← l16 sK0]
  have l26 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ ((X1 ◇ (sK0 ◇ sK0)) ◇ X2)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro X0 X1 sK0 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (sK0 ◇ sK0)) X2]
    conv => enter [1, 1]; rw [← h54291 sK0 sK0 X0 X1]
  have l27 : ∀ X0 X1 sK0 X2 : G, (X0 ◇ (X1 ◇ ((sK0 ◇ sK0) ◇ X2))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro X0 X1 sK0 X2
    conv => enter [1, 2]; rw [h4512 X1 (sK0 ◇ sK0) X2]
    conv => enter [1]; rw [l26 X0 X1 sK0 X2]
  have l28 : ∀ X2 sK0 : G, (X2 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro X2 sK0
    conv => enter [1]; rw [h54291 X2 (sK0 ◇ sK0) X2 X2]
    conv => enter [1]; rw [l27 X2 X2 sK0 X2]
  have l29 : ∀ sK0 X2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [← l25 X2 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l28 X2 sK0]
  have l30 : ∀ sK0 X2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [l29 sK0 X2]
  have l31 : ∀ sK0 X2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X2) := by
    intro sK0 X2
    conv => enter [1]; rw [l23 sK0]
    conv => enter [1]; rw [l30 sK0 X2]
  have l32 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l31 sK0 (sK0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h54291 X0 X1 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l33 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l32 sK0 sK1 sK2]
    conv => enter [1]; rw [h54291 sK1 sK2 X0 sK1]
  intro x y z
  conv => enter [1]; rw [l33 x x y z]

theorem Equation4512_53905_implies_Equation53878 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53905 : Equation53905 G) : Equation53878 G := by
  have l0 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK3 ◇ sK0) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1, 1]; rw [h4512 sK1 sK2 (sK3 ◇ sK0)]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK3 ◇ sK0) X0]
  have l1 : ∀ sK2 sK3 sK0 X0 X1 : G, (((sK2 ◇ (sK3 ◇ sK0)) ◇ X0) ◇ X1) = (sK2 ◇ (((sK3 ◇ sK0) ◇ X0) ◇ X1)) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK2 (sK3 ◇ sK0) X0]
    conv => enter [1]; rw [← h4512 sK2 ((sK3 ◇ sK0) ◇ X0) X1]
  have l2 : ∀ sK2 sK3 sK0 X0 X1 : G, (((sK2 ◇ (sK3 ◇ sK0)) ◇ X0) ◇ X1) = (sK2 ◇ ((sK3 ◇ sK0) ◇ (X0 ◇ X1))) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l1 sK2 sK3 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK3 ◇ sK0) X0 X1]
  have l3 : ∀ sK2 sK3 sK0 X0 X1 : G, (((sK2 ◇ (sK3 ◇ sK0)) ◇ X0) ◇ X1) = ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ sK2)) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l2 sK2 sK3 sK0 X0 X1]
    conv => enter [1]; rw [← h53905 (sK3 ◇ sK0) sK2 X0 X1]
  have l4 : ∀ sK2 sK3 sK0 X0 X1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ sK2)) := by
    intro sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK3 ◇ sK0)) X0 X1]
    conv => enter [1]; rw [l3 sK2 sK3 sK0 X0 X1]
  have l5 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ sK2)) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← l4 sK2 sK3 sK0 (sK1 ◇ sK2) (sK3 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 (sK3 ◇ sK0)]
  have l6 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (X0 ◇ X1)) = (sK1 ◇ ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK3 ◇ sK0)) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l4 sK2 sK3 sK0 X0 X1]
  have l7 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (X0 ◇ X1)) = ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l6 sK1 sK2 sK3 sK0 X0 X1]
    conv => enter [1]; rw [← h53905 (sK3 ◇ sK0) sK1 (sK3 ◇ sK0) sK2]
  have l8 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ ((sK3 ◇ sK0) ◇ sK2)) = ((sK1 ◇ sK2) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK3 sK0 ((sK3 ◇ sK0) ◇ sK2)]
    conv => enter [1, 2]; rw [← l4 sK2 sK3 sK0 sK1 sK2]
  have l9 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ ((sK3 ◇ sK0) ◇ sK2)) = (sK2 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK0) ((sK3 ◇ sK0) ◇ sK2)]
    conv => enter [1, 2]; rw [← l4 sK2 sK3 sK0 sK1 sK2]
  have l10 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ sK2)) = (sK2 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← l4 sK2 sK3 sK0 (sK3 ◇ sK0) sK2]
    conv => enter [1]; rw [l9 sK2 sK3 sK0 sK1]
  have l11 : ∀ sK3 sK0 sK1 sK2 : G, ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ sK1)) = ((sK1 ◇ sK2) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← l7 sK1 sK2 sK3 sK0 (sK3 ◇ sK0) sK2]
    conv => enter [1]; rw [l8 sK1 sK2 sK3 sK0]
  have l12 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (sK2 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [← l5 sK3 sK0 sK2 sK1]
    conv => enter [1]; rw [l10 sK3 sK0 sK2 sK1]
  have l13 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2)) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l4 sK2 sK3 sK0 sK1 sK2]
    conv => enter [1]; rw [l5 sK3 sK0 sK2 sK1]
  have l14 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [l13 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK3 ◇ sK0)) (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  have l15 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK3 ◇ sK0)) (sK1 ◇ sK2)]
    conv => enter [1]; rw [l14 sK1 sK2 sK3 sK0]
  have l16 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2))) = (sK1 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 sK2 ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l12 sK2 sK3 sK0 sK1]
  have l17 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l16 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ (sK3 ◇ sK0)) (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  have l18 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l17 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l15 sK1 sK2 sK3 sK0]
  have l19 : ∀ sK1 sK2 sK3 sK0 X0 : G, (((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ sK2) ◇ (((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1, 1]; rw [← l18 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2)) X0]
  have l20 : ∀ sK1 sK2 sK3 sK0 X0 : G, (((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ ((sK1 ◇ sK2) ◇ X0))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l19 sK1 sK2 sK3 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ (sK3 ◇ sK0)) (sK1 ◇ sK2) X0]
  have l21 : ∀ sK2 sK3 sK0 sK1 X0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2))) = (((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK2 sK3 sK0 sK1 X0
    conv => enter [1]; rw [h53905 (sK2 ◇ (sK3 ◇ sK0)) (sK1 ◇ sK2) (sK1 ◇ sK2) X0]
    conv => enter [1]; rw [← l20 sK1 sK2 sK3 sK0 X0]
  have l22 : ∀ sK2 sK3 sK0 sK1 X0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK2 sK3 sK0 sK1 X0
    conv => enter [1]; rw [l21 sK2 sK3 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) (sK1 ◇ sK2) X0]
  have l23 : ∀ sK3 sK0 sK1 sK2 : G, ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ sK1)) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← l7 sK1 sK2 sK3 sK0 (sK1 ◇ sK2) sK3]
    conv => enter [1]; rw [← l22 sK2 sK3 sK0 sK1 sK3]
  have l24 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ sK2)) = ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ sK1)) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← l4 sK2 sK3 sK0 (sK2 ◇ (sK3 ◇ sK0)) (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l23 sK3 sK0 sK1 sK2]
  have l25 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ sK2)) = ((sK1 ◇ sK2) ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [l24 sK3 sK0 sK2 sK1]
    conv => enter [1]; rw [l11 sK3 sK0 sK1 sK2]
  have l26 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ sK2)) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [l25 sK3 sK0 sK2 sK1]
    conv => enter [1]; rw [l18 sK1 sK2 sK3 sK0]
  have l27 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [← l5 sK3 sK0 sK2 sK1]
    conv => enter [1]; rw [l26 sK3 sK0 sK2 sK1]
  have l28 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l13 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l27 sK2 sK3 sK0 sK1]
  have l29 : ∀ X0 X1 sK1 sK2 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro X0 X1 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [h53905 X0 X1 (sK1 ◇ sK2) (sK3 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK2 (sK3 ◇ sK0)]
  have l30 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1, 2]; rw [← l18 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← h53905 (sK1 ◇ sK2) X0 (sK2 ◇ (sK3 ◇ sK0)) (sK1 ◇ sK2)]
  have l31 : ∀ sK3 sK0 X0 sK2 sK1 : G, ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ X0)) = (X0 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 X0 sK2 sK1
    conv => enter [1]; rw [h53905 (sK3 ◇ sK0) X0 (sK3 ◇ sK0) sK2]
    conv => enter [1, 2]; rw [← l4 sK2 sK3 sK0 sK1 sK2]
  have l32 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 sK2 sK1 X0 X1]
  have l33 : ∀ sK1 sK2 sK3 sK0 X0 X1 X2 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (X0 ◇ (X1 ◇ X2))) = ((sK1 ◇ sK2) ◇ (X0 ◇ (X0 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0 X0 X1 X2
    conv => enter [1]; rw [l0 sK1 sK2 sK3 sK0 (X0 ◇ (X1 ◇ X2))]
    conv => enter [1, 2]; rw [← h53905 X0 (sK3 ◇ sK0) X1 X2]
  have l34 : ∀ sK3 sK0 sK2 X0 : G, ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ sK2)) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1]; rw [← l4 sK2 sK3 sK0 X0 (sK3 ◇ sK3)]
    conv => enter [1]; rw [← h53905 X0 (sK2 ◇ (sK3 ◇ sK0)) sK3 sK3]
  have l35 : ∀ sK2 sK3 sK0 sK1 X0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0 sK1 X0
    conv => enter [1]; rw [← l5 sK3 sK0 sK2 sK1]
    conv => enter [1]; rw [l34 sK3 sK0 sK2 X0]
  have l36 : ∀ X0 sK1 sK2 sK3 sK0 X1 X2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 sK1 sK2 sK3 sK0 X1 X2
    conv => enter [1]; rw [h53905 X0 (sK1 ◇ sK2) X0 (sK3 ◇ sK0)]
    conv => enter [1]; rw [← l33 sK1 sK2 sK3 sK0 X0 X1 X2]
  have l37 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ sK2))) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l30 X0 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l32 sK1 sK2 (sK1 ◇ sK2) X0]
  have l38 : ∀ sK2 sK3 sK0 sK1 X0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0 sK1 X0
    conv => enter [1]; rw [l13 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l35 sK2 sK3 sK0 sK1 X0]
  have l39 : ∀ sK3 sK0 sK1 X0 sK2 : G, ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 sK1 X0 sK2
    conv => enter [1]; rw [← l7 sK1 sK2 sK3 sK0 X0 (sK3 ◇ sK3)]
    conv => enter [1]; rw [← l36 X0 sK1 sK2 sK3 sK0 sK3 sK3]
  have l40 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l37 X0 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l29 sK2 sK1 sK1 sK2 sK3 sK0]
  have l41 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [← l31 sK3 sK0 sK1 sK2 sK1]
    conv => enter [1]; rw [l39 sK3 sK0 sK1 X0 sK2]
  have l42 : ∀ X0 sK1 sK2 sK3 sK0 : G, (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l40 X0 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))]
  have l43 : ∀ sK1 sK2 sK3 sK0 X0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK3 ◇ sK0)) (sK1 ◇ sK2)]
    conv => enter [1]; rw [l41 sK1 sK2 sK3 sK0 X0]
  have l44 : ∀ X0 sK2 sK3 sK0 sK1 : G, (X0 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK2 sK3 sK0 sK1
    conv => enter [1, 2]; rw [l28 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l42 X0 sK1 sK2 sK3 sK0]
  have l45 : ∀ sK2 sK3 sK0 sK1 X0 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK3 sK0 sK1 X0
    conv => enter [1]; rw [l28 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l43 sK1 sK2 sK3 sK0 X0]
  have l46 : ∀ X0 X1 sK2 sK3 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK2 sK3 sK0 sK1
    conv => enter [1]; rw [h53905 X0 X1 X0 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [← l38 sK2 sK3 sK0 sK1 X0]
  have l47 : ∀ X0 X1 sK1 sK2 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro X0 X1 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l46 X0 X1 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l44 X1 sK2 sK3 sK0 sK1]
  have l48 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK3 ◇ sK0)) (sK1 ◇ sK2)]
    conv => enter [1, 2]; rw [l38 sK2 sK3 sK0 sK1 sK1]
  have l49 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l48 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l29 sK1 sK1 sK1 sK2 sK3 sK0]
  have l50 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l49 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [l47 sK1 sK1 sK1 sK2 sK3 sK0]
  have l51 : ∀ sK2 sK3 sK0 sK1 : G, ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [l28 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l50 sK1 sK2 sK3 sK0]
  have l52 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l38 sK2 sK3 sK0 sK1 sK1]
    conv => enter [1]; rw [l51 sK2 sK3 sK0 sK1]
  have l53 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l38 sK2 sK3 sK0 sK1 sK1]
    conv => enter [1]; rw [l45 sK2 sK3 sK0 sK1 sK1]
  have l54 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l45 sK2 sK3 sK0 sK1 sK1]
    conv => enter [1]; rw [l45 sK2 sK3 sK0 sK1 (sK2 ◇ (sK3 ◇ sK0))]
    conv => enter [1, 2]; rw [l45 sK2 sK3 sK0 sK1 sK1]
  have l55 : ∀ sK3 sK0 sK2 sK1 : G, ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 sK2 sK1
    conv => enter [1]; rw [← l4 sK2 sK3 sK0 sK1 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l54 sK1 sK2 sK3 sK0]
  have l56 : ∀ sK2 sK3 sK0 sK1 : G, (sK2 ◇ ((sK2 ◇ (sK3 ◇ sK0)) ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK3 sK0 sK1
    conv => enter [1]; rw [← l31 sK3 sK0 sK2 sK2 sK1]
    conv => enter [1]; rw [l55 sK3 sK0 sK2 sK1]
  have l57 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← l44 sK2 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l56 sK2 sK3 sK0 sK1]
  have l58 : ∀ X1 X0 X2 X3 sK1 sK2 sK3 sK0 : G, (X1 ◇ (X0 ◇ (X2 ◇ X3))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) := by
    intro X1 X0 X2 X3 sK1 sK2 sK3 sK0
    conv => enter [1]; rw [← h53905 X0 X1 X2 X3]
    conv => enter [1]; rw [l47 X0 X1 sK1 sK2 sK3 sK0]
  have l59 : ∀ sK1 sK2 sK3 sK0 X1 X0 X2 X3 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro sK1 sK2 sK3 sK0 X1 X0 X2 X3
    conv => enter [1]; rw [l52 sK1 sK2 sK3 sK0]
    conv => enter [1]; rw [← l58 X1 X0 X2 X3 sK1 sK2 sK3 sK0]
  have l60 : ∀ X1 X0 X2 X3 sK1 sK2 : G, (X1 ◇ (X0 ◇ (X2 ◇ X3))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X1 X0 X2 X3 sK1 sK2
    conv => enter [1]; rw [← l59 sK1 sK2 X1 X1 X1 X0 X2 X3]
    conv => enter [1]; rw [l53 sK1 sK2 X1 X1]
  have l61 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l47 sK1 sK2 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [l57 sK1 sK2 sK1 sK1]
  have l62 : ∀ X1 X2 X0 sK1 sK2 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK2)))) := by
    intro X1 X2 X0 sK1 sK2
    conv => enter [1]; rw [h53905 X1 X2 X1 X0]
    conv => enter [1, 2]; rw [h53905 X1 X0 sK1 sK2]
  have l63 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ (X1 ◇ X2)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [l62 X1 X2 X1 sK1 sK2]
    conv => enter [1]; rw [l60 X2 X1 X1 (sK1 ◇ sK2) sK1 sK2]
  have l64 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ (X1 ◇ X2)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [l63 X1 X2 sK1 sK2]
    conv => enter [1]; rw [← l61 sK1 sK2]
  have l65 : ∀ sK1 sK2 X1 X0 X2 X3 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro sK1 sK2 X1 X0 X2 X3
    conv => enter [1]; rw [l64 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h53905 X0 X1 X2 X3]
  intro x y z w
  conv => enter [1]; rw [l65 x y x y z w]

theorem Equation4512_53905_implies_Equation53946 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53905 : Equation53905 G) : Equation53946 G := by
  have l0 : ∀ X1 sK1 sK0 sK2 X0 : G, (X1 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) = (sK1 ◇ (sK1 ◇ X1)) := by
    intro X1 sK1 sK0 sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ sK2) X0]
    conv => enter [1]; rw [← h53905 sK1 X1 (sK0 ◇ sK2) X0]
  have l1 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK2) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 sK2 sK0 X0 X1]
  have l2 : ∀ X0 X1 X2 X3 sK0 sK2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 X2 X3 sK0 sK2
    conv => enter [1]; rw [← h53905 X1 X0 X2 X3]
    conv => enter [1]; rw [h53905 X1 X0 sK0 sK2]
  have l3 : ∀ X2 X0 X1 sK0 sK2 : G, (X2 ◇ (X2 ◇ X2)) = ((X0 ◇ X1) ◇ (X2 ◇ (sK0 ◇ sK2))) := by
    intro X2 X0 X1 sK0 sK2
    conv => enter [1]; rw [h53905 X2 X2 X0 X1]
    conv => enter [1]; rw [h53905 X2 (X0 ◇ X1) sK0 sK2]
  have l4 : ∀ X0 sK0 sK2 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 sK0 sK2 X1 X2
    conv => enter [1]; rw [h53905 X0 X0 sK0 sK2]
    conv => enter [1]; rw [h53905 X0 (sK0 ◇ sK2) X1 X2]
  have l5 : ∀ X1 X0 sK0 sK2 X2 X3 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (sK0 ◇ sK2)) ◇ (X1 ◇ (X2 ◇ X3))) := by
    intro X1 X0 sK0 sK2 X2 X3
    conv => enter [1, 2]; rw [h53905 X0 X1 sK0 sK2]
    conv => enter [1]; rw [h53905 X1 (X0 ◇ (sK0 ◇ sK2)) X2 X3]
  have l6 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h53905 sK2 sK0 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ sK2)]
  have l7 : ∀ X1 X0 sK0 sK2 X2 X3 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((sK0 ◇ sK2) ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X1 X0 sK0 sK2 X2 X3
    conv => enter [1]; rw [l5 X1 X0 sK0 sK2 X2 X3]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK2) (X1 ◇ (X2 ◇ X3))]
  have l8 : ∀ X0 sK2 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l4 X0 sK0 sK2 X0 X0]
    conv => enter [1]; rw [l1 sK0 sK2 X0 (X0 ◇ X0)]
  have l9 : ∀ X2 X0 X1 sK0 sK2 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ sK2)))) := by
    intro X2 X0 X1 sK0 sK2
    conv => enter [1]; rw [l3 X2 X0 X1 sK0 sK2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (sK0 ◇ sK2))]
  have l10 : ∀ X1 X0 sK0 sK2 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro X1 X0 sK0 sK2
    conv => enter [1]; rw [l7 X1 X0 sK0 sK2 X1 X1]
    conv => enter [1]; rw [← h53905 (sK0 ◇ sK2) X0 X1 (X1 ◇ X1)]
  have l11 : ∀ X0 sK0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l8 X0 sK2 sK0]
    conv => enter [1]; rw [l6 sK2 sK0]
  have l12 : ∀ X2 X0 X1 sK0 sK2 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro X2 X0 X1 sK0 sK2
    conv => enter [1]; rw [l9 X2 X0 X1 sK0 sK2]
    conv => enter [1]; rw [l2 X0 X1 X2 (sK0 ◇ sK2) sK0 sK2]
  have l13 : ∀ X1 X0 sK2 sK0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro X1 X0 sK2 sK0
    conv => enter [1]; rw [l10 X1 X0 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2 (sK0 ◇ sK2) X0]
  have l14 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [← l12 X0 X0 X1 sK0 sK2]
    conv => enter [1]; rw [l11 X0 sK0 sK2]
  have l15 : ∀ X1 X0 sK0 sK2 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro X1 X0 sK0 sK2
    conv => enter [1]; rw [l13 X1 X0 sK2 sK0]
    conv => enter [1]; rw [l6 sK2 sK0]
  have l16 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [h53905 X0 X1 X0 X1]
    conv => enter [1]; rw [l15 X1 X0 sK0 sK2]
  have l17 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK2 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [h53905 sK1 sK2 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK0 ◇ sK2)) X0]
  have l18 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l0 sK2 sK1 sK1 sK2 X0]
    conv => enter [1]; rw [← l17 sK1 sK2 X0 sK1]
  have l19 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [← l18 sK1 sK2 X0]
    conv => enter [1]; rw [h53905 sK1 sK2 sK0 sK2]
  have l20 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h53905 sK1 sK2 sK1 sK2]
    conv => enter [1]; rw [← l19 sK1 sK2 X0 sK1]
  have l21 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l20 sK1 sK2 (X0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← h53905 X0 (sK1 ◇ (sK1 ◇ sK2)) sK1 sK2]
  have l22 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l21 sK1 sK2 sK1]
    conv => enter [1]; rw [l16 sK1 (sK1 ◇ (sK1 ◇ sK2)) sK0 sK2]
  have l23 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK1 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l22 sK1 sK2 sK0]
    conv => enter [1]; rw [← l14 sK3 sK1 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l23 x y z w]

theorem Equation4512_53905_implies_Equation53985 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53905 : Equation53905 G) : Equation53985 G := by
  have l0 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = (sK1 ◇ ((sK2 ◇ X0) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ X0) X1]
  have l1 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = (sK1 ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X1]
  have l2 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h53905 sK2 sK1 X0 X1]
  have l3 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) X0 X1]
    conv => enter [1]; rw [l2 sK1 sK2 X0 X1]
  have l4 : ∀ sK1 sK2 X0 X1 X2 X3 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK2) ◇ (X2 ◇ X3)) := by
    intro sK1 sK2 X0 X1 X2 X3
    conv => enter [1]; rw [l3 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l3 sK1 sK2 X2 X3]
  have l5 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l4 sK1 sK2 X0 X1 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l7 : ∀ sK3 sK0 sK1 sK2 X0 X1 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) = (sK3 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro sK3 sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ (sK1 ◇ sK2)) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2 X0 X1]
  have l8 : ∀ sK3 sK0 sK1 sK2 X0 X1 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) = ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l7 sK3 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK3 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2)]
  have l9 : ∀ sK3 sK0 sK1 sK2 X0 X1 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK3)) := by
    intro sK3 sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ (sK1 ◇ sK2)) (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 (sK0 ◇ (sK1 ◇ sK2)) sK3 X0 X1]
  have l10 : ∀ sK3 sK0 sK1 sK2 X0 X1 X2 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ (X1 ◇ X2))) = (sK3 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK3 sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ (sK1 ◇ sK2)) (X0 ◇ (X1 ◇ X2))]
    conv => enter [1, 2]; rw [← h53905 X0 (sK0 ◇ (sK1 ◇ sK2)) X1 X2]
  have l11 : ∀ sK3 sK0 sK1 sK2 X0 X1 X2 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ sK3)) := by
    intro sK3 sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l10 sK3 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [← h53905 X0 sK3 X0 (sK0 ◇ (sK1 ◇ sK2))]
  have l12 : ∀ sK3 sK0 sK1 sK2 X0 X1 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK3 sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l9 sK3 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [l6 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2)) sK3]
  have l13 : ∀ sK3 sK0 sK1 sK2 X0 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ sK3)) := by
    intro sK3 sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l8 sK3 sK0 sK1 sK2 X0 (sK3 ◇ sK3)]
    conv => enter [1]; rw [l11 sK3 sK0 sK1 sK2 X0 sK3 sK3]
  have l14 : ∀ sK3 sK0 sK1 sK2 X0 X1 : G, ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ sK3))) := by
    intro sK3 sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l13 sK3 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ sK3)]
  have l15 : ∀ sK1 sK2 X0 X1 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 X0 X1 (sK1 ◇ sK2) sK3]
    conv => enter [1]; rw [← l13 sK3 sK0 sK1 sK2 (sK1 ◇ sK2)]
  have l16 : ∀ sK1 sK2 X0 X1 sK0 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0 X1 sK0
    conv => enter [1]; rw [l15 sK1 sK2 X0 X1 sK1 sK0]
    conv => enter [1]; rw [l12 sK1 sK0 sK1 sK2 sK1 sK2]
  have l17 : ∀ X1 X0 sK3 sK0 sK1 sK2 : G, (X1 ◇ (X1 ◇ X0)) = ((sK3 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK1 ◇ sK2)) := by
    intro X1 X0 sK3 sK0 sK1 sK2
    conv => enter [1]; rw [h53905 X1 X0 (X0 ◇ X1) sK3]
    conv => enter [1]; rw [← l14 sK3 sK0 sK1 sK2 X0 X1]
  have l18 : ∀ sK1 sK2 sK3 sK0 : G, ((sK1 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK3 (sK0 ◇ (sK1 ◇ sK2)) sK1 sK1]
    conv => enter [1]; rw [l16 sK1 sK2 sK1 sK1 sK0]
  have l19 : ∀ X1 X0 sK0 sK1 sK2 : G, (X1 ◇ (X1 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro X1 X0 sK0 sK1 sK2
    conv => enter [1]; rw [l17 X1 X0 X1 sK0 sK1 sK2]
    conv => enter [1]; rw [l12 X1 sK0 sK1 sK2 sK1 sK2]
  have l20 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK1 sK2 sK1 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l18 sK1 sK2 sK1 sK0]
  have l21 : ∀ sK0 sK1 sK2 X1 X0 X2 X3 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro sK0 sK1 sK2 X1 X0 X2 X3
    conv => enter [1]; rw [← l19 X0 X1 sK0 sK1 sK2]
    conv => enter [1]; rw [h53905 X0 X1 X2 X3]
  have l22 : ∀ sK1 sK2 X1 X0 X2 X3 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro sK1 sK2 X1 X0 X2 X3
    conv => enter [1]; rw [l20 sK1 sK2 sK1]
    conv => enter [1]; rw [l21 sK1 sK1 sK2 X1 X0 X2 X3]
  have l23 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l19 sK1 sK2 sK1 sK1 sK2]
    conv => enter [1]; rw [← l20 sK1 sK2 sK1]
  have l24 : ∀ X1 X2 X0 sK0 sK1 sK2 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro X1 X2 X0 sK0 sK1 sK2
    conv => enter [1]; rw [h53905 X1 X2 X1 X0]
    conv => enter [1, 2]; rw [h53905 X1 X0 sK0 (sK1 ◇ sK2)]
  have l25 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ (X1 ◇ X2)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [l24 X1 X2 X1 X1 sK1 sK2]
    conv => enter [1]; rw [← l22 sK1 sK2 X2 X1 X1 (X1 ◇ (sK1 ◇ sK2))]
  have l26 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ (X1 ◇ X2)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [l25 X1 X2 sK1 sK2]
    conv => enter [1]; rw [← l23 sK1 sK2]
  have l27 : ∀ sK1 sK2 X1 X0 X2 X3 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro sK1 sK2 X1 X0 X2 X3
    conv => enter [1]; rw [l26 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h53905 X0 X1 X2 X3]
  intro x y z w
  conv => enter [1]; rw [l27 x y z w x y]

theorem Equation4512_53905_implies_Equation53902 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53905 : Equation53905 G) : Equation53902 G := by
  have l0 : ∀ sK2 sK0 X0 X1 : G, (((sK2 ◇ sK0) ◇ X0) ◇ X1) = (sK2 ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK2 sK0 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK2 sK0 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ X0) X1]
  have l1 : ∀ sK2 sK0 X0 X1 : G, (((sK2 ◇ sK0) ◇ X0) ◇ X1) = (sK2 ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [l0 sK2 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l2 : ∀ sK2 sK0 X0 X1 : G, (((sK2 ◇ sK0) ◇ X0) ◇ X1) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [l1 sK2 sK0 X0 X1]
    conv => enter [1]; rw [← h53905 sK0 sK2 X0 X1]
  have l3 : ∀ sK2 sK0 X0 X1 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l2 sK2 sK0 X0 X1]
  have l4 : ∀ sK0 sK2 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) = (((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) ◇ X0) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK2) X0]
    conv => enter [1, 1]; rw [← l3 sK2 sK0 sK1 (sK0 ◇ (sK2 ◇ sK0))]
  have l5 : ∀ sK0 sK2 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) = ((sK2 ◇ sK0) ◇ ((sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0)) := by
    intro sK0 sK2 X0 sK1
    conv => enter [1]; rw [l4 sK0 sK2 X0 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK0) (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) X0]
  have l6 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK2)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l3 sK2 sK0 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) X0]
    conv => enter [1]; rw [← l5 sK0 sK2 X0 sK0]
  have l7 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ X0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l6 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK2 X0]
  have l8 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l7 sK0 sK2 sK0]
    conv => enter [1]; rw [← h53905 sK0 sK0 sK2 sK0]
  have l9 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l8 sK0 sK2]
    conv => enter [1]; rw [← l3 sK2 sK0 sK1 (sK0 ◇ (sK2 ◇ sK0))]
  have l10 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l3 sK2 sK0 X0 X1]
  have l11 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [l10 sK0 sK2 X0 X1]
    conv => enter [1]; rw [← h53905 sK0 sK0 sK0 sK2]
  have l12 : ∀ sK0 sK2 X0 X1 sK1 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 X0 X1 sK1
    conv => enter [1]; rw [l11 sK0 sK2 X0 X1]
    conv => enter [1]; rw [l9 sK0 sK2 sK1]
  have l13 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h53905 (sK2 ◇ sK0) X0 sK2 sK2]
    conv => enter [1, 2]; rw [l3 sK2 sK0 sK2 sK2]
  have l14 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l3 sK2 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h53905 X0 (sK2 ◇ sK0) sK0 sK0]
  have l15 : ∀ sK0 sK2 X0 X1 X2 : G, ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ X2))) = (sK0 ◇ (X0 ◇ (X0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK0) (X0 ◇ (X1 ◇ X2))]
    conv => enter [1, 2]; rw [← h53905 X0 (sK2 ◇ sK0) X1 X2]
  have l16 : ∀ X0 sK0 sK2 X1 X2 : G, (X0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 sK0 sK2 X1 X2
    conv => enter [1]; rw [h53905 X0 sK0 X0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l15 sK0 sK2 X0 X1 X2]
  have l17 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (X0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l3 sK2 sK0 sK1 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [l14 sK0 sK2 X0]
  have l18 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l13 sK2 sK0 X0]
    conv => enter [1]; rw [← h53905 sK0 X0 sK0 sK2]
  have l19 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← l12 sK0 sK2 X0 (sK2 ◇ sK2) sK1]
    conv => enter [1]; rw [← l16 X0 sK0 sK2 sK2 sK2]
  have l20 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l3 sK2 sK0 (sK2 ◇ sK0) X0]
    conv => enter [1]; rw [l18 sK2 sK0 X0]
  have l21 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l3 sK2 sK0 sK1 (sK0 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [l20 sK0 sK2 X0]
  have l22 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ sK0))) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l19 sK2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ sK0)]
  have l23 : ∀ X1 X0 sK2 sK0 sK1 : G, (X1 ◇ (X1 ◇ X0)) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X1 X0 sK2 sK0 sK1
    conv => enter [1]; rw [h53905 X1 X0 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← l22 sK2 sK0 sK1 X0 X1]
  have l24 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l3 sK2 sK0 sK0 sK1]
    conv => enter [1]; rw [← l3 sK2 sK0 sK1 (sK0 ◇ (sK2 ◇ sK0))]
  have l25 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l24 sK2 sK0 sK1]
    conv => enter [1]; rw [l17 sK2 sK0 sK1 sK0]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l21 sK2 sK0 sK1 sK1]
    conv => enter [1]; rw [l17 sK2 sK0 sK1 sK0]
  have l27 : ∀ X1 X0 X2 X3 sK0 sK1 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (X2 ◇ X3)) ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro X1 X0 X2 X3 sK0 sK1
    conv => enter [1, 2]; rw [h53905 X0 X1 X2 X3]
    conv => enter [1]; rw [h53905 X1 (X0 ◇ (X2 ◇ X3)) sK0 sK1]
  have l28 : ∀ X0 X1 X2 X3 sK0 sK1 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 X2 X3 sK0 sK1
    conv => enter [1]; rw [← h53905 X1 X0 X2 X3]
    conv => enter [1]; rw [h53905 X1 X0 sK0 sK1]
  have l29 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [h53905 X0 (X1 ◇ X2) sK0 sK1]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (sK0 ◇ sK1))]
  have l30 : ∀ sK2 sK0 sK1 X1 X2 X0 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (X1 ◇ (X2 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK0 sK1 X1 X2 X0
    conv => enter [1]; rw [← l23 X0 (X1 ◇ X2) sK2 sK0 sK1]
    conv => enter [1]; rw [l29 X0 X1 X2 sK0 sK1]
  have l31 : ∀ X1 X0 X2 X3 sK0 sK1 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X2 ◇ X3) ◇ (X1 ◇ (sK0 ◇ sK1)))) := by
    intro X1 X0 X2 X3 sK0 sK1
    conv => enter [1]; rw [l27 X1 X0 X2 X3 sK0 sK1]
    conv => enter [1]; rw [← h4512 X0 (X2 ◇ X3) (X1 ◇ (sK0 ◇ sK1))]
  have l32 : ∀ sK2 sK0 sK1 X1 X2 : G, ((sK2 ◇ sK0) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = (X1 ◇ (X2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 X1 X2
    conv => enter [1]; rw [l30 sK2 sK0 sK1 X1 X2 sK2]
    conv => enter [1]; rw [l28 X1 X2 sK2 (sK0 ◇ sK1) sK0 sK1]
  have l33 : ∀ X1 X0 X2 X3 sK0 sK1 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((X2 ◇ X3) ◇ (sK0 ◇ sK1))) := by
    intro X1 X0 X2 X3 sK0 sK1
    conv => enter [1]; rw [l31 X1 X0 X2 X3 sK0 sK1]
    conv => enter [1]; rw [l28 X0 (X2 ◇ X3) X1 (sK0 ◇ sK1) sK0 sK1]
  have l34 : ∀ sK2 sK0 sK1 X1 X2 : G, ((sK2 ◇ sK0) ◇ (sK0 ◇ sK1)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 X1 X2
    conv => enter [1]; rw [l24 sK2 sK0 sK1]
    conv => enter [1]; rw [l32 sK2 sK0 sK1 X1 X2]
  have l35 : ∀ X1 X0 X2 X3 sK0 sK1 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X2 ◇ (X3 ◇ (sK0 ◇ sK1)))) := by
    intro X1 X0 X2 X3 sK0 sK1
    conv => enter [1]; rw [l33 X1 X0 X2 X3 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 X2 X3 (sK0 ◇ sK1)]
  have l36 : ∀ sK0 sK2 X1 X2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X1 ◇ (X2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 X1 X2 sK1
    conv => enter [1]; rw [← l25 sK2 sK0 sK1]
    conv => enter [1]; rw [l34 sK2 sK0 sK1 X1 X2]
  have l37 : ∀ X1 X0 X2 sK0 sK1 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ (X2 ◇ (sK0 ◇ sK1))) := by
    intro X1 X0 X2 sK0 sK1
    conv => enter [1]; rw [l35 X1 X0 X2 X1 sK0 sK1]
    conv => enter [1]; rw [l28 X0 X2 X1 (sK0 ◇ sK1) sK0 sK1]
  have l38 : ∀ sK0 sK1 X1 X2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l26 sK0 sK1 sK0]
    conv => enter [1]; rw [l36 sK0 sK0 X1 X2 sK1]
  have l39 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X2 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [h53905 X0 X1 X0 X1]
    conv => enter [1]; rw [l37 X1 X0 X2 sK0 sK1]
  have l40 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l39 X0 X1 X0 sK0 sK1]
    conv => enter [1]; rw [← l38 sK0 sK1 X0 X0]
  have l41 : ∀ sK0 sK1 X1 X0 X2 X3 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro sK0 sK1 X1 X0 X2 X3
    conv => enter [1]; rw [l40 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h53905 X0 X1 X2 X3]
  intro x y z
  conv => enter [1]; rw [l41 x y y x z x]

theorem Equation4512_53905_implies_Equation53901 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53905 : Equation53905 G) : Equation53901 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK2 X0]
  have l1 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = (sK1 ◇ ((sK2 ◇ X0) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ X0) X1]
  have l2 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = (sK1 ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X1]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h53905 sK2 sK1 X0 X1]
  have l4 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) X0 X1]
    conv => enter [1]; rw [l3 sK1 sK2 X0 X1]
  have l5 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ X0) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l0 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK2 ◇ X0) X1]
  have l6 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X1]
  have l7 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l6 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h53905 sK2 (sK0 ◇ sK1) X0 X1]
  have l8 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) X0 X1]
    conv => enter [1]; rw [l7 sK0 sK1 sK2 X0 X1]
  have l9 : ∀ sK1 sK2 X0 X1 X2 X3 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK2) ◇ (X2 ◇ X3)) := by
    intro sK1 sK2 X0 X1 X2 X3
    conv => enter [1]; rw [l4 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l4 sK1 sK2 X2 X3]
  have l10 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l9 sK1 sK2 sK0 sK1 (sK0 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK2]
  have l11 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l9 sK1 sK2 X0 X1 sK0 sK1]
  have l12 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l11 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ sK1)]
  have l13 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l10 sK1 sK2 sK0]
  have l14 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ sK1)]
  have l15 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h53905 X0 X1 (sK0 ◇ sK1) sK2]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK1 sK2]
  have l16 : ∀ X1 sK0 sK1 sK2 X0 : G, (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X1)) := by
    intro X1 sK0 sK1 sK2 X0
    conv => enter [1, 2]; rw [l0 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h53905 (sK0 ◇ sK1) X1 sK2 X0]
  have l17 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 sK1 sK0 X0 X1]
  have l18 : ∀ sK1 sK0 sK2 X0 X1 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1)) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK1 ◇ sK2)) (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 (sK0 ◇ (sK1 ◇ sK2)) sK1 X0 X1]
  have l19 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ X2))) = (sK0 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (X0 ◇ (X1 ◇ X2))]
    conv => enter [1, 2]; rw [← h53905 X0 (sK1 ◇ sK2) X1 X2]
  have l20 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l19 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [← h53905 X0 sK0 X0 (sK1 ◇ sK2)]
  have l21 : ∀ sK1 sK0 sK2 X0 X1 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l18 sK1 sK0 sK2 X0 X1]
    conv => enter [1]; rw [l12 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2)) sK1]
  have l22 : ∀ X1 sK0 sK1 sK2 X0 : G, (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro X1 sK0 sK1 sK2 X0
    conv => enter [1]; rw [l16 X1 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l17 sK0 sK1 (sK0 ◇ sK1) X1]
  have l23 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← l8 sK0 sK1 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l20 sK0 sK1 sK2 X0 sK2 sK2]
  have l24 : ∀ sK0 sK1 sK2 X1 X0 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [← l15 sK1 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [← l22 X1 sK0 sK1 sK2 X0]
  have l25 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l23 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [l15 sK2 (sK0 ◇ sK1) sK0 sK1 sK2]
  have l26 : ∀ sK0 sK1 sK2 X1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l24 sK0 sK1 sK2 X1 X0]
  have l27 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l25 X0 sK0 sK1 sK2]
  have l28 : ∀ sK0 sK1 sK2 X1 X0 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l26 sK0 sK1 sK2 X1 X0]
  have l29 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l14 sK0 sK1 sK2]
    conv => enter [1]; rw [l27 sK0 sK1 sK2 X0]
  have l30 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l21 sK1 sK0 sK2 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h53905 X0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK0 sK0]
  have l31 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h53905 X0 X1 X0 sK0]
    conv => enter [1, 2]; rw [← l29 sK0 sK1 sK2 X0]
  have l32 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l31 X0 X1 sK0 sK1 sK2]
    conv => enter [1]; rw [← l28 sK0 sK1 sK2 X1 (sK0 ◇ sK1)]
  have l33 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l30 sK0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l32 sK0 sK1 sK0 sK1 sK2]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1 sK0 sK1 sK0]
    conv => enter [1]; rw [← l32 sK0 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l32 sK0 sK1 sK0 sK1 sK0]
  have l35 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [← l33 sK0 sK1 sK2]
  have l36 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) = (X0 ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l21 sK1 sK0 sK2 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1]; rw [h53905 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0 sK0 sK1]
  have l37 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← l32 X1 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [h53905 X1 X0 sK0 sK1]
  have l38 : ∀ sK0 sK1 sK2 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l32 sK0 (sK1 ◇ sK2) sK0 sK1 sK2]
    conv => enter [1]; rw [l37 sK0 sK1 sK2 X0 X1]
  have l39 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l36 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [l21 sK1 sK0 sK2 sK0 sK1]
  have l40 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l38 sK0 sK1 sK2 sK0 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l39 sK0 sK1 sK2 sK0]
  have l41 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l35 sK0 sK1 sK2]
    conv => enter [1]; rw [← l40 sK0 sK1 sK2]
  have l42 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l31 X0 X1 sK0 sK1 sK2]
    conv => enter [1]; rw [← l38 sK0 sK1 sK2 X1 (sK0 ◇ (sK1 ◇ sK2))]
  have l43 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l42 X0 X1 sK0 sK1 X0]
    conv => enter [1]; rw [← l41 sK0 sK1 X0]
  have l44 : ∀ sK0 sK1 X1 X0 X2 X3 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro sK0 sK1 X1 X0 X2 X3
    conv => enter [1]; rw [l43 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h53905 X0 X1 X2 X3]
  intro x y z
  conv => enter [1]; rw [l44 x y y x y z]

theorem Equation4512_53905_implies_Equation53942 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53905 : Equation53905 G) : Equation53942 G := by
  have l0 : ∀ sK2 sK1 X0 X1 : G, (((sK2 ◇ sK1) ◇ X0) ◇ X1) = (sK2 ◇ ((sK1 ◇ X0) ◇ X1)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ X0) X1]
  have l1 : ∀ sK2 sK1 X0 X1 : G, (((sK2 ◇ sK1) ◇ X0) ◇ X1) = (sK2 ◇ (sK1 ◇ (X0 ◇ X1))) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l0 sK2 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 X1]
  have l2 : ∀ sK2 sK1 X0 X1 : G, (((sK2 ◇ sK1) ◇ X0) ◇ X1) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [l1 sK2 sK1 X0 X1]
    conv => enter [1]; rw [← h53905 sK1 sK2 X0 X1]
  have l3 : ∀ sK2 sK1 X0 X1 : G, ((sK2 ◇ sK1) ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK1) X0 X1]
    conv => enter [1]; rw [l2 sK2 sK1 X0 X1]
  have l4 : ∀ sK0 sK2 sK1 X0 X1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X1)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l3 sK2 sK1 X0 X1]
  have l5 : ∀ sK0 sK2 sK1 X0 X1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1]; rw [l4 sK0 sK2 sK1 X0 X1]
    conv => enter [1]; rw [← h53905 sK1 sK0 sK1 sK2]
  have l6 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l3 sK2 sK1 sK0 sK1]
    conv => enter [1]; rw [← l3 sK2 sK1 sK2 (sK0 ◇ (sK2 ◇ sK1))]
  have l7 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK2 ◇ sK1)) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l5 sK0 sK2 sK1 X0 X1]
  have l8 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ X1)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l7 sK2 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK1 ◇ sK0)]
  have l9 : ∀ sK1 sK2 sK0 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [← l3 sK2 sK1 sK1 sK0]
    conv => enter [1]; rw [← l8 sK2 sK0 sK1 X0 X1]
  have l10 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ X1)) = ((sK2 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [← l9 sK1 sK2 sK0 X0 X1]
    conv => enter [1]; rw [← l3 sK2 sK1 sK2 (sK0 ◇ (sK2 ◇ sK1))]
  have l11 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ X1)) = ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l10 sK2 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l6 sK2 sK1 sK0]
  have l12 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 sK1 sK0 X0 X1]
  have l13 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ ((sK0 ◇ (sK2 ◇ sK1)) ◇ sK2)) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK2 ◇ sK1)) (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 (sK0 ◇ (sK2 ◇ sK1)) sK2 X0 X1]
  have l14 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← l3 sK2 sK1 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h53905 X0 (sK2 ◇ sK1) sK1 sK1]
  have l15 : ∀ sK2 sK0 sK1 X0 X1 X2 : G, ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ X2))) = (sK2 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK2 ◇ sK1)) (X0 ◇ (X1 ◇ X2))]
    conv => enter [1, 2]; rw [← h53905 X0 (sK0 ◇ (sK2 ◇ sK1)) X1 X2]
  have l16 : ∀ sK2 sK0 sK1 X0 X1 X2 : G, ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ (X0 ◇ sK2)) := by
    intro sK2 sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l15 sK2 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [← h53905 X0 sK2 X0 (sK0 ◇ (sK2 ◇ sK1))]
  have l17 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l3 sK2 sK1 sK2 (sK0 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [l14 sK1 sK2 X0]
  have l18 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l13 sK2 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l5 sK0 sK2 sK1 (sK0 ◇ (sK2 ◇ sK1)) sK2]
  have l19 : ∀ sK0 sK1 X0 X1 sK2 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 X0 X1 sK2
    conv => enter [1]; rw [l12 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l5 sK0 sK2 sK1 sK0 sK1]
  have l20 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ sK2)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [← l11 sK2 sK0 sK1 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [l16 sK2 sK0 sK1 X0 sK2 sK2]
  have l21 : ∀ sK2 sK1 sK0 X0 : G, ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l6 sK2 sK1 sK0]
    conv => enter [1]; rw [l17 sK2 sK1 sK0 X0]
  have l22 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l18 sK2 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l5 sK0 sK2 sK1 sK0 sK1]
  have l23 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l11 sK2 sK0 sK1 sK2 sK2]
    conv => enter [1]; rw [l22 sK2 sK0 sK1 sK2 sK2]
  have l24 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l23 sK2 sK1 sK0]
    conv => enter [1]; rw [← l19 sK0 sK1 sK0 sK1 sK2]
  have l25 : ∀ sK2 sK1 sK0 X0 X1 : G, ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ sK2))) := by
    intro sK2 sK1 sK0 X0 X1
    conv => enter [1]; rw [l20 sK2 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ sK2)]
  have l26 : ∀ X1 X0 sK2 sK1 sK0 : G, (X1 ◇ (X1 ◇ X0)) = ((sK2 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 sK2 sK1 sK0
    conv => enter [1]; rw [h53905 X1 X0 (X0 ◇ X1) sK2]
    conv => enter [1]; rw [← l25 sK2 sK1 sK0 X0 X1]
  have l27 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro X1 X0 sK0 sK1
    conv => enter [1]; rw [l26 X1 X0 X1 sK1 sK0]
    conv => enter [1]; rw [l24 X1 sK1 sK0]
  have l28 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l24 sK2 sK1 sK0]
    conv => enter [1]; rw [l21 sK2 sK1 sK0 sK0]
  have l29 : ∀ X0 X1 X2 X3 sK0 sK1 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 X2 X3 sK0 sK1
    conv => enter [1]; rw [← h53905 X1 X0 X2 X3]
    conv => enter [1]; rw [h53905 X1 X0 sK0 sK1]
  have l30 : ∀ X1 X2 X0 sK0 sK1 : G, (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = (X0 ◇ ((X1 ◇ X2) ◇ (sK0 ◇ sK1))) := by
    intro X1 X2 X0 sK0 sK1
    conv => enter [1]; rw [h4512 X1 X2 ((X1 ◇ X2) ◇ X0)]
    conv => enter [1]; rw [h53905 (X1 ◇ X2) X0 sK0 sK1]
  have l31 : ∀ X0 X1 X2 sK0 sK1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 X2 sK0 sK1
    conv => enter [1]; rw [h53905 X0 (X1 ◇ X2) sK0 sK1]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (sK0 ◇ sK1))]
  have l32 : ∀ sK0 sK1 X1 X2 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X1 ◇ (X2 ◇ (X0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X1 X2 X0
    conv => enter [1]; rw [← l27 X0 (X1 ◇ X2) sK0 sK1]
    conv => enter [1]; rw [l31 X0 X1 X2 sK0 sK1]
  have l33 : ∀ X1 X2 X0 sK0 sK1 : G, (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ sK1)))) := by
    intro X1 X2 X0 sK0 sK1
    conv => enter [1]; rw [l30 X1 X2 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 X1 X2 (sK0 ◇ sK1)]
  have l34 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← h53905 sK0 X0 sK0 sK1]
    conv => enter [1]; rw [l27 sK0 X0 sK0 sK1]
  have l35 : ∀ sK0 sK1 X1 X2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) = (X1 ◇ (X2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X1 X2
    conv => enter [1]; rw [l32 sK0 sK1 X1 X2 sK0]
    conv => enter [1]; rw [l29 X1 X2 sK0 (sK0 ◇ sK1) sK0 sK1]
  have l36 : ∀ X1 X2 X0 sK0 sK1 : G, (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro X1 X2 X0 sK0 sK1
    conv => enter [1]; rw [l33 X1 X2 X0 sK0 sK1]
    conv => enter [1]; rw [l29 X0 X1 X2 (sK0 ◇ sK1) sK0 sK1]
  have l37 : ∀ sK0 sK2 sK1 X1 X2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (X1 ◇ (X2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1 X1 X2
    conv => enter [1]; rw [← l28 sK0 sK1 sK2]
    conv => enter [1]; rw [l35 sK0 sK1 X1 X2]
  have l38 : ∀ X2 X1 X0 sK0 sK1 : G, (X2 ◇ (X2 ◇ X1)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK1))) := by
    intro X2 X1 X0 sK0 sK1
    conv => enter [1]; rw [h53905 X2 X1 (X1 ◇ X2) X0]
    conv => enter [1]; rw [l36 X1 X2 X0 sK0 sK1]
  have l39 : ∀ X2 X1 sK0 sK2 sK1 : G, (X2 ◇ (X2 ◇ X1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro X2 X1 sK0 sK2 sK1
    conv => enter [1]; rw [l38 X2 X1 X2 sK0 sK1]
    conv => enter [1]; rw [← l37 sK0 sK2 sK1 X2 X1]
  have l40 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l34 X0 sK0 sK1]
    conv => enter [1]; rw [l28 sK0 sK1 sK2]
  have l41 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l39 sK0 sK1 sK0 sK0 sK1]
    conv => enter [1]; rw [← l40 X0 sK0 sK1 sK0]
  have l42 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h53905 X0 X1 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l41 sK0 sK1 X0]
  have l43 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l42 X0 X1 sK0 sK1]
    conv => enter [1]; rw [← l41 sK0 sK1 X1]
  have l44 : ∀ sK0 sK1 X1 X0 X2 X3 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro sK0 sK1 X1 X0 X2 X3
    conv => enter [1]; rw [l43 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h53905 X0 X1 X2 X3]
  intro x y z
  conv => enter [1]; rw [l44 x y z x z y]

theorem Equation4512_53905_implies_Equation53939 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53905 : Equation53905 G) : Equation53939 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK2 ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK2 X0]
  have l1 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = (sK1 ◇ ((sK2 ◇ X0) ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ X0) X1]
  have l2 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = (sK1 ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X1]
  have l3 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ sK2) ◇ X0) ◇ X1) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h53905 sK2 sK1 X0 X1]
  have l4 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) X0 X1]
    conv => enter [1]; rw [l3 sK1 sK2 X0 X1]
  have l5 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [l6 sK0 sK1 sK2]
  have l8 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l7 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l9 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK2 ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2]
  have l10 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0)) = (((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK2 ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0]
    conv => enter [1, 1]; rw [← l9 sK2 sK0 sK1]
  have l11 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0)) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l10 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l12 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (sK2 ◇ ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← l11 sK2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l13 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK2)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l12 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← h53905 (sK0 ◇ sK1) sK2 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l14 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [l13 sK2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK2]
  have l15 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l14 sK2 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [l6 sK0 sK1 sK2]
  have l16 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X1) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) X1]
    conv => enter [1, 1]; rw [l14 sK2 sK0 sK1 X0]
  have l17 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) ◇ X1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1)) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l16 sK2 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK2)) X1]
  have l18 : ∀ sK0 sK1 sK2 X1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1)) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X1 X0
    conv => enter [1]; rw [← l17 sK2 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) X0 X1]
  have l19 : ∀ sK0 sK1 sK2 X1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X1)) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1]; rw [← l14 sK2 sK0 sK1 (sK0 ◇ X1)]
    conv => enter [1]; rw [← l18 sK0 sK1 sK2 X1 sK0]
  have l20 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0]
    conv => enter [1, 1]; rw [← l15 sK0 sK1 sK2]
  have l21 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [← l20 sK2 sK0 sK1 X0]
  have l22 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l21 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l23 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l22 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h53905 (sK0 ◇ sK1) (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l24 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l23 sK0 sK1 sK2 sK0]
  have l25 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)]
    conv => enter [1, 2]; rw [← l19 sK0 sK1 sK2 X0]
  have l26 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l25 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK2))]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l24 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))))]
  have l28 : ∀ sK0 sK1 sK2 X0 : G, (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l24 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0]
  have l29 : ∀ sK0 sK1 sK2 X0 : G, (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l28 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l30 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l27 sK0 sK1 sK2]
  have l31 : ∀ sK0 sK1 sK2 X0 : G, (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l29 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h53905 (sK0 ◇ sK1) (sK0 ◇ sK1) (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l32 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [l31 sK0 sK1 sK2 X0]
  have l33 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l32 sK0 sK1 sK2 sK0]
  have l34 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0]
    conv => enter [1, 1]; rw [← l30 sK0 sK1 sK2]
  have l35 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [← l34 sK0 sK1 sK2 X0]
  have l36 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l35 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l37 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l36 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h53905 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l38 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l26 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l37 sK0 sK1 sK2 sK0]
  have l39 : ∀ sK0 sK1 sK2 X0 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l38 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l40 : ∀ sK0 sK1 sK2 X0 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l39 sK0 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l41 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h53905 (sK0 ◇ sK1) (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [← l40 sK0 sK1 sK2 X0]
  have l42 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [← l41 sK0 sK1 sK2 X0]
  have l43 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l33 sK0 sK1 sK2]
    conv => enter [1]; rw [← l42 sK0 sK1 sK2 X0]
  have l44 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l43 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l26 sK0 sK1 sK2 sK0]
  have l45 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l4 sK1 sK2 X0 X1]
  have l46 : ∀ sK1 sK2 X0 X1 X2 : G, ((sK1 ◇ sK2) ◇ ((X0 ◇ X1) ◇ X2)) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ X2) := by
    intro sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [l4 sK1 sK2 X0 X1]
  have l47 : ∀ sK1 sK2 X0 X1 X2 : G, ((sK1 ◇ sK2) ◇ ((X0 ◇ X1) ◇ X2)) = (sK2 ◇ ((sK2 ◇ sK1) ◇ X2)) := by
    intro sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l46 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK1) X2]
  have l48 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l45 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← h53905 sK2 sK0 sK2 sK1]
  have l49 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h4512 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l4 sK1 sK2 sK0 (sK1 ◇ sK2)]
  have l50 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l4 sK1 sK2 sK1 sK2]
  have l51 : ∀ sK1 sK2 X0 X1 X2 : G, ((sK1 ◇ sK2) ◇ ((X0 ◇ X1) ◇ X2)) = (sK2 ◇ (sK2 ◇ (sK1 ◇ X2))) := by
    intro sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l47 sK1 sK2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 sK2 sK1 X2]
  have l52 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h4512 sK1 sK2 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l50 sK1 sK2 sK0]
  have l53 : ∀ sK1 sK2 X0 X1 X2 : G, ((sK1 ◇ sK2) ◇ ((X0 ◇ X1) ◇ X2)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l51 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [← h53905 sK2 sK2 sK1 X2]
  have l54 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l4 sK1 sK2 (sK2 ◇ sK2) sK2]
    conv => enter [1]; rw [l53 sK1 sK2 sK2 sK2 sK2]
  have l55 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK2 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l54 sK2 sK1]
  have l56 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l52 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l57 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [l56 sK0 sK1 sK2]
  have l58 : ∀ sK0 sK1 sK2 X0 : G, (((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l57 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK1 ◇ sK2)) (sK1 ◇ sK2) X0]
  have l59 : ∀ sK0 sK1 sK2 X0 : G, (((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l58 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l48 sK0 sK1 sK2 (sK1 ◇ sK2) X0]
  have l60 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1]; rw [l59 sK0 sK1 sK2 X0]
  have l61 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [h53905 X0 X1 (sK0 ◇ sK1) sK2]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK1 sK2]
  have l62 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ (sK0 ◇ X1)) := by
    intro X1 sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [← h53905 sK0 X1 sK1 X0]
  have l63 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ (sK0 ◇ X1)) := by
    intro X1 sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [← h53905 sK0 X1 (sK0 ◇ sK1) X0]
  have l64 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1, 2]; rw [l4 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← h53905 sK2 X0 sK2 sK1]
  have l65 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 sK1 sK0 X0 X1]
  have l66 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK0)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK2) (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 (sK1 ◇ sK2) sK0 X0 X1]
  have l67 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK1 ◇ sK2)) (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 (sK0 ◇ (sK1 ◇ sK2)) sK2 X0 X1]
  have l68 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l0 sK0 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 sK2 (sK0 ◇ sK1) X0 X1]
  have l69 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l14 sK2 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h53905 (sK0 ◇ (sK1 ◇ sK2)) (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) sK0 sK0]
  have l70 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l69 sK0 sK1 sK2]
    conv => enter [1]; rw [l8 sK0 sK1 sK2 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l71 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ sK0)) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l48 sK0 sK1 sK2 sK2 sK2]
    conv => enter [1]; rw [l68 sK0 sK1 sK2 sK2 sK2]
  have l72 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK1) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ sK2)) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l67 sK2 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l8 sK0 sK1 sK2 sK2]
  have l73 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l66 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [l4 sK1 sK2 (sK1 ◇ sK2) sK0]
  have l74 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l70 sK0 sK1 sK2]
    conv => enter [1]; rw [l60 sK0 sK1 sK2 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l75 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK0)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l71 sK2 sK0 sK2]
    conv => enter [1]; rw [← h53905 sK2 sK2 sK0 sK2]
  have l76 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l72 sK2 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l60 sK0 sK1 sK2 sK2]
  have l77 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l73 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l4 sK1 sK2 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l78 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l74 sK0 sK1 sK2]
    conv => enter [1]; rw [← l64 sK0 sK1 sK2 sK0]
  have l79 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l55 sK1 sK2 sK0]
    conv => enter [1]; rw [← l75 sK2 sK0]
  have l80 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l76 sK2 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l64 sK0 sK1 sK2 sK0]
  have l81 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l78 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ sK1)]
  have l82 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK1 ◇ sK2) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l79 sK1 sK2 sK0]
    conv => enter [1]; rw [← l64 sK0 sK1 sK2 sK0]
  have l83 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l80 sK2 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ sK1)]
  have l84 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l82 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK2) (sK0 ◇ sK1)]
  have l85 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l83 sK2 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l81 sK0 sK1 sK2]
  have l86 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l81 sK0 sK1 sK2]
    conv => enter [1]; rw [← l84 sK1 sK2 sK0]
  have l87 : ∀ sK0 sK1 sK2 X0 : G, (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [l86 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
  have l88 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [← l4 sK1 sK2 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1]; rw [← l87 sK0 sK1 sK2 X0]
  have l89 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [l88 sK2 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK2)) X0]
  have l90 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l89 sK2 sK1 sK0 sK2]
    conv => enter [1]; rw [← l19 sK0 sK1 sK2 sK2]
  have l91 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l49 sK1 sK2 sK0]
    conv => enter [1]; rw [l90 sK2 sK1 sK0]
  have l92 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l91 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ sK2))]
  have l93 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l92 sK0 sK1 sK2]
    conv => enter [1]; rw [← l44 sK0 sK1 sK2]
  have l94 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l91 sK1 sK2 sK0]
    conv => enter [1]; rw [← l93 sK0 sK1 sK2]
  have l95 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l94 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))]
  have l96 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l9 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← l95 sK1 sK2 sK0]
  have l97 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l96 sK2 sK0 sK1]
    conv => enter [1]; rw [← h53905 sK1 sK2 sK2 (sK0 ◇ (sK1 ◇ sK2))]
  have l98 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l86 sK0 sK1 sK2]
    conv => enter [1]; rw [← l77 sK0 sK1 sK2 sK0 (sK0 ◇ sK1)]
  have l99 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l91 sK1 sK2 sK0]
    conv => enter [1]; rw [l98 sK0 sK1 sK2]
  have l100 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l99 sK1 sK2 sK0]
  have l101 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h53905 sK1 sK2 sK2 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l100 sK2 sK0 sK1]
  have l102 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK2]
    conv => enter [1]; rw [l85 sK2 sK0 sK1 (sK0 ◇ sK1) sK2]
  have l103 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = ((sK2 ◇ (sK0 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l91 sK1 sK2 sK0]
    conv => enter [1]; rw [← l102 sK2 sK0 sK1]
  have l104 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l85 sK2 sK0 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l101 sK1 sK2 sK0]
  have l105 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l103 sK1 sK2 sK0]
    conv => enter [1]; rw [l97 sK2 sK0 sK1]
  have l106 : ∀ X1 X0 sK0 sK1 X2 X3 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = ((X0 ◇ (sK0 ◇ sK1)) ◇ (X1 ◇ (X2 ◇ X3))) := by
    intro X1 X0 sK0 sK1 X2 X3
    conv => enter [1, 2]; rw [h53905 X0 X1 sK0 sK1]
    conv => enter [1]; rw [h53905 X1 (X0 ◇ (sK0 ◇ sK1)) X2 X3]
  have l107 : ∀ X1 X0 sK0 sK1 X2 X3 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X0 ◇ ((sK0 ◇ sK1) ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro X1 X0 sK0 sK1 X2 X3
    conv => enter [1]; rw [l106 X1 X0 sK0 sK1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ sK1) (X1 ◇ (X2 ◇ X3))]
  have l108 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h53905 (sK0 ◇ sK1) X0 X1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l107 X1 X0 sK0 sK1 sK0 sK0]
  have l109 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [h53905 X0 X1 X0 X1]
    conv => enter [1]; rw [← l108 sK0 sK1 X0 X1]
  have l110 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l109 X0 X1 sK0 sK1]
    conv => enter [1]; rw [l65 sK0 sK1 (sK0 ◇ sK1) X0]
  have l111 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l110 X0 X1 sK1 sK0]
    conv => enter [1]; rw [l61 sK1 sK0 sK0 sK1 sK2]
  have l112 : ∀ X0 X1 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK0 sK1 sK2
    conv => enter [1]; rw [l111 X0 X1 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
  have l113 : ∀ X0 X1 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK2)))) := by
    intro X0 X1 sK1 sK2 sK0
    conv => enter [1]; rw [l112 X0 X1 sK0 sK1 sK2]
    conv => enter [1]; rw [← l91 sK1 sK2 sK0]
  have l114 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l113 X0 X1 sK1 sK2 X0]
    conv => enter [1]; rw [l105 sK1 sK2 X0]
  have l115 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← h53905 sK0 (sK0 ◇ sK1) sK0 sK1]
  have l116 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l115 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l117 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l116 sK0 sK1 X0]
    conv => enter [1]; rw [l63 sK0 sK0 sK1 X0]
  have l118 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l117 sK0 sK1 X0]
    conv => enter [1]; rw [h53905 sK0 sK0 sK0 sK1]
  have l119 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l65 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1]; rw [l118 sK0 sK1 sK1]
  have l120 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l61 sK1 sK0 sK0 sK1 sK2]
    conv => enter [1]; rw [l119 sK1 sK0]
  have l121 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [l120 sK0 sK1 sK2]
  have l122 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l104 sK0 sK1 sK2]
    conv => enter [1]; rw [l121 sK0 sK1 sK2]
  have l123 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK1 ◇ X0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [h53905 sK0 (sK1 ◇ X0) sK0 sK1]
  have l124 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ X1)) := by
    intro X1 X0 sK0 sK1
    conv => enter [1, 2]; rw [← h53905 sK0 X0 sK0 sK1]
    conv => enter [1]; rw [← h53905 sK0 X1 sK0 X0]
  have l125 : ∀ X1 X0 sK0 sK1 : G, (X1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X1 X0 sK0 sK1
    conv => enter [1]; rw [l124 X1 X0 sK0 sK1]
    conv => enter [1]; rw [h53905 sK0 X1 sK0 sK1]
  have l126 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK1 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l123 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 X0 (sK0 ◇ (sK0 ◇ sK1))]
  have l127 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l126 sK0 sK1 X0]
    conv => enter [1]; rw [l125 sK1 X0 sK0 sK1]
  have l128 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53905 sK0 sK1 sK0 sK1]
    conv => enter [1]; rw [← l127 sK0 sK1 X0]
  have l129 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l128 sK0 sK1 sK0]
    conv => enter [1]; rw [l62 sK0 sK0 sK1 sK0]
  have l130 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l129 sK0 sK1]
    conv => enter [1]; rw [h53905 sK0 sK0 sK0 sK1]
  have l131 : ∀ X1 X0 X2 X3 sK1 sK2 : G, (X1 ◇ (X0 ◇ (X2 ◇ X3))) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro X1 X0 X2 X3 sK1 sK2
    conv => enter [1]; rw [← h53905 X0 X1 X2 X3]
    conv => enter [1]; rw [l114 X0 X1 sK1 sK2]
  have l132 : ∀ X1 X0 X2 X3 sK0 sK1 : G, (X1 ◇ (X0 ◇ (X2 ◇ X3))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X1 X0 X2 X3 sK0 sK1
    conv => enter [1]; rw [l131 X1 X0 X2 X3 sK1 X1]
    conv => enter [1]; rw [l122 sK1 X1 sK0]
  have l133 : ∀ sK0 sK1 X1 X0 X2 X3 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro sK0 sK1 X1 X0 X2 X3
    conv => enter [1]; rw [l130 sK0 sK1]
    conv => enter [1]; rw [← l132 X1 X0 X2 X3 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l133 x y z x y z]

theorem Equation4512_53905_implies_Equation53858 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53905 : Equation53905 G) : Equation53858 G := by
  have l0 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK2 ◇ (sK2 ◇ (sK2 ◇ sK2))) ◇ X0) := by
    intro sK2 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) (sK2 ◇ sK2) X0]
    conv => enter [1, 1]; rw [← h4512 sK2 sK2 (sK2 ◇ sK2)]
  have l1 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [l0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK2 ◇ sK2)) X0]
  have l2 : ∀ X1 sK2 X0 : G, (X1 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) = (sK2 ◇ (sK2 ◇ X1)) := by
    intro X1 sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK2 (sK2 ◇ sK2) X0]
    conv => enter [1]; rw [← h53905 sK2 X1 (sK2 ◇ sK2) X0]
  have l3 : ∀ X1 sK2 X0 : G, (X1 ◇ (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0))) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X1)) := by
    intro X1 sK2 X0
    conv => enter [1, 2]; rw [← l1 sK2 X0]
    conv => enter [1]; rw [← h53905 (sK2 ◇ sK2) X1 (sK2 ◇ sK2) X0]
  have l4 : ∀ X1 sK2 X0 : G, (X1 ◇ (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0))) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro X1 sK2 X0
    conv => enter [1]; rw [l3 X1 sK2 X0]
    conv => enter [1]; rw [l1 sK2 X1]
  have l5 : ∀ X1 sK2 X0 : G, (X1 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X0)) = ((sK2 ◇ sK2) ◇ X1) := by
    intro X1 sK2 X0
    conv => enter [1]; rw [l2 X1 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 sK2 X1]
  have l6 : ∀ sK2 X1 : G, (sK2 ◇ (sK2 ◇ X1)) = (sK2 ◇ ((sK2 ◇ (sK2 ◇ sK2)) ◇ X1)) := by
    intro sK2 X1
    conv => enter [1]; rw [h53905 sK2 X1 (sK2 ◇ (sK2 ◇ sK2)) sK2]
    conv => enter [1]; rw [l4 X1 sK2 sK2]
  have l7 : ∀ sK2 X1 : G, ((sK2 ◇ sK2) ◇ sK2) = (sK2 ◇ (sK2 ◇ X1)) := by
    intro sK2 X1
    conv => enter [1]; rw [← l5 sK2 sK2 X1]
    conv => enter [1]; rw [← l6 sK2 X1]
  have l8 : ∀ sK2 X1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (sK2 ◇ X1)) := by
    intro sK2 X1
    conv => enter [1]; rw [h4512 sK2 sK2 sK2]
    conv => enter [1]; rw [l7 sK2 X1]
  have l9 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (sK2 ◇ (X0 ◇ (X0 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [l8 sK2 (X0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← h53905 X0 sK2 sK2 sK2]
  have l10 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X0 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [l9 sK2 X0]
    conv => enter [1]; rw [← h53905 X0 sK2 X0 sK2]
  have l11 : ∀ sK2 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ sK2))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l10 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ sK2)]
  have l12 : ∀ sK2 X1 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X1 ◇ X0)) := by
    intro sK2 X1 X0
    conv => enter [1]; rw [l11 sK2 X0 X1]
    conv => enter [1]; rw [← h53905 X1 X0 (X0 ◇ X1) sK2]
  have l13 : ∀ sK2 X0 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (sK4 ◇ (sK1 ◇ sK0))) := by
    intro sK2 X0 sK4 sK1 sK0
    conv => enter [1]; rw [l12 sK2 sK4 X0]
    conv => enter [1]; rw [h53905 sK4 X0 sK1 sK0]
  intro x y z w u
  conv => enter [1]; rw [l13 x y z w u]

theorem Equation4512_53905_implies_Equation53904 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53905 : Equation53905 G) : Equation53904 G := by
  have l0 : ∀ sK2 X0 X1 : G, (((sK2 ◇ sK2) ◇ X0) ◇ X1) = (sK2 ◇ ((sK2 ◇ X0) ◇ X1)) := by
    intro sK2 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ X0) X1]
  have l1 : ∀ sK2 X0 X1 : G, (((sK2 ◇ sK2) ◇ X0) ◇ X1) = (sK2 ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l0 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X1]
  have l2 : ∀ sK2 X0 X1 : G, (((sK2 ◇ sK2) ◇ X0) ◇ X1) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l1 sK2 X0 X1]
    conv => enter [1]; rw [← h53905 sK2 sK2 X0 X1]
  have l3 : ∀ sK2 X0 X1 : G, (((sK2 ◇ sK2) ◇ X0) ◇ X1) = ((sK2 ◇ sK2) ◇ sK2) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l2 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK2 sK2 sK2]
  have l4 : ∀ sK2 X0 X1 : G, (((sK2 ◇ sK2) ◇ X0) ◇ X1) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [l3 sK2 X0 X1]
    conv => enter [1]; rw [← h4512 sK2 sK2 sK2]
  have l5 : ∀ sK2 X0 X1 : G, ((sK2 ◇ sK2) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK2 ◇ sK2) X0 X1]
    conv => enter [1]; rw [l4 sK2 X0 X1]
  have l6 : ∀ X1 sK2 X0 : G, (X1 ◇ ((sK2 ◇ sK2) ◇ X0)) = (sK2 ◇ (sK2 ◇ X1)) := by
    intro X1 sK2 X0
    conv => enter [1, 2]; rw [← h4512 sK2 sK2 X0]
    conv => enter [1]; rw [← h53905 sK2 X1 sK2 X0]
  have l7 : ∀ sK2 X0 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK2 ◇ sK2))) := by
    intro sK2 X0
    conv => enter [1]; rw [← l5 sK2 X0 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h53905 X0 (sK2 ◇ sK2) sK2 sK2]
  have l8 : ∀ X1 sK2 X0 : G, (X1 ◇ ((sK2 ◇ sK2) ◇ X0)) = ((sK2 ◇ sK2) ◇ X1) := by
    intro X1 sK2 X0
    conv => enter [1]; rw [l6 X1 sK2 X0]
    conv => enter [1]; rw [h4512 sK2 sK2 X1]
  have l9 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [h53905 X0 X1 (sK2 ◇ sK2) X0]
    conv => enter [1, 2]; rw [l8 X0 sK2 X0]
  have l10 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = ((sK2 ◇ sK2) ◇ ((sK2 ◇ sK2) ◇ X0)) := by
    intro sK2 X0
    conv => enter [1]; rw [← l8 X0 sK2 (sK2 ◇ sK2)]
    conv => enter [1]; rw [← h53905 (sK2 ◇ sK2) X0 sK2 sK2]
  have l11 : ∀ sK2 X0 : G, ((sK2 ◇ sK2) ◇ X0) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro sK2 X0
    conv => enter [1]; rw [l10 sK2 X0]
    conv => enter [1]; rw [l5 sK2 (sK2 ◇ sK2) X0]
  have l12 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK2 ◇ sK2) ◇ X1) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l9 X0 X1 sK2]
    conv => enter [1]; rw [l8 X1 sK2 X0]
  have l13 : ∀ X0 X1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ sK2)) := by
    intro X0 X1 sK2
    conv => enter [1]; rw [l12 X0 X1 sK2]
    conv => enter [1]; rw [l11 sK2 X1]
  have l14 : ∀ sK2 X1 X0 X2 X3 : G, (sK2 ◇ (sK2 ◇ sK2)) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro sK2 X1 X0 X2 X3
    conv => enter [1]; rw [← l13 X0 X1 sK2]
    conv => enter [1]; rw [h53905 X0 X1 X2 X3]
  have l15 : ∀ X1 X0 X2 X3 sK0 sK2 : G, (X1 ◇ (X0 ◇ (X2 ◇ X3))) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X1 X0 X2 X3 sK0 sK2
    conv => enter [1]; rw [← l14 sK2 X1 X0 X2 X3]
    conv => enter [1]; rw [l7 sK2 sK0]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK2 sK0]
  have l17 : ∀ X1 X2 X0 sK0 sK1 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK1)))) := by
    intro X1 X2 X0 sK0 sK1
    conv => enter [1]; rw [h53905 X1 X2 X1 X0]
    conv => enter [1, 2]; rw [h53905 X1 X0 sK0 sK1]
  have l18 : ∀ X1 X2 sK0 sK2 : G, (X1 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK2))) := by
    intro X1 X2 sK0 sK2
    conv => enter [1]; rw [l17 X1 X2 X1 sK0 X1]
    conv => enter [1]; rw [l15 X2 X1 X1 (sK0 ◇ X1) sK0 sK2]
  have l19 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ (X1 ◇ X2)) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [l18 X1 X2 sK0 X1]
    conv => enter [1]; rw [← l16 sK0 sK1 X1]
  have l20 : ∀ sK0 sK1 X1 X0 X2 X3 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro sK0 sK1 X1 X0 X2 X3
    conv => enter [1]; rw [l19 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h53905 X0 X1 X2 X3]
  intro x y z
  conv => enter [1]; rw [l20 x y y x z z]

theorem Equation4512_53905_implies_Equation53854 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53905 : Equation53905 G) : Equation53854 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK0 ◇ sK1) ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [h4512 sK0 sK1 sK1]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l2 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l4 : ∀ X1 sK1 X0 : G, (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK1 ◇ (sK1 ◇ X1)) := by
    intro X1 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [← h53905 sK1 X1 (sK1 ◇ sK1) X0]
  have l5 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (X0 ◇ X1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← l1 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 (sK1 ◇ sK1) sK0 X0 X1]
  have l6 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 sK1 sK0 X0 X1]
  have l7 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h53905 sK1 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ X1)]
  have l8 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l7 sK1 X0 X1]
  have l9 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l6 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h4512 sK1 sK1 sK0]
  have l10 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (X0 ◇ X1))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l5 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l3 sK1 sK0]
  have l11 : ∀ X1 sK1 X0 : G, (X1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ sK1) ◇ X1) := by
    intro X1 sK1 X0
    conv => enter [1]; rw [l4 X1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 X1]
  have l12 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l8 sK1 X0 X1]
  have l13 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l9 sK0 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l10 sK0 sK1 sK1 sK1]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l11 sK1 sK1 sK0]
    conv => enter [1]; rw [← l13 sK1 sK0]
  have l15 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l14 sK1 sK0]
  have l16 : ∀ sK1 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l15 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) sK0 X0]
  have l17 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l12 sK1 sK1 X0]
    conv => enter [1]; rw [← l16 sK1 X0 sK1]
  have l18 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1]; rw [l17 sK1 (X0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← h53905 X0 (sK1 ◇ (sK1 ◇ sK1)) sK1 sK1]
  have l19 : ∀ sK1 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l18 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l20 : ∀ sK1 X1 X0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X1 ◇ X0)) := by
    intro sK1 X1 X0
    conv => enter [1]; rw [l19 sK1 X0 X1]
    conv => enter [1]; rw [← h53905 X1 X0 (X0 ◇ X1) (sK1 ◇ (sK1 ◇ sK1))]
  have l21 : ∀ sK1 X0 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK1 X0 sK3 sK0
    conv => enter [1]; rw [l20 sK1 sK3 X0]
    conv => enter [1]; rw [h53905 sK3 X0 sK0 sK1]
  intro x y z w
  conv => enter [1]; rw [l21 x y z w]

theorem Equation4512_53905_implies_Equation53827 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53905 : Equation53905 G) : Equation53827 G := by
  have l0 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h53905 sK0 sK0 X0 X1]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ X1)]
  have l1 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l0 sK0 X0 X1]
  have l2 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 sK0 X0 X1]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l2 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h53905 X0 (sK0 ◇ sK0) sK0 sK0]
  have l4 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l3 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (sK0 ◇ sK0))]
  have l5 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l4 sK0 X0 X1]
    conv => enter [1]; rw [← h53905 X1 X0 (X0 ◇ X1) (sK0 ◇ sK0)]
  have l6 : ∀ sK0 X1 X0 X2 X3 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro sK0 X1 X0 X2 X3
    conv => enter [1]; rw [l5 sK0 X0 X1]
    conv => enter [1]; rw [h53905 X0 X1 X2 X3]
  intro x y z
  conv => enter [1]; rw [l6 x y x y z]

theorem Equation4512_53905_implies_Equation53846 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53905 : Equation53905 G) : Equation53846 G := by
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
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l4 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK0)) sK0 X0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l7 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 ((sK0 ◇ sK0) ◇ X0)]
    conv => enter [1, 2]; rw [l3 sK0 X0]
  have l9 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l9 sK0 X0]
    conv => enter [1]; rw [← h53905 (sK0 ◇ (sK0 ◇ sK0)) sK0 (sK0 ◇ sK0) X0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1, 2]; rw [← l4 sK0]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← l6 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l13 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (sK0 ◇ (sK0 ◇ X1)) := by
    intro X1 sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← h53905 sK0 X1 (sK0 ◇ sK0) X0]
  have l14 : ∀ sK1 sK0 X0 X1 X2 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ X2)))) = ((sK1 ◇ sK0) ◇ (X0 ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [← l7 sK1 sK0 (X0 ◇ (X1 ◇ X2))]
    conv => enter [1, 2]; rw [← h53905 X0 (sK0 ◇ sK0) X1 X2]
  have l15 : ∀ sK1 sK0 X0 X1 X2 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ X2)))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [l14 sK1 sK0 X0 X1 X2]
    conv => enter [1]; rw [← h53905 X0 (sK1 ◇ sK0) X0 (sK0 ◇ sK0)]
  have l16 : ∀ X1 sK0 X0 : G, (X1 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [l13 X1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 X1]
  have l17 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53905 (sK0 ◇ (sK0 ◇ sK0)) sK1 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l15 sK1 sK0 X0 sK0 sK0]
  have l18 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l12 sK0 sK1]
    conv => enter [1]; rw [l17 sK0 sK1 X0]
  have l19 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l16 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l18 sK0 X0 sK1]
  have l20 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l19 sK0 X0 sK1]
  have l21 : ∀ sK0 X0 X1 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 X1 sK1
    conv => enter [1]; rw [l20 sK0 (X0 ◇ X1) sK1]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (sK1 ◇ sK0))]
  have l22 : ∀ sK0 X1 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [l21 sK0 X0 X1 sK0]
    conv => enter [1]; rw [← h53905 X1 X0 (X0 ◇ X1) (sK0 ◇ sK0)]
  have l23 : ∀ sK0 X1 X0 X2 X3 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro sK0 X1 X0 X2 X3
    conv => enter [1]; rw [l22 sK0 X0 X1]
    conv => enter [1]; rw [h53905 X0 X1 X2 X3]
  intro x y z
  conv => enter [1]; rw [l23 x y z y x]

theorem Equation4512_54219_implies_Equation54215 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54219 : Equation54219 G) : Equation54215 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK0 sK0 ((sK1 ◇ sK0) ◇ X0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1]; rw [l0 sK0 sK1 X0]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h54219 X0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 sK0]
    conv => enter [1]; rw [h54219 sK1 sK0 X0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h54219 sK0 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l6 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h54219 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK0) sK0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l8 sK0 sK1]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0]
    conv => enter [1]; rw [l9 sK0 sK1]
  have l11 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [l4 sK1 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ sK0)]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l4 sK1 sK0 (sK0 ◇ sK0)]
  have l13 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l4 sK1 sK0 sK0]
  have l14 : ∀ sK0 X0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l4 sK1 sK0 X0]
  have l15 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1]; rw [← l14 sK0 X0 sK1]
  have l16 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l13 sK0 sK1]
  have l17 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [l11 sK1 sK0 X0 X1]
  have l18 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 sK1 X0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK0 sK1]
    conv => enter [1]; rw [← l17 sK0 sK1 (sK0 ◇ sK0) sK0]
  have l20 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h54219 (sK1 ◇ sK0) sK0 X0]
    conv => enter [1, 2, 2]; rw [← l16 sK0 sK1]
  have l21 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X0) = ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK0) sK0 X0]
  have l22 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l21 sK0 sK1 sK0]
    conv => enter [1]; rw [l20 sK1 sK0 X0]
  have l23 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l22 sK0 sK1 X0]
  have l24 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l19 sK0 sK1]
    conv => enter [1]; rw [l23 sK0 X0 sK1]
  have l25 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1]
  have l26 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK0]
    conv => enter [1, 2]; rw [← l12 sK0 sK1]
  have l27 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l27 sK0 sK1]
  have l29 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1]; rw [l28 sK0 sK1]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 sK1]
  have l31 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [h54219 X0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l3 X0 sK0]
  have l32 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h54219 sK0 sK0 X0]
    conv => enter [1]; rw [← l31 X0 sK0]
  have l33 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l30 sK0 sK1]
    conv => enter [1]; rw [l32 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l33 y z x]

theorem Equation4512_54219_implies_Equation53818 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54219 : Equation54219 G) : Equation53818 G := by
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
  have l8 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (X0 ◇ X0)) = (X0 ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h54219 sK0 X0 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK0 X0]
  have l9 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ sK0) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 sK0 sK0]
    conv => enter [1]; rw [h54219 sK2 sK0 X0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h54219 sK0 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l11 : ∀ sK2 sK0 : G, ((sK2 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l9 sK2 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK2 ◇ sK0)]
  have l12 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK2 ◇ sK0) ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK2 X0
    conv => enter [1, 2]; rw [l9 sK2 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK2 ◇ sK0))]
  have l13 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l8 sK0 sK0 sK2]
    conv => enter [1]; rw [l12 sK0 sK2 X0]
  have l14 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l13 sK0 X0 sK2]
  have l15 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l14 sK0 X0 sK2]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l9 sK2 sK0 sK1]
    conv => enter [1]; rw [l11 sK2 sK0]
  have l17 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l16 sK0 sK1 sK2]
    conv => enter [1]; rw [l7 sK0 (sK2 ◇ sK0)]
  have l18 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l16 sK0 sK1 sK2]
    conv => enter [1]; rw [l3 sK0 (sK2 ◇ sK0)]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l16 sK0 sK1 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) (sK2 ◇ sK0)]
  have l20 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l16 sK0 sK1 sK2]
    conv => enter [1]; rw [← l9 sK2 sK0 (sK0 ◇ sK0)]
  have l21 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l9 sK2 sK0 sK1]
    conv => enter [1]; rw [← l20 sK0 sK1 sK2]
  have l22 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 sK1 sK2]
    conv => enter [1]; rw [← l10 sK0 (sK2 ◇ sK0)]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK2]
    conv => enter [1]; rw [← l17 sK0 sK1 sK2]
  have l24 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l19 sK0 sK1 sK2]
    conv => enter [1]; rw [← l22 sK0 sK1 sK2]
  have l25 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l21 sK0 sK1 sK2]
    conv => enter [1]; rw [l24 sK0 sK1 sK2]
  have l26 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l21 sK0 sK1 sK2]
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l23 sK0 sK1 sK2]
    conv => enter [1]; rw [← l26 sK0 sK1 sK2]
  have l28 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 sK1 sK2]
    conv => enter [1]; rw [← l25 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l28 x y z]

theorem Equation4512_53875_implies_Equation53879 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53875 : Equation53875 G) : Equation53879 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) sK1 X0]
  have l2 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h53875 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ sK0)]
  have l4 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h53875 sK0 (sK2 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK0 ◇ sK0)) (X0 ◇ sK0)]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← l0 sK0 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h53875 (sK0 ◇ sK0) sK0 X0]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1 (X0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [← h53875 (sK0 ◇ sK0) sK1 X0]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [← l6 sK0 sK1 X0]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l9 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK2 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l4 sK0 sK2 X0]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l3 sK0 sK1 X0]
  have l11 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h53875 sK0 X0 sK0]
  have l12 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0)]
  have l13 : ∀ sK0 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK2 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l9 sK0 sK2 X0]
  have l14 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [l10 sK0 sK1 X0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l12 sK0 X0]
  have l16 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l14 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l18 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ ((X0 ◇ sK0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (X0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [← l14 sK0 sK1 X0]
  have l19 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ X1))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [← l18 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 sK0 X1]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l14 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK0)]
  have l21 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK0))]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1]
    conv => enter [1]; rw [← l7 sK0 sK1 sK0]
  have l23 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l24 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l11 sK0 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l25 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l11 sK0 X0]
    conv => enter [1]; rw [← h53875 (sK0 ◇ sK0) sK0 X0]
  have l26 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l25 sK0 X0]
    conv => enter [1]; rw [h53875 (sK0 ◇ sK0) sK0 sK2]
  have l27 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l24 sK0 X0]
    conv => enter [1]; rw [← l15 sK0 X0]
  have l28 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l23 sK0]
  have l29 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l26 sK0 X0 sK2]
    conv => enter [1]; rw [l0 sK0 (sK2 ◇ (sK0 ◇ sK0))]
  have l30 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l29 sK0 X0 sK2]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK2 ◇ (sK0 ◇ sK0))]
  have l31 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l30 sK0 X0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))]
  have l32 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l27 sK0 sK0]
    conv => enter [1]; rw [l31 sK0 sK0 sK2]
  have l33 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l28 sK0]
    conv => enter [1]; rw [l32 sK0 sK2]
  have l34 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1, 2]; rw [l28 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l35 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l28 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l36 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l35 sK0 X0]
    conv => enter [1]; rw [l27 sK0 X0]
  have l37 : ∀ sK2 sK0 : G, ((sK2 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK2 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK2 sK0
    conv => enter [1]; rw [l2 sK2 sK0]
    conv => enter [1]; rw [l34 sK2 sK0]
  have l38 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l28 sK0]
    conv => enter [1]; rw [← l36 sK0 X0]
  have l39 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l38 sK0 X0]
  have l40 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l11 sK0 (sK2 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← l37 sK2 sK0]
  have l41 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [l40 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK0 ◇ sK0)) sK0]
  have l42 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [h4512 sK0 sK0 (sK2 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l41 sK0 sK2]
  have l43 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) ◇ X0) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l42 sK0 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) sK0 X0]
  have l44 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ X0)) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) X0]
    conv => enter [1]; rw [l43 sK0 sK2 X0]
  have l45 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l13 sK0 sK2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l46 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l45 sK0 sK2]
    conv => enter [1]; rw [← l44 sK0 sK2 (sK0 ◇ sK0)]
  have l47 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l46 sK0 sK2]
    conv => enter [1]; rw [← l11 sK0 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))]
  have l48 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l33 sK0 sK2]
    conv => enter [1]; rw [← l47 sK0 sK2]
  have l49 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 sK1 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l50 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l49 sK0 sK1 sK0]
    conv => enter [1]; rw [← l19 sK0 sK1 (sK0 ◇ sK0) sK0]
  have l51 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [← l20 sK0 sK1]
  have l52 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l39 sK0 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l52 sK0 sK1]
  have l54 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [← l22 sK0 sK1]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [← l54 sK0 sK1]
  have l56 : ∀ sK2 sK0 sK1 : G, ((sK2 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l2 sK2 sK0]
    conv => enter [1, 2]; rw [← l55 sK0 sK1]
  have l57 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK0]
    conv => enter [1, 2]; rw [← l55 sK0 sK1]
  have l58 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 sK1]
    conv => enter [1]; rw [← l57 sK0 sK1]
  have l59 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l13 sK0 sK2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l58 sK0 sK1]
  have l60 : ∀ sK0 X0 sK1 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h53875 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← l58 sK0 sK1]
  have l61 : ∀ sK0 X0 sK1 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l60 sK0 X0 sK1]
  have l62 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l48 sK0 sK2]
    conv => enter [1]; rw [l59 sK0 sK2 sK1]
  have l63 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l55 sK0 sK1]
    conv => enter [1]; rw [l62 sK0 sK2 sK1]
  have l64 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l63 sK0 sK1 sK2]
    conv => enter [1]; rw [← l59 sK0 sK2 sK1]
  have l65 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ sK2) = (sK0 ◇ ((sK2 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [l61 sK0 sK2 sK0]
    conv => enter [1, 2]; rw [← l56 sK2 sK0 sK0]
  have l66 : ∀ sK0 sK2 : G, ((sK0 ◇ sK0) ◇ sK2) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [l65 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK0 ◇ sK0)) sK0]
  have l67 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ sK2) := by
    intro sK0 sK2
    conv => enter [1]; rw [l42 sK0 sK2]
    conv => enter [1]; rw [← l66 sK0 sK2]
  have l68 : ∀ sK0 sK2 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK2
    conv => enter [1]; rw [← l11 sK0 sK2]
    conv => enter [1]; rw [← l67 sK0 sK2]
  have l69 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l64 sK0 sK1 sK2]
    conv => enter [1]; rw [← l68 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l69 x y z]

theorem Equation4512_53875_implies_Equation53818 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53875 : Equation53875 G) : Equation53818 G := by
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
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ X0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53875 sK0 X0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK0]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l1 sK0 X0]
    conv => enter [1]; rw [← h53875 X0 (sK0 ◇ sK0) sK0]
  have l6 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h53875 sK0 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ sK0)]
  have l7 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h53875 (sK0 ◇ sK0) sK0 X0]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l8 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l3 sK0 sK0]
    conv => enter [1]; rw [l7 sK0 X0]
  have l9 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l6 sK0 X0]
  have l10 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [l4 sK0 X0]
  have l11 : ∀ sK0 X0 sK2 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h53875 sK0 X0 sK2]
  have l12 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
    conv => enter [1]; rw [h53875 sK0 X0 sK0]
  have l13 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l5 sK0 sK0]
    conv => enter [1]; rw [l8 sK0 X0]
  have l14 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l9 sK0 X0]
  have l15 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l13 sK0 X0]
  have l16 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l15 sK0 X0]
  have l17 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l14 sK0 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l18 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l17 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
  have l19 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l12 sK0 X0]
    conv => enter [1]; rw [← l1 sK0 (X0 ◇ (sK0 ◇ sK0))]
  have l20 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l16 sK0 X0]
    conv => enter [1]; rw [← l19 sK0 X0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [l20 sK0 X0]
  have l22 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l21 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [← l1 sK0 X0]
  have l23 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ X0) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) ((sK0 ◇ sK0) ◇ X0) X1]
    conv => enter [1, 1]; rw [← l21 sK0 X0]
  have l24 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1, 2]; rw [h4512 (sK0 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l23 sK0 X0 X1]
  have l25 : ∀ sK0 X0 X1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l3 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [l24 sK0 X0 X1]
  have l26 : ∀ sK0 X0 X1 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l18 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [l25 sK0 X0 X1]
  have l27 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l22 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0)]
  have l28 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [← l26 sK0 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1]; rw [← l27 sK0 X0]
  have l29 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l17 sK0]
    conv => enter [1]; rw [← l28 sK0 X0]
  have l30 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [l10 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l31 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1, 1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) X1]
  have l32 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ X1))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l31 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ sK0)) X1]
  have l33 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l30 sK0 X0]
  have l34 : ∀ sK0 X0 X1 : G, (((sK0 ◇ sK0) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l32 sK0 X0 X1]
    conv => enter [1, 2, 2]; rw [← l29 sK0 X1]
  have l35 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [l29 sK0 X0]
    conv => enter [1]; rw [l33 sK0 X0]
  have l36 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = (((sK0 ◇ sK0) ◇ X0) ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l10 sK0 X0]
    conv => enter [1]; rw [← l34 sK0 X0 X1]
  have l37 : ∀ sK0 X0 X1 : G, ((sK0 ◇ sK0) ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X1)) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l36 sK0 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) X0 X1]
  have l38 : ∀ sK0 X0 X1 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l35 sK0 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ (sK0 ◇ sK0))]
  have l39 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l38 sK0 X0 sK0]
    conv => enter [1]; rw [← l37 sK0 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  have l40 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l11 sK0 sK1 sK2]
    conv => enter [1]; rw [← l39 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l40 x y z]

theorem Equation4512_54239_implies_Equation54187 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54239 : Equation54239 G) : Equation54187 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54239 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 sK2 sK1 X1 : G, (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (X1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK2 sK1 X1
    conv => enter [1]; rw [← h54239 sK2 sK1 X0]
    conv => enter [1]; rw [h54239 sK2 sK1 X1]
  have l2 : ∀ X0 sK2 sK1 X1 X2 : G, (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (X1 ◇ (X2 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK2 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK2 sK1 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK2 ◇ (sK1 ◇ sK2))]
  have l3 : ∀ X0 sK2 sK1 X1 sK0 : G, (X0 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (X1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK2 sK1 X1 sK0
    conv => enter [1]; rw [l2 X0 sK2 sK1 X1 X0]
    conv => enter [1, 2]; rw [l1 X0 sK2 sK1 sK0]
  have l4 : ∀ sK0 sK2 sK1 X1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (X1 ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK2 sK1 X1
    conv => enter [1]; rw [l3 sK0 sK2 sK1 X1 sK0]
  have l5 : ∀ sK2 sK1 X0 X1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) = (X1 ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))))) := by
    intro sK2 sK1 X0 X1 sK0
    conv => enter [1]; rw [h54239 (sK2 ◇ (sK1 ◇ sK2)) X0 X1]
    conv => enter [1, 2, 2]; rw [l1 X0 sK2 sK1 sK0]
  have l6 : ∀ X0 sK2 sK1 X1 sK0 : G, (X0 ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ X1)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X1) := by
    intro X0 sK2 sK1 X1 sK0
    conv => enter [1]; rw [h4512 X0 (sK2 ◇ (sK1 ◇ sK2)) X1]
    conv => enter [1, 1]; rw [l1 X0 sK2 sK1 sK0]
  have l7 : ∀ sK2 sK1 X0 sK0 : G, ((sK2 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2)))) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [l5 sK2 sK1 X0 sK2 sK0]
    conv => enter [1]; rw [l6 sK2 sK2 sK1 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) sK0]
  have l8 : ∀ sK0 sK2 sK1 X0 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK2 sK1 (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [← l7 sK2 sK1 X0 sK0]
  have l9 : ∀ sK0 sK2 sK1 X0 X1 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK2 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1]; rw [l8 sK0 sK2 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l10 : ∀ sK0 sK2 sK1 X1 X0 : G, (sK0 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 sK2 sK1 X1 X0
    conv => enter [1]; rw [l9 sK0 sK2 sK1 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0 (sK2 ◇ (sK1 ◇ sK2)) X0]
  intro x y z
  conv => enter [1]; rw [← l10 x z y x y]

theorem Equation4512_54239_implies_Equation54253 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54239 : Equation54239 G) : Equation54253 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54239 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK0]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54239 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK1) = (X0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l0 sK0 sK1 X0]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
    conv => enter [1]; rw [l2 sK0 sK1 X0]
  have l4 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l3 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((sK0 ◇ sK1) ◇ sK0)]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← l3 sK0 sK1 sK0]
  have l6 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h54239 (sK0 ◇ (sK1 ◇ sK1)) X0 X1]
    conv => enter [1, 2, 2]; rw [← l5 sK0 sK1 X0]
  have l7 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1) = (X0 ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ sK1)) X1]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1)) sK0]
    conv => enter [1]; rw [← l6 sK0 sK1 X0 sK0]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l8 sK0 sK1 X0]
  have l10 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l9 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l11 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l10 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l1 X1 X0 (sK0 ◇ (sK1 ◇ sK1)) X0]
  have l12 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 sK1 sK0]
    conv => enter [1]; rw [h54239 sK1 sK0 X0]
  intro x y z
  conv => enter [1]; rw [l12 x y z]

theorem Equation4512_54239_implies_Equation54243 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54239 : Equation54239 G) : Equation54243 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l1 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK1 sK0]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l4 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) = (((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = ((X1 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h54239 X0 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [← h54239 (X1 ◇ X0) X0 X2]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h54239 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [l5 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l8 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54239 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X1 ◇ X0))]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) = (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l5 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l7 sK0 sK1 X0]
  have l10 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l6 X2 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 (X0 ◇ X0)]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) = (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
    conv => enter [1]; rw [l9 sK0 sK1 X0]
  have l12 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ X0)) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l10 X2 X0 X1]
    conv => enter [1]; rw [← h54239 X0 X0 X1]
  have l13 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l11 sK0 sK1 X0]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l12 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [← l13 sK0 sK1 sK0]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l14 sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 sK1]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l17 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [← h54239 sK1 sK0 X0]
    conv => enter [1]; rw [h54239 sK1 sK0 X1]
  have l18 : ∀ X0 sK1 sK0 X1 X2 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X1 ◇ (X2 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0 X1 X2
    conv => enter [1]; rw [l17 X0 sK1 sK0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK1 ◇ (sK0 ◇ sK1))]
  have l19 : ∀ X0 sK1 sK0 X1 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0 X1
    conv => enter [1]; rw [l18 X0 sK1 sK0 X1 X0]
    conv => enter [1, 2]; rw [l17 X0 sK1 sK0 sK0]
  have l20 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l19 sK0 sK1 sK0 X1]
  have l21 : ∀ sK1 sK0 X0 X1 : G, ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0)) = (X1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0 X0 X1
    conv => enter [1]; rw [h54239 (sK1 ◇ (sK0 ◇ sK1)) X0 X1]
    conv => enter [1, 2, 2]; rw [l17 X0 sK1 sK0 sK0]
  have l22 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X1) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l17 sK0 sK1 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK0 ◇ sK1)) X1]
  have l23 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l22 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK0]
    conv => enter [1]; rw [← l21 sK1 sK0 X0 sK0]
  have l24 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 sK1]
    conv => enter [1]; rw [l23 sK0 sK1 X0]
  have l25 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l20 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l24 sK0 sK1 X0]
  have l26 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l25 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l27 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l26 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l8 X1 X0 (sK1 ◇ (sK0 ◇ sK1)) X0]
  intro x y z
  conv => enter [1]; rw [← l27 z x x y]

theorem Equation4512_54239_implies_Equation54275 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54239 : Equation54239 G) : Equation54275 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54239 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [← h54239 sK0 sK1 X0]
    conv => enter [1]; rw [h54239 sK0 sK1 X1]
  have l2 : ∀ X0 sK0 sK1 X1 X2 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ (X2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1 X1 X2
    conv => enter [1]; rw [l1 X0 sK0 sK1 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4512 X1 X2 (sK0 ◇ (sK1 ◇ sK0))]
  have l3 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [l2 X0 sK0 sK1 X1 X0]
    conv => enter [1, 2]; rw [l1 X0 sK0 sK1 sK0]
  have l4 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l3 sK0 sK0 sK1 X1]
  have l5 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X0)) = (X1 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h54239 (sK0 ◇ (sK1 ◇ sK0)) X0 X1]
    conv => enter [1, 2, 2]; rw [l1 X0 sK0 sK1 sK0]
  have l6 : ∀ X0 sK0 sK1 X1 : G, (X0 ◇ ((sK0 ◇ (sK1 ◇ sK0)) ◇ X1)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ X1) := by
    intro X0 sK0 sK1 X1
    conv => enter [1]; rw [h4512 X0 (sK0 ◇ (sK1 ◇ sK0)) X1]
    conv => enter [1, 1]; rw [l1 X0 sK0 sK1 sK0]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0 sK0]
    conv => enter [1]; rw [l6 sK0 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))]
    conv => enter [1]; rw [← l7 sK0 sK1 X0]
  have l9 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l8 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l10 : ∀ sK0 sK1 X1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (X1 ◇ (X0 ◇ X0)) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l0 X1 X0 (sK0 ◇ (sK1 ◇ sK0)) X0]
  intro x y z
  conv => enter [1]; rw [← l10 z y x y]

theorem Equation4512_54239_implies_Equation53844 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h54239 : Equation54239 G) : Equation53844 G := by
  have l0 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK0) sK2 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK0 sK2]
  have l1 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ sK0) ◇ (sK2 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [l0 sK0 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK2) X0]
  have l2 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ sK0)) = (X1 ◇ ((sK0 ◇ X0) ◇ ((sK0 ◇ sK0) ◇ X0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h54239 (sK0 ◇ X0) sK0 X1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK0 X0]
  have l3 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = (X0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h54239 sK0 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ X1)) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h54239 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h4512 X2 X3 (X0 ◇ (X1 ◇ X0))]
  have l5 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [l3 sK0 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l6 : ∀ sK0 X0 X1 : G, ((sK0 ◇ X0) ◇ (sK0 ◇ sK0)) = (X1 ◇ (sK0 ◇ (X0 ◇ ((sK0 ◇ sK0) ◇ X0)))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [l2 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 ((sK0 ◇ sK0) ◇ X0)]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ X0) ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [l4 X0 (sK0 ◇ sK0) X0 sK0]
    conv => enter [1]; rw [← l6 sK0 X0 X0]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1]; rw [l7 X0 sK0]
    conv => enter [1]; rw [← h4512 sK0 X0 (sK0 ◇ sK0)]
  have l9 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l8 X0 sK0]
  have l10 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [l5 sK0 sK0]
    conv => enter [1]; rw [l9 X0 sK0]
  have l11 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (X0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [l5 sK0 X0]
    conv => enter [1]; rw [l10 X0 sK0]
  have l12 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [← l1 sK0 sK2 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [h54239 sK2 sK0 X0]
  have l13 : ∀ sK2 sK0 X0 X1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0 X0 X1
    conv => enter [1]; rw [h54239 sK2 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ (sK0 ◇ sK2))]
  have l14 : ∀ sK1 sK2 sK0 X0 X1 : G, (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [← h54239 sK2 sK0 sK1]
    conv => enter [1]; rw [l13 sK2 sK0 X0 X1]
  have l15 : ∀ sK0 X0 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l11 sK0 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l12 sK0 sK2 X0]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 sK0 sK2]
    conv => enter [1]; rw [← l14 sK1 sK2 sK0 (sK0 ◇ sK0) sK0]
  intro x y z
  conv => enter [1]; rw [l16 x y z]

end Semigroup5
