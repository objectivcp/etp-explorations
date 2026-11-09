import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_53905_implies_Equation53988 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53905 : Equation53905 G) : Equation53988 G := by
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
  have l4 : ∀ sK2 sK0 X0 X1 X2 X3 : G, ((sK2 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK2 ◇ sK0) ◇ (X2 ◇ X3)) := by
    intro sK2 sK0 X0 X1 X2 X3
    conv => enter [1]; rw [l3 sK2 sK0 X0 X1]
    conv => enter [1]; rw [← l3 sK2 sK0 X2 X3]
  have l5 : ∀ sK1 sK2 sK0 X0 X1 X2 X3 : G, (sK1 ◇ ((sK2 ◇ sK0) ◇ (X0 ◇ X1))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X2 ◇ X3)) := by
    intro sK1 sK2 sK0 X0 X1 X2 X3
    conv => enter [1, 2]; rw [l4 sK2 sK0 X0 X1 X2 X3]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK0) (X2 ◇ X3)]
  have l6 : ∀ sK1 sK2 sK0 X2 X3 : G, ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X2 ◇ X3)) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK2 sK0 X2 X3
    conv => enter [1]; rw [← l5 sK1 sK2 sK0 sK1 sK1 X2 X3]
    conv => enter [1]; rw [← h53905 (sK2 ◇ sK0) sK1 sK1 sK1]
  have l7 : ∀ sK2 sK0 sK4 sK1 X2 X3 : G, ((sK2 ◇ sK0) ◇ (sK4 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ (X2 ◇ X3)) := by
    intro sK2 sK0 sK4 sK1 X2 X3
    conv => enter [1]; rw [l4 sK2 sK0 sK4 (sK1 ◇ (sK2 ◇ sK0)) (sK2 ◇ sK0) sK1]
    conv => enter [1]; rw [← l6 sK1 sK2 sK0 X2 X3]
  have l8 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h53905 (sK2 ◇ sK0) X0 sK2 sK2]
    conv => enter [1, 2]; rw [l3 sK2 sK0 sK2 sK2]
  have l9 : ∀ sK4 sK1 sK2 sK0 X0 X1 : G, ((sK4 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK2 ◇ sK0)) ◇ ((sK1 ◇ (sK2 ◇ sK0)) ◇ sK4)) := by
    intro sK4 sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK4 (sK1 ◇ (sK2 ◇ sK0)) (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 (sK1 ◇ (sK2 ◇ sK0)) sK4 X0 X1]
  have l10 : ∀ sK4 sK1 sK2 sK0 X0 X1 : G, ((sK4 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ X1)) = ((sK2 ◇ sK0) ◇ (sK4 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK4 sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [l9 sK4 sK1 sK2 sK0 X0 X1]
    conv => enter [1]; rw [← l7 sK2 sK0 sK4 sK1 (sK1 ◇ (sK2 ◇ sK0)) sK4]
  have l11 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [l8 sK2 sK0 X0]
    conv => enter [1]; rw [← h53905 sK0 X0 sK0 sK2]
  have l12 : ∀ sK4 sK1 sK2 sK0 X0 X1 sK3 : G, ((sK4 ◇ (sK1 ◇ (sK2 ◇ sK0))) ◇ (X0 ◇ X1)) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK3)) := by
    intro sK4 sK1 sK2 sK0 X0 X1 sK3
    conv => enter [1]; rw [l10 sK4 sK1 sK2 sK0 X0 X1]
    conv => enter [1]; rw [l4 sK2 sK0 sK4 (sK1 ◇ (sK2 ◇ sK0)) sK2 sK3]
  have l13 : ∀ sK2 sK0 sK4 sK1 X0 : G, ((sK2 ◇ sK0) ◇ (sK4 ◇ (sK1 ◇ (sK2 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK2 sK0 sK4 sK1 X0
    conv => enter [1]; rw [l4 sK2 sK0 sK4 (sK1 ◇ (sK2 ◇ sK0)) (sK2 ◇ sK0) X0]
    conv => enter [1]; rw [l11 sK2 sK0 X0]
  have l14 : ∀ sK2 sK0 sK3 X0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK3)) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK2 sK0 sK3 X0
    conv => enter [1]; rw [l4 sK2 sK0 sK2 sK3 sK2 (sK2 ◇ (sK2 ◇ sK0))]
    conv => enter [1]; rw [l13 sK2 sK0 sK2 sK2 X0]
  have l15 : ∀ sK2 sK0 sK3 X0 sK4 sK1 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK3)) = (X0 ◇ (X0 ◇ (sK4 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro sK2 sK0 sK3 X0 sK4 sK1
    conv => enter [1]; rw [← l12 sK4 sK1 sK2 sK0 X0 (sK2 ◇ sK2) sK3]
    conv => enter [1]; rw [← h53905 X0 (sK4 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK2 sK2]
  have l16 : ∀ sK2 sK0 sK3 X0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK3)) = (sK0 ◇ (X0 ◇ (X0 ◇ sK0))) := by
    intro sK2 sK0 sK3 X0
    conv => enter [1]; rw [l14 sK2 sK0 sK3 (X0 ◇ (sK2 ◇ sK2))]
    conv => enter [1, 2]; rw [← h53905 X0 sK0 sK2 sK2]
  have l17 : ∀ sK2 sK0 sK3 X0 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK3)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK2 sK0 sK3 X0
    conv => enter [1]; rw [l16 sK2 sK0 sK3 X0]
    conv => enter [1]; rw [← h53905 X0 sK0 X0 sK0]
  have l18 : ∀ sK2 sK0 sK3 X0 X1 sK4 sK1 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK3)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (sK4 ◇ (sK1 ◇ (sK2 ◇ sK0)))))) := by
    intro sK2 sK0 sK3 X0 X1 sK4 sK1
    conv => enter [1]; rw [l15 sK2 sK0 sK3 (X0 ◇ X1) sK4 sK1]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (sK4 ◇ (sK1 ◇ (sK2 ◇ sK0))))]
  have l19 : ∀ X1 X0 sK2 sK0 sK3 : G, (X1 ◇ (X1 ◇ X0)) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK3)) := by
    intro X1 X0 sK2 sK0 sK3
    conv => enter [1]; rw [h53905 X1 X0 (X0 ◇ X1) (X1 ◇ (X1 ◇ (sK2 ◇ sK0)))]
    conv => enter [1]; rw [← l18 sK2 sK0 sK3 X0 X1 X1 X1]
  have l20 : ∀ sK2 sK0 sK3 X1 X0 X2 X3 : G, ((sK2 ◇ sK0) ◇ (sK2 ◇ sK3)) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro sK2 sK0 sK3 X1 X0 X2 X3
    conv => enter [1]; rw [← l19 X0 X1 sK2 sK0 sK3]
    conv => enter [1]; rw [h53905 X0 X1 X2 X3]
  have l21 : ∀ X1 X0 X2 X3 sK2 sK0 : G, (X1 ◇ (X0 ◇ (X2 ◇ X3))) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro X1 X0 X2 X3 sK2 sK0
    conv => enter [1]; rw [← l20 sK2 sK0 X1 X1 X0 X2 X3]
    conv => enter [1]; rw [l17 sK2 sK0 X1 sK2]
  have l22 : ∀ sK2 sK3 sK0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK2 sK3 sK0
    conv => enter [1]; rw [l19 sK2 sK3 sK2 sK0 sK3]
    conv => enter [1]; rw [l17 sK2 sK0 sK3 sK2]
  have l23 : ∀ X1 X2 X0 sK1 sK2 sK0 : G, (X1 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ sK0))))) := by
    intro X1 X2 X0 sK1 sK2 sK0
    conv => enter [1]; rw [h53905 X1 X2 X1 X0]
    conv => enter [1, 2]; rw [h53905 X1 X0 sK1 (sK2 ◇ sK0)]
  have l24 : ∀ X1 X2 sK2 sK0 : G, (X1 ◇ (X1 ◇ X2)) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro X1 X2 sK2 sK0
    conv => enter [1]; rw [l23 X1 X2 X1 X1 sK2 sK0]
    conv => enter [1]; rw [l21 X2 X1 X1 (X1 ◇ (sK2 ◇ sK0)) sK2 sK0]
  have l25 : ∀ X1 X2 sK2 sK3 : G, (X1 ◇ (X1 ◇ X2)) = (sK2 ◇ (sK2 ◇ sK3)) := by
    intro X1 X2 sK2 sK3
    conv => enter [1]; rw [l24 X1 X2 sK2 X1]
    conv => enter [1]; rw [l22 sK2 X1 sK3]
  have l26 : ∀ sK2 sK3 X1 X0 X2 X3 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro sK2 sK3 X1 X0 X2 X3
    conv => enter [1]; rw [l25 sK2 sK3 X0 X1]
    conv => enter [1]; rw [h53905 X0 X1 X2 X3]
  intro x y z w u
  conv => enter [1]; rw [l26 x y z w x u]

@[equational_result]
theorem Equation53988_implies_Equation53905 (G : Type*) [Magma G] (h53988 : Equation53988 G) : Equation53905 G := by
  have l0 : ∀ sK1 sK2 X1 X2 X0 X3 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X2 ◇ (X0 ◇ X3))) := by
    intro sK1 sK2 X1 X2 X0 X3
    conv => enter [1]; rw [h53988 sK1 sK2 X0 X0 sK2]
    conv => enter [1]; rw [h53988 X0 (sK1 ◇ sK2) X1 X2 X3]
  intro x y z w
  conv => enter [1]; rw [l0 x y y x z w]

theorem Equation4512_53905_implies_Equation53989 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53905 : Equation53905 G) : Equation53989 G := by
  have l0 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ X0)) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK2) sK1 X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK2 sK1]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) X0]
  have l2 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK2) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK2 sK1]
  have l3 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ X0)) = (sK2 ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK2 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 X0]
  have l4 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK1 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ sK2) X0]
  have l5 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ sK2) ◇ (sK1 ◇ X0))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l3 sK2 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 X0]
  have l6 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l5 sK2 sK1 X0]
    conv => enter [1]; rw [← h53905 (sK1 ◇ sK2) sK2 sK1 X0]
  have l7 : ∀ sK2 sK1 X0 : G, (sK2 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ X0))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ ((sK2 ◇ sK1) ◇ X0))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l4 sK2 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [l1 sK1 sK2 X0]
  have l8 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ X0))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h53905 sK1 (sK2 ◇ sK1) (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [← l7 sK2 sK1 X0]
  have l9 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l8 sK1 sK2 sK1]
    conv => enter [1]; rw [← h53905 (sK1 ◇ (sK1 ◇ sK2)) sK2 sK1 sK1]
  have l10 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l2 sK1 sK2]
    conv => enter [1]; rw [l9 sK1 sK2]
  have l11 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK2)) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← l6 sK2 sK1 ((sK2 ◇ sK1) ◇ sK1)]
    conv => enter [1, 2]; rw [l6 sK2 sK1 sK1]
  have l12 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK2)) = (sK2 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ sK2) ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l11 sK1 sK2]
    conv => enter [1]; rw [l4 sK2 sK1 ((sK1 ◇ sK2) ◇ sK2)]
  have l13 : ∀ sK1 sK2 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l12 sK1 sK2]
    conv => enter [1]; rw [← h53905 (sK1 ◇ (sK1 ◇ sK2)) sK2 (sK1 ◇ sK2) sK2]
  have l14 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l10 sK1 sK2]
    conv => enter [1]; rw [← l13 sK1 sK2]
  have l15 : ∀ sK1 X0 sK2 : G, (sK1 ◇ (sK1 ◇ X0)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h53905 sK1 X0 sK1 (sK2 ◇ sK1)]
    conv => enter [1, 2]; rw [← l2 sK1 sK2]
  have l16 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ (sK1 ◇ ((sK2 ◇ sK1) ◇ X0))) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X1)) := by
    intro X1 sK1 sK2 X0
    conv => enter [1, 2]; rw [← l1 sK1 sK2 X0]
    conv => enter [1]; rw [← h53905 (sK1 ◇ sK2) X1 sK1 X0]
  have l17 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0)) = (X0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h53905 (sK1 ◇ sK2) X0 (sK1 ◇ sK2) sK2]
    conv => enter [1, 2]; rw [← l14 sK1 sK2]
  have l18 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = (X0 ◇ ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK2))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h53905 (sK2 ◇ sK1) X0 (sK2 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [l6 sK2 sK1 sK2]
  have l19 : ∀ sK0 sK2 sK1 X0 X1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X1)) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ sK1) (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 (sK2 ◇ sK1) sK0 X0 X1]
  have l20 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ sK2) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 sK2 sK1 X0 X1]
  have l21 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK2 ◇ sK1) ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h53905 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h4512 sK2 sK1 (X0 ◇ X1)]
  have l22 : ∀ sK0 sK2 sK1 X0 X1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ sK2)) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1]; rw [l19 sK0 sK2 sK1 X0 X1]
    conv => enter [1]; rw [l6 sK2 sK1 sK0]
  have l23 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l18 sK2 sK1 X0]
    conv => enter [1]; rw [← h53905 (sK1 ◇ sK2) X0 (sK1 ◇ sK2) sK2]
  have l24 : ∀ sK1 X1 sK2 : G, (sK1 ◇ (sK1 ◇ X1)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X1)) := by
    intro sK1 X1 sK2
    conv => enter [1]; rw [h53905 sK1 X1 (sK2 ◇ sK1) sK1]
    conv => enter [1]; rw [l16 X1 sK1 sK2 sK1]
  have l25 : ∀ sK0 sK2 sK1 X0 X1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X1)) = (sK2 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK1)) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1]; rw [l22 sK0 sK2 sK1 X0 X1]
    conv => enter [1]; rw [l17 sK1 sK2 sK2]
  have l26 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l23 sK2 sK1 X0]
    conv => enter [1]; rw [l20 sK1 sK2 (sK1 ◇ sK2) X0]
  have l27 : ∀ sK1 X1 sK2 : G, (sK1 ◇ (sK1 ◇ X1)) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 X1 sK2
    conv => enter [1]; rw [l24 sK1 X1 sK2]
    conv => enter [1]; rw [l20 sK1 sK2 (sK1 ◇ sK2) X1]
  have l28 : ∀ sK1 sK2 sK0 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [l15 sK1 sK2 sK2]
    conv => enter [1]; rw [← l25 sK0 sK2 sK1 X0 X1]
  have l29 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l21 sK1 sK2 (sK2 ◇ sK1) sK1]
    conv => enter [1]; rw [l26 sK2 sK1 sK1]
  have l30 : ∀ sK0 sK2 sK1 X0 X1 : G, ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK2 sK1 X0 X1
    conv => enter [1]; rw [← l28 sK1 sK2 sK0 X0 X1]
    conv => enter [1]; rw [l27 sK1 sK2 sK2]
  have l31 : ∀ sK1 sK2 sK0 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ (sK2 ◇ sK1)) ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 sK0 X0 X1
    conv => enter [1]; rw [l29 sK1 sK2]
    conv => enter [1]; rw [← l30 sK0 sK2 sK1 X0 X1]
  have l32 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l31 sK1 sK2 sK0 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h53905 X0 (sK0 ◇ (sK2 ◇ sK1)) sK1 sK1]
  have l33 : ∀ sK1 sK2 X0 X1 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (sK0 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK2 X0 X1 sK0
    conv => enter [1]; rw [l32 sK1 sK2 (X0 ◇ X1) sK0]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (sK0 ◇ (sK2 ◇ sK1)))]
  have l34 : ∀ sK1 sK2 X1 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [l33 sK1 sK2 X0 X1 sK1]
    conv => enter [1]; rw [← h53905 X1 X0 (X0 ◇ X1) (sK1 ◇ (sK2 ◇ sK1))]
  have l35 : ∀ sK1 sK2 X1 X0 X2 X3 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro sK1 sK2 X1 X0 X2 X3
    conv => enter [1]; rw [l34 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h53905 X0 X1 X2 X3]
  intro x y z w
  conv => enter [1]; rw [l35 x y z w y x]

theorem Equation4512_53989_implies_Equation53905 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53989 : Equation53989 G) : Equation53905 G := by
  have l0 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ X0)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h53989 X0 X1 sK1 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (X1 ◇ X0)]
  have l1 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK3 ◇ sK0) ◇ (X1 ◇ X0)) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [h53989 X0 X1 sK3 sK0]
    conv => enter [1]; rw [h4512 sK3 sK0 (X1 ◇ X0)]
  have l2 : ∀ X0 X1 sK3 sK0 : G, (X0 ◇ (X1 ◇ (sK3 ◇ sK0))) = ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)) := by
    intro X0 X1 sK3 sK0
    conv => enter [1]; rw [← h53989 sK0 sK3 X0 X1]
    conv => enter [1]; rw [l1 sK0 sK3 sK3 sK0]
  have l3 : ∀ sK1 sK3 sK0 X0 X1 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0 X0 X1
    conv => enter [1]; rw [l1 sK1 (sK3 ◇ sK0) sK3 sK0]
    conv => enter [1]; rw [h53989 (sK3 ◇ sK0) sK1 X0 X1]
  have l4 : ∀ sK3 sK0 sK1 sK2 : G, ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ sK0)) := by
    intro sK3 sK0 sK1 sK2
    conv => enter [1]; rw [← l2 sK1 (sK1 ◇ sK2) sK3 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK3 ◇ sK0)]
  have l5 : ∀ X1 sK1 sK3 sK0 X0 : G, (X1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (X0 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro X1 sK1 sK3 sK0 X0
    conv => enter [1]; rw [l2 X1 sK1 sK3 sK0]
    conv => enter [1]; rw [← l2 X0 sK1 sK3 sK0]
  have l6 : ∀ X0 X1 sK1 sK3 sK0 : G, (X0 ◇ (X1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)) := by
    intro X0 X1 sK1 sK3 sK0
    conv => enter [1]; rw [h4512 X0 X1 (sK1 ◇ (sK3 ◇ sK0))]
    conv => enter [1]; rw [l2 (X0 ◇ X1) sK1 sK3 sK0]
  have l7 : ∀ sK3 sK0 X1 X0 sK1 : G, ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ X1)) = ((X0 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X1) := by
    intro sK3 sK0 X1 X0 sK1
    conv => enter [1]; rw [h4512 (sK3 ◇ sK0) (sK3 ◇ sK0) X1]
    conv => enter [1, 1]; rw [← l2 X0 sK1 sK3 sK0]
  have l8 : ∀ X0 sK1 sK3 sK0 X1 : G, (X0 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X1)) = ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ X1)) := by
    intro X0 sK1 sK3 sK0 X1
    conv => enter [1]; rw [h4512 X0 (sK1 ◇ (sK3 ◇ sK0)) X1]
    conv => enter [1]; rw [← l7 sK3 sK0 X1 X0 sK1]
  have l9 : ∀ X0 X1 sK1 sK3 sK0 sK2 : G, (X0 ◇ (X1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ sK0)) := by
    intro X0 X1 sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l6 X0 X1 sK1 sK3 sK0]
    conv => enter [1]; rw [l4 sK3 sK0 sK1 sK2]
  have l10 : ∀ X0 sK1 sK3 sK0 X1 sK2 : G, (X0 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X1 ◇ (sK3 ◇ sK0))) := by
    intro X0 sK1 sK3 sK0 X1 sK2
    conv => enter [1]; rw [l8 X0 sK1 sK3 sK0 X1]
    conv => enter [1]; rw [l0 (sK3 ◇ sK0) X1 sK1 sK2]
  have l11 : ∀ sK1 sK3 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ sK0)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l3 sK1 sK3 sK0 sK1 sK1]
    conv => enter [1]; rw [l9 sK1 sK1 sK1 sK3 sK0 sK2]
  have l12 : ∀ X0 sK1 sK3 sK0 X1 : G, (X0 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X1)) = ((sK3 ◇ sK0) ◇ (sK3 ◇ sK0)) := by
    intro X0 sK1 sK3 sK0 X1
    conv => enter [1]; rw [l10 X0 sK1 sK3 sK0 X1 X0]
    conv => enter [1]; rw [l2 (sK1 ◇ (sK1 ◇ X0)) X1 sK3 sK0]
  have l13 : ∀ X0 sK1 sK3 sK0 X1 sK2 : G, (X0 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK3 ◇ sK0)) := by
    intro X0 sK1 sK3 sK0 X1 sK2
    conv => enter [1]; rw [l12 X0 sK1 sK3 sK0 X1]
    conv => enter [1]; rw [l4 sK3 sK0 sK1 sK2]
  have l14 : ∀ X0 sK1 sK3 sK0 X1 : G, (X0 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X1)) = (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro X0 sK1 sK3 sK0 X1
    conv => enter [1]; rw [l13 X0 sK1 sK3 sK0 X1 X0]
    conv => enter [1]; rw [← l11 sK1 sK3 sK0 X0]
  have l15 : ∀ sK2 sK1 sK3 sK0 X1 X0 : G, ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X1) = (X0 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ X1)) := by
    intro sK2 sK1 sK3 sK0 X1 X0
    conv => enter [1, 1]; rw [l5 sK2 sK1 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK3 ◇ sK0)) X1]
  have l16 : ∀ sK2 sK1 sK3 sK0 X1 : G, ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X1) = (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) := by
    intro sK2 sK1 sK3 sK0 X1
    conv => enter [1]; rw [l15 sK2 sK1 sK3 sK0 X1 sK2]
    conv => enter [1]; rw [l14 sK2 sK1 sK3 sK0 X1]
  have l17 : ∀ sK2 sK1 sK3 sK0 X1 : G, (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) = ((sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X1) := by
    intro sK2 sK1 sK3 sK0 X1
    conv => enter [1]; rw [l5 sK2 sK1 sK3 sK0 sK1]
    conv => enter [1]; rw [← l16 sK2 sK1 sK3 sK0 X1]
  have l18 : ∀ sK2 sK1 sK3 sK0 X0 X1 : G, (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK2 sK1 sK3 sK0 X0 X1
    conv => enter [1]; rw [l17 sK2 sK1 sK3 sK0 (sK2 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h53989 X0 X1 (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0))) sK2]
  intro x y z w
  conv => enter [1]; rw [← l18 y x z w x y]

theorem Equation4512_53905_implies_Equation53993 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53905 : Equation53905 G) : Equation53993 G := by
  have l0 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ sK3) ◇ (sK0 ◇ X0)) = ((sK2 ◇ (sK3 ◇ sK0)) ◇ X0) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ sK3) sK0 X0]
    conv => enter [1, 1]; rw [← h4512 sK2 sK3 sK0]
  have l1 : ∀ sK2 sK3 sK0 X0 : G, ((sK2 ◇ sK3) ◇ (sK0 ◇ X0)) = (sK2 ◇ ((sK3 ◇ sK0) ◇ X0)) := by
    intro sK2 sK3 sK0 X0
    conv => enter [1]; rw [l0 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK2 (sK3 ◇ sK0) X0]
  have l2 : ∀ sK3 sK0 X0 X1 : G, (((sK3 ◇ sK0) ◇ X0) ◇ X1) = (sK3 ◇ ((sK0 ◇ X0) ◇ X1)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1, 1]; rw [← h4512 sK3 sK0 X0]
    conv => enter [1]; rw [← h4512 sK3 (sK0 ◇ X0) X1]
  have l3 : ∀ sK3 sK0 X0 X1 : G, (((sK3 ◇ sK0) ◇ X0) ◇ X1) = (sK3 ◇ (sK0 ◇ (X0 ◇ X1))) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l2 sK3 sK0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 sK0 X0 X1]
  have l4 : ∀ sK3 sK0 X0 X1 : G, (((sK3 ◇ sK0) ◇ X0) ◇ X1) = (sK0 ◇ (sK0 ◇ sK3)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [l3 sK3 sK0 X0 X1]
    conv => enter [1]; rw [← h53905 sK0 sK3 X0 X1]
  have l5 : ∀ sK3 sK0 X0 X1 : G, ((sK3 ◇ sK0) ◇ (X0 ◇ X1)) = (sK0 ◇ (sK0 ◇ sK3)) := by
    intro sK3 sK0 X0 X1
    conv => enter [1]; rw [h4512 (sK3 ◇ sK0) X0 X1]
    conv => enter [1]; rw [l4 sK3 sK0 X0 X1]
  have l6 : ∀ sK3 sK0 X0 X1 X2 X3 : G, ((sK3 ◇ sK0) ◇ (X0 ◇ X1)) = ((sK3 ◇ sK0) ◇ (X2 ◇ X3)) := by
    intro sK3 sK0 X0 X1 X2 X3
    conv => enter [1]; rw [l5 sK3 sK0 X0 X1]
    conv => enter [1]; rw [← l5 sK3 sK0 X2 X3]
  have l7 : ∀ sK1 sK3 sK0 X0 X1 sK2 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ X1)) = (sK1 ◇ ((sK3 ◇ sK0) ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK3 sK0 X0 X1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ sK0) (X0 ◇ X1)]
    conv => enter [1, 2]; rw [l6 sK3 sK0 X0 X1 sK2 sK3]
  have l8 : ∀ sK1 sK3 sK0 X0 X1 sK2 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK3 sK0 X0 X1 sK2
    conv => enter [1]; rw [l7 sK1 sK3 sK0 X0 X1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK3 ◇ sK0) (sK2 ◇ sK3)]
  have l9 : ∀ X1 sK2 sK3 sK0 X0 : G, (X1 ◇ (sK2 ◇ ((sK3 ◇ sK0) ◇ X0))) = ((sK2 ◇ sK3) ◇ ((sK2 ◇ sK3) ◇ X1)) := by
    intro X1 sK2 sK3 sK0 X0
    conv => enter [1, 2]; rw [← l1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [← h53905 (sK2 ◇ sK3) X1 sK0 X0]
  have l10 : ∀ sK1 sK3 sK0 X0 X1 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK3 ◇ sK0) ◇ ((sK3 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK3 sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK3 ◇ sK0) (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 (sK3 ◇ sK0) sK1 X0 X1]
  have l11 : ∀ sK2 sK3 X0 X1 : G, ((sK2 ◇ sK3) ◇ (X0 ◇ X1)) = (sK3 ◇ (sK3 ◇ sK2)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [← h4512 sK2 sK3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 sK3 sK2 X0 X1]
  have l12 : ∀ sK4 sK1 sK3 sK0 X0 X1 : G, ((sK4 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ sK4)) := by
    intro sK4 sK1 sK3 sK0 X0 X1
    conv => enter [1]; rw [← h4512 sK4 (sK1 ◇ (sK3 ◇ sK0)) (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 (sK1 ◇ (sK3 ◇ sK0)) sK4 X0 X1]
  have l13 : ∀ sK4 sK1 sK3 sK0 X0 X1 sK2 : G, ((sK4 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ sK3)) := by
    intro sK4 sK1 sK3 sK0 X0 X1 sK2
    conv => enter [1]; rw [l12 sK4 sK1 sK3 sK0 X0 X1]
    conv => enter [1]; rw [l8 sK1 sK3 sK0 (sK1 ◇ (sK3 ◇ sK0)) sK4 sK2]
  have l14 : ∀ sK1 sK3 sK0 X0 X1 sK4 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK3 ◇ sK0) ◇ (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0 X0 X1 sK4
    conv => enter [1]; rw [l10 sK1 sK3 sK0 X0 X1]
    conv => enter [1]; rw [l6 sK3 sK0 (sK3 ◇ sK0) sK1 sK4 (sK1 ◇ (sK3 ◇ sK0))]
  have l15 : ∀ X1 sK2 sK3 sK0 X0 : G, (X1 ◇ (sK2 ◇ ((sK3 ◇ sK0) ◇ X0))) = (sK3 ◇ (sK3 ◇ sK2)) := by
    intro X1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l9 X1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [l11 sK2 sK3 (sK2 ◇ sK3) X1]
  have l16 : ∀ sK1 sK3 sK0 X0 X1 sK2 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (X0 ◇ X1)) = ((sK3 ◇ sK0) ◇ (sK2 ◇ sK3)) := by
    intro sK1 sK3 sK0 X0 X1 sK2
    conv => enter [1]; rw [l14 sK1 sK3 sK0 X0 X1 sK1]
    conv => enter [1]; rw [l6 sK3 sK0 sK1 (sK1 ◇ (sK3 ◇ sK0)) sK2 sK3]
  have l17 : ∀ X1 sK2 sK3 sK0 X0 sK4 sK1 : G, (X1 ◇ (sK2 ◇ ((sK3 ◇ sK0) ◇ X0))) = (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro X1 sK2 sK3 sK0 X0 sK4 sK1
    conv => enter [1]; rw [l15 X1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [h53905 sK3 sK2 sK4 (sK1 ◇ (sK3 ◇ sK0))]
  have l18 : ∀ X1 sK2 sK3 sK0 X0 sK4 sK1 : G, (X1 ◇ (sK2 ◇ ((sK3 ◇ sK0) ◇ X0))) = ((sK2 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro X1 sK2 sK3 sK0 X0 sK4 sK1
    conv => enter [1]; rw [l17 X1 sK2 sK3 sK0 X0 sK4 sK1]
    conv => enter [1]; rw [h4512 sK2 sK3 (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0)))]
  have l19 : ∀ sK2 X1 sK3 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ X1)) = ((sK2 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 X1 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [h53905 sK2 X1 (sK3 ◇ sK0) sK2]
    conv => enter [1]; rw [l18 X1 sK2 sK3 sK0 sK2 sK4 sK1]
  have l20 : ∀ sK4 sK1 sK3 sK0 X0 sK2 : G, ((sK4 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ ((sK4 ◇ (sK1 ◇ (sK3 ◇ sK0))) ◇ X0)) = (X0 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ sK3))) := by
    intro sK4 sK1 sK3 sK0 X0 sK2
    conv => enter [1]; rw [h53905 (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0))) X0 sK4 sK4]
    conv => enter [1, 2]; rw [l13 sK4 sK1 sK3 sK0 sK4 sK4 sK2]
  have l21 : ∀ sK1 sK3 sK0 sK2 X0 sK4 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ sK3)) = (X0 ◇ (X0 ◇ (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK3 sK0 sK2 X0 sK4
    conv => enter [1]; rw [← l13 sK4 sK1 sK3 sK0 X0 (sK1 ◇ sK1) sK2]
    conv => enter [1]; rw [← h53905 X0 (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0))) sK1 sK1]
  have l22 : ∀ sK1 sK3 sK0 sK2 X0 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ sK3)) = (X0 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ sK3))) := by
    intro sK1 sK3 sK0 sK2 X0
    conv => enter [1]; rw [← l13 sK1 sK1 sK3 sK0 (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0))) X0 sK2]
    conv => enter [1]; rw [l20 sK1 sK1 sK3 sK0 X0 sK2]
  have l23 : ∀ sK1 sK3 sK0 sK2 X0 X1 sK4 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ sK3)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0)))))) := by
    intro sK1 sK3 sK0 sK2 X0 X1 sK4
    conv => enter [1]; rw [l21 sK1 sK3 sK0 sK2 (X0 ◇ X1) sK4]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0))))]
  have l24 : ∀ sK2 sK3 sK4 sK1 sK0 : G, ((sK2 ◇ sK3) ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0))))) = (sK2 ◇ ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 sK3 (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0))))]
    conv => enter [1, 2]; rw [← l21 sK1 sK3 sK0 sK2 sK3 sK4]
  have l25 : ∀ sK1 sK3 sK0 sK2 sK4 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ sK3)) = ((sK2 ◇ sK3) ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK3 sK0 sK2 sK4
    conv => enter [1]; rw [l22 sK1 sK3 sK0 sK2 sK2]
    conv => enter [1]; rw [← l24 sK2 sK3 sK4 sK1 sK0]
  have l26 : ∀ X1 X0 sK1 sK3 sK0 sK2 : G, (X1 ◇ (X1 ◇ X0)) = ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ sK3)) := by
    intro X1 X0 sK1 sK3 sK0 sK2
    conv => enter [1]; rw [h53905 X1 X0 (X0 ◇ X1) (X1 ◇ (sK1 ◇ (sK3 ◇ sK0)))]
    conv => enter [1]; rw [← l23 sK1 sK3 sK0 sK2 X0 X1 X1]
  have l27 : ∀ sK1 sK3 sK0 sK2 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ sK3)) = (sK3 ◇ (sK3 ◇ sK2)) := by
    intro sK1 sK3 sK0 sK2
    conv => enter [1]; rw [l25 sK1 sK3 sK0 sK2 sK1]
    conv => enter [1]; rw [l11 sK2 sK3 sK3 (sK1 ◇ (sK1 ◇ (sK3 ◇ sK0)))]
  have l28 : ∀ X1 X0 sK3 sK0 sK2 : G, (X1 ◇ (X1 ◇ X0)) = ((sK3 ◇ sK0) ◇ (sK2 ◇ sK3)) := by
    intro X1 X0 sK3 sK0 sK2
    conv => enter [1]; rw [l26 X1 X0 X1 sK3 sK0 sK2]
    conv => enter [1]; rw [l16 X1 sK3 sK0 sK2 sK3 sK2]
  have l29 : ∀ sK1 sK3 sK0 sK2 sK4 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ sK3)) = (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK3 sK0 sK2 sK4
    conv => enter [1]; rw [l27 sK1 sK3 sK0 sK2]
    conv => enter [1]; rw [h53905 sK3 sK2 sK4 (sK1 ◇ (sK3 ◇ sK0))]
  have l30 : ∀ sK1 sK3 sK0 sK2 sK4 : G, ((sK1 ◇ (sK3 ◇ sK0)) ◇ (sK2 ◇ sK3)) = ((sK2 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK3 sK0 sK2 sK4
    conv => enter [1]; rw [l29 sK1 sK3 sK0 sK2 sK4]
    conv => enter [1]; rw [h4512 sK2 sK3 (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0)))]
  have l31 : ∀ sK3 sK0 sK2 sK4 sK1 : G, ((sK3 ◇ sK0) ◇ (sK2 ◇ sK3)) = ((sK2 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK2 sK4 sK1
    conv => enter [1]; rw [← l16 sK1 sK3 sK0 sK2 sK3 sK2]
    conv => enter [1]; rw [l30 sK1 sK3 sK0 sK2 sK4]
  have l32 : ∀ X0 X1 X2 X3 sK1 sK3 sK0 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = (X0 ◇ (X1 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro X0 X1 X2 X3 sK1 sK3 sK0
    conv => enter [1]; rw [← h53905 X1 X0 X2 X3]
    conv => enter [1]; rw [h53905 X1 X0 sK1 (sK3 ◇ sK0)]
  have l33 : ∀ X0 X1 X2 sK1 sK3 sK0 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X2 ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro X0 X1 X2 sK1 sK3 sK0
    conv => enter [1]; rw [h53905 X0 (X1 ◇ X2) sK1 (sK3 ◇ sK0)]
    conv => enter [1]; rw [← h4512 X1 X2 (X0 ◇ (sK1 ◇ (sK3 ◇ sK0)))]
  have l34 : ∀ sK3 sK0 sK2 X1 X2 X0 sK1 : G, ((sK3 ◇ sK0) ◇ (sK2 ◇ sK3)) = (X1 ◇ (X2 ◇ (X0 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK3 sK0 sK2 X1 X2 X0 sK1
    conv => enter [1]; rw [← l28 X0 (X1 ◇ X2) sK3 sK0 sK2]
    conv => enter [1]; rw [l33 X0 X1 X2 sK1 sK3 sK0]
  have l35 : ∀ sK3 sK0 sK2 X0 sK4 sK1 : G, ((sK3 ◇ sK0) ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK2 X0 sK4 sK1
    conv => enter [1]; rw [← l28 sK4 X0 sK3 sK0 sK2]
    conv => enter [1]; rw [h53905 sK4 X0 sK1 (sK3 ◇ sK0)]
  have l36 : ∀ sK3 sK0 sK2 X1 X2 sK1 : G, ((sK3 ◇ sK0) ◇ (sK2 ◇ sK3)) = (X1 ◇ (X2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK3 sK0 sK2 X1 X2 sK1
    conv => enter [1]; rw [l34 sK3 sK0 sK2 X1 X2 sK3 sK1]
    conv => enter [1]; rw [l32 X1 X2 sK3 (sK1 ◇ (sK3 ◇ sK0)) sK1 sK3 sK0]
  have l37 : ∀ sK2 sK3 sK4 sK1 sK0 X1 X2 : G, ((sK2 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = (X1 ◇ (X2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 sK4 sK1 sK0 X1 X2
    conv => enter [1]; rw [← l31 sK3 sK0 sK2 sK4 sK1]
    conv => enter [1]; rw [l36 sK3 sK0 sK2 X1 X2 sK1]
  have l38 : ∀ sK2 sK3 X1 X2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3))) = (X1 ◇ (X2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 X1 X2 sK1 sK0
    conv => enter [1]; rw [l19 sK2 (sK2 ◇ sK3) sK3 sK2 sK1 sK0]
    conv => enter [1]; rw [l37 sK2 sK3 sK2 sK1 sK0 X1 X2]
  have l39 : ∀ X0 sK4 sK1 sK3 sK0 sK2 : G, (X0 ◇ (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0)))) = ((sK2 ◇ sK3) ◇ (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro X0 sK4 sK1 sK3 sK0 sK2
    conv => enter [1]; rw [← l35 sK3 sK0 sK2 X0 sK4 sK1]
    conv => enter [1]; rw [l31 sK3 sK0 sK2 sK4 sK1]
  have l40 : ∀ sK2 sK3 X0 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK2 sK3 X0 sK4 sK1 sK0
    conv => enter [1]; rw [l19 sK2 sK3 sK3 sK4 sK1 sK0]
    conv => enter [1]; rw [← l39 X0 sK4 sK1 sK3 sK0 sK2]
  have l41 : ∀ sK2 sK3 X0 X1 sK4 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X0 ◇ (X1 ◇ (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0))))) := by
    intro sK2 sK3 X0 X1 sK4 sK1 sK0
    conv => enter [1]; rw [l40 sK2 sK3 (X0 ◇ X1) sK4 sK1 sK0]
    conv => enter [1]; rw [← h4512 X0 X1 (sK4 ◇ (sK1 ◇ (sK3 ◇ sK0)))]
  have l42 : ∀ sK2 sK3 X0 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X0 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro sK2 sK3 X0
    conv => enter [1]; rw [l41 sK2 sK3 X0 sK2 sK2 sK2 sK2]
    conv => enter [1, 2]; rw [← l40 sK2 sK3 sK2 sK2 sK2 sK2]
  have l43 : ∀ X0 X1 sK2 sK3 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK3)))) := by
    intro X0 X1 sK2 sK3
    conv => enter [1]; rw [h53905 X0 X1 X0 (X0 ◇ (sK3 ◇ X0))]
    conv => enter [1, 2]; rw [← l38 sK2 sK3 X0 X0 X0 X0]
  have l44 : ∀ X0 X1 sK2 sK3 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK2 ◇ (sK2 ◇ sK3))) := by
    intro X0 X1 sK2 sK3
    conv => enter [1]; rw [l43 X0 X1 sK2 sK3]
    conv => enter [1, 2]; rw [← l42 sK2 sK3 sK2]
  have l45 : ∀ sK2 sK3 X0 X1 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK2 sK3 X0 X1
    conv => enter [1]; rw [l42 sK2 sK3 X1]
    conv => enter [1]; rw [← l44 X0 X1 sK2 sK3]
  have l46 : ∀ sK2 sK3 X1 X0 X2 X3 : G, (sK2 ◇ (sK2 ◇ sK3)) = (X1 ◇ (X0 ◇ (X2 ◇ X3))) := by
    intro sK2 sK3 X1 X0 X2 X3
    conv => enter [1]; rw [l45 sK2 sK3 X0 X1]
    conv => enter [1]; rw [h53905 X0 X1 X2 X3]
  intro x y z w u
  conv => enter [1]; rw [l46 x y z w y u]

theorem Equation4512_53993_implies_Equation53905 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53993 : Equation53993 G) : Equation53905 G := by
  have l0 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ sK1)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h53993 X0 sK1 sK1 sK2 sK2]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h53993 X0 sK1 sK1 (sK1 ◇ sK2) sK2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (sK1 ◇ sK2)]
  have l2 : ∀ X1 X2 sK1 sK2 : G, (X1 ◇ (X2 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro X1 X2 sK1 sK2
    conv => enter [1]; rw [← h53993 X1 sK1 X1 X2 sK2]
    conv => enter [1]; rw [l0 X1 sK1 sK2]
  have l3 : ∀ sK1 sK2 X1 X2 X3 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = (X1 ◇ (X2 ◇ (sK1 ◇ X3))) := by
    intro sK1 sK2 X1 X2 X3
    conv => enter [1]; rw [← l0 sK1 sK1 sK2]
    conv => enter [1]; rw [h53993 sK1 sK1 X1 X2 X3]
  have l4 : ∀ X0 sK1 X1 sK2 : G, (X0 ◇ ((X0 ◇ sK1) ◇ X1)) = (((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) ◇ X1) := by
    intro X0 sK1 X1 sK2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ sK1) X1]
    conv => enter [1, 1]; rw [l0 X0 sK1 sK2]
  have l5 : ∀ X0 sK1 X1 sK2 : G, (X0 ◇ ((X0 ◇ sK1) ◇ X1)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X1)) := by
    intro X0 sK1 X1 sK2
    conv => enter [1]; rw [l4 X0 sK1 X1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK1 ◇ sK2) X1]
  have l6 : ∀ sK1 sK2 X1 X0 : G, ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X1)) = (X0 ◇ (X0 ◇ (sK1 ◇ X1))) := by
    intro sK1 sK2 X1 X0
    conv => enter [1]; rw [← l5 X0 sK1 X1 sK2]
    conv => enter [1, 2]; rw [← h4512 X0 sK1 X1]
  have l7 : ∀ sK1 sK2 X1 : G, ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X1)) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [l3 sK1 sK2 sK1 sK1 X1]
    conv => enter [1]; rw [← l6 sK1 sK2 X1 sK1]
  have l8 : ∀ X1 sK1 sK2 : G, (X1 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro X1 sK1 sK2
    conv => enter [1]; rw [← h53993 X1 sK1 X1 sK1 sK2]
    conv => enter [1]; rw [l1 X1 sK1 sK2]
  have l9 : ∀ X0 X1 X2 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 X2 sK1 sK2
    conv => enter [1]; rw [h53993 X0 X1 X2 X1 sK1]
    conv => enter [1, 2]; rw [l1 X1 sK1 sK2]
  have l10 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [l9 X0 X1 X0 sK1 sK2]
    conv => enter [1]; rw [l2 X0 (sK1 ◇ (sK1 ◇ sK2)) sK1 sK2]
  have l11 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l10 sK1 sK2 sK1 sK2]
    conv => enter [1]; rw [← l2 X0 (sK1 ◇ sK2) sK1 sK2]
    conv => enter [1, 2]; rw [← l10 sK1 sK2 sK1 sK2]
  have l12 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ sK2) ◇ ((sK1 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l10 sK1 sK2 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK2) (sK1 ◇ sK2) X0]
  have l13 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l12 sK1 sK2 X0]
    conv => enter [1]; rw [← l7 sK1 sK2 X0]
  have l14 : ∀ sK1 sK2 X0 sK3 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 X0 sK3 sK0
    conv => enter [1]; rw [l13 sK1 sK2 X0]
    conv => enter [1]; rw [← l10 sK2 (sK1 ◇ (sK3 ◇ sK0)) sK1 sK2]
  have l15 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ sK2)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l11 sK1 sK2 sK1]
    conv => enter [1]; rw [l8 sK1 sK1 sK2]
  have l16 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l15 sK1 sK2]
    conv => enter [1]; rw [l14 sK1 sK2 (sK1 ◇ sK2) sK3 sK0]
  have l17 : ∀ X0 X1 sK2 sK1 sK3 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK3 ◇ sK0)))) := by
    intro X0 X1 sK2 sK1 sK3 sK0
    conv => enter [1]; rw [h53993 X0 X1 (sK1 ◇ (sK1 ◇ sK2)) X0 X0]
    conv => enter [1]; rw [l14 sK1 sK2 (X0 ◇ (X1 ◇ X0)) sK3 sK0]
  have l18 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l16 sK1 sK2 sK1 sK1]
    conv => enter [1]; rw [← l17 X0 X1 sK2 sK1 sK1 sK1]
  have l19 : ∀ sK1 sK2 X2 X3 X1 X4 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X2 ◇ (X3 ◇ (X1 ◇ X4))) := by
    intro sK1 sK2 X2 X3 X1 X4
    conv => enter [1]; rw [l18 sK1 sK2 sK1 X1]
    conv => enter [1]; rw [h53993 sK1 X1 X2 X3 X4]
  intro x y z w
  conv => enter [1]; rw [l19 x y y x z w]

theorem Equation4512_53905_implies_Equation54004 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53905 : Equation53905 G) : Equation54004 G := by
  have l0 : ∀ sK0 sK2 X0 X1 : G, ((sK0 ◇ sK2) ◇ (X0 ◇ X1)) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 sK2 sK0 X0 X1]
  have l1 : ∀ X0 X1 X2 sK0 sK2 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ ((X0 ◇ X1) ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 X2 sK0 sK2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h53905 (X0 ◇ X1) X2 sK0 sK2]
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
  have l5 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK0
    conv => enter [1]; rw [h53905 sK2 sK0 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ sK2)]
  have l6 : ∀ X0 sK2 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [l4 X0 sK0 sK2 X0 X0]
    conv => enter [1]; rw [l0 sK0 sK2 X0 (X0 ◇ X0)]
  have l7 : ∀ X2 X0 X1 sK0 sK2 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (X2 ◇ (sK0 ◇ sK2)))) := by
    intro X2 X0 X1 sK0 sK2
    conv => enter [1]; rw [l3 X2 X0 X1 sK0 sK2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (sK0 ◇ sK2))]
  have l8 : ∀ X0 X1 X2 sK0 sK2 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X0 ◇ (X1 ◇ (sK0 ◇ sK2)))) := by
    intro X0 X1 X2 sK0 sK2
    conv => enter [1]; rw [l1 X0 X1 X2 sK0 sK2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK0 ◇ sK2)]
  have l9 : ∀ X0 sK0 sK2 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro X0 sK0 sK2
    conv => enter [1]; rw [l6 X0 sK2 sK0]
    conv => enter [1]; rw [l5 sK2 sK0]
  have l10 : ∀ X2 X0 X1 sK0 sK2 : G, (X2 ◇ (X2 ◇ X2)) = (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) := by
    intro X2 X0 X1 sK0 sK2
    conv => enter [1]; rw [l7 X2 X0 X1 sK0 sK2]
    conv => enter [1]; rw [l2 X0 X1 X2 (sK0 ◇ sK2) sK0 sK2]
  have l11 : ∀ X0 X1 X2 sK0 sK2 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X2))) = (X2 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 X2 sK0 sK2
    conv => enter [1]; rw [l8 X0 X1 X2 sK0 sK2]
    conv => enter [1]; rw [l2 X2 X0 X1 (sK0 ◇ sK2) sK0 sK2]
  have l12 : ∀ X0 X1 sK0 sK2 : G, (X0 ◇ (X1 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro X0 X1 sK0 sK2
    conv => enter [1]; rw [← l10 X0 X0 X1 sK0 sK2]
    conv => enter [1]; rw [l9 X0 sK0 sK2]
  have l13 : ∀ X0 X1 X2 sK0 sK2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = (X2 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro X0 X1 X2 sK0 sK2
    conv => enter [1]; rw [h4512 X0 X1 (X0 ◇ (X1 ◇ X2))]
    conv => enter [1]; rw [l11 X0 X1 X2 sK0 sK2]
  have l14 : ∀ X0 X1 X2 sK0 sK2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro X0 X1 X2 sK0 sK2
    conv => enter [1]; rw [l13 X0 X1 X2 sK0 sK2]
    conv => enter [1]; rw [l12 X2 X0 sK0 sK2]
  have l15 : ∀ X1 X0 sK0 sK2 : G, (X1 ◇ (X1 ◇ X0)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro X1 X0 sK0 sK2
    conv => enter [1]; rw [h53905 X1 X0 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l14 X0 X1 X1 sK0 sK2]
  have l16 : ∀ sK0 sK2 X1 X0 sK1 : G, ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X1)) = ((X0 ◇ (sK1 ◇ (sK0 ◇ sK2))) ◇ X1) := by
    intro sK0 sK2 X1 X0 sK1
    conv => enter [1]; rw [h4512 (sK0 ◇ sK2) (sK0 ◇ sK2) X1]
    conv => enter [1, 1]; rw [← l12 X0 sK1 sK0 sK2]
  have l17 : ∀ X0 sK1 sK0 sK2 X1 : G, (X0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1)) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X1)) := by
    intro X0 sK1 sK0 sK2 X1
    conv => enter [1]; rw [h4512 X0 (sK1 ◇ (sK0 ◇ sK2)) X1]
    conv => enter [1]; rw [← l16 sK0 sK2 X1 X0 sK1]
  have l18 : ∀ sK2 sK0 X0 sK1 X1 : G, (sK2 ◇ (sK2 ◇ sK0)) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1)) := by
    intro sK2 sK0 X0 sK1 X1
    conv => enter [1]; rw [← l0 sK0 sK2 (sK0 ◇ sK2) X1]
    conv => enter [1]; rw [← l17 X0 sK1 sK0 sK2 X1]
  have l19 : ∀ X0 sK1 sK0 sK2 X1 : G, (X0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1)) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro X0 sK1 sK0 sK2 X1
    conv => enter [1]; rw [← l18 sK2 sK0 X0 sK1 X1]
    conv => enter [1]; rw [l5 sK2 sK0]
  have l20 : ∀ sK4 sK1 sK0 sK2 X0 X1 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK2)) ◇ X1)) := by
    intro sK4 sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l12 sK4 sK1 sK0 sK2]
    conv => enter [1]; rw [← l19 X0 sK1 sK0 sK2 X1]
  have l21 : ∀ X0 sK4 sK1 sK0 sK2 : G, (X0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro X0 sK4 sK1 sK0 sK2
    conv => enter [1, 2]; rw [l12 sK4 sK1 sK0 sK2]
    conv => enter [1]; rw [← h53905 (sK0 ◇ sK2) X0 sK0 sK2]
  have l22 : ∀ X0 sK4 sK1 sK0 sK2 : G, (X0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro X0 sK4 sK1 sK0 sK2
    conv => enter [1]; rw [l21 X0 sK4 sK1 sK0 sK2]
    conv => enter [1]; rw [l0 sK0 sK2 (sK0 ◇ sK2) X0]
  have l23 : ∀ X0 sK4 sK1 sK0 sK2 : G, (X0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2)) := by
    intro X0 sK4 sK1 sK0 sK2
    conv => enter [1]; rw [l22 X0 sK4 sK1 sK0 sK2]
    conv => enter [1]; rw [l15 sK2 sK0 sK0 sK2]
  have l24 : ∀ sK4 sK1 sK0 sK2 X0 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X0 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro sK4 sK1 sK0 sK2 X0
    conv => enter [1]; rw [l12 sK4 sK1 sK0 sK2]
    conv => enter [1]; rw [← l23 X0 sK4 sK1 sK0 sK2]
  have l25 : ∀ X0 X1 sK4 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2)))) := by
    intro X0 X1 sK4 sK1 sK0 sK2
    conv => enter [1]; rw [h53905 X0 X1 (sK1 ◇ (sK0 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [← l20 sK4 sK1 sK0 sK2 X0 X0]
  have l26 : ∀ sK4 sK1 sK0 sK2 X0 X1 : G, (sK4 ◇ (sK1 ◇ (sK0 ◇ sK2))) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK4 sK1 sK0 sK2 X0 X1
    conv => enter [1]; rw [l24 sK4 sK1 sK0 sK2 X1]
    conv => enter [1]; rw [← l25 X0 X1 sK4 sK1 sK0 sK2]
  intro x y z w u
  conv => enter [1]; rw [← l26 z w u x x y]

@[equational_result]
theorem Equation54004_implies_Equation53905 (G : Type*) [Magma G] (h54004 : Equation54004 G) : Equation53905 G := by
  have l0 : ∀ X1 X2 sK1 sK2 X0 : G, (X1 ◇ (X2 ◇ (sK1 ◇ sK2))) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X1 X2 sK1 sK2 X0
    conv => enter [1]; rw [← h54004 sK2 X1 X1 X2 sK1]
    conv => enter [1]; rw [h54004 sK2 X1 X0 sK1 sK1]
  have l1 : ∀ X1 X2 X0 sK1 sK2 : G, (X1 ◇ (X1 ◇ X2)) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X1 X2 X0 sK1 sK2
    conv => enter [1]; rw [h54004 X1 X2 sK2 sK2 X1]
    conv => enter [1]; rw [h54004 sK2 (X1 ◇ X1) X0 sK1 sK1]
  have l2 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK1 sK2]
    conv => enter [1]; rw [← l0 X0 X1 sK1 sK2 sK1]
  have l3 : ∀ sK1 sK2 X1 X2 X3 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X2 ◇ (X3 ◇ X0))) := by
    intro sK1 sK2 X1 X2 X3 X0
    conv => enter [1]; rw [l2 sK1 sK2 X0 X0]
    conv => enter [1]; rw [h54004 X0 (sK1 ◇ sK2) X1 X2 X3]
  intro x y z w
  conv => enter [1]; rw [l3 x y y x z w]

theorem Equation4512_53905_implies_Equation54009 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53905 : Equation53905 G) : Equation54009 G := by
  have l0 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 sK1 sK0 X0 X1]
  have l1 : ∀ sK2 sK0 sK1 X0 X1 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (X0 ◇ X1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK2)) := by
    intro sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK1) (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 (sK0 ◇ sK1) sK2 X0 X1]
  have l2 : ∀ sK5 sK2 sK0 sK1 X0 X1 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (X0 ◇ X1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK5)) := by
    intro sK5 sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [← h4512 sK5 (sK2 ◇ (sK0 ◇ sK1)) (X0 ◇ X1)]
    conv => enter [1]; rw [← h53905 (sK2 ◇ (sK0 ◇ sK1)) sK5 X0 X1]
  have l3 : ∀ X0 sK0 sK1 X1 X2 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 sK0 sK1 X1 X2
    conv => enter [1]; rw [h53905 X0 X0 sK0 sK1]
    conv => enter [1]; rw [h53905 X0 (sK0 ◇ sK1) X1 X2]
  have l4 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK2)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53905 (sK0 ◇ sK1) sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l5 : ∀ sK2 sK0 sK1 sK5 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK5)) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1 sK5
    conv => enter [1]; rw [h53905 (sK2 ◇ (sK0 ◇ sK1)) sK5 sK0 sK1]
    conv => enter [1]; rw [h4512 sK5 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l6 : ∀ sK0 sK1 sK2 sK5 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK2)) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2 sK5
    conv => enter [1]; rw [← l1 sK2 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1)) sK5]
    conv => enter [1]; rw [l5 sK2 sK0 sK1 sK5]
  have l7 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ X0)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l3 X0 sK0 sK1 X0 X0]
    conv => enter [1]; rw [l0 sK0 sK1 X0 (X0 ◇ X0)]
  have l8 : ∀ sK2 sK0 sK1 sK5 : G, ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1 sK5
    conv => enter [1]; rw [← l4 sK0 sK1 sK2]
    conv => enter [1]; rw [l6 sK0 sK1 sK2 sK5]
  have l9 : ∀ X0 sK0 sK1 sK5 sK2 : G, (X0 ◇ (X0 ◇ X0)) = (sK0 ◇ (sK1 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK0 sK1 sK5 sK2
    conv => enter [1]; rw [l7 X0 sK1 sK0]
    conv => enter [1]; rw [h53905 sK1 sK0 sK5 (sK2 ◇ (sK0 ◇ sK1))]
  have l10 : ∀ X0 sK0 sK1 sK5 sK2 : G, (X0 ◇ (X0 ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1 sK5 sK2
    conv => enter [1]; rw [l9 X0 sK0 sK1 sK5 sK2]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
  have l11 : ∀ X1 X0 sK2 sK0 sK1 : G, (X1 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = (sK2 ◇ (sK2 ◇ X1)) := by
    intro X1 X0 sK2 sK0 sK1
    conv => enter [1, 2]; rw [← h53905 sK2 X0 sK0 sK1]
    conv => enter [1]; rw [← h53905 sK2 X1 sK2 X0]
  have l12 : ∀ sK2 X0 X1 sK0 sK1 : G, (sK2 ◇ ((sK2 ◇ X0) ◇ X1)) = ((X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X1) := by
    intro sK2 X0 X1 sK0 sK1
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ X0) X1]
    conv => enter [1, 1]; rw [h53905 sK2 X0 sK0 sK1]
  have l13 : ∀ X0 sK2 sK0 sK1 X1 : G, (X0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X1)) = (sK2 ◇ ((sK2 ◇ X0) ◇ X1)) := by
    intro X0 sK2 sK0 sK1 X1
    conv => enter [1]; rw [h4512 X0 (sK2 ◇ (sK0 ◇ sK1)) X1]
    conv => enter [1]; rw [← l12 sK2 X0 X1 sK0 sK1]
  have l14 : ∀ X1 X0 sK2 sK0 sK1 : G, (X1 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) = (X1 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro X1 X0 sK2 sK0 sK1
    conv => enter [1]; rw [l11 X1 X0 sK2 sK0 sK1]
    conv => enter [1]; rw [h53905 sK2 X1 sK0 sK1]
  have l15 : ∀ X0 sK2 sK0 sK1 X1 : G, (X0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X1)) = (sK2 ◇ (sK2 ◇ (X0 ◇ X1))) := by
    intro X0 sK2 sK0 sK1 X1
    conv => enter [1]; rw [l13 X0 sK2 sK0 sK1 X1]
    conv => enter [1, 2]; rw [← h4512 sK2 X0 X1]
  have l16 : ∀ X0 sK2 sK0 sK1 X1 : G, (X0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X1)) = ((X0 ◇ X1) ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK2 sK0 sK1 X1
    conv => enter [1]; rw [l15 X0 sK2 sK0 sK1 X1]
    conv => enter [1]; rw [h53905 sK2 (X0 ◇ X1) sK0 sK1]
  have l17 : ∀ X0 sK2 sK0 sK1 X1 : G, (X0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X1)) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK2 sK0 sK1 X1
    conv => enter [1]; rw [l16 X0 sK2 sK0 sK1 X1]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ (sK0 ◇ sK1))]
  have l18 : ∀ X0 sK2 sK0 sK1 X1 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro X0 sK2 sK0 sK1 X1
    conv => enter [1]; rw [← l14 X0 X1 sK2 sK0 sK1]
    conv => enter [1]; rw [← l17 X0 sK2 sK0 sK1 X1]
  have l19 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (X0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h53905 (sK0 ◇ sK1) X0 (sK0 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [l4 sK0 sK1 sK2]
  have l20 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l18 X0 sK2 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l19 sK0 sK1 X0 sK2]
  have l21 : ∀ sK5 sK2 sK0 sK1 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1)))) = (sK5 ◇ ((sK0 ◇ sK1) ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK5 sK2 sK0 sK1
    conv => enter [1]; rw [← h4512 sK5 (sK2 ◇ (sK0 ◇ sK1)) ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [l10 (sK2 ◇ (sK0 ◇ sK1)) sK0 sK1 sK5 sK2]
  have l22 : ∀ sK5 sK2 sK0 sK1 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK5)) := by
    intro sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l21 sK5 sK2 sK0 sK1]
    conv => enter [1]; rw [← h53905 (sK0 ◇ sK1) sK5 sK5 (sK2 ◇ (sK0 ◇ sK1))]
  have l23 : ∀ sK5 sK2 sK0 sK1 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l20 sK5 sK2 sK0 sK1]
    conv => enter [1]; rw [← l22 sK5 sK2 sK0 sK1]
  have l24 : ∀ sK5 sK2 sK0 sK1 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ sK5)) := by
    intro sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l23 sK5 sK2 sK0 sK1]
    conv => enter [1]; rw [l2 sK5 sK2 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1)) (sK2 ◇ (sK0 ◇ sK1))]
  have l25 : ∀ sK5 sK2 sK0 sK1 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK2)) := by
    intro sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l24 sK5 sK2 sK0 sK1]
    conv => enter [1]; rw [l1 sK2 sK0 sK1 (sK2 ◇ (sK0 ◇ sK1)) sK5]
  have l26 : ∀ sK5 sK2 sK0 sK1 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l25 sK5 sK2 sK0 sK1]
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
  have l27 : ∀ sK5 sK2 sK0 sK1 X0 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK5 sK2 sK0 sK1 X0
    conv => enter [1, 1]; rw [l26 sK5 sK2 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
  have l28 : ∀ sK5 sK2 sK0 sK1 X0 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK2)) := by
    intro sK5 sK2 sK0 sK1 X0
    conv => enter [1]; rw [l27 sK5 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [l1 sK2 sK0 sK1 (sK0 ◇ sK1) X0]
  have l29 : ∀ sK5 sK2 sK0 sK1 X0 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK5 sK2 sK0 sK1 X0
    conv => enter [1]; rw [l28 sK5 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [l4 sK0 sK1 sK2]
  have l30 : ∀ sK5 sK2 sK0 sK1 X0 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK5 sK2 sK0 sK1 X0
    conv => enter [1]; rw [l26 sK5 sK2 sK0 sK1]
    conv => enter [1]; rw [← l29 sK5 sK2 sK0 sK1 X0]
  have l31 : ∀ sK5 sK2 sK0 sK1 X0 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK5 sK2 sK0 sK1 X0
    conv => enter [1]; rw [l30 sK5 sK2 sK0 sK1 ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X0)]
    conv => enter [1]; rw [h53905 (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) X0 sK0 sK1]
  have l32 : ∀ sK5 sK2 sK0 sK1 X0 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK5 sK2 sK0 sK1 X0
    conv => enter [1]; rw [l31 sK5 sK2 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l8 sK2 sK0 sK1 sK5]
  have l33 : ∀ sK5 sK2 sK0 sK1 X0 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK5 sK2 sK0 sK1 X0
    conv => enter [1]; rw [l32 sK5 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← l18 X0 sK2 sK0 sK1 (sK0 ◇ sK1)]
  have l34 : ∀ sK5 sK2 sK0 sK1 X1 X0 : G, ((sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ X1) = (X0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro sK5 sK2 sK0 sK1 X1 X0
    conv => enter [1, 1]; rw [l33 sK5 sK2 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (sK2 ◇ (sK0 ◇ sK1)) X1]
  have l35 : ∀ sK5 sK2 sK0 sK1 X0 X1 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X1 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK5 sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l33 sK5 sK2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK2 ◇ (sK0 ◇ sK1))]
  have l36 : ∀ sK5 sK2 sK0 sK1 X0 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK5 sK2 sK0 sK1 X0
    conv => enter [1]; rw [l35 sK5 sK2 sK0 sK1 X0 sK5]
  have l37 : ∀ sK5 sK2 sK0 sK1 X0 X1 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ ((sK2 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro sK5 sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l30 sK5 sK2 sK0 sK1 X1]
    conv => enter [1]; rw [l34 sK5 sK2 sK0 sK1 X1 X0]
  have l38 : ∀ X0 X1 sK5 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro X0 X1 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [h53905 X0 X1 (sK2 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [← l37 sK5 sK2 sK0 sK1 X0 X0]
  have l39 : ∀ sK5 sK2 sK0 sK1 X0 X1 : G, (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ X1)) := by
    intro sK5 sK2 sK0 sK1 X0 X1
    conv => enter [1]; rw [l36 sK5 sK2 sK0 sK1 X1]
    conv => enter [1]; rw [← l38 X0 X1 sK5 sK2 sK0 sK1]
  intro x y z w u v
  conv => enter [1]; rw [← l39 z w u v x y]

@[equational_result]
theorem Equation54009_implies_Equation53905 (G : Type*) [Magma G] (h54009 : Equation54009 G) : Equation53905 G := by
  have l0 : ∀ sK1 sK2 X1 X2 X3 X4 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X1 ◇ (X2 ◇ (X3 ◇ X4))) := by
    intro sK1 sK2 X1 X2 X3 X4
    conv => enter [1]; rw [h54009 sK1 sK2 sK1 sK1 sK1 sK2]
    conv => enter [1]; rw [h54009 sK1 (sK1 ◇ sK2) X1 X2 X3 X4]
  intro x y z w
  conv => enter [1]; rw [l0 x y y x z w]

theorem Equation4512_53906_implies_Equation53909 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53906 : Equation53906 G) : Equation53909 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) sK0 X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 sK0]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ sK0) X0]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK1 ◇ sK0)]
  have l3 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l4 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK0 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) X0]
  have l5 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 sK0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 (sK0 ◇ sK1)]
  have l7 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53906 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53906 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53906 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK1 sK0 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53906 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK0]
  have l11 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = ((X0 ◇ (X0 ◇ X1)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X0 ◇ X0)) X2]
    conv => enter [1, 1]; rw [← h53906 X0 X1]
  have l12 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l11 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 ((sK1 ◇ sK0) ◇ sK0)]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK0) sK0]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l16 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l7 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l17 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ X2)) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l12 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l15 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK0]
  have l19 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l17 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X0) X2]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 (sK1 ◇ sK0)]
  have l21 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l19 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X2]
  have l22 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK0)) sK0 X0]
  have l23 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ sK0))) = (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l21 (sK0 ◇ sK1) X0 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK0 sK1 sK0]
  have l24 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l21 X1 X2 (X0 ◇ X0)]
    conv => enter [1, 2, 2]; rw [← h53906 X0 X1]
  have l25 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ X0))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l21 sK1 sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK1 ◇ X0)]
  have l26 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ X0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l21 (sK0 ◇ sK1) sK0 X0]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ X0)]
  have l27 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ X0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l26 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) ((sK0 ◇ sK1) ◇ X0)]
  have l28 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l25 sK1 sK0 X0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ X0)]
  have l29 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = (X0 ◇ (X0 ◇ (X2 ◇ X1))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l24 X1 X2 X0]
    conv => enter [1]; rw [← l21 X0 X2 X1]
  have l30 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ sK0))) = (X0 ◇ (X0 ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l23 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [l1 sK0 sK1 (sK1 ◇ sK0)]
  have l31 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK1 ◇ sK0) ◇ X0))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← l1 sK0 sK1 X0]
    conv => enter [1]; rw [l27 sK0 sK1 X0]
  have l32 : ∀ sK1 sK0 X0 : G, (sK1 ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 X0]
    conv => enter [1]; rw [l28 sK1 sK0 X0]
  have l33 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ sK0))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l30 sK0 sK1 X0]
    conv => enter [1]; rw [l29 X0 sK0 (sK1 ◇ sK0)]
  have l34 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l31 sK0 sK1 X0]
    conv => enter [1]; rw [l1 sK0 sK1 ((sK1 ◇ sK0) ◇ X0)]
  have l35 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK0) X0]
    conv => enter [1]; rw [l32 sK1 sK0 X0]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l20 sK0 sK1]
  have l37 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l36 sK0 sK1]
    conv => enter [1]; rw [← l34 sK0 sK1 (sK1 ◇ sK0)]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [← l37 sK0 sK1]
  have l39 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 X0]
    conv => enter [1]; rw [← l35 sK1 sK0 (sK0 ◇ X0)]
  have l40 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l22 sK0 sK1 X0]
    conv => enter [1]; rw [← l39 sK0 sK1 X0]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [l35 sK1 sK0 sK0]
  have l42 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l22 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l43 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1 ((sK1 ◇ sK0) ◇ (sK1 ◇ sK0))]
    conv => enter [1, 2]; rw [← l20 sK0 sK1]
  have l44 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l45 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l16 sK1 sK0]
    conv => enter [1]; rw [l22 sK0 sK1 sK1]
  have l46 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l41 sK0 sK1]
    conv => enter [1]; rw [← l44 sK0 sK1]
  have l47 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1 (sK1 ◇ sK0)]
    conv => enter [1]; rw [l43 sK0 sK1]
  have l48 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l46 sK1 sK0]
  have l49 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l47 sK0 sK1]
    conv => enter [1]; rw [← l42 sK0 sK1 (sK0 ◇ sK1)]
  have l50 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1]
    conv => enter [1]; rw [l49 sK0 sK1]
  have l51 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ X0))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l21 (sK1 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [← l40 sK0 sK1 ((sK1 ◇ sK0) ◇ X0)]
  have l52 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l51 sK1 sK0 X0]
    conv => enter [1, 2]; rw [← l40 sK0 sK1 X0]
  have l53 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [← l5 sK1 sK0 X0]
    conv => enter [1]; rw [l52 sK1 sK0 X0]
  have l54 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l53 sK1 sK0 X0]
    conv => enter [1]; rw [l3 sK1 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)]
  have l55 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l22 sK0 sK1 ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ sK0))]
  have l56 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK0) ◇ ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l21 (sK1 ◇ sK0) sK0 sK0]
  have l57 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1 sK0]
    conv => enter [1]; rw [← l56 sK0 sK1]
  have l58 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l55 sK1 sK0]
    conv => enter [1]; rw [← l40 sK0 sK1 ((sK1 ◇ sK0) ◇ sK0)]
  have l59 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53906 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l57 sK0 sK1]
  have l60 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1 sK0]
    conv => enter [1]; rw [← l58 sK1 sK0]
  have l61 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l59 sK0 sK1]
    conv => enter [1]; rw [← l22 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l62 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l59 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l63 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l61 sK1 sK0]
  have l64 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l60 sK0 sK1]
    conv => enter [1]; rw [← l22 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l65 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) = ((sK1 ◇ sK0) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l5 sK1 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l48 sK0 sK1]
  have l66 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l5 sK1 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l65 sK1 sK0]
  have l67 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l66 sK1 sK0]
    conv => enter [1, 2]; rw [l38 sK0 sK1]
  have l68 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l67 sK1 sK0]
    conv => enter [1]; rw [← l54 sK0 sK1 (sK0 ◇ sK1)]
  have l69 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [← l68 sK1 sK0]
  have l70 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l69 sK0 sK1]
    conv => enter [1]; rw [← l35 sK1 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))]
  have l71 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l69 sK0 sK1]
    conv => enter [1]; rw [l3 sK1 sK0 ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1))]
  have l72 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l71 sK1 sK0]
    conv => enter [1]; rw [← l54 sK0 sK1 (sK0 ◇ sK1)]
  have l73 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l70 sK0 sK1]
    conv => enter [1]; rw [← l42 sK0 sK1 (sK0 ◇ sK1)]
  have l74 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [← l72 sK1 sK0]
  have l75 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l50 sK0 sK1]
    conv => enter [1]; rw [← l73 sK0 sK1]
  have l76 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l74 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l77 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l75 sK0 sK1]
    conv => enter [1]; rw [← l64 sK0 sK1]
  have l78 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l76 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l79 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l78 sK0 sK1]
    conv => enter [1]; rw [l4 sK1 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l80 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l78 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l81 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l59 sK0 sK1]
    conv => enter [1]; rw [l80 sK0 sK1]
  have l82 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l79 sK1 sK0]
    conv => enter [1, 2]; rw [← l63 sK0 sK1]
  have l83 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) = ((sK1 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l64 sK0 sK1]
    conv => enter [1]; rw [← l82 sK1 sK0]
  have l84 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l62 sK1 sK0]
    conv => enter [1]; rw [← l83 sK1 sK0]
  have l85 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l77 sK0 sK1]
    conv => enter [1]; rw [← l84 sK1 sK0]
  have l86 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l76 sK0 sK1]
    conv => enter [1]; rw [← l85 sK1 sK0]
  have l87 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l81 sK0 sK1]
    conv => enter [1]; rw [← l63 sK0 sK1]
  have l88 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l75 sK0 sK1]
    conv => enter [1]; rw [← l87 sK0 sK1]
  have l89 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l86 sK0 sK1]
    conv => enter [1]; rw [← l6 sK1 sK0]
  have l90 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l45 sK1 sK0]
    conv => enter [1]; rw [← l89 sK1 sK0]
  have l91 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l86 sK0 sK1]
    conv => enter [1]; rw [← l90 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l91 x y]
  conv => enter [1]; rw [l88 y x]

theorem Equation4512_53909_implies_Equation53906 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53909 : Equation53909 G) : Equation53906 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK0 ◇ sK0)) X0]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK0))]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK1 ◇ X0)]
  have l5 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 ((sK0 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) X0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK0 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 X0]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ sK0) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l4 sK0 sK1 X0]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
  have l9 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l10 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53909 sK1 (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53909 (sK0 ◇ sK1) (sK0 ◇ sK0)]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [h53909 X0 X1]
    conv => enter [1, 2]; rw [h53909 X1 X0]
  have l13 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h53909 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 sK0 (sK0 ◇ sK0)]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [l6 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [l6 sK0 ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l16 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK1]
    conv => enter [1]; rw [h53909 (sK0 ◇ sK0) sK1]
  have l17 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l15 sK0 sK1]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l10 sK1 sK0]
    conv => enter [1]; rw [← l17 sK0 sK1]
  have l19 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l13 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l20 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ X0) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l13 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK0) (sK0 ◇ sK0) X0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ X0)) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [l20 sK0 X0]
  have l22 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l8 sK1 sK0]
    conv => enter [1]; rw [l19 sK1 sK0]
  have l23 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l16 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ (sK0 ◇ sK1))]
  have l24 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l22 sK1 sK0]
  have l25 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ sK0)) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l26 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 sK0]
    conv => enter [1, 2]; rw [l16 sK0 sK1]
  have l27 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l26 sK1 sK0]
    conv => enter [1]; rw [← l7 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l28 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53909 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l27 sK1 sK0]
  have l29 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l27 sK1 sK0]
    conv => enter [1]; rw [← l28 sK1 sK0]
  have l30 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l27 sK1 sK0]
    conv => enter [1]; rw [l29 sK0 sK1]
  have l31 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53909 (sK0 ◇ sK0) (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [l25 sK1 sK0]
  have l32 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53909 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [← l31 sK0 sK1]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l21 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l34 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [l34 sK0 sK1]
  have l36 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l35 sK0 sK1]
  have l37 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h53909 (sK0 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l30 sK1 sK0]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l27 sK1 sK0]
    conv => enter [1]; rw [l37 sK0 sK1]
  have l39 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l27 sK1 sK0]
    conv => enter [1]; rw [l38 sK0 sK1]
  have l40 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [l39 sK1 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) X0]
  have l41 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53909 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK1]
    conv => enter [1, 2]; rw [l23 sK1 sK0]
  have l42 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l41 sK1 sK0]
  have l43 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l40 sK1 sK0 sK1]
    conv => enter [1]; rw [← l42 sK1 sK0]
  have l44 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l30 sK1 sK0]
    conv => enter [1, 2]; rw [← l43 sK1 sK0]
  have l45 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l44 sK1 sK0]
    conv => enter [1]; rw [← l40 sK1 sK0 sK1]
  have l46 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h53909 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 2, 2]; rw [← l45 sK1 sK0]
  have l47 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l46 sK1 sK0]
    conv => enter [1]; rw [← l40 sK1 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l48 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l39 sK1 sK0]
    conv => enter [1]; rw [← l47 sK1 sK0]
  have l49 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l48 sK1 sK0]
    conv => enter [1]; rw [l23 sK1 sK0]
  have l50 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l48 sK1 sK0]
    conv => enter [1]; rw [← h53909 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK1]
  have l51 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) ◇ sK1) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l40 sK1 sK0 sK1]
    conv => enter [1]; rw [← l50 sK1 sK0]
  have l52 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l45 sK1 sK0]
    conv => enter [1]; rw [l51 sK1 sK0]
  have l53 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l52 sK1 sK0]
    conv => enter [1]; rw [← l7 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l54 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l27 sK1 sK0]
    conv => enter [1]; rw [← l53 sK0 sK1]
  have l55 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l54 sK1 sK0]
    conv => enter [1]; rw [← l3 sK0 sK1]
  have l56 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK1 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l57 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
  have l58 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [l57 sK0 sK1]
  have l59 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l6 sK0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))]
    conv => enter [1]; rw [l56 sK0 sK1]
  have l60 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l58 sK0 sK1]
  have l61 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l59 sK0 sK1]
  have l62 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l55 sK1 sK0]
    conv => enter [1]; rw [l60 sK0 sK1]
  have l63 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [l61 sK0 sK1]
  have l64 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l62 sK1 sK0]
    conv => enter [1]; rw [← l63 sK0 sK1]
  have l65 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l55 sK1 sK0]
    conv => enter [1]; rw [← l64 sK0 sK1]
  have l66 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK1))]
  have l67 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ sK1)]
  have l68 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l69 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l67 sK0 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK0 ◇ sK0) (sK0 ◇ sK1)]
  have l70 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l49 sK1 sK0]
    conv => enter [1]; rw [← l68 sK0 sK1]
  have l71 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l65 sK1 sK0]
    conv => enter [1]; rw [l70 sK0 sK1]
  have l72 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l9 sK1 sK0]
    conv => enter [1, 2]; rw [← l71 sK1 sK0]
  have l73 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) = ((sK1 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l52 sK1 sK0]
    conv => enter [1]; rw [← l72 sK1 sK0]
  have l74 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l69 sK0 sK1]
    conv => enter [1]; rw [← l73 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l74 x y]

@[equational_result]
theorem Equation53913_implies_Equation53925 (G : Type*) [Magma G] (h53913 : Equation53913 G) : Equation53925 G := by
  have l0 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h53913 sK2 sK1 sK2]
    conv => enter [1]; rw [← h53913 X0 sK1 sK2]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53913 sK0 sK1 sK0]
    conv => enter [1]; rw [← h53913 sK2 sK1 sK0]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK1 sK2 X0
    conv => enter [1, 2]; rw [l0 sK2 sK1 sK1]
    conv => enter [1]; rw [← h53913 X0 sK1 sK1]
  have l3 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l2 sK1 sK2 sK2]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation4512_53925_implies_Equation53913 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53925 : Equation53925 G) : Equation53913 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK2 ◇ sK1))]
  have l1 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) X0]
  have l2 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l3 : ∀ X1 sK1 X0 sK0 : G, (X1 ◇ (X1 ◇ (sK1 ◇ X0))) = ((sK1 ◇ X0) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro X1 sK1 X0 sK0
    conv => enter [1]; rw [h53925 X1 (sK1 ◇ X0) sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l4 : ∀ X1 sK1 X0 sK0 : G, (X1 ◇ (X1 ◇ (sK1 ◇ X0))) = (sK1 ◇ (X0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro X1 sK1 X0 sK0
    conv => enter [1]; rw [l3 X1 sK1 X0 sK0]
    conv => enter [1]; rw [← h4512 sK1 X0 (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))]
  have l5 : ∀ X1 sK1 X0 sK0 : G, (X1 ◇ (X1 ◇ (sK1 ◇ X0))) = (sK1 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro X1 sK1 X0 sK0
    conv => enter [1]; rw [l4 X1 sK1 X0 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 (sK0 ◇ sK1) X0]
  have l6 : ∀ sK2 sK1 X1 : G, ((sK2 ◇ sK1) ◇ (X1 ◇ (X1 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 X1
    conv => enter [1]; rw [← h53925 sK2 (sK2 ◇ sK1) X1]
    conv => enter [1]; rw [h53925 sK2 (sK2 ◇ sK1) sK1]
  have l7 : ∀ X0 sK2 sK1 X1 : G, (X0 ◇ ((X0 ◇ (sK2 ◇ sK1)) ◇ X1)) = (((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ X1) := by
    intro X0 sK2 sK1 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (sK2 ◇ sK1)) X1]
    conv => enter [1, 1]; rw [h53925 X0 (sK2 ◇ sK1) sK1]
  have l8 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [h53925 sK1 (sK2 ◇ sK1) sK1]
  have l9 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = (sK1 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK2
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ sK1) ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [h53925 (sK2 ◇ sK1) (sK2 ◇ sK1) sK1]
  have l10 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l9 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l11 : ∀ X0 sK2 sK1 X1 : G, (X0 ◇ ((X0 ◇ (sK2 ◇ sK1)) ◇ X1)) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X1)) := by
    intro X0 sK2 sK1 X1
    conv => enter [1]; rw [l7 X0 sK2 sK1 X1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) X1]
  have l12 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← l6 sK2 sK1 sK2]
    conv => enter [1, 2]; rw [h53925 sK2 (sK2 ◇ sK1) sK1]
  have l13 : ∀ X0 sK2 sK1 X1 : G, (X0 ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ X1))) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X1)) := by
    intro X0 sK2 sK1 X1
    conv => enter [1, 2]; rw [h4512 X0 (sK2 ◇ sK1) X1]
    conv => enter [1]; rw [l11 X0 sK2 sK1 X1]
  have l14 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h53925 X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) (sK2 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← h53925 sK1 (sK2 ◇ sK1) sK1]
  have l15 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [h53925 sK1 (sK2 ◇ sK1) sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0]
  have l16 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l14 X0 sK1 sK2]
    conv => enter [1, 2]; rw [← h53925 sK1 (sK2 ◇ sK1) sK1]
  have l17 : ∀ X0 sK1 X1 sK0 : G, (X0 ◇ ((X0 ◇ sK1) ◇ X1)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X1) := by
    intro X0 sK1 X1 sK0
    conv => enter [1]; rw [h4512 X0 (X0 ◇ sK1) X1]
    conv => enter [1, 1]; rw [h53925 X0 sK1 sK0]
  have l18 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [h53925 sK1 sK1 sK0]
  have l19 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l20 : ∀ X0 sK1 X1 sK0 : G, (X0 ◇ ((X0 ◇ sK1) ◇ X1)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro X0 sK1 X1 sK0
    conv => enter [1]; rw [l17 X0 sK1 X1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) X1]
  have l21 : ∀ X0 sK1 X1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ X1))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro X0 sK1 X1 sK0
    conv => enter [1, 2]; rw [h4512 X0 sK1 X1]
    conv => enter [1]; rw [l20 X0 sK1 X1 sK0]
  have l22 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53925 X0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
    conv => enter [1, 2, 2]; rw [← h53925 sK0 sK1 sK0]
  have l23 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [h53925 sK0 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l24 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l22 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← h53925 sK0 sK1 sK0]
  have l25 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h53925 sK2 (sK2 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [h53925 sK2 sK1 sK0]
  have l26 : ∀ sK2 sK1 X0 sK0 : G, (sK2 ◇ ((sK2 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK1) X0]
    conv => enter [1, 1]; rw [h53925 sK2 sK1 sK0]
  have l27 : ∀ sK2 sK1 X0 sK0 : G, (sK2 ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [l26 sK2 sK1 X0 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l28 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l25 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l29 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK2 ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l23 sK0 sK1 X0]
    conv => enter [1]; rw [← l27 sK2 sK1 X0 sK0]
  have l30 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h53925 sK1 (sK2 ◇ sK1) sK1]
    conv => enter [1]; rw [l28 sK2 sK1 sK0]
  have l31 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l30 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
  have l32 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h53925 X0 (sK0 ◇ (sK0 ◇ sK1)) (sK2 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l30 sK1 sK2 sK0]
  have l33 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l32 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← h53925 sK1 (sK2 ◇ sK1) sK1]
  have l34 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l24 sK0 sK0 sK1]
    conv => enter [1]; rw [l33 sK0 sK0 sK1 sK2]
  have l35 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l31 sK1 sK2 sK0]
    conv => enter [1]; rw [← l1 sK2 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l36 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l31 sK1 sK2 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
  have l37 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l16 sK1 sK1 sK2]
    conv => enter [1]; rw [l36 sK1 sK2 sK0]
  have l38 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l35 sK2 sK1 sK0]
    conv => enter [1]; rw [l24 (sK2 ◇ sK1) sK0 sK1]
  have l39 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [l38 sK2 sK1 sK0]
  have l40 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h53925 sK1 (sK2 ◇ sK1) sK1]
    conv => enter [1]; rw [l39 sK2 sK1 sK0]
  have l41 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h53925 X0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l40 sK1 sK2 sK0]
  have l42 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [l40 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l43 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l42 sK1 sK2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) sK0]
    conv => enter [1]; rw [← l41 X0 sK0 sK1 sK2]
  have l44 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l43 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [l24 sK1 sK0 sK1]
  have l45 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l40 sK1 sK2 sK1]
    conv => enter [1]; rw [← l44 sK1 sK2 sK1]
  have l46 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l45 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0]
  have l47 : ∀ sK0 sK1 X0 sK2 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 1]; rw [l34 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0]
  have l48 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l47 sK0 sK1 X0 sK2]
  have l49 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l42 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [l48 sK0 sK1 X0 sK2]
  have l50 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l45 sK1 sK2]
    conv => enter [1]; rw [l37 sK1 sK2 sK0]
  have l51 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) = (((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [l37 sK1 sK2 sK0]
  have l52 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l51 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l53 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l46 sK1 sK2 X0]
    conv => enter [1]; rw [l52 sK1 sK2 X0 sK0]
  have l54 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [← l10 sK1 sK2]
    conv => enter [1]; rw [← l1 sK2 sK1 ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1))]
  have l55 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l54 sK2 sK1]
    conv => enter [1]; rw [l13 (sK2 ◇ sK1) sK2 sK1 (sK2 ◇ sK1)]
  have l56 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l15 sK1 sK2 (sK2 ◇ sK1)]
    conv => enter [1]; rw [← l55 sK2 sK1]
  have l57 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l1 sK2 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [← l56 sK1 sK2]
  have l58 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l12 sK2 sK1]
    conv => enter [1]; rw [l57 sK2 sK1]
  have l59 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h53925 sK1 (sK2 ◇ sK1) sK1]
    conv => enter [1]; rw [l58 sK2 sK1]
  have l60 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l59 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) (sK2 ◇ sK1) X0]
  have l61 : ∀ X0 sK2 sK1 : G, (X0 ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) = (((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h53925 X0 ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) sK2]
    conv => enter [1, 2, 2]; rw [← l8 sK2 sK1]
  have l62 : ∀ sK2 sK1 X0 : G, (((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = (sK2 ◇ (((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 1]; rw [l8 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK2 ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) X0]
  have l63 : ∀ sK2 sK1 X0 : G, (((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = (sK2 ◇ ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0))) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [l62 sK2 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK2 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0]
  have l64 : ∀ X0 sK2 sK1 : G, (X0 ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l61 X0 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))))]
  have l65 : ∀ sK2 sK1 X0 sK0 : G, (((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1]; rw [l63 sK2 sK1 X0]
    conv => enter [1]; rw [← l29 sK0 sK1 ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) sK2]
  have l66 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))))) = (X0 ◇ (X0 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l15 sK1 sK2 (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))))]
    conv => enter [1]; rw [← l64 X0 sK2 sK1]
  have l67 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = (((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l49 sK1 sK2 X0 sK1]
    conv => enter [1]; rw [← l65 sK2 sK1 X0 sK1]
  have l68 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))))) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l66 sK1 sK2 sK1]
    conv => enter [1]; rw [l13 sK1 sK2 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l69 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l67 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l70 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l68 sK1 sK2]
    conv => enter [1]; rw [← l15 sK1 sK2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l71 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l70 sK1 sK2]
    conv => enter [1]; rw [l37 sK1 sK2 sK0]
  have l72 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l50 sK1 sK2 sK1]
    conv => enter [1]; rw [← l71 sK1 sK2 sK1]
  have l73 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l72 sK1 sK2]
    conv => enter [1, 2]; rw [← l29 sK0 sK1 (sK1 ◇ (sK2 ◇ sK1)) sK2]
  have l74 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l73 sK1 sK2 sK1]
    conv => enter [1]; rw [← l53 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1)) sK1]
  have l75 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l74 sK1 sK2]
    conv => enter [1]; rw [← l2 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
  have l76 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l74 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l77 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l75 sK2 sK1]
    conv => enter [1]; rw [← l69 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1))]
  have l78 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l74 sK1 sK2]
    conv => enter [1]; rw [← l77 sK2 sK1]
  have l79 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l78 sK1 sK2]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
  have l80 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h53925 X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) sK2]
    conv => enter [1, 2, 2]; rw [← l78 sK1 sK2]
  have l81 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l80 X0 sK1 sK2]
    conv => enter [1, 2]; rw [h4512 sK2 sK1 (sK1 ◇ (sK2 ◇ sK1))]
  have l82 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l81 X0 sK1 sK2]
    conv => enter [1]; rw [← l60 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1))]
  have l83 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l74 sK1 sK2]
    conv => enter [1]; rw [← l82 X0 sK1 sK2]
  have l84 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l79 sK1 sK2]
    conv => enter [1]; rw [h4512 sK1 (sK2 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
  have l85 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l83 sK1 sK2 sK0]
    conv => enter [1]; rw [← l0 sK0 sK1 sK2]
  have l86 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro sK1 sK2
    conv => enter [1, 2]; rw [l83 sK1 sK2 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK1)) ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))]
  have l87 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l86 sK1 sK2]
    conv => enter [1]; rw [← l76 sK1 sK2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
  have l88 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l45 sK1 sK2]
    conv => enter [1]; rw [← l87 sK1 sK2]
  have l89 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l88 sK1 sK2]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0]
  have l90 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h53925 X0 (sK1 ◇ (sK2 ◇ sK1)) (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l84 sK1 sK2]
  have l91 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l90 X0 sK1 sK2]
    conv => enter [1]; rw [l5 (sK1 ◇ (sK2 ◇ sK1)) sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) sK0]
  have l92 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l91 X0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l89 sK1 sK2 ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))))]
  have l93 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [l92 X0 sK1 sK2 X0]
    conv => enter [1]; rw [← l53 sK1 sK2 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) X0]
  have l94 : ∀ X0 sK1 sK2 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK2 sK0
    conv => enter [1]; rw [l93 X0 sK1 sK2]
    conv => enter [1]; rw [l37 sK1 sK2 sK0]
  have l95 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l50 sK1 sK2 sK1]
    conv => enter [1]; rw [← l94 X0 sK1 sK2 sK1]
  have l96 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l95 sK1 sK2 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l85 sK1 sK2 sK0]
  have l97 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h53925 X0 (sK1 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l19 sK0 sK1]
  have l98 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l97 X0 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l99 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l98 X0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [l24 (sK0 ◇ sK1) sK0 sK1]
  have l100 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l99 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← l23 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l101 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l23 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [← l100 X0 sK1 sK0]
  have l102 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l101 sK0 sK1 sK0]
    conv => enter [1]; rw [l21 sK0 sK1 sK1 sK0]
  have l103 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l102 sK0 sK1]
    conv => enter [1]; rw [← l23 sK0 sK1 sK1]
  have l104 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l40 sK1 sK2 sK0]
    conv => enter [1]; rw [l103 sK0 sK1]
  have l105 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← h53925 (sK0 ◇ (sK0 ◇ sK1)) sK1 sK0]
    conv => enter [1, 2]; rw [← l104 sK1 sK2 sK0]
  have l106 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l96 sK1 sK2 sK0]
    conv => enter [1]; rw [← l105 sK1 sK0 sK2]
  have l107 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53925 sK0 sK1 sK0]
    conv => enter [1]; rw [← l106 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l107 x y z]

theorem Equation4512_53913_implies_Equation53955 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53913 : Equation53913 G) : Equation53955 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l2 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l3 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l2 sK1 X0]
  have l4 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l4 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l6 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK1
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) sK1]
  have l7 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
  have l8 : ∀ sK1 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l7 sK1]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l9 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l6 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) sK1 X0]
  have l10 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l9 sK1 X0]
  have l11 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1) X0]
    conv => enter [1, 1]; rw [l8 sK1]
  have l12 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [l11 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l13 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK1 ◇ sK1)) sK1]
    conv => enter [1, 2]; rw [← l6 sK1]
  have l14 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l8 sK1]
  have l15 : ∀ sK1 X0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1, 2, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [← h53913 X0 sK1 (sK1 ◇ sK1)]
  have l16 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro X0 sK1
    conv => enter [1]; rw [h53913 X0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l6 sK1]
  have l17 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [← l16 X0 sK1]
  have l18 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l15 sK1 X0]
  have l19 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h53913 X0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK0 ◇ sK1)]
  have l20 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [l3 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l17 sK1 X0]
  have l21 : ∀ sK1 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l18 sK1 sK1]
    conv => enter [1]; rw [← l20 sK1 sK1]
  have l22 : ∀ sK2 sK1 : G, (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l21 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1))]
  have l23 : ∀ sK1 X0 : G, (((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l21 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l24 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1]; rw [l23 sK1 X0]
  have l25 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l14 sK2 sK1]
    conv => enter [1]; rw [l22 sK2 sK1]
  have l26 : ∀ sK2 sK1 X0 : G, (((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) ◇ X0) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 1]; rw [l25 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l27 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h4512 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l26 sK2 sK1 X0]
  have l28 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l19 (sK1 ◇ sK1) sK1 sK0]
  have l29 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l6 sK1]
    conv => enter [1]; rw [l19 (sK1 ◇ (sK1 ◇ sK1)) sK1 sK0]
  have l30 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l19 sK1 sK1 sK0]
  have l31 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l19 sK1 sK1 sK0]
  have l32 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l19 (sK1 ◇ sK1) sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 ((sK1 ◇ sK1) ◇ sK1)]
  have l33 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)) = (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK1 ◇ sK1)) ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1)]
    conv => enter [1, 2]; rw [l19 (sK1 ◇ (sK1 ◇ sK1)) sK1 sK0]
  have l34 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ sK1)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← l33 sK2 sK1 sK0]
    conv => enter [1]; rw [← l27 sK2 sK1 sK1]
  have l35 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1, 2]; rw [l12 sK1 sK1]
  have l36 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l31 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK0 ◇ sK1)]
  have l37 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [l30 sK1 sK0]
  have l38 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l29 sK1 sK0]
  have l39 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK2 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [h4512 sK1 sK1 sK1]
    conv => enter [1]; rw [← l34 sK2 sK1 sK0]
  have l40 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l6 sK1]
  have l41 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK1]
    conv => enter [1]; rw [l36 sK1 sK0]
  have l42 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l37 sK1 sK1]
    conv => enter [1]; rw [← l38 sK1 sK1]
  have l43 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [l37 sK1 sK2]
    conv => enter [1]; rw [← l39 sK2 sK1 sK2]
  have l44 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l40 sK0 sK1]
    conv => enter [1, 2]; rw [← l3 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l45 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1]
    conv => enter [1]; rw [l41 sK1 sK0]
  have l46 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1
    conv => enter [1]; rw [l42 sK1]
    conv => enter [1, 2]; rw [← l21 sK1]
  have l47 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [l43 sK2 sK1]
    conv => enter [1]; rw [← l25 sK2 sK1]
  have l48 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l21 sK1]
    conv => enter [1]; rw [← l44 sK0 sK1]
  have l49 : ∀ sK1 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1
    conv => enter [1]; rw [l46 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1))]
  have l50 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l48 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ sK1)]
  have l51 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l45 sK1 sK0]
    conv => enter [1]; rw [← l50 sK0 sK1]
  have l52 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l51 sK0 sK1]
    conv => enter [1, 2]; rw [l28 sK1 sK0]
  have l53 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l37 sK1 sK0]
    conv => enter [1]; rw [← l52 sK0 sK1]
  have l54 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l53 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l55 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0 sK1 sK0]
    conv => enter [1]; rw [← l37 sK1 sK0]
  have l56 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l5 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← l19 sK0 sK1 sK0]
  have l57 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l19 sK0 sK1 sK0]
    conv => enter [1]; rw [l1 sK0 sK1 (sK0 ◇ sK1)]
  have l58 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l45 sK1 sK0]
    conv => enter [1]; rw [← l57 sK0 sK1]
  have l59 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l45 sK1 sK0]
    conv => enter [1]; rw [l56 sK1 sK0]
  have l60 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l58 sK0 sK1]
  have l61 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l59 sK1 sK0]
  have l62 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l54 sK0 sK1]
    conv => enter [1]; rw [l60 sK0 sK1]
  have l63 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l28 sK1 sK0]
    conv => enter [1]; rw [l61 sK1 sK0]
  have l64 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l62 sK0 sK1]
    conv => enter [1, 2]; rw [← l55 sK0 sK1]
  have l65 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l37 sK1 sK0]
    conv => enter [1]; rw [l63 sK1 sK0]
  have l66 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l55 sK0 sK1]
    conv => enter [1]; rw [l65 sK1 sK0]
  have l67 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h53913 (sK1 ◇ sK1) (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← l19 sK0 sK1 sK0]
  have l68 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [h53913 (sK1 ◇ sK1) (sK0 ◇ sK1) sK0]
  have l69 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))) = (sK2 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ (sK1 ◇ sK1)) ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [h53913 (sK1 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK1) sK0]
  have l70 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))) = (sK2 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l69 sK2 sK1 sK0]
    conv => enter [1, 2, 2]; rw [l64 sK0 sK1]
  have l71 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l68 sK1 sK0]
    conv => enter [1, 2, 2]; rw [l64 sK0 sK1]
  have l72 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [← l67 sK0 sK1]
  have l73 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l70 sK2 sK1 sK0]
    conv => enter [1]; rw [← l27 sK2 sK1 (sK0 ◇ sK1)]
  have l74 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l12 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l71 sK1 sK0]
  have l75 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l72 sK0 sK1]
    conv => enter [1, 2]; rw [l64 sK0 sK1]
  have l76 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK2 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l37 sK1 sK0]
    conv => enter [1]; rw [← l73 sK2 sK0 sK1]
  have l77 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l45 sK1 sK0]
    conv => enter [1]; rw [l74 sK1 sK0]
  have l78 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l76 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [← l75 sK0 sK1]
  have l79 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l77 sK1 sK0]
    conv => enter [1, 2]; rw [← l75 sK0 sK1]
  have l80 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l25 sK2 sK1]
    conv => enter [1]; rw [l78 sK2 sK1 sK0]
  have l81 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [l79 sK1 sK0]
  have l82 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l47 sK2 sK1]
    conv => enter [1]; rw [l80 sK2 sK1 sK0]
  have l83 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l49 sK1]
    conv => enter [1]; rw [l81 sK1 sK0]
  have l84 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l55 sK0 sK1]
    conv => enter [1]; rw [l83 sK1 sK0]
  have l85 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l13 sK2 sK1]
    conv => enter [1, 2, 2]; rw [← l55 sK0 sK1]
  have l86 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l55 sK0 sK1]
    conv => enter [1]; rw [l21 sK1]
    conv => enter [1, 1]; rw [← l55 sK0 sK1]
    conv => enter [1, 2]; rw [← l55 sK0 sK1]
  have l87 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l66 sK0 sK1]
    conv => enter [1]; rw [l86 sK1 sK0]
  have l88 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l85 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [← l84 sK0 sK1]
  have l89 : ∀ sK2 sK1 : G, (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK2 sK1
    conv => enter [1]; rw [l82 sK2 sK1 sK2]
    conv => enter [1]; rw [← l88 sK2 sK1 sK2]
  have l90 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 1]; rw [l47 sK2 sK1]
    conv => enter [1]; rw [← h4512 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1) X0]
  have l91 : ∀ sK1 sK0 sK2 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l19 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) sK1 sK0]
    conv => enter [1, 2]; rw [← l89 sK2 sK1]
  have l92 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l37 sK1 sK1]
    conv => enter [1]; rw [l91 sK1 sK1 sK2]
  have l93 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l55 sK0 sK1]
    conv => enter [1]; rw [l92 sK1 sK2]
  have l94 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h53913 X0 (sK1 ◇ (sK1 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l28 sK1 sK0]
  have l95 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l94 X0 sK1 sK0]
    conv => enter [1]; rw [← l24 sK1 ((sK1 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l96 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l95 X0 sK1 sK0]
    conv => enter [1, 2]; rw [l12 sK1 (sK0 ◇ sK1)]
  have l97 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l96 X0 sK1 sK0]
    conv => enter [1]; rw [l5 sK1 ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))]
  have l98 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l97 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← l24 sK1 (sK0 ◇ sK1)]
  have l99 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l98 X0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))]
  have l100 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l99 X0 sK1 sK0]
    conv => enter [1]; rw [← l24 sK1 (sK0 ◇ sK1)]
  have l101 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [l45 sK1 sK1]
    conv => enter [1]; rw [← l100 X0 sK1 sK1]
  have l102 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2, 2]; rw [l55 sK0 sK1]
    conv => enter [1]; rw [l101 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l55 sK0 sK1]
  have l103 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l3 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l102 sK1 sK0 X0]
  have l104 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l55 sK0 sK1]
    conv => enter [1]; rw [l103 sK1 sK0 X0]
  have l105 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l87 sK0 sK1]
    conv => enter [1]; rw [l104 sK0 sK1 X0]
  have l106 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK2 X0 sK1
    conv => enter [1, 2]; rw [h53913 X0 (sK1 ◇ (sK1 ◇ sK1)) sK2]
    conv => enter [1]; rw [h4512 sK2 (sK1 ◇ (sK1 ◇ sK1)) ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l107 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((sK1 ◇ sK1) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l106 sK2 X0 sK1]
    conv => enter [1]; rw [← l27 sK2 sK1 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l108 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [l107 sK2 X0 sK1]
    conv => enter [1]; rw [← l90 sK2 sK1 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l109 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l93 sK0 sK1 sK2]
    conv => enter [1]; rw [← l108 sK2 X0 sK1]
  have l110 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l109 sK0 sK1 sK2 X0]
    conv => enter [1, 2, 2, 2]; rw [← l55 sK0 sK1]
  have l111 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l110 sK0 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l105 sK0 sK1 sK0]
  have l112 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l111 sK0 sK1 sK2]
    conv => enter [1]; rw [← l82 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l112 x y z]

@[equational_result]
theorem Equation53955_implies_Equation53913 (G : Type*) [Magma G] (h53955 : Equation53955 G) : Equation53913 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53955 X0 X1 X0]
    conv => enter [1]; rw [← h53955 X2 X1 X0]
  have l1 : ∀ X0 sK1 X1 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 X1 sK0
    conv => enter [1]; rw [h53955 X0 sK1 X1]
    conv => enter [1, 2]; rw [l0 sK1 sK1 sK0]
  have l2 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l1 sK0 sK1 X1 sK0]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [l0 sK2 sK1 sK0]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2]
    conv => enter [1]; rw [← l3 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation4512_53913_implies_Equation53972 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53913 : Equation53913 G) : Equation53972 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 X0]
  have l1 : ∀ sK2 sK1 : G, ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 (sK1 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 sK1]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h53913 X0 sK1 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK1 sK0]
    conv => enter [1]; rw [l2 sK1 sK1]
  have l4 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK1 ◇ sK1)) ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK1]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l5 : ∀ sK1 sK0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← l3 sK0 sK1]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l8 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l5 sK1 sK0]
    conv => enter [1]; rw [← l7 sK0 sK1 (sK1 ◇ sK1)]
  have l9 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l2 sK1 sK1]
    conv => enter [1]; rw [l6 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
    conv => enter [1]; rw [l9 sK1 sK0]
  have l11 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l12 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l10 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l12 sK1 sK0]
  have l14 : ∀ sK1 sK0 : G, ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1]; rw [← l7 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l14 sK1 sK0]
  have l16 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [l8 sK1 sK0]
  have l18 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53913 X0 (sK0 ◇ (sK0 ◇ sK1)) (sK1 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l8 sK1 sK0]
  have l19 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l18 X0 sK0 sK1]
    conv => enter [1, 2]; rw [← l16 sK0 sK1 (sK1 ◇ sK1)]
  have l20 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l19 X0 sK0 sK1]
  have l21 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [l20 sK0 sK1 X0]
  have l22 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK2 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [← l4 sK2 sK1 sK0]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK1 ◇ sK1)) sK1]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK2 ◇ (sK1 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l21 sK0 sK1 sK2]
    conv => enter [1]; rw [l22 sK2 sK0 sK1]
  have l24 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h53913 X0 sK1 (X0 ◇ (X0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l23 sK0 sK1 X0]
  have l25 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l24 X0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l26 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l25 X0 sK1 sK0]
    conv => enter [1]; rw [l8 sK1 sK0]
  have l27 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← l26 X0 sK1 sK0]
  have l28 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (X1 ◇ sK1))) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [h53913 sK0 sK1 X1]
  have l29 : ∀ sK0 sK1 X1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (X1 ◇ sK1)) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l28 sK0 sK1 X1]
    conv => enter [1]; rw [h4512 sK1 sK1 (X1 ◇ sK1)]
  have l30 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 sK1]
  have l31 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h53913 X0 (sK1 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← l30 sK0 sK1]
  have l32 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l31 X0 sK1 sK0]
    conv => enter [1]; rw [l8 sK1 sK0]
  have l33 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1]
    conv => enter [1]; rw [← l32 X0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l33 x y z]

theorem Equation4512_53972_implies_Equation53913 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53972 : Equation53972 G) : Equation53913 G := by
  have l0 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h53972 X0 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l1 : ∀ X0 sK2 sK1 : G, (X0 ◇ (X0 ◇ (sK2 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK2 ◇ sK1))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h53972 X0 (sK2 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) (sK2 ◇ sK1)]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53972 X0 X1 X0]
    conv => enter [1]; rw [← h53972 X2 X1 X0]
  have l3 : ∀ X0 sK2 sK1 : G, (X0 ◇ (X0 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l1 X0 sK2 sK1]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK1)) (sK2 ◇ sK1)]
  have l4 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l0 X0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK1]
  have l5 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l3 sK1 sK2 sK1]
    conv => enter [1]; rw [← l3 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) sK2 sK1]
    conv => enter [1, 2]; rw [← l3 sK1 sK2 sK1]
  have l6 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) = (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← l3 sK2 sK2 sK1]
    conv => enter [1, 2]; rw [l4 sK2 sK1 sK0]
  have l7 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0]
    conv => enter [1, 2]; rw [← l4 sK0 sK1 sK0]
  have l8 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK1]
    conv => enter [1]; rw [l7 sK1 sK2 sK0]
  have l9 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [l8 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 (sK2 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [l4 sK2 sK1 sK0]
  have l11 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1) := by
    intro sK1 sK2
    conv => enter [1]; rw [l10 sK1 sK2 sK1]
    conv => enter [1]; rw [← l9 sK1 sK2 sK1 sK1]
  have l12 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [l11 sK1 sK2]
    conv => enter [1]; rw [l4 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) sK1 sK0]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 sK1 sK0]
    conv => enter [1]; rw [← l12 sK1 sK2 sK0]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1 sK2]
    conv => enter [1]; rw [← l5 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l14 x y z]

theorem Equation4512_53913_implies_Equation53980 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53913 : Equation53913 G) : Equation53980 G := by
  have l0 : ∀ X0 sK2 sK0 : G, (X0 ◇ (X0 ◇ sK2)) = (sK0 ◇ (sK0 ◇ sK2)) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [h53913 X0 sK2 sK0]
    conv => enter [1]; rw [← h53913 sK0 sK2 sK0]
  have l1 : ∀ X0 sK2 sK0 : G, (X0 ◇ (X0 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [h53913 X0 sK2 sK2]
    conv => enter [1, 2]; rw [l0 sK2 sK2 sK0]
  have l2 : ∀ X0 sK2 X1 sK0 : G, (X0 ◇ ((X0 ◇ sK2) ◇ X1)) = ((sK0 ◇ (sK0 ◇ sK2)) ◇ X1) := by
    intro X0 sK2 X1 sK0
    conv => enter [1]; rw [h4512 X0 (X0 ◇ sK2) X1]
    conv => enter [1, 1]; rw [l0 X0 sK2 sK0]
  have l3 : ∀ X0 sK2 X1 sK0 : G, (X0 ◇ ((X0 ◇ sK2) ◇ X1)) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X1)) := by
    intro X0 sK2 X1 sK0
    conv => enter [1]; rw [l2 X0 sK2 X1 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK2) X1]
  have l4 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ sK2)) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1]; rw [l1 sK0 sK2 sK0]
  have l5 : ∀ X0 sK2 X1 sK0 : G, (X0 ◇ (X0 ◇ (sK2 ◇ X1))) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X1)) := by
    intro X0 sK2 X1 sK0
    conv => enter [1, 2]; rw [h4512 X0 sK2 X1]
    conv => enter [1]; rw [l3 X0 sK2 X1 sK0]
  have l6 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK2) X0]
  have l7 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK2]
  have l8 : ∀ sK0 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) = ((sK0 ◇ sK2) ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2
    conv => enter [1, 2]; rw [l4 sK0 sK2]
    conv => enter [1]; rw [h4512 sK0 sK2 (sK0 ◇ (sK0 ◇ sK2))]
  have l9 : ∀ sK0 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK2)) ◇ X0) = (sK2 ◇ ((sK0 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK2 X0
    conv => enter [1, 1]; rw [l4 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK0 ◇ sK2)) X0]
  have l10 : ∀ sK0 sK2 X0 : G, (sK0 ◇ ((sK0 ◇ sK2) ◇ X0)) = (sK2 ◇ (sK0 ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK0 sK2 X0
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK2) X0]
    conv => enter [1]; rw [l9 sK0 sK2 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK2) X0]
  have l11 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l8 sK0 sK2]
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK1]
  have l12 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK2 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l6 sK1 sK2 X0 sK1]
    conv => enter [1]; rw [l10 sK1 sK2 X0]
    conv => enter [1, 2]; rw [← l6 sK1 sK2 X0 sK1]
  have l13 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = (((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [← l11 sK0 sK2 sK1]
  have l14 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) = ((sK0 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l13 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK2) (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l15 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK2 ◇ (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h53913 X0 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1]; rw [l12 sK1 sK2 ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
    conv => enter [1, 2]; rw [← h53913 X0 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l16 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [← h53913 (sK2 ◇ (sK2 ◇ sK2)) sK2 sK0]
    conv => enter [1]; rw [l12 sK2 sK2 ((sK2 ◇ (sK2 ◇ sK2)) ◇ sK2)]
    conv => enter [1, 2]; rw [h53913 (sK2 ◇ (sK2 ◇ sK2)) sK2 sK0]
  have l17 : ∀ X0 sK2 sK1 : G, (X0 ◇ (X0 ◇ sK2)) = (sK2 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h53913 X0 sK2 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2]; rw [← l12 sK1 sK2 sK2]
  have l18 : ∀ X0 sK2 sK1 : G, (X0 ◇ (X0 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l17 X0 sK2 sK1]
    conv => enter [1]; rw [← l12 sK1 sK2 sK2]
  have l19 : ∀ sK2 sK0 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2))) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l16 sK2 sK0]
    conv => enter [1]; rw [l5 sK2 sK2 (sK0 ◇ sK2) sK0]
  have l20 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l19 sK2 sK0]
    conv => enter [1]; rw [← l6 sK1 sK2 (sK0 ◇ sK2) sK0]
  have l21 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK0 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l18 sK0 sK2 sK1]
  have l22 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← h53913 sK2 sK2 sK0]
    conv => enter [1]; rw [l18 sK2 sK2 sK1]
  have l23 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ sK2)) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2 ((sK0 ◇ sK2) ◇ sK2) sK0]
    conv => enter [1, 2]; rw [l18 (sK0 ◇ sK2) sK2 sK1]
  have l24 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ sK2)) = ((sK0 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l23 sK1 sK2 sK0]
    conv => enter [1]; rw [l14 sK0 sK1 sK2 sK2]
  have l25 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2) := by
    intro sK1 sK2
    conv => enter [1]; rw [l21 sK1 sK2 sK1]
  have l26 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l25 sK1 sK2]
    conv => enter [1]; rw [← l18 (sK1 ◇ (sK1 ◇ sK2)) sK2 sK1]
    conv => enter [1, 2]; rw [← l25 sK1 sK2]
  have l27 : ∀ X0 sK2 sK1 : G, (X0 ◇ (X0 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [h53913 X0 sK2 (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1, 2, 2]; rw [← l25 sK1 sK2]
  have l28 : ∀ X0 sK2 sK1 : G, (X0 ◇ (X0 ◇ sK2)) = (sK2 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro X0 sK2 sK1
    conv => enter [1]; rw [l27 X0 sK2 sK1]
    conv => enter [1, 2]; rw [← l7 sK1 sK2]
  have l29 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ sK2)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l7 sK1 sK2]
    conv => enter [1]; rw [← l28 X0 sK2 sK1]
  have l30 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h53913 sK1 sK2 sK0]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l29 sK1 sK2 (sK0 ◇ sK2)]
    conv => enter [1]; rw [← l6 sK1 sK2 ((sK0 ◇ sK2) ◇ sK2) sK0]
  have l32 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l11 sK0 sK2 sK1]
    conv => enter [1]; rw [l31 sK0 sK1 sK2]
  have l33 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1, 1]; rw [l30 sK1 sK2 sK0]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK0 ◇ sK2)) X0]
  have l34 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = (sK2 ◇ (sK2 ◇ ((sK0 ◇ sK2) ◇ X0))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l33 sK1 sK2 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 sK2 (sK0 ◇ sK2) X0]
  have l35 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK2)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l30 sK1 sK2 sK0]
    conv => enter [1]; rw [l20 sK2 sK0 sK1]
  have l36 : ∀ sK2 sK0 X0 sK1 : G, (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) = (((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK2)) ◇ X0) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ (sK0 ◇ sK2)) X0]
    conv => enter [1, 1]; rw [l20 sK2 sK0 sK1]
  have l37 : ∀ sK2 sK0 X0 sK1 : G, (sK2 ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ X0)) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [l36 sK2 sK0 X0 sK1]
    conv => enter [1]; rw [← h4512 (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ sK2) X0]
  have l38 : ∀ sK2 sK0 X0 sK1 : G, (sK2 ◇ (sK2 ◇ ((sK0 ◇ sK2) ◇ X0))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1, 2]; rw [h4512 sK2 (sK0 ◇ sK2) X0]
    conv => enter [1]; rw [l37 sK2 sK0 X0 sK1]
  have l39 : ∀ sK1 sK2 X0 sK0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ X0) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ X0)) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l34 sK1 sK2 X0 sK0]
    conv => enter [1]; rw [l38 sK2 sK0 X0 sK1]
  have l40 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = ((sK2 ◇ (sK0 ◇ sK2)) ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [h53913 X0 (sK2 ◇ (sK0 ◇ sK2)) sK2]
    conv => enter [1, 2, 2]; rw [l22 sK2 sK0 sK1]
  have l41 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = (sK2 ◇ ((sK0 ◇ sK2) ◇ ((sK2 ◇ (sK0 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l40 X0 sK2 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ sK2) ((sK2 ◇ (sK0 ◇ sK2)) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2))]
  have l42 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = (sK2 ◇ ((sK0 ◇ sK2) ◇ (sK2 ◇ ((sK0 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2))))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l41 X0 sK2 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK2 (sK0 ◇ sK2) ((sK1 ◇ (sK1 ◇ sK2)) ◇ sK2)]
  have l43 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = (sK2 ◇ ((sK0 ◇ sK2) ◇ (sK2 ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ sK2))))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l42 X0 sK2 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← l24 sK1 sK2 sK0]
  have l44 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = (sK2 ◇ ((sK0 ◇ sK2) ◇ ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ sK2)))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l43 X0 sK2 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l12 sK1 sK2 ((sK0 ◇ sK2) ◇ sK2)]
  have l45 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = (sK2 ◇ ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l44 X0 sK2 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l32 sK0 sK2 sK1]
  have l46 : ∀ X0 sK2 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK2 ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro X0 sK2 sK0 sK1
    conv => enter [1]; rw [l45 X0 sK2 sK0 sK1]
    conv => enter [1]; rw [← l15 (sK0 ◇ sK2) sK1 sK2]
  have l47 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))) = (sK0 ◇ ((sK0 ◇ sK2) ◇ (sK0 ◇ sK2))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [← l46 sK0 sK2 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK2 (sK0 ◇ sK2) sK0]
  have l48 : ∀ sK0 sK2 sK1 : G, ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l47 sK0 sK2 sK1]
    conv => enter [1]; rw [← l6 sK1 sK2 (sK0 ◇ sK2) sK0]
  have l49 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l35 sK1 sK2 sK0]
    conv => enter [1]; rw [← l48 sK0 sK2 sK1]
  have l50 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [l49 sK1 sK2 sK0]
    conv => enter [1]; rw [← l6 sK1 sK2 ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) sK0]
  have l51 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l50 sK0 sK1 sK2]
    conv => enter [1]; rw [← l39 sK1 sK2 (sK1 ◇ (sK1 ◇ sK2)) sK0]
  have l52 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l26 sK1 sK2]
    conv => enter [1]; rw [← l51 sK0 sK1 sK2]
  have l53 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l52 sK1 sK2 sK0]
    conv => enter [1]; rw [← l11 sK0 sK2 sK1]
  have l54 : ∀ sK0 sK2 sK3 sK1 : G, ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK2)))) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK3 sK1
    conv => enter [1]; rw [← h53913 sK0 (sK0 ◇ sK2) sK3]
    conv => enter [1, 2]; rw [l0 sK0 sK2 sK1]
  have l55 : ∀ sK0 sK2 sK3 sK1 : G, ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK2)))) = ((sK0 ◇ sK2) ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK2 sK3 sK1
    conv => enter [1]; rw [l54 sK0 sK2 sK3 sK1]
    conv => enter [1]; rw [← l11 sK0 sK2 sK1]
  have l56 : ∀ sK1 sK2 sK0 sK3 : G, (sK1 ◇ (sK1 ◇ sK2)) = ((sK0 ◇ sK2) ◇ ((sK0 ◇ sK2) ◇ (sK3 ◇ (sK0 ◇ sK2)))) := by
    intro sK1 sK2 sK0 sK3
    conv => enter [1]; rw [l53 sK1 sK2 sK0]
    conv => enter [1]; rw [← l55 sK0 sK2 sK3 sK1]
  have l57 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (X0 ◇ (X0 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l56 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← h53913 X0 (sK0 ◇ sK2) sK1]
  intro x y z w
  conv => enter [1]; rw [l57 x y z w]

theorem Equation4512_53980_implies_Equation53913 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53980 : Equation53980 G) : Equation53913 G := by
  have l0 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK2 ◇ sK1) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK2 ◇ sK1) X0]
  have l1 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = (sK2 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← h4512 sK2 sK1 ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l2 : ∀ sK1 sK2 X0 X1 : G, (sK1 ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 2]; rw [← h4512 sK1 (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [← h53980 X1 X0 sK1 (sK2 ◇ sK1)]
  have l3 : ∀ X1 X0 sK1 sK2 : G, (X1 ◇ (X1 ◇ X0)) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro X1 X0 sK1 sK2
    conv => enter [1]; rw [h53980 X1 X0 sK1 (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ (sK2 ◇ sK1)) X0]
  have l4 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = (X1 ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK2 ◇ sK1)) X0]
    conv => enter [1]; rw [l2 sK1 sK2 X0 X1]
  have l5 : ∀ X1 sK1 sK2 X0 : G, (X1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (X1 ◇ X0)) := by
    intro X1 sK1 sK2 X0
    conv => enter [1, 2]; rw [l4 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l4 sK1 sK2 (X1 ◇ X0) X1]
  have l6 : ∀ sK0 sK1 X0 sK2 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1, 2]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [← l4 sK1 sK2 (sK1 ◇ X0) sK0]
  have l7 : ∀ X2 sK1 sK2 X0 X1 : G, (X2 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) = (X1 ◇ (X1 ◇ X0)) := by
    intro X2 sK1 sK2 X0 X1
    conv => enter [1, 2]; rw [l4 sK1 sK2 X0 X2]
    conv => enter [1]; rw [← h53980 X1 X0 X2 X2]
  have l8 : ∀ sK1 sK2 X0 X2 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) = (X2 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK2 X0 X2
    conv => enter [1]; rw [l4 sK1 sK2 X0 sK1]
    conv => enter [1]; rw [← l7 X2 sK1 sK2 X0 sK1]
  have l9 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l6 sK0 sK1 X0 sK2]
  have l10 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l9 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← l5 sK1 sK1 sK2 X0]
  have l11 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l10 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← l8 sK1 sK2 X0 sK1]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l4 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [l4 sK1 sK2 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [l4 sK1 sK2 sK1 sK0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1 sK0]
    conv => enter [1]; rw [← l11 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l14 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l4 sK1 sK2 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [l4 sK1 sK2 (sK0 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))]
    conv => enter [1, 2]; rw [l4 sK1 sK2 (sK0 ◇ sK1) sK0]
  have l15 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l14 sK0 sK1 sK2]
    conv => enter [1]; rw [← l5 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ sK1))]
  have l16 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l15 sK0 sK1 sK2]
    conv => enter [1]; rw [← l8 sK1 sK2 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l16 sK0 sK1 sK0]
    conv => enter [1]; rw [← l11 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l18 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l17 sK0 sK1]
  have l19 : ∀ sK2 X0 sK1 sK0 : G, (sK2 ◇ (X0 ◇ (X0 ◇ sK1))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro sK2 X0 sK1 sK0
    conv => enter [1, 2]; rw [h53980 X0 sK1 (sK1 ◇ (sK2 ◇ sK1)) sK0]
    conv => enter [1]; rw [← l0 sK2 sK1 ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1))]
  have l20 : ∀ sK2 X0 sK1 sK0 : G, (sK2 ◇ (X0 ◇ (X0 ◇ sK1))) = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)))) := by
    intro sK2 X0 sK1 sK0
    conv => enter [1]; rw [l19 sK2 X0 sK1 sK0]
    conv => enter [1]; rw [l3 (sK2 ◇ sK1) ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)) sK1 sK2]
  have l21 : ∀ sK2 X0 sK1 sK0 : G, (sK2 ◇ (X0 ◇ (X0 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1))) := by
    intro sK2 X0 sK1 sK0
    conv => enter [1]; rw [l20 sK2 X0 sK1 sK0]
    conv => enter [1]; rw [← l8 sK1 sK2 ((sK1 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)) sK1]
  have l22 : ∀ sK2 X0 sK1 sK0 : G, (sK2 ◇ (X0 ◇ (X0 ◇ sK1))) = ((sK1 ◇ (sK2 ◇ sK1)) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ sK1))) := by
    intro sK2 X0 sK1 sK0
    conv => enter [1]; rw [l21 sK2 X0 sK1 sK0]
    conv => enter [1]; rw [← l5 (sK1 ◇ (sK2 ◇ sK1)) sK1 sK2 (sK0 ◇ sK1)]
  have l23 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ sK1)) = (sK2 ◇ (X0 ◇ (X0 ◇ sK1))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l8 sK1 sK2 (sK0 ◇ sK1) (sK1 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l22 sK2 X0 sK1 sK0]
  have l24 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ sK1)) = (sK2 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l23 sK1 sK2 sK0 sK1]
    conv => enter [1, 2]; rw [← l4 sK1 sK2 sK1 sK1]
  have l25 : ∀ sK1 sK2 sK0 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ sK1)) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l24 sK1 sK2 sK0]
    conv => enter [1]; rw [← l1 sK2 sK1 sK1]
  have l26 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l4 sK1 sK2 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [l25 sK1 sK2 sK0]
  have l27 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l18 sK0 sK1]
    conv => enter [1]; rw [l26 sK0 sK1 sK2]
  have l28 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) = (sK2 ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l4 sK1 sK2 (sK2 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [← l4 sK1 sK2 sK1 sK2]
  have l29 : ∀ sK1 sK2 : G, ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) = ((sK2 ◇ sK1) ◇ ((sK1 ◇ (sK2 ◇ sK1)) ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l28 sK1 sK2]
    conv => enter [1]; rw [← l1 sK2 sK1 sK1]
  have l30 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l27 sK0 sK1 sK2]
    conv => enter [1]; rw [← l29 sK1 sK2]
  have l31 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l30 sK0 sK1 sK2]
    conv => enter [1]; rw [← l11 sK0 sK1 (sK2 ◇ sK1) sK2]
  have l32 : ∀ X1 sK0 sK1 X0 sK2 : G, (X1 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (X0 ◇ (sK2 ◇ sK1))) := by
    intro X1 sK0 sK1 X0 sK2
    conv => enter [1, 2, 2]; rw [l31 sK0 sK1 sK2]
    conv => enter [1]; rw [← h53980 X0 (sK2 ◇ sK1) X1 (sK0 ◇ (sK0 ◇ sK1))]
  have l33 : ∀ X1 sK0 sK1 sK2 : G, (X1 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK2 ◇ sK1)) := by
    intro X1 sK0 sK1 sK2
    conv => enter [1]; rw [l32 X1 sK0 sK1 X1 sK2]
    conv => enter [1]; rw [← l4 sK1 sK2 (sK2 ◇ sK1) X1]
  have l34 : ∀ sK1 sK2 X1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X1 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 X1 sK0
    conv => enter [1]; rw [← l4 sK1 sK2 (sK2 ◇ sK1) sK1]
    conv => enter [1]; rw [← l33 X1 sK0 sK1 sK2]
  have l35 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l34 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [← l4 sK1 sK2 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l36 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l35 sK1 sK2 sK0]
    conv => enter [1]; rw [← l11 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1)) sK2]
  have l37 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l36 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l37 x y z]

@[equational_result]
theorem Equation53913_implies_Equation54000 (G : Type*) [Magma G] (h53913 : Equation53913 G) : Equation54000 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53913 X0 X1 X0]
    conv => enter [1]; rw [← h53913 X2 X1 X0]
  have l1 : ∀ X0 sK0 sK2 sK3 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK2)))) = (sK3 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK0 sK2 sK3
    conv => enter [1]; rw [h53913 X0 (sK0 ◇ (sK0 ◇ sK2)) sK3]
    conv => enter [1]; rw [← h53913 sK3 (sK0 ◇ (sK0 ◇ sK2)) sK3]
  have l2 : ∀ X0 sK0 sK2 sK3 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK2))) = (sK3 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK0 sK2 sK3
    conv => enter [1]; rw [h53913 X0 (sK0 ◇ sK2) sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ sK2) sK0 sK2 sK3]
  have l3 : ∀ X0 sK2 sK3 sK0 : G, (X0 ◇ (X0 ◇ sK2)) = (sK3 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2)))) := by
    intro X0 sK2 sK3 sK0
    conv => enter [1]; rw [h53913 X0 sK2 sK0]
    conv => enter [1]; rw [l2 sK2 sK0 sK2 sK3]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK1 sK0]
    conv => enter [1]; rw [← l2 sK0 sK0 sK2 sK1]
  have l5 : ∀ sK3 sK0 sK2 X0 : G, (sK3 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2)))) = (X0 ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))))) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1]; rw [h53913 sK3 (sK0 ◇ (sK0 ◇ sK2)) sK3]
    conv => enter [1]; rw [l0 (sK0 ◇ (sK0 ◇ sK2)) (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))) X0]
  have l6 : ∀ sK3 sK0 sK2 X0 : G, (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))) = (X0 ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))))) := by
    intro sK3 sK0 sK2 X0
    conv => enter [1, 2]; rw [l3 sK0 sK2 sK3 sK0]
    conv => enter [1]; rw [l0 sK3 (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))) X0]
  have l7 : ∀ sK0 sK2 X0 sK3 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) = (X0 ◇ (X0 ◇ (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))))) := by
    intro sK0 sK2 X0 sK3
    conv => enter [1]; rw [l2 sK0 sK0 sK2 sK3]
    conv => enter [1]; rw [l5 sK3 sK0 sK2 X0]
  have l8 : ∀ sK3 sK0 sK2 : G, (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK3 sK0 sK2
    conv => enter [1]; rw [l6 sK3 sK0 sK2 sK3]
    conv => enter [1]; rw [← l7 sK0 sK2 sK3 sK3]
  have l9 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ (sK1 ◇ sK2)) = (sK3 ◇ (sK0 ◇ (sK0 ◇ sK2))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l4 sK1 sK2 sK0]
    conv => enter [1]; rw [← l8 sK3 sK0 sK2]
  intro x y z w
  conv => enter [1]; rw [l9 x y z w]

@[equational_result]
theorem Equation54000_implies_Equation53913 (G : Type*) [Magma G] (h54000 : Equation54000 G) : Equation53913 G := by
  have l0 : ∀ sK1 sK2 X1 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (X1 ◇ (X1 ◇ (sK2 ◇ sK1))) := by
    intro sK1 sK2 X1
    conv => enter [1]; rw [h54000 sK1 (sK2 ◇ sK1) sK1 sK1]
    conv => enter [1]; rw [← h54000 X1 (sK2 ◇ sK1) sK1 sK1]
  have l1 : ∀ sK1 sK2 X0 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 X0 sK0
    conv => enter [1]; rw [l0 sK1 sK2 sK2]
    conv => enter [1, 2]; rw [h54000 sK2 sK1 X0 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [← h54000 sK0 sK1 sK1 sK0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h54000 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l2 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation4512_53913_implies_Equation53910 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53913 : Equation53913 G) : Equation53910 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK0) sK0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 sK0]
    conv => enter [1]; rw [← h53913 X0 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK0) sK0]
    conv => enter [1]; rw [l1 sK0 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) = (X0 ◇ (X0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l2 sK0 X0]
  intro x y
  conv => enter [1]; rw [← l3 y x]

theorem Equation4512_53910_implies_Equation53913 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53910 : Equation53910 G) : Equation53913 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53910 X0 X1]
    conv => enter [1]; rw [← h53910 X2 X1]
  have l1 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ ((sK2 ◇ sK1) ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [h53910 sK1 (sK2 ◇ sK1)]
  have l2 : ∀ X0 sK1 sK2 X1 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (X1 ◇ (X1 ◇ (X0 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 sK2 X1
    conv => enter [1, 2]; rw [l0 sK1 (sK2 ◇ sK1) X0]
    conv => enter [1]; rw [l0 X0 (X0 ◇ (sK2 ◇ sK1)) X1]
  have l3 : ∀ sK1 sK2 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK2]
    conv => enter [1]; rw [← l2 (sK2 ◇ sK1) sK1 sK2 (sK2 ◇ sK1)]
  have l4 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h53910 X0 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK0]
  have l6 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [l0 sK2 sK1 sK0]
  have l7 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [h4512 sK2 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l8 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ sK1)) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l8 sK1 sK0 X0]
  have l10 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l6 sK1 sK2 sK0]
    conv => enter [1]; rw [l7 sK2 sK0 sK1]
  have l11 : ∀ sK2 sK1 X0 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 X0 sK0
    conv => enter [1, 2]; rw [l10 sK1 sK2 sK0]
    conv => enter [1]; rw [l0 (sK2 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l9 sK0 sK1 sK0]
    conv => enter [1]; rw [← l11 sK2 sK1 sK0 sK0]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 sK1 sK2]
    conv => enter [1]; rw [← l3 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

theorem Equation4512_53913_implies_Equation53976 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53913 : Equation53913 G) : Equation53976 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53913 X0 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK0]
  have l1 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ sK0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53913 X0 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ sK1) sK0]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l1 X0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  have l3 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l0 X0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) sK0]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 sK0 sK1]
    conv => enter [1]; rw [l2 sK0 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l3 sK1 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ sK0)]
  have l6 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1]; rw [l5 sK0 sK1]
  have l7 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l6 sK0 sK1]
  have l8 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0 X0]
    conv => enter [1, 1]; rw [← l4 sK0 sK1]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK0 X0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ sK0)]
  have l11 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1]; rw [l10 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l11 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK1 ◇ sK0)]
  have l14 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1]; rw [l13 sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [l14 sK0 sK1]
  have l16 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK1 ◇ sK0) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK1 ◇ sK0) X0]
  have l17 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l16 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 sK0 X0]
  have l18 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) sK0 X0]
    conv => enter [1]; rw [l17 sK0 sK1 X0]
  have l19 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← h53913 (sK0 ◇ (sK0 ◇ sK1)) sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)]
  have l20 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l19 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l21 : ∀ sK2 sK1 X0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (X0 ◇ (X0 ◇ sK1)) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [h53913 sK2 sK1 sK2]
    conv => enter [1]; rw [← h53913 X0 sK1 sK2]
  have l22 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h53913 sK2 sK1 sK0]
  have l23 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← h53913 sK2 sK1 sK0]
  have l24 : ∀ sK2 sK1 X1 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (X1 ◇ sK1))) := by
    intro sK2 sK1 X1
    conv => enter [1]; rw [h53913 sK2 sK1 X1]
  have l25 : ∀ X0 sK1 sK2 : G, (X0 ◇ (X0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro X0 sK1 sK2
    conv => enter [1]; rw [h53913 X0 sK1 sK1]
    conv => enter [1, 2]; rw [l21 sK1 sK1 sK2]
  have l26 : ∀ sK2 sK1 X1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ X1) = (X0 ◇ ((X0 ◇ sK1) ◇ X1)) := by
    intro sK2 sK1 X1 X0
    conv => enter [1, 1]; rw [l21 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ sK1) X1]
  have l27 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l21 sK1 sK1 sK2]
  have l28 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l21 sK1 sK1 sK2]
  have l29 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)]
    conv => enter [1, 2]; rw [l21 (sK0 ◇ (sK0 ◇ sK1)) sK1 sK2]
  have l30 : ∀ sK2 sK1 X1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ X1) = (X0 ◇ (X0 ◇ (sK1 ◇ X1))) := by
    intro sK2 sK1 X1 X0
    conv => enter [1]; rw [l26 sK2 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 sK1 X1]
  have l31 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [l25 sK2 sK1 sK2]
  have l32 : ∀ sK2 sK1 : G, ((sK2 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ sK1))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h4512 sK2 sK1 (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1, 2]; rw [← l31 sK2 sK1]
  have l33 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l31 sK2 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK2 ◇ (sK2 ◇ sK1))]
  have l34 : ∀ sK2 sK1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK2 sK1 X0
    conv => enter [1, 1]; rw [l31 sK2 sK1]
    conv => enter [1]; rw [← h4512 sK1 (sK2 ◇ (sK2 ◇ sK1)) X0]
  have l35 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l34 sK0 sK1 X0]
  have l36 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK0 sK1]
  have l37 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [l21 sK0 sK1 sK2]
    conv => enter [1]; rw [l32 sK2 sK1]
    conv => enter [1, 2]; rw [l21 sK2 sK1 sK0]
  have l38 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [← l36 sK0 sK1]
  have l39 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK1) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l37 sK2 sK1 sK0]
  have l40 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 1]; rw [l21 sK0 sK1 sK2]
    conv => enter [1]; rw [l39 sK2 sK1 sK0]
  have l41 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l38 sK0 sK1]
    conv => enter [1]; rw [l40 sK0 sK1 sK2]
  have l42 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [l38 sK0 sK1]
  have l43 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l42 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l44 : ∀ sK2 sK1 sK0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2]; rw [l22 sK2 sK1 sK0]
  have l45 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2, 2]; rw [l21 sK0 sK1 sK2]
    conv => enter [1]; rw [← l44 sK2 sK1 sK0]
    conv => enter [1, 1]; rw [l21 sK2 sK1 sK0]
  have l46 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l45 sK0 sK0 sK1]
  have l47 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53913 X0 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← l36 sK0 sK1]
  have l48 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) ◇ X0) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [l23 sK0 sK1 sK2]
  have l49 : ∀ sK0 sK1 X0 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) = (sK0 ◇ ((sK2 ◇ (sK2 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0 sK2
    conv => enter [1]; rw [l48 sK0 sK1 X0 sK2]
    conv => enter [1]; rw [← h4512 sK0 (sK2 ◇ (sK2 ◇ sK1)) X0]
  have l50 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l49 sK0 sK1 X0 sK0]
  have l51 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0)) = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l50 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ sK1) X0]
  have l52 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
    conv => enter [1]; rw [l51 sK0 sK1 X0]
  have l53 : ∀ X0 sK1 X1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (X1 ◇ sK1)))) = ((sK1 ◇ (X1 ◇ sK1)) ◇ ((sK1 ◇ (X1 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 X1 sK2
    conv => enter [1]; rw [h53913 X0 (sK1 ◇ (X1 ◇ sK1)) sK1]
    conv => enter [1, 2, 2]; rw [← l24 sK2 sK1 X1]
  have l54 : ∀ sK2 sK1 X1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ X1) = (sK1 ◇ ((sK1 ◇ (X0 ◇ sK1)) ◇ X1)) := by
    intro sK2 sK1 X1 X0
    conv => enter [1, 1]; rw [l24 sK2 sK1 X0]
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (X0 ◇ sK1)) X1]
  have l55 : ∀ sK2 sK1 X1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ X1) = (sK1 ◇ (sK1 ◇ ((X0 ◇ sK1) ◇ X1))) := by
    intro sK2 sK1 X1 X0
    conv => enter [1]; rw [l54 sK2 sK1 X1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 (X0 ◇ sK1) X1]
  have l56 : ∀ X0 sK1 X1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (X1 ◇ sK1)))) = (sK1 ◇ ((X1 ◇ sK1) ◇ ((sK1 ◇ (X1 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK1 X1 sK2
    conv => enter [1]; rw [l53 X0 sK1 X1 sK2]
    conv => enter [1]; rw [← h4512 sK1 (X1 ◇ sK1) ((sK1 ◇ (X1 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1)))]
  have l57 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l21 sK0 sK1 sK2]
    conv => enter [1]; rw [l24 sK2 sK1 sK2]
  have l58 : ∀ sK2 sK1 X1 X0 : G, ((sK2 ◇ (sK2 ◇ sK1)) ◇ X1) = (sK1 ◇ (sK1 ◇ (X0 ◇ (sK1 ◇ X1)))) := by
    intro sK2 sK1 X1 X0
    conv => enter [1]; rw [l55 sK2 sK1 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 sK1 X1]
  have l59 : ∀ X0 sK1 X1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (X1 ◇ sK1)))) = (sK1 ◇ (X1 ◇ (sK1 ◇ ((sK1 ◇ (X1 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1)))))) := by
    intro X0 sK1 X1 sK2
    conv => enter [1]; rw [l56 X0 sK1 X1 sK2]
    conv => enter [1, 2]; rw [← h4512 X1 sK1 ((sK1 ◇ (X1 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1)))]
  have l60 : ∀ sK0 sK1 X1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ X1) = (sK1 ◇ (sK1 ◇ (X0 ◇ (sK1 ◇ X1)))) := by
    intro sK0 sK1 X1 X0
    conv => enter [1]; rw [l58 sK0 sK1 X1 X0]
  have l61 : ∀ X0 sK1 X1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (X1 ◇ sK1)))) = (sK1 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ ((X1 ◇ sK1) ◇ (sK2 ◇ (sK2 ◇ sK1))))))) := by
    intro X0 sK1 X1 sK2
    conv => enter [1]; rw [l59 X0 sK1 X1 sK2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 (X1 ◇ sK1) (sK2 ◇ (sK2 ◇ sK1))]
  have l62 : ∀ X0 sK1 X1 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (X1 ◇ sK1)))) = (sK1 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (X1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK1)))))))) := by
    intro X0 sK1 X1 sK2
    conv => enter [1]; rw [l61 X0 sK1 X1 sK2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 sK1 (sK2 ◇ (sK2 ◇ sK1))]
  have l63 : ∀ X0 sK1 X1 sK0 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (X1 ◇ sK1)))) = (sK1 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK2 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK1 X1 sK0 sK2
    conv => enter [1]; rw [l62 X0 sK1 X1 sK2]
    conv => enter [1, 2, 2]; rw [← l60 sK0 sK1 (sK2 ◇ (sK2 ◇ sK1)) X1]
  have l64 : ∀ X0 sK1 X1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (X1 ◇ sK1)))) = (sK1 ◇ (X1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro X0 sK1 X1 sK0
    conv => enter [1]; rw [l63 X0 sK1 X1 sK0 X0]
    conv => enter [1, 2, 2, 2]; rw [l21 X0 sK1 sK0]
  have l65 : ∀ X0 sK1 X1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (X1 ◇ sK1)))) = (sK1 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro X0 sK1 X1 sK0
    conv => enter [1]; rw [l64 X0 sK1 X1 sK0]
    conv => enter [1, 2, 2]; rw [l38 sK0 sK1]
  have l66 : ∀ sK1 X1 sK0 sK2 : G, (sK1 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (X1 ◇ sK1)) := by
    intro sK1 X1 sK0 sK2
    conv => enter [1]; rw [← l65 sK1 sK1 X1 sK0]
    conv => enter [1]; rw [← l30 sK2 sK1 (X1 ◇ sK1) sK1]
  have l67 : ∀ sK1 X1 sK0 : G, (sK1 ◇ (X1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (X1 ◇ sK1)) := by
    intro sK1 X1 sK0
    conv => enter [1]; rw [l66 sK1 X1 sK0 sK1]
    conv => enter [1, 1]; rw [l21 sK1 sK1 sK0]
  have l68 : ∀ sK2 sK1 : G, (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1, 2]; rw [← l27 sK2 sK1]
    conv => enter [1]; rw [h4512 sK2 (sK2 ◇ sK1) (sK1 ◇ sK1)]
  have l69 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2, 2]; rw [l21 sK0 sK1 sK2]
    conv => enter [1]; rw [l68 sK2 sK1]
    conv => enter [1, 1]; rw [l21 sK2 sK1 sK0]
  have l70 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l69 sK0 sK0 sK1]
  have l71 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = ((sK1 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [h53913 X0 (sK1 ◇ sK1) (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [l28 sK0 sK1 sK2]
  have l72 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l71 X0 sK1 sK0 sK2]
    conv => enter [1]; rw [← h4512 sK1 sK1 ((sK1 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))))]
  have l73 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))))))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l72 X0 sK1 sK0 sK2]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
  have l74 : ∀ X0 sK1 sK0 sK2 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK1 sK0 sK2
    conv => enter [1]; rw [l73 X0 sK1 sK0 sK2]
    conv => enter [1]; rw [← l60 sK0 sK1 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) sK1]
  have l75 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l74 X0 sK1 sK0 sK0]
  have l76 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l75 sK0 sK1 sK0]
    conv => enter [1]; rw [← l30 sK2 sK1 sK1 sK0]
  have l77 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l76 sK0 sK1 sK0]
  have l78 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [l77 sK0 sK1]
  have l79 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53913 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [l77 sK0 sK1]
  have l80 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [l77 sK0 sK1]
  have l81 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l80 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 X0]
  have l82 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l79 X0 sK0 sK1]
    conv => enter [1, 2]; rw [l20 sK0 sK1]
  have l83 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l78 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  have l84 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l82 X0 sK0 sK1]
    conv => enter [1, 2]; rw [l23 sK0 sK1 sK2]
  have l85 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l9 sK0 sK1 (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [← l84 X0 sK0 sK1 sK2]
  have l86 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l85 sK0 sK1 sK0 X0]
  have l87 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l77 sK0 sK1]
    conv => enter [1]; rw [l86 sK0 sK1 X0]
  have l88 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53913 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [l83 sK0 sK1]
  have l89 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l88 X0 sK0 sK1]
    conv => enter [1, 2]; rw [h53913 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK1 sK2]
  have l90 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [l57 sK0 sK1 sK0]
    conv => enter [1]; rw [← l89 X0 sK0 sK1 sK0]
  have l91 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l87 sK0 sK1 sK0]
    conv => enter [1]; rw [← l90 sK0 sK1 sK0]
  have l92 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53913 X0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l91 sK0 sK1]
  have l93 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l92 X0 sK0 sK1]
    conv => enter [1]; rw [l43 sK0 sK1 ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)]
  have l94 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l93 X0 sK0 sK1]
    conv => enter [1, 2]; rw [l20 sK0 sK1]
  have l95 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l94 X0 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1))]
  have l96 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l95 X0 sK0 sK1]
    conv => enter [1]; rw [← l46 sK0 sK1]
  have l97 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) = (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [h53913 X0 ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [l29 sK0 sK1 sK2]
  have l98 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l97 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 (((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))))]
  have l99 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l98 X0 sK0 sK1 sK2]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ (sK0 ◇ sK1)) sK1 (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
  have l100 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l99 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l35 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))))]
  have l101 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l100 X0 sK0 sK1 sK2]
    conv => enter [1]; rw [l43 sK0 sK1 (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))))]
  have l102 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))))) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [l101 X0 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [← l18 sK0 sK1 (sK2 ◇ (sK2 ◇ sK1))]
  have l103 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))]
    conv => enter [1]; rw [← l102 X0 sK0 sK1 sK2]
  have l104 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1)))) = (X0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l9 sK0 sK1 (sK2 ◇ (sK2 ◇ sK1))]
    conv => enter [1]; rw [l103 sK0 sK1 sK2 X0]
  have l105 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (X0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l104 sK0 sK1 sK0 X0]
  have l106 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = (X0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l77 sK0 sK1]
    conv => enter [1]; rw [l105 sK0 sK1 X0]
  have l107 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [h53913 X0 (sK1 ◇ (sK0 ◇ sK1)) (sK0 ◇ (sK0 ◇ sK1))]
    conv => enter [1, 2, 2]; rw [← l46 sK0 sK1]
  have l108 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l107 X0 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))]
  have l109 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l108 X0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l110 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK1 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l109 X0 sK1 sK0]
    conv => enter [1, 2]; rw [← l52 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))]
  have l111 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l110 X0 sK1 sK0]
    conv => enter [1]; rw [l67 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) sK0]
  have l112 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ sK1)) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l111 X0 sK1 sK0]
    conv => enter [1]; rw [l81 sK0 sK1 sK1]
  have l113 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l112 X0 sK1 sK0]
    conv => enter [1]; rw [← l70 sK0 sK1]
  have l114 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK2 ◇ (sK2 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l113 sK0 sK1 sK0]
    conv => enter [1]; rw [← l30 sK2 sK1 (sK0 ◇ sK1) sK0]
  have l115 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l114 sK0 sK1 sK0]
  have l116 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l115 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l117 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l115 sK0 sK1]
  have l118 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l117 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l119 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l87 sK0 sK1 sK0]
    conv => enter [1]; rw [l116 sK0 sK1]
  have l120 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h53913 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← l119 sK0 sK1]
  have l121 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1))) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h53913 X0 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l119 sK0 sK1]
  have l122 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [l121 X0 sK0 sK1]
    conv => enter [1]; rw [← l106 sK0 sK1 (sK0 ◇ sK1)]
  have l123 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l120 sK0 sK1]
    conv => enter [1]; rw [l20 sK0 sK1]
  have l124 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l122 sK0 sK0 sK1]
    conv => enter [1]; rw [l47 sK0 sK0 sK1]
  have l125 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l123 sK0 sK1]
    conv => enter [1]; rw [l23 sK0 sK1 sK2]
  have l126 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l125 sK0 sK1 sK0]
  have l127 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l126 sK0 sK1]
    conv => enter [1]; rw [l96 (sK0 ◇ sK1) sK0 sK1]
  have l128 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l127 sK0 sK1]
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
  have l129 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ sK1)) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← h53913 (sK0 ◇ (sK0 ◇ sK1)) sK1 sK0]
    conv => enter [1, 2]; rw [l124 sK0 sK1]
  have l130 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l129 sK1 sK0]
    conv => enter [1]; rw [l118 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l131 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l130 sK1 sK0]
    conv => enter [1]; rw [← l128 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l132 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1]; rw [l131 sK1 sK0]
    conv => enter [1]; rw [l83 sK0 sK1]
  have l133 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h53913 sK2 sK1 sK0]
    conv => enter [1]; rw [l132 sK1 sK0]
  have l134 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l133 sK0 sK1 sK0]
  have l135 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l24 sK2 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2]; rw [← l134 sK0 sK1]
  have l136 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ sK1)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l135 sK2 sK1 sK0]
    conv => enter [1]; rw [l96 sK1 sK0 sK1]
  have l137 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l127 sK0 sK1]
    conv => enter [1]; rw [← l136 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l137 z y x]

@[equational_result]
theorem Equation53976_implies_Equation53913 (G : Type*) [Magma G] (h53976 : Equation53976 G) : Equation53913 G := by
  have l0 : ∀ X1 sK1 X0 sK0 : G, (X1 ◇ (X1 ◇ sK1)) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro X1 sK1 X0 sK0
    conv => enter [1]; rw [h53976 X1 sK1 X0]
    conv => enter [1, 2]; rw [h53976 X0 sK1 sK0]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h53976 sK0 sK1 sK0]
    conv => enter [1]; rw [l0 sK0 sK1 X0 sK0]
  have l2 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) = (sK2 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [← h53976 sK2 (sK2 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [h53976 sK2 sK1 sK0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [← l2 sK1 sK2 sK0]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h53976 sK1 (sK2 ◇ sK1) sK1]
    conv => enter [1]; rw [← l3 sK0 sK1 sK2]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h53976 sK0 sK1 sK0]
    conv => enter [1]; rw [← l4 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

theorem Equation4512_53922_implies_Equation53941 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53922 : Equation53922 G) : Equation53941 G := by
  have l0 : ∀ sK2 sK0 X0 : G, (sK2 ◇ ((sK0 ◇ (sK2 ◇ sK0)) ◇ X0)) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK2 ◇ sK0) X0]
    conv => enter [1]; rw [h4512 sK2 sK0 ((sK2 ◇ sK0) ◇ X0)]
  have l1 : ∀ sK2 sK0 X0 : G, ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X0) = ((sK2 ◇ sK0) ◇ ((sK2 ◇ sK0) ◇ X0)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← h4512 sK2 (sK0 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1]; rw [l0 sK2 sK0 X0]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X2 ◇ (X2 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53922 X0 X1 X0]
    conv => enter [1]; rw [← h53922 X2 X1 X0]
  have l3 : ∀ X0 sK2 sK0 : G, (X0 ◇ (X0 ◇ sK2)) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro X0 sK2 sK0
    conv => enter [1]; rw [h53922 X0 sK2 sK0]
    conv => enter [1]; rw [h4512 sK2 sK0 (sK2 ◇ sK0)]
  have l4 : ∀ sK2 sK0 X0 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (X0 ◇ (X0 ◇ sK2)) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [h4512 sK2 sK0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l3 X0 sK2 sK0]
  have l5 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ ((X1 ◇ sK2) ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [h53922 X0 X1 (X1 ◇ sK2)]
    conv => enter [1, 2, 2]; rw [← l4 sK2 sK0 X1]
  have l6 : ∀ X0 sK2 X1 sK0 : G, (X0 ◇ ((X0 ◇ sK2) ◇ X1)) = ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X1) := by
    intro X0 sK2 X1 sK0
    conv => enter [1]; rw [h4512 X0 (X0 ◇ sK2) X1]
    conv => enter [1, 1]; rw [← l4 sK2 sK0 X0]
  have l7 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ sK2) := by
    intro sK2 sK0
    conv => enter [1]; rw [l4 sK2 sK0 (sK2 ◇ sK0)]
    conv => enter [1]; rw [← l1 sK2 sK0 sK2]
  have l8 : ∀ sK2 sK0 X1 X0 : G, ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ X1) = (X0 ◇ (X0 ◇ (sK2 ◇ X1))) := by
    intro sK2 sK0 X1 X0
    conv => enter [1]; rw [← l6 X0 sK2 X1 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 sK2 X1]
  have l9 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ (X0 ◇ X1)) = (X1 ◇ (X1 ◇ (sK2 ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [l5 X0 X1 sK2 sK0]
    conv => enter [1, 2]; rw [← h4512 X1 sK2 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
  have l10 : ∀ X0 X1 sK2 sK0 : G, (X0 ◇ (X0 ◇ X1)) = ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro X0 X1 sK2 sK0
    conv => enter [1]; rw [l9 X0 X1 sK2 sK0]
    conv => enter [1]; rw [← l8 sK2 sK0 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) X1]
  have l11 : ∀ sK2 sK0 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) = ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l4 sK2 sK0 (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))]
    conv => enter [1, 2]; rw [← l7 sK2 sK0]
  have l12 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) ◇ (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l10 sK0 sK1 sK2 sK0]
  have l13 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l12 sK0 sK1 sK2]
    conv => enter [1]; rw [← l11 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l13 x y z]

theorem Equation4512_53941_implies_Equation53922 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h53941 : Equation53941 G) : Equation53922 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h53941 X0 X1 X0]
    conv => enter [1]; rw [← h53941 X0 X2 X0]
  have l1 : ∀ sK2 X0 sK1 : G, (sK2 ◇ (sK2 ◇ X0)) = ((sK1 ◇ sK2) ◇ (sK1 ◇ sK2)) := by
    intro sK2 X0 sK1
    conv => enter [1]; rw [h53941 sK2 X0 sK1]
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
  have l2 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (sK2 ◇ (sK2 ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [h4512 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← l1 sK2 X0 sK1]
  have l3 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = (sK2 ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l2 sK1 sK2 ((sK1 ◇ sK2) ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK2 (sK1 ◇ sK2) X0]
  have l4 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK2 ◇ ((sK2 ◇ (sK1 ◇ sK2)) ◇ X0)) := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [l2 sK1 sK2 (sK1 ◇ sK2)]
    conv => enter [1]; rw [← h4512 sK2 (sK2 ◇ (sK1 ◇ sK2)) X0]
  have l5 : ∀ sK1 sK2 X0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [l3 sK1 sK2 X0]
    conv => enter [1]; rw [← l4 sK1 sK2 X0]
  have l6 : ∀ X0 X1 sK1 sK2 : G, (X0 ◇ (X0 ◇ X1)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro X0 X1 sK1 sK2
    conv => enter [1]; rw [h53941 X0 X1 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [← l5 sK1 sK2 (X0 ◇ ((sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) ◇ X0))]
  have l7 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK2))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [l6 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

end Semigroup5
