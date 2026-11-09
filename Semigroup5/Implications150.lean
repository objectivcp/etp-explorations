import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_4902_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4902 : Equation4902 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X2)) = (X0 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) X2]
    conv => enter [1, 1]; rw [← h4902 X0 X1]
  have l1 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l0 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X0 ◇ (X1 ◇ X1))) X2]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l1 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X1)) X2]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X1 X2]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (X1 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 (X0 ◇ (X1 ◇ X1)) X0]
    conv => enter [1, 2, 2, 2]; rw [← h4902 X0 X1]
  have l6 : ∀ X0 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) = ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [l5 X0 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1, 2]; rw [← h4902 X0 X0]
  have l7 : ∀ X0 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l6 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X0)) X0]
  have l8 : ∀ X0 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X0]
  have l9 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1, 2, 2]; rw [h4512 X0 X0 X0]
    conv => enter [1]; rw [← l8 X0]
  have l10 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [l9 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X0)) (X0 ◇ X0)]
  have l11 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) := by
    intro X0
    conv => enter [1]; rw [l10 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l12 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X0
    conv => enter [1]; rw [l11 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l13 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [l4 X0 X0 X0]
    conv => enter [1]; rw [← l12 X0]
  have l14 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l13 X0]
    conv => enter [1]; rw [← h4902 X0 X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [l13 X0]
    conv => enter [1]; rw [← l4 X1 (X0 ◇ (X0 ◇ X0)) X0]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l15 X0 X1]
    conv => enter [1]; rw [← h4902 X1 X0]
  have l17 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l14 X0]
    conv => enter [1]; rw [l16 X1 X0]
  have l18 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l17 X0 (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h4902 X1 X0]
  intro x y
  conv => enter [1]; rw [l18 x y]

@[equational_result]
theorem Equation2_implies_Equation4903 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4903 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (x ◇ (y ◇ z)))))]

theorem Equation4512_4903_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4903 : Equation4903 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X0)))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4903 X0 X1 X1]
    conv => enter [1]; rw [← h4903 X2 X1 (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4903 X0 X0 X0]
    conv => enter [1]; rw [← h4903 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))))]
    conv => enter [1]; rw [← h4903 X0 (X1 ◇ X2) X3]
  have l3 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l2 X1 X2 X0 X3]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X1 X0 (X1 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l3 X1 X1 X0 X1]
  have l5 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [← l4 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4903 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l4 X1 (X0 ◇ (X0 ◇ (X1 ◇ X2)))]
    conv => enter [1]; rw [l5 X1 X0 X2]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [← l4 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [l6 X0 X1 X2]
  have l8 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l4 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [l7 X0 X1 X2]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X1 X1 X0]
    conv => enter [1]; rw [l1 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation2_implies_Equation4905 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4905 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (x ◇ (z ◇ y)))))]

theorem Equation4512_4905_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4905 : Equation4905 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X3 ◇ (X3 ◇ (X3 ◇ X0)))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4905 X0 X2 X1]
    conv => enter [1]; rw [← h4905 X3 (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) X2]
  have l1 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X2 ◇ X0))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [h4905 X0 X2 X1]
    conv => enter [1]; rw [← h4905 X2 (X0 ◇ (X0 ◇ (X1 ◇ X2))) X0]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X2 ◇ X0)))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ X2)) (X2 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l1 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ (X3 ◇ (X3 ◇ X0))))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ (X1 ◇ X2))) (X3 ◇ (X3 ◇ (X3 ◇ X0)))]
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ X0))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ X2) (X2 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l2 X0 X1 X2]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X3 ◇ (X3 ◇ X0)))))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X0 (X0 ◇ (X1 ◇ X2)) (X3 ◇ (X3 ◇ (X3 ◇ X0)))]
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X0)))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X1 X2 (X2 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l4 X0 X1 X2]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ (X3 ◇ X0))))))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 (X1 ◇ X2) (X3 ◇ (X3 ◇ (X3 ◇ X0)))]
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
  have l8 : ∀ X0 X3 : G, (X0 ◇ X3) = X3 := by
    intro X0 X3
    conv => enter [1, 2]; rw [← l6 X0 (X0 ◇ X0) X3]
    conv => enter [1]; rw [l7 X0 X0 X0 X3]
  have l9 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l8 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← h4905 X0 X2 X1]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l8 X2 (X0 ◇ (X0 ◇ (X1 ◇ X2)))]
    conv => enter [1]; rw [l9 X2 X0 X1]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [← l8 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [l10 X0 X1 X2]
  have l12 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l8 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [l11 X0 X1 X2]
  have l13 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l12 X0 (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h4905 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l13 x y]

@[equational_result]
theorem Equation2_implies_Equation4906 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4906 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (x ◇ (z ◇ z)))))]

theorem Equation4512_4906_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4906 : Equation4906 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X3 X2 : G, (X0 ◇ X1) = (X3 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2)))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4906 (X0 ◇ X1) X3 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2)))]
  have l1 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X3)))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X3))))]
    conv => enter [1]; rw [← h4906 X0 (X1 ◇ X2) X3]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4906 X0 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X0 X1]
  have l3 : ∀ X0 X1 X3 X2 : G, (X0 ◇ X1) = (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l0 X0 X1 X3 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X2 ◇ X2))]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X0 X2]
    conv => enter [1, 2]; rw [l2 X0 (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2)))))]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2)))))]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1]; rw [l2 X1 (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))))]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2)))]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l7 X0 X1 X2]
    conv => enter [1]; rw [l2 X1 ((X0 ◇ X1) ◇ (X2 ◇ X2))]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X1 ◇ (X2 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 (X1 ◇ (X2 ◇ X2))]
  have l11 : ∀ X2 X0 X1 : G, (X2 ◇ X2) = (X0 ◇ X1) := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l2 X1 (X2 ◇ X2)]
    conv => enter [1]; rw [← l10 X0 X1 X2]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l11 X2 X0 X1]
    conv => enter [1]; rw [l2 X2 X2]
  have l13 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l12 X0 (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h4906 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l13 x y]

@[equational_result]
theorem Equation2_implies_Equation4907 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4907 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (x ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation4907_implies_Equation2 (G : Type*) [Magma G] (h4907 : Equation4907 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2]; rw [h4907 X0 X2 X1 X1]
    conv => enter [1]; rw [← h4907 X2 X1 X0 (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4907 X0 X0 X1 X1]
    conv => enter [1]; rw [← h4907 X0 X1 X0 (X1 ◇ X1)]
  have l2 : ∀ X2 X0 : G, (X2 ◇ (X2 ◇ X0)) = X2 := by
    intro X2 X0
    conv => enter [1, 2, 2]; rw [← l1 X2 X0]
    conv => enter [1]; rw [l0 X2 X2 X0]
  have l3 : ∀ X2 X0 : G, (X2 ◇ X0) = X2 := by
    intro X2 X0
    conv => enter [1, 2]; rw [← l1 X2 X0]
    conv => enter [1]; rw [l2 X2 X0]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h4907 X1 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation2_implies_Equation4909 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4909 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (y ◇ (x ◇ y)))))]

theorem Equation4512_4909_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4909 : Equation4909 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4909 X0 X1]
    conv => enter [1]; rw [← h4909 X1 (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X2)) = (X0 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) X2]
    conv => enter [1, 1]; rw [← h4909 X0 X1]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X0 ◇ X1))) X2]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X0 ◇ X1))) (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))]
    conv => enter [1]; rw [l0 X0 X1]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X1)) X2]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ (X0 ◇ X1)) (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))]
    conv => enter [1]; rw [l3 X0 X1]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X1 (X0 ◇ X1) (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))]
    conv => enter [1]; rw [l5 X0 X1]
  have l8 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))]
    conv => enter [1]; rw [l7 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X0 ◇ X1))) X0]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)))))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))))))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [l8 X0 X0 X1]
    conv => enter [1]; rw [l13 X0 X1]
  have l15 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0
    conv => enter [1, 2, 2, 2]; rw [← l14 X0 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l8 X0 X0 X0]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l14 X1 X0]
    conv => enter [1]; rw [← l8 X1 (X0 ◇ (X1 ◇ X1)) X0]
  have l17 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1]; rw [l15 X0]
    conv => enter [1]; rw [← h4909 X0 X0]
  have l18 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l16 X0 X0]
    conv => enter [1]; rw [l17 X0]
  have l19 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0 X0]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [l18 X0]
  have l20 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l19 X1 X0]
    conv => enter [1]; rw [← h4909 X1 X0]
  have l21 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l20 X0 (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))))]
    conv => enter [1]; rw [l14 X0 X1]
  intro x y
  conv => enter [1]; rw [l21 x y]

@[equational_result]
theorem Equation2_implies_Equation4910 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4910 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (y ◇ (x ◇ z)))))]

theorem Equation4512_4910_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4910 : Equation4910 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4910 X0 X2 X1]
    conv => enter [1]; rw [← h4910 X2 X1 (X0 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1))))]
  have l1 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X3)) := by
    intro X0 X3 X1 X2
    conv => enter [1, 1]; rw [h4910 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) X3]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l1 X0 X3 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X0 ◇ X2))) X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X2)) X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ X2) X3]
  have l5 : ∀ X0 X3 : G, (X0 ◇ X3) = X0 := by
    intro X0 X3
    conv => enter [1]; rw [l4 X0 X3 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 ((X0 ◇ X0) ◇ X3)]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))]
    conv => enter [1]; rw [← h4910 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation2_implies_Equation4912 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4912 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (y ◇ (y ◇ y)))))]

theorem Equation4512_4912_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4912 : Equation4912 G) : Equation2 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h4912 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h4912 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 : G, (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4512 X0 X0 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4912 X0 X0]
    conv => enter [1]; rw [l2 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l3 X0]
    conv => enter [1]; rw [← h4912 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l3 X0]
    conv => enter [1]; rw [l5 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l4 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4912 X0 X1]
    conv => enter [1]; rw [l7 (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1))) X0]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l7 X1 X1]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l11 X1 X0]
    conv => enter [1]; rw [l7 X0 X1]
  have l13 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l11 X0 X0]
    conv => enter [1]; rw [l12 X0 X1]
  intro x y
  conv => enter [1]; rw [l13 x y]

@[equational_result]
theorem Equation2_implies_Equation4913 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4913 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (y ◇ (y ◇ z)))))]

theorem Equation4512_4913_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4913 : Equation4913 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4913 X0 X1 X1]
    conv => enter [1]; rw [← h4913 X2 X1 (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))]
  have l1 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) X3]
    conv => enter [1, 1]; rw [← h4913 X0 X1 X2]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l1 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ X2))) X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X2)) X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X1 ◇ X2) X3]
  have l5 : ∀ X0 X3 : G, (X0 ◇ X3) = X0 := by
    intro X0 X3
    conv => enter [1]; rw [l4 X0 X3 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 ((X0 ◇ X0) ◇ X3)]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h4913 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation2_implies_Equation4915 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4915 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (y ◇ (z ◇ y)))))]

theorem Equation4512_4915_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4915 : Equation4915 G) : Equation2 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))))) = X3 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [← h4915 X3 X2 (X0 ◇ X1)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4915 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h4915 X1 X0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l3 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2]; rw [← l5 X1 X0]
    conv => enter [1]; rw [← h4915 X2 X1 X0]
  have l7 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0)))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2, 2]; rw [← l5 X1 X0]
    conv => enter [1]; rw [← h4915 X2 (X0 ◇ X1) X1]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0)))]
    conv => enter [1]; rw [l7 X0 X1 X2]
  have l9 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [l3 X2 X0]
    conv => enter [1]; rw [l6 X1 X2 X0]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0)))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [l3 X2 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [l8 X0 X1 X2]
  have l11 : ∀ X1 X2 : G, X1 = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l9 X1 X1 (X2 ◇ ((X1 ◇ X1) ◇ X1))]
    conv => enter [1]; rw [l10 X1 X1 X2]
  intro x y
  conv => enter [1]; rw [l11 x y]

@[equational_result]
theorem Equation2_implies_Equation4916 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4916 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (y ◇ (z ◇ z)))))]

theorem Equation4512_4916_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4916 : Equation4916 G) : Equation2 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h4916 (X0 ◇ X0) (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h4916 (X0 ◇ X0) (X0 ◇ X0) X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h4916 X0 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h4916 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l1 (X0 ◇ X0)]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1]; rw [← h4512 X0 X0 ((X0 ◇ X0) ◇ (X0 ◇ X0))]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l5 X0]
    conv => enter [1]; rw [← h4916 X0 X0 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l6 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4916 X0 X1 X1]
    conv => enter [1]; rw [← l7 X1 (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))]
    conv => enter [1]; rw [← h4916 X0 X1 X1]
  have l9 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l7 X0 (X1 ◇ (X2 ◇ X2))]
    conv => enter [1]; rw [← h4916 X0 X1 X2]
  have l10 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [← l6 X2]
    conv => enter [1]; rw [l9 X1 X0 X2]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = X0 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l8 X1 (X0 ◇ (X1 ◇ X2))]
    conv => enter [1]; rw [l10 X1 X0 X2]
  have l12 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l8 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [l11 X0 X1 X2]
  have l13 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l12 X1 (X1 ◇ (X1 ◇ X1)) X0]
    conv => enter [1]; rw [l2 X1]
  intro x y
  conv => enter [1]; rw [l13 x y]

@[equational_result]
theorem Equation2_implies_Equation4917 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4917 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (y ◇ (z ◇ w)))))]

theorem Equation4512_4917_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4917 : Equation4917 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2]; rw [h4917 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4917 X2 X1 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l1 : ∀ X1 X0 X2 X3 X4 : G, (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X4)) = (X0 ◇ X4) := by
    intro X1 X0 X2 X3 X4
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) X4]
    conv => enter [1, 1]; rw [← h4917 X0 X1 X2 X3]
  have l2 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l1 X1 X0 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ X3))) X4]
  have l3 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X3)) X4]
  have l4 : ∀ X0 X4 : G, (X0 ◇ X4) = X0 := by
    intro X0 X4
    conv => enter [1]; rw [l3 X0 X4 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 ((X0 ◇ (X0 ◇ X0)) ◇ X4)]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h4917 X1 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation2_implies_Equation4919 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4919 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (z ◇ (x ◇ y)))))]

theorem Equation4512_4919_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4919 : Equation4919 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4919 X0 X0 X1]
    conv => enter [1]; rw [← h4919 X0 (X1 ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4919 X0 X0 X0]
    conv => enter [1]; rw [← h4919 X0 (X0 ◇ X0) X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 X0 X0]
    conv => enter [1]; rw [l1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4512 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l3 X1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l2 X0]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2, 2]; rw [← l2 X0]
    conv => enter [1]; rw [← h4919 X0 X0 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [← l2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1, 2]; rw [l5 X1 (X0 ◇ X1)]
  have l9 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l5 X0 X0]
    conv => enter [1]; rw [l6 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l9 X0]
    conv => enter [1]; rw [l5 X1 X0]
  have l11 : ∀ X0 X1 X2 : G, ((X0 ◇ X0) ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) = X1 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2, 2]; rw [← l5 X1 X0]
    conv => enter [1]; rw [← h4919 X1 (X0 ◇ X0) X2]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0))))) = X1 := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X0 (X1 ◇ (X1 ◇ (X2 ◇ X0)))]
    conv => enter [1]; rw [l11 X0 X1 X2]
  have l13 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) = X1 := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 (X1 ◇ (X1 ◇ (X2 ◇ X0)))]
    conv => enter [1]; rw [l12 X0 X1 X2]
  have l14 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X1 := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l10 X0 (X1 ◇ (X1 ◇ (X2 ◇ X0)))]
    conv => enter [1]; rw [l13 X0 X1 X2]
  have l15 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = X1 := by
    intro X1 X2 X0
    conv => enter [1]; rw [l8 X1 (X2 ◇ X0)]
    conv => enter [1]; rw [l14 X1 X2 X0]
  have l16 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = X1 := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l10 X1 (X2 ◇ X0)]
    conv => enter [1]; rw [l15 X1 X2 X0]
  have l17 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l16 X1 X1 X0]
    conv => enter [1]; rw [l9 X1]
  intro x y
  conv => enter [1]; rw [l17 x y]

@[equational_result]
theorem Equation2_implies_Equation4920 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4920 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (z ◇ (x ◇ z)))))]

theorem Equation4512_4920_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4920 : Equation4920 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X3 X2 : G, (X0 ◇ X1) = (X3 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4920 (X0 ◇ X1) X3 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))]
  have l1 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X3)))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X3))))]
    conv => enter [1]; rw [← h4920 X0 (X1 ◇ X2) X3]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4920 X0 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X0 X1]
  have l3 : ∀ X0 X1 X3 X2 : G, (X0 ◇ X1) = (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l0 X0 X1 X3 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X2))]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X0 X2]
    conv => enter [1, 2]; rw [l2 X0 (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))))]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))))]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1]; rw [l2 X1 (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))))]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l7 X0 X1 X2]
    conv => enter [1]; rw [l2 X1 (X2 ◇ ((X0 ◇ X1) ◇ X2))]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1]; rw [l2 X2 ((X0 ◇ X1) ◇ X2)]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1 X2]
    conv => enter [1]; rw [l2 (X0 ◇ X1) X2]
  have l11 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l10 X0 (X2 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) X0]
    conv => enter [1]; rw [← h4920 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l11 x y]

@[equational_result]
theorem Equation2_implies_Equation4921 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4921 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (z ◇ (x ◇ w)))))]

@[equational_result]
theorem Equation4921_implies_Equation2 (G : Type*) [Magma G] (h4921 : Equation4921 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X0)))) = X2 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4921 X0 X2 X1 X1]
    conv => enter [1]; rw [← h4921 X2 X1 X3 (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4921 X0 X0 X0 X1]
    conv => enter [1]; rw [← h4921 X0 X1 X0 (X0 ◇ X1)]
  have l2 : ∀ X2 X3 X0 : G, (X2 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := by
    intro X2 X3 X0
    conv => enter [1, 2, 2]; rw [← l1 X2 (X3 ◇ X0)]
    conv => enter [1]; rw [l0 X2 X2 X3 X0]
  have l3 : ∀ X2 X3 X0 : G, (X2 ◇ (X3 ◇ X0)) = X2 := by
    intro X2 X3 X0
    conv => enter [1, 2]; rw [← l1 X2 (X3 ◇ X0)]
    conv => enter [1]; rw [l2 X2 X3 X0]
  have l4 : ∀ X3 X0 X2 : G, (X3 ◇ X0) = X2 := by
    intro X3 X0 X2
    conv => enter [1]; rw [← l1 X2 (X3 ◇ X0)]
    conv => enter [1]; rw [l3 X2 X3 X0]
  have l5 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l4 X0 (X2 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))) X0]
    conv => enter [1]; rw [← h4921 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation2_implies_Equation4923 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4923 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (z ◇ (y ◇ y)))))]

theorem Equation4512_4923_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4923 : Equation4923 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4923 (X0 ◇ (X1 ◇ X1)) X1 X0]
    conv => enter [1]; rw [← h4923 X1 (X0 ◇ (X1 ◇ X1)) (X0 ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) (X1 ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 X1 (X1 ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4923 X1 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) = X0 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [← l3 X0 (X1 ◇ (X2 ◇ X2))]
    conv => enter [1]; rw [← h4923 X0 X2 X1]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X2))) = X0 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l3 X2 (X0 ◇ (X1 ◇ (X2 ◇ X2)))]
    conv => enter [1]; rw [l4 X2 X0 X1]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X2)) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l3 X0 (X1 ◇ (X2 ◇ X2))]
    conv => enter [1]; rw [l5 X0 X1 X2]
  have l7 : ∀ X2 X0 : G, (X2 ◇ X2) = X0 := by
    intro X2 X0
    conv => enter [1, 2]; rw [← l3 X2 X2]
    conv => enter [1]; rw [l6 X2 X2 X0]
  have l8 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l3 X0 X0]
    conv => enter [1]; rw [l7 X0 X2]
  intro x y
  conv => enter [1]; rw [l8 x y]

@[equational_result]
theorem Equation2_implies_Equation4924 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4924 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (z ◇ (y ◇ z)))))]

theorem Equation4512_4924_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4924 : Equation4924 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4924 (X0 ◇ (X1 ◇ X0)) X1 X0]
    conv => enter [1]; rw [← h4924 X1 (X0 ◇ (X1 ◇ X0)) (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 X1 X3 X2 : G, (X0 ◇ X1) = (X3 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X2)))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4924 (X0 ◇ X1) X3 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X2)))]
  have l2 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) X3]
    conv => enter [1, 1]; rw [← h4924 X0 X1 X2]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l2 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X2 ◇ (X1 ◇ X2))) X3]
  have l4 : ∀ X0 X1 X3 X2 : G, (X0 ◇ X1) = (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2))))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l1 X0 X1 X3 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X2))]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) (X1 ◇ (X0 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [l0 X0 X1]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X2 ◇ (X1 ◇ X2)) X3]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 X0 (X1 ◇ (X0 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [l5 X0 X1]
  have l8 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l6 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (X1 ◇ X2) X3]
  have l9 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l8 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← l7 X1 X0]
    conv => enter [1]; rw [l7 (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) X1]
  have l11 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0)))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l7 X1 X0]
    conv => enter [1]; rw [← h4924 X2 X1 (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))]
  have l12 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [← l7 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) X2]
  have l13 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l12 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) X2]
  have l14 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) X0]
    conv => enter [1]; rw [l11 X1 X2 X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0)))))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0))))]
    conv => enter [1]; rw [l10 X0 X1]
  have l16 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l13 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ (X0 ◇ X1))) X2]
  have l17 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0)))))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X1 (X0 ◇ (X1 ◇ (X0 ◇ X1))) X0]
    conv => enter [1]; rw [l14 X1 X2 X0]
  have l18 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 (X0 ◇ (X1 ◇ (X0 ◇ X1))) (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0))))]
    conv => enter [1]; rw [l15 X0 X1]
  have l19 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l16 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X1)) X2]
  have l20 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0))))))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X0 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l17 X1 X2 X0]
  have l21 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0)))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 (X1 ◇ (X0 ◇ X1)) (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0))))]
    conv => enter [1]; rw [l18 X0 X1]
  have l22 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l19 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l23 : ∀ X2 X1 X0 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X2 := by
    intro X2 X1 X0
    conv => enter [1]; rw [l9 X2 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X1 X0]
    conv => enter [1]; rw [l20 X1 X2 X0]
  have l24 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0))))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 (X0 ◇ X1) (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0))))]
    conv => enter [1]; rw [l21 X0 X1]
  have l25 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l22 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l26 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2]; rw [h4512 X1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l23 X2 X1 X0]
  have l27 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0)))))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0))))]
    conv => enter [1]; rw [l24 X0 X1]
  have l28 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l26 X2 X1 X0]
  have l29 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0))))))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0))]
    conv => enter [1]; rw [l27 X0 X1]
  have l30 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0)))))))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X1 (X0 ◇ (X1 ◇ (X0 ◇ X1))) (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0))]
    conv => enter [1]; rw [l29 X0 X1]
  have l31 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0))))))))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 (X1 ◇ (X0 ◇ X1)) (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0))]
    conv => enter [1]; rw [l30 X0 X1]
  have l32 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0)))))))))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X1 (X0 ◇ X1) (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0))]
    conv => enter [1]; rw [l31 X0 X1]
  have l33 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0))))))))))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0))]
    conv => enter [1]; rw [l32 X0 X1]
  have l34 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0))))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [l25 X0 (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0)) X1]
    conv => enter [1]; rw [l33 X0 X1]
  have l35 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l25 X1 (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0)) X0]
    conv => enter [1]; rw [l34 X0 X1]
  have l36 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) X0]
    conv => enter [1]; rw [l35 X1 X0]
  have l37 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 (X0 ◇ (X1 ◇ (X0 ◇ X1))) X0]
    conv => enter [1]; rw [l36 X1 X0]
  have l38 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l37 X1 X0]
  have l39 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l38 X1 X0]
  have l40 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l39 X1 X0]
  have l41 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l4 X0 X1 X1 X0]
    conv => enter [1]; rw [l40 X1 X0]
  have l42 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l41 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  have l43 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l28 X0 X1 X0]
    conv => enter [1]; rw [l42 X0 X1]
  intro x y
  conv => enter [1]; rw [l43 x y]

@[equational_result]
theorem Equation2_implies_Equation4925 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4925 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (z ◇ (y ◇ w)))))]

@[equational_result]
theorem Equation4925_implies_Equation2 (G : Type*) [Magma G] (h4925 : Equation4925 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4925 X0 X1 X0 X0]
    conv => enter [1]; rw [← h4925 X1 X0 X0 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4925 X0 X0 X1 X1]
    conv => enter [1]; rw [← h4925 X0 X1 X0 (X0 ◇ X1)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h4925 X1 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation4927 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4927 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (z ◇ (z ◇ y)))))]

theorem Equation4512_4927_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4927 : Equation4927 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ (X3 ◇ (X3 ◇ (X2 ◇ X0)))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4927 X0 X2 X1]
    conv => enter [1]; rw [← h4927 X3 (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) X2]
  have l1 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ X2)) ◇ (X2 ◇ X0)) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h4927 X0 X2 X1]
    conv => enter [1]; rw [← h4927 X2 (X1 ◇ (X1 ◇ X2)) X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ X2) ◇ (X2 ◇ X0))) = X2 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ X2) (X2 ◇ X0)]
    conv => enter [1]; rw [l1 X1 X2 X0]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X3 ◇ (X3 ◇ (X2 ◇ X0))))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ X2))) (X3 ◇ (X3 ◇ (X2 ◇ X0)))]
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X1 X2 (X2 ◇ X0)]
    conv => enter [1]; rw [l2 X1 X2 X0]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X3 ◇ (X2 ◇ X0)))))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ (X1 ◇ X2)) (X3 ◇ (X3 ◇ (X2 ◇ X0)))]
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ (X2 ◇ X0))))))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X1 (X1 ◇ X2) (X3 ◇ (X3 ◇ (X2 ◇ X0)))]
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X2 ◇ X0)))))))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 X2 (X3 ◇ (X3 ◇ (X2 ◇ X0)))]
    conv => enter [1]; rw [l6 X0 X1 X2 X3]
  have l8 : ∀ X1 X3 : G, X1 = X3 := by
    intro X1 X3
    conv => enter [1]; rw [← l4 X1 X1 (X1 ◇ (X3 ◇ (X3 ◇ (X1 ◇ X1))))]
    conv => enter [1]; rw [l7 X1 X1 X1 X3]
  intro x y
  conv => enter [1]; rw [l8 x y]

@[equational_result]
theorem Equation2_implies_Equation4928 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4928 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (z ◇ (z ◇ z)))))]

theorem Equation4512_4928_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4928 : Equation4928 G) : Equation2 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))))) = X3 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h4928 X3 X2 (X0 ◇ X1)]
  have l1 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X3)))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X3))))]
    conv => enter [1]; rw [← h4928 X0 (X1 ◇ X2) X3]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4928 X0 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X0 X1]
  have l3 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))))) = X3 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X2 X3 X0 X1]
  have l4 : ∀ X3 X0 X1 : G, (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) = X3 := by
    intro X3 X0 X1
    conv => enter [1, 2, 2]; rw [← l2 X3 (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))]
    conv => enter [1]; rw [l3 X3 X3 X0 X1]
  have l5 : ∀ X3 X0 X1 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) = X3 := by
    intro X3 X0 X1
    conv => enter [1, 2]; rw [← l2 X3 (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))]
    conv => enter [1]; rw [l4 X3 X0 X1]
  have l6 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = X3 := by
    intro X0 X1 X3
    conv => enter [1]; rw [← l2 X3 (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))]
    conv => enter [1]; rw [l5 X3 X0 X1]
  have l7 : ∀ X1 X0 X3 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X3 := by
    intro X1 X0 X3
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))]
    conv => enter [1]; rw [l6 X0 X1 X3]
  have l8 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X3 := by
    intro X0 X1 X3
    conv => enter [1]; rw [← l2 X1 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l7 X1 X0 X3]
  have l9 : ∀ X1 X0 X3 : G, (X1 ◇ (X0 ◇ X1)) = X3 := by
    intro X1 X0 X3
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l8 X0 X1 X3]
  have l10 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = X3 := by
    intro X0 X1 X3
    conv => enter [1]; rw [← l2 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l9 X1 X0 X3]
  have l11 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l10 X0 (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h4928 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l11 x y]

@[equational_result]
theorem Equation2_implies_Equation4929 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4929 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (z ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation4929_implies_Equation2 (G : Type*) [Magma G] (h4929 : Equation4929 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h4929 X0 X2 X1 X1]
    conv => enter [1]; rw [← h4929 X2 X1 X0 (X1 ◇ (X1 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4929 X0 X0 X0 X1]
    conv => enter [1]; rw [← h4929 X0 X1 X0 (X0 ◇ X1)]
  have l2 : ∀ X2 X0 : G, (X2 ◇ X0) = X2 := by
    intro X2 X0
    conv => enter [1, 2]; rw [← l1 X2 X0]
    conv => enter [1]; rw [l0 X2 X2 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h4929 X1 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation4931 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4931 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (z ◇ (w ◇ y)))))]

theorem Equation4512_4931_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4931 : Equation4931 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 X3 X4 : G, ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X4 ◇ (X4 ◇ X0))) = X4 := by
    intro X0 X1 X2 X3 X4
    conv => enter [1, 2, 2, 2]; rw [h4931 X0 X3 X1 X2]
    conv => enter [1]; rw [← h4931 X4 (X0 ◇ (X1 ◇ (X2 ◇ X3))) X3 X0]
  have l1 : ∀ X1 X2 X3 X0 : G, ((X1 ◇ (X2 ◇ X3)) ◇ (X3 ◇ X0)) = X3 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2]; rw [h4931 X0 X3 X1 X2]
    conv => enter [1]; rw [← h4931 X3 (X1 ◇ (X2 ◇ X3)) X0 X0]
  have l2 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X2 ◇ X3) ◇ (X3 ◇ X0))) = X3 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ X3) (X3 ◇ X0)]
    conv => enter [1]; rw [l1 X1 X2 X3 X0]
  have l3 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X4 ◇ (X4 ◇ X0)))) = X4 := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ X3)) (X4 ◇ (X4 ◇ X0))]
    conv => enter [1]; rw [l0 X0 X1 X2 X3 X4]
  have l4 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))) = X3 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2]; rw [h4512 X2 X3 (X3 ◇ X0)]
    conv => enter [1]; rw [l2 X1 X2 X3 X0]
  have l5 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X4 ◇ (X4 ◇ X0))))) = X4 := by
    intro X0 X1 X2 X3 X4
    conv => enter [1, 2]; rw [h4512 X1 (X2 ◇ X3) (X4 ◇ (X4 ◇ X0))]
    conv => enter [1]; rw [l3 X0 X1 X2 X3 X4]
  have l6 : ∀ X0 X4 : G, (X0 ◇ X4) = X4 := by
    intro X0 X4
    conv => enter [1, 2]; rw [← l4 X0 (X0 ◇ X0) X4 X0]
    conv => enter [1]; rw [l5 X0 X0 X0 X0 X4]
  have l7 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X0 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2, 2]; rw [← l6 X0 (X1 ◇ (X2 ◇ X3))]
    conv => enter [1]; rw [← h4931 X0 X3 X1 X2]
  have l8 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ X3))) = X0 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l6 X3 (X0 ◇ (X1 ◇ (X2 ◇ X3)))]
    conv => enter [1]; rw [l7 X3 X0 X1 X2]
  have l9 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ X3)) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [← l6 X0 (X1 ◇ (X2 ◇ X3))]
    conv => enter [1]; rw [l8 X0 X1 X2 X3]
  have l10 : ∀ X2 X3 X0 : G, (X2 ◇ X3) = X0 := by
    intro X2 X3 X0
    conv => enter [1, 2]; rw [← l6 X2 X3]
    conv => enter [1]; rw [l9 X2 X2 X3 X0]
  have l11 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l10 X0 (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h4931 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l11 x y]

@[equational_result]
theorem Equation2_implies_Equation4932 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4932 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (z ◇ (w ◇ z)))))]

@[equational_result]
theorem Equation4932_implies_Equation2 (G : Type*) [Magma G] (h4932 : Equation4932 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ X0))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2]; rw [h4932 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1))) X1 X1]
    conv => enter [1]; rw [← h4932 X2 X1 (X0 ◇ (X1 ◇ (X1 ◇ X1))) X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4932 (X0 ◇ X1) X2 (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h4932 (X0 ◇ X1) (X0 ◇ X1) X1 X0]
  have l2 : ∀ X2 X0 : G, (X2 ◇ (X2 ◇ X0)) = X2 := by
    intro X2 X0
    conv => enter [1, 2]; rw [l1 X2 X0 X2]
    conv => enter [1]; rw [l0 X2 X2 X0]
  have l3 : ∀ X2 X0 : G, (X2 ◇ X0) = X2 := by
    intro X2 X0
    conv => enter [1]; rw [l1 X2 X0 X2]
    conv => enter [1]; rw [l2 X2 X0]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h4932 X1 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation2_implies_Equation4933 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4933 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (z ◇ (w ◇ w)))))]

@[equational_result]
theorem Equation4933_implies_Equation2 (G : Type*) [Magma G] (h4933 : Equation4933 G) : Equation2 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X1)))) = X3 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2]; rw [h4933 (X0 ◇ (X1 ◇ X1)) X3 X0 X1]
    conv => enter [1]; rw [← h4933 X3 X2 (X0 ◇ (X1 ◇ X1)) (X0 ◇ (X1 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4933 X0 X0 (X1 ◇ X1) X1]
    conv => enter [1]; rw [← h4933 X0 X1 X0 (X1 ◇ X1)]
  have l2 : ∀ X3 X0 X1 : G, (X3 ◇ (X0 ◇ (X1 ◇ X1))) = X3 := by
    intro X3 X0 X1
    conv => enter [1, 2]; rw [← l1 X3 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l0 X3 X3 X0 X1]
  have l3 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X1)) = X3 := by
    intro X0 X1 X3
    conv => enter [1]; rw [← l1 X3 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l2 X3 X0 X1]
  have l4 : ∀ X1 X3 : G, (X1 ◇ X1) = X3 := by
    intro X1 X3
    conv => enter [1, 2]; rw [← l1 X1 X1]
    conv => enter [1]; rw [l3 X1 X1 X3]
  have l5 : ∀ X1 X3 : G, X1 = X3 := by
    intro X1 X3
    conv => enter [1]; rw [← l1 X1 X1]
    conv => enter [1]; rw [l4 X1 X3]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation2_implies_Equation4934 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4934 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation4934_implies_Equation2 (G : Type*) [Magma G] (h4934 : Equation4934 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h4934 X0 X2 X1 X1 X1]
    conv => enter [1]; rw [← h4934 X2 X1 X0 X0 (X1 ◇ (X1 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4934 X0 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4934 X0 X1 X0 X1 (X1 ◇ X1)]
  have l2 : ∀ X2 X0 : G, (X2 ◇ X0) = X2 := by
    intro X2 X0
    conv => enter [1, 2]; rw [← l1 X2 X0]
    conv => enter [1]; rw [l0 X2 X2 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h4934 X1 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation4936 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4936 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (x ◇ (x ◇ y)))))]

theorem Equation4512_4936_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4936 : Equation4936 G) : Equation2 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2, 2]; rw [h4936 X0 X0]
    conv => enter [1]; rw [← h4936 X0 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X2)) = (X0 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) X2]
    conv => enter [1, 1]; rw [← h4936 X0 X1]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X0 ◇ (X0 ◇ X1))) X2]
  have l3 : ∀ X0 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)))) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ X0)) (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))]
    conv => enter [1]; rw [l0 X0]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X1)) X2]
  have l5 : ∀ X0 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4512 X0 (X0 ◇ X0) (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))]
    conv => enter [1]; rw [l3 X0]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l7 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0)))))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h4512 X0 X0 (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X0))]
    conv => enter [1]; rw [l5 X0]
  have l8 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l9 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))))))) = X0 := by
    intro X0
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X0 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [l7 X0]
  have l10 : ∀ X0 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [l8 X0 ((X0 ◇ (X0 ◇ X0)) ◇ X0) X0]
    conv => enter [1]; rw [l9 X0]
  have l11 : ∀ X0 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4512 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l10 X0]
  have l12 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h4512 X0 X0 X0]
    conv => enter [1]; rw [l11 X0]
  have l13 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l12 X0]
    conv => enter [1]; rw [← h4936 X0 X0]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l13 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l13 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l16 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4936 X0 X1]
    conv => enter [1]; rw [← l14 X1 (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))]
    conv => enter [1]; rw [← h4936 X0 X1]
  have l17 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [l14 X0 X1]
    conv => enter [1]; rw [← h4936 X0 X1]
  have l18 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l15 X0 X1]
    conv => enter [1]; rw [l17 X1 X0]
  have l19 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l16 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l18 X1 X0]
  have l20 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l19 X0 (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))]
    conv => enter [1]; rw [← h4936 X1 X0]
  intro x y
  conv => enter [1]; rw [l20 x y]

@[equational_result]
theorem Equation2_implies_Equation4937 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4937 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (x ◇ (x ◇ z)))))]

theorem Equation4512_4937_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4937 : Equation4937 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4937 X0 X2 X1]
    conv => enter [1]; rw [← h4937 X2 X1 (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1))))]
  have l1 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X3)) := by
    intro X0 X3 X1 X2
    conv => enter [1, 1]; rw [h4937 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) X3]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l1 X0 X3 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X0 ◇ (X0 ◇ X2))) X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X2)) X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X0 ◇ X2) X3]
  have l5 : ∀ X0 X3 : G, (X0 ◇ X3) = X0 := by
    intro X0 X3
    conv => enter [1]; rw [l4 X0 X3 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 ((X0 ◇ X0) ◇ X3)]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))]
    conv => enter [1]; rw [← h4937 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation2_implies_Equation4939 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4939 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (x ◇ (y ◇ y)))))]

theorem Equation4512_4939_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4939 : Equation4939 G) : Equation2 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4939 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h4939 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h4939 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0]
    conv => enter [1]; rw [l1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l3 X0]
    conv => enter [1]; rw [← h4939 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l5 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4939 X0 X1]
    conv => enter [1]; rw [l6 (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) X1]
  have l8 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l9 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l8 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l10 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X1 ◇ X1))) X0]
    conv => enter [1]; rw [l7 X0 X1]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l6 X0 (X1 ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1 X1]
    conv => enter [1]; rw [l11 X1 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l12 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l14 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l12 X0 X0]
    conv => enter [1]; rw [l13 X0 X1]
  intro x y
  conv => enter [1]; rw [l14 x y]

@[equational_result]
theorem Equation2_implies_Equation4940 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4940 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (x ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation4940_implies_Equation2 (G : Type*) [Magma G] (h4940 : Equation4940 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4940 X0 X1 X0]
    conv => enter [1]; rw [← h4940 X1 X0 (X1 ◇ X0)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l0 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation4942 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4942 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (x ◇ (z ◇ y)))))]

theorem Equation4512_4942_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4942 : Equation4942 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4942 (X0 ◇ X1) X1 X0]
    conv => enter [1]; rw [← h4942 X1 (X0 ◇ X1) (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [← l1 X0 X0]
    conv => enter [1]; rw [← h4942 X0 X0 X0]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X1 ◇ X0)) X2]
    conv => enter [1, 1]; rw [l1 X1 X0]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l3 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l6 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0]
    conv => enter [1]; rw [l1 X0 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l6 X0]
    conv => enter [1]; rw [← h4942 X1 X0 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0 X0]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation2_implies_Equation4943 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4943 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (x ◇ (z ◇ z)))))]

theorem Equation4512_4943_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4943 : Equation4943 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X3)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4943 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X3)))]
  have l1 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X3)))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X3 ◇ X3))))]
    conv => enter [1]; rw [← h4943 X0 (X1 ◇ X2) X3]
  have l2 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3))))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ X3))]
    conv => enter [1]; rw [l1 X1 X2 X0 X3]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X3))))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 (X3 ◇ X3)]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1 X0 X0]
    conv => enter [1]; rw [l2 X0 X0 X1 X0]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2)))) = X0 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l4 X1 (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X2))))]
    conv => enter [1]; rw [← h4943 X0 X1 X2]
  have l6 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ X2))) = X0 := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l4 X0 (X1 ◇ (X0 ◇ (X2 ◇ X2)))]
    conv => enter [1]; rw [l5 X0 X1 X2]
  have l7 : ∀ X0 X2 : G, (X0 ◇ (X2 ◇ X2)) = X0 := by
    intro X0 X2
    conv => enter [1, 2]; rw [← l4 X0 (X2 ◇ X2)]
    conv => enter [1]; rw [l6 X0 X0 X2]
  have l8 : ∀ X2 X0 : G, (X2 ◇ X2) = X0 := by
    intro X2 X0
    conv => enter [1]; rw [← l4 X0 (X2 ◇ X2)]
    conv => enter [1]; rw [l7 X0 X2]
  have l9 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l4 X0 X0]
    conv => enter [1]; rw [l8 X0 X2]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation2_implies_Equation4944 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4944 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (x ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation4944_implies_Equation2 (G : Type*) [Magma G] (h4944 : Equation4944 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4944 X0 X1 X0 X0]
    conv => enter [1]; rw [← h4944 X1 X0 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l0 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation4946 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4946 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (y ◇ (x ◇ y)))))]

theorem Equation4512_4946_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4946 : Equation4946 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4946 X0 X1]
    conv => enter [1]; rw [← h4946 X1 (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X2)) = (X0 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) X2]
    conv => enter [1, 1]; rw [← h4946 X0 X1]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ (X0 ◇ X1))) X2]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X1 ◇ (X0 ◇ X1))) (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))]
    conv => enter [1]; rw [l0 X0 X1]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ (X0 ◇ X1)) X2]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 (X1 ◇ (X0 ◇ X1)) (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))]
    conv => enter [1]; rw [l3 X0 X1]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X1 (X0 ◇ X1) (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))]
    conv => enter [1]; rw [l5 X0 X1]
  have l8 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))]
    conv => enter [1]; rw [l7 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 (X1 ◇ (X1 ◇ (X0 ◇ X1))) ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X1 (X1 ◇ (X0 ◇ X1)) ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l8 X0 ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)) X1]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 (X0 ◇ X1) ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)]
    conv => enter [1]; rw [l13 X0 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0)))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 (X1 ◇ (X1 ◇ (X0 ◇ X1))) X0]
    conv => enter [1]; rw [l14 X0 X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0))))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X1 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l15 X0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0)))))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l16 X0 X1]
  have l18 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l17 X0 X1]
  have l19 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2]; rw [l8 X0 X0 X1]
    conv => enter [1]; rw [l18 X0 X1]
  have l20 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4946 X0 X0]
    conv => enter [1]; rw [l19 X0 X0]
  have l21 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← l20 X0]
    conv => enter [1]; rw [l19 X0 X1]
  have l22 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l20 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l23 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l20 X0]
    conv => enter [1]; rw [l21 X0 X1]
  have l24 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l22 X1 X0]
    conv => enter [1]; rw [l23 X0 X1]
  have l25 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l24 X1 X0]
    conv => enter [1]; rw [← h4946 X0 X1]
  have l26 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l24 X0 X1]
    conv => enter [1]; rw [l25 X1 X0]
  have l27 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l26 X1 X0]
    conv => enter [1]; rw [l20 X1]
  intro x y
  conv => enter [1]; rw [l27 x y]

@[equational_result]
theorem Equation2_implies_Equation4947 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4947 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (y ◇ (x ◇ z)))))]

theorem Equation4512_4947_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4947 : Equation4947 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4947 X0 X2 X1]
    conv => enter [1]; rw [← h4947 X2 X1 (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))]
  have l1 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X3)) := by
    intro X0 X3 X1 X2
    conv => enter [1, 1]; rw [h4947 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) X3]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l1 X0 X3 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ (X0 ◇ X2))) X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ (X0 ◇ X2)) X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ X2) X3]
  have l5 : ∀ X0 X3 : G, (X0 ◇ X3) = X0 := by
    intro X0 X3
    conv => enter [1]; rw [l4 X0 X3 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 ((X0 ◇ X0) ◇ X3)]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))]
    conv => enter [1]; rw [← h4947 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation2_implies_Equation4950 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4950 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (y ◇ (y ◇ z)))))]

theorem Equation4512_4950_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4950 : Equation4950 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X1 ◇ X0)))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4950 X0 X1 X1]
    conv => enter [1]; rw [← h4950 X2 X1 (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X1))))]
  have l1 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) X3]
    conv => enter [1, 1]; rw [← h4950 X0 X1 X2]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l1 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ (X1 ◇ X2))) X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ (X1 ◇ X2)) X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X1 ◇ X2) X3]
  have l5 : ∀ X0 X3 : G, (X0 ◇ X3) = X0 := by
    intro X0 X3
    conv => enter [1]; rw [l4 X0 X3 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 ((X0 ◇ X0) ◇ X3)]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h4950 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation2_implies_Equation4952 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4952 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (y ◇ (z ◇ y)))))]

theorem Equation4512_4952_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4952 : Equation4952 G) : Equation2 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))))) = X3 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [← h4952 X3 X2 (X0 ◇ X1)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4952 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h4952 X1 X0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l3 X0 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ X0))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2]; rw [← l5 X1 X0]
    conv => enter [1]; rw [← h4952 X2 X1 X0]
  have l7 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2, 2]; rw [← l5 X1 X0]
    conv => enter [1]; rw [← h4952 X2 (X0 ◇ X1) X1]
  have l8 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [l5 X1 X0]
  have l9 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l8 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)))]
    conv => enter [1]; rw [l7 X0 X1 X2]
  have l11 : ∀ X0 X2 : G, (X0 ◇ X2) = X0 := by
    intro X0 X2
    conv => enter [1]; rw [l9 X0 X2 X0]
    conv => enter [1]; rw [l6 X0 X0 X2]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0)))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [l10 X0 X1 X2]
  have l13 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l11 X0 (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))))]
    conv => enter [1]; rw [l12 X0 X0 X2]
  intro x y
  conv => enter [1]; rw [l13 x y]

@[equational_result]
theorem Equation2_implies_Equation4953 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4953 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (y ◇ (z ◇ z)))))]

theorem Equation4512_4953_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4953 : Equation4953 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X3 X2 : G, ((X0 ◇ X1) ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = X3 := by
    intro X0 X1 X3 X2
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X2)]
    conv => enter [1]; rw [← h4953 X3 (X0 ◇ X1) X2]
  have l1 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := by
    intro X0 X2 X1
    conv => enter [1, 2, 2, 2]; rw [h4953 (X0 ◇ (X0 ◇ (X1 ◇ X1))) X0 X1]
    conv => enter [1]; rw [← h4953 X2 X0 (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X3)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4953 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ (X3 ◇ X3)))]
  have l3 : ∀ X2 X0 : G, (X2 ◇ X0) = X2 := by
    intro X2 X0
    conv => enter [1]; rw [l2 X2 X0 X0 X2]
    conv => enter [1]; rw [l1 X0 X2 X2]
  have l4 : ∀ X0 X1 X3 X2 : G, (X0 ◇ (X1 ◇ (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) = X3 := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4512 X0 X1 (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))]
    conv => enter [1]; rw [l0 X0 X1 X3 X2]
  have l5 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l3 X0 (X0 ◇ (X3 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))))]
    conv => enter [1]; rw [l4 X0 X0 X3 X0]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation2_implies_Equation4954 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4954 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (y ◇ (z ◇ w)))))]

theorem Equation4512_4954_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4954 : Equation4954 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ X0))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2]; rw [h4954 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4954 X2 X1 X0 (X1 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X3 ◇ X4)))))) = X2 := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X3 ◇ X4))))]
    conv => enter [1]; rw [← h4954 X2 (X0 ◇ X1) X3 X4]
  have l2 : ∀ X1 X0 X2 X3 X4 : G, (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X4)) = (X0 ◇ X4) := by
    intro X1 X0 X2 X3 X4
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) X4]
    conv => enter [1, 1]; rw [← h4954 X0 X1 X2 X3]
  have l3 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X1 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l2 X1 X0 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ (X2 ◇ X3))) X4]
  have l4 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X4))))))) = X2 := by
    intro X0 X1 X2 X3 X4
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ (X3 ◇ X4))]
    conv => enter [1]; rw [l1 X0 X1 X2 X3 X4]
  have l5 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l3 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ (X2 ◇ X3)) X4]
  have l6 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X4)))))))) = X2 := by
    intro X0 X1 X2 X3 X4
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 (X3 ◇ X4)]
    conv => enter [1]; rw [l4 X0 X1 X2 X3 X4]
  have l7 : ∀ X0 X4 : G, (X0 ◇ X4) = X0 := by
    intro X0 X4
    conv => enter [1]; rw [l5 X0 X4 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 ((X0 ◇ (X0 ◇ X0)) ◇ X4)]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X1))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [← l0 X0 X1 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l6 X0 X1 X2 X0 X0]
  have l9 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l7 X0 (X0 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l8 X0 X0 X2]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation2_implies_Equation4956 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4956 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (z ◇ (x ◇ y)))))]

theorem Equation4512_4956_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4956 : Equation4956 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2]; rw [h4956 X0 X1 X2]
    conv => enter [1]; rw [← h4956 X0 (X1 ◇ (X2 ◇ (X0 ◇ X1))) X1]
  have l1 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) X3]
    conv => enter [1, 1]; rw [← h4956 X0 X1 X2]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l1 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (X0 ◇ X1))) X3]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0)))) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ X1)) (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0))]
    conv => enter [1]; rw [l0 X1 X2 X0]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ (X0 ◇ X1)) X3]
  have l5 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0))))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X2 (X0 ◇ X1) (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0))]
    conv => enter [1]; rw [l3 X1 X2 X0]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l4 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (X0 ◇ X1) X3]
  have l7 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0)))))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0))]
    conv => enter [1]; rw [l5 X1 X2 X0]
  have l8 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l6 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X3]
  have l9 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0))))))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X1 (X2 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l7 X1 X2 X0]
  have l10 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0)))))))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X2 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l9 X1 X2 X0]
  have l11 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))))))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l10 X1 X2 X0]
  have l12 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2]; rw [l8 X0 X0 X1 X2]
    conv => enter [1]; rw [l11 X1 X2 X0]
  have l13 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l12 X0 X1 X0]
    conv => enter [1]; rw [← h4956 X1 (X0 ◇ (X0 ◇ X0)) X0]
  have l14 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l12 (X1 ◇ X2) X3 X0]
  have l15 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l12 X1 X1 X0]
    conv => enter [1]; rw [l14 X1 X1 X1 X0]
  have l16 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))]
    conv => enter [1]; rw [l13 X0 X1]
  have l17 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l15 X0 ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))]
    conv => enter [1]; rw [l16 X0 X1]
  have l18 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))]
    conv => enter [1]; rw [l17 X0 X1]
  have l19 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l15 X0 (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))]
    conv => enter [1]; rw [l18 X0 X1]
  have l20 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l15 X0 (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))]
    conv => enter [1]; rw [l19 X0 X1]
  have l21 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l15 X1 ((X0 ◇ (X0 ◇ X0)) ◇ X0)]
    conv => enter [1]; rw [l20 X1 X0]
  have l22 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l21 X0 X1]
  have l23 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l15 X0 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [l22 X0 X1]
  have l24 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 X0]
    conv => enter [1]; rw [l23 X0 X1]
  have l25 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l15 X0 X0]
    conv => enter [1]; rw [l24 X0 X1]
  have l26 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l15 X0 X0]
    conv => enter [1]; rw [l25 X0 X1]
  intro x y
  conv => enter [1]; rw [l26 x y]

@[equational_result]
theorem Equation2_implies_Equation4957 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4957 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (z ◇ (x ◇ z)))))]

theorem Equation4512_4957_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4957 : Equation4957 G) : Equation2 G := by
  have l0 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))))) = X2 := by
    intro X3 X2 X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h4957 X2 X3 (X0 ◇ X1)]
  have l1 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X3)) := by
    intro X0 X3 X1 X2
    conv => enter [1, 1]; rw [h4957 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X2)))) X3]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l1 X0 X3 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (X0 ◇ X2))) X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ (X0 ◇ X2)) X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (X0 ◇ X2) X3]
  have l5 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l4 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X2 X3]
  have l6 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X0)))) = X0 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2]; rw [h4957 X0 (X2 ◇ (X0 ◇ X2)) X2]
    conv => enter [1]; rw [l0 X1 X0 (X2 ◇ (X0 ◇ X2)) (X2 ◇ (X0 ◇ X2))]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4957 X0 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X0 X1]
  have l8 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X2) ◇ X0))))) = X0 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [h4512 X2 (X0 ◇ X2) X0]
    conv => enter [1]; rw [l6 X1 X0 X2]
  have l9 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0)))))) = X0 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X2 X0]
    conv => enter [1]; rw [l8 X1 X0 X2]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l5 X0 X0 X0 X0]
    conv => enter [1]; rw [l9 X0 X0 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l10 X0]
    conv => enter [1]; rw [← h4957 X0 X1 X0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l10 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l10 X0]
    conv => enter [1]; rw [l11 X1 X0]
  have l15 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l13 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l14 X0 X1]
  intro x y
  conv => enter [1]; rw [l15 x y]

@[equational_result]
theorem Equation2_implies_Equation4958 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4958 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (z ◇ (x ◇ w)))))]

@[equational_result]
theorem Equation4958_implies_Equation2 (G : Type*) [Magma G] (h4958 : Equation4958 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4958 X0 X1 X1 X0]
    conv => enter [1]; rw [← h4958 X1 X0 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l0 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation4960 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4960 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (z ◇ (y ◇ y)))))]

theorem Equation4512_4960_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4960 : Equation4960 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [h4960 (X0 ◇ (X1 ◇ (X0 ◇ X0))) X0 X1]
    conv => enter [1]; rw [← h4960 X2 (X0 ◇ (X1 ◇ (X0 ◇ X0))) X0]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X2)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4960 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ (X2 ◇ X2)))]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ X0)) (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 (X0 ◇ X0) (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))]
    conv => enter [1]; rw [l2 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X0 X0 (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))]
    conv => enter [1]; rw [l3 X0 X1 X2]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [l1 X2 (X0 ◇ (X1 ◇ (X0 ◇ X0))) X0 X1]
    conv => enter [1]; rw [l4 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4960 X2 X0 X1]
    conv => enter [1]; rw [l5 X0 X1 X2]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [← l6 X2 X1 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [← h4960 X2 X1 X0]
  have l8 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ X0)]
    conv => enter [1]; rw [l6 (X1 ◇ X2) X3 X0]
  have l9 : ∀ X3 X0 : G, (X3 ◇ X0) = X0 := by
    intro X3 X0
    conv => enter [1, 2]; rw [← l6 X3 X3 X0]
    conv => enter [1]; rw [l8 X3 X3 X3 X0]
  have l10 : ∀ X1 X2 : G, (X1 ◇ X1) = X2 := by
    intro X1 X2
    conv => enter [1, 2]; rw [← l6 X1 X1 X1]
    conv => enter [1]; rw [l7 X1 X1 X2]
  have l11 : ∀ X1 X2 : G, X1 = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l9 X1 X1]
    conv => enter [1]; rw [l10 X1 X2]
  intro x y
  conv => enter [1]; rw [l11 x y]

@[equational_result]
theorem Equation2_implies_Equation4961 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4961 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (z ◇ (y ◇ z)))))]

theorem Equation4512_4961_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4961 : Equation4961 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X3 ◇ (X1 ◇ X3)))) ◇ X0)))) = X2 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4961 X0 X1 X3]
    conv => enter [1]; rw [← h4961 X2 X1 (X0 ◇ (X1 ◇ (X3 ◇ (X1 ◇ X3))))]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h4961 (X0 ◇ (X1 ◇ X0)) X1 X0]
    conv => enter [1]; rw [← h4961 X2 X1 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))) X3]
    conv => enter [1, 1]; rw [← h4961 X0 X1 X2]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l2 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (X1 ◇ X2))) X3]
  have l4 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X3 ◇ (X1 ◇ X3))) ◇ X0))))) = X2 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 (X1 ◇ (X3 ◇ (X1 ◇ X3))) X0]
    conv => enter [1]; rw [l0 X1 X2 X0 X3]
  have l5 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ (X1 ◇ X2)) X3]
  have l6 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X3 ◇ (X1 ◇ X3)) ◇ X0)))))) = X2 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X1 (X3 ◇ (X1 ◇ X3)) X0]
    conv => enter [1]; rw [l4 X1 X2 X0 X3]
  have l7 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l5 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (X1 ◇ X2) X3]
  have l8 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ ((X1 ◇ X3) ◇ X0))))))) = X2 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X3 (X1 ◇ X3) X0]
    conv => enter [1]; rw [l6 X1 X2 X0 X3]
  have l9 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l7 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l10 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X1 ◇ (X3 ◇ X0)))))))) = X2 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X1 X3 X0]
    conv => enter [1]; rw [l8 X1 X2 X0 X3]
  have l11 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [l9 X0 X0 X1 X1]
    conv => enter [1]; rw [l10 X1 X2 X0 X1]
  have l12 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X3)))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ X3))]
    conv => enter [1]; rw [l11 (X1 ◇ X2) X0 X3]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l11 X1 X0 X1]
    conv => enter [1]; rw [l12 X1 X1 X0 X1]
  have l14 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [← l13 X2 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [← h4961 X2 X0 X1]
  have l15 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l1 X0 X0 X0]
    conv => enter [1]; rw [l14 X0 X0 X2]
  intro x y
  conv => enter [1]; rw [l15 x y]

@[equational_result]
theorem Equation2_implies_Equation4962 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4962 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (z ◇ (y ◇ w)))))]

theorem Equation4512_4962_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4962 : Equation4962 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h4962 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4962 X2 X1 X0 (X1 ◇ (X1 ◇ X1))]
  have l1 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X4)))))) = X0 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ ((X1 ◇ X2) ◇ X4))))]
    conv => enter [1]; rw [← h4962 X0 (X1 ◇ X2) X3 X4]
  have l2 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X4))))))) = X0 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 X2 (X3 ◇ ((X1 ◇ X2) ◇ X4))]
    conv => enter [1]; rw [l1 X1 X2 X0 X3 X4]
  have l3 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0 (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0)))))]
    conv => enter [1]; rw [l2 X0 X0 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation4964 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4964 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (z ◇ (z ◇ y)))))]

theorem Equation4512_4964_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4964 : Equation4964 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [h4964 X0 X0 X1]
    conv => enter [1]; rw [← h4964 X2 (X0 ◇ (X1 ◇ (X1 ◇ X0))) X0]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4964 (X0 ◇ X0) X0 X0]
    conv => enter [1]; rw [← h4964 X0 (X0 ◇ X0) X0]
  have l2 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) X3]
    conv => enter [1, 1]; rw [← h4964 X0 X1 X2]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l2 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (X2 ◇ X1))) X3]
  have l4 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l1 X0]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X1 ◇ X0)) (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0))]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ (X2 ◇ X1)) X3]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 (X1 ◇ X0) (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0))]
    conv => enter [1]; rw [l5 X0 X1 X2]
  have l8 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l6 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (X2 ◇ X1) X3]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0)))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X1 X0 (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X0))) ◇ X0))]
    conv => enter [1]; rw [l7 X0 X1 X2]
  have l10 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l8 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X2 X1 X3]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X0 (X1 ◇ (X1 ◇ X0)) X0]
    conv => enter [1]; rw [l9 X0 X1 X2]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0)))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X1 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l11 X0 X1 X2]
  have l13 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0))))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X1 X0 X0]
    conv => enter [1]; rw [l12 X0 X1 X2]
  have l14 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [l10 X2 X0 X0 X1]
    conv => enter [1]; rw [l13 X0 X1 X2]
  have l15 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l4 X0]
    conv => enter [1]; rw [← h4964 X1 (X0 ◇ (X0 ◇ X0)) X0]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X1]
    conv => enter [1, 2]; rw [l14 X1 (X0 ◇ X1) X0]
  have l18 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l15 X0 X1]
  have l19 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l17 X0 ((X0 ◇ X0) ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [l18 X0 X1]
  have l20 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l19 X0 X0]
    conv => enter [1]; rw [l19 X0 X2]
  intro x y
  conv => enter [1]; rw [l20 x y]

@[equational_result]
theorem Equation2_implies_Equation4965 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4965 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (z ◇ (z ◇ z)))))]

theorem Equation4512_4965_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4965 : Equation4965 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4965 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ (X3 ◇ X3)))]
  have l1 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X3)))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X3))))]
    conv => enter [1]; rw [← h4965 X0 (X1 ◇ X2) X3]
  have l2 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X3))))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 X2 (X3 ◇ (X3 ◇ X3))]
    conv => enter [1]; rw [l1 X1 X2 X0 X3]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X0 X1 X1 X1]
    conv => enter [1]; rw [l2 X1 X1 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 (X1 ◇ (X1 ◇ X1)) X0]
    conv => enter [1]; rw [← h4965 (X1 ◇ (X1 ◇ X1)) X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l3 X1 X1]
  have l6 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l5 X0 X0]
    conv => enter [1]; rw [l5 X0 X2]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation2_implies_Equation4966 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4966 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (z ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation4966_implies_Equation2 (G : Type*) [Magma G] (h4966 : Equation4966 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4966 X0 X1 X1 X0]
    conv => enter [1]; rw [← h4966 X1 X0 X1 (X1 ◇ X0)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l0 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation4968 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4968 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (z ◇ (w ◇ y)))))]

theorem Equation4512_4968_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4968 : Equation4968 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 X3 X4 X5 : G, ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ (X5 ◇ X0)))) = X4 := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1, 2, 2, 2, 2]; rw [h4968 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4968 X4 (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) X5 X1]
  have l1 : ∀ X1 X2 X3 X4 X0 : G, ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X0))) = X4 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2, 2]; rw [h4968 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4968 X4 (X1 ◇ (X2 ◇ (X3 ◇ X1))) X1 X0]
  have l2 : ∀ X1 X0 X2 X3 X4 : G, (X1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ X4)) = (X0 ◇ X4) := by
    intro X1 X0 X2 X3 X4
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) X4]
    conv => enter [1, 1]; rw [← h4968 X0 X1 X2 X3]
  have l3 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X1 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l2 X1 X0 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (X3 ◇ X1))) X4]
  have l4 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X0)))) = X4 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X3 ◇ X1)) (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X0))]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X0]
  have l5 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ (X5 ◇ X0))))) = X4 := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ (X3 ◇ X1))) (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ (X5 ◇ X0)))]
    conv => enter [1]; rw [l0 X0 X1 X2 X3 X4 X5]
  have l6 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X1 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l3 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ (X3 ◇ X1)) X4]
  have l7 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X0))))) = X4 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2]; rw [h4512 X2 (X3 ◇ X1) (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X0))]
    conv => enter [1]; rw [l4 X1 X2 X3 X4 X0]
  have l8 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ (X5 ◇ X0)))))) = X4 := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1, 2]; rw [h4512 X1 (X2 ◇ (X3 ◇ X1)) (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ (X5 ◇ X0)))]
    conv => enter [1]; rw [l5 X0 X1 X2 X3 X4 X5]
  have l9 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X4))))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l6 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (X3 ◇ X1) X4]
  have l10 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X0)))))) = X4 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2]; rw [h4512 X3 X1 (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X0))]
    conv => enter [1]; rw [l7 X1 X2 X3 X4 X0]
  have l11 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ (X5 ◇ X0))))))) = X4 := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1, 2, 2]; rw [h4512 X2 (X3 ◇ X1) (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ (X5 ◇ X0)))]
    conv => enter [1]; rw [l8 X0 X1 X2 X3 X4 X5]
  have l12 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X4)))))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l9 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X3 X1 X4]
  have l13 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X4 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X0))))))) = X4 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X1 (X2 ◇ (X3 ◇ X1)) X0]
    conv => enter [1]; rw [l10 X1 X2 X3 X4 X0]
  have l14 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ (X5 ◇ X0)))))))) = X4 := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1, 2, 2, 2]; rw [h4512 X3 X1 (X4 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ (X5 ◇ X0)))]
    conv => enter [1]; rw [l11 X0 X1 X2 X3 X4 X5]
  have l15 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X4 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ X0)))))))) = X4 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X2 (X3 ◇ X1) X0]
    conv => enter [1]; rw [l13 X1 X2 X3 X4 X0]
  have l16 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X4 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ (X5 ◇ X0))))))))) = X4 := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 (X1 ◇ (X2 ◇ (X3 ◇ X1))) (X5 ◇ X0)]
    conv => enter [1]; rw [l14 X0 X1 X2 X3 X4 X5]
  have l17 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X4 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X0))))))))) = X4 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X3 X1 X0]
    conv => enter [1]; rw [l15 X1 X2 X3 X4 X0]
  have l18 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X4 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ (X5 ◇ X0)))))))))) = X4 := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X1 (X2 ◇ (X3 ◇ X1)) (X5 ◇ X0)]
    conv => enter [1]; rw [l16 X0 X1 X2 X3 X4 X5]
  have l19 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X0)))) = X4 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2, 2]; rw [l12 X4 X0 X1 X2 X3]
    conv => enter [1]; rw [l17 X1 X2 X3 X4 X0]
  have l20 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ X1) ◇ (X5 ◇ X0))))))))))) = X4 := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X2 (X3 ◇ X1) (X5 ◇ X0)]
    conv => enter [1]; rw [l18 X0 X1 X2 X3 X4 X5]
  have l21 : ∀ X3 X4 : G, X3 = X4 := by
    intro X3 X4
    conv => enter [1]; rw [← l19 X3 X3 X3 X3 (X3 ◇ (X4 ◇ (X3 ◇ (X3 ◇ (X3 ◇ ((X3 ◇ X3) ◇ (X3 ◇ X3)))))))]
    conv => enter [1]; rw [l20 X3 X3 X3 X3 X4 X3]
  intro x y
  conv => enter [1]; rw [l21 x y]

@[equational_result]
theorem Equation2_implies_Equation4969 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4969 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (z ◇ (w ◇ z)))))]

@[equational_result]
theorem Equation4969_implies_Equation2 (G : Type*) [Magma G] (h4969 : Equation4969 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = (X0 ◇ X0) := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4969 (X1 ◇ X2) X0 (X1 ◇ X2) X2]
    conv => enter [1, 2]; rw [← h4969 X0 (X1 ◇ X2) X2 X1]
  have l1 : ∀ X0 X2 : G, (X0 ◇ X0) = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h4969 X2 X0 X0 X0]
  have l2 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l1 X0 X2]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation4970 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4970 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (z ◇ (w ◇ w)))))]

@[equational_result]
theorem Equation4970_implies_Equation2 (G : Type*) [Magma G] (h4970 : Equation4970 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4970 X0 X1 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h4970 X1 X0 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l0 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation4971 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4971 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation4971_implies_Equation2 (G : Type*) [Magma G] (h4971 : Equation4971 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4971 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [← h4971 X1 X0 X1 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l0 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation4973 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4973 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (x ◇ (x ◇ y)))))]

theorem Equation4512_4973_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4973 : Equation4973 G) : Equation2 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4973 X0 X0 X0]
    conv => enter [1]; rw [← h4973 X0 (X0 ◇ X0) X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 X0 X0]
    conv => enter [1]; rw [l0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h4973 X0 X0 X1]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) X2]
    conv => enter [1, 2, 2]; rw [← h4973 X0 X2 X1]
  have l4 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))) = X0 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h4973 X0 (X1 ◇ X0) X2]
  have l5 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 X0 (X0 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l4 X1 X0 X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ (X0 ◇ X2))) ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0)]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l5 X1 X0 X1]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X2)) ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0)]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0)))]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = ((X0 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1 X2]
    conv => enter [1]; rw [l7 X1 ((X0 ◇ (X0 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0))]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = (X0 ◇ ((X0 ◇ X2) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l10 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X2) ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0)]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = ((X0 ◇ X2) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l11 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 ((X0 ◇ X2) ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0))]
  have l13 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = (X0 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l12 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X2 ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0)]
  have l14 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l13 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 (X2 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0))]
  have l15 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l14 X0 X1 X2]
    conv => enter [1]; rw [l7 X2 ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0)]
  have l16 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l15 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ (X0 ◇ X2))) X0]
  have l17 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l16 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0)]
  have l18 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l17 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X2)) X0]
  have l19 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = ((X0 ◇ (X0 ◇ X2)) ◇ X0) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l18 X0 X1 X2]
    conv => enter [1]; rw [l7 X1 ((X0 ◇ (X0 ◇ X2)) ◇ X0)]
  have l20 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = (X0 ◇ ((X0 ◇ X2) ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l19 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X2) X0]
  have l21 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = ((X0 ◇ X2) ◇ X0) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l20 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 ((X0 ◇ X2) ◇ X0)]
  have l22 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = (X0 ◇ (X2 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l21 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 X2 X0]
  have l23 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = (X2 ◇ X0) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l22 X0 X1 X2]
    conv => enter [1]; rw [l7 X0 (X2 ◇ X0)]
  have l24 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := by
    intro X0 X1 X2
    conv => enter [1]; rw [l23 X0 X1 X2]
    conv => enter [1]; rw [l7 X2 X0]
  have l25 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ X2))) = X0 := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l7 X0 (X1 ◇ (X0 ◇ (X0 ◇ X2)))]
    conv => enter [1]; rw [l24 X0 X1 X2]
  have l26 : ∀ X0 X2 : G, (X0 ◇ (X0 ◇ X2)) = X0 := by
    intro X0 X2
    conv => enter [1, 2, 2]; rw [← l7 X0 X2]
    conv => enter [1]; rw [l25 X0 X0 X2]
  have l27 : ∀ X0 X2 : G, (X0 ◇ X2) = X0 := by
    intro X0 X2
    conv => enter [1, 2]; rw [← l7 X0 X2]
    conv => enter [1]; rw [l26 X0 X2]
  have l28 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l27 X0 (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))]
    conv => enter [1]; rw [← h4973 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l28 x y]

@[equational_result]
theorem Equation2_implies_Equation4974 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4974 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (x ◇ (x ◇ z)))))]

theorem Equation4512_4974_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4974 : Equation4974 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X3 X2 : G, (X0 ◇ X1) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4974 (X0 ◇ X1) X3 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)))]
  have l1 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X3)))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X3))))]
    conv => enter [1]; rw [← h4974 X0 (X1 ◇ X2) X3]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4974 X0 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X0 X1]
  have l3 : ∀ X0 X1 X3 X2 : G, (X0 ◇ X1) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l0 X0 X1 X3 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ X2)]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X0 X2]
    conv => enter [1, 2]; rw [l2 X0 (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))))]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))))]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1]; rw [l2 X1 (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))))]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2]
    conv => enter [1]; rw [l2 X2 (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l7 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 (X1 ◇ ((X0 ◇ X1) ◇ X2))]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1]; rw [l2 X1 ((X0 ◇ X1) ◇ X2)]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [l9 X0 X1 X2]
    conv => enter [1]; rw [l2 (X0 ◇ X1) X2]
  have l11 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l10 X0 (X2 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) X0]
    conv => enter [1]; rw [← h4974 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l11 x y]

@[equational_result]
theorem Equation2_implies_Equation4975 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4975 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (x ◇ (x ◇ w)))))]

@[equational_result]
theorem Equation4975_implies_Equation2 (G : Type*) [Magma G] (h4975 : Equation4975 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X0)))) = X2 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4975 X0 X2 X1 X1]
    conv => enter [1]; rw [← h4975 X2 X1 X3 (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4975 X0 X0 X0 X1]
    conv => enter [1]; rw [← h4975 X0 X1 X0 (X0 ◇ X1)]
  have l2 : ∀ X2 X3 X0 : G, (X2 ◇ (X3 ◇ (X2 ◇ X0))) = X2 := by
    intro X2 X3 X0
    conv => enter [1, 2]; rw [← l1 X2 (X3 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l0 X2 X2 X3 X0]
  have l3 : ∀ X3 X2 X0 : G, (X3 ◇ (X2 ◇ X0)) = X2 := by
    intro X3 X2 X0
    conv => enter [1]; rw [← l1 X2 (X3 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l2 X2 X3 X0]
  have l4 : ∀ X2 X0 : G, (X2 ◇ X0) = X2 := by
    intro X2 X0
    conv => enter [1, 2]; rw [← l1 X2 X0]
    conv => enter [1]; rw [l3 X2 X2 X0]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))]
    conv => enter [1]; rw [← h4975 X1 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation2_implies_Equation4977 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4977 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (x ◇ (y ◇ y)))))]

theorem Equation4512_4977_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4977 : Equation4977 G) : Equation2 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4977 (X0 ◇ X0) X0 X0]
    conv => enter [1]; rw [← h4977 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h4977 X0 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0]
    conv => enter [1]; rw [l1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l3 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [← h4977 X0 X1 (X0 ◇ (X1 ◇ X1))]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l3 X1]
    conv => enter [1]; rw [l5 X1 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l4 X0 X1]
    conv => enter [1]; rw [l6 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l7 (X1 ◇ X1) X0]
    conv => enter [1]; rw [← h4977 X0 X1 (X1 ◇ X1)]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X0]
    conv => enter [1]; rw [l8 X1 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l9 X1 X0]
    conv => enter [1]; rw [l7 X0 X1]
  have l11 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X0 X0]
    conv => enter [1]; rw [l10 X0 X1]
  intro x y
  conv => enter [1]; rw [l11 x y]

@[equational_result]
theorem Equation2_implies_Equation4978 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4978 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (x ◇ (y ◇ z)))))]

theorem Equation4512_4978_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4978 : Equation4978 G) : Equation2 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4978 (X0 ◇ X0) X0 X0]
    conv => enter [1]; rw [← h4978 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h4978 X0 X0 (X0 ◇ X0)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h4978 X1 X0 (X0 ◇ (X0 ◇ X0))]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 (X0 ◇ X0) (X1 ◇ X0)]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h4512 X0 X0 X0]
    conv => enter [1]; rw [l2 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [l5 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4978 X0 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X1 X0]
    conv => enter [1]; rw [l7 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation2_implies_Equation4979 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4979 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (x ◇ (y ◇ w)))))]

@[equational_result]
theorem Equation4979_implies_Equation2 (G : Type*) [Magma G] (h4979 : Equation4979 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4979 X0 X1 X1 X0]
    conv => enter [1]; rw [← h4979 X1 X0 X0 (X1 ◇ X0)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l0 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation4981 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4981 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (x ◇ (z ◇ y)))))]

theorem Equation4512_4981_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4981 : Equation4981 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X0 ◇ X0))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [h4981 X0 X2 X1]
    conv => enter [1]; rw [← h4981 X2 (X1 ◇ (X0 ◇ (X1 ◇ X2))) X0]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4981 X0 X1 X1]
    conv => enter [1]; rw [← h4981 X0 (X0 ◇ (X1 ◇ X1)) X1]
  have l2 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4981 X0 X1 X1]
    conv => enter [1]; rw [← h4981 X1 (X1 ◇ X1) X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X1 X0]
    conv => enter [1]; rw [l2 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) (X0 ◇ X0)]
    conv => enter [1]; rw [l1 X0 X1]
  have l5 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X0 ◇ X0)))) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X1 ◇ X2)) (X2 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l0 X1 X0 X2]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X2 ◇ (X0 ◇ X0))))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ X2) (X2 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l5 X1 X0 X2]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [l6 X0 X1]
  have l9 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [h4512 X1 X2 (X2 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l7 X1 X0 X2]
  have l10 : ∀ X1 X2 : G, X1 = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l8 X1 (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X1)))))]
    conv => enter [1]; rw [l9 X1 X1 X2]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation2_implies_Equation4982 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4982 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (x ◇ (z ◇ z)))))]

theorem Equation4512_4982_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4982 : Equation4982 G) : Equation2 G := by
  have l0 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))))) = X2 := by
    intro X3 X2 X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [← h4982 X2 X3 (X0 ◇ X1)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4982 (X0 ◇ X0) X0 X0]
    conv => enter [1]; rw [← h4982 X0 X1 (X0 ◇ X0)]
  have l2 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X3)))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X3))))]
    conv => enter [1]; rw [← h4982 X0 (X1 ◇ X2) X3]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4982 X0 X1 X1]
    conv => enter [1]; rw [l2 X1 X1 X0 X1]
  have l4 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = X2 := by
    intro X3 X2 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l1 X2 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X3 X2 X0 X1]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← l3 X2 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l4 X2 X2 X0 X1]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l3 X2 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l5 X2 X0 X1]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X1)) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l3 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l6 X0 X1 X2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l3 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l7 X1 X0 X2]
  have l9 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l8 X0 (X2 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h4982 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation2_implies_Equation4983 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4983 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (x ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation4983_implies_Equation2 (G : Type*) [Magma G] (h4983 : Equation4983 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4983 X0 X2 X2 X1]
    conv => enter [1]; rw [← h4983 X2 X1 X0 (X2 ◇ X1)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 (X2 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h4983 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation4985 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4985 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (x ◇ (w ◇ y)))))]

@[equational_result]
theorem Equation4985_implies_Equation2 (G : Type*) [Magma G] (h4985 : Equation4985 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, ((X1 ◇ X2) ◇ X0) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4985 X0 X2 X2 X1]
    conv => enter [1]; rw [← h4985 X2 (X1 ◇ X2) X0 X0]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0 (X2 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))))]
    conv => enter [1]; rw [← h4985 X2 (X0 ◇ X0) X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation4986 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4986 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (x ◇ (w ◇ z)))))]

theorem Equation4512_4986_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4986 : Equation4986 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ (X4 ◇ X3))) ◇ X0))) = X2 := by
    intro X1 X2 X3 X0 X4
    conv => enter [1, 2, 2, 2]; rw [h4986 X0 X2 X3 X4]
    conv => enter [1]; rw [← h4986 X2 X1 (X3 ◇ (X0 ◇ (X4 ◇ X3))) X0]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4986 (X0 ◇ X1) X1 X1 X0]
    conv => enter [1]; rw [← h4986 X1 X2 (X0 ◇ X1) (X0 ◇ X1)]
  have l2 : ∀ X3 X0 X4 X2 : G, ((X3 ◇ (X0 ◇ (X4 ◇ X3))) ◇ X0) = X2 := by
    intro X3 X0 X4 X2
    conv => enter [1]; rw [← l1 X3 X2 ((X3 ◇ (X0 ◇ (X4 ◇ X3))) ◇ X0)]
    conv => enter [1]; rw [l0 X3 X2 X3 X0 X4]
  have l3 : ∀ X3 X0 X4 X2 : G, (X3 ◇ ((X0 ◇ (X4 ◇ X3)) ◇ X0)) = X2 := by
    intro X3 X0 X4 X2
    conv => enter [1]; rw [h4512 X3 (X0 ◇ (X4 ◇ X3)) X0]
    conv => enter [1]; rw [l2 X3 X0 X4 X2]
  have l4 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l1 X0 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [l3 X0 X0 X0 X2]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation2_implies_Equation4987 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4987 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (x ◇ (w ◇ w)))))]

@[equational_result]
theorem Equation4987_implies_Equation2 (G : Type*) [Magma G] (h4987 : Equation4987 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4987 (X0 ◇ X0) X2 X2 X0]
    conv => enter [1]; rw [← h4987 X2 X1 (X0 ◇ X0) (X0 ◇ X0)]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X3]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation4988 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4988 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (x ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation4988_implies_Equation2 (G : Type*) [Magma G] (h4988 : Equation4988 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4988 X0 X2 X2 X1 X1]
    conv => enter [1]; rw [← h4988 X2 X1 X0 X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 (X2 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h4988 X2 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation4990 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4990 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (y ◇ (x ◇ y)))))]

theorem Equation4512_4990_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4990 : Equation4990 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4990 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4990 X1 (X0 ◇ X1) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ X0))) = X0 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h4990 X0 X1 X2]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [← l1 X0 X2]
    conv => enter [1]; rw [l2 X1 X0 X2]
  have l4 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l3 X0 (X2 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0)))) X0]
    conv => enter [1]; rw [← h4990 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation2_implies_Equation4991 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4991 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (y ◇ (x ◇ z)))))]

theorem Equation4512_4991_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4991 : Equation4991 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0))) = X0 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [h4991 X0 X1 X2]
    conv => enter [1]; rw [← h4991 X0 X1 (X2 ◇ (X1 ◇ (X0 ◇ X2)))]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1))))))) = X3 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [← h4991 X3 X2 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 X3 X2 : G, (X0 ◇ X1) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2)))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h4991 (X0 ◇ X1) X3 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X2)))]
  have l3 : ∀ X0 X1 X3 X2 : G, (X0 ◇ X1) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l2 X0 X1 X3 X2]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)))) = X0 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [h4512 X2 (X1 ◇ (X0 ◇ X2)) X0]
    conv => enter [1]; rw [l0 X1 X0 X2]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1 X0 X0]
    conv => enter [1]; rw [l1 X0 X0 X1 X0]
  have l6 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0))))) = X0 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 (X0 ◇ X2) X0]
    conv => enter [1]; rw [l4 X1 X0 X2]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X1))))]
    conv => enter [1]; rw [l6 X0 X1 X0]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation2_implies_Equation4992 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4992 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (y ◇ (x ◇ w)))))]

@[equational_result]
theorem Equation4992_implies_Equation2 (G : Type*) [Magma G] (h4992 : Equation4992 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4992 X0 X2 X1 X1]
    conv => enter [1]; rw [← h4992 X2 X1 X0 (X0 ◇ X1)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 (X2 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0)))) X0]
    conv => enter [1]; rw [← h4992 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation4994 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4994 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (y ◇ (y ◇ y)))))]

theorem Equation4512_4994_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4994 : Equation4994 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4994 (X0 ◇ (X0 ◇ X0)) X0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← h4994 X1 (X0 ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) (X1 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4994 (X0 ◇ X0) X0 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l2 X0 X0]
    conv => enter [1]; rw [l2 X0 X2]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation4995 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4995 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (y ◇ (y ◇ z)))))]

theorem Equation4512_4995_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4995 : Equation4995 G) : Equation2 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4995 (X0 ◇ X0) X0 X0]
    conv => enter [1]; rw [← h4995 X0 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h4995 X1 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [l1 X0 X0]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X1 ◇ X1)) X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 X2]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l2 X0]
    conv => enter [1]; rw [← h4995 X1 X0 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l5 X1 X0 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l8 x y]

@[equational_result]
theorem Equation2_implies_Equation4996 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4996 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (y ◇ (y ◇ w)))))]

@[equational_result]
theorem Equation4996_implies_Equation2 (G : Type*) [Magma G] (h4996 : Equation4996 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4996 X0 X0 X0 X0]
    conv => enter [1]; rw [← h4996 X1 X0 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4996 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4996 X1 X1 X0 (X1 ◇ X1)]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation4998 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4998 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (y ◇ (z ◇ y)))))]

theorem Equation4512_4998_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4998 : Equation4998 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4998 (X0 ◇ (X0 ◇ X0)) X0 X0]
    conv => enter [1]; rw [← h4998 X1 (X0 ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) (X1 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X0 (X1 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2))))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X2 (X0 ◇ X1)]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ X2))]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4998 X0 X0 X0]
    conv => enter [1]; rw [l2 X0 X0]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X2]
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [l4 X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [l4 X2]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l4 X0]
    conv => enter [1]; rw [← h4998 X1 X0 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← l4 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0 X0]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l8 X0 X0]
    conv => enter [1]; rw [l7 X0 X1]
  have l12 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l10 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l11 X0 X1]
  intro x y
  conv => enter [1]; rw [l12 x y]

@[equational_result]
theorem Equation2_implies_Equation4999 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4999 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (y ◇ (z ◇ z)))))]

theorem Equation4512_4999_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4999 : Equation4999 G) : Equation2 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h4999 (X0 ◇ X0) X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h4999 (X0 ◇ X0) (X0 ◇ X0) X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [l0 X0]
    conv => enter [1]; rw [← h4999 X1 X0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l0 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4999 (X0 ◇ (X1 ◇ (X0 ◇ X0))) X1 X0]
    conv => enter [1]; rw [l2 (X0 ◇ (X1 ◇ (X0 ◇ X0))) X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [← h4999 X1 X0 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ X0)) (X0 ◇ (X1 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l3 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 (X0 ◇ X0) (X0 ◇ (X1 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l5 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4999 (X0 ◇ X0) X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 X0]
    conv => enter [1]; rw [l7 X0 X1]
  intro x y
  conv => enter [1]; rw [l8 x y]

@[equational_result]
theorem Equation2_implies_Equation5000 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5000 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5000_implies_Equation2 (G : Type*) [Magma G] (h5000 : Equation5000 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h5000 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5000 X1 X0 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5000 X0 X0 X1 X1]
    conv => enter [1]; rw [← h5000 X0 X1 X0 (X1 ◇ X1)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l1 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5000 X1 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation5002 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5002 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (y ◇ (w ◇ y)))))]

theorem Equation4512_5002_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5002 : Equation5002 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [h5002 (X0 ◇ (X1 ◇ X0)) X0 X0 X1]
    conv => enter [1]; rw [← h5002 X2 (X0 ◇ (X1 ◇ X0)) X0 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) (X2 ◇ (X0 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h5002 (X1 ◇ X0) X0 X2 X1]
    conv => enter [1]; rw [l1 X0 X1 X2]
  have l3 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l2 X0 (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5002 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation5003 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5003 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (y ◇ (w ◇ z)))))]

theorem Equation4512_5003_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5003 : Equation5003 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ ((X3 ◇ (X1 ◇ (X4 ◇ X3))) ◇ X0))) = X2 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2, 2]; rw [h5003 X0 X1 X3 X4]
    conv => enter [1]; rw [← h5003 X2 X1 (X3 ◇ (X1 ◇ (X4 ◇ X3))) X0]
  have l1 : ∀ X1 X0 X2 X3 X4 : G, (X1 ◇ ((X0 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X2)))) ◇ X4)) = (X0 ◇ X4) := by
    intro X1 X0 X2 X3 X4
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X2)))) X4]
    conv => enter [1, 1]; rw [← h5003 X0 X1 X2 X3]
  have l2 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X1 ◇ (X0 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X2))) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l1 X1 X0 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 (X2 ◇ (X1 ◇ (X3 ◇ X2))) X4]
  have l3 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ (X4 ◇ X3)) ◇ X0)))) = X2 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2]; rw [h4512 X3 (X1 ◇ (X4 ◇ X3)) X0]
    conv => enter [1]; rw [l0 X1 X2 X3 X4 X0]
  have l4 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X1 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X2)) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X1 ◇ (X3 ◇ X2)) X4]
  have l5 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ ((X4 ◇ X3) ◇ X0))))) = X2 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 (X4 ◇ X3) X0]
    conv => enter [1]; rw [l3 X1 X2 X3 X4 X0]
  have l6 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ ((X3 ◇ X2) ◇ X4))))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l4 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X3 ◇ X2) X4]
  have l7 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X4 ◇ (X3 ◇ X0)))))) = X2 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X4 X3 X0]
    conv => enter [1]; rw [l5 X1 X2 X3 X4 X0]
  have l8 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X3 ◇ (X2 ◇ X4)))))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l6 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X3 X2 X4]
  have l9 : ∀ X0 X4 : G, (X0 ◇ X4) = X0 := by
    intro X0 X4
    conv => enter [1]; rw [l8 X0 X4 X0 X0 X0]
    conv => enter [1]; rw [l7 X0 X0 X0 X0 X4]
  have l10 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X0 (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5003 X1 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation2_implies_Equation5004 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5004 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (y ◇ (w ◇ w)))))]

theorem Equation4512_5004_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5004 : Equation5004 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X3 X2 X4 : G, (X0 ◇ X1) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X4)))))) := by
    intro X0 X1 X3 X2 X4
    conv => enter [1]; rw [h5004 (X0 ◇ X1) X3 X2 X4]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ (X4 ◇ X4)))]
  have l1 : ∀ X1 X0 X2 X3 X4 : G, (X1 ◇ ((X0 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X3)))) ◇ X4)) = (X0 ◇ X4) := by
    intro X1 X0 X2 X3 X4
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X3)))) X4]
    conv => enter [1, 1]; rw [← h5004 X0 X1 X2 X3]
  have l2 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X4 ◇ X4)))))) = X0 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X4 ◇ X4))))]
    conv => enter [1]; rw [← h5004 X0 (X1 ◇ X2) X3 X4]
  have l3 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X4 ◇ X4))))))) = X0 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X1 X2 (X4 ◇ X4)]
    conv => enter [1]; rw [l2 X1 X2 X0 X3 X4]
  have l4 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X1 ◇ (X0 ◇ ((X2 ◇ (X1 ◇ (X3 ◇ X3))) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l1 X1 X0 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 (X2 ◇ (X1 ◇ (X3 ◇ X3))) X4]
  have l5 : ∀ X1 X0 X3 : G, (X1 ◇ (X0 ◇ X3)) = X0 := by
    intro X1 X0 X3
    conv => enter [1, 2]; rw [l0 X0 X3 X1 X1 X1]
    conv => enter [1]; rw [l3 X1 X1 X0 X3 X1]
  have l6 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X1 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ (X3 ◇ X3)) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l4 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X1 ◇ (X3 ◇ X3)) X4]
  have l7 : ∀ X0 X4 : G, (X0 ◇ X4) = X0 := by
    intro X0 X4
    conv => enter [1]; rw [l6 X0 X4 X0 X0 X0]
    conv => enter [1]; rw [l5 X0 X0 (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X4))]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5004 X1 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l8 x y]

@[equational_result]
theorem Equation2_implies_Equation5005 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5005 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (y ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5005_implies_Equation2 (G : Type*) [Magma G] (h5005 : Equation5005 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5005 X0 X2 X1 X1 X1]
    conv => enter [1]; rw [← h5005 X2 X1 X0 X2 (X1 ◇ X1)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5005 X2 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5007 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5007 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (z ◇ (x ◇ y)))))]

theorem Equation4512_5007_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5007 : Equation5007 G) : Equation2 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h5007 X0 X0 X0]
    conv => enter [1]; rw [← h5007 X0 (X0 ◇ X0) X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 X0 X0]
    conv => enter [1]; rw [l0 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h5007 X0 X1 (X0 ◇ X1)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 (X0 ◇ (X0 ◇ X1)) X1]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [l2 X0 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1]; rw [l3 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [l5 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l4 (X0 ◇ X1)]
    conv => enter [1]; rw [← h5007 X0 X1 (X0 ◇ X1)]
  have l9 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X1 (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l8 X1 X0]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l7 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l12 X1 X0]
  have l14 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l13 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l14 x y]

@[equational_result]
theorem Equation2_implies_Equation5008 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5008 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (z ◇ (x ◇ z)))))]

theorem Equation4512_5008_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5008 : Equation5008 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X3 X2 : G, (X0 ◇ X1) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h5008 (X0 ◇ X1) X3 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))]
  have l1 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X3)))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X3))))]
    conv => enter [1]; rw [← h5008 X0 (X1 ◇ X2) X3]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5008 X0 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X0 X1]
  have l3 : ∀ X0 X1 X3 X2 : G, (X0 ◇ X1) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l0 X0 X1 X3 X2]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 X1 X0 X2]
    conv => enter [1, 2]; rw [l2 X0 (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))))]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))))]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l5 X0 X1 X2]
    conv => enter [1]; rw [l2 X1 (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l6 X0 X1 X2]
    conv => enter [1, 2]; rw [l2 X2 (X0 ◇ (X1 ◇ X2))]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X2 (X0 ◇ (X1 ◇ X2))]
    conv => enter [1]; rw [← l7 X0 X1 X2]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = X1 := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1]; rw [l2 X0 X1]
  have l10 : ∀ X1 X2 : G, (X1 ◇ X2) = X1 := by
    intro X1 X2
    conv => enter [1, 2]; rw [← l2 X1 X2]
    conv => enter [1]; rw [l9 X1 X1 X2]
  have l11 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l10 X0 (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))]
    conv => enter [1]; rw [← h5008 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l11 x y]

@[equational_result]
theorem Equation2_implies_Equation5009 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5009 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (z ◇ (x ◇ w)))))]

@[equational_result]
theorem Equation5009_implies_Equation2 (G : Type*) [Magma G] (h5009 : Equation5009 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h5009 X0 X0 X2 X1]
    conv => enter [1]; rw [← h5009 X2 X1 X0 (X2 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5009 X0 X0 X0 X1]
    conv => enter [1]; rw [← h5009 X0 X1 X0 (X0 ◇ X1)]
  have l2 : ∀ X2 X0 : G, (X2 ◇ X0) = X2 := by
    intro X2 X0
    conv => enter [1, 2]; rw [← l1 X2 X0]
    conv => enter [1]; rw [l0 X2 X2 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))]
    conv => enter [1]; rw [← h5009 X1 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation5011 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5011 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (z ◇ (y ◇ y)))))]

theorem Equation4512_5011_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5011 : Equation5011 G) : Equation2 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h5011 (X0 ◇ X0) X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h5011 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h5011 (X0 ◇ X0) X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [l1 (X0 ◇ X0)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h5011 X1 X0 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [l3 X0 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 2]; rw [l3 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [l4 X0]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5011 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l8 x y]

@[equational_result]
theorem Equation2_implies_Equation5012 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5012 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (z ◇ (y ◇ z)))))]

theorem Equation4512_5012_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5012 : Equation5012 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X3 X2 : G, (X0 ◇ X1) = (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2)))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h5012 (X0 ◇ X1) X3 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ (X3 ◇ X2)))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l0 (X0 ◇ (X1 ◇ X0)) (X0 ◇ (X1 ◇ X0)) X1 X0]
    conv => enter [1]; rw [← h5012 X1 X0 (X0 ◇ (X1 ◇ X0))]
  have l2 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ X1) ◇ X4) = (X2 ◇ ((X0 ◇ (X1 ◇ (X3 ◇ (X3 ◇ (X2 ◇ X3))))) ◇ X4)) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1, 1]; rw [l0 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X2 (X0 ◇ (X1 ◇ (X3 ◇ (X3 ◇ (X2 ◇ X3))))) X4]
  have l3 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ X1) ◇ X4) = (X2 ◇ (X0 ◇ ((X1 ◇ (X3 ◇ (X3 ◇ (X2 ◇ X3)))) ◇ X4))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l2 X0 X1 X4 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X3 ◇ (X3 ◇ (X2 ◇ X3)))) X4]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ X0) (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l1 X0 X1]
  have l5 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ X1) ◇ X4) = (X2 ◇ (X0 ◇ (X1 ◇ ((X3 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X4)))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l3 X0 X1 X4 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X3 ◇ (X3 ◇ (X2 ◇ X3))) X4]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X1 X0 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ X1) ◇ X4) = (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ ((X3 ◇ (X2 ◇ X3)) ◇ X4))))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l5 X0 X1 X4 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X3 (X3 ◇ (X2 ◇ X3)) X4]
  have l8 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ X1) ◇ X4) = (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X4)))))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l7 X0 X1 X4 X2 X3]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X3 (X2 ◇ X3) X4]
  have l9 : ∀ X0 X1 X4 X2 X3 : G, ((X0 ◇ X1) ◇ X4) = (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X3 ◇ X4))))))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [l8 X0 X1 X4 X2 X3]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X2 X3 X4]
  have l10 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ (X1 ◇ X4)) = (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ (X3 ◇ (X2 ◇ (X3 ◇ X4))))))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [h4512 X0 X1 X4]
    conv => enter [1]; rw [l9 X0 X1 X4 X2 X3]
  have l11 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h5012 X0 X2 X1]
    conv => enter [1]; rw [l6 (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) X2]
  have l12 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0)))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l6 X1 X0]
    conv => enter [1]; rw [← h5012 X2 X1 (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))))]
  have l13 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) X2]
  have l14 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l13 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) X2]
  have l15 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0))))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h4512 X1 (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ((X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0)]
    conv => enter [1]; rw [l12 X1 X2 X0]
  have l16 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0)))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X1 ◇ (X2 ◇ X1))) ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0))))]
    conv => enter [1]; rw [l11 X0 X1 X2]
  have l17 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l14 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ (X0 ◇ X1))) X2]
  have l18 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0)))))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 (X1 ◇ (X1 ◇ (X0 ◇ X1))) ((X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0)]
    conv => enter [1]; rw [l15 X1 X2 X0]
  have l19 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 (X1 ◇ (X2 ◇ X1)) ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0))))]
    conv => enter [1]; rw [l16 X0 X1 X2]
  have l20 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l17 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X1 ◇ (X0 ◇ X1)) X2]
  have l21 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0))))))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X1 (X1 ◇ (X0 ◇ X1)) ((X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0)]
    conv => enter [1]; rw [l18 X1 X2 X0]
  have l22 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0)))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X1 (X2 ◇ X1) ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0))))]
    conv => enter [1]; rw [l19 X0 X1 X2]
  have l23 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l20 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l24 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0)))))))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X1 (X0 ◇ X1) ((X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0)]
    conv => enter [1]; rw [l21 X1 X2 X0]
  have l25 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0))))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [h4512 X2 X1 ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0))))]
    conv => enter [1]; rw [l22 X0 X1 X2]
  have l26 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l23 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l27 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0))))))))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 ((X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))) ◇ X0)]
    conv => enter [1]; rw [l24 X1 X2 X0]
  have l28 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0)))))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X0 (X1 ◇ (X1 ◇ (X2 ◇ X1))) (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0)))]
    conv => enter [1]; rw [l25 X0 X1 X2]
  have l29 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))))))))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X1 (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) X0]
    conv => enter [1]; rw [l27 X1 X2 X0]
  have l30 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0))))))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X1 (X1 ◇ (X2 ◇ X1)) (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0)))]
    conv => enter [1]; rw [l28 X0 X1 X2]
  have l31 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))))))))))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 (X1 ◇ (X1 ◇ (X0 ◇ X1))) X0]
    conv => enter [1]; rw [l29 X1 X2 X0]
  have l32 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0)))))))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X1 (X2 ◇ X1) (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0)))]
    conv => enter [1]; rw [l30 X0 X1 X2]
  have l33 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)))))))))))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X1 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l31 X1 X2 X0]
  have l34 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0))))))))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X2 X1 (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0)))]
    conv => enter [1]; rw [l32 X0 X1 X2]
  have l35 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)))))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2]; rw [l26 X0 ((X1 ◇ (X0 ◇ X1)) ◇ X0) X1]
    conv => enter [1]; rw [l33 X1 X2 X0]
  have l36 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0)))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [l10 X1 X0 (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0))) X2 X1]
    conv => enter [1]; rw [l34 X0 X1 X2]
  have l37 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))))))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l35 X1 X2 X0]
  have l38 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0))))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 (X1 ◇ (X1 ◇ (X2 ◇ X1))) ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0)]
    conv => enter [1]; rw [l36 X0 X1 X2]
  have l39 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l37 X1 X2 X0]
  have l40 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0)))))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X1 (X1 ◇ (X2 ◇ X1)) ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0)]
    conv => enter [1]; rw [l38 X0 X1 X2]
  have l41 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X1 ◇ X0))) = X2 := by
    intro X2 X1 X0
    conv => enter [1]; rw [l10 X2 X1 (X1 ◇ X0) X1 X0]
    conv => enter [1]; rw [l39 X1 X2 X0]
  have l42 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0))))))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X1 (X2 ◇ X1) ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X0)]
    conv => enter [1]; rw [l40 X0 X1 X2]
  have l43 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l41 X0 X0 (X0 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0)))) ◇ X0))))))))]
    conv => enter [1]; rw [l42 X0 X0 X2]
  intro x y
  conv => enter [1]; rw [l43 x y]

@[equational_result]
theorem Equation2_implies_Equation5013 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5013 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (z ◇ (y ◇ w)))))]

@[equational_result]
theorem Equation5013_implies_Equation2 (G : Type*) [Magma G] (h5013 : Equation5013 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h5013 X0 X1 X0 X0]
    conv => enter [1]; rw [← h5013 X1 X0 X0 (X1 ◇ X0)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l0 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5015 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5015 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (z ◇ (z ◇ y)))))]

theorem Equation4512_5015_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5015 : Equation5015 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ (X3 ◇ (X2 ◇ (X2 ◇ X0)))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h5015 X0 X2 X1]
    conv => enter [1]; rw [← h5015 X3 (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) X2]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h5015 X0 X0 X0]
    conv => enter [1]; rw [← h5015 X1 (X0 ◇ (X0 ◇ X0)) X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h5015 X0 X1 X0]
    conv => enter [1]; rw [← h5015 X1 (X0 ◇ X1) X0]
  have l3 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X1)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X1)))) X3]
    conv => enter [1, 1]; rw [← h5015 X0 X1 X2]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ ((X2 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l3 X1 X0 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X2 ◇ (X2 ◇ (X2 ◇ X1))) X3]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) (X1 ◇ X0)]
    conv => enter [1]; rw [l1 X0 X1]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X3 ◇ (X2 ◇ (X2 ◇ X0))))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X1 ◇ (X1 ◇ X2))) (X3 ◇ (X2 ◇ (X2 ◇ X0)))]
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
  have l8 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X2 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l4 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X2 ◇ (X2 ◇ X1)) X3]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l6 X0 X1]
  have l10 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X2 ◇ (X2 ◇ X0)))))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 (X1 ◇ (X1 ◇ X2)) (X3 ◇ (X2 ◇ (X2 ◇ X0)))]
    conv => enter [1]; rw [l7 X0 X1 X2 X3]
  have l11 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l8 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (X2 ◇ X1) X3]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [l9 X0 X1]
  have l13 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X2 ◇ X0))))))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X1 (X1 ◇ X2) (X3 ◇ (X2 ◇ (X2 ◇ X0)))]
    conv => enter [1]; rw [l10 X0 X1 X2 X3]
  have l14 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l11 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X2 X1 X3]
  have l15 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X2 ◇ X0))))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [← l12 X1 ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ (X2 ◇ X0))))]
    conv => enter [1]; rw [l13 X0 X1 X2 X3]
  have l16 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l14 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [l12 X2 (X1 ◇ X3)]
  have l17 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X0)))))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 (X3 ◇ (X2 ◇ (X2 ◇ X0)))]
    conv => enter [1]; rw [l15 X0 X1 X2 X3]
  have l18 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ (X3 ◇ X0))) = X3 := by
    intro X0 X1 X3
    conv => enter [1, 2, 2]; rw [l16 X3 X0 X0 X0]
    conv => enter [1]; rw [l17 X0 X1 X0 X3]
  have l19 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l5 X0 X0]
    conv => enter [1]; rw [← h5015 X1 X0 X0]
  have l20 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l18 X0 X1 X0]
    conv => enter [1]; rw [l19 X0 X1]
  intro x y
  conv => enter [1]; rw [l20 x y]

@[equational_result]
theorem Equation2_implies_Equation5016 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5016 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (z ◇ (z ◇ z)))))]

theorem Equation4512_5016_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5016 : Equation5016 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2]; rw [h5016 (X0 ◇ (X0 ◇ (X0 ◇ X0))) (X0 ◇ (X0 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [← h5016 X2 X1 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l1 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ (X3 ◇ X3)))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ (X3 ◇ (X3 ◇ X3))))]
    conv => enter [1]; rw [← h5016 X0 (X1 ◇ X2) X3]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5016 X0 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X0 X1]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5016 (X0 ◇ (X0 ◇ (X0 ◇ X0))) X2 X0]
    conv => enter [1]; rw [l0 X1 X2 X0]
  have l4 : ∀ X0 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X2 := by
    intro X0 X2
    conv => enter [1, 2, 2, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [l3 X0 X0 X2]
  have l5 : ∀ X0 X2 : G, (X0 ◇ (X0 ◇ X0)) = X2 := by
    intro X0 X2
    conv => enter [1, 2, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [l4 X0 X2]
  have l6 : ∀ X0 X2 : G, (X0 ◇ X0) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [l5 X0 X2]
  have l7 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l2 X0 X0]
    conv => enter [1]; rw [l6 X0 X2]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation2_implies_Equation5017 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5017 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (z ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5017_implies_Equation2 (G : Type*) [Magma G] (h5017 : Equation5017 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5017 X0 X2 X0 X1]
    conv => enter [1]; rw [← h5017 X2 X1 X0 (X0 ◇ X1)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5017 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5019 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5019 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (z ◇ (w ◇ y)))))]

@[equational_result]
theorem Equation5019_implies_Equation2 (G : Type*) [Magma G] (h5019 : Equation5019 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, ((X1 ◇ X2) ◇ X0) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h5019 X0 X2 X0 X1]
    conv => enter [1]; rw [← h5019 X2 (X1 ◇ X2) X0 X0]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0 (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))]
    conv => enter [1]; rw [← h5019 X2 (X0 ◇ X0) X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5020 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5020 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (z ◇ (w ◇ z)))))]

theorem Equation4512_5020_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5020 : Equation5020 G) : Equation2 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) = X3 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2]; rw [h5020 (X0 ◇ (X1 ◇ X0)) (X0 ◇ (X1 ◇ X0)) X0 X1]
    conv => enter [1]; rw [← h5020 X3 X2 (X0 ◇ (X1 ◇ X0)) X0]
  have l1 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ (X4 ◇ X3)))))) = X0 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ (X3 ◇ (X4 ◇ X3))))]
    conv => enter [1]; rw [← h5020 X0 (X1 ◇ X2) X3 X4]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5020 X0 X1 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X0 X1 X1]
  have l3 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X3 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [← l2 X3 (X0 ◇ (X0 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [← h5020 X3 X2 X0 X1]
  have l4 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 X0 X0 X0]
    conv => enter [1]; rw [l3 X0 X0 X0 X3]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation2_implies_Equation5021 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5021 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (z ◇ (w ◇ w)))))]

@[equational_result]
theorem Equation5021_implies_Equation2 (G : Type*) [Magma G] (h5021 : Equation5021 G) : Equation2 G := by
  have l0 : ∀ X2 X3 X4 X0 X1 : G, (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X3 := by
    intro X2 X3 X4 X0 X1
    conv => enter [1, 2, 2, 2]; rw [h5021 (X0 ◇ (X0 ◇ (X1 ◇ X1))) X4 X0 X1]
    conv => enter [1]; rw [← h5021 X3 X2 X4 (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
  have l1 : ∀ X2 X4 X3 : G, (X2 ◇ X4) = X3 := by
    intro X2 X4 X3
    conv => enter [1, 2]; rw [h5021 X4 X3 X2 X2]
    conv => enter [1]; rw [l0 X2 X3 X4 X2 X2]
  have l2 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l1 X0 (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5021 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation5022 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5022 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5022_implies_Equation2 (G : Type*) [Magma G] (h5022 : Equation5022 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5022 X0 X2 X0 X1 X1]
    conv => enter [1]; rw [← h5022 X2 X1 X0 X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5022 X2 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5024 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5024 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (w ◇ (x ◇ y)))))]

theorem Equation4512_5024_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5024 : Equation5024 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 X3 X4 X5 : G, ((X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) ◇ (X3 ◇ (X4 ◇ (X5 ◇ X0)))) = X3 := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1, 2, 2, 2, 2]; rw [h5024 X0 X3 X1 X2]
    conv => enter [1]; rw [← h5024 X3 (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) X4 X5]
  have l1 : ∀ X1 X2 X0 X3 X4 : G, ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X0 ◇ (X4 ◇ X0))) = X0 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1, 2, 2, 2]; rw [h5024 X0 X3 X1 X2]
    conv => enter [1]; rw [← h5024 X0 (X1 ◇ (X2 ◇ (X0 ◇ X3))) X4 X3]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h5024 X0 X1 X0 X1]
    conv => enter [1]; rw [← h5024 X1 (X0 ◇ X1) X0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X0 ◇ (X4 ◇ X0)))) = X0 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ X3)) (X0 ◇ (X4 ◇ X0))]
    conv => enter [1]; rw [l1 X1 X2 X0 X3 X4]
  have l5 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ (X3 ◇ (X4 ◇ (X5 ◇ X0))))) = X3 := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X2 ◇ (X0 ◇ X3))) (X3 ◇ (X4 ◇ (X5 ◇ X0)))]
    conv => enter [1]; rw [l0 X0 X1 X2 X3 X4 X5]
  have l6 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ (X0 ◇ (X4 ◇ X0))))) = X0 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1, 2]; rw [h4512 X2 (X0 ◇ X3) (X0 ◇ (X4 ◇ X0))]
    conv => enter [1]; rw [l4 X1 X2 X0 X3 X4]
  have l7 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ (X3 ◇ (X4 ◇ (X5 ◇ X0)))))) = X3 := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1, 2]; rw [h4512 X1 (X2 ◇ (X0 ◇ X3)) (X3 ◇ (X4 ◇ (X5 ◇ X0)))]
    conv => enter [1]; rw [l5 X0 X1 X2 X3 X4 X5]
  have l8 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X0 ◇ (X4 ◇ X0)))))) = X0 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1, 2, 2]; rw [h4512 X0 X3 (X0 ◇ (X4 ◇ X0))]
    conv => enter [1]; rw [l6 X1 X2 X0 X3 X4]
  have l9 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ (X3 ◇ (X4 ◇ (X5 ◇ X0))))))) = X3 := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1, 2, 2]; rw [h4512 X2 (X0 ◇ X3) (X3 ◇ (X4 ◇ (X5 ◇ X0)))]
    conv => enter [1]; rw [l7 X0 X1 X2 X3 X4 X5]
  have l10 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ X4)))) = X0 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1, 2, 2, 2, 2]; rw [← l3 X0 X4]
    conv => enter [1]; rw [l8 X1 X2 X0 X3 X4]
  have l11 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ (X4 ◇ (X5 ◇ X0)))))))) = X3 := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X3 (X3 ◇ (X4 ◇ (X5 ◇ X0)))]
    conv => enter [1]; rw [l9 X0 X1 X2 X3 X4 X5]
  have l12 : ∀ X2 X3 : G, X2 = X3 := by
    intro X2 X3
    conv => enter [1]; rw [← l10 X2 X2 X2 X2 (X3 ◇ (X3 ◇ (X2 ◇ (X2 ◇ X2))))]
    conv => enter [1]; rw [l11 X2 X2 X2 X3 X2 X2]
  intro x y
  conv => enter [1]; rw [l12 x y]

@[equational_result]
theorem Equation2_implies_Equation5025 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5025 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (w ◇ (x ◇ z)))))]

theorem Equation4512_5025_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5025 : Equation5025 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h5025 X0 (X1 ◇ (X0 ◇ X2)) X2 X1]
    conv => enter [1]; rw [← h5025 X2 X1 (X1 ◇ (X0 ◇ X2)) X0]
  have l1 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X3)))))) = X0 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X3))))]
    conv => enter [1]; rw [← h5025 X0 (X1 ◇ X2) X3 X4]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5025 X0 X1 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X0 X1 X1]
  have l3 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [← l2 X2 (X0 ◇ (X1 ◇ (X2 ◇ X0)))]
    conv => enter [1]; rw [← h5025 X2 X3 X0 X1]
  have l4 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0 (X0 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l3 X0 X0 X0 X2]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation2_implies_Equation5026 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5026 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (w ◇ (x ◇ w)))))]

@[equational_result]
theorem Equation5026_implies_Equation2 (G : Type*) [Magma G] (h5026 : Equation5026 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5026 X0 X2 (X0 ◇ X2) X2]
    conv => enter [1]; rw [← h5026 X2 X1 X0 (X0 ◇ X2)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 (X2 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5026 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5027 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5027 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (w ◇ (x ◇ u)))))]

@[equational_result]
theorem Equation5027_implies_Equation2 (G : Type*) [Magma G] (h5027 : Equation5027 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5027 X0 X2 X1 X2 X1]
    conv => enter [1]; rw [← h5027 X2 X1 X0 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 (X2 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5027 X2 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5029 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5029 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (w ◇ (y ◇ y)))))]

end Semigroup5
