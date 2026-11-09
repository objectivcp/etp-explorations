import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_5235_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5235 : Equation5235 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ (X2 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [h5235 X0 X2 X1]
    conv => enter [1]; rw [← h5235 X1 (X0 ◇ (X1 ◇ (X0 ◇ X2))) X2]
  have l1 : ∀ X0 X1 X3 X2 : G, (X0 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3)))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h5235 (X0 ◇ X1) X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X3))]
  have l2 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))))) = X2 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))]
    conv => enter [1]; rw [← h5235 X2 X3 (X0 ◇ X1)]
  have l3 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))))) = X2 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [l2 X3 X0 X1 X2]
  have l4 : ∀ X0 X1 X3 X2 : G, (X0 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3))))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l1 X0 X1 X3 X2]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X0 X1 X3]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ (X0 ◇ X2)) (X2 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1 X0 X0]
    conv => enter [1]; rw [l3 X0 X0 X0 X1]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ (X1 ◇ X0))))) = X1 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 (X0 ◇ X2) (X2 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l5 X0 X1 X2]
  have l8 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ (X1 ◇ X0)))) = X1 := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l6 X0 (X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ (X1 ◇ X0))))]
    conv => enter [1]; rw [l7 X0 X1 X2]
  have l9 : ∀ X0 X2 X1 : G, ((X0 ◇ X2) ◇ (X2 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l6 X1 ((X0 ◇ X2) ◇ (X2 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [l8 X1 X0 X2]
  have l10 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X2 X1
    conv => enter [1]; rw [h4512 X0 X2 (X2 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l9 X0 X2 X1]
  have l11 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ (X1 ◇ X0))) = X1 := by
    intro X2 X1 X0
    conv => enter [1]; rw [← l6 X0 (X2 ◇ (X2 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [l10 X0 X2 X1]
  have l12 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ X0)) = X1 := by
    intro X2 X1 X0
    conv => enter [1, 2]; rw [← l6 X2 (X1 ◇ X0)]
    conv => enter [1]; rw [l11 X2 X1 X0]
  have l13 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l6 X1 X0]
    conv => enter [1]; rw [l12 X1 X1 X0]
  have l14 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l13 X0 (X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0))))]
    conv => enter [1]; rw [← h5235 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l14 x y]

@[equational_result]
theorem Equation2_implies_Equation5236 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5236 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (z ◇ (x ◇ z)))))]

theorem Equation4512_5236_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5236 : Equation5236 G) : Equation2 G := by
  have l0 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))))) = X2 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))]
    conv => enter [1]; rw [← h5236 X2 X3 (X0 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X3)))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X3))))]
    conv => enter [1]; rw [← h5236 X0 (X1 ◇ X2) X3]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5236 X0 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X1 X0]
  have l3 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))))) = X2 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l0 X3 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [← l2 X0 (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))))]
    conv => enter [1]; rw [l3 X0 X0 X1 X2]
  have l5 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))) = X2 := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))))]
    conv => enter [1]; rw [l4 X0 X1 X2]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l2 X1 (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))))]
    conv => enter [1]; rw [l5 X1 X2 X0]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X2 (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))]
    conv => enter [1]; rw [l6 X2 X0 X1]
  have l8 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X2 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l7 X0 X1 X2]
  have l9 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X2 := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l2 X1 (X2 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l8 X1 X2 X0]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X2 (X0 ◇ X1)]
    conv => enter [1]; rw [l9 X2 X0 X1]
  have l11 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l10 X0 (X0 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5236 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l11 x y]

@[equational_result]
theorem Equation2_implies_Equation5237 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5237 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (z ◇ (x ◇ w)))))]

@[equational_result]
theorem Equation5237_implies_Equation2 (G : Type*) [Magma G] (h5237 : Equation5237 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5237 X0 X0 X2 X1]
    conv => enter [1]; rw [← h5237 X2 X1 X0 (X0 ◇ X1)]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5237 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5239 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5239 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (z ◇ (y ◇ y)))))]

theorem Equation4512_5239_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5239 : Equation5239 G) : Equation2 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h5239 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h5239 X0 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h5239 X1 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [← h5239 X0 X0 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 X1 X0]
    conv => enter [1, 2]; rw [← l4 X1 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l2 X1 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l6 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [l2 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X0]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 X0]
    conv => enter [1]; rw [l8 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation2_implies_Equation5240 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5240 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (z ◇ (y ◇ z)))))]

theorem Equation4512_5240_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5240 : Equation5240 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X3 X2 : G, (X0 ◇ X1) = (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h5240 (X0 ◇ X1) X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X2))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X1 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h5240 (X0 ◇ X1) X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l3 : ∀ X2 X0 X1 : G, ((X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X0))) = X0 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2]; rw [h5240 X0 X1 X2]
    conv => enter [1]; rw [← l2 X1 (X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2))))]
    conv => enter [1]; rw [← h5240 X0 X1 X2]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l2 X2 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0 X0 X1]
    conv => enter [1, 2, 2]; rw [← l2 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h5240 X0 X0 X1]
  have l7 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X1 ◇ (X0 ◇ X1))) X2]
  have l8 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l7 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X1)) X2]
  have l9 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l4 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← l5 (X0 ◇ X1) X2]
  have l10 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ (X2 ◇ (X1 ◇ X2))) ◇ (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X0)))) = X0 := by
    intro X2 X0 X1
    conv => enter [1]; rw [h4512 X2 (X0 ◇ (X2 ◇ (X1 ◇ X2))) (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X0))]
    conv => enter [1]; rw [l3 X2 X0 X1]
  have l11 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l8 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l12 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X2 X0 X1
    conv => enter [1]; rw [l9 X2 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l13 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X0))))) = X0 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 (X2 ◇ (X1 ◇ X2)) (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X0))]
    conv => enter [1]; rw [l10 X2 X0 X1]
  have l14 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l11 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l15 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X2) ◇ (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X0)))))) = X0 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X2 (X1 ◇ X2) (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X0))]
    conv => enter [1]; rw [l13 X2 X0 X1]
  have l16 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = ((X1 ◇ X2) ◇ (X1 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l14 X0 X1 X2]
    conv => enter [1]; rw [← l12 (X1 ◇ X2) X1 X0]
  have l17 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X0))))))) = X0 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 X2 (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X0))]
    conv => enter [1]; rw [l15 X2 X0 X1]
  have l18 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X2 ◇ (X1 ◇ X0))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l16 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X1 X2 (X1 ◇ X0)]
  have l19 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (((X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X0) ◇ (X2 ◇ X1)))) = X0 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [l12 ((X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X0) X2 X1]
    conv => enter [1]; rw [l17 X2 X0 X1]
  have l20 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ (X0 ◇ (X2 ◇ X1))))) = X0 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [h4512 (X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))) X0 (X2 ◇ X1)]
    conv => enter [1]; rw [l19 X2 X0 X1]
  have l21 : ∀ X2 X1 X0 : G, (X2 ◇ ((X2 ◇ X1) ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2))))))) = X0 := by
    intro X2 X1 X0
    conv => enter [1, 2]; rw [l18 (X2 ◇ X1) X0 (X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2))))]
    conv => enter [1]; rw [l20 X2 X0 X1]
  have l22 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))))))) = X0 := by
    intro X2 X1 X0
    conv => enter [1, 2]; rw [h4512 X2 X1 (X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2)))))]
    conv => enter [1]; rw [l21 X2 X1 X0]
  have l23 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l6 X0 (X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))))]
    conv => enter [1]; rw [l22 X0 X0 X2]
  intro x y
  conv => enter [1]; rw [l23 x y]

@[equational_result]
theorem Equation2_implies_Equation5241 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5241 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (z ◇ (y ◇ w)))))]

theorem Equation4512_5241_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5241 : Equation5241 G) : Equation2 G := by
  have l0 : ∀ X3 X0 X1 X2 X4 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X4)))))) = X2 := by
    intro X3 X0 X1 X2 X4
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X4)))]
    conv => enter [1]; rw [← h5241 X2 X3 (X0 ◇ X1) X4]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5241 X0 X0 X1 X1]
    conv => enter [1]; rw [← h5241 X1 X1 X0 (X0 ◇ X1)]
  have l2 : ∀ X2 X3 : G, X2 = X3 := by
    intro X2 X3
    conv => enter [1]; rw [← l1 X2 (X2 ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X2) ◇ (X2 ◇ X2)))))]
    conv => enter [1]; rw [l0 X2 X2 X2 X3 X2]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation5243 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5243 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (z ◇ (z ◇ y)))))]

theorem Equation4512_5243_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5243 : Equation5243 G) : Equation2 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h5243 X0 X0 X0]
    conv => enter [1]; rw [← h5243 X0 (X0 ◇ X0) X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 X0 X0]
    conv => enter [1]; rw [l0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h5243 X1 X0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [l2 X0 X0]
  have l4 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h5243 X2 (X1 ◇ (X0 ◇ X1)) X1]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ (X0 ◇ X1)) X2]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0))))) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X1) (X1 ◇ (X2 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [l4 X1 X0 X2]
  have l8 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l9 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 (X1 ◇ (X2 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [l7 X1 X0 X2]
  have l10 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ X0))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [l8 X2 X0 X1]
    conv => enter [1]; rw [l9 X1 X0 X2]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1]; rw [l10 X0 X1 X0]
  have l13 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l12 X0 (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5243 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l13 x y]

@[equational_result]
theorem Equation2_implies_Equation5244 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5244 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (z ◇ (z ◇ z)))))]

theorem Equation4512_5244_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5244 : Equation5244 G) : Equation2 G := by
  have l0 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))))) = X2 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))]
    conv => enter [1]; rw [← h5244 X2 X3 (X0 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X3)))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X3))))]
    conv => enter [1]; rw [← h5244 X0 (X1 ◇ X2) X3]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5244 X0 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X1 X0]
  have l3 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))))) = X2 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l0 X3 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [← l2 X0 (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))))]
    conv => enter [1]; rw [l3 X0 X0 X1 X2]
  have l5 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))) = X2 := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))))]
    conv => enter [1]; rw [l4 X0 X1 X2]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l2 X1 (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))]
    conv => enter [1]; rw [l5 X1 X2 X0]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X2 (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))]
    conv => enter [1]; rw [l6 X2 X0 X1]
  have l8 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l2 X0 (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l7 X0 X1 X2]
  have l9 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X1 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l8 X1 X0 X2]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l9 X0 X1 X2]
  have l11 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X1)) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l10 X0 X1 X2]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l11 X1 X0 X2]
  have l13 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l12 X0 (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5244 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l13 x y]

@[equational_result]
theorem Equation2_implies_Equation5245 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5245 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (z ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5245_implies_Equation2 (G : Type*) [Magma G] (h5245 : Equation5245 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [h5245 X0 X2 X0 X1]
    conv => enter [1]; rw [← h5245 X2 X1 X0 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5245 X0 X0 X0 X1]
    conv => enter [1]; rw [← h5245 X0 X1 X0 (X0 ◇ X1)]
  have l2 : ∀ X0 X2 : G, (X0 ◇ X0) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X2]
  have l3 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l2 X0 X2]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation5247 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5247 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (z ◇ (w ◇ y)))))]

theorem Equation4512_5247_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5247 : Equation5247 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5247 X0 X0 X2 X1]
    conv => enter [1]; rw [← h5247 X2 (X1 ◇ X0) X0 X2]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 X0 X0]
    conv => enter [1]; rw [l0 X1 X0 X2]
  have l2 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l1 X0 X0 X0]
    conv => enter [1]; rw [l1 X0 X0 X3]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation5248 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5248 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (z ◇ (w ◇ z)))))]

@[equational_result]
theorem Equation5248_implies_Equation2 (G : Type*) [Magma G] (h5248 : Equation5248 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 X3 X4 : G, (X1 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ X2))) ◇ (X4 ◇ X0))) = X4 := by
    intro X1 X0 X2 X3 X4
    conv => enter [1, 2, 2, 2]; rw [h5248 X0 (X0 ◇ (X2 ◇ (X3 ◇ X2))) X2 X3]
    conv => enter [1]; rw [← h5248 X4 X1 (X0 ◇ (X2 ◇ (X3 ◇ X2))) X2]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h5248 (X0 ◇ X1) (X0 ◇ X1) X1 X0]
    conv => enter [1]; rw [← h5248 X1 X2 (X0 ◇ X1) X1]
  have l2 : ∀ X4 X0 : G, (X4 ◇ X0) = X4 := by
    intro X4 X0
    conv => enter [1, 2]; rw [← l1 (X0 ◇ (X4 ◇ (X4 ◇ X4))) X4 X0]
    conv => enter [1]; rw [l0 X4 X0 X4 X4 X4]
  have l3 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l2 X0 (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5248 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation5249 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5249 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (z ◇ (w ◇ w)))))]

theorem Equation4512_5249_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5249 : Equation5249 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X4 X2 X3 : G, (X0 ◇ X1) = (X4 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))))) := by
    intro X0 X1 X4 X2 X3
    conv => enter [1]; rw [h5249 (X0 ◇ X1) X4 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X3))]
  have l1 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X3)))))) = X2 := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X3)))]
    conv => enter [1]; rw [← h5249 X2 X4 (X0 ◇ X1) X3]
  have l2 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X4)))))) = X0 := by
    intro X1 X2 X3 X0 X4
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X4))))]
    conv => enter [1]; rw [← h5249 X0 (X1 ◇ X2) X3 X4]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5249 X0 X1 X1 X1]
    conv => enter [1]; rw [l2 X1 X1 X1 X0 X1]
  have l4 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X3))))))) = X2 := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 (X3 ◇ X3)]
    conv => enter [1]; rw [l1 X4 X0 X1 X2 X3]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X3)))))) = X2 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [← l3 X0 (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X3)))))]
    conv => enter [1]; rw [l4 X0 X0 X1 X2 X3]
  have l6 : ∀ X2 X0 : G, (X2 ◇ X0) = X2 := by
    intro X2 X0
    conv => enter [1]; rw [l0 X2 X0 X0 X2 X2]
    conv => enter [1]; rw [l5 X0 X2 X2 X2]
  have l7 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l6 X0 (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5249 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation2_implies_Equation5250 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5250 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5250_implies_Equation2 (G : Type*) [Magma G] (h5250 : Equation5250 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5250 X0 X0 X2 X1 X1]
    conv => enter [1]; rw [← h5250 X2 X1 X0 X2 (X1 ◇ X1)]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5250 X3 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5252 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5252 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (w ◇ (x ◇ y)))))]

theorem Equation4512_5252_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5252 : Equation5252 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h5252 X0 X1 X2 X2]
    conv => enter [1]; rw [← h5252 X2 (X0 ◇ X1) X1 X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l2 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l1 X0 X0 X0]
    conv => enter [1]; rw [l1 X0 X0 X3]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation5253 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5253 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (w ◇ (x ◇ z)))))]

@[equational_result]
theorem Equation5253_implies_Equation2 (G : Type*) [Magma G] (h5253 : Equation5253 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5253 X0 (X0 ◇ X2) X2 X2]
    conv => enter [1]; rw [← h5253 X2 X1 (X0 ◇ X2) X0]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5253 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5254 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5254 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (w ◇ (x ◇ w)))))]

@[equational_result]
theorem Equation5254_implies_Equation2 (G : Type*) [Magma G] (h5254 : Equation5254 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2]; rw [h5254 X0 (X0 ◇ (X1 ◇ (X0 ◇ X1))) X3 X1]
    conv => enter [1]; rw [← h5254 X3 X1 X2 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h5254 X0 X0 (X1 ◇ (X0 ◇ X1)) X1]
    conv => enter [1]; rw [← h5254 X0 X1 X2 (X1 ◇ (X0 ◇ X1))]
  have l2 : ∀ X3 X0 : G, (X3 ◇ X0) = X3 := by
    intro X3 X0
    conv => enter [1, 2]; rw [← l1 X3 X3 X0]
    conv => enter [1]; rw [l0 X3 X3 X3 X0]
  have l3 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l2 X0 (X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0))))]
    conv => enter [1]; rw [← h5254 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation5255 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5255 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (w ◇ (x ◇ u)))))]

@[equational_result]
theorem Equation5255_implies_Equation2 (G : Type*) [Magma G] (h5255 : Equation5255 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X3 : G, (X1 ◇ X0) = X3 := by
    intro X1 X0 X3
    conv => enter [1, 2]; rw [h5255 X0 X1 X3 X3 X1]
    conv => enter [1]; rw [← h5255 X3 X1 X1 X0 (X0 ◇ X1)]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5255 X3 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5257 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5257 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (w ◇ (y ◇ y)))))]

theorem Equation4512_5257_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5257 : Equation5257 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X3 X4 X2 : G, (X0 ◇ X1) = (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))))) := by
    intro X0 X1 X3 X4 X2
    conv => enter [1]; rw [h5257 (X0 ◇ X1) X3 X4 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X3))]
  have l1 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X4)))))) = X2 := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X4 ◇ X4)))]
    conv => enter [1]; rw [← h5257 X2 X4 (X0 ◇ X1) X3]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [l1 X0 X0 X0 X1 X0]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) = X1 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l2 X3 (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3))))]
    conv => enter [1]; rw [← h5257 X1 X3 X0 X2]
  have l4 : ∀ X1 X2 X3 : G, (X1 ◇ (X2 ◇ (X3 ◇ X3))) = X1 := by
    intro X1 X2 X3
    conv => enter [1, 2]; rw [← l2 X1 (X2 ◇ (X3 ◇ X3))]
    conv => enter [1]; rw [l3 X1 X1 X2 X3]
  have l5 : ∀ X2 X3 X1 : G, (X2 ◇ (X3 ◇ X3)) = X1 := by
    intro X2 X3 X1
    conv => enter [1]; rw [← l2 X1 (X2 ◇ (X3 ◇ X3))]
    conv => enter [1]; rw [l4 X1 X2 X3]
  have l6 : ∀ X3 X1 : G, (X3 ◇ X3) = X1 := by
    intro X3 X1
    conv => enter [1, 2]; rw [← l2 X3 X3]
    conv => enter [1]; rw [l5 X3 X3 X1]
  have l7 : ∀ X1 X3 : G, X1 = X3 := by
    intro X1 X3
    conv => enter [1]; rw [← l2 X1 X1]
    conv => enter [1]; rw [l6 X1 X3]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation2_implies_Equation5258 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5258 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (w ◇ (y ◇ z)))))]

theorem Equation4512_5258_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5258 : Equation5258 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 X3 X4 X5 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ (X1 ◇ X2)))) ◇ (X4 ◇ (X5 ◇ X0)))) = X4 := by
    intro X1 X2 X0 X3 X4 X5
    conv => enter [1, 2, 2, 2, 2]; rw [h5258 X0 X1 X2 X3]
    conv => enter [1]; rw [← h5258 X4 X1 (X2 ◇ (X0 ◇ (X3 ◇ (X1 ◇ X2)))) X5]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X0)) = X2 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h5258 X0 X2 X3 X1]
    conv => enter [1]; rw [← h5258 X2 X0 (X1 ◇ (X2 ◇ X3)) X3]
  have l2 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ (X1 ◇ X2)))) ◇ X4)) = (X0 ◇ X4) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ (X3 ◇ (X1 ◇ X2)))) X4]
    conv => enter [1, 1]; rw [← h5258 X0 X1 X2 X3]
  have l3 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ (X1 ◇ X2))) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l2 X1 X2 X0 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X3 ◇ (X1 ◇ X2))) X4]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ ((X2 ◇ X3) ◇ X0))) = X2 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 (X2 ◇ X3) X0]
    conv => enter [1]; rw [l1 X0 X1 X2 X3]
  have l5 : ∀ X1 X2 X0 X3 X4 X5 : G, (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ (X1 ◇ X2))) ◇ (X4 ◇ (X5 ◇ X0))))) = X4 := by
    intro X1 X2 X0 X3 X4 X5
    conv => enter [1, 2]; rw [h4512 X2 (X0 ◇ (X3 ◇ (X1 ◇ X2))) (X4 ◇ (X5 ◇ X0))]
    conv => enter [1]; rw [l0 X1 X2 X0 X3 X4 X5]
  have l6 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l3 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X3 ◇ (X1 ◇ X2)) X4]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) = X2 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X2 X3 X0]
    conv => enter [1]; rw [l4 X0 X1 X2 X3]
  have l8 : ∀ X1 X2 X0 X3 X4 X5 : G, (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ (X1 ◇ X2)) ◇ (X4 ◇ (X5 ◇ X0)))))) = X4 := by
    intro X1 X2 X0 X3 X4 X5
    conv => enter [1, 2, 2]; rw [h4512 X0 (X3 ◇ (X1 ◇ X2)) (X4 ◇ (X5 ◇ X0))]
    conv => enter [1]; rw [l5 X1 X2 X0 X3 X4 X5]
  have l9 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ ((X1 ◇ X2) ◇ X4))))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l6 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X3 (X1 ◇ X2) X4]
  have l10 : ∀ X1 X2 X4 : G, (X1 ◇ (X2 ◇ X4)) = X4 := by
    intro X1 X2 X4
    conv => enter [1, 2, 2]; rw [← l7 X1 (X1 ◇ (X1 ◇ X2)) X4 X1]
    conv => enter [1]; rw [l8 X1 X2 X1 X1 X4 X1]
  have l11 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X4)))))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l9 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X2 X4]
  have l12 : ∀ X0 X4 X3 X1 X2 : G, (X0 ◇ X4) = (X0 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X4)))) := by
    intro X0 X4 X3 X1 X2
    conv => enter [1]; rw [l11 X0 X4 X1 X2 X3]
    conv => enter [1]; rw [l10 X1 X2 (X0 ◇ (X3 ◇ (X1 ◇ (X2 ◇ X4))))]
  have l13 : ∀ X0 X4 X1 X2 : G, (X0 ◇ X4) = (X1 ◇ (X2 ◇ X4)) := by
    intro X0 X4 X1 X2
    conv => enter [1]; rw [l12 X0 X4 X0 X1 X2]
    conv => enter [1]; rw [l10 X0 X0 (X1 ◇ (X2 ◇ X4))]
  have l14 : ∀ X0 X4 : G, (X0 ◇ X4) = X4 := by
    intro X0 X4
    conv => enter [1]; rw [l13 X0 X4 X0 X0]
    conv => enter [1]; rw [l10 X0 X0 X4]
  have l15 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) = X1 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l14 X3 (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0))))]
    conv => enter [1]; rw [← h5258 X1 X3 X0 X2]
  have l16 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X0)) = X1 := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [← l10 X0 X1 (X2 ◇ (X3 ◇ X0))]
    conv => enter [1]; rw [l15 X0 X1 X2 X3]
  have l17 : ∀ X3 X0 X1 : G, (X3 ◇ X0) = X1 := by
    intro X3 X0 X1
    conv => enter [1, 2]; rw [← l14 X3 X0]
    conv => enter [1]; rw [l16 X3 X3 X0 X1]
  have l18 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l17 X0 (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5258 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l18 x y]

@[equational_result]
theorem Equation2_implies_Equation5259 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5259 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (w ◇ (y ◇ w)))))]

theorem Equation4512_5259_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5259 : Equation5259 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X3 X4 X2 : G, (X0 ◇ X1) = (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))))) := by
    intro X0 X1 X3 X4 X2
    conv => enter [1]; rw [h5259 (X0 ◇ X1) X3 X4 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X2))]
  have l1 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X3)))))) = X2 := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X4 ◇ X3)))]
    conv => enter [1]; rw [← h5259 X2 X4 (X0 ◇ X1) X3]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [l1 X0 X0 X0 X1 X0]
  have l3 : ∀ X0 X2 X3 X1 : G, (X0 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X1)))) = X3 := by
    intro X0 X2 X3 X1
    conv => enter [1, 2, 2, 2]; rw [← l2 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h5259 X3 X0 X2 X1]
  have l4 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ X1))) = X3 := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [← l2 X0 (X2 ◇ (X3 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l3 X0 X2 X3 X1]
  have l5 : ∀ X3 X0 X1 : G, (X3 ◇ (X0 ◇ X1)) = X3 := by
    intro X3 X0 X1
    conv => enter [1, 2]; rw [← l2 X3 (X0 ◇ X1)]
    conv => enter [1]; rw [l4 X3 X3 X0 X1]
  have l6 : ∀ X0 X1 X3 : G, (X0 ◇ X1) = X3 := by
    intro X0 X1 X3
    conv => enter [1]; rw [← l2 X3 (X0 ◇ X1)]
    conv => enter [1]; rw [l5 X3 X0 X1]
  have l7 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l6 X0 (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5259 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation2_implies_Equation5260 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5260 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (w ◇ (y ◇ u)))))]

@[equational_result]
theorem Equation5260_implies_Equation2 (G : Type*) [Magma G] (h5260 : Equation5260 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X3 : G, (X1 ◇ X0) = X3 := by
    intro X1 X0 X3
    conv => enter [1, 2]; rw [h5260 X0 X1 X3 X1 X1]
    conv => enter [1]; rw [← h5260 X3 X1 X1 X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5260 X3 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5262 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5262 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (w ◇ (z ◇ y)))))]

@[equational_result]
theorem Equation5262_implies_Equation2 (G : Type*) [Magma G] (h5262 : Equation5262 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, ((X1 ◇ X2) ◇ X0) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h5262 X0 X2 X1 X2]
    conv => enter [1]; rw [← h5262 X1 (X1 ◇ X2) X2 X0]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 X0 (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))]
    conv => enter [1]; rw [← h5262 X3 (X0 ◇ X0) X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5263 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5263 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (w ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5263_implies_Equation2 (G : Type*) [Magma G] (h5263 : Equation5263 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5263 X0 (X2 ◇ X2) X2 (X2 ◇ X2)]
    conv => enter [1]; rw [← h5263 X2 X1 (X2 ◇ X2) X0]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5263 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5264 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5264 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (w ◇ (z ◇ w)))))]

theorem Equation4512_5264_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5264 : Equation5264 G) : Equation2 G := by
  have l0 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X3)))))) = X2 := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ ((X0 ◇ X1) ◇ X3)))]
    conv => enter [1]; rw [← h5264 X2 X4 (X0 ◇ X1) X3]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X0 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h5264 (X0 ◇ X1) X1 X0 X1]
    conv => enter [1]; rw [← h5264 X0 X2 X1 (X0 ◇ X1)]
  have l2 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l1 X0 X0 (X0 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))]
    conv => enter [1]; rw [l0 X0 X0 X0 X2 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation5265 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5265 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (w ◇ (z ◇ u)))))]

@[equational_result]
theorem Equation5265_implies_Equation2 (G : Type*) [Magma G] (h5265 : Equation5265 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X3 : G, (X1 ◇ X0) = X3 := by
    intro X1 X0 X3
    conv => enter [1, 2]; rw [h5265 X0 X1 X3 X1 X1]
    conv => enter [1]; rw [← h5265 X3 X1 X1 X0 (X3 ◇ X1)]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5265 X3 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5267 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5267 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (w ◇ (w ◇ y)))))]

theorem Equation4512_5267_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5267 : Equation5267 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X3 X4 X2 : G, (X0 ◇ X1) = (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))))) := by
    intro X0 X1 X3 X4 X2
    conv => enter [1]; rw [h5267 (X0 ◇ X1) X3 X4 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ X3))]
  have l1 : ∀ X1 X2 X3 X0 : G, ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X2 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2]; rw [h5267 X0 X2 X0 X1]
    conv => enter [1]; rw [← h5267 X2 (X1 ◇ (X1 ◇ X2)) X3 X0]
  have l2 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4)))))) = X2 := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X3 ◇ X4)))]
    conv => enter [1]; rw [← h5267 X2 X4 (X0 ◇ X1) X3]
  have l3 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = X2 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ X2) (X3 ◇ X0)]
    conv => enter [1]; rw [l1 X1 X2 X3 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [l2 X0 X0 X0 X1 X0]
  have l5 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) = X2 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2]; rw [h4512 X1 X2 (X3 ◇ X0)]
    conv => enter [1]; rw [l3 X1 X2 X3 X0]
  have l6 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X2 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2]; rw [← l4 X1 (X2 ◇ (X3 ◇ X0))]
    conv => enter [1]; rw [l5 X1 X2 X3 X0]
  have l7 : ∀ X2 X3 X0 : G, (X2 ◇ (X3 ◇ X0)) = X2 := by
    intro X2 X3 X0
    conv => enter [1, 2]; rw [← l4 X2 (X3 ◇ X0)]
    conv => enter [1]; rw [l6 X2 X2 X3 X0]
  have l8 : ∀ X3 X0 X2 : G, (X3 ◇ X0) = X2 := by
    intro X3 X0 X2
    conv => enter [1]; rw [← l4 X2 (X3 ◇ X0)]
    conv => enter [1]; rw [l7 X2 X3 X0]
  have l9 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l8 X0 (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5267 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation2_implies_Equation5268 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5268 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (w ◇ (w ◇ z)))))]

@[equational_result]
theorem Equation5268_implies_Equation2 (G : Type*) [Magma G] (h5268 : Equation5268 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5268 X0 (X0 ◇ X2) X2 X0]
    conv => enter [1]; rw [← h5268 X2 X1 (X0 ◇ X2) X0]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5268 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5269 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5269 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (w ◇ (w ◇ w)))))]

theorem Equation4512_5269_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5269 : Equation5269 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2]; rw [h5269 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1))) (X0 ◇ (X1 ◇ (X1 ◇ X1))) X1]
    conv => enter [1]; rw [← h5269 X3 X1 X2 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l1 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X3)))) ◇ X4)) = (X0 ◇ X4) := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X3)))) X4]
    conv => enter [1, 1]; rw [← h5269 X0 X1 X2 X3]
  have l2 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ (X3 ◇ X3))) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l1 X1 X2 X0 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X3 ◇ (X3 ◇ X3))) X4]
  have l3 : ∀ X0 X3 X4 : G, (X0 ◇ (X3 ◇ (X3 ◇ X3))) = (X0 ◇ X4) := by
    intro X0 X3 X4
    conv => enter [1]; rw [← l0 X0 X0 (X0 ◇ (X3 ◇ (X3 ◇ X3))) X4]
    conv => enter [1]; rw [← l2 X0 X4 X0 X0 X3]
  have l4 : ∀ X0 X4 X3 : G, (X0 ◇ X4) = X3 := by
    intro X0 X4 X3
    conv => enter [1]; rw [← l3 X0 X3 X4]
    conv => enter [1]; rw [l0 X0 X3 X3 X3]
  have l5 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l4 X0 (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5269 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation2_implies_Equation5270 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5270 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (w ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5270_implies_Equation2 (G : Type*) [Magma G] (h5270 : Equation5270 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X3 : G, (X1 ◇ X0) = X3 := by
    intro X1 X0 X3
    conv => enter [1, 2]; rw [h5270 X0 X1 X3 X0 X1]
    conv => enter [1]; rw [← h5270 X3 X1 X1 X0 (X0 ◇ X1)]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5270 X3 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5272 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5272 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (w ◇ (u ◇ y)))))]

theorem Equation4512_5272_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5272 : Equation5272 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X4 X5 X2 X3 : G, (X0 ◇ X1) = (X4 ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))))) := by
    intro X0 X1 X4 X5 X2 X3
    conv => enter [1]; rw [h5272 (X0 ◇ X1) X4 X5 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
  have l1 : ∀ X5 X0 X1 X2 X3 X4 : G, (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))))) = X2 := by
    intro X5 X0 X1 X2 X3 X4
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X4 ◇ X5)))]
    conv => enter [1]; rw [← h5272 X2 X5 (X0 ◇ X1) X3 X4]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [l1 X0 X0 X0 X1 X0 X0]
  have l3 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = X1 := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [← l2 X4 (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))]
    conv => enter [1]; rw [← h5272 X1 X4 X0 X2 X3]
  have l4 : ∀ X1 X2 X3 X4 : G, (X1 ◇ (X2 ◇ (X3 ◇ X4))) = X1 := by
    intro X1 X2 X3 X4
    conv => enter [1, 2]; rw [← l2 X1 (X2 ◇ (X3 ◇ X4))]
    conv => enter [1]; rw [l3 X1 X1 X2 X3 X4]
  have l5 : ∀ X2 X3 X4 X1 : G, (X2 ◇ (X3 ◇ X4)) = X1 := by
    intro X2 X3 X4 X1
    conv => enter [1]; rw [← l2 X1 (X2 ◇ (X3 ◇ X4))]
    conv => enter [1]; rw [l4 X1 X2 X3 X4]
  have l6 : ∀ X3 X4 X1 : G, (X3 ◇ X4) = X1 := by
    intro X3 X4 X1
    conv => enter [1, 2]; rw [← l2 X3 X4]
    conv => enter [1]; rw [l5 X3 X3 X4 X1]
  have l7 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l6 X0 (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5272 X3 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation2_implies_Equation5273 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5273 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (w ◇ (u ◇ z)))))]

@[equational_result]
theorem Equation5273_implies_Equation2 (G : Type*) [Magma G] (h5273 : Equation5273 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X3 : G, (X1 ◇ X0) = X3 := by
    intro X1 X0 X3
    conv => enter [1, 2]; rw [h5273 X0 (X1 ◇ X3) X3 X1 X1]
    conv => enter [1]; rw [← h5273 X3 X1 (X1 ◇ X3) X0 X1]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5273 X3 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5274 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5274 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (w ◇ (u ◇ w)))))]

@[equational_result]
theorem Equation5274_implies_Equation2 (G : Type*) [Magma G] (h5274 : Equation5274 G) : Equation2 G := by
  have l0 : ∀ X2 X0 X1 X4 : G, (X2 ◇ (X0 ◇ X1)) = X4 := by
    intro X2 X0 X1 X4
    conv => enter [1, 2]; rw [h5274 (X0 ◇ X1) X2 X4 X1 X0]
    conv => enter [1]; rw [← h5274 X4 X2 X2 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 X0 (X3 ◇ (X0 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [← h5274 X3 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5275 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5275 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (w ◇ (u ◇ u)))))]

@[equational_result]
theorem Equation5275_implies_Equation2 (G : Type*) [Magma G] (h5275 : Equation5275 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X3 : G, (X1 ◇ X0) = X3 := by
    intro X1 X0 X3
    conv => enter [1, 2]; rw [h5275 X0 X1 X3 (X1 ◇ X1) X1]
    conv => enter [1]; rw [← h5275 X3 X1 X1 X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5275 X3 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5276 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5276 G := by
  intro x y z w u v
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (w ◇ (u ◇ v)))))]

theorem Equation4512_5276_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5276 : Equation5276 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X3 X0 X4 X5 X6 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X4 ◇ (X5 ◇ X6)))))) = X0 := by
    intro X1 X2 X3 X0 X4 X5 X6
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X0 ◇ (X4 ◇ (X5 ◇ X6))))]
    conv => enter [1]; rw [← h5276 X0 (X1 ◇ X2) X3 X4 X5 X6]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5276 X0 X0 X0 X3 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X0 X0 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5278 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5278 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (x ◇ (x ◇ y)))))]

theorem Equation4512_5278_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5278 : Equation5278 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0))) = X1 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [h5278 X0 X1 X1]
    conv => enter [1]; rw [← h5278 X1 (X1 ◇ (X0 ◇ (X0 ◇ X1))) X2]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h5278 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h5278 X0 (X0 ◇ X0) X0]
  have l2 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) X3]
    conv => enter [1, 1]; rw [← h5278 X0 X1 X2]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l2 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X1 ◇ (X0 ◇ (X0 ◇ X1))) X3]
  have l4 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 X0 X0]
    conv => enter [1]; rw [l1 X0]
  have l5 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)))) = X1 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X0 ◇ X1)) (X2 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0))]
    conv => enter [1]; rw [l0 X1 X0 X2]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X1)) X3]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0))))) = X1 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4512 X0 (X0 ◇ X1) (X2 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0))]
    conv => enter [1]; rw [l5 X1 X0 X2]
  have l8 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l6 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X0 ◇ X1) X3]
  have l9 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)))))) = X1 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0))]
    conv => enter [1]; rw [l7 X1 X0 X2]
  have l10 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l8 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X3]
  have l11 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))))))) = X1 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X1 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l9 X1 X0 X2]
  have l12 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))))))) = X1 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l11 X1 X0 X2]
  have l13 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))))))) = X1 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l12 X1 X0 X2]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [l10 X0 X0 X1 X1]
    conv => enter [1]; rw [l13 X1 X0 X1]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l4 X0]
    conv => enter [1]; rw [l14 X1 X0]
  have l16 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l4 X0]
    conv => enter [1]; rw [← h5278 X0 X0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l15 X1 X0]
    conv => enter [1]; rw [l16 X0 X1]
  have l18 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l17 X0 (X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0))))]
    conv => enter [1]; rw [← h5278 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l18 x y]

@[equational_result]
theorem Equation2_implies_Equation5279 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5279 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (x ◇ (x ◇ z)))))]

theorem Equation4512_5279_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5279 : Equation5279 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h5279 X0 X1 X1]
    conv => enter [1]; rw [← h5279 X1 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4512 X0 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [← h5279 X0 X1 (X0 ◇ (X0 ◇ X0))]
  have l4 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h5279 X1 X0 (X0 ◇ X1)]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [← h5279 X0 X0 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4512 X0 (X0 ◇ X0) (X1 ◇ X0)]
    conv => enter [1]; rw [l3 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4512 X0 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l7 X1 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l8 X1 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l5 X0]
    conv => enter [1]; rw [← h5279 X0 X1 X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l5 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1, 2]; rw [l9 X1 X0]
  have l13 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l5 X0]
    conv => enter [1]; rw [l10 X1 X0]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1]; rw [l5 X0]
  have l15 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l9 X0 X1]
    conv => enter [1]; rw [l13 X1 X0]
  have l16 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l14 X0 X0]
    conv => enter [1]; rw [l15 X0 X1]
  intro x y
  conv => enter [1]; rw [l16 x y]

@[equational_result]
theorem Equation2_implies_Equation5280 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5280 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (x ◇ (x ◇ w)))))]

@[equational_result]
theorem Equation5280_implies_Equation2 (G : Type*) [Magma G] (h5280 : Equation5280 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h5280 X0 X1 X1 X1]
    conv => enter [1]; rw [← h5280 X1 X1 X2 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5280 X0 X0 X1 X1]
    conv => enter [1]; rw [← h5280 X0 X1 X0 (X0 ◇ X1)]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ X0) = X1 := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l1 X1 (X2 ◇ X0)]
    conv => enter [1]; rw [l0 X1 X2 X0]
  have l3 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l2 X0 (X0 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5280 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation5282 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5282 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (x ◇ (y ◇ y)))))]

theorem Equation4512_5282_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5282 : Equation5282 G) : Equation2 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h5282 (X0 ◇ X0) X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h5282 X0 (X0 ◇ X0) X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h5282 X0 X0 X1]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [l1 X0]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 (X0 ◇ (X1 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [← h5282 X1 X0 (X0 ◇ (X1 ◇ (X0 ◇ X0)))]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X0 X1]
    conv => enter [1]; rw [l5 X0 X1]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [l3 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation2_implies_Equation5283 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5283 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (x ◇ (y ◇ z)))))]

theorem Equation4512_5283_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5283 : Equation5283 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X1 ◇ (X3 ◇ X0)))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h5283 X0 X1 X2]
    conv => enter [1]; rw [← h5283 X3 X1 (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2))))]
  have l1 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) X3]
    conv => enter [1, 1]; rw [← h5283 X0 X1 X2]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l1 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X1 ◇ (X0 ◇ (X1 ◇ X2))) X3]
  have l3 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X1 ◇ (X3 ◇ X0))))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2]; rw [h4512 X2 (X1 ◇ (X0 ◇ (X1 ◇ X2))) (X1 ◇ (X3 ◇ X0))]
    conv => enter [1]; rw [l0 X1 X2 X0 X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ X2)) X3]
  have l5 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X1 ◇ (X3 ◇ X0)))))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2]; rw [h4512 X1 (X0 ◇ (X1 ◇ X2)) (X1 ◇ (X3 ◇ X0))]
    conv => enter [1]; rw [l3 X1 X2 X0 X3]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l4 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l7 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X1 ◇ (X3 ◇ X0))))))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 (X1 ◇ X2) (X1 ◇ (X3 ◇ X0))]
    conv => enter [1]; rw [l5 X1 X2 X0 X3]
  have l8 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l6 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l9 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X0)))))))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X1 X2 (X1 ◇ (X3 ◇ X0))]
    conv => enter [1]; rw [l7 X1 X2 X0 X3]
  have l10 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ (X3 ◇ X0))) = X3 := by
    intro X0 X1 X3
    conv => enter [1]; rw [l8 X0 (X1 ◇ (X3 ◇ X0)) X1 X0]
    conv => enter [1]; rw [l9 X1 X0 X0 X3]
  have l11 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l10 X2 X3 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l12 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) = X2 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [l10 X3 (X0 ◇ X1) X2]
  have l13 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X2) ◇ (X1 ◇ X0))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [← l10 X2 X1 X0]
    conv => enter [1]; rw [← h5283 X2 X1 (X0 ◇ X2)]
  have l14 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4512 X0 X2 (X1 ◇ X0)]
    conv => enter [1]; rw [l13 X1 X0 X2]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1 X0 X0]
    conv => enter [1]; rw [l12 X0 X0 X0 X1]
  have l16 : ∀ X1 X2 : G, (X1 ◇ X1) = X2 := by
    intro X1 X2
    conv => enter [1, 2]; rw [← l10 X1 X2 X1]
    conv => enter [1]; rw [l14 X1 X1 X2]
  have l17 : ∀ X1 X2 : G, X1 = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l15 X1 X1]
    conv => enter [1]; rw [l16 X1 X2]
  intro x y
  conv => enter [1]; rw [l17 x y]

@[equational_result]
theorem Equation2_implies_Equation5284 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5284 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (x ◇ (y ◇ w)))))]

@[equational_result]
theorem Equation5284_implies_Equation2 (G : Type*) [Magma G] (h5284 : Equation5284 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h5284 X0 X1 X0 X0]
    conv => enter [1]; rw [← h5284 X1 X0 X1 (X1 ◇ X0)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l0 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5286 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5286 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (x ◇ (z ◇ y)))))]

theorem Equation4512_5286_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5286 : Equation5286 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0))) = X1 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [h5286 X0 X1 X2]
    conv => enter [1]; rw [← h5286 X1 (X1 ◇ (X0 ◇ (X2 ◇ X1))) X2]
  have l1 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))) X3]
    conv => enter [1, 1]; rw [← h5286 X0 X1 X2]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l1 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X1 ◇ (X0 ◇ (X2 ◇ X1))) X3]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0)))) = X1 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X2 ◇ X1)) (X2 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0))]
    conv => enter [1]; rw [l0 X1 X0 X2]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ (X2 ◇ X1)) X3]
  have l5 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0))))) = X1 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4512 X0 (X2 ◇ X1) (X2 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0))]
    conv => enter [1]; rw [l3 X1 X0 X2]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l4 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X2 ◇ X1) X3]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0)))))) = X1 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [h4512 X2 X1 (X2 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0))]
    conv => enter [1]; rw [l5 X1 X0 X2]
  have l8 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l6 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X2 X1 X3]
  have l9 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X0))))))) = X1 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X1 (X0 ◇ (X2 ◇ X1)) X0]
    conv => enter [1]; rw [l7 X1 X0 X2]
  have l10 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X0)))))))) = X1 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 (X2 ◇ X1) X0]
    conv => enter [1]; rw [l9 X1 X0 X2]
  have l11 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X0))))))))) = X1 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X2 X1 X0]
    conv => enter [1]; rw [l10 X1 X0 X2]
  have l12 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X0)))) = X1 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [l8 X0 X0 X1 X2]
    conv => enter [1]; rw [l11 X1 X0 X2]
  have l13 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))) = X3 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l12 X3 (X0 ◇ X1) X2]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l12 (X0 ◇ X0) X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l12 X1 (X0 ◇ X0) X0]
  have l15 : ∀ X1 X2 X0 X3 : G, ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X3 ◇ X0)))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2, 2]; rw [← l12 X0 X1 X2]
    conv => enter [1]; rw [← h5286 X3 (X1 ◇ (X2 ◇ (X1 ◇ X1))) X0]
  have l16 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X1 ◇ X1)) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X3 ◇ X0))))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X1 ◇ X1)) (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X3 ◇ X0)))]
    conv => enter [1]; rw [l15 X1 X2 X0 X3]
  have l17 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = X3 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [← l14 X2 (X0 ◇ X1)]
    conv => enter [1]; rw [l13 X3 X0 X1 X2]
  have l18 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ ((X1 ◇ X1) ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X3 ◇ X0)))))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2]; rw [h4512 X2 (X1 ◇ X1) (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X1))) ◇ (X3 ◇ X0)))]
    conv => enter [1]; rw [l16 X1 X2 X0 X3]
  have l19 : ∀ X1 X3 : G, X1 = X3 := by
    intro X1 X3
    conv => enter [1]; rw [← l17 X1 X1 (X1 ◇ X1) (X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X3 ◇ X1)))]
    conv => enter [1]; rw [l18 X1 X1 X1 X3]
  intro x y
  conv => enter [1]; rw [l19 x y]

@[equational_result]
theorem Equation2_implies_Equation5287 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5287 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (x ◇ (z ◇ z)))))]

theorem Equation4512_5287_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5287 : Equation5287 G) : Equation2 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h5287 (X0 ◇ X0) X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h5287 (X0 ◇ X0) (X0 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [l0 X0]
    conv => enter [1]; rw [← h5287 X0 X1 X0]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X1 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1, 2]; rw [← h5287 X0 (X0 ◇ (X1 ◇ X1)) X1]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l1 X0 X0]
    conv => enter [1]; rw [← h5287 X0 X0 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l5 X1]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l6 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l1 X1 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [l8 X1 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l3 X0 X1]
    conv => enter [1]; rw [l9 X1 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l7 X0 X1]
    conv => enter [1]; rw [l10 X1 X0]
  have l12 : ∀ X1 X2 X0 : G, ((X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X0) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h5287 X0 X2 X1]
    conv => enter [1]; rw [l11 (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) X2]
  have l13 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l11 (X1 ◇ X1) X0]
    conv => enter [1]; rw [← h5287 X0 (X1 ◇ X1) X1]
  have l14 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [← l11 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l15 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l14 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [l13 X1 X0]
  have l17 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0)) = X2 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ (X1 ◇ X1))) X0]
    conv => enter [1]; rw [l12 X1 X2 X0]
  have l18 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l15 X1 X0 X1]
    conv => enter [1]; rw [l16 X1 X0]
  have l19 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X2 (X0 ◇ (X1 ◇ X1)) X0]
    conv => enter [1]; rw [l17 X1 X2 X0]
  have l20 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) = X2 := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l18 X1 (X2 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))]
    conv => enter [1]; rw [l19 X1 X2 X0]
  have l21 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X0) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l18 X2 ((X0 ◇ (X1 ◇ X1)) ◇ X0)]
    conv => enter [1]; rw [l20 X2 X0 X1]
  have l22 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X1) ◇ X0)) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X0]
    conv => enter [1]; rw [l21 X0 X1 X2]
  have l23 : ∀ X1 X2 : G, (X1 ◇ X1) = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l11 X1 (X1 ◇ X1)]
    conv => enter [1]; rw [l22 X1 X1 X2]
  have l24 : ∀ X1 X2 : G, X1 = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l18 X1 X1]
    conv => enter [1]; rw [l23 X1 X2]
  intro x y
  conv => enter [1]; rw [l24 x y]

@[equational_result]
theorem Equation2_implies_Equation5288 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5288 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (x ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5288_implies_Equation2 (G : Type*) [Magma G] (h5288 : Equation5288 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X0)) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [h5288 X0 X1 X2 X1]
    conv => enter [1]; rw [← h5288 X2 X1 X1 (X0 ◇ (X2 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5288 X0 X0 X1 X1]
    conv => enter [1]; rw [← h5288 X0 X1 X0 (X1 ◇ X1)]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [l0 X1 X0 X2]
  have l3 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l2 X0 (X0 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5288 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation5290 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5290 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (x ◇ (w ◇ y)))))]

@[equational_result]
theorem Equation5290_implies_Equation2 (G : Type*) [Magma G] (h5290 : Equation5290 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, ((X1 ◇ X2) ◇ X0) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h5290 X0 X2 (X1 ◇ X2) X1]
    conv => enter [1]; rw [← h5290 X2 (X1 ◇ X2) X2 X0]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 X0 (X0 ◇ ((X0 ◇ X0) ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))))]
    conv => enter [1]; rw [← h5290 X3 (X0 ◇ X0) X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5291 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5291 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (x ◇ (w ◇ z)))))]

theorem Equation4512_5291_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5291 : Equation5291 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ X4))) ◇ (X1 ◇ X0))) = X2 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1, 2, 2, 2]; rw [h5291 X0 X2 X4 X3]
    conv => enter [1]; rw [← h5291 X2 X1 (X2 ◇ (X0 ◇ (X3 ◇ X4))) X4]
  have l1 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X0)) = X3 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2, 2]; rw [h5291 X0 X1 X3 X2]
    conv => enter [1]; rw [← h5291 X3 X1 (X0 ◇ (X2 ◇ X3)) X1]
  have l2 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X0))) = X3 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2]; rw [h4512 X0 (X2 ◇ X3) X0]
    conv => enter [1]; rw [l1 X1 X0 X2 X3]
  have l3 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ X4)) ◇ (X1 ◇ X0)))) = X2 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1, 2]; rw [h4512 X2 (X0 ◇ (X3 ◇ X4)) (X1 ◇ X0)]
    conv => enter [1]; rw [l0 X1 X2 X0 X3 X4]
  have l4 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X0)))) = X3 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X2 X3 X0]
    conv => enter [1]; rw [l2 X1 X0 X2 X3]
  have l5 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ X4) ◇ (X1 ◇ X0))))) = X2 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1, 2, 2]; rw [h4512 X0 (X3 ◇ X4) (X1 ◇ X0)]
    conv => enter [1]; rw [l3 X1 X2 X0 X3 X4]
  have l6 : ∀ X1 X2 : G, (X1 ◇ X1) = X2 := by
    intro X1 X2
    conv => enter [1, 2]; rw [← l4 X2 X1 (X1 ◇ X1) X1]
    conv => enter [1]; rw [l5 X1 X2 X1 X1 X1]
  have l7 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l6 X0 X0]
    conv => enter [1]; rw [l6 X0 X2]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation2_implies_Equation5292 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5292 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (x ◇ (w ◇ w)))))]

theorem Equation4512_5292_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5292 : Equation5292 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X0)) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h5292 X0 (X0 ◇ (X1 ◇ X1)) X3 X1]
    conv => enter [1]; rw [← h5292 X3 (X0 ◇ (X1 ◇ X1)) X2 (X0 ◇ (X1 ◇ X1))]
  have l1 : ∀ X2 X0 X1 X3 X4 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X4)))))) = X3 := by
    intro X2 X0 X1 X3 X4
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X4 ◇ X4)))]
    conv => enter [1]; rw [← h5292 X3 X2 (X0 ◇ X1) X4]
  have l2 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ (X2 ◇ (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X4 ◇ X4)))))) = X0 := by
    intro X1 X2 X3 X0 X4
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X4 ◇ X4))))]
    conv => enter [1]; rw [← h5292 X0 (X1 ◇ X2) X3 X4]
  have l3 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X4 ◇ X4))))))) = X0 := by
    intro X1 X2 X3 X0 X4
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 X2 (X0 ◇ (X4 ◇ X4))]
    conv => enter [1]; rw [l2 X1 X2 X3 X0 X4]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) (X2 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X1 X1 X1 X0 X1]
    conv => enter [1]; rw [l3 X1 X1 X1 X0 X1]
  have l6 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X1 (X2 ◇ X0)]
    conv => enter [1]; rw [l4 X0 X1 X2 X3]
  have l7 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [← l5 X0 (X1 ◇ (X1 ◇ (X2 ◇ X0)))]
    conv => enter [1]; rw [l6 X0 X1 X2 X3]
  have l8 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ X0)) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2]; rw [← l5 X1 (X2 ◇ X0)]
    conv => enter [1]; rw [l7 X1 X2 X0 X3]
  have l9 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = X3 := by
    intro X2 X0 X3
    conv => enter [1, 2]; rw [← l5 X2 X0]
    conv => enter [1]; rw [l8 X2 X2 X0 X3]
  have l10 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l9 X0 (X0 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5292 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation2_implies_Equation5293 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5293 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (x ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5293_implies_Equation2 (G : Type*) [Magma G] (h5293 : Equation5293 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5293 X0 X2 X1 X1 X1]
    conv => enter [1]; rw [← h5293 X2 X1 X2 X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5293 X3 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5295 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5295 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (y ◇ (x ◇ y)))))]

theorem Equation4512_5295_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5295 : Equation5295 G) : Equation2 G := by
  have l0 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2)))))) = X3 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ (X3 ◇ X2)))]
    conv => enter [1]; rw [← h5295 X3 X2 (X0 ◇ X1)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5295 X0 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X0]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2, 2]; rw [← l1 X2 X0]
    conv => enter [1]; rw [← h5295 X2 X0 X1]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l1 X0 (X1 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l2 X0 X1 X2]
  have l4 : ∀ X0 X2 : G, (X0 ◇ (X0 ◇ X0)) = X2 := by
    intro X0 X2
    conv => enter [1, 2, 2]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l3 X0 X0 X2]
  have l5 : ∀ X0 X2 : G, (X0 ◇ X0) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l4 X0 X2]
  have l6 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l5 X0 X2]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation2_implies_Equation5296 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5296 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (y ◇ (x ◇ z)))))]

theorem Equation4512_5296_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5296 : Equation5296 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h5296 X0 X1 X1]
    conv => enter [1]; rw [← h5296 X1 X1 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4512 X1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [l2 X0 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [← h5296 X0 X0 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h5296 X0 X0 (X1 ◇ (X0 ◇ X1))]
  have l6 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h5296 X1 X0 (X0 ◇ X1)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 (X0 ◇ X1) (X0 ◇ X0)]
    conv => enter [1]; rw [l5 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [l8 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l7 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l9 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l4 X0]
    conv => enter [1]; rw [l10 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l11 X1 X0]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l4 X0]
    conv => enter [1]; rw [← h5296 X0 X1 X0]
  have l15 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l13 X0 (X1 ◇ (X0 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l14 X0 X1]
  intro x y
  conv => enter [1]; rw [l15 x y]

@[equational_result]
theorem Equation2_implies_Equation5297 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5297 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (y ◇ (x ◇ w)))))]

theorem Equation4512_5297_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5297 : Equation5297 G) : Equation2 G := by
  have l0 : ∀ X2 X0 X1 X3 X4 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))))) = X3 := by
    intro X2 X0 X1 X3 X4
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ (X3 ◇ X4)))]
    conv => enter [1]; rw [← h5297 X3 X2 (X0 ◇ X1) X4]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5297 X0 X1 X1 X1]
    conv => enter [1]; rw [← h5297 X1 X1 X1 (X0 ◇ X1)]
  have l2 : ∀ X2 X3 : G, X2 = X3 := by
    intro X2 X3
    conv => enter [1]; rw [← l1 X2 (X2 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X2)))))]
    conv => enter [1]; rw [l0 X2 X2 X2 X3 X2]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation5299 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5299 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5299_implies_Equation2 (G : Type*) [Magma G] (h5299 : Equation5299 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5299 X0 X0 X0]
    conv => enter [1]; rw [← h5299 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5300 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5300 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5300_implies_Equation2 (G : Type*) [Magma G] (h5300 : Equation5300 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5300 X0 X0 X0]
    conv => enter [1]; rw [← h5300 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5301 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5301 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (y ◇ (y ◇ w)))))]

@[equational_result]
theorem Equation5301_implies_Equation2 (G : Type*) [Magma G] (h5301 : Equation5301 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5301 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5301 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5303 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5303 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (y ◇ (z ◇ y)))))]

@[equational_result]
theorem Equation5303_implies_Equation2 (G : Type*) [Magma G] (h5303 : Equation5303 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5303 X0 X0 X0]
    conv => enter [1]; rw [← h5303 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5304 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5304 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5304_implies_Equation2 (G : Type*) [Magma G] (h5304 : Equation5304 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5304 X0 X0 X0]
    conv => enter [1]; rw [← h5304 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5305 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5305 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5305_implies_Equation2 (G : Type*) [Magma G] (h5305 : Equation5305 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5305 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5305 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5307 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5307 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (y ◇ (w ◇ y)))))]

@[equational_result]
theorem Equation5307_implies_Equation2 (G : Type*) [Magma G] (h5307 : Equation5307 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5307 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5307 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5308 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5308 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (y ◇ (w ◇ z)))))]

@[equational_result]
theorem Equation5308_implies_Equation2 (G : Type*) [Magma G] (h5308 : Equation5308 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5308 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5308 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5309 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5309 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (y ◇ (w ◇ w)))))]

@[equational_result]
theorem Equation5309_implies_Equation2 (G : Type*) [Magma G] (h5309 : Equation5309 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5309 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5309 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5310 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5310 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (y ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5310_implies_Equation2 (G : Type*) [Magma G] (h5310 : Equation5310 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5310 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5310 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5312 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5312 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (z ◇ (x ◇ y)))))]

theorem Equation4512_5312_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5312 : Equation5312 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h5312 (X0 ◇ X1) (X0 ◇ X1) X1]
    conv => enter [1, 2]; rw [← h5312 X0 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h5312 X1 X0 X0]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X2)))]
    conv => enter [1]; rw [l2 (X0 ◇ X1) X2]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h5312 X0 X1 X1]
  have l5 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l4 X0 (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ X2))))]
    conv => enter [1]; rw [l3 X0 X0 X2]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation2_implies_Equation5313 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5313 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (z ◇ (x ◇ z)))))]

theorem Equation4512_5313_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5313 : Equation5313 G) : Equation2 G := by
  have l0 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))))))) = X3 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ (X0 ◇ X1))))]
    conv => enter [1]; rw [← h5313 X3 X2 (X0 ◇ X1)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5313 X0 (X0 ◇ X1) X1]
    conv => enter [1]; rw [← h5313 X1 X1 (X0 ◇ X1)]
  have l2 : ∀ X2 X3 : G, X2 = X3 := by
    intro X2 X3
    conv => enter [1]; rw [← l1 X2 (X2 ◇ (X2 ◇ (X2 ◇ ((X2 ◇ X2) ◇ (X3 ◇ (X2 ◇ X2))))))]
    conv => enter [1]; rw [l0 X2 X2 X2 X3]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation5314 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5314 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (z ◇ (x ◇ w)))))]

theorem Equation4512_5314_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5314 : Equation5314 G) : Equation2 G := by
  have l0 : ∀ X2 X0 X1 X3 X4 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X4)))))) = X3 := by
    intro X2 X0 X1 X3 X4
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X4)))]
    conv => enter [1]; rw [← h5314 X3 X2 (X0 ◇ X1) X4]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5314 X0 X1 X1 X1]
    conv => enter [1]; rw [← h5314 X1 X1 X1 (X0 ◇ X1)]
  have l2 : ∀ X2 X3 : G, X2 = X3 := by
    intro X2 X3
    conv => enter [1]; rw [← l1 X2 (X2 ◇ (X2 ◇ (X2 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X2)))))]
    conv => enter [1]; rw [l0 X2 X2 X2 X3 X2]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation5316 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5316 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (z ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5316_implies_Equation2 (G : Type*) [Magma G] (h5316 : Equation5316 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5316 X0 X0 X0]
    conv => enter [1]; rw [← h5316 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5317 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5317 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (z ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5317_implies_Equation2 (G : Type*) [Magma G] (h5317 : Equation5317 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5317 X0 X0 X0]
    conv => enter [1]; rw [← h5317 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5318 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5318 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (z ◇ (y ◇ w)))))]

@[equational_result]
theorem Equation5318_implies_Equation2 (G : Type*) [Magma G] (h5318 : Equation5318 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5318 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5318 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5320 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5320 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (z ◇ (z ◇ y)))))]

@[equational_result]
theorem Equation5320_implies_Equation2 (G : Type*) [Magma G] (h5320 : Equation5320 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5320 X0 X0 X0]
    conv => enter [1]; rw [← h5320 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5321 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5321 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (z ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5321_implies_Equation2 (G : Type*) [Magma G] (h5321 : Equation5321 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5321 X0 X0 X0]
    conv => enter [1]; rw [← h5321 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5322 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5322 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (z ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5322_implies_Equation2 (G : Type*) [Magma G] (h5322 : Equation5322 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5322 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5322 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5324 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5324 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (z ◇ (w ◇ y)))))]

@[equational_result]
theorem Equation5324_implies_Equation2 (G : Type*) [Magma G] (h5324 : Equation5324 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5324 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5324 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5325 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5325 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (z ◇ (w ◇ z)))))]

@[equational_result]
theorem Equation5325_implies_Equation2 (G : Type*) [Magma G] (h5325 : Equation5325 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5325 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5325 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5326 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5326 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (z ◇ (w ◇ w)))))]

@[equational_result]
theorem Equation5326_implies_Equation2 (G : Type*) [Magma G] (h5326 : Equation5326 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5326 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5326 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5327 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5327 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5327_implies_Equation2 (G : Type*) [Magma G] (h5327 : Equation5327 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5327 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5327 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5329 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5329 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (w ◇ (x ◇ y)))))]

theorem Equation4512_5329_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5329 : Equation5329 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X2 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h5329 (X0 ◇ X1) X2 X3 X4]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X1 X2 X3 X0 X4 X5 : G, ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X5 ◇ X0)))) = X2 := by
    intro X1 X2 X3 X0 X4 X5
    conv => enter [1, 2, 2, 2, 2]; rw [h5329 X0 X2 X1 X3]
    conv => enter [1]; rw [← h5329 X2 (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) X4 X5]
  have l2 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) = X2 := by
    intro X3 X4 X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h5329 X2 X3 X4 (X0 ◇ X1)]
  have l3 : ∀ X1 X2 X3 X0 X4 X5 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X2))) ◇ (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X5 ◇ X0))))) = X2 := by
    intro X1 X2 X3 X0 X4 X5
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X3 ◇ (X0 ◇ X2))) (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X5 ◇ X0)))]
    conv => enter [1]; rw [l1 X1 X2 X3 X0 X4 X5]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [l2 X0 X0 X0 X0 X1]
  have l5 : ∀ X1 X2 X3 X0 X4 X5 : G, (X1 ◇ (X2 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X5 ◇ X0)))))) = X2 := by
    intro X1 X2 X3 X0 X4 X5
    conv => enter [1, 2]; rw [h4512 X2 (X3 ◇ (X0 ◇ X2)) (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X5 ◇ X0)))]
    conv => enter [1]; rw [l3 X1 X2 X3 X0 X4 X5]
  have l6 : ∀ X2 X3 X0 X4 X1 X5 : G, (X2 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X5 ◇ X0))))) = X2 := by
    intro X2 X3 X0 X4 X1 X5
    conv => enter [1]; rw [← l4 X1 (X2 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X5 ◇ X0)))))]
    conv => enter [1]; rw [l5 X1 X2 X3 X0 X4 X5]
  have l7 : ∀ X3 X0 X2 X4 X1 X5 : G, ((X3 ◇ (X0 ◇ X2)) ◇ (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X5 ◇ X0)))) = X2 := by
    intro X3 X0 X2 X4 X1 X5
    conv => enter [1]; rw [← l4 X2 ((X3 ◇ (X0 ◇ X2)) ◇ (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X5 ◇ X0))))]
    conv => enter [1]; rw [l6 X2 X3 X0 X4 X1 X5]
  have l8 : ∀ X3 X0 X2 X4 X1 X5 : G, (X3 ◇ ((X0 ◇ X2) ◇ (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X5 ◇ X0))))) = X2 := by
    intro X3 X0 X2 X4 X1 X5
    conv => enter [1]; rw [h4512 X3 (X0 ◇ X2) (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X5 ◇ X0)))]
    conv => enter [1]; rw [l7 X3 X0 X2 X4 X1 X5]
  have l9 : ∀ X0 X2 X4 X1 X3 X5 : G, ((X0 ◇ X2) ◇ (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X5 ◇ X0)))) = X2 := by
    intro X0 X2 X4 X1 X3 X5
    conv => enter [1]; rw [← l4 X3 ((X0 ◇ X2) ◇ (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X5 ◇ X0))))]
    conv => enter [1]; rw [l8 X3 X0 X2 X4 X1 X5]
  have l10 : ∀ X0 X2 X4 X1 X3 X5 : G, (X0 ◇ (X2 ◇ (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X5 ◇ X0))))) = X2 := by
    intro X0 X2 X4 X1 X3 X5
    conv => enter [1]; rw [h4512 X0 X2 (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X5 ◇ X0)))]
    conv => enter [1]; rw [l9 X0 X2 X4 X1 X3 X5]
  have l11 : ∀ X2 X4 X1 X3 X0 X5 : G, (X2 ◇ (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X5 ◇ X0)))) = X2 := by
    intro X2 X4 X1 X3 X0 X5
    conv => enter [1]; rw [← l4 X0 (X2 ◇ (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X5 ◇ X0))))]
    conv => enter [1]; rw [l10 X0 X2 X4 X1 X3 X5]
  have l12 : ∀ X4 X1 X2 X3 X0 X5 : G, (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X5 ◇ X0))) = X2 := by
    intro X4 X1 X2 X3 X0 X5
    conv => enter [1]; rw [← l4 X2 (X4 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X5 ◇ X0)))]
    conv => enter [1]; rw [l11 X2 X4 X1 X3 X0 X5]
  have l13 : ∀ X1 X2 X3 X0 X5 : G, ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X5 ◇ X0)) = X2 := by
    intro X1 X2 X3 X0 X5
    conv => enter [1]; rw [← l4 X1 ((X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ X2)))) ◇ (X5 ◇ X0))]
    conv => enter [1]; rw [l12 X1 X1 X2 X3 X0 X5]
  have l14 : ∀ X1 X2 X3 X0 X5 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X0 ◇ X2))) ◇ (X5 ◇ X0))) = X2 := by
    intro X1 X2 X3 X0 X5
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X3 ◇ (X0 ◇ X2))) (X5 ◇ X0)]
    conv => enter [1]; rw [l13 X1 X2 X3 X0 X5]
  have l15 : ∀ X2 X3 X0 X5 : G, ((X2 ◇ (X3 ◇ (X0 ◇ X2))) ◇ (X5 ◇ X0)) = X2 := by
    intro X2 X3 X0 X5
    conv => enter [1]; rw [← l4 X2 ((X2 ◇ (X3 ◇ (X0 ◇ X2))) ◇ (X5 ◇ X0))]
    conv => enter [1]; rw [l14 X2 X2 X3 X0 X5]
  have l16 : ∀ X2 X3 X0 X5 : G, (X2 ◇ ((X3 ◇ (X0 ◇ X2)) ◇ (X5 ◇ X0))) = X2 := by
    intro X2 X3 X0 X5
    conv => enter [1]; rw [h4512 X2 (X3 ◇ (X0 ◇ X2)) (X5 ◇ X0)]
    conv => enter [1]; rw [l15 X2 X3 X0 X5]
  have l17 : ∀ X3 X0 X2 X5 : G, ((X3 ◇ (X0 ◇ X2)) ◇ (X5 ◇ X0)) = X2 := by
    intro X3 X0 X2 X5
    conv => enter [1]; rw [← l4 X2 ((X3 ◇ (X0 ◇ X2)) ◇ (X5 ◇ X0))]
    conv => enter [1]; rw [l16 X2 X3 X0 X5]
  have l18 : ∀ X3 X0 X2 X5 : G, (X3 ◇ ((X0 ◇ X2) ◇ (X5 ◇ X0))) = X2 := by
    intro X3 X0 X2 X5
    conv => enter [1]; rw [h4512 X3 (X0 ◇ X2) (X5 ◇ X0)]
    conv => enter [1]; rw [l17 X3 X0 X2 X5]
  have l19 : ∀ X0 X2 X5 : G, ((X0 ◇ X2) ◇ (X5 ◇ X0)) = X2 := by
    intro X0 X2 X5
    conv => enter [1]; rw [← l4 X0 ((X0 ◇ X2) ◇ (X5 ◇ X0))]
    conv => enter [1]; rw [l18 X0 X0 X2 X5]
  have l20 : ∀ X0 X2 X5 : G, (X0 ◇ (X2 ◇ (X5 ◇ X0))) = X2 := by
    intro X0 X2 X5
    conv => enter [1]; rw [h4512 X0 X2 (X5 ◇ X0)]
    conv => enter [1]; rw [l19 X0 X2 X5]
  have l21 : ∀ X2 X5 X0 : G, (X2 ◇ (X5 ◇ X0)) = X2 := by
    intro X2 X5 X0
    conv => enter [1]; rw [← l4 X0 (X2 ◇ (X5 ◇ X0))]
    conv => enter [1]; rw [l20 X0 X2 X5]
  have l22 : ∀ X5 X0 X2 : G, (X5 ◇ X0) = X2 := by
    intro X5 X0 X2
    conv => enter [1]; rw [← l4 X2 (X5 ◇ X0)]
    conv => enter [1]; rw [l21 X2 X5 X0]
  have l23 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l22 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X4 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5329 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l23 x y]

@[equational_result]
theorem Equation2_implies_Equation5330 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5330 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (w ◇ (x ◇ z)))))]

@[equational_result]
theorem Equation5330_implies_Equation2 (G : Type*) [Magma G] (h5330 : Equation5330 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5330 X0 (X0 ◇ X1) X1 X2]
    conv => enter [1]; rw [← h5330 X2 X1 (X0 ◇ X1) (X0 ◇ X1)]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X4 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5330 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5331 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5331 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (w ◇ (x ◇ w)))))]

@[equational_result]
theorem Equation5331_implies_Equation2 (G : Type*) [Magma G] (h5331 : Equation5331 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5331 X0 (X0 ◇ X2) X1 X2]
    conv => enter [1]; rw [← h5331 X2 X1 (X0 ◇ X2) (X0 ◇ X2)]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X4 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5331 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5332 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5332 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (w ◇ (x ◇ u)))))]

@[equational_result]
theorem Equation5332_implies_Equation2 (G : Type*) [Magma G] (h5332 : Equation5332 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X3 : G, (X1 ◇ X0) = X3 := by
    intro X1 X0 X3
    conv => enter [1, 2]; rw [h5332 X0 X1 X1 X3 X1]
    conv => enter [1]; rw [← h5332 X3 X1 X1 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X4 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5332 X4 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5334 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5334 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (w ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5334_implies_Equation2 (G : Type*) [Magma G] (h5334 : Equation5334 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5334 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5334 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5335 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5335 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (w ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5335_implies_Equation2 (G : Type*) [Magma G] (h5335 : Equation5335 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5335 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5335 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5336 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5336 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (w ◇ (y ◇ w)))))]

@[equational_result]
theorem Equation5336_implies_Equation2 (G : Type*) [Magma G] (h5336 : Equation5336 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5336 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5336 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5337 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5337 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (w ◇ (y ◇ u)))))]

@[equational_result]
theorem Equation5337_implies_Equation2 (G : Type*) [Magma G] (h5337 : Equation5337 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5337 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5337 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5339 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5339 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (w ◇ (z ◇ y)))))]

@[equational_result]
theorem Equation5339_implies_Equation2 (G : Type*) [Magma G] (h5339 : Equation5339 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5339 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5339 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5340 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5340 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (w ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5340_implies_Equation2 (G : Type*) [Magma G] (h5340 : Equation5340 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5340 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5340 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5341 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5341 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (w ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5341_implies_Equation2 (G : Type*) [Magma G] (h5341 : Equation5341 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5341 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5341 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5342 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5342 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (w ◇ (z ◇ u)))))]

@[equational_result]
theorem Equation5342_implies_Equation2 (G : Type*) [Magma G] (h5342 : Equation5342 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5342 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5342 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5344 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5344 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (w ◇ (w ◇ y)))))]

@[equational_result]
theorem Equation5344_implies_Equation2 (G : Type*) [Magma G] (h5344 : Equation5344 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5344 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5344 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5345 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5345 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (w ◇ (w ◇ z)))))]

@[equational_result]
theorem Equation5345_implies_Equation2 (G : Type*) [Magma G] (h5345 : Equation5345 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5345 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5345 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5346 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5346 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (w ◇ (w ◇ w)))))]

@[equational_result]
theorem Equation5346_implies_Equation2 (G : Type*) [Magma G] (h5346 : Equation5346 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5346 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5346 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5347 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5347 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (w ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5347_implies_Equation2 (G : Type*) [Magma G] (h5347 : Equation5347 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5347 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5347 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5349 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5349 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (w ◇ (u ◇ y)))))]

@[equational_result]
theorem Equation5349_implies_Equation2 (G : Type*) [Magma G] (h5349 : Equation5349 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5349 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5349 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5350 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5350 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (w ◇ (u ◇ z)))))]

@[equational_result]
theorem Equation5350_implies_Equation2 (G : Type*) [Magma G] (h5350 : Equation5350 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5350 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5350 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5351 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5351 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (w ◇ (u ◇ w)))))]

@[equational_result]
theorem Equation5351_implies_Equation2 (G : Type*) [Magma G] (h5351 : Equation5351 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5351 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5351 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5352 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5352 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (w ◇ (u ◇ u)))))]

@[equational_result]
theorem Equation5352_implies_Equation2 (G : Type*) [Magma G] (h5352 : Equation5352 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5352 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5352 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5353 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5353 G := by
  intro x y z w u v
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (w ◇ (u ◇ v)))))]

@[equational_result]
theorem Equation5353_implies_Equation2 (G : Type*) [Magma G] (h5353 : Equation5353 G) : Equation2 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5353 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5353 X6 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5355 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5355 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (x ◇ (x ◇ y)))))]

theorem Equation4512_5355_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5355 : Equation5355 G) : Equation2 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h5355 X0 X0 X0]
    conv => enter [1]; rw [← h5355 X0 (X0 ◇ X0) X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 X0 X0]
    conv => enter [1]; rw [l0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h5355 X0 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h5355 X0 X1 (X0 ◇ (X0 ◇ X1))]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l2 (X1 ◇ (X0 ◇ (X0 ◇ X1))) X1]
    conv => enter [1, 2]; rw [← h5355 X0 X1 X1]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [l2 X0 X0]
  have l6 : ∀ X1 X0 X2 : G, ((X1 ◇ (X1 ◇ X0)) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h5355 X0 (X1 ◇ (X1 ◇ X0)) X2]
  have l7 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [← l2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X0)) X2]
  have l8 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l7 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ X0) X2]
  have l9 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0))))) = X0 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X1 ◇ X0) (X2 ◇ (X2 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l6 X1 X0 X2]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X1)) X0]
  have l11 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l8 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X0 X2]
  have l12 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))))) = X0 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4512 X1 X0 (X2 ◇ (X2 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l9 X1 X0 X2]
  have l13 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l10 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X0]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l11 X0 X0 X1]
    conv => enter [1]; rw [l12 X1 X0 X1]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l13 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X0]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l5 X0]
    conv => enter [1]; rw [l14 X1 X0]
  have l17 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = (X1 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l15 X1 X0]
    conv => enter [1]; rw [← l11 X1 X0 X0]
  have l18 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l17 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  have l19 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) = X1 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l18 X2 (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))]
    conv => enter [1]; rw [← h5355 X1 X2 X0]
  have l20 : ∀ X1 X2 : G, (X1 ◇ (X1 ◇ X2)) = X1 := by
    intro X1 X2
    conv => enter [1, 2, 2]; rw [← l16 X1 X2]
    conv => enter [1]; rw [l19 X1 X1 X2]
  have l21 : ∀ X1 X2 : G, (X1 ◇ X2) = X1 := by
    intro X1 X2
    conv => enter [1, 2]; rw [← l18 X1 X2]
    conv => enter [1]; rw [l20 X1 X2]
  have l22 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l21 X0 (X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0))))]
    conv => enter [1]; rw [← h5355 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l22 x y]

@[equational_result]
theorem Equation2_implies_Equation5356 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5356 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (x ◇ (x ◇ z)))))]

theorem Equation4512_5356_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5356 : Equation5356 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [h5356 X0 (X0 ◇ (X0 ◇ X2)) X2]
    conv => enter [1]; rw [← h5356 X2 X1 (X0 ◇ (X0 ◇ X2))]
  have l1 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X3)))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X3))))]
    conv => enter [1]; rw [← h5356 X0 (X1 ◇ X2) X3]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5356 X0 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X1 X0]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X0))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4512 X0 (X0 ◇ X2) X0]
    conv => enter [1]; rw [l0 X1 X0 X2]
  have l4 : ∀ X0 X2 : G, (X0 ◇ ((X0 ◇ X2) ◇ X0)) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [← l2 X0 ((X0 ◇ X2) ◇ X0)]
    conv => enter [1]; rw [l3 X0 X0 X2]
  have l5 : ∀ X0 X2 : G, ((X0 ◇ X2) ◇ X0) = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l2 X0 ((X0 ◇ X2) ◇ X0)]
    conv => enter [1]; rw [l4 X0 X2]
  have l6 : ∀ X0 X2 : G, (X0 ◇ (X2 ◇ X0)) = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h4512 X0 X2 X0]
    conv => enter [1]; rw [l5 X0 X2]
  have l7 : ∀ X2 X0 : G, (X2 ◇ X0) = X2 := by
    intro X2 X0
    conv => enter [1]; rw [← l2 X0 (X2 ◇ X0)]
    conv => enter [1]; rw [l6 X0 X2]
  have l8 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l7 X0 (X0 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0))))]
    conv => enter [1]; rw [← h5356 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l8 x y]

@[equational_result]
theorem Equation2_implies_Equation5357 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5357 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (x ◇ (x ◇ w)))))]

@[equational_result]
theorem Equation5357_implies_Equation2 (G : Type*) [Magma G] (h5357 : Equation5357 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ X0)) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2]; rw [h5357 X0 X2 X3 X1]
    conv => enter [1]; rw [← h5357 X3 X1 X2 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5357 X0 X0 X0 X1]
    conv => enter [1]; rw [← h5357 X0 X1 X0 (X0 ◇ X1)]
  have l2 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = X3 := by
    intro X2 X0 X3
    conv => enter [1, 2]; rw [← l1 X2 X0]
    conv => enter [1]; rw [l0 X2 X2 X0 X3]
  have l3 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l2 X0 (X0 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5357 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation5359 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5359 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (x ◇ (y ◇ y)))))]

theorem Equation4512_5359_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5359 : Equation5359 G) : Equation2 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h5359 (X0 ◇ X0) X0 X0]
    conv => enter [1]; rw [← h5359 X0 (X0 ◇ X0) X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h5359 X0 X0 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l2 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [← h5359 X0 X1 (X0 ◇ (X1 ◇ X1))]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0]
    conv => enter [1]; rw [l1 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l4 X1]
    conv => enter [1]; rw [l3 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l4 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [← h5359 X0 X1 (X0 ◇ (X1 ◇ X1))]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l4 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1, 2]; rw [l5 X1 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ X1))))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ X1) (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l6 X1 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l4 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4512 X1 X1 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l9 X1 X0]
  have l12 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l10 X0 (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))]
    conv => enter [1]; rw [l11 X0 X1]
  intro x y
  conv => enter [1]; rw [l12 x y]

@[equational_result]
theorem Equation2_implies_Equation5360 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5360 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (x ◇ (y ◇ z)))))]

theorem Equation4512_5360_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5360 : Equation5360 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h5360 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [h5360 X0 X2 X1]
    conv => enter [1]; rw [← h5360 X2 X1 (X1 ◇ (X0 ◇ (X2 ◇ X1)))]
  have l2 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3)))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))))]
    conv => enter [1]; rw [← h5360 X0 (X1 ◇ X2) X3]
  have l3 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l2 X1 X2 X3 X0]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0)))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4512 X1 (X0 ◇ (X2 ◇ X1)) ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0)]
    conv => enter [1]; rw [l1 X1 X0 X2]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l0 X0 X1 X1 X1]
    conv => enter [1]; rw [l3 X1 X1 X1 X0]
  have l6 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0))))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [h4512 X0 (X2 ◇ X1) ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0)]
    conv => enter [1]; rw [l4 X1 X0 X2]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0)))))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [h4512 X2 X1 ((X1 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X0)]
    conv => enter [1]; rw [l6 X1 X0 X2]
  have l8 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X0))))))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X1 (X0 ◇ (X2 ◇ X1)) X0]
    conv => enter [1]; rw [l7 X1 X0 X2]
  have l9 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X0)))))))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 (X2 ◇ X1) X0]
    conv => enter [1]; rw [l8 X1 X0 X2]
  have l10 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1))))))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [← l5 X0 (X2 ◇ X1)]
    conv => enter [1]; rw [l9 X1 X0 X2]
  have l11 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X2))))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← l5 X1 X2]
    conv => enter [1]; rw [l10 X1 X0 X2]
  have l12 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X0 ◇ X1))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [← l5 X2 X1]
    conv => enter [1]; rw [l11 X1 X0 X2]
  have l13 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [← l5 X1 X0]
    conv => enter [1]; rw [l12 X1 X0 X2]
  have l14 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l13 X0 (X0 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5360 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l14 x y]

@[equational_result]
theorem Equation2_implies_Equation5361 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5361 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (x ◇ (y ◇ w)))))]

theorem Equation4512_5361_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5361 : Equation5361 G) : Equation2 G := by
  have l0 : ∀ X3 X0 X1 X2 X4 : G, (X3 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))))) = X2 := by
    intro X3 X0 X1 X2 X4
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
    conv => enter [1]; rw [← h5361 X2 X3 (X0 ◇ X1) X4]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h5361 X0 X2 X1 X1]
    conv => enter [1]; rw [← h5361 X1 X1 X2 (X0 ◇ (X2 ◇ X1))]
  have l2 : ∀ X2 X3 : G, X2 = X3 := by
    intro X2 X3
    conv => enter [1]; rw [← l1 X2 (X2 ◇ X2) (X2 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X2))))]
    conv => enter [1]; rw [l0 X2 X2 X2 X3 X2]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation5363 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5363 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (x ◇ (z ◇ y)))))]

theorem Equation4512_5363_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5363 : Equation5363 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h5363 X0 X1 X1]
    conv => enter [1]; rw [← h5363 X1 (X0 ◇ (X1 ◇ X1)) X1]
  have l1 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h5363 X0 X0 X0]
    conv => enter [1]; rw [← h5363 X0 (X0 ◇ X0) X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 X0 X0]
    conv => enter [1]; rw [l1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) (X1 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2, 2]; rw [← l2 X0]
    conv => enter [1]; rw [← h5363 X0 X0 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l8 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0]
    conv => enter [1]; rw [l5 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l8 X0]
    conv => enter [1]; rw [← h5363 X1 X0 X0]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [h5363 (X0 ◇ X1) X1 X0]
    conv => enter [1, 2, 2, 2]; rw [l8 (X0 ◇ X1)]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1]; rw [l4 X1 X0]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l9 X0 X1]
  have l13 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l11 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l12 X0 X1]
  intro x y
  conv => enter [1]; rw [l13 x y]

@[equational_result]
theorem Equation2_implies_Equation5364 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5364 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (x ◇ (z ◇ z)))))]

theorem Equation4512_5364_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5364 : Equation5364 G) : Equation2 G := by
  have l0 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))))) = X2 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))]
    conv => enter [1]; rw [← h5364 X2 X3 (X0 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X3)))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X3 ◇ (X0 ◇ (X3 ◇ X3))))]
    conv => enter [1]; rw [← h5364 X0 (X1 ◇ X2) X3]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5364 X0 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X1 X0]
  have l3 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))))) = X2 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l0 X3 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [← l2 X0 (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))))]
    conv => enter [1]; rw [l3 X0 X0 X1 X2]
  have l5 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))))]
    conv => enter [1]; rw [l4 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X1 (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))))]
    conv => enter [1]; rw [l5 X1 X0 X2]
  have l7 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) = X2 := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))]
    conv => enter [1]; rw [l6 X0 X1 X2]
  have l8 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X2 := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l2 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l7 X1 X2 X0]
  have l9 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X2 ((X0 ◇ X1) ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l8 X2 X0 X1]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l9 X0 X1 X2]
  have l11 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X1)) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l10 X0 X1 X2]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l11 X1 X0 X2]
  have l13 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l12 X0 (X0 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5364 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l13 x y]

@[equational_result]
theorem Equation2_implies_Equation5365 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5365 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (x ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5365_implies_Equation2 (G : Type*) [Magma G] (h5365 : Equation5365 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h5365 X0 X2 X2 X1]
    conv => enter [1]; rw [← h5365 X2 X1 X2 (X0 ◇ (X2 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5365 X0 X0 X0 X1]
    conv => enter [1]; rw [← h5365 X0 X1 X0 (X0 ◇ X1)]
  have l2 : ∀ X2 X0 : G, (X2 ◇ X0) = X2 := by
    intro X2 X0
    conv => enter [1, 2]; rw [← l1 X2 X0]
    conv => enter [1]; rw [l0 X2 X2 X0]
  have l3 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l2 X0 (X0 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5365 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation5367 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5367 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (x ◇ (w ◇ y)))))]

@[equational_result]
theorem Equation5367_implies_Equation2 (G : Type*) [Magma G] (h5367 : Equation5367 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, ((X1 ◇ X2) ◇ X0) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h5367 X0 X2 X2 X1]
    conv => enter [1]; rw [← h5367 X2 (X1 ◇ X2) X2 X0]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 X0 (X0 ◇ (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))))]
    conv => enter [1]; rw [← h5367 X3 (X0 ◇ X0) X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5368 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5368 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (x ◇ (w ◇ z)))))]

theorem Equation4512_5368_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5368 : Equation5368 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X0)) = X3 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2, 2]; rw [h5368 X0 (X0 ◇ (X2 ◇ X3)) X3 X2]
    conv => enter [1]; rw [← h5368 X3 X1 (X0 ◇ (X2 ◇ X3)) X3]
  have l1 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X4 ◇ X3)))))) = X0 := by
    intro X1 X2 X3 X0 X4
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X3 ◇ (X0 ◇ (X4 ◇ X3))))]
    conv => enter [1]; rw [← h5368 X0 (X1 ◇ X2) X3 X4]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5368 X0 X1 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X1 X0 X1]
  have l3 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X0))) = X3 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2]; rw [h4512 X0 (X2 ◇ X3) X0]
    conv => enter [1]; rw [l0 X1 X0 X2 X3]
  have l4 : ∀ X0 X2 X3 : G, (X0 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := by
    intro X0 X2 X3
    conv => enter [1, 2]; rw [← l2 X0 ((X2 ◇ X3) ◇ X0)]
    conv => enter [1]; rw [l3 X0 X0 X2 X3]
  have l5 : ∀ X2 X3 X0 : G, ((X2 ◇ X3) ◇ X0) = X3 := by
    intro X2 X3 X0
    conv => enter [1]; rw [← l2 X0 ((X2 ◇ X3) ◇ X0)]
    conv => enter [1]; rw [l4 X0 X2 X3]
  have l6 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l2 (X0 ◇ X3) X0]
    conv => enter [1]; rw [l5 X0 X3 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation2_implies_Equation5369 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5369 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (x ◇ (w ◇ w)))))]

theorem Equation4512_5369_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5369 : Equation5369 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X0)))) = X3 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h5369 X0 (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1)))) X1 X1]
    conv => enter [1]; rw [← h5369 X3 X1 X2 (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))]
  have l1 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X4 ◇ X4)))))) = X0 := by
    intro X1 X2 X3 X0 X4
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X3 ◇ (X0 ◇ (X4 ◇ X4))))]
    conv => enter [1]; rw [← h5369 X0 (X1 ◇ X2) X3 X4]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5369 X0 X1 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X1 X0 X1]
  have l3 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0)))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2]; rw [← l2 X3 (X0 ◇ X0)]
    conv => enter [1]; rw [← h5369 X3 X1 X2 X0]
  have l4 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 X0 X0 X0]
    conv => enter [1]; rw [l3 X0 X0 X0 X3]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation2_implies_Equation5370 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5370 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (x ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5370_implies_Equation2 (G : Type*) [Magma G] (h5370 : Equation5370 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5370 X0 X2 X2 X1 X1]
    conv => enter [1]; rw [← h5370 X2 X1 X2 X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5370 X3 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5372 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5372 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (y ◇ (x ◇ y)))))]

theorem Equation4512_5372_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5372 : Equation5372 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h5372 (X1 ◇ (X0 ◇ X1)) (X1 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 2, 2]; rw [← h5372 X0 X1 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) X3]
    conv => enter [1, 1]; rw [← h5372 X0 X1 X2]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l1 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X2 ◇ (X1 ◇ (X0 ◇ X1))) X3]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X1) (X1 ◇ X0)]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X1 ◇ (X0 ◇ X1)) X3]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (X1 ◇ X0)]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l4 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ X1) X3]
  have l7 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l6 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X3]
  have l8 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X1)) = (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l5 X1 (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1))))]
    conv => enter [1, 2, 2, 2]; rw [← h5372 X0 X1 X2]
  have l9 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l5 X0 X0]
    conv => enter [1]; rw [← h5372 X0 X0 X0]
  have l10 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X1)) = (X1 ◇ (X2 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l8 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X2 (X2 ◇ (X1 ◇ (X0 ◇ X1))) (X1 ◇ X0)]
  have l11 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X1)) = (X1 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l10 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X1 ◇ (X0 ◇ X1)) (X1 ◇ X0)]
  have l12 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X1)) = (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l11 X1 X2 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ X1) (X1 ◇ X0)]
  have l13 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X1)) = ((X0 ◇ X1) ◇ X0) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l12 X1 X2 X0]
    conv => enter [1]; rw [← l7 (X0 ◇ X1) X0 X1 X2]
  have l14 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [← l13 X1 X2 X0]
  have l15 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X2 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l14 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X2 (X2 ◇ (X1 ◇ (X0 ◇ X1))) X1]
  have l16 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l15 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X1 ◇ (X0 ◇ X1)) X1]
  have l17 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X0)) = (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l16 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ X1) X1]
  have l18 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h5372 (X0 ◇ X1) X1 X0]
    conv => enter [1]; rw [← l17 X0 X1 X0]
  have l19 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [← l9 X0]
    conv => enter [1]; rw [← h5372 X0 X0 X0]
  have l20 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l18 X0 X0]
    conv => enter [1]; rw [l19 X0]
  have l21 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l20 X0]
    conv => enter [1]; rw [← h5372 X0 X0 X1]
  have l22 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l20 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l23 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l22 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [l21 X0 X1]
  have l24 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l20 X0]
    conv => enter [1]; rw [l23 X0 X1]
  have l25 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ X2))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l24 X2 (X0 ◇ X1)]
  have l26 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X2 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X0)))) = X0 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2]; rw [← l24 X0 X1]
    conv => enter [1]; rw [← h5372 X0 (X1 ◇ X0) X2]
  have l27 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X0))))) = X0 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 X0 (X2 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X0)))]
    conv => enter [1]; rw [l26 X1 X0 X2]
  have l28 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ X0) ◇ X0)))) = X0 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [l22 X2 ((X1 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [l27 X1 X0 X2]
  have l29 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l25 X0 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [l28 X1 X0 X1]
  have l30 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2, 2]; rw [← l29 X2 X0]
    conv => enter [1]; rw [← h5372 X2 X0 X1]
  have l31 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l29 X0 (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l30 X0 X1 X2]
  have l32 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [l22 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [l31 X1 X0 X2]
  have l33 : ∀ X0 X2 : G, (X0 ◇ X0) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [← l29 X0 X0]
    conv => enter [1]; rw [l32 X0 X0 X2]
  have l34 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l29 X0 X0]
    conv => enter [1]; rw [l33 X0 X2]
  intro x y
  conv => enter [1]; rw [l34 x y]

@[equational_result]
theorem Equation2_implies_Equation5373 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5373 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (y ◇ (x ◇ z)))))]

theorem Equation4512_5373_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5373 : Equation5373 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X3 X2 : G, (X0 ◇ X1) = (X3 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h5373 (X0 ◇ X1) X3 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2)))) X3]
    conv => enter [1, 1]; rw [← h5373 X0 X1 X2]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l1 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X2 ◇ (X1 ◇ (X0 ◇ X2))) X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X1 ◇ (X0 ◇ X2)) X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ X2) X3]
  have l5 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l4 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X2 X3]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ ((X0 ◇ X1) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 (X0 ◇ X1) X1 (X0 ◇ X1)]
    conv => enter [1, 2, 2]; rw [← h5373 X0 (X0 ◇ X1) X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = (X1 ◇ (X0 ◇ (X1 ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X0]
  have l8 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X1)) = (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X0)) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l7 X1 (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2))))]
    conv => enter [1, 2, 2]; rw [← h5373 X0 X1 X2]
  have l9 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [l7 X0 X0]
    conv => enter [1]; rw [← h5373 X0 X0 X0]
  have l10 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l7 X0 X0]
    conv => enter [1]; rw [l9 X0]
  have l11 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X1)) = (X1 ◇ (X2 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l8 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X2 (X2 ◇ (X1 ◇ (X0 ◇ X2))) X0]
  have l12 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [l7 X0 X0]
    conv => enter [1]; rw [l10 X0]
  have l13 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X1)) = (X1 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l11 X1 X2 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X1 ◇ (X0 ◇ X2)) X0]
  have l14 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X1)) = (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l13 X1 X2 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ X2) X0]
  have l15 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X1)) = (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))))) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l14 X1 X2 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X2 X0]
  have l16 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X1)) = (X0 ◇ X0) := by
    intro X1 X2 X0
    conv => enter [1]; rw [l15 X1 X2 X0]
    conv => enter [1]; rw [← l5 X0 X0 X1 X2]
  have l17 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X1))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l16 X1 X2 X0]
    conv => enter [1, 2]; rw [← h4512 X2 (X2 ◇ (X1 ◇ (X0 ◇ X2))) X1]
  have l18 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X1)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l17 X0 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X1 ◇ (X0 ◇ X2)) X1]
  have l19 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X1))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l18 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ X2) X1]
  have l20 : ∀ X0 X1 X2 : G, (X0 ◇ X0) = (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X1)))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l19 X0 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X2 X1]
  have l21 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1 X1 X0]
    conv => enter [1]; rw [← l20 X0 X1 X0]
  have l22 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l12 X0]
    conv => enter [1]; rw [← l7 X0 X0]
    conv => enter [1]; rw [l12 X0]
  have l23 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l12 X0]
    conv => enter [1]; rw [← h5373 X0 X1 (X0 ◇ X0)]
  have l24 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l21 X1 ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [l23 X1 X0]
  have l25 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l24 X1 X0]
    conv => enter [1]; rw [l22 X1]
  intro x y
  conv => enter [1]; rw [l25 x y]

@[equational_result]
theorem Equation2_implies_Equation5374 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5374 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (y ◇ (x ◇ w)))))]

theorem Equation4512_5374_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5374 : Equation5374 G) : Equation2 G := by
  have l0 : ∀ X2 X0 X1 X3 X4 : G, (X2 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X4)))))) = X3 := by
    intro X2 X0 X1 X3 X4
    conv => enter [1, 2]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ (X2 ◇ (X3 ◇ X4)))]
    conv => enter [1]; rw [← h5374 X3 X2 (X0 ◇ X1) X4]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5374 X0 X1 X1 X1]
    conv => enter [1]; rw [← h5374 X1 X1 X1 (X0 ◇ X1)]
  have l2 : ∀ X2 X3 : G, X2 = X3 := by
    intro X2 X3
    conv => enter [1]; rw [← l1 X2 (X2 ◇ (X2 ◇ ((X2 ◇ X2) ◇ (X2 ◇ (X3 ◇ X2)))))]
    conv => enter [1]; rw [l0 X2 X2 X2 X3 X2]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation5376 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5376 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5376_implies_Equation2 (G : Type*) [Magma G] (h5376 : Equation5376 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5376 X0 X0 X0]
    conv => enter [1]; rw [← h5376 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5377 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5377 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5377_implies_Equation2 (G : Type*) [Magma G] (h5377 : Equation5377 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5377 X0 X0 X0]
    conv => enter [1]; rw [← h5377 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5378 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5378 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (y ◇ (y ◇ w)))))]

@[equational_result]
theorem Equation5378_implies_Equation2 (G : Type*) [Magma G] (h5378 : Equation5378 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5378 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5378 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5380 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5380 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (y ◇ (z ◇ y)))))]

@[equational_result]
theorem Equation5380_implies_Equation2 (G : Type*) [Magma G] (h5380 : Equation5380 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5380 X0 X0 X0]
    conv => enter [1]; rw [← h5380 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5381 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5381 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5381_implies_Equation2 (G : Type*) [Magma G] (h5381 : Equation5381 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5381 X0 X0 X0]
    conv => enter [1]; rw [← h5381 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5382 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5382 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5382_implies_Equation2 (G : Type*) [Magma G] (h5382 : Equation5382 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5382 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5382 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5384 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5384 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (y ◇ (w ◇ y)))))]

@[equational_result]
theorem Equation5384_implies_Equation2 (G : Type*) [Magma G] (h5384 : Equation5384 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5384 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5384 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5385 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5385 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (y ◇ (w ◇ z)))))]

@[equational_result]
theorem Equation5385_implies_Equation2 (G : Type*) [Magma G] (h5385 : Equation5385 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5385 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5385 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5386 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5386 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (y ◇ (w ◇ w)))))]

@[equational_result]
theorem Equation5386_implies_Equation2 (G : Type*) [Magma G] (h5386 : Equation5386 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5386 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5386 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5387 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5387 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (y ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5387_implies_Equation2 (G : Type*) [Magma G] (h5387 : Equation5387 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5387 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5387 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5389 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5389 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (z ◇ (x ◇ y)))))]

theorem Equation4512_5389_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5389 : Equation5389 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h5389 X0 X1 X1]
    conv => enter [1]; rw [← h5389 X1 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 X2 : G, ((X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5389 X0 X2 X1]
    conv => enter [1]; rw [l1 (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) X2]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 (X0 ◇ X1) (X0 ◇ X1)]
    conv => enter [1]; rw [← h5389 X0 X1 (X0 ◇ X1)]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l3 X1 X0]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0)) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X1 ◇ (X0 ◇ X2))) X0]
    conv => enter [1]; rw [l2 X1 X0 X2]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 (X0 ◇ X1) X1]
    conv => enter [1]; rw [l6 X1 X0]
  have l9 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4512 X1 (X1 ◇ (X0 ◇ X2)) X0]
    conv => enter [1]; rw [l7 X1 X0 X2]
  have l10 : ∀ X1 X2 : G, X1 = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l8 X1 ((X1 ◇ (X1 ◇ X2)) ◇ X1)]
    conv => enter [1]; rw [l9 X1 X1 X2]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation2_implies_Equation5390 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5390 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (z ◇ (x ◇ z)))))]

theorem Equation4512_5390_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5390 : Equation5390 G) : Equation2 G := by
  have l0 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))))) = X2 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))]
    conv => enter [1]; rw [← h5390 X2 X3 (X0 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X3)))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X3))))]
    conv => enter [1]; rw [← h5390 X0 (X1 ◇ X2) X3]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5390 X0 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X1 X0]
  have l3 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))))))) = X2 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l0 X3 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [← l2 X0 (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))))]
    conv => enter [1]; rw [l3 X0 X0 X1 X2]
  have l5 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))))) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))))]
    conv => enter [1]; rw [l4 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X1 (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))))]
    conv => enter [1]; rw [l5 X1 X0 X2]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l2 X0 (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))))]
    conv => enter [1]; rw [l6 X0 X1 X2]
  have l8 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X1 ((X0 ◇ X1) ◇ (X2 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l7 X1 X0 X2]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l8 X0 X1 X2]
  have l10 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X2 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l9 X0 X1 X2]
  have l11 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X2 := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l2 X1 (X2 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l10 X1 X2 X0]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X2 (X0 ◇ X1)]
    conv => enter [1]; rw [l11 X2 X0 X1]
  have l13 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l12 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5390 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l13 x y]

@[equational_result]
theorem Equation2_implies_Equation5391 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5391 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (z ◇ (x ◇ w)))))]

@[equational_result]
theorem Equation5391_implies_Equation2 (G : Type*) [Magma G] (h5391 : Equation5391 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5391 X0 X2 X2 X1]
    conv => enter [1]; rw [← h5391 X2 X1 X2 (X0 ◇ X1)]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5391 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5393 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5393 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (z ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5393_implies_Equation2 (G : Type*) [Magma G] (h5393 : Equation5393 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5393 X0 X0 X0]
    conv => enter [1]; rw [← h5393 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5394 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5394 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (z ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5394_implies_Equation2 (G : Type*) [Magma G] (h5394 : Equation5394 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5394 X0 X0 X0]
    conv => enter [1]; rw [← h5394 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5395 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5395 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (z ◇ (y ◇ w)))))]

@[equational_result]
theorem Equation5395_implies_Equation2 (G : Type*) [Magma G] (h5395 : Equation5395 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5395 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5395 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5397 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5397 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (z ◇ (z ◇ y)))))]

@[equational_result]
theorem Equation5397_implies_Equation2 (G : Type*) [Magma G] (h5397 : Equation5397 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5397 X0 X0 X0]
    conv => enter [1]; rw [← h5397 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5398 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5398 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (z ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5398_implies_Equation2 (G : Type*) [Magma G] (h5398 : Equation5398 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5398 X0 X0 X0]
    conv => enter [1]; rw [← h5398 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5399 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5399 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (z ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5399_implies_Equation2 (G : Type*) [Magma G] (h5399 : Equation5399 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5399 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5399 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5401 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5401 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (z ◇ (w ◇ y)))))]

@[equational_result]
theorem Equation5401_implies_Equation2 (G : Type*) [Magma G] (h5401 : Equation5401 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5401 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5401 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5402 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5402 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (z ◇ (w ◇ z)))))]

@[equational_result]
theorem Equation5402_implies_Equation2 (G : Type*) [Magma G] (h5402 : Equation5402 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5402 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5402 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5403 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5403 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (z ◇ (w ◇ w)))))]

@[equational_result]
theorem Equation5403_implies_Equation2 (G : Type*) [Magma G] (h5403 : Equation5403 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5403 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5403 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5404 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5404 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5404_implies_Equation2 (G : Type*) [Magma G] (h5404 : Equation5404 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5404 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5404 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5406 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5406 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (w ◇ (x ◇ y)))))]

theorem Equation4512_5406_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5406 : Equation5406 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h5406 (X0 ◇ X1) X2 X3 X4]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) = X2 := by
    intro X3 X4 X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h5406 X2 X3 X4 (X0 ◇ X1)]
  have l2 : ∀ X1 X0 X2 X3 : G, ((X1 ◇ (X0 ◇ X2)) ◇ (X2 ◇ X0)) = X3 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2, 2]; rw [h5406 X0 X2 X3 X1]
    conv => enter [1]; rw [← h5406 X3 (X1 ◇ (X0 ◇ X2)) X2 X3]
  have l3 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ X2) ◇ (X2 ◇ X0))) = X3 := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X2) (X2 ◇ X0)]
    conv => enter [1]; rw [l2 X1 X0 X2 X3]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [l1 X0 X0 X0 X0 X1]
  have l5 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X0)))) = X3 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2]; rw [h4512 X0 X2 (X2 ◇ X0)]
    conv => enter [1]; rw [l3 X1 X0 X2 X3]
  have l6 : ∀ X0 X2 X3 : G, (X0 ◇ (X2 ◇ (X2 ◇ X0))) = X3 := by
    intro X0 X2 X3
    conv => enter [1, 2]; rw [← l4 X0 (X2 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l5 X0 X0 X2 X3]
  have l7 : ∀ X2 X0 X3 : G, (X2 ◇ (X2 ◇ X0)) = X3 := by
    intro X2 X0 X3
    conv => enter [1]; rw [← l4 X0 (X2 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l6 X0 X2 X3]
  have l8 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = X3 := by
    intro X2 X0 X3
    conv => enter [1, 2]; rw [← l4 X2 X0]
    conv => enter [1]; rw [l7 X2 X0 X3]
  have l9 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l8 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X4 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5406 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation2_implies_Equation5407 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5407 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (w ◇ (x ◇ z)))))]

theorem Equation4512_5407_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5407 : Equation5407 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ X3)) ◇ X0)) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2]; rw [h5407 X0 (X2 ◇ (X0 ◇ X3)) X3 X2]
    conv => enter [1]; rw [← h5407 X3 X1 (X2 ◇ (X0 ◇ X3)) X3]
  have l1 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X3)))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X3 ◇ (X4 ◇ (X0 ◇ X3))))]
    conv => enter [1]; rw [← h5407 X0 (X1 ◇ X2) X3 X4]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5407 X0 X1 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X1 X1 X0]
  have l3 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ ((X0 ◇ X3) ◇ X0))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2]; rw [h4512 X2 (X0 ◇ X3) X0]
    conv => enter [1]; rw [l0 X1 X2 X0 X3]
  have l4 : ∀ X2 X0 X3 : G, (X2 ◇ ((X0 ◇ X3) ◇ X0)) = X3 := by
    intro X2 X0 X3
    conv => enter [1, 2]; rw [← l2 X2 ((X0 ◇ X3) ◇ X0)]
    conv => enter [1]; rw [l3 X2 X2 X0 X3]
  have l5 : ∀ X0 X3 : G, ((X0 ◇ X3) ◇ X0) = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l2 X0 ((X0 ◇ X3) ◇ X0)]
    conv => enter [1]; rw [l4 X0 X0 X3]
  have l6 : ∀ X0 X3 : G, (X0 ◇ (X3 ◇ X0)) = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h4512 X0 X3 X0]
    conv => enter [1]; rw [l5 X0 X3]
  have l7 : ∀ X3 X0 : G, (X3 ◇ X0) = X3 := by
    intro X3 X0
    conv => enter [1]; rw [← l2 X0 (X3 ◇ X0)]
    conv => enter [1]; rw [l6 X0 X3]
  have l8 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l7 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X0))))]
    conv => enter [1]; rw [← h5407 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l8 x y]

@[equational_result]
theorem Equation2_implies_Equation5408 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5408 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (w ◇ (x ◇ w)))))]

@[equational_result]
theorem Equation5408_implies_Equation2 (G : Type*) [Magma G] (h5408 : Equation5408 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5408 X0 (X0 ◇ X2) (X0 ◇ X2) X2]
    conv => enter [1]; rw [← h5408 X2 X1 (X0 ◇ X2) (X0 ◇ X2)]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X4 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5408 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5409 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5409 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (w ◇ (x ◇ u)))))]

@[equational_result]
theorem Equation5409_implies_Equation2 (G : Type*) [Magma G] (h5409 : Equation5409 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X3 : G, (X1 ◇ X0) = X3 := by
    intro X1 X0 X3
    conv => enter [1, 2]; rw [h5409 X0 X1 X1 X3 X1]
    conv => enter [1]; rw [← h5409 X3 X1 X1 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X4 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5409 X4 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5411 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5411 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (w ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5411_implies_Equation2 (G : Type*) [Magma G] (h5411 : Equation5411 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5411 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5411 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5412 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5412 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (w ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5412_implies_Equation2 (G : Type*) [Magma G] (h5412 : Equation5412 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5412 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5412 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5413 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5413 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (w ◇ (y ◇ w)))))]

@[equational_result]
theorem Equation5413_implies_Equation2 (G : Type*) [Magma G] (h5413 : Equation5413 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5413 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5413 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5414 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5414 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (w ◇ (y ◇ u)))))]

@[equational_result]
theorem Equation5414_implies_Equation2 (G : Type*) [Magma G] (h5414 : Equation5414 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5414 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5414 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5416 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5416 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (w ◇ (z ◇ y)))))]

@[equational_result]
theorem Equation5416_implies_Equation2 (G : Type*) [Magma G] (h5416 : Equation5416 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5416 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5416 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5417 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5417 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (w ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5417_implies_Equation2 (G : Type*) [Magma G] (h5417 : Equation5417 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5417 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5417 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5418 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5418 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (w ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5418_implies_Equation2 (G : Type*) [Magma G] (h5418 : Equation5418 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5418 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5418 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5419 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5419 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (w ◇ (z ◇ u)))))]

@[equational_result]
theorem Equation5419_implies_Equation2 (G : Type*) [Magma G] (h5419 : Equation5419 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5419 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5419 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5421 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5421 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (w ◇ (w ◇ y)))))]

@[equational_result]
theorem Equation5421_implies_Equation2 (G : Type*) [Magma G] (h5421 : Equation5421 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5421 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5421 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5422 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5422 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (w ◇ (w ◇ z)))))]

@[equational_result]
theorem Equation5422_implies_Equation2 (G : Type*) [Magma G] (h5422 : Equation5422 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5422 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5422 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5423 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5423 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (w ◇ (w ◇ w)))))]

@[equational_result]
theorem Equation5423_implies_Equation2 (G : Type*) [Magma G] (h5423 : Equation5423 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5423 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5423 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5424 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5424 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (w ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5424_implies_Equation2 (G : Type*) [Magma G] (h5424 : Equation5424 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5424 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5424 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5426 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5426 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (w ◇ (u ◇ y)))))]

@[equational_result]
theorem Equation5426_implies_Equation2 (G : Type*) [Magma G] (h5426 : Equation5426 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5426 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5426 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5427 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5427 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (w ◇ (u ◇ z)))))]

@[equational_result]
theorem Equation5427_implies_Equation2 (G : Type*) [Magma G] (h5427 : Equation5427 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5427 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5427 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5428 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5428 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (w ◇ (u ◇ w)))))]

@[equational_result]
theorem Equation5428_implies_Equation2 (G : Type*) [Magma G] (h5428 : Equation5428 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5428 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5428 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5429 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5429 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (w ◇ (u ◇ u)))))]

@[equational_result]
theorem Equation5429_implies_Equation2 (G : Type*) [Magma G] (h5429 : Equation5429 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5429 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5429 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5430 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5430 G := by
  intro x y z w u v
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (w ◇ (u ◇ v)))))]

@[equational_result]
theorem Equation5430_implies_Equation2 (G : Type*) [Magma G] (h5430 : Equation5430 G) : Equation2 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5430 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5430 X6 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5432 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5432 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (x ◇ (x ◇ y)))))]

theorem Equation4512_5432_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5432 : Equation5432 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h5432 X0 X1 X0 X0]
    conv => enter [1]; rw [← h5432 X0 (X0 ◇ X1) X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [← l1 X0 X0]
    conv => enter [1]; rw [← h5432 X0 X0 X1 X2]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [← l1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← h5432 X0 X1 X2 (X0 ◇ X1)]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l2 X0 X0 X0]
  have l5 : ∀ X1 X0 X2 X3 : G, ((X1 ◇ X0) ◇ (X2 ◇ (X3 ◇ X0))) = X0 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2, 2, 2]; rw [← l2 X0 X0 X1]
    conv => enter [1]; rw [← h5432 X0 (X1 ◇ X0) X2 X3]
  have l6 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X0)))) = X0 := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h4512 X1 X0 (X2 ◇ (X3 ◇ X0))]
    conv => enter [1]; rw [l5 X1 X0 X2 X3]
  have l7 : ∀ X1 X3 X0 : G, (X1 ◇ X3) = X0 := by
    intro X1 X3 X0
    conv => enter [1, 2]; rw [← l3 X0 X1 X3]
    conv => enter [1]; rw [l6 X1 X0 X1 X3]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X1 X1 X0]
    conv => enter [1]; rw [l4 X1]
  intro x y
  conv => enter [1]; rw [l8 x y]

@[equational_result]
theorem Equation2_implies_Equation5433 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5433 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (x ◇ (x ◇ z)))))]

theorem Equation4512_5433_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5433 : Equation5433 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0)) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [h5433 X0 X1 X2 X2]
    conv => enter [1]; rw [← h5433 X2 X1 (X0 ◇ (X0 ◇ X2)) X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5433 X0 (X0 ◇ X1) X1 X0]
    conv => enter [1]; rw [← h5433 X0 X1 (X0 ◇ X1) X1]
  have l2 : ∀ X0 X2 : G, ((X0 ◇ (X0 ◇ X2)) ◇ X0) = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l1 X0 ((X0 ◇ (X0 ◇ X2)) ◇ X0)]
    conv => enter [1]; rw [l0 X0 X0 X2]
  have l3 : ∀ X0 X2 : G, (X0 ◇ ((X0 ◇ X2) ◇ X0)) = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X2) X0]
    conv => enter [1]; rw [l2 X0 X2]
  have l4 : ∀ X0 X2 : G, ((X0 ◇ X2) ◇ X0) = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l1 X0 ((X0 ◇ X2) ◇ X0)]
    conv => enter [1]; rw [l3 X0 X2]
  have l5 : ∀ X0 X2 : G, (X0 ◇ (X2 ◇ X0)) = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h4512 X0 X2 X0]
    conv => enter [1]; rw [l4 X0 X2]
  have l6 : ∀ X2 X0 : G, (X2 ◇ X0) = X2 := by
    intro X2 X0
    conv => enter [1]; rw [← l1 X0 (X2 ◇ X0)]
    conv => enter [1]; rw [l5 X0 X2]
  have l7 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l6 X0 (X0 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X0))))]
    conv => enter [1]; rw [← h5433 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation2_implies_Equation5434 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5434 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (x ◇ (x ◇ w)))))]

@[equational_result]
theorem Equation5434_implies_Equation2 (G : Type*) [Magma G] (h5434 : Equation5434 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ X0)) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2]; rw [h5434 X0 (X0 ◇ (X0 ◇ X3)) X3 X3]
    conv => enter [1]; rw [← h5434 X3 X1 X2 (X0 ◇ (X0 ◇ X3))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5434 X0 X1 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h5434 X0 X1 X1 (X0 ◇ X0)]
  have l2 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = X3 := by
    intro X2 X0 X3
    conv => enter [1, 2]; rw [← l1 X2 X0]
    conv => enter [1]; rw [l0 X2 X2 X0 X3]
  have l3 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l2 X0 (X0 ◇ (X0 ◇ (X4 ◇ (X4 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5434 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation5435 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5435 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (x ◇ (x ◇ u)))))]

@[equational_result]
theorem Equation5435_implies_Equation2 (G : Type*) [Magma G] (h5435 : Equation5435 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 X4 : G, (X1 ◇ (X2 ◇ X0)) = X4 := by
    intro X1 X2 X0 X4
    conv => enter [1, 2, 2]; rw [h5435 X0 X1 X4 X4 X1]
    conv => enter [1]; rw [← h5435 X4 X1 X2 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5435 X0 X1 X1 X0 X1]
    conv => enter [1]; rw [← h5435 X0 X1 X1 X1 (X0 ◇ X1)]
  have l2 : ∀ X2 X0 X4 : G, (X2 ◇ X0) = X4 := by
    intro X2 X0 X4
    conv => enter [1, 2]; rw [← l1 X2 X0]
    conv => enter [1]; rw [l0 X2 X2 X0 X4]
  have l3 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l2 X0 (X0 ◇ (X0 ◇ (X4 ◇ (X4 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5435 X4 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation5437 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5437 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (x ◇ (y ◇ y)))))]

theorem Equation4512_5437_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5437 : Equation5437 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h5437 (X0 ◇ X1) X2 X3 X4]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l1 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X1)) ◇ (X2 ◇ X0)) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h5437 X0 X1 X3 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [← h5437 X3 (X0 ◇ (X1 ◇ X1)) X2 X1]
  have l2 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X4)))))) = X3 := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X4 ◇ X4)))]
    conv => enter [1]; rw [← h5437 X3 X4 (X0 ◇ X1) X2]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X1) ◇ (X2 ◇ X0))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) (X2 ◇ X0)]
    conv => enter [1]; rw [l1 X0 X1 X2 X3]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [l2 X0 X0 X0 X0 X1]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) = X3 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X1 (X2 ◇ X0)]
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
  have l6 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [← l4 X0 (X1 ◇ (X1 ◇ (X2 ◇ X0)))]
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
  have l7 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ X0)) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2]; rw [← l4 X1 (X2 ◇ X0)]
    conv => enter [1]; rw [l6 X1 X2 X0 X3]
  have l8 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = X3 := by
    intro X2 X0 X3
    conv => enter [1, 2]; rw [← l4 X2 X0]
    conv => enter [1]; rw [l7 X2 X2 X0 X3]
  have l9 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l8 X0 (X0 ◇ (X0 ◇ (X4 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5437 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation2_implies_Equation5438 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5438 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (x ◇ (y ◇ z)))))]

theorem Equation4512_5438_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5438 : Equation5438 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h5438 (X0 ◇ X1) X2 X3 X4]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l1 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))))) = X2 := by
    intro X3 X4 X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
    conv => enter [1]; rw [← h5438 X2 X3 X4 (X0 ◇ X1)]
  have l2 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X0)) = X3 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2, 2]; rw [h5438 X0 X2 X3 X1]
    conv => enter [1]; rw [← h5438 X3 X1 (X0 ◇ (X2 ◇ X3)) X2]
  have l3 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X0))) = X3 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2]; rw [h4512 X0 (X2 ◇ X3) X0]
    conv => enter [1]; rw [l2 X1 X0 X2 X3]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [l1 X0 X0 X0 X0 X1]
  have l5 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X0)))) = X3 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X2 X3 X0]
    conv => enter [1]; rw [l3 X1 X0 X2 X3]
  have l6 : ∀ X0 X2 X3 : G, (X0 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := by
    intro X0 X2 X3
    conv => enter [1, 2]; rw [← l4 X0 (X2 ◇ (X3 ◇ X0))]
    conv => enter [1]; rw [l5 X0 X0 X2 X3]
  have l7 : ∀ X2 X3 X0 : G, (X2 ◇ (X3 ◇ X0)) = X3 := by
    intro X2 X3 X0
    conv => enter [1]; rw [← l4 X0 (X2 ◇ (X3 ◇ X0))]
    conv => enter [1]; rw [l6 X0 X2 X3]
  have l8 : ∀ X3 X0 : G, (X3 ◇ X0) = X3 := by
    intro X3 X0
    conv => enter [1, 2]; rw [← l4 X3 X0]
    conv => enter [1]; rw [l7 X3 X3 X0]
  have l9 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l8 X0 (X0 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5438 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation2_implies_Equation5439 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5439 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (x ◇ (y ◇ w)))))]

@[equational_result]
theorem Equation5439_implies_Equation2 (G : Type*) [Magma G] (h5439 : Equation5439 G) : Equation2 G := by
  have l0 : ∀ X0 X2 : G, (X0 ◇ X0) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [h5439 X0 X0 (X0 ◇ X2) X2]
    conv => enter [1]; rw [← h5439 X2 X0 X0 (X0 ◇ X2)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l0 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5440 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5440 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (x ◇ (y ◇ u)))))]

@[equational_result]
theorem Equation5440_implies_Equation2 (G : Type*) [Magma G] (h5440 : Equation5440 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, (X0 ◇ X0) = X3 := by
    intro X0 X3
    conv => enter [1, 2]; rw [h5440 X0 X0 X0 X3 X0]
    conv => enter [1]; rw [← h5440 X3 X0 X0 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l0 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5442 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5442 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (x ◇ (z ◇ y)))))]

theorem Equation4512_5442_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5442 : Equation5442 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X3 X2 X4 : G, (X0 ◇ X1) = (X3 ◇ (X2 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) := by
    intro X0 X1 X3 X2 X4
    conv => enter [1]; rw [h5442 (X0 ◇ X1) X3 X2 X4]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l1 : ∀ X4 X3 X0 X1 X2 : G, (X4 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))))) = X2 := by
    intro X4 X3 X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
    conv => enter [1]; rw [← h5442 X2 X4 X3 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X1 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h5442 X0 X2 X1 X3]
    conv => enter [1]; rw [← h5442 X1 (X0 ◇ (X1 ◇ X2)) X3 X2]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = X1 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) (X3 ◇ X0)]
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [l1 X0 X0 X0 X0 X1]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) = X1 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 (X3 ◇ X0)]
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
  have l6 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X1 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [← l4 X0 (X1 ◇ (X2 ◇ (X3 ◇ X0)))]
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
  have l7 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ X0)) = X1 := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [← l4 X1 (X2 ◇ (X3 ◇ X0))]
    conv => enter [1]; rw [l6 X1 X2 X3 X0]
  have l8 : ∀ X3 X0 X1 : G, (X3 ◇ X0) = X1 := by
    intro X3 X0 X1
    conv => enter [1, 2]; rw [← l4 X3 X0]
    conv => enter [1]; rw [l7 X3 X3 X0 X1]
  have l9 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l8 X0 (X0 ◇ (X0 ◇ (X4 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5442 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation2_implies_Equation5443 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5443 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (x ◇ (z ◇ z)))))]

theorem Equation4512_5443_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5443 : Equation5443 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X2)) ◇ X0)) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [h5443 X0 X1 X2 (X0 ◇ (X2 ◇ X2))]
    conv => enter [1]; rw [← h5443 X2 X1 (X0 ◇ (X2 ◇ X2)) X1]
  have l1 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X3 ◇ X3)))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X4 ◇ (X0 ◇ (X3 ◇ X3))))]
    conv => enter [1]; rw [← h5443 X0 (X1 ◇ X2) X3 X4]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5443 X0 X1 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X1 X1 X0]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ ((X2 ◇ X2) ◇ X0))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4512 X0 (X2 ◇ X2) X0]
    conv => enter [1]; rw [l0 X1 X0 X2]
  have l4 : ∀ X0 X2 : G, (X0 ◇ ((X2 ◇ X2) ◇ X0)) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [← l2 X0 ((X2 ◇ X2) ◇ X0)]
    conv => enter [1]; rw [l3 X0 X0 X2]
  have l5 : ∀ X2 X0 : G, ((X2 ◇ X2) ◇ X0) = X2 := by
    intro X2 X0
    conv => enter [1]; rw [← l2 X0 ((X2 ◇ X2) ◇ X0)]
    conv => enter [1]; rw [l4 X0 X2]
  have l6 : ∀ X2 X0 : G, (X2 ◇ (X2 ◇ X0)) = X2 := by
    intro X2 X0
    conv => enter [1]; rw [h4512 X2 X2 X0]
    conv => enter [1]; rw [l5 X2 X0]
  have l7 : ∀ X2 X0 : G, (X2 ◇ X0) = X2 := by
    intro X2 X0
    conv => enter [1, 2]; rw [← l2 X2 X0]
    conv => enter [1]; rw [l6 X2 X0]
  have l8 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l7 X0 (X0 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5443 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l8 x y]

@[equational_result]
theorem Equation2_implies_Equation5444 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5444 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (x ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5444_implies_Equation2 (G : Type*) [Magma G] (h5444 : Equation5444 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ X0)) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2]; rw [h5444 X0 (X0 ◇ (X3 ◇ X2)) X3 X2]
    conv => enter [1]; rw [← h5444 X3 X1 X2 (X0 ◇ (X3 ◇ X2))]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 X0 (X0 ◇ (X4 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [← h5444 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5445 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5445 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (x ◇ (z ◇ u)))))]

@[equational_result]
theorem Equation5445_implies_Equation2 (G : Type*) [Magma G] (h5445 : Equation5445 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X3 : G, (X1 ◇ X0) = X3 := by
    intro X1 X0 X3
    conv => enter [1, 2]; rw [h5445 X0 X0 X1 X3 X1]
    conv => enter [1]; rw [← h5445 X3 X1 X0 X1 (X1 ◇ X1)]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X4 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5445 X4 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5447 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5447 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (x ◇ (w ◇ y)))))]

@[equational_result]
theorem Equation5447_implies_Equation2 (G : Type*) [Magma G] (h5447 : Equation5447 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, ((X1 ◇ X2) ◇ X0) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h5447 X0 X2 X0 X1]
    conv => enter [1]; rw [← h5447 X1 (X1 ◇ X2) X2 X0]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 X0 (X0 ◇ (X0 ◇ (X4 ◇ (X0 ◇ (X0 ◇ X0)))))]
    conv => enter [1]; rw [← h5447 X4 (X0 ◇ X0) X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5448 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5448 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (x ◇ (w ◇ z)))))]

@[equational_result]
theorem Equation5448_implies_Equation2 (G : Type*) [Magma G] (h5448 : Equation5448 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5448 X0 (X2 ◇ X0) X0 X2]
    conv => enter [1]; rw [← h5448 X2 X1 (X2 ◇ X0) X0]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X4 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5448 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5449 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5449 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (x ◇ (w ◇ w)))))]

theorem Equation4512_5449_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5449 : Equation5449 G) : Equation2 G := by
  have l0 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))))) = X2 := by
    intro X3 X4 X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [← h5449 X2 X3 X4 (X0 ◇ X1)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5449 (X0 ◇ X0) X1 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h5449 X0 X1 X1 (X0 ◇ X0)]
  have l2 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X4 ◇ X4)))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X4 ◇ (X0 ◇ (X4 ◇ X4))))]
    conv => enter [1]; rw [← h5449 X0 (X1 ◇ X2) X3 X4]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5449 X0 X1 X1 X1]
    conv => enter [1]; rw [l2 X1 X1 X1 X1 X0]
  have l4 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = X2 := by
    intro X3 X4 X0 X1 X2
    conv => enter [1, 2, 2, 2, 2]; rw [← l1 X2 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X3 X4 X0 X1 X2]
  have l5 : ∀ X4 X0 X1 X2 : G, (X4 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := by
    intro X4 X0 X1 X2
    conv => enter [1, 2]; rw [← l3 X4 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l4 X4 X4 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [← l3 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l5 X0 X0 X1 X2]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X1)) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l3 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l6 X0 X1 X2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l3 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l7 X1 X0 X2]
  have l9 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l8 X0 (X0 ◇ (X0 ◇ (X4 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5449 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation2_implies_Equation5450 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5450 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (x ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5450_implies_Equation2 (G : Type*) [Magma G] (h5450 : Equation5450 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X3 : G, (X1 ◇ X0) = X3 := by
    intro X1 X0 X3
    conv => enter [1, 2]; rw [h5450 X0 X1 X0 X3 X1]
    conv => enter [1]; rw [← h5450 X3 X1 X1 X0 (X3 ◇ X1)]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X4 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5450 X4 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5452 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5452 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (x ◇ (u ◇ y)))))]

theorem Equation4512_5452_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5452 : Equation5452 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X3 X4 X5 X2 : G, (X0 ◇ X1) = (X3 ◇ (X4 ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) := by
    intro X0 X1 X3 X4 X5 X2
    conv => enter [1]; rw [h5452 (X0 ◇ X1) X3 X4 X5 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l1 : ∀ X5 X0 X1 X2 X3 X4 : G, (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))))) = X3 := by
    intro X5 X0 X1 X2 X3 X4
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X4 ◇ X5)))]
    conv => enter [1]; rw [← h5452 X3 X5 (X0 ◇ X1) X2 X4]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [l1 X0 X0 X0 X0 X1 X0]
  have l3 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) = X2 := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [← l2 X4 (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))]
    conv => enter [1]; rw [← h5452 X2 X4 X0 X1 X3]
  have l4 : ∀ X1 X2 X3 X4 : G, (X1 ◇ (X2 ◇ (X3 ◇ X4))) = X2 := by
    intro X1 X2 X3 X4
    conv => enter [1, 2]; rw [← l2 X1 (X2 ◇ (X3 ◇ X4))]
    conv => enter [1]; rw [l3 X1 X1 X2 X3 X4]
  have l5 : ∀ X2 X3 X4 : G, (X2 ◇ (X3 ◇ X4)) = X2 := by
    intro X2 X3 X4
    conv => enter [1, 2]; rw [← l2 X2 (X3 ◇ X4)]
    conv => enter [1]; rw [l4 X2 X2 X3 X4]
  have l6 : ∀ X3 X4 X2 : G, (X3 ◇ X4) = X2 := by
    intro X3 X4 X2
    conv => enter [1]; rw [← l2 X2 (X3 ◇ X4)]
    conv => enter [1]; rw [l5 X2 X3 X4]
  have l7 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l6 X0 (X0 ◇ (X0 ◇ (X4 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5452 X4 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation2_implies_Equation5453 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5453 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (x ◇ (u ◇ z)))))]

@[equational_result]
theorem Equation5453_implies_Equation2 (G : Type*) [Magma G] (h5453 : Equation5453 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X4 : G, (X1 ◇ X0) = X4 := by
    intro X1 X0 X4
    conv => enter [1, 2]; rw [h5453 X0 (X1 ◇ X1) X1 X4 X1]
    conv => enter [1]; rw [← h5453 X4 X1 (X1 ◇ X1) X1 X0]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X4 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5453 X4 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5454 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5454 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (x ◇ (u ◇ w)))))]

@[equational_result]
theorem Equation5454_implies_Equation2 (G : Type*) [Magma G] (h5454 : Equation5454 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X4 : G, (X1 ◇ X0) = X4 := by
    intro X1 X0 X4
    conv => enter [1, 2]; rw [h5454 X0 X1 (X1 ◇ X4) X4 X1]
    conv => enter [1]; rw [← h5454 X4 X1 X1 (X1 ◇ X4) X0]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X4 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5454 X4 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5455 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5455 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (x ◇ (u ◇ u)))))]

@[equational_result]
theorem Equation5455_implies_Equation2 (G : Type*) [Magma G] (h5455 : Equation5455 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 X4 : G, (X1 ◇ (X2 ◇ X0)) = X4 := by
    intro X1 X2 X0 X4
    conv => enter [1, 2, 2]; rw [h5455 X0 X1 X4 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1]; rw [← h5455 X4 X1 X2 X1 (X0 ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 X0 (X0 ◇ (X4 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [← h5455 X4 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5456 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5456 G := by
  intro x y z w u v
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (x ◇ (u ◇ v)))))]

theorem Equation4512_5456_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5456 : Equation5456 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X3 X4 X0 X5 X6 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X5 ◇ X6)))))) = X0 := by
    intro X1 X2 X3 X4 X0 X5 X6
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X4 ◇ (X0 ◇ (X5 ◇ X6))))]
    conv => enter [1]; rw [← h5456 X0 (X1 ◇ X2) X3 X4 X5 X6]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5456 X0 X0 X0 X0 X4 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X0 X0 X0 X4 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

end Semigroup5
