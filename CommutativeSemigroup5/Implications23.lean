import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace CommutativeSemigroup5

@[equational_result]
theorem Equation5101_implies_Equation4729 (G : Type*) [Magma G] (h5101 : Equation5101 G) : Equation4729 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5101 X0 X0 X0]
    conv => enter [1]; rw [← h5101 X3 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5101_implies_Equation4746 (G : Type*) [Magma G] (h5101 : Equation5101 G) : Equation4746 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5101 X0 X0 X0]
    conv => enter [1]; rw [← h5101 X3 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5101_implies_Equation4799 (G : Type*) [Magma G] (h5101 : Equation5101 G) : Equation4799 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5101 X0 X0 X0]
    conv => enter [1]; rw [← h5101 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5101_implies_Equation4802 (G : Type*) [Magma G] (h5101 : Equation5101 G) : Equation4802 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5101 X0 X0 X0]
    conv => enter [1]; rw [← h5101 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5101_implies_Equation4803 (G : Type*) [Magma G] (h5101 : Equation5101 G) : Equation4803 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5101 X0 X0 X0]
    conv => enter [1]; rw [← h5101 X3 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5101_implies_Equation4815 (G : Type*) [Magma G] (h5101 : Equation5101 G) : Equation4815 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5101 X0 X0 X0]
    conv => enter [1]; rw [← h5101 X3 X0 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (z ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5101_implies_Equation4820 (G : Type*) [Magma G] (h5101 : Equation5101 G) : Equation4820 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5101 X0 X0 X0]
    conv => enter [1]; rw [← h5101 X3 X0 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5101_implies_Equation4897 (G : Type*) [Magma G] (h5101 : Equation5101 G) : Equation4897 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5101 X0 X0 X0]
    conv => enter [1]; rw [← h5101 X3 X0 X0]
  intro x y z w u v
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (z ◇ (w ◇ (u ◇ v)))))]

@[equational_result]
theorem Equation5101_implies_Equation5100 (G : Type*) [Magma G] (h5101 : Equation5101 G) : Equation5100 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5101 X0 X0 X0]
    conv => enter [1]; rw [← h5101 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5101_implies_Equation5104 (G : Type*) [Magma G] (h5101 : Equation5101 G) : Equation5104 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5101 X0 X0 X0]
    conv => enter [1]; rw [← h5101 X3 X0 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5100_implies_Equation2 (G : Type*) [Magma G] (h5100 : Equation5100 G) : Equation2 G := by
  have l0 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h5100 X0 X0]
    conv => enter [1]; rw [← h5100 X2 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5100_implies_Equation4696 (G : Type*) [Magma G] (h5100 : Equation5100 G) : Equation4696 G := by
  have l0 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h5100 X0 X0]
    conv => enter [1]; rw [← h5100 X2 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (x ◇ y)))))]

@[equational_result]
theorem Equation5100_implies_Equation4698 (G : Type*) [Magma G] (h5100 : Equation5100 G) : Equation4698 G := by
  have l0 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h5100 X0 X0]
    conv => enter [1]; rw [← h5100 X2 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5100_implies_Equation4699 (G : Type*) [Magma G] (h5100 : Equation5100 G) : Equation4699 G := by
  have l0 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h5100 X0 X0]
    conv => enter [1]; rw [← h5100 X2 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5100_implies_Equation4704 (G : Type*) [Magma G] (h5100 : Equation5100 G) : Equation4704 G := by
  have l0 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h5100 X0 X0]
    conv => enter [1]; rw [← h5100 X2 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5100_implies_Equation4705 (G : Type*) [Magma G] (h5100 : Equation5100 G) : Equation4705 G := by
  have l0 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h5100 X0 X0]
    conv => enter [1]; rw [← h5100 X2 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5100_implies_Equation4709 (G : Type*) [Magma G] (h5100 : Equation5100 G) : Equation4709 G := by
  have l0 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h5100 X0 X0]
    conv => enter [1]; rw [← h5100 X2 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (x ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5100_implies_Equation4724 (G : Type*) [Magma G] (h5100 : Equation5100 G) : Equation4724 G := by
  have l0 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h5100 X0 X0]
    conv => enter [1]; rw [← h5100 X2 X0]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5100_implies_Equation4725 (G : Type*) [Magma G] (h5100 : Equation5100 G) : Equation4725 G := by
  have l0 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h5100 X0 X0]
    conv => enter [1]; rw [← h5100 X2 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5100_implies_Equation4728 (G : Type*) [Magma G] (h5100 : Equation5100 G) : Equation4728 G := by
  have l0 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h5100 X0 X0]
    conv => enter [1]; rw [← h5100 X2 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5100_implies_Equation4729 (G : Type*) [Magma G] (h5100 : Equation5100 G) : Equation4729 G := by
  have l0 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h5100 X0 X0]
    conv => enter [1]; rw [← h5100 X2 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5100_implies_Equation4746 (G : Type*) [Magma G] (h5100 : Equation5100 G) : Equation4746 G := by
  have l0 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h5100 X0 X0]
    conv => enter [1]; rw [← h5100 X2 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (x ◇ (x ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5100_implies_Equation4799 (G : Type*) [Magma G] (h5100 : Equation5100 G) : Equation4799 G := by
  have l0 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h5100 X0 X0]
    conv => enter [1]; rw [← h5100 X2 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5100_implies_Equation4802 (G : Type*) [Magma G] (h5100 : Equation5100 G) : Equation4802 G := by
  have l0 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h5100 X0 X0]
    conv => enter [1]; rw [← h5100 X2 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5100_implies_Equation4803 (G : Type*) [Magma G] (h5100 : Equation5100 G) : Equation4803 G := by
  have l0 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h5100 X0 X0]
    conv => enter [1]; rw [← h5100 X2 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5100_implies_Equation4815 (G : Type*) [Magma G] (h5100 : Equation5100 G) : Equation4815 G := by
  have l0 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h5100 X0 X0]
    conv => enter [1]; rw [← h5100 X2 X0]
  intro x y z w
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (z ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5100_implies_Equation4820 (G : Type*) [Magma G] (h5100 : Equation5100 G) : Equation4820 G := by
  have l0 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h5100 X0 X0]
    conv => enter [1]; rw [← h5100 X2 X0]
  intro x y z w u
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5100_implies_Equation4897 (G : Type*) [Magma G] (h5100 : Equation5100 G) : Equation4897 G := by
  have l0 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h5100 X0 X0]
    conv => enter [1]; rw [← h5100 X2 X0]
  intro x y z w u v
  conv => enter [1]; rw [l0 x (x ◇ (y ◇ (z ◇ (w ◇ (u ◇ v)))))]

@[equational_result]
theorem Equation5100_implies_Equation5101 (G : Type*) [Magma G] (h5100 : Equation5100 G) : Equation5101 G := by
  have l0 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h5100 X0 X0]
    conv => enter [1]; rw [← h5100 X2 X0]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ (y ◇ (y ◇ (y ◇ (y ◇ z)))))]

theorem Equation43_4512_4897_implies_Equation2 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4897 : Equation4897 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4897 X0 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4897 X1 X0 X1 X1 X1 (X1 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X4 X5 X0 : G, ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) ◇ X0) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) X0]
    conv => enter [1]; rw [← h4897 X0 X1 X2 X3 X4 X5]
  have l2 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X0)) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X3 ◇ (X4 ◇ X5))) X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X5 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X0 X0 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation43_4512_4897_implies_Equation4696 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4897 : Equation4897 G) : Equation4696 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4897 X0 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4897 X1 X0 X1 X1 X1 (X1 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X4 X5 X0 : G, ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) ◇ X0) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) X0]
    conv => enter [1]; rw [← h4897 X0 X1 X2 X3 X4 X5]
  have l2 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X0)) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X3 ◇ (X4 ◇ X5))) X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X5 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X0 X0 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x (x ◇ (x ◇ (x ◇ (x ◇ (x ◇ y)))))]

theorem Equation43_4512_4897_implies_Equation4698 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4897 : Equation4897 G) : Equation4698 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4897 X0 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4897 X1 X0 X1 X1 X1 (X1 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X4 X5 X0 : G, ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) ◇ X0) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) X0]
    conv => enter [1]; rw [← h4897 X0 X1 X2 X3 X4 X5]
  have l2 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X0)) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X3 ◇ (X4 ◇ X5))) X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X5 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X0 X0 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ y)))))]

theorem Equation43_4512_4897_implies_Equation4699 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4897 : Equation4897 G) : Equation4699 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4897 X0 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4897 X1 X0 X1 X1 X1 (X1 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X4 X5 X0 : G, ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) ◇ X0) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) X0]
    conv => enter [1]; rw [← h4897 X0 X1 X2 X3 X4 X5]
  have l2 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X0)) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X3 ◇ (X4 ◇ X5))) X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X5 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X0 X0 X0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l3 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ z)))))]

theorem Equation43_4512_4897_implies_Equation4704 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4897 : Equation4897 G) : Equation4704 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4897 X0 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4897 X1 X0 X1 X1 X1 (X1 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X4 X5 X0 : G, ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) ◇ X0) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) X0]
    conv => enter [1]; rw [← h4897 X0 X1 X2 X3 X4 X5]
  have l2 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X0)) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X3 ◇ (X4 ◇ X5))) X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X5 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X0 X0 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ y)))))]

theorem Equation43_4512_4897_implies_Equation4705 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4897 : Equation4897 G) : Equation4705 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4897 X0 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4897 X1 X0 X1 X1 X1 (X1 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X4 X5 X0 : G, ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) ◇ X0) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) X0]
    conv => enter [1]; rw [← h4897 X0 X1 X2 X3 X4 X5]
  have l2 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X0)) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X3 ◇ (X4 ◇ X5))) X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X5 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X0 X0 X0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l3 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ z)))))]

theorem Equation43_4512_4897_implies_Equation4709 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4897 : Equation4897 G) : Equation4709 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4897 X0 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4897 X1 X0 X1 X1 X1 (X1 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X4 X5 X0 : G, ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) ◇ X0) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) X0]
    conv => enter [1]; rw [← h4897 X0 X1 X2 X3 X4 X5]
  have l2 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X0)) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X3 ◇ (X4 ◇ X5))) X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X5 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X0 X0 X0 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l3 x (x ◇ (x ◇ (x ◇ (y ◇ (z ◇ w)))))]

theorem Equation43_4512_4897_implies_Equation4724 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4897 : Equation4897 G) : Equation4724 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4897 X0 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4897 X1 X0 X1 X1 X1 (X1 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X4 X5 X0 : G, ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) ◇ X0) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) X0]
    conv => enter [1]; rw [← h4897 X0 X1 X2 X3 X4 X5]
  have l2 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X0)) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X3 ◇ (X4 ◇ X5))) X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X5 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X0 X0 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y)))))]

theorem Equation43_4512_4897_implies_Equation4725 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4897 : Equation4897 G) : Equation4725 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4897 X0 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4897 X1 X0 X1 X1 X1 (X1 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X4 X5 X0 : G, ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) ◇ X0) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) X0]
    conv => enter [1]; rw [← h4897 X0 X1 X2 X3 X4 X5]
  have l2 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X0)) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X3 ◇ (X4 ◇ X5))) X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X5 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X0 X0 X0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l3 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ z)))))]

theorem Equation43_4512_4897_implies_Equation4728 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4897 : Equation4897 G) : Equation4728 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4897 X0 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4897 X1 X0 X1 X1 X1 (X1 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X4 X5 X0 : G, ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) ◇ X0) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) X0]
    conv => enter [1]; rw [← h4897 X0 X1 X2 X3 X4 X5]
  have l2 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X0)) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X3 ◇ (X4 ◇ X5))) X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X5 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X0 X0 X0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l3 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ z)))))]

theorem Equation43_4512_4897_implies_Equation4729 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4897 : Equation4897 G) : Equation4729 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4897 X0 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4897 X1 X0 X1 X1 X1 (X1 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X4 X5 X0 : G, ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) ◇ X0) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) X0]
    conv => enter [1]; rw [← h4897 X0 X1 X2 X3 X4 X5]
  have l2 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X0)) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X3 ◇ (X4 ◇ X5))) X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X5 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X0 X0 X0 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l3 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ w)))))]

theorem Equation43_4512_4897_implies_Equation4746 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4897 : Equation4897 G) : Equation4746 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4897 X0 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4897 X1 X0 X1 X1 X1 (X1 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X4 X5 X0 : G, ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) ◇ X0) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) X0]
    conv => enter [1]; rw [← h4897 X0 X1 X2 X3 X4 X5]
  have l2 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X0)) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X3 ◇ (X4 ◇ X5))) X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X5 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X0 X0 X0 X0 X1]
  intro x y z w u
  conv => enter [1]; rw [l3 x (x ◇ (x ◇ (y ◇ (z ◇ (w ◇ u)))))]

theorem Equation43_4512_4897_implies_Equation4799 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4897 : Equation4897 G) : Equation4799 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4897 X0 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4897 X1 X0 X1 X1 X1 (X1 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X4 X5 X0 : G, ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) ◇ X0) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) X0]
    conv => enter [1]; rw [← h4897 X0 X1 X2 X3 X4 X5]
  have l2 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X0)) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X3 ◇ (X4 ◇ X5))) X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X5 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X0 X0 X0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l3 x (x ◇ (y ◇ (y ◇ (y ◇ (y ◇ z)))))]

theorem Equation43_4512_4897_implies_Equation4802 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4897 : Equation4897 G) : Equation4802 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4897 X0 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4897 X1 X0 X1 X1 X1 (X1 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X4 X5 X0 : G, ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) ◇ X0) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) X0]
    conv => enter [1]; rw [← h4897 X0 X1 X2 X3 X4 X5]
  have l2 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X0)) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X3 ◇ (X4 ◇ X5))) X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X5 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X0 X0 X0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l3 x (x ◇ (y ◇ (y ◇ (y ◇ (z ◇ z)))))]

theorem Equation43_4512_4897_implies_Equation4803 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4897 : Equation4897 G) : Equation4803 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4897 X0 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4897 X1 X0 X1 X1 X1 (X1 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X4 X5 X0 : G, ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) ◇ X0) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) X0]
    conv => enter [1]; rw [← h4897 X0 X1 X2 X3 X4 X5]
  have l2 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X0)) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X3 ◇ (X4 ◇ X5))) X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X5 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X0 X0 X0 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l3 x (x ◇ (y ◇ (y ◇ (y ◇ (z ◇ w)))))]

theorem Equation43_4512_4897_implies_Equation4815 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4897 : Equation4897 G) : Equation4815 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4897 X0 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4897 X1 X0 X1 X1 X1 (X1 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X4 X5 X0 : G, ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) ◇ X0) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) X0]
    conv => enter [1]; rw [← h4897 X0 X1 X2 X3 X4 X5]
  have l2 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X0)) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X3 ◇ (X4 ◇ X5))) X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X5 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X0 X0 X0 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l3 x (x ◇ (y ◇ (y ◇ (z ◇ (z ◇ w)))))]

theorem Equation43_4512_4897_implies_Equation4820 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4897 : Equation4897 G) : Equation4820 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4897 X0 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4897 X1 X0 X1 X1 X1 (X1 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X4 X5 X0 : G, ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) ◇ X0) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) X0]
    conv => enter [1]; rw [← h4897 X0 X1 X2 X3 X4 X5]
  have l2 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X0)) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X3 ◇ (X4 ◇ X5))) X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X5 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X0 X0 X0 X0 X1]
  intro x y z w u
  conv => enter [1]; rw [l3 x (x ◇ (y ◇ (y ◇ (z ◇ (w ◇ u)))))]

theorem Equation43_4512_4897_implies_Equation5100 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4897 : Equation4897 G) : Equation5100 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4897 X0 X1 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4897 X1 X0 X1 X1 X1 (X1 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X4 X5 X0 : G, ((X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) ◇ X0) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))) X0]
    conv => enter [1]; rw [← h4897 X0 X1 X2 X3 X4 X5]
  have l2 : ∀ X1 X2 X3 X4 X5 X0 : G, (X1 ◇ ((X2 ◇ (X3 ◇ (X4 ◇ X5))) ◇ X0)) = X0 := by
    intro X1 X2 X3 X4 X5 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X3 ◇ (X4 ◇ X5))) X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X5 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X0 X0 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x (y ◇ (y ◇ (y ◇ (y ◇ (y ◇ y)))))]

theorem Equation43_4512_4820_implies_Equation2 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4820 : Equation4820 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4820 X0 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4820 X1 X0 X0 X1 (X1 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X4 X0 : G, ((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X0) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) X0]
    conv => enter [1]; rw [← h4820 X0 X1 X2 X3 X4]
  have l2 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X2 ◇ (X3 ◇ X4))) X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X0 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation43_4512_4820_implies_Equation4696 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4820 : Equation4820 G) : Equation4696 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4820 X0 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4820 X1 X0 X0 X1 (X1 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X4 X0 : G, ((X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X0) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) X0]
    conv => enter [1]; rw [← h4820 X0 X1 X2 X3 X4]
  have l2 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X0)) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X2 ◇ (X3 ◇ X4))) X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X4 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X0 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x (x ◇ (x ◇ (x ◇ (x ◇ (x ◇ y)))))]

theorem Equation43_4512_4820_implies_Equation4698 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4820 : Equation4820 G) : Equation4698 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4820 X0 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4820 X1 X0 X0 X1 (X1 ◇ X1)]
  have l2 : ∀ sK0 sK1 X0 X1 X2 : G, sK0 = (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [h4820 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0 X1 X2]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l3 : ∀ sK0 sK1 X0 X1 X2 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l2 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation43_4512_4820_implies_Equation4699 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4820 : Equation4820 G) : Equation4699 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4820 X0 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4820 X1 X0 X0 X1 (X1 ◇ X1)]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, sK0 = (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [h4820 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0 X1 X2]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l3 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_4512_4820_implies_Equation4704 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4820 : Equation4820 G) : Equation4704 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4820 X0 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4820 X1 X0 X0 X1 (X1 ◇ X1)]
  have l2 : ∀ sK0 sK1 X0 X1 X2 : G, sK0 = (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [h4820 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0 X1 X2]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l3 : ∀ sK0 sK1 X0 X1 X2 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l2 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation43_4512_4820_implies_Equation4705 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4820 : Equation4820 G) : Equation4705 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4820 X0 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4820 X1 X0 X0 X1 (X1 ◇ X1)]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, sK0 = (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [h4820 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0 X1 X2]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l3 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_4512_4820_implies_Equation4709 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4820 : Equation4820 G) : Equation4709 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4820 X0 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4820 X1 X0 X0 X1 (X1 ◇ X1)]
  have l2 : ∀ sK1 sK2 sK3 sK0 X0 X1 X2 : G, sK1 = (((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) := by
    intro sK1 sK2 sK3 sK0 X0 X1 X2
    conv => enter [1]; rw [h4820 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) X0 X1 X2]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l3 : ∀ sK1 sK2 sK3 sK0 X0 X1 X2 : G, sK1 = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK1 sK2 sK3 sK0 X0 X1 X2
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0 X0 X1 X2]
    conv => enter [1]; rw [h43 ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ X2))) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK3 sK0 sK1 sK1 sK1]
    conv => enter [1]; rw [l1 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation43_4512_4820_implies_Equation4724 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4820 : Equation4820 G) : Equation4724 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4820 X0 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4820 X1 X0 X0 X1 (X1 ◇ X1)]
  have l2 : ∀ sK0 sK1 X0 X1 X2 : G, sK0 = (((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [h4820 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0 X1 X2]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l3 : ∀ sK0 sK1 X0 X1 X2 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l2 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation43_4512_4820_implies_Equation4725 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4820 : Equation4820 G) : Equation4725 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4820 X0 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4820 X1 X0 X0 X1 (X1 ◇ X1)]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, sK0 = (((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [h4820 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0 X1 X2]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l3 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_4512_4820_implies_Equation4728 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4820 : Equation4820 G) : Equation4728 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4820 X0 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4820 X1 X0 X0 X1 (X1 ◇ X1)]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, sK0 = (((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [h4820 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) X0 X1 X2]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l3 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_4512_4820_implies_Equation4729 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4820 : Equation4820 G) : Equation4729 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4820 X0 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4820 X1 X0 X0 X1 (X1 ◇ X1)]
  have l2 : ∀ sK1 sK2 sK3 sK0 X0 X1 X2 : G, sK1 = (((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) := by
    intro sK1 sK2 sK3 sK0 X0 X1 X2
    conv => enter [1]; rw [h4820 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) X0 X1 X2]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l3 : ∀ sK1 sK2 sK3 sK0 X0 X1 X2 : G, sK1 = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK1 sK2 sK3 sK0 X0 X1 X2
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0 X0 X1 X2]
    conv => enter [1]; rw [h43 ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ X2))) (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))))]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK3 sK0 sK1 sK1 sK1]
    conv => enter [1]; rw [l1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation43_4512_4820_implies_Equation4746 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4820 : Equation4820 G) : Equation4746 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4820 X0 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4820 X1 X0 X0 X1 (X1 ◇ X1)]
  have l2 : ∀ sK2 sK3 sK4 sK1 sK0 X0 X1 X2 : G, sK2 = (((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))))) := by
    intro sK2 sK3 sK4 sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [h4820 sK2 (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) X0 X1 X2]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 X0 X1 X2 : G, sK2 = ((sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))))) ◇ ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK2 sK3 sK4 sK1 sK0 X0 X1 X2
    conv => enter [1]; rw [l2 sK2 sK3 sK4 sK1 sK0 X0 X1 X2]
    conv => enter [1]; rw [h43 ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ X2))) (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))))]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, sK2 = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l3 sK2 sK3 sK4 sK1 sK0 sK2 sK2 sK2]
    conv => enter [1]; rw [l1 (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))))) ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ (sK2 ◇ (sK2 ◇ sK2)))]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

theorem Equation43_4512_4820_implies_Equation4799 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4820 : Equation4820 G) : Equation4799 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4820 X0 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4820 X1 X0 X0 X1 (X1 ◇ X1)]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, sK0 = (((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [h4820 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0 X1 X2]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l3 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [h43 ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2))) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_4512_4820_implies_Equation4802 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4820 : Equation4820 G) : Equation4802 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4820 X0 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4820 X1 X0 X0 X1 (X1 ◇ X1)]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, sK0 = (((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [h4820 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) X0 X1 X2]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l3 : ∀ sK0 sK1 sK2 X0 X1 X2 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK0 sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [h43 ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2))) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_4512_4820_implies_Equation4803 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4820 : Equation4820 G) : Equation4803 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4820 X0 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4820 X1 X0 X0 X1 (X1 ◇ X1)]
  have l2 : ∀ sK1 sK2 sK3 sK0 X0 X1 X2 : G, sK1 = (((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) := by
    intro sK1 sK2 sK3 sK0 X0 X1 X2
    conv => enter [1]; rw [h4820 sK1 (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) X0 X1 X2]
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l3 : ∀ sK1 sK2 sK3 sK0 X0 X1 X2 : G, sK1 = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK1 sK2 sK3 sK0 X0 X1 X2
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0 X0 X1 X2]
    conv => enter [1]; rw [h43 ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ X2))) (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))))]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK3 sK0 sK1 sK1 sK1]
    conv => enter [1]; rw [l1 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation43_4512_4820_implies_Equation4815 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4820 : Equation4820 G) : Equation4815 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4820 X0 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4820 X1 X0 X0 X1 (X1 ◇ X1)]
  have l2 : ∀ sK1 sK2 sK3 sK0 X0 X1 X2 : G, sK1 = (((sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))))) := by
    intro sK1 sK2 sK3 sK0 X0 X1 X2
    conv => enter [1]; rw [h4820 sK1 (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) X0 X1 X2]
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) ((sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l3 : ∀ sK1 sK2 sK3 sK0 X0 X1 X2 : G, sK1 = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))))) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK1 sK2 sK3 sK0 X0 X1 X2
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0 X0 X1 X2]
    conv => enter [1]; rw [h43 ((sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X1 ◇ X2))) (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))))]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK3 sK0 sK1 sK1 sK1]
    conv => enter [1]; rw [l1 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))))) ((sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation43_4512_4820_implies_Equation4897 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4820 : Equation4820 G) : Equation4897 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4820 X0 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4820 X1 X0 X0 X1 (X1 ◇ X1)]
  have l2 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 X0 X1 X2 : G, sK3 = (((sK4 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))) ◇ (sK3 ◇ (sK4 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [h4820 sK3 (sK4 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) X0 X1 X2]
    conv => enter [1]; rw [l0 sK3 (sK4 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ((sK4 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2)))]
  have l3 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 X0 X1 X2 : G, sK3 = ((sK3 ◇ (sK4 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))))) ◇ ((sK4 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1 X0 X1 X2
    conv => enter [1]; rw [l2 sK3 sK4 sK5 sK2 sK0 sK1 X0 X1 X2]
    conv => enter [1]; rw [h43 ((sK4 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ X2))) (sK3 ◇ (sK4 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))))]
  have l4 : ∀ sK3 sK4 sK5 sK2 sK0 sK1 : G, sK3 = (sK3 ◇ (sK4 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))))) := by
    intro sK3 sK4 sK5 sK2 sK0 sK1
    conv => enter [1]; rw [l3 sK3 sK4 sK5 sK2 sK0 sK1 sK3 sK3 sK3]
    conv => enter [1]; rw [l1 (sK3 ◇ (sK4 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1))))) ((sK4 ◇ (sK5 ◇ (sK2 ◇ (sK0 ◇ sK1)))) ◇ (sK3 ◇ (sK3 ◇ sK3)))]
  intro x y z w u v
  conv => enter [1]; rw [l4 x y z w u v]

theorem Equation43_4512_4815_implies_Equation2 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4815 : Equation4815 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4815 X0 X0 X0 X1]
    conv => enter [1]; rw [← h4815 X1 X0 X0 (X0 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X0 : G, ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) ◇ X0) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) X0]
    conv => enter [1]; rw [← h4815 X0 X1 X2 X3]
  have l2 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X0)) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X2 ◇ (X2 ◇ X3))) X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation43_4512_4815_implies_Equation4696 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4815 : Equation4815 G) : Equation4696 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4815 X0 X0 X0 X1]
    conv => enter [1]; rw [← h4815 X1 X0 X0 (X0 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X0 : G, ((X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) ◇ X0) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) X0]
    conv => enter [1]; rw [← h4815 X0 X1 X2 X3]
  have l2 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X0)) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X2 ◇ (X2 ◇ X3))) X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x (x ◇ (x ◇ (x ◇ (x ◇ (x ◇ y)))))]

theorem Equation43_4512_4815_implies_Equation4698 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4815 : Equation4815 G) : Equation4698 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4815 X0 X0 X0 X1]
    conv => enter [1]; rw [← h4815 X1 X0 X0 (X0 ◇ X1)]
  have l2 : ∀ sK0 sK1 X0 X1 : G, sK0 = (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4815 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X0 ◇ X1)))]
  have l3 : ∀ sK0 sK1 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X0 ◇ X1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation43_4512_4815_implies_Equation4699 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4815 : Equation4815 G) : Equation4699 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4815 X0 X0 X0 X1]
    conv => enter [1]; rw [← h4815 X1 X0 X0 (X0 ◇ X1)]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4815 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X0 ◇ X1)))]
  have l3 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X0 ◇ X1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_4512_4815_implies_Equation4704 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4815 : Equation4815 G) : Equation4704 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4815 X0 X0 X0 X1]
    conv => enter [1]; rw [← h4815 X1 X0 X0 (X0 ◇ X1)]
  have l2 : ∀ sK0 sK1 X0 X1 : G, sK0 = (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4815 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X0 ◇ X1)))]
  have l3 : ∀ sK0 sK1 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X0 ◇ X1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation43_4512_4815_implies_Equation4705 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4815 : Equation4815 G) : Equation4705 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4815 X0 X0 X0 X1]
    conv => enter [1]; rw [← h4815 X1 X0 X0 (X0 ◇ X1)]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4815 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X0 ◇ X1)))]
  have l3 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X0 ◇ X1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_4512_4815_implies_Equation4709 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4815 : Equation4815 G) : Equation4709 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4815 X0 X0 X0 X1]
    conv => enter [1]; rw [← h4815 X1 X0 X0 (X0 ◇ X1)]
  have l2 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, sK1 = (((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [h4815 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) X0 X1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X0 ◇ X1)))]
  have l3 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, sK1 = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0 X0 X1]
    conv => enter [1]; rw [h43 ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X0 ◇ X1))) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK3 sK0 sK1 sK1]
    conv => enter [1]; rw [l1 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation43_4512_4815_implies_Equation4724 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4815 : Equation4815 G) : Equation4724 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4815 X0 X0 X0 X1]
    conv => enter [1]; rw [← h4815 X1 X0 X0 (X0 ◇ X1)]
  have l2 : ∀ sK0 sK1 X0 X1 : G, sK0 = (((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4815 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X0 ◇ X1)))]
  have l3 : ∀ sK0 sK1 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X0 ◇ X1))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation43_4512_4815_implies_Equation4725 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4815 : Equation4815 G) : Equation4725 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4815 X0 X0 X0 X1]
    conv => enter [1]; rw [← h4815 X1 X0 X0 (X0 ◇ X1)]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = (((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4815 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X0 ◇ X1)))]
  have l3 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X0 ◇ X1))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_4512_4815_implies_Equation4728 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4815 : Equation4815 G) : Equation4728 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4815 X0 X0 X0 X1]
    conv => enter [1]; rw [← h4815 X1 X0 X0 (X0 ◇ X1)]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = (((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4815 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) X0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (X0 ◇ (X0 ◇ X1)))]
  have l3 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (X0 ◇ (X0 ◇ X1))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_4512_4815_implies_Equation4729 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4815 : Equation4815 G) : Equation4729 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4815 X0 X0 X0 X1]
    conv => enter [1]; rw [← h4815 X1 X0 X0 (X0 ◇ X1)]
  have l2 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, sK1 = (((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [h4815 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) X0 X1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X0 ◇ X1)))]
  have l3 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, sK1 = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0 X0 X1]
    conv => enter [1]; rw [h43 ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X0 ◇ X1))) (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))))]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK3 sK0 sK1 sK1]
    conv => enter [1]; rw [l1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation43_4512_4815_implies_Equation4746 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4815 : Equation4815 G) : Equation4746 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4815 X0 X0 X0 X1]
    conv => enter [1]; rw [← h4815 X1 X0 X0 (X0 ◇ X1)]
  have l2 : ∀ sK2 sK3 sK4 sK1 sK0 X0 X1 : G, sK2 = (((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))))) := by
    intro sK2 sK3 sK4 sK1 sK0 X0 X1
    conv => enter [1]; rw [h4815 sK2 (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) X0 X1]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (X0 ◇ X1)))]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 X0 X1 : G, sK2 = ((sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))))) ◇ ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK2 sK3 sK4 sK1 sK0 X0 X1
    conv => enter [1]; rw [l2 sK2 sK3 sK4 sK1 sK0 X0 X1]
    conv => enter [1]; rw [h43 ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (X0 ◇ X1))) (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))))]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, sK2 = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l3 sK2 sK3 sK4 sK1 sK0 sK2 sK2]
    conv => enter [1]; rw [l1 (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))))) ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ (sK2 ◇ (sK2 ◇ sK2)))]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

theorem Equation43_4512_4815_implies_Equation4799 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4815 : Equation4815 G) : Equation4799 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4815 X0 X0 X0 X1]
    conv => enter [1]; rw [← h4815 X1 X0 X0 (X0 ◇ X1)]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = (((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4815 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0 X1]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X0 ◇ X1)))]
  have l3 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h43 ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X0 ◇ X1))) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_4512_4815_implies_Equation4802 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4815 : Equation4815 G) : Equation4802 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4815 X0 X0 X0 X1]
    conv => enter [1]; rw [← h4815 X1 X0 X0 (X0 ◇ X1)]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = (((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4815 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) X0 X1]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (X0 ◇ (X0 ◇ X1)))]
  have l3 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h43 ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (X0 ◇ (X0 ◇ X1))) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (sK0 ◇ (sK0 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_4512_4815_implies_Equation4803 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4815 : Equation4815 G) : Equation4803 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4815 X0 X0 X0 X1]
    conv => enter [1]; rw [← h4815 X1 X0 X0 (X0 ◇ X1)]
  have l2 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, sK1 = (((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [h4815 sK1 (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) X0 X1]
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X0 ◇ X1)))]
  have l3 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, sK1 = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ◇ ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0 X0 X1]
    conv => enter [1]; rw [h43 ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ (X0 ◇ X1))) (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))))]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK3 sK0 sK1 sK1]
    conv => enter [1]; rw [l1 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ((sK2 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation43_4512_4815_implies_Equation4820 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4815 : Equation4815 G) : Equation4820 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4815 X0 X0 X0 X1]
    conv => enter [1]; rw [← h4815 X1 X0 X0 (X0 ◇ X1)]
  have l2 : ∀ sK2 sK3 sK4 sK1 sK0 X0 X1 : G, sK2 = (((sK3 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (X0 ◇ X1))) ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))))) := by
    intro sK2 sK3 sK4 sK1 sK0 X0 X1
    conv => enter [1]; rw [h4815 sK2 (sK3 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) X0 X1]
    conv => enter [1]; rw [l0 sK2 (sK3 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ((sK3 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (X0 ◇ X1)))]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 X0 X1 : G, sK2 = ((sK2 ◇ (sK3 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))))) ◇ ((sK3 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro sK2 sK3 sK4 sK1 sK0 X0 X1
    conv => enter [1]; rw [l2 sK2 sK3 sK4 sK1 sK0 X0 X1]
    conv => enter [1]; rw [h43 ((sK3 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ (X0 ◇ X1))) (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))))]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, sK2 = (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l3 sK2 sK3 sK4 sK1 sK0 sK2 sK2]
    conv => enter [1]; rw [l1 (sK2 ◇ (sK3 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))))) ((sK3 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ (sK2 ◇ (sK2 ◇ sK2)))]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

theorem Equation43_4512_4803_implies_Equation2 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4803 : Equation4803 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4803 X0 X0 X1 X1]
    conv => enter [1]; rw [← h4803 X1 X0 X0 (X1 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X0 : G, ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X0) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) X0]
    conv => enter [1]; rw [← h4803 X0 X1 X2 X3]
  have l2 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0)) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X1 ◇ (X2 ◇ X3))) X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation43_4512_4803_implies_Equation4696 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4803 : Equation4803 G) : Equation4696 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4803 X0 X0 X1 X1]
    conv => enter [1]; rw [← h4803 X1 X0 X0 (X1 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X0 : G, ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X0) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) X0]
    conv => enter [1]; rw [← h4803 X0 X1 X2 X3]
  have l2 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X0)) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X1 ◇ (X2 ◇ X3))) X0]
    conv => enter [1]; rw [l1 X1 X2 X3 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x (x ◇ (x ◇ (x ◇ (x ◇ (x ◇ y)))))]

theorem Equation43_4512_4803_implies_Equation4698 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4803 : Equation4803 G) : Equation4698 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4803 X0 X0 X1 X1]
    conv => enter [1]; rw [← h4803 X1 X0 X0 (X1 ◇ X1)]
  have l2 : ∀ sK0 sK1 X0 X1 : G, sK0 = (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4803 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)))]
  have l3 : ∀ sK0 sK1 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ sK0)))]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation43_4512_4803_implies_Equation4699 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4803 : Equation4803 G) : Equation4699 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4803 X0 X0 X1 X1]
    conv => enter [1]; rw [← h4803 X1 X0 X0 (X1 ◇ X1)]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4803 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1)))]
  have l3 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_4512_4803_implies_Equation4704 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4803 : Equation4803 G) : Equation4704 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4803 X0 X0 X1 X1]
    conv => enter [1]; rw [← h4803 X1 X0 X0 (X1 ◇ X1)]
  have l2 : ∀ sK0 sK1 X0 X1 : G, sK0 = (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4803 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)))]
  have l3 : ∀ sK0 sK1 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ sK0)))]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation43_4512_4803_implies_Equation4705 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4803 : Equation4803 G) : Equation4705 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4803 X0 X0 X1 X1]
    conv => enter [1]; rw [← h4803 X1 X0 X0 (X1 ◇ X1)]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4803 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1)))]
  have l3 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_4512_4803_implies_Equation4709 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4803 : Equation4803 G) : Equation4709 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4803 X0 X0 X1 X1]
    conv => enter [1]; rw [← h4803 X1 X0 X0 (X1 ◇ X1)]
  have l2 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, sK1 = (((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ X1))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [h4803 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) X0 X1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ X1)))]
  have l3 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, sK1 = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ X1)))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0 X0 X1]
    conv => enter [1]; rw [h43 ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ X1))) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK3 sK0 sK1 sK1]
    conv => enter [1]; rw [l1 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ sK1)))]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation43_4512_4803_implies_Equation4724 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4803 : Equation4803 G) : Equation4724 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4803 X0 X0 X1 X1]
    conv => enter [1]; rw [← h4803 X1 X0 X0 (X1 ◇ X1)]
  have l2 : ∀ sK0 sK1 X0 X1 : G, sK0 = (((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4803 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)))]
  have l3 : ∀ sK0 sK1 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 X0 X1]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ sK0)))]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation43_4512_4803_implies_Equation4725 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4803 : Equation4803 G) : Equation4725 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4803 X0 X0 X1 X1]
    conv => enter [1]; rw [← h4803 X1 X0 X0 (X1 ◇ X1)]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = (((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4803 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1)))]
  have l3 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_4512_4803_implies_Equation4728 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4803 : Equation4803 G) : Equation4728 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4803 X0 X0 X1 X1]
    conv => enter [1]; rw [← h4803 X1 X0 X0 (X1 ◇ X1)]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = (((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (X0 ◇ X1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4803 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) X0 X1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (X0 ◇ X1)))]
  have l3 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (X0 ◇ X1))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (sK0 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_4512_4803_implies_Equation4729 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4803 : Equation4803 G) : Equation4729 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4803 X0 X0 X1 X1]
    conv => enter [1]; rw [← h4803 X1 X0 X0 (X1 ◇ X1)]
  have l2 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, sK1 = (((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ X1))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [h4803 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) X0 X1]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ X1)))]
  have l3 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, sK1 = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ X1)))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0 X0 X1]
    conv => enter [1]; rw [h43 ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ X1))) (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))))]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK3 sK0 sK1 sK1]
    conv => enter [1]; rw [l1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ sK1)))]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation43_4512_4803_implies_Equation4746 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4803 : Equation4803 G) : Equation4746 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4803 X0 X0 X1 X1]
    conv => enter [1]; rw [← h4803 X1 X0 X0 (X1 ◇ X1)]
  have l2 : ∀ sK2 sK3 sK4 sK1 sK0 X0 X1 : G, sK2 = (((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ X1))) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))))) := by
    intro sK2 sK3 sK4 sK1 sK0 X0 X1
    conv => enter [1]; rw [h4803 sK2 (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) X0 X1]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ X1)))]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 X0 X1 : G, sK2 = ((sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))))) ◇ ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ X1)))) := by
    intro sK2 sK3 sK4 sK1 sK0 X0 X1
    conv => enter [1]; rw [l2 sK2 sK3 sK4 sK1 sK0 X0 X1]
    conv => enter [1]; rw [h43 ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ (X0 ◇ X1))) (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))))]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, sK2 = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l3 sK2 sK3 sK4 sK1 sK0 sK2 sK2]
    conv => enter [1]; rw [l1 (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))))) ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ (sK2 ◇ sK2)))]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

theorem Equation43_4512_4803_implies_Equation4799 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4803 : Equation4803 G) : Equation4799 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4803 X0 X0 X1 X1]
    conv => enter [1]; rw [← h4803 X1 X0 X0 (X1 ◇ X1)]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = (((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4803 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0 X1]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1)))]
  have l3 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h43 ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1))) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK0 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_4512_4803_implies_Equation4802 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4803 : Equation4803 G) : Equation4802 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4803 X0 X0 X1 X1]
    conv => enter [1]; rw [← h4803 X1 X0 X0 (X1 ◇ X1)]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = (((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (X0 ◇ X1))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4803 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) X0 X1]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (X0 ◇ X1)))]
  have l3 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [h43 ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (X0 ◇ X1))) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ (sK0 ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_4512_4803_implies_Equation4815 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4803 : Equation4803 G) : Equation4815 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4803 X0 X0 X1 X1]
    conv => enter [1]; rw [← h4803 X1 X0 X0 (X1 ◇ X1)]
  have l2 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, sK1 = (((sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ X1))) ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [h4803 sK1 (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) X0 X1]
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) ((sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ X1)))]
  have l3 : ∀ sK1 sK2 sK3 sK0 X0 X1 : G, sK1 = ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))))) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ X1)))) := by
    intro sK1 sK2 sK3 sK0 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0 X0 X1]
    conv => enter [1]; rw [h43 ((sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) ◇ (X0 ◇ X1))) (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))))]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK3 sK0 sK1 sK1]
    conv => enter [1]; rw [l1 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0))))) ((sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) ◇ ((sK2 ◇ (sK2 ◇ (sK3 ◇ (sK3 ◇ sK0)))) ◇ (sK1 ◇ sK1)))]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation43_4512_4802_implies_Equation2 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4802 : Equation4802 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X1 X0 X2]
    conv => enter [1]; rw [h43 (X1 ◇ X0) X2]
  have l2 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [l1 (X0 ◇ X0) X1 X1]
    conv => enter [1]; rw [← h4802 X2 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4802 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h4802 X1 (X0 ◇ X0) (X0 ◇ X0)]
  have l4 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X0) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) X0]
    conv => enter [1]; rw [← h4802 X0 X1 X2]
  have l5 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X1 ◇ (X2 ◇ X2))) X0]
    conv => enter [1]; rw [l4 X1 X2 X0]
  have l6 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ X0))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l3 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l2 X2 X1 X0]
  have l7 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X1 (X1 ◇ (X2 ◇ X2)) X0]
    conv => enter [1]; rw [l5 X1 X2 X0]
  have l8 : ∀ X2 X1 : G, (X2 ◇ X1) = X2 := by
    intro X2 X1
    conv => enter [1, 2]; rw [← l3 X1 X2]
    conv => enter [1]; rw [l6 X2 X1 X2]
  have l9 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0)))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h4512 X1 (X2 ◇ X2) X0]
    conv => enter [1]; rw [l7 X1 X2 X0]
  have l10 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))]
    conv => enter [1]; rw [l9 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation43_4512_4802_implies_Equation4696 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4802 : Equation4802 G) : Equation4696 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l0 X1 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h4802 X2 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4802 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h4802 X1 (X0 ◇ X0) (X0 ◇ X0)]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X0) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) X0]
    conv => enter [1]; rw [← h4802 X0 X1 X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X1 ◇ (X2 ◇ X2))) X0]
    conv => enter [1]; rw [l3 X1 X2 X0]
  have l5 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ X0))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l2 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l1 X2 X1 X0]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X1 (X1 ◇ (X2 ◇ X2)) X0]
    conv => enter [1]; rw [l4 X1 X2 X0]
  have l7 : ∀ X2 X1 : G, (X2 ◇ X1) = X2 := by
    intro X2 X1
    conv => enter [1, 2]; rw [← l2 X1 X2]
    conv => enter [1]; rw [l5 X2 X1 X2]
  have l8 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0)))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h4512 X1 (X2 ◇ X2) X0]
    conv => enter [1]; rw [l6 X1 X2 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))]
    conv => enter [1]; rw [l8 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x (x ◇ (x ◇ (x ◇ (x ◇ (x ◇ y)))))]

theorem Equation43_4512_4802_implies_Equation4698 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4802 : Equation4802 G) : Equation4698 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l0 X1 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h4802 X2 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4802 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h4802 X1 (X0 ◇ X0) (X0 ◇ X0)]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X0) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) X0]
    conv => enter [1]; rw [← h4802 X0 X1 X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X1 ◇ (X2 ◇ X2))) X0]
    conv => enter [1]; rw [l3 X1 X2 X0]
  have l5 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ X0))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l2 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l1 X2 X1 X0]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X1 (X1 ◇ (X2 ◇ X2)) X0]
    conv => enter [1]; rw [l4 X1 X2 X0]
  have l7 : ∀ X2 X1 : G, (X2 ◇ X1) = X2 := by
    intro X2 X1
    conv => enter [1, 2]; rw [← l2 X1 X2]
    conv => enter [1]; rw [l5 X2 X1 X2]
  have l8 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0)))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h4512 X1 (X2 ◇ X2) X0]
    conv => enter [1]; rw [l6 X1 X2 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))]
    conv => enter [1]; rw [l8 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ y)))))]

theorem Equation43_4512_4802_implies_Equation4699 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4802 : Equation4802 G) : Equation4699 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l0 X1 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h4802 X2 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4802 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h4802 X1 (X0 ◇ X0) (X0 ◇ X0)]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X0) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) X0]
    conv => enter [1]; rw [← h4802 X0 X1 X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X1 ◇ (X2 ◇ X2))) X0]
    conv => enter [1]; rw [l3 X1 X2 X0]
  have l5 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ X0))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l2 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l1 X2 X1 X0]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X1 (X1 ◇ (X2 ◇ X2)) X0]
    conv => enter [1]; rw [l4 X1 X2 X0]
  have l7 : ∀ X2 X1 : G, (X2 ◇ X1) = X2 := by
    intro X2 X1
    conv => enter [1, 2]; rw [← l2 X1 X2]
    conv => enter [1]; rw [l5 X2 X1 X2]
  have l8 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0)))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h4512 X1 (X2 ◇ X2) X0]
    conv => enter [1]; rw [l6 X1 X2 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))]
    conv => enter [1]; rw [l8 X0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l9 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ z)))))]

theorem Equation43_4512_4802_implies_Equation4704 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4802 : Equation4802 G) : Equation4704 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l0 X1 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h4802 X2 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4802 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h4802 X1 (X0 ◇ X0) (X0 ◇ X0)]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X0) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) X0]
    conv => enter [1]; rw [← h4802 X0 X1 X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X1 ◇ (X2 ◇ X2))) X0]
    conv => enter [1]; rw [l3 X1 X2 X0]
  have l5 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ X0))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l2 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l1 X2 X1 X0]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X1 (X1 ◇ (X2 ◇ X2)) X0]
    conv => enter [1]; rw [l4 X1 X2 X0]
  have l7 : ∀ X2 X1 : G, (X2 ◇ X1) = X2 := by
    intro X2 X1
    conv => enter [1, 2]; rw [← l2 X1 X2]
    conv => enter [1]; rw [l5 X2 X1 X2]
  have l8 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0)))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h4512 X1 (X2 ◇ X2) X0]
    conv => enter [1]; rw [l6 X1 X2 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))]
    conv => enter [1]; rw [l8 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ y)))))]

theorem Equation43_4512_4802_implies_Equation4705 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4802 : Equation4802 G) : Equation4705 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l0 X1 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h4802 X2 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4802 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h4802 X1 (X0 ◇ X0) (X0 ◇ X0)]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X0) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) X0]
    conv => enter [1]; rw [← h4802 X0 X1 X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X1 ◇ (X2 ◇ X2))) X0]
    conv => enter [1]; rw [l3 X1 X2 X0]
  have l5 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ X0))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l2 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l1 X2 X1 X0]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X1 (X1 ◇ (X2 ◇ X2)) X0]
    conv => enter [1]; rw [l4 X1 X2 X0]
  have l7 : ∀ X2 X1 : G, (X2 ◇ X1) = X2 := by
    intro X2 X1
    conv => enter [1, 2]; rw [← l2 X1 X2]
    conv => enter [1]; rw [l5 X2 X1 X2]
  have l8 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0)))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h4512 X1 (X2 ◇ X2) X0]
    conv => enter [1]; rw [l6 X1 X2 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))]
    conv => enter [1]; rw [l8 X0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l9 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ z)))))]

theorem Equation43_4512_4802_implies_Equation4709 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4802 : Equation4802 G) : Equation4709 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l0 X1 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h4802 X2 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4802 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h4802 X1 (X0 ◇ X0) (X0 ◇ X0)]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X0) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) X0]
    conv => enter [1]; rw [← h4802 X0 X1 X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X1 ◇ (X2 ◇ X2))) X0]
    conv => enter [1]; rw [l3 X1 X2 X0]
  have l5 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ X0))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l2 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l1 X2 X1 X0]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X1 (X1 ◇ (X2 ◇ X2)) X0]
    conv => enter [1]; rw [l4 X1 X2 X0]
  have l7 : ∀ X2 X1 : G, (X2 ◇ X1) = X2 := by
    intro X2 X1
    conv => enter [1, 2]; rw [← l2 X1 X2]
    conv => enter [1]; rw [l5 X2 X1 X2]
  have l8 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0)))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h4512 X1 (X2 ◇ X2) X0]
    conv => enter [1]; rw [l6 X1 X2 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))]
    conv => enter [1]; rw [l8 X0 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l9 x (x ◇ (x ◇ (x ◇ (y ◇ (z ◇ w)))))]

theorem Equation43_4512_4802_implies_Equation4724 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4802 : Equation4802 G) : Equation4724 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l0 X1 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h4802 X2 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4802 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h4802 X1 (X0 ◇ X0) (X0 ◇ X0)]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X0) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) X0]
    conv => enter [1]; rw [← h4802 X0 X1 X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X1 ◇ (X2 ◇ X2))) X0]
    conv => enter [1]; rw [l3 X1 X2 X0]
  have l5 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ X0))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l2 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l1 X2 X1 X0]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X1 (X1 ◇ (X2 ◇ X2)) X0]
    conv => enter [1]; rw [l4 X1 X2 X0]
  have l7 : ∀ X2 X1 : G, (X2 ◇ X1) = X2 := by
    intro X2 X1
    conv => enter [1, 2]; rw [← l2 X1 X2]
    conv => enter [1]; rw [l5 X2 X1 X2]
  have l8 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0)))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h4512 X1 (X2 ◇ X2) X0]
    conv => enter [1]; rw [l6 X1 X2 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))]
    conv => enter [1]; rw [l8 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y)))))]

theorem Equation43_4512_4802_implies_Equation4725 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4802 : Equation4802 G) : Equation4725 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l0 X1 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h4802 X2 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4802 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h4802 X1 (X0 ◇ X0) (X0 ◇ X0)]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X0) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) X0]
    conv => enter [1]; rw [← h4802 X0 X1 X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X1 ◇ (X2 ◇ X2))) X0]
    conv => enter [1]; rw [l3 X1 X2 X0]
  have l5 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ X0))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l2 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l1 X2 X1 X0]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X1 (X1 ◇ (X2 ◇ X2)) X0]
    conv => enter [1]; rw [l4 X1 X2 X0]
  have l7 : ∀ X2 X1 : G, (X2 ◇ X1) = X2 := by
    intro X2 X1
    conv => enter [1, 2]; rw [← l2 X1 X2]
    conv => enter [1]; rw [l5 X2 X1 X2]
  have l8 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0)))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h4512 X1 (X2 ◇ X2) X0]
    conv => enter [1]; rw [l6 X1 X2 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))]
    conv => enter [1]; rw [l8 X0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l9 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ z)))))]

theorem Equation43_4512_4802_implies_Equation4728 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4802 : Equation4802 G) : Equation4728 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l0 X1 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h4802 X2 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4802 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h4802 X1 (X0 ◇ X0) (X0 ◇ X0)]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X0) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) X0]
    conv => enter [1]; rw [← h4802 X0 X1 X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X1 ◇ (X2 ◇ X2))) X0]
    conv => enter [1]; rw [l3 X1 X2 X0]
  have l5 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ X0))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l2 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l1 X2 X1 X0]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X1 (X1 ◇ (X2 ◇ X2)) X0]
    conv => enter [1]; rw [l4 X1 X2 X0]
  have l7 : ∀ X2 X1 : G, (X2 ◇ X1) = X2 := by
    intro X2 X1
    conv => enter [1, 2]; rw [← l2 X1 X2]
    conv => enter [1]; rw [l5 X2 X1 X2]
  have l8 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0)))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h4512 X1 (X2 ◇ X2) X0]
    conv => enter [1]; rw [l6 X1 X2 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))]
    conv => enter [1]; rw [l8 X0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l9 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ z)))))]

theorem Equation43_4512_4802_implies_Equation4729 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4802 : Equation4802 G) : Equation4729 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l0 X1 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h4802 X2 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4802 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h4802 X1 (X0 ◇ X0) (X0 ◇ X0)]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X0) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) X0]
    conv => enter [1]; rw [← h4802 X0 X1 X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X1 ◇ (X2 ◇ X2))) X0]
    conv => enter [1]; rw [l3 X1 X2 X0]
  have l5 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ X0))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l2 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l1 X2 X1 X0]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X1 (X1 ◇ (X2 ◇ X2)) X0]
    conv => enter [1]; rw [l4 X1 X2 X0]
  have l7 : ∀ X2 X1 : G, (X2 ◇ X1) = X2 := by
    intro X2 X1
    conv => enter [1, 2]; rw [← l2 X1 X2]
    conv => enter [1]; rw [l5 X2 X1 X2]
  have l8 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0)))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h4512 X1 (X2 ◇ X2) X0]
    conv => enter [1]; rw [l6 X1 X2 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))]
    conv => enter [1]; rw [l8 X0 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l9 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ w)))))]

theorem Equation43_4512_4802_implies_Equation4746 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4802 : Equation4802 G) : Equation4746 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l0 X1 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h4802 X2 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4802 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h4802 X1 (X0 ◇ X0) (X0 ◇ X0)]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X0) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) X0]
    conv => enter [1]; rw [← h4802 X0 X1 X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X1 ◇ (X2 ◇ X2))) X0]
    conv => enter [1]; rw [l3 X1 X2 X0]
  have l5 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ X0))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l2 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l1 X2 X1 X0]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X1 (X1 ◇ (X2 ◇ X2)) X0]
    conv => enter [1]; rw [l4 X1 X2 X0]
  have l7 : ∀ X2 X1 : G, (X2 ◇ X1) = X2 := by
    intro X2 X1
    conv => enter [1, 2]; rw [← l2 X1 X2]
    conv => enter [1]; rw [l5 X2 X1 X2]
  have l8 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0)))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h4512 X1 (X2 ◇ X2) X0]
    conv => enter [1]; rw [l6 X1 X2 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))]
    conv => enter [1]; rw [l8 X0 X0 X1]
  intro x y z w u
  conv => enter [1]; rw [l9 x (x ◇ (x ◇ (y ◇ (z ◇ (w ◇ u)))))]

theorem Equation43_4512_4802_implies_Equation4799 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4802 : Equation4802 G) : Equation4799 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l0 X1 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h4802 X2 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4802 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h4802 X1 (X0 ◇ X0) (X0 ◇ X0)]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X0) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) X0]
    conv => enter [1]; rw [← h4802 X0 X1 X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X1 ◇ (X2 ◇ X2))) X0]
    conv => enter [1]; rw [l3 X1 X2 X0]
  have l5 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ X0))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l2 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l1 X2 X1 X0]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X1 (X1 ◇ (X2 ◇ X2)) X0]
    conv => enter [1]; rw [l4 X1 X2 X0]
  have l7 : ∀ X2 X1 : G, (X2 ◇ X1) = X2 := by
    intro X2 X1
    conv => enter [1, 2]; rw [← l2 X1 X2]
    conv => enter [1]; rw [l5 X2 X1 X2]
  have l8 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0)))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h4512 X1 (X2 ◇ X2) X0]
    conv => enter [1]; rw [l6 X1 X2 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))]
    conv => enter [1]; rw [l8 X0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l9 x (x ◇ (y ◇ (y ◇ (y ◇ (y ◇ z)))))]

theorem Equation43_4512_4802_implies_Equation4803 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4802 : Equation4802 G) : Equation4803 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l0 X1 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← h4802 X2 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4802 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h4802 X1 (X0 ◇ X0) (X0 ◇ X0)]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X0) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X2)))) X0]
    conv => enter [1]; rw [← h4802 X0 X1 X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X1 ◇ (X2 ◇ X2))) X0]
    conv => enter [1]; rw [l3 X1 X2 X0]
  have l5 : ∀ X2 X1 X0 : G, (X2 ◇ (X1 ◇ (X0 ◇ X0))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2]; rw [← l2 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l1 X2 X1 X0]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X0))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X1 (X1 ◇ (X2 ◇ X2)) X0]
    conv => enter [1]; rw [l4 X1 X2 X0]
  have l7 : ∀ X2 X1 : G, (X2 ◇ X1) = X2 := by
    intro X2 X1
    conv => enter [1, 2]; rw [← l2 X1 X2]
    conv => enter [1]; rw [l5 X2 X1 X2]
  have l8 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X0)))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h4512 X1 (X2 ◇ X2) X0]
    conv => enter [1]; rw [l6 X1 X2 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1)))]
    conv => enter [1]; rw [l8 X0 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l9 x (x ◇ (y ◇ (y ◇ (y ◇ (z ◇ w)))))]

theorem Equation43_4512_4799_implies_Equation2 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4799 : Equation4799 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4799 X0 X0 X1]
    conv => enter [1]; rw [← h4799 X1 X0 (X0 ◇ X1)]
  have l1 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X0) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) X0]
    conv => enter [1]; rw [← h4799 X0 X1 X2]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X1 ◇ (X1 ◇ X2))) X0]
    conv => enter [1]; rw [l1 X1 X2 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation43_4512_4799_implies_Equation4696 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4799 : Equation4799 G) : Equation4696 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4799 X0 X0 X1]
    conv => enter [1]; rw [← h4799 X1 X0 (X0 ◇ X1)]
  have l1 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X0) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h43 (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) X0]
    conv => enter [1]; rw [← h4799 X0 X1 X2]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X1 ◇ (X1 ◇ X2))) X0]
    conv => enter [1]; rw [l1 X1 X2 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X1)]
    conv => enter [1]; rw [l2 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x (x ◇ (x ◇ (x ◇ (x ◇ (x ◇ y)))))]

theorem Equation43_4512_4799_implies_Equation4698 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4799 : Equation4799 G) : Equation4698 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4799 X0 X0 X1]
    conv => enter [1]; rw [← h4799 X1 X0 (X0 ◇ X1)]
  have l2 : ∀ sK0 sK1 X0 : G, sK0 = (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4799 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)))]
  have l3 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X0))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ sK0)))]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation43_4512_4799_implies_Equation4699 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4799 : Equation4799 G) : Equation4699 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4799 X0 X0 X1]
    conv => enter [1]; rw [← h4799 X1 X0 (X0 ◇ X1)]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, sK0 = (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4799 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0)))]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X0))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_4512_4799_implies_Equation4704 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4799 : Equation4799 G) : Equation4704 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4799 X0 X0 X1]
    conv => enter [1]; rw [← h4799 X1 X0 (X0 ◇ X1)]
  have l2 : ∀ sK0 sK1 X0 : G, sK0 = (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4799 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0)))]
  have l3 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK0)))]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation43_4512_4799_implies_Equation4705 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4799 : Equation4799 G) : Equation4705 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4799 X0 X0 X1]
    conv => enter [1]; rw [← h4799 X1 X0 (X0 ◇ X1)]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, sK0 = (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0))) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4799 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0)))]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0))) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_4512_4799_implies_Equation4709 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4799 : Equation4799 G) : Equation4709 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4799 X0 X0 X1]
    conv => enter [1]; rw [← h4799 X1 X0 (X0 ◇ X1)]
  have l2 : ∀ sK1 sK2 sK3 sK0 X0 : G, sK1 = (((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0))) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h4799 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) X0]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0)))]
  have l3 : ∀ sK1 sK2 sK3 sK0 X0 : G, sK1 = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0)))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [h43 ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0))) (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))))]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l1 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ sK1)))]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation43_4512_4799_implies_Equation4724 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4799 : Equation4799 G) : Equation4724 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4799 X0 X0 X1]
    conv => enter [1]; rw [← h4799 X1 X0 (X0 ◇ X1)]
  have l2 : ∀ sK0 sK1 X0 : G, sK0 = (((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4799 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0)))]
  have l3 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ sK0)))]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation43_4512_4799_implies_Equation4725 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4799 : Equation4799 G) : Equation4725 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4799 X0 X0 X1]
    conv => enter [1]; rw [← h4799 X1 X0 (X0 ◇ X1)]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, sK0 = (((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4799 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0)))]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_4512_4799_implies_Equation4728 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4799 : Equation4799 G) : Equation4728 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4799 X0 X0 X1]
    conv => enter [1]; rw [← h4799 X1 X0 (X0 ◇ X1)]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, sK0 = (((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ X0))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4799 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) X0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ X0)))]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ X0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ X0))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_4512_4799_implies_Equation4729 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4799 : Equation4799 G) : Equation4729 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4799 X0 X0 X1]
    conv => enter [1]; rw [← h4799 X1 X0 (X0 ◇ X1)]
  have l2 : ∀ sK1 sK2 sK3 sK0 X0 : G, sK1 = (((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0))) ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [h4799 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) X0]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0)))]
  have l3 : ∀ sK1 sK2 sK3 sK0 X0 : G, sK1 = ((sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0)))) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l2 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [h43 ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ X0))) (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))))]
  have l4 : ∀ sK1 sK2 sK3 sK0 : G, sK1 = (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l3 sK1 sK2 sK3 sK0 sK1]
    conv => enter [1]; rw [l1 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ ((sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) ◇ sK1)))]
  intro x y z w
  conv => enter [1]; rw [l4 x y z w]

theorem Equation43_4512_4799_implies_Equation4746 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4799 : Equation4799 G) : Equation4746 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4799 X0 X0 X1]
    conv => enter [1]; rw [← h4799 X1 X0 (X0 ◇ X1)]
  have l2 : ∀ sK2 sK3 sK4 sK1 sK0 X0 : G, sK2 = (((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ X0))) ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))))) := by
    intro sK2 sK3 sK4 sK1 sK0 X0
    conv => enter [1]; rw [h4799 sK2 (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) X0]
    conv => enter [1]; rw [l0 sK2 (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ X0)))]
  have l3 : ∀ sK2 sK3 sK4 sK1 sK0 X0 : G, sK2 = ((sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))))) ◇ ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ X0)))) := by
    intro sK2 sK3 sK4 sK1 sK0 X0
    conv => enter [1]; rw [l2 sK2 sK3 sK4 sK1 sK0 X0]
    conv => enter [1]; rw [h43 ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ X0))) (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))))]
  have l4 : ∀ sK2 sK3 sK4 sK1 sK0 : G, sK2 = (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))))) := by
    intro sK2 sK3 sK4 sK1 sK0
    conv => enter [1]; rw [l3 sK2 sK3 sK4 sK1 sK0 sK2]
    conv => enter [1]; rw [l1 (sK2 ◇ (sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0))))) ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ ((sK2 ◇ (sK3 ◇ (sK4 ◇ (sK1 ◇ sK0)))) ◇ sK2)))]
  intro x y z w u
  conv => enter [1]; rw [l4 x y z w u]

theorem Equation43_4512_4799_implies_Equation4802 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4799 : Equation4799 G) : Equation4802 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4799 X0 X0 X1]
    conv => enter [1]; rw [← h4799 X1 X0 (X0 ◇ X1)]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, sK0 = (((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ X0))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h4799 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) X0]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ X0)))]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, sK0 = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ X0)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [h43 ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ X0))) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))]
  have l4 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [l1 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) ◇ sK0)))]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

theorem Equation43_4512_4798_implies_Equation4695 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4798 : Equation4798 G) : Equation4695 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))) = X0 := by
    intro X0 sK0
    conv => enter [1, 2, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h4798 X0 sK0]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0))) = X0 := by
    intro X0 sK0
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1]; rw [l1 X0 sK0]
  have l3 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0))) = X0 := by
    intro X0 sK0
    conv => enter [1, 2]; rw [← l0 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
    conv => enter [1]; rw [l2 X0 sK0]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = X0 := by
    intro X0 sK0
    conv => enter [1, 2]; rw [← l0 sK0 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [l3 X0 sK0]
  have l5 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) = X0 := by
    intro X0 sK0
    conv => enter [1, 2]; rw [← h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l4 X0 sK0]
  have l6 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))))) = X0 := by
    intro X0 sK0
    conv => enter [1, 2]; rw [h4512 sK0 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1]; rw [l5 X0 sK0]
  intro x
  conv => enter [1]; rw [← l6 x x]

theorem Equation43_4512_4746_implies_Equation2 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4746 : Equation4746 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4746 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4746 X1 X0 X0 X1 (X1 ◇ (X1 ◇ X1))]
  have l2 : ∀ X0 X5 X1 X2 X3 X4 : G, (X0 ◇ X5) = (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X5)) := by
    intro X0 X5 X1 X2 X3 X4
    conv => enter [1, 1]; rw [h4746 X0 X1 X2 X3 X4]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) X5]
  have l3 : ∀ X5 X0 X1 X2 X3 X4 : G, (X5 ◇ X0) = (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X5)) := by
    intro X5 X0 X1 X2 X3 X4
    conv => enter [1, 2]; rw [h4746 X0 X1 X2 X3 X4]
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) X5]
  have l4 : ∀ X5 X0 X1 X2 X3 X4 : G, (X5 ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5))) := by
    intro X5 X0 X1 X2 X3 X4
    conv => enter [1]; rw [l3 X5 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (X3 ◇ X4))) X5]
  have l5 : ∀ X0 X5 X1 X2 X3 X4 : G, (X0 ◇ X5) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5))) := by
    intro X0 X5 X1 X2 X3 X4
    conv => enter [1]; rw [l2 X0 X5 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (X3 ◇ X4))) X5]
  have l6 : ∀ X5 X0 : G, (X5 ◇ X0) = X0 := by
    intro X5 X0
    conv => enter [1]; rw [l4 X5 X0 X5 X5 X5 X5]
    conv => enter [1]; rw [l1 X0 ((X5 ◇ (X5 ◇ (X5 ◇ X5))) ◇ X5)]
  have l7 : ∀ X0 X5 : G, (X0 ◇ X5) = X0 := by
    intro X0 X5
    conv => enter [1]; rw [l5 X0 X5 X0 X0 X0 X0]
    conv => enter [1]; rw [l1 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X5)]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation4512_4746_implies_Equation4696 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4746 : Equation4746 G) : Equation4696 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4746 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4746 X1 X0 X0 X1 (X1 ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X5)) = (X0 ◇ X5) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) X5]
    conv => enter [1, 1]; rw [← h4746 X0 X1 X2 X3 X4]
  have l2 : ∀ X0 X5 X1 X2 X3 X4 : G, (X0 ◇ X5) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5))) := by
    intro X0 X5 X1 X2 X3 X4
    conv => enter [1]; rw [← l1 X0 X1 X2 X3 X4 X5]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (X3 ◇ X4))) X5]
  have l3 : ∀ X0 X5 : G, (X0 ◇ X5) = X0 := by
    intro X0 X5
    conv => enter [1]; rw [l2 X0 X5 X0 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X5)]
  intro x y
  conv => enter [1]; rw [← l3 x (x ◇ (x ◇ (x ◇ (x ◇ y))))]

theorem Equation43_4512_4746_implies_Equation4698 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4746 : Equation4746 G) : Equation4698 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (sK1 ◇ (X0 ◇ sK1)) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1, 2]; rw [h43 sK1 X0]
  have l3 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ (X1 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l2 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 sK1]
  have l4 : ∀ sK1 X0 X1 : G, (((sK1 ◇ sK1) ◇ X0) ◇ X1) = ((X0 ◇ sK1) ◇ (sK1 ◇ X1)) := by
    intro sK1 X0 X1
    conv => enter [1, 1]; rw [l2 sK1 X0]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ sK1) X1]
  have l5 : ∀ sK1 X0 X1 : G, (((sK1 ◇ sK1) ◇ X0) ◇ X1) = (sK1 ◇ (X1 ◇ (X0 ◇ sK1))) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l4 sK1 X0 X1]
    conv => enter [1]; rw [← l1 sK1 X1 (X0 ◇ sK1)]
  have l6 : ∀ sK1 X0 X1 : G, (((sK1 ◇ sK1) ◇ X0) ◇ X1) = ((sK1 ◇ sK1) ◇ (X1 ◇ X0)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [l5 sK1 X0 X1]
    conv => enter [1]; rw [← l3 sK1 X1 X0]
  have l7 : ∀ sK1 X0 X1 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ X1)) = ((sK1 ◇ sK1) ◇ (X1 ◇ X0)) := by
    intro sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ sK1) X0 X1]
    conv => enter [1]; rw [l6 sK1 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4746 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4746 X1 X0 X0 X1 (X1 ◇ (X1 ◇ X1))]
  have l9 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X5)) = (X5 ◇ X0) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [l1 X0 (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) X5]
    conv => enter [1, 2]; rw [← h4746 X0 X1 X2 X3 X4]
  have l10 : ∀ sK1 X0 X1 X2 X3 : G, sK1 = ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro sK1 X0 X1 X2 X3
    conv => enter [1]; rw [h4746 sK1 X0 X1 X2 X3]
    conv => enter [1]; rw [h4512 sK1 sK1 (X0 ◇ (X1 ◇ (X2 ◇ X3)))]
  have l11 : ∀ sK0 sK1 X0 X1 X2 X3 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro sK0 sK1 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4746 (sK1 ◇ sK1) X0 X1 X2 X3]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ sK1) ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))]
  have l12 : ∀ sK0 sK1 X0 X1 X2 X3 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0 X1 X2 X3
    conv => enter [1]; rw [l11 sK0 sK1 X0 X1 X2 X3]
    conv => enter [1]; rw [← l1 (sK1 ◇ sK1) (X0 ◇ (X1 ◇ (X2 ◇ X3))) (sK0 ◇ (sK1 ◇ sK1))]
  have l13 : ∀ X5 X0 X1 X2 X3 X4 : G, (X5 ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5))) := by
    intro X5 X0 X1 X2 X3 X4
    conv => enter [1]; rw [← l9 X0 X1 X2 X3 X4 X5]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (X3 ◇ X4))) X5]
  have l14 : ∀ sK0 sK1 X0 X1 X2 X3 : G, (sK0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro sK0 sK1 X0 X1 X2 X3
    conv => enter [1]; rw [l12 sK0 sK1 X0 X1 X2 X3]
    conv => enter [1]; rw [l7 sK1 (X0 ◇ (X1 ◇ (X2 ◇ X3))) (sK0 ◇ (sK1 ◇ sK1))]
  have l15 : ∀ X5 X0 : G, (X5 ◇ X0) = X0 := by
    intro X5 X0
    conv => enter [1]; rw [l13 X5 X0 X5 X5 X5 X5]
    conv => enter [1]; rw [l8 X0 ((X5 ◇ (X5 ◇ (X5 ◇ X5))) ◇ X5)]
  have l16 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l10 sK1 (sK0 ◇ (sK1 ◇ sK1)) sK1 sK1 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l14 sK0 sK1 sK1 sK1 sK1 sK1]
  have l17 : ∀ sK1 : G, sK1 = (sK1 ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [l16 sK1 sK1]
    conv => enter [1, 2]; rw [l15 sK1 sK1]
  have l18 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l1 sK0 (sK1 ◇ sK1) X0]
    conv => enter [1, 2, 1]; rw [← l17 sK1]
  have l19 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (X0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← l15 sK0 (sK1 ◇ X0)]
    conv => enter [1]; rw [← l18 X0 sK0 sK1]
  have l20 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l15 X0 (sK0 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l19 sK1 X0 sK0]
  have l21 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = X0 := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l20 sK0 sK1 X0]
    conv => enter [1]; rw [l15 sK1 X0]
  intro x y
  conv => enter [1]; rw [← l21 x y x]
  conv => enter [1]; rw [l21 x y (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ y)))))]

theorem Equation4512_4746_implies_Equation4699 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4746 : Equation4746 G) : Equation4699 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4746 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4746 X1 X0 X0 X1 (X1 ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X5)) = (X0 ◇ X5) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) X5]
    conv => enter [1, 1]; rw [← h4746 X0 X1 X2 X3 X4]
  have l2 : ∀ X0 X5 X1 X2 X3 X4 : G, (X0 ◇ X5) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5))) := by
    intro X0 X5 X1 X2 X3 X4
    conv => enter [1]; rw [← l1 X0 X1 X2 X3 X4 X5]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (X3 ◇ X4))) X5]
  have l3 : ∀ X0 X5 : G, (X0 ◇ X5) = X0 := by
    intro X0 X5
    conv => enter [1]; rw [l2 X0 X5 X0 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X5)]
  intro x y z
  conv => enter [1]; rw [← l3 x (x ◇ (x ◇ (x ◇ (y ◇ z))))]

theorem Equation43_4512_4746_implies_Equation4704 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4746 : Equation4746 G) : Equation4704 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l3 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (sK1 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l2 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l4 : ∀ sK0 sK1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 sK1]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) (sK1 ◇ (sK1 ◇ sK1))]
  have l5 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) := by
    intro sK1 sK0 X0
    conv => enter [1, 1]; rw [← l4 sK0 sK1]
    conv => enter [1]; rw [l0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
  have l6 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [l5 sK1 sK0 X0]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l7 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK1)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) X0]
    conv => enter [1]; rw [l6 sK1 sK0 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4746 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4746 X1 X0 X0 X1 (X1 ◇ (X1 ◇ X1))]
  have l9 : ∀ sK1 X0 X1 X2 : G, sK1 = (sK1 ◇ ((sK1 ◇ sK1) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK1 X0 X1 X2
    conv => enter [1]; rw [h4746 sK1 sK1 X0 X1 X2]
    conv => enter [1, 2]; rw [h4512 sK1 sK1 (X0 ◇ (X1 ◇ X2))]
  have l10 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X5)) = (X5 ◇ X0) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [l1 X0 (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) X5]
    conv => enter [1, 2]; rw [← h4746 X0 X1 X2 X3 X4]
  have l11 : ∀ sK0 sK1 X0 X1 X2 X3 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro sK0 sK1 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4746 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0 X1 X2 X3]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))]
  have l12 : ∀ sK0 sK1 X0 X1 X2 X3 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1 X2 X3
    conv => enter [1]; rw [l11 sK0 sK1 X0 X1 X2 X3]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) (X0 ◇ (X1 ◇ (X2 ◇ X3))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l13 : ∀ X5 X0 X1 X2 X3 X4 : G, (X5 ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5))) := by
    intro X5 X0 X1 X2 X3 X4
    conv => enter [1]; rw [← l10 X0 X1 X2 X3 X4 X5]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (X3 ◇ X4))) X5]
  have l14 : ∀ sK1 X0 X1 X2 : G, sK1 = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK1 X0 X1 X2
    conv => enter [1]; rw [l9 sK1 X0 X1 X2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK1) (X0 ◇ (X1 ◇ X2))]
  have l15 : ∀ sK0 sK1 X0 X1 X2 X3 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro sK0 sK1 X0 X1 X2 X3
    conv => enter [1]; rw [l12 sK0 sK1 X0 X1 X2 X3]
    conv => enter [1]; rw [← l7 sK1 sK0 (X0 ◇ (X1 ◇ (X2 ◇ X3)))]
  have l16 : ∀ X5 X0 : G, (X5 ◇ X0) = X0 := by
    intro X5 X0
    conv => enter [1]; rw [l13 X5 X0 X5 X5 X5 X5]
    conv => enter [1]; rw [l8 X0 ((X5 ◇ (X5 ◇ (X5 ◇ X5))) ◇ X5)]
  have l17 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l14 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l15 sK0 sK1 sK1 sK1 sK1 sK1]
  have l18 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l17 sK1 sK0]
    conv => enter [1, 2]; rw [l16 sK0 (sK1 ◇ (sK1 ◇ sK1))]
  have l19 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 2, 1]; rw [← l18 sK1 sK0]
  have l20 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [← l16 sK0 (sK1 ◇ X0)]
    conv => enter [1]; rw [← l19 X0 sK0 sK1]
  have l21 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK1 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l16 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
    conv => enter [1]; rw [← l20 sK1 X0 sK0]
  have l22 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = X0 := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l21 sK0 sK1 X0]
    conv => enter [1]; rw [l16 sK1 X0]
  intro x y
  conv => enter [1]; rw [← l22 x y x]
  conv => enter [1, 2]; rw [← l22 x y (x ◇ (y ◇ (y ◇ y)))]

theorem Equation43_4512_4746_implies_Equation4705 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4746 : Equation4746 G) : Equation4705 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ sK2)) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK1 ◇ sK2)) X0]
  have l3 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l2 sK0 sK1 sK2 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l4 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (sK1 ◇ (sK1 ◇ sK2))]
    conv => enter [1]; rw [← l2 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l5 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l4 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) (sK1 ◇ (sK1 ◇ sK2))]
  have l6 : ∀ sK0 sK1 sK2 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l3 sK0 sK1 sK2]
    conv => enter [1]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (sK1 ◇ (sK1 ◇ sK2))]
  have l7 : ∀ sK1 sK2 sK0 X0 : G, (((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) ◇ X0) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ X0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 1]; rw [← l5 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0]
  have l8 : ∀ sK1 sK2 sK0 X0 : G, (((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) ◇ X0) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [l7 sK1 sK2 sK0 X0]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l9 : ∀ sK1 sK2 sK0 X0 : G, ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ X0)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) X0]
    conv => enter [1]; rw [l8 sK1 sK2 sK0 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4746 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4746 X1 X0 X0 X1 (X1 ◇ (X1 ◇ X1))]
  have l11 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4746 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h4746 X0 X0 X0 X0 (X0 ◇ X0)]
  have l12 : ∀ sK1 sK2 X0 X1 X2 : G, sK1 = (sK1 ◇ ((sK1 ◇ sK2) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [h4746 sK1 sK2 X0 X1 X2]
    conv => enter [1, 2]; rw [h4512 sK1 sK2 (X0 ◇ (X1 ◇ X2))]
  have l13 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X5)) = (X5 ◇ X0) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [l1 X0 (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) X5]
    conv => enter [1, 2]; rw [← h4746 X0 X1 X2 X3 X4]
  have l14 : ∀ sK0 sK1 sK2 X0 X1 X2 X3 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro sK0 sK1 sK2 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4746 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0 X1 X2 X3]
    conv => enter [1]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))]
  have l15 : ∀ sK0 sK1 sK2 X0 X1 X2 X3 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0 X1 X2 X3
    conv => enter [1]; rw [l14 sK0 sK1 sK2 X0 X1 X2 X3]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) (X0 ◇ (X1 ◇ (X2 ◇ X3))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l16 : ∀ X5 X0 X1 X2 X3 X4 : G, (X5 ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5))) := by
    intro X5 X0 X1 X2 X3 X4
    conv => enter [1]; rw [← l13 X0 X1 X2 X3 X4 X5]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (X3 ◇ X4))) X5]
  have l17 : ∀ sK1 sK2 X0 X1 X2 : G, sK1 = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l12 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ sK2) (X0 ◇ (X1 ◇ X2))]
  have l18 : ∀ sK0 sK1 sK2 X0 X1 X2 X3 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro sK0 sK1 sK2 X0 X1 X2 X3
    conv => enter [1]; rw [l15 sK0 sK1 sK2 X0 X1 X2 X3]
    conv => enter [1]; rw [← l9 sK1 sK2 sK0 (X0 ◇ (X1 ◇ (X2 ◇ X3)))]
  have l19 : ∀ X5 X0 : G, (X5 ◇ X0) = X0 := by
    intro X5 X0
    conv => enter [1]; rw [l16 X5 X0 X5 X5 X5 X5]
    conv => enter [1]; rw [l10 X0 ((X5 ◇ (X5 ◇ (X5 ◇ X5))) ◇ X5)]
  have l20 : ∀ sK1 sK0 sK2 : G, sK1 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l17 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l18 sK0 sK1 sK2 sK1 sK1 sK1 sK1]
  have l21 : ∀ sK1 sK0 sK2 : G, sK1 = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l20 sK1 sK0 sK2]
    conv => enter [1, 2]; rw [l19 sK0 (sK1 ◇ (sK1 ◇ sK2))]
  have l22 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = ((sK1 ◇ (sK1 ◇ sK2)) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l11 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
    conv => enter [1]; rw [l6 sK0 sK1 sK2]
  have l23 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l22 sK0 sK1 sK2]
    conv => enter [1]; rw [l19 (sK1 ◇ (sK1 ◇ sK2)) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l24 : ∀ sK1 sK0 sK2 : G, sK1 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l21 sK1 sK0 sK2]
    conv => enter [1]; rw [l23 sK0 sK1 sK2]
  have l25 : ∀ X0 sK0 sK1 sK2 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) = (sK0 ◇ (sK1 ◇ X0)) := by
    intro X0 sK0 sK1 sK2
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0]
    conv => enter [1, 2, 1]; rw [← l24 sK1 sK0 sK2]
  have l26 : ∀ sK1 X0 sK0 sK2 : G, (sK1 ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK1 X0 sK0 sK2
    conv => enter [1]; rw [← l19 sK0 (sK1 ◇ X0)]
    conv => enter [1]; rw [← l25 X0 sK0 sK1 sK2]
  have l27 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = (sK1 ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l19 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))]
    conv => enter [1]; rw [← l26 sK1 X0 sK0 sK2]
  have l28 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = X0 := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l27 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l19 sK1 X0]
  intro x y z
  conv => enter [1]; rw [← l28 x y z x]

theorem Equation43_4512_4746_implies_Equation4709 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4746 : Equation4746 G) : Equation4709 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ sK0 sK3 X0 : G, (sK0 ◇ (sK3 ◇ X0)) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK0 sK3 X0
    conv => enter [1]; rw [l0 sK0 sK3 X0]
    conv => enter [1, 2]; rw [h43 sK0 sK3]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4746 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4746 X1 X0 X0 X1 (X1 ◇ (X1 ◇ X1))]
  have l3 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X5)) = (X5 ◇ X0) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [l0 X0 (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) X5]
    conv => enter [1, 2]; rw [← h4746 X0 X1 X2 X3 X4]
  have l4 : ∀ X5 X0 X1 X2 X3 X4 : G, (X5 ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5))) := by
    intro X5 X0 X1 X2 X3 X4
    conv => enter [1]; rw [← l3 X0 X1 X2 X3 X4 X5]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (X3 ◇ X4))) X5]
  have l5 : ∀ X5 X0 : G, (X5 ◇ X0) = X0 := by
    intro X5 X0
    conv => enter [1]; rw [l4 X5 X0 X5 X5 X5 X5]
    conv => enter [1]; rw [l2 X0 ((X5 ◇ (X5 ◇ (X5 ◇ X5))) ◇ X5)]
  have l6 : ∀ sK0 X0 sK3 : G, (sK0 ◇ X0) = (X0 ◇ (sK3 ◇ sK0)) := by
    intro sK0 X0 sK3
    conv => enter [1, 2]; rw [← l5 sK3 X0]
    conv => enter [1]; rw [l1 sK0 sK3 X0]
  have l7 : ∀ sK3 sK0 X0 : G, (sK3 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [← l5 X0 (sK3 ◇ sK0)]
    conv => enter [1]; rw [← l6 sK0 X0 sK3]
  have l8 : ∀ sK3 sK0 X0 : G, (sK3 ◇ sK0) = X0 := by
    intro sK3 sK0 X0
    conv => enter [1]; rw [l7 sK3 sK0 X0]
    conv => enter [1]; rw [l5 sK0 X0]
  intro x y z w
  conv => enter [1]; rw [← l8 z w x]
  conv => enter [1]; rw [l8 z w (y ◇ (z ◇ w))]
  conv => enter [1]; rw [← l5 x (y ◇ (z ◇ w))]
  conv => enter [1, 2]; rw [← l5 x (y ◇ (z ◇ w))]
  conv => enter [1, 2, 2]; rw [← l5 x (y ◇ (z ◇ w))]

theorem Equation43_4512_4746_implies_Equation4724 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4746 : Equation4746 G) : Equation4724 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
  have l3 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = ((sK1 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 2]; rw [← h4512 sK1 sK1 X0]
    conv => enter [1]; rw [h4512 sK1 sK1 (sK1 ◇ X0)]
  have l4 : ∀ sK1 X0 : G, (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [l3 sK1 X0]
    conv => enter [1]; rw [← l1 sK1 X0 (sK1 ◇ sK1)]
  have l5 : ∀ sK1 X0 : G, ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
    conv => enter [1]; rw [l4 sK1 X0]
  have l6 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l2 sK0 sK1 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
  have l7 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ X1) = ((X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (sK0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l2 sK0 sK1 X0]
    conv => enter [1]; rw [l0 sK0 (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X1]
  have l8 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ X1) = (sK0 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l7 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l1 sK0 X1 (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))]
  have l9 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X0) ◇ X1) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l8 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l6 sK0 sK1 X1 X0]
  have l10 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X1 ◇ X0)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0 X1]
    conv => enter [1]; rw [l9 sK0 sK1 X0 X1]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4746 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4746 X1 X0 X0 X1 (X1 ◇ (X1 ◇ X1))]
  have l12 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X5)) = (X5 ◇ X0) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [l1 X0 (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) X5]
    conv => enter [1, 2]; rw [← h4746 X0 X1 X2 X3 X4]
  have l13 : ∀ sK1 X0 X1 X2 X3 : G, (sK1 ◇ sK1) = ((sK1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ (sK1 ◇ sK1)) := by
    intro sK1 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4746 sK1 X0 X1 X2 X3]
    conv => enter [1]; rw [l1 sK1 sK1 (sK1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))]
  have l14 : ∀ sK0 sK1 X0 X1 X2 X3 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = (((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4746 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0 X1 X2 X3]
    conv => enter [1]; rw [l1 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))]
  have l15 : ∀ sK0 sK1 X0 X1 X2 X3 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro sK0 sK1 X0 X1 X2 X3
    conv => enter [1]; rw [l14 sK0 sK1 X0 X1 X2 X3]
    conv => enter [1]; rw [h43 ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))]
  have l16 : ∀ sK1 X0 X1 X2 X3 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ (sK1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro sK1 X0 X1 X2 X3
    conv => enter [1]; rw [l13 sK1 X0 X1 X2 X3]
    conv => enter [1]; rw [h43 (sK1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) (sK1 ◇ sK1)]
  have l17 : ∀ X5 X0 X1 X2 X3 X4 : G, (X5 ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5))) := by
    intro X5 X0 X1 X2 X3 X4
    conv => enter [1]; rw [← l12 X0 X1 X2 X3 X4 X5]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (X3 ◇ X4))) X5]
  have l18 : ∀ sK0 sK1 X0 X1 X2 X3 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))))) := by
    intro sK0 sK1 X0 X1 X2 X3
    conv => enter [1]; rw [l15 sK0 sK1 X0 X1 X2 X3]
    conv => enter [1]; rw [← l1 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) (X0 ◇ (X1 ◇ (X2 ◇ X3))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))]
  have l19 : ∀ sK1 X0 X1 X2 X3 : G, (sK1 ◇ sK1) = (sK1 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0 X1 X2 X3
    conv => enter [1]; rw [l16 sK1 X0 X1 X2 X3]
    conv => enter [1]; rw [← l1 sK1 (X0 ◇ (X1 ◇ (X2 ◇ X3))) (sK1 ◇ sK1)]
  have l20 : ∀ X5 X0 : G, (X5 ◇ X0) = X0 := by
    intro X5 X0
    conv => enter [1]; rw [l17 X5 X0 X5 X5 X5 X5]
    conv => enter [1]; rw [l11 X0 ((X5 ◇ (X5 ◇ (X5 ◇ X5))) ◇ X5)]
  have l21 : ∀ sK0 sK1 X0 X1 X2 X3 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro sK0 sK1 X0 X1 X2 X3
    conv => enter [1]; rw [l18 sK0 sK1 X0 X1 X2 X3]
    conv => enter [1]; rw [l10 sK0 sK1 (X0 ◇ (X1 ◇ (X2 ◇ X3))) (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))]
  have l22 : ∀ sK1 X0 X1 X2 X3 : G, (sK1 ◇ sK1) = ((sK1 ◇ (sK1 ◇ sK1)) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro sK1 X0 X1 X2 X3
    conv => enter [1]; rw [l19 sK1 X0 X1 X2 X3]
    conv => enter [1]; rw [← l5 sK1 (X0 ◇ (X1 ◇ (X2 ◇ X3)))]
  have l23 : ∀ sK0 sK1 X0 X1 X2 X3 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) := by
    intro sK0 sK1 X0 X1 X2 X3
    conv => enter [1]; rw [l21 sK0 sK1 X0 X1 X2 X3]
    conv => enter [1]; rw [l20 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))]
  have l24 : ∀ sK1 X0 X1 X2 X3 : G, (sK1 ◇ sK1) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := by
    intro sK1 X0 X1 X2 X3
    conv => enter [1]; rw [l22 sK1 X0 X1 X2 X3]
    conv => enter [1]; rw [l20 (sK1 ◇ (sK1 ◇ sK1)) (X0 ◇ (X1 ◇ (X2 ◇ X3)))]
  have l25 : ∀ sK0 sK1 X0 X1 X2 X3 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = (X0 ◇ (X1 ◇ (X2 ◇ X3))) := by
    intro sK0 sK1 X0 X1 X2 X3
    conv => enter [1]; rw [l23 sK0 sK1 X0 X1 X2 X3]
    conv => enter [1]; rw [l20 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) (X0 ◇ (X1 ◇ (X2 ◇ X3)))]
  have l26 : ∀ sK1 X1 X2 X3 : G, (sK1 ◇ sK1) = (X1 ◇ (X2 ◇ X3)) := by
    intro sK1 X1 X2 X3
    conv => enter [1]; rw [l24 sK1 sK1 X1 X2 X3]
    conv => enter [1]; rw [l20 sK1 (X1 ◇ (X2 ◇ X3))]
  have l27 : ∀ sK0 sK1 X1 X2 X3 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = (X1 ◇ (X2 ◇ X3)) := by
    intro sK0 sK1 X1 X2 X3
    conv => enter [1]; rw [l25 sK0 sK1 sK0 X1 X2 X3]
    conv => enter [1]; rw [l20 sK0 (X1 ◇ (X2 ◇ X3))]
  have l28 : ∀ sK1 X2 X3 : G, (sK1 ◇ sK1) = (X2 ◇ X3) := by
    intro sK1 X2 X3
    conv => enter [1]; rw [l26 sK1 sK1 X2 X3]
    conv => enter [1]; rw [l20 sK1 (X2 ◇ X3)]
  have l29 : ∀ sK0 sK1 X2 X3 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = (X2 ◇ X3) := by
    intro sK0 sK1 X2 X3
    conv => enter [1]; rw [l27 sK0 sK1 sK0 X2 X3]
    conv => enter [1]; rw [l20 sK0 (X2 ◇ X3)]
  have l30 : ∀ sK1 X2 X3 : G, sK1 = (X2 ◇ X3) := by
    intro sK1 X2 X3
    conv => enter [1]; rw [← l20 sK1 sK1]
    conv => enter [1]; rw [l28 sK1 X2 X3]
  have l31 : ∀ sK0 sK1 X2 X3 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (X2 ◇ X3) := by
    intro sK0 sK1 X2 X3
    conv => enter [1, 2]; rw [← l20 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))]
    conv => enter [1]; rw [l29 sK0 sK1 X2 X3]
  have l32 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l30 sK1 sK1 sK1]
    conv => enter [1]; rw [← l31 sK0 sK1 sK1 sK1]
  have l33 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l32 sK1 sK0]
    conv => enter [1]; rw [h43 sK0 sK1]
  have l34 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l20 sK1 sK0]
    conv => enter [1]; rw [← l33 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l34 x y]

theorem Equation4512_4746_implies_Equation4725 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4746 : Equation4746 G) : Equation4725 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4746 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4746 X1 X0 X0 X1 (X1 ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X5)) = (X0 ◇ X5) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) X5]
    conv => enter [1, 1]; rw [← h4746 X0 X1 X2 X3 X4]
  have l2 : ∀ X0 X5 X1 X2 X3 X4 : G, (X0 ◇ X5) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5))) := by
    intro X0 X5 X1 X2 X3 X4
    conv => enter [1]; rw [← l1 X0 X1 X2 X3 X4 X5]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (X3 ◇ X4))) X5]
  have l3 : ∀ X0 X5 : G, (X0 ◇ X5) = X0 := by
    intro X0 X5
    conv => enter [1]; rw [l2 X0 X5 X0 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X5)]
  intro x y z
  conv => enter [1]; rw [← l3 x (x ◇ (y ◇ (y ◇ (y ◇ z))))]

theorem Equation43_4512_4746_implies_Equation4728 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4746 : Equation4746 G) : Equation4728 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4746 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4746 X1 X0 X0 X1 (X1 ◇ (X1 ◇ X1))]
  have l2 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X5)) = (X5 ◇ X0) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [l0 X0 (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) X5]
    conv => enter [1, 2]; rw [← h4746 X0 X1 X2 X3 X4]
  have l3 : ∀ X5 X0 X1 X2 X3 X4 : G, (X5 ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5))) := by
    intro X5 X0 X1 X2 X3 X4
    conv => enter [1]; rw [← l2 X0 X1 X2 X3 X4 X5]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (X3 ◇ X4))) X5]
  have l4 : ∀ X5 X0 : G, (X5 ◇ X0) = X0 := by
    intro X5 X0
    conv => enter [1]; rw [l3 X5 X0 X5 X5 X5 X5]
    conv => enter [1]; rw [l1 X0 ((X5 ◇ (X5 ◇ (X5 ◇ X5))) ◇ X5)]
  have l5 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1, 2]; rw [← l4 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) X0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))) X0]
  have l6 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) = (sK0 ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l4 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2)))))]
    conv => enter [1]; rw [← l5 sK0 X0 sK1 sK2]
  have l7 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK2))))) = X0 := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l6 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [l4 sK0 X0]
  intro x y z
  conv => enter [1]; rw [← l7 x y z x]

theorem Equation43_4512_4746_implies_Equation4729 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4746 : Equation4746 G) : Equation4729 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4746 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4746 X1 X0 X0 X1 (X1 ◇ (X1 ◇ X1))]
  have l2 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X5)) = (X5 ◇ X0) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [l0 X0 (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) X5]
    conv => enter [1, 2]; rw [← h4746 X0 X1 X2 X3 X4]
  have l3 : ∀ X5 X0 X1 X2 X3 X4 : G, (X5 ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5))) := by
    intro X5 X0 X1 X2 X3 X4
    conv => enter [1]; rw [← l2 X0 X1 X2 X3 X4 X5]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (X3 ◇ X4))) X5]
  have l4 : ∀ X5 X0 : G, (X5 ◇ X0) = X0 := by
    intro X5 X0
    conv => enter [1]; rw [l3 X5 X0 X5 X5 X5 X5]
    conv => enter [1]; rw [l1 X0 ((X5 ◇ (X5 ◇ (X5 ◇ X5))) ◇ X5)]
  have l5 : ∀ sK1 X0 sK2 sK3 sK0 : G, (sK1 ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))))) := by
    intro sK1 X0 sK2 sK3 sK0
    conv => enter [1, 2]; rw [← l4 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) X0]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))) X0]
  have l6 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = (sK1 ◇ X0) := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [← l4 X0 (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0)))))]
    conv => enter [1]; rw [← l5 sK1 X0 sK2 sK3 sK0]
  have l7 : ∀ sK1 sK2 sK3 sK0 X0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK3 ◇ sK0))))) = X0 := by
    intro sK1 sK2 sK3 sK0 X0
    conv => enter [1]; rw [l6 sK1 sK2 sK3 sK0 X0]
    conv => enter [1]; rw [l4 sK1 X0]
  intro x y z w
  conv => enter [1]; rw [← l7 x y z w x]

theorem Equation43_4512_4746_implies_Equation4799 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4746 : Equation4746 G) : Equation4799 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) = (sK1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
    conv => enter [1, 2]; rw [h43 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) X0]
  have l3 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1)) = (sK1 ◇ (X0 ◇ (X1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l2 sK1 sK2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))]
  have l4 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) ◇ X1) = ((X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (sK1 ◇ X1)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l2 sK1 sK2 X0]
    conv => enter [1]; rw [l0 sK1 (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X1]
  have l5 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) ◇ X1) = (sK1 ◇ (X1 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l4 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l1 sK1 X1 (X0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))]
  have l6 : ∀ sK1 sK2 X0 X1 : G, (((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X0) ◇ X1) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [l5 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l3 sK1 sK2 X1 X0]
  have l7 : ∀ sK1 sK2 X0 X1 : G, ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1)) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X1 ◇ X0)) := by
    intro sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0 X1]
    conv => enter [1]; rw [l6 sK1 sK2 X0 X1]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4746 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [← h4746 X1 X0 X0 X1 (X1 ◇ (X1 ◇ X1))]
  have l9 : ∀ sK1 sK2 X0 X1 X2 : G, sK1 = (sK1 ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [h4746 sK1 (sK1 ◇ (sK1 ◇ sK2)) X0 X1 X2]
    conv => enter [1, 2]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ sK2)) (X0 ◇ (X1 ◇ X2))]
  have l10 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) ◇ X5)) = (X5 ◇ X0) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [l1 X0 (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))) X5]
    conv => enter [1, 2]; rw [← h4746 X0 X1 X2 X3 X4]
  have l11 : ∀ sK0 sK1 sK2 X0 X1 X2 X3 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro sK0 sK1 sK2 X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4746 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0 X1 X2 X3]
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))]
  have l12 : ∀ sK0 sK1 sK2 X0 X1 X2 X3 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))))) := by
    intro sK0 sK1 sK2 X0 X1 X2 X3
    conv => enter [1]; rw [l11 sK0 sK1 sK2 X0 X1 X2 X3]
    conv => enter [1]; rw [← l1 (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) (X0 ◇ (X1 ◇ (X2 ◇ X3))) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))]
  have l13 : ∀ X5 X0 X1 X2 X3 X4 : G, (X5 ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X4))) ◇ X5))) := by
    intro X5 X0 X1 X2 X3 X4
    conv => enter [1]; rw [← l10 X0 X1 X2 X3 X4 X5]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (X3 ◇ X4))) X5]
  have l14 : ∀ sK1 sK2 X0 X1 X2 : G, sK1 = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro sK1 sK2 X0 X1 X2
    conv => enter [1]; rw [l9 sK1 sK2 X0 X1 X2]
    conv => enter [1]; rw [h4512 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))) (X0 ◇ (X1 ◇ X2))]
  have l15 : ∀ sK0 sK1 sK2 X0 X1 X2 X3 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = ((sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))) := by
    intro sK0 sK1 sK2 X0 X1 X2 X3
    conv => enter [1]; rw [l12 sK0 sK1 sK2 X0 X1 X2 X3]
    conv => enter [1]; rw [l7 sK1 sK2 (X0 ◇ (X1 ◇ (X2 ◇ X3))) (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))]
  have l16 : ∀ X5 X0 : G, (X5 ◇ X0) = X0 := by
    intro X5 X0
    conv => enter [1]; rw [l13 X5 X0 X5 X5 X5 X5]
    conv => enter [1]; rw [l8 X0 ((X5 ◇ (X5 ◇ (X5 ◇ X5))) ◇ X5)]
  have l17 : ∀ sK1 sK0 sK2 : G, sK1 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l14 sK1 sK2 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) sK1 (sK1 ◇ (sK1 ◇ sK1))]
    conv => enter [1]; rw [← l15 sK0 sK1 sK2 sK1 sK1 sK1 sK1]
  have l18 : ∀ sK1 sK2 : G, sK1 = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) := by
    intro sK1 sK2
    conv => enter [1]; rw [l17 sK1 sK1 sK2]
    conv => enter [1, 2, 2, 2, 2]; rw [l16 sK1 sK2]
  have l19 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) = (sK1 ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [← l18 sK1 sK2]
    conv => enter [1]; rw [h43 sK0 sK1]
  have l20 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l16 sK1 sK0]
    conv => enter [1]; rw [← l19 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l20 x y z]

theorem Equation43_4512_4729_implies_Equation2 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4729 : Equation4729 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X1 X0 X2]
    conv => enter [1]; rw [h43 (X1 ◇ X0) X2]
  have l3 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) = X1 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2]; rw [l1 X0 X1 (X0 ◇ (X2 ◇ X3))]
    conv => enter [1]; rw [← h4729 X1 X0 X2 X3]
  have l4 : ∀ X1 X2 X3 X0 : G, ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l2 (X1 ◇ (X1 ◇ (X2 ◇ X3))) X0 X0]
    conv => enter [1]; rw [← h4729 X0 X1 X2 X3]
  have l5 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4729 (X0 ◇ X1) X2 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4))))]
  have l6 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4))))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l5 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ (X3 ◇ X4)))]
  have l7 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X2 ◇ X3)) (X0 ◇ X0)]
    conv => enter [1]; rw [l4 X1 X2 X3 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [l3 X0 X1 X0 (X0 ◇ (X0 ◇ X0))]
  have l9 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2]; rw [h4512 X1 (X2 ◇ X3) (X0 ◇ X0)]
    conv => enter [1]; rw [l7 X1 X2 X3 X0]
  have l10 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l9 X0 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l10 x y]

theorem Equation43_4512_4729_implies_Equation4696 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4729 : Equation4729 G) : Equation4696 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) X1]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X1]
  have l3 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) X0 X1]
    conv => enter [1]; rw [l2 sK0 sK1 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4729 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4729 X1 X0 X1 (X1 ◇ (X1 ◇ X1))]
  have l5 : ∀ sK0 sK1 X0 X1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4729 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) ◇ (X0 ◇ X1))]
  have l6 : ∀ sK0 sK1 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l5 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l3 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) (X0 ◇ X1)]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l4 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))))) (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation43_4512_4729_implies_Equation4698 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4729 : Equation4729 G) : Equation4698 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) X1]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X1]
  have l3 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) X0 X1]
    conv => enter [1]; rw [l2 sK0 sK1 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4729 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4729 X1 X0 X1 (X1 ◇ (X1 ◇ X1))]
  have l5 : ∀ sK0 sK1 X0 X1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4729 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1))]
  have l6 : ∀ sK0 sK1 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l5 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l3 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) (X0 ◇ X1)]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l4 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))))) (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation43_4512_4729_implies_Equation4699 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4729 : Equation4729 G) : Equation4699 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0]
  have l1 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l0 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) X1]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X1]
  have l3 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) X0 X1]
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4729 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4729 X1 X0 X1 (X1 ◇ (X1 ◇ X1))]
  have l5 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4729 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1))]
  have l6 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l3 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) (X0 ◇ X1)]
  have l7 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [l4 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK2))))) (sK0 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation43_4512_4729_implies_Equation4704 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4729 : Equation4729 G) : Equation4704 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) X1]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X1]
  have l3 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) X0 X1]
    conv => enter [1]; rw [l2 sK0 sK1 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4729 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4729 X1 X0 X1 (X1 ◇ (X1 ◇ X1))]
  have l5 : ∀ sK0 sK1 X0 X1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4729 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1))]
  have l6 : ∀ sK0 sK1 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l5 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l3 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) (X0 ◇ X1)]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l4 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK1))))) (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation43_4512_4729_implies_Equation4705 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4729 : Equation4729 G) : Equation4705 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0]
  have l1 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l0 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) X1]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X1]
  have l3 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) X0 X1]
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4729 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4729 X1 X0 X1 (X1 ◇ (X1 ◇ X1))]
  have l5 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4729 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1))]
  have l6 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l3 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) (X0 ◇ X1)]
  have l7 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [l4 (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK2))))) (sK0 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation43_4512_4729_implies_Equation4709 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4729 : Equation4729 G) : Equation4709 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l3 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) = X1 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2]; rw [l2 X0 X1 (X0 ◇ (X2 ◇ X3))]
    conv => enter [1]; rw [← h4729 X1 X0 X2 X3]
  have l4 : ∀ X1 X2 X3 X0 : G, ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [← l1 X0 X0 (X1 ◇ (X1 ◇ (X2 ◇ X3)))]
    conv => enter [1]; rw [← h4729 X0 X1 X2 X3]
  have l5 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4729 (X0 ◇ X1) X2 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4))))]
  have l6 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4))))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l5 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ (X3 ◇ X4)))]
  have l7 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X2 ◇ X3)) (X0 ◇ X0)]
    conv => enter [1]; rw [l4 X1 X2 X3 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [l3 X0 X1 X0 (X0 ◇ (X0 ◇ X0))]
  have l9 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2]; rw [h4512 X1 (X2 ◇ X3) (X0 ◇ X0)]
    conv => enter [1]; rw [l7 X1 X2 X3 X0]
  have l10 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l9 X0 X0 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l10 x (x ◇ (x ◇ (x ◇ (y ◇ (z ◇ w)))))]

theorem Equation43_4512_4729_implies_Equation4724 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4729 : Equation4729 G) : Equation4724 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0]
  have l1 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1, 1]; rw [l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) X1]
  have l2 : ∀ sK0 sK1 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X1]
  have l3 : ∀ sK0 sK1 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) X0 X1]
    conv => enter [1]; rw [l2 sK0 sK1 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4729 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4729 X1 X0 X1 (X1 ◇ (X1 ◇ X1))]
  have l5 : ∀ sK0 sK1 X0 X1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4729 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) ◇ (X0 ◇ X1))]
  have l6 : ∀ sK0 sK1 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l5 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← l3 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) (X0 ◇ X1)]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1 sK0 sK0]
    conv => enter [1]; rw [l4 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1))))) (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation43_4512_4729_implies_Equation4725 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4729 : Equation4729 G) : Equation4725 G := by
  have l0 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ X0) = (sK0 ◇ (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))))) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0]
    conv => enter [1, 2]; rw [h43 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0]
  have l1 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ X0) ◇ X1) = (sK0 ◇ ((X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ X1)) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1, 1]; rw [l0 sK0 sK1 sK2 X0]
    conv => enter [1]; rw [← h4512 sK0 (X0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) X1]
  have l2 : ∀ sK0 sK1 sK2 X0 X1 : G, (((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ X0) ◇ X1) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l1 sK0 sK1 sK2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X1]
  have l3 : ∀ sK0 sK1 sK2 X0 X1 : G, ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ (X0 ◇ X1)) = (sK0 ◇ (X0 ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4512 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) X0 X1]
    conv => enter [1]; rw [l2 sK0 sK1 sK2 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4729 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4729 X1 X0 X1 (X1 ◇ (X1 ◇ X1))]
  have l5 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = (sK0 ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1)))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [h4729 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) X0 X1]
    conv => enter [1, 2]; rw [h4512 sK0 (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ((sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2)))) ◇ (X0 ◇ X1))]
  have l6 : ∀ sK0 sK1 sK2 X0 X1 : G, sK0 = ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ ((sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) ◇ (X0 ◇ X1))) := by
    intro sK0 sK1 sK2 X0 X1
    conv => enter [1]; rw [l5 sK0 sK1 sK2 X0 X1]
    conv => enter [1]; rw [← l3 sK0 sK1 sK2 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) (X0 ◇ X1)]
  have l7 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l6 sK0 sK1 sK2 sK0 sK0]
    conv => enter [1]; rw [l4 (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK2))))) (sK0 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

theorem Equation43_4512_4729_implies_Equation4728 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4729 : Equation4729 G) : Equation4728 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l3 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) = X1 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2]; rw [l2 X0 X1 (X0 ◇ (X2 ◇ X3))]
    conv => enter [1]; rw [← h4729 X1 X0 X2 X3]
  have l4 : ∀ X1 X2 X3 X0 : G, ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [← l1 X0 X0 (X1 ◇ (X1 ◇ (X2 ◇ X3)))]
    conv => enter [1]; rw [← h4729 X0 X1 X2 X3]
  have l5 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4729 (X0 ◇ X1) X2 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4))))]
  have l6 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4))))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l5 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ (X3 ◇ X4)))]
  have l7 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X2 ◇ X3)) (X0 ◇ X0)]
    conv => enter [1]; rw [l4 X1 X2 X3 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [l3 X0 X1 X0 (X0 ◇ (X0 ◇ X0))]
  have l9 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2]; rw [h4512 X1 (X2 ◇ X3) (X0 ◇ X0)]
    conv => enter [1]; rw [l7 X1 X2 X3 X0]
  have l10 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l9 X0 X0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l10 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ z)))))]

theorem Equation43_4512_4729_implies_Equation4746 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4729 : Equation4729 G) : Equation4746 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X1 X0 X2]
    conv => enter [1]; rw [h43 (X1 ◇ X0) X2]
  have l3 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3))))) = X1 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2]; rw [l1 X0 X1 (X0 ◇ (X2 ◇ X3))]
    conv => enter [1]; rw [← h4729 X1 X0 X2 X3]
  have l4 : ∀ X1 X2 X3 X0 : G, ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [l2 (X1 ◇ (X1 ◇ (X2 ◇ X3))) X0 X0]
    conv => enter [1]; rw [← h4729 X0 X1 X2 X3]
  have l5 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4)))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4729 (X0 ◇ X1) X2 X3 X4]
    conv => enter [1]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4))))]
  have l6 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X4))))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [l5 X0 X1 X2 X3 X4]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X2 ◇ (X3 ◇ X4)))]
  have l7 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X2 ◇ X3)) (X0 ◇ X0)]
    conv => enter [1]; rw [l4 X1 X2 X3 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [l3 X0 X1 X0 (X0 ◇ (X0 ◇ X0))]
  have l9 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X1 ◇ ((X2 ◇ X3) ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2]; rw [h4512 X1 (X2 ◇ X3) (X0 ◇ X0)]
    conv => enter [1]; rw [l7 X1 X2 X3 X0]
  have l10 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l9 X0 X0 X0 X1]
  intro x y z w u
  conv => enter [1]; rw [l10 x (x ◇ (x ◇ (y ◇ (z ◇ (w ◇ u)))))]

theorem Equation43_4512_4728_implies_Equation2 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4728 : Equation4728 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X2) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1, 1]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h4512 X1 X0 X2]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X1 ◇ (X0 ◇ X2)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [l0 X0 X1 X2]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X1 ◇ X0)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X1 X0 X2]
    conv => enter [1]; rw [h43 (X1 ◇ X0) X2]
  have l3 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4728 X2 X3 (X0 ◇ X1)]
  have l4 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2, 2]; rw [l1 X0 X1 X0]
    conv => enter [1]; rw [← h4728 X2 X1 X0]
  have l5 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [l2 (X1 ◇ (X1 ◇ (X2 ◇ X2))) X0 X0]
    conv => enter [1]; rw [← h4728 X0 X1 X2]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X2 ◇ X2)) (X0 ◇ X0)]
    conv => enter [1]; rw [l5 X1 X2 X0]
  have l7 : ∀ X2 X3 : G, (X2 ◇ (X2 ◇ X3)) = X2 := by
    intro X2 X3
    conv => enter [1, 2, 2]; rw [← l4 X3 X2 X2]
    conv => enter [1]; rw [l3 X2 X3 X2 X2]
  have l8 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X1 (X2 ◇ X2) (X0 ◇ X0)]
    conv => enter [1]; rw [l6 X1 X2 X0]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 ((X0 ◇ X0) ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l8 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

theorem Equation43_4512_4728_implies_Equation4696 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4728 : Equation4728 G) : Equation4696 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4728 X2 X3 (X0 ◇ X1)]
  have l2 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l0 X1 X0 X0]
    conv => enter [1]; rw [← h4728 X2 X1 X0]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l0 X0 X0 (X1 ◇ (X1 ◇ (X2 ◇ X2)))]
    conv => enter [1]; rw [← h4728 X0 X1 X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X2 ◇ X2)) (X0 ◇ X0)]
    conv => enter [1]; rw [l3 X1 X2 X0]
  have l5 : ∀ X2 X3 : G, (X2 ◇ (X2 ◇ X3)) = X2 := by
    intro X2 X3
    conv => enter [1, 2, 2]; rw [← l2 X3 X2 X2]
    conv => enter [1]; rw [l1 X2 X3 X2 X2]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X1 (X2 ◇ X2) (X0 ◇ X0)]
    conv => enter [1]; rw [l4 X1 X2 X0]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 ((X0 ◇ X0) ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l6 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x (x ◇ (x ◇ (x ◇ (x ◇ (x ◇ y)))))]

theorem Equation43_4512_4728_implies_Equation4698 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4728 : Equation4728 G) : Equation4698 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4728 X2 X3 (X0 ◇ X1)]
  have l2 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l0 X1 X0 X0]
    conv => enter [1]; rw [← h4728 X2 X1 X0]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l0 X0 X0 (X1 ◇ (X1 ◇ (X2 ◇ X2)))]
    conv => enter [1]; rw [← h4728 X0 X1 X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X2 ◇ X2)) (X0 ◇ X0)]
    conv => enter [1]; rw [l3 X1 X2 X0]
  have l5 : ∀ X2 X3 : G, (X2 ◇ (X2 ◇ X3)) = X2 := by
    intro X2 X3
    conv => enter [1, 2, 2]; rw [← l2 X3 X2 X2]
    conv => enter [1]; rw [l1 X2 X3 X2 X2]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X1 (X2 ◇ X2) (X0 ◇ X0)]
    conv => enter [1]; rw [l4 X1 X2 X0]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 ((X0 ◇ X0) ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l6 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ y)))))]

theorem Equation43_4512_4728_implies_Equation4699 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4728 : Equation4728 G) : Equation4699 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4728 X2 X3 (X0 ◇ X1)]
  have l2 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l0 X1 X0 X0]
    conv => enter [1]; rw [← h4728 X2 X1 X0]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l0 X0 X0 (X1 ◇ (X1 ◇ (X2 ◇ X2)))]
    conv => enter [1]; rw [← h4728 X0 X1 X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X2 ◇ X2)) (X0 ◇ X0)]
    conv => enter [1]; rw [l3 X1 X2 X0]
  have l5 : ∀ X2 X3 : G, (X2 ◇ (X2 ◇ X3)) = X2 := by
    intro X2 X3
    conv => enter [1, 2, 2]; rw [← l2 X3 X2 X2]
    conv => enter [1]; rw [l1 X2 X3 X2 X2]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X1 (X2 ◇ X2) (X0 ◇ X0)]
    conv => enter [1]; rw [l4 X1 X2 X0]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 ((X0 ◇ X0) ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l6 X0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l7 x (x ◇ (x ◇ (x ◇ (x ◇ (y ◇ z)))))]

theorem Equation43_4512_4728_implies_Equation4704 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4728 : Equation4728 G) : Equation4704 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4728 X2 X3 (X0 ◇ X1)]
  have l2 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l0 X1 X0 X0]
    conv => enter [1]; rw [← h4728 X2 X1 X0]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l0 X0 X0 (X1 ◇ (X1 ◇ (X2 ◇ X2)))]
    conv => enter [1]; rw [← h4728 X0 X1 X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X2 ◇ X2)) (X0 ◇ X0)]
    conv => enter [1]; rw [l3 X1 X2 X0]
  have l5 : ∀ X2 X3 : G, (X2 ◇ (X2 ◇ X3)) = X2 := by
    intro X2 X3
    conv => enter [1, 2, 2]; rw [← l2 X3 X2 X2]
    conv => enter [1]; rw [l1 X2 X3 X2 X2]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X1 (X2 ◇ X2) (X0 ◇ X0)]
    conv => enter [1]; rw [l4 X1 X2 X0]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 ((X0 ◇ X0) ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l6 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ y)))))]

theorem Equation43_4512_4728_implies_Equation4705 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4728 : Equation4728 G) : Equation4705 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4728 X2 X3 (X0 ◇ X1)]
  have l2 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l0 X1 X0 X0]
    conv => enter [1]; rw [← h4728 X2 X1 X0]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l0 X0 X0 (X1 ◇ (X1 ◇ (X2 ◇ X2)))]
    conv => enter [1]; rw [← h4728 X0 X1 X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X2 ◇ X2)) (X0 ◇ X0)]
    conv => enter [1]; rw [l3 X1 X2 X0]
  have l5 : ∀ X2 X3 : G, (X2 ◇ (X2 ◇ X3)) = X2 := by
    intro X2 X3
    conv => enter [1, 2, 2]; rw [← l2 X3 X2 X2]
    conv => enter [1]; rw [l1 X2 X3 X2 X2]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X1 (X2 ◇ X2) (X0 ◇ X0)]
    conv => enter [1]; rw [l4 X1 X2 X0]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 ((X0 ◇ X0) ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l6 X0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l7 x (x ◇ (x ◇ (x ◇ (y ◇ (y ◇ z)))))]

theorem Equation43_4512_4728_implies_Equation4709 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4728 : Equation4728 G) : Equation4709 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4728 X2 X3 (X0 ◇ X1)]
  have l2 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l0 X1 X0 X0]
    conv => enter [1]; rw [← h4728 X2 X1 X0]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l0 X0 X0 (X1 ◇ (X1 ◇ (X2 ◇ X2)))]
    conv => enter [1]; rw [← h4728 X0 X1 X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X2 ◇ X2)) (X0 ◇ X0)]
    conv => enter [1]; rw [l3 X1 X2 X0]
  have l5 : ∀ X2 X3 : G, (X2 ◇ (X2 ◇ X3)) = X2 := by
    intro X2 X3
    conv => enter [1, 2, 2]; rw [← l2 X3 X2 X2]
    conv => enter [1]; rw [l1 X2 X3 X2 X2]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X1 (X2 ◇ X2) (X0 ◇ X0)]
    conv => enter [1]; rw [l4 X1 X2 X0]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 ((X0 ◇ X0) ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l6 X0 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l7 x (x ◇ (x ◇ (x ◇ (y ◇ (z ◇ w)))))]

theorem Equation43_4512_4728_implies_Equation4724 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4728 : Equation4728 G) : Equation4724 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4728 X2 X3 (X0 ◇ X1)]
  have l2 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l0 X1 X0 X0]
    conv => enter [1]; rw [← h4728 X2 X1 X0]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l0 X0 X0 (X1 ◇ (X1 ◇ (X2 ◇ X2)))]
    conv => enter [1]; rw [← h4728 X0 X1 X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X2 ◇ X2)) (X0 ◇ X0)]
    conv => enter [1]; rw [l3 X1 X2 X0]
  have l5 : ∀ X2 X3 : G, (X2 ◇ (X2 ◇ X3)) = X2 := by
    intro X2 X3
    conv => enter [1, 2, 2]; rw [← l2 X3 X2 X2]
    conv => enter [1]; rw [l1 X2 X3 X2 X2]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X1 (X2 ◇ X2) (X0 ◇ X0)]
    conv => enter [1]; rw [l4 X1 X2 X0]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 ((X0 ◇ X0) ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l6 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ y)))))]

theorem Equation43_4512_4728_implies_Equation4725 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4728 : Equation4728 G) : Equation4725 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4728 X2 X3 (X0 ◇ X1)]
  have l2 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l0 X1 X0 X0]
    conv => enter [1]; rw [← h4728 X2 X1 X0]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l0 X0 X0 (X1 ◇ (X1 ◇ (X2 ◇ X2)))]
    conv => enter [1]; rw [← h4728 X0 X1 X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X2 ◇ X2)) (X0 ◇ X0)]
    conv => enter [1]; rw [l3 X1 X2 X0]
  have l5 : ∀ X2 X3 : G, (X2 ◇ (X2 ◇ X3)) = X2 := by
    intro X2 X3
    conv => enter [1, 2, 2]; rw [← l2 X3 X2 X2]
    conv => enter [1]; rw [l1 X2 X3 X2 X2]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X1 (X2 ◇ X2) (X0 ◇ X0)]
    conv => enter [1]; rw [l4 X1 X2 X0]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 ((X0 ◇ X0) ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l6 X0 X0 X1]
  intro x y z
  conv => enter [1]; rw [l7 x (x ◇ (x ◇ (y ◇ (y ◇ (y ◇ z)))))]

theorem Equation43_4512_4728_implies_Equation4729 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4728 : Equation4728 G) : Equation4729 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4728 X2 X3 (X0 ◇ X1)]
  have l2 : ∀ X2 X1 X0 : G, (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))) = X2 := by
    intro X2 X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l0 X1 X0 X0]
    conv => enter [1]; rw [← h4728 X2 X1 X0]
  have l3 : ∀ X1 X2 X0 : G, ((X1 ◇ (X1 ◇ (X2 ◇ X2))) ◇ (X0 ◇ X0)) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l0 X0 X0 (X1 ◇ (X1 ◇ (X2 ◇ X2)))]
    conv => enter [1]; rw [← h4728 X0 X1 X2]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X2 ◇ X2)) (X0 ◇ X0)]
    conv => enter [1]; rw [l3 X1 X2 X0]
  have l5 : ∀ X2 X3 : G, (X2 ◇ (X2 ◇ X3)) = X2 := by
    intro X2 X3
    conv => enter [1, 2, 2]; rw [← l2 X3 X2 X2]
    conv => enter [1]; rw [l1 X2 X3 X2 X2]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ ((X2 ◇ X2) ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X1 (X2 ◇ X2) (X0 ◇ X0)]
    conv => enter [1]; rw [l4 X1 X2 X0]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 ((X0 ◇ X0) ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l6 X0 X0 X1]
  intro x y z w
  conv => enter [1]; rw [l7 x (x ◇ (x ◇ (y ◇ (y ◇ (z ◇ w)))))]

theorem Equation43_4512_4725_implies_Equation2 (G : Type*) [Magma G] (h43 : Equation43 G) (h4512 : Equation4512 G) (h4725 : Equation4725 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X2 ◇ (X0 ◇ X1)) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4725 X0 X0 X1]
    conv => enter [1]; rw [← h4725 X1 X0 (X0 ◇ (X0 ◇ X1))]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X3)) := by
    intro X0 X3 X1 X2
    conv => enter [1, 1]; rw [h4725 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) X3]
  have l3 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X0) = (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X3)) := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4725 X0 X1 X2]
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) X3]
  have l4 : ∀ X3 X0 X1 X2 : G, (X3 ◇ X0) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [l3 X3 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ (X1 ◇ X2))) X3]
  have l5 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ (X1 ◇ X2))) X3]
  have l6 : ∀ X3 X0 : G, (X3 ◇ X0) = X0 := by
    intro X3 X0
    conv => enter [1]; rw [l4 X3 X0 X3 X3]
    conv => enter [1]; rw [l1 X0 ((X3 ◇ (X3 ◇ (X3 ◇ X3))) ◇ X3)]
  have l7 : ∀ X0 X3 : G, (X0 ◇ X3) = X0 := by
    intro X0 X3
    conv => enter [1]; rw [l5 X0 X3 X0 X0]
    conv => enter [1]; rw [l1 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X3)]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X1 X0]
    conv => enter [1]; rw [l7 X1 X0]
  intro x y
  conv => enter [1]; rw [l8 x y]

end CommutativeSemigroup5
