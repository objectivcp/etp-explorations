import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

theorem Equation4512_5029_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5029 : Equation5029 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X3 X0 : G, ((X1 ◇ (X2 ◇ X2)) ◇ (X3 ◇ X0)) = X3 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2]; rw [h5029 X0 X2 (X1 ◇ (X2 ◇ X2)) X1]
    conv => enter [1]; rw [← h5029 X3 (X1 ◇ (X2 ◇ X2)) X2 X0]
  have l1 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5029 X0 X1 X1 (X1 ◇ X1)]
    conv => enter [1]; rw [← h5029 X1 (X1 ◇ X1) X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X2 ◇ X2) ◇ (X3 ◇ X0))) = X3 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ X2) (X3 ◇ X0)]
    conv => enter [1]; rw [l0 X1 X2 X3 X0]
  have l4 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ (X3 ◇ X0)))) = X3 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2]; rw [h4512 X2 X2 (X3 ◇ X0)]
    conv => enter [1]; rw [l3 X1 X2 X3 X0]
  have l5 : ∀ X1 X2 X3 : G, (X1 ◇ X2) = X3 := by
    intro X1 X2 X3
    conv => enter [1, 2]; rw [← l2 X2 (X3 ◇ X1)]
    conv => enter [1]; rw [l4 X1 X2 X3 X1]
  have l6 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l5 X0 (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5029 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation2_implies_Equation5030 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5030 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (w ◇ (y ◇ z)))))]

theorem Equation4512_5030_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5030 : Equation5030 G) : Equation2 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X0 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h5030 (X0 ◇ X1) X0 X1 X2]
    conv => enter [1]; rw [← h5030 X0 X2 (X0 ◇ X1) X1]
  have l1 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X4 ◇ ((X1 ◇ X2) ◇ X3)))))) = X0 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ (X4 ◇ ((X1 ◇ X2) ◇ X3))))]
    conv => enter [1]; rw [← h5030 X0 (X1 ◇ X2) X3 X4]
  have l2 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X4 ◇ (X1 ◇ (X2 ◇ X3))))))) = X0 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X1 X2 X3]
    conv => enter [1]; rw [l1 X1 X2 X0 X3 X4]
  have l3 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0 (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))]
    conv => enter [1]; rw [l2 X0 X0 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation5031 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5031 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (w ◇ (y ◇ w)))))]

@[equational_result]
theorem Equation5031_implies_Equation2 (G : Type*) [Magma G] (h5031 : Equation5031 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5031 X0 X2 (X2 ◇ X1) X1]
    conv => enter [1]; rw [← h5031 X2 X1 X0 (X2 ◇ X1)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5031 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5032 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5032 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (w ◇ (y ◇ u)))))]

@[equational_result]
theorem Equation5032_implies_Equation2 (G : Type*) [Magma G] (h5032 : Equation5032 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5032 X0 X2 X1 X1 X1]
    conv => enter [1]; rw [← h5032 X2 X1 X0 X1 (X2 ◇ X1)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5032 X2 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5034 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5034 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (w ◇ (z ◇ y)))))]

@[equational_result]
theorem Equation5034_implies_Equation2 (G : Type*) [Magma G] (h5034 : Equation5034 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, ((X1 ◇ X2) ◇ X0) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h5034 X0 X2 X1 X0]
    conv => enter [1]; rw [← h5034 X2 (X1 ◇ X2) X0 X1]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0 (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))]
    conv => enter [1]; rw [← h5034 X2 (X0 ◇ X0) X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5035 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5035 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (w ◇ (z ◇ z)))))]

theorem Equation4512_5035_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5035 : Equation5035 G) : Equation2 G := by
  have l0 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))))) = X4 := by
    intro X3 X4 X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [← h5035 X4 X3 (X0 ◇ X1) X2]
  have l1 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X4 ◇ (X3 ◇ X3)))))) = X0 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ (X4 ◇ (X3 ◇ X3))))]
    conv => enter [1]; rw [← h5035 X0 (X1 ◇ X2) X3 X4]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5035 X0 X1 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X0 X1 X1]
  have l3 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))))) = X4 := by
    intro X3 X4 X0 X1 X2
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X3 X4 X0 X1 X2]
  have l4 : ∀ X4 X0 X1 X2 : G, (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) = X4 := by
    intro X4 X0 X1 X2
    conv => enter [1, 2]; rw [← l2 X4 (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))]
    conv => enter [1]; rw [l3 X4 X4 X0 X1 X2]
  have l5 : ∀ X0 X1 X2 X4 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) = X4 := by
    intro X0 X1 X2 X4
    conv => enter [1]; rw [← l2 X4 (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))]
    conv => enter [1]; rw [l4 X4 X0 X1 X2]
  have l6 : ∀ X1 X2 X0 X4 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = X4 := by
    intro X1 X2 X0 X4
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))]
    conv => enter [1]; rw [l5 X0 X1 X2 X4]
  have l7 : ∀ X2 X0 X1 X4 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X4 := by
    intro X2 X0 X1 X4
    conv => enter [1]; rw [← l2 X1 (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))]
    conv => enter [1]; rw [l6 X1 X2 X0 X4]
  have l8 : ∀ X0 X1 X4 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X4 := by
    intro X0 X1 X4
    conv => enter [1, 2]; rw [← l2 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l7 X0 X0 X1 X4]
  have l9 : ∀ X1 X0 X4 : G, (X1 ◇ (X0 ◇ X1)) = X4 := by
    intro X1 X0 X4
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l8 X0 X1 X4]
  have l10 : ∀ X0 X1 X4 : G, (X0 ◇ X1) = X4 := by
    intro X0 X1 X4
    conv => enter [1]; rw [← l2 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l9 X1 X0 X4]
  have l11 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l10 X0 (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5035 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l11 x y]

@[equational_result]
theorem Equation2_implies_Equation5036 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5036 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (w ◇ (z ◇ w)))))]

theorem Equation4512_5036_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5036 : Equation5036 G) : Equation2 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X0)))) = X3 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2]; rw [h5036 (X0 ◇ (X1 ◇ X0)) X1 X1 X0]
    conv => enter [1]; rw [← h5036 X3 X2 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X4 ◇ (X3 ◇ X4)))))) = X0 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ (X4 ◇ (X3 ◇ X4))))]
    conv => enter [1]; rw [← h5036 X0 (X1 ◇ X2) X3 X4]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5036 X0 X1 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X0 X1 X1]
  have l3 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X3 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [← l2 X3 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [← h5036 X3 X2 X0 X1]
  have l4 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 X0 X0 X0]
    conv => enter [1]; rw [l3 X0 X0 X0 X3]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation2_implies_Equation5037 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5037 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (w ◇ (z ◇ u)))))]

@[equational_result]
theorem Equation5037_implies_Equation2 (G : Type*) [Magma G] (h5037 : Equation5037 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5037 X0 X2 X1 X0 X1]
    conv => enter [1]; rw [← h5037 X2 X1 X0 X1 (X1 ◇ X1)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5037 X2 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5039 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5039 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (w ◇ (w ◇ y)))))]

theorem Equation4512_5039_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5039 : Equation5039 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 X3 X4 : G, ((X1 ◇ (X2 ◇ (X2 ◇ X0))) ◇ (X3 ◇ (X4 ◇ X0))) = X3 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1, 2, 2, 2]; rw [h5039 X0 X0 X1 X2]
    conv => enter [1]; rw [← h5039 X3 (X1 ◇ (X2 ◇ (X2 ◇ X0))) X4 X0]
  have l1 : ∀ X1 X2 X3 X0 : G, ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X3 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2]; rw [h5039 X0 X2 X0 X1]
    conv => enter [1]; rw [← h5039 X3 (X1 ◇ (X1 ◇ X2)) X2 X0]
  have l2 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = X3 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ X2) (X3 ◇ X0)]
    conv => enter [1]; rw [l1 X1 X2 X3 X0]
  have l3 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ ((X2 ◇ (X2 ◇ X0)) ◇ (X3 ◇ (X4 ◇ X0)))) = X3 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X2 ◇ X0)) (X3 ◇ (X4 ◇ X0))]
    conv => enter [1]; rw [l0 X1 X2 X0 X3 X4]
  have l4 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) = X3 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2]; rw [h4512 X1 X2 (X3 ◇ X0)]
    conv => enter [1]; rw [l2 X1 X2 X3 X0]
  have l5 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ ((X2 ◇ X0) ◇ (X3 ◇ (X4 ◇ X0))))) = X3 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1, 2]; rw [h4512 X2 (X2 ◇ X0) (X3 ◇ (X4 ◇ X0))]
    conv => enter [1]; rw [l3 X1 X2 X0 X3 X4]
  have l6 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X4 ◇ X0)))))) = X3 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1, 2, 2]; rw [h4512 X2 X0 (X3 ◇ (X4 ◇ X0))]
    conv => enter [1]; rw [l5 X1 X2 X0 X3 X4]
  have l7 : ∀ X1 X3 : G, (X1 ◇ X3) = X3 := by
    intro X1 X3
    conv => enter [1, 2]; rw [← l4 X1 X1 X3 (X1 ◇ X1)]
    conv => enter [1]; rw [l6 X1 X1 X1 X3 X1]
  have l8 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) = X0 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [← l7 X3 (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3))))]
    conv => enter [1]; rw [← h5039 X0 X3 X1 X2]
  have l9 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ X3))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [← l7 X0 (X1 ◇ (X2 ◇ (X2 ◇ X3)))]
    conv => enter [1]; rw [l8 X0 X1 X2 X3]
  have l10 : ∀ X2 X3 X0 : G, (X2 ◇ (X2 ◇ X3)) = X0 := by
    intro X2 X3 X0
    conv => enter [1, 2, 2]; rw [← l7 X2 X3]
    conv => enter [1]; rw [l9 X2 X2 X3 X0]
  have l11 : ∀ X2 X3 X0 : G, (X2 ◇ X3) = X0 := by
    intro X2 X3 X0
    conv => enter [1, 2]; rw [← l7 X2 X3]
    conv => enter [1]; rw [l10 X2 X3 X0]
  have l12 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l11 X0 (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5039 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l12 x y]

@[equational_result]
theorem Equation2_implies_Equation5040 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5040 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (w ◇ (w ◇ z)))))]

theorem Equation4512_5040_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5040 : Equation5040 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h5040 X0 (X1 ◇ (X1 ◇ X0)) X0 X1]
    conv => enter [1]; rw [← h5040 X2 X1 (X1 ◇ (X1 ◇ X0)) X0]
  have l1 : ∀ X1 X2 X0 X3 X4 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X4 ◇ (X4 ◇ X3)))))) = X0 := by
    intro X1 X2 X0 X3 X4
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ (X4 ◇ (X4 ◇ X3))))]
    conv => enter [1]; rw [← h5040 X0 (X1 ◇ X2) X3 X4]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5040 X0 X1 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X0 X1 X1]
  have l3 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X3 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [← l2 X3 (X0 ◇ (X1 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [← h5040 X3 X2 X0 X1]
  have l4 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 X0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l3 X0 X0 X0 X3]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation2_implies_Equation5041 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5041 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (w ◇ (w ◇ w)))))]

theorem Equation4512_5041_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5041 : Equation5041 G) : Equation2 G := by
  have l0 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X2)))))) = X4 := by
    intro X3 X4 X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ X2))]
    conv => enter [1]; rw [← h5041 X4 X3 (X0 ◇ X1) X2]
  have l1 : ∀ X3 X0 X4 : G, (X3 ◇ X0) = X4 := by
    intro X3 X0 X4
    conv => enter [1, 2]; rw [h5041 X0 X4 X3 X3]
    conv => enter [1]; rw [l0 X3 X4 X0 X3 X3]
  have l2 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l1 X0 (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5041 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation5042 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5042 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (w ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5042_implies_Equation2 (G : Type*) [Magma G] (h5042 : Equation5042 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5042 X0 X2 X1 X1 X1]
    conv => enter [1]; rw [← h5042 X2 X1 X0 X1 (X1 ◇ X1)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5042 X2 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5044 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5044 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (w ◇ (u ◇ y)))))]

@[equational_result]
theorem Equation5044_implies_Equation2 (G : Type*) [Magma G] (h5044 : Equation5044 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, ((X1 ◇ X2) ◇ X0) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h5044 X0 X2 X1 X1 X1]
    conv => enter [1]; rw [← h5044 X2 (X1 ◇ X2) X0 X1 X1]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0 (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))]
    conv => enter [1]; rw [← h5044 X2 (X0 ◇ X0) X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5045 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5045 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (w ◇ (u ◇ z)))))]

@[equational_result]
theorem Equation5045_implies_Equation2 (G : Type*) [Magma G] (h5045 : Equation5045 G) : Equation2 G := by
  have l0 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ X1)) = X3 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2]; rw [h5045 (X0 ◇ X1) X3 X1 X2 X0]
    conv => enter [1]; rw [← h5045 X3 X2 (X0 ◇ X1) X1 X2]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X2 (X0 ◇ (X0 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [← h5045 X2 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5046 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5046 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (w ◇ (u ◇ w)))))]

@[equational_result]
theorem Equation5046_implies_Equation2 (G : Type*) [Magma G] (h5046 : Equation5046 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5046 X0 X2 (X1 ◇ X1) X1 X1]
    conv => enter [1]; rw [← h5046 X2 X1 X0 (X1 ◇ X1) X1]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5046 X2 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5047 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5047 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (w ◇ (u ◇ u)))))]

@[equational_result]
theorem Equation5047_implies_Equation2 (G : Type*) [Magma G] (h5047 : Equation5047 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5047 X0 X2 X1 (X1 ◇ X1) X1]
    conv => enter [1]; rw [← h5047 X2 X1 X0 X1 (X1 ◇ X1)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5047 X2 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5048 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5048 G := by
  intro x y z w u v
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (w ◇ (u ◇ v)))))]

theorem Equation4512_5048_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5048 : Equation5048 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 X3 X4 X5 X6 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X3 ◇ (X4 ◇ (X5 ◇ X6)))))) = X0 := by
    intro X1 X2 X0 X3 X4 X5 X6
    conv => enter [1]; rw [h4512 X1 X2 (X0 ◇ (X3 ◇ (X4 ◇ (X5 ◇ X6))))]
    conv => enter [1]; rw [← h5048 X0 (X1 ◇ X2) X3 X4 X5 X6]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h5048 X0 X0 X2 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X0 X2 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5050 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5050 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ y)))))]

theorem Equation4512_5050_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5050 : Equation5050 G) : Equation2 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h5050 X0 X0]
    conv => enter [1]; rw [← h5050 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X2)) = (X0 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) X2]
    conv => enter [1, 1]; rw [← h5050 X0 X1]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X0 ◇ (X0 ◇ X1))) X2]
  have l3 : ∀ X0 : G, (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0))) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) ((X0 ◇ (X0 ◇ X0)) ◇ X0)]
    conv => enter [1]; rw [l0 X0]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X1)) X2]
  have l5 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4512 X0 X0 ((X0 ◇ (X0 ◇ X0)) ◇ X0)]
    conv => enter [1]; rw [l3 X0]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l7 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) = X0 := by
    intro X0
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l5 X0]
  have l8 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l9 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := by
    intro X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X0 X0]
    conv => enter [1]; rw [l7 X0]
  have l10 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l8 X0 X0 X0]
    conv => enter [1]; rw [l9 X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l10 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5050 X0 X1]
    conv => enter [1, 2]; rw [← l11 X1 (X0 ◇ (X0 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [← h5050 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 (X1 ◇ (X1 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [← h5050 X1 X0]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l11 X1 X0]
    conv => enter [1]; rw [l13 X0 X1]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l12 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l14 X0 X1]
  have l16 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l12 X1 X0]
    conv => enter [1]; rw [l15 X1 X0]
  have l17 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l16 X0 (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0))))]
    conv => enter [1]; rw [← h5050 X1 X0]
  intro x y
  conv => enter [1]; rw [l17 x y]

@[equational_result]
theorem Equation2_implies_Equation5051 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5051 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (x ◇ (x ◇ z)))))]

theorem Equation4512_5051_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5051 : Equation5051 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2]; rw [h5051 X0 X2 X1]
    conv => enter [1]; rw [← h5051 X2 X1 (X0 ◇ (X0 ◇ (X0 ◇ X1)))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h5051 X0 X0 X1]
    conv => enter [1]; rw [← h5051 X0 X1 (X0 ◇ (X0 ◇ X1))]
  have l2 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X3)))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 X2 ((X1 ◇ X2) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X3))))]
    conv => enter [1]; rw [← h5051 X0 (X1 ◇ X2) X3]
  have l3 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X3))))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2]; rw [h4512 X1 X2 (X0 ◇ (X0 ◇ (X0 ◇ X3)))]
    conv => enter [1]; rw [l2 X1 X2 X0 X3]
  have l4 : ∀ X2 X0 : G, (X2 ◇ X0) = X2 := by
    intro X2 X0
    conv => enter [1, 2]; rw [← l1 X2 X0]
    conv => enter [1]; rw [l0 X2 X2 X0]
  have l5 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3))))) = X0 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← l1 X0 X3]
    conv => enter [1]; rw [l3 X1 X2 X0 X3]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))]
    conv => enter [1]; rw [l5 X0 X0 X1 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation2_implies_Equation5053 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5053 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (x ◇ (y ◇ y)))))]

theorem Equation4512_5053_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5053 : Equation5053 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) ◇ X2)) = (X0 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) X2]
    conv => enter [1, 1]; rw [← h5053 X0 X1]
  have l1 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l0 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X0 ◇ (X1 ◇ X1))) X2]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l1 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X1)) X2]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X1 X2]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 (X0 ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← h5053 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [l5 X0 X1]
    conv => enter [1]; rw [← h5053 X1 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [h5053 (X1 ◇ X1) X1]
    conv => enter [1, 2, 2]; rw [l5 (X1 ◇ X1) X0]
  have l8 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = ((X1 ◇ (X1 ◇ X2)) ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [l5 X0 (X1 ◇ (X1 ◇ X2))]
    conv => enter [1]; rw [← l4 (X1 ◇ (X1 ◇ X2)) X2 X1]
  have l9 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = (X1 ◇ ((X1 ◇ X2) ◇ X2)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l8 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ X2) X2]
  have l10 : ∀ X1 : G, (X1 ◇ (X1 ◇ X1)) = X1 := by
    intro X1
    conv => enter [1, 2]; rw [l7 X1 X1]
    conv => enter [1]; rw [l6 X1 X1]
  have l11 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ X2))) = (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X1 X2 X2]
    conv => enter [1]; rw [← l9 X1 X0 X2]
  have l12 : ∀ X1 X2 : G, (X1 ◇ X1) = (X1 ◇ (X1 ◇ (X2 ◇ X2))) := by
    intro X1 X2
    conv => enter [1]; rw [l7 X1 X1]
    conv => enter [1]; rw [← l11 X1 X2 X1]
  have l13 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2, 2]; rw [← l10 X0]
    conv => enter [1]; rw [← h5053 X0 X0]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = ((X0 ◇ (X0 ◇ X1)) ◇ X1) := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l10 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← l4 (X0 ◇ (X0 ◇ X1)) X1 X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l10 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) = (X0 ◇ ((X0 ◇ X1) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) X1]
  have l18 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l12 X0 X0]
    conv => enter [1]; rw [l13 X0]
  have l19 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 X1]
    conv => enter [1]; rw [← l17 X0 X1]
  have l20 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l19 X0 X1]
    conv => enter [1, 2]; rw [← l16 X0 X1]
  have l21 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1]; rw [l20 X0 X1]
  have l22 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l21 X0 X1]
    conv => enter [1]; rw [l18 X0]
  have l23 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l18 X0]
    conv => enter [1]; rw [← h5053 X1 X0]
  have l24 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l22 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l23 X0 X1]
  intro x y
  conv => enter [1]; rw [l24 x y]

@[equational_result]
theorem Equation2_implies_Equation5054 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5054 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (x ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5054_implies_Equation2 (G : Type*) [Magma G] (h5054 : Equation5054 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h5054 X0 X1 X0]
    conv => enter [1]; rw [← h5054 X1 X0 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h5054 X0 X0 X0]
    conv => enter [1]; rw [← h5054 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l1 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation5056 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5056 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (x ◇ (z ◇ y)))))]

theorem Equation4512_5056_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5056 : Equation5056 G) : Equation2 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))))) = X3 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [← h5056 X3 X2 (X0 ◇ X1)]
  have l1 : ∀ X1 X2 X0 : G, ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X0)) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h5056 X0 X2 X1]
    conv => enter [1]; rw [l0 (X1 ◇ X2) X2 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h5056 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X0 X0]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X0))) = X2 := by
    intro X1 X2 X0
    conv => enter [1]; rw [h4512 X1 X2 ((X1 ◇ X2) ◇ X0)]
    conv => enter [1]; rw [l1 X1 X2 X0]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h4512 X1 X2 X0]
    conv => enter [1]; rw [l3 X1 X2 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [h5056 (X0 ◇ X1) X1 X0]
    conv => enter [1, 2, 2, 2]; rw [l2 (X0 ◇ X1)]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [← l5 X1 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l4 X1 X0 X1]
  have l10 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X0 (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))))]
    conv => enter [1]; rw [l0 X0 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation2_implies_Equation5057 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5057 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (x ◇ (z ◇ z)))))]

theorem Equation4512_5057_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5057 : Equation5057 G) : Equation2 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h5057 (X0 ◇ X0) (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h5057 (X0 ◇ X0) (X0 ◇ X0) X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h5057 X0 X1 X0]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X0)) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [← l2 X2 X0]
    conv => enter [1]; rw [← h5057 X2 X1 X0]
  have l4 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l3 X0 (X2 ◇ (X2 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [← h5057 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation2_implies_Equation5058 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5058 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (x ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5058_implies_Equation2 (G : Type*) [Magma G] (h5058 : Equation5058 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X0)) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [h5058 X0 X2 X1 X1]
    conv => enter [1]; rw [← h5058 X2 X1 X0 (X0 ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 (X2 ◇ (X2 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [← h5058 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5060 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5060 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (y ◇ (x ◇ y)))))]

theorem Equation4512_5060_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5060 : Equation5060 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h5060 X0 X1]
    conv => enter [1]; rw [← h5060 X1 (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X2)) = (X0 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) X2]
    conv => enter [1, 1]; rw [← h5060 X0 X1]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ (X0 ◇ X1))) X2]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))))) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X1 ◇ (X0 ◇ X1))) ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))]
    conv => enter [1]; rw [l0 X1 X0]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X1)) X2]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ (X0 ◇ X1)) ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))]
    conv => enter [1]; rw [l3 X1 X0]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4512 X1 (X0 ◇ X1) ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))]
    conv => enter [1]; rw [l5 X1 X0]
  have l8 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))]
    conv => enter [1]; rw [l7 X1 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X1 (X0 ◇ (X1 ◇ (X0 ◇ X1))) (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))]
    conv => enter [1]; rw [l9 X1 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 (X1 ◇ (X0 ◇ X1)) (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))]
    conv => enter [1]; rw [l10 X1 X0]
  have l12 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))))))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X1 (X0 ◇ X1) (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))]
    conv => enter [1]; rw [l11 X1 X0]
  have l13 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))))))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))]
    conv => enter [1]; rw [l12 X1 X0]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [l8 X0 (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)) X1]
    conv => enter [1]; rw [l13 X1 X0]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0)))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X1 (X0 ◇ (X1 ◇ (X0 ◇ X1))) X0]
    conv => enter [1]; rw [l14 X1 X0]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0))))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l15 X1 X0]
  have l17 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0)))))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l16 X1 X0]
  have l18 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l17 X1 X0]
  have l19 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2, 2]; rw [l8 X0 X0 X1]
    conv => enter [1]; rw [l18 X1 X0]
  have l20 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h5060 X0 X0]
    conv => enter [1]; rw [l19 X0 X0]
  have l21 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l20 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l22 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l20 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l23 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5060 X0 X1]
    conv => enter [1, 2]; rw [← l21 X1 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [← h5060 X0 X1]
  have l24 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l21 X0 (X1 ◇ (X0 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [← h5060 X1 X0]
  have l25 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l22 X1 X0]
    conv => enter [1]; rw [l24 X0 X1]
  have l26 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l23 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l25 X0 X1]
  have l27 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l26 X0 (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))]
    conv => enter [1]; rw [← h5060 X1 X0]
  intro x y
  conv => enter [1]; rw [l27 x y]

@[equational_result]
theorem Equation2_implies_Equation5061 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5061 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (y ◇ (x ◇ z)))))]

theorem Equation4512_5061_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5061 : Equation5061 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h5061 X0 X2 X1]
    conv => enter [1]; rw [← h5061 X2 X1 (X2 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1))))]
  have l1 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X3)) := by
    intro X0 X3 X1 X2
    conv => enter [1, 1]; rw [h5061 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X1 (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) X3]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l1 X0 X3 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ (X0 ◇ X2))) X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X2)) X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ X2) X3]
  have l5 : ∀ X0 X3 : G, (X0 ◇ X3) = X0 := by
    intro X0 X3
    conv => enter [1]; rw [l4 X0 X3 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 ((X0 ◇ X0) ◇ X3)]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))]
    conv => enter [1]; rw [← h5061 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation2_implies_Equation5064 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5064 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5064_implies_Equation2 (G : Type*) [Magma G] (h5064 : Equation5064 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2]; rw [h5064 X0 X1 X1]
    conv => enter [1]; rw [← h5064 X2 X1 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h5064 X0 X0 X0]
    conv => enter [1]; rw [← h5064 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [l0 X1 X0 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X1 X0 X1]
    conv => enter [1]; rw [l0 X1 X1 (X0 ◇ X1)]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation2_implies_Equation5066 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5066 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (y ◇ (z ◇ y)))))]

theorem Equation4512_5066_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5066 : Equation5066 G) : Equation2 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))))) = X3 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [← h5066 X3 X2 (X0 ◇ X1)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h5066 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h5066 X1 X0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h5066 (X1 ◇ X0) X0 X1]
    conv => enter [1, 2, 2]; rw [l5 (X1 ◇ X0) X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1]; rw [← l3 X0 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l7 X1 X0]
    conv => enter [1]; rw [l1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l8 X1 X0]
    conv => enter [1]; rw [l5 X0 X1]
  have l10 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l8 X0 X0]
    conv => enter [1]; rw [l9 X0 X1]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation2_implies_Equation5067 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5067 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5067_implies_Equation2 (G : Type*) [Magma G] (h5067 : Equation5067 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h5067 (X0 ◇ (X1 ◇ X1)) X0 X1]
    conv => enter [1]; rw [← h5067 X0 X0 (X0 ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h5067 (X0 ◇ (X1 ◇ X1)) X0 X1]
    conv => enter [1]; rw [l0 X0 (X0 ◇ (X1 ◇ X1))]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0 X0]
    conv => enter [1]; rw [← h5067 X0 X0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l2 X1]
    conv => enter [1]; rw [l1 X0 X1]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X0)))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l2 X0]
    conv => enter [1]; rw [← h5067 X2 X1 X0]
  have l5 : ∀ X1 X2 : G, X1 = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l3 X1 (X2 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l4 X1 X2 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation2_implies_Equation5068 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5068 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5068_implies_Equation2 (G : Type*) [Magma G] (h5068 : Equation5068 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2]; rw [h5068 X0 X1 X1 X1]
    conv => enter [1]; rw [← h5068 X2 X1 X1 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h5068 X0 X1 X1 X1]
    conv => enter [1]; rw [← h5068 X1 X1 X0 (X1 ◇ (X1 ◇ X1))]
  have l2 : ∀ X1 X2 : G, X1 = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l1 X1 (X2 ◇ X1)]
    conv => enter [1]; rw [l0 X1 X2 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation5070 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5070 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (z ◇ (x ◇ y)))))]

theorem Equation4512_5070_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5070 : Equation5070 G) : Equation2 G := by
  have l0 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) = X2 := by
    intro X3 X2 X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h5070 X2 X3 (X0 ◇ X1)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h5070 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h5070 X0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l3 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l4 X0 X1]
  have l6 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) = ((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l5 (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) X1]
    conv => enter [1, 2]; rw [← h5070 X0 X1 X2]
  have l7 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0)))) = X0 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← h5070 X0 (X1 ◇ X0) X2]
  have l8 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [← l5 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l9 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l8 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l10 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))))) = X0 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 X0 ((X1 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0)))]
    conv => enter [1]; rw [l7 X1 X0 X2]
  have l11 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) = (X1 ◇ ((X0 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l6 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X2 ◇ (X0 ◇ X1))) X0]
  have l12 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ X0))) = X0 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [l9 X0 (X2 ◇ X0) (X1 ◇ X0)]
    conv => enter [1]; rw [l10 X1 X0 X2]
  have l13 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) = (X1 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l11 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X2 ◇ (X0 ◇ X1)) X0]
  have l14 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l5 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l12 (X1 ◇ X0) X0 X1]
  have l15 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) = (X1 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l13 X1 X0 X2]
    conv => enter [1, 2]; rw [l5 X0 (X2 ◇ (X0 ◇ X1))]
  have l16 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X1)))) = X0 := by
    intro X1 X0 X2
    conv => enter [1]; rw [l15 X1 X0 X2]
    conv => enter [1]; rw [l14 X1 X0]
  have l17 : ∀ X0 X2 X1 : G, (X0 ◇ (X2 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l14 X1 (X0 ◇ (X2 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l16 X1 X0 X2]
  have l18 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X0 := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l14 X0 (X2 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l17 X0 X2 X1]
  have l19 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l14 X0 X1]
    conv => enter [1]; rw [l18 X0 X0 X1]
  have l20 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l19 X0 (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))]
    conv => enter [1]; rw [l0 X0 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [l20 x y]

@[equational_result]
theorem Equation2_implies_Equation5071 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5071 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (z ◇ (x ◇ z)))))]

theorem Equation4512_5071_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5071 : Equation5071 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X3)))) ◇ X0)))) = X2 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h5071 X0 X2 X3]
    conv => enter [1]; rw [← h5071 X2 X1 (X2 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X3))))]
  have l1 : ∀ X3 X2 X0 X1 : G, (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))))) = X2 := by
    intro X3 X2 X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [← h5071 X2 X3 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 X3 X2 : G, (X0 ◇ X1) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h5071 (X0 ◇ X1) X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X2))]
  have l3 : ∀ X0 X1 X3 X2 : G, (X0 ◇ X1) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [l2 X0 X1 X3 X2]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l4 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ (X3 ◇ (X0 ◇ X3))) ◇ X0))))) = X2 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X2 (X0 ◇ (X3 ◇ (X0 ◇ X3))) X0]
    conv => enter [1]; rw [l0 X1 X2 X0 X3]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1 X0 X0]
    conv => enter [1]; rw [l1 X0 X0 X1 X0]
  have l6 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ ((X3 ◇ (X0 ◇ X3)) ◇ X0)))))) = X2 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 (X3 ◇ (X0 ◇ X3)) X0]
    conv => enter [1]; rw [l4 X1 X2 X0 X3]
  have l7 : ∀ X1 X2 : G, X1 = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l5 X1 (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)))))]
    conv => enter [1]; rw [l6 X1 X2 X1 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation2_implies_Equation5072 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5072 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (z ◇ (x ◇ w)))))]

@[equational_result]
theorem Equation5072_implies_Equation2 (G : Type*) [Magma G] (h5072 : Equation5072 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h5072 X0 X0 X1 X1]
    conv => enter [1]; rw [← h5072 X0 X1 X0 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5072 X0 X1 X1 X1]
    conv => enter [1]; rw [← h5072 X1 X1 X0 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation5074 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5074 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (z ◇ (y ◇ y)))))]

theorem Equation4512_5074_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5074 : Equation5074 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h5074 (X0 ◇ (X1 ◇ X1)) X1 X0]
    conv => enter [1]; rw [← h5074 X1 (X0 ◇ (X1 ◇ X1)) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1))))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 X1 ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h5074 (X0 ◇ (X1 ◇ X1)) X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← h5074 X1 X0 X1]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 (X1 ◇ X1) X0]
    conv => enter [1]; rw [l3 (X1 ◇ X1) X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation2_implies_Equation5075 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5075 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (z ◇ (y ◇ z)))))]

theorem Equation4512_5075_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5075 : Equation5075 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X3 X2 : G, (X0 ◇ X1) = (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h5075 (X0 ◇ X1) X3 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X2))]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h5075 (X0 ◇ X0) X0 X0]
    conv => enter [1]; rw [← h5075 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h5075 X1 X0 X0]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h5075 X2 X1 (X1 ◇ (X0 ◇ X1))]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l3 X1 X2 X0]
  have l5 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l4 X1 X2 X0]
  have l6 : ∀ X2 X1 : G, (X2 ◇ X1) = X2 := by
    intro X2 X1
    conv => enter [1]; rw [l0 X2 X1 X1 X2]
    conv => enter [1]; rw [l5 X1 X2 X2]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation2_implies_Equation5076 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5076 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (z ◇ (y ◇ w)))))]

@[equational_result]
theorem Equation5076_implies_Equation2 (G : Type*) [Magma G] (h5076 : Equation5076 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h5076 X0 X1 X0 X0]
    conv => enter [1]; rw [← h5076 X1 X0 X1 (X0 ◇ (X1 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5076 X0 X1 X1 X1]
    conv => enter [1]; rw [← h5076 X1 X1 X0 (X1 ◇ X1)]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation5078 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5078 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (z ◇ (z ◇ y)))))]

theorem Equation4512_5078_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5078 : Equation5078 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ X0)) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h5078 X0 X0 X1]
    conv => enter [1]; rw [← h5078 X0 (X1 ◇ (X1 ◇ X0)) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ X0) ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ X0) ((X1 ◇ (X1 ◇ X0)) ◇ X0)]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X0)) ◇ X0)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4512 X1 X0 ((X1 ◇ (X1 ◇ X0)) ◇ X0)]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X0) ◇ X0))))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 (X1 ◇ X0) X0]
    conv => enter [1]; rw [l2 X1 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X1 X0 X0]
    conv => enter [1]; rw [l3 X1 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h5078 X0 X0 X0]
    conv => enter [1]; rw [l4 X0 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l5 X0]
    conv => enter [1]; rw [← h5078 X1 X0 X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l6 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l5 X0]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l9 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l11 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X1)))) ◇ X0) = X1 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5078 X0 X1 X2]
    conv => enter [1]; rw [l9 (X1 ◇ (X0 ◇ (X2 ◇ (X2 ◇ X1)))) X1]
  have l12 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X0)) = X1 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X2 ◇ (X2 ◇ X1))) X0]
    conv => enter [1]; rw [l11 X1 X0 X2]
  have l13 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X0))) = X1 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4512 X0 (X2 ◇ (X2 ◇ X1)) X0]
    conv => enter [1]; rw [l12 X1 X0 X2]
  have l14 : ∀ X1 X2 : G, (X1 ◇ (X2 ◇ (X2 ◇ X1))) = X1 := by
    intro X1 X2
    conv => enter [1, 2]; rw [← l9 X1 (X2 ◇ (X2 ◇ X1))]
    conv => enter [1]; rw [l13 X1 X1 X2]
  have l15 : ∀ X2 X1 : G, (X2 ◇ X2) = X1 := by
    intro X2 X1
    conv => enter [1]; rw [l10 X2 X2 X1]
    conv => enter [1]; rw [l14 X1 X2]
  have l16 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l15 X1 X0]
    conv => enter [1]; rw [l5 X1]
  intro x y
  conv => enter [1]; rw [l16 x y]

@[equational_result]
theorem Equation2_implies_Equation5079 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5079 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (z ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5079_implies_Equation2 (G : Type*) [Magma G] (h5079 : Equation5079 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2]; rw [h5079 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1))) X1]
    conv => enter [1]; rw [← h5079 X2 X1 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l0 X0 X0 X0]
    conv => enter [1]; rw [← h5079 X0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X1 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h5079 X1 X1 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation5080 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5080 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (z ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5080_implies_Equation2 (G : Type*) [Magma G] (h5080 : Equation5080 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h5080 X0 X0 X1 X1]
    conv => enter [1]; rw [← h5080 X0 X1 X0 (X1 ◇ (X1 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5080 X0 X1 X0 X1]
    conv => enter [1]; rw [← h5080 X1 X1 X0 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation5082 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5082 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (z ◇ (w ◇ y)))))]

theorem Equation4512_5082_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5082 : Equation5082 G) : Equation2 G := by
  have l0 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) = X4 := by
    intro X3 X4 X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h5082 X4 X3 (X0 ◇ X1) X2]
  have l1 : ∀ X4 X5 X0 X1 X2 X3 : G, (X4 ◇ (X4 ◇ (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4))))))) = X5 := by
    intro X4 X5 X0 X1 X2 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
    conv => enter [1]; rw [l0 X4 X5 (X0 ◇ X1) X2 X3]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5082 X0 X1 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X0 X1 X1]
  have l3 : ∀ X4 X5 : G, X4 = X5 := by
    intro X4 X5
    conv => enter [1]; rw [← l2 X4 (X4 ◇ (X5 ◇ (X4 ◇ (X4 ◇ (X4 ◇ (X4 ◇ X4))))))]
    conv => enter [1]; rw [l1 X4 X5 X4 X4 X4 X4]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation5083 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5083 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (z ◇ (w ◇ z)))))]

@[equational_result]
theorem Equation5083_implies_Equation2 (G : Type*) [Magma G] (h5083 : Equation5083 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2]; rw [h5083 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1))) X1 X1]
    conv => enter [1]; rw [← h5083 X2 X1 (X0 ◇ (X1 ◇ (X1 ◇ X1))) (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h5083 (X0 ◇ X1) X2 X1 X0]
    conv => enter [1]; rw [← h5083 X2 X2 (X0 ◇ X1) X1]
  have l2 : ∀ X1 X2 : G, X1 = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l1 X1 X1 (X2 ◇ X1)]
    conv => enter [1]; rw [l0 X1 X2 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation5084 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5084 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (z ◇ (w ◇ w)))))]

@[equational_result]
theorem Equation5084_implies_Equation2 (G : Type*) [Magma G] (h5084 : Equation5084 G) : Equation2 G := by
  have l0 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X1)))) = X3 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2, 2]; rw [h5084 (X0 ◇ (X1 ◇ X1)) X3 X0 X1]
    conv => enter [1]; rw [← h5084 X3 X2 X3 (X0 ◇ (X1 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5084 X0 X1 (X1 ◇ X1) X1]
    conv => enter [1]; rw [← h5084 X1 X1 X0 (X1 ◇ X1)]
  have l2 : ∀ X2 X3 : G, X2 = X3 := by
    intro X2 X3
    conv => enter [1]; rw [← l1 X2 (X2 ◇ (X2 ◇ (X2 ◇ X2)))]
    conv => enter [1]; rw [l0 X2 X2 X2 X3]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation5085 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5085 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5085_implies_Equation2 (G : Type*) [Magma G] (h5085 : Equation5085 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X0)) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [h5085 X0 X2 X1 X1 X1]
    conv => enter [1]; rw [← h5085 X2 X1 X2 X0 (X1 ◇ (X1 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5085 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [← h5085 X1 X1 X0 X1 (X1 ◇ X1)]
  have l2 : ∀ X1 X2 : G, X1 = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l1 X1 (X1 ◇ X1)]
    conv => enter [1]; rw [l0 X1 X1 X2]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation5087 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5087 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (x ◇ (x ◇ y)))))]

theorem Equation4512_5087_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5087 : Equation5087 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h5087 X0 X1]
    conv => enter [1]; rw [← h5087 X1 (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X2)) = (X0 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) X2]
    conv => enter [1, 1]; rw [← h5087 X0 X1]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X1 ◇ (X0 ◇ (X0 ◇ X1))) X2]
  have l3 : ∀ X1 X0 : G, (X1 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X0))))) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X0 ◇ (X0 ◇ X1))) ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [l0 X1 X0]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X1)) X2]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X0)))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4512 X1 (X0 ◇ (X0 ◇ X1)) ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [l3 X1 X0]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X0))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4512 X0 (X0 ◇ X1) ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [l5 X1 X0]
  have l8 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l9 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X0)))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [l7 X1 X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X0))))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X1 (X1 ◇ (X0 ◇ (X0 ◇ X1))) ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l9 X1 X0]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X0)))))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X1 (X0 ◇ (X0 ◇ X1)) ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l10 X1 X0]
  have l12 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X0))))))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 (X0 ◇ X1) ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l11 X1 X0]
  have l13 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X0)))))))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l12 X1 X0]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X0))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [l8 X0 ((X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X0)) X1]
    conv => enter [1]; rw [l13 X1 X0]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ X0)))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X1 (X1 ◇ (X0 ◇ (X0 ◇ X1))) (X1 ◇ X0)]
    conv => enter [1]; rw [l14 X1 X0]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ X0))))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X1 (X0 ◇ (X0 ◇ X1)) (X1 ◇ X0)]
    conv => enter [1]; rw [l15 X1 X0]
  have l17 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0)))))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 (X0 ◇ X1) (X1 ◇ X0)]
    conv => enter [1]; rw [l16 X1 X0]
  have l18 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X1 ◇ X0))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l8 X1 ((X0 ◇ X1) ◇ (X1 ◇ X0)) X0]
    conv => enter [1]; rw [l17 X1 X0]
  have l19 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [l18 X1 X0]
  have l20 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h5087 X0 X1]
    conv => enter [1]; rw [l19 X1 (X1 ◇ (X0 ◇ (X0 ◇ X1)))]
  have l21 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h5087 X0 X0]
    conv => enter [1]; rw [l19 X0 X0]
  have l22 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l20 X1 X0]
  have l23 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0)))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l22 X1 X0]
  have l24 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0))))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l23 X1 X0]
  have l25 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l8 X0 X0 X1]
    conv => enter [1]; rw [l24 X1 X0]
  have l26 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l21 X0]
    conv => enter [1]; rw [l25 X1 X0]
  have l27 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l26 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))]
    conv => enter [1]; rw [← h5087 X1 X0]
  intro x y
  conv => enter [1]; rw [l27 x y]

@[equational_result]
theorem Equation2_implies_Equation5088 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5088 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (x ◇ (x ◇ z)))))]

@[equational_result]
theorem Equation5088_implies_Equation2 (G : Type*) [Magma G] (h5088 : Equation5088 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [h5088 X0 X2 X1]
    conv => enter [1]; rw [← h5088 X2 X1 (X2 ◇ (X0 ◇ (X0 ◇ X1)))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h5088 X0 X1 X1]
    conv => enter [1]; rw [← h5088 X1 X1 (X0 ◇ (X0 ◇ X1))]
  have l2 : ∀ X1 X2 : G, X1 = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l1 X1 (X1 ◇ X1)]
    conv => enter [1]; rw [l0 X1 X1 X2]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation5091 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5091 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (x ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5091_implies_Equation2 (G : Type*) [Magma G] (h5091 : Equation5091 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h5091 X0 X1 X1]
    conv => enter [1]; rw [← h5091 X2 X1 (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X1))))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h5091 X0 X1 X1]
    conv => enter [1]; rw [← h5091 X1 X1 (X0 ◇ (X1 ◇ X1))]
  have l2 : ∀ X1 X2 : G, X1 = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l1 X1 (X1 ◇ (X2 ◇ X1))]
    conv => enter [1]; rw [l0 X1 X2 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation5093 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5093 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (x ◇ (z ◇ y)))))]

theorem Equation4512_5093_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5093 : Equation5093 G) : Equation2 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))))) = X3 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [← h5093 X3 X2 (X0 ◇ X1)]
  have l1 : ∀ X3 X4 X0 X1 X2 : G, (X3 ◇ (X3 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))))) = X4 := by
    intro X3 X4 X0 X1 X2
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [l0 X3 X4 (X0 ◇ X1) X2]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5093 X0 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X0 X1]
  have l3 : ∀ X3 X4 : G, X3 = X4 := by
    intro X3 X4
    conv => enter [1]; rw [← l2 X3 (X3 ◇ (X3 ◇ (X4 ◇ (X3 ◇ (X3 ◇ (X3 ◇ X3))))))]
    conv => enter [1]; rw [l1 X3 X4 X3 X3 X3]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation5094 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5094 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (x ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5094_implies_Equation2 (G : Type*) [Magma G] (h5094 : Equation5094 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5094 (X0 ◇ X0) X1 X0]
    conv => enter [1]; rw [← h5094 X1 X1 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [h5094 (X1 ◇ X1) X0 X1]
    conv => enter [1, 2, 2]; rw [l0 X0 (X1 ◇ X1)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [l0 X0 X0]
  have l3 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l2 X0 X0]
    conv => enter [1]; rw [l2 X0 X2]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation5095 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5095 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (x ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5095_implies_Equation2 (G : Type*) [Magma G] (h5095 : Equation5095 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [h5095 X0 X2 X1 X1]
    conv => enter [1]; rw [← h5095 X2 X1 X2 (X2 ◇ (X0 ◇ (X1 ◇ X1)))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5095 X0 X1 X1 X1]
    conv => enter [1]; rw [← h5095 X1 X1 X0 (X1 ◇ X1)]
  have l2 : ∀ X1 X2 : G, X1 = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l1 X1 (X1 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [l0 X1 X1 X2]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation5098 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5098 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (y ◇ (x ◇ z)))))]

@[equational_result]
theorem Equation5098_implies_Equation2 (G : Type*) [Magma G] (h5098 : Equation5098 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X0)))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2]; rw [h5098 X0 X2 X1]
    conv => enter [1]; rw [← h5098 X2 X1 (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5098 X0 X1 X1]
    conv => enter [1]; rw [← h5098 X1 X1 (X0 ◇ X1)]
  have l2 : ∀ X1 X2 : G, X1 = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l1 X1 (X1 ◇ (X1 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l0 X1 X1 X2]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation5100 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5100 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5100_implies_Equation2 (G : Type*) [Magma G] (h5100 : Equation5100 G) : Equation2 G := by
  have l0 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h5100 X0 X0]
    conv => enter [1]; rw [← h5100 X2 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5101 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5101 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5101_implies_Equation2 (G : Type*) [Magma G] (h5101 : Equation5101 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5101 X0 X0 X0]
    conv => enter [1]; rw [← h5101 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5103 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5103 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (y ◇ (z ◇ y)))))]

@[equational_result]
theorem Equation5103_implies_Equation2 (G : Type*) [Magma G] (h5103 : Equation5103 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5103 X0 X0 X0]
    conv => enter [1]; rw [← h5103 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5104 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5104 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5104_implies_Equation2 (G : Type*) [Magma G] (h5104 : Equation5104 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5104 X0 X0 X0]
    conv => enter [1]; rw [← h5104 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5105 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5105 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5105_implies_Equation2 (G : Type*) [Magma G] (h5105 : Equation5105 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5105 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5105 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5107 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5107 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (z ◇ (x ◇ y)))))]

theorem Equation4512_5107_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5107 : Equation5107 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h5107 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) = X2 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X3)]
    conv => enter [1]; rw [← h5107 X2 X3 (X0 ◇ X1)]
  have l2 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 X2 ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))))]
    conv => enter [1]; rw [← h5107 X0 (X1 ◇ X2) X3]
  have l3 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2]; rw [h4512 X1 X2 ((X1 ◇ X2) ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))]
    conv => enter [1]; rw [l2 X1 X2 X3 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0 X0]
    conv => enter [1]; rw [l1 X0 X0 X0 X1]
  have l5 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X1 X2 (X3 ◇ (X0 ◇ (X1 ◇ X2)))]
    conv => enter [1]; rw [l3 X1 X2 X3 X0]
  have l6 : ∀ X2 X1 X3 X0 : G, (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))))))) = X0 := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [← l4 X1 (X2 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))))))]
    conv => enter [1]; rw [l5 X1 X2 X3 X0]
  have l7 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [← l4 X2 (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))))))]
    conv => enter [1]; rw [l6 X2 X1 X3 X0]
  have l8 : ∀ X2 X1 X3 X0 : G, (X2 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))))) = X0 := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [← l4 X1 (X2 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))))]
    conv => enter [1]; rw [l7 X1 X2 X3 X0]
  have l9 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [← l4 X2 (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))))]
    conv => enter [1]; rw [l8 X2 X1 X3 X0]
  have l10 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = X0 := by
    intro X2 X3 X0 X1
    conv => enter [1]; rw [← l4 X1 (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))]
    conv => enter [1]; rw [l9 X1 X2 X3 X0]
  have l11 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ X2))) = X0 := by
    intro X3 X0 X1 X2
    conv => enter [1]; rw [← l4 X2 (X3 ◇ (X0 ◇ (X1 ◇ X2)))]
    conv => enter [1]; rw [l10 X2 X3 X0 X1]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = X0 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [← l4 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [l11 X0 X0 X1 X2]
  have l13 : ∀ X1 X2 X0 : G, (X1 ◇ X2) = X0 := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l4 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [l12 X0 X1 X2]
  have l14 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l13 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5107 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l14 x y]

@[equational_result]
theorem Equation2_implies_Equation5108 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5108 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (z ◇ (x ◇ z)))))]

theorem Equation4512_5108_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5108 : Equation5108 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h5108 X0 (X0 ◇ X1) X1]
    conv => enter [1]; rw [← h5108 X1 (X0 ◇ X1) (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 (X0 ◇ (X1 ◇ X0)) (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h5108 X1 (X0 ◇ (X1 ◇ X0)) X0]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l5 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X0) (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l2 X0 X1]
  have l6 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l4 (X1 ◇ X0) (X1 ◇ X0) X0]
    conv => enter [1]; rw [l5 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l6 X1 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X0 X1]
    conv => enter [1]; rw [l7 X1 X0]
  have l9 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l8 X0 X0]
    conv => enter [1]; rw [l8 X0 X2]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation2_implies_Equation5109 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5109 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (z ◇ (x ◇ w)))))]

@[equational_result]
theorem Equation5109_implies_Equation2 (G : Type*) [Magma G] (h5109 : Equation5109 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5109 X0 X1 X2 X1]
    conv => enter [1]; rw [← h5109 X2 X1 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5109 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5111 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5111 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (z ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5111_implies_Equation2 (G : Type*) [Magma G] (h5111 : Equation5111 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5111 X0 X0 X0]
    conv => enter [1]; rw [← h5111 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5112 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5112 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (z ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5112_implies_Equation2 (G : Type*) [Magma G] (h5112 : Equation5112 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5112 X0 X0 X0]
    conv => enter [1]; rw [← h5112 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5113 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5113 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (z ◇ (y ◇ w)))))]

@[equational_result]
theorem Equation5113_implies_Equation2 (G : Type*) [Magma G] (h5113 : Equation5113 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5113 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5113 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5115 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5115 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (z ◇ (z ◇ y)))))]

@[equational_result]
theorem Equation5115_implies_Equation2 (G : Type*) [Magma G] (h5115 : Equation5115 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5115 X0 X0 X0]
    conv => enter [1]; rw [← h5115 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5116 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5116 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (z ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5116_implies_Equation2 (G : Type*) [Magma G] (h5116 : Equation5116 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5116 X0 X0 X0]
    conv => enter [1]; rw [← h5116 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5117 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5117 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (z ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5117_implies_Equation2 (G : Type*) [Magma G] (h5117 : Equation5117 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5117 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5117 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5119 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5119 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (z ◇ (w ◇ y)))))]

@[equational_result]
theorem Equation5119_implies_Equation2 (G : Type*) [Magma G] (h5119 : Equation5119 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5119 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5119 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5120 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5120 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (z ◇ (w ◇ z)))))]

@[equational_result]
theorem Equation5120_implies_Equation2 (G : Type*) [Magma G] (h5120 : Equation5120 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5120 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5120 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5121 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5121 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (z ◇ (w ◇ w)))))]

@[equational_result]
theorem Equation5121_implies_Equation2 (G : Type*) [Magma G] (h5121 : Equation5121 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5121 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5121 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5122 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5122 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5122_implies_Equation2 (G : Type*) [Magma G] (h5122 : Equation5122 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5122 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5122 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5124 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5124 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (x ◇ (x ◇ y)))))]

theorem Equation4512_5124_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5124 : Equation5124 G) : Equation2 G := by
  have l0 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))))) = X2 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ X3))]
    conv => enter [1]; rw [← h5124 X2 X3 (X0 ◇ X1)]
  have l1 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4))))))) = X3 := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X3 ◇ X4)))]
    conv => enter [1]; rw [l0 X4 (X0 ◇ X1) X2 X3]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5124 X0 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X0]
  have l3 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4)))))) = X3 := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2]; rw [← l2 X4 (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4)))))]
    conv => enter [1]; rw [l1 X4 X0 X1 X2 X3]
  have l4 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4))))) = X3 := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [← l2 X4 (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4)))))]
    conv => enter [1]; rw [l3 X4 X0 X1 X2 X3]
  have l5 : ∀ X1 X2 X3 X4 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X4)))) = X3 := by
    intro X1 X2 X3 X4
    conv => enter [1, 2]; rw [← l2 X1 (X2 ◇ (X3 ◇ (X3 ◇ X4)))]
    conv => enter [1]; rw [l4 X1 X1 X2 X3 X4]
  have l6 : ∀ X2 X3 X4 : G, (X2 ◇ (X3 ◇ (X3 ◇ X4))) = X3 := by
    intro X2 X3 X4
    conv => enter [1, 2]; rw [← l2 X2 (X3 ◇ (X3 ◇ X4))]
    conv => enter [1]; rw [l5 X2 X2 X3 X4]
  have l7 : ∀ X3 X4 : G, (X3 ◇ (X3 ◇ X4)) = X3 := by
    intro X3 X4
    conv => enter [1, 2, 2]; rw [← l2 X3 X4]
    conv => enter [1]; rw [l6 X3 X3 X4]
  have l8 : ∀ X3 X4 : G, (X3 ◇ X4) = X3 := by
    intro X3 X4
    conv => enter [1, 2]; rw [← l2 X3 X4]
    conv => enter [1]; rw [l7 X3 X4]
  have l9 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l8 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X0)))))]
    conv => enter [1]; rw [l0 X0 X0 X0 X3]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation2_implies_Equation5125 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5125 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (x ◇ (x ◇ z)))))]

theorem Equation4512_5125_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5125 : Equation5125 G) : Equation2 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h5125 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h5125 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 X0 X0]
    conv => enter [1]; rw [l0 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h5125 X0 X1 X0]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ ((X0 ◇ X0) ◇ X0))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [← l2 X2 X0]
    conv => enter [1]; rw [← h5125 X2 X1 (X0 ◇ X0)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [← h5125 X0 X1 X0]
  have l5 : ∀ X0 X2 : G, ((X0 ◇ X0) ◇ X0) = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l4 X0 ((X0 ◇ X0) ◇ X0)]
    conv => enter [1]; rw [l3 X0 X0 X2]
  have l6 : ∀ X0 X2 : G, (X0 ◇ (X0 ◇ X0)) = X2 := by
    intro X0 X2
    conv => enter [1]; rw [h4512 X0 X0 X0]
    conv => enter [1]; rw [l5 X0 X2]
  have l7 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l4 X0 X0]
    conv => enter [1]; rw [l6 X0 X2]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation2_implies_Equation5126 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5126 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (x ◇ (x ◇ w)))))]

@[equational_result]
theorem Equation5126_implies_Equation2 (G : Type*) [Magma G] (h5126 : Equation5126 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X0)) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [h5126 X0 X2 X2 X1]
    conv => enter [1]; rw [← h5126 X2 X1 X2 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5126 X0 X1 X0 X1]
    conv => enter [1]; rw [← h5126 X0 X1 X1 (X0 ◇ X1)]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [l0 X1 X0 X2]
  have l3 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l2 X0 (X0 ◇ (X0 ◇ (X3 ◇ (X3 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5126 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation5128 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5128 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (x ◇ (y ◇ y)))))]

theorem Equation4512_5128_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5128 : Equation5128 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h5128 (X0 ◇ X1) X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l1 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))))) = X2 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ X3))]
    conv => enter [1]; rw [← h5128 X2 X3 (X0 ◇ X1)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h5128 X0 X1 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [← h5128 X1 (X0 ◇ (X1 ◇ X1)) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) ((X0 ◇ (X1 ◇ X1)) ◇ X0)]
    conv => enter [1]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0 X0]
    conv => enter [1]; rw [l1 X0 X0 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 X1 ((X0 ◇ (X1 ◇ X1)) ◇ X0)]
    conv => enter [1]; rw [l3 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X0 (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)))]
    conv => enter [1]; rw [l5 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l4 X1 ((X0 ◇ (X1 ◇ X1)) ◇ X0)]
    conv => enter [1]; rw [l6 X1 X0]
  have l8 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X1 ((X0 ◇ (X1 ◇ X1)) ◇ X0)]
    conv => enter [1]; rw [l7 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) X0]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X1 X0 : G, ((X1 ◇ X1) ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l4 X0 ((X1 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [h4512 X1 X1 X0]
    conv => enter [1]; rw [l10 X1 X0]
  have l12 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l4 X1 X0]
    conv => enter [1]; rw [l11 X1 X0]
  have l13 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l12 X0 (X0 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5128 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l13 x y]

@[equational_result]
theorem Equation2_implies_Equation5129 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5129 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (x ◇ (y ◇ z)))))]

theorem Equation4512_5129_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5129 : Equation5129 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X3 ◇ X0)))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h5129 X0 X1 X2]
    conv => enter [1]; rw [← h5129 X3 X1 (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))]
  have l1 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2)))) X3]
    conv => enter [1, 1]; rw [← h5129 X0 X1 X2]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l1 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X0 ◇ (X1 ◇ X2))) X3]
  have l3 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ X0))))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2]; rw [h4512 X1 (X2 ◇ (X0 ◇ (X1 ◇ X2))) (X3 ◇ X0)]
    conv => enter [1]; rw [l0 X1 X2 X0 X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X0 ◇ (X1 ◇ X2)) X3]
  have l5 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)))))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X2 (X0 ◇ (X1 ◇ X2)) (X3 ◇ X0)]
    conv => enter [1]; rw [l3 X1 X2 X0 X3]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l4 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l7 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))))))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 (X1 ◇ X2) (X3 ◇ X0)]
    conv => enter [1]; rw [l5 X1 X2 X0 X3]
  have l8 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l6 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l9 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))))))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X1 X2 (X3 ◇ X0)]
    conv => enter [1]; rw [l7 X1 X2 X0 X3]
  have l10 : ∀ X1 X0 X3 : G, (X1 ◇ (X0 ◇ (X3 ◇ X0))) = X3 := by
    intro X1 X0 X3
    conv => enter [1, 2]; rw [l8 X0 (X3 ◇ X0) X1 X1]
    conv => enter [1]; rw [l9 X1 X1 X0 X3]
  have l11 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [← l10 (X0 ◇ X2) X2 X0]
    conv => enter [1]; rw [l10 X1 (X0 ◇ X2) X2]
  have l12 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l11 X0 (X0 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5129 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l12 x y]

@[equational_result]
theorem Equation2_implies_Equation5130 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5130 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (x ◇ (y ◇ w)))))]

@[equational_result]
theorem Equation5130_implies_Equation2 (G : Type*) [Magma G] (h5130 : Equation5130 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h5130 X0 X0 X1 X0]
    conv => enter [1]; rw [← h5130 X1 X0 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l0 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5132 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5132 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (x ◇ (z ◇ y)))))]

theorem Equation4512_5132_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5132 : Equation5132 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X3 X2 : G, (X0 ◇ X1) = (X3 ◇ (X3 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) := by
    intro X0 X1 X3 X2
    conv => enter [1]; rw [h5132 (X0 ◇ X1) X3 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X1 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h5132 X0 X1 X1]
    conv => enter [1]; rw [← h5132 X1 (X0 ◇ (X1 ◇ X1)) X1]
  have l2 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X1)))) X3]
    conv => enter [1, 1]; rw [← h5132 X0 X1 X2]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ (X2 ◇ X1))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l2 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X1 (X2 ◇ (X0 ◇ (X2 ◇ X1))) X3]
  have l4 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ X1) ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X1) ((X0 ◇ (X1 ◇ X1)) ◇ X0)]
    conv => enter [1]; rw [l1 X0 X1]
  have l5 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ (X2 ◇ X1)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X2 (X0 ◇ (X2 ◇ X1)) X3]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 X1 ((X0 ◇ (X1 ◇ X1)) ◇ X0)]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ ((X2 ◇ X1) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l5 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X2 ◇ X1) X3]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 (X1 ◇ X1) X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l9 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X2 ◇ (X1 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l7 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X2 X1 X3]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X1 X1 X0]
    conv => enter [1]; rw [l8 X0 X1]
  have l11 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← l10 X1 X0]
    conv => enter [1]; rw [l10 (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) X1]
  have l12 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X2 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0)))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2]; rw [h5132 X0 X2 X1]
    conv => enter [1]; rw [l10 (X1 ◇ (X0 ◇ (X1 ◇ X2))) X2]
  have l13 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h5132 X0 X0 X0]
    conv => enter [1]; rw [l10 X0 X0]
  have l14 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2, 2]; rw [← l10 X1 X0]
    conv => enter [1]; rw [← h5132 X2 (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) X1]
  have l15 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [← l10 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) X2]
  have l16 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l15 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) X2]
  have l17 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ (X2 ◇ X0))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ (X2 ◇ X0)))]
    conv => enter [1]; rw [l14 X0 X1 X2]
  have l18 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X2 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0))))) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X1 ◇ X2)) (X2 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0)))]
    conv => enter [1]; rw [l12 X1 X0 X2]
  have l19 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ X0)))))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ X0))))]
    conv => enter [1]; rw [l11 X0 X1]
  have l20 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l16 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X0 ◇ (X0 ◇ X1))) X2]
  have l21 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ (X2 ◇ X0)))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X0 ◇ X1))) ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ (X2 ◇ X0)))]
    conv => enter [1]; rw [l17 X0 X1 X2]
  have l22 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X2 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0)))))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ X2) (X2 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0)))]
    conv => enter [1]; rw [l18 X1 X0 X2]
  have l23 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ X0))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X0 ◇ X1))) (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ X0))))]
    conv => enter [1]; rw [l19 X0 X1]
  have l24 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l20 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X1)) X2]
  have l25 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ (X2 ◇ X0))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4512 X1 (X0 ◇ (X0 ◇ X1)) ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ (X2 ◇ X0)))]
    conv => enter [1]; rw [l21 X0 X1 X2]
  have l26 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0))))))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [h4512 X1 X2 (X2 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0)))]
    conv => enter [1]; rw [l22 X1 X0 X2]
  have l27 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ X0)))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X1 (X0 ◇ (X0 ◇ X1)) (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ X0))))]
    conv => enter [1]; rw [l23 X0 X1]
  have l28 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l24 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l29 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ (X2 ◇ X0)))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 (X0 ◇ X1) ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ (X2 ◇ X0)))]
    conv => enter [1]; rw [l25 X0 X1 X2]
  have l30 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)))))))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X1 (X0 ◇ (X1 ◇ X2)) X0]
    conv => enter [1]; rw [l26 X1 X0 X2]
  have l31 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ X0))))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 (X0 ◇ X1) (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ X0))))]
    conv => enter [1]; rw [l27 X0 X1]
  have l32 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l28 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l33 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ (X2 ◇ X0))))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ (X2 ◇ X0)))]
    conv => enter [1]; rw [l29 X0 X1 X2]
  have l34 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X0))))))))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 (X1 ◇ X2) X0]
    conv => enter [1]; rw [l30 X1 X0 X2]
  have l35 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ X0)))))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X1 (X1 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) ◇ (X1 ◇ X0))))]
    conv => enter [1]; rw [l31 X0 X1]
  have l36 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ (X2 ◇ X0)))))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) (X1 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l33 X0 X1 X2]
  have l37 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))))))))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X1 X2 X0]
    conv => enter [1]; rw [l34 X1 X0 X2]
  have l38 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X0))))))))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) (X1 ◇ X0)]
    conv => enter [1]; rw [l35 X0 X1]
  have l39 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X1 ◇ (X2 ◇ X0))))))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X0 ◇ X1))) (X1 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l36 X0 X1 X2]
  have l40 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0))))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2]; rw [l9 X0 X0 X2 X1]
    conv => enter [1]; rw [l37 X1 X0 X2]
  have l41 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X0)))))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [l9 X1 ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X1 ◇ X0)) X0 X1]
    conv => enter [1]; rw [l38 X0 X1]
  have l42 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X0)))))))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2, 2, 2, 2, 2, 2]; rw [h4512 X1 (X0 ◇ (X0 ◇ X1)) (X1 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l39 X0 X1 X2]
  have l43 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X0)))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2]; rw [← l13 X0]
    conv => enter [1]; rw [l40 X1 X0 X2]
  have l44 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) X0 X1]
    conv => enter [1]; rw [l41 X0 X1]
  have l45 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X0)))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [l32 X0 ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X2 ◇ X0))) X1]
    conv => enter [1]; rw [l42 X0 X1 X2]
  have l46 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l43 X0 X1 X0]
    conv => enter [1]; rw [l44 X1 X0]
  have l47 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ X0))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 (X0 ◇ X1) (X1 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l45 X0 X1 X2]
  have l48 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l46 X0 (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X2 ◇ X0))))))]
    conv => enter [1]; rw [l47 X0 X0 X2]
  intro x y
  conv => enter [1]; rw [l48 x y]

@[equational_result]
theorem Equation2_implies_Equation5133 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5133 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (x ◇ (z ◇ z)))))]

theorem Equation4512_5133_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5133 : Equation5133 G) : Equation2 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h5133 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h5133 X0 (X0 ◇ X0) (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = ((X1 ◇ (X0 ◇ (X1 ◇ X1))) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X1 ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1, 2]; rw [← h5133 X0 (X1 ◇ (X0 ◇ (X1 ◇ X1))) X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h5133 X0 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X0)) X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X1 ◇ X1)) X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l3 X0 ((X0 ◇ X0) ◇ X1)]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X0))) := by
    intro X1 X0
    conv => enter [1]; rw [l6 X1 X0]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X1) X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l7 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X1))) = (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) := by
    intro X1 X0
    conv => enter [1]; rw [l8 X1 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X1 X1 X0]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l3 X0 X1]
    conv => enter [1, 2]; rw [← l9 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  have l12 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ (X0 ◇ (X1 ◇ X1))) := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l3 X1 X0]
    conv => enter [1]; rw [← l10 X1 X0]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = (X1 ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l12 X0 X1]
    conv => enter [1]; rw [l11 X0 (X1 ◇ (X0 ◇ X0))]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ (X1 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [← l11 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [l13 X1 X0]
  have l15 : ∀ X1 X0 : G, (X1 ◇ X1) = (X0 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l14 X1 X0]
    conv => enter [1]; rw [l11 X1 (X0 ◇ X0)]
  have l16 : ∀ X1 X0 : G, (X1 ◇ X1) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l15 X1 X0]
    conv => enter [1]; rw [l11 X0 X0]
  have l17 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l11 X0 X0]
    conv => enter [1]; rw [l16 X0 X1]
  intro x y
  conv => enter [1]; rw [l17 x y]

@[equational_result]
theorem Equation2_implies_Equation5134 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5134 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (x ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5134_implies_Equation2 (G : Type*) [Magma G] (h5134 : Equation5134 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h5134 X0 X0 X1 X0]
    conv => enter [1]; rw [← h5134 X1 X0 X0 (X1 ◇ X0)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l0 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5136 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5136 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (x ◇ (w ◇ y)))))]

theorem Equation4512_5136_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5136 : Equation5136 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X3 X4 X2 : G, (X0 ◇ X1) = (X3 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) := by
    intro X0 X1 X3 X4 X2
    conv => enter [1]; rw [h5136 (X0 ◇ X1) X3 X4 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l1 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))))) = X2 := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
    conv => enter [1]; rw [← h5136 X2 X4 (X0 ◇ X1) X3]
  have l2 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X2)) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [h5136 X0 X2 X0 X1]
    conv => enter [1]; rw [← h5136 X2 (X0 ◇ (X1 ◇ X2)) X2 X0]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) ((X0 ◇ (X1 ◇ X2)) ◇ X0)]
    conv => enter [1]; rw [l2 X0 X1 X2]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [l1 X0 X0 X0 X1 X0]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X1 X2 ((X0 ◇ (X1 ◇ X2)) ◇ X0)]
    conv => enter [1]; rw [l3 X0 X1 X2]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0))) = X2 := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l4 X0 (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)))]
    conv => enter [1]; rw [l5 X0 X1 X2]
  have l7 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) = X2 := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l4 X1 (X2 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0))]
    conv => enter [1]; rw [l6 X1 X2 X0]
  have l8 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X0) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l4 X2 ((X0 ◇ (X1 ◇ X2)) ◇ X0)]
    conv => enter [1]; rw [l7 X2 X0 X1]
  have l9 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X0]
    conv => enter [1]; rw [l8 X0 X1 X2]
  have l10 : ∀ X1 X2 X0 : G, ((X1 ◇ X2) ◇ X0) = X2 := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l4 X0 ((X1 ◇ X2) ◇ X0)]
    conv => enter [1]; rw [l9 X0 X1 X2]
  have l11 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l4 (X0 ◇ X2) X0]
    conv => enter [1]; rw [l10 X0 X2 X0]
  intro x y
  conv => enter [1]; rw [l11 x y]

@[equational_result]
theorem Equation2_implies_Equation5137 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5137 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (x ◇ (w ◇ z)))))]

@[equational_result]
theorem Equation5137_implies_Equation2 (G : Type*) [Magma G] (h5137 : Equation5137 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, ((X1 ◇ X2) ◇ X0) = X2 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h5137 X0 (X1 ◇ X2) X2 X1]
    conv => enter [1]; rw [← h5137 X2 (X1 ◇ X2) (X1 ◇ X2) X0]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 X0 ((X0 ◇ X0) ◇ (X0 ◇ (X3 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5137 X3 (X0 ◇ X0) X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5138 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5138 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (x ◇ (w ◇ w)))))]

@[equational_result]
theorem Equation5138_implies_Equation2 (G : Type*) [Magma G] (h5138 : Equation5138 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X0)) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [h5138 X0 X2 (X0 ◇ (X1 ◇ X1)) X1]
    conv => enter [1]; rw [← h5138 X2 X1 X2 (X0 ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X3 ◇ (X0 ◇ X0))) X0]
    conv => enter [1]; rw [← h5138 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5139 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5139 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (x ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5139_implies_Equation2 (G : Type*) [Magma G] (h5139 : Equation5139 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5139 X0 X1 X2 X1 X1]
    conv => enter [1]; rw [← h5139 X2 X1 X1 X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X3 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5139 X3 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5141 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5141 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (y ◇ (x ◇ y)))))]

theorem Equation4512_5141_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5141 : Equation5141 G) : Equation2 G := by
  have l0 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))))) = X3 := by
    intro X2 X0 X1 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ X2))]
    conv => enter [1]; rw [← h5141 X3 X2 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h5141 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 (X0 ◇ X1) X1 X1 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5141 X0 X1 X1]
    conv => enter [1]; rw [l0 X1 X1 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [l1 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ X1) ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 (X1 ◇ ((X0 ◇ X1) ◇ X0))]
    conv => enter [1]; rw [l3 X0 X1]
  have l5 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l2 X1 ((X0 ◇ X1) ◇ X0)]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l5 X0 X1]
  have l7 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [← l2 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l7 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X0)))))]
    conv => enter [1]; rw [l0 X0 X0 X0 X3]
  intro x y
  conv => enter [1]; rw [l8 x y]

@[equational_result]
theorem Equation2_implies_Equation5142 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5142 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (y ◇ (x ◇ z)))))]

theorem Equation4512_5142_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5142 : Equation5142 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X0))) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2]; rw [h5142 X0 X1 X2]
    conv => enter [1]; rw [← h5142 X1 X1 (X2 ◇ (X1 ◇ (X0 ◇ X2)))]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)))) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [h4512 X2 (X1 ◇ (X0 ◇ X2)) X0]
    conv => enter [1]; rw [l0 X1 X2 X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0))))) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 (X0 ◇ X2) X0]
    conv => enter [1]; rw [l1 X1 X2 X0]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))))) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X2 X0]
    conv => enter [1]; rw [l2 X1 X2 X0]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h5142 X0 X0 X0]
    conv => enter [1]; rw [l3 X0 X0 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← l4 X0]
    conv => enter [1]; rw [l3 X1 X0 X0]
  have l6 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h5142 X0 X1 X0]
    conv => enter [1]; rw [l5 X1 X0]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation2_implies_Equation5143 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5143 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (y ◇ (x ◇ w)))))]

@[equational_result]
theorem Equation5143_implies_Equation2 (G : Type*) [Magma G] (h5143 : Equation5143 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X0)) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [h5143 X0 X1 X2 X1]
    conv => enter [1]; rw [← h5143 X2 X1 X1 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5143 X0 X1 X1 X1]
    conv => enter [1]; rw [← h5143 X1 X1 X1 (X0 ◇ X1)]
  have l2 : ∀ X1 X2 : G, X1 = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l1 X1 (X1 ◇ X1)]
    conv => enter [1]; rw [l0 X1 X1 X2]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation5145 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5145 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5145_implies_Equation2 (G : Type*) [Magma G] (h5145 : Equation5145 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5145 X0 X0 X0]
    conv => enter [1]; rw [← h5145 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5146 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5146 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5146_implies_Equation2 (G : Type*) [Magma G] (h5146 : Equation5146 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5146 X0 X0 X0]
    conv => enter [1]; rw [← h5146 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5147 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5147 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (y ◇ (y ◇ w)))))]

@[equational_result]
theorem Equation5147_implies_Equation2 (G : Type*) [Magma G] (h5147 : Equation5147 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5147 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5147 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5149 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5149 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (y ◇ (z ◇ y)))))]

@[equational_result]
theorem Equation5149_implies_Equation2 (G : Type*) [Magma G] (h5149 : Equation5149 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5149 X0 X0 X0]
    conv => enter [1]; rw [← h5149 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5150 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5150 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5150_implies_Equation2 (G : Type*) [Magma G] (h5150 : Equation5150 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5150 X0 X0 X0]
    conv => enter [1]; rw [← h5150 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5151 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5151 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5151_implies_Equation2 (G : Type*) [Magma G] (h5151 : Equation5151 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5151 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5151 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5153 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5153 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (y ◇ (w ◇ y)))))]

@[equational_result]
theorem Equation5153_implies_Equation2 (G : Type*) [Magma G] (h5153 : Equation5153 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5153 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5153 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5154 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5154 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (y ◇ (w ◇ z)))))]

@[equational_result]
theorem Equation5154_implies_Equation2 (G : Type*) [Magma G] (h5154 : Equation5154 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5154 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5154 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5155 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5155 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (y ◇ (w ◇ w)))))]

@[equational_result]
theorem Equation5155_implies_Equation2 (G : Type*) [Magma G] (h5155 : Equation5155 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5155 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5155 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5156 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5156 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (y ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5156_implies_Equation2 (G : Type*) [Magma G] (h5156 : Equation5156 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5156 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5156 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5158 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5158 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (z ◇ (x ◇ y)))))]

theorem Equation4512_5158_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5158 : Equation5158 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) = X1 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [h5158 X0 X2 X1]
    conv => enter [1]; rw [← h5158 X1 (X1 ◇ (X0 ◇ X2)) X2]
  have l1 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X2) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0))) = X1 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X2) ((X1 ◇ (X0 ◇ X2)) ◇ X0)]
    conv => enter [1]; rw [l0 X1 X0 X2]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)))) = X1 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4512 X0 X2 ((X1 ◇ (X0 ◇ X2)) ◇ X0)]
    conv => enter [1]; rw [l1 X1 X0 X2]
  have l3 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X0))))) = X1 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 (X0 ◇ X2) X0]
    conv => enter [1]; rw [l2 X1 X0 X2]
  have l4 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X0)))))) = X1 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X2 X0]
    conv => enter [1]; rw [l3 X1 X0 X2]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l4 (X0 ◇ X1) X1 X0]
    conv => enter [1]; rw [l4 X0 (X0 ◇ X1) X1]
  have l6 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l4 X0 X0 X1]
    conv => enter [1]; rw [← h5158 X1 (X0 ◇ (X0 ◇ (X1 ◇ X0))) X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ X0)) ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ X0) ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0)]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l5 X0 ((X1 ◇ X0) ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X0))) ◇ X0))]
    conv => enter [1]; rw [l8 X0 X1]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation2_implies_Equation5159 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5159 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (z ◇ (x ◇ z)))))]

@[equational_result]
theorem Equation5159_implies_Equation2 (G : Type*) [Magma G] (h5159 : Equation5159 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ (X1 ◇ X0)) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [h5159 X0 (X2 ◇ (X0 ◇ X2)) X2]
    conv => enter [1]; rw [← h5159 X2 X1 (X2 ◇ (X0 ◇ X2))]
  have l1 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X3 ◇ X0))) X0]
    conv => enter [1]; rw [← h5159 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5160 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5160 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (z ◇ (x ◇ w)))))]

@[equational_result]
theorem Equation5160_implies_Equation2 (G : Type*) [Magma G] (h5160 : Equation5160 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X3 : G, (X1 ◇ (X1 ◇ X0)) = X3 := by
    intro X1 X0 X3
    conv => enter [1, 2, 2]; rw [h5160 X0 X1 X3 X1]
    conv => enter [1]; rw [← h5160 X3 X1 X1 (X3 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5160 X0 X1 X1 X1]
    conv => enter [1]; rw [← h5160 X1 X1 X1 (X0 ◇ X1)]
  have l2 : ∀ X1 X3 : G, X1 = X3 := by
    intro X1 X3
    conv => enter [1]; rw [← l1 X1 (X1 ◇ X1)]
    conv => enter [1]; rw [l0 X1 X1 X3]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation5162 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5162 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (z ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5162_implies_Equation2 (G : Type*) [Magma G] (h5162 : Equation5162 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5162 X0 X0 X0]
    conv => enter [1]; rw [← h5162 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5163 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5163 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (z ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5163_implies_Equation2 (G : Type*) [Magma G] (h5163 : Equation5163 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5163 X0 X0 X0]
    conv => enter [1]; rw [← h5163 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5164 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5164 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (z ◇ (y ◇ w)))))]

@[equational_result]
theorem Equation5164_implies_Equation2 (G : Type*) [Magma G] (h5164 : Equation5164 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5164 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5164 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5166 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5166 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (z ◇ (z ◇ y)))))]

@[equational_result]
theorem Equation5166_implies_Equation2 (G : Type*) [Magma G] (h5166 : Equation5166 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5166 X0 X0 X0]
    conv => enter [1]; rw [← h5166 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5167 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5167 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (z ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5167_implies_Equation2 (G : Type*) [Magma G] (h5167 : Equation5167 G) : Equation2 G := by
  have l0 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [h5167 X0 X0 X0]
    conv => enter [1]; rw [← h5167 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5168 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5168 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (z ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5168_implies_Equation2 (G : Type*) [Magma G] (h5168 : Equation5168 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5168 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5168 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5170 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5170 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (z ◇ (w ◇ y)))))]

@[equational_result]
theorem Equation5170_implies_Equation2 (G : Type*) [Magma G] (h5170 : Equation5170 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5170 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5170 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5171 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5171 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (z ◇ (w ◇ z)))))]

@[equational_result]
theorem Equation5171_implies_Equation2 (G : Type*) [Magma G] (h5171 : Equation5171 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5171 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5171 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5172 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5172 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (z ◇ (w ◇ w)))))]

@[equational_result]
theorem Equation5172_implies_Equation2 (G : Type*) [Magma G] (h5172 : Equation5172 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5172 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5172 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5173 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5173 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5173_implies_Equation2 (G : Type*) [Magma G] (h5173 : Equation5173 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5173 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5173 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5175 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5175 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (w ◇ (x ◇ y)))))]

theorem Equation4512_5175_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5175 : Equation5175 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ X1) = (X2 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h5175 (X0 ◇ X1) X2 X3 X4]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X4 X0 X1 X2 X3 : G, (X4 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))))) = X3 := by
    intro X4 X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
    conv => enter [1]; rw [← h5175 X3 X4 (X0 ◇ X1) X2]
  have l2 : ∀ X1 X0 X2 X3 : G, ((X1 ◇ (X0 ◇ X2)) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) = X3 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2, 2]; rw [h5175 X0 X2 X3 X1]
    conv => enter [1]; rw [← h5175 X3 (X1 ◇ (X0 ◇ X2)) X2 X2]
  have l3 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ X2) ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0))) = X3 := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X2) ((X1 ◇ (X0 ◇ X2)) ◇ X0)]
    conv => enter [1]; rw [l2 X1 X0 X2 X3]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [l1 X0 X0 X0 X0 X1]
  have l5 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)))) = X3 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2]; rw [h4512 X0 X2 ((X1 ◇ (X0 ◇ X2)) ◇ X0)]
    conv => enter [1]; rw [l3 X1 X0 X2 X3]
  have l6 : ∀ X0 X2 X1 X3 : G, (X0 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0))) = X3 := by
    intro X0 X2 X1 X3
    conv => enter [1]; rw [← l4 X1 (X0 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)))]
    conv => enter [1]; rw [l5 X1 X0 X2 X3]
  have l7 : ∀ X2 X1 X0 X3 : G, (X2 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0)) = X3 := by
    intro X2 X1 X0 X3
    conv => enter [1]; rw [← l4 X0 (X2 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X0))]
    conv => enter [1]; rw [l6 X0 X2 X1 X3]
  have l8 : ∀ X1 X0 X2 X3 : G, ((X1 ◇ (X0 ◇ X2)) ◇ X0) = X3 := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [← l4 X2 ((X1 ◇ (X0 ◇ X2)) ◇ X0)]
    conv => enter [1]; rw [l7 X2 X1 X0 X3]
  have l9 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ X2) ◇ X0)) = X3 := by
    intro X1 X0 X2 X3
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X2) X0]
    conv => enter [1]; rw [l8 X1 X0 X2 X3]
  have l10 : ∀ X0 X2 X3 : G, ((X0 ◇ X2) ◇ X0) = X3 := by
    intro X0 X2 X3
    conv => enter [1]; rw [← l4 X0 ((X0 ◇ X2) ◇ X0)]
    conv => enter [1]; rw [l9 X0 X0 X2 X3]
  have l11 : ∀ X0 X2 X3 : G, (X0 ◇ (X2 ◇ X0)) = X3 := by
    intro X0 X2 X3
    conv => enter [1]; rw [h4512 X0 X2 X0]
    conv => enter [1]; rw [l10 X0 X2 X3]
  have l12 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = X3 := by
    intro X2 X0 X3
    conv => enter [1]; rw [← l4 X0 (X2 ◇ X0)]
    conv => enter [1]; rw [l11 X0 X2 X3]
  have l13 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l12 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X4 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5175 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l13 x y]

@[equational_result]
theorem Equation2_implies_Equation5176 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5176 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (w ◇ (x ◇ z)))))]

@[equational_result]
theorem Equation5176_implies_Equation2 (G : Type*) [Magma G] (h5176 : Equation5176 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X3 : G, (X1 ◇ (X1 ◇ X0)) = X3 := by
    intro X1 X0 X3
    conv => enter [1, 2, 2]; rw [h5176 X0 (X1 ◇ (X0 ◇ X3)) X3 X1]
    conv => enter [1]; rw [← h5176 X3 X1 (X1 ◇ (X0 ◇ X3)) (X1 ◇ (X0 ◇ X3))]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X4 ◇ X0))) X0]
    conv => enter [1]; rw [← h5176 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5177 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5177 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (w ◇ (x ◇ w)))))]

@[equational_result]
theorem Equation5177_implies_Equation2 (G : Type*) [Magma G] (h5177 : Equation5177 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5177 X0 X1 (X0 ◇ X2) X2]
    conv => enter [1]; rw [← h5177 X2 X1 X1 (X0 ◇ X2)]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X4 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5177 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5178 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5178 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (w ◇ (x ◇ u)))))]

@[equational_result]
theorem Equation5178_implies_Equation2 (G : Type*) [Magma G] (h5178 : Equation5178 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X3 : G, (X1 ◇ X0) = X3 := by
    intro X1 X0 X3
    conv => enter [1, 2]; rw [h5178 X0 X1 X1 X3 X1]
    conv => enter [1]; rw [← h5178 X3 X1 X1 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X4 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5178 X4 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5180 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5180 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (w ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5180_implies_Equation2 (G : Type*) [Magma G] (h5180 : Equation5180 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5180 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5180 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5181 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5181 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (w ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5181_implies_Equation2 (G : Type*) [Magma G] (h5181 : Equation5181 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5181 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5181 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5182 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5182 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (w ◇ (y ◇ w)))))]

@[equational_result]
theorem Equation5182_implies_Equation2 (G : Type*) [Magma G] (h5182 : Equation5182 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5182 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5182 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5183 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5183 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (w ◇ (y ◇ u)))))]

@[equational_result]
theorem Equation5183_implies_Equation2 (G : Type*) [Magma G] (h5183 : Equation5183 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5183 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5183 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5185 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5185 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (w ◇ (z ◇ y)))))]

@[equational_result]
theorem Equation5185_implies_Equation2 (G : Type*) [Magma G] (h5185 : Equation5185 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5185 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5185 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5186 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5186 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (w ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5186_implies_Equation2 (G : Type*) [Magma G] (h5186 : Equation5186 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5186 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5186 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5187 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5187 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (w ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5187_implies_Equation2 (G : Type*) [Magma G] (h5187 : Equation5187 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5187 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5187 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5188 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5188 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (w ◇ (z ◇ u)))))]

@[equational_result]
theorem Equation5188_implies_Equation2 (G : Type*) [Magma G] (h5188 : Equation5188 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5188 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5188 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5190 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5190 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (w ◇ (w ◇ y)))))]

@[equational_result]
theorem Equation5190_implies_Equation2 (G : Type*) [Magma G] (h5190 : Equation5190 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5190 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5190 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5191 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5191 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (w ◇ (w ◇ z)))))]

@[equational_result]
theorem Equation5191_implies_Equation2 (G : Type*) [Magma G] (h5191 : Equation5191 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5191 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5191 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5192 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5192 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (w ◇ (w ◇ w)))))]

@[equational_result]
theorem Equation5192_implies_Equation2 (G : Type*) [Magma G] (h5192 : Equation5192 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5192 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5192 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5193 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5193 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (w ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5193_implies_Equation2 (G : Type*) [Magma G] (h5193 : Equation5193 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5193 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5193 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5195 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5195 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (w ◇ (u ◇ y)))))]

@[equational_result]
theorem Equation5195_implies_Equation2 (G : Type*) [Magma G] (h5195 : Equation5195 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5195 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5195 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5196 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5196 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (w ◇ (u ◇ z)))))]

@[equational_result]
theorem Equation5196_implies_Equation2 (G : Type*) [Magma G] (h5196 : Equation5196 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5196 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5196 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5197 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5197 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (w ◇ (u ◇ w)))))]

@[equational_result]
theorem Equation5197_implies_Equation2 (G : Type*) [Magma G] (h5197 : Equation5197 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5197 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5197 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5198 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5198 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (w ◇ (u ◇ u)))))]

@[equational_result]
theorem Equation5198_implies_Equation2 (G : Type*) [Magma G] (h5198 : Equation5198 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5198 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5198 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5199 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5199 G := by
  intro x y z w u v
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (w ◇ (u ◇ v)))))]

@[equational_result]
theorem Equation5199_implies_Equation2 (G : Type*) [Magma G] (h5199 : Equation5199 G) : Equation2 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5199 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5199 X6 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5201 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5201 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (x ◇ (x ◇ y)))))]

theorem Equation4512_5201_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5201 : Equation5201 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h5201 X0 X1 X0]
    conv => enter [1]; rw [← h5201 X0 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) = ((X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l1 (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) X2]
    conv => enter [1, 2]; rw [← h5201 X0 X2 X1]
  have l3 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h5201 X0 (X1 ◇ X0) X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l6 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 X0 (X2 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l3 X1 X0 X2]
  have l7 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) = (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l2 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X0 ◇ (X0 ◇ X2))) X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l5 X0 (X0 ◇ X0) X1]
    conv => enter [1]; rw [l6 X1 X0 X1]
  have l9 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) = (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l7 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X2)) X0]
  have l10 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l8 X1 X0]
  have l11 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) = (X1 ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l9 X1 X0 X2]
    conv => enter [1, 2]; rw [l1 X0 (X0 ◇ (X0 ◇ X2))]
  have l12 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) = X0 := by
    intro X1 X0 X2
    conv => enter [1]; rw [l11 X1 X0 X2]
    conv => enter [1]; rw [l10 X1 X0]
  have l13 : ∀ X0 X2 : G, (X0 ◇ (X0 ◇ (X0 ◇ X2))) = X0 := by
    intro X0 X2
    conv => enter [1, 2, 2, 2]; rw [← l10 X0 X2]
    conv => enter [1]; rw [l12 X0 X0 X2]
  have l14 : ∀ X0 X2 : G, (X0 ◇ X2) = X0 := by
    intro X0 X2
    conv => enter [1]; rw [l5 X0 X2 X0]
    conv => enter [1]; rw [l13 X0 X2]
  have l15 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l14 X0 (X0 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X0))))]
    conv => enter [1]; rw [← h5201 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l15 x y]

@[equational_result]
theorem Equation2_implies_Equation5202 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5202 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (x ◇ (x ◇ z)))))]

theorem Equation4512_5202_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5202 : Equation5202 G) : Equation2 G := by
  have l0 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))))) = X2 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))]
    conv => enter [1]; rw [← h5202 X2 X3 (X0 ◇ X1)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5202 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h5202 X0 X1 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [← l1 X0 (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))))]
    conv => enter [1]; rw [l0 X0 X0 X1 X2]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))) = X2 := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l1 X0 (X1 ◇ (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))))]
    conv => enter [1]; rw [l2 X0 X1 X2]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1)))) = X2 := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l1 X1 (X2 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X1))))]
    conv => enter [1]; rw [l3 X1 X2 X0]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ X1))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [← l1 X2 (X0 ◇ X1)]
    conv => enter [1]; rw [l4 X2 X0 X1]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← l1 X2 (X0 ◇ X1)]
    conv => enter [1]; rw [l5 X2 X0 X1]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l1 X2 (X0 ◇ X1)]
    conv => enter [1]; rw [l6 X2 X0 X1]
  have l8 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l7 X0 (X0 ◇ (X3 ◇ (X3 ◇ (X3 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5202 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l8 x y]

@[equational_result]
theorem Equation2_implies_Equation5203 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5203 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (x ◇ (x ◇ w)))))]

@[equational_result]
theorem Equation5203_implies_Equation2 (G : Type*) [Magma G] (h5203 : Equation5203 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2]; rw [h5203 X0 X3 X3 X1]
    conv => enter [1]; rw [← h5203 X3 X1 X2 (X0 ◇ (X0 ◇ (X0 ◇ X1)))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5203 X0 X1 X0 X1]
    conv => enter [1]; rw [← h5203 X0 X1 X1 (X0 ◇ X1)]
  have l2 : ∀ X2 X3 X0 : G, (X2 ◇ (X3 ◇ X0)) = X3 := by
    intro X2 X3 X0
    conv => enter [1, 2]; rw [← l1 X2 (X3 ◇ X0)]
    conv => enter [1]; rw [l0 X2 X2 X3 X0]
  have l3 : ∀ X3 X0 : G, (X3 ◇ X0) = X3 := by
    intro X3 X0
    conv => enter [1, 2]; rw [← l1 X3 X0]
    conv => enter [1]; rw [l2 X3 X3 X0]
  have l4 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l3 X0 (X0 ◇ (X2 ◇ (X2 ◇ (X2 ◇ X0))))]
    conv => enter [1]; rw [← h5203 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation2_implies_Equation5205 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5205 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (x ◇ (y ◇ y)))))]

theorem Equation4512_5205_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5205 : Equation5205 G) : Equation2 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h5205 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h5205 (X0 ◇ X0) X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h5205 (X0 ◇ X0) X0 (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← l1 (X0 ◇ X0)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h5205 X0 X0 X1]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [l3 X0 (X0 ◇ X0)]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l4 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l4 (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [← h5205 X0 X1 (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l4 X1]
    conv => enter [1]; rw [l6 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l5 X0 X1]
    conv => enter [1]; rw [l7 X1 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l8 (X0 ◇ (X1 ◇ X1)) X0]
    conv => enter [1]; rw [← h5205 X0 X1 (X0 ◇ (X1 ◇ X1))]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l9 X1 X0]
    conv => enter [1]; rw [l8 X0 X1]
  have l11 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l9 X0 X0]
    conv => enter [1]; rw [l10 X0 X1]
  intro x y
  conv => enter [1]; rw [l11 x y]

@[equational_result]
theorem Equation2_implies_Equation5206 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5206 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (x ◇ (y ◇ z)))))]

theorem Equation4512_5206_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5206 : Equation5206 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ (X3 ◇ (X3 ◇ X0)))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h5206 X0 X1 X2]
    conv => enter [1]; rw [← h5206 X3 X1 (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2))))]
  have l1 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) X3]
    conv => enter [1, 1]; rw [← h5206 X0 X1 X2]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l1 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X0 ◇ (X1 ◇ X2))) X3]
  have l3 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ (X3 ◇ X0))))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2]; rw [h4512 X2 (X0 ◇ (X0 ◇ (X1 ◇ X2))) (X3 ◇ (X3 ◇ X0))]
    conv => enter [1]; rw [l0 X1 X2 X0 X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X2)) X3]
  have l5 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X3 ◇ X0)))))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 (X0 ◇ (X1 ◇ X2)) (X3 ◇ (X3 ◇ X0))]
    conv => enter [1]; rw [l3 X1 X2 X0 X3]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l4 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l7 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X3 ◇ X0))))))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 (X1 ◇ X2) (X3 ◇ (X3 ◇ X0))]
    conv => enter [1]; rw [l5 X1 X2 X0 X3]
  have l8 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l6 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l9 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ X0)))))))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X1 X2 (X3 ◇ (X3 ◇ X0))]
    conv => enter [1]; rw [l7 X1 X2 X0 X3]
  have l10 : ∀ X0 X3 : G, (X0 ◇ (X3 ◇ (X3 ◇ X0))) = X3 := by
    intro X0 X3
    conv => enter [1]; rw [l8 X0 (X3 ◇ (X3 ◇ X0)) X0 X0]
    conv => enter [1]; rw [l9 X0 X0 X0 X3]
  have l11 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [← l10 X0 X0]
    conv => enter [1]; rw [← h5206 X0 X0 X0]
  have l12 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X0 ◇ X1)) X2]
    conv => enter [1, 1]; rw [l10 X1 X0]
  have l13 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l12 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l14 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l13 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 X2]
  have l15 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l11 X0]
    conv => enter [1]; rw [l10 X0 X0]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l15 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 (X1 ◇ (X1 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [← h5206 X1 X0 X0]
  have l18 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l14 X1 X0 X0]
    conv => enter [1]; rw [l17 X0 X1]
  have l19 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l18 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l10 X0 X1]
  intro x y
  conv => enter [1]; rw [l19 x y]

@[equational_result]
theorem Equation2_implies_Equation5207 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5207 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (x ◇ (y ◇ w)))))]

theorem Equation4512_5207_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5207 : Equation5207 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2]; rw [h5207 X0 X3 X1 X1]
    conv => enter [1]; rw [← h5207 X3 X1 X2 (X0 ◇ (X0 ◇ (X3 ◇ X1)))]
  have l1 : ∀ X0 X1 X2 X4 X3 : G, (X0 ◇ X1) = (X2 ◇ (X4 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X3)))))) := by
    intro X0 X1 X2 X4 X3
    conv => enter [1]; rw [h5207 (X0 ◇ X1) X2 X4 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X2 ◇ X3))]
  have l2 : ∀ X0 X1 X2 X4 X3 : G, (X0 ◇ X1) = (X2 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3))))))) := by
    intro X0 X1 X2 X4 X3
    conv => enter [1]; rw [l1 X0 X1 X2 X4 X3]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X3)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X0 (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))]
  have l4 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l3 X0 (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5207 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation2_implies_Equation5209 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5209 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (x ◇ (z ◇ y)))))]

theorem Equation4512_5209_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5209 : Equation5209 G) : Equation2 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h5209 X0 X0 X0]
    conv => enter [1]; rw [← h5209 X0 (X0 ◇ X0) X0]
  have l1 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h4512 X0 X0 X0]
    conv => enter [1]; rw [l0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h5209 X0 X0 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [h5209 (X0 ◇ X1) X1 X0]
    conv => enter [1, 2, 2]; rw [l1 (X0 ◇ X1)]
  have l4 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h5209 X1 (X0 ◇ X0) X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X0))))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 (X0 ◇ (X1 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [l4 X0 X1]
  have l8 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l3 X0 X0]
    conv => enter [1]; rw [l2 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 (X1 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l7 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l8 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [h5209 (X0 ◇ X1) X1 X0]
    conv => enter [1, 2, 2, 2]; rw [l8 (X0 ◇ X1)]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l8 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l13 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l14 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l13 X0 X1]
    conv => enter [1, 2]; rw [← l10 X0 (X1 ◇ (X0 ◇ X1))]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l14 X0 X1]
    conv => enter [1, 2]; rw [← l12 X0 X1]
  have l16 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l9 X1 X0]
    conv => enter [1]; rw [← h5209 X1 (X0 ◇ X1) X0]
  have l17 : ∀ X0 X1 X2 : G, ((X0 ◇ (X0 ◇ X1)) ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2, 2]; rw [← l9 X1 X0]
    conv => enter [1]; rw [← h5209 X2 (X0 ◇ (X0 ◇ X1)) X1]
  have l18 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ X1) ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) (X1 ◇ (X2 ◇ (X2 ◇ X0)))]
    conv => enter [1]; rw [l17 X0 X1 X2]
  have l19 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l16 X0 X1]
  have l20 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 (X1 ◇ (X2 ◇ (X2 ◇ X0)))]
    conv => enter [1]; rw [l18 X0 X1 X2]
  have l21 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l12 X1 X0]
    conv => enter [1]; rw [l19 X0 X1]
  have l22 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [l10 X0 (X1 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0))))]
    conv => enter [1]; rw [l20 X0 X1 X2]
  have l23 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X0)))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [l10 X1 (X2 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l22 X0 X1 X2]
  have l24 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ X0))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2]; rw [l10 X2 X0]
    conv => enter [1]; rw [l23 X0 X1 X2]
  have l25 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l21 X2 (X0 ◇ X1)]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l26 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5209 X0 X2 X1]
    conv => enter [1]; rw [l21 (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) X2]
  have l27 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X0)) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ (X0 ◇ (X1 ◇ X2))) X0]
    conv => enter [1]; rw [l26 X1 X0 X2]
  have l28 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l25 X0 X1 X0]
    conv => enter [1]; rw [l24 X0 X0 X1]
  have l29 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4512 X0 (X0 ◇ (X1 ◇ X2)) X0]
    conv => enter [1]; rw [l27 X1 X0 X2]
  have l30 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0)) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l28 X1 (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X0))]
    conv => enter [1]; rw [l29 X1 X0 X2]
  have l31 : ∀ X0 X1 X2 : G, ((X0 ◇ (X1 ◇ X2)) ◇ X0) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [l15 (X0 ◇ (X1 ◇ X2)) X0]
    conv => enter [1]; rw [l30 X0 X1 X2]
  have l32 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X2) ◇ X0)) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) X0]
    conv => enter [1]; rw [l31 X0 X1 X2]
  have l33 : ∀ X1 X2 X0 : G, ((X1 ◇ X2) ◇ X0) = X2 := by
    intro X1 X2 X0
    conv => enter [1]; rw [l15 (X1 ◇ X2) X0]
    conv => enter [1]; rw [l32 X0 X1 X2]
  have l34 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l28 (X0 ◇ X2) X0]
    conv => enter [1]; rw [l33 X0 X2 X0]
  intro x y
  conv => enter [1]; rw [l34 x y]

@[equational_result]
theorem Equation2_implies_Equation5210 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5210 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (x ◇ (z ◇ z)))))]

theorem Equation4512_5210_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5210 : Equation5210 G) : Equation2 G := by
  have l0 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))))) = X2 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X1))))]
    conv => enter [1]; rw [← h5210 X2 X3 (X0 ◇ X1)]
  have l1 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X3)))))) = X0 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X0 ◇ (X0 ◇ (X3 ◇ X3))))]
    conv => enter [1]; rw [← h5210 X0 (X1 ◇ X2) X3]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5210 X0 X1 X1]
    conv => enter [1]; rw [l1 X1 X1 X1 X0]
  have l3 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))))) = X2 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X3 X0 X1 X2]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [← l2 X0 (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))]
    conv => enter [1]; rw [l3 X0 X0 X1 X2]
  have l5 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))) = X2 := by
    intro X1 X2 X0
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))))]
    conv => enter [1]; rw [l4 X0 X1 X2]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1]; rw [← l2 X1 (X2 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))))]
    conv => enter [1]; rw [l5 X1 X2 X0]
  have l7 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← l2 X2 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l6 X2 X0 X1]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X2 (X0 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l7 X2 X0 X1]
  have l9 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X1)) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l2 X0 (X1 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l8 X0 X1 X2]
  have l10 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = X2 := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l9 X1 X0 X2]
  have l11 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l10 X0 (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5210 X3 X0 X0]
  intro x y
  conv => enter [1]; rw [l11 x y]

@[equational_result]
theorem Equation2_implies_Equation5211 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5211 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (x ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5211_implies_Equation2 (G : Type*) [Magma G] (h5211 : Equation5211 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ X0)) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2]; rw [h5211 X0 X2 X2 X1]
    conv => enter [1]; rw [← h5211 X2 X1 X0 (X0 ◇ (X2 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5211 X0 X0 X0 X1]
    conv => enter [1]; rw [← h5211 X0 X1 X0 (X0 ◇ X1)]
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
theorem Equation2_implies_Equation5213 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5213 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (x ◇ (w ◇ y)))))]

theorem Equation4512_5213_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5213 : Equation5213 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ (X3 ◇ (X2 ◇ X0))) = X2 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2, 2]; rw [h5213 X0 X2 X0 X1]
    conv => enter [1]; rw [← h5213 X2 (X0 ◇ (X0 ◇ (X1 ◇ X2))) X3 X0]
  have l1 : ∀ X0 X1 X2 X3 : G, ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ X0)) = X2 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h5213 X0 X2 X2 X1]
    conv => enter [1]; rw [← h5213 X2 (X0 ◇ (X1 ◇ X2)) X3 X0]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ X0))) = X2 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X1 ◇ X2) (X3 ◇ X0)]
    conv => enter [1]; rw [l1 X0 X1 X2 X3]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X2 ◇ X0)))) = X2 := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ X2)) (X3 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
  have l4 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X0)))) = X2 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X1 X2 (X3 ◇ X0)]
    conv => enter [1]; rw [l2 X0 X1 X2 X3]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X2 ◇ X0))))) = X2 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ X2) (X3 ◇ (X2 ◇ X0))]
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
  have l6 : ∀ X0 X3 X2 : G, (X0 ◇ X3) = X2 := by
    intro X0 X3 X2
    conv => enter [1, 2]; rw [← l4 X0 (X0 ◇ X2) X3 X2]
    conv => enter [1]; rw [l5 X0 X0 X2 X3]
  have l7 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l6 X0 (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5213 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l7 x y]

@[equational_result]
theorem Equation2_implies_Equation5214 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5214 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (x ◇ (w ◇ z)))))]

theorem Equation4512_5214_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5214 : Equation5214 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 X3 : G, (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X0)) = X3 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2, 2]; rw [h5214 X0 X3 X3 X2]
    conv => enter [1]; rw [← h5214 X3 X1 (X0 ◇ (X2 ◇ X3)) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5214 X0 (X1 ◇ X0) X0 X1]
    conv => enter [1]; rw [← h5214 X0 X1 (X1 ◇ X0) X0]
  have l2 : ∀ X0 X2 X3 : G, ((X0 ◇ (X2 ◇ X3)) ◇ X0) = X3 := by
    intro X0 X2 X3
    conv => enter [1]; rw [← l1 X0 ((X0 ◇ (X2 ◇ X3)) ◇ X0)]
    conv => enter [1]; rw [l0 X0 X0 X2 X3]
  have l3 : ∀ X0 X2 X3 : G, (X0 ◇ ((X2 ◇ X3) ◇ X0)) = X3 := by
    intro X0 X2 X3
    conv => enter [1]; rw [h4512 X0 (X2 ◇ X3) X0]
    conv => enter [1]; rw [l2 X0 X2 X3]
  have l4 : ∀ X2 X3 X0 : G, ((X2 ◇ X3) ◇ X0) = X3 := by
    intro X2 X3 X0
    conv => enter [1]; rw [← l1 X0 ((X2 ◇ X3) ◇ X0)]
    conv => enter [1]; rw [l3 X0 X2 X3]
  have l5 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l1 (X0 ◇ X3) X0]
    conv => enter [1]; rw [l4 X0 X3 X0]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation2_implies_Equation5215 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5215 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (x ◇ (w ◇ w)))))]

theorem Equation4512_5215_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5215 : Equation5215 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2]; rw [h5215 X0 X3 (X0 ◇ (X0 ◇ (X1 ◇ X1))) X1]
    conv => enter [1]; rw [← h5215 X3 X1 X2 (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
  have l1 : ∀ X0 X1 X3 X4 X2 : G, (X0 ◇ X1) = (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ (X2 ◇ X2)))))) := by
    intro X0 X1 X3 X4 X2
    conv => enter [1]; rw [h5215 (X0 ◇ X1) X3 X4 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 ((X0 ◇ X1) ◇ (X2 ◇ X2))]
  have l2 : ∀ X0 X1 X3 X4 X2 : G, (X0 ◇ X1) = (X3 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2))))))) := by
    intro X0 X1 X3 X4 X2
    conv => enter [1]; rw [l1 X0 X1 X3 X4 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ X2)]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 X0 (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0))))]
  have l4 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l3 X0 (X0 ◇ (X2 ◇ (X2 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [← h5215 X2 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation2_implies_Equation5216 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5216 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (x ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5216_implies_Equation2 (G : Type*) [Magma G] (h5216 : Equation5216 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ X0)) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2]; rw [h5216 X0 X3 X3 X1 X1]
    conv => enter [1]; rw [← h5216 X3 X1 X2 X0 (X0 ◇ (X1 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h5216 X0 X1 X0 X1 X1]
    conv => enter [1]; rw [← h5216 X0 X1 X1 X0 (X1 ◇ X1)]
  have l2 : ∀ X2 X0 X3 : G, (X2 ◇ X0) = X3 := by
    intro X2 X0 X3
    conv => enter [1, 2]; rw [← l1 X2 X0]
    conv => enter [1]; rw [l0 X2 X2 X0 X3]
  have l3 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l2 X0 (X0 ◇ (X3 ◇ (X3 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5216 X3 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation5218 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5218 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (y ◇ (x ◇ y)))))]

theorem Equation4512_5218_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5218 : Equation5218 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h5218 X0 X0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← h5218 X0 (X0 ◇ (X0 ◇ X0)) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) (X1 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [← h5218 X0 X0 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l3 X0]
    conv => enter [1]; rw [← h5218 X0 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l5 X0 X0]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l3 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))) = ((X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))) ◇ X0) := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l7 (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))) X2]
    conv => enter [1, 2]; rw [← h5218 X0 X2 X1]
  have l9 : ∀ X1 X0 X2 : G, ((X1 ◇ X0) ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))) = X0 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2]; rw [← l7 X0 X1]
    conv => enter [1]; rw [← h5218 X0 (X1 ◇ X0) X2]
  have l10 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X1 ◇ X0) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l11 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X1 ◇ (X0 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l10 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X1 X0 X2]
  have l12 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))))) = X0 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 X0 (X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0)))]
    conv => enter [1]; rw [l9 X1 X0 X2]
  have l13 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))) = (X1 ◇ ((X0 ◇ (X2 ◇ (X0 ◇ X2))) ◇ X0)) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l8 X1 X0 X2]
    conv => enter [1]; rw [← h4512 X1 (X0 ◇ (X2 ◇ (X0 ◇ X2))) X0]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l11 X0 ((X1 ◇ X0) ◇ X0) X1]
    conv => enter [1]; rw [l12 X1 X0 X1]
  have l15 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))) = (X1 ◇ (X0 ◇ ((X2 ◇ (X0 ◇ X2)) ◇ X0))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l13 X1 X0 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X2 ◇ (X0 ◇ X2)) X0]
  have l16 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l7 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l14 X1 X0]
  have l17 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ (X2 ◇ (X0 ◇ X2)))) := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [← l7 X0 (X2 ◇ (X0 ◇ X2))]
    conv => enter [1]; rw [← l15 X1 X0 X2]
  have l18 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X0 ◇ (X2 ◇ (X0 ◇ X2))) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l17 X1 X0 X2]
    conv => enter [1]; rw [l16 X1 (X0 ◇ (X2 ◇ (X0 ◇ X2)))]
  have l19 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = (X0 ◇ X2) := by
    intro X1 X0 X2
    conv => enter [1]; rw [l18 X1 X0 X2]
    conv => enter [1]; rw [← l11 X0 X2 X2]
  have l20 : ∀ X0 X2 : G, (X0 ◇ X2) = X0 := by
    intro X0 X2
    conv => enter [1]; rw [← l19 X0 X0 X2]
    conv => enter [1]; rw [l16 X0 X0]
  have l21 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l20 X0 (X0 ◇ (X2 ◇ (X0 ◇ (X2 ◇ X0))))]
    conv => enter [1]; rw [← h5218 X2 X0 X0]
  intro x y
  conv => enter [1]; rw [l21 x y]

@[equational_result]
theorem Equation2_implies_Equation5219 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5219 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (y ◇ (x ◇ z)))))]

theorem Equation4512_5219_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5219 : Equation5219 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h5219 X0 X0 X1]
    conv => enter [1]; rw [← h5219 X0 X1 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4512 X0 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [← h5219 X0 X0 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l2 X1 X0]
    conv => enter [1]; rw [← h5219 X0 X1 (X0 ◇ (X1 ◇ X0))]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ X0) (X0 ◇ X0)]
    conv => enter [1]; rw [l4 X1 X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4512 X1 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l5 X1 X0]
  have l7 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l3 X0]
    conv => enter [1]; rw [l6 X1 X0]
  have l8 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l3 X0]
    conv => enter [1]; rw [l7 X1 X0]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l10 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h5219 X0 (X0 ◇ X1) X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l3 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l12 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l11 X0 X1]
    conv => enter [1]; rw [l8 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 (X1 ◇ (X0 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l10 X0 X1]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l12 X0 (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))]
    conv => enter [1]; rw [l13 X0 X1]
  have l15 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l9 X1 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l14 X1 X0]
  have l16 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [← l12 X1 (X0 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l15 X1 X0]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l12 X0 X1]
    conv => enter [1]; rw [l16 X0 X1]
  have l18 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l17 X0 (X1 ◇ (X1 ◇ (X0 ◇ X1)))]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l18 x y]

@[equational_result]
theorem Equation2_implies_Equation5220 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5220 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (y ◇ (x ◇ w)))))]

@[equational_result]
theorem Equation5220_implies_Equation2 (G : Type*) [Magma G] (h5220 : Equation5220 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h5220 X0 X1 X1 X0]
    conv => enter [1]; rw [← h5220 X1 X0 X1 (X0 ◇ X0)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l0 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5222 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5222 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (y ◇ (y ◇ y)))))]

theorem Equation4512_5222_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5222 : Equation5222 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h5222 (X0 ◇ (X0 ◇ X0)) X0 (X0 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [← h5222 X0 (X0 ◇ (X0 ◇ X0)) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0))))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X0) (X1 ◇ (X0 ◇ (X0 ◇ X0)))]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h5222 X0 X1 (X1 ◇ X1)]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation2_implies_Equation5223 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5223 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (y ◇ (y ◇ z)))))]

theorem Equation4512_5223_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5223 : Equation5223 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ (X3 ◇ (X1 ◇ X0)))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h5223 X0 X1 X2]
    conv => enter [1]; rw [← h5223 X3 X1 (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2))))]
  have l1 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X1 X2 X0 X3
    conv => enter [1]; rw [h4512 X1 (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) X3]
    conv => enter [1, 1]; rw [← h5223 X0 X1 X2]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l1 X1 X2 X0 X3]
    conv => enter [1, 2]; rw [← h4512 X2 (X0 ◇ (X1 ◇ (X1 ◇ X2))) X3]
  have l3 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ (X3 ◇ (X1 ◇ X0))))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2]; rw [h4512 X2 (X0 ◇ (X1 ◇ (X1 ◇ X2))) (X3 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l0 X1 X2 X0 X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X2)) X3]
  have l5 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ (X3 ◇ (X1 ◇ X0)))))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 (X1 ◇ (X1 ◇ X2)) (X3 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l3 X1 X2 X0 X3]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l4 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X1 ◇ X2) X3]
  have l7 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X2) ◇ (X3 ◇ (X1 ◇ X0))))))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 (X1 ◇ X2) (X3 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l5 X1 X2 X0 X3]
  have l8 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l6 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l9 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X1 ◇ X0)))))))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X1 X2 (X3 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l7 X1 X2 X0 X3]
  have l10 : ∀ X0 X3 X1 : G, (X0 ◇ (X3 ◇ (X1 ◇ X0))) = X3 := by
    intro X0 X3 X1
    conv => enter [1]; rw [l8 X0 (X3 ◇ (X1 ◇ X0)) X1 X0]
    conv => enter [1]; rw [l9 X1 X0 X0 X3]
  have l11 : ∀ X0 X1 X2 : G, (X0 ◇ ((X1 ◇ X0) ◇ (X2 ◇ X0))) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [← l10 X0 X0 X1]
    conv => enter [1]; rw [← h5223 X2 X0 (X1 ◇ X0)]
  have l12 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [← l10 X0 (X1 ◇ X0) X2]
    conv => enter [1]; rw [l11 X0 X1 X2]
  have l13 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l12 X0 (X2 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [l10 X0 X2 X0]
  intro x y
  conv => enter [1]; rw [l13 x y]

@[equational_result]
theorem Equation2_implies_Equation5224 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5224 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (y ◇ (y ◇ w)))))]

theorem Equation4512_5224_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5224 : Equation5224 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2]; rw [h5224 X0 X1 X1 X1]
    conv => enter [1]; rw [← h5224 X3 X1 X2 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l1 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X4)))))) = X0 := by
    intro X1 X2 X3 X0 X4
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ ((X1 ◇ X2) ◇ X4))))]
    conv => enter [1]; rw [← h5224 X0 (X1 ◇ X2) X3 X4]
  have l2 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X4))))))) = X0 := by
    intro X1 X2 X3 X0 X4
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X1 X2 ((X1 ◇ X2) ◇ X4)]
    conv => enter [1]; rw [l1 X1 X2 X3 X0 X4]
  have l3 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 X0 X0 (X3 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))]
    conv => enter [1]; rw [l2 X0 X0 X0 X3 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation5226 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5226 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (y ◇ (z ◇ y)))))]

theorem Equation4512_5226_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5226 : Equation5226 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h5226 (X0 ◇ X1) X1 X0]
    conv => enter [1]; rw [← h5226 X0 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X0 ◇ X1))]
    conv => enter [1]; rw [l1 X2 (X0 ◇ X1)]
  have l3 : ∀ X1 X0 X2 : G, ((X1 ◇ (X0 ◇ X1)) ◇ (X0 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2, 2, 2, 2]; rw [← l1 X0 X1]
    conv => enter [1]; rw [← h5226 X2 (X1 ◇ (X0 ◇ X1)) X0]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X2)))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l1 (X0 ◇ X1) X2]
    conv => enter [1]; rw [← h4512 X0 X1 (X2 ◇ ((X0 ◇ X1) ◇ X2))]
  have l5 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X2))))) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l4 X0 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l6 : ∀ X1 X0 X2 : G, (X1 ◇ ((X0 ◇ X1) ◇ (X0 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0))))) = X2 := by
    intro X1 X0 X2
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X1) (X0 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)))]
    conv => enter [1]; rw [l3 X1 X0 X2]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1 X0]
    conv => enter [1]; rw [l2 X0 X1 X0]
  have l8 : ∀ X1 X0 X2 : G, (X1 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)))))) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 (X0 ◇ (X2 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)))]
    conv => enter [1]; rw [l6 X1 X0 X2]
  have l9 : ∀ X1 X2 : G, X1 = X2 := by
    intro X1 X2
    conv => enter [1]; rw [← l7 X1 (X1 ◇ (X1 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X1)))))]
    conv => enter [1]; rw [l8 X1 X1 X2]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation2_implies_Equation5227 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5227 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5227_implies_Equation2 (G : Type*) [Magma G] (h5227 : Equation5227 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h5227 X0 (X1 ◇ X1) X1]
    conv => enter [1]; rw [← h5227 X1 X0 (X1 ◇ X1)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l0 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5228 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5228 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5228_implies_Equation2 (G : Type*) [Magma G] (h5228 : Equation5228 G) : Equation2 G := by
  have l0 : ∀ X0 X2 : G, (X0 ◇ X0) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [h5228 X0 X0 X2 X0]
    conv => enter [1]; rw [← h5228 X2 X0 X0 (X2 ◇ X0)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l0 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5230 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5230 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (y ◇ (w ◇ y)))))]

theorem Equation4512_5230_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5230 : Equation5230 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 X4 X3 : G, (X0 ◇ X1) = (X2 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X2)))))) := by
    intro X0 X1 X2 X4 X3
    conv => enter [1]; rw [h5230 (X0 ◇ X1) X2 X4 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X1 (X2 ◇ (X3 ◇ X2))]
  have l1 : ∀ X1 X2 X3 X0 : G, ((X1 ◇ (X2 ◇ X1)) ◇ (X3 ◇ X0)) = X1 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2]; rw [h5230 X0 X1 (X1 ◇ (X2 ◇ X1)) X2]
    conv => enter [1]; rw [← h5230 X1 (X1 ◇ (X2 ◇ X1)) X3 X0]
  have l2 : ∀ X3 X0 X1 X2 X4 : G, (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X3)))))) = X2 := by
    intro X3 X0 X1 X2 X4
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X4 ◇ X3)))]
    conv => enter [1]; rw [← h5230 X2 X3 (X0 ◇ X1) X4]
  have l3 : ∀ X1 X2 X3 X0 : G, (X1 ◇ ((X2 ◇ X1) ◇ (X3 ◇ X0))) = X1 := by
    intro X1 X2 X3 X0
    conv => enter [1]; rw [h4512 X1 (X2 ◇ X1) (X3 ◇ X0)]
    conv => enter [1]; rw [l1 X1 X2 X3 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0 X0 X0]
    conv => enter [1]; rw [l2 X0 X0 X0 X1 X0]
  have l5 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X1 ◇ (X3 ◇ X0)))) = X1 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2]; rw [h4512 X2 X1 (X3 ◇ X0)]
    conv => enter [1]; rw [l3 X1 X2 X3 X0]
  have l6 : ∀ X2 X1 X3 X0 : G, (X2 ◇ (X1 ◇ (X3 ◇ X0))) = X1 := by
    intro X2 X1 X3 X0
    conv => enter [1]; rw [← l4 X1 (X2 ◇ (X1 ◇ (X3 ◇ X0)))]
    conv => enter [1]; rw [l5 X1 X2 X3 X0]
  have l7 : ∀ X1 X3 X0 : G, (X1 ◇ (X3 ◇ X0)) = X1 := by
    intro X1 X3 X0
    conv => enter [1, 2]; rw [← l4 X1 (X3 ◇ X0)]
    conv => enter [1]; rw [l6 X1 X1 X3 X0]
  have l8 : ∀ X3 X0 X1 : G, (X3 ◇ X0) = X1 := by
    intro X3 X0 X1
    conv => enter [1]; rw [← l4 X1 (X3 ◇ X0)]
    conv => enter [1]; rw [l7 X1 X3 X0]
  have l9 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l8 X0 (X0 ◇ (X3 ◇ (X0 ◇ (X0 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5230 X3 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation2_implies_Equation5231 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5231 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (y ◇ (w ◇ z)))))]

@[equational_result]
theorem Equation5231_implies_Equation2 (G : Type*) [Magma G] (h5231 : Equation5231 G) : Equation2 G := by
  have l0 : ∀ X0 X2 : G, (X0 ◇ X0) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [h5231 X0 (X0 ◇ X2) X2 X0]
    conv => enter [1]; rw [← h5231 X2 X0 (X0 ◇ X2) (X0 ◇ X2)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l0 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5232 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5232 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (y ◇ (w ◇ w)))))]

theorem Equation4512_5232_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5232 : Equation5232 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ X0))) = X3 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2]; rw [h5232 X0 X1 (X0 ◇ (X1 ◇ (X1 ◇ X1))) X1]
    conv => enter [1]; rw [← h5232 X3 X1 X2 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l1 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X4 ◇ X4)))))) = X0 := by
    intro X1 X2 X3 X0 X4
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X0 ◇ ((X1 ◇ X2) ◇ (X4 ◇ X4))))]
    conv => enter [1]; rw [← h5232 X0 (X1 ◇ X2) X3 X4]
  have l2 : ∀ X1 X2 X3 X0 X4 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X4 ◇ X4))))))) = X0 := by
    intro X1 X2 X3 X0 X4
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X1 X2 (X4 ◇ X4)]
    conv => enter [1]; rw [l1 X1 X2 X3 X0 X4]
  have l3 : ∀ X0 X3 : G, X0 = X3 := by
    intro X0 X3
    conv => enter [1]; rw [← l0 X0 X0 X0 (X3 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))]
    conv => enter [1]; rw [l2 X0 X0 X0 X3 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation5233 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5233 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (y ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5233_implies_Equation2 (G : Type*) [Magma G] (h5233 : Equation5233 G) : Equation2 G := by
  have l0 : ∀ X0 X2 : G, (X0 ◇ X0) = X2 := by
    intro X0 X2
    conv => enter [1, 2]; rw [h5233 X0 X0 X2 X0 X0]
    conv => enter [1]; rw [← h5233 X2 X0 X0 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X2 : G, X0 = X2 := by
    intro X0 X2
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l0 X0 X2]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5235 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5235 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (z ◇ (x ◇ y)))))]

end Semigroup5
