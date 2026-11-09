import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup5

@[equational_result]
theorem Equation2_implies_Equation5458 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5458 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (y ◇ (x ◇ y)))))]

theorem Equation4512_5458_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5458 : Equation5458 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h5458 X0 X1 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h5458 X1 (X0 ◇ X1) X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [← l1 (X1 ◇ (X2 ◇ X1)) X0]
    conv => enter [1]; rw [← h5458 X2 X1 (X1 ◇ (X2 ◇ X1)) X0]
  have l3 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l2 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X4 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5458 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation2_implies_Equation5459 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5459 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (y ◇ (x ◇ z)))))]

theorem Equation4512_5459_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5459 : Equation5459 G) : Equation2 G := by
  have l0 : ∀ X2 X4 X0 X1 X3 : G, (X2 ◇ (X4 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X4)))))) = X3 := by
    intro X2 X4 X0 X1 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ X4))]
    conv => enter [1]; rw [← h5459 X3 X2 X4 (X0 ◇ X1)]
  have l1 : ∀ X1 X2 X0 X3 : G, (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X0)) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2]; rw [h5459 X0 X2 X1 X3]
    conv => enter [1]; rw [← h5459 X3 X1 (X2 ◇ (X0 ◇ X1)) X2]
  have l2 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3)))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X4 ◇ ((X1 ◇ X2) ◇ (X0 ◇ X3))))]
    conv => enter [1]; rw [← h5459 X0 (X1 ◇ X2) X3 X4]
  have l3 : ∀ X1 X2 X3 X4 X0 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3))))))) = X0 := by
    intro X1 X2 X3 X4 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X1 X2 (X0 ◇ X3)]
    conv => enter [1]; rw [l2 X1 X2 X3 X4 X0]
  have l4 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X0))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2]; rw [h4512 X2 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l1 X1 X2 X0 X3]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X1 X1 X1 X1 X0]
    conv => enter [1]; rw [l3 X1 X1 X1 X1 X0]
  have l6 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l4 X1 X2 X0 X3]
  have l7 : ∀ X2 X0 X1 X3 : G, (X2 ◇ (X0 ◇ (X1 ◇ X0))) = X3 := by
    intro X2 X0 X1 X3
    conv => enter [1]; rw [← l5 X1 (X2 ◇ (X0 ◇ (X1 ◇ X0)))]
    conv => enter [1]; rw [l6 X1 X2 X0 X3]
  have l8 : ∀ X0 X1 X3 : G, (X0 ◇ (X1 ◇ X0)) = X3 := by
    intro X0 X1 X3
    conv => enter [1, 2]; rw [← l5 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l7 X0 X0 X1 X3]
  have l9 : ∀ X1 X0 X3 : G, (X1 ◇ X0) = X3 := by
    intro X1 X0 X3
    conv => enter [1]; rw [← l5 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l8 X0 X1 X3]
  have l10 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l9 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X4 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5459 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation2_implies_Equation5460 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5460 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (y ◇ (x ◇ w)))))]

@[equational_result]
theorem Equation5460_implies_Equation2 (G : Type*) [Magma G] (h5460 : Equation5460 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5460 X0 X2 (X0 ◇ X1) X1]
    conv => enter [1]; rw [← h5460 X2 X1 X2 (X0 ◇ X1)]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X4 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5460 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5461 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5461 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (y ◇ (x ◇ u)))))]

@[equational_result]
theorem Equation5461_implies_Equation2 (G : Type*) [Magma G] (h5461 : Equation5461 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5461 X0 X2 X1 X1 X1]
    conv => enter [1]; rw [← h5461 X2 X1 X2 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X4 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5461 X4 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5463 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5463 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (y ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5463_implies_Equation2 (G : Type*) [Magma G] (h5463 : Equation5463 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5463 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5463 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5464 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5464 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (y ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5464_implies_Equation2 (G : Type*) [Magma G] (h5464 : Equation5464 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5464 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5464 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5465 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5465 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (y ◇ (y ◇ w)))))]

@[equational_result]
theorem Equation5465_implies_Equation2 (G : Type*) [Magma G] (h5465 : Equation5465 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5465 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5465 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5466 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5466 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (y ◇ (y ◇ u)))))]

@[equational_result]
theorem Equation5466_implies_Equation2 (G : Type*) [Magma G] (h5466 : Equation5466 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5466 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5466 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5468 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5468 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (y ◇ (z ◇ y)))))]

@[equational_result]
theorem Equation5468_implies_Equation2 (G : Type*) [Magma G] (h5468 : Equation5468 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5468 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5468 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5469 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5469 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (y ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5469_implies_Equation2 (G : Type*) [Magma G] (h5469 : Equation5469 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5469 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5469 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5470 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5470 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (y ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5470_implies_Equation2 (G : Type*) [Magma G] (h5470 : Equation5470 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5470 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5470 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5471 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5471 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (y ◇ (z ◇ u)))))]

@[equational_result]
theorem Equation5471_implies_Equation2 (G : Type*) [Magma G] (h5471 : Equation5471 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5471 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5471 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5473 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5473 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (y ◇ (w ◇ y)))))]

@[equational_result]
theorem Equation5473_implies_Equation2 (G : Type*) [Magma G] (h5473 : Equation5473 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5473 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5473 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5474 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5474 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (y ◇ (w ◇ z)))))]

@[equational_result]
theorem Equation5474_implies_Equation2 (G : Type*) [Magma G] (h5474 : Equation5474 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5474 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5474 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5475 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5475 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (y ◇ (w ◇ w)))))]

@[equational_result]
theorem Equation5475_implies_Equation2 (G : Type*) [Magma G] (h5475 : Equation5475 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5475 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5475 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5476 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5476 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (y ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5476_implies_Equation2 (G : Type*) [Magma G] (h5476 : Equation5476 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5476 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5476 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5478 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5478 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (y ◇ (u ◇ y)))))]

@[equational_result]
theorem Equation5478_implies_Equation2 (G : Type*) [Magma G] (h5478 : Equation5478 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5478 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5478 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5479 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5479 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (y ◇ (u ◇ z)))))]

@[equational_result]
theorem Equation5479_implies_Equation2 (G : Type*) [Magma G] (h5479 : Equation5479 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5479 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5479 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5480 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5480 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (y ◇ (u ◇ w)))))]

@[equational_result]
theorem Equation5480_implies_Equation2 (G : Type*) [Magma G] (h5480 : Equation5480 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5480 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5480 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5481 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5481 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (y ◇ (u ◇ u)))))]

@[equational_result]
theorem Equation5481_implies_Equation2 (G : Type*) [Magma G] (h5481 : Equation5481 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5481 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5481 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5482 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5482 G := by
  intro x y z w u v
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (y ◇ (u ◇ v)))))]

@[equational_result]
theorem Equation5482_implies_Equation2 (G : Type*) [Magma G] (h5482 : Equation5482 G) : Equation2 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5482 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5482 X6 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5484 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5484 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (z ◇ (x ◇ y)))))]

theorem Equation4512_5484_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5484 : Equation5484 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h5484 X0 X1 X2 X1]
    conv => enter [1]; rw [← h5484 X2 (X0 ◇ X1) X1 X2]
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
theorem Equation2_implies_Equation5485 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5485 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (z ◇ (x ◇ z)))))]

@[equational_result]
theorem Equation5485_implies_Equation2 (G : Type*) [Magma G] (h5485 : Equation5485 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5485 X0 (X0 ◇ X2) X2 (X0 ◇ X2)]
    conv => enter [1]; rw [← h5485 X2 X1 (X0 ◇ X2) X2]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X4 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5485 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5486 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5486 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (z ◇ (x ◇ w)))))]

@[equational_result]
theorem Equation5486_implies_Equation2 (G : Type*) [Magma G] (h5486 : Equation5486 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ X0)) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2]; rw [h5486 X0 (X2 ◇ (X0 ◇ X3)) X2 X3]
    conv => enter [1]; rw [← h5486 X3 X1 X2 (X2 ◇ (X0 ◇ X3))]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 X0 (X0 ◇ (X0 ◇ (X4 ◇ X0))) X0]
    conv => enter [1]; rw [← h5486 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5487 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5487 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (z ◇ (x ◇ u)))))]

@[equational_result]
theorem Equation5487_implies_Equation2 (G : Type*) [Magma G] (h5487 : Equation5487 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X3 : G, (X1 ◇ X0) = X3 := by
    intro X1 X0 X3
    conv => enter [1, 2]; rw [h5487 X0 X1 X3 X1 X1]
    conv => enter [1]; rw [← h5487 X3 X1 X1 X3 (X0 ◇ X1)]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X4 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5487 X4 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5489 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5489 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (z ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5489_implies_Equation2 (G : Type*) [Magma G] (h5489 : Equation5489 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5489 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5489 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5490 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5490 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (z ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5490_implies_Equation2 (G : Type*) [Magma G] (h5490 : Equation5490 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5490 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5490 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5491 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5491 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (z ◇ (y ◇ w)))))]

@[equational_result]
theorem Equation5491_implies_Equation2 (G : Type*) [Magma G] (h5491 : Equation5491 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5491 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5491 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5492 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5492 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (z ◇ (y ◇ u)))))]

@[equational_result]
theorem Equation5492_implies_Equation2 (G : Type*) [Magma G] (h5492 : Equation5492 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5492 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5492 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5494 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5494 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (z ◇ (z ◇ y)))))]

@[equational_result]
theorem Equation5494_implies_Equation2 (G : Type*) [Magma G] (h5494 : Equation5494 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5494 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5494 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5495 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5495 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (z ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5495_implies_Equation2 (G : Type*) [Magma G] (h5495 : Equation5495 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5495 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5495 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5496 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5496 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (z ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5496_implies_Equation2 (G : Type*) [Magma G] (h5496 : Equation5496 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5496 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5496 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5497 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5497 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (z ◇ (z ◇ u)))))]

@[equational_result]
theorem Equation5497_implies_Equation2 (G : Type*) [Magma G] (h5497 : Equation5497 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5497 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5497 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5499 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5499 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (z ◇ (w ◇ y)))))]

@[equational_result]
theorem Equation5499_implies_Equation2 (G : Type*) [Magma G] (h5499 : Equation5499 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5499 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5499 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5500 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5500 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (z ◇ (w ◇ z)))))]

@[equational_result]
theorem Equation5500_implies_Equation2 (G : Type*) [Magma G] (h5500 : Equation5500 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5500 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5500 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5501 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5501 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (z ◇ (w ◇ w)))))]

@[equational_result]
theorem Equation5501_implies_Equation2 (G : Type*) [Magma G] (h5501 : Equation5501 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5501 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5501 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5502 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5502 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (z ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5502_implies_Equation2 (G : Type*) [Magma G] (h5502 : Equation5502 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5502 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5502 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5504 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5504 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (z ◇ (u ◇ y)))))]

@[equational_result]
theorem Equation5504_implies_Equation2 (G : Type*) [Magma G] (h5504 : Equation5504 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5504 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5504 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5505 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5505 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (z ◇ (u ◇ z)))))]

@[equational_result]
theorem Equation5505_implies_Equation2 (G : Type*) [Magma G] (h5505 : Equation5505 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5505 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5505 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5506 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5506 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (z ◇ (u ◇ w)))))]

@[equational_result]
theorem Equation5506_implies_Equation2 (G : Type*) [Magma G] (h5506 : Equation5506 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5506 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5506 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5507 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5507 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (z ◇ (u ◇ u)))))]

@[equational_result]
theorem Equation5507_implies_Equation2 (G : Type*) [Magma G] (h5507 : Equation5507 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5507 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5507 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5508 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5508 G := by
  intro x y z w u v
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (z ◇ (u ◇ v)))))]

@[equational_result]
theorem Equation5508_implies_Equation2 (G : Type*) [Magma G] (h5508 : Equation5508 G) : Equation2 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5508 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5508 X6 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5510 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5510 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (w ◇ (x ◇ y)))))]

theorem Equation4512_5510_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5510 : Equation5510 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 : G, ((X0 ◇ X1) ◇ X0) = X2 := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h5510 X0 X1 X2 X2]
    conv => enter [1]; rw [← h5510 X2 (X0 ◇ X1) X1 X2]
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
theorem Equation2_implies_Equation5511 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5511 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (w ◇ (x ◇ z)))))]

@[equational_result]
theorem Equation5511_implies_Equation2 (G : Type*) [Magma G] (h5511 : Equation5511 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X2 : G, (X1 ◇ X0) = X2 := by
    intro X1 X0 X2
    conv => enter [1, 2]; rw [h5511 X0 (X0 ◇ X2) X2 X2]
    conv => enter [1]; rw [← h5511 X2 X1 (X0 ◇ X2) X2]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X4 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5511 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5512 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5512 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (w ◇ (x ◇ w)))))]

@[equational_result]
theorem Equation5512_implies_Equation2 (G : Type*) [Magma G] (h5512 : Equation5512 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X0 X3 : G, (X1 ◇ (X2 ◇ X0)) = X3 := by
    intro X1 X2 X0 X3
    conv => enter [1, 2, 2]; rw [h5512 X0 (X3 ◇ (X0 ◇ X3)) (X3 ◇ (X0 ◇ X3)) X3]
    conv => enter [1]; rw [← h5512 X3 X1 X2 (X3 ◇ (X0 ◇ X3))]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 X0 (X0 ◇ (X0 ◇ (X4 ◇ X0))) X0]
    conv => enter [1]; rw [← h5512 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5513 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5513 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (w ◇ (x ◇ u)))))]

@[equational_result]
theorem Equation5513_implies_Equation2 (G : Type*) [Magma G] (h5513 : Equation5513 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X3 : G, (X1 ◇ X0) = X3 := by
    intro X1 X0 X3
    conv => enter [1, 2]; rw [h5513 X0 X1 X3 X3 X1]
    conv => enter [1]; rw [← h5513 X3 X1 X1 X3 (X0 ◇ X1)]
  have l1 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X4 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5513 X4 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5515 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5515 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (w ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5515_implies_Equation2 (G : Type*) [Magma G] (h5515 : Equation5515 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5515 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5515 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5516 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5516 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (w ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5516_implies_Equation2 (G : Type*) [Magma G] (h5516 : Equation5516 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5516 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5516 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5517 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5517 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (w ◇ (y ◇ w)))))]

@[equational_result]
theorem Equation5517_implies_Equation2 (G : Type*) [Magma G] (h5517 : Equation5517 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5517 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5517 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5518 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5518 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (w ◇ (y ◇ u)))))]

@[equational_result]
theorem Equation5518_implies_Equation2 (G : Type*) [Magma G] (h5518 : Equation5518 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5518 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5518 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5520 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5520 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (w ◇ (z ◇ y)))))]

@[equational_result]
theorem Equation5520_implies_Equation2 (G : Type*) [Magma G] (h5520 : Equation5520 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5520 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5520 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5521 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5521 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (w ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5521_implies_Equation2 (G : Type*) [Magma G] (h5521 : Equation5521 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5521 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5521 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5522 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5522 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (w ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5522_implies_Equation2 (G : Type*) [Magma G] (h5522 : Equation5522 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5522 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5522 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5523 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5523 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (w ◇ (z ◇ u)))))]

@[equational_result]
theorem Equation5523_implies_Equation2 (G : Type*) [Magma G] (h5523 : Equation5523 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5523 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5523 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5525 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5525 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (w ◇ (w ◇ y)))))]

@[equational_result]
theorem Equation5525_implies_Equation2 (G : Type*) [Magma G] (h5525 : Equation5525 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5525 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5525 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5526 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5526 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (w ◇ (w ◇ z)))))]

@[equational_result]
theorem Equation5526_implies_Equation2 (G : Type*) [Magma G] (h5526 : Equation5526 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5526 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5526 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5527 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5527 G := by
  intro x y z w
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (w ◇ (w ◇ w)))))]

@[equational_result]
theorem Equation5527_implies_Equation2 (G : Type*) [Magma G] (h5527 : Equation5527 G) : Equation2 G := by
  have l0 : ∀ X0 X4 : G, X0 = X4 := by
    intro X0 X4
    conv => enter [1]; rw [h5527 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5527 X4 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5528 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5528 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (w ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5528_implies_Equation2 (G : Type*) [Magma G] (h5528 : Equation5528 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5528 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5528 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5530 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5530 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (w ◇ (u ◇ y)))))]

@[equational_result]
theorem Equation5530_implies_Equation2 (G : Type*) [Magma G] (h5530 : Equation5530 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5530 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5530 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5531 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5531 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (w ◇ (u ◇ z)))))]

@[equational_result]
theorem Equation5531_implies_Equation2 (G : Type*) [Magma G] (h5531 : Equation5531 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5531 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5531 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5532 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5532 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (w ◇ (u ◇ w)))))]

@[equational_result]
theorem Equation5532_implies_Equation2 (G : Type*) [Magma G] (h5532 : Equation5532 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5532 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5532 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5533 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5533 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (w ◇ (u ◇ u)))))]

@[equational_result]
theorem Equation5533_implies_Equation2 (G : Type*) [Magma G] (h5533 : Equation5533 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5533 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5533 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5534 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5534 G := by
  intro x y z w u v
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (w ◇ (u ◇ v)))))]

@[equational_result]
theorem Equation5534_implies_Equation2 (G : Type*) [Magma G] (h5534 : Equation5534 G) : Equation2 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5534 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5534 X6 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5536 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5536 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (x ◇ y)))))]

theorem Equation4512_5536_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5536 : Equation5536 G) : Equation2 G := by
  have l0 : ∀ X0 X1 X2 X3 X4 X5 : G, (X0 ◇ X1) = (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X1 X2 X3 X4 X5
    conv => enter [1]; rw [h5536 (X0 ◇ X1) X2 X3 X4 X5]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l1 : ∀ X1 X0 X2 X3 X5 : G, ((X1 ◇ (X0 ◇ X2)) ◇ (X3 ◇ X0)) = X5 := by
    intro X1 X0 X2 X3 X5
    conv => enter [1, 2, 2]; rw [h5536 X0 X2 X1 X5 X1]
    conv => enter [1]; rw [← h5536 X5 (X1 ◇ (X0 ◇ X2)) X3 X2 X1]
  have l2 : ∀ X5 X0 X1 X2 X3 X4 : G, (X5 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ X5)))))) = X4 := by
    intro X5 X0 X1 X2 X3 X4
    conv => enter [1, 2]; rw [h4512 X0 X1 (X2 ◇ (X3 ◇ (X4 ◇ X5)))]
    conv => enter [1]; rw [← h5536 X4 X5 (X0 ◇ X1) X2 X3]
  have l3 : ∀ X1 X0 X2 X3 X5 : G, (X1 ◇ ((X0 ◇ X2) ◇ (X3 ◇ X0))) = X5 := by
    intro X1 X0 X2 X3 X5
    conv => enter [1]; rw [h4512 X1 (X0 ◇ X2) (X3 ◇ X0)]
    conv => enter [1]; rw [l1 X1 X0 X2 X3 X5]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1 X0 X0 X0 X0]
    conv => enter [1]; rw [l2 X0 X0 X0 X0 X0 X1]
  have l5 : ∀ X1 X0 X2 X3 X5 : G, (X1 ◇ (X0 ◇ (X2 ◇ (X3 ◇ X0)))) = X5 := by
    intro X1 X0 X2 X3 X5
    conv => enter [1, 2]; rw [h4512 X0 X2 (X3 ◇ X0)]
    conv => enter [1]; rw [l3 X1 X0 X2 X3 X5]
  have l6 : ∀ X0 X2 X3 X5 : G, (X0 ◇ (X2 ◇ (X3 ◇ X0))) = X5 := by
    intro X0 X2 X3 X5
    conv => enter [1, 2]; rw [← l4 X0 (X2 ◇ (X3 ◇ X0))]
    conv => enter [1]; rw [l5 X0 X0 X2 X3 X5]
  have l7 : ∀ X2 X3 X0 X5 : G, (X2 ◇ (X3 ◇ X0)) = X5 := by
    intro X2 X3 X0 X5
    conv => enter [1]; rw [← l4 X0 (X2 ◇ (X3 ◇ X0))]
    conv => enter [1]; rw [l6 X0 X2 X3 X5]
  have l8 : ∀ X3 X0 X5 : G, (X3 ◇ X0) = X5 := by
    intro X3 X0 X5
    conv => enter [1, 2]; rw [← l4 X3 X0]
    conv => enter [1]; rw [l7 X3 X3 X0 X5]
  have l9 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [← l8 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X5 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5536 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation2_implies_Equation5537 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5537 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (x ◇ z)))))]

@[equational_result]
theorem Equation5537_implies_Equation2 (G : Type*) [Magma G] (h5537 : Equation5537 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X4 : G, (X1 ◇ X0) = X4 := by
    intro X1 X0 X4
    conv => enter [1, 2]; rw [h5537 X0 (X0 ◇ X1) X1 X1 X4]
    conv => enter [1]; rw [← h5537 X4 X1 (X0 ◇ X1) X1 X1]
  have l1 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X5 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5537 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5538 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5538 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (x ◇ w)))))]

@[equational_result]
theorem Equation5538_implies_Equation2 (G : Type*) [Magma G] (h5538 : Equation5538 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X4 : G, (X1 ◇ X0) = X4 := by
    intro X1 X0 X4
    conv => enter [1, 2]; rw [h5538 X0 X1 (X0 ◇ X1) X1 X4]
    conv => enter [1]; rw [← h5538 X4 X1 X1 (X0 ◇ X1) X1]
  have l1 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X5 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5538 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5539 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5539 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (x ◇ u)))))]

@[equational_result]
theorem Equation5539_implies_Equation2 (G : Type*) [Magma G] (h5539 : Equation5539 G) : Equation2 G := by
  have l0 : ∀ X1 X0 X4 : G, (X1 ◇ X0) = X4 := by
    intro X1 X0 X4
    conv => enter [1, 2]; rw [h5539 X0 X1 X1 (X0 ◇ X4) X4]
    conv => enter [1]; rw [← h5539 X4 X1 X1 X1 (X0 ◇ X4)]
  have l1 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [← l0 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X5 ◇ X0)))) X0]
    conv => enter [1]; rw [← h5539 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5540 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5540 G := by
  intro x y z w u v
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (x ◇ v)))))]

theorem Equation4512_5540_implies_Equation2 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h5540 : Equation5540 G) : Equation2 G := by
  have l0 : ∀ X1 X2 X3 X4 X5 X0 X6 : G, (X1 ◇ (X2 ◇ (X3 ◇ (X4 ◇ (X5 ◇ (X0 ◇ X6)))))) = X0 := by
    intro X1 X2 X3 X4 X5 X0 X6
    conv => enter [1]; rw [h4512 X1 X2 (X3 ◇ (X4 ◇ (X5 ◇ (X0 ◇ X6))))]
    conv => enter [1]; rw [← h5540 X0 (X1 ◇ X2) X3 X4 X5 X6]
  have l1 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5540 X0 X0 X0 X0 X0 (X5 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X0 X0 X0 X0 X5 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation2_implies_Equation5542 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5542 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (y ◇ y)))))]

@[equational_result]
theorem Equation5542_implies_Equation2 (G : Type*) [Magma G] (h5542 : Equation5542 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5542 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5542 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5543 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5543 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (y ◇ z)))))]

@[equational_result]
theorem Equation5543_implies_Equation2 (G : Type*) [Magma G] (h5543 : Equation5543 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5543 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5543 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5544 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5544 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (y ◇ w)))))]

@[equational_result]
theorem Equation5544_implies_Equation2 (G : Type*) [Magma G] (h5544 : Equation5544 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5544 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5544 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5545 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5545 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (y ◇ u)))))]

@[equational_result]
theorem Equation5545_implies_Equation2 (G : Type*) [Magma G] (h5545 : Equation5545 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5545 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5545 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5546 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5546 G := by
  intro x y z w u v
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (y ◇ v)))))]

@[equational_result]
theorem Equation5546_implies_Equation2 (G : Type*) [Magma G] (h5546 : Equation5546 G) : Equation2 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5546 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5546 X6 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5548 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5548 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (z ◇ y)))))]

@[equational_result]
theorem Equation5548_implies_Equation2 (G : Type*) [Magma G] (h5548 : Equation5548 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5548 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5548 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5549 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5549 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (z ◇ z)))))]

@[equational_result]
theorem Equation5549_implies_Equation2 (G : Type*) [Magma G] (h5549 : Equation5549 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5549 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5549 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5550 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5550 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (z ◇ w)))))]

@[equational_result]
theorem Equation5550_implies_Equation2 (G : Type*) [Magma G] (h5550 : Equation5550 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5550 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5550 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5551 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5551 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (z ◇ u)))))]

@[equational_result]
theorem Equation5551_implies_Equation2 (G : Type*) [Magma G] (h5551 : Equation5551 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5551 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5551 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5552 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5552 G := by
  intro x y z w u v
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (z ◇ v)))))]

@[equational_result]
theorem Equation5552_implies_Equation2 (G : Type*) [Magma G] (h5552 : Equation5552 G) : Equation2 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5552 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5552 X6 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5554 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5554 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (w ◇ y)))))]

@[equational_result]
theorem Equation5554_implies_Equation2 (G : Type*) [Magma G] (h5554 : Equation5554 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5554 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5554 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5555 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5555 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (w ◇ z)))))]

@[equational_result]
theorem Equation5555_implies_Equation2 (G : Type*) [Magma G] (h5555 : Equation5555 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5555 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5555 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5556 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5556 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (w ◇ w)))))]

@[equational_result]
theorem Equation5556_implies_Equation2 (G : Type*) [Magma G] (h5556 : Equation5556 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5556 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5556 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5557 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5557 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (w ◇ u)))))]

@[equational_result]
theorem Equation5557_implies_Equation2 (G : Type*) [Magma G] (h5557 : Equation5557 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5557 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5557 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5558 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5558 G := by
  intro x y z w u v
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (w ◇ v)))))]

@[equational_result]
theorem Equation5558_implies_Equation2 (G : Type*) [Magma G] (h5558 : Equation5558 G) : Equation2 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5558 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5558 X6 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5560 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5560 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (u ◇ y)))))]

@[equational_result]
theorem Equation5560_implies_Equation2 (G : Type*) [Magma G] (h5560 : Equation5560 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5560 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5560 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5561 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5561 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (u ◇ z)))))]

@[equational_result]
theorem Equation5561_implies_Equation2 (G : Type*) [Magma G] (h5561 : Equation5561 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5561 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5561 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5562 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5562 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (u ◇ w)))))]

@[equational_result]
theorem Equation5562_implies_Equation2 (G : Type*) [Magma G] (h5562 : Equation5562 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5562 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5562 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5563 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5563 G := by
  intro x y z w u
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (u ◇ u)))))]

@[equational_result]
theorem Equation5563_implies_Equation2 (G : Type*) [Magma G] (h5563 : Equation5563 G) : Equation2 G := by
  have l0 : ∀ X0 X5 : G, X0 = X5 := by
    intro X0 X5
    conv => enter [1]; rw [h5563 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5563 X5 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5564 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5564 G := by
  intro x y z w u v
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (u ◇ v)))))]

@[equational_result]
theorem Equation5564_implies_Equation2 (G : Type*) [Magma G] (h5564 : Equation5564 G) : Equation2 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5564 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5564 X6 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5566 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5566 G := by
  intro x y z w u v
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (v ◇ y)))))]

@[equational_result]
theorem Equation5566_implies_Equation2 (G : Type*) [Magma G] (h5566 : Equation5566 G) : Equation2 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5566 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5566 X6 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5567 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5567 G := by
  intro x y z w u v
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (v ◇ z)))))]

@[equational_result]
theorem Equation5567_implies_Equation2 (G : Type*) [Magma G] (h5567 : Equation5567 G) : Equation2 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5567 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5567 X6 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5568 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5568 G := by
  intro x y z w u v
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (v ◇ w)))))]

@[equational_result]
theorem Equation5568_implies_Equation2 (G : Type*) [Magma G] (h5568 : Equation5568 G) : Equation2 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5568 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5568 X6 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5569 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5569 G := by
  intro x y z w u v
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (v ◇ u)))))]

@[equational_result]
theorem Equation5569_implies_Equation2 (G : Type*) [Magma G] (h5569 : Equation5569 G) : Equation2 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5569 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5569 X6 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5570 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5570 G := by
  intro x y z w u v
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (v ◇ v)))))]

@[equational_result]
theorem Equation5570_implies_Equation2 (G : Type*) [Magma G] (h5570 : Equation5570 G) : Equation2 G := by
  have l0 : ∀ X0 X6 : G, X0 = X6 := by
    intro X0 X6
    conv => enter [1]; rw [h5570 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5570 X6 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation2_implies_Equation5571 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5571 G := by
  intro x y z w u v r
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (w ◇ (u ◇ (v ◇ r)))))]

@[equational_result]
theorem Equation5571_implies_Equation2 (G : Type*) [Magma G] (h5571 : Equation5571 G) : Equation2 G := by
  have l0 : ∀ X0 X7 : G, X0 = X7 := by
    intro X0 X7
    conv => enter [1]; rw [h5571 X0 X0 X0 X0 X0 X0 X0]
    conv => enter [1]; rw [← h5571 X7 X0 X0 X0 X0 X0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation4_implies_Equation9 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation9 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ y)]

theorem Equation9_4512_implies_Equation4 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h9 X0 X0]
    conv => enter [1]; rw [← h9 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [← h9 X0 X1]
  intro x y
  conv => enter [1]; rw [← l2 x y]

@[equational_result]
theorem Equation4_implies_Equation12 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation12 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ z)]

@[equational_result]
theorem Equation12_implies_Equation4 (G : Type*) [Magma G] (h12 : Equation12 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h12 X0 X1 X1]
    conv => enter [1]; rw [← h12 X1 X0 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation48 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation48 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ (x ◇ y))]

theorem Equation48_4512_implies_Equation4 (G : Type*) [Magma G] (h48 : Equation48 G) (h4512 : Equation4512 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h48 X0 X0]
    conv => enter [1]; rw [← h48 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ X1)) X2]
    conv => enter [1, 1]; rw [← h48 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1]; rw [← l2 X0 ((X0 ◇ X1) ◇ X2)]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← l5 X0 X2 X1]
  have l7 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h48 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l8 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l7 sK0 sK1 X0]
    conv => enter [1]; rw [← l2 sK0 ((sK0 ◇ sK1) ◇ X0)]
  have l9 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l8 sK0 sK0 X0]
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ sK0) X0]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation4_implies_Equation50 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation50 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ y))]

theorem Equation50_4512_implies_Equation4 (G : Type*) [Magma G] (h50 : Equation50 G) (h4512 : Equation4512 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h50 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h50 (X0 ◇ X0) X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [← h50 X0 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l2 X0]
    conv => enter [1]; rw [← h50 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [← l5 x y]

@[equational_result]
theorem Equation4_implies_Equation51 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation51 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ z))]

theorem Equation51_4512_implies_Equation4 (G : Type*) [Magma G] (h51 : Equation51 G) (h4512 : Equation4512 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h51 X0 X1 X1]
    conv => enter [1]; rw [← h51 X1 X0 (X0 ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h51 X0 X0 X0]
    conv => enter [1]; rw [← h51 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

@[equational_result]
theorem Equation4_implies_Equation53 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation53 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ y))]

theorem Equation53_4512_implies_Equation4 (G : Type*) [Magma G] (h53 : Equation53 G) (h4512 : Equation4512 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h53 X0 X1]
    conv => enter [1]; rw [← h53 X0 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h4512 X1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [h53 X1 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

@[equational_result]
theorem Equation4_implies_Equation54 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation54 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ z))]

@[equational_result]
theorem Equation54_implies_Equation4 (G : Type*) [Magma G] (h54 : Equation54 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h54 X0 X1 X1]
    conv => enter [1]; rw [← h54 X1 X0 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation57 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation57 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ z))]

@[equational_result]
theorem Equation57_implies_Equation4 (G : Type*) [Magma G] (h57 : Equation57 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h57 X0 X0 X1]
    conv => enter [1]; rw [← h57 X1 X0 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation59 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation59 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ y))]

@[equational_result]
theorem Equation59_implies_Equation4 (G : Type*) [Magma G] (h59 : Equation59 G) : Equation4 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h59 (X0 ◇ X1) X1 X0]
    conv => enter [1]; rw [← h59 X2 (X0 ◇ X1) X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0 X1 X0]
    conv => enter [1]; rw [← h59 X1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation4_implies_Equation60 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation60 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ z))]

@[equational_result]
theorem Equation60_implies_Equation4 (G : Type*) [Magma G] (h60 : Equation60 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h60 X0 (X1 ◇ X1) X1]
    conv => enter [1]; rw [← h60 X1 X0 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation61 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation61 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ w))]

@[equational_result]
theorem Equation61_implies_Equation4 (G : Type*) [Magma G] (h61 : Equation61 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h61 X0 X1 X1 X1]
    conv => enter [1]; rw [← h61 X1 X0 X1 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation412 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation412 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ (x ◇ (x ◇ y)))]

theorem Equation412_4512_implies_Equation4 (G : Type*) [Magma G] (h412 : Equation412 G) (h4512 : Equation4512 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h412 X0 X0]
    conv => enter [1]; rw [← h412 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ (X0 ◇ X1))) X2]
    conv => enter [1, 1]; rw [← h412 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X1)) X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1]; rw [← l2 X0 ((X0 ◇ (X0 ◇ X1)) ◇ X2)]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1]; rw [← l2 X0 ((X0 ◇ X1) ◇ X2)]
  have l7 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l8 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [← l7 X0 X2 X1]
  have l9 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2]; rw [h412 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ (sK1 ◇ X0)))]
  have l10 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK1 ◇ X0) ◇ X1)) = (((sK0 ◇ sK1) ◇ X0) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [h4512 sK0 (sK1 ◇ X0) X1]
    conv => enter [1, 1]; rw [h4512 sK0 sK1 X0]
  have l11 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h412 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l12 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l11 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l2 sK0 ((sK0 ◇ sK1) ◇ X0)]
  have l13 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK1 ◇ X0) ◇ X1)) = ((sK0 ◇ sK1) ◇ (X0 ◇ X1)) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l10 sK0 sK1 X0 X1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) X0 X1]
  have l14 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l9 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [l8 sK1 sK1 X0]
  have l15 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l12 sK0 sK1 X0]
    conv => enter [1]; rw [← l2 sK0 ((sK0 ◇ sK1) ◇ X0)]
  have l16 : ∀ sK0 sK1 X0 X1 : G, (sK0 ◇ ((sK1 ◇ X0) ◇ X1)) = ((sK0 ◇ sK1) ◇ X1) := by
    intro sK0 sK1 X0 X1
    conv => enter [1]; rw [l13 sK0 sK1 X0 X1]
    conv => enter [1]; rw [l8 (sK0 ◇ sK1) X0 X1]
  have l17 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l14 sK0 sK1 X0]
    conv => enter [1, 2]; rw [l8 sK1 sK1 X0]
  have l18 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l15 sK0 sK0 X0]
    conv => enter [1]; rw [l8 sK0 (sK0 ◇ sK0) X0]
  have l19 : ∀ sK0 sK1 X1 : G, ((sK0 ◇ sK1) ◇ X1) = (sK0 ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [← l16 sK0 sK1 sK0 X1]
    conv => enter [1]; rw [l8 sK0 (sK1 ◇ sK0) X1]
  have l20 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l17 sK0 sK1 X0]
    conv => enter [1]; rw [l8 (sK0 ◇ sK1) sK1 X0]
  have l21 : ∀ sK0 sK1 X1 : G, sK0 = ((sK0 ◇ sK1) ◇ X1) := by
    intro sK0 sK1 X1
    conv => enter [1]; rw [l18 sK0 X1]
    conv => enter [1]; rw [← l19 sK0 sK1 X1]
  have l22 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l21 sK0 sK1 sK0]
    conv => enter [1]; rw [← l20 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l22 x y]

@[equational_result]
theorem Equation4_implies_Equation415 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation415 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (x ◇ (x ◇ (y ◇ z)))]

theorem Equation415_4512_implies_Equation4 (G : Type*) [Magma G] (h415 : Equation415 G) (h4512 : Equation4512 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h415 X0 X1 X1]
    conv => enter [1]; rw [← h415 X1 X0 (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h415 X0 X0 X0]
    conv => enter [1]; rw [← h415 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1, 1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X1)) X2]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ ((X0 ◇ X1) ◇ X2)) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1]; rw [← l3 X0 ((X0 ◇ X1) ◇ X2)]
  have l6 : ∀ X0 X1 X2 : G, (X0 ◇ (X0 ◇ (X1 ◇ X2))) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1, 2]; rw [h4512 X0 X1 X2]
    conv => enter [1]; rw [← l5 X0 X2 X1]
  have l7 : ∀ X0 X1 X2 : G, (X0 ◇ (X1 ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l3 X0 (X1 ◇ X2)]
    conv => enter [1]; rw [l6 X0 X1 X2]
  have l8 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l0 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l9 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1 X0]
    conv => enter [1]; rw [← l3 sK0 ((sK0 ◇ sK1) ◇ X0)]
  have l10 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l9 sK0 sK0 X0]
    conv => enter [1]; rw [l7 sK0 (sK0 ◇ sK0) X0]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation4_implies_Equation418 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation418 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (x ◇ z)))]

theorem Equation418_4512_implies_Equation4 (G : Type*) [Magma G] (h418 : Equation418 G) (h4512 : Equation4512 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h418 X0 X0 X0]
    conv => enter [1]; rw [← h418 X0 X1 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h418 X0 X0 X0]
    conv => enter [1]; rw [← h418 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h418 X0 (X0 ◇ X1) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = ((X0 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ (X0 ◇ X1)) X0]
    conv => enter [1, 2, 2]; rw [l2 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X1) ((X0 ◇ (X0 ◇ X1)) ◇ X0)]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X1 ((X0 ◇ (X0 ◇ X1)) ◇ X0)]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X0))))) := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X0 ◇ X1) X0]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 X1]
    conv => enter [1]; rw [← h418 X0 X1 ((X0 ◇ X1) ◇ X0)]
  have l8 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1]; rw [l7 X0 X1]
  intro x y
  conv => enter [1]; rw [← l9 x y]

@[equational_result]
theorem Equation4_implies_Equation420 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation420 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (y ◇ y)))]

theorem Equation420_4512_implies_Equation4 (G : Type*) [Magma G] (h420 : Equation420 G) (h4512 : Equation4512 G) : Equation4 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h420 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) ◇ X0)) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ sK1) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ sK1) X0]
  have l3 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l2 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 sK1 X0]
  have l4 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) = (sK0 ◇ (sK1 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2, 2, 2]; rw [h420 sK1 X0]
    conv => enter [1]; rw [← l3 sK0 (sK1 ◇ (X0 ◇ (X0 ◇ X0))) sK1]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (X0 ◇ X0))]
  have l6 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l5 sK0 sK1 X0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← l6 sK0 sK1 sK1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h420 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← l6 sK0 sK1 sK0]
  have l9 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l10 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← l7 sK0 sK1]
  have l11 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l9 sK0 sK1 (sK0 ◇ sK1)]
  have l12 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l11 sK0 sK1]
  have l13 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l14 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l12 sK0 sK0]
    conv => enter [1]; rw [← l13 sK0 sK0 sK0]
  have l15 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0]
    conv => enter [1]; rw [← l7 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l15 x y]

@[equational_result]
theorem Equation4_implies_Equation421 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation421 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (y ◇ z)))]

theorem Equation421_4512_implies_Equation4 (G : Type*) [Magma G] (h421 : Equation421 G) (h4512 : Equation4512 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h421 X0 X1 X1]
    conv => enter [1]; rw [← h421 X1 X0 (X1 ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h421 X0 X0 X0]
    conv => enter [1]; rw [← h421 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

@[equational_result]
theorem Equation4_implies_Equation423 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation423 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (z ◇ y)))]

theorem Equation423_4512_implies_Equation4 (G : Type*) [Magma G] (h423 : Equation423 G) (h4512 : Equation4512 G) : Equation4 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h423 (sK0 ◇ sK1) (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h423 (sK0 ◇ sK1) sK1 sK0]
  have l1 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2, 2]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← h423 X0 (sK0 ◇ sK1) (sK0 ◇ sK1)]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ (sK0 ◇ sK1))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 X0 sK0 sK1]
  have l3 : ∀ sK1 : G, sK1 = (sK1 ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [h423 sK1 sK1 sK1]
    conv => enter [1, 2]; rw [l2 sK1 sK1 sK1]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ (sK1 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2, 2, 2]; rw [l3 sK1]
    conv => enter [1]; rw [← h423 X0 sK1 sK1]
  have l5 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ sK1)) = X0 := by
    intro X0 sK1
    conv => enter [1, 2, 2]; rw [l3 sK1]
    conv => enter [1]; rw [l4 X0 sK1]
  have l6 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X1)) := by
    intro X0 X1 sK1 sK0
    conv => enter [1, 1]; rw [h423 X0 sK1 sK0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) X1]
  have l7 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ sK1) ◇ X1)) := by
    intro X0 X1 sK1
    conv => enter [1, 1]; rw [← l5 X0 sK1]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ sK1) X1]
  have l8 : ∀ X0 X1 sK1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (sK1 ◇ X1))) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [l7 X0 X1 sK1]
    conv => enter [1, 2]; rw [← h4512 X0 sK1 X1]
  have l9 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X1))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l6 X0 X1 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK1 ◇ (sK0 ◇ sK1)) X1]
  have l10 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ X1)))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l9 X0 X1 sK1 sK0]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 (sK0 ◇ sK1) X1]
  have l11 : ∀ X0 X1 sK0 sK1 : G, (X0 ◇ X1) = (X0 ◇ ((sK0 ◇ sK1) ◇ X1)) := by
    intro X0 X1 sK0 sK1
    conv => enter [1]; rw [l10 X0 X1 sK1 sK0]
    conv => enter [1]; rw [← l8 X0 ((sK0 ◇ sK1) ◇ X1) sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l3 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l13 : ∀ sK0 sK1 X0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h423 sK0 sK1 X0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (X0 ◇ sK1)]
  have l14 : ∀ sK0 X0 sK1 : G, sK0 = (sK0 ◇ (X0 ◇ sK1)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l13 sK0 sK1 X0]
    conv => enter [1]; rw [← l11 sK0 (X0 ◇ sK1) sK0 sK1]
  have l15 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l16 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l16 x y]

@[equational_result]
theorem Equation4_implies_Equation424 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation424 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (z ◇ z)))]

theorem Equation424_4512_implies_Equation4 (G : Type*) [Magma G] (h424 : Equation424 G) (h4512 : Equation4512 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h424 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h424 X0 X0 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h424 X1 (X0 ◇ X0) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l0 X0]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]

@[equational_result]
theorem Equation4_implies_Equation425 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation425 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (z ◇ w)))]

theorem Equation425_4512_implies_Equation4 (G : Type*) [Magma G] (h425 : Equation425 G) (h4512 : Equation4512 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h425 X0 X1 X1 X1]
    conv => enter [1]; rw [← h425 X1 X0 X0 (X1 ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h425 X0 X0 X0 X0]
    conv => enter [1]; rw [← h425 X0 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l3 x y]

@[equational_result]
theorem Equation4_implies_Equation428 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation428 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (x ◇ z)))]

theorem Equation428_4512_implies_Equation4 (G : Type*) [Magma G] (h428 : Equation428 G) (h4512 : Equation4512 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h428 X0 X0 X0]
    conv => enter [1]; rw [← h428 X0 X1 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 (X0 ◇ X1) X0]
    conv => enter [1]; rw [← h428 X0 (X0 ◇ X1) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [l1 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h4512 X0 X1 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]

@[equational_result]
theorem Equation4_implies_Equation430 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation430 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (y ◇ y)))]

theorem Equation430_4512_implies_Equation4 (G : Type*) [Magma G] (h430 : Equation430 G) (h4512 : Equation4512 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h430 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h430 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h430 sK1 sK0]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h430 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l5 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l3 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))]
  have l7 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1, 2]; rw [l2 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2, 2]; rw [← l5 sK0 sK1]
  have l8 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ sK1) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← l5 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 (sK0 ◇ sK1) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l6 sK0 sK1]
  have l10 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1, 2]; rw [l9 sK0 sK1]
  have l11 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h430 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l10 sK1 sK0]
  have l12 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l11 sK1 sK0]
    conv => enter [1, 2]; rw [l8 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l12 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ sK0)]
  have l14 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l14 x y]

@[equational_result]
theorem Equation4_implies_Equation431 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation431 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (y ◇ z)))]

@[equational_result]
theorem Equation431_implies_Equation4 (G : Type*) [Magma G] (h431 : Equation431 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h431 X0 X1 X1]
    conv => enter [1]; rw [← h431 X1 X0 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation433 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation433 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (z ◇ y)))]

theorem Equation433_4512_implies_Equation4 (G : Type*) [Magma G] (h433 : Equation433 G) (h4512 : Equation4512 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h433 (X0 ◇ X1) X1 X0]
    conv => enter [1]; rw [← h433 X1 (X0 ◇ X1) (X0 ◇ X1)]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ ((X2 ◇ X0) ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2]; rw [← l0 X0 X2]
    conv => enter [1]; rw [← h433 X1 (X2 ◇ X0) X0]
  have l2 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2]; rw [h4512 X2 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [l1 X1 X2 X0]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [l2 X1 X2 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X0 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [← h433 X1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]

@[equational_result]
theorem Equation4_implies_Equation434 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation434 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (z ◇ z)))]

theorem Equation434_4512_implies_Equation4 (G : Type*) [Magma G] (h434 : Equation434 G) (h4512 : Equation4512 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h434 X0 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h434 X0 X1 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h434 (X0 ◇ X0) X1 X0]
    conv => enter [1]; rw [← h434 X1 (X0 ◇ X0) (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l4 x y]

@[equational_result]
theorem Equation4_implies_Equation435 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation435 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (z ◇ w)))]

@[equational_result]
theorem Equation435_implies_Equation4 (G : Type*) [Magma G] (h435 : Equation435 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h435 X0 X1 X1 X1]
    conv => enter [1]; rw [← h435 X1 X0 X0 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation437 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation437 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (x ◇ y)))]

theorem Equation437_4512_implies_Equation4 (G : Type*) [Magma G] (h437 : Equation437 G) (h4512 : Equation4512 G) : Equation4 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h437 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l1 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h437 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK1 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l1 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 ((sK0 ◇ sK1) ◇ sK0) X0]
  have l3 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h437 sK1 ((sK0 ◇ sK1) ◇ sK0)]
    conv => enter [1, 2, 2, 2]; rw [← l1 sK1 sK0]
  have l4 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l3 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) sK0 (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)]
  have l5 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ X0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l2 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l6 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l4 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 (sK0 ◇ sK1) sK0 sK1]
  have l7 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l6 sK1 sK0]
    conv => enter [1]; rw [← l5 sK1 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) sK0]
  have l8 : ∀ sK1 : G, sK1 = (sK1 ◇ sK1) := by
    intro sK1
    conv => enter [1]; rw [l7 sK1 sK1]
    conv => enter [1]; rw [← l5 sK1 sK1 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l8 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l10 : ∀ sK1 X0 : G, (sK1 ◇ X0) = (sK1 ◇ (sK1 ◇ X0)) := by
    intro sK1 X0
    conv => enter [1, 1]; rw [l8 sK1]
    conv => enter [1]; rw [← h4512 sK1 sK1 X0]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h437 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2, 2, 2]; rw [← l9 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1, 2]; rw [← l10 sK1 (sK0 ◇ sK1)]
  have l13 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← l12 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l13 x y]

@[equational_result]
theorem Equation4_implies_Equation438 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation438 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (x ◇ z)))]

@[equational_result]
theorem Equation438_implies_Equation4 (G : Type*) [Magma G] (h438 : Equation438 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h438 X0 X1 X1]
    conv => enter [1]; rw [← h438 X1 X0 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h438 X0 X0 X0]
    conv => enter [1]; rw [← h438 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [l0 X1 X0]
  intro x y
  conv => enter [1]; rw [← l2 x y]

@[equational_result]
theorem Equation4_implies_Equation441 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation441 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (y ◇ z)))]

@[equational_result]
theorem Equation441_implies_Equation4 (G : Type*) [Magma G] (h441 : Equation441 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h441 X0 X0 X1]
    conv => enter [1]; rw [← h441 X1 X0 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation443 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation443 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (z ◇ y)))]

theorem Equation443_4512_implies_Equation4 (G : Type*) [Magma G] (h443 : Equation443 G) (h4512 : Equation4512 G) : Equation4 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ (X0 ◇ (X1 ◇ X0)))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [h443 (X0 ◇ (X1 ◇ X0)) X0 X1]
    conv => enter [1]; rw [← h443 X2 (X0 ◇ (X1 ◇ X0)) X0]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ ((X1 ◇ X0) ◇ (X0 ◇ (X1 ◇ X0))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h4512 X0 (X1 ◇ X0) (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l0 X2 X0 X1]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X0)))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X1 X0 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [l1 X2 X0 X1]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [h443 X1 X0 X1]
    conv => enter [1]; rw [l2 X2 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l3 X0 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← h443 X1 X0 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]

@[equational_result]
theorem Equation4_implies_Equation445 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation445 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (z ◇ w)))]

@[equational_result]
theorem Equation445_implies_Equation4 (G : Type*) [Magma G] (h445 : Equation445 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h445 X0 X0 X1 X1]
    conv => enter [1]; rw [← h445 X1 X0 X0 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation447 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation447 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (x ◇ y)))]

theorem Equation447_4512_implies_Equation4 (G : Type*) [Magma G] (h447 : Equation447 G) (h4512 : Equation4512 G) : Equation4 G := by
  have l0 : ∀ sK1 X0 sK0 : G, sK1 = (sK1 ◇ ((X0 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h447 sK1 (X0 ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1, 2, 2]; rw [← h447 sK0 sK1 X0]
  have l1 : ∀ sK1 X0 sK0 : G, sK1 = (sK1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l0 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← h4512 X0 (sK0 ◇ sK1) sK0]
  have l2 : ∀ X0 sK0 sK1 : G, (X0 ◇ (((sK0 ◇ sK1) ◇ sK0) ◇ sK1)) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2]; rw [l1 sK1 X0 sK0]
    conv => enter [1]; rw [← h447 X0 ((sK0 ◇ sK1) ◇ sK0) sK1]
  have l3 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2]; rw [h4512 (sK0 ◇ sK1) sK0 sK1]
    conv => enter [1]; rw [l2 X0 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h447 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l3 sK1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation4_implies_Equation448 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation448 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (x ◇ z)))]

@[equational_result]
theorem Equation448_implies_Equation4 (G : Type*) [Magma G] (h448 : Equation448 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h448 X0 (X0 ◇ X1) X1]
    conv => enter [1]; rw [← h448 X1 X0 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation449 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation449 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (x ◇ w)))]

@[equational_result]
theorem Equation449_implies_Equation4 (G : Type*) [Magma G] (h449 : Equation449 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h449 X0 X1 X1 X1]
    conv => enter [1]; rw [← h449 X1 X0 X1 (X0 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation451 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation451 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (y ◇ y)))]

@[equational_result]
theorem Equation451_implies_Equation4 (G : Type*) [Magma G] (h451 : Equation451 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h451 (X0 ◇ X0) X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h451 X1 (X0 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h451 X1 X0 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation4_implies_Equation453 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation453 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (y ◇ w)))]

@[equational_result]
theorem Equation453_implies_Equation4 (G : Type*) [Magma G] (h453 : Equation453 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h453 X0 X1 X0 X1]
    conv => enter [1]; rw [← h453 X1 X0 X1 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation456 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation456 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (z ◇ z)))]

theorem Equation456_4512_implies_Equation4 (G : Type*) [Magma G] (h456 : Equation456 G) (h4512 : Equation4512 G) : Equation4 G := by
  have l0 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2]; rw [h456 (X0 ◇ (X1 ◇ (X1 ◇ X1))) X0 X1]
    conv => enter [1]; rw [← h456 X2 X3 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l1 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 (X1 ◇ (X1 ◇ X1)) (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l0 X2 X3 X0 X1]
  have l2 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))))))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 (X1 ◇ X1) (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l1 X2 X3 X0 X1]
  have l3 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))))))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X1 X1 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l2 X2 X3 X0 X1]
  have l4 : ∀ X2 X3 X0 X1 : G, (X2 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1))))) = X2 := by
    intro X2 X3 X0 X1
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h456 X1 X0 X1]
    conv => enter [1]; rw [l3 X2 X3 X0 X1]
  have l5 : ∀ X2 X3 : G, (X2 ◇ X3) = X2 := by
    intro X2 X3
    conv => enter [1, 2]; rw [h456 X3 X2 X2]
    conv => enter [1]; rw [l4 X2 X3 X2 X2]
  intro x y
  conv => enter [1]; rw [← l5 x y]

@[equational_result]
theorem Equation4_implies_Equation457 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation457 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (z ◇ w)))]

@[equational_result]
theorem Equation457_implies_Equation4 (G : Type*) [Magma G] (h457 : Equation457 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h457 X0 X1 X1 X1]
    conv => enter [1]; rw [← h457 X1 X0 X1 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation459 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation459 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (w ◇ y)))]

@[equational_result]
theorem Equation459_implies_Equation4 (G : Type*) [Magma G] (h459 : Equation459 G) : Equation4 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [h459 (X0 ◇ X1) X1 X2 X0]
    conv => enter [1]; rw [← h459 X2 (X0 ◇ X1) X1 X2]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0 X1 (X1 ◇ X0)]
    conv => enter [1]; rw [← h459 X1 X0 X1 X1]
  intro x y
  conv => enter [1]; rw [← l1 x y]

@[equational_result]
theorem Equation4_implies_Equation460 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation460 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (w ◇ z)))]

@[equational_result]
theorem Equation460_implies_Equation4 (G : Type*) [Magma G] (h460 : Equation460 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h460 X0 (X1 ◇ X1) X1 X1]
    conv => enter [1]; rw [← h460 X1 X0 (X1 ◇ X1) X1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation461 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation461 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (w ◇ w)))]

@[equational_result]
theorem Equation461_implies_Equation4 (G : Type*) [Magma G] (h461 : Equation461 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h461 X0 X1 (X1 ◇ X1) X1]
    conv => enter [1]; rw [← h461 X1 X0 X1 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation462 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation462 G := by
  intro x y z w u
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (w ◇ u)))]

@[equational_result]
theorem Equation462_implies_Equation4 (G : Type*) [Magma G] (h462 : Equation462 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h462 X0 X1 X1 X1 X1]
    conv => enter [1]; rw [← h462 X1 X0 X1 X1 (X1 ◇ X1)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation4_implies_Equation4696 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4696 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ (x ◇ (x ◇ (x ◇ y))))]

theorem Equation4512_4696_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4696 : Equation4696 G) : Equation4 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) X2]
    conv => enter [1, 1]; rw [← h4696 X0 X1]
  have l1 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l0 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X0 ◇ (X0 ◇ X1))) X2]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l1 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X1)) X2]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l5 : ∀ X0 X2 : G, (X0 ◇ X2) = X0 := by
    intro X0 X2
    conv => enter [1]; rw [l4 X0 X2 X0]
    conv => enter [1]; rw [← h4696 X0 (X0 ◇ X2)]
  intro x y
  conv => enter [1]; rw [← l5 x y]

@[equational_result]
theorem Equation4_implies_Equation4698 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4698 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ (x ◇ (x ◇ (y ◇ y))))]

theorem Equation4512_4698_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4698 : Equation4698 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h4698 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h4698 (X0 ◇ X0) X0]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [h4698 (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← l1 (X0 ◇ X0)]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [l2 X0]
    conv => enter [1]; rw [← h4512 X0 X0 ((X0 ◇ X0) ◇ (X0 ◇ X0))]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l4 X0]
    conv => enter [1]; rw [← h4698 X0 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [l6 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [← h4698 X0 X1]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l6 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l7 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l6 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l8 X0 X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l5 X1]
    conv => enter [1]; rw [l9 X0 X1]
  have l11 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l10 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l6 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l11 x y]

@[equational_result]
theorem Equation4_implies_Equation4699 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4699 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (x ◇ (x ◇ (x ◇ (y ◇ z))))]

theorem Equation4512_4699_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4699 : Equation4699 G) : Equation4 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))) X3]
    conv => enter [1, 1]; rw [← h4699 X0 X1 X2]
  have l1 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l0 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X0 ◇ (X1 ◇ X2))) X3]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l1 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ X2)) X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l4 : ∀ X0 X3 : G, (X0 ◇ X3) = X0 := by
    intro X0 X3
    conv => enter [1]; rw [l3 X0 X3 X0 X0]
    conv => enter [1]; rw [← h4699 X0 (X0 ◇ X0) X3]
  intro x y
  conv => enter [1]; rw [← l4 x y]

@[equational_result]
theorem Equation4_implies_Equation4701 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4701 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ (x ◇ (y ◇ (x ◇ y))))]

theorem Equation4512_4701_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4701 : Equation4701 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4701 X0 X1]
    conv => enter [1]; rw [← h4701 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1))))]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X1)))) X2]
    conv => enter [1, 1]; rw [← h4701 X0 X1]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X0 ◇ X1))) X2]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X0 ◇ X1))) X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X1)) X2]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0)))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l3 X0 X1]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0))))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l5 X0 X1]
  have l8 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l7 X0 X1]
  have l10 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [l8 X0 X0 X0]
    conv => enter [1]; rw [l9 X0 X0]
  have l11 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [← l10 X0]
    conv => enter [1]; rw [← h4701 X0 X0]
  have l12 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)))) = X0 := by
    intro X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l10 X0]
    conv => enter [1]; rw [← h4701 X0 (X0 ◇ (X0 ◇ X0))]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l10 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l14 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))))) = X0 := by
    intro X0
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [l12 X0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1, 2]; rw [l11 sK1]
  have l16 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := by
    intro X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 X0 X0]
    conv => enter [1]; rw [l14 X0]
  have l17 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l8 X0 X0 X0]
    conv => enter [1]; rw [l16 X0]
  have l18 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l19 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l17 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l20 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l17 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l21 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4701 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l18 sK0 sK1 (sK0 ◇ sK1)]
  have l22 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4701 (sK0 ◇ sK1) (sK1 ◇ X0)]
    conv => enter [1, 2, 2, 2, 2]; rw [← l18 sK0 sK1 X0]
  have l23 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l22 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← l19 (sK0 ◇ sK1) ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0))]
  have l24 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l21 sK1 sK0]
    conv => enter [1, 2]; rw [← l19 sK1 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l25 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l23 sK0 sK1 X0]
    conv => enter [1]; rw [← l19 (sK0 ◇ sK1) ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0))]
  have l26 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l24 sK1 sK0]
    conv => enter [1]; rw [← l19 sK1 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))]
  have l27 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l25 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 ((sK0 ◇ sK1) ◇ X0)]
  have l28 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l26 sK1 sK0]
    conv => enter [1, 2]; rw [l17 (sK0 ◇ sK1)]
  have l29 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l27 sK0 sK1 X0]
    conv => enter [1]; rw [← l18 sK0 sK1 (X0 ◇ ((sK0 ◇ sK1) ◇ X0))]
  have l30 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l29 sK0 sK1 X0]
    conv => enter [1]; rw [← l20 (sK0 ◇ sK1) X0]
  have l31 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l28 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) X0]
  have l32 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l31 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← l30 sK0 sK1 X0]
  have l33 : ∀ sK1 X0 : G, sK1 = (sK1 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l28 sK1 sK1]
    conv => enter [1]; rw [← l32 sK1 X0 sK1]
  have l34 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ (X0 ◇ sK1))) = X0 := by
    intro X0 sK1
    conv => enter [1, 2, 2, 2]; rw [l33 sK1 (X0 ◇ sK1)]
    conv => enter [1]; rw [← h4701 X0 sK1]
  have l35 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ sK1)) = X0 := by
    intro X0 sK1
    conv => enter [1, 2]; rw [l19 X0 sK1]
    conv => enter [1]; rw [l34 X0 sK1]
  have l36 : ∀ X0 sK1 : G, (X0 ◇ sK1) = X0 := by
    intro X0 sK1
    conv => enter [1]; rw [l19 X0 sK1]
    conv => enter [1]; rw [l35 X0 sK1]
  intro x y
  conv => enter [1]; rw [← l36 x y]

@[equational_result]
theorem Equation4_implies_Equation4702 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4702 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (x ◇ (x ◇ (y ◇ (x ◇ z))))]

theorem Equation4512_4702_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4702 : Equation4702 G) : Equation4 G := by
  have l0 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X3)) := by
    intro X0 X3 X1 X2
    conv => enter [1, 1]; rw [h4702 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X2)))) X3]
  have l1 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l0 X0 X3 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X0 ◇ X2))) X3]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l1 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X0 ◇ X2)) X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ X2) X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X2 X3]
  have l5 : ∀ X0 X3 : G, (X0 ◇ X3) = X0 := by
    intro X0 X3
    conv => enter [1]; rw [l4 X0 X3 X0 X0]
    conv => enter [1]; rw [← h4702 X0 X0 (X0 ◇ X3)]
  intro x y
  conv => enter [1]; rw [← l5 x y]

@[equational_result]
theorem Equation4_implies_Equation4704 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4704 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ (x ◇ (y ◇ (y ◇ y))))]

theorem Equation4512_4704_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4704 : Equation4704 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = ((X0 ◇ (X0 ◇ X0)) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0
    conv => enter [1]; rw [h4704 (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0))]
    conv => enter [1, 2, 2]; rw [← h4704 (X0 ◇ (X0 ◇ X0)) X0]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X1)))) X2]
    conv => enter [1, 1]; rw [← h4704 X0 X1]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X1))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1))) X2]
  have l3 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ ((X0 ◇ X0) ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X1)) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X1)) X2]
  have l5 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))))) := by
    intro X0
    conv => enter [1]; rw [l3 X0]
    conv => enter [1, 2]; rw [← h4512 X0 X0 ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ (X0 ◇ X0)))]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ X1) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X1 ◇ X1) X2]
  have l7 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ (X0 ◇ X0))))))) := by
    intro X0
    conv => enter [1]; rw [l5 X0]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X0 ◇ X0) (X0 ◇ (X0 ◇ X0))]
  have l8 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X1 X2]
  have l9 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))))) := by
    intro X0
    conv => enter [1]; rw [l7 X0]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X0 (X0 ◇ (X0 ◇ X0))]
  have l10 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l9 X0]
    conv => enter [1, 2, 2]; rw [← l8 X0 X0 X0]
  have l11 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [l10 X0]
    conv => enter [1]; rw [← h4704 X0 X0]
  have l12 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l10 X0]
    conv => enter [1]; rw [l11 X0]
  have l13 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [← l12 X0]
    conv => enter [1]; rw [← h4704 X0 X0]
  have l14 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [← l13 X0]
    conv => enter [1]; rw [← h4704 X1 X0]
  have l15 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l13 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l16 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l15 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l17 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l16 X0 X1]
    conv => enter [1]; rw [l14 X0 X1]
  intro x y
  conv => enter [1]; rw [← l17 x y]

@[equational_result]
theorem Equation4_implies_Equation4705 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4705 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (x ◇ (x ◇ (y ◇ (y ◇ z))))]

theorem Equation4512_4705_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4705 : Equation4705 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4705 X0 X1 X1]
    conv => enter [1]; rw [← h4705 X1 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ X2)))) X3]
    conv => enter [1, 1]; rw [← h4705 X0 X1 X2]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l1 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ X2))) X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ X2)) X3]
  have l4 : ∀ X0 X3 : G, (X0 ◇ X3) = X0 := by
    intro X0 X3
    conv => enter [1]; rw [l3 X0 X3 X0 X0]
    conv => enter [1]; rw [l0 X0 ((X0 ◇ (X0 ◇ X0)) ◇ X3)]
  intro x y
  conv => enter [1]; rw [← l4 x y]

@[equational_result]
theorem Equation4_implies_Equation4707 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4707 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (x ◇ (x ◇ (y ◇ (z ◇ y))))]

theorem Equation4512_4707_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4707 : Equation4707 G) : Equation4 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X1)))) X3]
    conv => enter [1, 1]; rw [← h4707 X0 X1 X2]
  have l1 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l0 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ X1))) X3]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l1 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X1)) X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X2 ◇ X1) X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X2 X1 X3]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4707 (sK0 ◇ sK1) (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h4707 (sK0 ◇ sK1) sK1 sK0]
  have l6 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l7 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ (((sK0 ◇ sK1) ◇ X0) ◇ ((sK0 ◇ sK1) ◇ X0))))) = X1 := by
    intro X1 sK0 sK1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [l6 sK0 sK1 X0]
    conv => enter [1]; rw [← h4707 X1 ((sK0 ◇ sK1) ◇ X0) (sK0 ◇ sK1)]
  have l8 : ∀ X1 sK0 sK1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ ((sK0 ◇ sK1) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0)))))) = X1 := by
    intro X1 sK0 sK1 X0
    conv => enter [1, 2, 2, 2]; rw [h4512 (sK0 ◇ sK1) X0 ((sK0 ◇ sK1) ◇ X0)]
    conv => enter [1]; rw [l7 X1 sK0 sK1 X0]
  have l9 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0 (X1 ◇ X1) X0]
    conv => enter [1]; rw [l8 X1 X1 X1 X0]
  intro x y
  conv => enter [1]; rw [← l9 x y]

@[equational_result]
theorem Equation4_implies_Equation4708 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4708 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (x ◇ (x ◇ (y ◇ (z ◇ z))))]

theorem Equation4512_4708_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4708 : Equation4708 G) : Equation4 G := by
  have l0 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))))) = X3 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X1 (X2 ◇ X2)]
    conv => enter [1]; rw [← h4708 X3 (X0 ◇ X1) X2]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4708 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h4708 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X2)))) X3]
    conv => enter [1, 1]; rw [← h4708 X0 X1 X2]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l2 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ X2))) X3]
  have l4 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2))))) = X3 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2, 2, 2, 2, 2]; rw [← l1 X2]
    conv => enter [1]; rw [l0 X3 X0 X1 X2]
  have l5 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X2)) X3]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l5 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X2 ◇ X2) X3]
  have l7 : ∀ X0 X3 : G, (X0 ◇ X3) = X0 := by
    intro X0 X3
    conv => enter [1]; rw [l6 X0 X3 X0 X0]
    conv => enter [1]; rw [l4 X0 X0 (X0 ◇ X0) X3]
  intro x y
  conv => enter [1]; rw [← l7 x y]

@[equational_result]
theorem Equation4_implies_Equation4709 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4709 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (x ◇ (x ◇ (y ◇ (z ◇ w))))]

theorem Equation4512_4709_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4709 : Equation4709 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X1 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2, 2]; rw [h4709 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4709 X1 X0 X0 (X0 ◇ (X1 ◇ (X1 ◇ X1)))]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X4)) = (X0 ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))) X4]
    conv => enter [1, 1]; rw [← h4709 X0 X1 X2 X3]
  have l2 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l1 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ X3))) X4]
  have l3 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ X3)) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ X3)) X4]
  have l4 : ∀ X0 X4 : G, (X0 ◇ X4) = X0 := by
    intro X0 X4
    conv => enter [1]; rw [l3 X0 X4 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 ((X0 ◇ (X0 ◇ X0)) ◇ X4)]
  intro x y
  conv => enter [1]; rw [← l4 x y]

@[equational_result]
theorem Equation4_implies_Equation4711 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4711 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (x ◇ (x ◇ y))))]

theorem Equation4512_4711_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4711 : Equation4711 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ (X0 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4711 X0 X1]
    conv => enter [1]; rw [← h4711 X0 (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1))))]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X1)))) X2]
    conv => enter [1, 1]; rw [← h4711 X0 X1]
  have l2 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l1 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X0 ◇ (X0 ◇ X1))) X2]
  have l3 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X1))) ◇ (X0 ◇ X0))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 (X1 ◇ (X0 ◇ (X0 ◇ X1))) (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1]
  have l4 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l2 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X1)) X2]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X1)) ◇ (X0 ◇ X0)))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 (X0 ◇ (X0 ◇ X1)) (X0 ◇ X0)]
    conv => enter [1]; rw [l3 X0 X1]
  have l6 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l4 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X0 ◇ X1) X2]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X1) ◇ (X0 ◇ X0))))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X0 (X0 ◇ X1) (X0 ◇ X0)]
    conv => enter [1]; rw [l5 X0 X1]
  have l8 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l6 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [l7 X0 X1]
  have l10 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [l8 X0 X0 X0]
    conv => enter [1]; rw [l9 X0 X0]
  have l11 : ∀ X0 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2, 2]; rw [← l10 X0]
    conv => enter [1]; rw [← h4711 X0 (X0 ◇ X0)]
  have l12 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [← l10 X0]
    conv => enter [1]; rw [← h4711 X0 X0]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l10 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l14 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h4512 X0 X0 X0]
    conv => enter [1]; rw [l11 X0]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1, 2]; rw [l12 sK1]
  have l16 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l10 X0]
    conv => enter [1]; rw [l14 X0]
  have l17 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l15 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l18 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l16 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l19 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l16 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l20 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4711 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2]; rw [← l17 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l21 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4711 (sK0 ◇ sK1) (sK1 ◇ X0)]
    conv => enter [1, 2, 2, 2, 2]; rw [← l17 sK0 sK1 X0]
  have l22 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l21 sK0 sK1 X0]
    conv => enter [1]; rw [← l18 (sK0 ◇ sK1) ((sK1 ◇ X0) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)))]
  have l23 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l20 sK1 sK0]
    conv => enter [1]; rw [← l18 sK1 ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l24 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0))))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l22 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK1 X0 ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0))]
  have l25 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l23 sK1 sK0]
    conv => enter [1]; rw [← l19 sK1 (sK0 ◇ sK1)]
  have l26 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l24 sK0 sK1 X0]
    conv => enter [1]; rw [← l17 sK0 sK1 (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)))]
  have l27 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l26 sK0 sK1 X0]
    conv => enter [1, 2, 2]; rw [← l18 (sK0 ◇ sK1) X0]
  have l28 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l27 sK0 sK1 X0]
    conv => enter [1]; rw [← l19 (sK0 ◇ sK1) X0]
  have l29 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK1 X0 sK0
    conv => enter [1, 1]; rw [l25 sK1 sK0]
    conv => enter [1]; rw [← h4512 sK1 (sK0 ◇ sK1) X0]
  have l30 : ∀ sK1 X0 sK0 : G, (sK1 ◇ X0) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [l29 sK1 X0 sK0]
    conv => enter [1, 2]; rw [← l28 sK0 sK1 X0]
  have l31 : ∀ sK1 X0 : G, sK1 = (sK1 ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [l25 sK1 sK1]
    conv => enter [1]; rw [← l30 sK1 X0 sK1]
  have l32 : ∀ X0 sK1 : G, (X0 ◇ (X0 ◇ sK1)) = X0 := by
    intro X0 sK1
    conv => enter [1, 2, 2]; rw [l31 sK1 (X0 ◇ (X0 ◇ sK1))]
    conv => enter [1]; rw [← h4711 X0 sK1]
  have l33 : ∀ X0 sK1 : G, (X0 ◇ sK1) = X0 := by
    intro X0 sK1
    conv => enter [1]; rw [l18 X0 sK1]
    conv => enter [1]; rw [l32 X0 sK1]
  intro x y
  conv => enter [1]; rw [← l33 x y]

@[equational_result]
theorem Equation4_implies_Equation4712 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4712 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (x ◇ (x ◇ z))))]

theorem Equation4512_4712_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4712 : Equation4712 G) : Equation4 G := by
  have l0 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X3)) := by
    intro X0 X3 X1 X2
    conv => enter [1, 1]; rw [h4712 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X2)))) X3]
  have l1 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l0 X0 X3 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X0 ◇ (X0 ◇ X2))) X3]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l1 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ (X0 ◇ X2)) X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X0 ◇ X2) X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X2 X3]
  have l5 : ∀ X0 X3 : G, (X0 ◇ X3) = X0 := by
    intro X0 X3
    conv => enter [1]; rw [l4 X0 X3 X0 X0]
    conv => enter [1]; rw [← h4712 X0 X0 (X0 ◇ X3)]
  intro x y
  conv => enter [1]; rw [← l5 x y]

@[equational_result]
theorem Equation4_implies_Equation4714 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4714 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (x ◇ (y ◇ y))))]

theorem Equation4512_4714_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4714 : Equation4714 G) : Equation4 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h4714 sK1 sK0]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4714 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h4512 sK0 sK1 sK1]
  have l3 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) ◇ X0)) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1)) X0]
    conv => enter [1, 1]; rw [← l2 sK0 sK1]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l3 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) ((sK0 ◇ sK1) ◇ sK1) X0]
  have l5 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l4 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)))]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1))) = (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2, 2, 2]; rw [l0 sK1 sK0]
    conv => enter [1]; rw [← l5 sK0 (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) sK1]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1))) = (sK0 ◇ (sK1 ◇ (X0 ◇ (sK1 ◇ (X0 ◇ X0))))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2, 2, 2]; rw [h4714 sK1 X0]
    conv => enter [1]; rw [← l5 sK0 (sK1 ◇ (X0 ◇ (sK1 ◇ (X0 ◇ X0)))) sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1, 2, 2]; rw [← l6 sK0 sK1]
  have l10 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l8 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (sK1 ◇ (X0 ◇ X0)))]
  have l11 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK1))) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))]
  have l12 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ sK1) ◇ (X0 ◇ (sK1 ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l10 sK0 sK1 X0]
  have l13 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l11 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [l12 sK0 sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l5 sK0 ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) sK1]
  have l15 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4714 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 2, 2, 2]; rw [← l14 sK0 sK1]
  have l16 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l15 sK0 sK1]
    conv => enter [1, 2]; rw [l9 sK0 sK1]
  have l17 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l16 sK0 sK0]
    conv => enter [1, 2]; rw [← l14 sK0 sK0]
  have l18 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h4714 sK0 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l17 sK0]
  have l19 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l18 sK0]
    conv => enter [1, 2]; rw [← l17 sK0]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← l19 sK0]
  have l21 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l19 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  have l22 : ∀ sK0 sK1 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1))) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1, 2, 2]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [← l5 sK0 ((sK0 ◇ sK1) ◇ sK0) sK1]
  have l23 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [l22 sK0 sK1]
  have l24 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l19 sK0]
    conv => enter [1]; rw [l23 sK0 sK1]
  have l25 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [l21 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l26 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l24 sK0 sK1]
    conv => enter [1]; rw [← l25 sK0 sK1 sK0]
  have l27 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4714 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2, 2]; rw [← l25 sK0 sK1 (sK0 ◇ sK0)]
  have l28 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1, 2]; rw [← l13 sK0 sK1]
  have l29 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l26 sK0 sK1]
    conv => enter [1]; rw [← l28 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l29 x y]

@[equational_result]
theorem Equation4_implies_Equation4715 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4715 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (x ◇ (y ◇ z))))]

theorem Equation4512_4715_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4715 : Equation4715 G) : Equation4 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))) X3]
    conv => enter [1, 1]; rw [← h4715 X0 X1 X2]
  have l1 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l0 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X0 ◇ (X1 ◇ X2))) X3]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l1 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ (X1 ◇ X2)) X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X1 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X1 ◇ X2) X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ (X1 ◇ (X2 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l5 : ∀ X0 X3 : G, (X0 ◇ X3) = X0 := by
    intro X0 X3
    conv => enter [1]; rw [l4 X0 X3 X0 X0]
    conv => enter [1]; rw [← h4715 X0 X0 (X0 ◇ X3)]
  intro x y
  conv => enter [1]; rw [← l5 x y]

@[equational_result]
theorem Equation4_implies_Equation4717 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4717 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (x ◇ (z ◇ y))))]

theorem Equation4512_4717_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4717 : Equation4717 G) : Equation4 G := by
  have l0 : ∀ sK0 X0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h4717 sK0 X0 sK1]
    conv => enter [1, 2, 2, 2]; rw [h4512 sK0 sK1 X0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h4717 sK0 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l0 sK0 sK0 sK0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ X0) = (sK0 ◇ (sK0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [l1 sK0]
    conv => enter [1]; rw [← h4512 sK0 sK0 X0]
  have l3 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [l2 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
    conv => enter [1, 2]; rw [← l2 sK0 ((sK0 ◇ sK1) ◇ sK0)]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4717 sK0 sK1 sK0]
    conv => enter [1]; rw [← l2 sK0 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l6 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l7 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1]
    conv => enter [1]; rw [← l2 sK0 ((sK0 ◇ sK1) ◇ sK0)]
  have l8 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l6 sK0 sK1]
    conv => enter [1, 2]; rw [← l2 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1]
    conv => enter [1]; rw [← l3 sK0 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4717 (sK0 ◇ sK1) sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l8 sK0 sK1]
  have l11 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
  have l12 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l10 sK0 sK1]
    conv => enter [1]; rw [← l11 sK0 (sK1 ◇ sK0) sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l14 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l13 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l14 x y]

@[equational_result]
theorem Equation4_implies_Equation4718 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4718 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (x ◇ (z ◇ z))))]

theorem Equation4512_4718_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4718 : Equation4718 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h4718 X0 (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h4718 X0 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h4718 X0 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  have l4 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [l1 X0 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l4 (X0 ◇ (X1 ◇ X1))]
    conv => enter [1]; rw [← h4718 X0 (X0 ◇ (X1 ◇ X1)) X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l3 X0 (X1 ◇ X1)]
    conv => enter [1]; rw [l5 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l4 X1]
    conv => enter [1]; rw [l6 X0 X1]
  intro x y
  conv => enter [1]; rw [← l7 x y]

@[equational_result]
theorem Equation4_implies_Equation4719 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4719 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (x ◇ (z ◇ w))))]

theorem Equation4512_4719_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4719 : Equation4719 G) : Equation4 G := by
  have l0 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) ◇ X4)) = (X0 ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X0 ◇ (X2 ◇ X3)))) X4]
    conv => enter [1, 1]; rw [← h4719 X0 X1 X2 X3]
  have l1 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X0 ◇ ((X1 ◇ (X0 ◇ (X2 ◇ X3))) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l0 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X0 ◇ (X2 ◇ X3))) X4]
  have l2 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X2 ◇ X3)) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X0 ◇ (X2 ◇ X3)) X4]
  have l3 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ ((X2 ◇ X3) ◇ X4))))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X2 ◇ X3) X4]
  have l4 : ∀ X0 X4 : G, (X0 ◇ X4) = X0 := by
    intro X0 X4
    conv => enter [1]; rw [l3 X0 X4 X0 X0 X0]
    conv => enter [1]; rw [← h4719 X0 X0 (X0 ◇ X0) X4]
  intro x y
  conv => enter [1]; rw [← l4 x y]

@[equational_result]
theorem Equation4_implies_Equation4721 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4721 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (y ◇ (x ◇ y))))]

theorem Equation4512_4721_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4721 : Equation4721 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4721 X0 X1]
    conv => enter [1]; rw [← h4721 X0 (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1))))]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4721 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK1 ◇ (sK0 ◇ sK1))]
  have l2 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) X2]
    conv => enter [1, 1]; rw [← h4721 X0 X1]
  have l3 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l2 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ (X0 ◇ X1))) X2]
  have l4 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 (X1 ◇ (X1 ◇ (X0 ◇ X1))) ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X2)))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l3 X0 X2 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ (X0 ◇ X1)) X2]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 (X1 ◇ (X0 ◇ X1)) ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)]
    conv => enter [1]; rw [l4 X0 X1]
  have l7 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X2))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l5 X0 X2 X1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X0 ◇ X1) X2]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X1 (X0 ◇ X1) ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)]
    conv => enter [1]; rw [l6 X0 X1]
  have l9 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X2)))))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [l7 X0 X2 X1]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X2]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)))))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0)]
    conv => enter [1]; rw [l8 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1, 2]; rw [l9 X0 ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X1)))) ◇ X0) X1]
    conv => enter [1]; rw [l10 X0 X1]
  have l12 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X1))) ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 (X1 ◇ (X1 ◇ (X0 ◇ X1))) X0]
    conv => enter [1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X0 ◇ X1)) ◇ X0))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 (X1 ◇ (X0 ◇ X1)) X0]
    conv => enter [1]; rw [l12 X0 X1]
  have l14 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X0 ◇ X1) ◇ X0)))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X1 (X0 ◇ X1) X0]
    conv => enter [1]; rw [l13 X0 X1]
  have l15 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0))))))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 X0]
    conv => enter [1]; rw [l14 X0 X1]
  have l16 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l9 X0 X0 X0]
    conv => enter [1]; rw [l15 X0 X0]
  have l17 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2, 2]; rw [← l16 X0]
    conv => enter [1]; rw [← h4721 X0 X0]
  have l18 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l16 X0]
    conv => enter [1]; rw [l17 X0]
  have l19 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l18 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l20 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [← l18 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK1]
  have l21 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l20 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK1 X0]
  have l22 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4721 sK0 ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2, 2, 2, 2]; rw [← l1 sK0 sK1]
  have l23 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ X0)) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← l1 sK0 sK1]
  have l24 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l23 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l25 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l22 sK0 sK1]
    conv => enter [1]; rw [← l19 sK0 (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK0))]
  have l26 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l24 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 (sK0 ◇ sK1) X0]
  have l27 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l25 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1)) (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK0)]
  have l28 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l26 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← l21 sK0 sK1 ((sK0 ◇ sK1) ◇ X0)]
  have l29 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK0))))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l27 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 (sK0 ◇ sK1) (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK0)]
  have l30 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l28 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← l19 (sK0 ◇ sK1) X0]
  have l31 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l29 sK0 sK1]
    conv => enter [1, 2]; rw [← l21 sK0 sK1 ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK0))]
  have l32 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l31 sK0 sK1]
    conv => enter [1]; rw [← l30 sK0 ((sK0 ◇ sK1) ◇ (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK0)) sK1]
  have l33 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l32 sK0 sK1]
    conv => enter [1]; rw [← l30 sK0 (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ sK0) sK1]
  have l34 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l33 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ (sK0 ◇ sK1)) sK0]
  have l35 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l34 sK0 sK1]
    conv => enter [1]; rw [← l30 sK0 ((sK1 ◇ (sK0 ◇ sK1)) ◇ sK0) sK1]
  have l36 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l35 sK0 sK1]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ sK1) sK0]
  have l37 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l36 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 ((sK0 ◇ sK1) ◇ sK0)]
  have l38 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l37 sK0 sK1]
    conv => enter [1]; rw [← l19 (sK0 ◇ sK1) sK0]
  have l39 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4721 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l38 sK0 sK1]
  have l40 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l38 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l41 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l39 sK0 sK1]
    conv => enter [1]; rw [← l19 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ sK0))]
  have l42 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l41 sK0 sK1]
    conv => enter [1]; rw [← l40 sK0 (sK0 ◇ sK0) sK1]
  have l43 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l16 sK0]
    conv => enter [1]; rw [← l42 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l43 x y]

@[equational_result]
theorem Equation4_implies_Equation4722 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4722 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (y ◇ (x ◇ z))))]

theorem Equation4512_4722_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4722 : Equation4722 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4722 X0 X1 X1]
    conv => enter [1]; rw [← h4722 X1 X0 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) ◇ X3)) := by
    intro X0 X3 X1 X2
    conv => enter [1, 1]; rw [h4722 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ X2)))) X3]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X0 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l1 X0 X3 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ (X0 ◇ X2))) X3]
  have l3 : ∀ X0 X3 : G, (X0 ◇ X3) = X0 := by
    intro X0 X3
    conv => enter [1]; rw [l2 X0 X3 X0 X0]
    conv => enter [1]; rw [l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X3)]
  intro x y
  conv => enter [1]; rw [← l3 x y]

@[equational_result]
theorem Equation4_implies_Equation4724 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4724 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (y ◇ (y ◇ y))))]

theorem Equation4512_4724_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4724 : Equation4724 G) : Equation4 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4724 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK1 ◇ (sK1 ◇ sK1))]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) ◇ X0)) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← l0 sK0 sK1]
  have l2 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK1 ◇ sK1)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l1 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 (sK0 ◇ sK1) (sK1 ◇ (sK1 ◇ sK1)) X0]
  have l3 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ ((sK1 ◇ sK1) ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l2 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK1 (sK1 ◇ sK1) X0]
  have l4 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ X0))))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l3 sK0 X0 sK1]
    conv => enter [1, 2, 2, 2]; rw [← h4512 sK1 sK1 X0]
  have l5 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = (sK0 ◇ (sK1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0))))) := by
    intro sK0 sK1 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4724 sK1 X0]
    conv => enter [1]; rw [← l4 sK0 (sK1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) sK1]
  have l6 : ∀ sK0 sK1 X0 : G, (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ sK1)))) = ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l5 sK0 sK1 X0]
    conv => enter [1]; rw [h4512 sK0 sK1 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l7 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ sK1) ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l6 sK0 sK1 X0]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [← l7 sK0 sK1 sK1]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4724 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← l7 sK0 sK1 sK0]
  have l10 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l11 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l7 sK0 sK1 sK0]
    conv => enter [1, 2, 2, 2]; rw [← l8 sK0 sK1]
  have l12 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l11 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 sK1 (sK0 ◇ (sK0 ◇ sK1))]
  have l13 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 sK1 (sK0 ◇ sK1)]
  have l14 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2, 2, 2]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← h4724 X0 (sK0 ◇ sK1)]
  have l15 : ∀ X0 sK0 sK1 : G, (X0 ◇ (X0 ◇ ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2, 2]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [l14 X0 sK0 sK1]
  have l16 : ∀ X0 sK0 : G, (X0 ◇ (X0 ◇ sK0)) = X0 := by
    intro X0 sK0
    conv => enter [1, 2, 2]; rw [l13 sK0 X0]
    conv => enter [1]; rw [l15 X0 sK0 X0]
  have l17 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l16 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [← l9 sK0 sK1]
  have l18 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l17 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l18 x y]

@[equational_result]
theorem Equation4_implies_Equation4725 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4725 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (y ◇ (y ◇ z))))]

theorem Equation4512_4725_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4725 : Equation4725 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4725 X0 X0 X1]
    conv => enter [1]; rw [← h4725 X1 X0 (X0 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ (X1 ◇ X2)))) X3]
    conv => enter [1, 1]; rw [← h4725 X0 X1 X2]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l1 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ (X1 ◇ X2))) X3]
  have l3 : ∀ X0 X3 : G, (X0 ◇ X3) = X0 := by
    intro X0 X3
    conv => enter [1]; rw [l2 X0 X3 X0 X0]
    conv => enter [1]; rw [l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X3)]
  intro x y
  conv => enter [1]; rw [← l3 x y]

@[equational_result]
theorem Equation4_implies_Equation4727 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4727 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (y ◇ (z ◇ y))))]

theorem Equation4512_4727_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4727 : Equation4727 G) : Equation4 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X1)))) X3]
    conv => enter [1, 1]; rw [← h4727 X0 X1 X2]
  have l1 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X1))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l0 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ (X2 ◇ X1))) X3]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ ((X1 ◇ (X2 ◇ X1)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l1 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X1 ◇ (X2 ◇ X1)) X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ ((X2 ◇ X1) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X1 (X2 ◇ X1) X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X2 X1 X3]
  have l5 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ ((sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))))) = X0 := by
    intro X0 sK1 sK0
    conv => enter [1, 2, 2, 2]; rw [h4727 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) sK1 sK0]
    conv => enter [1]; rw [← h4727 X0 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))) (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
  have l6 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1))))))) = X0 := by
    intro X0 sK1 sK0
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK1 ◇ (sK0 ◇ sK1)) (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l5 X0 sK1 sK0]
  have l7 : ∀ X0 sK1 sK0 : G, (X0 ◇ (X0 ◇ (sK1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))))))) = X0 := by
    intro X0 sK1 sK0
    conv => enter [1, 2, 2, 2]; rw [h4512 sK1 (sK0 ◇ sK1) (sK1 ◇ (sK1 ◇ (sK0 ◇ sK1)))]
    conv => enter [1]; rw [l6 X0 sK1 sK0]
  have l8 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK0 ◇ sK1))) = X0 := by
    intro X0 sK1 sK0
    conv => enter [1]; rw [l4 X0 (sK1 ◇ (sK0 ◇ sK1)) sK1 (sK0 ◇ sK1)]
    conv => enter [1]; rw [l7 X0 sK1 sK0]
  have l9 : ∀ X1 sK1 sK0 X0 : G, (X1 ◇ (X1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)))) = X1 := by
    intro X1 sK1 sK0 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l8 X0 sK1 sK0]
    conv => enter [1]; rw [← h4727 X1 (sK1 ◇ (sK0 ◇ sK1)) X0]
  have l10 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ X1) = (X0 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X1)) := by
    intro X0 X1 sK1 sK0
    conv => enter [1, 1]; rw [← l8 X0 sK1 sK0]
    conv => enter [1]; rw [← h4512 X0 (sK1 ◇ (sK0 ◇ sK1)) X1]
  have l11 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l8 sK0 sK1 sK0]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ sK1)]
  have l12 : ∀ X0 X1 sK1 sK0 : G, (X0 ◇ X1) = (X0 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ X1))) := by
    intro X0 X1 sK1 sK0
    conv => enter [1]; rw [l10 X0 X1 sK1 sK0]
    conv => enter [1, 2]; rw [← h4512 sK1 (sK0 ◇ sK1) X1]
  have l13 : ∀ X1 sK1 sK0 X0 : G, (X1 ◇ (X1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0))))) = X1 := by
    intro X1 sK1 sK0 X0
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK0 ◇ sK1) ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0)]
    conv => enter [1]; rw [l9 X1 sK1 sK0 X0]
  have l14 : ∀ X1 sK1 sK0 X0 : G, (X1 ◇ (X1 ◇ ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0))) = X1 := by
    intro X1 sK1 sK0 X0
    conv => enter [1, 2]; rw [l12 X1 ((sK1 ◇ (sK0 ◇ sK1)) ◇ X0) sK1 sK0]
    conv => enter [1]; rw [l13 X1 sK1 sK0 X0]
  have l15 : ∀ X1 sK1 sK0 X0 : G, (X1 ◇ (X1 ◇ (sK1 ◇ ((sK0 ◇ sK1) ◇ X0)))) = X1 := by
    intro X1 sK1 sK0 X0
    conv => enter [1, 2, 2]; rw [h4512 sK1 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l14 X1 sK1 sK0 X0]
  have l16 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l12 X1 X0 X1 X1]
    conv => enter [1]; rw [l15 X1 X1 X1 X0]
  have l17 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ X0)) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l11 sK0 sK1]
  have l18 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l16 (sK0 ◇ sK1) X0]
    conv => enter [1]; rw [l17 sK0 sK1 X0]
  have l19 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l8 sK0 sK1 sK0]
    conv => enter [1]; rw [l18 sK0 (sK1 ◇ (sK0 ◇ sK1)) sK1]
  intro x y
  conv => enter [1]; rw [l19 x y]

@[equational_result]
theorem Equation4_implies_Equation4728 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4728 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (y ◇ (z ◇ z))))]

theorem Equation4512_4728_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4728 : Equation4728 G) : Equation4 G := by
  have l0 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ ((X0 ◇ (X0 ◇ (X1 ◇ X1))) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4728 (X0 ◇ (X0 ◇ (X1 ◇ X1))) X0 X1]
    conv => enter [1]; rw [← h4728 X2 (X0 ◇ (X0 ◇ (X1 ◇ X1))) (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h4728 (X0 ◇ X0) (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h4728 (X0 ◇ X0) (X0 ◇ X0) X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l1 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l3 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2]; rw [h4512 X0 (X0 ◇ (X1 ◇ X1)) (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l0 X2 X0 X1]
  have l4 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1)))))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 (X1 ◇ X1) (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l3 X2 X0 X1]
  have l5 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X1 ◇ X1))))))))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X1 X1 (X0 ◇ (X0 ◇ (X1 ◇ X1)))]
    conv => enter [1]; rw [l4 X2 X0 X1]
  have l6 : ∀ X2 X0 X1 : G, (X2 ◇ (X2 ◇ (X0 ◇ (X0 ◇ X1)))) = X2 := by
    intro X2 X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [h4728 X1 X0 X1]
    conv => enter [1]; rw [l5 X2 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 1]; rw [← l2 X0]
  have l8 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h4512 X0 X0 X1]
    conv => enter [1]; rw [← l7 X0 X1]
  have l9 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l8 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l10 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X1)))) := by
    intro X0 X1
    conv => enter [1]; rw [l9 X0 X1]
    conv => enter [1, 2, 2]; rw [← h4512 X0 X0 X1]
  have l11 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l10 X0 X1]
    conv => enter [1]; rw [l6 X0 X0 X1]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ X1) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ X1) X2]
    conv => enter [1, 1]; rw [l11 X0 X1]
  have l13 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ (X1 ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l12 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 X1 X2]
  have l14 : ∀ X0 X2 : G, (X0 ◇ X2) = X0 := by
    intro X0 X2
    conv => enter [1]; rw [l13 X0 X2 X0]
    conv => enter [1]; rw [l11 X0 (X0 ◇ X2)]
  intro x y
  conv => enter [1]; rw [← l14 x y]

@[equational_result]
theorem Equation4_implies_Equation4729 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4729 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (y ◇ (z ◇ w))))]

theorem Equation4512_4729_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4729 : Equation4729 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4729 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4729 X1 X0 X1 (X1 ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) ◇ X4)) = (X0 ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X1 ◇ (X2 ◇ X3)))) X4]
    conv => enter [1, 1]; rw [← h4729 X0 X1 X2 X3]
  have l2 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X0 ◇ ((X1 ◇ (X1 ◇ (X2 ◇ X3))) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l1 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X1 ◇ (X2 ◇ X3))) X4]
  have l3 : ∀ X0 X4 : G, (X0 ◇ X4) = X0 := by
    intro X0 X4
    conv => enter [1]; rw [l2 X0 X4 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X4)]
  intro x y
  conv => enter [1]; rw [← l3 x y]

@[equational_result]
theorem Equation4_implies_Equation4731 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4731 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (z ◇ (x ◇ y))))]

theorem Equation4512_4731_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4731 : Equation4731 G) : Equation4 G := by
  have l0 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ (X3 ◇ X0)))) = X0 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4731 X0 X1 X2]
    conv => enter [1]; rw [← h4731 X0 (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) X3]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X1)))) X3]
    conv => enter [1, 1]; rw [← h4731 X0 X1 X2]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l1 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (X0 ◇ X1))) X3]
  have l3 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X1))) ◇ (X3 ◇ X0))))) = X0 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2]; rw [h4512 X0 (X1 ◇ (X2 ◇ (X0 ◇ X1))) (X3 ◇ X0)]
    conv => enter [1]; rw [l0 X0 X1 X2 X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ (X0 ◇ X1)) X3]
  have l5 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X0 ◇ X1)) ◇ (X3 ◇ X0)))))) = X0 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X1 (X2 ◇ (X0 ◇ X1)) (X3 ◇ X0)]
    conv => enter [1]; rw [l3 X0 X1 X2 X3]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l4 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (X0 ◇ X1) X3]
  have l7 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X0 ◇ X1) ◇ (X3 ◇ X0))))))) = X0 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X2 (X0 ◇ X1) (X3 ◇ X0)]
    conv => enter [1]; rw [l5 X0 X1 X2 X3]
  have l8 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l6 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X1 X3]
  have l9 : ∀ X0 X1 X2 X3 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ (X1 ◇ (X3 ◇ X0)))))))) = X0 := by
    intro X0 X1 X2 X3
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X0 X1 (X3 ◇ X0)]
    conv => enter [1]; rw [l7 X0 X1 X2 X3]
  have l10 : ∀ X0 X3 : G, (X0 ◇ (X0 ◇ (X3 ◇ X0))) = X0 := by
    intro X0 X3
    conv => enter [1, 2]; rw [l8 X0 (X3 ◇ X0) X0 X0]
    conv => enter [1]; rw [l9 X0 X0 X0 X3]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l10 X0 X1]
    conv => enter [1]; rw [← h4731 X1 X0 X0]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X0)) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ X0)) X2]
    conv => enter [1, 1]; rw [l10 X0 X1]
  have l13 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ X0) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l12 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X0) X2]
  have l14 : ∀ X0 X2 : G, (X0 ◇ X2) = X0 := by
    intro X0 X2
    conv => enter [1]; rw [l13 X0 X2 X0]
    conv => enter [1]; rw [l11 X0 ((X0 ◇ X0) ◇ X2)]
  intro x y
  conv => enter [1]; rw [← l14 x y]

@[equational_result]
theorem Equation4_implies_Equation4732 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4732 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (z ◇ (x ◇ z))))]

theorem Equation4512_4732_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4732 : Equation4732 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4732 X0 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h4732 X0 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ (X0 ◇ X0)))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2, 2, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h4732 X0 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X1 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l0 (X0 ◇ (X1 ◇ X0))]
    conv => enter [1]; rw [← h4732 X1 (X0 ◇ (X1 ◇ X0)) X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X1 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (X0 ◇ X1)]
  have l5 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l4 X1 X0]
    conv => enter [1]; rw [l3 X1 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ (X0 ◇ X0))) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 (X1 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l1 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l0 X0]
    conv => enter [1]; rw [l6 X0 X1]
  have l8 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2]; rw [l5 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l7 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l10 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l9 sK0 sK1]
    conv => enter [1]; rw [← l8 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l10 x y]

@[equational_result]
theorem Equation4_implies_Equation4733 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4733 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (z ◇ (x ◇ w))))]

theorem Equation4512_4733_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4733 : Equation4733 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4733 X0 X1 X1 X1]
    conv => enter [1]; rw [← h4733 X1 X0 X0 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) ◇ X4)) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1, 1]; rw [h4733 X0 X1 X2 X3]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X3)))) X4]
  have l2 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X0 ◇ X3))) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l1 X0 X4 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (X0 ◇ X3))) X4]
  have l3 : ∀ X0 X4 : G, (X0 ◇ X4) = X0 := by
    intro X0 X4
    conv => enter [1]; rw [l2 X0 X4 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X4)]
  intro x y
  conv => enter [1]; rw [← l3 x y]

@[equational_result]
theorem Equation4_implies_Equation4735 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4735 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (z ◇ (y ◇ y))))]

theorem Equation4512_4735_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4735 : Equation4735 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h4735 (X0 ◇ X0) (X0 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h4735 (X0 ◇ X0) X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0
    conv => enter [1]; rw [l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 (X0 ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l1 X0]
    conv => enter [1]; rw [← h4735 X1 X0 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l2 X0 X0]
    conv => enter [1]; rw [← h4735 X1 X0 X0]
  have l4 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ X1)) X2]
    conv => enter [1, 1]; rw [l2 X0 X1]
  have l5 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l4 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l6 : ∀ X0 X2 : G, (X0 ◇ X2) = X0 := by
    intro X0 X2
    conv => enter [1]; rw [l5 X0 X2 X0]
    conv => enter [1]; rw [l3 X0 ((X0 ◇ X0) ◇ X2)]
  intro x y
  conv => enter [1]; rw [← l6 x y]

@[equational_result]
theorem Equation4_implies_Equation4736 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4736 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (z ◇ (y ◇ z))))]

theorem Equation4512_4736_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4736 : Equation4736 G) : Equation4 G := by
  have l0 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3)))) ◇ X0)))) = X1 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4736 X0 X2 X3]
    conv => enter [1]; rw [← h4736 X1 X0 (X0 ◇ (X2 ◇ (X3 ◇ (X2 ◇ X3))))]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X2)))) X3]
    conv => enter [1, 1]; rw [← h4736 X0 X1 X2]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l1 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (X1 ◇ X2))) X3]
  have l3 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X2 ◇ (X3 ◇ (X2 ◇ X3))) ◇ X0))))) = X1 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 (X2 ◇ (X3 ◇ (X2 ◇ X3))) X0]
    conv => enter [1]; rw [l0 X1 X0 X2 X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X1 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ (X1 ◇ X2)) X3]
  have l5 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ ((X3 ◇ (X2 ◇ X3)) ◇ X0)))))) = X1 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X2 (X3 ◇ (X2 ◇ X3)) X0]
    conv => enter [1]; rw [l3 X1 X0 X2 X3]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X1 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l4 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (X1 ◇ X2) X3]
  have l7 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ ((X2 ◇ X3) ◇ X0))))))) = X1 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2, 2, 2, 2, 2]; rw [h4512 X3 (X2 ◇ X3) X0]
    conv => enter [1]; rw [l5 X1 X0 X2 X3]
  have l8 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ (X2 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l6 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X1 X2 X3]
  have l9 : ∀ X1 X0 X2 X3 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X2 ◇ (X3 ◇ (X2 ◇ (X3 ◇ X0)))))))) = X1 := by
    intro X1 X0 X2 X3
    conv => enter [1, 2, 2, 2, 2, 2, 2]; rw [h4512 X2 X3 X0]
    conv => enter [1]; rw [l7 X1 X0 X2 X3]
  have l10 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [l8 X0 X0 X1 X1]
    conv => enter [1]; rw [l9 X1 X0 X1 X1]
  have l11 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l10 X0 X0]
    conv => enter [1]; rw [← h4736 X1 X0 X0]
  have l12 : ∀ X0 X1 X2 : G, (X0 ◇ ((X0 ◇ (X1 ◇ X1)) ◇ X2)) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ X1)) X2]
    conv => enter [1, 1]; rw [l10 X0 X1]
  have l13 : ∀ X0 X2 X1 : G, (X0 ◇ X2) = (X0 ◇ (X0 ◇ ((X1 ◇ X1) ◇ X2))) := by
    intro X0 X2 X1
    conv => enter [1]; rw [← l12 X0 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ X1) X2]
  have l14 : ∀ X0 X2 : G, (X0 ◇ X2) = X0 := by
    intro X0 X2
    conv => enter [1]; rw [l13 X0 X2 X0]
    conv => enter [1]; rw [l11 X0 ((X0 ◇ X0) ◇ X2)]
  intro x y
  conv => enter [1]; rw [← l14 x y]

@[equational_result]
theorem Equation4_implies_Equation4737 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4737 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (z ◇ (y ◇ w))))]

theorem Equation4512_4737_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4737 : Equation4737 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4737 X0 X0 X1 X1]
    conv => enter [1]; rw [← h4737 X1 X0 X0 (X1 ◇ (X0 ◇ X1))]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) ◇ X4)) = (X0 ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ (X1 ◇ X3)))) X4]
    conv => enter [1, 1]; rw [← h4737 X0 X1 X2 X3]
  have l2 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X1 ◇ X3))) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l1 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (X1 ◇ X3))) X4]
  have l3 : ∀ X0 X4 : G, (X0 ◇ X4) = X0 := by
    intro X0 X4
    conv => enter [1]; rw [l2 X0 X4 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X4)]
  intro x y
  conv => enter [1]; rw [← l3 x y]

@[equational_result]
theorem Equation4_implies_Equation4739 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4739 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (z ◇ (z ◇ y))))]

theorem Equation4512_4739_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4739 : Equation4739 G) : Equation4 G := by
  have l0 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ (X3 ◇ X2))) ◇ X0))) = X1 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2]; rw [h4739 X0 X2 X3]
    conv => enter [1]; rw [← h4739 X1 (X2 ◇ (X3 ◇ (X3 ◇ X2))) X0]
  have l1 : ∀ X0 X1 X2 X3 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) ◇ X3)) = (X0 ◇ X3) := by
    intro X0 X1 X2 X3
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X1)))) X3]
    conv => enter [1, 1]; rw [← h4739 X0 X1 X2]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X1))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [← l1 X0 X1 X2 X3]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (X2 ◇ X1))) X3]
  have l3 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ ((X3 ◇ (X3 ◇ X2)) ◇ X0)))) = X1 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2]; rw [h4512 X2 (X3 ◇ (X3 ◇ X2)) X0]
    conv => enter [1]; rw [l0 X1 X2 X3 X0]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X2 ◇ X1)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ (X2 ◇ X1)) X3]
  have l5 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ ((X3 ◇ X2) ◇ X0))))) = X1 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2]; rw [h4512 X3 (X3 ◇ X2) X0]
    conv => enter [1]; rw [l3 X1 X2 X3 X0]
  have l6 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ ((X2 ◇ X1) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l4 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X2 (X2 ◇ X1) X3]
  have l7 : ∀ X1 X2 X3 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X3 ◇ (X3 ◇ (X2 ◇ X0)))))) = X1 := by
    intro X1 X2 X3 X0
    conv => enter [1, 2, 2, 2, 2]; rw [h4512 X3 X2 X0]
    conv => enter [1]; rw [l5 X1 X2 X3 X0]
  have l8 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ (X1 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l6 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X2 X1 X3]
  have l9 : ∀ X0 X3 : G, (X0 ◇ X3) = X0 := by
    intro X0 X3
    conv => enter [1]; rw [l8 X0 X3 X0 X0]
    conv => enter [1]; rw [l7 X0 X0 X0 X3]
  intro x y
  conv => enter [1]; rw [← l9 x y]

@[equational_result]
theorem Equation4_implies_Equation4740 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4740 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (z ◇ (z ◇ z))))]

theorem Equation4512_4740_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4740 : Equation4740 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ (X0 ◇ (X0 ◇ X0)))) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4740 (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0)) X0]
    conv => enter [1]; rw [← h4740 X1 (X0 ◇ (X0 ◇ X0)) (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l0 X0 X0]
    conv => enter [1]; rw [← h4740 X0 X0 X0]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2, 2]; rw [l2 sK1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l2 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l5 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l2 X0]
    conv => enter [1]; rw [← h4740 X1 X2 X0]
  have l6 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ X0))) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2]; rw [← l2 X0]
    conv => enter [1]; rw [l5 X1 X2 X0]
  have l7 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = X1 := by
    intro X1 X2 X0
    conv => enter [1]; rw [l4 X1 (X2 ◇ X0)]
    conv => enter [1]; rw [l6 X1 X2 X0]
  have l8 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (((sK0 ◇ sK1) ◇ sK1) ◇ X0)) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 sK0 ((sK0 ◇ sK1) ◇ sK1) X0]
    conv => enter [1, 1]; rw [← l3 sK0 sK1]
  have l9 : ∀ sK0 X0 : G, sK0 = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l7 sK0 ((sK0 ◇ sK0) ◇ sK0) X0]
    conv => enter [1]; rw [l8 sK0 sK0 X0]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation4_implies_Equation4741 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4741 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (z ◇ (z ◇ w))))]

theorem Equation4512_4741_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4741 : Equation4741 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4741 X0 X0 X1 X1]
    conv => enter [1]; rw [← h4741 X1 X0 X0 (X1 ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) ◇ X4)) = (X0 ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ (X2 ◇ X3)))) X4]
    conv => enter [1, 1]; rw [← h4741 X0 X1 X2 X3]
  have l2 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X2 ◇ X3))) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l1 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (X2 ◇ X3))) X4]
  have l3 : ∀ X0 X4 : G, (X0 ◇ X4) = X0 := by
    intro X0 X4
    conv => enter [1]; rw [l2 X0 X4 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X4)]
  intro x y
  conv => enter [1]; rw [← l3 x y]

@[equational_result]
theorem Equation4_implies_Equation4743 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4743 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (z ◇ (w ◇ y))))]

theorem Equation4512_4743_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4743 : Equation4743 G) : Equation4 G := by
  have l0 : ∀ X3 X0 X1 X2 : G, (X3 ◇ (X3 ◇ (X0 ◇ (X1 ◇ X2)))) = X3 := by
    intro X3 X0 X1 X2
    conv => enter [1, 2, 2]; rw [h4743 (X0 ◇ (X1 ◇ X2)) X2 X0 X1]
    conv => enter [1]; rw [← h4743 X3 (X0 ◇ (X1 ◇ X2)) (X0 ◇ (X1 ◇ X2)) X2]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) ◇ X4)) = (X0 ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X1)))) X4]
    conv => enter [1, 1]; rw [← h4743 X0 X1 X2 X3]
  have l2 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X1))) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l1 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (X3 ◇ X1))) X4]
  have l3 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X0 ◇ (X1 ◇ ((X2 ◇ (X3 ◇ X1)) ◇ X4)))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [l2 X0 X4 X1 X2 X3]
    conv => enter [1, 2, 2]; rw [← h4512 X1 (X2 ◇ (X3 ◇ X1)) X4]
  have l4 : ∀ X0 X4 : G, (X0 ◇ X4) = X0 := by
    intro X0 X4
    conv => enter [1]; rw [l3 X0 X4 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 X0 (X0 ◇ (X0 ◇ X0)) X4]
  intro x y
  conv => enter [1]; rw [← l4 x y]

@[equational_result]
theorem Equation4_implies_Equation4744 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4744 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (z ◇ (w ◇ z))))]

theorem Equation4512_4744_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4744 : Equation4744 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4744 X0 (X0 ◇ X0) X0 X0]
    conv => enter [1]; rw [← h4744 X0 X0 (X0 ◇ X0) X0]
  have l1 : ∀ X1 X2 X0 : G, (X1 ◇ (X1 ◇ (X2 ◇ (X0 ◇ X0)))) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2, 2, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h4744 X1 X2 X0 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ (X0 ◇ X0))) = X1 := by
    intro X1 X2 X0
    conv => enter [1]; rw [l2 X1 (X2 ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l1 X1 X2 X0]
  have l4 : ∀ X1 X2 X0 : G, (X1 ◇ (X2 ◇ X0)) = X1 := by
    intro X1 X2 X0
    conv => enter [1, 2, 2]; rw [← l0 X0]
    conv => enter [1]; rw [l3 X1 X2 X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [← l0 X0]
    conv => enter [1]; rw [l4 X1 X0 X0]
  intro x y
  conv => enter [1]; rw [← l5 x y]

@[equational_result]
theorem Equation4_implies_Equation4745 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4745 G := by
  intro x y z w
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (z ◇ (w ◇ w))))]

theorem Equation4512_4745_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4745 : Equation4745 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [h4745 X0 (X1 ◇ (X1 ◇ X1)) X1 X1]
    conv => enter [1]; rw [← h4745 X1 X0 X0 (X1 ◇ (X1 ◇ X1))]
  have l1 : ∀ X0 X1 X2 X3 X4 : G, (X0 ◇ ((X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) ◇ X4)) = (X0 ◇ X4) := by
    intro X0 X1 X2 X3 X4
    conv => enter [1]; rw [h4512 X0 (X0 ◇ (X1 ◇ (X2 ◇ (X3 ◇ X3)))) X4]
    conv => enter [1, 1]; rw [← h4745 X0 X1 X2 X3]
  have l2 : ∀ X0 X4 X1 X2 X3 : G, (X0 ◇ X4) = (X0 ◇ (X0 ◇ ((X1 ◇ (X2 ◇ (X3 ◇ X3))) ◇ X4))) := by
    intro X0 X4 X1 X2 X3
    conv => enter [1]; rw [← l1 X0 X1 X2 X3 X4]
    conv => enter [1, 2]; rw [← h4512 X0 (X1 ◇ (X2 ◇ (X3 ◇ X3))) X4]
  have l3 : ∀ X0 X4 : G, (X0 ◇ X4) = X0 := by
    intro X0 X4
    conv => enter [1]; rw [l2 X0 X4 X0 X0 X0]
    conv => enter [1]; rw [l0 X0 ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ X4)]
  intro x y
  conv => enter [1]; rw [← l3 x y]

@[equational_result]
theorem Equation4_implies_Equation4746 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4746 G := by
  intro x y z w u
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (z ◇ (w ◇ u))))]

theorem Equation4512_4746_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4746 : Equation4746 G) : Equation4 G := by
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
  conv => enter [1]; rw [← l3 x y]

@[equational_result]
theorem Equation4_implies_Equation4748 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4748 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (x ◇ (x ◇ y))))]

theorem Equation4512_4748_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4748 : Equation4748 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X0))) ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2, 2, 2]; rw [h4748 X0 X0]
    conv => enter [1]; rw [← h4748 X0 (X0 ◇ (X0 ◇ (X0 ◇ X0)))]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4748 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
  have l2 : ∀ X0 : G, (X0 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ (X0 ◇ X0)))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4512 X0 (X0 ◇ (X0 ◇ X0)) (X0 ◇ X0)]
    conv => enter [1]; rw [l0 X0]
  have l3 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))))) = X0 := by
    intro X0
    conv => enter [1, 2, 2]; rw [h4512 X0 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1]; rw [l2 X0]
  have l4 : ∀ X0 : G, (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X0)))))) = X0 := by
    intro X0
    conv => enter [1, 2, 2, 2]; rw [h4512 X0 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [l3 X0]
  have l5 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h4748 X0 X0]
    conv => enter [1]; rw [l4 X0]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l5 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l7 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ ((sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) ◇ X0)) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h4512 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) X0]
    conv => enter [1, 1]; rw [← l1 sK0 sK1]
  have l8 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ (sK0 ◇ sK1)) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [← l7 sK0 sK1 X0]
    conv => enter [1, 2]; rw [← h4512 sK0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l9 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l8 sK0 X0 sK1]
    conv => enter [1, 2, 2]; rw [← h4512 sK0 (sK0 ◇ sK1) X0]
  have l10 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ X0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l9 sK0 X0 sK1]
    conv => enter [1, 2]; rw [← l6 sK0 ((sK0 ◇ sK1) ◇ X0)]
  have l11 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ X0) = (sK0 ◇ ((sK0 ◇ sK1) ◇ X0)) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h4512 sK0 sK1 X0]
    conv => enter [1]; rw [l6 sK0 (sK1 ◇ X0)]
    conv => enter [1, 2]; rw [h4512 sK0 sK1 X0]
  have l12 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l6 (sK0 ◇ sK1) (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l1 sK0 sK1]
  have l13 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ ((sK0 ◇ sK1) ◇ ((sK0 ◇ sK1) ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4748 (sK0 ◇ sK1) sK0]
    conv => enter [1, 2, 2, 2, 2]; rw [← l12 sK0 sK1]
  have l14 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l13 sK0 sK1]
    conv => enter [1]; rw [← l10 sK0 ((sK0 ◇ sK1) ◇ sK0) sK1]
  have l15 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l14 sK0 sK1]
    conv => enter [1]; rw [← l11 sK0 sK1 sK0]
  have l16 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l12 sK0 sK1]
    conv => enter [1]; rw [← l15 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l16 x y]

@[equational_result]
theorem Equation4_implies_Equation4749 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4749 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (x ◇ (x ◇ z))))]

theorem Equation4512_4749_implies_Equation4 (G : Type*) [Magma G] (h4512 : Equation4512 G) (h4749 : Equation4749 G) : Equation4 G := by
  have l0 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ ((X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) ◇ X3)) := by
    intro X0 X3 X1 X2
    conv => enter [1, 1]; rw [h4749 X0 X1 X2]
    conv => enter [1]; rw [← h4512 X0 (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ X2)))) X3]
  have l1 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ ((X0 ◇ (X0 ◇ (X0 ◇ X2))) ◇ X3))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l0 X0 X3 X1 X2]
    conv => enter [1, 2]; rw [← h4512 X1 (X0 ◇ (X0 ◇ (X0 ◇ X2))) X3]
  have l2 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ ((X0 ◇ (X0 ◇ X2)) ◇ X3)))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l1 X0 X3 X1 X2]
    conv => enter [1, 2, 2]; rw [← h4512 X0 (X0 ◇ (X0 ◇ X2)) X3]
  have l3 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ ((X0 ◇ X2) ◇ X3))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l2 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2]; rw [← h4512 X0 (X0 ◇ X2) X3]
  have l4 : ∀ X0 X3 X1 X2 : G, (X0 ◇ X3) = (X0 ◇ (X1 ◇ (X0 ◇ (X0 ◇ (X0 ◇ (X2 ◇ X3)))))) := by
    intro X0 X3 X1 X2
    conv => enter [1]; rw [l3 X0 X3 X1 X2]
    conv => enter [1, 2, 2, 2, 2]; rw [← h4512 X0 X2 X3]
  have l5 : ∀ X0 X3 : G, (X0 ◇ X3) = X0 := by
    intro X0 X3
    conv => enter [1]; rw [l4 X0 X3 X0 X0]
    conv => enter [1]; rw [← h4749 X0 X0 (X0 ◇ X3)]
  intro x y
  conv => enter [1]; rw [← l5 x y]

@[equational_result]
theorem Equation4_implies_Equation4751 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4751 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (x ◇ (y ◇ y))))]

end Semigroup5
