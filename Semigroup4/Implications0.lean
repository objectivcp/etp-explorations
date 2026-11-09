import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Semigroup4

@[equational_result]
theorem Equation2_implies_Equation63 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation63 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation467 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation467 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (y ◇ y))))]

@[equational_result]
theorem Equation2_implies_Equation474 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation474 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (x ◇ y))))]

@[equational_result]
theorem Equation2_implies_Equation501 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation501 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (x ◇ y))))]

@[equational_result]
theorem Equation2_implies_Equation14 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation14 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation41 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation41 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ z)]

@[equational_result]
theorem Equation2_implies_Equation66 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation66 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation73 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation73 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation464 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation464 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (x ◇ y))))]

@[equational_result]
theorem Equation2_implies_Equation481 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation481 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (z ◇ z))))]

@[equational_result]
theorem Equation2_implies_Equation489 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation489 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (y ◇ z))))]

@[equational_result]
theorem Equation2_implies_Equation492 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation492 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (z ◇ y))))]

@[equational_result]
theorem Equation2_implies_Equation508 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation508 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (z ◇ z))))]

@[equational_result]
theorem Equation2_implies_Equation522 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation522 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (z ◇ (x ◇ z))))]

@[equational_result]
theorem Equation2_implies_Equation543 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation543 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (y ◇ z))))]

@[equational_result]
theorem Equation2_implies_Equation546 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation546 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (z ◇ y))))]

@[equational_result]
theorem Equation2_implies_Equation556 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation556 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (x ◇ z))))]

@[equational_result]
theorem Equation2_implies_Equation572 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation572 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (x ◇ y))))]

@[equational_result]
theorem Equation2_implies_Equation4 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation5 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation9 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation9 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation13 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation13 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation48 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation48 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ (x ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation50 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation50 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ (y ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation53 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation53 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (x ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation62 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation62 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation65 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation65 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation72 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation72 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation332 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation332 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation335 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation335 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation412 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation412 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ (x ◇ (x ◇ y))))]

@[equational_result]
theorem Equation2_implies_Equation418 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation418 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ (y ◇ (x ◇ z))))]

@[equational_result]
theorem Equation2_implies_Equation420 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation420 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ (y ◇ (y ◇ y))))]

@[equational_result]
theorem Equation2_implies_Equation428 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation428 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (x ◇ (x ◇ z))))]

@[equational_result]
theorem Equation2_implies_Equation430 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation430 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (x ◇ (y ◇ y))))]

@[equational_result]
theorem Equation2_implies_Equation433 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation433 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (x ◇ (z ◇ y))))]

@[equational_result]
theorem Equation2_implies_Equation434 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation434 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (x ◇ (z ◇ z))))]

@[equational_result]
theorem Equation2_implies_Equation437 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation437 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (y ◇ (x ◇ y))))]

@[equational_result]
theorem Equation2_implies_Equation443 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation443 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (y ◇ (z ◇ y))))]

@[equational_result]
theorem Equation2_implies_Equation463 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation463 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (x ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation469 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation469 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (z ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation476 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation476 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (y ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation477 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation477 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (y ◇ y))))]

@[equational_result]
theorem Equation2_implies_Equation483 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation483 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (z ◇ (x ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation503 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation503 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (y ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation506 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation506 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (z ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation510 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation510 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (x ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation511 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation511 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (x ◇ y))))]

@[equational_result]
theorem Equation2_implies_Equation541 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation541 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (x ◇ (y ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation558 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation558 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (y ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation3345 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3345 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ (x ◇ (y ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation3350 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3350 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ (x ◇ (z ◇ z)))]

@[equational_result]
theorem Equation2_implies_Equation3352 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3352 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ (y ◇ (x ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation3364 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3364 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ (z ◇ (x ◇ z)))]

@[equational_result]
theorem Equation2_implies_Equation3385 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3385 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ y) (z ◇ (x ◇ (y ◇ z)))]

@[equational_result]
theorem Equation2_implies_Equation3398 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3398 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ y) (z ◇ (y ◇ (x ◇ z)))]

@[equational_result]
theorem Equation2_implies_Equation3404 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3404 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ y) (z ◇ (y ◇ (z ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation3417 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3417 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ y) (z ◇ (z ◇ (y ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation11 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation11 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation16 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation16 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation38 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation38 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 x y]

@[equational_result]
theorem Equation2_implies_Equation39 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation39 G := by
  intro x y
  conv => enter [1, 1]; rw [h2 x y]

@[equational_result]
theorem Equation2_implies_Equation314 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation314 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (x ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation322 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation322 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 y (x ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation336 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation336 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ (y ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation414 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation414 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ (x ◇ (y ◇ y))))]

@[equational_result]
theorem Equation2_implies_Equation417 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation417 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ (y ◇ (x ◇ y))))]

@[equational_result]
theorem Equation2_implies_Equation427 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation427 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (x ◇ (x ◇ y))))]

@[equational_result]
theorem Equation2_implies_Equation452 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation452 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (z ◇ (y ◇ z))))]

@[equational_result]
theorem Equation2_implies_Equation455 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation455 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (z ◇ (z ◇ y))))]

@[equational_result]
theorem Equation2_implies_Equation466 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation466 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (x ◇ (y ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation473 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation473 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ (y ◇ (x ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation500 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation500 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (x ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation504 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation504 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (x ◇ (y ◇ y))))]

@[equational_result]
theorem Equation2_implies_Equation562 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation562 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (y ◇ (z ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation575 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation575 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (y ◇ (z ◇ (z ◇ (y ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation3329 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3329 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 y (z ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation3342 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3342 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ (x ◇ (x ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation3349 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3349 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ (x ◇ (z ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation3355 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3355 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ (y ◇ (y ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation10 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation10 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation49 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation49 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ (y ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation52 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation52 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (x ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation55 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation55 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (y ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation56 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation56 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (y ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation58 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation58 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (z ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation75 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation75 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation413 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation413 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ (x ◇ (y ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation416 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation416 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ (y ◇ (x ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation422 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation422 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ (y ◇ (z ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation426 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation426 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (x ◇ (x ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation432 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation432 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (x ◇ (z ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation439 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation439 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (y ◇ (y ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation442 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation442 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (y ◇ (z ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation446 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation446 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (z ◇ (x ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation450 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation450 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (z ◇ (y ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation454 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation454 G := by
  intro x y z
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (z ◇ (z ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation3331 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3331 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 y (z ◇ (y ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation3388 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3388 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ y) (z ◇ (x ◇ (z ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation311 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation311 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 x (y ◇ z)]

@[equational_result]
theorem Equation2_implies_Equation318 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation318 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (z ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation327 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation327 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 y (y ◇ z)]

@[equational_result]
theorem Equation2_implies_Equation329 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation329 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 y (z ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation343 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation343 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ y) (z ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation419 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation419 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ (y ◇ (y ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation436 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation436 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (y ◇ (x ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation3312 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3312 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 y (x ◇ (z ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation3317 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3317 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 y (y ◇ (x ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation3320 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3320 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 y (y ◇ (y ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation3321 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3321 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 y (y ◇ (z ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation3330 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3330 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 y (z ◇ (y ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation3363 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3363 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ (z ◇ (x ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation3380 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3380 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ y) (z ◇ (x ◇ (x ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation3397 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3397 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ y) (z ◇ (y ◇ (x ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation4274 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4274 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (x ◇ x)) (y ◇ (x ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation4295 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4295 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (x ◇ y)) (y ◇ (z ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation4303 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4303 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (x ◇ y)) (z ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation4344 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4344 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (y ◇ y)) (y ◇ (x ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation4345 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4345 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (y ◇ y)) (y ◇ (z ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation429 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation429 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (x ◇ (y ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation440 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation440 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (y ◇ (y ◇ y))))]

@[equational_result]
theorem Equation2_implies_Equation513 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation513 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ (y ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation3308 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3308 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 y (x ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation3323 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3323 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 y (y ◇ (z ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation3334 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3334 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 y (z ◇ (z ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation3346 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3346 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ (x ◇ (y ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation3414 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3414 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ y) (z ◇ (z ◇ (x ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation3 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3 G := by
  intro x
  conv => enter [1]; rw [h2 x (x ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation325 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation325 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 y (y ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation333 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation333 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation3318 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3318 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 y (y ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation3322 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3322 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 y (y ◇ (z ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation3326 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3326 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 y (z ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation3343 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3343 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ (x ◇ (x ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation4271 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4271 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 (x ◇ x) (y ◇ z)]

@[equational_result]
theorem Equation2_implies_Equation4278 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4278 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (x ◇ x)) (y ◇ (z ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation3309 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3309 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 y (x ◇ (y ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation47 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ (x ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation3315 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3315 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 y (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation3353 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3353 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ (y ◇ (x ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation4287 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4287 G := by
  intro x y z
  conv => enter [1, 2, 1]; rw [h2 x z]

@[equational_result]
theorem Equation2_implies_Equation4300 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4300 G := by
  intro x y z
  conv => enter [1, 1]; rw [h2 x z]

@[equational_result]
theorem Equation2_implies_Equation4315 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4315 G := by
  intro x y z
  conv => enter [1, 2, 2]; rw [h2 x z]

@[equational_result]
theorem Equation2_implies_Equation4330 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4330 G := by
  intro x y z
  conv => enter [1, 1]; rw [h2 x z]

@[equational_result]
theorem Equation2_implies_Equation4339 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4339 G := by
  intro x y z
  conv => enter [1, 2, 2]; rw [h2 y z]

@[equational_result]
theorem Equation2_implies_Equation4340 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4340 G := by
  intro x y z
  conv => enter [1, 2, 1]; rw [h2 y z]

@[equational_result]
theorem Equation2_implies_Equation3277 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3277 G := by
  intro x y z w
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (x ◇ (z ◇ w)))]

@[equational_result]
theorem Equation2_implies_Equation3291 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3291 G := by
  intro x y z w
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (z ◇ (x ◇ w)))]

@[equational_result]
theorem Equation2_implies_Equation8 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation8 G := by
  intro x
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation323 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation323 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 y (x ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation326 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation326 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 y (y ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation43 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation43 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation313 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation313 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation319 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation319 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (z ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation3267 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3267 G := by
  intro x y z w
  conv => enter [1, 2]; rw [h2 x (y ◇ (z ◇ w))]

@[equational_result]
theorem Equation2_implies_Equation3300 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3300 G := by
  intro x y z w
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (z ◇ (w ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation3316 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3316 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 y (y ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation411 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation411 G := by
  intro x
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ (x ◇ (x ◇ x))))]

@[equational_result]
theorem Equation2_implies_Equation3306 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3306 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 y (x ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation3319 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3319 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 y (y ◇ (y ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation309 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation309 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 x (y ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation3273 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3273 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (x ◇ (y ◇ z)))]

@[equational_result]
theorem Equation2_implies_Equation3290 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3290 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (z ◇ (x ◇ z)))]

@[equational_result]
theorem Equation2_implies_Equation3275 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3275 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (x ◇ (z ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation3289 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3289 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (z ◇ (x ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation4364 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4364 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (y ◇ z)) (y ◇ (z ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation316 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation316 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (y ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation317 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation317 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (y ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation320 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation320 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (z ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation3260 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3260 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 x (y ◇ (x ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation3265 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3265 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 x (y ◇ (z ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation3270 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3270 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (x ◇ (x ◇ z)))]

@[equational_result]
theorem Equation2_implies_Equation3272 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3272 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (x ◇ (y ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation3274 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3274 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (x ◇ (z ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation3276 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3276 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (x ◇ (z ◇ z)))]

@[equational_result]
theorem Equation2_implies_Equation3279 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3279 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (y ◇ (x ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation3280 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3280 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (y ◇ (x ◇ z)))]

@[equational_result]
theorem Equation2_implies_Equation3283 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3283 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (y ◇ (y ◇ z)))]

@[equational_result]
theorem Equation2_implies_Equation3285 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3285 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (y ◇ (z ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation3292 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3292 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (z ◇ (y ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation3293 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3293 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (z ◇ (y ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation3298 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3298 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (z ◇ (z ◇ z)))]

@[equational_result]
theorem Equation2_implies_Equation40 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation40 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation3269 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3269 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (x ◇ (x ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation3282 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3282 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (y ◇ (y ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation3294 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3294 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (z ◇ (y ◇ z)))]

@[equational_result]
theorem Equation2_implies_Equation3297 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3297 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (z ◇ (z ◇ y)))]

@[equational_result]
theorem Equation2_implies_Equation310 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation310 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 x (y ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation315 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation315 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation3262 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3262 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 x (y ◇ (y ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation3263 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3263 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 x (y ◇ (y ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation3266 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3266 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 x (y ◇ (z ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation3281 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3281 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (y ◇ (y ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation3284 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3284 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (y ◇ (z ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation3296 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3296 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (z ◇ (z ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation3259 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3259 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 x (y ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation3264 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3264 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 x (y ◇ (z ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation3271 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3271 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (x ◇ (y ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation4301 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4301 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (x ◇ y)) (z ◇ (x ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation4331 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4331 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (y ◇ x)) (z ◇ (y ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation308 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation308 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 x (x ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation312 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation312 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation3254 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3254 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 x (x ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation3257 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3257 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 x (x ◇ (y ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation3268 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3268 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (x ◇ (x ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation3288 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3288 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (z ◇ (x ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation4305 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4305 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (x ◇ y)) (z ◇ (y ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation4325 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4325 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (y ◇ x)) (y ◇ (z ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation3256 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3256 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 x (x ◇ (y ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation3261 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3261 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 x (y ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation3278 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3278 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ (y ◇ (x ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation4286 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4286 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 (x ◇ y) (z ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation4296 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4296 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (x ◇ y)) (y ◇ (z ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation4318 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4318 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 (y ◇ x) (z ◇ z)]

@[equational_result]
theorem Equation2_implies_Equation4327 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4327 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (y ◇ x)) (z ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation4369 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4369 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (y ◇ z)) (z ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation3255 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3255 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 x (x ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation3258 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3258 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 x (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation4358 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4358 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 (y ◇ z) (z ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation4362 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4362 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (y ◇ z)) (y ◇ (x ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation4279 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4279 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (x ◇ x)) (y ◇ (z ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation4273 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4273 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ (x ◇ x)) (y ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation4299 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4299 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (x ◇ y)) (z ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation4297 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4297 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (x ◇ y)) (y ◇ (z ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation4288 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4288 G := by
  intro x y z
  conv => enter [1, 2]; rw [h2 (x ◇ y) (z ◇ z)]

@[equational_result]
theorem Equation2_implies_Equation4304 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4304 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (x ◇ y)) (z ◇ (y ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation4269 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4269 G := by
  intro x y
  conv => enter [1, 2, 1]; rw [h2 x y]

@[equational_result]
theorem Equation2_implies_Equation4277 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4277 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (x ◇ x)) (y ◇ (y ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation4280 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4280 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ (x ◇ x)) (y ◇ (z ◇ z))]

@[equational_result]
theorem Equation2_implies_Equation4270 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4270 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 (x ◇ x) (y ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation4275 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4275 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ (x ◇ x)) (y ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation4268 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4268 G := by
  intro x y
  conv => enter [1, 2, 2]; rw [h2 x y]

@[equational_result]
theorem Equation2_implies_Equation4272 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4272 G := by
  intro x y
  conv => enter [1, 1]; rw [h2 x y]

@[equational_result]
theorem Equation2_implies_Equation4291 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4291 G := by
  intro x y
  conv => enter [1, 1]; rw [h2 x y]

@[equational_result]
theorem Equation2_implies_Equation4314 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4314 G := by
  intro x y
  conv => enter [1, 2, 2]; rw [h2 x y]

@[equational_result]
theorem Equation2_implies_Equation307 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation307 G := by
  intro x
  conv => enter [1, 2]; rw [h2 x (x ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation4283 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4283 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 (x ◇ y) (y ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation4320 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4320 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ (y ◇ x)) (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation4284 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4284 G := by
  intro x y
  conv => enter [1, 2, 1]; rw [h2 x y]

@[equational_result]
theorem Equation2_implies_Equation4293 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4293 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ (x ◇ y)) (y ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation4321 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4321 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ (y ◇ x)) (y ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation4343 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4343 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ (y ◇ y)) (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation3253 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3253 G := by
  intro x
  conv => enter [1, 2]; rw [h2 x (x ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation4290 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4290 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ (x ◇ y)) (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation4276 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4276 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ (x ◇ x)) (y ◇ (y ◇ y))]

@[equational_result]
theorem Equation3_implies_Equation47 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation47 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

@[equational_result]
theorem Equation3_implies_Equation8 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation8 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation3_implies_Equation326 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation326 G := by
  intro x y
  conv => enter [1, 2]; rw [h3 y]

@[equational_result]
theorem Equation3_implies_Equation411 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation411 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [l0 sK0]
  have l2 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [l1 sK0]
  intro x
  conv => enter [1]; rw [l2 x]

@[equational_result]
theorem Equation3_implies_Equation3319 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation3319 G := by
  have l0 : ∀ sK1 : G, sK1 = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h3 sK1]
    conv => enter [1, 2]; rw [h3 sK1]
  intro x y
  conv => enter [1, 2]; rw [l0 y]

@[equational_result]
theorem Equation3_implies_Equation307 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation307 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  intro x
  conv => enter [1]; rw [← h3 x]
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation3_implies_Equation3253 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation3253 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [← h3 x]
  conv => enter [1]; rw [l1 x]

theorem Equation3_4512_implies_Equation323 (G : Type*) [Magma G] (h3 : Equation3 G) (h4512 : Equation4512 G) : Equation323 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation3_4512_implies_Equation3306 (G : Type*) [Magma G] (h3 : Equation3 G) (h4512 : Equation4512 G) : Equation3306 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation4_implies_Equation9 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation9 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation48 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation48 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ (x ◇ y))]

@[equational_result]
theorem Equation4_implies_Equation50 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation50 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ y))]

@[equational_result]
theorem Equation4_implies_Equation53 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation53 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ y))]

@[equational_result]
theorem Equation4_implies_Equation412 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation412 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ (x ◇ (x ◇ y)))]

@[equational_result]
theorem Equation4_implies_Equation418 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation418 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (x ◇ z)))]

@[equational_result]
theorem Equation4_implies_Equation420 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation420 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (y ◇ y)))]

@[equational_result]
theorem Equation4_implies_Equation428 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation428 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (x ◇ z)))]

@[equational_result]
theorem Equation4_implies_Equation430 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation430 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (y ◇ y)))]

@[equational_result]
theorem Equation4_implies_Equation433 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation433 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (z ◇ y)))]

@[equational_result]
theorem Equation4_implies_Equation434 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation434 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (z ◇ z)))]

@[equational_result]
theorem Equation4_implies_Equation437 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation437 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (x ◇ y)))]

@[equational_result]
theorem Equation4_implies_Equation443 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation443 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (z ◇ y)))]

@[equational_result]
theorem Equation4_implies_Equation11 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation11 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation38 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation38 G := by
  intro x y
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x y]

@[equational_result]
theorem Equation4_implies_Equation322 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation322 G := by
  intro x y
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (x ◇ x)]

@[equational_result]
theorem Equation4_implies_Equation414 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation414 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ (x ◇ (y ◇ y)))]

@[equational_result]
theorem Equation4_implies_Equation417 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation417 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (x ◇ y)))]

@[equational_result]
theorem Equation4_implies_Equation427 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation427 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (x ◇ y)))]

@[equational_result]
theorem Equation4_implies_Equation452 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation452 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (y ◇ z)))]

@[equational_result]
theorem Equation4_implies_Equation455 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation455 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (z ◇ y)))]

@[equational_result]
theorem Equation4_implies_Equation3329 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3329 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (z ◇ (y ◇ x))]

@[equational_result]
theorem Equation4_implies_Equation10 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation10 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ x)]

@[equational_result]
theorem Equation4_implies_Equation49 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation49 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ x))]

@[equational_result]
theorem Equation4_implies_Equation52 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation52 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation4_implies_Equation55 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation55 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ x))]

@[equational_result]
theorem Equation4_implies_Equation56 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation56 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ y))]

@[equational_result]
theorem Equation4_implies_Equation58 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation58 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ x))]

@[equational_result]
theorem Equation4_implies_Equation413 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation413 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ (x ◇ (y ◇ x)))]

@[equational_result]
theorem Equation4_implies_Equation416 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation416 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (x ◇ x)))]

@[equational_result]
theorem Equation4_implies_Equation422 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation422 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (z ◇ x)))]

@[equational_result]
theorem Equation4_implies_Equation426 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation426 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (x ◇ x)))]

@[equational_result]
theorem Equation4_implies_Equation432 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation432 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (z ◇ x)))]

@[equational_result]
theorem Equation4_implies_Equation439 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation439 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (y ◇ x)))]

@[equational_result]
theorem Equation4_implies_Equation442 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation442 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (z ◇ x)))]

@[equational_result]
theorem Equation4_implies_Equation446 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation446 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (x ◇ x)))]

@[equational_result]
theorem Equation4_implies_Equation450 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation450 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (y ◇ x)))]

@[equational_result]
theorem Equation4_implies_Equation454 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation454 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ (z ◇ x)))]

@[equational_result]
theorem Equation4_implies_Equation3331 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3331 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (z ◇ (y ◇ z))]

@[equational_result]
theorem Equation4_implies_Equation311 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation311 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (y ◇ z)]

@[equational_result]
theorem Equation4_implies_Equation327 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation327 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (y ◇ z)]

@[equational_result]
theorem Equation4_implies_Equation329 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation329 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (z ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation419 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation419 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ (y ◇ x)))]

@[equational_result]
theorem Equation4_implies_Equation436 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation436 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (x ◇ x)))]

@[equational_result]
theorem Equation4_implies_Equation3312 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3312 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (x ◇ (z ◇ y))]

@[equational_result]
theorem Equation4_implies_Equation3317 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3317 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ z))]

@[equational_result]
theorem Equation4_implies_Equation3320 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3320 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ z))]

@[equational_result]
theorem Equation4_implies_Equation3321 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3321 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ x))]

@[equational_result]
theorem Equation4_implies_Equation3330 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3330 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (z ◇ (y ◇ y))]

@[equational_result]
theorem Equation4_implies_Equation429 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation429 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ (y ◇ x)))]

@[equational_result]
theorem Equation4_implies_Equation440 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation440 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ (y ◇ y)))]

@[equational_result]
theorem Equation4_implies_Equation3308 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3308 G := by
  intro x y
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ x))]

@[equational_result]
theorem Equation4_implies_Equation3323 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3323 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ z))]

@[equational_result]
theorem Equation4_implies_Equation3334 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3334 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (z ◇ (z ◇ y))]

@[equational_result]
theorem Equation4_implies_Equation3 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3 G := by
  intro x
  conv => enter [1]; rw [h4 x x]

@[equational_result]
theorem Equation4_implies_Equation325 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation325 G := by
  intro x y
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (y ◇ x)]

@[equational_result]
theorem Equation4_implies_Equation3318 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3318 G := by
  intro x y
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ x))]

@[equational_result]
theorem Equation4_implies_Equation3322 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3322 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ y))]

@[equational_result]
theorem Equation4_implies_Equation3326 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3326 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h4 sK0 sK1]
    conv => enter [1]; rw [h4 sK0 (sK2 ◇ (sK0 ◇ sK1))]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation4_implies_Equation4271 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4271 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x (x ◇ x)]
  conv => enter [1]; rw [h4 x (y ◇ z)]

@[equational_result]
theorem Equation4_implies_Equation3309 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3309 G := by
  intro x y
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ y))]

@[equational_result]
theorem Equation4_implies_Equation3315 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3315 G := by
  intro x y
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation4_implies_Equation4287 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4287 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x (x ◇ y)]
  conv => enter [1]; rw [h4 x (z ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation4315 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4315 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x (y ◇ x)]
  conv => enter [1]; rw [h4 x (y ◇ z)]

@[equational_result]
theorem Equation4_implies_Equation4339 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4339 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x (y ◇ y)]
  conv => enter [1]; rw [h4 x (y ◇ z)]

@[equational_result]
theorem Equation4_implies_Equation4340 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4340 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x (y ◇ y)]
  conv => enter [1]; rw [h4 x (z ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation3267 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3267 G := by
  intro x y z w
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ w))]

@[equational_result]
theorem Equation4_implies_Equation3316 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3316 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4 sK0 sK1]
    conv => enter [1]; rw [h4 sK0 (sK1 ◇ (sK0 ◇ sK1))]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation4_implies_Equation309 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation309 G := by
  intro x y
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (y ◇ x)]

@[equational_result]
theorem Equation4_implies_Equation3260 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3260 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ z))]

@[equational_result]
theorem Equation4_implies_Equation3265 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3265 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ y))]

@[equational_result]
theorem Equation4_implies_Equation310 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation310 G := by
  intro x y
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (y ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation3262 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3262 G := by
  intro x y
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ y))]

@[equational_result]
theorem Equation4_implies_Equation3263 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3263 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ z))]

@[equational_result]
theorem Equation4_implies_Equation3266 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3266 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ z))]

@[equational_result]
theorem Equation4_implies_Equation3259 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3259 G := by
  intro x y
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ y))]

@[equational_result]
theorem Equation4_implies_Equation3264 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3264 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ x))]

@[equational_result]
theorem Equation4_implies_Equation308 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation308 G := by
  intro x y
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (x ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation3254 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3254 G := by
  intro x y
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (x ◇ (x ◇ y))]

@[equational_result]
theorem Equation4_implies_Equation3257 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3257 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ z))]

@[equational_result]
theorem Equation4_implies_Equation3256 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3256 G := by
  intro x y
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ y))]

@[equational_result]
theorem Equation4_implies_Equation3261 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3261 G := by
  intro x y
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ x))]

@[equational_result]
theorem Equation4_implies_Equation4286 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4286 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x (x ◇ y)]
  conv => enter [1]; rw [h4 x (z ◇ x)]

@[equational_result]
theorem Equation4_implies_Equation4318 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4318 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x (y ◇ x)]
  conv => enter [1]; rw [h4 x (z ◇ z)]

@[equational_result]
theorem Equation4_implies_Equation3255 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3255 G := by
  intro x y
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ x))]

@[equational_result]
theorem Equation4_implies_Equation3258 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3258 G := by
  intro x y
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation4_implies_Equation4358 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4358 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x (y ◇ z)]
  conv => enter [1]; rw [h4 x (z ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation4288 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4288 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x (x ◇ y)]
  conv => enter [1]; rw [h4 x (z ◇ z)]

@[equational_result]
theorem Equation4_implies_Equation4269 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4269 G := by
  intro x y
  conv => enter [1]; rw [← h4 x (x ◇ x)]
  conv => enter [1]; rw [h4 x (y ◇ x)]

@[equational_result]
theorem Equation4_implies_Equation4270 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4270 G := by
  intro x y
  conv => enter [1]; rw [← h4 x (x ◇ x)]
  conv => enter [1]; rw [h4 x (y ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation4268 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4268 G := by
  intro x y
  conv => enter [1]; rw [← h4 x (x ◇ x)]
  conv => enter [1]; rw [h4 x (x ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation4314 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4314 G := by
  intro x y
  conv => enter [1]; rw [← h4 x (y ◇ x)]
  conv => enter [1]; rw [h4 x (y ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation4283 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4283 G := by
  intro x y
  conv => enter [1]; rw [← h4 x (x ◇ y)]
  conv => enter [1]; rw [h4 x (y ◇ x)]

@[equational_result]
theorem Equation4_implies_Equation4284 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation4284 G := by
  intro x y
  conv => enter [1]; rw [← h4 x (x ◇ y)]
  conv => enter [1]; rw [h4 x (y ◇ y)]

@[equational_result]
theorem Equation5_implies_Equation13 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation13 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation62 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation62 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1, 2]; rw [h5 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x]
  conv => enter [1]; rw [h5 (x ◇ (x ◇ x)) y]

@[equational_result]
theorem Equation5_implies_Equation65 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation65 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [h5 (x ◇ (y ◇ x)) y]

@[equational_result]
theorem Equation5_implies_Equation72 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation72 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1, 2]; rw [h5 (x ◇ x) y]

@[equational_result]
theorem Equation5_implies_Equation463 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation463 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1, 2]; rw [h5 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2, 2]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation5_implies_Equation469 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation469 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [h5 (sK2 ◇ sK0) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation5_implies_Equation476 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation476 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 (sK1 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation5_implies_Equation483 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation483 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK2]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation5_implies_Equation503 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation503 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [h5 (sK0 ◇ (sK1 ◇ sK0)) sK1]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation5_implies_Equation506 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation506 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [h5 (sK0 ◇ (sK2 ◇ sK0)) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation5_implies_Equation510 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation510 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h5 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2, 2]; rw [h5 (sK0 ◇ sK0) sK1]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation5_implies_Equation541 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation541 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ sK0)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation5_implies_Equation558 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation558 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  have l1 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h5 (sK1 ◇ (sK1 ◇ sK0)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation5_implies_Equation16 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation16 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation39 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation39 G := by
  intro x y
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [h5 x y]

@[equational_result]
theorem Equation5_implies_Equation336 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation336 G := by
  have l0 : ∀ sK1 : G, sK1 = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h5 sK1 sK1]
    conv => enter [1, 2]; rw [h5 sK1 sK1]
  intro x y
  conv => enter [1]; rw [← h5 y x]
  conv => enter [1]; rw [l0 y]

@[equational_result]
theorem Equation5_implies_Equation466 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation466 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h5 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation5_implies_Equation473 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation473 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation5_implies_Equation500 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation500 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1, 2]; rw [h5 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1, 2]; rw [h5 (sK0 ◇ (sK0 ◇ sK0)) sK1]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation5_implies_Equation562 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation562 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h5 (sK1 ◇ (sK2 ◇ sK0)) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation5_implies_Equation575 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation575 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK2]
  have l1 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [h5 (sK1 ◇ sK0) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation5_implies_Equation3349 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3349 G := by
  have l0 : ∀ sK1 sK0 sK2 : G, sK1 = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h5 sK1 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK1) sK0]
  intro x y z
  conv => enter [1]; rw [← h5 y x]
  conv => enter [1]; rw [l0 y x z]
  conv => enter [1]; rw [h5 (x ◇ (z ◇ y)) y]

@[equational_result]
theorem Equation5_implies_Equation10 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation10 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation49 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation49 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1, 2]; rw [h5 (y ◇ x) x]

@[equational_result]
theorem Equation5_implies_Equation52 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation52 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [h5 (y ◇ (x ◇ x)) x]

@[equational_result]
theorem Equation5_implies_Equation55 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation55 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [h5 (y ◇ (y ◇ x)) x]

@[equational_result]
theorem Equation5_implies_Equation58 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation58 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]
  conv => enter [1]; rw [h5 (y ◇ (z ◇ x)) x]

@[equational_result]
theorem Equation5_implies_Equation75 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation75 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1, 2, 2]; rw [h5 x y]

@[equational_result]
theorem Equation5_implies_Equation413 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation413 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h5 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2, 2]; rw [h5 (sK1 ◇ sK0) sK0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation5_implies_Equation416 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation416 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [h5 (sK1 ◇ (sK0 ◇ sK0)) sK0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation5_implies_Equation422 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation422 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [h5 (sK1 ◇ (sK2 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [h5 (sK1 ◇ (sK2 ◇ sK0)) sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation5_implies_Equation426 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation426 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1, 2]; rw [h5 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1]; rw [l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation5_implies_Equation432 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation432 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ (sK2 ◇ sK0)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation5_implies_Equation439 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation439 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2, 2]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation5_implies_Equation442 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation442 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [h5 (sK2 ◇ sK0) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK2]
    conv => enter [1]; rw [l1 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation5_implies_Equation446 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation446 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK2]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation5_implies_Equation450 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation450 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK2]
  have l1 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h5 (sK2 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2 sK1]
    conv => enter [1]; rw [l1 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation5_implies_Equation454 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation454 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1, 2]; rw [h5 sK0 sK2]
  have l1 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h5 (sK2 ◇ (sK2 ◇ sK0)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK2]
    conv => enter [1]; rw [l1 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation5_implies_Equation3388 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3388 G := by
  have l0 : ∀ sK1 sK0 sK2 : G, sK1 = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h5 sK1 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK1) sK0]
  intro x y z
  conv => enter [1]; rw [← h5 y x]
  conv => enter [1]; rw [l0 y x z]
  conv => enter [1]; rw [h5 (x ◇ (z ◇ y)) z]

@[equational_result]
theorem Equation5_implies_Equation318 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation318 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK1]
  intro x y z
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation5_implies_Equation329 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation329 G := by
  have l0 : ∀ sK1 sK0 sK2 : G, sK1 = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h5 sK1 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK1) sK0]
  intro x y z
  conv => enter [1]; rw [← h5 y x]
  conv => enter [1]; rw [l0 y x z]

@[equational_result]
theorem Equation5_implies_Equation343 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation343 G := by
  intro x y z
  conv => enter [1]; rw [h5 (x ◇ y) z]

@[equational_result]
theorem Equation5_implies_Equation419 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation419 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 (sK1 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1, 2]; rw [h5 (sK1 ◇ (sK1 ◇ sK0)) sK0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation5_implies_Equation436 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation436 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [h5 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation5_implies_Equation3312 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3312 G := by
  have l0 : ∀ sK1 sK0 sK2 : G, sK1 = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h5 sK1 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK1) sK0]
  intro x y z
  conv => enter [1]; rw [← h5 y x]
  conv => enter [1]; rw [l0 y x z]
  conv => enter [1, 2]; rw [h5 (z ◇ y) x]

@[equational_result]
theorem Equation5_implies_Equation3330 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3330 G := by
  have l0 : ∀ sK1 sK2 : G, sK1 = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h5 sK1 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK1) sK2]
  intro x y z
  conv => enter [1]; rw [← h5 y x]
  conv => enter [1]; rw [l0 y z]
  conv => enter [1]; rw [h5 (z ◇ (y ◇ y)) x]

@[equational_result]
theorem Equation5_implies_Equation3363 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3363 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ sK1)) sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation5_implies_Equation3380 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3380 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1, 2]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ sK1)) sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation5_implies_Equation3397 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3397 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ sK1)) sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation5_implies_Equation429 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation429 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ (sK1 ◇ sK0)) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation5_implies_Equation513 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation513 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ sK0)) = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0
    conv => enter [1, 2, 2]; rw [h5 sK0 sK1]
    conv => enter [1, 2, 2, 2]; rw [h5 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation5_implies_Equation3334 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3334 G := by
  have l0 : ∀ sK1 sK2 : G, sK1 = (sK2 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h5 sK1 sK2]
    conv => enter [1, 2]; rw [h5 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← h5 y x]
  conv => enter [1]; rw [l0 y z]
  conv => enter [1]; rw [h5 (z ◇ (z ◇ y)) x]

@[equational_result]
theorem Equation5_implies_Equation3346 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3346 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK1) sK0]
  intro x y
  conv => enter [1]; rw [← h5 y x]
  conv => enter [1]; rw [l0 y x]
  conv => enter [1]; rw [h5 (x ◇ (y ◇ y)) y]

@[equational_result]
theorem Equation5_implies_Equation3414 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3414 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK2]
    conv => enter [1, 2]; rw [h5 (sK0 ◇ sK1) sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation5_implies_Equation3 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3 G := by
  intro x
  conv => enter [1]; rw [h5 x x]

@[equational_result]
theorem Equation5_implies_Equation333 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation333 G := by
  intro x y
  conv => enter [1]; rw [h5 (x ◇ y) y]

@[equational_result]
theorem Equation5_implies_Equation3322 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3322 G := by
  have l0 : ∀ sK1 sK2 : G, sK1 = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h5 sK1 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK1) sK1]
  intro x y z
  conv => enter [1]; rw [← h5 y x]
  conv => enter [1]; rw [l0 y z]
  conv => enter [1]; rw [h5 (y ◇ (z ◇ y)) x]

@[equational_result]
theorem Equation5_implies_Equation3326 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3326 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ sK1)) sK0]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation5_implies_Equation3343 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3343 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation4278 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4278 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1, 2]; rw [h5 sK0 sK0]
  have l1 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK1]
  intro x y z
  conv => enter [1]; rw [← l0 x]
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation5_implies_Equation3309 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3309 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK1) sK0]
  intro x y
  conv => enter [1]; rw [← h5 y x]
  conv => enter [1]; rw [l0 y x]
  conv => enter [1, 2]; rw [h5 (y ◇ y) x]

@[equational_result]
theorem Equation5_implies_Equation3353 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3353 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK1]
  intro x y
  conv => enter [1]; rw [← h5 y x]
  conv => enter [1]; rw [l0 y x]
  conv => enter [1, 2]; rw [h5 (x ◇ y) y]

@[equational_result]
theorem Equation5_implies_Equation4287 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4287 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1, 2]; rw [h5 sK1 sK0]
  have l1 : ∀ sK1 sK0 sK2 : G, sK1 = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h5 sK1 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK1) sK0]
  intro x y z
  conv => enter [1]; rw [← l0 y x]
  conv => enter [1]; rw [l1 y x z]

@[equational_result]
theorem Equation5_implies_Equation4300 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4300 G := by
  intro x y z
  conv => enter [1, 2]; rw [← h5 y x]
  conv => enter [1]; rw [h5 (x ◇ y) z]

@[equational_result]
theorem Equation5_implies_Equation4330 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4330 G := by
  intro x y z
  conv => enter [1]; rw [← h5 (y ◇ x) x]
  conv => enter [1]; rw [h5 (y ◇ x) z]

@[equational_result]
theorem Equation5_implies_Equation4340 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4340 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK1) sK0]
  have l1 : ∀ sK1 sK0 sK2 : G, sK1 = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h5 sK1 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK1) sK0]
  intro x y z
  conv => enter [1]; rw [← l0 y x]
  conv => enter [1]; rw [l1 y x z]

@[equational_result]
theorem Equation5_implies_Equation3300 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3300 G := by
  have l0 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK3]
  intro x y z w
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [l0 x z w]
  conv => enter [1]; rw [h5 (z ◇ (w ◇ x)) y]

@[equational_result]
theorem Equation5_implies_Equation3316 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3316 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ (sK0 ◇ sK1)) sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation309 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation309 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  intro x y
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation3274 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3274 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK0]
  intro x y z
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [l0 x z]
  conv => enter [1]; rw [h5 (x ◇ (z ◇ x)) y]

@[equational_result]
theorem Equation5_implies_Equation3292 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3292 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK2]
  intro x y z
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [l0 x z y]
  conv => enter [1]; rw [h5 (z ◇ (y ◇ x)) y]

@[equational_result]
theorem Equation5_implies_Equation315 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation315 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation3281 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3281 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [l0 x y]
  conv => enter [1, 2, 2]; rw [h5 x y]

@[equational_result]
theorem Equation5_implies_Equation3284 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3284 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK1]
  intro x y z
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [l0 x y z]
  conv => enter [1, 2]; rw [h5 (z ◇ x) y]

@[equational_result]
theorem Equation5_implies_Equation3296 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3296 G := by
  have l0 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1, 2]; rw [h5 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [l0 x z]
  conv => enter [1]; rw [h5 (z ◇ (z ◇ x)) y]

@[equational_result]
theorem Equation5_implies_Equation3264 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3264 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) sK1]
  intro x y z
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [l0 x y z]
  conv => enter [1]; rw [h5 (y ◇ (z ◇ x)) x]

@[equational_result]
theorem Equation5_implies_Equation3271 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3271 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  intro x y
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [h5 (x ◇ (y ◇ x)) y]

@[equational_result]
theorem Equation5_implies_Equation312 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation312 G := by
  intro x y
  conv => enter [1]; rw [h5 (x ◇ x) y]

@[equational_result]
theorem Equation5_implies_Equation3268 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3268 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1, 2]; rw [h5 sK0 sK0]
  intro x y
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [l0 x]
  conv => enter [1]; rw [h5 (x ◇ (x ◇ x)) y]

@[equational_result]
theorem Equation5_implies_Equation3288 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3288 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ (sK0 ◇ sK0)) sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation5_implies_Equation3261 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3261 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [h5 (y ◇ (y ◇ x)) x]

@[equational_result]
theorem Equation5_implies_Equation3278 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3278 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [h5 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation4296 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4296 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1, 2]; rw [h5 sK1 sK0]
  have l1 : ∀ sK1 sK2 : G, sK1 = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h5 sK1 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK1) sK1]
  intro x y z
  conv => enter [1]; rw [← l0 y x]
  conv => enter [1]; rw [l1 y z]

@[equational_result]
theorem Equation5_implies_Equation4327 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4327 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK2]
  intro x y z
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1]; rw [l1 x z]

@[equational_result]
theorem Equation5_implies_Equation3255 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3255 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  intro x y
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [l0 x y]
  conv => enter [1, 2]; rw [h5 (y ◇ x) x]

@[equational_result]
theorem Equation5_implies_Equation3258 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3258 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [h5 (y ◇ (x ◇ x)) x]

@[equational_result]
theorem Equation5_implies_Equation4362 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4362 G := by
  have l0 : ∀ sK2 sK0 sK1 : G, sK2 = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h5 sK2 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK2) sK0]
  have l1 : ∀ sK2 sK1 sK0 : G, sK2 = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [h5 sK2 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK2) sK1]
  intro x y z
  conv => enter [1]; rw [← l0 z x y]
  conv => enter [1]; rw [l1 z y x]

@[equational_result]
theorem Equation5_implies_Equation4304 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4304 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1, 2]; rw [h5 sK1 sK0]
  have l1 : ∀ sK1 sK2 : G, sK1 = (sK2 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [h5 sK1 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK1) sK2]
  intro x y z
  conv => enter [1]; rw [← l0 y x]
  conv => enter [1]; rw [l1 y z]

@[equational_result]
theorem Equation5_implies_Equation4269 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4269 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1, 2]; rw [h5 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  intro x y
  conv => enter [1]; rw [← l0 x]
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation5_implies_Equation4275 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4275 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1, 2]; rw [h5 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l0 x]
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation5_implies_Equation4272 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4272 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1, 2]; rw [h5 sK0 sK0]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [← l0 x]
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation5_implies_Equation4291 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4291 G := by
  intro x y
  conv => enter [1, 2]; rw [← h5 y x]
  conv => enter [1]; rw [h5 (x ◇ y) y]

@[equational_result]
theorem Equation5_implies_Equation4320 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4320 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [← l0 x y]
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation5_implies_Equation4284 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation4284 G := by
  have l0 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK0]
    conv => enter [1, 2]; rw [h5 sK1 sK0]
  have l1 : ∀ sK1 sK0 : G, sK1 = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h5 sK1 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK1) sK0]
  intro x y
  conv => enter [1]; rw [← l0 y x]
  conv => enter [1]; rw [l1 y x]

@[equational_result]
theorem Equation8_implies_Equation411 (G : Type*) [Magma G] (h8 : Equation8 G) : Equation411 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0
    conv => enter [1]; rw [h8 sK0]
    conv => enter [1, 2, 2]; rw [h8 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation8_implies_Equation3319 (G : Type*) [Magma G] (h8 : Equation8 G) : Equation3319 G := by
  intro x y
  conv => enter [1, 2]; rw [h8 y]

@[equational_result]
theorem Equation8_implies_Equation3253 (G : Type*) [Magma G] (h8 : Equation8 G) : Equation3253 G := by
  intro x
  conv => enter [1, 2]; rw [h8 x]

theorem Equation8_4512_implies_Equation3306 (G : Type*) [Magma G] (h8 : Equation8 G) (h4512 : Equation4512 G) : Equation3306 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h8 X0]
    conv => enter [1]; rw [← h4512 X0 (X0 ◇ X0) X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ (X0 ◇ X1))) := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1, 2]; rw [← h4512 X0 X0 X1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation9_implies_Equation48 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation48 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h9 X0 X0]
    conv => enter [1]; rw [← h9 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0]
    conv => enter [1, 2]; rw [h9 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation9_implies_Equation50 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation50 G := by
  intro x y
  conv => enter [1]; rw [h9 x (y ◇ y)]

@[equational_result]
theorem Equation9_implies_Equation412 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation412 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h9 X0 X0]
    conv => enter [1]; rw [← h9 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0]
    conv => enter [1, 2]; rw [h9 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation9_implies_Equation418 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation418 G := by
  intro x y z
  conv => enter [1]; rw [h9 x (y ◇ (x ◇ z))]

@[equational_result]
theorem Equation9_implies_Equation420 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation420 G := by
  intro x y
  conv => enter [1]; rw [h9 x (y ◇ (y ◇ y))]

@[equational_result]
theorem Equation9_implies_Equation414 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation414 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h9 X0 X0]
    conv => enter [1]; rw [← h9 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0]
    conv => enter [1, 2]; rw [h9 sK0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation9_implies_Equation417 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation417 G := by
  intro x y
  conv => enter [1]; rw [h9 x (y ◇ (x ◇ y))]

@[equational_result]
theorem Equation9_implies_Equation49 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation49 G := by
  intro x y
  conv => enter [1]; rw [h9 x (y ◇ x)]

@[equational_result]
theorem Equation9_implies_Equation413 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation413 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h9 X0 X0]
    conv => enter [1]; rw [← h9 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0]
    conv => enter [1, 2]; rw [h9 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation9_implies_Equation416 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation416 G := by
  intro x y
  conv => enter [1]; rw [h9 x (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation9_implies_Equation422 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation422 G := by
  intro x y z
  conv => enter [1]; rw [h9 x (y ◇ (z ◇ x))]

@[equational_result]
theorem Equation9_implies_Equation419 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation419 G := by
  intro x y
  conv => enter [1]; rw [h9 x (y ◇ (y ◇ x))]

@[equational_result]
theorem Equation9_implies_Equation3320 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation3320 G := by
  intro x y z
  conv => enter [1, 2]; rw [h9 y z]

@[equational_result]
theorem Equation9_implies_Equation3 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h9 X0 X0]
    conv => enter [1]; rw [← h9 X0 (X0 ◇ X0)]
  intro x
  conv => enter [1]; rw [← l0 x]

@[equational_result]
theorem Equation9_implies_Equation3318 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation3318 G := by
  intro x y
  conv => enter [1, 2]; rw [h9 y x]

@[equational_result]
theorem Equation9_implies_Equation308 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation308 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h9 X0 X0]
    conv => enter [1]; rw [← h9 X0 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l0 x]
  conv => enter [1]; rw [h9 x y]

@[equational_result]
theorem Equation9_implies_Equation3254 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation3254 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h9 X0 X0]
    conv => enter [1]; rw [← h9 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0]
    conv => enter [1, 2]; rw [h9 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x]
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation9_implies_Equation3257 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation3257 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h9 X0 X0]
    conv => enter [1]; rw [← h9 X0 (X0 ◇ X0)]
  intro x y z
  conv => enter [1]; rw [l0 x]
  conv => enter [1]; rw [h9 x (y ◇ z)]

@[equational_result]
theorem Equation9_implies_Equation3256 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation3256 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h9 X0 X0]
    conv => enter [1]; rw [← h9 X0 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l0 x]
  conv => enter [1]; rw [h9 x (y ◇ y)]

@[equational_result]
theorem Equation9_implies_Equation3255 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation3255 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h9 X0 X0]
    conv => enter [1]; rw [← h9 X0 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l0 x]
  conv => enter [1]; rw [h9 x (y ◇ x)]

@[equational_result]
theorem Equation9_implies_Equation4268 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation4268 G := by
  intro x y
  conv => enter [1]; rw [← h9 x x]
  conv => enter [1]; rw [h9 x y]

theorem Equation13_4512_implies_Equation62 (G : Type*) [Magma G] (h13 : Equation13 G) (h4512 : Equation4512 G) : Equation62 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [h13 sK0 sK0]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h13 X1 X2]
  have l3 : ∀ sK0 X0 X1 : G, sK0 = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h13 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [l2 sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l4 x]
  conv => enter [1]; rw [l1 x y]

theorem Equation13_4512_implies_Equation72 (G : Type*) [Magma G] (h13 : Equation13 G) (h4512 : Equation4512 G) : Equation72 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [h13 sK0 sK1]
  have l2 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h13 X1 X2]
  have l3 : ∀ sK0 X0 X1 : G, sK0 = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h13 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l4 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l3 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [l2 sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l4 x]
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation13_implies_Equation463 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation463 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1, 2, 2]; rw [← h13 sK0 sK0]
    conv => enter [1]; rw [← l0 (sK0 ◇ sK0) sK1]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h13 sK0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation13_implies_Equation483 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation483 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h13 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h13 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation13_implies_Equation510 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation510 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [h13 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h13 sK0 sK1]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation13_implies_Equation473 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation473 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h13 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h13 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation13_implies_Equation500 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation500 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [h13 sK0 sK0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h13 sK0 sK1]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation13_4512_implies_Equation52 (G : Type*) [Magma G] (h13 : Equation13 G) (h4512 : Equation4512 G) : Equation52 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h13 X1 X2]
  have l2 : ∀ sK0 X0 X1 : G, sK0 = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h13 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l3 x]
  conv => enter [1, 2]; rw [h13 x y]

@[equational_result]
theorem Equation13_implies_Equation416 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation416 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h13 sK0 sK0]
    conv => enter [1, 2, 2]; rw [h13 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation13_implies_Equation426 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation426 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [h13 sK0 sK0]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h13 sK0 sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation13_implies_Equation446 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation446 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [h13 sK0 sK2]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h13 sK0 sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation13_implies_Equation436 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation436 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [h13 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h13 sK0 sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation13_implies_Equation3380 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation3380 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h13 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0]
  have l2 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← l0 (sK0 ◇ (sK0 ◇ sK1)) sK2]
    conv => enter [1]; rw [l0 (sK0 ◇ (sK0 ◇ sK1)) X0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1]; rw [l2 sK0 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation13_4512_implies_Equation3 (G : Type*) [Magma G] (h13 : Equation13 G) (h4512 : Equation4512 G) : Equation3 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h13 X1 X2]
  have l2 : ∀ sK0 X0 X1 : G, sK0 = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h13 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK0 sK0]
  intro x
  conv => enter [1]; rw [l3 x]

@[equational_result]
theorem Equation13_implies_Equation3343 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation3343 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h13 (sK0 ◇ sK1) X0]
    conv => enter [1, 2]; rw [l0 (sK0 ◇ sK1) sK0]
  intro x y
  conv => enter [1]; rw [l1 x y y]

theorem Equation13_4512_implies_Equation312 (G : Type*) [Magma G] (h13 : Equation13 G) (h4512 : Equation4512 G) : Equation312 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ X2 X0 X1 : G, (X2 ◇ (X0 ◇ X1)) = X1 := by
    intro X2 X0 X1
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h13 X1 X2]
  have l2 : ∀ sK0 X0 X1 : G, sK0 = (X0 ◇ (X1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [h13 sK0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h4512 X0 X1 (sK0 ◇ sK0)]
  have l3 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0 sK0 sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK0 sK0]
  intro x y
  conv => enter [1]; rw [← l3 x]
  conv => enter [1]; rw [h13 x y]

@[equational_result]
theorem Equation13_implies_Equation3268 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation3268 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [h13 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation13_implies_Equation3288 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation3288 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [h13 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation13_implies_Equation3278 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation3278 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [h13 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation13_implies_Equation3258 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation3258 G := by
  intro x y
  conv => enter [1, 2]; rw [h13 x y]

@[equational_result]
theorem Equation13_implies_Equation4272 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation4272 G := by
  intro x y
  conv => enter [1]; rw [← h13 x x]
  conv => enter [1]; rw [h13 x y]

@[equational_result]
theorem Equation10_implies_Equation413 (G : Type*) [Magma G] (h10 : Equation10 G) : Equation413 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 sK0 sK1]
    conv => enter [1]; rw [h10 (sK0 ◇ (sK1 ◇ sK0)) sK0]
    conv => enter [1, 1]; rw [← h10 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation10_implies_Equation426 (G : Type*) [Magma G] (h10 : Equation10 G) : Equation426 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 sK0 sK0]
    conv => enter [1]; rw [h10 (sK0 ◇ (sK0 ◇ sK0)) sK1]
    conv => enter [1, 1]; rw [← h10 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation10_implies_Equation432 (G : Type*) [Magma G] (h10 : Equation10 G) : Equation432 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 sK0 sK2]
    conv => enter [1]; rw [h10 (sK0 ◇ (sK2 ◇ sK0)) sK1]
    conv => enter [1, 1]; rw [← h10 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation10_implies_Equation429 (G : Type*) [Magma G] (h10 : Equation10 G) : Equation429 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h10 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation10_implies_Equation3322 (G : Type*) [Magma G] (h10 : Equation10 G) : Equation3322 G := by
  intro x y z
  conv => enter [1, 2]; rw [h10 y z]

@[equational_result]
theorem Equation10_implies_Equation8 (G : Type*) [Magma G] (h10 : Equation10 G) : Equation8 G := by
  intro x
  conv => enter [1]; rw [h10 x x]

@[equational_result]
theorem Equation10_implies_Equation3316 (G : Type*) [Magma G] (h10 : Equation10 G) : Equation3316 G := by
  intro x y
  conv => enter [1, 2]; rw [h10 y x]

@[equational_result]
theorem Equation10_implies_Equation3255 (G : Type*) [Magma G] (h10 : Equation10 G) : Equation3255 G := by
  intro x y
  conv => enter [1, 2]; rw [h10 x y]

@[equational_result]
theorem Equation10_implies_Equation4269 (G : Type*) [Magma G] (h10 : Equation10 G) : Equation4269 G := by
  intro x y
  conv => enter [1]; rw [← h10 x x]
  conv => enter [1]; rw [h10 x y]

theorem Equation10_4512_implies_Equation3326 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation3326 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ sK1)) = ((sK2 ◇ (sK0 ◇ sK1)) ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [h10 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [← h10 (sK0 ◇ sK1) sK2]
  have l3 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h10 X0 X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l3 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l5 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 sK1 sK0]
  have l6 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ (sK0 ◇ X0)) := by
    intro sK0 X0 sK1
    conv => enter [1, 1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← h4512 (sK0 ◇ sK1) sK0 X0]
  have l7 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK2 sK1
    conv => enter [1, 2]; rw [l2 sK2 sK0 sK1]
    conv => enter [1]; rw [h4512 sK0 (sK2 ◇ (sK0 ◇ sK1)) (sK0 ◇ sK1)]
  have l8 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h10 (sK0 ◇ sK1) (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))]
    conv => enter [1, 2]; rw [← l7 sK0 sK2 sK1]
  have l9 : ∀ sK0 sK2 sK1 : G, (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) = ((sK0 ◇ sK1) ◇ (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1)))) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l4 sK0 (sK2 ◇ (sK0 ◇ sK1))]
    conv => enter [1]; rw [l6 sK0 (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) sK1]
    conv => enter [1, 2]; rw [← l4 sK0 (sK2 ◇ (sK0 ◇ sK1))]
  have l10 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l8 sK0 sK1 sK2]
    conv => enter [1]; rw [← l9 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l10 x y z]

theorem Equation10_4512_implies_Equation3258 (G : Type*) [Magma G] (h10 : Equation10 G) (h4512 : Equation4512 G) : Equation3258 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X1 ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h4512 X1 X0 X0]
  have l2 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [l1 X0 X0]
    conv => enter [1]; rw [← h10 X0 X0]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK0]
    conv => enter [1]; rw [h10 (sK0 ◇ sK0) sK1]
    conv => enter [1, 1]; rw [l2 sK0]
  intro x y
  conv => enter [1]; rw [l2 x]
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation11_implies_Equation414 (G : Type*) [Magma G] (h11 : Equation11 G) : Equation414 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 2, 2]; rw [← h11 sK0 sK1]
    conv => enter [1]; rw [← h11 X0 sK0]
  intro x y
  conv => enter [1]; rw [← l0 x x y]

@[equational_result]
theorem Equation11_implies_Equation436 (G : Type*) [Magma G] (h11 : Equation11 G) : Equation436 G := by
  have l0 : ∀ X0 sK1 sK0 : G, (X0 ◇ (sK1 ◇ (sK1 ◇ (sK0 ◇ sK0)))) = X0 := by
    intro X0 sK1 sK0
    conv => enter [1, 2, 2]; rw [← h11 sK1 sK0]
    conv => enter [1]; rw [← h11 X0 sK1]
  intro x y
  conv => enter [1]; rw [← l0 x y x]

@[equational_result]
theorem Equation11_implies_Equation440 (G : Type*) [Magma G] (h11 : Equation11 G) : Equation440 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h11 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h11 sK1 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation11_implies_Equation3323 (G : Type*) [Magma G] (h11 : Equation11 G) : Equation3323 G := by
  intro x y z
  conv => enter [1, 2]; rw [h11 y z]

@[equational_result]
theorem Equation11_implies_Equation3315 (G : Type*) [Magma G] (h11 : Equation11 G) : Equation3315 G := by
  intro x y
  conv => enter [1, 2]; rw [h11 y x]

@[equational_result]
theorem Equation11_implies_Equation8 (G : Type*) [Magma G] (h11 : Equation11 G) : Equation8 G := by
  intro x
  conv => enter [1]; rw [h11 x x]

@[equational_result]
theorem Equation11_implies_Equation3256 (G : Type*) [Magma G] (h11 : Equation11 G) : Equation3256 G := by
  intro x y
  conv => enter [1, 2]; rw [h11 x y]

@[equational_result]
theorem Equation11_implies_Equation4270 (G : Type*) [Magma G] (h11 : Equation11 G) : Equation4270 G := by
  intro x y
  conv => enter [1]; rw [← h11 x x]
  conv => enter [1]; rw [h11 x y]

@[equational_result]
theorem Equation16_implies_Equation500 (G : Type*) [Magma G] (h16 : Equation16 G) : Equation500 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h16 sK0 sK0]
    conv => enter [1]; rw [h16 (sK0 ◇ (sK0 ◇ sK0)) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation16_implies_Equation419 (G : Type*) [Magma G] (h16 : Equation16 G) : Equation419 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h16 sK0 sK1]
    conv => enter [1]; rw [h16 (sK1 ◇ (sK1 ◇ sK0)) sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation16_implies_Equation513 (G : Type*) [Magma G] (h16 : Equation16 G) : Equation513 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h16 sK0 sK1]
    conv => enter [1, 2, 2]; rw [h16 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation16_implies_Equation3414 (G : Type*) [Magma G] (h16 : Equation16 G) : Equation3414 G := by
  intro x y z
  conv => enter [1]; rw [h16 (x ◇ y) z]

@[equational_result]
theorem Equation16_implies_Equation3353 (G : Type*) [Magma G] (h16 : Equation16 G) : Equation3353 G := by
  intro x y
  conv => enter [1]; rw [h16 (x ◇ y) y]

@[equational_result]
theorem Equation16_implies_Equation8 (G : Type*) [Magma G] (h16 : Equation16 G) : Equation8 G := by
  intro x
  conv => enter [1]; rw [h16 x x]

@[equational_result]
theorem Equation16_implies_Equation3278 (G : Type*) [Magma G] (h16 : Equation16 G) : Equation3278 G := by
  intro x y
  conv => enter [1]; rw [h16 (x ◇ x) y]

@[equational_result]
theorem Equation16_implies_Equation4275 (G : Type*) [Magma G] (h16 : Equation16 G) : Equation4275 G := by
  intro x y
  conv => enter [1]; rw [← h16 x x]
  conv => enter [1]; rw [h16 x y]

@[equational_result]
theorem Equation13_implies_Equation469 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation469 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK2 sK0 X0 : G, (sK2 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK2]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 sK2 : G, sK0 = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h13 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK2]
  have l3 : ∀ sK2 sK0 : G, (sK2 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0
    conv => enter [1]; rw [l1 sK2 sK0 sK0]
    conv => enter [1, 2]; rw [l2 sK0 sK0 sK2]
  have l4 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) = ((sK2 ◇ sK0) ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [← l0 (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0))) sK1]
    conv => enter [1, 1]; rw [← l3 sK2 sK0]
    conv => enter [1, 2]; rw [← l3 sK2 sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 (sK2 ◇ sK0) sK2]
    conv => enter [1]; rw [← l4 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation13_implies_Equation476 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation476 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h13 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK1]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l3 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation13_implies_Equation503 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation503 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h13 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l2 sK0 sK0 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0 sK0]
    conv => enter [1]; rw [← l3 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l4 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation13_implies_Equation506 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation506 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK2 sK0 X0 : G, (sK2 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK2]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 sK2 : G, sK0 = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h13 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK2]
  have l3 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) = (sK0 ◇ sK0) := by
    intro sK1 sK0 sK2
    conv => enter [1, 2]; rw [← l2 sK0 sK0 sK2]
    conv => enter [1]; rw [← l0 sK0 sK1]
  have l4 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l1 sK2 sK0 sK0]
    conv => enter [1]; rw [← l3 sK1 sK0 sK2]
  have l5 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l4 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation13_implies_Equation541 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation541 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h13 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  have l3 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) = (sK0 ◇ sK0) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [← l0 (sK0 ◇ (sK1 ◇ sK0)) sK2]
    conv => enter [1, 1]; rw [← l2 sK0 sK0 sK1]
    conv => enter [1, 2]; rw [← l2 sK0 sK0 sK1]
  have l4 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l1 sK1 sK0 sK0]
    conv => enter [1]; rw [← l3 sK2 sK0 sK1]
  have l5 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l4 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation13_implies_Equation558 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation558 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l0 X1 X2]
  have l2 : ∀ sK1 sK0 X0 sK2 : G, (sK1 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK2 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK1 sK0 X0 sK2
    conv => enter [1]; rw [h13 (sK1 ◇ (sK1 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [l0 (sK1 ◇ (sK1 ◇ sK0)) sK2]
  have l3 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h13 sK0 X0]
    conv => enter [1, 2]; rw [l1 sK0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l3 x y y]
  conv => enter [1]; rw [l2 y x y z]

@[equational_result]
theorem Equation13_implies_Equation16 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation16 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h13 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y y]

@[equational_result]
theorem Equation13_implies_Equation39 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation39 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h13 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h13 sK0 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation13_implies_Equation466 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation466 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h13 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [l2 sK0 sK0 sK1]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l3 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation13_implies_Equation562 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation562 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK2 sK0 X0 : G, (sK2 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK2]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 sK2 : G, sK0 = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h13 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK2]
  have l3 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK0 ◇ sK0) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [← l2 sK0 sK1 sK2]
    conv => enter [1]; rw [← l0 sK0 sK2]
  have l4 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK0) = (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l1 sK2 sK0 sK0]
    conv => enter [1]; rw [← l3 sK2 sK1 sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2]
    conv => enter [1, 2]; rw [l4 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation13_implies_Equation575 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation575 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h13 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  have l3 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))) = (sK0 ◇ sK0) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [← l2 sK0 sK2 sK1]
    conv => enter [1]; rw [← l0 sK0 sK2]
  have l4 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l1 sK1 sK0 sK0]
    conv => enter [1]; rw [← l3 sK2 sK1 sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l4 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation13_implies_Equation3349 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation3349 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l0 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ sK1 X0 sK0 : G, sK1 = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h13 sK1 X0]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l0 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 sK2]
  have l4 : ∀ sK1 sK0 sK2 : G, sK1 = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l2 sK1 sK0 sK0]
    conv => enter [1, 2]; rw [l3 sK0 sK1 sK2]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l4 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation13_implies_Equation10 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation10 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h13 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x x y]

@[equational_result]
theorem Equation13_implies_Equation422 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation422 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1]; rw [← l0 (sK2 ◇ sK0) sK1]
    conv => enter [1]; rw [l0 (sK2 ◇ sK0) X0]
  have l2 : ∀ sK2 sK0 X0 sK1 : G, (sK2 ◇ sK0) = (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [h13 (sK2 ◇ sK0) X0]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ sK0) sK1]
  have l3 : ∀ sK0 X0 sK2 : G, sK0 = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h13 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK2]
  have l4 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (sK0 ◇ (sK0 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l1 sK1 sK2 sK0 sK0]
    conv => enter [1, 2]; rw [l2 sK2 sK0 sK0 sK1]
  have l5 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l3 sK0 (sK2 ◇ sK0) sK2]
    conv => enter [1]; rw [l0 (sK2 ◇ sK0) sK1]
  intro x y z
  conv => enter [1]; rw [l5 x y z]
  conv => enter [1]; rw [l4 y z x]

@[equational_result]
theorem Equation13_implies_Equation439 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation439 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h13 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  have l3 : ∀ sK1 sK0 : G, (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) = (sK0 ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [← l2 sK0 sK1 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l1 sK1 sK0 sK0]
    conv => enter [1]; rw [← l3 sK1 sK0]
  have l5 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0 sK0 sK1]
    conv => enter [1, 2]; rw [l4 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation13_implies_Equation442 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation442 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK2 sK0 X0 : G, (sK2 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK2 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK2]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 sK2 : G, sK0 = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h13 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK2]
  have l3 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [← l2 sK0 sK1 sK2]
    conv => enter [1]; rw [← l0 sK0 sK1]
  have l4 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK2 sK0 sK1
    conv => enter [1]; rw [l1 sK2 sK0 sK0]
    conv => enter [1]; rw [← l3 sK1 sK2 sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK0 sK2]
    conv => enter [1, 2]; rw [l4 sK2 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation13_implies_Equation450 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation450 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK1 sK0 X0 : G, (sK1 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 X0]
  have l2 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h13 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  have l3 : ∀ sK2 sK1 sK0 X0 : G, (sK2 ◇ (sK1 ◇ sK0)) = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK2 sK1 sK0 X0
    conv => enter [1]; rw [← l0 (sK1 ◇ sK0) sK2]
    conv => enter [1]; rw [l0 (sK1 ◇ sK0) X0]
  have l4 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [l2 sK0 sK0 sK1]
    conv => enter [1]; rw [l3 sK0 sK1 sK0 sK2]
  have l5 : ∀ sK1 sK2 sK0 : G, (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) = (sK0 ◇ sK0) := by
    intro sK1 sK2 sK0
    conv => enter [1, 2]; rw [← l4 sK0 sK2 sK1]
    conv => enter [1]; rw [← l0 sK0 sK1]
  have l6 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l1 sK1 sK0 sK0]
    conv => enter [1]; rw [← l5 sK1 sK2 sK0]
  have l7 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK0 sK1]
    conv => enter [1, 2]; rw [l6 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l7 x y z]

@[equational_result]
theorem Equation13_implies_Equation454 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation454 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK2 sK0 X0 sK1 : G, (sK2 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0)))) := by
    intro sK2 sK0 X0 sK1
    conv => enter [1]; rw [h13 (sK2 ◇ (sK2 ◇ sK0)) X0]
    conv => enter [1, 2]; rw [l0 (sK2 ◇ (sK2 ◇ sK0)) sK1]
  have l2 : ∀ sK0 X0 sK2 : G, sK0 = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h13 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x z z]
  conv => enter [1]; rw [l1 z x x y]

@[equational_result]
theorem Equation13_implies_Equation3388 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation3388 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l0 sK1 sK2]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ sK1 X0 sK2 : G, sK1 = (X0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h13 sK1 X0]
    conv => enter [1, 2]; rw [l0 sK1 sK2]
  have l3 : ∀ sK2 sK0 sK1 : G, (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) = (sK1 ◇ sK1) := by
    intro sK2 sK0 sK1
    conv => enter [1, 2]; rw [← l2 sK1 sK0 sK2]
    conv => enter [1]; rw [← l0 sK1 sK2]
  have l4 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK1 sK1]
    conv => enter [1]; rw [← l3 sK2 sK0 sK1]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [l4 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation13_implies_Equation3312 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation3312 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l0 sK1 sK2]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ sK1 X0 sK2 : G, sK1 = (X0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h13 sK1 X0]
    conv => enter [1, 2]; rw [l0 sK1 sK2]
  have l3 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [l2 sK1 sK0 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [l3 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation13_implies_Equation3330 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation3330 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK1 X0
    conv => enter [1]; rw [h13 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← h13 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK1 sK0 sK2 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1, 2]; rw [h13 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 y x]
  conv => enter [1]; rw [l2 y x z]

@[equational_result]
theorem Equation13_implies_Equation3363 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation3363 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l0 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ sK1 X0 sK0 : G, sK1 = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h13 sK1 X0]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  have l3 : ∀ sK2 sK0 sK1 X0 : G, (sK2 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← l0 (sK0 ◇ sK1) sK2]
    conv => enter [1]; rw [l0 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK1 sK2 sK0 : G, sK1 = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK2 sK0
    conv => enter [1]; rw [l2 sK1 sK1 sK0]
    conv => enter [1]; rw [l3 sK1 sK0 sK1 sK2]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l4 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation13_implies_Equation3397 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation3397 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l0 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ sK1 X0 sK0 : G, sK1 = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h13 sK1 X0]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  have l3 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK1)) = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← l0 (sK0 ◇ sK1) sK1]
    conv => enter [1]; rw [l0 (sK0 ◇ sK1) X0]
  have l4 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [l2 sK1 sK1 sK0]
  have l5 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) = (sK1 ◇ sK1) := by
    intro sK2 sK1 sK0
    conv => enter [1, 2]; rw [← l4 sK1 sK0]
    conv => enter [1]; rw [← l0 sK1 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK1 ◇ (sK0 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK1]
    conv => enter [1]; rw [← l5 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

@[equational_result]
theorem Equation13_implies_Equation3334 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation3334 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l0 sK1 sK2]
    conv => enter [1]; rw [l0 sK1 X0]
  have l2 : ∀ sK1 X0 sK2 : G, sK1 = (X0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 X0 sK2
    conv => enter [1]; rw [h13 sK1 X0]
    conv => enter [1, 2]; rw [l0 sK1 sK2]
  have l3 : ∀ sK2 sK1 sK0 : G, (sK2 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK2 sK1 sK0
    conv => enter [1]; rw [l1 sK2 sK1 sK0]
    conv => enter [1, 2]; rw [l2 sK1 sK2 sK2]
  have l4 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ (sK2 ◇ sK1))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK2]
    conv => enter [1]; rw [l3 sK2 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [l4 x y z]

@[equational_result]
theorem Equation13_implies_Equation3346 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation3346 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK1 X0
    conv => enter [1]; rw [h13 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← h13 sK1 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [← l0 y x]
  conv => enter [1, 2]; rw [h13 y x]

@[equational_result]
theorem Equation13_implies_Equation4278 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation4278 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h13 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h13 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h13 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [← h13 x x]
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation13_implies_Equation3309 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation3309 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK1 X0
    conv => enter [1]; rw [h13 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← h13 sK1 (sK1 ◇ sK1)]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK1 sK0
    conv => enter [1]; rw [l0 sK1 sK0]
    conv => enter [1, 2]; rw [h13 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l0 y x]
  conv => enter [1]; rw [l1 y x]

@[equational_result]
theorem Equation13_implies_Equation4287 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation4287 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK2 sK1 X0 : G, (sK2 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK2 sK1 X0
    conv => enter [1]; rw [← l0 sK1 sK2]
    conv => enter [1]; rw [l0 sK1 X0]
  intro x y z
  conv => enter [1, 2]; rw [l1 x y z]

@[equational_result]
theorem Equation13_implies_Equation4300 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation4300 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l0 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK1) sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation13_implies_Equation4330 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation4330 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK0)) = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l0 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [l0 (sK1 ◇ sK0) sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation13_implies_Equation4340 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation4340 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK1 X0
    conv => enter [1]; rw [h13 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← h13 sK1 (sK1 ◇ sK1)]
  have l1 : ∀ sK1 sK0 sK2 : G, sK1 = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK0 sK2
    conv => enter [1]; rw [h13 sK1 sK0]
    conv => enter [1, 2]; rw [l0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← h13 y x]
  conv => enter [1]; rw [l1 y x z]

@[equational_result]
theorem Equation13_implies_Equation3300 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation3300 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK1 X0
    conv => enter [1]; rw [h13 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← h13 sK1 (sK1 ◇ sK1)]
  have l2 : ∀ sK1 sK3 sK0 : G, sK1 = (sK3 ◇ (sK0 ◇ sK1)) := by
    intro sK1 sK3 sK0
    conv => enter [1]; rw [h13 sK1 sK3]
    conv => enter [1, 2]; rw [l1 sK1 sK0]
  have l3 : ∀ sK1 sK2 sK3 sK0 : G, (sK1 ◇ sK1) = (sK2 ◇ (sK3 ◇ (sK0 ◇ sK1))) := by
    intro sK1 sK2 sK3 sK0
    conv => enter [1]; rw [l0 sK1 sK2]
    conv => enter [1, 2]; rw [l2 sK1 sK3 sK0]
  intro x y z w
  conv => enter [1]; rw [l3 x y z w]

@[equational_result]
theorem Equation13_implies_Equation3274 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation3274 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h13 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h13 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 sK2 : G, sK0 = (sK0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h13 sK0 sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [l2 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation13_implies_Equation3292 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation3292 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h13 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h13 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 sK2 sK1 : G, sK0 = (sK2 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h13 sK0 sK2]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [l2 sK0 sK2 sK1]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation13_implies_Equation3281 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation3281 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h13 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h13 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h13 sK0 sK1]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation13_implies_Equation3284 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation3284 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h13 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h13 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h13 sK0 sK1]
    conv => enter [1, 2]; rw [l1 sK0 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [l2 sK0 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation13_implies_Equation3296 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation3296 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h13 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h13 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 sK2 : G, sK0 = (sK2 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK2
    conv => enter [1]; rw [h13 sK0 sK2]
    conv => enter [1, 2]; rw [l1 sK0 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ (sK2 ◇ sK0))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [l2 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation13_implies_Equation3264 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation3264 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h13 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h13 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h13 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK2]
  intro x y z
  conv => enter [1, 2]; rw [l1 x y z]

@[equational_result]
theorem Equation13_implies_Equation3271 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation3271 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h13 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h13 sK0 (sK0 ◇ sK0)]
  have l2 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h13 sK0 sK0]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1, 2]; rw [l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation13_implies_Equation3261 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation3261 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h13 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h13 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h13 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1, 2]; rw [l1 x y]

@[equational_result]
theorem Equation13_implies_Equation4296 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation4296 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK1 X0 sK0 : G, sK1 = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h13 sK1 X0]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l0 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 sK2]
  have l3 : ∀ sK1 sK2 : G, sK1 = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK1 sK2
    conv => enter [1]; rw [l1 sK1 sK1 sK1]
    conv => enter [1, 2]; rw [l2 sK1 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [← l1 y x x]
  conv => enter [1]; rw [l3 y z]

@[equational_result]
theorem Equation13_implies_Equation4327 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation4327 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h13 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h13 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h13 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y z
  conv => enter [1]; rw [← l1 x x y]
  conv => enter [1]; rw [h13 x z]

@[equational_result]
theorem Equation13_implies_Equation4362 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation4362 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [l0 X1 X2]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ (sK1 ◇ sK2)) = (sK1 ◇ (sK0 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 (sK1 ◇ sK2) sK1]
    conv => enter [1, 2]; rw [l1 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation13_implies_Equation4304 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation4304 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK1 X0
    conv => enter [1]; rw [h13 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← h13 sK1 (sK1 ◇ sK1)]
  have l1 : ∀ sK1 X0 sK0 : G, sK1 = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h13 sK1 X0]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  intro x y z
  conv => enter [1]; rw [← l1 y x x]
  conv => enter [1]; rw [h13 y z]

@[equational_result]
theorem Equation13_implies_Equation4291 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation4291 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ (sK0 ◇ sK1)) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 (sK0 ◇ sK1) sK0]
    conv => enter [1]; rw [l0 (sK0 ◇ sK1) sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation13_implies_Equation4320 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation4320 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h13 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h13 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h13 sK0 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← l1 x y]
  conv => enter [1]; rw [h13 x y]

@[equational_result]
theorem Equation13_implies_Equation4284 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation4284 G := by
  have l0 : ∀ sK1 X0 : G, (sK1 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK1 X0
    conv => enter [1]; rw [h13 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← h13 sK1 (sK1 ◇ sK1)]
  have l1 : ∀ sK1 X0 sK0 : G, sK1 = (X0 ◇ (sK0 ◇ sK1)) := by
    intro sK1 X0 sK0
    conv => enter [1]; rw [h13 sK1 X0]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [← l1 y x x]
  conv => enter [1]; rw [h13 y x]

theorem Equation9_4512_implies_Equation428 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation428 G := by
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
  intro x y z
  conv => enter [1]; rw [← l2 x (y ◇ (x ◇ (x ◇ z)))]

theorem Equation9_4512_implies_Equation430 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation430 G := by
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
  conv => enter [1]; rw [← l2 x (y ◇ (x ◇ (y ◇ y)))]

theorem Equation9_4512_implies_Equation433 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation433 G := by
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
  intro x y z
  conv => enter [1]; rw [← l2 x (y ◇ (x ◇ (z ◇ y)))]

theorem Equation9_4512_implies_Equation434 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation434 G := by
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
  intro x y z
  conv => enter [1]; rw [← l2 x (y ◇ (x ◇ (z ◇ z)))]

theorem Equation9_4512_implies_Equation437 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation437 G := by
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
  conv => enter [1]; rw [← l2 x (y ◇ (y ◇ (x ◇ y)))]

theorem Equation9_4512_implies_Equation443 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation443 G := by
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
  have l3 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK1)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l2 sK0 sK1]
    conv => enter [1, 2]; rw [h9 sK1 (sK2 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation9_4512_implies_Equation11 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation11 G := by
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
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l2 sK0 sK1]
    conv => enter [1, 2]; rw [← l0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation9_4512_implies_Equation38 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation38 G := by
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
  conv => enter [1]; rw [l0 x]
  conv => enter [1]; rw [← l2 x y]

theorem Equation9_4512_implies_Equation427 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation427 G := by
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
  conv => enter [1]; rw [← l2 x (y ◇ (x ◇ (x ◇ y)))]

theorem Equation9_4512_implies_Equation452 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation452 G := by
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
  intro x y z
  conv => enter [1]; rw [← l2 x (y ◇ (z ◇ (y ◇ z)))]

theorem Equation9_4512_implies_Equation455 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation455 G := by
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
  intro x y z
  conv => enter [1]; rw [← l2 x (y ◇ (z ◇ (z ◇ y)))]

theorem Equation9_4512_implies_Equation3329 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation3329 G := by
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
  intro x y z
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [← l2 x (z ◇ (y ◇ x))]

theorem Equation9_4512_implies_Equation10 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation10 G := by
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
  conv => enter [1]; rw [← l2 x (y ◇ x)]

theorem Equation9_4512_implies_Equation439 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation439 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h9 X0 X0]
    conv => enter [1]; rw [← h9 X0 (X0 ◇ X0)]
  have l1 : ∀ sK1 sK0 : G, sK1 = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l0 sK1]
    conv => enter [1, 2]; rw [h9 sK1 sK0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h9 X0 X1]
  have l4 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 sK0 sK1]
    conv => enter [1, 2]; rw [l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation9_4512_implies_Equation442 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation442 G := by
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
  have l3 : ∀ sK0 sK1 sK2 : G, sK0 = (sK0 ◇ (sK1 ◇ (sK1 ◇ (sK2 ◇ sK0)))) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l2 sK0 sK1]
    conv => enter [1, 2]; rw [h9 sK1 (sK2 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

theorem Equation9_4512_implies_Equation446 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation446 G := by
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
  intro x y z
  conv => enter [1]; rw [← l2 x (y ◇ (z ◇ (x ◇ x)))]

theorem Equation9_4512_implies_Equation450 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation450 G := by
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
  intro x y z
  conv => enter [1]; rw [← l2 x (y ◇ (z ◇ (y ◇ x)))]

theorem Equation9_4512_implies_Equation454 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation454 G := by
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
  intro x y z
  conv => enter [1]; rw [← l2 x (y ◇ (z ◇ (z ◇ x)))]

theorem Equation9_4512_implies_Equation3331 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation3331 G := by
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
  intro x y z
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [← l2 x (z ◇ (y ◇ z))]

theorem Equation9_4512_implies_Equation3312 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation3312 G := by
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
  intro x y z
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [h9 x (z ◇ y)]

theorem Equation9_4512_implies_Equation3317 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation3317 G := by
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
  intro x y z
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [← l2 x (y ◇ (x ◇ z))]

theorem Equation9_4512_implies_Equation3321 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation3321 G := by
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
  intro x y z
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [← l2 x (y ◇ (z ◇ x))]

theorem Equation9_4512_implies_Equation3330 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation3330 G := by
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
  intro x y z
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [← l2 x (z ◇ (y ◇ y))]

theorem Equation9_4512_implies_Equation3308 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation3308 G := by
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
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [h9 x (y ◇ x)]

theorem Equation9_4512_implies_Equation3334 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation3334 G := by
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
  intro x y z
  conv => enter [1]; rw [l2 x y]
  conv => enter [1]; rw [← l2 x (z ◇ (z ◇ y))]

theorem Equation9_4512_implies_Equation4271 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation4271 G := by
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
  intro x y z
  conv => enter [1]; rw [← h9 x x]
  conv => enter [1]; rw [← l2 x (y ◇ z)]

theorem Equation9_4512_implies_Equation3309 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation3309 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h9 X0 X0]
    conv => enter [1]; rw [← h9 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [h9 sK0 sK1]
    conv => enter [1, 2, 2]; rw [← l0 sK1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h4512 X0 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← h9 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]
  conv => enter [1]; rw [l1 x y]

theorem Equation9_4512_implies_Equation4287 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation4287 G := by
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
  intro x y z
  conv => enter [1]; rw [← h9 x y]
  conv => enter [1]; rw [← l2 x (z ◇ y)]

theorem Equation9_4512_implies_Equation4315 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation4315 G := by
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
  intro x y z
  conv => enter [1]; rw [l2 x (y ◇ x)]
  conv => enter [1]; rw [← l2 x (y ◇ z)]

theorem Equation9_4512_implies_Equation4339 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation4339 G := by
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
  intro x y z
  conv => enter [1]; rw [l2 x (y ◇ y)]
  conv => enter [1]; rw [← l2 x (y ◇ z)]

theorem Equation9_4512_implies_Equation4340 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation4340 G := by
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
  intro x y z
  conv => enter [1]; rw [l2 x (y ◇ y)]
  conv => enter [1]; rw [← l2 x (z ◇ y)]

theorem Equation9_4512_implies_Equation3267 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation3267 G := by
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
  intro x y z w
  conv => enter [1]; rw [l0 x]
  conv => enter [1]; rw [← l2 x (y ◇ (z ◇ w))]

theorem Equation9_4512_implies_Equation3260 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation3260 G := by
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
  intro x y z
  conv => enter [1]; rw [l0 x]
  conv => enter [1]; rw [← l2 x (y ◇ (x ◇ z))]

theorem Equation9_4512_implies_Equation3265 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation3265 G := by
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
  intro x y z
  conv => enter [1]; rw [l0 x]
  conv => enter [1]; rw [← l2 x (y ◇ (z ◇ y))]

theorem Equation9_4512_implies_Equation3262 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation3262 G := by
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
  conv => enter [1]; rw [l0 x]
  conv => enter [1]; rw [← l2 x (y ◇ (y ◇ y))]

theorem Equation9_4512_implies_Equation3263 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation3263 G := by
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
  intro x y z
  conv => enter [1]; rw [l0 x]
  conv => enter [1]; rw [← l2 x (y ◇ (y ◇ z))]

theorem Equation9_4512_implies_Equation3266 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation3266 G := by
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
  intro x y z
  conv => enter [1]; rw [l0 x]
  conv => enter [1]; rw [← l2 x (y ◇ (z ◇ z))]

theorem Equation9_4512_implies_Equation3259 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation3259 G := by
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
  conv => enter [1]; rw [l0 x]
  conv => enter [1]; rw [← l2 x (y ◇ (x ◇ y))]

theorem Equation9_4512_implies_Equation3264 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation3264 G := by
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
  intro x y z
  conv => enter [1]; rw [l0 x]
  conv => enter [1]; rw [← l2 x (y ◇ (z ◇ x))]

theorem Equation9_4512_implies_Equation3261 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation3261 G := by
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
  conv => enter [1]; rw [l0 x]
  conv => enter [1]; rw [← l2 x (y ◇ (y ◇ x))]

theorem Equation9_4512_implies_Equation4286 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation4286 G := by
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
  intro x y z
  conv => enter [1]; rw [← h9 x y]
  conv => enter [1]; rw [← l2 x (z ◇ x)]

theorem Equation9_4512_implies_Equation4318 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation4318 G := by
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
  intro x y z
  conv => enter [1]; rw [l2 x (y ◇ x)]
  conv => enter [1]; rw [← l2 x (z ◇ z)]

theorem Equation9_4512_implies_Equation4358 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation4358 G := by
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
  intro x y z
  conv => enter [1]; rw [l2 x (y ◇ z)]
  conv => enter [1]; rw [← l2 x (z ◇ y)]

theorem Equation9_4512_implies_Equation4288 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation4288 G := by
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
  intro x y z
  conv => enter [1]; rw [← h9 x y]
  conv => enter [1]; rw [← l2 x (z ◇ z)]

theorem Equation9_4512_implies_Equation4314 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation4314 G := by
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
  conv => enter [1]; rw [l2 x (y ◇ x)]
  conv => enter [1]; rw [← l2 x (y ◇ y)]

theorem Equation9_4512_implies_Equation4283 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation4283 G := by
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
  conv => enter [1]; rw [← h9 x y]
  conv => enter [1]; rw [← l2 x (y ◇ x)]

theorem Equation9_4512_implies_Equation4284 (G : Type*) [Magma G] (h9 : Equation9 G) (h4512 : Equation4512 G) : Equation4284 G := by
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
  conv => enter [1]; rw [← h9 x y]
  conv => enter [1]; rw [← l2 x y]
  conv => enter [1, 2]; rw [← l0 y]

end Semigroup4
