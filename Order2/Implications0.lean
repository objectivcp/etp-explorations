import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Order2

@[equational_result]
theorem Equation2_implies_Equation4 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation4 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation5 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation5 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation41 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation41 G := by
  intro x y z
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ z)]

@[equational_result]
theorem Equation2_implies_Equation13 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation13 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation24 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation24 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((x ◇ x) ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation38 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation38 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 x y]

@[equational_result]
theorem Equation2_implies_Equation39 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation39 G := by
  intro x y
  conv => enter [1, 1]; rw [h2 x y]

@[equational_result]
theorem Equation2_implies_Equation9 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation9 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation28 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation28 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((y ◇ x) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation14 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation14 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation29 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation29 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((y ◇ x) ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation10 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation10 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation25 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation25 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((x ◇ y) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation43 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation43 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ y) (y ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation11 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation11 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation31 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation31 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((y ◇ y) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation16 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation16 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation26 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation26 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((x ◇ y) ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation40 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation40 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation3 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3 G := by
  intro x
  conv => enter [1]; rw [h2 x (x ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation8 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation8 G := by
  intro x
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation23 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation23 G := by
  intro x
  conv => enter [1]; rw [h2 x ((x ◇ x) ◇ x)]

@[equational_result]
theorem Equation3_implies_Equation8 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation8 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation3_implies_Equation23 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation23 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [h3 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation4_implies_Equation24 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation24 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4 sK0 sK0]
    conv => enter [1]; rw [h4 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation4_implies_Equation38 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation38 G := by
  intro x y
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x y]

@[equational_result]
theorem Equation4_implies_Equation9 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation9 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation10 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation10 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ x)]

@[equational_result]
theorem Equation4_implies_Equation25 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation25 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4 sK0 sK1]
    conv => enter [1]; rw [h4 (sK0 ◇ sK1) sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation4_implies_Equation11 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation11 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation26 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation26 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4 sK0 sK1]
    conv => enter [1, 1]; rw [h4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation4_implies_Equation3 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3 G := by
  intro x
  conv => enter [1]; rw [h4 x x]

@[equational_result]
theorem Equation5_implies_Equation13 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation13 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation39 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation39 G := by
  intro x y
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [h5 x y]

@[equational_result]
theorem Equation5_implies_Equation28 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation28 G := by
  intro x y
  conv => enter [1]; rw [h5 x (y ◇ x)]

@[equational_result]
theorem Equation5_implies_Equation10 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation10 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation25 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation25 G := by
  intro x y
  conv => enter [1]; rw [h5 x (x ◇ y)]

@[equational_result]
theorem Equation5_implies_Equation31 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation31 G := by
  intro x y
  conv => enter [1]; rw [h5 x (y ◇ y)]

@[equational_result]
theorem Equation5_implies_Equation16 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation16 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation3 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3 G := by
  intro x
  conv => enter [1]; rw [h5 x x]

@[equational_result]
theorem Equation9_implies_Equation3 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h9 X0 X0]
    conv => enter [1]; rw [← h9 X0 (X0 ◇ X0)]
  intro x
  conv => enter [1]; rw [← l0 x]

@[equational_result]
theorem Equation28_implies_Equation3 (G : Type*) [Magma G] (h28 : Equation28 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h28 X0 X0]
    conv => enter [1]; rw [← h28 X0 (X0 ◇ X0)]
  intro x
  conv => enter [1]; rw [← l0 x]

@[equational_result]
theorem Equation10_implies_Equation8 (G : Type*) [Magma G] (h10 : Equation10 G) : Equation8 G := by
  intro x
  conv => enter [1]; rw [h10 x x]

@[equational_result]
theorem Equation25_implies_Equation23 (G : Type*) [Magma G] (h25 : Equation25 G) : Equation23 G := by
  intro x
  conv => enter [1]; rw [h25 x x]

@[equational_result]
theorem Equation11_implies_Equation8 (G : Type*) [Magma G] (h11 : Equation11 G) : Equation8 G := by
  intro x
  conv => enter [1]; rw [h11 x x]

@[equational_result]
theorem Equation31_implies_Equation23 (G : Type*) [Magma G] (h31 : Equation31 G) : Equation23 G := by
  intro x
  conv => enter [1]; rw [h31 x x]

@[equational_result]
theorem Equation13_implies_Equation39 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation39 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h13 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h13 sK0 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l0 x y]

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
theorem Equation24_implies_Equation38 (G : Type*) [Magma G] (h24 : Equation24 G) : Equation38 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h24 (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h24 sK0 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation24_implies_Equation25 (G : Type*) [Magma G] (h24 : Equation24 G) : Equation25 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h24 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h24 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h24 sK0 X0]
    conv => enter [1, 1]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y x]

@[equational_result]
theorem Equation24_implies_Equation26 (G : Type*) [Magma G] (h24 : Equation24 G) : Equation26 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h24 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h24 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h24 sK0 X0]
    conv => enter [1, 1]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y y]

@[equational_result]
theorem Equation14_implies_Equation29 (G : Type*) [Magma G] (h14 : Equation14 G) : Equation29 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h14 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation14_implies_Equation8 (G : Type*) [Magma G] (h14 : Equation14 G) : Equation8 G := by
  intro x
  conv => enter [1]; rw [h14 x x]

@[equational_result]
theorem Equation14_implies_Equation23 (G : Type*) [Magma G] (h14 : Equation14 G) : Equation23 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h14 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h14 sK0 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation29_implies_Equation14 (G : Type*) [Magma G] (h29 : Equation29 G) : Equation14 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h29 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 1]; rw [← h29 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation16_implies_Equation8 (G : Type*) [Magma G] (h16 : Equation16 G) : Equation8 G := by
  intro x
  conv => enter [1]; rw [h16 x x]

@[equational_result]
theorem Equation26_implies_Equation23 (G : Type*) [Magma G] (h26 : Equation26 G) : Equation23 G := by
  intro x
  conv => enter [1]; rw [h26 x x]

@[equational_result]
theorem Equation41_implies_Equation38 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation38 G := by
  intro x y
  conv => enter [1]; rw [h41 x x y]

@[equational_result]
theorem Equation41_implies_Equation39 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation39 G := by
  intro x y
  conv => enter [1]; rw [h41 x y x]

@[equational_result]
theorem Equation41_implies_Equation43 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation43 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation41_implies_Equation40 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation40 G := by
  intro x y
  conv => enter [1]; rw [h41 x y y]

theorem Equation39_43_implies_Equation41 (G : Type*) [Magma G] (h39 : Equation39 G) (h43 : Equation43 G) : Equation41 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h39 sK0 X0]
    conv => enter [1]; rw [h43 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [h39 X0 sK0]
    conv => enter [1]; rw [← l0 sK0 X0]
  have l2 : ∀ X1 X0 sK0 : G, (X1 ◇ X0) = (sK0 ◇ sK0) := by
    intro X1 X0 sK0
    conv => enter [1]; rw [← h39 X0 X1]
    conv => enter [1]; rw [l1 X0 sK0]
  intro x y z
  conv => enter [1]; rw [← l2 y z x]

theorem Equation38_43_implies_Equation41 (G : Type*) [Magma G] (h38 : Equation38 G) (h43 : Equation43 G) : Equation41 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (sK1 ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 X0]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h38 sK0 X0]
    conv => enter [1]; rw [h43 sK0 X0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

theorem Equation39_40_implies_Equation41 (G : Type*) [Magma G] (h39 : Equation39 G) (h40 : Equation40 G) : Equation41 G := by
  have l0 : ∀ X0 X2 X1 : G, (X0 ◇ X0) = (X2 ◇ X1) := by
    intro X0 X2 X1
    conv => enter [1]; rw [h40 X0 X1]
    conv => enter [1]; rw [h39 X1 X2]
  have l1 : ∀ sK0 X2 X1 : G, (sK0 ◇ sK0) = (X2 ◇ X1) := by
    intro sK0 X2 X1
    conv => enter [1]; rw [l0 sK0 X2 X1]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation38_40_implies_Equation41 (G : Type*) [Magma G] (h38 : Equation38 G) (h40 : Equation40 G) : Equation41 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (sK1 ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h40 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation38_39_implies_Equation41 (G : Type*) [Magma G] (h38 : Equation38 G) (h39 : Equation39 G) : Equation41 G := by
  have l0 : ∀ sK1 sK2 X0 : G, (sK1 ◇ sK2) = (sK1 ◇ X0) := by
    intro sK1 sK2 X0
    conv => enter [1]; rw [← h38 sK1 sK2]
    conv => enter [1]; rw [h38 sK1 X0]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h39 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

theorem Equation23_43_implies_Equation8 (G : Type*) [Magma G] (h23 : Equation23 G) (h43 : Equation43 G) : Equation8 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1]; rw [h43 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h23 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation8_43_implies_Equation23 (G : Type*) [Magma G] (h8 : Equation8 G) (h43 : Equation43 G) : Equation23 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h8 sK0]
    conv => enter [1]; rw [h43 sK0 (sK0 ◇ sK0)]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation23_40_implies_Equation31 (G : Type*) [Magma G] (h23 : Equation23 G) (h40 : Equation40 G) : Equation31 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h40 X0 X1]
    conv => enter [1]; rw [← h23 X1]
  have l1 : ∀ sK1 X1 : G, ((sK1 ◇ sK1) ◇ X1) = X1 := by
    intro sK1 X1
    conv => enter [1]; rw [l0 sK1 X1]
  intro x y
  conv => enter [1]; rw [← l1 y x]

theorem Equation8_40_implies_Equation11 (G : Type*) [Magma G] (h8 : Equation8 G) (h40 : Equation40 G) : Equation11 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = X0 := by
    intro X0 sK1
    conv => enter [1, 2]; rw [h40 sK1 X0]
    conv => enter [1]; rw [← h8 X0]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation23_39_implies_Equation5 (G : Type*) [Magma G] (h23 : Equation23 G) (h39 : Equation39 G) : Equation5 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h39 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h23 X0]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0]
    conv => enter [1]; rw [h39 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation8_38_implies_Equation4 (G : Type*) [Magma G] (h8 : Equation8 G) (h38 : Equation38 G) : Equation4 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1]; rw [h38 X0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h8 X0]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0]
    conv => enter [1]; rw [h38 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation23_38_implies_Equation24 (G : Type*) [Magma G] (h23 : Equation23 G) (h38 : Equation38 G) : Equation24 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h38 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [h38 (sK0 ◇ sK0) X0]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h23 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation8_39_implies_Equation13 (G : Type*) [Magma G] (h8 : Equation8 G) (h39 : Equation39 G) : Equation13 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (sK1 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [← h39 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [h39 (sK0 ◇ sK0) X0]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h8 sK0]
    conv => enter [1]; rw [l0 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation26_31_implies_Equation40 (G : Type*) [Magma G] (h26 : Equation26 G) (h31 : Equation31 G) : Equation40 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1, 1]; rw [h31 X0 sK0]
    conv => enter [1]; rw [← h26 (sK0 ◇ sK0) X0]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1, 1]; rw [h31 X0 sK1]
    conv => enter [1]; rw [← h26 (sK1 ◇ sK1) X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation11_16_implies_Equation40 (G : Type*) [Magma G] (h11 : Equation11 G) (h16 : Equation16 G) : Equation40 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [h11 X0 sK0]
    conv => enter [1]; rw [← h16 (sK0 ◇ sK0) X0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h11 (sK1 ◇ sK1) sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation25_26_implies_Equation24 (G : Type*) [Magma G] (h25 : Equation25 G) (h26 : Equation26 G) : Equation24 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h25 (sK0 ◇ sK0) sK0]
    conv => enter [1, 1]; rw [← h25 sK0 sK0]
  have l1 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h26 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← l0 sK0]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h26 ((sK0 ◇ sK0) ◇ sK1) (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← h25 (sK0 ◇ sK0) sK1]
  have l3 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation10_16_implies_Equation13 (G : Type*) [Magma G] (h10 : Equation10 G) (h16 : Equation16 G) : Equation13 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h10 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h16 (sK1 ◇ (sK0 ◇ sK0)) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h10 (sK0 ◇ sK0) sK1]
  have l2 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h16 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← l0 sK0]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1]; rw [← l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation31_43_implies_Equation11 (G : Type*) [Magma G] (h31 : Equation31 G) (h43 : Equation43 G) : Equation11 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = X0 := by
    intro X0 sK1
    conv => enter [1]; rw [h43 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h31 X0 sK1]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation31_43_implies_Equation40 (G : Type*) [Magma G] (h31 : Equation31 G) (h43 : Equation43 G) : Equation40 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = X0 := by
    intro X0 sK0
    conv => enter [1]; rw [h43 X0 (sK0 ◇ sK0)]
    conv => enter [1]; rw [← h31 X0 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h31 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [l0 (sK1 ◇ sK1) sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation11_43_implies_Equation31 (G : Type*) [Magma G] (h11 : Equation11 G) (h43 : Equation43 G) : Equation31 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h11 sK0 sK1]
    conv => enter [1]; rw [h43 sK0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation26_43_implies_Equation14 (G : Type*) [Magma G] (h26 : Equation26 G) (h43 : Equation43 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h26 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation26_43_implies_Equation16 (G : Type*) [Magma G] (h26 : Equation26 G) (h43 : Equation43 G) : Equation16 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [h43 X1 (X0 ◇ X1)]
    conv => enter [1]; rw [← h26 X0 X1]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK1 sK0]
    conv => enter [1, 2]; rw [h43 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation16_43_implies_Equation14 (G : Type*) [Magma G] (h16 : Equation16 G) (h43 : Equation43 G) : Equation14 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h16 X0 X1]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation16_43_implies_Equation26 (G : Type*) [Magma G] (h16 : Equation16 G) (h43 : Equation43 G) : Equation26 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X0 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h16 X0 X1]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK1 sK0]
    conv => enter [1]; rw [h43 sK1 (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation8_25_implies_Equation3 (G : Type*) [Magma G] (h8 : Equation8 G) (h25 : Equation25 G) : Equation3 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h25 (sK0 ◇ sK0) sK0]
    conv => enter [1, 1]; rw [← h25 sK0 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h8 sK0]
    conv => enter [1]; rw [← l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation10_23_implies_Equation3 (G : Type*) [Magma G] (h10 : Equation10 G) (h23 : Equation23 G) : Equation3 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h10 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h23 sK0]
    conv => enter [1]; rw [← l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation16_26_implies_Equation14 (G : Type*) [Magma G] (h16 : Equation16 G) (h26 : Equation26 G) : Equation14 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h26 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 1]; rw [← h16 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation16_26_implies_Equation43 (G : Type*) [Magma G] (h16 : Equation16 G) (h26 : Equation26 G) : Equation43 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h26 sK0 (sK0 ◇ sK1)]
    conv => enter [1, 1]; rw [← h16 sK1 sK0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = (sK0 ◇ sK1) := by
    intro sK1 sK0
    conv => enter [1, 2]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← h16 (sK0 ◇ sK1) sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation14_43_implies_Equation16 (G : Type*) [Magma G] (h14 : Equation14 G) (h43 : Equation43 G) : Equation16 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 sK0 sK1]
    conv => enter [1, 2]; rw [h43 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation14_31_implies_Equation11 (G : Type*) [Magma G] (h14 : Equation14 G) (h31 : Equation31 G) : Equation11 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← h31 (sK0 ◇ (sK1 ◇ sK1)) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation14_31_implies_Equation40 (G : Type*) [Magma G] (h14 : Equation14 G) (h31 : Equation31 G) : Equation40 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [h31 X0 sK0]
    conv => enter [1]; rw [← h14 (sK0 ◇ sK0) X0]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1, 2]; rw [h31 X0 sK1]
    conv => enter [1]; rw [← h14 (sK1 ◇ sK1) X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation11_14_implies_Equation31 (G : Type*) [Magma G] (h11 : Equation11 G) (h14 : Equation14 G) : Equation31 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (((sK1 ◇ sK1) ◇ sK0) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 sK0 ((sK1 ◇ sK1) ◇ sK0)]
    conv => enter [1, 2]; rw [← h14 (sK1 ◇ sK1) sK0]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← h11 ((sK1 ◇ sK1) ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation14_26_implies_Equation43 (G : Type*) [Magma G] (h14 : Equation14 G) (h26 : Equation26 G) : Equation43 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h14 sK0 (sK1 ◇ sK0)]
    conv => enter [1, 2]; rw [← h14 sK1 sK0]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [← h26 (sK1 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation14_16_implies_Equation43 (G : Type*) [Magma G] (h14 : Equation14 G) (h16 : Equation16 G) : Equation43 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1, 2]; rw [h14 sK1 sK0]
    conv => enter [1]; rw [← h16 (sK1 ◇ sK0) sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation11_31_implies_Equation40 (G : Type*) [Magma G] (h11 : Equation11 G) (h31 : Equation31 G) : Equation40 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h11 (sK0 ◇ sK0) sK1]
    conv => enter [1]; rw [← h31 (sK1 ◇ sK1) sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation3_31_implies_Equation5 (G : Type*) [Magma G] (h3 : Equation3 G) (h31 : Equation31 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h3 X0]
    conv => enter [1]; rw [← h31 X1 X0]
  intro x y
  conv => enter [1]; rw [← l0 y x]

theorem Equation3_11_implies_Equation4 (G : Type*) [Magma G] (h3 : Equation3 G) (h11 : Equation11 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h3 X0]
    conv => enter [1]; rw [← h11 X1 X0]
  intro x y
  conv => enter [1]; rw [← l0 x y]

theorem Equation28_43_implies_Equation2 (G : Type*) [Magma G] (h28 : Equation28 G) (h43 : Equation43 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X1 ◇ X0)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← h28 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [h43 (X1 ◇ X0) X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 X0 X1]
    conv => enter [1]; rw [l3 X1 X0]
  have l5 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l4 X0 X1]
    conv => enter [1]; rw [l3 X0 X1]
  intro x y
  conv => enter [1]; rw [l5 x y]

theorem Equation9_43_implies_Equation2 (G : Type*) [Magma G] (h9 : Equation9 G) (h43 : Equation43 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h43 X0 X1]
    conv => enter [1]; rw [← h9 X1 X0]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l0 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h9 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l0 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l2 X1 X0]
    conv => enter [1]; rw [h43 (X1 ◇ X0) X0]
  have l4 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X0]
  have l5 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [l0 X0 X1]
  have l6 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l4 X0 X1]
    conv => enter [1]; rw [← h9 X0 X1]
  have l7 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l6 X0 X1]
    conv => enter [1]; rw [l5 X0 X1]
  intro x y
  conv => enter [1]; rw [l7 x y]

theorem Equation26_28_implies_Equation2 (G : Type*) [Magma G] (h26 : Equation26 G) (h28 : Equation28 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h28 X0 X1]
    conv => enter [1]; rw [← h26 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation9_16_implies_Equation2 (G : Type*) [Magma G] (h9 : Equation9 G) (h16 : Equation16 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h16 X0 X1]
    conv => enter [1]; rw [← h9 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation25_43_implies_Equation2 (G : Type*) [Magma G] (h25 : Equation25 G) (h43 : Equation43 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X1)) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 X0 (X0 ◇ X1)]
    conv => enter [1]; rw [← h25 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h43 X0 X1]
    conv => enter [1]; rw [l0 X1 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [← l1 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [l0 X0 X1]
  have l3 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [← l1 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [l1 X0 X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [h43 (X1 ◇ X0) X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [h43 (X0 ◇ X1) X0]
  have l6 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l4 X1 X0]
    conv => enter [1]; rw [l1 X0 X1]
  have l7 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l5 X0 X1]
    conv => enter [1]; rw [l0 X0 X1]
  have l8 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l7 X0 X1]
    conv => enter [1]; rw [l6 X0 X1]
  intro x y
  conv => enter [1]; rw [l8 x y]

theorem Equation10_43_implies_Equation2 (G : Type*) [Magma G] (h10 : Equation10 G) (h43 : Equation43 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = (X0 ◇ (X1 ◇ X0)) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [h43 (X1 ◇ X0) X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h10 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [h43 X0 X1]
    conv => enter [1]; rw [l2 X1 X0]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

theorem Equation16_25_implies_Equation5 (G : Type*) [Magma G] (h16 : Equation16 G) (h25 : Equation25 G) : Equation5 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h16 X0 X1]
    conv => enter [1]; rw [← h25 X1 (X1 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h16 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation10_26_implies_Equation4 (G : Type*) [Magma G] (h10 : Equation10 G) (h26 : Equation26 G) : Equation4 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 1]; rw [h26 X1 X0]
    conv => enter [1, 1]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h26 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y]

theorem Equation3_14_28_implies_Equation2 (G : Type*) [Magma G] (h3 : Equation3 G) (h14 : Equation14 G) (h28 : Equation28 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1, 2]; rw [h28 X0 X1]
    conv => enter [1]; rw [← h14 (X1 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h3 X0]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l1 X1 X0]
    conv => enter [1]; rw [← h14 X1 X0]
  have l3 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l1 X0 X0]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation9_14_implies_Equation2 (G : Type*) [Magma G] (h9 : Equation9 G) (h14 : Equation14 G) : Equation2 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [h14 X0 X1]
    conv => enter [1]; rw [← h9 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 (X1 ◇ X0)]
    conv => enter [1]; rw [← h14 X1 X0]
  intro x y
  conv => enter [1]; rw [l1 x y]

theorem Equation14_25_implies_Equation2 (G : Type*) [Magma G] (h14 : Equation14 G) (h25 : Equation25 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = X1 := by
    intro X0 X1
    conv => enter [1, 1]; rw [h14 X0 X1]
    conv => enter [1]; rw [← h25 X1 (X0 ◇ X1)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X0) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X1 X0]
    conv => enter [1]; rw [← h14 X1 X0]
  have l2 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l0 X0 X0]
    conv => enter [1]; rw [l1 X0 X1]
  intro x y
  conv => enter [1]; rw [l2 x y]

theorem Equation10_14_implies_Equation2 (G : Type*) [Magma G] (h10 : Equation10 G) (h14 : Equation14 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [h14 X0 X1]
    conv => enter [1]; rw [← h10 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

theorem Equation10_28_implies_Equation5 (G : Type*) [Magma G] (h10 : Equation10 G) (h28 : Equation28 G) : Equation5 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h10 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h10 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1]; rw [← h28 X0 X1]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h10 (sK1 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 (sK1 ◇ sK0) sK0]
    conv => enter [1]; rw [← l2 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation9_25_implies_Equation4 (G : Type*) [Magma G] (h9 : Equation9 G) (h25 : Equation25 G) : Equation4 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X1) ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h9 (X0 ◇ X1) X0]
    conv => enter [1, 2]; rw [← h25 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h25 X0 X1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h25 (sK0 ◇ sK1) sK0]
    conv => enter [1, 1]; rw [← h25 sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [← l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

theorem Equation9_28_implies_Equation2 (G : Type*) [Magma G] (h9 : Equation9 G) (h28 : Equation28 G) : Equation2 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ (X0 ◇ X1)) := by
    intro X0 X1
    conv => enter [1]; rw [h28 (X0 ◇ X1) X0]
    conv => enter [1, 1]; rw [← h9 X0 X1]
  have l1 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X1 ◇ X0) ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [h9 (X1 ◇ X0) X0]
    conv => enter [1, 2]; rw [← h28 X0 X1]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h28 X0 X1]
  have l3 : ∀ X0 X1 : G, (X0 ◇ X1) = X0 := by
    intro X0 X1
    conv => enter [1]; rw [l0 X0 X1]
    conv => enter [1]; rw [← h9 X0 X1]
  have l4 : ∀ X0 X1 : G, X0 = X1 := by
    intro X0 X1
    conv => enter [1]; rw [← l3 X0 X1]
    conv => enter [1]; rw [l2 X0 X1]
  intro x y
  conv => enter [1]; rw [l4 x y]

end Order2
