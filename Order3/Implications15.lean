import ExplorationLaws
import equational_theories.EquationalResult
import Mathlib.Tactic.TypeStar

set_option linter.unusedVariables false

namespace Order3

@[equational_result]
theorem Equation2_implies_Equation152 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation152 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((x ◇ x) ◇ (x ◇ y))]

@[equational_result]
theorem Equation2_implies_Equation166 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation166 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((y ◇ x) ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation221 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation221 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((y ◇ (x ◇ y)) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation310 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation310 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 x (y ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation367 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation367 G := by
  intro x y
  conv => enter [1, 1]; rw [h2 x (y ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation55 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation55 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (y ◇ (y ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation263 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation263 G := by
  intro x y
  conv => enter [1]; rw [h2 x (((x ◇ y) ◇ y) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation107 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation107 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ ((y ◇ y) ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation211 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation211 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((x ◇ (y ◇ y)) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation49 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation49 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ (y ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation260 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation260 G := by
  intro x y
  conv => enter [1]; rw [h2 x (((x ◇ y) ◇ x) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation75 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation75 G := by
  intro x y
  conv => enter [1]; rw [h2 x (y ◇ (y ◇ (y ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation264 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation264 G := by
  intro x y
  conv => enter [1]; rw [h2 x (((x ◇ y) ◇ y) ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation40 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation40 G := by
  intro x y
  conv => enter [1]; rw [h2 (x ◇ x) (y ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation309 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation309 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 x (y ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation361 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation361 G := by
  intro x y
  conv => enter [1, 1]; rw [h2 x (x ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation308 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation308 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 x (x ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation364 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation364 G := by
  intro x y
  conv => enter [1, 1]; rw [h2 x (y ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation101 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation101 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ ((x ◇ y) ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation208 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation208 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((x ◇ (y ◇ x)) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation323 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation323 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 y (x ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation378 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation378 G := by
  intro x y
  conv => enter [1, 1]; rw [h2 x (x ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation104 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation104 G := by
  intro x y
  conv => enter [1]; rw [h2 x (x ◇ ((y ◇ x) ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation205 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation205 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((x ◇ (x ◇ y)) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation159 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation159 G := by
  intro x y
  conv => enter [1]; rw [h2 x ((x ◇ y) ◇ (y ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation3 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation3 G := by
  intro x
  conv => enter [1]; rw [h2 x (x ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation326 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation326 G := by
  intro x y
  conv => enter [1, 2]; rw [h2 y (y ◇ y)]

@[equational_result]
theorem Equation2_implies_Equation375 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation375 G := by
  intro x y
  conv => enter [1, 1]; rw [h2 x (x ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation8 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation8 G := by
  intro x
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation23 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation23 G := by
  intro x
  conv => enter [1]; rw [h2 x ((x ◇ x) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation47 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h2 x (x ◇ (x ◇ (x ◇ x)))]

@[equational_result]
theorem Equation2_implies_Equation255 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation255 G := by
  intro x
  conv => enter [1]; rw [h2 x (((x ◇ x) ◇ x) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation151 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation151 G := by
  intro x
  conv => enter [1]; rw [h2 x ((x ◇ x) ◇ (x ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation99 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation99 G := by
  intro x
  conv => enter [1]; rw [h2 x (x ◇ ((x ◇ x) ◇ x))]

@[equational_result]
theorem Equation2_implies_Equation203 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation203 G := by
  intro x
  conv => enter [1]; rw [h2 x ((x ◇ (x ◇ x)) ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation307 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation307 G := by
  intro x
  conv => enter [1, 2]; rw [h2 x (x ◇ x)]

@[equational_result]
theorem Equation2_implies_Equation359 (G : Type*) [Magma G] (h2 : Equation2 G) : Equation359 G := by
  intro x
  conv => enter [1, 1]; rw [h2 x (x ◇ x)]

@[equational_result]
theorem Equation3_implies_Equation326 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation326 G := by
  intro x y
  conv => enter [1, 2]; rw [h3 y]

@[equational_result]
theorem Equation3_implies_Equation375 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation375 G := by
  intro x y
  conv => enter [1, 1]; rw [h3 x]

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
theorem Equation3_implies_Equation255 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation255 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, sK0 = (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

@[equational_result]
theorem Equation3_implies_Equation151 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation151 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1]; rw [h3 (sK0 ◇ sK0)]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation3_implies_Equation99 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation99 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

@[equational_result]
theorem Equation3_implies_Equation203 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation203 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 2]; rw [h3 sK0]
  have l1 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

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
theorem Equation3_implies_Equation359 (G : Type*) [Magma G] (h3 : Equation3 G) : Equation359 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h3 sK0]
    conv => enter [1, 1]; rw [h3 sK0]
  intro x
  conv => enter [1]; rw [← h3 x]
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation4_implies_Equation374 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation374 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h4 sK0 sK0]
    conv => enter [1, 1]; rw [h4 sK0 sK0]
  intro x y
  conv => enter [1]; rw [← h4 x y]
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
theorem Equation4_implies_Equation256 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation256 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h4 sK0 sK0]
    conv => enter [1, 1]; rw [h4 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x]
  conv => enter [1]; rw [h4 ((x ◇ x) ◇ x) y]

@[equational_result]
theorem Equation4_implies_Equation38 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation38 G := by
  intro x y
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x y]

@[equational_result]
theorem Equation4_implies_Equation106 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation106 G := by
  intro x y z
  conv => enter [1]; rw [h4 x ((y ◇ x) ◇ z)]

@[equational_result]
theorem Equation4_implies_Equation215 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation215 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK2)) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4 sK0 (sK1 ◇ sK2)]
    conv => enter [1]; rw [h4 (sK0 ◇ (sK1 ◇ sK2)) sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation4_implies_Equation111 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation111 G := by
  intro x y z
  conv => enter [1]; rw [h4 x ((y ◇ z) ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation162 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation162 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4 sK0 sK1]
    conv => enter [1]; rw [h4 (sK0 ◇ sK1) (sK2 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation4_implies_Equation363 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation363 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ sK1) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4 sK0 sK1]
    conv => enter [1]; rw [h4 (sK0 ◇ sK1) sK2]
  intro x y z
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation4_implies_Equation379 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation379 G := by
  intro x y z
  conv => enter [1]; rw [h4 (x ◇ y) z]

@[equational_result]
theorem Equation4_implies_Equation58 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation58 G := by
  intro x y z
  conv => enter [1]; rw [h4 x (y ◇ (z ◇ x))]

@[equational_result]
theorem Equation4_implies_Equation266 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation266 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ sK1) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h4 sK0 sK1]
    conv => enter [1]; rw [h4 (sK0 ◇ sK1) sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]
  conv => enter [1]; rw [h4 ((x ◇ y) ◇ z) x]

@[equational_result]
theorem Equation4_implies_Equation206 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation206 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4 (sK0 ◇ (sK0 ◇ sK1)) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

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
theorem Equation4_implies_Equation381 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation381 G := by
  have l0 : ∀ sK0 sK2 sK1 : G, sK0 = ((sK0 ◇ sK2) ◇ sK1) := by
    intro sK0 sK2 sK1
    conv => enter [1]; rw [h4 sK0 sK2]
    conv => enter [1]; rw [h4 (sK0 ◇ sK2) sK1]
  intro x y z
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [l0 x z y]

@[equational_result]
theorem Equation4_implies_Equation109 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation109 G := by
  intro x y z
  conv => enter [1]; rw [h4 x ((y ◇ y) ◇ z)]

@[equational_result]
theorem Equation4_implies_Equation258 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation258 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4 sK0 sK0]
    conv => enter [1]; rw [h4 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1, 1]; rw [h4 (x ◇ x) y]

@[equational_result]
theorem Equation4_implies_Equation311 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation311 G := by
  intro x y z
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (y ◇ z)]

@[equational_result]
theorem Equation4_implies_Equation261 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation261 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4 sK0 sK1]
    conv => enter [1]; rw [h4 (sK0 ◇ sK1) sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [h4 ((x ◇ y) ◇ x) y]

@[equational_result]
theorem Equation4_implies_Equation103 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation103 G := by
  intro x y z
  conv => enter [1]; rw [h4 x ((x ◇ y) ◇ z)]

@[equational_result]
theorem Equation4_implies_Equation26 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation26 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4 sK0 sK1]
    conv => enter [1, 1]; rw [h4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation4_implies_Equation52 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation52 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation4_implies_Equation257 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation257 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4 sK0 sK0]
    conv => enter [1]; rw [h4 (sK0 ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [h4 ((x ◇ x) ◇ y) x]

@[equational_result]
theorem Equation4_implies_Equation11 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation11 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation362 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation362 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4 sK0 sK1]
    conv => enter [1, 1]; rw [h4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [l0 x y]

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
theorem Equation4_implies_Equation212 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation212 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4 (sK0 ◇ (sK1 ◇ sK1)) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation4_implies_Equation53 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation53 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (x ◇ y))]

@[equational_result]
theorem Equation4_implies_Equation56 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation56 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ y))]

@[equational_result]
theorem Equation4_implies_Equation209 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation209 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4 (sK0 ◇ (sK1 ◇ sK0)) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation4_implies_Equation325 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation325 G := by
  intro x y
  conv => enter [1]; rw [← h4 x y]
  conv => enter [1]; rw [h4 x (y ◇ x)]

@[equational_result]
theorem Equation4_implies_Equation108 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation108 G := by
  intro x y
  conv => enter [1]; rw [h4 x ((y ◇ y) ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation377 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation377 G := by
  intro x y
  conv => enter [1]; rw [h4 (x ◇ y) x]

@[equational_result]
theorem Equation4_implies_Equation153 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation153 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4 sK0 sK0]
    conv => enter [1]; rw [h4 (sK0 ◇ sK0) (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation4_implies_Equation156 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation156 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4 sK0 sK1]
    conv => enter [1]; rw [h4 (sK0 ◇ sK1) (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation4_implies_Equation100 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation100 G := by
  intro x y
  conv => enter [1]; rw [h4 x ((x ◇ x) ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation50 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation50 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ y))]

@[equational_result]
theorem Equation4_implies_Equation48 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation48 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ (x ◇ y))]

@[equational_result]
theorem Equation4_implies_Equation102 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation102 G := by
  intro x y
  conv => enter [1]; rw [h4 x ((x ◇ y) ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation360 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation360 G := by
  intro x y
  conv => enter [1]; rw [h4 (x ◇ x) y]

@[equational_result]
theorem Equation4_implies_Equation105 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation105 G := by
  intro x y
  conv => enter [1]; rw [h4 x ((y ◇ x) ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation152 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation152 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4 sK0 sK0]
    conv => enter [1]; rw [h4 (sK0 ◇ sK0) (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation4_implies_Equation310 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation310 G := by
  intro x y
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (y ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation55 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation55 G := by
  intro x y
  conv => enter [1]; rw [h4 x (y ◇ (y ◇ x))]

@[equational_result]
theorem Equation4_implies_Equation263 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation263 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4 sK0 sK1]
    conv => enter [1, 1]; rw [h4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1]; rw [h4 ((x ◇ y) ◇ y) x]

@[equational_result]
theorem Equation4_implies_Equation107 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation107 G := by
  intro x y
  conv => enter [1]; rw [h4 x ((y ◇ y) ◇ x)]

@[equational_result]
theorem Equation4_implies_Equation211 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation211 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h4 (sK0 ◇ (sK1 ◇ sK1)) sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation4_implies_Equation49 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation49 G := by
  intro x y
  conv => enter [1]; rw [h4 x (x ◇ (y ◇ x))]

@[equational_result]
theorem Equation4_implies_Equation260 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation260 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4 sK0 sK1]
    conv => enter [1]; rw [h4 (sK0 ◇ sK1) sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1, 1]; rw [h4 (x ◇ y) x]

@[equational_result]
theorem Equation4_implies_Equation264 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation264 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4 sK0 sK1]
    conv => enter [1, 1]; rw [h4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]
  conv => enter [1, 1, 1]; rw [h4 x y]

@[equational_result]
theorem Equation4_implies_Equation309 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation309 G := by
  intro x y
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (y ◇ x)]

@[equational_result]
theorem Equation4_implies_Equation361 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation361 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4 sK0 sK1]
    conv => enter [1]; rw [h4 (sK0 ◇ sK1) sK0]
  intro x y
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation4_implies_Equation308 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation308 G := by
  intro x y
  conv => enter [1]; rw [← h4 x x]
  conv => enter [1]; rw [h4 x (x ◇ y)]

@[equational_result]
theorem Equation4_implies_Equation101 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation101 G := by
  intro x y
  conv => enter [1]; rw [h4 x ((x ◇ y) ◇ x)]

@[equational_result]
theorem Equation4_implies_Equation208 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation208 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h4 (sK0 ◇ (sK1 ◇ sK0)) sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation4_implies_Equation323 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation323 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h4 sK0 sK1]
    conv => enter [1]; rw [h4 sK0 (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation4_implies_Equation378 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation378 G := by
  intro x y
  conv => enter [1, 1]; rw [h4 x y]

@[equational_result]
theorem Equation4_implies_Equation104 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation104 G := by
  intro x y
  conv => enter [1]; rw [h4 x ((y ◇ x) ◇ x)]

@[equational_result]
theorem Equation4_implies_Equation205 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation205 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h4 (sK0 ◇ (sK0 ◇ sK1)) sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation4_implies_Equation159 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation159 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h4 sK0 sK1]
    conv => enter [1]; rw [h4 (sK0 ◇ sK1) (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation4_implies_Equation3 (G : Type*) [Magma G] (h4 : Equation4 G) : Equation3 G := by
  intro x
  conv => enter [1]; rw [h4 x x]

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
theorem Equation5_implies_Equation39 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation39 G := by
  intro x y
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [h5 x y]

@[equational_result]
theorem Equation5_implies_Equation224 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation224 G := by
  intro x y z
  conv => enter [1]; rw [h5 x (y ◇ (x ◇ z))]

@[equational_result]
theorem Equation5_implies_Equation138 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation138 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = (sK1 ◇ ((sK2 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 sK0 (sK2 ◇ sK1)]
    conv => enter [1]; rw [h5 ((sK2 ◇ sK1) ◇ sK0) sK1]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation5_implies_Equation162 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation162 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [h5 sK0 sK2]
    conv => enter [1]; rw [h5 (sK2 ◇ sK0) (sK0 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation5_implies_Equation242 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation242 G := by
  intro x y z
  conv => enter [1]; rw [h5 x (y ◇ (z ◇ y))]

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
theorem Equation5_implies_Equation343 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation343 G := by
  intro x y z
  conv => enter [1]; rw [h5 (x ◇ y) z]

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
theorem Equation5_implies_Equation266 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation266 G := by
  intro x y z
  conv => enter [1]; rw [h5 x ((x ◇ y) ◇ z)]

@[equational_result]
theorem Equation5_implies_Equation124 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation124 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h5 ((sK1 ◇ sK0) ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

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
theorem Equation5_implies_Equation381 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation381 G := by
  intro x y z
  conv => enter [1]; rw [← h5 y x]
  conv => enter [1]; rw [h5 y (x ◇ z)]

@[equational_result]
theorem Equation5_implies_Equation395 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation395 G := by
  intro x y z
  conv => enter [1]; rw [← h5 y x]
  conv => enter [1]; rw [h5 y (z ◇ x)]

@[equational_result]
theorem Equation5_implies_Equation246 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation246 G := by
  intro x y z
  conv => enter [1]; rw [h5 x (y ◇ (z ◇ z))]

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
theorem Equation5_implies_Equation370 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation370 G := by
  intro x y z
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [h5 x (y ◇ z)]

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
theorem Equation5_implies_Equation238 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation238 G := by
  intro x y z
  conv => enter [1]; rw [h5 x (y ◇ (z ◇ x))]

@[equational_result]
theorem Equation5_implies_Equation16 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation16 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1, 2]; rw [h5 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

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
theorem Equation5_implies_Equation257 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation257 G := by
  intro x y
  conv => enter [1]; rw [h5 x ((x ◇ x) ◇ y)]

@[equational_result]
theorem Equation5_implies_Equation31 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation31 G := by
  intro x y
  conv => enter [1]; rw [h5 x (y ◇ y)]

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
theorem Equation5_implies_Equation127 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation127 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK1 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h5 ((sK1 ◇ sK1) ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation273 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation273 G := by
  intro x y
  conv => enter [1]; rw [h5 x ((y ◇ x) ◇ y)]

@[equational_result]
theorem Equation5_implies_Equation283 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation283 G := by
  intro x y
  conv => enter [1]; rw [h5 x ((y ◇ y) ◇ y)]

@[equational_result]
theorem Equation5_implies_Equation117 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation117 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h5 ((sK0 ◇ sK1) ◇ sK0) sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation385 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation385 G := by
  intro x y
  conv => enter [1]; rw [← h5 y x]
  conv => enter [1]; rw [h5 y (y ◇ x)]

@[equational_result]
theorem Equation5_implies_Equation231 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation231 G := by
  intro x y
  conv => enter [1]; rw [h5 x (y ◇ (y ◇ y))]

@[equational_result]
theorem Equation5_implies_Equation333 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation333 G := by
  intro x y
  conv => enter [1]; rw [h5 (x ◇ y) y]

@[equational_result]
theorem Equation5_implies_Equation153 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation153 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation156 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation156 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation218 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation218 G := by
  intro x y
  conv => enter [1]; rw [h5 x (y ◇ (x ◇ x))]

@[equational_result]
theorem Equation5_implies_Equation280 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation280 G := by
  intro x y
  conv => enter [1]; rw [h5 x ((y ◇ y) ◇ x)]

@[equational_result]
theorem Equation5_implies_Equation228 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation228 G := by
  intro x y
  conv => enter [1]; rw [h5 x (y ◇ (y ◇ x))]

@[equational_result]
theorem Equation5_implies_Equation270 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation270 G := by
  intro x y
  conv => enter [1]; rw [h5 x ((y ◇ x) ◇ x)]

@[equational_result]
theorem Equation5_implies_Equation312 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation312 G := by
  intro x y
  conv => enter [1]; rw [h5 (x ◇ x) y]

@[equational_result]
theorem Equation5_implies_Equation166 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation166 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK0]
    conv => enter [1]; rw [h5 (sK0 ◇ sK0) (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation221 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation221 G := by
  intro x y
  conv => enter [1]; rw [h5 x (y ◇ (x ◇ y))]

@[equational_result]
theorem Equation5_implies_Equation367 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation367 G := by
  intro x y
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [h5 x (y ◇ y)]

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
theorem Equation5_implies_Equation263 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation263 G := by
  intro x y
  conv => enter [1]; rw [h5 x ((x ◇ y) ◇ y)]

@[equational_result]
theorem Equation5_implies_Equation107 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation107 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h5 ((sK1 ◇ sK1) ◇ sK0) sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation211 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation211 G := by
  intro x y
  conv => enter [1]; rw [h5 x (x ◇ (y ◇ y))]

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
theorem Equation5_implies_Equation260 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation260 G := by
  intro x y
  conv => enter [1]; rw [h5 x ((x ◇ y) ◇ x)]

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
theorem Equation5_implies_Equation309 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation309 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) sK0]
  intro x y
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation361 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation361 G := by
  intro x y
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [h5 x (x ◇ y)]

@[equational_result]
theorem Equation5_implies_Equation364 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation364 G := by
  intro x y
  conv => enter [1]; rw [← h5 x x]
  conv => enter [1]; rw [h5 x (y ◇ x)]

@[equational_result]
theorem Equation5_implies_Equation101 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation101 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 (sK0 ◇ sK1)]
    conv => enter [1]; rw [h5 ((sK0 ◇ sK1) ◇ sK0) sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation208 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation208 G := by
  intro x y
  conv => enter [1]; rw [h5 x (x ◇ (y ◇ x))]

@[equational_result]
theorem Equation5_implies_Equation323 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation323 G := by
  intro x y
  conv => enter [1, 2]; rw [h5 y x]

@[equational_result]
theorem Equation5_implies_Equation378 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation378 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h5 sK1 sK0]
    conv => enter [1]; rw [h5 sK1 (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation104 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation104 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 (sK1 ◇ sK0)]
    conv => enter [1]; rw [h5 ((sK1 ◇ sK0) ◇ sK0) sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation205 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation205 G := by
  intro x y
  conv => enter [1]; rw [h5 x (x ◇ (x ◇ y))]

@[equational_result]
theorem Equation5_implies_Equation159 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation159 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h5 sK0 sK1]
    conv => enter [1]; rw [h5 (sK1 ◇ sK0) (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation5_implies_Equation3 (G : Type*) [Magma G] (h5 : Equation5 G) : Equation3 G := by
  intro x
  conv => enter [1]; rw [h5 x x]

@[equational_result]
theorem Equation9_implies_Equation100 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation100 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h9 X0 X0]
    conv => enter [1]; rw [← h9 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0]
    conv => enter [1]; rw [h9 (sK0 ◇ sK0) sK1]
    conv => enter [1, 1]; rw [l0 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation9_implies_Equation50 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation50 G := by
  intro x y
  conv => enter [1]; rw [h9 x (y ◇ y)]

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
theorem Equation9_implies_Equation152 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation152 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h9 X0 X0]
    conv => enter [1]; rw [← h9 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h9 sK0 sK1]
    conv => enter [1, 1]; rw [← l0 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation9_implies_Equation49 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation49 G := by
  intro x y
  conv => enter [1]; rw [h9 x (y ◇ x)]

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
theorem Equation9_implies_Equation205 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation205 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h9 X0 X0]
    conv => enter [1]; rw [← h9 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0]
    conv => enter [1, 1]; rw [h9 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation9_implies_Equation3 (G : Type*) [Magma G] (h9 : Equation9 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h9 X0 X0]
    conv => enter [1]; rw [← h9 X0 (X0 ◇ X0)]
  intro x
  conv => enter [1]; rw [← l0 x]

@[equational_result]
theorem Equation28_implies_Equation218 (G : Type*) [Magma G] (h28 : Equation28 G) : Equation218 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h28 X0 X0]
    conv => enter [1]; rw [← h28 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0]
    conv => enter [1]; rw [h28 (sK0 ◇ sK0) sK1]
    conv => enter [1, 2]; rw [l0 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation28_implies_Equation280 (G : Type*) [Magma G] (h28 : Equation28 G) : Equation280 G := by
  intro x y
  conv => enter [1]; rw [h28 x (y ◇ y)]

@[equational_result]
theorem Equation28_implies_Equation270 (G : Type*) [Magma G] (h28 : Equation28 G) : Equation270 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h28 X0 X0]
    conv => enter [1]; rw [← h28 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = (((sK1 ◇ sK0) ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0]
    conv => enter [1, 1]; rw [h28 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation28_implies_Equation166 (G : Type*) [Magma G] (h28 : Equation28 G) : Equation166 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h28 X0 X0]
    conv => enter [1]; rw [← h28 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h28 sK0 sK1]
    conv => enter [1, 2]; rw [← l0 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation28_implies_Equation260 (G : Type*) [Magma G] (h28 : Equation28 G) : Equation260 G := by
  intro x y
  conv => enter [1]; rw [h28 x (x ◇ y)]

@[equational_result]
theorem Equation28_implies_Equation364 (G : Type*) [Magma G] (h28 : Equation28 G) : Equation364 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h28 X0 X0]
    conv => enter [1]; rw [← h28 X0 (X0 ◇ X0)]
  intro x y
  conv => enter [1]; rw [l0 x]
  conv => enter [1]; rw [h28 x y]

@[equational_result]
theorem Equation28_implies_Equation104 (G : Type*) [Magma G] (h28 : Equation28 G) : Equation104 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h28 X0 X0]
    conv => enter [1]; rw [← h28 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0]
    conv => enter [1, 2]; rw [h28 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation28_implies_Equation3 (G : Type*) [Magma G] (h28 : Equation28 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h28 X0 X0]
    conv => enter [1]; rw [← h28 X0 (X0 ◇ X0)]
  intro x
  conv => enter [1]; rw [← l0 x]

@[equational_result]
theorem Equation10_implies_Equation107 (G : Type*) [Magma G] (h10 : Equation10 G) : Equation107 G := by
  intro x y
  conv => enter [1]; rw [h10 x (y ◇ y)]

@[equational_result]
theorem Equation10_implies_Equation101 (G : Type*) [Magma G] (h10 : Equation10 G) : Equation101 G := by
  intro x y
  conv => enter [1]; rw [h10 x (x ◇ y)]

@[equational_result]
theorem Equation10_implies_Equation378 (G : Type*) [Magma G] (h10 : Equation10 G) : Equation378 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h10 (sK0 ◇ sK1) sK1]
    conv => enter [1, 2]; rw [← h10 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation10_implies_Equation104 (G : Type*) [Magma G] (h10 : Equation10 G) : Equation104 G := by
  intro x y
  conv => enter [1]; rw [h10 x (y ◇ x)]

@[equational_result]
theorem Equation10_implies_Equation8 (G : Type*) [Magma G] (h10 : Equation10 G) : Equation8 G := by
  intro x
  conv => enter [1]; rw [h10 x x]

@[equational_result]
theorem Equation10_implies_Equation99 (G : Type*) [Magma G] (h10 : Equation10 G) : Equation99 G := by
  intro x
  conv => enter [1]; rw [h10 x (x ◇ x)]

@[equational_result]
theorem Equation10_implies_Equation359 (G : Type*) [Magma G] (h10 : Equation10 G) : Equation359 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h10 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h10 sK0 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation25_implies_Equation211 (G : Type*) [Magma G] (h25 : Equation25 G) : Equation211 G := by
  intro x y
  conv => enter [1]; rw [h25 x (y ◇ y)]

@[equational_result]
theorem Equation25_implies_Equation208 (G : Type*) [Magma G] (h25 : Equation25 G) : Equation208 G := by
  intro x y
  conv => enter [1]; rw [h25 x (y ◇ x)]

@[equational_result]
theorem Equation25_implies_Equation323 (G : Type*) [Magma G] (h25 : Equation25 G) : Equation323 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h25 (sK0 ◇ sK1) sK0]
    conv => enter [1, 1]; rw [← h25 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation25_implies_Equation205 (G : Type*) [Magma G] (h25 : Equation25 G) : Equation205 G := by
  intro x y
  conv => enter [1]; rw [h25 x (x ◇ y)]

@[equational_result]
theorem Equation25_implies_Equation23 (G : Type*) [Magma G] (h25 : Equation25 G) : Equation23 G := by
  intro x
  conv => enter [1]; rw [h25 x x]

@[equational_result]
theorem Equation25_implies_Equation203 (G : Type*) [Magma G] (h25 : Equation25 G) : Equation203 G := by
  intro x
  conv => enter [1]; rw [h25 x (x ◇ x)]

@[equational_result]
theorem Equation25_implies_Equation307 (G : Type*) [Magma G] (h25 : Equation25 G) : Equation307 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h25 (sK0 ◇ sK0) sK0]
    conv => enter [1, 1]; rw [← h25 sK0 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

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
theorem Equation13_implies_Equation138 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation138 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 X0 sK2 sK1 : G, sK0 = (X0 ◇ ((sK2 ◇ sK1) ◇ sK0)) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [h13 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 (sK2 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [l1 x y z y]

@[equational_result]
theorem Equation13_implies_Equation162 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation162 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 X0 sK2 : G, sK0 = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h13 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK2]
  intro x y z
  conv => enter [1]; rw [l1 x (x ◇ y) z]

@[equational_result]
theorem Equation13_implies_Equation124 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation124 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h13 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  have l2 : ∀ sK1 sK0 : G, (sK1 ◇ sK0) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK0)]
  have l3 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK1]
    conv => enter [1, 2]; rw [l2 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation13_implies_Equation381 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation381 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ sK2) ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← l0 sK1 (sK0 ◇ sK2)]
    conv => enter [1]; rw [l0 sK1 X0]
  intro x y z
  conv => enter [1]; rw [← l1 x z y x]

@[equational_result]
theorem Equation13_implies_Equation395 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation395 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ sK1) = (X0 ◇ sK1) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← l0 sK1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [l0 sK1 X0]
  intro x y z
  conv => enter [1]; rw [← l1 z x y x]

@[equational_result]
theorem Equation13_implies_Equation370 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation370 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h13 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h13 sK0 (sK0 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ z)]

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
theorem Equation13_implies_Equation127 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation127 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ ((sK1 ◇ sK1) ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h13 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l1 x y y]

@[equational_result]
theorem Equation13_implies_Equation117 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation117 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ ((sK0 ◇ sK1) ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h13 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l1 x y y]

@[equational_result]
theorem Equation13_implies_Equation385 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation385 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK1 sK0]
    conv => enter [1]; rw [l0 sK1 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation13_implies_Equation153 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation153 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h13 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h13 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h13 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation13_implies_Equation156 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation156 G := by
  intro x y
  conv => enter [1]; rw [h13 x (x ◇ y)]

@[equational_result]
theorem Equation13_implies_Equation166 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation166 G := by
  intro x y
  conv => enter [1]; rw [h13 x (y ◇ x)]

@[equational_result]
theorem Equation13_implies_Equation367 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation367 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h13 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h13 sK0 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l0 x (y ◇ y)]

@[equational_result]
theorem Equation13_implies_Equation361 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation361 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h13 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h13 sK0 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ y)]

@[equational_result]
theorem Equation13_implies_Equation364 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation364 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h13 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h13 sK0 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l0 x (y ◇ x)]

@[equational_result]
theorem Equation13_implies_Equation159 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation159 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h13 sK0 X0]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x (x ◇ y) y]

@[equational_result]
theorem Equation13_implies_Equation375 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation375 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h13 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h13 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l0 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [l0 sK1 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y x]

@[equational_result]
theorem Equation13_implies_Equation151 (G : Type*) [Magma G] (h13 : Equation13 G) : Equation151 G := by
  intro x
  conv => enter [1]; rw [h13 x (x ◇ x)]

@[equational_result]
theorem Equation24_implies_Equation38 (G : Type*) [Magma G] (h24 : Equation24 G) : Equation38 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h24 (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h24 sK0 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation24_implies_Equation215 (G : Type*) [Magma G] (h24 : Equation24 G) : Equation215 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h24 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h24 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 sK2 X0 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK2)) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [h24 sK0 X0]
    conv => enter [1, 1]; rw [l0 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l1 x y z y]

@[equational_result]
theorem Equation24_implies_Equation162 (G : Type*) [Magma G] (h24 : Equation24 G) : Equation162 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h24 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h24 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h24 sK0 X0]
    conv => enter [1, 1]; rw [l0 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [← l0 (sK0 ◇ sK1) (sK2 ◇ sK0)]
    conv => enter [1]; rw [l0 (sK0 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 sK2 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1]; rw [← l2 sK0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation24_implies_Equation206 (G : Type*) [Magma G] (h24 : Equation24 G) : Equation206 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h24 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h24 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h24 sK0 X0]
    conv => enter [1, 1]; rw [l0 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK1)]
  have l3 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK1)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK1]
    conv => enter [1, 1]; rw [l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation24_implies_Equation327 (G : Type*) [Magma G] (h24 : Equation24 G) : Equation327 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h24 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h24 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation24_implies_Equation329 (G : Type*) [Magma G] (h24 : Equation24 G) : Equation329 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h24 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h24 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 (sK2 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [l1 x y z]

@[equational_result]
theorem Equation24_implies_Equation311 (G : Type*) [Magma G] (h24 : Equation24 G) : Equation311 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h24 (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h24 sK0 (sK0 ◇ sK0)]
  intro x y z
  conv => enter [1]; rw [l0 x (y ◇ z)]

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
theorem Equation24_implies_Equation212 (G : Type*) [Magma G] (h24 : Equation24 G) : Equation212 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h24 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h24 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK1)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h24 sK0 X0]
    conv => enter [1, 1]; rw [l0 sK0 (sK1 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l1 x y y]

@[equational_result]
theorem Equation24_implies_Equation209 (G : Type*) [Magma G] (h24 : Equation24 G) : Equation209 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h24 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h24 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ (sK1 ◇ sK0)) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h24 sK0 X0]
    conv => enter [1, 1]; rw [l0 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l1 x y y]

@[equational_result]
theorem Equation24_implies_Equation325 (G : Type*) [Magma G] (h24 : Equation24 G) : Equation325 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h24 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h24 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0 sK1]
    conv => enter [1]; rw [l0 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation24_implies_Equation153 (G : Type*) [Magma G] (h24 : Equation24 G) : Equation153 G := by
  intro x y
  conv => enter [1]; rw [h24 x (y ◇ x)]

@[equational_result]
theorem Equation24_implies_Equation156 (G : Type*) [Magma G] (h24 : Equation24 G) : Equation156 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h24 (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h24 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h24 sK0 X0]
    conv => enter [1, 1]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l1 x y (x ◇ x)]

@[equational_result]
theorem Equation24_implies_Equation152 (G : Type*) [Magma G] (h24 : Equation24 G) : Equation152 G := by
  intro x y
  conv => enter [1]; rw [h24 x (x ◇ y)]

@[equational_result]
theorem Equation24_implies_Equation310 (G : Type*) [Magma G] (h24 : Equation24 G) : Equation310 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h24 (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h24 sK0 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l0 x (y ◇ y)]

@[equational_result]
theorem Equation24_implies_Equation309 (G : Type*) [Magma G] (h24 : Equation24 G) : Equation309 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h24 (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h24 sK0 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l0 x (y ◇ x)]

@[equational_result]
theorem Equation24_implies_Equation308 (G : Type*) [Magma G] (h24 : Equation24 G) : Equation308 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h24 (sK0 ◇ sK0) X0]
    conv => enter [1, 1]; rw [← h24 sK0 (sK0 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l0 x (x ◇ y)]

@[equational_result]
theorem Equation24_implies_Equation159 (G : Type*) [Magma G] (h24 : Equation24 G) : Equation159 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h24 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h24 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 X0 : G, sK0 = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h24 sK0 X0]
    conv => enter [1, 1]; rw [l0 sK0 sK1]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l0 (sK0 ◇ sK1) (sK1 ◇ sK0)]
    conv => enter [1]; rw [l0 (sK0 ◇ sK1) X0]
  have l3 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1 sK0]
    conv => enter [1]; rw [← l2 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation24_implies_Equation326 (G : Type*) [Magma G] (h24 : Equation24 G) : Equation326 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X0 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h24 (X0 ◇ X0) X1]
    conv => enter [1, 1]; rw [← h24 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← l0 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [l0 sK0 X0]
  intro x y
  conv => enter [1]; rw [← l1 x y y]

@[equational_result]
theorem Equation24_implies_Equation151 (G : Type*) [Magma G] (h24 : Equation24 G) : Equation151 G := by
  intro x
  conv => enter [1]; rw [h24 x (x ◇ x)]

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
theorem Equation38_implies_Equation327 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation327 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK1 ◇ sK2)]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation38_implies_Equation329 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation329 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK2 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation38_implies_Equation311 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation311 G := by
  intro x y z
  conv => enter [1]; rw [h38 x (y ◇ z)]

@[equational_result]
theorem Equation38_implies_Equation325 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation325 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation38_implies_Equation310 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation310 G := by
  intro x y
  conv => enter [1]; rw [h38 x (y ◇ y)]

@[equational_result]
theorem Equation38_implies_Equation309 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation309 G := by
  intro x y
  conv => enter [1]; rw [h38 x (y ◇ x)]

@[equational_result]
theorem Equation38_implies_Equation308 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation308 G := by
  intro x y
  conv => enter [1]; rw [h38 x (x ◇ y)]

@[equational_result]
theorem Equation38_implies_Equation323 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation323 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h38 sK0 sK1]
    conv => enter [1]; rw [h38 sK0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y (x ◇ y)]

@[equational_result]
theorem Equation38_implies_Equation326 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation326 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ (sK1 ◇ sK1)) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h38 sK0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [h38 sK0 X0]
  intro x y
  conv => enter [1]; rw [← l0 x y y]

@[equational_result]
theorem Equation38_implies_Equation307 (G : Type*) [Magma G] (h38 : Equation38 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h38 x (x ◇ x)]

@[equational_result]
theorem Equation39_implies_Equation381 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation381 G := by
  have l0 : ∀ sK0 sK2 sK1 X0 : G, ((sK0 ◇ sK2) ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK2 sK1 X0
    conv => enter [1]; rw [← h39 sK1 (sK0 ◇ sK2)]
    conv => enter [1]; rw [h39 sK1 X0]
  intro x y z
  conv => enter [1]; rw [← l0 x z y x]

@[equational_result]
theorem Equation39_implies_Equation395 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation395 G := by
  have l0 : ∀ sK2 sK0 sK1 X0 : G, ((sK2 ◇ sK0) ◇ sK1) = (X0 ◇ sK1) := by
    intro sK2 sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 (sK2 ◇ sK0)]
    conv => enter [1]; rw [h39 sK1 X0]
  intro x y z
  conv => enter [1]; rw [← l0 z x y x]

@[equational_result]
theorem Equation39_implies_Equation370 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation370 G := by
  intro x y z
  conv => enter [1]; rw [h39 x (y ◇ z)]

@[equational_result]
theorem Equation39_implies_Equation385 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation385 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation39_implies_Equation367 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation367 G := by
  intro x y
  conv => enter [1]; rw [h39 x (y ◇ y)]

@[equational_result]
theorem Equation39_implies_Equation361 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation361 G := by
  intro x y
  conv => enter [1]; rw [h39 x (x ◇ y)]

@[equational_result]
theorem Equation39_implies_Equation364 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation364 G := by
  intro x y
  conv => enter [1]; rw [h39 x (y ◇ x)]

@[equational_result]
theorem Equation39_implies_Equation378 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation378 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 sK0]
    conv => enter [1]; rw [h39 sK1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y (x ◇ y)]

@[equational_result]
theorem Equation39_implies_Equation375 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation375 G := by
  have l0 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK0) ◇ sK1) = (X0 ◇ sK1) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [← h39 sK1 (sK0 ◇ sK0)]
    conv => enter [1]; rw [h39 sK1 X0]
  intro x y
  conv => enter [1]; rw [← l0 x y x]

@[equational_result]
theorem Equation39_implies_Equation359 (G : Type*) [Magma G] (h39 : Equation39 G) : Equation359 G := by
  intro x
  conv => enter [1]; rw [h39 x (x ◇ x)]

@[equational_result]
theorem Equation41_implies_Equation336 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation336 G := by
  intro x y
  conv => enter [1]; rw [← h41 y x y]
  conv => enter [1]; rw [h41 y y (y ◇ y)]

@[equational_result]
theorem Equation41_implies_Equation374 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation374 G := by
  intro x y
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [h41 x (x ◇ x) x]

@[equational_result]
theorem Equation41_implies_Equation332 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation332 G := by
  intro x y
  conv => enter [1]; rw [← h41 x x y]
  conv => enter [1]; rw [h41 x y (x ◇ x)]

@[equational_result]
theorem Equation41_implies_Equation387 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation387 G := by
  have l0 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK1 ◇ sK1) ◇ sK0) := by
    intro sK1 sK0
    conv => enter [1]; rw [h41 sK1 (sK1 ◇ sK1) sK0]
  intro x y
  conv => enter [1]; rw [← h41 y x y]
  conv => enter [1]; rw [l0 y x]

@[equational_result]
theorem Equation41_implies_Equation38 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation38 G := by
  intro x y
  conv => enter [1]; rw [h41 x x y]

@[equational_result]
theorem Equation41_implies_Equation39 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation39 G := by
  intro x y
  conv => enter [1]; rw [h41 x y x]

@[equational_result]
theorem Equation41_implies_Equation314 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation314 G := by
  intro x y z
  conv => enter [1]; rw [h41 x y (x ◇ z)]

@[equational_result]
theorem Equation41_implies_Equation366 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation366 G := by
  intro x y z
  conv => enter [1]; rw [h41 x (y ◇ x) z]

@[equational_result]
theorem Equation41_implies_Equation335 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation335 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK1 (sK0 ◇ sK1)]
    conv => enter [1, 2]; rw [l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation41_implies_Equation384 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation384 G := by
  have l0 : ∀ X1 X2 sK0 sK1 : G, (X1 ◇ X2) = (sK0 ◇ sK1) := by
    intro X1 X2 sK0 sK1
    conv => enter [1]; rw [← h41 X1 X1 X2]
    conv => enter [1]; rw [h41 X1 sK0 sK1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 (sK0 ◇ sK1) sK0]
    conv => enter [1, 1]; rw [l1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation41_implies_Equation43 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation43 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation41_implies_Equation318 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation318 G := by
  intro x y z
  conv => enter [1]; rw [h41 x y (z ◇ x)]

@[equational_result]
theorem Equation41_implies_Equation363 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation363 G := by
  intro x y z
  conv => enter [1]; rw [h41 x (x ◇ y) z]

@[equational_result]
theorem Equation41_implies_Equation343 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation343 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK2 (sK0 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation41_implies_Equation379 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation379 G := by
  have l0 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 (sK0 ◇ sK1) sK2]
  intro x y z
  conv => enter [1]; rw [l0 x y z]

@[equational_result]
theorem Equation41_implies_Equation317 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation317 G := by
  intro x y z
  conv => enter [1]; rw [h41 x y (y ◇ z)]

@[equational_result]
theorem Equation41_implies_Equation372 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation372 G := by
  intro x y z
  conv => enter [1]; rw [h41 x (y ◇ z) z]

@[equational_result]
theorem Equation41_implies_Equation319 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation319 G := by
  have l0 : ∀ sK2 sK1 : G, (sK2 ◇ sK1) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK2 sK1
    conv => enter [1]; rw [← h41 sK2 sK2 sK1]
    conv => enter [1]; rw [h41 sK2 sK1 (sK2 ◇ sK1)]
  intro x y z
  conv => enter [1]; rw [h41 x z y]
  conv => enter [1]; rw [l0 z y]

@[equational_result]
theorem Equation41_implies_Equation371 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation371 G := by
  intro x y z
  conv => enter [1]; rw [h41 x (y ◇ z) y]

@[equational_result]
theorem Equation41_implies_Equation313 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation313 G := by
  intro x y
  conv => enter [1]; rw [h41 x y (x ◇ y)]

@[equational_result]
theorem Equation41_implies_Equation365 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation365 G := by
  intro x y
  conv => enter [1]; rw [h41 x (y ◇ x) y]

@[equational_result]
theorem Equation41_implies_Equation315 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation315 G := by
  intro x y
  conv => enter [1]; rw [h41 x y (y ◇ x)]

@[equational_result]
theorem Equation41_implies_Equation362 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation362 G := by
  intro x y
  conv => enter [1]; rw [h41 x (x ◇ y) y]

@[equational_result]
theorem Equation41_implies_Equation316 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation316 G := by
  intro x y
  conv => enter [1]; rw [h41 x y (y ◇ y)]

@[equational_result]
theorem Equation41_implies_Equation368 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation368 G := by
  intro x y
  conv => enter [1]; rw [h41 x (y ◇ y) y]

@[equational_result]
theorem Equation41_implies_Equation333 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation333 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 sK1 (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation41_implies_Equation377 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation377 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [← h41 sK0 sK0 sK1]
    conv => enter [1]; rw [h41 sK0 (sK0 ◇ sK1) sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation41_implies_Equation312 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation312 G := by
  intro x y
  conv => enter [1]; rw [h41 x y (x ◇ x)]

@[equational_result]
theorem Equation41_implies_Equation360 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation360 G := by
  intro x y
  conv => enter [1]; rw [h41 x (x ◇ x) y]

@[equational_result]
theorem Equation41_implies_Equation40 (G : Type*) [Magma G] (h41 : Equation41 G) : Equation40 G := by
  intro x y
  conv => enter [1]; rw [h41 x y y]

@[equational_result]
theorem Equation48_implies_Equation3 (G : Type*) [Magma G] (h48 : Equation48 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h48 X0 X0]
    conv => enter [1]; rw [← h48 X0 (X0 ◇ X0)]
  intro x
  conv => enter [1]; rw [← l0 x]

@[equational_result]
theorem Equation270_implies_Equation3 (G : Type*) [Magma G] (h270 : Equation270 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h270 X0 X0]
    conv => enter [1]; rw [← h270 X0 (X0 ◇ X0)]
  intro x
  conv => enter [1]; rw [← l0 x]

@[equational_result]
theorem Equation49_implies_Equation47 (G : Type*) [Magma G] (h49 : Equation49 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h49 x x]

@[equational_result]
theorem Equation260_implies_Equation255 (G : Type*) [Magma G] (h260 : Equation260 G) : Equation255 G := by
  intro x
  conv => enter [1]; rw [h260 x x]

@[equational_result]
theorem Equation50_implies_Equation47 (G : Type*) [Magma G] (h50 : Equation50 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h50 x x]

@[equational_result]
theorem Equation280_implies_Equation255 (G : Type*) [Magma G] (h280 : Equation280 G) : Equation255 G := by
  intro x
  conv => enter [1]; rw [h280 x x]

@[equational_result]
theorem Equation52_implies_Equation47 (G : Type*) [Magma G] (h52 : Equation52 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h52 x x]

@[equational_result]
theorem Equation52_implies_Equation359 (G : Type*) [Magma G] (h52 : Equation52 G) : Equation359 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h52 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h52 sK0 (sK0 ◇ sK0)]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation257_implies_Equation255 (G : Type*) [Magma G] (h257 : Equation257 G) : Equation255 G := by
  intro x
  conv => enter [1]; rw [h257 x x]

@[equational_result]
theorem Equation257_implies_Equation307 (G : Type*) [Magma G] (h257 : Equation257 G) : Equation307 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h257 (sK0 ◇ sK0) sK0]
    conv => enter [1, 1]; rw [← h257 sK0 (sK0 ◇ sK0)]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation53_implies_Equation47 (G : Type*) [Magma G] (h53 : Equation53 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h53 x x]

@[equational_result]
theorem Equation273_implies_Equation255 (G : Type*) [Magma G] (h273 : Equation273 G) : Equation255 G := by
  intro x
  conv => enter [1]; rw [h273 x x]

@[equational_result]
theorem Equation55_implies_Equation47 (G : Type*) [Magma G] (h55 : Equation55 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h55 x x]

@[equational_result]
theorem Equation55_implies_Equation359 (G : Type*) [Magma G] (h55 : Equation55 G) : Equation359 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h55 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h55 sK0 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation263_implies_Equation255 (G : Type*) [Magma G] (h263 : Equation263 G) : Equation255 G := by
  intro x
  conv => enter [1]; rw [h263 x x]

@[equational_result]
theorem Equation263_implies_Equation307 (G : Type*) [Magma G] (h263 : Equation263 G) : Equation307 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h263 (sK0 ◇ sK0) sK0]
    conv => enter [1, 1]; rw [← h263 sK0 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation56_implies_Equation47 (G : Type*) [Magma G] (h56 : Equation56 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h56 x x]

@[equational_result]
theorem Equation283_implies_Equation255 (G : Type*) [Magma G] (h283 : Equation283 G) : Equation255 G := by
  intro x
  conv => enter [1]; rw [h283 x x]

@[equational_result]
theorem Equation58_implies_Equation52 (G : Type*) [Magma G] (h58 : Equation58 G) : Equation52 G := by
  intro x y
  conv => enter [1]; rw [h58 x y x]

@[equational_result]
theorem Equation58_implies_Equation55 (G : Type*) [Magma G] (h58 : Equation58 G) : Equation55 G := by
  intro x y
  conv => enter [1]; rw [h58 x y y]

@[equational_result]
theorem Equation58_implies_Equation49 (G : Type*) [Magma G] (h58 : Equation58 G) : Equation49 G := by
  intro x y
  conv => enter [1]; rw [h58 x x y]

@[equational_result]
theorem Equation58_implies_Equation378 (G : Type*) [Magma G] (h58 : Equation58 G) : Equation378 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h58 (sK0 ◇ sK1) sK1 sK0]
    conv => enter [1, 2]; rw [← h58 sK1 sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation266_implies_Equation257 (G : Type*) [Magma G] (h266 : Equation266 G) : Equation257 G := by
  intro x y
  conv => enter [1]; rw [h266 x x y]

@[equational_result]
theorem Equation266_implies_Equation263 (G : Type*) [Magma G] (h266 : Equation266 G) : Equation263 G := by
  intro x y
  conv => enter [1]; rw [h266 x y y]

@[equational_result]
theorem Equation266_implies_Equation260 (G : Type*) [Magma G] (h266 : Equation266 G) : Equation260 G := by
  intro x y
  conv => enter [1]; rw [h266 x y x]

@[equational_result]
theorem Equation266_implies_Equation323 (G : Type*) [Magma G] (h266 : Equation266 G) : Equation323 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h266 (sK0 ◇ sK1) sK0 sK0]
    conv => enter [1, 1]; rw [← h266 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation62_implies_Equation39 (G : Type*) [Magma G] (h62 : Equation62 G) : Equation39 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h62 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2, 2]; rw [← h62 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h62 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← l0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1, 2]; rw [← h62 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)]
  have l3 : ∀ X0 sK0 X1 : G, (X0 ◇ sK0) = (X1 ◇ sK0) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l2 sK0 X0]
    conv => enter [1]; rw [l2 sK0 X1]
  intro x y
  conv => enter [1]; rw [l3 x x y]

@[equational_result]
theorem Equation62_implies_Equation58 (G : Type*) [Magma G] (h62 : Equation62 G) : Equation58 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h62 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h62 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X1 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h62 ((X0 ◇ (X0 ◇ X0)) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← l0 X0 ((X0 ◇ (X0 ◇ X0)) ◇ X0)]
  have l2 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [l1 X0 X1]
    conv => enter [1, 2]; rw [← h62 X0 ((X0 ◇ (X0 ◇ X0)) ◇ X0)]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [← l2 X1 X0]
    conv => enter [1]; rw [l2 X1 X2]
  have l4 : ∀ sK0 X0 sK2 : G, sK0 = (X0 ◇ (sK0 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [h62 sK0 X0]
    conv => enter [1, 2, 2]; rw [l3 sK0 sK0 sK2]
  have l5 : ∀ sK0 X0 sK1 sK2 : G, sK0 = (X0 ◇ (sK1 ◇ (sK2 ◇ sK0))) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l4 sK0 X0 sK2]
    conv => enter [1, 2]; rw [l3 sK0 (sK2 ◇ sK0) sK1]
  intro x y z
  conv => enter [1]; rw [l5 x x y z]

@[equational_result]
theorem Equation62_implies_Equation72 (G : Type*) [Magma G] (h62 : Equation62 G) : Equation72 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h62 (sK0 ◇ (sK0 ◇ sK0)) X0]
    conv => enter [1, 2, 2]; rw [← h62 sK0 (sK0 ◇ (sK0 ◇ sK0))]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0)))) := by
    intro sK0 X0
    conv => enter [1]; rw [h62 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) X0]
    conv => enter [1, 2, 2]; rw [← l0 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1, 2]; rw [← h62 sK0 ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0)]
  have l3 : ∀ X0 sK0 X1 : G, (X0 ◇ sK0) = (X1 ◇ sK0) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [← l2 sK0 X0]
    conv => enter [1]; rw [l2 sK0 X1]
  have l4 : ∀ sK0 X0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 2]; rw [l3 (sK0 ◇ (sK0 ◇ sK0)) sK0 sK0]
  have l5 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK1 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h62 sK0 X0]
    conv => enter [1, 2]; rw [l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y y]

@[equational_result]
theorem Equation62_implies_Equation65 (G : Type*) [Magma G] (h62 : Equation62 G) : Equation65 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h62 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h62 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X1 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h62 ((X0 ◇ (X0 ◇ X0)) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← l0 X0 ((X0 ◇ (X0 ◇ X0)) ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h62 X0 ((X0 ◇ (X0 ◇ X0)) ◇ X0)]
    conv => enter [1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l2 X2 X1]
  have l4 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h62 sK0 X0]
    conv => enter [1, 2, 2]; rw [l3 sK0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y y]

@[equational_result]
theorem Equation62_implies_Equation75 (G : Type*) [Magma G] (h62 : Equation62 G) : Equation75 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ X0)) = (X1 ◇ ((X0 ◇ (X0 ◇ X0)) ◇ X0)) := by
    intro X0 X1
    conv => enter [1]; rw [h62 (X0 ◇ (X0 ◇ X0)) X1]
    conv => enter [1, 2, 2]; rw [← h62 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ X0 X1 : G, ((X0 ◇ (X0 ◇ X0)) ◇ X0) = (X1 ◇ (((X0 ◇ (X0 ◇ X0)) ◇ X0) ◇ (X0 ◇ (X0 ◇ X0)))) := by
    intro X0 X1
    conv => enter [1]; rw [h62 ((X0 ◇ (X0 ◇ X0)) ◇ X0) X1]
    conv => enter [1, 2, 2]; rw [← l0 X0 ((X0 ◇ (X0 ◇ X0)) ◇ X0)]
  have l2 : ∀ X1 X0 : G, (X1 ◇ X0) = ((X0 ◇ (X0 ◇ X0)) ◇ X0) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h62 X0 ((X0 ◇ (X0 ◇ X0)) ◇ X0)]
    conv => enter [1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l2 X2 X1]
  have l4 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK0 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h62 sK0 X0]
    conv => enter [1, 2, 2]; rw [l3 sK0 sK0 sK1]
  have l5 : ∀ sK0 X0 sK1 : G, sK0 = (X0 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [l4 sK0 X0 sK1]
    conv => enter [1, 2]; rw [l3 sK0 (sK1 ◇ sK0) sK1]
  have l6 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK1 ◇ (sK1 ◇ sK0))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK0 sK1]
    conv => enter [1]; rw [l3 sK0 (sK1 ◇ (sK1 ◇ sK0)) sK1]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation256_implies_Equation38 (G : Type*) [Magma G] (h256 : Equation256 G) : Equation38 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h256 ((sK0 ◇ sK0) ◇ sK0) X0]
    conv => enter [1, 1, 1]; rw [← h256 sK0 ((sK0 ◇ sK0) ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h256 (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) X0]
    conv => enter [1, 1, 1]; rw [← l0 sK0 (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1, 1]; rw [← h256 sK0 (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (sK0 ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l2 sK0 X0]
    conv => enter [1]; rw [l2 sK0 X1]
  intro x y
  conv => enter [1]; rw [l3 x x y]

@[equational_result]
theorem Equation256_implies_Equation266 (G : Type*) [Magma G] (h256 : Equation256 G) : Equation266 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h256 ((X0 ◇ X0) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h256 X0 ((X0 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h256 (X0 ◇ ((X0 ◇ X0) ◇ X0)) X1]
    conv => enter [1, 1, 1]; rw [← l0 X0 (X0 ◇ ((X0 ◇ X0) ◇ X0))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h256 X0 (X0 ◇ ((X0 ◇ X0) ◇ X0))]
    conv => enter [1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l2 X0 X2]
  have l4 : ∀ sK0 sK1 X0 : G, sK0 = (((sK0 ◇ sK1) ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h256 sK0 X0]
    conv => enter [1, 1, 1]; rw [l3 sK0 sK0 sK1]
  have l5 : ∀ sK0 sK1 sK2 X0 : G, sK0 = (((sK0 ◇ sK1) ◇ sK2) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0]
    conv => enter [1, 1]; rw [l3 (sK0 ◇ sK1) sK0 sK2]
  have l6 : ∀ sK0 sK1 sK2 : G, sK0 = (((sK0 ◇ sK1) ◇ sK2) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l5 sK0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

@[equational_result]
theorem Equation256_implies_Equation258 (G : Type*) [Magma G] (h256 : Equation256 G) : Equation258 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h256 ((sK0 ◇ sK0) ◇ sK0) X0]
    conv => enter [1, 1, 1]; rw [← h256 sK0 ((sK0 ◇ sK0) ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = ((((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h256 (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) X0]
    conv => enter [1, 1, 1]; rw [← l0 sK0 (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l1 sK0 X0]
    conv => enter [1, 1]; rw [← h256 sK0 (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))]
  have l3 : ∀ sK0 X0 X1 : G, (sK0 ◇ X0) = (sK0 ◇ X1) := by
    intro sK0 X0 X1
    conv => enter [1]; rw [← l2 sK0 X0]
    conv => enter [1]; rw [l2 sK0 X1]
  have l4 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [l0 sK0 X0]
    conv => enter [1, 1]; rw [l3 sK0 ((sK0 ◇ sK0) ◇ sK0) sK0]
  have l5 : ∀ sK0 sK1 X0 : G, sK0 = (((sK0 ◇ sK0) ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h256 sK0 X0]
    conv => enter [1, 1]; rw [l4 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y y]

@[equational_result]
theorem Equation256_implies_Equation261 (G : Type*) [Magma G] (h256 : Equation256 G) : Equation261 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h256 ((X0 ◇ X0) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h256 X0 ((X0 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h256 (X0 ◇ ((X0 ◇ X0) ◇ X0)) X1]
    conv => enter [1, 1, 1]; rw [← l0 X0 (X0 ◇ ((X0 ◇ X0) ◇ X0))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h256 X0 (X0 ◇ ((X0 ◇ X0) ◇ X0))]
    conv => enter [1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l2 X0 X2]
  have l4 : ∀ sK0 sK1 X0 : G, sK0 = (((sK0 ◇ sK1) ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h256 sK0 X0]
    conv => enter [1, 1, 1]; rw [l3 sK0 sK0 sK1]
  have l5 : ∀ sK0 sK1 : G, sK0 = (((sK0 ◇ sK1) ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l4 sK0 sK1 sK0]
    conv => enter [1]; rw [l3 ((sK0 ◇ sK1) ◇ sK0) sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation256_implies_Equation264 (G : Type*) [Magma G] (h256 : Equation256 G) : Equation264 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X0) = ((X0 ◇ ((X0 ◇ X0) ◇ X0)) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h256 ((X0 ◇ X0) ◇ X0) X1]
    conv => enter [1, 1, 1]; rw [← h256 X0 ((X0 ◇ X0) ◇ X0)]
  have l1 : ∀ X0 X1 : G, (X0 ◇ ((X0 ◇ X0) ◇ X0)) = ((((X0 ◇ X0) ◇ X0) ◇ (X0 ◇ ((X0 ◇ X0) ◇ X0))) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h256 (X0 ◇ ((X0 ◇ X0) ◇ X0)) X1]
    conv => enter [1, 1, 1]; rw [← l0 X0 (X0 ◇ ((X0 ◇ X0) ◇ X0))]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = (X0 ◇ ((X0 ◇ X0) ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1]; rw [h256 X0 (X0 ◇ ((X0 ◇ X0) ◇ X0))]
    conv => enter [1]; rw [← l1 X0 X1]
  have l3 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [l2 X0 X1]
    conv => enter [1]; rw [← l2 X0 X2]
  have l4 : ∀ sK0 sK1 X0 : G, sK0 = (((sK0 ◇ sK1) ◇ sK0) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h256 sK0 X0]
    conv => enter [1, 1, 1]; rw [l3 sK0 sK0 sK1]
  have l5 : ∀ sK0 sK1 X0 : G, sK0 = (((sK0 ◇ sK1) ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l4 sK0 sK1 X0]
    conv => enter [1, 1]; rw [l3 (sK0 ◇ sK1) sK0 sK1]
  intro x y
  conv => enter [1]; rw [l5 x y y]

@[equational_result]
theorem Equation63_implies_Equation23 (G : Type*) [Magma G] (h63 : Equation63 G) : Equation23 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h63 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h63 sK0 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation63_implies_Equation47 (G : Type*) [Magma G] (h63 : Equation63 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h63 x x]

@[equational_result]
theorem Equation271_implies_Equation8 (G : Type*) [Magma G] (h271 : Equation271 G) : Equation8 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h271 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← h271 sK0 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation271_implies_Equation255 (G : Type*) [Magma G] (h271 : Equation271 G) : Equation255 G := by
  intro x
  conv => enter [1]; rw [h271 x x]

@[equational_result]
theorem Equation65_implies_Equation47 (G : Type*) [Magma G] (h65 : Equation65 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h65 x x]

@[equational_result]
theorem Equation261_implies_Equation255 (G : Type*) [Magma G] (h261 : Equation261 G) : Equation255 G := by
  intro x
  conv => enter [1]; rw [h261 x x]

@[equational_result]
theorem Equation66_implies_Equation281 (G : Type*) [Magma G] (h66 : Equation66 G) : Equation281 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h66 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h66 X0 (X0 ◇ X0)]
  have l1 : ∀ sK1 : G, sK1 = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h66 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h66 (sK1 ◇ sK1) sK1]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ (X0 ◇ sK1)) = X0 := by
    intro sK1 X0
    conv => enter [1, 2, 2]; rw [l1 sK1]
    conv => enter [1]; rw [← h66 X0 (sK1 ◇ sK1)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h66 X1 (X0 ◇ X0)]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (((((sK1 ◇ sK1) ◇ sK0) ◇ sK1) ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1)) ◇ ((sK1 ◇ sK1) ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l3 (((sK1 ◇ sK1) ◇ sK0) ◇ sK1) (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [l2 sK1 ((sK1 ◇ sK1) ◇ sK0)]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((((sK1 ◇ sK1) ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 ((sK1 ◇ sK1) ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l3 sK0 (sK1 ◇ sK1)]
  have l6 : ∀ sK1 sK0 : G, ((((sK1 ◇ sK1) ◇ sK0) ◇ sK1) ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1)) = ((((sK1 ◇ sK1) ◇ sK0) ◇ ((sK1 ◇ sK1) ◇ sK0)) ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l3 ((sK1 ◇ sK1) ◇ sK0) ((((sK1 ◇ sK1) ◇ sK0) ◇ sK1) ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1))]
    conv => enter [1, 2]; rw [← l4 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((((sK1 ◇ sK1) ◇ sK0) ◇ sK1) ◇ (((sK1 ◇ sK1) ◇ sK0) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l6 sK1 sK0]
  have l8 : ∀ sK1 sK0 : G, (((sK1 ◇ sK1) ◇ sK0) ◇ sK1) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l3 (((sK1 ◇ sK1) ◇ sK0) ◇ sK1) (((sK1 ◇ sK1) ◇ sK0) ◇ sK1)]
    conv => enter [1, 1]; rw [← l7 sK0 sK1]
    conv => enter [1, 2]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, sK0 = (((sK1 ◇ sK1) ◇ sK0) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0]
    conv => enter [1]; rw [← l8 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation66_implies_Equation47 (G : Type*) [Magma G] (h66 : Equation66 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h66 x x]

@[equational_result]
theorem Equation66_implies_Equation255 (G : Type*) [Magma G] (h66 : Equation66 G) : Equation255 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h66 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h66 X0 (X0 ◇ X0)]
  have l1 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h66 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h66 (sK0 ◇ sK0) sK0]
  have l2 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (X0 ◇ sK0)) = X0 := by
    intro sK0 X0
    conv => enter [1, 2, 2]; rw [l1 sK0]
    conv => enter [1]; rw [← h66 X0 (sK0 ◇ sK0)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ (X1 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 2, 2]; rw [← l0 X0]
    conv => enter [1]; rw [← h66 X1 (X0 ◇ X0)]
  have l4 : ∀ sK0 : G, (sK0 ◇ sK0) = ((((sK0 ◇ sK0) ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← l3 ((sK0 ◇ sK0) ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l2 sK0 (sK0 ◇ sK0)]
  have l5 : ∀ sK0 : G, (sK0 ◇ sK0) = (((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← l3 (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [l2 sK0 ((sK0 ◇ sK0) ◇ sK0)]
  have l6 : ∀ sK0 : G, ((((sK0 ◇ sK0) ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) ◇ (sK0 ◇ sK0)) = ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1, 2]; rw [l5 sK0]
    conv => enter [1]; rw [l3 ((sK0 ◇ sK0) ◇ sK0) ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0))]
  have l7 : ∀ sK0 : G, (sK0 ◇ sK0) = ((((sK0 ◇ sK0) ◇ sK0) ◇ sK0) ◇ (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l4 sK0]
    conv => enter [1]; rw [l6 sK0]
  have l8 : ∀ sK0 : G, (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [← l3 (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) (((sK0 ◇ sK0) ◇ sK0) ◇ sK0)]
    conv => enter [1, 1]; rw [← l7 sK0]
    conv => enter [1, 2]; rw [← l7 sK0]
  have l9 : ∀ sK0 : G, sK0 = (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1]; rw [← l8 sK0]
  intro x
  conv => enter [1]; rw [l9 x]

@[equational_result]
theorem Equation66_implies_Equation151 (G : Type*) [Magma G] (h66 : Equation66 G) : Equation151 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h66 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h66 (sK0 ◇ sK0) sK0]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation281_implies_Equation66 (G : Type*) [Magma G] (h281 : Equation281 G) : Equation66 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h281 (X0 ◇ X0) X0]
    conv => enter [1]; rw [← h281 X0 (X0 ◇ X0)]
  have l1 : ∀ sK1 : G, sK1 = ((sK1 ◇ sK1) ◇ (sK1 ◇ sK1)) := by
    intro sK1
    conv => enter [1]; rw [h281 sK1 (sK1 ◇ sK1)]
    conv => enter [1, 1]; rw [← h281 (sK1 ◇ sK1) sK1]
  have l2 : ∀ sK1 X0 : G, ((sK1 ◇ X0) ◇ (sK1 ◇ sK1)) = X0 := by
    intro sK1 X0
    conv => enter [1, 1, 1]; rw [l1 sK1]
    conv => enter [1]; rw [← h281 X0 (sK1 ◇ sK1)]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ (X0 ◇ X0)) = X1 := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l0 X0]
    conv => enter [1]; rw [← h281 X1 (X0 ◇ X0)]
  have l4 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = ((sK0 ◇ (sK1 ◇ sK1)) ◇ ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l3 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ sK1)]
    conv => enter [1, 1]; rw [l2 sK1 (sK0 ◇ (sK1 ◇ sK1))]
  have l5 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l3 (sK0 ◇ (sK1 ◇ sK1)) (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [l3 sK0 (sK1 ◇ sK1)]
  have l6 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) = ((sK1 ◇ sK1) ◇ ((sK0 ◇ (sK1 ◇ sK1)) ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l3 (sK0 ◇ (sK1 ◇ sK1)) ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))))]
    conv => enter [1, 1]; rw [← l4 sK1 sK0]
  have l7 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) ◇ (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [← l6 sK1 sK0]
  have l8 : ∀ sK1 sK0 : G, (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l3 (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1)))]
    conv => enter [1, 1]; rw [← l7 sK0 sK1]
    conv => enter [1, 2]; rw [← l7 sK0 sK1]
  have l9 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ (sK0 ◇ (sK1 ◇ sK1))) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l0 sK0]
    conv => enter [1]; rw [← l8 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation72_implies_Equation55 (G : Type*) [Magma G] (h72 : Equation72 G) : Equation55 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = ((X0 ◇ X0) ◇ X0) := by
    intro X0
    conv => enter [1]; rw [h72 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 2]; rw [← h72 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [l0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h72 X0 ((X0 ◇ X0) ◇ (X0 ◇ X0))]
  have l2 : ∀ X0 : G, (X0 ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← l0 ((X0 ◇ X0) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X1 ◇ X0)) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X1 X0
    conv => enter [1, 2, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← h72 ((X0 ◇ X0) ◇ (X0 ◇ X0)) X1]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ (X0 ◇ X1))) = X1 := by
    intro X1 X0
    conv => enter [1, 2]; rw [l3 X0 X1]
    conv => enter [1]; rw [l2 X1]
  intro x y
  conv => enter [1]; rw [← l4 x y]

@[equational_result]
theorem Equation258_implies_Equation263 (G : Type*) [Magma G] (h258 : Equation258 G) : Equation263 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = (X0 ◇ (X0 ◇ X0)) := by
    intro X0
    conv => enter [1]; rw [h258 (X0 ◇ X0) (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h258 X0 (X0 ◇ X0)]
  have l1 : ∀ X0 : G, (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ ((X0 ◇ X0) ◇ (X0 ◇ X0))) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [l0 (X0 ◇ X0)]
    conv => enter [1]; rw [← h258 X0 ((X0 ◇ X0) ◇ (X0 ◇ X0))]
  have l2 : ∀ X0 : G, (((X0 ◇ X0) ◇ (X0 ◇ X0)) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [← l1 X0]
    conv => enter [1]; rw [← l0 ((X0 ◇ X0) ◇ (X0 ◇ X0))]
    conv => enter [1]; rw [l1 X0]
  have l3 : ∀ X0 X1 : G, ((X0 ◇ X1) ◇ X1) = ((X0 ◇ X0) ◇ (X0 ◇ X0)) := by
    intro X0 X1
    conv => enter [1, 1, 1]; rw [← l1 X0]
    conv => enter [1]; rw [← h258 ((X0 ◇ X0) ◇ (X0 ◇ X0)) X1]
  have l4 : ∀ X0 X1 : G, (((X0 ◇ X1) ◇ X1) ◇ X0) = X0 := by
    intro X0 X1
    conv => enter [1, 1]; rw [l3 X0 X1]
    conv => enter [1]; rw [l2 X0]
  intro x y
  conv => enter [1]; rw [← l4 x y]

@[equational_result]
theorem Equation73_implies_Equation47 (G : Type*) [Magma G] (h73 : Equation73 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h73 x x]

@[equational_result]
theorem Equation274_implies_Equation255 (G : Type*) [Magma G] (h274 : Equation274 G) : Equation255 G := by
  intro x
  conv => enter [1]; rw [h274 x x]

@[equational_result]
theorem Equation75_implies_Equation47 (G : Type*) [Magma G] (h75 : Equation75 G) : Equation47 G := by
  intro x
  conv => enter [1]; rw [h75 x x]

@[equational_result]
theorem Equation264_implies_Equation255 (G : Type*) [Magma G] (h264 : Equation264 G) : Equation255 G := by
  intro x
  conv => enter [1]; rw [h264 x x]

@[equational_result]
theorem Equation100_implies_Equation8 (G : Type*) [Magma G] (h100 : Equation100 G) : Equation8 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h100 sK0 (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ sK0)]
    conv => enter [1, 2]; rw [← h100 (sK0 ◇ sK0) sK0]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation100_implies_Equation99 (G : Type*) [Magma G] (h100 : Equation100 G) : Equation99 G := by
  intro x
  conv => enter [1]; rw [h100 x x]

@[equational_result]
theorem Equation218_implies_Equation23 (G : Type*) [Magma G] (h218 : Equation218 G) : Equation23 G := by
  have l0 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h218 sK0 (sK0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)))]
    conv => enter [1, 1]; rw [← h218 (sK0 ◇ sK0) sK0]
  intro x
  conv => enter [1]; rw [l0 x]

@[equational_result]
theorem Equation218_implies_Equation203 (G : Type*) [Magma G] (h218 : Equation218 G) : Equation203 G := by
  intro x
  conv => enter [1]; rw [h218 x x]

@[equational_result]
theorem Equation101_implies_Equation8 (G : Type*) [Magma G] (h101 : Equation101 G) : Equation8 G := by
  have l0 : ∀ X0 : G, (X0 ◇ (X0 ◇ X0)) = X0 := by
    intro X0
    conv => enter [1, 2, 1]; rw [h101 X0 X0]
    conv => enter [1]; rw [← h101 X0 ((X0 ◇ X0) ◇ X0)]
  intro x
  conv => enter [1]; rw [← l0 x]

@[equational_result]
theorem Equation101_implies_Equation99 (G : Type*) [Magma G] (h101 : Equation101 G) : Equation99 G := by
  intro x
  conv => enter [1]; rw [h101 x x]

@[equational_result]
theorem Equation208_implies_Equation23 (G : Type*) [Magma G] (h208 : Equation208 G) : Equation23 G := by
  have l0 : ∀ X0 : G, ((X0 ◇ X0) ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1, 2]; rw [h208 X0 X0]
    conv => enter [1]; rw [← h208 X0 (X0 ◇ (X0 ◇ X0))]
  intro x
  conv => enter [1]; rw [← l0 x]

@[equational_result]
theorem Equation208_implies_Equation203 (G : Type*) [Magma G] (h208 : Equation208 G) : Equation203 G := by
  intro x
  conv => enter [1]; rw [h208 x x]

@[equational_result]
theorem Equation102_implies_Equation3 (G : Type*) [Magma G] (h102 : Equation102 G) : Equation3 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ ((X0 ◇ X1) ◇ X1))) = X0 := by
    intro X0 X1
    conv => enter [1, 2, 1]; rw [h102 X0 X1]
    conv => enter [1]; rw [← h102 X0 ((X0 ◇ X1) ◇ X1)]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h102 X0 X0]
    conv => enter [1]; rw [l0 X0 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

@[equational_result]
theorem Equation228_implies_Equation3 (G : Type*) [Magma G] (h228 : Equation228 G) : Equation3 G := by
  have l0 : ∀ X1 X0 : G, (((X1 ◇ (X1 ◇ X0)) ◇ X0) ◇ X0) = X0 := by
    intro X1 X0
    conv => enter [1, 1, 2]; rw [h228 X0 X1]
    conv => enter [1]; rw [← h228 X0 (X1 ◇ (X1 ◇ X0))]
  have l1 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h228 X0 X0]
    conv => enter [1]; rw [l0 X0 X0]
  intro x
  conv => enter [1]; rw [← l1 x]

@[equational_result]
theorem Equation103_implies_Equation9 (G : Type*) [Magma G] (h103 : Equation103 G) : Equation9 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h103 sK0 sK1 (((sK0 ◇ sK1) ◇ sK0) ◇ sK0)]
    conv => enter [1, 2]; rw [← h103 (sK0 ◇ sK1) sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation103_implies_Equation102 (G : Type*) [Magma G] (h103 : Equation103 G) : Equation102 G := by
  intro x y
  conv => enter [1]; rw [h103 x y y]

@[equational_result]
theorem Equation103_implies_Equation101 (G : Type*) [Magma G] (h103 : Equation103 G) : Equation101 G := by
  intro x y
  conv => enter [1]; rw [h103 x y x]

@[equational_result]
theorem Equation238_implies_Equation28 (G : Type*) [Magma G] (h238 : Equation238 G) : Equation28 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h238 sK0 (sK0 ◇ (sK0 ◇ (sK1 ◇ sK0))) sK1]
    conv => enter [1, 1]; rw [← h238 (sK1 ◇ sK0) sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation238_implies_Equation228 (G : Type*) [Magma G] (h238 : Equation238 G) : Equation228 G := by
  intro x y
  conv => enter [1]; rw [h238 x y y]

@[equational_result]
theorem Equation238_implies_Equation208 (G : Type*) [Magma G] (h238 : Equation238 G) : Equation208 G := by
  intro x y
  conv => enter [1]; rw [h238 x x y]

@[equational_result]
theorem Equation104_implies_Equation99 (G : Type*) [Magma G] (h104 : Equation104 G) : Equation99 G := by
  intro x
  conv => enter [1]; rw [h104 x x]

@[equational_result]
theorem Equation205_implies_Equation203 (G : Type*) [Magma G] (h205 : Equation205 G) : Equation203 G := by
  intro x
  conv => enter [1]; rw [h205 x x]

@[equational_result]
theorem Equation105_implies_Equation99 (G : Type*) [Magma G] (h105 : Equation105 G) : Equation99 G := by
  intro x
  conv => enter [1]; rw [h105 x x]

@[equational_result]
theorem Equation221_implies_Equation203 (G : Type*) [Magma G] (h221 : Equation221 G) : Equation203 G := by
  intro x
  conv => enter [1]; rw [h221 x x]

@[equational_result]
theorem Equation106_implies_Equation10 (G : Type*) [Magma G] (h106 : Equation106 G) : Equation10 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = (sK0 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h106 sK0 sK1 ((sK0 ◇ (sK1 ◇ sK0)) ◇ sK0)]
    conv => enter [1, 2]; rw [← h106 (sK1 ◇ sK0) sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation106_implies_Equation100 (G : Type*) [Magma G] (h106 : Equation106 G) : Equation100 G := by
  intro x y
  conv => enter [1]; rw [h106 x x y]

@[equational_result]
theorem Equation106_implies_Equation105 (G : Type*) [Magma G] (h106 : Equation106 G) : Equation105 G := by
  intro x y
  conv => enter [1]; rw [h106 x y y]

@[equational_result]
theorem Equation224_implies_Equation25 (G : Type*) [Magma G] (h224 : Equation224 G) : Equation25 G := by
  have l0 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h224 sK0 (sK0 ◇ ((sK0 ◇ sK1) ◇ sK0)) sK1]
    conv => enter [1, 1]; rw [← h224 (sK0 ◇ sK1) sK0 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation224_implies_Equation218 (G : Type*) [Magma G] (h224 : Equation224 G) : Equation218 G := by
  intro x y
  conv => enter [1]; rw [h224 x y x]

@[equational_result]
theorem Equation224_implies_Equation221 (G : Type*) [Magma G] (h224 : Equation224 G) : Equation221 G := by
  intro x y
  conv => enter [1]; rw [h224 x y y]

@[equational_result]
theorem Equation107_implies_Equation99 (G : Type*) [Magma G] (h107 : Equation107 G) : Equation99 G := by
  intro x
  conv => enter [1]; rw [h107 x x]

@[equational_result]
theorem Equation211_implies_Equation203 (G : Type*) [Magma G] (h211 : Equation211 G) : Equation203 G := by
  intro x
  conv => enter [1]; rw [h211 x x]

@[equational_result]
theorem Equation108_implies_Equation99 (G : Type*) [Magma G] (h108 : Equation108 G) : Equation99 G := by
  intro x
  conv => enter [1]; rw [h108 x x]

@[equational_result]
theorem Equation231_implies_Equation203 (G : Type*) [Magma G] (h231 : Equation231 G) : Equation203 G := by
  intro x
  conv => enter [1]; rw [h231 x x]

@[equational_result]
theorem Equation109_implies_Equation11 (G : Type*) [Magma G] (h109 : Equation109 G) : Equation11 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = X0 := by
    intro X0 sK1
    conv => enter [1, 2]; rw [h109 (sK1 ◇ sK1) sK1 X0]
    conv => enter [1]; rw [← h109 X0 sK1 ((sK1 ◇ sK1) ◇ X0)]
  intro x y
  conv => enter [1]; rw [← l0 x y]

@[equational_result]
theorem Equation109_implies_Equation108 (G : Type*) [Magma G] (h109 : Equation109 G) : Equation108 G := by
  intro x y
  conv => enter [1]; rw [h109 x y y]

@[equational_result]
theorem Equation109_implies_Equation100 (G : Type*) [Magma G] (h109 : Equation109 G) : Equation100 G := by
  intro x y
  conv => enter [1]; rw [h109 x x y]

@[equational_result]
theorem Equation109_implies_Equation107 (G : Type*) [Magma G] (h109 : Equation109 G) : Equation107 G := by
  intro x y
  conv => enter [1]; rw [h109 x y x]

@[equational_result]
theorem Equation246_implies_Equation31 (G : Type*) [Magma G] (h246 : Equation246 G) : Equation31 G := by
  have l0 : ∀ sK1 X1 : G, ((sK1 ◇ sK1) ◇ X1) = X1 := by
    intro sK1 X1
    conv => enter [1, 1]; rw [h246 (sK1 ◇ sK1) sK1 sK1]
    conv => enter [1]; rw [← h246 X1 (sK1 ◇ (sK1 ◇ sK1)) sK1]
  intro x y
  conv => enter [1]; rw [← l0 y x]

@[equational_result]
theorem Equation246_implies_Equation231 (G : Type*) [Magma G] (h246 : Equation246 G) : Equation231 G := by
  intro x y
  conv => enter [1]; rw [h246 x y y]

@[equational_result]
theorem Equation246_implies_Equation218 (G : Type*) [Magma G] (h246 : Equation246 G) : Equation218 G := by
  intro x y
  conv => enter [1]; rw [h246 x y x]

@[equational_result]
theorem Equation246_implies_Equation211 (G : Type*) [Magma G] (h246 : Equation246 G) : Equation211 G := by
  intro x y
  conv => enter [1]; rw [h246 x x y]

@[equational_result]
theorem Equation111_implies_Equation109 (G : Type*) [Magma G] (h111 : Equation111 G) : Equation109 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = X1 := by
    intro X1 X0
    conv => enter [1, 2, 1]; rw [h111 X0 X1 X1]
    conv => enter [1]; rw [← h111 X1 X0 ((X1 ◇ X1) ◇ X1)]
  have l1 : ∀ X0 sK1 sK2 : G, (X0 ◇ ((sK1 ◇ sK1) ◇ sK2)) = X0 := by
    intro X0 sK1 sK2
    conv => enter [1, 2]; rw [← l0 ((sK1 ◇ sK1) ◇ sK2) sK1]
    conv => enter [1]; rw [← h111 X0 (sK1 ◇ sK1) sK2]
  intro x y z
  conv => enter [1]; rw [← l1 x y z]

@[equational_result]
theorem Equation111_implies_Equation105 (G : Type*) [Magma G] (h111 : Equation111 G) : Equation105 G := by
  intro x y
  conv => enter [1]; rw [h111 x y x]

@[equational_result]
theorem Equation111_implies_Equation101 (G : Type*) [Magma G] (h111 : Equation111 G) : Equation101 G := by
  intro x y
  conv => enter [1]; rw [h111 x x y]

@[equational_result]
theorem Equation242_implies_Equation246 (G : Type*) [Magma G] (h242 : Equation242 G) : Equation246 G := by
  have l0 : ∀ X0 X3 : G, ((X0 ◇ X0) ◇ X3) = X3 := by
    intro X0 X3
    conv => enter [1, 1, 2]; rw [h242 X0 X0 X0]
    conv => enter [1]; rw [← h242 X3 X0 (X0 ◇ (X0 ◇ X0))]
  have l1 : ∀ sK1 sK2 X0 : G, ((sK1 ◇ (sK2 ◇ sK2)) ◇ X0) = X0 := by
    intro sK1 sK2 X0
    conv => enter [1, 1]; rw [← l0 sK2 (sK1 ◇ (sK2 ◇ sK2))]
    conv => enter [1]; rw [← h242 X0 (sK2 ◇ sK2) sK1]
  intro x y z
  conv => enter [1]; rw [← l1 y z x]

@[equational_result]
theorem Equation242_implies_Equation221 (G : Type*) [Magma G] (h242 : Equation242 G) : Equation221 G := by
  intro x y
  conv => enter [1]; rw [h242 x y x]

@[equational_result]
theorem Equation242_implies_Equation208 (G : Type*) [Magma G] (h242 : Equation242 G) : Equation208 G := by
  intro x y
  conv => enter [1]; rw [h242 x x y]

@[equational_result]
theorem Equation115_implies_Equation99 (G : Type*) [Magma G] (h115 : Equation115 G) : Equation99 G := by
  intro x
  conv => enter [1]; rw [h115 x x]

@[equational_result]
theorem Equation219_implies_Equation203 (G : Type*) [Magma G] (h219 : Equation219 G) : Equation203 G := by
  intro x
  conv => enter [1]; rw [h219 x x]

@[equational_result]
theorem Equation117_implies_Equation99 (G : Type*) [Magma G] (h117 : Equation117 G) : Equation99 G := by
  intro x
  conv => enter [1]; rw [h117 x x]

@[equational_result]
theorem Equation209_implies_Equation203 (G : Type*) [Magma G] (h209 : Equation209 G) : Equation203 G := by
  intro x
  conv => enter [1]; rw [h209 x x]

@[equational_result]
theorem Equation118_implies_Equation47 (G : Type*) [Magma G] (h118 : Equation118 G) : Equation47 G := by
  have l0 : ∀ sK0 : G, sK0 = (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h118 sK0 ((sK0 ◇ sK0) ◇ sK0)]
    conv => enter [1, 2, 1]; rw [← h118 sK0 sK0]
  have l1 : ∀ sK0 : G, sK0 = (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1, 2]; rw [← h118 sK0 sK0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2, 1]; rw [l1 sK0]
    conv => enter [1]; rw [← h118 ((sK0 ◇ sK0) ◇ sK0) sK0]
  have l3 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h118 sK0 sK0]
    conv => enter [1, 2]; rw [← l2 sK0]
  intro x
  conv => enter [1]; rw [l3 x]

@[equational_result]
theorem Equation118_implies_Equation255 (G : Type*) [Magma G] (h118 : Equation118 G) : Equation255 G := by
  have l0 : ∀ sK0 : G, sK0 = (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h118 sK0 ((sK0 ◇ sK0) ◇ sK0)]
    conv => enter [1, 2, 1]; rw [← h118 sK0 sK0]
  have l1 : ∀ sK0 : G, sK0 = (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1, 2]; rw [← h118 sK0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

@[equational_result]
theorem Equation118_implies_Equation99 (G : Type*) [Magma G] (h118 : Equation118 G) : Equation99 G := by
  intro x
  conv => enter [1]; rw [h118 x x]

@[equational_result]
theorem Equation118_implies_Equation203 (G : Type*) [Magma G] (h118 : Equation118 G) : Equation203 G := by
  have l0 : ∀ sK0 : G, sK0 = (((sK0 ◇ sK0) ◇ sK0) ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h118 sK0 ((sK0 ◇ sK0) ◇ sK0)]
    conv => enter [1, 2, 1]; rw [← h118 sK0 sK0]
  have l1 : ∀ sK0 : G, sK0 = (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1, 2]; rw [← h118 sK0 sK0]
  have l2 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2, 1]; rw [l1 sK0]
    conv => enter [1]; rw [← h118 ((sK0 ◇ sK0) ◇ sK0) sK0]
  have l3 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1, 1]; rw [← l2 sK0]
  intro x
  conv => enter [1]; rw [l3 x]

@[equational_result]
theorem Equation229_implies_Equation47 (G : Type*) [Magma G] (h229 : Equation229 G) : Equation47 G := by
  have l0 : ∀ sK0 : G, sK0 = (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h229 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 1, 2]; rw [← h229 sK0 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1, 1]; rw [← h229 sK0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

@[equational_result]
theorem Equation229_implies_Equation255 (G : Type*) [Magma G] (h229 : Equation229 G) : Equation255 G := by
  have l0 : ∀ sK0 : G, sK0 = (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h229 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 1, 2]; rw [← h229 sK0 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1, 1]; rw [← h229 sK0 sK0]
  have l2 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 1, 2]; rw [l1 sK0]
    conv => enter [1]; rw [← h229 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l3 : ∀ sK0 : G, sK0 = (((sK0 ◇ sK0) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h229 sK0 sK0]
    conv => enter [1, 1]; rw [← l2 sK0]
  intro x
  conv => enter [1]; rw [l3 x]

@[equational_result]
theorem Equation229_implies_Equation99 (G : Type*) [Magma G] (h229 : Equation229 G) : Equation99 G := by
  have l0 : ∀ sK0 : G, sK0 = (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h229 sK0 (sK0 ◇ (sK0 ◇ sK0))]
    conv => enter [1, 1, 2]; rw [← h229 sK0 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [l0 sK0]
    conv => enter [1, 1]; rw [← h229 sK0 sK0]
  have l2 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 1, 2]; rw [l1 sK0]
    conv => enter [1]; rw [← h229 (sK0 ◇ (sK0 ◇ sK0)) sK0]
  have l3 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1, 2]; rw [← l2 sK0]
  intro x
  conv => enter [1]; rw [l3 x]

@[equational_result]
theorem Equation229_implies_Equation203 (G : Type*) [Magma G] (h229 : Equation229 G) : Equation203 G := by
  intro x
  conv => enter [1]; rw [h229 x x]

@[equational_result]
theorem Equation124_implies_Equation8 (G : Type*) [Magma G] (h124 : Equation124 G) : Equation8 G := by
  have l0 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h124 ((sK0 ◇ sK0) ◇ sK0) sK0]
    conv => enter [1, 2, 1]; rw [← h124 sK0 sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h124 sK0 sK0]
    conv => enter [1]; rw [← l0 sK0]
  have l2 : ∀ sK0 : G, sK0 = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h124 sK0 sK0]
    conv => enter [1, 2]; rw [← l1 sK0]
  intro x
  conv => enter [1]; rw [l2 x]

@[equational_result]
theorem Equation124_implies_Equation151 (G : Type*) [Magma G] (h124 : Equation124 G) : Equation151 G := by
  have l0 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h124 ((sK0 ◇ sK0) ◇ sK0) sK0]
    conv => enter [1, 2, 1]; rw [← h124 sK0 sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h124 sK0 sK0]
    conv => enter [1]; rw [← l0 sK0]
  have l2 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h124 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 2, 1]; rw [← l1 sK0]
  have l3 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1, 2]; rw [← l1 sK0]
  intro x
  conv => enter [1]; rw [l3 x]

@[equational_result]
theorem Equation124_implies_Equation99 (G : Type*) [Magma G] (h124 : Equation124 G) : Equation99 G := by
  intro x
  conv => enter [1]; rw [h124 x x]

@[equational_result]
theorem Equation124_implies_Equation359 (G : Type*) [Magma G] (h124 : Equation124 G) : Equation359 G := by
  have l0 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0))) := by
    intro sK0
    conv => enter [1]; rw [h124 ((sK0 ◇ sK0) ◇ sK0) sK0]
    conv => enter [1, 2, 1]; rw [← h124 sK0 sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1, 2]; rw [h124 sK0 sK0]
    conv => enter [1]; rw [← l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

@[equational_result]
theorem Equation206_implies_Equation23 (G : Type*) [Magma G] (h206 : Equation206 G) : Equation23 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h206 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 1, 2]; rw [← h206 sK0 sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 1]; rw [h206 sK0 sK0]
    conv => enter [1]; rw [← l0 sK0]
  have l2 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h206 sK0 sK0]
    conv => enter [1, 1]; rw [← l1 sK0]
  intro x
  conv => enter [1]; rw [l2 x]

@[equational_result]
theorem Equation206_implies_Equation151 (G : Type*) [Magma G] (h206 : Equation206 G) : Equation151 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h206 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 1, 2]; rw [← h206 sK0 sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 1]; rw [h206 sK0 sK0]
    conv => enter [1]; rw [← l0 sK0]
  have l2 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK0)) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h206 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 1, 2]; rw [← l1 sK0]
  have l3 : ∀ sK0 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [l2 sK0]
    conv => enter [1, 1]; rw [← l1 sK0]
  intro x
  conv => enter [1]; rw [l3 x]

@[equational_result]
theorem Equation206_implies_Equation203 (G : Type*) [Magma G] (h206 : Equation206 G) : Equation203 G := by
  intro x
  conv => enter [1]; rw [h206 x x]

@[equational_result]
theorem Equation206_implies_Equation307 (G : Type*) [Magma G] (h206 : Equation206 G) : Equation307 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = (((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h206 (sK0 ◇ (sK0 ◇ sK0)) sK0]
    conv => enter [1, 1, 2]; rw [← h206 sK0 sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1, 1]; rw [h206 sK0 sK0]
    conv => enter [1]; rw [← l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

@[equational_result]
theorem Equation125_implies_Equation73 (G : Type*) [Magma G] (h125 : Equation125 G) : Equation73 G := by
  have l0 : ∀ X1 X0 : G, ((X1 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h125 ((X1 ◇ X0) ◇ X1) X1]
    conv => enter [1, 2, 1]; rw [← h125 X0 X1]
  have l1 : ∀ X0 X1 : G, (X0 ◇ (X0 ◇ (X1 ◇ X0))) = X1 := by
    intro X0 X1
    conv => enter [1, 2]; rw [← l0 X0 X1]
    conv => enter [1]; rw [← h125 X1 X0]
  intro x y
  conv => enter [1]; rw [← l1 y x]

@[equational_result]
theorem Equation125_implies_Equation229 (G : Type*) [Magma G] (h125 : Equation125 G) : Equation229 G := by
  have l0 : ∀ sK1 sK0 : G, ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) = (sK1 ◇ ((sK1 ◇ sK0) ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h125 ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) sK1]
    conv => enter [1, 2, 1]; rw [← h125 (sK1 ◇ sK0) sK1]
  have l1 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ (sK1 ◇ sK0)) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h125 sK0 sK1]
    conv => enter [1]; rw [← l0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation222_implies_Equation118 (G : Type*) [Magma G] (h222 : Equation222 G) : Equation118 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h222 (X1 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h222 X0 X1]
  have l1 : ∀ sK0 sK1 : G, sK0 = (sK1 ◇ ((sK0 ◇ sK1) ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h222 sK0 sK1]
    conv => enter [1]; rw [← l0 sK1 (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation222_implies_Equation274 (G : Type*) [Magma G] (h222 : Equation222 G) : Equation274 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X1)) = ((X1 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h222 (X1 ◇ (X0 ◇ X1)) X1]
    conv => enter [1, 1, 2]; rw [← h222 X0 X1]
  have l1 : ∀ sK0 sK1 : G, sK0 = (((sK1 ◇ sK0) ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [h222 sK0 sK1]
    conv => enter [1, 1]; rw [l0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l1 x y]

@[equational_result]
theorem Equation127_implies_Equation151 (G : Type*) [Magma G] (h127 : Equation127 G) : Equation151 G := by
  have l0 : ∀ sK0 X0 : G, (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h127 (((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0) sK0]
    conv => enter [1, 2]; rw [← h127 X0 (sK0 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = X0 := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l0 sK0 X0]
    conv => enter [1]; rw [← h127 X0 (sK0 ◇ sK0)]
  intro x
  conv => enter [1]; rw [← l1 x x]

@[equational_result]
theorem Equation127_implies_Equation99 (G : Type*) [Magma G] (h127 : Equation127 G) : Equation99 G := by
  intro x
  conv => enter [1]; rw [h127 x x]

@[equational_result]
theorem Equation212_implies_Equation151 (G : Type*) [Magma G] (h212 : Equation212 G) : Equation151 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) = (X0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [h212 (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0))) sK0]
    conv => enter [1, 1]; rw [← h212 X0 (sK0 ◇ sK0)]
  have l1 : ∀ X0 sK0 : G, ((X0 ◇ sK0) ◇ (sK0 ◇ sK0)) = X0 := by
    intro X0 sK0
    conv => enter [1, 1]; rw [← l0 X0 sK0]
    conv => enter [1]; rw [← h212 X0 (sK0 ◇ sK0)]
  intro x
  conv => enter [1]; rw [← l1 x x]

@[equational_result]
theorem Equation212_implies_Equation203 (G : Type*) [Magma G] (h212 : Equation212 G) : Equation203 G := by
  intro x
  conv => enter [1]; rw [h212 x x]

@[equational_result]
theorem Equation138_implies_Equation127 (G : Type*) [Magma G] (h138 : Equation138 G) : Equation127 G := by
  intro x y
  conv => enter [1]; rw [h138 x y y]

@[equational_result]
theorem Equation138_implies_Equation117 (G : Type*) [Magma G] (h138 : Equation138 G) : Equation117 G := by
  intro x y
  conv => enter [1]; rw [h138 x y x]

@[equational_result]
theorem Equation138_implies_Equation166 (G : Type*) [Magma G] (h138 : Equation138 G) : Equation166 G := by
  have l0 : ∀ sK1 sK0 X0 : G, (((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0) = (sK0 ◇ X0) := by
    intro sK1 sK0 X0
    conv => enter [1]; rw [h138 (((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) ◇ X0) sK0 sK0]
    conv => enter [1, 2]; rw [← h138 X0 (sK0 ◇ sK0) (sK1 ◇ sK0)]
  have l1 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ X0)) = X0 := by
    intro sK0 X0
    conv => enter [1, 2]; rw [← l0 sK0 sK0 X0]
    conv => enter [1]; rw [← h138 X0 (sK0 ◇ sK0) (sK0 ◇ sK0)]
  have l2 : ∀ sK1 sK0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK0
    conv => enter [1]; rw [← l1 sK0 ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0))]
    conv => enter [1, 2]; rw [← h138 (sK0 ◇ sK0) sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, sK0 = ((sK1 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK0]
    conv => enter [1]; rw [← l2 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation138_implies_Equation104 (G : Type*) [Magma G] (h138 : Equation138 G) : Equation104 G := by
  intro x y
  conv => enter [1]; rw [h138 x x y]

@[equational_result]
theorem Equation138_implies_Equation159 (G : Type*) [Magma G] (h138 : Equation138 G) : Equation159 G := by
  have l0 : ∀ sK0 sK1 X0 : G, (((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ X0) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [h138 (((sK0 ◇ sK1) ◇ (sK1 ◇ sK0)) ◇ X0) sK0 sK1]
    conv => enter [1, 2]; rw [← h138 X0 (sK1 ◇ sK0) (sK0 ◇ sK1)]
  have l1 : ∀ sK1 sK0 X0 : G, ((sK1 ◇ sK0) ◇ (sK0 ◇ X0)) = X0 := by
    intro sK1 sK0 X0
    conv => enter [1, 2]; rw [← l0 sK0 sK1 X0]
    conv => enter [1]; rw [← h138 X0 (sK1 ◇ sK0) (sK0 ◇ sK1)]
  have l2 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ (sK1 ◇ X0)) = X0 := by
    intro sK0 sK1 X0
    conv => enter [1, 2, 1]; rw [← l1 sK1 sK0 sK1]
    conv => enter [1]; rw [← h138 X0 (sK0 ◇ sK1) (sK1 ◇ sK0)]
  intro x y
  conv => enter [1]; rw [← l2 x y x]

@[equational_result]
theorem Equation215_implies_Equation212 (G : Type*) [Magma G] (h215 : Equation215 G) : Equation212 G := by
  intro x y
  conv => enter [1]; rw [h215 x y y]

@[equational_result]
theorem Equation215_implies_Equation209 (G : Type*) [Magma G] (h215 : Equation215 G) : Equation209 G := by
  intro x y
  conv => enter [1]; rw [h215 x y x]

@[equational_result]
theorem Equation215_implies_Equation152 (G : Type*) [Magma G] (h215 : Equation215 G) : Equation152 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1))) = (X0 ◇ sK0) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h215 (X0 ◇ ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1))) sK0 sK0]
    conv => enter [1, 1]; rw [← h215 X0 (sK0 ◇ sK0) (sK0 ◇ sK1)]
  have l1 : ∀ X0 sK0 : G, ((X0 ◇ sK0) ◇ (sK0 ◇ sK0)) = X0 := by
    intro X0 sK0
    conv => enter [1, 1]; rw [← l0 X0 sK0 X0]
    conv => enter [1]; rw [← h215 X0 (sK0 ◇ sK0) (sK0 ◇ X0)]
  have l2 : ∀ sK0 sK1 : G, ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) sK0]
    conv => enter [1, 1]; rw [← h215 (sK0 ◇ sK0) sK0 sK1]
  have l3 : ∀ sK0 sK1 : G, sK0 = ((sK0 ◇ sK0) ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [← l1 sK0 sK0]
    conv => enter [1]; rw [← l2 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation215_implies_Equation205 (G : Type*) [Magma G] (h215 : Equation215 G) : Equation205 G := by
  intro x y
  conv => enter [1]; rw [h215 x x y]

@[equational_result]
theorem Equation215_implies_Equation159 (G : Type*) [Magma G] (h215 : Equation215 G) : Equation159 G := by
  have l0 : ∀ X0 sK0 sK1 : G, (X0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) = (X0 ◇ sK0) := by
    intro X0 sK0 sK1
    conv => enter [1]; rw [h215 (X0 ◇ ((sK0 ◇ sK1) ◇ (sK1 ◇ sK0))) sK0 sK1]
    conv => enter [1, 1]; rw [← h215 X0 (sK0 ◇ sK1) (sK1 ◇ sK0)]
  have l1 : ∀ X0 sK0 sK1 : G, ((X0 ◇ sK0) ◇ (sK0 ◇ sK1)) = X0 := by
    intro X0 sK0 sK1
    conv => enter [1, 1]; rw [← l0 X0 sK0 sK1]
    conv => enter [1]; rw [← h215 X0 (sK0 ◇ sK1) (sK1 ◇ sK0)]
  have l2 : ∀ X0 sK1 sK0 : G, ((X0 ◇ sK1) ◇ (sK1 ◇ sK0)) = X0 := by
    intro X0 sK1 sK0
    conv => enter [1, 1, 2]; rw [← l1 sK1 sK0 sK1]
    conv => enter [1]; rw [← h215 X0 (sK1 ◇ sK0) (sK0 ◇ sK1)]
  intro x y
  conv => enter [1]; rw [← l2 x y x]

@[equational_result]
theorem Equation152_implies_Equation151 (G : Type*) [Magma G] (h152 : Equation152 G) : Equation151 G := by
  intro x
  conv => enter [1]; rw [h152 x x]

@[equational_result]
theorem Equation166_implies_Equation151 (G : Type*) [Magma G] (h166 : Equation166 G) : Equation151 G := by
  intro x
  conv => enter [1]; rw [h166 x x]

@[equational_result]
theorem Equation153_implies_Equation151 (G : Type*) [Magma G] (h153 : Equation153 G) : Equation151 G := by
  intro x
  conv => enter [1]; rw [h153 x x]

@[equational_result]
theorem Equation156_implies_Equation151 (G : Type*) [Magma G] (h156 : Equation156 G) : Equation151 G := by
  intro x
  conv => enter [1]; rw [h156 x x]

@[equational_result]
theorem Equation159_implies_Equation151 (G : Type*) [Magma G] (h159 : Equation159 G) : Equation151 G := by
  intro x
  conv => enter [1]; rw [h159 x x]

@[equational_result]
theorem Equation162_implies_Equation153 (G : Type*) [Magma G] (h162 : Equation162 G) : Equation153 G := by
  intro x y
  conv => enter [1]; rw [h162 x x y]

@[equational_result]
theorem Equation162_implies_Equation156 (G : Type*) [Magma G] (h162 : Equation162 G) : Equation156 G := by
  intro x y
  conv => enter [1]; rw [h162 x y x]

@[equational_result]
theorem Equation162_implies_Equation159 (G : Type*) [Magma G] (h162 : Equation162 G) : Equation159 G := by
  intro x y
  conv => enter [1]; rw [h162 x y y]

@[equational_result]
theorem Equation167_implies_Equation151 (G : Type*) [Magma G] (h167 : Equation167 G) : Equation151 G := by
  intro x
  conv => enter [1]; rw [h167 x x]

@[equational_result]
theorem Equation168_implies_Equation167 (G : Type*) [Magma G] (h168 : Equation168 G) : Equation167 G := by
  intro x y
  conv => enter [1]; rw [h168 x y y]

@[equational_result]
theorem Equation168_implies_Equation152 (G : Type*) [Magma G] (h168 : Equation168 G) : Equation152 G := by
  intro x y
  conv => enter [1]; rw [h168 x x y]

@[equational_result]
theorem Equation168_implies_Equation166 (G : Type*) [Magma G] (h168 : Equation168 G) : Equation166 G := by
  intro x y
  conv => enter [1]; rw [h168 x y x]

@[equational_result]
theorem Equation308_implies_Equation307 (G : Type*) [Magma G] (h308 : Equation308 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h308 x x]

@[equational_result]
theorem Equation364_implies_Equation359 (G : Type*) [Magma G] (h364 : Equation364 G) : Equation359 G := by
  intro x
  conv => enter [1]; rw [h364 x x]

@[equational_result]
theorem Equation309_implies_Equation307 (G : Type*) [Magma G] (h309 : Equation309 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h309 x x]

@[equational_result]
theorem Equation361_implies_Equation359 (G : Type*) [Magma G] (h361 : Equation361 G) : Equation359 G := by
  intro x
  conv => enter [1]; rw [h361 x x]

@[equational_result]
theorem Equation310_implies_Equation307 (G : Type*) [Magma G] (h310 : Equation310 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h310 x x]

@[equational_result]
theorem Equation367_implies_Equation359 (G : Type*) [Magma G] (h367 : Equation367 G) : Equation359 G := by
  intro x
  conv => enter [1]; rw [h367 x x]

@[equational_result]
theorem Equation311_implies_Equation310 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation310 G := by
  intro x y
  conv => enter [1]; rw [h311 x y y]

@[equational_result]
theorem Equation311_implies_Equation309 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation309 G := by
  intro x y
  conv => enter [1]; rw [h311 x y x]

@[equational_result]
theorem Equation311_implies_Equation308 (G : Type*) [Magma G] (h311 : Equation311 G) : Equation308 G := by
  intro x y
  conv => enter [1]; rw [h311 x x y]

@[equational_result]
theorem Equation370_implies_Equation367 (G : Type*) [Magma G] (h370 : Equation370 G) : Equation367 G := by
  intro x y
  conv => enter [1]; rw [h370 x y y]

@[equational_result]
theorem Equation370_implies_Equation361 (G : Type*) [Magma G] (h370 : Equation370 G) : Equation361 G := by
  intro x y
  conv => enter [1]; rw [h370 x x y]

@[equational_result]
theorem Equation370_implies_Equation364 (G : Type*) [Magma G] (h370 : Equation370 G) : Equation364 G := by
  intro x y
  conv => enter [1]; rw [h370 x y x]

@[equational_result]
theorem Equation312_implies_Equation307 (G : Type*) [Magma G] (h312 : Equation312 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h312 x x]

@[equational_result]
theorem Equation360_implies_Equation359 (G : Type*) [Magma G] (h360 : Equation360 G) : Equation359 G := by
  intro x
  conv => enter [1]; rw [h360 x x]

@[equational_result]
theorem Equation313_implies_Equation307 (G : Type*) [Magma G] (h313 : Equation313 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h313 x x]

@[equational_result]
theorem Equation365_implies_Equation359 (G : Type*) [Magma G] (h365 : Equation365 G) : Equation359 G := by
  intro x
  conv => enter [1]; rw [h365 x x]

@[equational_result]
theorem Equation314_implies_Equation318 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation318 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ sK0 X0 sK2 : G, (sK0 ◇ sK0) = (X0 ◇ (sK2 ◇ sK0)) := by
    intro sK0 X0 sK2
    conv => enter [1]; rw [l1 sK0 sK2]
    conv => enter [1]; rw [h314 sK2 X0 sK0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation314_implies_Equation317 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation317 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK2)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h314 sK1 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation314_implies_Equation311 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation311 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ sK0 X0 sK1 sK2 : G, (sK0 ◇ sK0) = (X0 ◇ (sK1 ◇ sK2)) := by
    intro sK0 X0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h314 sK1 X0 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x x y z]

@[equational_result]
theorem Equation314_implies_Equation319 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation319 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ sK0 X0 sK2 sK1 : G, (sK0 ◇ sK0) = (X0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 X0 sK2 sK1
    conv => enter [1]; rw [l1 sK0 sK2]
    conv => enter [1]; rw [h314 sK2 X0 sK1]
  intro x y z
  conv => enter [1]; rw [l2 x y z y]

@[equational_result]
theorem Equation314_implies_Equation313 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation313 G := by
  intro x y
  conv => enter [1]; rw [h314 x y y]

@[equational_result]
theorem Equation314_implies_Equation315 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation315 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK1 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h314 sK1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation314_implies_Equation316 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation316 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h314 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h314 sK1 X0 sK1]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l2 X0 X0 sK1]
    conv => enter [1]; rw [← h314 sK1 X0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]
  conv => enter [1]; rw [h314 y y y]

@[equational_result]
theorem Equation314_implies_Equation312 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation312 G := by
  intro x y
  conv => enter [1]; rw [h314 x y x]

@[equational_result]
theorem Equation314_implies_Equation40 (G : Type*) [Magma G] (h314 : Equation314 G) : Equation40 G := by
  have l0 : ∀ X0 X1 sK0 : G, (X0 ◇ X0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro X0 X1 sK0
    conv => enter [1]; rw [h314 X0 X1 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h314 sK0 X0 sK0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 X0 sK0]
    conv => enter [1]; rw [← h314 sK0 X0 sK0]
  have l2 : ∀ X0 X1 sK1 : G, (X0 ◇ X0) = (X1 ◇ (sK1 ◇ sK1)) := by
    intro X0 X1 sK1
    conv => enter [1]; rw [h314 X0 X1 (sK1 ◇ sK1)]
    conv => enter [1, 2]; rw [← h314 sK1 X0 sK1]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l2 X0 X0 sK1]
    conv => enter [1]; rw [← h314 sK1 X0 sK1]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation366_implies_Equation363 (G : Type*) [Magma G] (h366 : Equation366 G) : Equation363 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h366 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [← h366 sK0 sK0 X0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 sK0 X0]
    conv => enter [1]; rw [← h366 sK0 sK0 X0]
  have l2 : ∀ sK0 sK1 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h366 sK1 sK0 X0]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation366_implies_Equation372 (G : Type*) [Magma G] (h366 : Equation366 G) : Equation372 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h366 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [← h366 sK0 sK0 X0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 sK0 X0]
    conv => enter [1]; rw [← h366 sK0 sK0 X0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK2) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK2]
    conv => enter [1]; rw [h366 sK2 sK1 sK2]
  intro x y z
  conv => enter [1]; rw [l2 x y z]

@[equational_result]
theorem Equation366_implies_Equation370 (G : Type*) [Magma G] (h366 : Equation366 G) : Equation370 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h366 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [← h366 sK0 sK0 X0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 sK0 X0]
    conv => enter [1]; rw [← h366 sK0 sK0 X0]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK2) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l1 sK0 sK2]
    conv => enter [1]; rw [h366 sK2 sK1 X0]
  intro x y z
  conv => enter [1]; rw [l2 x y z x]

@[equational_result]
theorem Equation366_implies_Equation371 (G : Type*) [Magma G] (h366 : Equation366 G) : Equation371 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h366 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [← h366 sK0 sK0 X0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 sK0 X0]
    conv => enter [1]; rw [← h366 sK0 sK0 X0]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK2) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l1 sK0 sK2]
    conv => enter [1]; rw [h366 sK2 sK1 X0]
  intro x y z
  conv => enter [1]; rw [l2 x y z y]

@[equational_result]
theorem Equation366_implies_Equation365 (G : Type*) [Magma G] (h366 : Equation366 G) : Equation365 G := by
  intro x y
  conv => enter [1]; rw [h366 x y y]

@[equational_result]
theorem Equation366_implies_Equation362 (G : Type*) [Magma G] (h366 : Equation366 G) : Equation362 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h366 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [← h366 sK0 sK0 X0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 sK0 X0]
    conv => enter [1]; rw [← h366 sK0 sK0 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1]; rw [h366 sK1 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation366_implies_Equation368 (G : Type*) [Magma G] (h366 : Equation366 G) : Equation368 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h366 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [← h366 sK0 sK0 X0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 sK0 X0]
    conv => enter [1]; rw [← h366 sK0 sK0 X0]
  have l2 : ∀ X0 sK1 X1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ X1) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [h366 X0 (sK1 ◇ sK1) X1]
    conv => enter [1, 1]; rw [← h366 sK1 sK1 X0]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l2 X0 sK1 X0]
    conv => enter [1]; rw [← h366 sK1 sK1 X0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]
  conv => enter [1]; rw [h366 y y y]

@[equational_result]
theorem Equation366_implies_Equation360 (G : Type*) [Magma G] (h366 : Equation366 G) : Equation360 G := by
  intro x y
  conv => enter [1]; rw [h366 x x y]

@[equational_result]
theorem Equation366_implies_Equation40 (G : Type*) [Magma G] (h366 : Equation366 G) : Equation40 G := by
  have l0 : ∀ X0 sK0 X1 : G, (X0 ◇ X0) = ((sK0 ◇ sK0) ◇ X1) := by
    intro X0 sK0 X1
    conv => enter [1]; rw [h366 X0 (sK0 ◇ sK0) X1]
    conv => enter [1, 1]; rw [← h366 sK0 sK0 X0]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [l0 X0 sK0 X0]
    conv => enter [1]; rw [← h366 sK0 sK0 X0]
  have l2 : ∀ X0 sK1 X1 : G, (X0 ◇ X0) = ((sK1 ◇ sK1) ◇ X1) := by
    intro X0 sK1 X1
    conv => enter [1]; rw [h366 X0 (sK1 ◇ sK1) X1]
    conv => enter [1, 1]; rw [← h366 sK1 sK1 X0]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l2 X0 sK1 X0]
    conv => enter [1]; rw [← h366 sK1 sK1 X0]
  have l4 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK1) := by
    intro sK0 sK1
    conv => enter [1]; rw [l3 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l4 x y]

@[equational_result]
theorem Equation315_implies_Equation307 (G : Type*) [Magma G] (h315 : Equation315 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h315 x x]

@[equational_result]
theorem Equation362_implies_Equation359 (G : Type*) [Magma G] (h362 : Equation362 G) : Equation359 G := by
  intro x
  conv => enter [1]; rw [h362 x x]

@[equational_result]
theorem Equation316_implies_Equation312 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation312 G := by
  have l0 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [h316 X0 sK0]
    conv => enter [1]; rw [← h316 sK0 sK0]
  have l1 : ∀ X1 sK0 : G, (X1 ◇ (X1 ◇ X1)) = (sK0 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [← h316 X1 X1]
    conv => enter [1]; rw [l0 X1 sK0]
  have l2 : ∀ sK0 X1 : G, (sK0 ◇ sK0) = (X1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X1
    conv => enter [1]; rw [← l1 X1 sK0]
    conv => enter [1, 2]; rw [l0 X1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation316_implies_Equation310 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation310 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 sK1 X0]
  have l1 : ∀ sK1 sK0 : G, (sK1 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK1 sK0
    conv => enter [1]; rw [h316 sK1 sK0]
    conv => enter [1, 2]; rw [l0 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1]
    conv => enter [1]; rw [l1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation316_implies_Equation40 (G : Type*) [Magma G] (h316 : Equation316 G) : Equation40 G := by
  have l0 : ∀ X0 sK1 : G, (X0 ◇ X0) = (sK1 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [h316 X0 X0]
    conv => enter [1]; rw [← h316 sK1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation368_implies_Equation360 (G : Type*) [Magma G] (h368 : Equation368 G) : Equation360 G := by
  have l0 : ∀ X1 sK0 : G, ((X1 ◇ X1) ◇ X1) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [← h368 X1 X1]
    conv => enter [1]; rw [h368 X1 sK0]
  have l1 : ∀ X1 sK0 : G, ((X1 ◇ X1) ◇ X1) = (sK0 ◇ sK0) := by
    intro X1 sK0
    conv => enter [1]; rw [l0 X1 sK0]
    conv => enter [1]; rw [← h368 sK0 sK0]
  have l2 : ∀ X0 sK0 : G, (X0 ◇ X0) = (sK0 ◇ sK0) := by
    intro X0 sK0
    conv => enter [1]; rw [h368 X0 sK0]
    conv => enter [1]; rw [← h368 sK0 sK0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l1 X0 sK0]
    conv => enter [1, 1]; rw [l2 X0 sK0]
  intro x y
  conv => enter [1]; rw [l3 x y]

@[equational_result]
theorem Equation368_implies_Equation367 (G : Type*) [Magma G] (h368 : Equation368 G) : Equation367 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h368 X0 X0]
    conv => enter [1]; rw [← h368 X1 X0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h368 sK0 sK0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = ((sK1 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0]
    conv => enter [1, 1]; rw [l0 sK0 sK1]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation368_implies_Equation40 (G : Type*) [Magma G] (h368 : Equation368 G) : Equation40 G := by
  have l0 : ∀ X0 X1 : G, (X0 ◇ X0) = (X1 ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h368 X0 X0]
    conv => enter [1]; rw [← h368 X1 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation317_implies_Equation315 (G : Type*) [Magma G] (h317 : Equation317 G) : Equation315 G := by
  intro x y
  conv => enter [1]; rw [h317 x y x]

@[equational_result]
theorem Equation317_implies_Equation316 (G : Type*) [Magma G] (h317 : Equation317 G) : Equation316 G := by
  intro x y
  conv => enter [1]; rw [h317 x y y]

@[equational_result]
theorem Equation317_implies_Equation308 (G : Type*) [Magma G] (h317 : Equation317 G) : Equation308 G := by
  intro x y
  conv => enter [1]; rw [h317 x x y]

@[equational_result]
theorem Equation372_implies_Equation362 (G : Type*) [Magma G] (h372 : Equation372 G) : Equation362 G := by
  intro x y
  conv => enter [1]; rw [h372 x x y]

@[equational_result]
theorem Equation372_implies_Equation368 (G : Type*) [Magma G] (h372 : Equation372 G) : Equation368 G := by
  intro x y
  conv => enter [1]; rw [h372 x y y]

@[equational_result]
theorem Equation372_implies_Equation364 (G : Type*) [Magma G] (h372 : Equation372 G) : Equation364 G := by
  intro x y
  conv => enter [1]; rw [h372 x y x]

@[equational_result]
theorem Equation318_implies_Equation315 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation315 G := by
  intro x y
  conv => enter [1]; rw [h318 x y y]

@[equational_result]
theorem Equation318_implies_Equation312 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation312 G := by
  intro x y
  conv => enter [1]; rw [h318 x y x]

@[equational_result]
theorem Equation318_implies_Equation309 (G : Type*) [Magma G] (h318 : Equation318 G) : Equation309 G := by
  intro x y
  conv => enter [1]; rw [h318 x x y]

@[equational_result]
theorem Equation363_implies_Equation362 (G : Type*) [Magma G] (h363 : Equation363 G) : Equation362 G := by
  intro x y
  conv => enter [1]; rw [h363 x y y]

@[equational_result]
theorem Equation363_implies_Equation360 (G : Type*) [Magma G] (h363 : Equation363 G) : Equation360 G := by
  intro x y
  conv => enter [1]; rw [h363 x x y]

@[equational_result]
theorem Equation363_implies_Equation361 (G : Type*) [Magma G] (h363 : Equation363 G) : Equation361 G := by
  intro x y
  conv => enter [1]; rw [h363 x y x]

@[equational_result]
theorem Equation319_implies_Equation313 (G : Type*) [Magma G] (h319 : Equation319 G) : Equation313 G := by
  intro x y
  conv => enter [1]; rw [h319 x y x]

@[equational_result]
theorem Equation319_implies_Equation316 (G : Type*) [Magma G] (h319 : Equation319 G) : Equation316 G := by
  intro x y
  conv => enter [1]; rw [h319 x y y]

@[equational_result]
theorem Equation319_implies_Equation309 (G : Type*) [Magma G] (h319 : Equation319 G) : Equation309 G := by
  intro x y
  conv => enter [1]; rw [h319 x x y]

@[equational_result]
theorem Equation371_implies_Equation365 (G : Type*) [Magma G] (h371 : Equation371 G) : Equation365 G := by
  intro x y
  conv => enter [1]; rw [h371 x y x]

@[equational_result]
theorem Equation371_implies_Equation368 (G : Type*) [Magma G] (h371 : Equation371 G) : Equation368 G := by
  intro x y
  conv => enter [1]; rw [h371 x y y]

@[equational_result]
theorem Equation371_implies_Equation361 (G : Type*) [Magma G] (h371 : Equation371 G) : Equation361 G := by
  intro x y
  conv => enter [1]; rw [h371 x x y]

@[equational_result]
theorem Equation323_implies_Equation307 (G : Type*) [Magma G] (h323 : Equation323 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h323 x x]

@[equational_result]
theorem Equation378_implies_Equation359 (G : Type*) [Magma G] (h378 : Equation378 G) : Equation359 G := by
  intro x
  conv => enter [1]; rw [h378 x x]

@[equational_result]
theorem Equation325_implies_Equation307 (G : Type*) [Magma G] (h325 : Equation325 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h325 x x]

@[equational_result]
theorem Equation385_implies_Equation359 (G : Type*) [Magma G] (h385 : Equation385 G) : Equation359 G := by
  intro x
  conv => enter [1]; rw [h385 x x]

@[equational_result]
theorem Equation326_implies_Equation307 (G : Type*) [Magma G] (h326 : Equation326 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h326 x x]

@[equational_result]
theorem Equation375_implies_Equation359 (G : Type*) [Magma G] (h375 : Equation375 G) : Equation359 G := by
  intro x
  conv => enter [1]; rw [h375 x x]

@[equational_result]
theorem Equation327_implies_Equation325 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation325 G := by
  intro x y
  conv => enter [1]; rw [h327 x y x]

@[equational_result]
theorem Equation327_implies_Equation308 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation308 G := by
  intro x y
  conv => enter [1]; rw [h327 x x y]

@[equational_result]
theorem Equation327_implies_Equation326 (G : Type*) [Magma G] (h327 : Equation327 G) : Equation326 G := by
  intro x y
  conv => enter [1]; rw [h327 x y y]

@[equational_result]
theorem Equation395_implies_Equation385 (G : Type*) [Magma G] (h395 : Equation395 G) : Equation385 G := by
  intro x y
  conv => enter [1]; rw [h395 x y y]

@[equational_result]
theorem Equation395_implies_Equation364 (G : Type*) [Magma G] (h395 : Equation395 G) : Equation364 G := by
  intro x y
  conv => enter [1]; rw [h395 x x y]

@[equational_result]
theorem Equation395_implies_Equation375 (G : Type*) [Magma G] (h395 : Equation395 G) : Equation375 G := by
  intro x y
  conv => enter [1]; rw [h395 x y x]

@[equational_result]
theorem Equation329_implies_Equation309 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation309 G := by
  intro x y
  conv => enter [1]; rw [h329 x x y]

@[equational_result]
theorem Equation329_implies_Equation323 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation323 G := by
  intro x y
  conv => enter [1]; rw [h329 x y x]

@[equational_result]
theorem Equation329_implies_Equation326 (G : Type*) [Magma G] (h329 : Equation329 G) : Equation326 G := by
  intro x y
  conv => enter [1]; rw [h329 x y y]

@[equational_result]
theorem Equation381_implies_Equation361 (G : Type*) [Magma G] (h381 : Equation381 G) : Equation361 G := by
  intro x y
  conv => enter [1]; rw [h381 x x y]

@[equational_result]
theorem Equation381_implies_Equation378 (G : Type*) [Magma G] (h381 : Equation381 G) : Equation378 G := by
  intro x y
  conv => enter [1]; rw [h381 x y y]

@[equational_result]
theorem Equation381_implies_Equation375 (G : Type*) [Magma G] (h381 : Equation381 G) : Equation375 G := by
  intro x y
  conv => enter [1]; rw [h381 x y x]

@[equational_result]
theorem Equation332_implies_Equation387 (G : Type*) [Magma G] (h332 : Equation332 G) : Equation387 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h332 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← h332 sK1 (sK1 ◇ sK1)]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro X0 sK1
    conv => enter [1, 2]; rw [h332 sK1 sK1]
    conv => enter [1]; rw [← l0 sK1 X0]
  have l2 : ∀ sK1 X0 : G, (sK1 ◇ X0) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h332 sK1 X0]
    conv => enter [1]; rw [l1 X0 sK1]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [h332 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l2 sK1 (X0 ◇ X0)]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l3 X0 sK1]
    conv => enter [1]; rw [← h332 X0 sK1]
  have l5 : ∀ sK1 X0 : G, (sK1 ◇ X0) = (X0 ◇ sK1) := by
    intro sK1 X0
    conv => enter [1]; rw [h332 sK1 X0]
    conv => enter [1]; rw [l4 X0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK1 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [l2 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation332_implies_Equation43 (G : Type*) [Magma G] (h332 : Equation332 G) : Equation43 G := by
  have l0 : ∀ X0 X1 : G, ((X0 ◇ X0) ◇ X1) = (X1 ◇ (X0 ◇ (X0 ◇ X0))) := by
    intro X0 X1
    conv => enter [1]; rw [h332 (X0 ◇ X0) X1]
    conv => enter [1, 2]; rw [← h332 X0 (X0 ◇ X0)]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1, 2]; rw [h332 X0 X0]
    conv => enter [1]; rw [← l0 X0 X1]
  have l2 : ∀ X0 X1 : G, (X0 ◇ X1) = ((X0 ◇ X0) ◇ X1) := by
    intro X0 X1
    conv => enter [1]; rw [h332 X0 X1]
    conv => enter [1]; rw [l1 X1 X0]
  have l3 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X0 ◇ (X1 ◇ X1)) := by
    intro X1 X0
    conv => enter [1]; rw [h332 X1 (X0 ◇ X0)]
    conv => enter [1]; rw [← l2 X0 (X1 ◇ X1)]
  have l4 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l3 X1 X0]
    conv => enter [1]; rw [← h332 X1 X0]
  have l5 : ∀ X0 X1 : G, (X0 ◇ X1) = (X1 ◇ X0) := by
    intro X0 X1
    conv => enter [1]; rw [h332 X0 X1]
    conv => enter [1]; rw [l4 X1 X0]
  intro x y
  conv => enter [1]; rw [l5 x y]

@[equational_result]
theorem Equation332_implies_Equation326 (G : Type*) [Magma G] (h332 : Equation332 G) : Equation326 G := by
  have l0 : ∀ sK1 X0 : G, ((sK1 ◇ sK1) ◇ X0) = (X0 ◇ (sK1 ◇ (sK1 ◇ sK1))) := by
    intro sK1 X0
    conv => enter [1]; rw [h332 (sK1 ◇ sK1) X0]
    conv => enter [1, 2]; rw [← h332 sK1 (sK1 ◇ sK1)]
  have l1 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = ((sK1 ◇ sK1) ◇ X0) := by
    intro X0 sK1
    conv => enter [1, 2]; rw [h332 sK1 sK1]
    conv => enter [1]; rw [← l0 sK1 X0]
  have l2 : ∀ sK1 X0 : G, (sK1 ◇ X0) = ((sK1 ◇ sK1) ◇ X0) := by
    intro sK1 X0
    conv => enter [1]; rw [h332 sK1 X0]
    conv => enter [1]; rw [l1 X0 sK1]
  have l3 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (sK1 ◇ (X0 ◇ X0)) := by
    intro X0 sK1
    conv => enter [1]; rw [h332 X0 (sK1 ◇ sK1)]
    conv => enter [1]; rw [← l2 sK1 (X0 ◇ X0)]
  have l4 : ∀ X0 sK1 : G, (X0 ◇ (sK1 ◇ sK1)) = (X0 ◇ sK1) := by
    intro X0 sK1
    conv => enter [1]; rw [l3 X0 sK1]
    conv => enter [1]; rw [← h332 X0 sK1]
  have l5 : ∀ sK1 X0 : G, (sK1 ◇ X0) = (X0 ◇ sK1) := by
    intro sK1 X0
    conv => enter [1]; rw [h332 sK1 X0]
    conv => enter [1]; rw [l4 X0 sK1]
  have l6 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l5 sK0 sK1]
    conv => enter [1]; rw [h332 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l6 x y]

@[equational_result]
theorem Equation332_implies_Equation375 (G : Type*) [Magma G] (h332 : Equation332 G) : Equation375 G := by
  have l0 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ (sK0 ◇ sK0))) := by
    intro sK0 X0
    conv => enter [1]; rw [h332 (sK0 ◇ sK0) X0]
    conv => enter [1, 2]; rw [← h332 sK0 (sK0 ◇ sK0)]
  have l1 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1, 2]; rw [h332 sK0 sK0]
    conv => enter [1]; rw [← l0 sK0 X0]
  have l2 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h332 sK0 X0]
    conv => enter [1]; rw [l1 X0 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation387_implies_Equation332 (G : Type*) [Magma G] (h387 : Equation387 G) : Equation332 G := by
  have l0 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (((X0 ◇ X0) ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [h387 X1 (X0 ◇ X0)]
    conv => enter [1, 1]; rw [← h387 (X0 ◇ X0) X0]
  have l1 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = ((X0 ◇ X0) ◇ X1) := by
    intro X1 X0
    conv => enter [1]; rw [l0 X1 X0]
    conv => enter [1, 1]; rw [← h387 X0 X0]
  have l2 : ∀ X1 X0 : G, (X1 ◇ (X0 ◇ X0)) = (X1 ◇ X0) := by
    intro X1 X0
    conv => enter [1]; rw [l1 X1 X0]
    conv => enter [1]; rw [← h387 X1 X0]
  have l3 : ∀ sK0 X0 : G, (sK0 ◇ X0) = ((sK0 ◇ sK0) ◇ (X0 ◇ X0)) := by
    intro sK0 X0
    conv => enter [1]; rw [h387 sK0 X0]
    conv => enter [1]; rw [h387 (X0 ◇ X0) sK0]
  have l4 : ∀ X0 sK0 : G, (X0 ◇ (sK0 ◇ sK0)) = (((sK0 ◇ sK0) ◇ sK0) ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [h387 X0 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← h387 (sK0 ◇ sK0) sK0]
  have l5 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK0 X0
    conv => enter [1, 1]; rw [h387 sK0 sK0]
    conv => enter [1]; rw [← l4 X0 sK0]
  have l6 : ∀ sK0 X0 : G, ((sK0 ◇ sK0) ◇ X0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [← l2 (sK0 ◇ sK0) X0]
    conv => enter [1]; rw [← l3 sK0 X0]
  have l7 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X0 sK0
    conv => enter [1]; rw [h387 X0 sK0]
    conv => enter [1]; rw [l5 sK0 X0]
  have l8 : ∀ X0 sK0 : G, (X0 ◇ sK0) = (sK0 ◇ X0) := by
    intro X0 sK0
    conv => enter [1]; rw [h387 X0 sK0]
    conv => enter [1]; rw [l6 sK0 X0]
  have l9 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK0)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l8 sK0 sK1]
    conv => enter [1]; rw [l7 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l9 x y]

@[equational_result]
theorem Equation333_implies_Equation307 (G : Type*) [Magma G] (h333 : Equation333 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h333 x x]

@[equational_result]
theorem Equation377_implies_Equation359 (G : Type*) [Magma G] (h377 : Equation377 G) : Equation359 G := by
  intro x
  conv => enter [1]; rw [h377 x x]

@[equational_result]
theorem Equation335_implies_Equation307 (G : Type*) [Magma G] (h335 : Equation335 G) : Equation307 G := by
  intro x
  conv => enter [1]; rw [h335 x x]

@[equational_result]
theorem Equation335_implies_Equation359 (G : Type*) [Magma G] (h335 : Equation335 G) : Equation359 G := by
  have l0 : ∀ sK0 : G, ((sK0 ◇ sK0) ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h335 (sK0 ◇ sK0) sK0]
    conv => enter [1, 2]; rw [← h335 sK0 sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h335 sK0 sK0]
    conv => enter [1]; rw [← l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

@[equational_result]
theorem Equation384_implies_Equation307 (G : Type*) [Magma G] (h384 : Equation384 G) : Equation307 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ (sK0 ◇ sK0)) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h384 sK0 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← h384 sK0 sK0]
  have l1 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h384 sK0 sK0]
    conv => enter [1]; rw [← l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

@[equational_result]
theorem Equation384_implies_Equation359 (G : Type*) [Magma G] (h384 : Equation384 G) : Equation359 G := by
  intro x
  conv => enter [1]; rw [h384 x x]

@[equational_result]
theorem Equation336_implies_Equation39 (G : Type*) [Magma G] (h336 : Equation336 G) : Equation39 G := by
  have l0 : ∀ sK0 sK1 : G, (sK0 ◇ sK0) = (sK1 ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [h336 sK0 sK0]
    conv => enter [1]; rw [← h336 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation336_implies_Equation318 (G : Type*) [Magma G] (h336 : Equation336 G) : Equation318 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h336 X0 X1]
    conv => enter [1]; rw [← h336 X2 X1]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (X0 ◇ sK0) := by
    intro sK0 X0
    conv => enter [1]; rw [h336 sK0 sK0]
    conv => enter [1]; rw [← h336 X0 sK0]
  have l2 : ∀ sK0 sK2 : G, (sK0 ◇ sK0) = (sK2 ◇ sK0) := by
    intro sK0 sK2
    conv => enter [1]; rw [h336 sK0 sK0]
    conv => enter [1]; rw [← h336 sK2 sK0]
  have l3 : ∀ X1 sK0 X0 : G, (X1 ◇ sK0) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro X1 sK0 X0
    conv => enter [1]; rw [h336 X1 sK0]
    conv => enter [1]; rw [l0 sK0 (sK0 ◇ sK0) X0]
  have l4 : ∀ sK1 sK2 sK0 X0 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X0 ◇ (sK0 ◇ sK0)) := by
    intro sK1 sK2 sK0 X0
    conv => enter [1, 2]; rw [← l2 sK0 sK2]
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ sK0) X0]
  have l5 : ∀ sK1 sK2 sK0 X1 : G, (sK1 ◇ (sK2 ◇ sK0)) = (X1 ◇ sK0) := by
    intro sK1 sK2 sK0 X1
    conv => enter [1]; rw [l4 sK1 sK2 sK0 sK1]
    conv => enter [1]; rw [← l3 X1 sK0 sK1]
  have l6 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = (sK1 ◇ (sK2 ◇ sK0)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l5 sK1 sK2 sK0 sK0]
  intro x y z
  conv => enter [1]; rw [l6 x y z]

@[equational_result]
theorem Equation336_implies_Equation343 (G : Type*) [Magma G] (h336 : Equation336 G) : Equation343 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h336 X0 X1]
    conv => enter [1]; rw [← h336 X2 X1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h336 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK1 sK0]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK2 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1]
    conv => enter [1]; rw [l0 sK1 (sK0 ◇ sK1) sK2]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation336_implies_Equation329 (G : Type*) [Magma G] (h336 : Equation336 G) : Equation329 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h336 X0 X1]
    conv => enter [1]; rw [← h336 X2 X1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h336 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK1 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = (sK0 ◇ (sK2 ◇ sK1)) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 sK1 (sK2 ◇ sK1) sK0]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation336_implies_Equation333 (G : Type*) [Magma G] (h336 : Equation336 G) : Equation333 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X2 ◇ X1) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h336 X0 X1]
    conv => enter [1]; rw [← h336 X2 X1]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK1 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [h336 sK0 sK1]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = (sK1 ◇ (sK0 ◇ sK1)) := by
    intro sK0 sK1
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 2]; rw [l0 sK1 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation374_implies_Equation38 (G : Type*) [Magma G] (h374 : Equation374 G) : Equation38 G := by
  have l0 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h374 sK0 sK0]
    conv => enter [1]; rw [← h374 sK0 X0]
  intro x y
  conv => enter [1]; rw [l0 x y]

@[equational_result]
theorem Equation374_implies_Equation363 (G : Type*) [Magma G] (h374 : Equation374 G) : Equation363 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h374 X0 X1]
    conv => enter [1]; rw [← h374 X0 X2]
  have l1 : ∀ sK0 X0 : G, (sK0 ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 X0
    conv => enter [1]; rw [h374 sK0 sK0]
    conv => enter [1]; rw [← h374 sK0 X0]
  have l2 : ∀ sK0 X1 X0 : G, (sK0 ◇ X1) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 X1 X0
    conv => enter [1]; rw [h374 sK0 X1]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0) sK0 X0]
  have l3 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ sK2) = ((sK0 ◇ sK0) ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1, 1]; rw [← l1 sK0 sK1]
    conv => enter [1]; rw [l0 (sK0 ◇ sK0) sK2 X0]
  have l4 : ∀ sK0 sK1 sK2 X1 : G, ((sK0 ◇ sK1) ◇ sK2) = (sK0 ◇ X1) := by
    intro sK0 sK1 sK2 X1
    conv => enter [1]; rw [l3 sK0 sK1 sK2 sK0]
    conv => enter [1]; rw [← l2 sK0 X1 sK0]
  have l5 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK1) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [← l4 sK0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l5 x y z]

@[equational_result]
theorem Equation374_implies_Equation379 (G : Type*) [Magma G] (h374 : Equation374 G) : Equation379 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h374 X0 X1]
    conv => enter [1]; rw [← h374 X0 X2]
  have l1 : ∀ sK0 X0 sK1 : G, (sK0 ◇ X0) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 X0 sK1
    conv => enter [1]; rw [h374 sK0 X0]
    conv => enter [1, 1]; rw [l0 sK0 sK0 sK1]
  have l2 : ∀ sK0 sK1 sK2 X0 : G, ((sK0 ◇ sK1) ◇ sK2) = (sK0 ◇ X0) := by
    intro sK0 sK1 sK2 X0
    conv => enter [1]; rw [l0 (sK0 ◇ sK1) sK2 sK0]
    conv => enter [1]; rw [← l1 sK0 X0 sK1]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK2) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [← l2 sK0 sK1 sK2 sK0]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation374_implies_Equation381 (G : Type*) [Magma G] (h374 : Equation374 G) : Equation381 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h374 X0 X1]
    conv => enter [1]; rw [← h374 X0 X2]
  have l1 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [h374 sK0 sK0]
  have l2 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK2) ◇ sK0) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l1 sK0 sK1]
    conv => enter [1, 1]; rw [l0 sK0 sK0 sK2]
  have l3 : ∀ sK0 sK1 sK2 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK2) ◇ sK1) := by
    intro sK0 sK1 sK2
    conv => enter [1]; rw [l2 sK0 sK1 sK2]
    conv => enter [1]; rw [l0 (sK0 ◇ sK2) sK0 sK1]
  intro x y z
  conv => enter [1]; rw [l3 x y z]

@[equational_result]
theorem Equation374_implies_Equation377 (G : Type*) [Magma G] (h374 : Equation374 G) : Equation377 G := by
  have l0 : ∀ X0 X1 X2 : G, (X0 ◇ X1) = (X0 ◇ X2) := by
    intro X0 X1 X2
    conv => enter [1]; rw [h374 X0 X1]
    conv => enter [1]; rw [← h374 X0 X2]
  have l1 : ∀ sK0 sK1 X0 : G, ((sK0 ◇ sK1) ◇ sK0) = (sK0 ◇ X0) := by
    intro sK0 sK1 X0
    conv => enter [1, 1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [← h374 sK0 X0]
  have l2 : ∀ sK0 sK1 : G, (sK0 ◇ sK1) = ((sK0 ◇ sK1) ◇ sK0) := by
    intro sK0 sK1
    conv => enter [1]; rw [l0 sK0 sK1 sK0]
    conv => enter [1]; rw [← l1 sK0 sK1 sK0]
  intro x y
  conv => enter [1]; rw [l2 x y]

@[equational_result]
theorem Equation343_implies_Equation333 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation333 G := by
  intro x y
  conv => enter [1]; rw [h343 x y y]

@[equational_result]
theorem Equation343_implies_Equation312 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation312 G := by
  intro x y
  conv => enter [1]; rw [h343 x x y]

@[equational_result]
theorem Equation343_implies_Equation323 (G : Type*) [Magma G] (h343 : Equation343 G) : Equation323 G := by
  intro x y
  conv => enter [1]; rw [h343 x y x]

@[equational_result]
theorem Equation379_implies_Equation377 (G : Type*) [Magma G] (h379 : Equation379 G) : Equation377 G := by
  intro x y
  conv => enter [1]; rw [h379 x y x]

@[equational_result]
theorem Equation379_implies_Equation360 (G : Type*) [Magma G] (h379 : Equation379 G) : Equation360 G := by
  intro x y
  conv => enter [1]; rw [h379 x x y]

@[equational_result]
theorem Equation379_implies_Equation378 (G : Type*) [Magma G] (h379 : Equation379 G) : Equation378 G := by
  intro x y
  conv => enter [1]; rw [h379 x y y]

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

theorem Equation8_47_implies_Equation3 (G : Type*) [Magma G] (h8 : Equation8 G) (h47 : Equation47 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h8 X0]
    conv => enter [1]; rw [← h47 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation23_255_implies_Equation3 (G : Type*) [Magma G] (h23 : Equation23 G) (h255 : Equation255 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h23 X0]
    conv => enter [1]; rw [← h255 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation8_151_implies_Equation99 (G : Type*) [Magma G] (h8 : Equation8 G) (h151 : Equation151 G) : Equation99 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h8 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h151 sK0]
  have l1 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h8 sK0]
    conv => enter [1, 2]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation8_151_implies_Equation359 (G : Type*) [Magma G] (h8 : Equation8 G) (h151 : Equation151 G) : Equation359 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = ((sK0 ◇ sK0) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h8 (sK0 ◇ sK0)]
    conv => enter [1, 2]; rw [← h151 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation23_151_implies_Equation203 (G : Type*) [Magma G] (h23 : Equation23 G) (h151 : Equation151 G) : Equation203 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h23 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← h151 sK0]
  have l1 : ∀ sK0 : G, sK0 = ((sK0 ◇ (sK0 ◇ sK0)) ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h23 sK0]
    conv => enter [1, 1]; rw [l0 sK0]
  intro x
  conv => enter [1]; rw [l1 x]

theorem Equation23_151_implies_Equation307 (G : Type*) [Magma G] (h23 : Equation23 G) (h151 : Equation151 G) : Equation307 G := by
  have l0 : ∀ sK0 : G, (sK0 ◇ sK0) = (sK0 ◇ (sK0 ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h23 (sK0 ◇ sK0)]
    conv => enter [1, 1]; rw [← h151 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation8_203_implies_Equation3 (G : Type*) [Magma G] (h8 : Equation8 G) (h203 : Equation203 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 1]; rw [h8 X0]
    conv => enter [1]; rw [← h203 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation23_99_implies_Equation3 (G : Type*) [Magma G] (h23 : Equation23 G) (h99 : Equation99 G) : Equation3 G := by
  have l0 : ∀ X0 : G, (X0 ◇ X0) = X0 := by
    intro X0
    conv => enter [1, 2]; rw [h23 X0]
    conv => enter [1]; rw [← h99 X0]
  intro x
  conv => enter [1]; rw [← l0 x]

theorem Equation8_307_implies_Equation3 (G : Type*) [Magma G] (h8 : Equation8 G) (h307 : Equation307 G) : Equation3 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h8 sK0]
    conv => enter [1]; rw [← h307 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation23_359_implies_Equation3 (G : Type*) [Magma G] (h23 : Equation23 G) (h359 : Equation359 G) : Equation3 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ sK0) := by
    intro sK0
    conv => enter [1]; rw [h23 sK0]
    conv => enter [1]; rw [← h359 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

theorem Equation8_359_implies_Equation99 (G : Type*) [Magma G] (h8 : Equation8 G) (h359 : Equation359 G) : Equation99 G := by
  have l0 : ∀ sK0 : G, sK0 = (sK0 ◇ ((sK0 ◇ sK0) ◇ sK0)) := by
    intro sK0
    conv => enter [1]; rw [h8 sK0]
    conv => enter [1, 2]; rw [h359 sK0]
  intro x
  conv => enter [1]; rw [l0 x]

end Order3
