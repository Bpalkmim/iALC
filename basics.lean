-- TODO Conjunto de proposições??
-- TODO arbitrary inductive type!!

-- Arquivo com as definições dos tipos básicos de iALC e de seu cálculo de sequentes.
-- Autor: Bernardo Alkmim
-- bpalkmim@gmail.com

namespace iALCbasics

open list

constant Nominal : Type
constant Formula : Prop
constant Concept : Formula
constant Assertion : Formula
constant Sequent : list Formula → Formula → Type
constant Proof {X : list Formula} {Y : Formula} : Sequent X Y → Type

-- ⊤
constant Top : Concept
-- ⊥
constant Bot : Concept
-- xRy
constant Role : Nominal → Nominal → Prop

-- x:C
constant ElemOf : Nominal → Concept → Prop
-- ∀R.C
constant Univ {X Y : Nominal} : Role X Y → Concept → Concept
-- ∃R.C
constant Exis {X Y : Nominal} : Role X Y → Concept → Concept
-- C ⊑ D
constant Sub : Concept → Concept → Concept
-- C ⊓ D
constant Conj : Concept → Concept → Concept
-- C ⊔ D
constant Disj : Concept → Concept → Concept
-- ¬C
constant Neg : Concept → Concept
notation ¬c := neg c

end iALCbasics