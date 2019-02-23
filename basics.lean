-- TODO Conjunto de proposições??
-- TODO arbitrary inductive type!!

-- Arquivo com as definições dos tipos básicos de iALC e de seu cálculo de sequentes.
-- Autor: Bernardo Alkmim
-- bpalkmim@gmail.com

namespace iALCbasics

open list

constant Nominal : Type
constant Role : Type
constant Formula : Prop
constant Concept : Formula
constant Assertion : Formula
constant Sequent : list Formula → Formula → Type
constant Proof {X : list Formula} {Y : Formula} : Sequent X Y → Type

-- ⊤
constant Top : Concept
notation ⊤ := Top
-- ⊥
constant Bot : Concept
notation ⊥ := Bot
-- xRy
constant Relation : Role → Nominal → Nominal → Assertion
-- x:C
constant ElemOf : Nominal → Concept → Assertion
-- ∀R.C
constant Univ : Role → Concept → Concept
-- ∃R.C
constant Exis : Role → Concept → Concept
-- C ⊑ D
constant Subj : Concept → Concept → Concept
notation c ⊑ d := Subj c d
-- C ⊓ D
constant Conj : Concept → Concept → Concept
notation c ⊓ d := Subj c d
-- C ⊔ D
constant Disj : Concept → Concept → Concept
notation c ⊔ d := Subj c d
-- ¬C
constant Neg : Concept → Concept
notation ¬c := Neg c

end iALCbasics