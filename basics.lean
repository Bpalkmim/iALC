-- Conjunto de proposições??
-- arbitrary inductive type!!

-- Arquivo para estudo do artigo das relações entre Jurisprudência Kelseniana
-- e Lógica Intuicionista (Haeusler, Rademaker, 2015)
-- Noções básicas de iALC.
-- Autor: Bernardo Alkmim
-- bpalkmim@gmail.com

namespace iALCbasics

open list

constant Nominal : Type
constant Concept : Prop
constant Sequent : list Concept → list Prop → Prop → Type
constant Proof {X : list Concept} {Z : list Prop} {Y : Concept} : Sequent X Z Y → Type

-- ⊤
constant Top : Concept
-- ⊥
constant Bot : Concept
-- xRy
constant Relation : Nominal → Nominal → Prop

-- x:C
constant ElementOf : Nominal → Concept → Prop
-- ∀R.C
constant Universal {X Y : Nominal} : Relation X Y → Concept → Concept
-- ∃R.C
constant Existential {X Y : Nominal} : Relation X Y → Concept → Concept
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