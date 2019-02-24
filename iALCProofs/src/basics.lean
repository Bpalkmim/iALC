-- Arquivo com as definições dos tipos básicos de iALC e de seu cálculo de sequentes.
-- Autor: Bernardo Alkmim
-- bpalkmim@gmail.com

--import .list

namespace iALCbasics

open list

constant Concept : Type
constant Nominal : Type
constant Role : Type

constant Top : Concept
constant Bot : Concept

-- Fórmulas (tanto conceitos quanto asserções)
inductive Formula
| simple : Concept → Formula
| univ : Role → Formula → Formula
| exis : Role → Formula → Formula
| subj : Formula → Formula → Formula
| conj : Concept → Concept → Formula
| disj : Concept → Concept → Formula
| neg : Formula → Formula
| elemOf : Nominal → Formula → Formula -- Asserções também são fórmulas
| relation : Role → Nominal → Nominal → Formula

-- Funções para serem passadas ao map de listas para promoção
-- Devem manter asserções inalteradas
def add_nom (x : Nominal) : Formula → Formula
| (Formula.simple c) 		:= Formula.elemOf x (Formula.simple c)
| (Formula.univ r f) 		:= Formula.elemOf x (Formula.univ r f)
| (Formula.exis r f) 		:= Formula.elemOf x (Formula.exis r f)
| (Formula.subj c d) 		:= Formula.elemOf x (Formula.subj c d)
| (Formula.conj c d) 		:= Formula.elemOf x (Formula.conj c d)
| (Formula.disj c d) 		:= Formula.elemOf x (Formula.disj c d)
| (Formula.neg c) 			:= Formula.elemOf x (Formula.neg c)
| (Formula.elemOf y c) 		:= Formula.elemOf y c
| (Formula.relation rel y z):= Formula.relation rel y z

def add_univ (r : Role) : Formula → Formula
| (Formula.simple c) 		:= Formula.univ r (Formula.simple c)
| (Formula.univ rel f) 		:= Formula.univ r (Formula.univ rel f)
| (Formula.exis rel f) 		:= Formula.univ r (Formula.exis rel f)
| (Formula.subj c d) 		:= Formula.univ r (Formula.subj c d)
| (Formula.conj c d) 		:= Formula.univ r (Formula.conj c d)
| (Formula.disj c d) 		:= Formula.univ r (Formula.disj c d)
| (Formula.neg c) 			:= Formula.univ r (Formula.neg c)
| (Formula.elemOf y c) 		:= Formula.elemOf y c
| (Formula.relation rel y z):= Formula.relation rel y z

def add_exis (r : Role) : Formula → Formula
| (Formula.simple c) 		:= Formula.exis r (Formula.simple c)
| (Formula.univ rel f) 		:= Formula.exis r (Formula.univ rel f)
| (Formula.exis rel f) 		:= Formula.exis r (Formula.exis rel f)
| (Formula.subj c d) 		:= Formula.exis r (Formula.subj c d)
| (Formula.conj c d) 		:= Formula.exis r (Formula.conj c d)
| (Formula.disj c d) 		:= Formula.exis r (Formula.disj c d)
| (Formula.neg c) 			:= Formula.univ r (Formula.neg c)
| (Formula.elemOf y c) 		:= Formula.elemOf y c
| (Formula.relation rel y z):= Formula.relation rel y z

constant Sequent : list Formula → Formula → Prop
constant Proof : Prop → Type

end iALCbasics