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

inductive Formula
| simple : Concept → Formula
| univ : Role → Concept → Formula
| exis : Role → Concept → Formula
| subj : Formula → Concept → Formula
| conj : Concept → Concept → Formula
| disj : Concept → Concept → Formula
| neg : Concept → Formula
| elemOf : Nominal → Formula → Formula -- Asserções também são fórmulas
| relation : Role → Nominal → Nominal → Formula

constant Sequent : list Formula → Formula → Prop
constant Proof : Prop → Type

end iALCbasics