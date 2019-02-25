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

-- Definições úteis para a definição de um sequente válido, utilizada na prova de correção
constant Interpretation : list Formula → Prop
constant Model : Interpretation → Nominal → list Formula → Prop

-- Função que mapeia a validade de um sequente a partir de uma lista de nominals
-- para a validade de um sequente a partir da conjunção das validades para cada
-- nominal
def model_list : Interpretation → list Nominal → list Formula → Prop
| I l nil 		:= ff
| I nil Δ 		:= tt
| I (x :: l) Δ 	:= (Model I x Δ) ∧ (model_list I l Δ) 

-- Função que busca por uma relação entre dois nominals numa lista de fórmulas
def rel_in_formula_list : Role → Nominal → Nominal → list Formula → Prop
| r x y nil 							:= ff
| r x y ((Formula.relation rel x y) :: l) := tt
| r x y (_ :: l) 						:= in_formula_list r x y l

-- Função que busca numa lista de fórmulas pelas relações entre
-- o nominal da esquerda e os da lista à direita
def prec_general : Role → Nominal → list Nominal → list Formula → Prop
| r x nil Δ 		:= ff
| r x (y :: l) Δ 	:= (rel_in_formula_list r x y Δ) ∧ prec_general r x l Δ

-- Função auxiliar para obter os nominals externos de uma lista de fórmulas
def nom_ext : list Formula → list Nominal
| nil 							:= nil
| ((Formula.elemOf y c) :: l) 	:= y :: (nom_ext l)
| (_ :: l) 			            := nom_ext l

-- Definição de sequente válido
def valid_seq {prec : Role} {Θ Γ : list Formula} {δ : Formula} :
	Proof (Sequent (Θ ++ Γ) δ) →  
	∀ I : Interpretation, ((∀ x : Nominal, Model I x Θ) →
		(∀ x : nom_ext (δ :: Γ),
			(prec_general prec x (nom_ext (δ :: Γ)) (δ :: Γ) →
				(model_list I (nom_ext (δ :: Γ)) Γ →
					model_list I (nom_ext (δ :: Γ)) (δ :: nil))
			)
		)
	)

end iALCbasics