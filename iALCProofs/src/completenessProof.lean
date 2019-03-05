-- Prova de completude de SCiALC, composta por derivações dos axiomas do
-- cálculo de Hilbert para iALC utilizando as regras de SCiALC.
-- Autor: Bernardo Alkmim
-- bpalkmim@gmail.com

import .basics
import .axiomsSC
import .rightRules
import .leftRules
import .promRules
import .structRules

namespace completenessSCiALC

open list
open iALCbasics
open axiomsSCiALC
open leftRulesSCiALC
open rightRulesSCiALC
open promRulesSCiALC
open structRulesSCiALC

-- Constantes
constants x y : Nominal
constants a b : Formula
constant r : Role

-- Variáveis úteis
--variable h1_1 : list.append nil nil = nil
variable h1_2 : map (add_univ r) [Formula.subj a b] = [add_univ r (Formula.subj a b)]

variable seq_concl_1 : Proof (Sequent (Formula.univ r (Formula.subj a b) :: nil) (Formula.subj (Formula.univ r a) (Formula.univ r b)))

-- variable seq_concl_2 : Proof (Sequent (() ()))

variable seq_concl_3 : Proof (Sequent nil (Formula.elemOf x (Formula.subj (Formula.exis r (Formula.disj a b)) (Formula.disj (Formula.exis r a) (Formula.exis r b)))))

variable seq_concl_4 : Proof (Sequent nil (Formula.elemOf x (Formula.subj (Formula.exis r (Formula.simple Bot)) (Formula.simple Bot))))


-- Axioma 1: ∀R.(a ⊑ b) ⇒ ∀R.a ⊑ ∀R.b
#print "\n\n"

#check subj_r (prom_forall r (perm_head (subj_l (axiom_id nil a) (axiom_id nil b))))

#print "\n\n"

theorem T1 : subj_r (prom_forall r (perm_head (subj_l (axiom_id nil a) (axiom_id nil b)))) = seq_concl_1 :=
by rw [h1_1, h1_2, add_univ, add_univ]
/-
calc
	Proof (Sequent (map (add_univ r) (Formula.subj a b :: list.append nil nil)) (Formula.subj (add_univ r a) (Formula.univ r b))) =
		Proof (Sequent (map (add_univ r) [Formula.subj a b]) (Formula.subj (add_univ r a) (Formula.univ r b))) : by rw h1_1
	... = Proof (Sequent [add_univ r (Formula.subj. a b)] (Formula.subj (add_univ r a) (Formula.univ r b))) : by rw h1_2
	... = Proof (Sequent [Formula.univ r (Formula.subj. a b)] (Formula.subj (add_univ r a) (Formula.univ r b))) : by rw add_univ
	... = seq_concl_1 : by rw add_univ
-/
#print "\n\n"

-- Axioma 3: x : ∃R.(α ⊔ β) ⇒ x : ∃R.α ⊔ ∃R.β
#print "Axioma 3"
#check subj_r_n x
	(exists_l
		(disj_l_n y
			(disj_r1_n (Formula.exis r b) x 
				(exists_r 
					(perm_head
						(axiom_id [Formula.elemOf y a] (Formula.relation r x y)))
					(axiom_id [Formula.relation r x y] (Formula.elemOf y a))))
			(disj_r2_n (Formula.exis r a) x 
				(exists_r 
					(perm_head
						(axiom_id [Formula.elemOf y b] (Formula.relation r x y)))
					(axiom_id [Formula.relation r x y] (Formula.elemOf y b))))))

#print "\n\n"

-- Axioma 4: ⇒ ∃R.⊥ ⊑ ⊥
#print "Axioma 4"
#check subj_r_n x
	(exists_l
		(axiom_efq (Formula.relation r x y :: nil) (Formula.elemOf x (Formula.simple Bot)) y))

#print "\n\n"

-- Axioma 5: ⇒ x : ((∃R.α ⊑ ∀R.β) ⊑ ∀R.(α ⊑ β))
#print "Axioma 5"
#check exists_r 
	(perm_head
		(axiom_id [Formula.elemOf y a] (Formula.relation r x y)))
	(axiom_id [Formula.relation r x y] (Formula.elemOf y a))

#print "\n\n"
#check forall_l
	(axiom_id [Formula.relation r x y, Formula.elemOf x (Formula.univ r b), Formula.elemOf y a] (Formula.elemOf y b))

end completenessSCiALC