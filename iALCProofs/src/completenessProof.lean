-- Prova de completude de SCiALC, composta por derivações dos axiomas do
-- cálculo de Hilbert para iALC utilizando as regras de SCiALC.
-- Autor: Bernardo Alkmim
-- bpalkmim@gmail.com

import .basics
import .axiomsSC
import .rightRules
import .leftRules

namespace completenessSCiALC

open list
open iALCbasics
open axiomsSCiALC
open leftRulesSCiALC
open rightRulesSCiALC

-- Constantes
constants x y : Nominal
constant r : Role

-- Variáveis úteis
variable seq_concl : Proof (Sequent nil (Formula.elemOf x (Formula.subj (Formula.exis r Bot) Bot)))

-- TODO completar

-- Axioma 4: ∃R.⊥ ⊑ ⊥
#check axiom_efq (Formula.relation r x y :: nil) y (Formula.elemOf x (Formula.simple Bot))

#print "\n\n"

#check exists_l (
		axiom_efq (Formula.relation r x y :: nil) y (Formula.elemOf x (Formula.simple Bot))
	)

#print "\n\n"

#check subj_r_n (
	exists_l (
		axiom_efq (
			(Formula.relation r x y :: nil) y (Formula.elemOf x (Formula.simple Bot))
		)
	)
)

#print "\n\n"

#check seq_concl

end completenessSCiALC