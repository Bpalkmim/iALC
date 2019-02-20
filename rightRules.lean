-- Regras do lado direito do sequente de SCiALC.
-- Autor: Bernardo Alkmim
-- bpalkmim@gmail.com

namespace rightRulesSCiALC

open iALCbasics

constant conj_r {X : list Formula} {Y Z : Formula} :
	Proof (Sequent X Y) → Proof (Sequent X Z) → Proof (Sequent X (Conj X Z))

TODO completar

end rightRulesSCiALC