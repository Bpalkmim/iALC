-- Regras de promoção de SCiALC.
-- Autor: Bernardo Alkmim
-- bpalkmim@gmail.com

import .basics

namespace promRulesSCiALC

open iALCbasics

constant prom_n {Δ : list Formula} {X : Nominal} {δ : Formula} :
	Proof (Sequent Δ δ) → Proof (Sequent (list.map (add_nom X) Δ) (Formula.elemOf X δ))

#check prom_n

-- TODO completar

end promRulesSCiALC