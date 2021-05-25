-- Regras de promoção de SCiALC.
-- Autor: Bernardo Alkmim
-- bpalkmim@gmail.com

import .basics

namespace promRulesSCiALC

open iALCbasics

constant prom_n {Δ : list Formula} {δ : Formula} (X : Nominal) :
	Proof (Sequent Δ δ) → Proof (Sequent (list.map (add_nom X) Δ) (Formula.elemOf X δ))

constant prom_forall {Δ : list Formula} {δ : Formula} (R : Role) :
	Proof (Sequent Δ δ) → Proof (Sequent (list.map (add_univ R) Δ) (Formula.univ R δ))

constant prom_exists {Δ : list Formula} {α β : Formula} (R : Role) :
	Proof (Sequent (α :: Δ) β) → Proof (Sequent (Formula.exis R α :: (list.map (add_univ R) Δ)) (Formula.exis R β))

end promRulesSCiALC