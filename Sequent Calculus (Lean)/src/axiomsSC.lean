-- Axiomas de SCiALC.
-- Autor: Bernardo Alkmim
-- bpalkmim@gmail.com

import .basics

namespace axiomsSCiALC

open iALCbasics

-- Identidade
-- Δ, δ ⇒ δ
constant axiom_id (Δ : list Formula) (δ : Formula) :
	Proof (Sequent (δ :: Δ) δ)

-- Ex falso quodlibet
-- Δ, x:⊥ ⇒ δ
constant axiom_efq (Δ : list Formula) (δ : Formula) (X : Nominal) :
	Proof (Sequent (Formula.elemOf X (Formula.simple Bot) :: Δ) δ)

end axiomsSCiALC