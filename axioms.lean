-- Axiomas de SCiALC.
-- Autor: Bernardo Alkmim
-- bpalkmim@gmail.com

namespace axiomsSCiALC

open iALCbasics

-- Identidade
-- Δ, δ ⇒ δ
constant axiom_id {Δ : list Formula} {δ : Formula} :
	Proof (Sequent (δ :: Δ) δ)

-- Δ, x:⊥ ⇒ δ
constant axiom_efq {Δ : list Formula} {X : Nominal} {δ : Formula} :
	Proof (Sequent (ElemOf X Bot :: Δ) δ)

end axiomsSCiALC