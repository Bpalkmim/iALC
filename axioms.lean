-- Axiomas de SCiALC.
-- Autor: Bernardo Alkmim
-- bpalkmim@gmail.com

namespace axiomsSCiALC

open iALCbasics

-- Identidade
-- Δ, x:δ ⇒ x:δ
constant id {X : Nominal} {Y : Concept} {Z : list Concept} :
	Proof (Sequent Z (ElementOf X Y))

-- Δ, x:⊥ ⇒ x:δ
-- aqui ver se vai o próprio X ou outro cara ou ninguém
constant efq {X : Nominal} {Y : Concept} {Z : list Concept} :
	Proof (Sequent (ElementOf X Bot :: Z) (ElementOf X Y))

end axiomsSCiALC