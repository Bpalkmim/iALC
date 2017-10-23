-- Arquivo para estudo do artigo das relações entre Jurisprudência Kelseniana
-- e Lógica Intuicionista (Haeusler, Rademaker, 2015)
-- Axiomas para SCiALC.
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