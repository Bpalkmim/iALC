-- Regras estruturais de SCiALC.
-- Autor: Bernardo Alkmim
-- bpalkmim@gmail.com

namespace structRulesSCiALC

open iALCbasics

-- Corte
constant cut {Δ1 Δ2 : list Formula} {δ1 δ2 δ : Formula} :
	Proof (Sequent Δ1 δ1) → Proof (Sequent (δ1 :: Δ2) δ) → Proof (Sequent (Δ1 ++ Δ2) δ)

-- Enfraquecimento

-- Contração

-- Permutação

end structRulesSCiALC