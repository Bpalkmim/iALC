-- Regras estruturais de SCiALC.
-- Autor: Bernardo Alkmim
-- bpalkmim@gmail.com

import .basics

namespace structRulesSCiALC

open iALCbasics

-- Corte
constant cut {Δ1 Δ2 : list Formula} {δ1 δ2 δ : Formula} :
	Proof (Sequent Δ1 δ1) → Proof (Sequent (δ1 :: Δ2) δ) → Proof (Sequent (Δ1 ++ Δ2) δ)

-- Enfraquecimento
constant weak {Δ : list Formula} {δ δ1 : Formula} :
	Proof (Sequent Δ δ) → Proof (Sequent (δ1 :: Δ) δ)

-- Contração
constant contr {Δ : list Formula} {δ δ1 : Formula} :
	Proof (Sequent (δ1 :: (δ1 :: Δ)) δ) → Proof (Sequent (δ1 :: Δ) δ)

-- Permutação
constant perm {Δ1 Δ2 : list Formula} {δ1 δ2 δ : Formula} :
	Proof (Sequent ((δ1 :: Δ1) ++ (δ2 :: Δ2)) δ) → Proof (Sequent ((δ2 :: Δ1) ++ (δ1 :: Δ2)) δ)

-- Permutação apenas na cabeça da lista
constant perm_head {Δ : list Formula} {δ1 δ2 δ : Formula} :
	Proof (Sequent (δ1 ::(δ2 :: Δ)) δ) → Proof (Sequent (δ2 ::(δ1 :: Δ)) δ)

-- Permutação que troca o primeiro com o terceiro elementos
constant perm_1_3 {Δ : list Formula} {δ1 δ2 δ3 δ : Formula} :
	Proof (Sequent (δ1 :: (δ2 :: (δ3 :: Δ))) δ) → Proof (Sequent (δ3 :: (δ2 :: (δ1 :: Δ))) δ)

end structRulesSCiALC