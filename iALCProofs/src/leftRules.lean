-- Regras do lado esquerdo do sequente de SCiALC.
-- Autor: Bernardo Alkmim
-- bpalkmim@gmail.com

import .basics

namespace leftRulesSCiALC

open iALCbasics

-- Subjunção
constant subj_l {Δ1 Δ2 : list Formula} {α β δ : Formula} :
	Proof (Sequent Δ1 α) → Proof (Sequent (β :: Δ2) δ) → Proof (Sequent ((Formula.subj α β :: Δ1) ++ Δ2) δ)

-- Conjunção
constant conj_l {Δ : list Formula} {α β : Formula} {δ : Formula} :
	Proof (Sequent (α :: (β :: Δ)) δ) → Proof (Sequent (Formula.conj α β :: Δ) δ)

-- Disjunção
constant disj_l {Δ : list Formula} {α β : Formula} {δ : Formula} :
	Proof (Sequent (α :: Δ) δ) → Proof (Sequent (β :: Δ) δ) → Proof (Sequent (Formula.disj α β :: Δ) δ)

-- Disjunção (com nominals)
constant disj_l_n {Δ : list Formula} {α β : Formula} {δ : Formula} (X : Nominal) :
	Proof (Sequent (Formula.elemOf X α :: Δ) δ) → Proof (Sequent (Formula.elemOf X β :: Δ) δ) → Proof (Sequent (Formula.elemOf X (Formula.disj α β) :: Δ) δ)


-- Restrição universal
constant forall_l {Δ : list Formula} {R : Role} {X Y : Nominal} {α : Formula} {δ : Formula} :
	Proof (Sequent (Formula.elemOf Y α :: (Formula.relation R X Y :: (Formula.elemOf X (Formula.univ R α) :: Δ))) δ) → Proof (Sequent (Formula.relation R X Y :: (Formula.elemOf X (Formula.univ R α) :: Δ)) δ)

-- Restrição existencial
constant exists_l {Δ : list Formula} {R : Role} {X Y : Nominal} {α : Formula} {δ : Formula} :
	Proof (Sequent (Formula.elemOf Y α :: (Formula.relation R X Y :: Δ)) δ) → Proof (Sequent (Formula.elemOf X (Formula.exis R α) :: Δ) δ)

end leftRulesSCiALC