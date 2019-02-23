-- Regras do lado esquerdo do sequente de SCiALC.
-- Autor: Bernardo Alkmim
-- bpalkmim@gmail.com

namespace leftRulesSCiALC

open iALCbasics

-- Subjunção
constant subj_l {Δ1 Δ2 : list Formula} {α β : Concept} {δ : Formula} :
	Proof (Sequent Δ1 α) → Proof (Sequent (β :: Δ2) δ) → Proof (Sequent ((α ⊑ β :: Δ1) ++ Δ2) δ)

-- Conjunção
constant conj_l {Δ : list Formula} {α β : Concept} {δ : Formula} :
	Proof (Sequent (α :: (β :: Δ)) δ) → Proof (Sequent (α ⊓ β :: Δ) δ)

-- Disjunção
constant disj_l {Δ : list Formula} {α β : Concept} {δ : Formula} :
	Proof (Sequent (α :: Δ) δ) → Proof (Sequent (β :: Δ) δ) → Proof (Sequent (α ⊔ β :: Δ) δ)

-- Restrição universal
constant forall_l {Δ : list Formula} {R : Role} {X Y : Nominal} {α : Concept} {δ : Formula} :
	Proof (Sequent (ElemOf Y α :: (Relation R X Y :: (ElemOf X (Univ R α) :: Δ))) δ) → Proof (Sequent (Relation R X Y :: (ElemOf X (Univ R α) :: Δ)) δ)

-- Restrição existencial
constant exists_l {Δ : list Formula} {R : Role} {X Y : Nominal} {α : Concept} {δ : Formula} :
	Proof (Sequent (ElemOf Y α :: (Relation R X Y :: Δ)) δ) → Proof (Sequent (ElemOf X (Exis R α) :: Δ) δ)

end leftRulesSCiALC