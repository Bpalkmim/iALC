-- Regras do lado direito do sequente de SCiALC.
-- Autor: Bernardo Alkmim
-- bpalkmim@gmail.com

namespace rightRulesSCiALC

open iALCbasics

-- Subjunção
constant subj_r {Δ : list Formula} {α β : Concept} :
	Proof (Sequent (α :: Δ) β) → Proof (Sequent Δ (α ⊑ β))

-- Subjunção com nominals
constant subj_r_n {Δ : list Formula} {X : Nominal} {α β : Concept} :
	Proof (Sequent (ElemOf X α :: Δ) (ElemOf X β)) → Proof (Sequent Δ (ElemOf X (α ⊑ β)))

-- Conjunção
constant conj_r {Δ : list Formula} {α β : Concept} :
	Proof (Sequent Δ α) → Proof (Sequent Δ β) → Proof (Sequent Δ (α ⊓ β))

-- Disjunção (duas regras)
constant disj_r1 {Δ : list Formula} {α β : Concept} :
	Proof (Sequent Δ α) → Proof (Sequent Δ (α ⊔ β))

constant disj_r2 {Δ : list Formula} {α β : Concept} :
	Proof (Sequent Δ β) → Proof (Sequent Δ (α ⊔ β))

-- Restrição universal
constant forall_r {Δ : list Formula} {R : Role} {X Y : Nominal} {α : Concept} :
	Proof (Sequent (Relation R X Y :: Δ) (ElemOf Y α)) → Proof (Sequent Δ (ElemOf X (Univ R α)))

-- Restrição existencial
constant exists_r {Δ : list Formula} {R : Role} {X Y : Nominal} {α : Concept} :
	Proof (Sequent Δ (Relation R X Y)) → Proof (Sequent Δ (ElemOf Y α)) → Proof (Sequent Δ (ElemOf X (Exis R α)))

end rightRulesSCiALC