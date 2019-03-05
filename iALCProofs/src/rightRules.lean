-- Regras do lado direito do sequente de SCiALC.
-- Autor: Bernardo Alkmim
-- bpalkmim@gmail.com

import .basics

namespace rightRulesSCiALC

open iALCbasics

-- Subjunção
constant subj_r {Δ : list Formula} {α β : Formula} :
	Proof (Sequent (α :: Δ) β) → Proof (Sequent Δ (Formula.subj α β))

-- Subjunção com nominals
constant subj_r_n {Δ : list Formula} {α β : Formula} (X : Nominal) :
	Proof (Sequent (Formula.elemOf X α :: Δ) (Formula.elemOf X β)) → Proof (Sequent Δ (Formula.elemOf X (Formula.subj α β)))

-- Conjunção
constant conj_r {Δ : list Formula} {α β : Formula} :
	Proof (Sequent Δ α) → Proof (Sequent Δ β) → Proof (Sequent Δ (Formula.conj α β))

-- Disjunção (duas regras)
constant disj_r1 {Δ : list Formula} {α : Formula} (β : Formula) :
	Proof (Sequent Δ α) → Proof (Sequent Δ (Formula.disj α β))

constant disj_r2 {Δ : list Formula} {β : Formula} (α : Formula):
	Proof (Sequent Δ β) → Proof (Sequent Δ (Formula.disj α β))

-- Disjunção com nominals (duas regras)
constant disj_r1_n {Δ : list Formula} {α : Formula} (β : Formula) (X : Nominal) :
	Proof (Sequent Δ (Formula.elemOf X α)) → Proof (Sequent Δ (Formula.elemOf X (Formula.disj α β)))

constant disj_r2_n {Δ : list Formula} {β : Formula} (α : Formula) (X : Nominal):
	Proof (Sequent Δ (Formula.elemOf X β)) → Proof (Sequent Δ (Formula.elemOf X (Formula.disj α β)))

-- Restrição universal
constant forall_r {Δ : list Formula} {R : Role} {X Y : Nominal} {α : Formula} :
	Proof (Sequent (Formula.relation R X Y :: Δ) (Formula.elemOf Y α)) → Proof (Sequent Δ (Formula.elemOf X (Formula.univ R α)))

-- Restrição existencial
constant exists_r {Δ : list Formula} {R : Role} {X Y : Nominal} {α : Formula} :
	Proof (Sequent Δ (Formula.relation R X Y)) → Proof (Sequent Δ (Formula.elemOf Y α)) → Proof (Sequent Δ (Formula.elemOf X (Formula.exis R α)))

end rightRulesSCiALC