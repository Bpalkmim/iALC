-- Regras do lado direito do sequente de SCiALC.
-- Autor: Bernardo Alkmim
-- bpalkmim@gmail.com

import .basics

namespace rightRulesSCiALC

open iALCbasics

-- Subjunção
constant subj_r {Δ : list Formula} {α : Formula} {β : Concept} :
	Proof (Sequent (α :: Δ) (Formula.simple β)) → Proof (Sequent Δ (Formula.subj α β))

-- Subjunção com nominals
constant subj_r_n {Δ : list Formula} {X : Nominal} {α : Formula} {β : Concept} :
	Proof (Sequent (Formula.elemOf X α :: Δ) (Formula.elemOf X (Formula.simple β))) → Proof (Sequent Δ (Formula.elemOf X (Formula.subj α β)))

-- Conjunção
constant conj_r {Δ : list Formula} {α β : Concept} :
	Proof (Sequent Δ (Formula.simple α)) → Proof (Sequent Δ (Formula.simple β)) → Proof (Sequent Δ (Formula.conj α β))

-- Disjunção (duas regras)
constant disj_r1 {Δ : list Formula} {α β : Concept} :
	Proof (Sequent Δ (Formula.simple α)) → Proof (Sequent Δ (Formula.disj α β))

constant disj_r2 {Δ : list Formula} {α β : Concept} :
	Proof (Sequent Δ (Formula.simple β)) → Proof (Sequent Δ (Formula.disj α β))

-- Restrição universal
constant forall_r {Δ : list Formula} {R : Role} {X Y : Nominal} {α : Concept} :
	Proof (Sequent (Formula.relation R X Y :: Δ) (Formula.elemOf Y (Formula.simple α))) → Proof (Sequent Δ (Formula.elemOf X (Formula.univ R α)))

-- Restrição existencial
constant exists_r {Δ : list Formula} {R : Role} {X Y : Nominal} {α : Concept} :
	Proof (Sequent Δ (Formula.relation R X Y)) → Proof (Sequent Δ (Formula.elemOf Y (Formula.simple α))) → Proof (Sequent Δ (Formula.elemOf X (Formula.exis R α)))

end rightRulesSCiALC