(**********************************************
  iALC - Labeled Natural Deduction System
  Completeness and Soundness Proofs
  Author: Bernardo Alkmim (bpalkmim@gmail.com)
  TODO
**********************************************)

Require Export Unicode.Utf8.
Require Export Relations_1.
Require Export Ensembles.
Require Export List.
Set Implicit Arguments.

Module iALC_ND.

Declare Scope NDscope.
Open Scope NDscope.

(* Definitions *)
(* TODO
 *)

(* Definition of variables, used in the Completeness proof. *)
Parameter ConV : Set.

(* Nominal variables. *)
Parameter NomV : Set.

(* Role Variables. *)
Parameter RoleV : Set.

(* Labels. *)
(* TODO *)

(* Constructor for nominals. *)
Inductive Nom : Set :=
  AtomN : NomV → Nom.


(* Constructor for roles. *)
Inductive Role : Set :=
  AtomR : RoleV → Role.

(* Constructor for Concepts. *)
Inductive Concept : Set :=
  | Top : Concept
  | Bot : Concept
  | AtomC : ConV → Concept
  | Conj : Concept → Concept → Concept
  | Disj : Concept → Concept → Concept
  | Neg : Concept → Concept
  | Univ : Role → Concept → Concept
  | Exis : Role → Concept → Concept
  | Subj : Concept → Concept → Concept
.

(* Useful notations. *)
Notation "⊤" := Top (at level 0) : NDscope.
Notation "⊥" := Bot (at level 0) : NDscope.
Notation "' C" := (AtomC C) (at level 1) : NDscope.
Notation "# R" := (RoleV R) (at level 1) : NDscope.
Notation "$ N" := (NomV N) (at level 1) : NDscope.
Notation "C ⊓ D" := (Conj C D) (at level 15, right associativity) : NDscope.
Notation "C ⊔ D" := (Disj C D) (at level 15, right associativity) : NDscope.
Notation "¬ C" := (Neg C) (at level 75, right associativity) : NDscope.
Notation "∀ R . C" := (Univ R C) (at level 5, right associativity) : NDscope.
Notation "∃ R . C" := (Exis R C) (at level 5, right associativity) : NDscope.
Notation "C ⊑ D" := (Subj C D) (at level 16, right associativity) : NDscope.
Notation "x ∈ C" := (In C x) (at level 25, right associativity) : NDscope.

(* Defining a semantic interpretation for iALC. *)
Record Inter : Type := {
  Dom : Set;
  inter_n : NomV → Ensemble Dom;
  inter_c : ConV → Ensemble Dom;
  inter_r : RoleV → Relation Dom
}.

(* Interpretation of roles. *)
Definition interR {Dom : Set} (inter_r : RoleV → Relation Dom) (r : Role) : Relation Dom :=
match r with
  AtomR R => inter_r R
end.

(* Interpretation of nominals. *)
Definition interN {Dom : Set} (inter_n : NomV → Ensemble Dom) (n : Nom) : Ensemble Dom :=
match n with
  AtomN x => inter_n x
end.

(* Definition of the ABox-esque sentences. They are needed to the definition of interpretation, mainly due to the precedence relation. *)
Inductive Fact : Set :=
  | inst : Nom → Concept → Fact
  | rel : Role → Nom → Nom → Fact
  | dif : Nom → Nom → Fact
  | prec : Nom → Nom → Fact.

(* definir propriedades de precedência TODO
Definition prec_trans := ∀ x y z, (prec x y) → (prec y z) → (prec x z). *)

Notation "x ≼ y" := (prec x y) (at level 20, right associativity) : NDscope.

(* Coercion *)
Definition Dom_to_Nom {i : Inter} (d : Dom i) : Nom :=
match d with
  | interN x => AtomN x
end.

Coercion Dom_to_Nom : Dom >-> Nom.
(* Relation_Definitions 
    Nom → (relation Dom) *)
(* Interpretation of formulas. *)
Fixpoint interC (i : Inter) (c : Concept) {struct c}: Ensemble (Dom i) :=
match c with
  | ⊥ => Empty_set (Dom i)
  | ⊤ => Full_set (Dom i)
  | 'C => inter_c i C
  | ¬ C => fun x => ∀ y, (x ≼ y) → ~ (interC i C y)
  | C ⊓ D => Intersection (Dom i) (interC i C) (interC i D)
  | C ⊔ D => Union (Dom i) (interC i C) (interC i D)
  | Univ R C => fun x => ∀ y, (x ≼ y) → (∀ z, (interR (inter_r i) R y z) → (interC i C z))
  | Exis R C => fun x => ∀ y, (x ≼ y) → (∃ z, (interR (inter_r i) R y z) → (interC i C z))
  | C ⊑ D => fun x => ∀ y, (x ≼ y /\ (interC i C y)) → interC i D y
end.

(* Valuation function (for Soundness). *)
Fixpoint NDeval (eval : Vars → Set) (F : Concept) : Set := 
match F with
  | ⊥ => ⊥
  | C ⊓ D => (NDeval eval C) /\ (NDeval eval D)
  | C ⊔ D => (NDeval eval C) \/ (NDeval eval D)
  | C ⊑ D => ∀ x y, x ≼ y /\ y ∈ (NDeval eval C) → y ∈ (NDeval eval D)
  | default => ⊥
end.

(* Natural Deduction Rules *)
(* TODO *)
Inductive NDcalc : list Concept → Concept → Concept
  |

(* Completeness *)
(* TODO *)

(* Soundness *)
(* TODO *)

End iALC_ND.