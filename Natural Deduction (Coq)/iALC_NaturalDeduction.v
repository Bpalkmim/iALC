(**********************************************
  iALC - Natural Deduction System
  Author: Bernardo Alkmim (bpalkmim@gmail.com)
  TODO
**********************************************)

Require Export Unicode.Utf8.
Require Export Relations_1.
Require Export Ensembles.
Require Export List.
(*Require Export iALC_NaturalDeduction_Definitions.*)
Set Implicit Arguments.

Module iALC_ND.

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
  | NCon : Nom → Concept → Concept
.

(* Useful notations. *)
Notation "⊤" := Top (at level 0).
Notation "⊥" := Bot (at level 0).
Notation "' C" := (AtomC C) (at level 1).
Notation "# R" := (RoleV R) (at level 1).
Notation "$ N" := (NomV N) (at level 1).
Notation "C ⊓ D" := (Conj C D) (at level 15, right associativity).
Notation "C ⊔ D" := (Disj C D) (at level 15, right associativity).
Notation "¬ C" := (Neg C) (at level 75, right associativity).
Notation "∀ R . C" := (Univ R C) (at level 5, right associativity).
Notation "∃ R . C" := (Exis R C) (at level 5, right associativity).
Notation "C ⊑ D" := (Subj C D) (at level 16, right associativity).
Notation "x ∈ C" := (NCon x C) (at level 25, right associativity).

(* Natural Deduction Rules *)
(* TODO *)
Reserved Notation "Γ ⊢ A" (at level 80).
Inductive NDcalc : list Concept → Concept → Set :=
  (* Without nominals *)
  | SubjI : ∀ Γ α β, α::Γ ⊢ β → Γ ⊢ α ⊑ β (* Cuidado com Labels *)
  | SubjE : ∀ Γ α β, Γ ⊢ α → Γ ⊢ α ⊑ β → Γ ⊢ β
  | NegI : ∀ Γ α, α::Γ ⊢ ⊥ → Γ ⊢ ¬α
  | NegE : ∀ Γ α, Γ ⊢ α → Γ ⊢ ¬α → Γ ⊢ ⊥
  | ConjI : ∀ Γ α β, Γ ⊢ α → Γ ⊢ β → Γ ⊢ α ⊓ β (* Cuidado com Labels *)
  | ConjE1 : ∀ Γ α β, Γ ⊢ α ⊓ β → Γ ⊢ α
  | ConjE2 : ∀ Γ α β, Γ ⊢ α ⊓ β → Γ ⊢ β
  | DisjI1 : ∀ Γ α β, Γ ⊢ α → Γ ⊢ α ⊔ β (* Cuidado com Labels *)
  | DisjI2 : ∀ Γ α β, Γ ⊢ β → Γ ⊢ α ⊔ β
  | DisjE : ∀ Γ α β δ, Γ ⊢ α ⊔ β → α::Γ ⊢ δ → β::Γ ⊢ δ → Γ ⊢ δ
  | Efq : ∀ Γ δ, Γ ⊢ ⊥ → Γ ⊢ δ
  (* With nominals *)
  | SubjIn : ∀ Γ α β x, (x ∈ α)::Γ ⊢ (x ∈ β) → Γ ⊢ (x ∈ α ⊑ β) (* Cuidado com Labels *)
  | SubjEn : ∀ Γ α β x, Γ ⊢ (x ∈ α) → Γ ⊢ (x ∈ α ⊑ β) → Γ ⊢ (x ∈ β)
  | NegIn : ∀ Γ α x, (x ∈ α)::Γ ⊢ (x ∈ ⊥) → Γ ⊢ (x ∈ ¬α)
  | NegEn : ∀ Γ α x, Γ ⊢ (x ∈ α) → Γ ⊢ (x ∈ ¬α) → Γ ⊢ (x ∈ ⊥)
  | ConjIn : ∀ Γ α β x, Γ ⊢ (x ∈ α) → Γ ⊢ (x ∈ β) → Γ ⊢ (x ∈ α ⊓ β) (* Cuidado com Labels *)
  | ConjE1n : ∀ Γ α β x, Γ ⊢ (x ∈ α ⊓ β) → Γ ⊢ (x ∈ α)
  | ConjE2n : ∀ Γ α β x, Γ ⊢ (x ∈ α ⊓ β) → Γ ⊢ (x ∈ β)
  | DisjI1n : ∀ Γ α β x, Γ ⊢ (x ∈ α) → Γ ⊢ (x ∈ α ⊔ β) (* Cuidado com Labels *)
  | DisjI2n : ∀ Γ α β x, Γ ⊢ (x ∈ β) → Γ ⊢ (x ∈ α ⊔ β)
  | DisjEn : ∀ Γ α β δ x, Γ ⊢ (x ∈ α ⊔ β) → (x ∈ α)::Γ ⊢ δ → (x ∈ β)::Γ ⊢ δ → Γ ⊢ δ
  | Efqn : ∀ Γ δ x, Γ ⊢ (x ∈ ⊥) → Γ ⊢ δ
  (* ∃ and ∀ rules - how to guarantee x ≼ y ? Only semantically *)
  | ExisI : ∀ Γ α R x y, Γ ⊢ (y ∈ α) → Γ ⊢ x ∈ (Exis R α) (* Cuidado com Labels *)
  | ExisE : ∀ Γ α R x y, Γ ⊢ x ∈ (Exis R α) → Γ ⊢ (y ∈ α)
  | UnivI : ∀ Γ α R x y, Γ ⊢ (y ∈ α) → Γ ⊢ x ∈ (Univ R α)
  | UnivE : ∀ Γ α R x y, Γ ⊢ x ∈ (Univ R α) → Γ ⊢ (y ∈ α)
  (* Structural rules TODO *)
  | Hyp : ∀ Γ α, In α Γ → Γ ⊢ α
  where "Γ ⊢ A" := (NDcalc Γ A).


(* Casos de teste *)
(* Sem Nominals *)
Lemma ConjComm : ∀ Γ C D, Γ ⊢ ((D ⊓ C) ⊑ (C ⊓ D)).
Proof.
  intros.
  apply SubjI.
  apply ConjI.
  - apply @ConjE2 with (α := D).
    apply Hyp. apply in_eq.
  - apply @ConjE1 with (β := C).
    apply Hyp. apply in_eq.
Qed.

Lemma DisjComm : ∀ Γ C D, Γ ⊢ ((D ⊔ C) ⊑ (C ⊔ D)).
Proof.
  intros.
  apply SubjI.
  apply @DisjE with (α := D) (β := C).
  - apply Hyp. apply in_eq.
  - apply DisjI2.
    apply Hyp. apply in_eq.
  - apply DisjI1.
    apply Hyp. apply in_eq.
Qed.

Lemma SubjABA : ∀ Γ C D, Γ ⊢ (C ⊑ (D ⊑ C)).
Proof.
  intros.
  apply SubjI.
  apply SubjI.
  apply Hyp. apply in_cons. apply in_eq.
Qed.

Lemma ModusTollensAlmost : ∀ Γ C D, Γ ⊢ ((C ⊑ D) ⊑ ((¬D) ⊑ ¬C)).
Proof.
  intros.
  apply SubjI.
  apply SubjI.
  apply NegI.
  apply NegE with (α := D).
  - apply SubjE with (α := C).
    * apply Hyp. apply in_eq.
    * apply Hyp. apply in_cons. apply in_cons. apply in_eq.
  - apply Hyp. apply in_cons. apply in_eq.
Qed.

Lemma EfqTest : ∀ Γ C D G, (C ⊑ D :: (C ⊓ ¬D) :: Γ) ⊢ G.
Proof.
  intros.
  apply Efq.
  apply @NegE with (α := C).
  - apply @ConjE1 with (β := ¬D).
    apply Hyp. apply in_cons. apply in_eq.
  - apply NegI.
    apply @NegE with (α := D).
    * apply @SubjE with (α := C).
      + apply Hyp. apply in_eq.
      + apply Hyp. apply in_cons. apply in_eq.
    * apply @ConjE2 with (α := C).
      apply Hyp. apply in_cons. apply in_cons. apply in_eq.
Qed.

(* Com Nominals *)
Lemma ConjCommN : ∀ Γ C D x, Γ ⊢ (x ∈ ((D ⊓ C) ⊑ (C ⊓ D))).
Proof.
  intros.
  apply SubjIn.
  apply ConjIn.
  - apply @ConjE2n with (α := D).
    apply Hyp. apply in_eq.
  - apply @ConjE1n with (β := C).
    apply Hyp. apply in_eq.
Qed.

Lemma DisjCommN : ∀ Γ C D x, Γ ⊢ (x ∈ ((D ⊔ C) ⊑ (C ⊔ D))).
Proof.
  intros.
  apply SubjIn.
  apply @DisjEn with (x := x) (α := D) (β := C).
  - apply Hyp. apply in_eq.
  - apply DisjI2n.
    apply Hyp. apply in_eq.
  - apply DisjI1n.
    apply Hyp. apply in_eq.
Qed.

Lemma SubjABAN : ∀ Γ C D x, Γ ⊢ (x ∈ (C ⊑ (D ⊑ C))).
Proof.
  intros.
  apply SubjIn.
  apply SubjIn.
  apply Hyp. apply in_cons. apply in_eq.
Qed.

Lemma ModusTollensAlmostN : ∀ Γ C D x, Γ ⊢ (x ∈ ((C ⊑ D) ⊑ ((¬D) ⊑ ¬C))).
Proof.
  intros.
  apply SubjIn.
  apply SubjIn.
  apply NegIn.
  apply NegEn with (α := D).
  - apply SubjEn with (α := C).
    * apply Hyp. apply in_eq.
    * apply Hyp. apply in_cons. apply in_cons. apply in_eq.
  - apply Hyp. apply in_cons. apply in_eq.
Qed.

Lemma EfqTestN : ∀ Γ C D G x, (x ∈ C ⊑ D :: x ∈ (C ⊓ ¬D) :: Γ) ⊢ x ∈ G.
Proof.
  intros.
  apply @Efqn with (x := x).
  apply @NegEn with (α := C).
  - apply @ConjE1n with (β := ¬D).
    apply Hyp. apply in_cons. apply in_eq.
  - apply NegIn.
    apply @NegEn with (α := D).
    * apply @SubjEn with (α := C).
      + apply Hyp. apply in_eq.
      + apply Hyp. apply in_cons. apply in_eq.
    * apply @ConjE2n with (α := C).
      apply Hyp. apply in_cons. apply in_cons. apply in_eq.
Qed.

Lemma proof1 : ∀ Γ C D R x (y : Nom), Γ ⊢ (x ∈ ((Univ R (C ⊑ D)) ⊑ ((Univ R C)⊑(Univ R D)))).
Proof.
  intros.
  apply SubjIn.
  apply SubjIn.
  apply @UnivI with (y := y).
  Admitted.

Lemma proof4 : ∀ Γ R x (y : Nom), Γ ⊢ (x ∈ ((Exis R ⊥) ⊑ ⊥)).
Proof.
  intros.
  apply SubjIn.
  apply @Efqn with (x := y).
  apply @ExisE with (R := R) (x := x).
  apply Hyp. apply in_eq.
Qed.

End iALC_ND.