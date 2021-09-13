(**********************************************
  iALC - Labeled Natural Deduction System
  Author: Bernardo Alkmim (bpalkmim@gmail.com)
  TODO
**********************************************)

Require Export Unicode.Utf8.
Require Export Relations_1.
Require Export Ensembles.
Require Export List.
(*Require Export iALC_NaturalDeduction_Definitions.*)
Set Implicit Arguments.

Module iALC_ND_Labels.

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

(* Constructor for labels. *)
Inductive Label : Set :=
  | ExisL : RoleV → Label
  | UnivL : RoleV → Label
  | NegL : Label → Label
.

(* Constructor for Concepts. *)
Inductive Concept : Set :=
  | Top : Concept
  | Bot : Concept
  | AtomC : Concept
  (*| Neg : Concept → Concept -- moved to Formula (defined by subj) *)
  | Conj : Concept → Concept → Concept
  | Disj : Concept → Concept → Concept
  (*| Subj : Concept → Concept → Concept -- moved to Formula *)
  | Univ : Role → Concept → Concept
  | Exis : Role → Concept → Concept
.

(* Formulas are concepts with a list of labels. *)
(* TODO possible problems may arise with ⊑, ∀, ∃, ¬, rest seems ok *)
Inductive Formula : Set :=
  | Simple : Concept → list Label → Formula
  | NCon : Nom → Formula → Formula (* for nominals *)
  | Neg : Formula → list Label → Formula
  | Subj : Formula → Formula → list Label → Formula
.

(* Useful notations. *)
Notation "' C" := (AtomC C) (at level 1).
Notation "# R" := (AtomR R) (at level 1).
Notation "$ N" := (NomV N) (at level 1).
Notation "⊤" := (Simple Top nil) (at level 0).
Notation "⊥" := (Simple Bot nil) (at level 0).
Notation "C ⊓ D" := (Conj C D) (at level 15, right associativity).
Notation "C ⊔ D" := (Disj C D) (at level 15, right associativity).
Notation "¬ C" := (Neg C) (at level 75, right associativity).
Notation "x ∈ C" := (NCon x C) (at level 25, right associativity).
(*
Notation "C ⊑ D" := (Subj C D nil) (at level 16, right associativity).
Notation "( C ⊑ D ) L" := (Subj C D L) (at level 16, right associativity).
Notation "∀ R . C" := (Univ R C nil) (at level 14, right associativity).
Notation "( ∀ R . C ) L" := (Univ R C L) (at level 14, right associativity).
Notation "∃ R . C" := (Exis R C nil) (at level 14, right associativity).
Notation "( ∃ R . C ) L" := (Exis R C L) (at level 14, right associativity).
*)

(* Natural Deduction Rules *)
(* TODO see how to force ¬L, ∀L, ∃L (lists restricted to negations, univ restrictions
        and exis restrictions, respectively). Perhaps only semantically possible. *)
Reserved Notation "Γ ⊢ A" (at level 80).
Inductive NDcalc : list Formula → Formula → Set :=
  (* Without nominals *)
  | SubjI : ∀ Γ α β L, α::Γ ⊢ β → Γ ⊢ (Subj α β L) (* α and β are already formulas with their respective lists of labels *)
  | SubjE : ∀ Γ α β L, Γ ⊢ α → Γ ⊢ (Subj α β L) → Γ ⊢ β
  | NegI : ∀ Γ α L, α::Γ ⊢ ⊥ → Γ ⊢ ((¬α) L) (* Ver como definir ¬L *)
  | NegE : ∀ Γ α L, Γ ⊢ α → Γ ⊢ ((¬α) L) → Γ ⊢ ⊥
  | ConjI : ∀ Γ α β L, Γ ⊢ (Simple α L) → Γ ⊢ (Simple β L) → Γ ⊢ (Simple (α ⊓ β) L) (* Garantia de ter apenas ∀ : semântica?*)
  | ConjE1 : ∀ Γ α β L, Γ ⊢ (Simple (α ⊓ β) L) → Γ ⊢ (Simple α L)
  | ConjE2 : ∀ Γ α β L, Γ ⊢ (Simple (α ⊓ β) L) → Γ ⊢ (Simple β L)
  | DisjI1 : ∀ Γ α β L, Γ ⊢ (Simple α L) → Γ ⊢ (Simple (α ⊔ β) L) (* Garantia de ter apenas ∃ : semântica?*)
  | DisjI2 : ∀ Γ α β L, Γ ⊢ (Simple β L) → Γ ⊢ (Simple (α ⊔ β) L)
  | DisjE : ∀ Γ α β δ L, Γ ⊢ (Simple (α ⊔ β) L) → (Simple α L)::Γ ⊢ δ → (Simple β L)::Γ ⊢ δ → Γ ⊢ δ
  | Efq : ∀ Γ δ, Γ ⊢ ⊥ → Γ ⊢ δ
  (* With nominals *)
  | SubjIn : ∀ Γ α β x L1 L2 L, (x ∈ (Simple α L1))::Γ ⊢ (x ∈ (Simple β L2)) → Γ ⊢ (x ∈ (Subj (Simple α L1) (Simple β L2) L))
  | SubjEn : ∀ Γ α β x L1 L2 L, Γ ⊢ (x ∈ (Simple α L1)) → Γ ⊢ (x ∈ (Subj (Simple α L1) (Simple β L2) L)) → Γ ⊢ (x ∈ (Simple β L2))
  | NegIn : ∀ Γ α x L, (x ∈ α)::Γ ⊢ (x ∈ ⊥) → Γ ⊢ (x ∈ ((¬α) L))
  | NegEn : ∀ Γ α x L, Γ ⊢ (x ∈ α) → Γ ⊢ (x ∈ ((¬α) L)) → Γ ⊢ (x ∈ ⊥)
  | ConjIn : ∀ Γ α β x L, Γ ⊢ (x ∈ (Simple α L)) → Γ ⊢ (x ∈ (Simple β L)) → Γ ⊢ (x ∈ (Simple (α ⊓ β) L))
  | ConjE1n : ∀ Γ α β x L, Γ ⊢ (x ∈ (Simple (α ⊓ β) L)) → Γ ⊢ (x ∈ (Simple α L))
  | ConjE2n : ∀ Γ α β x L, Γ ⊢ (x ∈ (Simple (α ⊓ β) L)) → Γ ⊢ (x ∈ (Simple β L))
  | DisjI1n : ∀ Γ α β x L, Γ ⊢ (x ∈ (Simple α L)) → Γ ⊢ (x ∈ (Simple (α ⊔ β) L))
  | DisjI2n : ∀ Γ α β x L, Γ ⊢ (x ∈ (Simple β L)) → Γ ⊢ (x ∈ (Simple (α ⊔ β) L))
  | DisjEn : ∀ Γ α β δ x L, Γ ⊢ (x ∈ (Simple (α ⊔ β) L)) → (x ∈ (Simple α L))::Γ ⊢ δ → (x ∈ (Simple β L))::Γ ⊢ δ → Γ ⊢ δ
  | Efqn : ∀ Γ δ x, Γ ⊢ (x ∈ ⊥) → Γ ⊢ δ
  (* ∃ and ∀ rules - how to guarantee x ≼ y ? Only semantically *)
  | ExisI : ∀ Γ α R x y L, Γ ⊢ (y ∈ (Simple α ((ExisL R)::L))) → Γ ⊢ x ∈ (Simple (Exis (#R) α) L)
  | ExisE : ∀ Γ α R x y L, Γ ⊢ x ∈ (Simple (Exis (#R) α) L) → Γ ⊢ (y ∈ (Simple α ((ExisL R)::L)))
  | UnivI : ∀ Γ α R x y L, Γ ⊢ (y ∈ (Simple α ((UnivL R)::L))) → Γ ⊢ x ∈ (Simple (Univ (#R) α) L)
  | UnivE : ∀ Γ α R x y L, Γ ⊢ x ∈ (Simple (Univ (#R) α) L) → Γ ⊢ (y ∈ (Simple α ((UnivL R)::L)))
  (* Structural rules TODO *)
  | Hyp : ∀ Γ α, In α Γ → Γ ⊢ α
  where "Γ ⊢ A" := (NDcalc Γ A).


(* Casos de teste *)
(* Sem Nominals *)
Lemma ConjComm : ∀ Γ C D L, Γ ⊢ (Subj (Simple (D ⊓ C) L) (Simple (C ⊓ D) L) nil).
Proof.
  intros.
  apply SubjI.
  apply ConjI.
  - apply ConjE2 with (α := D).
    apply Hyp. apply in_eq.
  - apply ConjE1 with (β := C).
    apply Hyp. apply in_eq.
Qed.

Lemma DisjComm : ∀ Γ C D L, Γ ⊢ (Subj (Simple (D ⊔ C) L) (Simple (C ⊔ D) L) nil).
Proof.
  intros.
  apply SubjI.
  apply DisjE with (α := D) (β := C) (L := L).
  - apply Hyp. apply in_eq.
  - apply DisjI2.
    apply Hyp. apply in_eq.
  - apply DisjI1.
    apply Hyp. apply in_eq.
Qed.

Lemma SubjABA : ∀ Γ C D L1 L2 L3 L4, (* Γ ⊢ C ⊑ (C ⊑ D) *)
  Γ ⊢ (Subj (Simple C L1) (Subj (Simple D L2) (Simple C L1) L3) L4).
Proof.
  intros.
  apply SubjI.
  apply SubjI.
  apply Hyp. apply in_cons. apply in_eq.
Qed.

Lemma ModusTollensAlmost : ∀ Γ C D L1 L2 L3 L4, (* Γ ⊢ (C ⊑ D) ⊑ (¬D ⊑ ¬C) *)
  Γ ⊢ (Subj (Subj (Simple C L1) (Simple D L2) L1) (Subj ((¬(Simple D L2)) L2) ((¬(Simple C L1)) L1) L3) L4).
Proof.
  intros.
  apply SubjI.
  apply SubjI.
  apply NegI.
  apply NegE with (α := Simple D L2) (L := L2).
  - apply SubjE with (α := Simple C L1) (L:= L1).
    * apply Hyp. apply in_eq.
    * apply Hyp. apply in_cons. apply in_cons. apply in_eq.
  - apply Hyp. apply in_cons. apply in_eq.
Qed.

Lemma EfqTest : ∀ Γ C D G L, (* (C ⊑ D :: (C ⊓ ¬D) :: Γ) ⊢ G *)
  (() :: (Simple (C ⊓ ¬(Simple D L)) L) :: Γ) ⊢ G.
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
  

End iALC_ND.