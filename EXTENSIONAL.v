Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXTENSIONAL_term_abbrevs.
Lemma lem4382759 {A B : Type'} : (@EXTENSIONAL A B) = (term0 A B).
Proof. exact (@EXTENSIONAL_def A B). Qed.
Lemma lem4382760 {A : Type'} (_50046 : A -> Prop) : _50046 = _50046.
Proof. exact (eq_refl _50046). Qed.
Lemma lem4382761 {A B : Type'} (_50046 : A -> Prop) : (@EXTENSIONAL A B _50046) = (term1 A B _50046).
Proof. exact (MK_COMB (@lem4382759 A B) (@lem4382760 A _50046)). Qed.
Lemma lem4382762 {A B : Type'} (_50046 : A -> Prop) : (term1 A B _50046) = (term2 A B _50046).
Proof. exact (eq_refl (term1 A B _50046)). Qed.
Lemma lem4382763 {A B : Type'} (_50046 : A -> Prop) : (@EXTENSIONAL A B _50046) = (term2 A B _50046).
Proof. exact (TRANS (@lem4382761 A B _50046) (@lem4382762 A B _50046)). Qed.
Lemma lem4382764 {A B : Type'} : term3 A B.
Proof. exact (fun _50046 : A -> Prop => @lem4382763 A B _50046). Qed.
Lemma lem4382765 {A B : Type'} (_50046 : A -> Prop) : term4 A B _50046.
Proof. exact (@lem4382764 A B _50046). Qed.
Lemma lem4382766 {A B : Type'} (_50046 : A -> Prop) : (term4 A B _50046) = ((@EXTENSIONAL A B _50046) = (term2 A B _50046)).
Proof. exact (eq_refl (term4 A B _50046)). Qed.
Lemma lem4382767 {A B : Type'} (_50046 : A -> Prop) : (@EXTENSIONAL A B _50046) = (term2 A B _50046).
Proof. exact (EQ_MP (@lem4382766 A B _50046) (@lem4382765 A B _50046)). Qed.
Lemma lem4382797 {A B : Type'} (s : A -> Prop) : (@EXTENSIONAL A B s) = (term2 A B s).
Proof. exact (@lem4382767 A B s). Qed.
Lemma lem4382798 {A B : Type'} : term3 A B.
Proof. exact (fun s : A -> Prop => @lem4382797 A B s). Qed.
