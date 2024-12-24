Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_LE_REFL_term_abbrevs.
Require Import LE_ADD_spec.
Require Import nadd_le_spec.
Require Import thm0_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem1270570 (m : nat) : term0 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem1270571 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1270572 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1270571 m) (@lem1270570 m)). Qed.
Lemma lem1270573 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1270572 m n). Qed.
Lemma lem1270574 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1270575 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem1270574 m n) (@lem1270573 m n)). Qed.
Lemma lem1270576 (m : nat) (n : nat) : (term3 m n) = ((term3 m n) = True).
Proof. exact (@lem7 (term3 m n)). Qed.
Lemma lem1270578 (x : nadd) : term4 x.
Proof. exact (@lem1269692 x). Qed.
Lemma lem1270579 (x : nadd) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1270580 (x : nadd) : term5 x.
Proof. exact (EQ_MP (@lem1270579 x) (@lem1270578 x)). Qed.
Lemma lem1270581 (x : nadd) (y : nadd) : term6 x y.
Proof. exact (@lem1270580 x y). Qed.
Lemma lem1270582 (x : nadd) (y : nadd) : (term6 x y) = ((nadd_le x y) = (term7 x y)).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem1270589 (x : nadd) (y : nadd) : (nadd_le x y) = (term7 x y).
Proof. exact (EQ_MP (@lem1270582 x y) (@lem1270581 x y)). Qed.
Lemma lem1270590 (x : nadd) : (nadd_le x x) = (term8 x).
Proof. exact (@lem1270589 x x). Qed.
Lemma lem1270600 (m : nat) (n : nat) : (term3 m n) = True.
Proof. exact (EQ_MP (@lem1270576 m n) (@lem1270575 m n)). Qed.
Lemma lem1270601 (x : nadd) (n : nat) (B : nat) : (term9 x n B) = True.
Proof. exact (@lem1270600 (dest_nadd x n) B). Qed.
Lemma lem1270602 (x : nadd) (B : nat) : (term10 x B) = term11.
Proof. exact (fun_ext (fun n : nat => @lem1270601 x n B)). Qed.
Lemma lem1270603 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1270604 (x : nadd) (B : nat) : (term12 x B) = term13.
Proof. exact (MK_COMB (@lem1270603) (@lem1270602 x B)). Qed.
Lemma lem1270606 {A : Type'} (t : Prop) : (term14 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1270607 (t : Prop) : (term15 t) = t.
Proof. exact (@lem1270606 nat t). Qed.
Lemma lem1270608 : term13 = True.
Proof. exact (@lem1270607 True). Qed.
Lemma lem1270609 (x : nadd) (B : nat) : (term12 x B) = True.
Proof. exact (TRANS (@lem1270604 x B) (@lem1270608)). Qed.
Lemma lem1270610 (x : nadd) : (term16 x) = term11.
Proof. exact (fun_ext (fun B : nat => @lem1270609 x B)). Qed.
Lemma lem1270611 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1270612 (x : nadd) : (term8 x) = term17.
Proof. exact (MK_COMB (@lem1270611) (@lem1270610 x)). Qed.
Lemma lem1270614 {A : Type'} (t : Prop) : (term18 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem1270615 (t : Prop) : (term19 t) = t.
Proof. exact (@lem1270614 nat t). Qed.
Lemma lem1270616 : term17 = True.
Proof. exact (@lem1270615 True). Qed.
Lemma lem1270617 (x : nadd) : (term8 x) = True.
Proof. exact (TRANS (@lem1270612 x) (@lem1270616)). Qed.
Lemma lem1270618 (x : nadd) : (nadd_le x x) = True.
Proof. exact (TRANS (@lem1270590 x) (@lem1270617 x)). Qed.
Lemma lem1270619 : term20 = term21.
Proof. exact (fun_ext (fun x : nadd => @lem1270618 x)). Qed.
Lemma lem1270620 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1270621 : term22 = term23.
Proof. exact (MK_COMB (@lem1270620) (@lem1270619)). Qed.
Lemma lem1270623 {A : Type'} (t : Prop) : (term14 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1270624 (t : Prop) : (term24 t) = t.
Proof. exact (@lem1270623 nadd t). Qed.
Lemma lem1270625 : term23 = True.
Proof. exact (@lem1270624 True). Qed.
Lemma lem1270626 : term22 = True.
Proof. exact (TRANS (@lem1270621) (@lem1270625)). Qed.
Lemma lem1270627 : True = term22.
Proof. exact (SYM (@lem1270626)). Qed.
Lemma lem1270628 : term22.
Proof. exact (EQ_MP (@lem1270627) (@lem0)). Qed.
