Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm516614_term_abbrevs.
Require Import DISJ_SYM_spec.
Require Import LE_LT_spec.
Lemma lem516581 (t1 : Prop) : term0 t1.
Proof. exact (@lem720 t1). Qed.
Lemma lem516582 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem516583 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem516582 t1) (@lem516581 t1)). Qed.
Lemma lem516584 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem516583 t1 t2). Qed.
Lemma lem516585 (t2 : Prop) (t1 : Prop) : (term2 t1 t2) = ((t1 \/ t2) = (t2 \/ t1)).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem516600 (t2 : Prop) (t1 : Prop) : (t1 \/ t2) = (t2 \/ t1).
Proof. exact (EQ_MP (@lem516585 t2 t1) (@lem516584 t1 t2)). Qed.
Lemma lem516601 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (@lem516600 (m = n) (Peano.lt m n)). Qed.
Lemma lem516602 (m : nat) (n : nat) : (term5 m n) = (term5 m n).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem516603 (m : nat) (n : nat) : ((Peano.le m n) = (term3 m n)) = ((Peano.le m n) = (term4 m n)).
Proof. exact (MK_COMB (@lem516602 m n) (@lem516601 m n)). Qed.
Lemma lem516604 (m : nat) : (term6 m) = (term7 m).
Proof. exact (fun_ext (fun n : nat => @lem516603 m n)). Qed.
Lemma lem516605 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem516606 (m : nat) : (term8 m) = (term9 m).
Proof. exact (MK_COMB (@lem516605) (@lem516604 m)). Qed.
Lemma lem516607 : term10 = term11.
Proof. exact (fun_ext (fun m : nat => @lem516606 m)). Qed.
Lemma lem516608 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem516609 : term12 = term13.
Proof. exact (MK_COMB (@lem516608) (@lem516607)). Qed.
Lemma lem516610 : term13.
Proof. exact (EQ_MP (@lem516609) (@lem97338)). Qed.
Lemma lem516611 (m : nat) : term14 m.
Proof. exact (@lem516610 m). Qed.
Lemma lem516612 (m : nat) : (term14 m) = (term9 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem516613 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem516612 m) (@lem516611 m)). Qed.
Lemma lem516614 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem516613 m n). Qed.
