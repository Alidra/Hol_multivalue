Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LTE_ADD2_term_abbrevs.
Require Import ADD_SYM_spec.
Require Import CONJ_SYM_spec.
Require Import LET_ADD2_spec.
Lemma lem101696 (t1 : Prop) : term0 t1.
Proof. exact (@lem539 t1). Qed.
Lemma lem101697 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem101698 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem101697 t1) (@lem101696 t1)). Qed.
Lemma lem101699 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem101698 t1 t2). Qed.
Lemma lem101700 (t2 : Prop) (t1 : Prop) : (term2 t1 t2) = ((t1 /\ t2) = (t2 /\ t1)).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem101702 (m : nat) : term3 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem101703 (m : nat) : (term3 m) = (term4 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem101704 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem101703 m) (@lem101702 m)). Qed.
Lemma lem101705 (m : nat) (n : nat) : term5 m n.
Proof. exact (@lem101704 m n). Qed.
Lemma lem101706 (n : nat) (m : nat) : (term5 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem101729 (t2 : Prop) (t1 : Prop) : (t1 /\ t2) = (t2 /\ t1).
Proof. exact (EQ_MP (@lem101700 t2 t1) (@lem101699 t1 t2)). Qed.
Lemma lem101730 (n : nat) (q : nat) (m : nat) (p : nat) : (term6 m p n q) = (term7 n q m p).
Proof. exact (@lem101729 (Peano.le n q) (Peano.lt m p)). Qed.
Lemma lem101731 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem101732 (n : nat) (q : nat) (m : nat) (p : nat) : (term8 m p n q) = (term9 n q m p).
Proof. exact (MK_COMB (@lem101731) (@lem101730 n q m p)). Qed.
Lemma lem101734 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem101706 n m) (@lem101705 m n)). Qed.
Lemma lem101735 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem101736 (n : nat) (m : nat) : (term10 m n) = (term10 n m).
Proof. exact (MK_COMB (@lem101735) (@lem101734 n m)). Qed.
Lemma lem101738 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem101706 n m) (@lem101705 m n)). Qed.
Lemma lem101739 (q : nat) (p : nat) : (Nat.add p q) = (Nat.add q p).
Proof. exact (@lem101738 q p). Qed.
Lemma lem101740 (n : nat) (m : nat) (q : nat) (p : nat) : (term11 m n p q) = (term11 n m q p).
Proof. exact (MK_COMB (@lem101736 n m) (@lem101739 q p)). Qed.
Lemma lem101741 (n : nat) (m : nat) (q : nat) (p : nat) : (term12 m n p q) = (term13 n m q p).
Proof. exact (MK_COMB (@lem101732 n q m p) (@lem101740 n m q p)). Qed.
Lemma lem101742 (n : nat) (m : nat) (p : nat) : (term14 m n p) = (term15 n m p).
Proof. exact (fun_ext (fun q : nat => @lem101741 n m q p)). Qed.
Lemma lem101743 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem101744 (n : nat) (m : nat) (p : nat) : (term16 m n p) = (term17 n m p).
Proof. exact (MK_COMB (@lem101743) (@lem101742 n m p)). Qed.
Lemma lem101745 (n : nat) (m : nat) : (term18 m n) = (term19 n m).
Proof. exact (fun_ext (fun p : nat => @lem101744 n m p)). Qed.
Lemma lem101746 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem101747 (n : nat) (m : nat) : (term20 m n) = (term21 n m).
Proof. exact (MK_COMB (@lem101746) (@lem101745 n m)). Qed.
Lemma lem101748 (m : nat) : (term22 m) = (term23 m).
Proof. exact (fun_ext (fun n : nat => @lem101747 n m)). Qed.
Lemma lem101749 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem101750 (m : nat) : (term24 m) = (term25 m).
Proof. exact (MK_COMB (@lem101749) (@lem101748 m)). Qed.
Lemma lem101751 : term26 = term27.
Proof. exact (fun_ext (fun m : nat => @lem101750 m)). Qed.
Lemma lem101752 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem101753 : term28 = term29.
Proof. exact (MK_COMB (@lem101752) (@lem101751)). Qed.
Lemma lem101754 : term29 = term28.
Proof. exact (SYM (@lem101753)). Qed.
Lemma lem101755 (m : nat) : term30 m.
Proof. exact (@lem101695 m). Qed.
Lemma lem101756 (m : nat) : (term30 m) = (term31 m).
Proof. exact (eq_refl (term30 m)). Qed.
Lemma lem101757 (m : nat) : term31 m.
Proof. exact (EQ_MP (@lem101756 m) (@lem101755 m)). Qed.
Lemma lem101758 (m : nat) (n : nat) : term32 m n.
Proof. exact (@lem101757 m n). Qed.
Lemma lem101759 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (eq_refl (term32 m n)). Qed.
Lemma lem101760 (m : nat) (n : nat) : term33 m n.
Proof. exact (EQ_MP (@lem101759 m n) (@lem101758 m n)). Qed.
Lemma lem101761 (m : nat) (n : nat) (p : nat) : term34 m n p.
Proof. exact (@lem101760 m n p). Qed.
Lemma lem101762 (m : nat) (n : nat) (p : nat) : (term34 m n p) = (term35 m n p).
Proof. exact (eq_refl (term34 m n p)). Qed.
Lemma lem101763 (m : nat) (n : nat) (p : nat) : term35 m n p.
Proof. exact (EQ_MP (@lem101762 m n p) (@lem101761 m n p)). Qed.
Lemma lem101764 (m : nat) (n : nat) (p : nat) (q : nat) : term36 m n p q.
Proof. exact (@lem101763 m n p q). Qed.
Lemma lem101765 (m : nat) (n : nat) (p : nat) (q : nat) : (term36 m n p q) = (term13 m n p q).
Proof. exact (eq_refl (term36 m n p q)). Qed.
Lemma lem101768 (m : nat) (n : nat) (p : nat) (q : nat) : term13 m n p q.
Proof. exact (EQ_MP (@lem101765 m n p q) (@lem101764 m n p q)). Qed.
Lemma lem101769 (n : nat) (m : nat) (q : nat) (p : nat) : term13 n m q p.
Proof. exact (@lem101768 n m q p). Qed.
Lemma lem101774 (n : nat) (m : nat) (p : nat) : term17 n m p.
Proof. exact (fun q : nat => @lem101769 n m q p). Qed.
Lemma lem101779 (n : nat) (m : nat) : term21 n m.
Proof. exact (fun p : nat => @lem101774 n m p). Qed.
Lemma lem101784 (m : nat) : term25 m.
Proof. exact (fun n : nat => @lem101779 n m). Qed.
Lemma lem101789 : term29.
Proof. exact (fun m : nat => @lem101784 m). Qed.
Lemma lem101790 : term28.
Proof. exact (EQ_MP (@lem101754) (@lem101789)). Qed.
