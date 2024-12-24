Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HALF_DOUBLE_term_abbrevs.
Require Import DIV_MULT_spec.
Require Import MULT_SYM_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_SUC_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm80550_spec.
Require Import thm82_spec.
Lemma lem204675 (n : nat) : term0 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem204676 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem204677 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem204676 n) (@lem204675 n)). Qed.
Lemma lem204678 (n : nat) : term2 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem204691 (m : nat) : term3 m.
Proof. exact (@lem170527 m). Qed.
Lemma lem204692 (m : nat) : (term3 m) = (term4 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem204693 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem204692 m) (@lem204691 m)). Qed.
Lemma lem204694 (m : nat) (n : nat) : term5 m n.
Proof. exact (@lem204693 m n). Qed.
Lemma lem204695 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem204696 (m : nat) (n : nat) : term6 m n.
Proof. exact (EQ_MP (@lem204695 m n) (@lem204694 m n)). Qed.
Lemma lem204697 (m : nat) (h1 : term7 m) : term7 m.
Proof. exact (h1). Qed.
Lemma lem204698 (n : nat) (m : nat) (h1 : term7 m) : (term8 n m) = n.
Proof. exact (@lem204696 m n (@lem204697 m h1)). Qed.
Lemma lem204704 (m : nat) : term9 m.
Proof. exact (@lem81820 m). Qed.
Lemma lem204705 (m : nat) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem204706 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem204705 m) (@lem204704 m)). Qed.
Lemma lem204707 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem204706 m n). Qed.
Lemma lem204708 (n : nat) (m : nat) : (term11 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem204711 (n : nat) (m : nat) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem204708 n m) (@lem204707 m n)). Qed.
Lemma lem204712 (n : nat) : (term12 n) = (term13 n).
Proof. exact (@lem204711 term14 n). Qed.
Lemma lem204713 : Nat.div = Nat.div.
Proof. exact (eq_refl Nat.div). Qed.
Lemma lem204714 (n : nat) : (term15 n) = (term16 n).
Proof. exact (MK_COMB (@lem204713) (@lem204712 n)). Qed.
Lemma lem204715 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem204716 (n : nat) : (term17 n) = (term18 n).
Proof. exact (MK_COMB (@lem204714 n) (@lem204715)). Qed.
Lemma lem204717 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem204718 (n : nat) : (term19 n) = (term20 n).
Proof. exact (MK_COMB (@lem204717) (@lem204716 n)). Qed.
Lemma lem204719 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem204720 (n : nat) : ((term17 n) = n) = ((term18 n) = n).
Proof. exact (MK_COMB (@lem204718 n) (@lem204719 n)). Qed.
Lemma lem204721 : term21 = term22.
Proof. exact (fun_ext (fun n : nat => @lem204720 n)). Qed.
Lemma lem204722 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem204723 : term23 = term24.
Proof. exact (MK_COMB (@lem204722) (@lem204721)). Qed.
Lemma lem204724 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem204725 : term26 = term27.
Proof. exact (MK_COMB (@lem204724) (@lem204723)). Qed.
Lemma lem204726 : term27 = term26.
Proof. exact (SYM (@lem204725)). Qed.
Lemma lem204728 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem204729 : term27 = term24.
Proof. exact (@lem204728 term24). Qed.
Lemma lem204737 (m : nat) (n : nat) : term6 m n.
Proof. exact (fun h0 : term7 m => @lem204698 n m h0). Qed.
Lemma lem204738 (n : nat) : term28 n.
Proof. exact (@lem204737 term14 n). Qed.
Lemma lem204742 : term14 = term29.
Proof. exact (EQ_MP (@lem80550) (@lem0)). Qed.
Lemma lem204743 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem204744 : term30 = term31.
Proof. exact (MK_COMB (@lem204743) (@lem204742)). Qed.
Lemma lem204745 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem204746 : (term14 = (NUMERAL 0)) = (term29 = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem204744) (@lem204745)). Qed.
Lemma lem204748 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem204678 n (@lem204677 n)). Qed.
Lemma lem204749 : (term29 = (NUMERAL 0)) = False.
Proof. exact (@lem204748 term32). Qed.
Lemma lem204750 : (term14 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem204746) (@lem204749)). Qed.
Lemma lem204751 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem204752 : term33 = (~ False).
Proof. exact (MK_COMB (@lem204751) (@lem204750)). Qed.
Lemma lem204754 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem204755 : term33 = True.
Proof. exact (TRANS (@lem204752) (@lem204754)). Qed.
Lemma lem204756 : True = term33.
Proof. exact (SYM (@lem204755)). Qed.
Lemma lem204757 : term33.
Proof. exact (EQ_MP (@lem204756) (@lem0)). Qed.
Lemma lem204758 (n : nat) : (term18 n) = n.
Proof. exact (@lem204738 n (@lem204757)). Qed.
Lemma lem204759 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem204760 (n : nat) : (term20 n) = (@eq nat n).
Proof. exact (MK_COMB (@lem204759) (@lem204758 n)). Qed.
Lemma lem204761 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem204762 (n : nat) : ((term18 n) = n) = (n = n).
Proof. exact (MK_COMB (@lem204760 n) (@lem204761 n)). Qed.
Lemma lem204764 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem204765 (x : nat) : (x = x) = True.
Proof. exact (@lem204764 nat x). Qed.
Lemma lem204766 (n : nat) : (n = n) = True.
Proof. exact (@lem204765 n). Qed.
Lemma lem204767 (n : nat) : ((term18 n) = n) = True.
Proof. exact (TRANS (@lem204762 n) (@lem204766 n)). Qed.
Lemma lem204768 : term22 = term34.
Proof. exact (fun_ext (fun n : nat => @lem204767 n)). Qed.
Lemma lem204769 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem204770 : term24 = term35.
Proof. exact (MK_COMB (@lem204769) (@lem204768)). Qed.
Lemma lem204772 {A : Type'} (t : Prop) : (term36 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem204773 (t : Prop) : (term37 t) = t.
Proof. exact (@lem204772 nat t). Qed.
Lemma lem204774 : term35 = True.
Proof. exact (@lem204773 True). Qed.
Lemma lem204775 : term24 = True.
Proof. exact (TRANS (@lem204770) (@lem204774)). Qed.
Lemma lem204776 : term27 = True.
Proof. exact (TRANS (@lem204729) (@lem204775)). Qed.
Lemma lem204777 : True = term27.
Proof. exact (SYM (@lem204776)). Qed.
Lemma lem204778 : term27.
Proof. exact (EQ_MP (@lem204777) (@lem0)). Qed.
Lemma lem204779 : term26.
Proof. exact (EQ_MP (@lem204726) (@lem204778)). Qed.
