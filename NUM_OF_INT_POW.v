Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NUM_OF_INT_POW_term_abbrevs.
Require Import INT_FORALL_POS_spec.
Require Import INT_OF_NUM_POW_spec.
Require Import NUM_OF_INT_OF_NUM_spec.
Require Import SWAP_FORALL_THM_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem2835699 (P : int -> Prop) (h1 : (term0 P) = (term1 P)) : (term0 P) = (term1 P).
Proof. exact (h1). Qed.
Lemma lem2835700 (P : int -> Prop) (h1 : (term0 P) = (term1 P)) : (term1 P) = (term0 P).
Proof. exact (SYM (@lem2835699 P h1)). Qed.
Lemma lem2835701 (P : int -> Prop) (h1 : (term1 P) = (term0 P)) : (term1 P) = (term0 P).
Proof. exact (h1). Qed.
Lemma lem2835702 (P : int -> Prop) (h1 : (term1 P) = (term0 P)) : (term0 P) = (term1 P).
Proof. exact (SYM (@lem2835701 P h1)). Qed.
Lemma lem2835703 (P : int -> Prop) : ((term0 P) = (term1 P)) = ((term1 P) = (term0 P)).
Proof. exact (prop_ext (fun h1 : (term0 P) = (term1 P) => @lem2835700 P h1) (fun h1 : (term1 P) = (term0 P) => @lem2835702 P h1)). Qed.
Lemma lem2835704 : term2 = term3.
Proof. exact (fun_ext (fun P : int -> Prop => @lem2835703 P)). Qed.
Lemma lem2835705 : (@all (int -> Prop)) = (@all (int -> Prop)).
Proof. exact (eq_refl (@all (int -> Prop))). Qed.
Lemma lem2835706 : term4 = term5.
Proof. exact (MK_COMB (@lem2835705) (@lem2835704)). Qed.
Lemma lem2835707 : term5.
Proof. exact (EQ_MP (@lem2835706) (@lem2315380)). Qed.
Lemma lem2835708 (n : nat) : term6 n.
Proof. exact (@lem2833991 n). Qed.
Lemma lem2835709 (n : nat) : (term6 n) = ((term7 n) = n).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem2835711 (x : nat) : term8 x.
Proof. exact (@lem2307411 x). Qed.
Lemma lem2835712 (x : nat) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem2835713 (x : nat) : term9 x.
Proof. exact (EQ_MP (@lem2835712 x) (@lem2835711 x)). Qed.
Lemma lem2835714 (x : nat) (n : nat) : term10 x n.
Proof. exact (@lem2835713 x n). Qed.
Lemma lem2835715 (x : nat) (n : nat) : (term10 x n) = ((term11 x n) = (term12 x n)).
Proof. exact (eq_refl (term10 x n)). Qed.
Lemma lem2835717 (P : int -> Prop) : term13 P.
Proof. exact (@lem2835707 P). Qed.
Lemma lem2835718 (P : int -> Prop) : (term13 P) = ((term1 P) = (term0 P)).
Proof. exact (eq_refl (term13 P)). Qed.
Lemma lem2835720 {A B : Type'} (P : type1413 A B) : term14 A B P.
Proof. exact (@lem4792 A B P). Qed.
Lemma lem2835721 {A B : Type'} (P : type1413 A B) : (term14 A B P) = ((term15 A B P) = (term16 A B P)).
Proof. exact (eq_refl (term14 A B P)). Qed.
Lemma lem2835724 {A B : Type'} (P : type1413 A B) : (term15 A B P) = (term16 A B P).
Proof. exact (EQ_MP (@lem2835721 A B P) (@lem2835720 A B P)). Qed.
Lemma lem2835725 (P : type1552) : (term17 P) = (term18 P).
Proof. exact (@lem2835724 int nat P). Qed.
Lemma lem2835726 : term19 = term20.
Proof. exact (@lem2835725 term21). Qed.
Lemma lem2835727 (x : int) : (term22 x) = (term23 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem2835728 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2835729 (x : int) (n : nat) : (term24 x n) = (term25 x n).
Proof. exact (MK_COMB (@lem2835727 x) (@lem2835728 n)). Qed.
Lemma lem2835730 (x : int) (n : nat) : (term25 x n) = (term26 x n).
Proof. exact (eq_refl (term25 x n)). Qed.
Lemma lem2835731 (x : int) (n : nat) : (term24 x n) = (term26 x n).
Proof. exact (TRANS (@lem2835729 x n) (@lem2835730 x n)). Qed.
Lemma lem2835732 (x : int) : (term27 x) = (term23 x).
Proof. exact (fun_ext (fun n : nat => @lem2835731 x n)). Qed.
Lemma lem2835733 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2835734 (x : int) : (term28 x) = (term29 x).
Proof. exact (MK_COMB (@lem2835733) (@lem2835732 x)). Qed.
Lemma lem2835735 : term30 = term31.
Proof. exact (fun_ext (fun x : int => @lem2835734 x)). Qed.
Lemma lem2835736 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2835737 : term19 = term32.
Proof. exact (MK_COMB (@lem2835736) (@lem2835735)). Qed.
Lemma lem2835738 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2835739 : term33 = term34.
Proof. exact (MK_COMB (@lem2835738) (@lem2835737)). Qed.
Lemma lem2835740 (x : int) : (term22 x) = (term23 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem2835741 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2835742 (x : int) (n : nat) : (term24 x n) = (term25 x n).
Proof. exact (MK_COMB (@lem2835740 x) (@lem2835741 n)). Qed.
Lemma lem2835743 (x : int) (n : nat) : (term25 x n) = (term26 x n).
Proof. exact (eq_refl (term25 x n)). Qed.
Lemma lem2835744 (x : int) (n : nat) : (term24 x n) = (term26 x n).
Proof. exact (TRANS (@lem2835742 x n) (@lem2835743 x n)). Qed.
Lemma lem2835745 (n : nat) : (term35 n) = (term36 n).
Proof. exact (fun_ext (fun x : int => @lem2835744 x n)). Qed.
Lemma lem2835746 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2835747 (n : nat) : (term37 n) = (term38 n).
Proof. exact (MK_COMB (@lem2835746) (@lem2835745 n)). Qed.
Lemma lem2835748 : term39 = term40.
Proof. exact (fun_ext (fun n : nat => @lem2835747 n)). Qed.
Lemma lem2835749 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2835750 : term20 = term41.
Proof. exact (MK_COMB (@lem2835749) (@lem2835748)). Qed.
Lemma lem2835751 : (term19 = term20) = (term32 = term41).
Proof. exact (MK_COMB (@lem2835739) (@lem2835750)). Qed.
Lemma lem2835752 : term32 = term41.
Proof. exact (EQ_MP (@lem2835751) (@lem2835726)). Qed.
Lemma lem2835753 : term41 = term32.
Proof. exact (SYM (@lem2835752)). Qed.
Lemma lem2835759 (P : int -> Prop) : (term1 P) = (term0 P).
Proof. exact (EQ_MP (@lem2835718 P) (@lem2835717 P)). Qed.
Lemma lem2835760 (n : nat) : (term42 n) = (term43 n).
Proof. exact (@lem2835759 (term44 n)). Qed.
Lemma lem2835761 (x : int) (n : nat) : (term45 n x) = ((term46 x n) = (term47 x n)).
Proof. exact (eq_refl (term45 n x)). Qed.
Lemma lem2835762 (x : int) : (term48 x) = (term48 x).
Proof. exact (eq_refl (term48 x)). Qed.
Lemma lem2835763 (x : int) (n : nat) : (term49 n x) = (term26 x n).
Proof. exact (MK_COMB (@lem2835762 x) (@lem2835761 x n)). Qed.
Lemma lem2835764 (n : nat) : (term50 n) = (term36 n).
Proof. exact (fun_ext (fun x : int => @lem2835763 x n)). Qed.
Lemma lem2835765 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2835766 (n : nat) : (term42 n) = (term38 n).
Proof. exact (MK_COMB (@lem2835765) (@lem2835764 n)). Qed.
Lemma lem2835767 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2835768 (n : nat) : (term51 n) = (term52 n).
Proof. exact (MK_COMB (@lem2835767) (@lem2835766 n)). Qed.
Lemma lem2835769 (n' : nat) (n : nat) : (term53 n n') = ((term54 n' n) = (term55 n' n)).
Proof. exact (eq_refl (term53 n n')). Qed.
Lemma lem2835770 (n : nat) : (term56 n) = (term57 n).
Proof. exact (fun_ext (fun n' : nat => @lem2835769 n' n)). Qed.
Lemma lem2835771 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2835772 (n : nat) : (term43 n) = (term58 n).
Proof. exact (MK_COMB (@lem2835771) (@lem2835770 n)). Qed.
Lemma lem2835773 (n : nat) : ((term42 n) = (term43 n)) = ((term38 n) = (term58 n)).
Proof. exact (MK_COMB (@lem2835768 n) (@lem2835772 n)). Qed.
Lemma lem2835774 (n : nat) : (term38 n) = (term58 n).
Proof. exact (EQ_MP (@lem2835773 n) (@lem2835760 n)). Qed.
Lemma lem2835782 (x : nat) (n : nat) : (term11 x n) = (term12 x n).
Proof. exact (EQ_MP (@lem2835715 x n) (@lem2835714 x n)). Qed.
Lemma lem2835783 (n' : nat) (n : nat) : (term11 n' n) = (term12 n' n).
Proof. exact (@lem2835782 n' n). Qed.
Lemma lem2835784 : num_of_int = num_of_int.
Proof. exact (eq_refl num_of_int). Qed.
Lemma lem2835785 (n' : nat) (n : nat) : (term54 n' n) = (term59 n' n).
Proof. exact (MK_COMB (@lem2835784) (@lem2835783 n' n)). Qed.
Lemma lem2835787 (n : nat) : (term7 n) = n.
Proof. exact (EQ_MP (@lem2835709 n) (@lem2835708 n)). Qed.
Lemma lem2835788 (n' : nat) (n : nat) : (term59 n' n) = (Nat.pow n' n).
Proof. exact (@lem2835787 (Nat.pow n' n)). Qed.
Lemma lem2835789 (n' : nat) (n : nat) : (term54 n' n) = (Nat.pow n' n).
Proof. exact (TRANS (@lem2835785 n' n) (@lem2835788 n' n)). Qed.
Lemma lem2835790 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem2835791 (n' : nat) (n : nat) : (term60 n' n) = (term61 n' n).
Proof. exact (MK_COMB (@lem2835790) (@lem2835789 n' n)). Qed.
Lemma lem2835793 (n : nat) : (term7 n) = n.
Proof. exact (EQ_MP (@lem2835709 n) (@lem2835708 n)). Qed.
Lemma lem2835794 (n' : nat) : (term7 n') = n'.
Proof. exact (@lem2835793 n'). Qed.
Lemma lem2835795 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem2835796 (n' : nat) : (term62 n') = (Nat.pow n').
Proof. exact (MK_COMB (@lem2835795) (@lem2835794 n')). Qed.
Lemma lem2835797 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem2835798 (n' : nat) (n : nat) : (term55 n' n) = (Nat.pow n' n).
Proof. exact (MK_COMB (@lem2835796 n') (@lem2835797 n)). Qed.
Lemma lem2835799 (n' : nat) (n : nat) : ((term54 n' n) = (term55 n' n)) = ((Nat.pow n' n) = (Nat.pow n' n)).
Proof. exact (MK_COMB (@lem2835791 n' n) (@lem2835798 n' n)). Qed.
Lemma lem2835801 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2835802 (x : nat) : (x = x) = True.
Proof. exact (@lem2835801 nat x). Qed.
Lemma lem2835803 (n' : nat) (n : nat) : ((Nat.pow n' n) = (Nat.pow n' n)) = True.
Proof. exact (@lem2835802 (Nat.pow n' n)). Qed.
Lemma lem2835804 (n' : nat) (n : nat) : ((term54 n' n) = (term55 n' n)) = True.
Proof. exact (TRANS (@lem2835799 n' n) (@lem2835803 n' n)). Qed.
Lemma lem2835805 (n : nat) : (term57 n) = term63.
Proof. exact (fun_ext (fun n' : nat => @lem2835804 n' n)). Qed.
Lemma lem2835806 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2835807 (n : nat) : (term58 n) = term64.
Proof. exact (MK_COMB (@lem2835806) (@lem2835805 n)). Qed.
Lemma lem2835809 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2835810 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2835809 nat t). Qed.
Lemma lem2835811 : term64 = True.
Proof. exact (@lem2835810 True). Qed.
Lemma lem2835812 (n : nat) : (term58 n) = True.
Proof. exact (TRANS (@lem2835807 n) (@lem2835811)). Qed.
Lemma lem2835813 (n : nat) : (term38 n) = True.
Proof. exact (TRANS (@lem2835774 n) (@lem2835812 n)). Qed.
Lemma lem2835814 : term40 = term63.
Proof. exact (fun_ext (fun n : nat => @lem2835813 n)). Qed.
Lemma lem2835815 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2835816 : term41 = term64.
Proof. exact (MK_COMB (@lem2835815) (@lem2835814)). Qed.
Lemma lem2835818 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2835819 (t : Prop) : (term66 t) = t.
Proof. exact (@lem2835818 nat t). Qed.
Lemma lem2835820 : term64 = True.
Proof. exact (@lem2835819 True). Qed.
Lemma lem2835821 : term41 = True.
Proof. exact (TRANS (@lem2835816) (@lem2835820)). Qed.
Lemma lem2835822 : True = term41.
Proof. exact (SYM (@lem2835821)). Qed.
Lemma lem2835823 : term41.
Proof. exact (EQ_MP (@lem2835822) (@lem0)). Qed.
Lemma lem2835824 : term32.
Proof. exact (EQ_MP (@lem2835753) (@lem2835823)). Qed.
