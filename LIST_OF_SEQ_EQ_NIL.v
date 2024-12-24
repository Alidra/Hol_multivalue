Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LIST_OF_SEQ_EQ_NIL_term_abbrevs.
Require Import LENGTH_EQ_NIL_spec.
Require Import LENGTH_LIST_OF_SEQ_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1237534 {A : Type'} (l : list A) (h1 : ((@List.length A l) = (NUMERAL 0)) = (l = (@nil A))) : ((@List.length A l) = (NUMERAL 0)) = (l = (@nil A)).
Proof. exact (h1). Qed.
Lemma lem1237535 {A : Type'} (l : list A) (h1 : ((@List.length A l) = (NUMERAL 0)) = (l = (@nil A))) : (l = (@nil A)) = ((@List.length A l) = (NUMERAL 0)).
Proof. exact (SYM (@lem1237534 A l h1)). Qed.
Lemma lem1237536 {A : Type'} (l : list A) (h1 : (l = (@nil A)) = ((@List.length A l) = (NUMERAL 0))) : (l = (@nil A)) = ((@List.length A l) = (NUMERAL 0)).
Proof. exact (h1). Qed.
Lemma lem1237537 {A : Type'} (l : list A) (h1 : (l = (@nil A)) = ((@List.length A l) = (NUMERAL 0))) : ((@List.length A l) = (NUMERAL 0)) = (l = (@nil A)).
Proof. exact (SYM (@lem1237536 A l h1)). Qed.
Lemma lem1237538 {A : Type'} (l : list A) : (((@List.length A l) = (NUMERAL 0)) = (l = (@nil A))) = ((l = (@nil A)) = ((@List.length A l) = (NUMERAL 0))).
Proof. exact (prop_ext (fun h1 : ((@List.length A l) = (NUMERAL 0)) = (l = (@nil A)) => @lem1237535 A l h1) (fun h1 : (l = (@nil A)) = ((@List.length A l) = (NUMERAL 0)) => @lem1237537 A l h1)). Qed.
Lemma lem1237539 {A : Type'} : (term0 A) = (term1 A).
Proof. exact (fun_ext (fun l : list A => @lem1237538 A l)). Qed.
Lemma lem1237540 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1237541 {A : Type'} : (term2 A) = (term3 A).
Proof. exact (MK_COMB (@lem1237540 A) (@lem1237539 A)). Qed.
Lemma lem1237542 {A : Type'} : term3 A.
Proof. exact (EQ_MP (@lem1237541 A) (@lem1117066 A)). Qed.
Lemma lem1237551 {A : Type'} (s : nat -> A) : term4 A s.
Proof. exact (@lem1237097 A s). Qed.
Lemma lem1237552 {A : Type'} (s : nat -> A) : (term4 A s) = (term5 A s).
Proof. exact (eq_refl (term4 A s)). Qed.
Lemma lem1237553 {A : Type'} (s : nat -> A) : term5 A s.
Proof. exact (EQ_MP (@lem1237552 A s) (@lem1237551 A s)). Qed.
Lemma lem1237554 {A : Type'} (s : nat -> A) (n : nat) : term6 A s n.
Proof. exact (@lem1237553 A s n). Qed.
Lemma lem1237555 {A : Type'} (s : nat -> A) (n : nat) : (term6 A s n) = ((term7 A s n) = n).
Proof. exact (eq_refl (term6 A s n)). Qed.
Lemma lem1237557 {A : Type'} (l : list A) : term8 A l.
Proof. exact (@lem1237542 A l). Qed.
Lemma lem1237558 {A : Type'} (l : list A) : (term8 A l) = ((l = (@nil A)) = ((@List.length A l) = (NUMERAL 0))).
Proof. exact (eq_refl (term8 A l)). Qed.
Lemma lem1237571 {A : Type'} (l : list A) : (l = (@nil A)) = ((@List.length A l) = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1237558 A l) (@lem1237557 A l)). Qed.
Lemma lem1237572 {A : Type'} (l : list A) : (l = (@nil A)) = ((@List.length A l) = (NUMERAL 0)).
Proof. exact (@lem1237571 A l). Qed.
Lemma lem1237573 {A : Type'} (s : nat -> A) (n : nat) : ((@list_of_seq A s n) = (@nil A)) = ((term7 A s n) = (NUMERAL 0)).
Proof. exact (@lem1237572 A (@list_of_seq A s n)). Qed.
Lemma lem1237577 {A : Type'} (s : nat -> A) (n : nat) : (term7 A s n) = n.
Proof. exact (EQ_MP (@lem1237555 A s n) (@lem1237554 A s n)). Qed.
Lemma lem1237578 {A : Type'} (s : nat -> A) (n : nat) : (term7 A s n) = n.
Proof. exact (@lem1237577 A s n). Qed.
Lemma lem1237579 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1237580 {A : Type'} (s : nat -> A) (n : nat) : (term9 A s n) = (@eq nat n).
Proof. exact (MK_COMB (@lem1237579) (@lem1237578 A s n)). Qed.
Lemma lem1237581 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1237582 {A : Type'} (s : nat -> A) (n : nat) : ((term7 A s n) = (NUMERAL 0)) = (n = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1237580 A s n) (@lem1237581)). Qed.
Lemma lem1237585 {A : Type'} (s : nat -> A) (n : nat) : ((@list_of_seq A s n) = (@nil A)) = (n = (NUMERAL 0)).
Proof. exact (TRANS (@lem1237573 A s n) (@lem1237582 A s n)). Qed.
Lemma lem1237586 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1237587 {A : Type'} (s : nat -> A) (n : nat) : (term10 A s n) = (term11 n).
Proof. exact (MK_COMB (@lem1237586) (@lem1237585 A s n)). Qed.
Lemma lem1237590 (n : nat) : (n = (NUMERAL 0)) = (n = (NUMERAL 0)).
Proof. exact (eq_refl (n = (NUMERAL 0))). Qed.
Lemma lem1237591 {A : Type'} (s : nat -> A) (n : nat) : (((@list_of_seq A s n) = (@nil A)) = (n = (NUMERAL 0))) = ((n = (NUMERAL 0)) = (n = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1237587 A s n) (@lem1237590 n)). Qed.
Lemma lem1237593 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1237594 (x : Prop) : (x = x) = True.
Proof. exact (@lem1237593 Prop x). Qed.
Lemma lem1237595 (n : nat) : ((n = (NUMERAL 0)) = (n = (NUMERAL 0))) = True.
Proof. exact (@lem1237594 (n = (NUMERAL 0))). Qed.
Lemma lem1237596 {A : Type'} (s : nat -> A) (n : nat) : (((@list_of_seq A s n) = (@nil A)) = (n = (NUMERAL 0))) = True.
Proof. exact (TRANS (@lem1237591 A s n) (@lem1237595 n)). Qed.
Lemma lem1237597 {A : Type'} (s : nat -> A) : (term12 A s) = term13.
Proof. exact (fun_ext (fun n : nat => @lem1237596 A s n)). Qed.
Lemma lem1237598 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1237599 {A : Type'} (s : nat -> A) : (term14 A s) = term15.
Proof. exact (MK_COMB (@lem1237598) (@lem1237597 A s)). Qed.
Lemma lem1237601 {A : Type'} (t : Prop) : (term16 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1237602 (t : Prop) : (term17 t) = t.
Proof. exact (@lem1237601 nat t). Qed.
Lemma lem1237603 : term15 = True.
Proof. exact (@lem1237602 True). Qed.
Lemma lem1237604 {A : Type'} (s : nat -> A) : (term14 A s) = True.
Proof. exact (TRANS (@lem1237599 A s) (@lem1237603)). Qed.
Lemma lem1237605 {A : Type'} : (term18 A) = (term19 A).
Proof. exact (fun_ext (fun s : nat -> A => @lem1237604 A s)). Qed.
Lemma lem1237606 {A : Type'} : (@all (nat -> A)) = (@all (nat -> A)).
Proof. exact (eq_refl (@all (nat -> A))). Qed.
Lemma lem1237607 {A : Type'} : (term20 A) = (term21 A).
Proof. exact (MK_COMB (@lem1237606 A) (@lem1237605 A)). Qed.
Lemma lem1237609 {A : Type'} (t : Prop) : (term16 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1237610 {A : Type'} (t : Prop) : (term22 A t) = t.
Proof. exact (@lem1237609 (nat -> A) t). Qed.
Lemma lem1237611 {A : Type'} : (term21 A) = True.
Proof. exact (@lem1237610 A True). Qed.
Lemma lem1237612 {A : Type'} : (term20 A) = True.
Proof. exact (TRANS (@lem1237607 A) (@lem1237611 A)). Qed.
Lemma lem1237613 {A : Type'} : True = (term20 A).
Proof. exact (SYM (@lem1237612 A)). Qed.
Lemma lem1237614 {A : Type'} : term20 A.
Proof. exact (EQ_MP (@lem1237613 A) (@lem0)). Qed.
