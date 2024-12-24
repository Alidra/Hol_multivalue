Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NOT_ODD_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm124233_spec.
Require Import thm124616_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem124717 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem124718 : term1.
Proof. exact (@lem124717 term2). Qed.
Lemma lem124719 : term3 = (term4 = term5).
Proof. exact (eq_refl term3). Qed.
Lemma lem124720 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem124721 : term6 = term7.
Proof. exact (MK_COMB (@lem124720) (@lem124719)). Qed.
Lemma lem124722 (n : nat) : (term8 n) = ((term9 n) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem124723 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem124724 (n : nat) : (term10 n) = (term11 n).
Proof. exact (MK_COMB (@lem124723) (@lem124722 n)). Qed.
Lemma lem124725 (n : nat) : (term12 n) = ((term13 n) = (term14 n)).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem124726 (n : nat) : (term15 n) = (term16 n).
Proof. exact (MK_COMB (@lem124724 n) (@lem124725 n)). Qed.
Lemma lem124727 : term17 = term18.
Proof. exact (fun_ext (fun n : nat => @lem124726 n)). Qed.
Lemma lem124728 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem124729 : term19 = term20.
Proof. exact (MK_COMB (@lem124728) (@lem124727)). Qed.
Lemma lem124730 : term21 = term22.
Proof. exact (MK_COMB (@lem124721) (@lem124729)). Qed.
Lemma lem124731 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem124732 : term23 = term24.
Proof. exact (MK_COMB (@lem124731) (@lem124730)). Qed.
Lemma lem124733 (n : nat) : (term8 n) = ((term9 n) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem124734 : term25 = term2.
Proof. exact (fun_ext (fun n : nat => @lem124733 n)). Qed.
Lemma lem124735 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem124736 : term26 = term27.
Proof. exact (MK_COMB (@lem124735) (@lem124734)). Qed.
Lemma lem124737 : term1 = term28.
Proof. exact (MK_COMB (@lem124732) (@lem124736)). Qed.
Lemma lem124738 : term28.
Proof. exact (EQ_MP (@lem124737) (@lem124718)). Qed.
Lemma lem124753 : term29 = False.
Proof. exact (proj1 (@lem124616)). Qed.
Lemma lem124754 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem124755 : term4 = (~ False).
Proof. exact (MK_COMB (@lem124754) (@lem124753)). Qed.
Lemma lem124757 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem124758 : term4 = True.
Proof. exact (TRANS (@lem124755) (@lem124757)). Qed.
Lemma lem124759 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem124760 : term30 = (@eq Prop True).
Proof. exact (MK_COMB (@lem124759) (@lem124758)). Qed.
Lemma lem124762 : term5 = True.
Proof. exact (proj1 (@lem124233)). Qed.
Lemma lem124763 : (term4 = term5) = (True = True).
Proof. exact (MK_COMB (@lem124760) (@lem124762)). Qed.
Lemma lem124765 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem124766 : (True = True) = True.
Proof. exact (@lem124765 True). Qed.
Lemma lem124767 : (term4 = term5) = True.
Proof. exact (TRANS (@lem124763) (@lem124766)). Qed.
Lemma lem124768 : True = (term4 = term5).
Proof. exact (SYM (@lem124767)). Qed.
Lemma lem124769 : term4 = term5.
Proof. exact (EQ_MP (@lem124768) (@lem0)). Qed.
Lemma lem124770 : term31.
Proof. exact (proj2 (@lem124616)). Qed.
Lemma lem124771 (n : nat) : term32 n.
Proof. exact (@lem124770 n). Qed.
Lemma lem124772 (n : nat) : (term32 n) = ((term33 n) = (term9 n)).
Proof. exact (eq_refl (term32 n)). Qed.
Lemma lem124775 : term34.
Proof. exact (proj2 (@lem124233)). Qed.
Lemma lem124776 (n : nat) : term35 n.
Proof. exact (@lem124775 n). Qed.
Lemma lem124777 (n : nat) : (term35 n) = ((term14 n) = (term36 n)).
Proof. exact (eq_refl (term35 n)). Qed.
Lemma lem124783 (n : nat) : (term33 n) = (term9 n).
Proof. exact (EQ_MP (@lem124772 n) (@lem124771 n)). Qed.
Lemma lem124785 (n : nat) (h1 : (term9 n) = (Coq.Arith.PeanoNat.Nat.Even n)) : (term9 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (h1). Qed.
Lemma lem124786 (n : nat) (h1 : (term9 n) = (Coq.Arith.PeanoNat.Nat.Even n)) : (term33 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (TRANS (@lem124783 n) (@lem124785 n h1)). Qed.
Lemma lem124787 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem124788 (n : nat) (h1 : (term9 n) = (Coq.Arith.PeanoNat.Nat.Even n)) : (term13 n) = (term36 n).
Proof. exact (MK_COMB (@lem124787) (@lem124786 n h1)). Qed.
Lemma lem124789 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem124790 (n : nat) (h1 : (term9 n) = (Coq.Arith.PeanoNat.Nat.Even n)) : (term37 n) = (term38 n).
Proof. exact (MK_COMB (@lem124789) (@lem124788 n h1)). Qed.
Lemma lem124792 (n : nat) : (term14 n) = (term36 n).
Proof. exact (EQ_MP (@lem124777 n) (@lem124776 n)). Qed.
Lemma lem124793 (n : nat) (h1 : (term9 n) = (Coq.Arith.PeanoNat.Nat.Even n)) : ((term13 n) = (term14 n)) = ((term36 n) = (term36 n)).
Proof. exact (MK_COMB (@lem124790 n h1) (@lem124792 n)). Qed.
Lemma lem124795 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem124796 (x : Prop) : (x = x) = True.
Proof. exact (@lem124795 Prop x). Qed.
Lemma lem124797 (n : nat) : ((term36 n) = (term36 n)) = True.
Proof. exact (@lem124796 (term36 n)). Qed.
Lemma lem124798 (n : nat) (h1 : (term9 n) = (Coq.Arith.PeanoNat.Nat.Even n)) : ((term13 n) = (term14 n)) = True.
Proof. exact (TRANS (@lem124793 n h1) (@lem124797 n)). Qed.
Lemma lem124799 (n : nat) (h1 : (term9 n) = (Coq.Arith.PeanoNat.Nat.Even n)) : True = ((term13 n) = (term14 n)).
Proof. exact (SYM (@lem124798 n h1)). Qed.
Lemma lem124800 (n : nat) (h1 : (term9 n) = (Coq.Arith.PeanoNat.Nat.Even n)) : (term13 n) = (term14 n).
Proof. exact (EQ_MP (@lem124799 n h1) (@lem0)). Qed.
Lemma lem124801 (n : nat) : term16 n.
Proof. exact (fun h0 : (term9 n) = (Coq.Arith.PeanoNat.Nat.Even n) => @lem124800 n h0). Qed.
Lemma lem124806 : term20.
Proof. exact (fun n : nat => @lem124801 n). Qed.
Lemma lem124807 : term22.
Proof. exact (conj (@lem124769) (@lem124806)). Qed.
Lemma lem124808 : term27.
Proof. exact (@lem124738 (@lem124807)). Qed.
