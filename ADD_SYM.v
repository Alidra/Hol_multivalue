Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ADD_SYM_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem77631 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem77632 : term1.
Proof. exact (@lem77631 term2). Qed.
Lemma lem77633 : term3 = term4.
Proof. exact (eq_refl term3). Qed.
Lemma lem77634 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem77635 : term5 = term6.
Proof. exact (MK_COMB (@lem77634) (@lem77633)). Qed.
Lemma lem77636 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem77637 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem77638 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem77637) (@lem77636 m)). Qed.
Lemma lem77639 (m : nat) : (term11 m) = (term12 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem77640 (m : nat) : (term13 m) = (term14 m).
Proof. exact (MK_COMB (@lem77638 m) (@lem77639 m)). Qed.
Lemma lem77641 : term15 = term16.
Proof. exact (fun_ext (fun m : nat => @lem77640 m)). Qed.
Lemma lem77642 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem77643 : term17 = term18.
Proof. exact (MK_COMB (@lem77642) (@lem77641)). Qed.
Lemma lem77644 : term19 = term20.
Proof. exact (MK_COMB (@lem77635) (@lem77643)). Qed.
Lemma lem77645 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem77646 : term21 = term22.
Proof. exact (MK_COMB (@lem77645) (@lem77644)). Qed.
Lemma lem77647 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem77648 : term23 = term2.
Proof. exact (fun_ext (fun m : nat => @lem77647 m)). Qed.
Lemma lem77649 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem77650 : term24 = term25.
Proof. exact (MK_COMB (@lem77649) (@lem77648)). Qed.
Lemma lem77651 : term1 = term26.
Proof. exact (MK_COMB (@lem77646) (@lem77650)). Qed.
Lemma lem77652 : term26.
Proof. exact (EQ_MP (@lem77651) (@lem77632)). Qed.
Lemma lem77653 (m : nat) (h1 : term8 m) : term8 m.
Proof. exact (h1). Qed.
Lemma lem77654 : term27.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem77670 : term28.
Proof. exact (proj1 (@lem77654)). Qed.
Lemma lem77671 (m : nat) : term29 m.
Proof. exact (@lem77670 m). Qed.
Lemma lem77672 (m : nat) : (term29 m) = ((term30 m) = m).
Proof. exact (eq_refl (term29 m)). Qed.
Lemma lem77674 : term31.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem77675 (n : nat) : term32 n.
Proof. exact (@lem77674 n). Qed.
Lemma lem77676 (n : nat) : (term32 n) = ((term33 n) = n).
Proof. exact (eq_refl (term32 n)). Qed.
Lemma lem77685 (n : nat) : (term33 n) = n.
Proof. exact (EQ_MP (@lem77676 n) (@lem77675 n)). Qed.
Lemma lem77686 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem77687 (n : nat) : (term34 n) = (@eq nat n).
Proof. exact (MK_COMB (@lem77686) (@lem77685 n)). Qed.
Lemma lem77689 (m : nat) : (term30 m) = m.
Proof. exact (EQ_MP (@lem77672 m) (@lem77671 m)). Qed.
Lemma lem77690 (n : nat) : (term30 n) = n.
Proof. exact (@lem77689 n). Qed.
Lemma lem77691 (n : nat) : ((term33 n) = (term30 n)) = (n = n).
Proof. exact (MK_COMB (@lem77687 n) (@lem77690 n)). Qed.
Lemma lem77693 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem77694 (x : nat) : (x = x) = True.
Proof. exact (@lem77693 nat x). Qed.
Lemma lem77695 (n : nat) : (n = n) = True.
Proof. exact (@lem77694 n). Qed.
Lemma lem77696 (n : nat) : ((term33 n) = (term30 n)) = True.
Proof. exact (TRANS (@lem77691 n) (@lem77695 n)). Qed.
Lemma lem77697 : term35 = term36.
Proof. exact (fun_ext (fun n : nat => @lem77696 n)). Qed.
Lemma lem77698 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem77699 : term4 = term37.
Proof. exact (MK_COMB (@lem77698) (@lem77697)). Qed.
Lemma lem77701 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem77702 (t : Prop) : (term39 t) = t.
Proof. exact (@lem77701 nat t). Qed.
Lemma lem77703 : term37 = True.
Proof. exact (@lem77702 True). Qed.
Lemma lem77704 : term4 = True.
Proof. exact (TRANS (@lem77699) (@lem77703)). Qed.
Lemma lem77705 : True = term4.
Proof. exact (SYM (@lem77704)). Qed.
Lemma lem77706 : term4.
Proof. exact (EQ_MP (@lem77705) (@lem0)). Qed.
Lemma lem77707 : term27.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem77708 : term40.
Proof. exact (proj2 (@lem77707)). Qed.
Lemma lem77709 : term41.
Proof. exact (proj2 (@lem77708)). Qed.
Lemma lem77710 (m : nat) : term42 m.
Proof. exact (@lem77709 m). Qed.
Lemma lem77711 (m : nat) : (term42 m) = (term43 m).
Proof. exact (eq_refl (term42 m)). Qed.
Lemma lem77712 (m : nat) : term43 m.
Proof. exact (EQ_MP (@lem77711 m) (@lem77710 m)). Qed.
Lemma lem77713 (m : nat) (n : nat) : term44 m n.
Proof. exact (@lem77712 m n). Qed.
Lemma lem77714 (m : nat) (n : nat) : (term44 m n) = ((term45 m n) = (term46 m n)).
Proof. exact (eq_refl (term44 m n)). Qed.
Lemma lem77716 : term47.
Proof. exact (proj1 (@lem77708)). Qed.
Lemma lem77717 (m : nat) : term48 m.
Proof. exact (@lem77716 m). Qed.
Lemma lem77718 (m : nat) : (term48 m) = (term49 m).
Proof. exact (eq_refl (term48 m)). Qed.
Lemma lem77719 (m : nat) : term49 m.
Proof. exact (EQ_MP (@lem77718 m) (@lem77717 m)). Qed.
Lemma lem77720 (m : nat) (n : nat) : term50 m n.
Proof. exact (@lem77719 m n). Qed.
Lemma lem77721 (m : nat) (n : nat) : (term50 m n) = ((term51 m n) = (term46 m n)).
Proof. exact (eq_refl (term50 m n)). Qed.
Lemma lem77731 (n : nat) (m : nat) (h1 : term8 m) : term52 m n.
Proof. exact (@lem77653 m h1 n). Qed.
Lemma lem77732 (n : nat) (m : nat) : (term52 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term52 m n)). Qed.
Lemma lem77741 (m : nat) (n : nat) : (term51 m n) = (term46 m n).
Proof. exact (EQ_MP (@lem77721 m n) (@lem77720 m n)). Qed.
Lemma lem77743 (n : nat) (m : nat) (h1 : term8 m) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem77732 n m) (@lem77731 n m h1)). Qed.
Lemma lem77744 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem77745 (n : nat) (m : nat) (h1 : term8 m) : (term46 m n) = (term46 n m).
Proof. exact (MK_COMB (@lem77744) (@lem77743 n m h1)). Qed.
Lemma lem77746 (n : nat) (m : nat) (h1 : term8 m) : (term51 m n) = (term46 n m).
Proof. exact (TRANS (@lem77741 m n) (@lem77745 n m h1)). Qed.
Lemma lem77747 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem77748 (n : nat) (m : nat) (h1 : term8 m) : (term53 m n) = (term54 n m).
Proof. exact (MK_COMB (@lem77747) (@lem77746 n m h1)). Qed.
Lemma lem77750 (m : nat) (n : nat) : (term45 m n) = (term46 m n).
Proof. exact (EQ_MP (@lem77714 m n) (@lem77713 m n)). Qed.
Lemma lem77751 (n : nat) (m : nat) : (term45 n m) = (term46 n m).
Proof. exact (@lem77750 n m). Qed.
Lemma lem77752 (n : nat) (m : nat) (h1 : term8 m) : ((term51 m n) = (term45 n m)) = ((term46 n m) = (term46 n m)).
Proof. exact (MK_COMB (@lem77748 n m h1) (@lem77751 n m)). Qed.
Lemma lem77754 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem77755 (x : nat) : (x = x) = True.
Proof. exact (@lem77754 nat x). Qed.
Lemma lem77756 (n : nat) (m : nat) : ((term46 n m) = (term46 n m)) = True.
Proof. exact (@lem77755 (term46 n m)). Qed.
Lemma lem77757 (n : nat) (m : nat) (h1 : term8 m) : ((term51 m n) = (term45 n m)) = True.
Proof. exact (TRANS (@lem77752 n m h1) (@lem77756 n m)). Qed.
Lemma lem77758 (m : nat) (h1 : term8 m) : (term55 m) = term36.
Proof. exact (fun_ext (fun n : nat => @lem77757 n m h1)). Qed.
Lemma lem77759 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem77760 (m : nat) (h1 : term8 m) : (term12 m) = term37.
Proof. exact (MK_COMB (@lem77759) (@lem77758 m h1)). Qed.
Lemma lem77762 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem77763 (t : Prop) : (term39 t) = t.
Proof. exact (@lem77762 nat t). Qed.
Lemma lem77764 : term37 = True.
Proof. exact (@lem77763 True). Qed.
Lemma lem77765 (m : nat) (h1 : term8 m) : (term12 m) = True.
Proof. exact (TRANS (@lem77760 m h1) (@lem77764)). Qed.
Lemma lem77766 (m : nat) (h1 : term8 m) : True = (term12 m).
Proof. exact (SYM (@lem77765 m h1)). Qed.
Lemma lem77767 (m : nat) (h1 : term8 m) : term12 m.
Proof. exact (EQ_MP (@lem77766 m h1) (@lem0)). Qed.
Lemma lem77768 (m : nat) : term14 m.
Proof. exact (fun h0 : term8 m => @lem77767 m h0). Qed.
Lemma lem77773 : term18.
Proof. exact (fun m : nat => @lem77768 m). Qed.
Lemma lem77774 : term20.
Proof. exact (conj (@lem77706) (@lem77773)). Qed.
Lemma lem77775 : term25.
Proof. exact (@lem77652 (@lem77774)). Qed.
