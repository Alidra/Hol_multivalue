Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MULT_SYM_term_abbrevs.
Require Import ADD_SYM_spec.
Require Import MULT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem81646 (m : nat) : term0 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem81647 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem81648 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem81647 m) (@lem81646 m)). Qed.
Lemma lem81649 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem81648 m n). Qed.
Lemma lem81650 (n : nat) (m : nat) : (term2 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem81651 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem81650 n m) (@lem81649 m n)). Qed.
Lemma lem81652 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = (((Nat.add m n) = (Nat.add n m)) = True).
Proof. exact (@lem7 ((Nat.add m n) = (Nat.add n m))). Qed.
Lemma lem81655 (P : nat -> Prop) : term3 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem81656 : term4.
Proof. exact (@lem81655 term5). Qed.
Lemma lem81657 : term6 = term7.
Proof. exact (eq_refl term6). Qed.
Lemma lem81658 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem81659 : term8 = term9.
Proof. exact (MK_COMB (@lem81658) (@lem81657)). Qed.
Lemma lem81660 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem81661 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem81662 (m : nat) : (term12 m) = (term13 m).
Proof. exact (MK_COMB (@lem81661) (@lem81660 m)). Qed.
Lemma lem81663 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem81664 (m : nat) : (term16 m) = (term17 m).
Proof. exact (MK_COMB (@lem81662 m) (@lem81663 m)). Qed.
Lemma lem81665 : term18 = term19.
Proof. exact (fun_ext (fun m : nat => @lem81664 m)). Qed.
Lemma lem81666 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem81667 : term20 = term21.
Proof. exact (MK_COMB (@lem81666) (@lem81665)). Qed.
Lemma lem81668 : term22 = term23.
Proof. exact (MK_COMB (@lem81659) (@lem81667)). Qed.
Lemma lem81669 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem81670 : term24 = term25.
Proof. exact (MK_COMB (@lem81669) (@lem81668)). Qed.
Lemma lem81671 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem81672 : term26 = term5.
Proof. exact (fun_ext (fun m : nat => @lem81671 m)). Qed.
Lemma lem81673 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem81674 : term27 = term28.
Proof. exact (MK_COMB (@lem81673) (@lem81672)). Qed.
Lemma lem81675 : term4 = term29.
Proof. exact (MK_COMB (@lem81670) (@lem81674)). Qed.
Lemma lem81676 : term29.
Proof. exact (EQ_MP (@lem81675) (@lem81656)). Qed.
Lemma lem81677 (m : nat) (h1 : term11 m) : term11 m.
Proof. exact (h1). Qed.
Lemma lem81678 : term30.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem81704 : term31.
Proof. exact (proj1 (@lem81678)). Qed.
Lemma lem81705 (m : nat) : term32 m.
Proof. exact (@lem81704 m). Qed.
Lemma lem81706 (m : nat) : (term32 m) = ((term33 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term32 m)). Qed.
Lemma lem81708 : term34.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem81709 (n : nat) : term35 n.
Proof. exact (@lem81708 n). Qed.
Lemma lem81710 (n : nat) : (term35 n) = ((term36 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term35 n)). Qed.
Lemma lem81719 (n : nat) : (term36 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem81710 n) (@lem81709 n)). Qed.
Lemma lem81720 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem81721 (n : nat) : (term37 n) = term38.
Proof. exact (MK_COMB (@lem81720) (@lem81719 n)). Qed.
Lemma lem81723 (m : nat) : (term33 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem81706 m) (@lem81705 m)). Qed.
Lemma lem81724 (n : nat) : (term33 n) = (NUMERAL 0).
Proof. exact (@lem81723 n). Qed.
Lemma lem81725 (n : nat) : ((term36 n) = (term33 n)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem81721 n) (@lem81724 n)). Qed.
Lemma lem81727 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem81728 (x : nat) : (x = x) = True.
Proof. exact (@lem81727 nat x). Qed.
Lemma lem81729 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem81728 (NUMERAL 0)). Qed.
Lemma lem81730 (n : nat) : ((term36 n) = (term33 n)) = True.
Proof. exact (TRANS (@lem81725 n) (@lem81729)). Qed.
Lemma lem81731 : term39 = term40.
Proof. exact (fun_ext (fun n : nat => @lem81730 n)). Qed.
Lemma lem81732 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem81733 : term7 = term41.
Proof. exact (MK_COMB (@lem81732) (@lem81731)). Qed.
Lemma lem81735 {A : Type'} (t : Prop) : (term42 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem81736 (t : Prop) : (term43 t) = t.
Proof. exact (@lem81735 nat t). Qed.
Lemma lem81737 : term41 = True.
Proof. exact (@lem81736 True). Qed.
Lemma lem81738 : term7 = True.
Proof. exact (TRANS (@lem81733) (@lem81737)). Qed.
Lemma lem81739 : True = term7.
Proof. exact (SYM (@lem81738)). Qed.
Lemma lem81740 : term7.
Proof. exact (EQ_MP (@lem81739) (@lem0)). Qed.
Lemma lem81741 : term30.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem81742 : term44.
Proof. exact (proj2 (@lem81741)). Qed.
Lemma lem81743 : term45.
Proof. exact (proj2 (@lem81742)). Qed.
Lemma lem81744 : term46.
Proof. exact (proj2 (@lem81743)). Qed.
Lemma lem81745 : term47.
Proof. exact (proj2 (@lem81744)). Qed.
Lemma lem81746 (m : nat) : term48 m.
Proof. exact (@lem81745 m). Qed.
Lemma lem81747 (m : nat) : (term48 m) = (term49 m).
Proof. exact (eq_refl (term48 m)). Qed.
Lemma lem81748 (m : nat) : term49 m.
Proof. exact (EQ_MP (@lem81747 m) (@lem81746 m)). Qed.
Lemma lem81749 (m : nat) (n : nat) : term50 m n.
Proof. exact (@lem81748 m n). Qed.
Lemma lem81750 (m : nat) (n : nat) : (term50 m n) = ((term51 m n) = (term52 m n)).
Proof. exact (eq_refl (term50 m n)). Qed.
Lemma lem81752 : term53.
Proof. exact (proj1 (@lem81744)). Qed.
Lemma lem81753 (m : nat) : term54 m.
Proof. exact (@lem81752 m). Qed.
Lemma lem81754 (m : nat) : (term54 m) = (term55 m).
Proof. exact (eq_refl (term54 m)). Qed.
Lemma lem81755 (m : nat) : term55 m.
Proof. exact (EQ_MP (@lem81754 m) (@lem81753 m)). Qed.
Lemma lem81756 (m : nat) (n : nat) : term56 m n.
Proof. exact (@lem81755 m n). Qed.
Lemma lem81757 (m : nat) (n : nat) : (term56 m n) = ((term57 m n) = (term58 m n)).
Proof. exact (eq_refl (term56 m n)). Qed.
Lemma lem81775 (n : nat) (m : nat) (h1 : term11 m) : term59 m n.
Proof. exact (@lem81677 m h1 n). Qed.
Lemma lem81776 (n : nat) (m : nat) : (term59 m n) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl (term59 m n)). Qed.
Lemma lem81785 (m : nat) (n : nat) : (term57 m n) = (term58 m n).
Proof. exact (EQ_MP (@lem81757 m n) (@lem81756 m n)). Qed.
Lemma lem81787 (n : nat) (m : nat) (h1 : term11 m) : (Nat.mul m n) = (Nat.mul n m).
Proof. exact (EQ_MP (@lem81776 n m) (@lem81775 n m h1)). Qed.
Lemma lem81788 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem81789 (n : nat) (m : nat) (h1 : term11 m) : (term60 m n) = (term60 n m).
Proof. exact (MK_COMB (@lem81788) (@lem81787 n m h1)). Qed.
Lemma lem81790 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem81791 (n : nat) (m : nat) (h1 : term11 m) : (term58 m n) = (term61 m n).
Proof. exact (MK_COMB (@lem81789 n m h1) (@lem81790 n)). Qed.
Lemma lem81792 (n : nat) (m : nat) (h1 : term11 m) : (term57 m n) = (term61 m n).
Proof. exact (TRANS (@lem81785 m n) (@lem81791 n m h1)). Qed.
Lemma lem81793 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem81794 (n : nat) (m : nat) (h1 : term11 m) : (term62 m n) = (term63 m n).
Proof. exact (MK_COMB (@lem81793) (@lem81792 n m h1)). Qed.
Lemma lem81796 (m : nat) (n : nat) : (term51 m n) = (term52 m n).
Proof. exact (EQ_MP (@lem81750 m n) (@lem81749 m n)). Qed.
Lemma lem81797 (n : nat) (m : nat) : (term51 n m) = (term52 n m).
Proof. exact (@lem81796 n m). Qed.
Lemma lem81798 (n : nat) (m : nat) (h1 : term11 m) : ((term57 m n) = (term51 n m)) = ((term61 m n) = (term52 n m)).
Proof. exact (MK_COMB (@lem81794 n m h1) (@lem81797 n m)). Qed.
Lemma lem81800 (n : nat) (m : nat) : ((Nat.add m n) = (Nat.add n m)) = True.
Proof. exact (EQ_MP (@lem81652 n m) (@lem81651 n m)). Qed.
Lemma lem81801 (n : nat) (m : nat) : ((term61 m n) = (term52 n m)) = True.
Proof. exact (@lem81800 n (Nat.mul n m)). Qed.
Lemma lem81802 (n : nat) (m : nat) (h1 : term11 m) : ((term57 m n) = (term51 n m)) = True.
Proof. exact (TRANS (@lem81798 n m h1) (@lem81801 n m)). Qed.
Lemma lem81803 (m : nat) (h1 : term11 m) : (term64 m) = term40.
Proof. exact (fun_ext (fun n : nat => @lem81802 n m h1)). Qed.
Lemma lem81804 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem81805 (m : nat) (h1 : term11 m) : (term15 m) = term41.
Proof. exact (MK_COMB (@lem81804) (@lem81803 m h1)). Qed.
Lemma lem81807 {A : Type'} (t : Prop) : (term42 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem81808 (t : Prop) : (term43 t) = t.
Proof. exact (@lem81807 nat t). Qed.
Lemma lem81809 : term41 = True.
Proof. exact (@lem81808 True). Qed.
Lemma lem81810 (m : nat) (h1 : term11 m) : (term15 m) = True.
Proof. exact (TRANS (@lem81805 m h1) (@lem81809)). Qed.
Lemma lem81811 (m : nat) (h1 : term11 m) : True = (term15 m).
Proof. exact (SYM (@lem81810 m h1)). Qed.
Lemma lem81812 (m : nat) (h1 : term11 m) : term15 m.
Proof. exact (EQ_MP (@lem81811 m h1) (@lem0)). Qed.
Lemma lem81813 (m : nat) : term17 m.
Proof. exact (fun h0 : term11 m => @lem81812 m h0). Qed.
Lemma lem81818 : term21.
Proof. exact (fun m : nat => @lem81813 m). Qed.
Lemma lem81819 : term23.
Proof. exact (conj (@lem81740) (@lem81818)). Qed.
Lemma lem81820 : term28.
Proof. exact (@lem81676 (@lem81819)). Qed.
