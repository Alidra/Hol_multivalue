Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_NEG_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_MUL_LNEG_spec.
Require Import REAL_MUL_RNEG_spec.
Require Import REAL_NEG_NEG_spec.
Require Import thm0_spec.
Require Import thm124233_spec.
Require Import thm12653_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1344313_spec.
Require Import thm1344314_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Lemma lem1362596 (n : nat) : term0 n.
Proof. exact (@lem9784 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem1362597 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1362598 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem1362597 n) (@lem1362596 n)). Qed.
Lemma lem1362599 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (h1). Qed.
Lemma lem1362600 (n : nat) (h1 : term2 n) : term2 n.
Proof. exact (h1). Qed.
Lemma lem1362602 (P : nat -> Prop) : term3 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1362603 (x : real) : term4 x.
Proof. exact (@lem1362602 (term5 x)). Qed.
Lemma lem1362604 (x : real) : (term6 x) = ((term7 x) = (term8 x)).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem1362605 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1362606 (x : real) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem1362605) (@lem1362604 x)). Qed.
Lemma lem1362607 (x : real) (n : nat) : (term11 x n) = ((term12 x n) = (term13 x n)).
Proof. exact (eq_refl (term11 x n)). Qed.
Lemma lem1362608 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1362609 (x : real) (n : nat) : (term14 x n) = (term15 x n).
Proof. exact (MK_COMB (@lem1362608) (@lem1362607 x n)). Qed.
Lemma lem1362610 (x : real) (n : nat) : (term16 x n) = ((term17 x n) = (term18 x n)).
Proof. exact (eq_refl (term16 x n)). Qed.
Lemma lem1362611 (x : real) (n : nat) : (term19 x n) = (term20 x n).
Proof. exact (MK_COMB (@lem1362609 x n) (@lem1362610 x n)). Qed.
Lemma lem1362612 (x : real) : (term21 x) = (term22 x).
Proof. exact (fun_ext (fun n : nat => @lem1362611 x n)). Qed.
Lemma lem1362613 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1362614 (x : real) : (term23 x) = (term24 x).
Proof. exact (MK_COMB (@lem1362613) (@lem1362612 x)). Qed.
Lemma lem1362615 (x : real) : (term25 x) = (term26 x).
Proof. exact (MK_COMB (@lem1362606 x) (@lem1362614 x)). Qed.
Lemma lem1362616 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1362617 (x : real) : (term27 x) = (term28 x).
Proof. exact (MK_COMB (@lem1362616) (@lem1362615 x)). Qed.
Lemma lem1362618 (x : real) (n : nat) : (term11 x n) = ((term12 x n) = (term13 x n)).
Proof. exact (eq_refl (term11 x n)). Qed.
Lemma lem1362619 (x : real) : (term29 x) = (term5 x).
Proof. exact (fun_ext (fun n : nat => @lem1362618 x n)). Qed.
Lemma lem1362620 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1362621 (x : real) : (term30 x) = (term31 x).
Proof. exact (MK_COMB (@lem1362620) (@lem1362619 x)). Qed.
Lemma lem1362622 (x : real) : (term4 x) = (term32 x).
Proof. exact (MK_COMB (@lem1362617 x) (@lem1362621 x)). Qed.
Lemma lem1362623 (x : real) : term32 x.
Proof. exact (EQ_MP (@lem1362622 x) (@lem1362603 x)). Qed.
Lemma lem1362638 (x : real) : (term33 x) = term34.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1362639 (x : real) : (term7 x) = term34.
Proof. exact (@lem1362638 (real_neg x)). Qed.
Lemma lem1362640 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1362641 (x : real) : (term35 x) = term36.
Proof. exact (MK_COMB (@lem1362640) (@lem1362639 x)). Qed.
Lemma lem1362643 : term37 = True.
Proof. exact (proj1 (@lem124233)). Qed.
Lemma lem1362644 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1362645 : term38 = (@COND real True).
Proof. exact (MK_COMB (@lem1362644) (@lem1362643)). Qed.
Lemma lem1362647 (x : real) : (term33 x) = term34.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1362648 (x : real) : (term39 x) = term40.
Proof. exact (MK_COMB (@lem1362645) (@lem1362647 x)). Qed.
Lemma lem1362650 (x : real) : (term33 x) = term34.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1362651 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1362652 (x : real) : (term41 x) = term42.
Proof. exact (MK_COMB (@lem1362651) (@lem1362650 x)). Qed.
Lemma lem1362653 (x : real) : (term8 x) = term43.
Proof. exact (MK_COMB (@lem1362648 x) (@lem1362652 x)). Qed.
Lemma lem1362655 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1362656 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1362655 real t2 t1). Qed.
Lemma lem1362657 : term43 = term34.
Proof. exact (@lem1362656 term42 term34). Qed.
Lemma lem1362658 (x : real) : (term8 x) = term34.
Proof. exact (TRANS (@lem1362653 x) (@lem1362657)). Qed.
Lemma lem1362659 (x : real) : ((term7 x) = (term8 x)) = (term34 = term34).
Proof. exact (MK_COMB (@lem1362641 x) (@lem1362658 x)). Qed.
Lemma lem1362661 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1362662 (x : real) : (x = x) = True.
Proof. exact (@lem1362661 real x). Qed.
Lemma lem1362663 : (term34 = term34) = True.
Proof. exact (@lem1362662 term34). Qed.
Lemma lem1362664 (x : real) : ((term7 x) = (term8 x)) = True.
Proof. exact (TRANS (@lem1362659 x) (@lem1362663)). Qed.
Lemma lem1362665 (x : real) : True = ((term7 x) = (term8 x)).
Proof. exact (SYM (@lem1362664 x)). Qed.
Lemma lem1362666 (x : real) : (term7 x) = (term8 x).
Proof. exact (EQ_MP (@lem1362665 x) (@lem0)). Qed.
Lemma lem1362667 : term44.
Proof. exact (proj2 (@lem124233)). Qed.
Lemma lem1362668 (n : nat) : term45 n.
Proof. exact (@lem1362667 n). Qed.
Lemma lem1362669 (n : nat) : (term45 n) = ((term46 n) = (term2 n)).
Proof. exact (eq_refl (term45 n)). Qed.
Lemma lem1362672 (x : real) : term47 x.
Proof. exact (EQ_MP (@lem1344314 x) (@lem1344313 x)). Qed.
Lemma lem1362673 (x : real) (n : nat) : term48 x n.
Proof. exact (@lem1362672 x n). Qed.
Lemma lem1362674 (x : real) (n : nat) : (term48 x n) = ((term49 x n) = (term50 x n)).
Proof. exact (eq_refl (term48 x n)). Qed.
Lemma lem1362680 (x : real) (n : nat) : (term49 x n) = (term50 x n).
Proof. exact (EQ_MP (@lem1362674 x n) (@lem1362673 x n)). Qed.
Lemma lem1362681 (x : real) (n : nat) : (term17 x n) = (term51 x n).
Proof. exact (@lem1362680 (real_neg x) n). Qed.
Lemma lem1362683 (x : real) (n : nat) (h1 : (term12 x n) = (term13 x n)) : (term12 x n) = (term13 x n).
Proof. exact (h1). Qed.
Lemma lem1362684 (x : real) : (term52 x) = (term52 x).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem1362685 (x : real) (n : nat) (h1 : (term12 x n) = (term13 x n)) : (term51 x n) = (term53 x n).
Proof. exact (MK_COMB (@lem1362684 x) (@lem1362683 x n h1)). Qed.
Lemma lem1362686 (x : real) (n : nat) (h1 : (term12 x n) = (term13 x n)) : (term17 x n) = (term53 x n).
Proof. exact (TRANS (@lem1362681 x n) (@lem1362685 x n h1)). Qed.
Lemma lem1362687 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1362688 (x : real) (n : nat) (h1 : (term12 x n) = (term13 x n)) : (term54 x n) = (term55 x n).
Proof. exact (MK_COMB (@lem1362687) (@lem1362686 x n h1)). Qed.
Lemma lem1362690 (n : nat) : (term46 n) = (term2 n).
Proof. exact (EQ_MP (@lem1362669 n) (@lem1362668 n)). Qed.
Lemma lem1362691 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1362692 (n : nat) : (term56 n) = (term57 n).
Proof. exact (MK_COMB (@lem1362691) (@lem1362690 n)). Qed.
Lemma lem1362694 (x : real) (n : nat) : (term49 x n) = (term50 x n).
Proof. exact (EQ_MP (@lem1362674 x n) (@lem1362673 x n)). Qed.
Lemma lem1362695 (x : real) (n : nat) : (term58 x n) = (term59 x n).
Proof. exact (MK_COMB (@lem1362692 n) (@lem1362694 x n)). Qed.
Lemma lem1362697 (x : real) (n : nat) : (term49 x n) = (term50 x n).
Proof. exact (EQ_MP (@lem1362674 x n) (@lem1362673 x n)). Qed.
Lemma lem1362698 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1362699 (x : real) (n : nat) : (term60 x n) = (term61 x n).
Proof. exact (MK_COMB (@lem1362698) (@lem1362697 x n)). Qed.
Lemma lem1362700 (x : real) (n : nat) : (term18 x n) = (term62 x n).
Proof. exact (MK_COMB (@lem1362695 x n) (@lem1362699 x n)). Qed.
Lemma lem1362701 (x : real) (n : nat) (h1 : (term12 x n) = (term13 x n)) : ((term17 x n) = (term18 x n)) = ((term53 x n) = (term62 x n)).
Proof. exact (MK_COMB (@lem1362688 x n h1) (@lem1362700 x n)). Qed.
Lemma lem1362704 (x : real) (n : nat) (h1 : (term12 x n) = (term13 x n)) : ((term53 x n) = (term62 x n)) = ((term17 x n) = (term18 x n)).
Proof. exact (SYM (@lem1362701 x n h1)). Qed.
Lemma lem1362708 (x : real) : term63 x.
Proof. exact (@lem1360913 x). Qed.
Lemma lem1362709 (x : real) : (term63 x) = (term64 x).
Proof. exact (eq_refl (term63 x)). Qed.
Lemma lem1362710 (x : real) : term64 x.
Proof. exact (EQ_MP (@lem1362709 x) (@lem1362708 x)). Qed.
Lemma lem1362711 (x : real) (y : real) : term65 x y.
Proof. exact (@lem1362710 x y). Qed.
Lemma lem1362712 (x : real) (y : real) : (term65 x y) = ((term66 x y) = (term67 x y)).
Proof. exact (eq_refl (term65 x y)). Qed.
Lemma lem1362720 (n : nat) : (Coq.Arith.PeanoNat.Nat.Even n) = ((Coq.Arith.PeanoNat.Nat.Even n) = True).
Proof. exact (@lem7 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem1362725 (x : real) (y : real) : (term66 x y) = (term67 x y).
Proof. exact (EQ_MP (@lem1362712 x y) (@lem1362711 x y)). Qed.
Lemma lem1362726 (x : real) (n : nat) : (term53 x n) = (term68 x n).
Proof. exact (@lem1362725 x (term13 x n)). Qed.
Lemma lem1362728 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (Coq.Arith.PeanoNat.Nat.Even n) = True.
Proof. exact (EQ_MP (@lem1362720 n) (@lem1362599 n h1)). Qed.
Lemma lem1362729 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1362730 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term69 n) = (@COND real True).
Proof. exact (MK_COMB (@lem1362729) (@lem1362728 n h1)). Qed.
Lemma lem1362731 (x : real) (n : nat) : (real_pow x n) = (real_pow x n).
Proof. exact (eq_refl (real_pow x n)). Qed.
Lemma lem1362732 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term70 x n) = (term71 x n).
Proof. exact (MK_COMB (@lem1362730 n h1) (@lem1362731 x n)). Qed.
Lemma lem1362733 (x : real) (n : nat) : (term72 x n) = (term72 x n).
Proof. exact (eq_refl (term72 x n)). Qed.
Lemma lem1362734 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term13 x n) = (term73 x n).
Proof. exact (MK_COMB (@lem1362732 x n h1) (@lem1362733 x n)). Qed.
Lemma lem1362736 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1362737 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1362736 real t2 t1). Qed.
Lemma lem1362738 (x : real) (n : nat) : (term73 x n) = (real_pow x n).
Proof. exact (@lem1362737 (term72 x n) (real_pow x n)). Qed.
Lemma lem1362739 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term13 x n) = (real_pow x n).
Proof. exact (TRANS (@lem1362734 x n h1) (@lem1362738 x n)). Qed.
Lemma lem1362740 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1362741 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term74 x n) = (term50 x n).
Proof. exact (MK_COMB (@lem1362740 x) (@lem1362739 x n h1)). Qed.
Lemma lem1362742 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1362743 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term68 x n) = (term61 x n).
Proof. exact (MK_COMB (@lem1362742) (@lem1362741 x n h1)). Qed.
Lemma lem1362744 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term53 x n) = (term61 x n).
Proof. exact (TRANS (@lem1362726 x n) (@lem1362743 x n h1)). Qed.
Lemma lem1362745 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1362746 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term55 x n) = (term75 x n).
Proof. exact (MK_COMB (@lem1362745) (@lem1362744 x n h1)). Qed.
Lemma lem1362748 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (Coq.Arith.PeanoNat.Nat.Even n) = True.
Proof. exact (EQ_MP (@lem1362720 n) (@lem1362599 n h1)). Qed.
Lemma lem1362749 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1362750 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term2 n) = (~ True).
Proof. exact (MK_COMB (@lem1362749) (@lem1362748 n h1)). Qed.
Lemma lem1362752 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1362753 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term2 n) = False.
Proof. exact (TRANS (@lem1362750 n h1) (@lem1362752)). Qed.
Lemma lem1362754 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1362755 (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term57 n) = (@COND real False).
Proof. exact (MK_COMB (@lem1362754) (@lem1362753 n h1)). Qed.
Lemma lem1362756 (x : real) (n : nat) : (term50 x n) = (term50 x n).
Proof. exact (eq_refl (term50 x n)). Qed.
Lemma lem1362757 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term59 x n) = (term76 x n).
Proof. exact (MK_COMB (@lem1362755 n h1) (@lem1362756 x n)). Qed.
Lemma lem1362758 (x : real) (n : nat) : (term61 x n) = (term61 x n).
Proof. exact (eq_refl (term61 x n)). Qed.
Lemma lem1362759 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term62 x n) = (term77 x n).
Proof. exact (MK_COMB (@lem1362757 x n h1) (@lem1362758 x n)). Qed.
Lemma lem1362761 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1362762 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1362761 real t1 t2). Qed.
Lemma lem1362763 (x : real) (n : nat) : (term77 x n) = (term61 x n).
Proof. exact (@lem1362762 (term50 x n) (term61 x n)). Qed.
Lemma lem1362764 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term62 x n) = (term61 x n).
Proof. exact (TRANS (@lem1362759 x n h1) (@lem1362763 x n)). Qed.
Lemma lem1362765 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : ((term53 x n) = (term62 x n)) = ((term61 x n) = (term61 x n)).
Proof. exact (MK_COMB (@lem1362746 x n h1) (@lem1362764 x n h1)). Qed.
Lemma lem1362767 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1362768 (x : real) : (x = x) = True.
Proof. exact (@lem1362767 real x). Qed.
Lemma lem1362769 (x : real) (n : nat) : ((term61 x n) = (term61 x n)) = True.
Proof. exact (@lem1362768 (term61 x n)). Qed.
Lemma lem1362770 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : ((term53 x n) = (term62 x n)) = True.
Proof. exact (TRANS (@lem1362765 x n h1) (@lem1362769 x n)). Qed.
Lemma lem1362771 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : True = ((term53 x n) = (term62 x n)).
Proof. exact (SYM (@lem1362770 x n h1)). Qed.
Lemma lem1362772 (x : real) (n : nat) (h1 : Coq.Arith.PeanoNat.Nat.Even n) : (term53 x n) = (term62 x n).
Proof. exact (EQ_MP (@lem1362771 x n h1) (@lem0)). Qed.
Lemma lem1362773 (x : real) : term78 x.
Proof. exact (@lem1358662 x). Qed.
Lemma lem1362774 (x : real) : (term78 x) = ((term79 x) = x).
Proof. exact (eq_refl (term78 x)). Qed.
Lemma lem1362776 (x : real) : term63 x.
Proof. exact (@lem1360913 x). Qed.
Lemma lem1362777 (x : real) : (term63 x) = (term64 x).
Proof. exact (eq_refl (term63 x)). Qed.
Lemma lem1362778 (x : real) : term64 x.
Proof. exact (EQ_MP (@lem1362777 x) (@lem1362776 x)). Qed.
Lemma lem1362779 (x : real) (y : real) : term65 x y.
Proof. exact (@lem1362778 x y). Qed.
Lemma lem1362780 (x : real) (y : real) : (term65 x y) = ((term66 x y) = (term67 x y)).
Proof. exact (eq_refl (term65 x y)). Qed.
Lemma lem1362782 (x : real) : term80 x.
Proof. exact (@lem1360282 x). Qed.
Lemma lem1362783 (x : real) : (term80 x) = (term81 x).
Proof. exact (eq_refl (term80 x)). Qed.
Lemma lem1362784 (x : real) : term81 x.
Proof. exact (EQ_MP (@lem1362783 x) (@lem1362782 x)). Qed.
Lemma lem1362785 (x : real) (y : real) : term82 x y.
Proof. exact (@lem1362784 x y). Qed.
Lemma lem1362786 (x : real) (y : real) : (term82 x y) = ((term83 x y) = (term67 x y)).
Proof. exact (eq_refl (term82 x y)). Qed.
Lemma lem1362788 (n : nat) : term84 n.
Proof. exact (@lem82 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem1362793 (x : real) (y : real) : (term66 x y) = (term67 x y).
Proof. exact (EQ_MP (@lem1362780 x y) (@lem1362779 x y)). Qed.
Lemma lem1362794 (x : real) (n : nat) : (term53 x n) = (term68 x n).
Proof. exact (@lem1362793 x (term13 x n)). Qed.
Lemma lem1362796 (n : nat) (h1 : term2 n) : (Coq.Arith.PeanoNat.Nat.Even n) = False.
Proof. exact (@lem1362788 n (@lem1362600 n h1)). Qed.
Lemma lem1362797 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1362798 (n : nat) (h1 : term2 n) : (term69 n) = (@COND real False).
Proof. exact (MK_COMB (@lem1362797) (@lem1362796 n h1)). Qed.
Lemma lem1362799 (x : real) (n : nat) : (real_pow x n) = (real_pow x n).
Proof. exact (eq_refl (real_pow x n)). Qed.
Lemma lem1362800 (x : real) (n : nat) (h1 : term2 n) : (term70 x n) = (term85 x n).
Proof. exact (MK_COMB (@lem1362798 n h1) (@lem1362799 x n)). Qed.
Lemma lem1362801 (x : real) (n : nat) : (term72 x n) = (term72 x n).
Proof. exact (eq_refl (term72 x n)). Qed.
Lemma lem1362802 (x : real) (n : nat) (h1 : term2 n) : (term13 x n) = (term86 x n).
Proof. exact (MK_COMB (@lem1362800 x n h1) (@lem1362801 x n)). Qed.
Lemma lem1362804 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1362805 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1362804 real t1 t2). Qed.
Lemma lem1362806 (x : real) (n : nat) : (term86 x n) = (term72 x n).
Proof. exact (@lem1362805 (real_pow x n) (term72 x n)). Qed.
Lemma lem1362807 (x : real) (n : nat) (h1 : term2 n) : (term13 x n) = (term72 x n).
Proof. exact (TRANS (@lem1362802 x n h1) (@lem1362806 x n)). Qed.
Lemma lem1362808 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1362809 (x : real) (n : nat) (h1 : term2 n) : (term74 x n) = (term87 x n).
Proof. exact (MK_COMB (@lem1362808 x) (@lem1362807 x n h1)). Qed.
Lemma lem1362811 (x : real) (y : real) : (term83 x y) = (term67 x y).
Proof. exact (EQ_MP (@lem1362786 x y) (@lem1362785 x y)). Qed.
Lemma lem1362812 (x : real) (n : nat) : (term87 x n) = (term61 x n).
Proof. exact (@lem1362811 x (real_pow x n)). Qed.
Lemma lem1362813 (x : real) (n : nat) (h1 : term2 n) : (term74 x n) = (term61 x n).
Proof. exact (TRANS (@lem1362809 x n h1) (@lem1362812 x n)). Qed.
Lemma lem1362814 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1362815 (x : real) (n : nat) (h1 : term2 n) : (term68 x n) = (term88 x n).
Proof. exact (MK_COMB (@lem1362814) (@lem1362813 x n h1)). Qed.
Lemma lem1362817 (x : real) : (term79 x) = x.
Proof. exact (EQ_MP (@lem1362774 x) (@lem1362773 x)). Qed.
Lemma lem1362818 (x : real) (n : nat) : (term88 x n) = (term50 x n).
Proof. exact (@lem1362817 (term50 x n)). Qed.
Lemma lem1362819 (x : real) (n : nat) (h1 : term2 n) : (term68 x n) = (term50 x n).
Proof. exact (TRANS (@lem1362815 x n h1) (@lem1362818 x n)). Qed.
Lemma lem1362820 (x : real) (n : nat) (h1 : term2 n) : (term53 x n) = (term50 x n).
Proof. exact (TRANS (@lem1362794 x n) (@lem1362819 x n h1)). Qed.
Lemma lem1362821 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1362822 (x : real) (n : nat) (h1 : term2 n) : (term55 x n) = (term89 x n).
Proof. exact (MK_COMB (@lem1362821) (@lem1362820 x n h1)). Qed.
Lemma lem1362824 (n : nat) (h1 : term2 n) : (Coq.Arith.PeanoNat.Nat.Even n) = False.
Proof. exact (@lem1362788 n (@lem1362600 n h1)). Qed.
Lemma lem1362825 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1362826 (n : nat) (h1 : term2 n) : (term2 n) = (~ False).
Proof. exact (MK_COMB (@lem1362825) (@lem1362824 n h1)). Qed.
Lemma lem1362828 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1362829 (n : nat) (h1 : term2 n) : (term2 n) = True.
Proof. exact (TRANS (@lem1362826 n h1) (@lem1362828)). Qed.
Lemma lem1362830 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1362831 (n : nat) (h1 : term2 n) : (term57 n) = (@COND real True).
Proof. exact (MK_COMB (@lem1362830) (@lem1362829 n h1)). Qed.
Lemma lem1362832 (x : real) (n : nat) : (term50 x n) = (term50 x n).
Proof. exact (eq_refl (term50 x n)). Qed.
Lemma lem1362833 (x : real) (n : nat) (h1 : term2 n) : (term59 x n) = (term90 x n).
Proof. exact (MK_COMB (@lem1362831 n h1) (@lem1362832 x n)). Qed.
Lemma lem1362834 (x : real) (n : nat) : (term61 x n) = (term61 x n).
Proof. exact (eq_refl (term61 x n)). Qed.
Lemma lem1362835 (x : real) (n : nat) (h1 : term2 n) : (term62 x n) = (term91 x n).
Proof. exact (MK_COMB (@lem1362833 x n h1) (@lem1362834 x n)). Qed.
Lemma lem1362837 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1362838 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1362837 real t2 t1). Qed.
Lemma lem1362839 (x : real) (n : nat) : (term91 x n) = (term50 x n).
Proof. exact (@lem1362838 (term61 x n) (term50 x n)). Qed.
Lemma lem1362840 (x : real) (n : nat) (h1 : term2 n) : (term62 x n) = (term50 x n).
Proof. exact (TRANS (@lem1362835 x n h1) (@lem1362839 x n)). Qed.
Lemma lem1362841 (x : real) (n : nat) (h1 : term2 n) : ((term53 x n) = (term62 x n)) = ((term50 x n) = (term50 x n)).
Proof. exact (MK_COMB (@lem1362822 x n h1) (@lem1362840 x n h1)). Qed.
Lemma lem1362843 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1362844 (x : real) : (x = x) = True.
Proof. exact (@lem1362843 real x). Qed.
Lemma lem1362845 (x : real) (n : nat) : ((term50 x n) = (term50 x n)) = True.
Proof. exact (@lem1362844 (term50 x n)). Qed.
Lemma lem1362846 (x : real) (n : nat) (h1 : term2 n) : ((term53 x n) = (term62 x n)) = True.
Proof. exact (TRANS (@lem1362841 x n h1) (@lem1362845 x n)). Qed.
Lemma lem1362847 (x : real) (n : nat) (h1 : term2 n) : True = ((term53 x n) = (term62 x n)).
Proof. exact (SYM (@lem1362846 x n h1)). Qed.
Lemma lem1362848 (x : real) (n : nat) (h1 : term2 n) : (term53 x n) = (term62 x n).
Proof. exact (EQ_MP (@lem1362847 x n h1) (@lem0)). Qed.
Lemma lem1362849 (x : real) (n : nat) : (term53 x n) = (term62 x n).
Proof. exact (or_elim (@lem1362598 n) (fun h0 : Coq.Arith.PeanoNat.Nat.Even n => @lem1362772 x n h0) (fun h0 : term2 n => @lem1362848 x n h0)). Qed.
Lemma lem1362850 (x : real) (n : nat) (h1 : (term12 x n) = (term13 x n)) : (term17 x n) = (term18 x n).
Proof. exact (EQ_MP (@lem1362704 x n h1) (@lem1362849 x n)). Qed.
Lemma lem1362851 (x : real) (n : nat) : term20 x n.
Proof. exact (fun h0 : (term12 x n) = (term13 x n) => @lem1362850 x n h0). Qed.
Lemma lem1362856 (x : real) : term24 x.
Proof. exact (fun n : nat => @lem1362851 x n). Qed.
Lemma lem1362857 (x : real) : term26 x.
Proof. exact (conj (@lem1362666 x) (@lem1362856 x)). Qed.
Lemma lem1362858 (x : real) : term31 x.
Proof. exact (@lem1362623 x (@lem1362857 x)). Qed.
Lemma lem1362863 : term92.
Proof. exact (fun x : real => @lem1362858 x). Qed.
