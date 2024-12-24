Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1251039_term_abbrevs.
Require Import ADD_AC_spec.
Require Import thm0_spec.
Require Import thm272789_spec.
Require Import thm272790_spec.
Require Import thm272791_spec.
Require Import thm272793_spec.
Lemma lem1250725 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1250726 (x : nat) : (x = x) = True.
Proof. exact (@lem1250725 nat x). Qed.
Lemma lem1250727 (n : nat) : (n = n) = True.
Proof. exact (@lem1250726 n). Qed.
Lemma lem1250728 (n : nat) : True = (n = n).
Proof. exact (SYM (@lem1250727 n)). Qed.
Lemma lem1250729 (n : nat) : n = n.
Proof. exact (EQ_MP (@lem1250728 n) (@lem0)). Qed.
Lemma lem1250733 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1250734 (n : nat) (d' : nat) (d''' : nat) (d'' : nat) : (term2 n d' d''' d'') = (term3 n d' d''' d'').
Proof. exact (@lem1250733 (Nat.add n d') (term4 d' d'' d''') d''). Qed.
Lemma lem1250736 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1250737 (n : nat) (d' : nat) (d''' : nat) (d'' : nat) : (term3 n d' d''' d'') = (term5 n d' d''' d'').
Proof. exact (@lem1250736 n d' (term6 d' d''' d'')). Qed.
Lemma lem1250739 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250740 (n : nat) (d' : nat) (d''' : nat) (d'' : nat) : (term5 n d' d''' d'') = (term7 n d' d''' d'').
Proof. exact (@lem1250739 d' n (term6 d' d''' d'')). Qed.
Lemma lem1250747 (n : nat) (d' : nat) (d''' : nat) (d'' : nat) : (term3 n d' d''' d'') = (term7 n d' d''' d'').
Proof. exact (TRANS (@lem1250737 n d' d''' d'') (@lem1250740 n d' d''' d'')). Qed.
Lemma lem1250748 (n : nat) (d' : nat) (d''' : nat) (d'' : nat) : (term2 n d' d''' d'') = (term7 n d' d''' d'').
Proof. exact (TRANS (@lem1250734 n d' d''' d'') (@lem1250747 n d' d''' d'')). Qed.
Lemma lem1250756 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1250757 (d' : nat) (d''' : nat) (d'' : nat) : (term6 d' d''' d'') = (term8 d' d''' d'').
Proof. exact (@lem1250756 (Nat.add d' d'') (S d''') d''). Qed.
Lemma lem1250759 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1250760 (d' : nat) (d''' : nat) (d'' : nat) : (term8 d' d''' d'') = (term9 d' d''' d'').
Proof. exact (@lem1250759 d' d'' (term10 d''' d'')). Qed.
Lemma lem1250767 (d' : nat) (d''' : nat) (d'' : nat) : (term6 d' d''' d'') = (term9 d' d''' d'').
Proof. exact (TRANS (@lem1250757 d' d''' d'') (@lem1250760 d' d''' d'')). Qed.
Lemma lem1250775 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1250776 (d'' : nat) (d''' : nat) : (term10 d''' d'') = (term11 d'' d''').
Proof. exact (@lem1250775 d'' (S d''')). Qed.
Lemma lem1250780 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1250781 (d'' : nat) (d''' : nat) : (term12 d''' d'') = (term13 d'' d''').
Proof. exact (MK_COMB (@lem1250780 d'') (@lem1250776 d'' d''')). Qed.
Lemma lem1250788 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1250789 (d' : nat) (d'' : nat) (d''' : nat) : (term9 d' d''' d'') = (term14 d' d'' d''').
Proof. exact (MK_COMB (@lem1250788 d') (@lem1250781 d'' d''')). Qed.
Lemma lem1250796 (d' : nat) (d'' : nat) (d''' : nat) : (term6 d' d''' d'') = (term14 d' d'' d''').
Proof. exact (TRANS (@lem1250767 d' d''' d'') (@lem1250789 d' d'' d''')). Qed.
Lemma lem1250797 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem1250798 (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term15 n d' d''' d'') = (term16 n d' d'' d''').
Proof. exact (MK_COMB (@lem1250797 n) (@lem1250796 d' d'' d''')). Qed.
Lemma lem1250800 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250801 (d' : nat) (n : nat) (d'' : nat) (d''' : nat) : (term16 n d' d'' d''') = (term16 d' n d'' d''').
Proof. exact (@lem1250800 d' n (term13 d'' d''')). Qed.
Lemma lem1250809 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250810 (n : nat) (d'' : nat) (d''' : nat) : (term14 n d'' d''') = (term17 n d'' d''').
Proof. exact (@lem1250809 d'' n (term11 d'' d''')). Qed.
Lemma lem1250818 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250819 (d'' : nat) (n : nat) (d''' : nat) : (term18 n d'' d''') = (term18 d'' n d''').
Proof. exact (@lem1250818 d'' n (S d''')). Qed.
Lemma lem1250829 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1250830 (d'' : nat) (n : nat) (d''' : nat) : (term17 n d'' d''') = (term19 d'' n d''').
Proof. exact (MK_COMB (@lem1250829 d'') (@lem1250819 d'' n d''')). Qed.
Lemma lem1250837 (d'' : nat) (n : nat) (d''' : nat) : (term14 n d'' d''') = (term19 d'' n d''').
Proof. exact (TRANS (@lem1250810 n d'' d''') (@lem1250830 d'' n d''')). Qed.
Lemma lem1250838 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1250839 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term16 d' n d'' d''') = (term20 d' d'' n d''').
Proof. exact (MK_COMB (@lem1250838 d') (@lem1250837 d'' n d''')). Qed.
Lemma lem1250846 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term16 n d' d'' d''') = (term20 d' d'' n d''').
Proof. exact (TRANS (@lem1250801 d' n d'' d''') (@lem1250839 d' d'' n d''')). Qed.
Lemma lem1250847 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term15 n d' d''' d'') = (term20 d' d'' n d''').
Proof. exact (TRANS (@lem1250798 n d' d'' d''') (@lem1250846 d' d'' n d''')). Qed.
Lemma lem1250848 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1250849 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term7 n d' d''' d'') = (term21 d' d'' n d''').
Proof. exact (MK_COMB (@lem1250848 d') (@lem1250847 d' d'' n d''')). Qed.
Lemma lem1250856 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term2 n d' d''' d'') = (term21 d' d'' n d''').
Proof. exact (TRANS (@lem1250748 n d' d''' d'') (@lem1250849 d' d'' n d''')). Qed.
Lemma lem1250857 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1250858 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term22 n d' d''' d'') = (term23 d' d'' n d''').
Proof. exact (MK_COMB (@lem1250857) (@lem1250856 d' d'' n d''')). Qed.
Lemma lem1250860 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250861 (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term24 n d'' d' d''') = (term25 n d'' d' d''').
Proof. exact (@lem1250860 d'' n (term14 d'' d' d''')). Qed.
Lemma lem1250869 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250870 (d'' : nat) (n : nat) (d' : nat) (d''' : nat) : (term16 n d'' d' d''') = (term16 d'' n d' d''').
Proof. exact (@lem1250869 d'' n (term13 d' d''')). Qed.
Lemma lem1250878 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250879 (n : nat) (d' : nat) (d''' : nat) : (term14 n d' d''') = (term17 n d' d''').
Proof. exact (@lem1250878 d' n (term11 d' d''')). Qed.
Lemma lem1250887 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250888 (d' : nat) (n : nat) (d''' : nat) : (term18 n d' d''') = (term18 d' n d''').
Proof. exact (@lem1250887 d' n (S d''')). Qed.
Lemma lem1250898 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1250899 (d' : nat) (n : nat) (d''' : nat) : (term17 n d' d''') = (term19 d' n d''').
Proof. exact (MK_COMB (@lem1250898 d') (@lem1250888 d' n d''')). Qed.
Lemma lem1250906 (d' : nat) (n : nat) (d''' : nat) : (term14 n d' d''') = (term19 d' n d''').
Proof. exact (TRANS (@lem1250879 n d' d''') (@lem1250899 d' n d''')). Qed.
Lemma lem1250907 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1250908 (d'' : nat) (d' : nat) (n : nat) (d''' : nat) : (term16 d'' n d' d''') = (term20 d'' d' n d''').
Proof. exact (MK_COMB (@lem1250907 d'') (@lem1250906 d' n d''')). Qed.
Lemma lem1250910 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250911 (d'' : nat) (d' : nat) (n : nat) (d''' : nat) : (term20 d'' d' n d''') = (term26 d'' d' n d''').
Proof. exact (@lem1250910 d' d'' (term18 d' n d''')). Qed.
Lemma lem1250919 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250920 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term27 d'' d' n d''') = (term27 d' d'' n d''').
Proof. exact (@lem1250919 d' d'' (term11 n d''')). Qed.
Lemma lem1250936 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1250937 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term26 d'' d' n d''') = (term28 d' d'' n d''').
Proof. exact (MK_COMB (@lem1250936 d') (@lem1250920 d' d'' n d''')). Qed.
Lemma lem1250944 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term20 d'' d' n d''') = (term28 d' d'' n d''').
Proof. exact (TRANS (@lem1250911 d'' d' n d''') (@lem1250937 d' d'' n d''')). Qed.
Lemma lem1250945 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term16 d'' n d' d''') = (term28 d' d'' n d''').
Proof. exact (TRANS (@lem1250908 d'' d' n d''') (@lem1250944 d' d'' n d''')). Qed.
Lemma lem1250946 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term16 n d'' d' d''') = (term28 d' d'' n d''').
Proof. exact (TRANS (@lem1250870 d'' n d' d''') (@lem1250945 d' d'' n d''')). Qed.
Lemma lem1250947 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1250948 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term25 n d'' d' d''') = (term29 d' d'' n d''').
Proof. exact (MK_COMB (@lem1250947 d'') (@lem1250946 d' d'' n d''')). Qed.
Lemma lem1250950 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250951 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term29 d' d'' n d''') = (term30 d' d'' n d''').
Proof. exact (@lem1250950 d' d'' (term27 d' d'' n d''')). Qed.
Lemma lem1250959 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1250960 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term26 d' d'' n d''') = (term20 d' d'' n d''').
Proof. exact (@lem1250959 d' d'' (term18 d'' n d''')). Qed.
Lemma lem1250982 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1250983 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term30 d' d'' n d''') = (term21 d' d'' n d''').
Proof. exact (MK_COMB (@lem1250982 d') (@lem1250960 d' d'' n d''')). Qed.
Lemma lem1250990 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term29 d' d'' n d''') = (term21 d' d'' n d''').
Proof. exact (TRANS (@lem1250951 d' d'' n d''') (@lem1250983 d' d'' n d''')). Qed.
Lemma lem1250991 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term25 n d'' d' d''') = (term21 d' d'' n d''').
Proof. exact (TRANS (@lem1250948 d' d'' n d''') (@lem1250990 d' d'' n d''')). Qed.
Lemma lem1250992 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term24 n d'' d' d''') = (term21 d' d'' n d''').
Proof. exact (TRANS (@lem1250861 n d'' d' d''') (@lem1250991 d' d'' n d''')). Qed.
Lemma lem1250993 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : ((term2 n d' d''' d'') = (term24 n d'' d' d''')) = ((term21 d' d'' n d''') = (term21 d' d'' n d''')).
Proof. exact (MK_COMB (@lem1250858 d' d'' n d''') (@lem1250992 d' d'' n d''')). Qed.
Lemma lem1250995 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1250996 (x : nat) : (x = x) = True.
Proof. exact (@lem1250995 nat x). Qed.
Lemma lem1250997 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : ((term21 d' d'' n d''') = (term21 d' d'' n d''')) = True.
Proof. exact (@lem1250996 (term21 d' d'' n d''')). Qed.
Lemma lem1250998 (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term2 n d' d''' d'') = (term24 n d'' d' d''')) = True.
Proof. exact (TRANS (@lem1250993 d' d'' n d''') (@lem1250997 d' d'' n d''')). Qed.
Lemma lem1250999 (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : True = ((term2 n d' d''' d'') = (term24 n d'' d' d''')).
Proof. exact (SYM (@lem1250998 n d'' d' d''')). Qed.
Lemma lem1251000 (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term2 n d' d''' d'') = (term24 n d'' d' d''').
Proof. exact (EQ_MP (@lem1250999 n d'' d' d''') (@lem0)). Qed.
Lemma lem1251001 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1251002 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (MK_COMB (@lem1251001) (@lem1250729 n)). Qed.
Lemma lem1251003 (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (n = (term2 n d' d''' d'')) = (n = (term24 n d'' d' d''')).
Proof. exact (MK_COMB (@lem1251002 n) (@lem1251000 n d'' d' d''')). Qed.
Lemma lem1251004 (m : nat) : term31 m.
Proof. exact (@lem272789 m). Qed.
Lemma lem1251005 (m : nat) : (term31 m) = (term32 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem1251006 (m : nat) : term32 m.
Proof. exact (EQ_MP (@lem1251005 m) (@lem1251004 m)). Qed.
Lemma lem1251007 (m : nat) (n : nat) : term33 m n.
Proof. exact (@lem1251006 m n). Qed.
Lemma lem1251008 (m : nat) (n : nat) : (term33 m n) = ((m = (Nat.add m n)) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem1251026 (m : nat) (n : nat) : (m = (Nat.add m n)) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1251008 m n) (@lem1251007 m n)). Qed.
Lemma lem1251031 (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (n = (term24 n d'' d' d''')) = ((term34 d'' d' d''') = (NUMERAL 0)).
Proof. exact (@lem1251026 n (term34 d'' d' d''')). Qed.
Lemma lem1251032 (n : nat) (d' : nat) (d''' : nat) (d'' : nat) : (term35 n d' d''' d'') = (term35 n d' d''' d'').
Proof. exact (eq_refl (term35 n d' d''' d'')). Qed.
Lemma lem1251033 (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((n = (term2 n d' d''' d'')) = (n = (term24 n d'' d' d'''))) = ((n = (term2 n d' d''' d'')) = ((term34 d'' d' d''') = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1251032 n d' d''' d'') (@lem1251031 n d'' d' d''')). Qed.
Lemma lem1251034 (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (n = (term2 n d' d''' d'')) = ((term34 d'' d' d''') = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1251033 n d'' d' d''') (@lem1251003 n d'' d' d''')). Qed.
Lemma lem1251035 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1251036 (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term36 n d' d''' d'') = (term37 d'' d' d''').
Proof. exact (MK_COMB (@lem1251035) (@lem1251034 n d'' d' d''')). Qed.
Lemma lem1251037 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1251038 (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term38 n d' d''' d'') = (term39 d'' d' d''').
Proof. exact (MK_COMB (@lem1251036 n d'' d' d''') (@lem1251037)). Qed.
Lemma lem1251039 (n : nat) (d' : nat) (d''' : nat) (d'' : nat) : (term39 d'' d' d''') = (term38 n d' d''' d'').
Proof. exact (SYM (@lem1251038 n d'' d' d''')). Qed.
