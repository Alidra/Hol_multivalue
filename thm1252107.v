Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1252107_term_abbrevs.
Require Import ADD_AC_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import thm0_spec.
Require Import thm272789_spec.
Require Import thm272790_spec.
Require Import thm272791_spec.
Require Import thm272793_spec.
Lemma lem1251723 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1251724 (p : nat) (d' : nat) (q : nat) (d'' : nat) : (term2 p d' q d'') = (term3 p d' q d'').
Proof. exact (@lem1251723 p d' (Nat.add q d'')). Qed.
Lemma lem1251726 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251727 (d' : nat) (p : nat) (q : nat) (d'' : nat) : (term3 p d' q d'') = (term3 d' p q d'').
Proof. exact (@lem1251726 d' p (Nat.add q d'')). Qed.
Lemma lem1251734 (d' : nat) (p : nat) (q : nat) (d'' : nat) : (term2 p d' q d'') = (term3 d' p q d'').
Proof. exact (TRANS (@lem1251724 p d' q d'') (@lem1251727 d' p q d'')). Qed.
Lemma lem1251742 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1251743 (d'' : nat) (q : nat) : (Nat.add q d'') = (Nat.add d'' q).
Proof. exact (@lem1251742 d'' q). Qed.
Lemma lem1251747 (p : nat) : (Nat.add p) = (Nat.add p).
Proof. exact (eq_refl (Nat.add p)). Qed.
Lemma lem1251748 (p : nat) (d'' : nat) (q : nat) : (term1 p q d'') = (term1 p d'' q).
Proof. exact (MK_COMB (@lem1251747 p) (@lem1251743 d'' q)). Qed.
Lemma lem1251750 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251751 (d'' : nat) (p : nat) (q : nat) : (term1 p d'' q) = (term1 d'' p q).
Proof. exact (@lem1251750 d'' p q). Qed.
Lemma lem1251761 (d'' : nat) (p : nat) (q : nat) : (term1 p q d'') = (term1 d'' p q).
Proof. exact (TRANS (@lem1251748 p d'' q) (@lem1251751 d'' p q)). Qed.
Lemma lem1251762 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1251763 (d' : nat) (d'' : nat) (p : nat) (q : nat) : (term3 d' p q d'') = (term3 d' d'' p q).
Proof. exact (MK_COMB (@lem1251762 d') (@lem1251761 d'' p q)). Qed.
Lemma lem1251770 (d' : nat) (d'' : nat) (p : nat) (q : nat) : (term2 p d' q d'') = (term3 d' d'' p q).
Proof. exact (TRANS (@lem1251734 d' p q d'') (@lem1251763 d' d'' p q)). Qed.
Lemma lem1251771 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1251772 (d' : nat) (d'' : nat) (p : nat) (q : nat) : (term4 p d' q d'') = (term5 d' d'' p q).
Proof. exact (MK_COMB (@lem1251771) (@lem1251770 d' d'' p q)). Qed.
Lemma lem1251774 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251775 (p : nat) (q : nat) (d'' : nat) (d' : nat) : (term3 q p d'' d') = (term3 p q d'' d').
Proof. exact (@lem1251774 p q (Nat.add d'' d')). Qed.
Lemma lem1251783 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251784 (d'' : nat) (q : nat) (d' : nat) : (term1 q d'' d') = (term1 d'' q d').
Proof. exact (@lem1251783 d'' q d'). Qed.
Lemma lem1251792 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1251793 (d' : nat) (q : nat) : (Nat.add q d') = (Nat.add d' q).
Proof. exact (@lem1251792 d' q). Qed.
Lemma lem1251797 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1251798 (d'' : nat) (d' : nat) (q : nat) : (term1 d'' q d') = (term1 d'' d' q).
Proof. exact (MK_COMB (@lem1251797 d'') (@lem1251793 d' q)). Qed.
Lemma lem1251800 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251801 (d' : nat) (d'' : nat) (q : nat) : (term1 d'' d' q) = (term1 d' d'' q).
Proof. exact (@lem1251800 d' d'' q). Qed.
Lemma lem1251811 (d' : nat) (d'' : nat) (q : nat) : (term1 d'' q d') = (term1 d' d'' q).
Proof. exact (TRANS (@lem1251798 d'' d' q) (@lem1251801 d' d'' q)). Qed.
Lemma lem1251812 (d' : nat) (d'' : nat) (q : nat) : (term1 q d'' d') = (term1 d' d'' q).
Proof. exact (TRANS (@lem1251784 d'' q d') (@lem1251811 d' d'' q)). Qed.
Lemma lem1251813 (p : nat) : (Nat.add p) = (Nat.add p).
Proof. exact (eq_refl (Nat.add p)). Qed.
Lemma lem1251814 (p : nat) (d' : nat) (d'' : nat) (q : nat) : (term3 p q d'' d') = (term3 p d' d'' q).
Proof. exact (MK_COMB (@lem1251813 p) (@lem1251812 d' d'' q)). Qed.
Lemma lem1251816 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251817 (d' : nat) (p : nat) (d'' : nat) (q : nat) : (term3 p d' d'' q) = (term3 d' p d'' q).
Proof. exact (@lem1251816 d' p (Nat.add d'' q)). Qed.
Lemma lem1251825 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251826 (d'' : nat) (p : nat) (q : nat) : (term1 p d'' q) = (term1 d'' p q).
Proof. exact (@lem1251825 d'' p q). Qed.
Lemma lem1251836 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1251837 (d' : nat) (d'' : nat) (p : nat) (q : nat) : (term3 d' p d'' q) = (term3 d' d'' p q).
Proof. exact (MK_COMB (@lem1251836 d') (@lem1251826 d'' p q)). Qed.
Lemma lem1251844 (d' : nat) (d'' : nat) (p : nat) (q : nat) : (term3 p d' d'' q) = (term3 d' d'' p q).
Proof. exact (TRANS (@lem1251817 d' p d'' q) (@lem1251837 d' d'' p q)). Qed.
Lemma lem1251845 (d' : nat) (d'' : nat) (p : nat) (q : nat) : (term3 p q d'' d') = (term3 d' d'' p q).
Proof. exact (TRANS (@lem1251814 p d' d'' q) (@lem1251844 d' d'' p q)). Qed.
Lemma lem1251846 (d' : nat) (d'' : nat) (p : nat) (q : nat) : (term3 q p d'' d') = (term3 d' d'' p q).
Proof. exact (TRANS (@lem1251775 p q d'' d') (@lem1251845 d' d'' p q)). Qed.
Lemma lem1251847 (d' : nat) (d'' : nat) (p : nat) (q : nat) : ((term2 p d' q d'') = (term3 q p d'' d')) = ((term3 d' d'' p q) = (term3 d' d'' p q)).
Proof. exact (MK_COMB (@lem1251772 d' d'' p q) (@lem1251846 d' d'' p q)). Qed.
Lemma lem1251849 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1251850 (x : nat) : (x = x) = True.
Proof. exact (@lem1251849 nat x). Qed.
Lemma lem1251851 (d' : nat) (d'' : nat) (p : nat) (q : nat) : ((term3 d' d'' p q) = (term3 d' d'' p q)) = True.
Proof. exact (@lem1251850 (term3 d' d'' p q)). Qed.
Lemma lem1251852 (q : nat) (p : nat) (d'' : nat) (d' : nat) : ((term2 p d' q d'') = (term3 q p d'' d')) = True.
Proof. exact (TRANS (@lem1251847 d' d'' p q) (@lem1251851 d' d'' p q)). Qed.
Lemma lem1251853 (q : nat) (p : nat) (d'' : nat) (d' : nat) : True = ((term2 p d' q d'') = (term3 q p d'' d')).
Proof. exact (SYM (@lem1251852 q p d'' d')). Qed.
Lemma lem1251854 (q : nat) (p : nat) (d'' : nat) (d' : nat) : (term2 p d' q d'') = (term3 q p d'' d').
Proof. exact (EQ_MP (@lem1251853 q p d'' d') (@lem0)). Qed.
Lemma lem1251858 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1251859 (p : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term6 p q d' d'' d''') = (term7 p q d' d'' d''').
Proof. exact (@lem1251858 p q (term8 d' d'' d''')). Qed.
Lemma lem1251873 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1251874 (d' : nat) (d'' : nat) (d''' : nat) : (term8 d' d'' d''') = (term9 d' d'' d''').
Proof. exact (@lem1251873 d' d'' (S d''')). Qed.
Lemma lem1251884 (q : nat) : (Nat.add q) = (Nat.add q).
Proof. exact (eq_refl (Nat.add q)). Qed.
Lemma lem1251885 (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term10 q d' d'' d''') = (term11 q d' d'' d''').
Proof. exact (MK_COMB (@lem1251884 q) (@lem1251874 d' d'' d''')). Qed.
Lemma lem1251887 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251888 (d' : nat) (q : nat) (d'' : nat) (d''' : nat) : (term11 q d' d'' d''') = (term11 d' q d'' d''').
Proof. exact (@lem1251887 d' q (term12 d'' d''')). Qed.
Lemma lem1251896 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251897 (d'' : nat) (q : nat) (d''' : nat) : (term9 q d'' d''') = (term9 d'' q d''').
Proof. exact (@lem1251896 d'' q (S d''')). Qed.
Lemma lem1251907 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1251908 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term11 d' q d'' d''') = (term11 d' d'' q d''').
Proof. exact (MK_COMB (@lem1251907 d') (@lem1251897 d'' q d''')). Qed.
Lemma lem1251915 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term11 q d' d'' d''') = (term11 d' d'' q d''').
Proof. exact (TRANS (@lem1251888 d' q d'' d''') (@lem1251908 d' d'' q d''')). Qed.
Lemma lem1251916 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term10 q d' d'' d''') = (term11 d' d'' q d''').
Proof. exact (TRANS (@lem1251885 q d' d'' d''') (@lem1251915 d' d'' q d''')). Qed.
Lemma lem1251917 (p : nat) : (Nat.add p) = (Nat.add p).
Proof. exact (eq_refl (Nat.add p)). Qed.
Lemma lem1251918 (p : nat) (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term7 p q d' d'' d''') = (term13 p d' d'' q d''').
Proof. exact (MK_COMB (@lem1251917 p) (@lem1251916 d' d'' q d''')). Qed.
Lemma lem1251920 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251921 (d' : nat) (p : nat) (d'' : nat) (q : nat) (d''' : nat) : (term13 p d' d'' q d''') = (term13 d' p d'' q d''').
Proof. exact (@lem1251920 d' p (term9 d'' q d''')). Qed.
Lemma lem1251929 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251930 (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term11 p d'' q d''') = (term11 d'' p q d''').
Proof. exact (@lem1251929 d'' p (term12 q d''')). Qed.
Lemma lem1251946 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1251947 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term13 d' p d'' q d''') = (term13 d' d'' p q d''').
Proof. exact (MK_COMB (@lem1251946 d') (@lem1251930 d'' p q d''')). Qed.
Lemma lem1251954 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term13 p d' d'' q d''') = (term13 d' d'' p q d''').
Proof. exact (TRANS (@lem1251921 d' p d'' q d''') (@lem1251947 d' d'' p q d''')). Qed.
Lemma lem1251955 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term7 p q d' d'' d''') = (term13 d' d'' p q d''').
Proof. exact (TRANS (@lem1251918 p d' d'' q d''') (@lem1251954 d' d'' p q d''')). Qed.
Lemma lem1251956 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term6 p q d' d'' d''') = (term13 d' d'' p q d''').
Proof. exact (TRANS (@lem1251859 p q d' d'' d''') (@lem1251955 d' d'' p q d''')). Qed.
Lemma lem1251957 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1251958 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term14 p q d' d'' d''') = (term15 d' d'' p q d''').
Proof. exact (MK_COMB (@lem1251957) (@lem1251956 d' d'' p q d''')). Qed.
Lemma lem1251960 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251961 (p : nat) (q : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term13 q p d'' d' d''') = (term13 p q d'' d' d''').
Proof. exact (@lem1251960 p q (term9 d'' d' d''')). Qed.
Lemma lem1251969 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251970 (d'' : nat) (q : nat) (d' : nat) (d''' : nat) : (term11 q d'' d' d''') = (term11 d'' q d' d''').
Proof. exact (@lem1251969 d'' q (term12 d' d''')). Qed.
Lemma lem1251978 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251979 (d' : nat) (q : nat) (d''' : nat) : (term9 q d' d''') = (term9 d' q d''').
Proof. exact (@lem1251978 d' q (S d''')). Qed.
Lemma lem1251989 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1251990 (d'' : nat) (d' : nat) (q : nat) (d''' : nat) : (term11 d'' q d' d''') = (term11 d'' d' q d''').
Proof. exact (MK_COMB (@lem1251989 d'') (@lem1251979 d' q d''')). Qed.
Lemma lem1251992 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1251993 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term11 d'' d' q d''') = (term11 d' d'' q d''').
Proof. exact (@lem1251992 d' d'' (term12 q d''')). Qed.
Lemma lem1252009 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term11 d'' q d' d''') = (term11 d' d'' q d''').
Proof. exact (TRANS (@lem1251990 d'' d' q d''') (@lem1251993 d' d'' q d''')). Qed.
Lemma lem1252010 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term11 q d'' d' d''') = (term11 d' d'' q d''').
Proof. exact (TRANS (@lem1251970 d'' q d' d''') (@lem1252009 d' d'' q d''')). Qed.
Lemma lem1252011 (p : nat) : (Nat.add p) = (Nat.add p).
Proof. exact (eq_refl (Nat.add p)). Qed.
Lemma lem1252012 (p : nat) (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term13 p q d'' d' d''') = (term13 p d' d'' q d''').
Proof. exact (MK_COMB (@lem1252011 p) (@lem1252010 d' d'' q d''')). Qed.
Lemma lem1252014 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252015 (d' : nat) (p : nat) (d'' : nat) (q : nat) (d''' : nat) : (term13 p d' d'' q d''') = (term13 d' p d'' q d''').
Proof. exact (@lem1252014 d' p (term9 d'' q d''')). Qed.
Lemma lem1252023 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252024 (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term11 p d'' q d''') = (term11 d'' p q d''').
Proof. exact (@lem1252023 d'' p (term12 q d''')). Qed.
Lemma lem1252040 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1252041 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term13 d' p d'' q d''') = (term13 d' d'' p q d''').
Proof. exact (MK_COMB (@lem1252040 d') (@lem1252024 d'' p q d''')). Qed.
Lemma lem1252048 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term13 p d' d'' q d''') = (term13 d' d'' p q d''').
Proof. exact (TRANS (@lem1252015 d' p d'' q d''') (@lem1252041 d' d'' p q d''')). Qed.
Lemma lem1252049 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term13 p q d'' d' d''') = (term13 d' d'' p q d''').
Proof. exact (TRANS (@lem1252012 p d' d'' q d''') (@lem1252048 d' d'' p q d''')). Qed.
Lemma lem1252050 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term13 q p d'' d' d''') = (term13 d' d'' p q d''').
Proof. exact (TRANS (@lem1251961 p q d'' d' d''') (@lem1252049 d' d'' p q d''')). Qed.
Lemma lem1252051 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : ((term6 p q d' d'' d''') = (term13 q p d'' d' d''')) = ((term13 d' d'' p q d''') = (term13 d' d'' p q d''')).
Proof. exact (MK_COMB (@lem1251958 d' d'' p q d''') (@lem1252050 d' d'' p q d''')). Qed.
Lemma lem1252053 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1252054 (x : nat) : (x = x) = True.
Proof. exact (@lem1252053 nat x). Qed.
Lemma lem1252055 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : ((term13 d' d'' p q d''') = (term13 d' d'' p q d''')) = True.
Proof. exact (@lem1252054 (term13 d' d'' p q d''')). Qed.
Lemma lem1252056 (q : nat) (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term6 p q d' d'' d''') = (term13 q p d'' d' d''')) = True.
Proof. exact (TRANS (@lem1252051 d' d'' p q d''') (@lem1252055 d' d'' p q d''')). Qed.
Lemma lem1252057 (q : nat) (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : True = ((term6 p q d' d'' d''') = (term13 q p d'' d' d''')).
Proof. exact (SYM (@lem1252056 q p d'' d' d''')). Qed.
Lemma lem1252058 (q : nat) (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term6 p q d' d'' d''') = (term13 q p d'' d' d''').
Proof. exact (EQ_MP (@lem1252057 q p d'' d' d''') (@lem0)). Qed.
Lemma lem1252059 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1252060 (q : nat) (p : nat) (d'' : nat) (d' : nat) : (term4 p d' q d'') = (term5 q p d'' d').
Proof. exact (MK_COMB (@lem1252059) (@lem1251854 q p d'' d')). Qed.
Lemma lem1252061 (q : nat) (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term2 p d' q d'') = (term6 p q d' d'' d''')) = ((term3 q p d'' d') = (term13 q p d'' d' d''')).
Proof. exact (MK_COMB (@lem1252060 q p d'' d') (@lem1252058 q p d'' d' d''')). Qed.
Lemma lem1252062 (m : nat) : term16 m.
Proof. exact (@lem272789 m). Qed.
Lemma lem1252063 (m : nat) : (term16 m) = (term17 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem1252064 (m : nat) : term17 m.
Proof. exact (EQ_MP (@lem1252063 m) (@lem1252062 m)). Qed.
Lemma lem1252065 (m : nat) (n : nat) : term18 m n.
Proof. exact (@lem1252064 m n). Qed.
Lemma lem1252066 (m : nat) (n : nat) : (term18 m n) = ((m = (Nat.add m n)) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem1252074 (m : nat) : term19 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1252075 (m : nat) : (term19 m) = (term20 m).
Proof. exact (eq_refl (term19 m)). Qed.
Lemma lem1252076 (m : nat) : term20 m.
Proof. exact (EQ_MP (@lem1252075 m) (@lem1252074 m)). Qed.
Lemma lem1252077 (m : nat) (n : nat) : term21 m n.
Proof. exact (@lem1252076 m n). Qed.
Lemma lem1252078 (m : nat) (n : nat) : (term21 m n) = (term22 m n).
Proof. exact (eq_refl (term21 m n)). Qed.
Lemma lem1252079 (m : nat) (n : nat) : term22 m n.
Proof. exact (EQ_MP (@lem1252078 m n) (@lem1252077 m n)). Qed.
Lemma lem1252080 (m : nat) (n : nat) (p : nat) : term23 m n p.
Proof. exact (@lem1252079 m n p). Qed.
Lemma lem1252081 (m : nat) (n : nat) (p : nat) : (term23 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term23 m n p)). Qed.
Lemma lem1252084 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1252081 m n p) (@lem1252080 m n p)). Qed.
Lemma lem1252085 (q : nat) (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term3 q p d'' d') = (term13 q p d'' d' d''')) = ((term1 p d'' d') = (term11 p d'' d' d''')).
Proof. exact (@lem1252084 q (term1 p d'' d') (term11 p d'' d' d''')). Qed.
Lemma lem1252087 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1252081 m n p) (@lem1252080 m n p)). Qed.
Lemma lem1252088 (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term1 p d'' d') = (term11 p d'' d' d''')) = ((Nat.add d'' d') = (term9 d'' d' d''')).
Proof. exact (@lem1252087 p (Nat.add d'' d') (term9 d'' d' d''')). Qed.
Lemma lem1252090 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1252081 m n p) (@lem1252080 m n p)). Qed.
Lemma lem1252091 (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add d'' d') = (term9 d'' d' d''')) = (d' = (term12 d' d''')).
Proof. exact (@lem1252090 d'' d' (term12 d' d''')). Qed.
Lemma lem1252093 (m : nat) (n : nat) : (m = (Nat.add m n)) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1252066 m n) (@lem1252065 m n)). Qed.
Lemma lem1252096 (d' : nat) (d''' : nat) : (d' = (term12 d' d''')) = ((S d''') = (NUMERAL 0)).
Proof. exact (@lem1252093 d' (S d''')). Qed.
Lemma lem1252097 (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add d'' d') = (term9 d'' d' d''')) = ((S d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1252091 d'' d' d''') (@lem1252096 d' d''')). Qed.
Lemma lem1252098 (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term1 p d'' d') = (term11 p d'' d' d''')) = ((S d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1252088 p d'' d' d''') (@lem1252097 d'' d' d''')). Qed.
Lemma lem1252099 (q : nat) (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term3 q p d'' d') = (term13 q p d'' d' d''')) = ((S d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1252085 q p d'' d' d''') (@lem1252098 p d'' d' d''')). Qed.
Lemma lem1252100 (p : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term24 p q d' d'' d''') = (term24 p q d' d'' d''').
Proof. exact (eq_refl (term24 p q d' d'' d''')). Qed.
Lemma lem1252101 (p : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (((term2 p d' q d'') = (term6 p q d' d'' d''')) = ((term3 q p d'' d') = (term13 q p d'' d' d'''))) = (((term2 p d' q d'') = (term6 p q d' d'' d''')) = ((S d''') = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1252100 p q d' d'' d''') (@lem1252099 q p d'' d' d''')). Qed.
Lemma lem1252102 (p : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term2 p d' q d'') = (term6 p q d' d'' d''')) = ((S d''') = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1252101 p q d' d'' d''') (@lem1252061 q p d'' d' d''')). Qed.
Lemma lem1252103 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1252104 (p : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term25 p q d' d'' d''') = (term26 d''').
Proof. exact (MK_COMB (@lem1252103) (@lem1252102 p q d' d'' d''')). Qed.
Lemma lem1252105 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1252106 (p : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term27 p q d' d'' d''') = (term28 d''').
Proof. exact (MK_COMB (@lem1252104 p q d' d'' d''') (@lem1252105)). Qed.
Lemma lem1252107 (p : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term28 d''') = (term27 p q d' d'' d''').
Proof. exact (SYM (@lem1252106 p q d' d'' d''')). Qed.
