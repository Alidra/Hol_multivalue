Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1258084_term_abbrevs.
Require Import ADD_AC_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import EQ_ADD_LCANCEL_0_spec.
Require Import thm0_spec.
Require Import thm272790_spec.
Require Import thm272791_spec.
Require Import thm272793_spec.
Lemma lem1257680 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1257681 (m : nat) (d' : nat) (d'' : nat) (d''' : nat) (q : nat) : (term2 m d' d'' d''' q) = (term3 m d' d'' d''' q).
Proof. exact (@lem1257680 m (term4 d' d'' d''') q). Qed.
Lemma lem1257689 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1257690 (d' : nat) (d'' : nat) (d''' : nat) (q : nat) : (term5 d' d'' d''' q) = (term6 d' d'' d''' q).
Proof. exact (@lem1257689 (Nat.add d' d'') (S d''') q). Qed.
Lemma lem1257692 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1257693 (d' : nat) (d'' : nat) (d''' : nat) (q : nat) : (term6 d' d'' d''' q) = (term7 d' d'' d''' q).
Proof. exact (@lem1257692 d' d'' (term8 d''' q)). Qed.
Lemma lem1257700 (d' : nat) (d'' : nat) (d''' : nat) (q : nat) : (term5 d' d'' d''' q) = (term7 d' d'' d''' q).
Proof. exact (TRANS (@lem1257690 d' d'' d''' q) (@lem1257693 d' d'' d''' q)). Qed.
Lemma lem1257708 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1257709 (q : nat) (d''' : nat) : (term8 d''' q) = (term9 q d''').
Proof. exact (@lem1257708 q (S d''')). Qed.
Lemma lem1257713 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1257714 (d'' : nat) (q : nat) (d''' : nat) : (term10 d'' d''' q) = (term11 d'' q d''').
Proof. exact (MK_COMB (@lem1257713 d'') (@lem1257709 q d''')). Qed.
Lemma lem1257721 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1257722 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term7 d' d'' d''' q) = (term12 d' d'' q d''').
Proof. exact (MK_COMB (@lem1257721 d') (@lem1257714 d'' q d''')). Qed.
Lemma lem1257729 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term5 d' d'' d''' q) = (term12 d' d'' q d''').
Proof. exact (TRANS (@lem1257700 d' d'' d''' q) (@lem1257722 d' d'' q d''')). Qed.
Lemma lem1257730 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1257731 (m : nat) (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term3 m d' d'' d''' q) = (term13 m d' d'' q d''').
Proof. exact (MK_COMB (@lem1257730 m) (@lem1257729 d' d'' q d''')). Qed.
Lemma lem1257733 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257734 (d' : nat) (m : nat) (d'' : nat) (q : nat) (d''' : nat) : (term13 m d' d'' q d''') = (term13 d' m d'' q d''').
Proof. exact (@lem1257733 d' m (term11 d'' q d''')). Qed.
Lemma lem1257742 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257743 (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term12 m d'' q d''') = (term12 d'' m q d''').
Proof. exact (@lem1257742 d'' m (term9 q d''')). Qed.
Lemma lem1257759 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1257760 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term13 d' m d'' q d''') = (term13 d' d'' m q d''').
Proof. exact (MK_COMB (@lem1257759 d') (@lem1257743 d'' m q d''')). Qed.
Lemma lem1257767 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term13 m d' d'' q d''') = (term13 d' d'' m q d''').
Proof. exact (TRANS (@lem1257734 d' m d'' q d''') (@lem1257760 d' d'' m q d''')). Qed.
Lemma lem1257768 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term3 m d' d'' d''' q) = (term13 d' d'' m q d''').
Proof. exact (TRANS (@lem1257731 m d' d'' q d''') (@lem1257767 d' d'' m q d''')). Qed.
Lemma lem1257769 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term2 m d' d'' d''' q) = (term13 d' d'' m q d''').
Proof. exact (TRANS (@lem1257681 m d' d'' d''' q) (@lem1257768 d' d'' m q d''')). Qed.
Lemma lem1257770 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1257771 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term14 m d' d'' d''' q) = (term15 d' d'' m q d''').
Proof. exact (MK_COMB (@lem1257770) (@lem1257769 d' d'' m q d''')). Qed.
Lemma lem1257773 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257774 (m : nat) (q : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term13 q m d'' d' d''') = (term13 m q d'' d' d''').
Proof. exact (@lem1257773 m q (term11 d'' d' d''')). Qed.
Lemma lem1257782 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257783 (d'' : nat) (q : nat) (d' : nat) (d''' : nat) : (term12 q d'' d' d''') = (term12 d'' q d' d''').
Proof. exact (@lem1257782 d'' q (term9 d' d''')). Qed.
Lemma lem1257791 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257792 (d' : nat) (q : nat) (d''' : nat) : (term11 q d' d''') = (term11 d' q d''').
Proof. exact (@lem1257791 d' q (S d''')). Qed.
Lemma lem1257802 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1257803 (d'' : nat) (d' : nat) (q : nat) (d''' : nat) : (term12 d'' q d' d''') = (term12 d'' d' q d''').
Proof. exact (MK_COMB (@lem1257802 d'') (@lem1257792 d' q d''')). Qed.
Lemma lem1257805 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257806 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term12 d'' d' q d''') = (term12 d' d'' q d''').
Proof. exact (@lem1257805 d' d'' (term9 q d''')). Qed.
Lemma lem1257822 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term12 d'' q d' d''') = (term12 d' d'' q d''').
Proof. exact (TRANS (@lem1257803 d'' d' q d''') (@lem1257806 d' d'' q d''')). Qed.
Lemma lem1257823 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term12 q d'' d' d''') = (term12 d' d'' q d''').
Proof. exact (TRANS (@lem1257783 d'' q d' d''') (@lem1257822 d' d'' q d''')). Qed.
Lemma lem1257824 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1257825 (m : nat) (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term13 m q d'' d' d''') = (term13 m d' d'' q d''').
Proof. exact (MK_COMB (@lem1257824 m) (@lem1257823 d' d'' q d''')). Qed.
Lemma lem1257827 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257828 (d' : nat) (m : nat) (d'' : nat) (q : nat) (d''' : nat) : (term13 m d' d'' q d''') = (term13 d' m d'' q d''').
Proof. exact (@lem1257827 d' m (term11 d'' q d''')). Qed.
Lemma lem1257836 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257837 (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term12 m d'' q d''') = (term12 d'' m q d''').
Proof. exact (@lem1257836 d'' m (term9 q d''')). Qed.
Lemma lem1257853 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1257854 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term13 d' m d'' q d''') = (term13 d' d'' m q d''').
Proof. exact (MK_COMB (@lem1257853 d') (@lem1257837 d'' m q d''')). Qed.
Lemma lem1257861 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term13 m d' d'' q d''') = (term13 d' d'' m q d''').
Proof. exact (TRANS (@lem1257828 d' m d'' q d''') (@lem1257854 d' d'' m q d''')). Qed.
Lemma lem1257862 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term13 m q d'' d' d''') = (term13 d' d'' m q d''').
Proof. exact (TRANS (@lem1257825 m d' d'' q d''') (@lem1257861 d' d'' m q d''')). Qed.
Lemma lem1257863 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term13 q m d'' d' d''') = (term13 d' d'' m q d''').
Proof. exact (TRANS (@lem1257774 m q d'' d' d''') (@lem1257862 d' d'' m q d''')). Qed.
Lemma lem1257864 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : ((term2 m d' d'' d''' q) = (term13 q m d'' d' d''')) = ((term13 d' d'' m q d''') = (term13 d' d'' m q d''')).
Proof. exact (MK_COMB (@lem1257771 d' d'' m q d''') (@lem1257863 d' d'' m q d''')). Qed.
Lemma lem1257866 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1257867 (x : nat) : (x = x) = True.
Proof. exact (@lem1257866 nat x). Qed.
Lemma lem1257868 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : ((term13 d' d'' m q d''') = (term13 d' d'' m q d''')) = True.
Proof. exact (@lem1257867 (term13 d' d'' m q d''')). Qed.
Lemma lem1257869 (q : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term2 m d' d'' d''' q) = (term13 q m d'' d' d''')) = True.
Proof. exact (TRANS (@lem1257864 d' d'' m q d''') (@lem1257868 d' d'' m q d''')). Qed.
Lemma lem1257870 (q : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : True = ((term2 m d' d'' d''' q) = (term13 q m d'' d' d''')).
Proof. exact (SYM (@lem1257869 q m d'' d' d''')). Qed.
Lemma lem1257871 (q : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term2 m d' d'' d''' q) = (term13 q m d'' d' d''').
Proof. exact (EQ_MP (@lem1257870 q m d'' d' d''') (@lem0)). Qed.
Lemma lem1257875 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1257876 (m : nat) (q : nat) (d'' : nat) (d' : nat) : (term16 m q d'' d') = (term17 m q d'' d').
Proof. exact (@lem1257875 m (Nat.add q d'') d'). Qed.
Lemma lem1257884 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1257885 (q : nat) (d'' : nat) (d' : nat) : (term0 q d'' d') = (term1 q d'' d').
Proof. exact (@lem1257884 q d'' d'). Qed.
Lemma lem1257887 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257888 (d'' : nat) (q : nat) (d' : nat) : (term1 q d'' d') = (term1 d'' q d').
Proof. exact (@lem1257887 d'' q d'). Qed.
Lemma lem1257895 (d'' : nat) (q : nat) (d' : nat) : (term0 q d'' d') = (term1 d'' q d').
Proof. exact (TRANS (@lem1257885 q d'' d') (@lem1257888 d'' q d')). Qed.
Lemma lem1257897 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1257898 (d' : nat) (q : nat) : (Nat.add q d') = (Nat.add d' q).
Proof. exact (@lem1257897 d' q). Qed.
Lemma lem1257902 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1257903 (d'' : nat) (d' : nat) (q : nat) : (term1 d'' q d') = (term1 d'' d' q).
Proof. exact (MK_COMB (@lem1257902 d'') (@lem1257898 d' q)). Qed.
Lemma lem1257905 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257906 (d' : nat) (d'' : nat) (q : nat) : (term1 d'' d' q) = (term1 d' d'' q).
Proof. exact (@lem1257905 d' d'' q). Qed.
Lemma lem1257916 (d' : nat) (d'' : nat) (q : nat) : (term1 d'' q d') = (term1 d' d'' q).
Proof. exact (TRANS (@lem1257903 d'' d' q) (@lem1257906 d' d'' q)). Qed.
Lemma lem1257917 (d' : nat) (d'' : nat) (q : nat) : (term0 q d'' d') = (term1 d' d'' q).
Proof. exact (TRANS (@lem1257895 d'' q d') (@lem1257916 d' d'' q)). Qed.
Lemma lem1257918 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1257919 (m : nat) (d' : nat) (d'' : nat) (q : nat) : (term17 m q d'' d') = (term18 m d' d'' q).
Proof. exact (MK_COMB (@lem1257918 m) (@lem1257917 d' d'' q)). Qed.
Lemma lem1257921 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257922 (d' : nat) (m : nat) (d'' : nat) (q : nat) : (term18 m d' d'' q) = (term18 d' m d'' q).
Proof. exact (@lem1257921 d' m (Nat.add d'' q)). Qed.
Lemma lem1257930 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257931 (d'' : nat) (m : nat) (q : nat) : (term1 m d'' q) = (term1 d'' m q).
Proof. exact (@lem1257930 d'' m q). Qed.
Lemma lem1257941 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1257942 (d' : nat) (d'' : nat) (m : nat) (q : nat) : (term18 d' m d'' q) = (term18 d' d'' m q).
Proof. exact (MK_COMB (@lem1257941 d') (@lem1257931 d'' m q)). Qed.
Lemma lem1257949 (d' : nat) (d'' : nat) (m : nat) (q : nat) : (term18 m d' d'' q) = (term18 d' d'' m q).
Proof. exact (TRANS (@lem1257922 d' m d'' q) (@lem1257942 d' d'' m q)). Qed.
Lemma lem1257950 (d' : nat) (d'' : nat) (m : nat) (q : nat) : (term17 m q d'' d') = (term18 d' d'' m q).
Proof. exact (TRANS (@lem1257919 m d' d'' q) (@lem1257949 d' d'' m q)). Qed.
Lemma lem1257951 (d' : nat) (d'' : nat) (m : nat) (q : nat) : (term16 m q d'' d') = (term18 d' d'' m q).
Proof. exact (TRANS (@lem1257876 m q d'' d') (@lem1257950 d' d'' m q)). Qed.
Lemma lem1257952 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1257953 (d' : nat) (d'' : nat) (m : nat) (q : nat) : (term19 m q d'' d') = (term20 d' d'' m q).
Proof. exact (MK_COMB (@lem1257952) (@lem1257951 d' d'' m q)). Qed.
Lemma lem1257955 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257956 (m : nat) (q : nat) (d'' : nat) (d' : nat) : (term18 q m d'' d') = (term18 m q d'' d').
Proof. exact (@lem1257955 m q (Nat.add d'' d')). Qed.
Lemma lem1257964 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257965 (d'' : nat) (q : nat) (d' : nat) : (term1 q d'' d') = (term1 d'' q d').
Proof. exact (@lem1257964 d'' q d'). Qed.
Lemma lem1257973 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1257974 (d' : nat) (q : nat) : (Nat.add q d') = (Nat.add d' q).
Proof. exact (@lem1257973 d' q). Qed.
Lemma lem1257978 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1257979 (d'' : nat) (d' : nat) (q : nat) : (term1 d'' q d') = (term1 d'' d' q).
Proof. exact (MK_COMB (@lem1257978 d'') (@lem1257974 d' q)). Qed.
Lemma lem1257981 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257982 (d' : nat) (d'' : nat) (q : nat) : (term1 d'' d' q) = (term1 d' d'' q).
Proof. exact (@lem1257981 d' d'' q). Qed.
Lemma lem1257992 (d' : nat) (d'' : nat) (q : nat) : (term1 d'' q d') = (term1 d' d'' q).
Proof. exact (TRANS (@lem1257979 d'' d' q) (@lem1257982 d' d'' q)). Qed.
Lemma lem1257993 (d' : nat) (d'' : nat) (q : nat) : (term1 q d'' d') = (term1 d' d'' q).
Proof. exact (TRANS (@lem1257965 d'' q d') (@lem1257992 d' d'' q)). Qed.
Lemma lem1257994 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1257995 (m : nat) (d' : nat) (d'' : nat) (q : nat) : (term18 m q d'' d') = (term18 m d' d'' q).
Proof. exact (MK_COMB (@lem1257994 m) (@lem1257993 d' d'' q)). Qed.
Lemma lem1257997 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257998 (d' : nat) (m : nat) (d'' : nat) (q : nat) : (term18 m d' d'' q) = (term18 d' m d'' q).
Proof. exact (@lem1257997 d' m (Nat.add d'' q)). Qed.
Lemma lem1258006 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1258007 (d'' : nat) (m : nat) (q : nat) : (term1 m d'' q) = (term1 d'' m q).
Proof. exact (@lem1258006 d'' m q). Qed.
Lemma lem1258017 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1258018 (d' : nat) (d'' : nat) (m : nat) (q : nat) : (term18 d' m d'' q) = (term18 d' d'' m q).
Proof. exact (MK_COMB (@lem1258017 d') (@lem1258007 d'' m q)). Qed.
Lemma lem1258025 (d' : nat) (d'' : nat) (m : nat) (q : nat) : (term18 m d' d'' q) = (term18 d' d'' m q).
Proof. exact (TRANS (@lem1257998 d' m d'' q) (@lem1258018 d' d'' m q)). Qed.
Lemma lem1258026 (d' : nat) (d'' : nat) (m : nat) (q : nat) : (term18 m q d'' d') = (term18 d' d'' m q).
Proof. exact (TRANS (@lem1257995 m d' d'' q) (@lem1258025 d' d'' m q)). Qed.
Lemma lem1258027 (d' : nat) (d'' : nat) (m : nat) (q : nat) : (term18 q m d'' d') = (term18 d' d'' m q).
Proof. exact (TRANS (@lem1257956 m q d'' d') (@lem1258026 d' d'' m q)). Qed.
Lemma lem1258028 (d' : nat) (d'' : nat) (m : nat) (q : nat) : ((term16 m q d'' d') = (term18 q m d'' d')) = ((term18 d' d'' m q) = (term18 d' d'' m q)).
Proof. exact (MK_COMB (@lem1257953 d' d'' m q) (@lem1258027 d' d'' m q)). Qed.
Lemma lem1258030 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1258031 (x : nat) : (x = x) = True.
Proof. exact (@lem1258030 nat x). Qed.
Lemma lem1258032 (d' : nat) (d'' : nat) (m : nat) (q : nat) : ((term18 d' d'' m q) = (term18 d' d'' m q)) = True.
Proof. exact (@lem1258031 (term18 d' d'' m q)). Qed.
Lemma lem1258033 (q : nat) (m : nat) (d'' : nat) (d' : nat) : ((term16 m q d'' d') = (term18 q m d'' d')) = True.
Proof. exact (TRANS (@lem1258028 d' d'' m q) (@lem1258032 d' d'' m q)). Qed.
Lemma lem1258034 (q : nat) (m : nat) (d'' : nat) (d' : nat) : True = ((term16 m q d'' d') = (term18 q m d'' d')).
Proof. exact (SYM (@lem1258033 q m d'' d')). Qed.
Lemma lem1258035 (q : nat) (m : nat) (d'' : nat) (d' : nat) : (term16 m q d'' d') = (term18 q m d'' d').
Proof. exact (EQ_MP (@lem1258034 q m d'' d') (@lem0)). Qed.
Lemma lem1258036 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1258037 (q : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term14 m d' d'' d''' q) = (term15 q m d'' d' d''').
Proof. exact (MK_COMB (@lem1258036) (@lem1257871 q m d'' d' d''')). Qed.
Lemma lem1258038 (d''' : nat) (q : nat) (m : nat) (d'' : nat) (d' : nat) : ((term2 m d' d'' d''' q) = (term16 m q d'' d')) = ((term13 q m d'' d' d''') = (term18 q m d'' d')).
Proof. exact (MK_COMB (@lem1258037 q m d'' d' d''') (@lem1258035 q m d'' d')). Qed.
Lemma lem1258045 (m : nat) : term21 m.
Proof. exact (@lem79890 m). Qed.
Lemma lem1258046 (m : nat) : (term21 m) = (term22 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem1258047 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem1258046 m) (@lem1258045 m)). Qed.
Lemma lem1258048 (m : nat) (n : nat) : term23 m n.
Proof. exact (@lem1258047 m n). Qed.
Lemma lem1258049 (m : nat) (n : nat) : (term23 m n) = (((Nat.add m n) = m) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term23 m n)). Qed.
Lemma lem1258051 (m : nat) : term24 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1258052 (m : nat) : (term24 m) = (term25 m).
Proof. exact (eq_refl (term24 m)). Qed.
Lemma lem1258053 (m : nat) : term25 m.
Proof. exact (EQ_MP (@lem1258052 m) (@lem1258051 m)). Qed.
Lemma lem1258054 (m : nat) (n : nat) : term26 m n.
Proof. exact (@lem1258053 m n). Qed.
Lemma lem1258055 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (eq_refl (term26 m n)). Qed.
Lemma lem1258056 (m : nat) (n : nat) : term27 m n.
Proof. exact (EQ_MP (@lem1258055 m n) (@lem1258054 m n)). Qed.
Lemma lem1258057 (m : nat) (n : nat) (p : nat) : term28 m n p.
Proof. exact (@lem1258056 m n p). Qed.
Lemma lem1258058 (m : nat) (n : nat) (p : nat) : (term28 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term28 m n p)). Qed.
Lemma lem1258061 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1258058 m n p) (@lem1258057 m n p)). Qed.
Lemma lem1258062 (q : nat) (d''' : nat) (m : nat) (d'' : nat) (d' : nat) : ((term13 q m d'' d' d''') = (term18 q m d'' d')) = ((term12 m d'' d' d''') = (term1 m d'' d')).
Proof. exact (@lem1258061 q (term12 m d'' d' d''') (term1 m d'' d')). Qed.
Lemma lem1258064 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1258058 m n p) (@lem1258057 m n p)). Qed.
Lemma lem1258065 (m : nat) (d''' : nat) (d'' : nat) (d' : nat) : ((term12 m d'' d' d''') = (term1 m d'' d')) = ((term11 d'' d' d''') = (Nat.add d'' d')).
Proof. exact (@lem1258064 m (term11 d'' d' d''') (Nat.add d'' d')). Qed.
Lemma lem1258067 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1258058 m n p) (@lem1258057 m n p)). Qed.
Lemma lem1258068 (d'' : nat) (d''' : nat) (d' : nat) : ((term11 d'' d' d''') = (Nat.add d'' d')) = ((term9 d' d''') = d').
Proof. exact (@lem1258067 d'' (term9 d' d''') d'). Qed.
Lemma lem1258070 (m : nat) (n : nat) : ((Nat.add m n) = m) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1258049 m n) (@lem1258048 m n)). Qed.
Lemma lem1258073 (d' : nat) (d''' : nat) : ((term9 d' d''') = d') = ((S d''') = (NUMERAL 0)).
Proof. exact (@lem1258070 d' (S d''')). Qed.
Lemma lem1258074 (d'' : nat) (d' : nat) (d''' : nat) : ((term11 d'' d' d''') = (Nat.add d'' d')) = ((S d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1258068 d'' d''' d') (@lem1258073 d' d''')). Qed.
Lemma lem1258075 (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term12 m d'' d' d''') = (term1 m d'' d')) = ((S d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1258065 m d''' d'' d') (@lem1258074 d'' d' d''')). Qed.
Lemma lem1258076 (q : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term13 q m d'' d' d''') = (term18 q m d'' d')) = ((S d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1258062 q d''' m d'' d') (@lem1258075 m d'' d' d''')). Qed.
Lemma lem1258077 (d''' : nat) (m : nat) (q : nat) (d'' : nat) (d' : nat) : (term29 d''' m q d'' d') = (term29 d''' m q d'' d').
Proof. exact (eq_refl (term29 d''' m q d'' d')). Qed.
Lemma lem1258078 (m : nat) (q : nat) (d'' : nat) (d' : nat) (d''' : nat) : (((term2 m d' d'' d''' q) = (term16 m q d'' d')) = ((term13 q m d'' d' d''') = (term18 q m d'' d'))) = (((term2 m d' d'' d''' q) = (term16 m q d'' d')) = ((S d''') = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1258077 d''' m q d'' d') (@lem1258076 q m d'' d' d''')). Qed.
Lemma lem1258079 (m : nat) (q : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term2 m d' d'' d''' q) = (term16 m q d'' d')) = ((S d''') = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1258078 m q d'' d' d''') (@lem1258038 d''' q m d'' d')). Qed.
Lemma lem1258080 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1258081 (m : nat) (q : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term30 d''' m q d'' d') = (term31 d''').
Proof. exact (MK_COMB (@lem1258080) (@lem1258079 m q d'' d' d''')). Qed.
Lemma lem1258082 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1258083 (m : nat) (q : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term32 d''' m q d'' d') = (term33 d''').
Proof. exact (MK_COMB (@lem1258081 m q d'' d' d''') (@lem1258082)). Qed.
Lemma lem1258084 (d''' : nat) (m : nat) (q : nat) (d'' : nat) (d' : nat) : (term33 d''') = (term32 d''' m q d'' d').
Proof. exact (SYM (@lem1258083 m q d'' d' d''')). Qed.
