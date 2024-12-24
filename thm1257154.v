Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1257154_term_abbrevs.
Require Import ADD_AC_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import thm0_spec.
Require Import thm272789_spec.
Require Import thm272790_spec.
Require Import thm272791_spec.
Require Import thm272793_spec.
Lemma lem1256738 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1256739 (d'' : nat) (q : nat) : (Nat.add q d'') = (Nat.add d'' q).
Proof. exact (@lem1256738 d'' q). Qed.
Lemma lem1256743 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1256744 (m : nat) (d'' : nat) (q : nat) : (term0 m q d'') = (term0 m d'' q).
Proof. exact (MK_COMB (@lem1256743 m) (@lem1256739 d'' q)). Qed.
Lemma lem1256746 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256747 (d'' : nat) (m : nat) (q : nat) : (term0 m d'' q) = (term0 d'' m q).
Proof. exact (@lem1256746 d'' m q). Qed.
Lemma lem1256757 (d'' : nat) (m : nat) (q : nat) : (term0 m q d'') = (term0 d'' m q).
Proof. exact (TRANS (@lem1256744 m d'' q) (@lem1256747 d'' m q)). Qed.
Lemma lem1256758 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1256759 (d'' : nat) (m : nat) (q : nat) : (term1 m q d'') = (term1 d'' m q).
Proof. exact (MK_COMB (@lem1256758) (@lem1256757 d'' m q)). Qed.
Lemma lem1256761 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256762 (m : nat) (q : nat) (d'' : nat) : (term0 q m d'') = (term0 m q d'').
Proof. exact (@lem1256761 m q d''). Qed.
Lemma lem1256770 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1256771 (d'' : nat) (q : nat) : (Nat.add q d'') = (Nat.add d'' q).
Proof. exact (@lem1256770 d'' q). Qed.
Lemma lem1256775 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1256776 (m : nat) (d'' : nat) (q : nat) : (term0 m q d'') = (term0 m d'' q).
Proof. exact (MK_COMB (@lem1256775 m) (@lem1256771 d'' q)). Qed.
Lemma lem1256778 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256779 (d'' : nat) (m : nat) (q : nat) : (term0 m d'' q) = (term0 d'' m q).
Proof. exact (@lem1256778 d'' m q). Qed.
Lemma lem1256789 (d'' : nat) (m : nat) (q : nat) : (term0 m q d'') = (term0 d'' m q).
Proof. exact (TRANS (@lem1256776 m d'' q) (@lem1256779 d'' m q)). Qed.
Lemma lem1256790 (d'' : nat) (m : nat) (q : nat) : (term0 q m d'') = (term0 d'' m q).
Proof. exact (TRANS (@lem1256762 m q d'') (@lem1256789 d'' m q)). Qed.
Lemma lem1256791 (d'' : nat) (m : nat) (q : nat) : ((term0 m q d'') = (term0 q m d'')) = ((term0 d'' m q) = (term0 d'' m q)).
Proof. exact (MK_COMB (@lem1256759 d'' m q) (@lem1256790 d'' m q)). Qed.
Lemma lem1256793 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1256794 (x : nat) : (x = x) = True.
Proof. exact (@lem1256793 nat x). Qed.
Lemma lem1256795 (d'' : nat) (m : nat) (q : nat) : ((term0 d'' m q) = (term0 d'' m q)) = True.
Proof. exact (@lem1256794 (term0 d'' m q)). Qed.
Lemma lem1256796 (q : nat) (m : nat) (d'' : nat) : ((term0 m q d'') = (term0 q m d'')) = True.
Proof. exact (TRANS (@lem1256791 d'' m q) (@lem1256795 d'' m q)). Qed.
Lemma lem1256797 (q : nat) (m : nat) (d'' : nat) : True = ((term0 m q d'') = (term0 q m d'')).
Proof. exact (SYM (@lem1256796 q m d'')). Qed.
Lemma lem1256798 (q : nat) (m : nat) (d'' : nat) : (term0 m q d'') = (term0 q m d'').
Proof. exact (EQ_MP (@lem1256797 q m d'') (@lem0)). Qed.
Lemma lem1256802 (m : nat) (n : nat) (p : nat) : (term2 m n p) = (term0 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1256803 (m : nat) (d'' : nat) (d''' : nat) (q : nat) (d' : nat) : (term3 m d'' d''' q d') = (term4 m d'' d''' q d').
Proof. exact (@lem1256802 (term5 m d' d'' d''') q d'). Qed.
Lemma lem1256805 (m : nat) (n : nat) (p : nat) : (term2 m n p) = (term0 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1256806 (m : nat) (d'' : nat) (d''' : nat) (q : nat) (d' : nat) : (term4 m d'' d''' q d') = (term6 m d'' d''' q d').
Proof. exact (@lem1256805 m (term7 d' d'' d''') (Nat.add q d')). Qed.
Lemma lem1256813 (m : nat) (d'' : nat) (d''' : nat) (q : nat) (d' : nat) : (term3 m d'' d''' q d') = (term6 m d'' d''' q d').
Proof. exact (TRANS (@lem1256803 m d'' d''' q d') (@lem1256806 m d'' d''' q d')). Qed.
Lemma lem1256815 (m : nat) (n : nat) (p : nat) : (term2 m n p) = (term0 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1256816 (d'' : nat) (d''' : nat) (q : nat) (d' : nat) : (term8 d'' d''' q d') = (term9 d'' d''' q d').
Proof. exact (@lem1256815 (Nat.add d' d'') (S d''') (Nat.add q d')). Qed.
Lemma lem1256818 (m : nat) (n : nat) (p : nat) : (term2 m n p) = (term0 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1256819 (d'' : nat) (d''' : nat) (q : nat) (d' : nat) : (term9 d'' d''' q d') = (term10 d'' d''' q d').
Proof. exact (@lem1256818 d' d'' (term11 d''' q d')). Qed.
Lemma lem1256826 (d'' : nat) (d''' : nat) (q : nat) (d' : nat) : (term8 d'' d''' q d') = (term10 d'' d''' q d').
Proof. exact (TRANS (@lem1256816 d'' d''' q d') (@lem1256819 d'' d''' q d')). Qed.
Lemma lem1256834 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256835 (q : nat) (d''' : nat) (d' : nat) : (term11 d''' q d') = (term12 q d''' d').
Proof. exact (@lem1256834 q (S d''') d'). Qed.
Lemma lem1256843 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1256844 (d' : nat) (d''' : nat) : (term13 d''' d') = (term14 d' d''').
Proof. exact (@lem1256843 d' (S d''')). Qed.
Lemma lem1256848 (q : nat) : (Nat.add q) = (Nat.add q).
Proof. exact (eq_refl (Nat.add q)). Qed.
Lemma lem1256849 (q : nat) (d' : nat) (d''' : nat) : (term12 q d''' d') = (term15 q d' d''').
Proof. exact (MK_COMB (@lem1256848 q) (@lem1256844 d' d''')). Qed.
Lemma lem1256851 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256852 (d' : nat) (q : nat) (d''' : nat) : (term15 q d' d''') = (term15 d' q d''').
Proof. exact (@lem1256851 d' q (S d''')). Qed.
Lemma lem1256862 (d' : nat) (q : nat) (d''' : nat) : (term12 q d''' d') = (term15 d' q d''').
Proof. exact (TRANS (@lem1256849 q d' d''') (@lem1256852 d' q d''')). Qed.
Lemma lem1256863 (d' : nat) (q : nat) (d''' : nat) : (term11 d''' q d') = (term15 d' q d''').
Proof. exact (TRANS (@lem1256835 q d''' d') (@lem1256862 d' q d''')). Qed.
Lemma lem1256864 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1256865 (d'' : nat) (d' : nat) (q : nat) (d''' : nat) : (term16 d'' d''' q d') = (term17 d'' d' q d''').
Proof. exact (MK_COMB (@lem1256864 d'') (@lem1256863 d' q d''')). Qed.
Lemma lem1256867 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256868 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term17 d'' d' q d''') = (term17 d' d'' q d''').
Proof. exact (@lem1256867 d' d'' (term14 q d''')). Qed.
Lemma lem1256884 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term16 d'' d''' q d') = (term17 d' d'' q d''').
Proof. exact (TRANS (@lem1256865 d'' d' q d''') (@lem1256868 d' d'' q d''')). Qed.
Lemma lem1256885 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1256886 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term10 d'' d''' q d') = (term18 d' d'' q d''').
Proof. exact (MK_COMB (@lem1256885 d') (@lem1256884 d' d'' q d''')). Qed.
Lemma lem1256893 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term8 d'' d''' q d') = (term18 d' d'' q d''').
Proof. exact (TRANS (@lem1256826 d'' d''' q d') (@lem1256886 d' d'' q d''')). Qed.
Lemma lem1256894 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1256895 (m : nat) (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term6 m d'' d''' q d') = (term19 m d' d'' q d''').
Proof. exact (MK_COMB (@lem1256894 m) (@lem1256893 d' d'' q d''')). Qed.
Lemma lem1256897 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256898 (m : nat) (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term19 m d' d'' q d''') = (term20 m d' d'' q d''').
Proof. exact (@lem1256897 d' m (term17 d' d'' q d''')). Qed.
Lemma lem1256906 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256907 (d' : nat) (m : nat) (d'' : nat) (q : nat) (d''' : nat) : (term21 m d' d'' q d''') = (term21 d' m d'' q d''').
Proof. exact (@lem1256906 d' m (term15 d'' q d''')). Qed.
Lemma lem1256915 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256916 (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term17 m d'' q d''') = (term17 d'' m q d''').
Proof. exact (@lem1256915 d'' m (term14 q d''')). Qed.
Lemma lem1256932 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1256933 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term21 d' m d'' q d''') = (term21 d' d'' m q d''').
Proof. exact (MK_COMB (@lem1256932 d') (@lem1256916 d'' m q d''')). Qed.
Lemma lem1256940 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term21 m d' d'' q d''') = (term21 d' d'' m q d''').
Proof. exact (TRANS (@lem1256907 d' m d'' q d''') (@lem1256933 d' d'' m q d''')). Qed.
Lemma lem1256941 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1256942 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term20 m d' d'' q d''') = (term22 d' d'' m q d''').
Proof. exact (MK_COMB (@lem1256941 d') (@lem1256940 d' d'' m q d''')). Qed.
Lemma lem1256949 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term19 m d' d'' q d''') = (term22 d' d'' m q d''').
Proof. exact (TRANS (@lem1256898 m d' d'' q d''') (@lem1256942 d' d'' m q d''')). Qed.
Lemma lem1256950 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term6 m d'' d''' q d') = (term22 d' d'' m q d''').
Proof. exact (TRANS (@lem1256895 m d' d'' q d''') (@lem1256949 d' d'' m q d''')). Qed.
Lemma lem1256951 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term3 m d'' d''' q d') = (term22 d' d'' m q d''').
Proof. exact (TRANS (@lem1256813 m d'' d''' q d') (@lem1256950 d' d'' m q d''')). Qed.
Lemma lem1256952 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1256953 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term23 m d'' d''' q d') = (term24 d' d'' m q d''').
Proof. exact (MK_COMB (@lem1256952) (@lem1256951 d' d'' m q d''')). Qed.
Lemma lem1256955 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256956 (m : nat) (q : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term25 q m d'' d' d''') = (term25 m q d'' d' d''').
Proof. exact (@lem1256955 m q (term26 d'' d' d''')). Qed.
Lemma lem1256964 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256965 (d'' : nat) (q : nat) (d' : nat) (d''' : nat) : (term27 q d'' d' d''') = (term27 d'' q d' d''').
Proof. exact (@lem1256964 d'' q (term28 d' d''')). Qed.
Lemma lem1256973 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256974 (q : nat) (d' : nat) (d''' : nat) : (term26 q d' d''') = (term29 q d' d''').
Proof. exact (@lem1256973 d' q (term14 d' d''')). Qed.
Lemma lem1256982 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256983 (d' : nat) (q : nat) (d''' : nat) : (term15 q d' d''') = (term15 d' q d''').
Proof. exact (@lem1256982 d' q (S d''')). Qed.
Lemma lem1256993 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1256994 (d' : nat) (q : nat) (d''' : nat) : (term29 q d' d''') = (term30 d' q d''').
Proof. exact (MK_COMB (@lem1256993 d') (@lem1256983 d' q d''')). Qed.
Lemma lem1257001 (d' : nat) (q : nat) (d''' : nat) : (term26 q d' d''') = (term30 d' q d''').
Proof. exact (TRANS (@lem1256974 q d' d''') (@lem1256994 d' q d''')). Qed.
Lemma lem1257002 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1257003 (d'' : nat) (d' : nat) (q : nat) (d''' : nat) : (term27 d'' q d' d''') = (term31 d'' d' q d''').
Proof. exact (MK_COMB (@lem1257002 d'') (@lem1257001 d' q d''')). Qed.
Lemma lem1257005 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257006 (d'' : nat) (d' : nat) (q : nat) (d''' : nat) : (term31 d'' d' q d''') = (term32 d'' d' q d''').
Proof. exact (@lem1257005 d' d'' (term15 d' q d''')). Qed.
Lemma lem1257014 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257015 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term17 d'' d' q d''') = (term17 d' d'' q d''').
Proof. exact (@lem1257014 d' d'' (term14 q d''')). Qed.
Lemma lem1257031 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1257032 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term32 d'' d' q d''') = (term18 d' d'' q d''').
Proof. exact (MK_COMB (@lem1257031 d') (@lem1257015 d' d'' q d''')). Qed.
Lemma lem1257039 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term31 d'' d' q d''') = (term18 d' d'' q d''').
Proof. exact (TRANS (@lem1257006 d'' d' q d''') (@lem1257032 d' d'' q d''')). Qed.
Lemma lem1257040 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term27 d'' q d' d''') = (term18 d' d'' q d''').
Proof. exact (TRANS (@lem1257003 d'' d' q d''') (@lem1257039 d' d'' q d''')). Qed.
Lemma lem1257041 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term27 q d'' d' d''') = (term18 d' d'' q d''').
Proof. exact (TRANS (@lem1256965 d'' q d' d''') (@lem1257040 d' d'' q d''')). Qed.
Lemma lem1257042 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1257043 (m : nat) (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term25 m q d'' d' d''') = (term19 m d' d'' q d''').
Proof. exact (MK_COMB (@lem1257042 m) (@lem1257041 d' d'' q d''')). Qed.
Lemma lem1257045 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257046 (m : nat) (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term19 m d' d'' q d''') = (term20 m d' d'' q d''').
Proof. exact (@lem1257045 d' m (term17 d' d'' q d''')). Qed.
Lemma lem1257054 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257055 (d' : nat) (m : nat) (d'' : nat) (q : nat) (d''' : nat) : (term21 m d' d'' q d''') = (term21 d' m d'' q d''').
Proof. exact (@lem1257054 d' m (term15 d'' q d''')). Qed.
Lemma lem1257063 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1257064 (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term17 m d'' q d''') = (term17 d'' m q d''').
Proof. exact (@lem1257063 d'' m (term14 q d''')). Qed.
Lemma lem1257080 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1257081 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term21 d' m d'' q d''') = (term21 d' d'' m q d''').
Proof. exact (MK_COMB (@lem1257080 d') (@lem1257064 d'' m q d''')). Qed.
Lemma lem1257088 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term21 m d' d'' q d''') = (term21 d' d'' m q d''').
Proof. exact (TRANS (@lem1257055 d' m d'' q d''') (@lem1257081 d' d'' m q d''')). Qed.
Lemma lem1257089 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1257090 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term20 m d' d'' q d''') = (term22 d' d'' m q d''').
Proof. exact (MK_COMB (@lem1257089 d') (@lem1257088 d' d'' m q d''')). Qed.
Lemma lem1257097 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term19 m d' d'' q d''') = (term22 d' d'' m q d''').
Proof. exact (TRANS (@lem1257046 m d' d'' q d''') (@lem1257090 d' d'' m q d''')). Qed.
Lemma lem1257098 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term25 m q d'' d' d''') = (term22 d' d'' m q d''').
Proof. exact (TRANS (@lem1257043 m d' d'' q d''') (@lem1257097 d' d'' m q d''')). Qed.
Lemma lem1257099 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term25 q m d'' d' d''') = (term22 d' d'' m q d''').
Proof. exact (TRANS (@lem1256956 m q d'' d' d''') (@lem1257098 d' d'' m q d''')). Qed.
Lemma lem1257100 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : ((term3 m d'' d''' q d') = (term25 q m d'' d' d''')) = ((term22 d' d'' m q d''') = (term22 d' d'' m q d''')).
Proof. exact (MK_COMB (@lem1256953 d' d'' m q d''') (@lem1257099 d' d'' m q d''')). Qed.
Lemma lem1257102 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1257103 (x : nat) : (x = x) = True.
Proof. exact (@lem1257102 nat x). Qed.
Lemma lem1257104 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : ((term22 d' d'' m q d''') = (term22 d' d'' m q d''')) = True.
Proof. exact (@lem1257103 (term22 d' d'' m q d''')). Qed.
Lemma lem1257105 (q : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term3 m d'' d''' q d') = (term25 q m d'' d' d''')) = True.
Proof. exact (TRANS (@lem1257100 d' d'' m q d''') (@lem1257104 d' d'' m q d''')). Qed.
Lemma lem1257106 (q : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : True = ((term3 m d'' d''' q d') = (term25 q m d'' d' d''')).
Proof. exact (SYM (@lem1257105 q m d'' d' d''')). Qed.
Lemma lem1257107 (q : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term3 m d'' d''' q d') = (term25 q m d'' d' d''').
Proof. exact (EQ_MP (@lem1257106 q m d'' d' d''') (@lem0)). Qed.
Lemma lem1257108 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1257109 (q : nat) (m : nat) (d'' : nat) : (term1 m q d'') = (term1 q m d'').
Proof. exact (MK_COMB (@lem1257108) (@lem1256798 q m d'')). Qed.
Lemma lem1257110 (q : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term0 m q d'') = (term3 m d'' d''' q d')) = ((term0 q m d'') = (term25 q m d'' d' d''')).
Proof. exact (MK_COMB (@lem1257109 q m d'') (@lem1257107 q m d'' d' d''')). Qed.
Lemma lem1257111 (m : nat) : term33 m.
Proof. exact (@lem272789 m). Qed.
Lemma lem1257112 (m : nat) : (term33 m) = (term34 m).
Proof. exact (eq_refl (term33 m)). Qed.
Lemma lem1257113 (m : nat) : term34 m.
Proof. exact (EQ_MP (@lem1257112 m) (@lem1257111 m)). Qed.
Lemma lem1257114 (m : nat) (n : nat) : term35 m n.
Proof. exact (@lem1257113 m n). Qed.
Lemma lem1257115 (m : nat) (n : nat) : (term35 m n) = ((m = (Nat.add m n)) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term35 m n)). Qed.
Lemma lem1257123 (m : nat) : term36 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1257124 (m : nat) : (term36 m) = (term37 m).
Proof. exact (eq_refl (term36 m)). Qed.
Lemma lem1257125 (m : nat) : term37 m.
Proof. exact (EQ_MP (@lem1257124 m) (@lem1257123 m)). Qed.
Lemma lem1257126 (m : nat) (n : nat) : term38 m n.
Proof. exact (@lem1257125 m n). Qed.
Lemma lem1257127 (m : nat) (n : nat) : (term38 m n) = (term39 m n).
Proof. exact (eq_refl (term38 m n)). Qed.
Lemma lem1257128 (m : nat) (n : nat) : term39 m n.
Proof. exact (EQ_MP (@lem1257127 m n) (@lem1257126 m n)). Qed.
Lemma lem1257129 (m : nat) (n : nat) (p : nat) : term40 m n p.
Proof. exact (@lem1257128 m n p). Qed.
Lemma lem1257130 (m : nat) (n : nat) (p : nat) : (term40 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term40 m n p)). Qed.
Lemma lem1257133 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1257130 m n p) (@lem1257129 m n p)). Qed.
Lemma lem1257134 (q : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term0 q m d'') = (term25 q m d'' d' d''')) = ((Nat.add m d'') = (term27 m d'' d' d''')).
Proof. exact (@lem1257133 q (Nat.add m d'') (term27 m d'' d' d''')). Qed.
Lemma lem1257136 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1257130 m n p) (@lem1257129 m n p)). Qed.
Lemma lem1257137 (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add m d'') = (term27 m d'' d' d''')) = (d'' = (term26 d'' d' d''')).
Proof. exact (@lem1257136 m d'' (term26 d'' d' d''')). Qed.
Lemma lem1257139 (m : nat) (n : nat) : (m = (Nat.add m n)) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1257115 m n) (@lem1257114 m n)). Qed.
Lemma lem1257144 (d'' : nat) (d' : nat) (d''' : nat) : (d'' = (term26 d'' d' d''')) = ((term28 d' d''') = (NUMERAL 0)).
Proof. exact (@lem1257139 d'' (term28 d' d''')). Qed.
Lemma lem1257145 (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add m d'') = (term27 m d'' d' d''')) = ((term28 d' d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1257137 m d'' d' d''') (@lem1257144 d'' d' d''')). Qed.
Lemma lem1257146 (q : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term0 q m d'') = (term25 q m d'' d' d''')) = ((term28 d' d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1257134 q m d'' d' d''') (@lem1257145 m d'' d' d''')). Qed.
Lemma lem1257147 (m : nat) (d'' : nat) (d''' : nat) (q : nat) (d' : nat) : (term41 m d'' d''' q d') = (term41 m d'' d''' q d').
Proof. exact (eq_refl (term41 m d'' d''' q d')). Qed.
Lemma lem1257148 (m : nat) (d'' : nat) (q : nat) (d' : nat) (d''' : nat) : (((term0 m q d'') = (term3 m d'' d''' q d')) = ((term0 q m d'') = (term25 q m d'' d' d'''))) = (((term0 m q d'') = (term3 m d'' d''' q d')) = ((term28 d' d''') = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1257147 m d'' d''' q d') (@lem1257146 q m d'' d' d''')). Qed.
Lemma lem1257149 (m : nat) (d'' : nat) (q : nat) (d' : nat) (d''' : nat) : ((term0 m q d'') = (term3 m d'' d''' q d')) = ((term28 d' d''') = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1257148 m d'' q d' d''') (@lem1257110 q m d'' d' d''')). Qed.
Lemma lem1257150 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1257151 (m : nat) (d'' : nat) (q : nat) (d' : nat) (d''' : nat) : (term42 m d'' d''' q d') = (term43 d' d''').
Proof. exact (MK_COMB (@lem1257150) (@lem1257149 m d'' q d' d''')). Qed.
Lemma lem1257152 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1257153 (m : nat) (d'' : nat) (q : nat) (d' : nat) (d''' : nat) : (term44 m d'' d''' q d') = (term45 d' d''').
Proof. exact (MK_COMB (@lem1257151 m d'' q d' d''') (@lem1257152)). Qed.
Lemma lem1257154 (m : nat) (d'' : nat) (d''' : nat) (q : nat) (d' : nat) : (term45 d' d''') = (term44 m d'' d''' q d').
Proof. exact (SYM (@lem1257153 m d'' q d' d''')). Qed.
