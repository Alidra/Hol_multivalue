Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1256354_term_abbrevs.
Require Import ADD_AC_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import thm0_spec.
Require Import thm272789_spec.
Require Import thm272790_spec.
Require Import thm272791_spec.
Require Import thm272793_spec.
Lemma lem1255837 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1255838 (p : nat) (q : nat) : (Nat.add q p) = (Nat.add p q).
Proof. exact (@lem1255837 p q). Qed.
Lemma lem1255842 (p : nat) (q : nat) : (term0 p q) = (term0 p q).
Proof. exact (eq_refl (term0 p q)). Qed.
Lemma lem1255843 (p : nat) (q : nat) : ((Nat.add p q) = (Nat.add q p)) = ((Nat.add p q) = (Nat.add p q)).
Proof. exact (MK_COMB (@lem1255842 p q) (@lem1255838 p q)). Qed.
Lemma lem1255845 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1255846 (x : nat) : (x = x) = True.
Proof. exact (@lem1255845 nat x). Qed.
Lemma lem1255847 (p : nat) (q : nat) : ((Nat.add p q) = (Nat.add p q)) = True.
Proof. exact (@lem1255846 (Nat.add p q)). Qed.
Lemma lem1255848 (q : nat) (p : nat) : ((Nat.add p q) = (Nat.add q p)) = True.
Proof. exact (TRANS (@lem1255843 p q) (@lem1255847 p q)). Qed.
Lemma lem1255849 (q : nat) (p : nat) : True = ((Nat.add p q) = (Nat.add q p)).
Proof. exact (SYM (@lem1255848 q p)). Qed.
Lemma lem1255850 (q : nat) (p : nat) : (Nat.add p q) = (Nat.add q p).
Proof. exact (EQ_MP (@lem1255849 q p) (@lem0)). Qed.
Lemma lem1255854 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term2 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1255855 (p : nat) (d''' : nat) (q : nat) (d'' : nat) (d' : nat) : (term3 p d''' q d'' d') = (term4 p d''' q d'' d').
Proof. exact (@lem1255854 (term5 p d' d'' d''') (Nat.add q d'') d'). Qed.
Lemma lem1255857 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term2 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1255858 (p : nat) (d''' : nat) (q : nat) (d'' : nat) (d' : nat) : (term4 p d''' q d'' d') = (term6 p d''' q d'' d').
Proof. exact (@lem1255857 p (term7 d' d'' d''') (term1 q d'' d')). Qed.
Lemma lem1255865 (p : nat) (d''' : nat) (q : nat) (d'' : nat) (d' : nat) : (term3 p d''' q d'' d') = (term6 p d''' q d'' d').
Proof. exact (TRANS (@lem1255855 p d''' q d'' d') (@lem1255858 p d''' q d'' d')). Qed.
Lemma lem1255867 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term2 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1255868 (d''' : nat) (q : nat) (d'' : nat) (d' : nat) : (term8 d''' q d'' d') = (term9 d''' q d'' d').
Proof. exact (@lem1255867 (Nat.add d' d'') (S d''') (term1 q d'' d')). Qed.
Lemma lem1255870 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term2 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1255871 (d''' : nat) (q : nat) (d'' : nat) (d' : nat) : (term9 d''' q d'' d') = (term10 d''' q d'' d').
Proof. exact (@lem1255870 d' d'' (term11 d''' q d'' d')). Qed.
Lemma lem1255878 (d''' : nat) (q : nat) (d'' : nat) (d' : nat) : (term8 d''' q d'' d') = (term10 d''' q d'' d').
Proof. exact (TRANS (@lem1255868 d''' q d'' d') (@lem1255871 d''' q d'' d')). Qed.
Lemma lem1255892 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term2 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1255893 (q : nat) (d'' : nat) (d' : nat) : (term1 q d'' d') = (term2 q d'' d').
Proof. exact (@lem1255892 q d'' d'). Qed.
Lemma lem1255895 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255896 (d'' : nat) (q : nat) (d' : nat) : (term2 q d'' d') = (term2 d'' q d').
Proof. exact (@lem1255895 d'' q d'). Qed.
Lemma lem1255903 (d'' : nat) (q : nat) (d' : nat) : (term1 q d'' d') = (term2 d'' q d').
Proof. exact (TRANS (@lem1255893 q d'' d') (@lem1255896 d'' q d')). Qed.
Lemma lem1255905 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1255906 (d' : nat) (q : nat) : (Nat.add q d') = (Nat.add d' q).
Proof. exact (@lem1255905 d' q). Qed.
Lemma lem1255910 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1255911 (d'' : nat) (d' : nat) (q : nat) : (term2 d'' q d') = (term2 d'' d' q).
Proof. exact (MK_COMB (@lem1255910 d'') (@lem1255906 d' q)). Qed.
Lemma lem1255913 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255914 (d' : nat) (d'' : nat) (q : nat) : (term2 d'' d' q) = (term2 d' d'' q).
Proof. exact (@lem1255913 d' d'' q). Qed.
Lemma lem1255924 (d' : nat) (d'' : nat) (q : nat) : (term2 d'' q d') = (term2 d' d'' q).
Proof. exact (TRANS (@lem1255911 d'' d' q) (@lem1255914 d' d'' q)). Qed.
Lemma lem1255925 (d' : nat) (d'' : nat) (q : nat) : (term1 q d'' d') = (term2 d' d'' q).
Proof. exact (TRANS (@lem1255903 d'' q d') (@lem1255924 d' d'' q)). Qed.
Lemma lem1255926 (d''' : nat) : (term12 d''') = (term12 d''').
Proof. exact (eq_refl (term12 d''')). Qed.
Lemma lem1255927 (d''' : nat) (d' : nat) (d'' : nat) (q : nat) : (term11 d''' q d'' d') = (term13 d''' d' d'' q).
Proof. exact (MK_COMB (@lem1255926 d''') (@lem1255925 d' d'' q)). Qed.
Lemma lem1255929 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255930 (d' : nat) (d''' : nat) (d'' : nat) (q : nat) : (term13 d''' d' d'' q) = (term14 d' d''' d'' q).
Proof. exact (@lem1255929 d' (S d''') (Nat.add d'' q)). Qed.
Lemma lem1255938 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255939 (d'' : nat) (d''' : nat) (q : nat) : (term15 d''' d'' q) = (term16 d'' d''' q).
Proof. exact (@lem1255938 d'' (S d''') q). Qed.
Lemma lem1255947 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1255948 (q : nat) (d''' : nat) : (term17 d''' q) = (term18 q d''').
Proof. exact (@lem1255947 q (S d''')). Qed.
Lemma lem1255952 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1255953 (d'' : nat) (q : nat) (d''' : nat) : (term16 d'' d''' q) = (term19 d'' q d''').
Proof. exact (MK_COMB (@lem1255952 d'') (@lem1255948 q d''')). Qed.
Lemma lem1255960 (d'' : nat) (q : nat) (d''' : nat) : (term15 d''' d'' q) = (term19 d'' q d''').
Proof. exact (TRANS (@lem1255939 d'' d''' q) (@lem1255953 d'' q d''')). Qed.
Lemma lem1255961 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1255962 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term14 d' d''' d'' q) = (term20 d' d'' q d''').
Proof. exact (MK_COMB (@lem1255961 d') (@lem1255960 d'' q d''')). Qed.
Lemma lem1255969 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term13 d''' d' d'' q) = (term20 d' d'' q d''').
Proof. exact (TRANS (@lem1255930 d' d''' d'' q) (@lem1255962 d' d'' q d''')). Qed.
Lemma lem1255970 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term11 d''' q d'' d') = (term20 d' d'' q d''').
Proof. exact (TRANS (@lem1255927 d''' d' d'' q) (@lem1255969 d' d'' q d''')). Qed.
Lemma lem1255971 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1255972 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term21 d''' q d'' d') = (term22 d' d'' q d''').
Proof. exact (MK_COMB (@lem1255971 d'') (@lem1255970 d' d'' q d''')). Qed.
Lemma lem1255974 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1255975 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term22 d' d'' q d''') = (term23 d' d'' q d''').
Proof. exact (@lem1255974 d' d'' (term19 d'' q d''')). Qed.
Lemma lem1255997 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term21 d''' q d'' d') = (term23 d' d'' q d''').
Proof. exact (TRANS (@lem1255972 d' d'' q d''') (@lem1255975 d' d'' q d''')). Qed.
Lemma lem1255998 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1255999 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term10 d''' q d'' d') = (term24 d' d'' q d''').
Proof. exact (MK_COMB (@lem1255998 d') (@lem1255997 d' d'' q d''')). Qed.
Lemma lem1256006 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term8 d''' q d'' d') = (term24 d' d'' q d''').
Proof. exact (TRANS (@lem1255878 d''' q d'' d') (@lem1255999 d' d'' q d''')). Qed.
Lemma lem1256007 (p : nat) : (Nat.add p) = (Nat.add p).
Proof. exact (eq_refl (Nat.add p)). Qed.
Lemma lem1256008 (p : nat) (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term6 p d''' q d'' d') = (term25 p d' d'' q d''').
Proof. exact (MK_COMB (@lem1256007 p) (@lem1256006 d' d'' q d''')). Qed.
Lemma lem1256010 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256011 (p : nat) (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term25 p d' d'' q d''') = (term26 p d' d'' q d''').
Proof. exact (@lem1256010 d' p (term23 d' d'' q d''')). Qed.
Lemma lem1256019 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256020 (d' : nat) (p : nat) (d'' : nat) (q : nat) (d''' : nat) : (term27 p d' d'' q d''') = (term27 d' p d'' q d''').
Proof. exact (@lem1256019 d' p (term28 d'' q d''')). Qed.
Lemma lem1256028 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256029 (p : nat) (d'' : nat) (q : nat) (d''' : nat) : (term23 p d'' q d''') = (term22 p d'' q d''').
Proof. exact (@lem1256028 d'' p (term19 d'' q d''')). Qed.
Lemma lem1256037 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256038 (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term20 p d'' q d''') = (term20 d'' p q d''').
Proof. exact (@lem1256037 d'' p (term18 q d''')). Qed.
Lemma lem1256054 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1256055 (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term22 p d'' q d''') = (term29 d'' p q d''').
Proof. exact (MK_COMB (@lem1256054 d'') (@lem1256038 d'' p q d''')). Qed.
Lemma lem1256062 (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term23 p d'' q d''') = (term29 d'' p q d''').
Proof. exact (TRANS (@lem1256029 p d'' q d''') (@lem1256055 d'' p q d''')). Qed.
Lemma lem1256063 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1256064 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term27 d' p d'' q d''') = (term30 d' d'' p q d''').
Proof. exact (MK_COMB (@lem1256063 d') (@lem1256062 d'' p q d''')). Qed.
Lemma lem1256071 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term27 p d' d'' q d''') = (term30 d' d'' p q d''').
Proof. exact (TRANS (@lem1256020 d' p d'' q d''') (@lem1256064 d' d'' p q d''')). Qed.
Lemma lem1256072 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1256073 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term26 p d' d'' q d''') = (term31 d' d'' p q d''').
Proof. exact (MK_COMB (@lem1256072 d') (@lem1256071 d' d'' p q d''')). Qed.
Lemma lem1256080 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term25 p d' d'' q d''') = (term31 d' d'' p q d''').
Proof. exact (TRANS (@lem1256011 p d' d'' q d''') (@lem1256073 d' d'' p q d''')). Qed.
Lemma lem1256081 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term6 p d''' q d'' d') = (term31 d' d'' p q d''').
Proof. exact (TRANS (@lem1256008 p d' d'' q d''') (@lem1256080 d' d'' p q d''')). Qed.
Lemma lem1256082 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term3 p d''' q d'' d') = (term31 d' d'' p q d''').
Proof. exact (TRANS (@lem1255865 p d''' q d'' d') (@lem1256081 d' d'' p q d''')). Qed.
Lemma lem1256083 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1256084 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term32 p d''' q d'' d') = (term33 d' d'' p q d''').
Proof. exact (MK_COMB (@lem1256083) (@lem1256082 d' d'' p q d''')). Qed.
Lemma lem1256086 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256087 (p : nat) (q : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term34 q p d'' d' d''') = (term34 p q d'' d' d''').
Proof. exact (@lem1256086 p q (term35 d'' d' d''')). Qed.
Lemma lem1256095 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256096 (q : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term36 q d'' d' d''') = (term37 q d'' d' d''').
Proof. exact (@lem1256095 d'' q (term38 d'' d' d''')). Qed.
Lemma lem1256104 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256105 (d'' : nat) (q : nat) (d' : nat) (d''' : nat) : (term39 q d'' d' d''') = (term39 d'' q d' d''').
Proof. exact (@lem1256104 d'' q (term40 d' d''')). Qed.
Lemma lem1256113 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256114 (q : nat) (d' : nat) (d''' : nat) : (term38 q d' d''') = (term41 q d' d''').
Proof. exact (@lem1256113 d' q (term18 d' d''')). Qed.
Lemma lem1256122 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256123 (d' : nat) (q : nat) (d''' : nat) : (term19 q d' d''') = (term19 d' q d''').
Proof. exact (@lem1256122 d' q (S d''')). Qed.
Lemma lem1256133 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1256134 (d' : nat) (q : nat) (d''' : nat) : (term41 q d' d''') = (term28 d' q d''').
Proof. exact (MK_COMB (@lem1256133 d') (@lem1256123 d' q d''')). Qed.
Lemma lem1256141 (d' : nat) (q : nat) (d''' : nat) : (term38 q d' d''') = (term28 d' q d''').
Proof. exact (TRANS (@lem1256114 q d' d''') (@lem1256134 d' q d''')). Qed.
Lemma lem1256142 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1256143 (d'' : nat) (d' : nat) (q : nat) (d''' : nat) : (term39 d'' q d' d''') = (term23 d'' d' q d''').
Proof. exact (MK_COMB (@lem1256142 d'') (@lem1256141 d' q d''')). Qed.
Lemma lem1256145 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256146 (d'' : nat) (d' : nat) (q : nat) (d''' : nat) : (term23 d'' d' q d''') = (term22 d'' d' q d''').
Proof. exact (@lem1256145 d' d'' (term19 d' q d''')). Qed.
Lemma lem1256154 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256155 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term20 d'' d' q d''') = (term20 d' d'' q d''').
Proof. exact (@lem1256154 d' d'' (term18 q d''')). Qed.
Lemma lem1256171 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1256172 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term22 d'' d' q d''') = (term29 d' d'' q d''').
Proof. exact (MK_COMB (@lem1256171 d') (@lem1256155 d' d'' q d''')). Qed.
Lemma lem1256179 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term23 d'' d' q d''') = (term29 d' d'' q d''').
Proof. exact (TRANS (@lem1256146 d'' d' q d''') (@lem1256172 d' d'' q d''')). Qed.
Lemma lem1256180 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term39 d'' q d' d''') = (term29 d' d'' q d''').
Proof. exact (TRANS (@lem1256143 d'' d' q d''') (@lem1256179 d' d'' q d''')). Qed.
Lemma lem1256181 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term39 q d'' d' d''') = (term29 d' d'' q d''').
Proof. exact (TRANS (@lem1256105 d'' q d' d''') (@lem1256180 d' d'' q d''')). Qed.
Lemma lem1256182 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1256183 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term37 q d'' d' d''') = (term42 d' d'' q d''').
Proof. exact (MK_COMB (@lem1256182 d'') (@lem1256181 d' d'' q d''')). Qed.
Lemma lem1256185 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256186 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term42 d' d'' q d''') = (term43 d' d'' q d''').
Proof. exact (@lem1256185 d' d'' (term20 d' d'' q d''')). Qed.
Lemma lem1256194 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256195 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term22 d' d'' q d''') = (term23 d' d'' q d''').
Proof. exact (@lem1256194 d' d'' (term19 d'' q d''')). Qed.
Lemma lem1256217 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1256218 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term43 d' d'' q d''') = (term24 d' d'' q d''').
Proof. exact (MK_COMB (@lem1256217 d') (@lem1256195 d' d'' q d''')). Qed.
Lemma lem1256225 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term42 d' d'' q d''') = (term24 d' d'' q d''').
Proof. exact (TRANS (@lem1256186 d' d'' q d''') (@lem1256218 d' d'' q d''')). Qed.
Lemma lem1256226 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term37 q d'' d' d''') = (term24 d' d'' q d''').
Proof. exact (TRANS (@lem1256183 d' d'' q d''') (@lem1256225 d' d'' q d''')). Qed.
Lemma lem1256227 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term36 q d'' d' d''') = (term24 d' d'' q d''').
Proof. exact (TRANS (@lem1256096 q d'' d' d''') (@lem1256226 d' d'' q d''')). Qed.
Lemma lem1256228 (p : nat) : (Nat.add p) = (Nat.add p).
Proof. exact (eq_refl (Nat.add p)). Qed.
Lemma lem1256229 (p : nat) (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term34 p q d'' d' d''') = (term25 p d' d'' q d''').
Proof. exact (MK_COMB (@lem1256228 p) (@lem1256227 d' d'' q d''')). Qed.
Lemma lem1256231 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256232 (p : nat) (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term25 p d' d'' q d''') = (term26 p d' d'' q d''').
Proof. exact (@lem1256231 d' p (term23 d' d'' q d''')). Qed.
Lemma lem1256240 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256241 (d' : nat) (p : nat) (d'' : nat) (q : nat) (d''' : nat) : (term27 p d' d'' q d''') = (term27 d' p d'' q d''').
Proof. exact (@lem1256240 d' p (term28 d'' q d''')). Qed.
Lemma lem1256249 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256250 (p : nat) (d'' : nat) (q : nat) (d''' : nat) : (term23 p d'' q d''') = (term22 p d'' q d''').
Proof. exact (@lem1256249 d'' p (term19 d'' q d''')). Qed.
Lemma lem1256258 (n : nat) (m : nat) (p : nat) : (term2 m n p) = (term2 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1256259 (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term20 p d'' q d''') = (term20 d'' p q d''').
Proof. exact (@lem1256258 d'' p (term18 q d''')). Qed.
Lemma lem1256275 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1256276 (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term22 p d'' q d''') = (term29 d'' p q d''').
Proof. exact (MK_COMB (@lem1256275 d'') (@lem1256259 d'' p q d''')). Qed.
Lemma lem1256283 (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term23 p d'' q d''') = (term29 d'' p q d''').
Proof. exact (TRANS (@lem1256250 p d'' q d''') (@lem1256276 d'' p q d''')). Qed.
Lemma lem1256284 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1256285 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term27 d' p d'' q d''') = (term30 d' d'' p q d''').
Proof. exact (MK_COMB (@lem1256284 d') (@lem1256283 d'' p q d''')). Qed.
Lemma lem1256292 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term27 p d' d'' q d''') = (term30 d' d'' p q d''').
Proof. exact (TRANS (@lem1256241 d' p d'' q d''') (@lem1256285 d' d'' p q d''')). Qed.
Lemma lem1256293 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1256294 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term26 p d' d'' q d''') = (term31 d' d'' p q d''').
Proof. exact (MK_COMB (@lem1256293 d') (@lem1256292 d' d'' p q d''')). Qed.
Lemma lem1256301 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term25 p d' d'' q d''') = (term31 d' d'' p q d''').
Proof. exact (TRANS (@lem1256232 p d' d'' q d''') (@lem1256294 d' d'' p q d''')). Qed.
Lemma lem1256302 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term34 p q d'' d' d''') = (term31 d' d'' p q d''').
Proof. exact (TRANS (@lem1256229 p d' d'' q d''') (@lem1256301 d' d'' p q d''')). Qed.
Lemma lem1256303 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : (term34 q p d'' d' d''') = (term31 d' d'' p q d''').
Proof. exact (TRANS (@lem1256087 p q d'' d' d''') (@lem1256302 d' d'' p q d''')). Qed.
Lemma lem1256304 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : ((term3 p d''' q d'' d') = (term34 q p d'' d' d''')) = ((term31 d' d'' p q d''') = (term31 d' d'' p q d''')).
Proof. exact (MK_COMB (@lem1256084 d' d'' p q d''') (@lem1256303 d' d'' p q d''')). Qed.
Lemma lem1256306 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1256307 (x : nat) : (x = x) = True.
Proof. exact (@lem1256306 nat x). Qed.
Lemma lem1256308 (d' : nat) (d'' : nat) (p : nat) (q : nat) (d''' : nat) : ((term31 d' d'' p q d''') = (term31 d' d'' p q d''')) = True.
Proof. exact (@lem1256307 (term31 d' d'' p q d''')). Qed.
Lemma lem1256309 (q : nat) (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term3 p d''' q d'' d') = (term34 q p d'' d' d''')) = True.
Proof. exact (TRANS (@lem1256304 d' d'' p q d''') (@lem1256308 d' d'' p q d''')). Qed.
Lemma lem1256310 (q : nat) (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : True = ((term3 p d''' q d'' d') = (term34 q p d'' d' d''')).
Proof. exact (SYM (@lem1256309 q p d'' d' d''')). Qed.
Lemma lem1256311 (q : nat) (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term3 p d''' q d'' d') = (term34 q p d'' d' d''').
Proof. exact (EQ_MP (@lem1256310 q p d'' d' d''') (@lem0)). Qed.
Lemma lem1256312 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1256313 (q : nat) (p : nat) : (term0 p q) = (term0 q p).
Proof. exact (MK_COMB (@lem1256312) (@lem1255850 q p)). Qed.
Lemma lem1256314 (q : nat) (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add p q) = (term3 p d''' q d'' d')) = ((Nat.add q p) = (term34 q p d'' d' d''')).
Proof. exact (MK_COMB (@lem1256313 q p) (@lem1256311 q p d'' d' d''')). Qed.
Lemma lem1256315 (m : nat) : term44 m.
Proof. exact (@lem272789 m). Qed.
Lemma lem1256316 (m : nat) : (term44 m) = (term45 m).
Proof. exact (eq_refl (term44 m)). Qed.
Lemma lem1256317 (m : nat) : term45 m.
Proof. exact (EQ_MP (@lem1256316 m) (@lem1256315 m)). Qed.
Lemma lem1256318 (m : nat) (n : nat) : term46 m n.
Proof. exact (@lem1256317 m n). Qed.
Lemma lem1256319 (m : nat) (n : nat) : (term46 m n) = ((m = (Nat.add m n)) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term46 m n)). Qed.
Lemma lem1256327 (m : nat) : term47 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1256328 (m : nat) : (term47 m) = (term48 m).
Proof. exact (eq_refl (term47 m)). Qed.
Lemma lem1256329 (m : nat) : term48 m.
Proof. exact (EQ_MP (@lem1256328 m) (@lem1256327 m)). Qed.
Lemma lem1256330 (m : nat) (n : nat) : term49 m n.
Proof. exact (@lem1256329 m n). Qed.
Lemma lem1256331 (m : nat) (n : nat) : (term49 m n) = (term50 m n).
Proof. exact (eq_refl (term49 m n)). Qed.
Lemma lem1256332 (m : nat) (n : nat) : term50 m n.
Proof. exact (EQ_MP (@lem1256331 m n) (@lem1256330 m n)). Qed.
Lemma lem1256333 (m : nat) (n : nat) (p : nat) : term51 m n p.
Proof. exact (@lem1256332 m n p). Qed.
Lemma lem1256334 (m : nat) (n : nat) (p : nat) : (term51 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term51 m n p)). Qed.
Lemma lem1256337 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1256334 m n p) (@lem1256333 m n p)). Qed.
Lemma lem1256338 (q : nat) (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add q p) = (term34 q p d'' d' d''')) = (p = (term36 p d'' d' d''')).
Proof. exact (@lem1256337 q p (term36 p d'' d' d''')). Qed.
Lemma lem1256340 (m : nat) (n : nat) : (m = (Nat.add m n)) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1256319 m n) (@lem1256318 m n)). Qed.
Lemma lem1256345 (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : (p = (term36 p d'' d' d''')) = ((term35 d'' d' d''') = (NUMERAL 0)).
Proof. exact (@lem1256340 p (term35 d'' d' d''')). Qed.
Lemma lem1256346 (q : nat) (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add q p) = (term34 q p d'' d' d''')) = ((term35 d'' d' d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1256338 q p d'' d' d''') (@lem1256345 p d'' d' d''')). Qed.
Lemma lem1256347 (p : nat) (d''' : nat) (q : nat) (d'' : nat) (d' : nat) : (term52 p d''' q d'' d') = (term52 p d''' q d'' d').
Proof. exact (eq_refl (term52 p d''' q d'' d')). Qed.
Lemma lem1256348 (p : nat) (q : nat) (d'' : nat) (d' : nat) (d''' : nat) : (((Nat.add p q) = (term3 p d''' q d'' d')) = ((Nat.add q p) = (term34 q p d'' d' d'''))) = (((Nat.add p q) = (term3 p d''' q d'' d')) = ((term35 d'' d' d''') = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1256347 p d''' q d'' d') (@lem1256346 q p d'' d' d''')). Qed.
Lemma lem1256349 (p : nat) (q : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add p q) = (term3 p d''' q d'' d')) = ((term35 d'' d' d''') = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1256348 p q d'' d' d''') (@lem1256314 q p d'' d' d''')). Qed.
Lemma lem1256350 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1256351 (p : nat) (q : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term53 p d''' q d'' d') = (term54 d'' d' d''').
Proof. exact (MK_COMB (@lem1256350) (@lem1256349 p q d'' d' d''')). Qed.
Lemma lem1256352 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1256353 (p : nat) (q : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term55 p d''' q d'' d') = (term56 d'' d' d''').
Proof. exact (MK_COMB (@lem1256351 p q d'' d' d''') (@lem1256352)). Qed.
Lemma lem1256354 (p : nat) (d''' : nat) (q : nat) (d'' : nat) (d' : nat) : (term56 d'' d' d''') = (term55 p d''' q d'' d').
Proof. exact (SYM (@lem1256353 p q d'' d' d''')). Qed.
