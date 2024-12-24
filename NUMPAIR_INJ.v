Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NUMPAIR_INJ_term_abbrevs.
Require Import EQ_ADD_RCANCEL_spec.
Require Import EQ_MULT_LCANCEL_spec.
Require Import EXP_EQ_0_spec.
Require Import NUMPAIR_spec.
Require Import NUMPAIR_INJ_LEMMA_spec.
Require Import thm0_spec.
Require Import thm1823_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm521920_spec.
Require Import thm522075_spec.
Lemma lem1051568 : term0.
Proof. exact (EQ_MP (@lem521920) (@lem522075)). Qed.
Lemma lem1051569 : term1.
Proof. exact (proj2 (@lem1051568)). Qed.
Lemma lem1051570 : term2.
Proof. exact (proj2 (@lem1051569)). Qed.
Lemma lem1051571 : term3.
Proof. exact (proj2 (@lem1051570)). Qed.
Lemma lem1051613 : term4.
Proof. exact (proj1 (@lem1051571)). Qed.
Lemma lem1051614 (n : nat) : term5 n.
Proof. exact (@lem1051613 n). Qed.
Lemma lem1051615 (n : nat) : (term5 n) = (((BIT1 n) = 0) = False).
Proof. exact (eq_refl (term5 n)). Qed.
Lemma lem1051617 : term6.
Proof. exact (proj1 (@lem1051570)). Qed.
Lemma lem1051618 (n : nat) : term7 n.
Proof. exact (@lem1051617 n). Qed.
Lemma lem1051619 (n : nat) : (term7 n) = (((BIT0 n) = 0) = (n = 0)).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem1051622 : term8.
Proof. exact (proj1 (@lem1051568)). Qed.
Lemma lem1051623 (m : nat) : term9 m.
Proof. exact (@lem1051622 m). Qed.
Lemma lem1051624 (m : nat) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem1051625 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem1051624 m) (@lem1051623 m)). Qed.
Lemma lem1051626 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem1051625 m n). Qed.
Lemma lem1051627 (m : nat) (n : nat) : (term11 m n) = (((NUMERAL m) = (NUMERAL n)) = (m = n)).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem1051879 (m : nat) : term12 m.
Proof. exact (@lem86997 m). Qed.
Lemma lem1051880 (m : nat) : (term12 m) = (term13 m).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem1051881 (m : nat) : term13 m.
Proof. exact (EQ_MP (@lem1051880 m) (@lem1051879 m)). Qed.
Lemma lem1051882 (m : nat) (n : nat) : term14 m n.
Proof. exact (@lem1051881 m n). Qed.
Lemma lem1051883 (m : nat) (n : nat) : (term14 m n) = (((Nat.pow m n) = (NUMERAL 0)) = (term15 m n)).
Proof. exact (eq_refl (term14 m n)). Qed.
Lemma lem1051885 (m : nat) : term16 m.
Proof. exact (@lem79714 m). Qed.
Lemma lem1051886 (m : nat) : (term16 m) = (term17 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem1051887 (m : nat) : term17 m.
Proof. exact (EQ_MP (@lem1051886 m) (@lem1051885 m)). Qed.
Lemma lem1051888 (m : nat) (n : nat) : term18 m n.
Proof. exact (@lem1051887 m n). Qed.
Lemma lem1051889 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem1051890 (m : nat) (n : nat) : term19 m n.
Proof. exact (EQ_MP (@lem1051889 m n) (@lem1051888 m n)). Qed.
Lemma lem1051891 (m : nat) (n : nat) (p : nat) : term20 m n p.
Proof. exact (@lem1051890 m n p). Qed.
Lemma lem1051892 (p : nat) (m : nat) (n : nat) : (term20 m n p) = (((Nat.add m p) = (Nat.add n p)) = (m = n)).
Proof. exact (eq_refl (term20 m n p)). Qed.
Lemma lem1051894 (m : nat) : term21 m.
Proof. exact (@lem84830 m). Qed.
Lemma lem1051895 (m : nat) : (term21 m) = (term22 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem1051896 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem1051895 m) (@lem1051894 m)). Qed.
Lemma lem1051897 (m : nat) (n : nat) : term23 m n.
Proof. exact (@lem1051896 m n). Qed.
Lemma lem1051898 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (eq_refl (term23 m n)). Qed.
Lemma lem1051899 (m : nat) (n : nat) : term24 m n.
Proof. exact (EQ_MP (@lem1051898 m n) (@lem1051897 m n)). Qed.
Lemma lem1051900 (m : nat) (n : nat) (p : nat) : term25 m n p.
Proof. exact (@lem1051899 m n p). Qed.
Lemma lem1051901 (m : nat) (n : nat) (p : nat) : (term25 m n p) = (((Nat.mul m n) = (Nat.mul m p)) = (term26 m n p)).
Proof. exact (eq_refl (term25 m n p)). Qed.
Lemma lem1051903 (x : nat) : term27 x.
Proof. exact (@lem1046874 x). Qed.
Lemma lem1051904 (x : nat) : (term27 x) = (term28 x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem1051905 (x : nat) : term28 x.
Proof. exact (EQ_MP (@lem1051904 x) (@lem1051903 x)). Qed.
Lemma lem1051906 (x : nat) (y : nat) : term29 x y.
Proof. exact (@lem1051905 x y). Qed.
Lemma lem1051907 (x : nat) (y : nat) : (term29 x y) = ((NUMPAIR x y) = (term30 x y)).
Proof. exact (eq_refl (term29 x y)). Qed.
Lemma lem1051909 (x1 : nat) : term31 x1.
Proof. exact (@lem1051234 x1). Qed.
Lemma lem1051910 (x1 : nat) : (term31 x1) = (term32 x1).
Proof. exact (eq_refl (term31 x1)). Qed.
Lemma lem1051911 (x1 : nat) : term32 x1.
Proof. exact (EQ_MP (@lem1051910 x1) (@lem1051909 x1)). Qed.
Lemma lem1051912 (x1 : nat) (y1 : nat) : term33 x1 y1.
Proof. exact (@lem1051911 x1 y1). Qed.
Lemma lem1051913 (y1 : nat) (x1 : nat) : (term33 x1 y1) = (term34 y1 x1).
Proof. exact (eq_refl (term33 x1 y1)). Qed.
Lemma lem1051914 (y1 : nat) (x1 : nat) : term34 y1 x1.
Proof. exact (EQ_MP (@lem1051913 y1 x1) (@lem1051912 x1 y1)). Qed.
Lemma lem1051915 (y1 : nat) (x1 : nat) (x2 : nat) : term35 y1 x1 x2.
Proof. exact (@lem1051914 y1 x1 x2). Qed.
Lemma lem1051916 (y1 : nat) (x1 : nat) (x2 : nat) : (term35 y1 x1 x2) = (term36 y1 x1 x2).
Proof. exact (eq_refl (term35 y1 x1 x2)). Qed.
Lemma lem1051917 (y1 : nat) (x1 : nat) (x2 : nat) : term36 y1 x1 x2.
Proof. exact (EQ_MP (@lem1051916 y1 x1 x2) (@lem1051915 y1 x1 x2)). Qed.
Lemma lem1051918 (y1 : nat) (x1 : nat) (x2 : nat) (y2 : nat) : term37 y1 x1 x2 y2.
Proof. exact (@lem1051917 y1 x1 x2 y2). Qed.
Lemma lem1051919 (y1 : nat) (y2 : nat) (x1 : nat) (x2 : nat) : (term37 y1 x1 x2 y2) = (term38 y1 y2 x1 x2).
Proof. exact (eq_refl (term37 y1 x1 x2 y2)). Qed.
Lemma lem1051921 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : (NUMPAIR x1 y1) = (NUMPAIR x2 y2)) : (NUMPAIR x1 y1) = (NUMPAIR x2 y2).
Proof. exact (h1). Qed.
Lemma lem1051922 (x1 : nat) (x2 : nat) (y1 : nat) (y2 : nat) (h1 : term39 x1 x2 y1 y2) : term39 x1 x2 y1 y2.
Proof. exact (h1). Qed.
Lemma lem1051936 (x1 : nat) (x2 : nat) (y1 : nat) (y2 : nat) (h1 : term39 x1 x2 y1 y2) : x1 = x2.
Proof. exact (proj1 (@lem1051922 x1 x2 y1 y2 h1)). Qed.
Lemma lem1051937 : NUMPAIR = NUMPAIR.
Proof. exact (eq_refl NUMPAIR). Qed.
Lemma lem1051938 (x1 : nat) (x2 : nat) (y1 : nat) (y2 : nat) (h1 : term39 x1 x2 y1 y2) : (NUMPAIR x1) = (NUMPAIR x2).
Proof. exact (MK_COMB (@lem1051937) (@lem1051936 x1 x2 y1 y2 h1)). Qed.
Lemma lem1051940 (x1 : nat) (x2 : nat) (y1 : nat) (y2 : nat) (h1 : term39 x1 x2 y1 y2) : y1 = y2.
Proof. exact (proj2 (@lem1051922 x1 x2 y1 y2 h1)). Qed.
Lemma lem1051941 (x1 : nat) (x2 : nat) (y1 : nat) (y2 : nat) (h1 : term39 x1 x2 y1 y2) : (NUMPAIR x1 y1) = (NUMPAIR x2 y2).
Proof. exact (MK_COMB (@lem1051938 x1 x2 y1 y2 h1) (@lem1051940 x1 x2 y1 y2 h1)). Qed.
Lemma lem1051942 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1051943 (x1 : nat) (x2 : nat) (y1 : nat) (y2 : nat) (h1 : term39 x1 x2 y1 y2) : (term40 x1 y1) = (term40 x2 y2).
Proof. exact (MK_COMB (@lem1051942) (@lem1051941 x1 x2 y1 y2 h1)). Qed.
Lemma lem1051944 (x2 : nat) (y2 : nat) : (NUMPAIR x2 y2) = (NUMPAIR x2 y2).
Proof. exact (eq_refl (NUMPAIR x2 y2)). Qed.
Lemma lem1051945 (x1 : nat) (x2 : nat) (y1 : nat) (y2 : nat) (h1 : term39 x1 x2 y1 y2) : ((NUMPAIR x1 y1) = (NUMPAIR x2 y2)) = ((NUMPAIR x2 y2) = (NUMPAIR x2 y2)).
Proof. exact (MK_COMB (@lem1051943 x1 x2 y1 y2 h1) (@lem1051944 x2 y2)). Qed.
Lemma lem1051947 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1051948 (x : nat) : (x = x) = True.
Proof. exact (@lem1051947 nat x). Qed.
Lemma lem1051949 (x2 : nat) (y2 : nat) : ((NUMPAIR x2 y2) = (NUMPAIR x2 y2)) = True.
Proof. exact (@lem1051948 (NUMPAIR x2 y2)). Qed.
Lemma lem1051950 (x1 : nat) (x2 : nat) (y1 : nat) (y2 : nat) (h1 : term39 x1 x2 y1 y2) : ((NUMPAIR x1 y1) = (NUMPAIR x2 y2)) = True.
Proof. exact (TRANS (@lem1051945 x1 x2 y1 y2 h1) (@lem1051949 x2 y2)). Qed.
Lemma lem1051951 (x1 : nat) (x2 : nat) (y1 : nat) (y2 : nat) (h1 : term39 x1 x2 y1 y2) : True = ((NUMPAIR x1 y1) = (NUMPAIR x2 y2)).
Proof. exact (SYM (@lem1051950 x1 x2 y1 y2 h1)). Qed.
Lemma lem1051952 (x1 : nat) (x2 : nat) (y1 : nat) (y2 : nat) (h1 : term39 x1 x2 y1 y2) : (NUMPAIR x1 y1) = (NUMPAIR x2 y2).
Proof. exact (EQ_MP (@lem1051951 x1 x2 y1 y2 h1) (@lem0)). Qed.
Lemma lem1051954 (y1 : nat) (y2 : nat) (x1 : nat) (x2 : nat) : term38 y1 y2 x1 x2.
Proof. exact (EQ_MP (@lem1051919 y1 y2 x1 x2) (@lem1051918 y1 x1 x2 y2)). Qed.
Lemma lem1051955 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : (NUMPAIR x1 y1) = (NUMPAIR x2 y2)) : x1 = x2.
Proof. exact (@lem1051954 y1 y2 x1 x2 (@lem1051921 x1 y1 x2 y2 h1)). Qed.
Lemma lem1051956 (x2 : nat) (y1 : nat) (y2 : nat) : (term41 x2 y1 y2) = (term41 x2 y1 y2).
Proof. exact (eq_refl (term41 x2 y1 y2)). Qed.
Lemma lem1051957 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : (NUMPAIR x1 y1) = (NUMPAIR x2 y2)) : (term42 x2 y1 y2 x1) = (term43 y1 y2 x2).
Proof. exact (MK_COMB (@lem1051956 x2 y1 y2) (@lem1051955 x1 y1 x2 y2 h1)). Qed.
Lemma lem1051958 (x2 : nat) (y1 : nat) (y2 : nat) : (term43 y1 y2 x2) = (term44 x2 y1 y2).
Proof. exact (eq_refl (term43 y1 y2 x2)). Qed.
Lemma lem1051959 (x2 : nat) (y1 : nat) (y2 : nat) (x1 : nat) : (term45 x2 y1 y2 x1) = (term45 x2 y1 y2 x1).
Proof. exact (eq_refl (term45 x2 y1 y2 x1)). Qed.
Lemma lem1051960 (x1 : nat) (x2 : nat) (y1 : nat) (y2 : nat) : ((term42 x2 y1 y2 x1) = (term43 y1 y2 x2)) = ((term42 x2 y1 y2 x1) = (term44 x2 y1 y2)).
Proof. exact (MK_COMB (@lem1051959 x2 y1 y2 x1) (@lem1051958 x2 y1 y2)). Qed.
Lemma lem1051961 (x1 : nat) (x2 : nat) (y1 : nat) (y2 : nat) : (term42 x2 y1 y2 x1) = (term39 x1 x2 y1 y2).
Proof. exact (eq_refl (term42 x2 y1 y2 x1)). Qed.
Lemma lem1051962 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1051963 (x1 : nat) (x2 : nat) (y1 : nat) (y2 : nat) : (term45 x2 y1 y2 x1) = (term46 x1 x2 y1 y2).
Proof. exact (MK_COMB (@lem1051962) (@lem1051961 x1 x2 y1 y2)). Qed.
Lemma lem1051964 (x2 : nat) (y1 : nat) (y2 : nat) : (term44 x2 y1 y2) = (term44 x2 y1 y2).
Proof. exact (eq_refl (term44 x2 y1 y2)). Qed.
Lemma lem1051965 (x1 : nat) (x2 : nat) (y1 : nat) (y2 : nat) : ((term42 x2 y1 y2 x1) = (term44 x2 y1 y2)) = ((term39 x1 x2 y1 y2) = (term44 x2 y1 y2)).
Proof. exact (MK_COMB (@lem1051963 x1 x2 y1 y2) (@lem1051964 x2 y1 y2)). Qed.
Lemma lem1051966 (x1 : nat) (x2 : nat) (y1 : nat) (y2 : nat) : ((term42 x2 y1 y2 x1) = (term43 y1 y2 x2)) = ((term39 x1 x2 y1 y2) = (term44 x2 y1 y2)).
Proof. exact (TRANS (@lem1051960 x1 x2 y1 y2) (@lem1051965 x1 x2 y1 y2)). Qed.
Lemma lem1051967 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : (NUMPAIR x1 y1) = (NUMPAIR x2 y2)) : (term39 x1 x2 y1 y2) = (term44 x2 y1 y2).
Proof. exact (EQ_MP (@lem1051966 x1 x2 y1 y2) (@lem1051957 x1 y1 x2 y2 h1)). Qed.
Lemma lem1051968 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : (NUMPAIR x1 y1) = (NUMPAIR x2 y2)) : (term44 x2 y1 y2) = (term39 x1 x2 y1 y2).
Proof. exact (SYM (@lem1051967 x1 y1 x2 y2 h1)). Qed.
Lemma lem1051969 (y1 : nat) (x2 : nat) (y2 : nat) : (term47 y1 x2 y2) = (term47 y1 x2 y2).
Proof. exact (eq_refl (term47 y1 x2 y2)). Qed.
Lemma lem1051970 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : (NUMPAIR x1 y1) = (NUMPAIR x2 y2)) : (term48 y1 x2 y2 x1) = (term49 y1 y2 x2).
Proof. exact (MK_COMB (@lem1051969 y1 x2 y2) (@lem1051955 x1 y1 x2 y2 h1)). Qed.
Lemma lem1051971 (y1 : nat) (x2 : nat) (y2 : nat) : (term49 y1 y2 x2) = ((NUMPAIR x2 y1) = (NUMPAIR x2 y2)).
Proof. exact (eq_refl (term49 y1 y2 x2)). Qed.
Lemma lem1051972 (y1 : nat) (x2 : nat) (y2 : nat) (x1 : nat) : (term50 y1 x2 y2 x1) = (term50 y1 x2 y2 x1).
Proof. exact (eq_refl (term50 y1 x2 y2 x1)). Qed.
Lemma lem1051973 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : ((term48 y1 x2 y2 x1) = (term49 y1 y2 x2)) = ((term48 y1 x2 y2 x1) = ((NUMPAIR x2 y1) = (NUMPAIR x2 y2))).
Proof. exact (MK_COMB (@lem1051972 y1 x2 y2 x1) (@lem1051971 y1 x2 y2)). Qed.
Lemma lem1051974 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term48 y1 x2 y2 x1) = ((NUMPAIR x1 y1) = (NUMPAIR x2 y2)).
Proof. exact (eq_refl (term48 y1 x2 y2 x1)). Qed.
Lemma lem1051975 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1051976 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : (term50 y1 x2 y2 x1) = (term51 x1 y1 x2 y2).
Proof. exact (MK_COMB (@lem1051975) (@lem1051974 x1 y1 x2 y2)). Qed.
Lemma lem1051977 (y1 : nat) (x2 : nat) (y2 : nat) : ((NUMPAIR x2 y1) = (NUMPAIR x2 y2)) = ((NUMPAIR x2 y1) = (NUMPAIR x2 y2)).
Proof. exact (eq_refl ((NUMPAIR x2 y1) = (NUMPAIR x2 y2))). Qed.
Lemma lem1051978 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : ((term48 y1 x2 y2 x1) = ((NUMPAIR x2 y1) = (NUMPAIR x2 y2))) = (((NUMPAIR x1 y1) = (NUMPAIR x2 y2)) = ((NUMPAIR x2 y1) = (NUMPAIR x2 y2))).
Proof. exact (MK_COMB (@lem1051976 x1 y1 x2 y2) (@lem1051977 y1 x2 y2)). Qed.
Lemma lem1051979 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : ((term48 y1 x2 y2 x1) = (term49 y1 y2 x2)) = (((NUMPAIR x1 y1) = (NUMPAIR x2 y2)) = ((NUMPAIR x2 y1) = (NUMPAIR x2 y2))).
Proof. exact (TRANS (@lem1051973 x1 y1 x2 y2) (@lem1051978 x1 y1 x2 y2)). Qed.
Lemma lem1051980 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : (NUMPAIR x1 y1) = (NUMPAIR x2 y2)) : ((NUMPAIR x1 y1) = (NUMPAIR x2 y2)) = ((NUMPAIR x2 y1) = (NUMPAIR x2 y2)).
Proof. exact (EQ_MP (@lem1051979 x1 y1 x2 y2) (@lem1051970 x1 y1 x2 y2 h1)). Qed.
Lemma lem1051981 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : (NUMPAIR x1 y1) = (NUMPAIR x2 y2)) : (NUMPAIR x2 y1) = (NUMPAIR x2 y2).
Proof. exact (EQ_MP (@lem1051980 x1 y1 x2 y2 h1) (@lem1051921 x1 y1 x2 y2 h1)). Qed.
Lemma lem1051989 (x : nat) (y : nat) : (NUMPAIR x y) = (term30 x y).
Proof. exact (EQ_MP (@lem1051907 x y) (@lem1051906 x y)). Qed.
Lemma lem1051990 (x2 : nat) (y1 : nat) : (NUMPAIR x2 y1) = (term30 x2 y1).
Proof. exact (@lem1051989 x2 y1). Qed.
Lemma lem1051991 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1051992 (x2 : nat) (y1 : nat) : (term40 x2 y1) = (term52 x2 y1).
Proof. exact (MK_COMB (@lem1051991) (@lem1051990 x2 y1)). Qed.
Lemma lem1051994 (x : nat) (y : nat) : (NUMPAIR x y) = (term30 x y).
Proof. exact (EQ_MP (@lem1051907 x y) (@lem1051906 x y)). Qed.
Lemma lem1051995 (x2 : nat) (y2 : nat) : (NUMPAIR x2 y2) = (term30 x2 y2).
Proof. exact (@lem1051994 x2 y2). Qed.
Lemma lem1051996 (y1 : nat) (x2 : nat) (y2 : nat) : ((NUMPAIR x2 y1) = (NUMPAIR x2 y2)) = ((term30 x2 y1) = (term30 x2 y2)).
Proof. exact (MK_COMB (@lem1051992 x2 y1) (@lem1051995 x2 y2)). Qed.
Lemma lem1051999 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1052000 (y1 : nat) (x2 : nat) (y2 : nat) : (term53 y1 x2 y2) = (term54 y1 x2 y2).
Proof. exact (MK_COMB (@lem1051999) (@lem1051996 y1 x2 y2)). Qed.
Lemma lem1052004 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1052005 (x : nat) : (x = x) = True.
Proof. exact (@lem1052004 nat x). Qed.
Lemma lem1052006 (x2 : nat) : (x2 = x2) = True.
Proof. exact (@lem1052005 x2). Qed.
Lemma lem1052007 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1052008 (x2 : nat) : (term55 x2) = (and True).
Proof. exact (MK_COMB (@lem1052007) (@lem1052006 x2)). Qed.
Lemma lem1052011 (y1 : nat) (y2 : nat) : (y1 = y2) = (y1 = y2).
Proof. exact (eq_refl (y1 = y2)). Qed.
Lemma lem1052012 (x2 : nat) (y1 : nat) (y2 : nat) : (term44 x2 y1 y2) = (term56 y1 y2).
Proof. exact (MK_COMB (@lem1052008 x2) (@lem1052011 y1 y2)). Qed.
Lemma lem1052014 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1052015 (y1 : nat) (y2 : nat) : (term56 y1 y2) = (y1 = y2).
Proof. exact (@lem1052014 (y1 = y2)). Qed.
Lemma lem1052018 (x2 : nat) (y1 : nat) (y2 : nat) : (term44 x2 y1 y2) = (y1 = y2).
Proof. exact (TRANS (@lem1052012 x2 y1 y2) (@lem1052015 y1 y2)). Qed.
Lemma lem1052019 (x2 : nat) (y1 : nat) (y2 : nat) : (term57 x2 y1 y2) = (term58 x2 y1 y2).
Proof. exact (MK_COMB (@lem1052000 y1 x2 y2) (@lem1052018 x2 y1 y2)). Qed.
Lemma lem1052024 (x2 : nat) (y1 : nat) (y2 : nat) : (term58 x2 y1 y2) = (term57 x2 y1 y2).
Proof. exact (SYM (@lem1052019 x2 y1 y2)). Qed.
Lemma lem1052030 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (Nat.mul m p)) = (term26 m n p).
Proof. exact (EQ_MP (@lem1051901 m n p) (@lem1051900 m n p)). Qed.
Lemma lem1052031 (x2 : nat) (y1 : nat) (y2 : nat) : ((term30 x2 y1) = (term30 x2 y2)) = (term59 x2 y1 y2).
Proof. exact (@lem1052030 (term60 x2) (term61 y1) (term61 y2)). Qed.
Lemma lem1052035 (m : nat) (n : nat) : ((Nat.pow m n) = (NUMERAL 0)) = (term15 m n).
Proof. exact (EQ_MP (@lem1051883 m n) (@lem1051882 m n)). Qed.
Lemma lem1052036 (x2 : nat) : ((term60 x2) = (NUMERAL 0)) = (term62 x2).
Proof. exact (@lem1052035 term63 x2). Qed.
Lemma lem1052040 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem1051627 m n) (@lem1051626 m n)). Qed.
Lemma lem1052041 : (term63 = (NUMERAL 0)) = (term64 = 0).
Proof. exact (@lem1052040 term64 0). Qed.
Lemma lem1052043 (n : nat) : ((BIT0 n) = 0) = (n = 0).
Proof. exact (EQ_MP (@lem1051619 n) (@lem1051618 n)). Qed.
Lemma lem1052044 : (term64 = 0) = ((BIT1 0) = 0).
Proof. exact (@lem1052043 (BIT1 0)). Qed.
Lemma lem1052046 (n : nat) : ((BIT1 n) = 0) = False.
Proof. exact (EQ_MP (@lem1051615 n) (@lem1051614 n)). Qed.
Lemma lem1052047 : ((BIT1 0) = 0) = False.
Proof. exact (@lem1052046 0). Qed.
Lemma lem1052048 : (term64 = 0) = False.
Proof. exact (TRANS (@lem1052044) (@lem1052047)). Qed.
Lemma lem1052049 : (term63 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1052041) (@lem1052048)). Qed.
Lemma lem1052050 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1052051 : term65 = (and False).
Proof. exact (MK_COMB (@lem1052050) (@lem1052049)). Qed.
Lemma lem1052054 (x2 : nat) : (term66 x2) = (term66 x2).
Proof. exact (eq_refl (term66 x2)). Qed.
Lemma lem1052055 (x2 : nat) : (term62 x2) = (term67 x2).
Proof. exact (MK_COMB (@lem1052051) (@lem1052054 x2)). Qed.
Lemma lem1052057 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1052058 (x2 : nat) : (term67 x2) = False.
Proof. exact (@lem1052057 (term66 x2)). Qed.
Lemma lem1052059 (x2 : nat) : (term62 x2) = False.
Proof. exact (TRANS (@lem1052055 x2) (@lem1052058 x2)). Qed.
Lemma lem1052060 (x2 : nat) : ((term60 x2) = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1052036 x2) (@lem1052059 x2)). Qed.
Lemma lem1052061 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1052062 (x2 : nat) : (term68 x2) = (or False).
Proof. exact (MK_COMB (@lem1052061) (@lem1052060 x2)). Qed.
Lemma lem1052064 (p : nat) (m : nat) (n : nat) : ((Nat.add m p) = (Nat.add n p)) = (m = n).
Proof. exact (EQ_MP (@lem1051892 p m n) (@lem1051891 m n p)). Qed.
Lemma lem1052065 (y1 : nat) (y2 : nat) : ((term61 y1) = (term61 y2)) = ((term69 y1) = (term69 y2)).
Proof. exact (@lem1052064 term70 (term69 y1) (term69 y2)). Qed.
Lemma lem1052067 (m : nat) (n : nat) (p : nat) : ((Nat.mul m n) = (Nat.mul m p)) = (term26 m n p).
Proof. exact (EQ_MP (@lem1051901 m n p) (@lem1051900 m n p)). Qed.
Lemma lem1052068 (y1 : nat) (y2 : nat) : ((term69 y1) = (term69 y2)) = (term71 y1 y2).
Proof. exact (@lem1052067 term63 y1 y2). Qed.
Lemma lem1052071 (y1 : nat) (y2 : nat) : ((term61 y1) = (term61 y2)) = (term71 y1 y2).
Proof. exact (TRANS (@lem1052065 y1 y2) (@lem1052068 y1 y2)). Qed.
Lemma lem1052073 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem1051627 m n) (@lem1051626 m n)). Qed.
Lemma lem1052074 : (term63 = (NUMERAL 0)) = (term64 = 0).
Proof. exact (@lem1052073 term64 0). Qed.
Lemma lem1052076 (n : nat) : ((BIT0 n) = 0) = (n = 0).
Proof. exact (EQ_MP (@lem1051619 n) (@lem1051618 n)). Qed.
Lemma lem1052077 : (term64 = 0) = ((BIT1 0) = 0).
Proof. exact (@lem1052076 (BIT1 0)). Qed.
Lemma lem1052079 (n : nat) : ((BIT1 n) = 0) = False.
Proof. exact (EQ_MP (@lem1051615 n) (@lem1051614 n)). Qed.
Lemma lem1052080 : ((BIT1 0) = 0) = False.
Proof. exact (@lem1052079 0). Qed.
Lemma lem1052081 : (term64 = 0) = False.
Proof. exact (TRANS (@lem1052077) (@lem1052080)). Qed.
Lemma lem1052082 : (term63 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem1052074) (@lem1052081)). Qed.
Lemma lem1052083 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1052084 : term72 = (or False).
Proof. exact (MK_COMB (@lem1052083) (@lem1052082)). Qed.
Lemma lem1052087 (y1 : nat) (y2 : nat) : (y1 = y2) = (y1 = y2).
Proof. exact (eq_refl (y1 = y2)). Qed.
Lemma lem1052088 (y1 : nat) (y2 : nat) : (term71 y1 y2) = (term73 y1 y2).
Proof. exact (MK_COMB (@lem1052084) (@lem1052087 y1 y2)). Qed.
Lemma lem1052090 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1052091 (y1 : nat) (y2 : nat) : (term73 y1 y2) = (y1 = y2).
Proof. exact (@lem1052090 (y1 = y2)). Qed.
Lemma lem1052094 (y1 : nat) (y2 : nat) : (term71 y1 y2) = (y1 = y2).
Proof. exact (TRANS (@lem1052088 y1 y2) (@lem1052091 y1 y2)). Qed.
Lemma lem1052095 (y1 : nat) (y2 : nat) : ((term61 y1) = (term61 y2)) = (y1 = y2).
Proof. exact (TRANS (@lem1052071 y1 y2) (@lem1052094 y1 y2)). Qed.
Lemma lem1052096 (x2 : nat) (y1 : nat) (y2 : nat) : (term59 x2 y1 y2) = (term73 y1 y2).
Proof. exact (MK_COMB (@lem1052062 x2) (@lem1052095 y1 y2)). Qed.
Lemma lem1052098 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1052099 (y1 : nat) (y2 : nat) : (term73 y1 y2) = (y1 = y2).
Proof. exact (@lem1052098 (y1 = y2)). Qed.
Lemma lem1052102 (x2 : nat) (y1 : nat) (y2 : nat) : (term59 x2 y1 y2) = (y1 = y2).
Proof. exact (TRANS (@lem1052096 x2 y1 y2) (@lem1052099 y1 y2)). Qed.
Lemma lem1052103 (x2 : nat) (y1 : nat) (y2 : nat) : ((term30 x2 y1) = (term30 x2 y2)) = (y1 = y2).
Proof. exact (TRANS (@lem1052031 x2 y1 y2) (@lem1052102 x2 y1 y2)). Qed.
Lemma lem1052104 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1052105 (x2 : nat) (y1 : nat) (y2 : nat) : (term54 y1 x2 y2) = (term74 y1 y2).
Proof. exact (MK_COMB (@lem1052104) (@lem1052103 x2 y1 y2)). Qed.
Lemma lem1052108 (y1 : nat) (y2 : nat) : (y1 = y2) = (y1 = y2).
Proof. exact (eq_refl (y1 = y2)). Qed.
Lemma lem1052109 (x2 : nat) (y1 : nat) (y2 : nat) : (term58 x2 y1 y2) = (term75 y1 y2).
Proof. exact (MK_COMB (@lem1052105 x2 y1 y2) (@lem1052108 y1 y2)). Qed.
Lemma lem1052113 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1052114 (y1 : nat) (y2 : nat) : (term75 y1 y2) = True.
Proof. exact (@lem1052113 (y1 = y2)). Qed.
Lemma lem1052115 (x2 : nat) (y1 : nat) (y2 : nat) : (term58 x2 y1 y2) = True.
Proof. exact (TRANS (@lem1052109 x2 y1 y2) (@lem1052114 y1 y2)). Qed.
Lemma lem1052116 (x2 : nat) (y1 : nat) (y2 : nat) : True = (term58 x2 y1 y2).
Proof. exact (SYM (@lem1052115 x2 y1 y2)). Qed.
Lemma lem1052117 (x2 : nat) (y1 : nat) (y2 : nat) : term58 x2 y1 y2.
Proof. exact (EQ_MP (@lem1052116 x2 y1 y2) (@lem0)). Qed.
Lemma lem1052118 (x2 : nat) (y1 : nat) (y2 : nat) : term57 x2 y1 y2.
Proof. exact (EQ_MP (@lem1052024 x2 y1 y2) (@lem1052117 x2 y1 y2)). Qed.
Lemma lem1052119 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : (NUMPAIR x1 y1) = (NUMPAIR x2 y2)) : term44 x2 y1 y2.
Proof. exact (@lem1052118 x2 y1 y2 (@lem1051981 x1 y1 x2 y2 h1)). Qed.
Lemma lem1052121 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) (h1 : (NUMPAIR x1 y1) = (NUMPAIR x2 y2)) : term39 x1 x2 y1 y2.
Proof. exact (EQ_MP (@lem1051968 x1 y1 x2 y2 h1) (@lem1052119 x1 y1 x2 y2 h1)). Qed.
Lemma lem1052122 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : term76 x1 y1 x2 y2.
Proof. exact (fun h0 : term39 x1 x2 y1 y2 => @lem1051952 x1 x2 y1 y2 h0). Qed.
Lemma lem1052123 (x1 : nat) (x2 : nat) (y1 : nat) (y2 : nat) : term77 x1 x2 y1 y2.
Proof. exact (fun h0 : (NUMPAIR x1 y1) = (NUMPAIR x2 y2) => @lem1052121 x1 y1 x2 y2 h0). Qed.
Lemma lem1052124 (x1 : nat) (y1 : nat) (x2 : nat) (y2 : nat) : term78 x1 y1 x2 y2.
Proof. exact (conj (@lem1052123 x1 x2 y1 y2) (@lem1052122 x1 y1 x2 y2)). Qed.
Lemma lem1052125 (x1 : nat) (x2 : nat) (y1 : nat) (y2 : nat) : (term78 x1 y1 x2 y2) = (((NUMPAIR x1 y1) = (NUMPAIR x2 y2)) = (term39 x1 x2 y1 y2)).
Proof. exact (@lem32 ((NUMPAIR x1 y1) = (NUMPAIR x2 y2)) (term39 x1 x2 y1 y2)). Qed.
Lemma lem1052126 (x1 : nat) (x2 : nat) (y1 : nat) (y2 : nat) : ((NUMPAIR x1 y1) = (NUMPAIR x2 y2)) = (term39 x1 x2 y1 y2).
Proof. exact (EQ_MP (@lem1052125 x1 x2 y1 y2) (@lem1052124 x1 y1 x2 y2)). Qed.
Lemma lem1052131 (x1 : nat) (x2 : nat) (y1 : nat) : term79 x1 x2 y1.
Proof. exact (fun y2 : nat => @lem1052126 x1 x2 y1 y2). Qed.
Lemma lem1052136 (x1 : nat) (y1 : nat) : term80 x1 y1.
Proof. exact (fun x2 : nat => @lem1052131 x1 x2 y1). Qed.
Lemma lem1052141 (x1 : nat) : term81 x1.
Proof. exact (fun y1 : nat => @lem1052136 x1 y1). Qed.
Lemma lem1052146 : term82.
Proof. exact (fun x1 : nat => @lem1052141 x1). Qed.
