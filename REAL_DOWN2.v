Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_DOWN2_term_abbrevs.
Require Import REAL_DOWN_spec.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1339697_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483480_spec.
Require Import thm1483482_spec.
Require Import thm1483484_spec.
Require Import thm1483488_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483523_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17045_spec.
Require Import thm17362_spec.
Require Import thm1820_spec.
Require Import thm19158_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Lemma lem1634774 (d2 : real) : term0 d2.
Proof. exact (@lem1634773 d2). Qed.
Lemma lem1634775 (d2 : real) : (term0 d2) = (term1 d2).
Proof. exact (eq_refl (term0 d2)). Qed.
Lemma lem1634776 (d2 : real) : term1 d2.
Proof. exact (EQ_MP (@lem1634775 d2) (@lem1634774 d2)). Qed.
Lemma lem1634777 (d1 : real) : term0 d1.
Proof. exact (@lem1634773 d1). Qed.
Lemma lem1634778 (d1 : real) : (term0 d1) = (term1 d1).
Proof. exact (eq_refl (term0 d1)). Qed.
Lemma lem1634779 (d1 : real) : term1 d1.
Proof. exact (EQ_MP (@lem1634778 d1) (@lem1634777 d1)). Qed.
Lemma lem1634780 (d1 : real) : term2 d1.
Proof. exact (@lem1339697 d1). Qed.
Lemma lem1634781 (d1 : real) : (term2 d1) = (term3 d1).
Proof. exact (eq_refl (term2 d1)). Qed.
Lemma lem1634782 (d1 : real) : term3 d1.
Proof. exact (EQ_MP (@lem1634781 d1) (@lem1634780 d1)). Qed.
Lemma lem1634783 (d1 : real) (d2 : real) : term4 d1 d2.
Proof. exact (@lem1634782 d1 d2). Qed.
Lemma lem1634784 (d2 : real) (d1 : real) : (term4 d1 d2) = (term5 d2 d1).
Proof. exact (eq_refl (term4 d1 d2)). Qed.
Lemma lem1634785 (d2 : real) (d1 : real) : term5 d2 d1.
Proof. exact (EQ_MP (@lem1634784 d2 d1) (@lem1634783 d1 d2)). Qed.
Lemma lem1634786 (d1 : real) (d2 : real) (h1 : real_le d1 d2) : real_le d1 d2.
Proof. exact (h1). Qed.
Lemma lem1634787 (d2 : real) (d1 : real) (h1 : real_le d2 d1) : real_le d2 d1.
Proof. exact (h1). Qed.
Lemma lem1634788 (d1 : real) (d2 : real) (h1 : term6 d1 d2) : term6 d1 d2.
Proof. exact (h1). Qed.
Lemma lem1634789 (d2 : real) (h1 : term7 d2) : term7 d2.
Proof. exact (h1). Qed.
Lemma lem1634790 (d1 : real) (h1 : term7 d1) : term7 d1.
Proof. exact (h1). Qed.
Lemma lem1634791 (d1 : real) : (term7 d1) = ((term7 d1) = True).
Proof. exact (@lem7 (term7 d1)). Qed.
Lemma lem1634802 (d1 : real) (h1 : term7 d1) : (term7 d1) = True.
Proof. exact (EQ_MP (@lem1634791 d1) (@lem1634790 d1 h1)). Qed.
Lemma lem1634803 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1634804 (d1 : real) (h1 : term7 d1) : (term8 d1) = (imp True).
Proof. exact (MK_COMB (@lem1634803) (@lem1634802 d1 h1)). Qed.
Lemma lem1634811 (d1 : real) : (term9 d1) = (term9 d1).
Proof. exact (eq_refl (term9 d1)). Qed.
Lemma lem1634812 (d1 : real) (h1 : term7 d1) : (term1 d1) = (term10 d1).
Proof. exact (MK_COMB (@lem1634804 d1 h1) (@lem1634811 d1)). Qed.
Lemma lem1634814 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1634815 (d1 : real) : (term10 d1) = (term9 d1).
Proof. exact (@lem1634814 (term9 d1)). Qed.
Lemma lem1634822 (d1 : real) (h1 : term7 d1) : (term1 d1) = (term9 d1).
Proof. exact (TRANS (@lem1634812 d1 h1) (@lem1634815 d1)). Qed.
Lemma lem1634823 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1634824 (d1 : real) (h1 : term7 d1) : (term11 d1) = (term12 d1).
Proof. exact (MK_COMB (@lem1634823) (@lem1634822 d1 h1)). Qed.
Lemma lem1634833 (d1 : real) (d2 : real) : (term13 d1 d2) = (term13 d1 d2).
Proof. exact (eq_refl (term13 d1 d2)). Qed.
Lemma lem1634834 (d2 : real) (d1 : real) (h1 : term7 d1) : (term14 d1 d2) = (term15 d1 d2).
Proof. exact (MK_COMB (@lem1634824 d1 h1) (@lem1634833 d1 d2)). Qed.
Lemma lem1634837 (d2 : real) (d1 : real) (h1 : term7 d1) : (term15 d1 d2) = (term14 d1 d2).
Proof. exact (SYM (@lem1634834 d2 d1 h1)). Qed.
Lemma lem1634840 (d2 : real) : (term7 d2) = ((term7 d2) = True).
Proof. exact (@lem7 (term7 d2)). Qed.
Lemma lem1634849 (d2 : real) (h1 : term7 d2) : (term7 d2) = True.
Proof. exact (EQ_MP (@lem1634840 d2) (@lem1634789 d2 h1)). Qed.
Lemma lem1634850 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1634851 (d2 : real) (h1 : term7 d2) : (term8 d2) = (imp True).
Proof. exact (MK_COMB (@lem1634850) (@lem1634849 d2 h1)). Qed.
Lemma lem1634858 (d2 : real) : (term9 d2) = (term9 d2).
Proof. exact (eq_refl (term9 d2)). Qed.
Lemma lem1634859 (d2 : real) (h1 : term7 d2) : (term1 d2) = (term10 d2).
Proof. exact (MK_COMB (@lem1634851 d2 h1) (@lem1634858 d2)). Qed.
Lemma lem1634861 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1634862 (d2 : real) : (term10 d2) = (term9 d2).
Proof. exact (@lem1634861 (term9 d2)). Qed.
Lemma lem1634869 (d2 : real) (h1 : term7 d2) : (term1 d2) = (term9 d2).
Proof. exact (TRANS (@lem1634859 d2 h1) (@lem1634862 d2)). Qed.
Lemma lem1634870 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1634871 (d2 : real) (h1 : term7 d2) : (term11 d2) = (term12 d2).
Proof. exact (MK_COMB (@lem1634870) (@lem1634869 d2 h1)). Qed.
Lemma lem1634880 (d1 : real) (d2 : real) : (term13 d1 d2) = (term13 d1 d2).
Proof. exact (eq_refl (term13 d1 d2)). Qed.
Lemma lem1634881 (d1 : real) (d2 : real) (h1 : term7 d2) : (term16 d1 d2) = (term17 d1 d2).
Proof. exact (MK_COMB (@lem1634871 d2 h1) (@lem1634880 d1 d2)). Qed.
Lemma lem1634884 (d1 : real) (d2 : real) (h1 : term7 d2) : (term17 d1 d2) = (term16 d1 d2).
Proof. exact (SYM (@lem1634881 d1 d2 h1)). Qed.
Lemma lem1634885 (d1 : real) (h1 : term9 d1) : term9 d1.
Proof. exact (h1). Qed.
Lemma lem1634886 (e : real) (d1 : real) (h1 : term18 e d1) : term18 e d1.
Proof. exact (h1). Qed.
Lemma lem1634887 (e : real) (d1 : real) (h1 : real_lt e d1) : real_lt e d1.
Proof. exact (h1). Qed.
Lemma lem1634888 (e : real) (h1 : term7 e) : term7 e.
Proof. exact (h1). Qed.
Lemma lem1634889 (d2 : real) (h1 : term9 d2) : term9 d2.
Proof. exact (h1). Qed.
Lemma lem1634890 (e : real) (d2 : real) (h1 : term18 e d2) : term18 e d2.
Proof. exact (h1). Qed.
Lemma lem1634891 (e : real) (d2 : real) (h1 : real_lt e d2) : real_lt e d2.
Proof. exact (h1). Qed.
Lemma lem1634892 (e : real) (h1 : term7 e) : term7 e.
Proof. exact (h1). Qed.
Lemma lem1634893 (d1 : real) (d2 : real) (h1 : term7 d1) (h2 : term7 d2) : term6 d2 d1.
Proof. exact (conj (@lem1634789 d2 h2) (@lem1634790 d1 h1)). Qed.
Lemma lem1634894 (d1 : real) (d2 : real) (h1 : real_le d1 d2) (h2 : term7 d1) (h3 : term7 d2) : term19 d2 d1.
Proof. exact (conj (@lem1634786 d1 d2 h1) (@lem1634893 d1 d2 h2 h3)). Qed.
Lemma lem1634895 (d1 : real) (d2 : real) (e : real) (h1 : real_le d1 d2) (h2 : term7 d1) (h3 : term7 d2) (h4 : term7 e) : term20 e d2 d1.
Proof. exact (conj (@lem1634888 e h4) (@lem1634894 d1 d2 h1 h2 h3)). Qed.
Lemma lem1634896 (d1 : real) (d2 : real) (e : real) (h1 : real_le d1 d2) (h2 : real_lt e d1) (h3 : term7 d1) (h4 : term7 d2) (h5 : term7 e) : term21 e d2 d1.
Proof. exact (conj (@lem1634887 e d1 h2) (@lem1634895 d1 d2 e h1 h3 h4 h5)). Qed.
Lemma lem1634897 (d1 : real) (d2 : real) (h1 : term7 d1) (h2 : term7 d2) : term6 d2 d1.
Proof. exact (conj (@lem1634789 d2 h2) (@lem1634790 d1 h1)). Qed.
Lemma lem1634898 (d1 : real) (d2 : real) (h1 : real_le d2 d1) (h2 : term7 d1) (h3 : term7 d2) : term22 d2 d1.
Proof. exact (conj (@lem1634787 d2 d1 h1) (@lem1634897 d1 d2 h2 h3)). Qed.
Lemma lem1634899 (d1 : real) (d2 : real) (e : real) (h1 : real_le d2 d1) (h2 : term7 d1) (h3 : term7 d2) (h4 : term7 e) : term23 e d2 d1.
Proof. exact (conj (@lem1634892 e h4) (@lem1634898 d1 d2 h1 h2 h3)). Qed.
Lemma lem1634900 (d1 : real) (d2 : real) (e : real) (h1 : real_le d2 d1) (h2 : real_lt e d2) (h3 : term7 d1) (h4 : term7 d2) (h5 : term7 e) : term24 e d2 d1.
Proof. exact (conj (@lem1634891 e d2 h2) (@lem1634899 d1 d2 e h1 h3 h4 h5)). Qed.
Lemma lem1634942 (d1 : real) (e : real) (d2 : real) : (term25 d1 e d2) = (term26 d1 e d2).
Proof. exact (@lem17045 (real_lt e d1) (real_lt e d2)). Qed.
Lemma lem1634944 (e : real) : (term27 e) = (term27 e).
Proof. exact (eq_refl (term27 e)). Qed.
Lemma lem1634945 (d1 : real) (e : real) (d2 : real) : (term28 d1 e d2) = (term29 d1 e d2).
Proof. exact (MK_COMB (@lem1634944 e) (@lem1634942 d1 e d2)). Qed.
Lemma lem1634946 (d1 : real) (e : real) (d2 : real) : (term30 d1 e d2) = (term28 d1 e d2).
Proof. exact (@lem17045 (term7 e) (term31 d1 e d2)). Qed.
Lemma lem1634947 (d1 : real) (e : real) (d2 : real) : (term30 d1 e d2) = (term29 d1 e d2).
Proof. exact (TRANS (@lem1634946 d1 e d2) (@lem1634945 d1 e d2)). Qed.
Lemma lem1634949 (e : real) (d2 : real) (d1 : real) : (term32 e d2 d1) = (term32 e d2 d1).
Proof. exact (eq_refl (term32 e d2 d1)). Qed.
Lemma lem1634950 (d1 : real) (e : real) (d2 : real) : (term33 d1 e d2) = (term34 d1 e d2).
Proof. exact (MK_COMB (@lem1634949 e d2 d1) (@lem1634947 d1 e d2)). Qed.
Lemma lem1634951 (d1 : real) (e : real) (d2 : real) : (term35 d1 e d2) = (term33 d1 e d2).
Proof. exact (@lem17362 (term21 e d2 d1) (term36 d1 e d2)). Qed.
Lemma lem1634989 (d1 : real) (e : real) (d2 : real) : (term35 d1 e d2) = (term34 d1 e d2).
Proof. exact (TRANS (@lem1634951 d1 e d2) (@lem1634950 d1 e d2)). Qed.
Lemma lem1634990 (d1 : real) (e : real) : (real_lt e d1) = (term37 d1 e).
Proof. exact (@lem1483521 d1 e). Qed.
Lemma lem1635003 (d1 : real) (e : real) : (real_sub d1 e) = (term38 d1 e).
Proof. exact (@lem1483519 d1 e). Qed.
Lemma lem1635004 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1635005 (d1 : real) (e : real) : (term39 d1 e) = (term40 d1 e).
Proof. exact (MK_COMB (@lem1635004) (@lem1635003 d1 e)). Qed.
Lemma lem1635006 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635007 (d1 : real) (e : real) : (term37 d1 e) = (term42 d1 e).
Proof. exact (MK_COMB (@lem1635005 d1 e) (@lem1635006)). Qed.
Lemma lem1635008 (d1 : real) (e : real) : (real_lt e d1) = (term42 d1 e).
Proof. exact (TRANS (@lem1634990 d1 e) (@lem1635007 d1 e)). Qed.
Lemma lem1635009 (e : real) : (term7 e) = (term43 e).
Proof. exact (@lem1483521 e term41). Qed.
Lemma lem1635015 (e : real) : (term44 e) = (term45 e).
Proof. exact (@lem1483519 e term41). Qed.
Lemma lem1635017 (x : nat) : (term46 x) = term41.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1635018 : term47 = term41.
Proof. exact (@lem1635017 term48). Qed.
Lemma lem1635019 (e : real) : (real_add e) = (real_add e).
Proof. exact (eq_refl (real_add e)). Qed.
Lemma lem1635020 (e : real) : (term45 e) = (term49 e).
Proof. exact (MK_COMB (@lem1635019 e) (@lem1635018)). Qed.
Lemma lem1635021 (e : real) : (term49 e) = e.
Proof. exact (@lem1483450 e). Qed.
Lemma lem1635022 (e : real) : (term45 e) = e.
Proof. exact (TRANS (@lem1635020 e) (@lem1635021 e)). Qed.
Lemma lem1635024 (e : real) : (term44 e) = e.
Proof. exact (TRANS (@lem1635015 e) (@lem1635022 e)). Qed.
Lemma lem1635025 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1635026 (e : real) : (term50 e) = (real_gt e).
Proof. exact (MK_COMB (@lem1635025) (@lem1635024 e)). Qed.
Lemma lem1635027 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635028 (e : real) : (term43 e) = (term51 e).
Proof. exact (MK_COMB (@lem1635026 e) (@lem1635027)). Qed.
Lemma lem1635029 (e : real) : (term7 e) = (term51 e).
Proof. exact (TRANS (@lem1635009 e) (@lem1635028 e)). Qed.
Lemma lem1635030 (d2 : real) (d1 : real) : (real_le d1 d2) = (term52 d2 d1).
Proof. exact (@lem1483523 d2 d1). Qed.
Lemma lem1635036 (d2 : real) (d1 : real) : (real_sub d2 d1) = (term38 d2 d1).
Proof. exact (@lem1483519 d2 d1). Qed.
Lemma lem1635041 (d1 : real) (d2 : real) : (term38 d2 d1) = (term53 d1 d2).
Proof. exact (@lem1483488 (term54 d1) d2). Qed.
Lemma lem1635043 (d1 : real) (d2 : real) : (real_sub d2 d1) = (term53 d1 d2).
Proof. exact (TRANS (@lem1635036 d2 d1) (@lem1635041 d1 d2)). Qed.
Lemma lem1635044 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1635045 (d1 : real) (d2 : real) : (term55 d2 d1) = (term56 d1 d2).
Proof. exact (MK_COMB (@lem1635044) (@lem1635043 d1 d2)). Qed.
Lemma lem1635046 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635047 (d1 : real) (d2 : real) : (term52 d2 d1) = (term57 d1 d2).
Proof. exact (MK_COMB (@lem1635045 d1 d2) (@lem1635046)). Qed.
Lemma lem1635048 (d1 : real) (d2 : real) : (real_le d1 d2) = (term57 d1 d2).
Proof. exact (TRANS (@lem1635030 d2 d1) (@lem1635047 d1 d2)). Qed.
Lemma lem1635049 (d2 : real) : (term7 d2) = (term43 d2).
Proof. exact (@lem1483521 d2 term41). Qed.
Lemma lem1635055 (d2 : real) : (term44 d2) = (term45 d2).
Proof. exact (@lem1483519 d2 term41). Qed.
Lemma lem1635057 (x : nat) : (term46 x) = term41.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1635058 : term47 = term41.
Proof. exact (@lem1635057 term48). Qed.
Lemma lem1635059 (d2 : real) : (real_add d2) = (real_add d2).
Proof. exact (eq_refl (real_add d2)). Qed.
Lemma lem1635060 (d2 : real) : (term45 d2) = (term49 d2).
Proof. exact (MK_COMB (@lem1635059 d2) (@lem1635058)). Qed.
Lemma lem1635061 (d2 : real) : (term49 d2) = d2.
Proof. exact (@lem1483450 d2). Qed.
Lemma lem1635062 (d2 : real) : (term45 d2) = d2.
Proof. exact (TRANS (@lem1635060 d2) (@lem1635061 d2)). Qed.
Lemma lem1635064 (d2 : real) : (term44 d2) = d2.
Proof. exact (TRANS (@lem1635055 d2) (@lem1635062 d2)). Qed.
Lemma lem1635065 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1635066 (d2 : real) : (term50 d2) = (real_gt d2).
Proof. exact (MK_COMB (@lem1635065) (@lem1635064 d2)). Qed.
Lemma lem1635067 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635068 (d2 : real) : (term43 d2) = (term51 d2).
Proof. exact (MK_COMB (@lem1635066 d2) (@lem1635067)). Qed.
Lemma lem1635069 (d2 : real) : (term7 d2) = (term51 d2).
Proof. exact (TRANS (@lem1635049 d2) (@lem1635068 d2)). Qed.
Lemma lem1635070 (d1 : real) : (term7 d1) = (term43 d1).
Proof. exact (@lem1483521 d1 term41). Qed.
Lemma lem1635076 (d1 : real) : (term44 d1) = (term45 d1).
Proof. exact (@lem1483519 d1 term41). Qed.
Lemma lem1635078 (x : nat) : (term46 x) = term41.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1635079 : term47 = term41.
Proof. exact (@lem1635078 term48). Qed.
Lemma lem1635080 (d1 : real) : (real_add d1) = (real_add d1).
Proof. exact (eq_refl (real_add d1)). Qed.
Lemma lem1635081 (d1 : real) : (term45 d1) = (term49 d1).
Proof. exact (MK_COMB (@lem1635080 d1) (@lem1635079)). Qed.
Lemma lem1635082 (d1 : real) : (term49 d1) = d1.
Proof. exact (@lem1483450 d1). Qed.
Lemma lem1635083 (d1 : real) : (term45 d1) = d1.
Proof. exact (TRANS (@lem1635081 d1) (@lem1635082 d1)). Qed.
Lemma lem1635085 (d1 : real) : (term44 d1) = d1.
Proof. exact (TRANS (@lem1635076 d1) (@lem1635083 d1)). Qed.
Lemma lem1635086 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1635087 (d1 : real) : (term50 d1) = (real_gt d1).
Proof. exact (MK_COMB (@lem1635086) (@lem1635085 d1)). Qed.
Lemma lem1635088 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635089 (d1 : real) : (term43 d1) = (term51 d1).
Proof. exact (MK_COMB (@lem1635087 d1) (@lem1635088)). Qed.
Lemma lem1635090 (d1 : real) : (term7 d1) = (term51 d1).
Proof. exact (TRANS (@lem1635070 d1) (@lem1635089 d1)). Qed.
Lemma lem1635091 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1635092 (d2 : real) : (term58 d2) = (term59 d2).
Proof. exact (MK_COMB (@lem1635091) (@lem1635069 d2)). Qed.
Lemma lem1635093 (d2 : real) (d1 : real) : (term6 d2 d1) = (term60 d2 d1).
Proof. exact (MK_COMB (@lem1635092 d2) (@lem1635090 d1)). Qed.
Lemma lem1635094 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1635095 (d1 : real) (d2 : real) : (term61 d1 d2) = (term62 d1 d2).
Proof. exact (MK_COMB (@lem1635094) (@lem1635048 d1 d2)). Qed.
Lemma lem1635096 (d2 : real) (d1 : real) : (term19 d2 d1) = (term63 d2 d1).
Proof. exact (MK_COMB (@lem1635095 d1 d2) (@lem1635093 d2 d1)). Qed.
Lemma lem1635097 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1635098 (e : real) : (term58 e) = (term59 e).
Proof. exact (MK_COMB (@lem1635097) (@lem1635029 e)). Qed.
Lemma lem1635099 (e : real) (d2 : real) (d1 : real) : (term20 e d2 d1) = (term64 e d2 d1).
Proof. exact (MK_COMB (@lem1635098 e) (@lem1635096 d2 d1)). Qed.
Lemma lem1635100 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1635101 (d1 : real) (e : real) : (term65 e d1) = (term66 d1 e).
Proof. exact (MK_COMB (@lem1635100) (@lem1635008 d1 e)). Qed.
Lemma lem1635102 (e : real) (d2 : real) (d1 : real) : (term21 e d2 d1) = (term67 e d2 d1).
Proof. exact (MK_COMB (@lem1635101 d1 e) (@lem1635099 e d2 d1)). Qed.
Lemma lem1635103 (e : real) : (term68 e) = (term69 e).
Proof. exact (@lem1483531 term41 e). Qed.
Lemma lem1635109 (e : real) : (term70 e) = (term71 e).
Proof. exact (@lem1483519 term41 e). Qed.
Lemma lem1635114 (e : real) : (term71 e) = (term54 e).
Proof. exact (@lem1483448 (term54 e)). Qed.
Lemma lem1635116 (e : real) : (term70 e) = (term54 e).
Proof. exact (TRANS (@lem1635109 e) (@lem1635114 e)). Qed.
Lemma lem1635117 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1635118 (e : real) : (term72 e) = (term73 e).
Proof. exact (MK_COMB (@lem1635117) (@lem1635116 e)). Qed.
Lemma lem1635119 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635120 (e : real) : (term69 e) = (term74 e).
Proof. exact (MK_COMB (@lem1635118 e) (@lem1635119)). Qed.
Lemma lem1635121 (e : real) : (term68 e) = (term74 e).
Proof. exact (TRANS (@lem1635103 e) (@lem1635120 e)). Qed.
Lemma lem1635122 (e : real) (d1 : real) : (term75 e d1) = (term52 e d1).
Proof. exact (@lem1483531 e d1). Qed.
Lemma lem1635128 (e : real) (d1 : real) : (real_sub e d1) = (term38 e d1).
Proof. exact (@lem1483519 e d1). Qed.
Lemma lem1635133 (d1 : real) (e : real) : (term38 e d1) = (term53 d1 e).
Proof. exact (@lem1483488 (term54 d1) e). Qed.
Lemma lem1635135 (d1 : real) (e : real) : (real_sub e d1) = (term53 d1 e).
Proof. exact (TRANS (@lem1635128 e d1) (@lem1635133 d1 e)). Qed.
Lemma lem1635136 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1635137 (d1 : real) (e : real) : (term55 e d1) = (term56 d1 e).
Proof. exact (MK_COMB (@lem1635136) (@lem1635135 d1 e)). Qed.
Lemma lem1635138 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635139 (d1 : real) (e : real) : (term52 e d1) = (term57 d1 e).
Proof. exact (MK_COMB (@lem1635137 d1 e) (@lem1635138)). Qed.
Lemma lem1635140 (d1 : real) (e : real) : (term75 e d1) = (term57 d1 e).
Proof. exact (TRANS (@lem1635122 e d1) (@lem1635139 d1 e)). Qed.
Lemma lem1635141 (e : real) (d2 : real) : (term75 e d2) = (term52 e d2).
Proof. exact (@lem1483531 e d2). Qed.
Lemma lem1635147 (e : real) (d2 : real) : (real_sub e d2) = (term38 e d2).
Proof. exact (@lem1483519 e d2). Qed.
Lemma lem1635152 (d2 : real) (e : real) : (term38 e d2) = (term53 d2 e).
Proof. exact (@lem1483488 (term54 d2) e). Qed.
Lemma lem1635154 (d2 : real) (e : real) : (real_sub e d2) = (term53 d2 e).
Proof. exact (TRANS (@lem1635147 e d2) (@lem1635152 d2 e)). Qed.
Lemma lem1635155 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1635156 (d2 : real) (e : real) : (term55 e d2) = (term56 d2 e).
Proof. exact (MK_COMB (@lem1635155) (@lem1635154 d2 e)). Qed.
Lemma lem1635157 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635158 (d2 : real) (e : real) : (term52 e d2) = (term57 d2 e).
Proof. exact (MK_COMB (@lem1635156 d2 e) (@lem1635157)). Qed.
Lemma lem1635159 (d2 : real) (e : real) : (term75 e d2) = (term57 d2 e).
Proof. exact (TRANS (@lem1635141 e d2) (@lem1635158 d2 e)). Qed.
Lemma lem1635160 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1635161 (d1 : real) (e : real) : (term76 e d1) = (term77 d1 e).
Proof. exact (MK_COMB (@lem1635160) (@lem1635140 d1 e)). Qed.
Lemma lem1635162 (d1 : real) (d2 : real) (e : real) : (term26 d1 e d2) = (term78 d1 d2 e).
Proof. exact (MK_COMB (@lem1635161 d1 e) (@lem1635159 d2 e)). Qed.
Lemma lem1635163 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1635164 (e : real) : (term27 e) = (term79 e).
Proof. exact (MK_COMB (@lem1635163) (@lem1635121 e)). Qed.
Lemma lem1635165 (d1 : real) (d2 : real) (e : real) : (term29 d1 e d2) = (term80 d1 d2 e).
Proof. exact (MK_COMB (@lem1635164 e) (@lem1635162 d1 d2 e)). Qed.
Lemma lem1635166 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1635167 (e : real) (d2 : real) (d1 : real) : (term32 e d2 d1) = (term81 e d2 d1).
Proof. exact (MK_COMB (@lem1635166) (@lem1635102 e d2 d1)). Qed.
Lemma lem1635168 (d1 : real) (d2 : real) (e : real) : (term34 d1 e d2) = (term82 d1 d2 e).
Proof. exact (MK_COMB (@lem1635167 e d2 d1) (@lem1635165 d1 d2 e)). Qed.
Lemma lem1635175 (d1 : real) (d2 : real) (e : real) : (term35 d1 e d2) = (term82 d1 d2 e).
Proof. exact (TRANS (@lem1634989 d1 e d2) (@lem1635168 d1 d2 e)). Qed.
Lemma lem1635213 (d1 : real) (d2 : real) (e : real) : (term82 d1 d2 e) = (term83 d1 d2 e).
Proof. exact (@lem19158 (term74 e) (term67 e d2 d1) (term78 d1 d2 e)). Qed.
Lemma lem1635220 (d1 : real) (d2 : real) (e : real) : (term84 d1 d2 e) = (term85 d1 d2 e).
Proof. exact (@lem19158 (term57 d1 e) (term67 e d2 d1) (term57 d2 e)). Qed.
Lemma lem1635223 (d2 : real) (d1 : real) (e : real) : (term86 d2 d1 e) = (term86 d2 d1 e).
Proof. exact (eq_refl (term86 d2 d1 e)). Qed.
Lemma lem1635224 (d1 : real) (d2 : real) (e : real) : (term83 d1 d2 e) = (term87 d1 d2 e).
Proof. exact (MK_COMB (@lem1635223 d2 d1 e) (@lem1635220 d1 d2 e)). Qed.
Lemma lem1635226 (d1 : real) (d2 : real) (e : real) : (term82 d1 d2 e) = (term87 d1 d2 e).
Proof. exact (TRANS (@lem1635213 d1 d2 e) (@lem1635224 d1 d2 e)). Qed.
Lemma lem1635227 (d1 : real) (d2 : real) (e : real) : (term35 d1 e d2) = (term87 d1 d2 e).
Proof. exact (TRANS (@lem1635175 d1 d2 e) (@lem1635226 d1 d2 e)). Qed.
Lemma lem1635243 (d1 : real) (d2 : real) (e : real) (h1 : term87 d1 d2 e) : term87 d1 d2 e.
Proof. exact (h1). Qed.
Lemma lem1635244 (d2 : real) (d1 : real) (e : real) (h1 : term88 d2 d1 e) : term88 d2 d1 e.
Proof. exact (h1). Qed.
Lemma lem1635245 (d2 : real) (d1 : real) (e : real) (h1 : term88 d2 d1 e) : term74 e.
Proof. exact (proj2 (@lem1635244 d2 d1 e h1)). Qed.
Lemma lem1635246 (d2 : real) (d1 : real) (e : real) (h1 : term88 d2 d1 e) : term67 e d2 d1.
Proof. exact (proj1 (@lem1635244 d2 d1 e h1)). Qed.
Lemma lem1635247 (d2 : real) (d1 : real) (e : real) (h1 : term88 d2 d1 e) : term64 e d2 d1.
Proof. exact (proj2 (@lem1635246 d2 d1 e h1)). Qed.
Lemma lem1635250 (d2 : real) (d1 : real) (e : real) (h1 : term88 d2 d1 e) : term51 e.
Proof. exact (proj1 (@lem1635247 d2 d1 e h1)). Qed.
Lemma lem1635256 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1635257 : term90 = term91.
Proof. exact (@lem1635256 (NUMERAL 0) term48). Qed.
Lemma lem1635258 : term92 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1635259 (h1 : term92 = (BIT1 0)) : term91 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1635260 : (term92 = (BIT1 0)) = (term91 = True).
Proof. exact (prop_ext (fun h1 : term92 = (BIT1 0) => @lem1635259 h1) (fun h1 : term91 = True => @lem1635258)). Qed.
Lemma lem1635261 : term91 = True.
Proof. exact (EQ_MP (@lem1635260) (@lem1635258)). Qed.
Lemma lem1635262 : term90 = True.
Proof. exact (TRANS (@lem1635257) (@lem1635261)). Qed.
Lemma lem1635263 : True = term90.
Proof. exact (SYM (@lem1635262)). Qed.
Lemma lem1635264 : term90.
Proof. exact (EQ_MP (@lem1635263) (@lem0)). Qed.
Lemma lem1635265 (d2 : real) (d1 : real) (e : real) (h1 : term88 d2 d1 e) : term93 e.
Proof. exact (conj (@lem1635264) (@lem1635245 d2 d1 e h1)). Qed.
Lemma lem1635267 (x : real) (y : real) : term94 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1635268 (e : real) : term95 e.
Proof. exact (@lem1635267 term96 (term54 e)). Qed.
Lemma lem1635269 (d2 : real) (d1 : real) (e : real) (h1 : term88 d2 d1 e) : term97 e.
Proof. exact (@lem1635268 e (@lem1635265 d2 d1 e h1)). Qed.
Lemma lem1635270 (e : real) : (term98 e) = (term54 e).
Proof. exact (@lem1483460 (term54 e)). Qed.
Lemma lem1635271 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1635272 (e : real) : (term99 e) = (term73 e).
Proof. exact (MK_COMB (@lem1635271) (@lem1635270 e)). Qed.
Lemma lem1635273 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635274 (e : real) : (term97 e) = (term74 e).
Proof. exact (MK_COMB (@lem1635272 e) (@lem1635273)). Qed.
Lemma lem1635275 (d2 : real) (d1 : real) (e : real) (h1 : term88 d2 d1 e) : term74 e.
Proof. exact (EQ_MP (@lem1635274 e) (@lem1635269 d2 d1 e h1)). Qed.
Lemma lem1635277 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1635278 : term90 = term91.
Proof. exact (@lem1635277 (NUMERAL 0) term48). Qed.
Lemma lem1635279 : term92 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1635280 (h1 : term92 = (BIT1 0)) : term91 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1635281 : (term92 = (BIT1 0)) = (term91 = True).
Proof. exact (prop_ext (fun h1 : term92 = (BIT1 0) => @lem1635280 h1) (fun h1 : term91 = True => @lem1635279)). Qed.
Lemma lem1635282 : term91 = True.
Proof. exact (EQ_MP (@lem1635281) (@lem1635279)). Qed.
Lemma lem1635283 : term90 = True.
Proof. exact (TRANS (@lem1635278) (@lem1635282)). Qed.
Lemma lem1635284 : True = term90.
Proof. exact (SYM (@lem1635283)). Qed.
Lemma lem1635285 : term90.
Proof. exact (EQ_MP (@lem1635284) (@lem0)). Qed.
Lemma lem1635286 (d2 : real) (d1 : real) (e : real) (h1 : term88 d2 d1 e) : term100 e.
Proof. exact (conj (@lem1635285) (@lem1635250 d2 d1 e h1)). Qed.
Lemma lem1635288 (x : real) (y : real) : term101 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1635289 (e : real) : term102 e.
Proof. exact (@lem1635288 term96 e). Qed.
Lemma lem1635290 (d2 : real) (d1 : real) (e : real) (h1 : term88 d2 d1 e) : term103 e.
Proof. exact (@lem1635289 e (@lem1635286 d2 d1 e h1)). Qed.
Lemma lem1635291 (e : real) : (term104 e) = e.
Proof. exact (@lem1483460 e). Qed.
Lemma lem1635292 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1635293 (e : real) : (term105 e) = (real_gt e).
Proof. exact (MK_COMB (@lem1635292) (@lem1635291 e)). Qed.
Lemma lem1635294 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635295 (e : real) : (term103 e) = (term51 e).
Proof. exact (MK_COMB (@lem1635293 e) (@lem1635294)). Qed.
Lemma lem1635296 (d2 : real) (d1 : real) (e : real) (h1 : term88 d2 d1 e) : term51 e.
Proof. exact (EQ_MP (@lem1635295 e) (@lem1635290 d2 d1 e h1)). Qed.
Lemma lem1635297 (d2 : real) (d1 : real) (e : real) (h1 : term88 d2 d1 e) : term106 e.
Proof. exact (conj (@lem1635296 d2 d1 e h1) (@lem1635275 d2 d1 e h1)). Qed.
Lemma lem1635299 (x : real) (y : real) : term107 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1635300 (e : real) : term108 e.
Proof. exact (@lem1635299 e (term54 e)). Qed.
Lemma lem1635301 (d2 : real) (d1 : real) (e : real) (h1 : term88 d2 d1 e) : term109 e.
Proof. exact (@lem1635300 e (@lem1635297 d2 d1 e h1)). Qed.
Lemma lem1635302 (e : real) : (term110 e) = (term111 e).
Proof. exact (@lem1483442 term112 e). Qed.
Lemma lem1635304 (m : nat) : (term113 m) = term41.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1635305 : term114 = term41.
Proof. exact (@lem1635304 term48). Qed.
Lemma lem1635306 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1635307 : term115 = term116.
Proof. exact (MK_COMB (@lem1635306) (@lem1635305)). Qed.
Lemma lem1635308 (e : real) : e = e.
Proof. exact (eq_refl e). Qed.
Lemma lem1635309 (e : real) : (term111 e) = (term117 e).
Proof. exact (MK_COMB (@lem1635307) (@lem1635308 e)). Qed.
Lemma lem1635310 (e : real) : (term110 e) = (term117 e).
Proof. exact (TRANS (@lem1635302 e) (@lem1635309 e)). Qed.
Lemma lem1635311 (e : real) : (term117 e) = term41.
Proof. exact (@lem1483446 e). Qed.
Lemma lem1635312 (e : real) : (term110 e) = term41.
Proof. exact (TRANS (@lem1635310 e) (@lem1635311 e)). Qed.
Lemma lem1635313 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1635314 (e : real) : (term118 e) = term119.
Proof. exact (MK_COMB (@lem1635313) (@lem1635312 e)). Qed.
Lemma lem1635315 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635316 (e : real) : (term109 e) = term120.
Proof. exact (MK_COMB (@lem1635314 e) (@lem1635315)). Qed.
Lemma lem1635317 (d2 : real) (d1 : real) (e : real) (h1 : term88 d2 d1 e) : term120.
Proof. exact (EQ_MP (@lem1635316 e) (@lem1635301 d2 d1 e h1)). Qed.
Lemma lem1635319 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1635320 : term120 = term121.
Proof. exact (@lem1635319 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1635321 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1635322 : term120 = False.
Proof. exact (TRANS (@lem1635320) (@lem1635321)). Qed.
Lemma lem1635323 (d2 : real) (d1 : real) (e : real) (h1 : term88 d2 d1 e) : False.
Proof. exact (EQ_MP (@lem1635322) (@lem1635317 d2 d1 e h1)). Qed.
Lemma lem1635324 (d1 : real) (d2 : real) (e : real) (h1 : term85 d1 d2 e) : term85 d1 d2 e.
Proof. exact (h1). Qed.
Lemma lem1635325 (d2 : real) (d1 : real) (e : real) (h1 : term122 d2 d1 e) : term122 d2 d1 e.
Proof. exact (h1). Qed.
Lemma lem1635326 (d2 : real) (d1 : real) (e : real) (h1 : term122 d2 d1 e) : term57 d1 e.
Proof. exact (proj2 (@lem1635325 d2 d1 e h1)). Qed.
Lemma lem1635327 (d2 : real) (d1 : real) (e : real) (h1 : term122 d2 d1 e) : term67 e d2 d1.
Proof. exact (proj1 (@lem1635325 d2 d1 e h1)). Qed.
Lemma lem1635329 (d2 : real) (d1 : real) (e : real) (h1 : term122 d2 d1 e) : term42 d1 e.
Proof. exact (proj1 (@lem1635327 d2 d1 e h1)). Qed.
Lemma lem1635337 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1635338 : term90 = term91.
Proof. exact (@lem1635337 (NUMERAL 0) term48). Qed.
Lemma lem1635339 : term92 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1635340 (h1 : term92 = (BIT1 0)) : term91 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1635341 : (term92 = (BIT1 0)) = (term91 = True).
Proof. exact (prop_ext (fun h1 : term92 = (BIT1 0) => @lem1635340 h1) (fun h1 : term91 = True => @lem1635339)). Qed.
Lemma lem1635342 : term91 = True.
Proof. exact (EQ_MP (@lem1635341) (@lem1635339)). Qed.
Lemma lem1635343 : term90 = True.
Proof. exact (TRANS (@lem1635338) (@lem1635342)). Qed.
Lemma lem1635344 : True = term90.
Proof. exact (SYM (@lem1635343)). Qed.
Lemma lem1635345 : term90.
Proof. exact (EQ_MP (@lem1635344) (@lem0)). Qed.
Lemma lem1635346 (d2 : real) (d1 : real) (e : real) (h1 : term122 d2 d1 e) : term123 d1 e.
Proof. exact (conj (@lem1635345) (@lem1635326 d2 d1 e h1)). Qed.
Lemma lem1635348 (x : real) (y : real) : term94 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1635349 (d1 : real) (e : real) : term124 d1 e.
Proof. exact (@lem1635348 term96 (term53 d1 e)). Qed.
Lemma lem1635350 (d2 : real) (d1 : real) (e : real) (h1 : term122 d2 d1 e) : term125 d1 e.
Proof. exact (@lem1635349 d1 e (@lem1635346 d2 d1 e h1)). Qed.
Lemma lem1635351 (d1 : real) (e : real) : (term126 d1 e) = (term53 d1 e).
Proof. exact (@lem1483460 (term53 d1 e)). Qed.
Lemma lem1635352 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1635353 (d1 : real) (e : real) : (term127 d1 e) = (term56 d1 e).
Proof. exact (MK_COMB (@lem1635352) (@lem1635351 d1 e)). Qed.
Lemma lem1635354 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635355 (d1 : real) (e : real) : (term125 d1 e) = (term57 d1 e).
Proof. exact (MK_COMB (@lem1635353 d1 e) (@lem1635354)). Qed.
Lemma lem1635356 (d2 : real) (d1 : real) (e : real) (h1 : term122 d2 d1 e) : term57 d1 e.
Proof. exact (EQ_MP (@lem1635355 d1 e) (@lem1635350 d2 d1 e h1)). Qed.
Lemma lem1635358 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1635359 : term90 = term91.
Proof. exact (@lem1635358 (NUMERAL 0) term48). Qed.
Lemma lem1635360 : term92 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1635361 (h1 : term92 = (BIT1 0)) : term91 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1635362 : (term92 = (BIT1 0)) = (term91 = True).
Proof. exact (prop_ext (fun h1 : term92 = (BIT1 0) => @lem1635361 h1) (fun h1 : term91 = True => @lem1635360)). Qed.
Lemma lem1635363 : term91 = True.
Proof. exact (EQ_MP (@lem1635362) (@lem1635360)). Qed.
Lemma lem1635364 : term90 = True.
Proof. exact (TRANS (@lem1635359) (@lem1635363)). Qed.
Lemma lem1635365 : True = term90.
Proof. exact (SYM (@lem1635364)). Qed.
Lemma lem1635366 : term90.
Proof. exact (EQ_MP (@lem1635365) (@lem0)). Qed.
Lemma lem1635367 (d2 : real) (d1 : real) (e : real) (h1 : term122 d2 d1 e) : term128 d1 e.
Proof. exact (conj (@lem1635366) (@lem1635329 d2 d1 e h1)). Qed.
Lemma lem1635369 (x : real) (y : real) : term101 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1635370 (d1 : real) (e : real) : term129 d1 e.
Proof. exact (@lem1635369 term96 (term38 d1 e)). Qed.
Lemma lem1635371 (d2 : real) (d1 : real) (e : real) (h1 : term122 d2 d1 e) : term130 d1 e.
Proof. exact (@lem1635370 d1 e (@lem1635367 d2 d1 e h1)). Qed.
Lemma lem1635372 (d1 : real) (e : real) : (term131 d1 e) = (term38 d1 e).
Proof. exact (@lem1483460 (term38 d1 e)). Qed.
Lemma lem1635373 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1635374 (d1 : real) (e : real) : (term132 d1 e) = (term40 d1 e).
Proof. exact (MK_COMB (@lem1635373) (@lem1635372 d1 e)). Qed.
Lemma lem1635375 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635376 (d1 : real) (e : real) : (term130 d1 e) = (term42 d1 e).
Proof. exact (MK_COMB (@lem1635374 d1 e) (@lem1635375)). Qed.
Lemma lem1635377 (d2 : real) (d1 : real) (e : real) (h1 : term122 d2 d1 e) : term42 d1 e.
Proof. exact (EQ_MP (@lem1635376 d1 e) (@lem1635371 d2 d1 e h1)). Qed.
Lemma lem1635378 (d2 : real) (d1 : real) (e : real) (h1 : term122 d2 d1 e) : term133 d1 e.
Proof. exact (conj (@lem1635377 d2 d1 e h1) (@lem1635356 d2 d1 e h1)). Qed.
Lemma lem1635380 (x : real) (y : real) : term107 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1635381 (d1 : real) (e : real) : term134 d1 e.
Proof. exact (@lem1635380 (term38 d1 e) (term53 d1 e)). Qed.
Lemma lem1635382 (d2 : real) (d1 : real) (e : real) (h1 : term122 d2 d1 e) : term135 d1 e.
Proof. exact (@lem1635381 d1 e (@lem1635378 d2 d1 e h1)). Qed.
Lemma lem1635383 (d1 : real) (e : real) : (term136 d1 e) = (term137 d1 e).
Proof. exact (@lem1483480 d1 (term54 d1) (term54 e) e). Qed.
Lemma lem1635384 (d1 : real) : (term110 d1) = (term111 d1).
Proof. exact (@lem1483442 term112 d1). Qed.
Lemma lem1635386 (m : nat) : (term113 m) = term41.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1635387 : term114 = term41.
Proof. exact (@lem1635386 term48). Qed.
Lemma lem1635388 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1635389 : term115 = term116.
Proof. exact (MK_COMB (@lem1635388) (@lem1635387)). Qed.
Lemma lem1635390 (d1 : real) : d1 = d1.
Proof. exact (eq_refl d1). Qed.
Lemma lem1635391 (d1 : real) : (term111 d1) = (term117 d1).
Proof. exact (MK_COMB (@lem1635389) (@lem1635390 d1)). Qed.
Lemma lem1635392 (d1 : real) : (term110 d1) = (term117 d1).
Proof. exact (TRANS (@lem1635384 d1) (@lem1635391 d1)). Qed.
Lemma lem1635393 (d1 : real) : (term117 d1) = term41.
Proof. exact (@lem1483446 d1). Qed.
Lemma lem1635394 (d1 : real) : (term110 d1) = term41.
Proof. exact (TRANS (@lem1635392 d1) (@lem1635393 d1)). Qed.
Lemma lem1635395 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1635396 (d1 : real) : (term138 d1) = term139.
Proof. exact (MK_COMB (@lem1635395) (@lem1635394 d1)). Qed.
Lemma lem1635397 (e : real) : (term140 e) = (term111 e).
Proof. exact (@lem1483440 term112 e). Qed.
Lemma lem1635399 (m : nat) : (term113 m) = term41.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1635400 : term114 = term41.
Proof. exact (@lem1635399 term48). Qed.
Lemma lem1635401 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1635402 : term115 = term116.
Proof. exact (MK_COMB (@lem1635401) (@lem1635400)). Qed.
Lemma lem1635403 (e : real) : e = e.
Proof. exact (eq_refl e). Qed.
Lemma lem1635404 (e : real) : (term111 e) = (term117 e).
Proof. exact (MK_COMB (@lem1635402) (@lem1635403 e)). Qed.
Lemma lem1635405 (e : real) : (term140 e) = (term117 e).
Proof. exact (TRANS (@lem1635397 e) (@lem1635404 e)). Qed.
Lemma lem1635406 (e : real) : (term117 e) = term41.
Proof. exact (@lem1483446 e). Qed.
Lemma lem1635407 (e : real) : (term140 e) = term41.
Proof. exact (TRANS (@lem1635405 e) (@lem1635406 e)). Qed.
Lemma lem1635408 (d1 : real) (e : real) : (term137 d1 e) = term141.
Proof. exact (MK_COMB (@lem1635396 d1) (@lem1635407 e)). Qed.
Lemma lem1635409 (d1 : real) (e : real) : (term136 d1 e) = term141.
Proof. exact (TRANS (@lem1635383 d1 e) (@lem1635408 d1 e)). Qed.
Lemma lem1635410 : term141 = term41.
Proof. exact (@lem1483448 term41). Qed.
Lemma lem1635411 (d1 : real) (e : real) : (term136 d1 e) = term41.
Proof. exact (TRANS (@lem1635409 d1 e) (@lem1635410)). Qed.
Lemma lem1635412 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1635413 (d1 : real) (e : real) : (term142 d1 e) = term119.
Proof. exact (MK_COMB (@lem1635412) (@lem1635411 d1 e)). Qed.
Lemma lem1635414 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635415 (d1 : real) (e : real) : (term135 d1 e) = term120.
Proof. exact (MK_COMB (@lem1635413 d1 e) (@lem1635414)). Qed.
Lemma lem1635416 (d2 : real) (d1 : real) (e : real) (h1 : term122 d2 d1 e) : term120.
Proof. exact (EQ_MP (@lem1635415 d1 e) (@lem1635382 d2 d1 e h1)). Qed.
Lemma lem1635418 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1635419 : term120 = term121.
Proof. exact (@lem1635418 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1635420 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1635421 : term120 = False.
Proof. exact (TRANS (@lem1635419) (@lem1635420)). Qed.
Lemma lem1635422 (d2 : real) (d1 : real) (e : real) (h1 : term122 d2 d1 e) : False.
Proof. exact (EQ_MP (@lem1635421) (@lem1635416 d2 d1 e h1)). Qed.
Lemma lem1635423 (d1 : real) (d2 : real) (e : real) (h1 : term143 d1 d2 e) : term143 d1 d2 e.
Proof. exact (h1). Qed.
Lemma lem1635424 (d1 : real) (d2 : real) (e : real) (h1 : term143 d1 d2 e) : term57 d2 e.
Proof. exact (proj2 (@lem1635423 d1 d2 e h1)). Qed.
Lemma lem1635425 (d1 : real) (d2 : real) (e : real) (h1 : term143 d1 d2 e) : term67 e d2 d1.
Proof. exact (proj1 (@lem1635423 d1 d2 e h1)). Qed.
Lemma lem1635426 (d1 : real) (d2 : real) (e : real) (h1 : term143 d1 d2 e) : term64 e d2 d1.
Proof. exact (proj2 (@lem1635425 d1 d2 e h1)). Qed.
Lemma lem1635427 (d1 : real) (d2 : real) (e : real) (h1 : term143 d1 d2 e) : term42 d1 e.
Proof. exact (proj1 (@lem1635425 d1 d2 e h1)). Qed.
Lemma lem1635428 (d1 : real) (d2 : real) (e : real) (h1 : term143 d1 d2 e) : term63 d2 d1.
Proof. exact (proj2 (@lem1635426 d1 d2 e h1)). Qed.
Lemma lem1635431 (d1 : real) (d2 : real) (e : real) (h1 : term143 d1 d2 e) : term57 d1 d2.
Proof. exact (proj1 (@lem1635428 d1 d2 e h1)). Qed.
Lemma lem1635435 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1635436 : term90 = term91.
Proof. exact (@lem1635435 (NUMERAL 0) term48). Qed.
Lemma lem1635437 : term92 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1635438 (h1 : term92 = (BIT1 0)) : term91 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1635439 : (term92 = (BIT1 0)) = (term91 = True).
Proof. exact (prop_ext (fun h1 : term92 = (BIT1 0) => @lem1635438 h1) (fun h1 : term91 = True => @lem1635437)). Qed.
Lemma lem1635440 : term91 = True.
Proof. exact (EQ_MP (@lem1635439) (@lem1635437)). Qed.
Lemma lem1635441 : term90 = True.
Proof. exact (TRANS (@lem1635436) (@lem1635440)). Qed.
Lemma lem1635442 : True = term90.
Proof. exact (SYM (@lem1635441)). Qed.
Lemma lem1635443 : term90.
Proof. exact (EQ_MP (@lem1635442) (@lem0)). Qed.
Lemma lem1635444 (d1 : real) (d2 : real) (e : real) (h1 : term143 d1 d2 e) : term123 d1 d2.
Proof. exact (conj (@lem1635443) (@lem1635431 d1 d2 e h1)). Qed.
Lemma lem1635446 (x : real) (y : real) : term94 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1635447 (d1 : real) (d2 : real) : term124 d1 d2.
Proof. exact (@lem1635446 term96 (term53 d1 d2)). Qed.
Lemma lem1635448 (d1 : real) (d2 : real) (e : real) (h1 : term143 d1 d2 e) : term125 d1 d2.
Proof. exact (@lem1635447 d1 d2 (@lem1635444 d1 d2 e h1)). Qed.
Lemma lem1635449 (d1 : real) (d2 : real) : (term126 d1 d2) = (term53 d1 d2).
Proof. exact (@lem1483460 (term53 d1 d2)). Qed.
Lemma lem1635450 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1635451 (d1 : real) (d2 : real) : (term127 d1 d2) = (term56 d1 d2).
Proof. exact (MK_COMB (@lem1635450) (@lem1635449 d1 d2)). Qed.
Lemma lem1635452 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635453 (d1 : real) (d2 : real) : (term125 d1 d2) = (term57 d1 d2).
Proof. exact (MK_COMB (@lem1635451 d1 d2) (@lem1635452)). Qed.
Lemma lem1635454 (d1 : real) (d2 : real) (e : real) (h1 : term143 d1 d2 e) : term57 d1 d2.
Proof. exact (EQ_MP (@lem1635453 d1 d2) (@lem1635448 d1 d2 e h1)). Qed.
Lemma lem1635456 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1635457 : term90 = term91.
Proof. exact (@lem1635456 (NUMERAL 0) term48). Qed.
Lemma lem1635458 : term92 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1635459 (h1 : term92 = (BIT1 0)) : term91 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1635460 : (term92 = (BIT1 0)) = (term91 = True).
Proof. exact (prop_ext (fun h1 : term92 = (BIT1 0) => @lem1635459 h1) (fun h1 : term91 = True => @lem1635458)). Qed.
Lemma lem1635461 : term91 = True.
Proof. exact (EQ_MP (@lem1635460) (@lem1635458)). Qed.
Lemma lem1635462 : term90 = True.
Proof. exact (TRANS (@lem1635457) (@lem1635461)). Qed.
Lemma lem1635463 : True = term90.
Proof. exact (SYM (@lem1635462)). Qed.
Lemma lem1635464 : term90.
Proof. exact (EQ_MP (@lem1635463) (@lem0)). Qed.
Lemma lem1635465 (d1 : real) (d2 : real) (e : real) (h1 : term143 d1 d2 e) : term123 d2 e.
Proof. exact (conj (@lem1635464) (@lem1635424 d1 d2 e h1)). Qed.
Lemma lem1635467 (x : real) (y : real) : term94 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1635468 (d2 : real) (e : real) : term124 d2 e.
Proof. exact (@lem1635467 term96 (term53 d2 e)). Qed.
Lemma lem1635469 (d1 : real) (d2 : real) (e : real) (h1 : term143 d1 d2 e) : term125 d2 e.
Proof. exact (@lem1635468 d2 e (@lem1635465 d1 d2 e h1)). Qed.
Lemma lem1635470 (d2 : real) (e : real) : (term126 d2 e) = (term53 d2 e).
Proof. exact (@lem1483460 (term53 d2 e)). Qed.
Lemma lem1635471 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1635472 (d2 : real) (e : real) : (term127 d2 e) = (term56 d2 e).
Proof. exact (MK_COMB (@lem1635471) (@lem1635470 d2 e)). Qed.
Lemma lem1635473 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635474 (d2 : real) (e : real) : (term125 d2 e) = (term57 d2 e).
Proof. exact (MK_COMB (@lem1635472 d2 e) (@lem1635473)). Qed.
Lemma lem1635475 (d1 : real) (d2 : real) (e : real) (h1 : term143 d1 d2 e) : term57 d2 e.
Proof. exact (EQ_MP (@lem1635474 d2 e) (@lem1635469 d1 d2 e h1)). Qed.
Lemma lem1635477 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1635478 : term90 = term91.
Proof. exact (@lem1635477 (NUMERAL 0) term48). Qed.
Lemma lem1635479 : term92 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1635480 (h1 : term92 = (BIT1 0)) : term91 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1635481 : (term92 = (BIT1 0)) = (term91 = True).
Proof. exact (prop_ext (fun h1 : term92 = (BIT1 0) => @lem1635480 h1) (fun h1 : term91 = True => @lem1635479)). Qed.
Lemma lem1635482 : term91 = True.
Proof. exact (EQ_MP (@lem1635481) (@lem1635479)). Qed.
Lemma lem1635483 : term90 = True.
Proof. exact (TRANS (@lem1635478) (@lem1635482)). Qed.
Lemma lem1635484 : True = term90.
Proof. exact (SYM (@lem1635483)). Qed.
Lemma lem1635485 : term90.
Proof. exact (EQ_MP (@lem1635484) (@lem0)). Qed.
Lemma lem1635486 (d1 : real) (d2 : real) (e : real) (h1 : term143 d1 d2 e) : term128 d1 e.
Proof. exact (conj (@lem1635485) (@lem1635427 d1 d2 e h1)). Qed.
Lemma lem1635488 (x : real) (y : real) : term101 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1635489 (d1 : real) (e : real) : term129 d1 e.
Proof. exact (@lem1635488 term96 (term38 d1 e)). Qed.
Lemma lem1635490 (d1 : real) (d2 : real) (e : real) (h1 : term143 d1 d2 e) : term130 d1 e.
Proof. exact (@lem1635489 d1 e (@lem1635486 d1 d2 e h1)). Qed.
Lemma lem1635491 (d1 : real) (e : real) : (term131 d1 e) = (term38 d1 e).
Proof. exact (@lem1483460 (term38 d1 e)). Qed.
Lemma lem1635492 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1635493 (d1 : real) (e : real) : (term132 d1 e) = (term40 d1 e).
Proof. exact (MK_COMB (@lem1635492) (@lem1635491 d1 e)). Qed.
Lemma lem1635494 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635495 (d1 : real) (e : real) : (term130 d1 e) = (term42 d1 e).
Proof. exact (MK_COMB (@lem1635493 d1 e) (@lem1635494)). Qed.
Lemma lem1635496 (d1 : real) (d2 : real) (e : real) (h1 : term143 d1 d2 e) : term42 d1 e.
Proof. exact (EQ_MP (@lem1635495 d1 e) (@lem1635490 d1 d2 e h1)). Qed.
Lemma lem1635497 (d1 : real) (d2 : real) (e : real) (h1 : term143 d1 d2 e) : term144 d1 d2 e.
Proof. exact (conj (@lem1635496 d1 d2 e h1) (@lem1635475 d1 d2 e h1)). Qed.
Lemma lem1635499 (x : real) (y : real) : term107 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1635500 (d1 : real) (d2 : real) (e : real) : term145 d1 d2 e.
Proof. exact (@lem1635499 (term38 d1 e) (term53 d2 e)). Qed.
Lemma lem1635501 (d1 : real) (d2 : real) (e : real) (h1 : term143 d1 d2 e) : term146 d1 d2 e.
Proof. exact (@lem1635500 d1 d2 e (@lem1635497 d1 d2 e h1)). Qed.
Lemma lem1635502 (d1 : real) (d2 : real) (e : real) : (term147 d1 d2 e) = (term148 d1 d2 e).
Proof. exact (@lem1483482 d1 (term54 e) (term53 d2 e)). Qed.
Lemma lem1635503 (d2 : real) (e : real) : (term149 d2 e) = (term150 d2 e).
Proof. exact (@lem1483484 (term54 d2) (term54 e) e). Qed.
Lemma lem1635504 (e : real) : (term140 e) = (term111 e).
Proof. exact (@lem1483440 term112 e). Qed.
Lemma lem1635506 (m : nat) : (term113 m) = term41.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1635507 : term114 = term41.
Proof. exact (@lem1635506 term48). Qed.
Lemma lem1635508 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1635509 : term115 = term116.
Proof. exact (MK_COMB (@lem1635508) (@lem1635507)). Qed.
Lemma lem1635510 (e : real) : e = e.
Proof. exact (eq_refl e). Qed.
Lemma lem1635511 (e : real) : (term111 e) = (term117 e).
Proof. exact (MK_COMB (@lem1635509) (@lem1635510 e)). Qed.
Lemma lem1635512 (e : real) : (term140 e) = (term117 e).
Proof. exact (TRANS (@lem1635504 e) (@lem1635511 e)). Qed.
Lemma lem1635513 (e : real) : (term117 e) = term41.
Proof. exact (@lem1483446 e). Qed.
Lemma lem1635514 (e : real) : (term140 e) = term41.
Proof. exact (TRANS (@lem1635512 e) (@lem1635513 e)). Qed.
Lemma lem1635515 (d2 : real) : (term151 d2) = (term151 d2).
Proof. exact (eq_refl (term151 d2)). Qed.
Lemma lem1635516 (e : real) (d2 : real) : (term150 d2 e) = (term152 d2).
Proof. exact (MK_COMB (@lem1635515 d2) (@lem1635514 e)). Qed.
Lemma lem1635517 (e : real) (d2 : real) : (term149 d2 e) = (term152 d2).
Proof. exact (TRANS (@lem1635503 d2 e) (@lem1635516 e d2)). Qed.
Lemma lem1635518 (d2 : real) : (term152 d2) = (term54 d2).
Proof. exact (@lem1483450 (term54 d2)). Qed.
Lemma lem1635519 (e : real) (d2 : real) : (term149 d2 e) = (term54 d2).
Proof. exact (TRANS (@lem1635517 e d2) (@lem1635518 d2)). Qed.
Lemma lem1635520 (d1 : real) : (real_add d1) = (real_add d1).
Proof. exact (eq_refl (real_add d1)). Qed.
Lemma lem1635521 (e : real) (d1 : real) (d2 : real) : (term148 d1 d2 e) = (term38 d1 d2).
Proof. exact (MK_COMB (@lem1635520 d1) (@lem1635519 e d2)). Qed.
Lemma lem1635522 (e : real) (d1 : real) (d2 : real) : (term147 d1 d2 e) = (term38 d1 d2).
Proof. exact (TRANS (@lem1635502 d1 d2 e) (@lem1635521 e d1 d2)). Qed.
Lemma lem1635523 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1635524 (e : real) (d1 : real) (d2 : real) : (term153 d1 d2 e) = (term40 d1 d2).
Proof. exact (MK_COMB (@lem1635523) (@lem1635522 e d1 d2)). Qed.
Lemma lem1635525 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635526 (e : real) (d1 : real) (d2 : real) : (term146 d1 d2 e) = (term42 d1 d2).
Proof. exact (MK_COMB (@lem1635524 e d1 d2) (@lem1635525)). Qed.
Lemma lem1635527 (d1 : real) (d2 : real) (e : real) (h1 : term143 d1 d2 e) : term42 d1 d2.
Proof. exact (EQ_MP (@lem1635526 e d1 d2) (@lem1635501 d1 d2 e h1)). Qed.
Lemma lem1635529 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1635530 : term90 = term91.
Proof. exact (@lem1635529 (NUMERAL 0) term48). Qed.
Lemma lem1635531 : term92 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1635532 (h1 : term92 = (BIT1 0)) : term91 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1635533 : (term92 = (BIT1 0)) = (term91 = True).
Proof. exact (prop_ext (fun h1 : term92 = (BIT1 0) => @lem1635532 h1) (fun h1 : term91 = True => @lem1635531)). Qed.
Lemma lem1635534 : term91 = True.
Proof. exact (EQ_MP (@lem1635533) (@lem1635531)). Qed.
Lemma lem1635535 : term90 = True.
Proof. exact (TRANS (@lem1635530) (@lem1635534)). Qed.
Lemma lem1635536 : True = term90.
Proof. exact (SYM (@lem1635535)). Qed.
Lemma lem1635537 : term90.
Proof. exact (EQ_MP (@lem1635536) (@lem0)). Qed.
Lemma lem1635538 (d1 : real) (d2 : real) (e : real) (h1 : term143 d1 d2 e) : term128 d1 d2.
Proof. exact (conj (@lem1635537) (@lem1635527 d1 d2 e h1)). Qed.
Lemma lem1635540 (x : real) (y : real) : term101 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1635541 (d1 : real) (d2 : real) : term129 d1 d2.
Proof. exact (@lem1635540 term96 (term38 d1 d2)). Qed.
Lemma lem1635542 (d1 : real) (d2 : real) (e : real) (h1 : term143 d1 d2 e) : term130 d1 d2.
Proof. exact (@lem1635541 d1 d2 (@lem1635538 d1 d2 e h1)). Qed.
Lemma lem1635543 (d1 : real) (d2 : real) : (term131 d1 d2) = (term38 d1 d2).
Proof. exact (@lem1483460 (term38 d1 d2)). Qed.
Lemma lem1635544 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1635545 (d1 : real) (d2 : real) : (term132 d1 d2) = (term40 d1 d2).
Proof. exact (MK_COMB (@lem1635544) (@lem1635543 d1 d2)). Qed.
Lemma lem1635546 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635547 (d1 : real) (d2 : real) : (term130 d1 d2) = (term42 d1 d2).
Proof. exact (MK_COMB (@lem1635545 d1 d2) (@lem1635546)). Qed.
Lemma lem1635548 (d1 : real) (d2 : real) (e : real) (h1 : term143 d1 d2 e) : term42 d1 d2.
Proof. exact (EQ_MP (@lem1635547 d1 d2) (@lem1635542 d1 d2 e h1)). Qed.
Lemma lem1635549 (d1 : real) (d2 : real) (e : real) (h1 : term143 d1 d2 e) : term133 d1 d2.
Proof. exact (conj (@lem1635548 d1 d2 e h1) (@lem1635454 d1 d2 e h1)). Qed.
Lemma lem1635551 (x : real) (y : real) : term107 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1635552 (d1 : real) (d2 : real) : term134 d1 d2.
Proof. exact (@lem1635551 (term38 d1 d2) (term53 d1 d2)). Qed.
Lemma lem1635553 (d1 : real) (d2 : real) (e : real) (h1 : term143 d1 d2 e) : term135 d1 d2.
Proof. exact (@lem1635552 d1 d2 (@lem1635549 d1 d2 e h1)). Qed.
Lemma lem1635554 (d1 : real) (d2 : real) : (term136 d1 d2) = (term137 d1 d2).
Proof. exact (@lem1483480 d1 (term54 d1) (term54 d2) d2). Qed.
Lemma lem1635555 (d1 : real) : (term110 d1) = (term111 d1).
Proof. exact (@lem1483442 term112 d1). Qed.
Lemma lem1635557 (m : nat) : (term113 m) = term41.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1635558 : term114 = term41.
Proof. exact (@lem1635557 term48). Qed.
Lemma lem1635559 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1635560 : term115 = term116.
Proof. exact (MK_COMB (@lem1635559) (@lem1635558)). Qed.
Lemma lem1635561 (d1 : real) : d1 = d1.
Proof. exact (eq_refl d1). Qed.
Lemma lem1635562 (d1 : real) : (term111 d1) = (term117 d1).
Proof. exact (MK_COMB (@lem1635560) (@lem1635561 d1)). Qed.
Lemma lem1635563 (d1 : real) : (term110 d1) = (term117 d1).
Proof. exact (TRANS (@lem1635555 d1) (@lem1635562 d1)). Qed.
Lemma lem1635564 (d1 : real) : (term117 d1) = term41.
Proof. exact (@lem1483446 d1). Qed.
Lemma lem1635565 (d1 : real) : (term110 d1) = term41.
Proof. exact (TRANS (@lem1635563 d1) (@lem1635564 d1)). Qed.
Lemma lem1635566 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1635567 (d1 : real) : (term138 d1) = term139.
Proof. exact (MK_COMB (@lem1635566) (@lem1635565 d1)). Qed.
Lemma lem1635568 (d2 : real) : (term140 d2) = (term111 d2).
Proof. exact (@lem1483440 term112 d2). Qed.
Lemma lem1635570 (m : nat) : (term113 m) = term41.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1635571 : term114 = term41.
Proof. exact (@lem1635570 term48). Qed.
Lemma lem1635572 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1635573 : term115 = term116.
Proof. exact (MK_COMB (@lem1635572) (@lem1635571)). Qed.
Lemma lem1635574 (d2 : real) : d2 = d2.
Proof. exact (eq_refl d2). Qed.
Lemma lem1635575 (d2 : real) : (term111 d2) = (term117 d2).
Proof. exact (MK_COMB (@lem1635573) (@lem1635574 d2)). Qed.
Lemma lem1635576 (d2 : real) : (term140 d2) = (term117 d2).
Proof. exact (TRANS (@lem1635568 d2) (@lem1635575 d2)). Qed.
Lemma lem1635577 (d2 : real) : (term117 d2) = term41.
Proof. exact (@lem1483446 d2). Qed.
Lemma lem1635578 (d2 : real) : (term140 d2) = term41.
Proof. exact (TRANS (@lem1635576 d2) (@lem1635577 d2)). Qed.
Lemma lem1635579 (d1 : real) (d2 : real) : (term137 d1 d2) = term141.
Proof. exact (MK_COMB (@lem1635567 d1) (@lem1635578 d2)). Qed.
Lemma lem1635580 (d1 : real) (d2 : real) : (term136 d1 d2) = term141.
Proof. exact (TRANS (@lem1635554 d1 d2) (@lem1635579 d1 d2)). Qed.
Lemma lem1635581 : term141 = term41.
Proof. exact (@lem1483448 term41). Qed.
Lemma lem1635582 (d1 : real) (d2 : real) : (term136 d1 d2) = term41.
Proof. exact (TRANS (@lem1635580 d1 d2) (@lem1635581)). Qed.
Lemma lem1635583 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1635584 (d1 : real) (d2 : real) : (term142 d1 d2) = term119.
Proof. exact (MK_COMB (@lem1635583) (@lem1635582 d1 d2)). Qed.
Lemma lem1635585 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635586 (d1 : real) (d2 : real) : (term135 d1 d2) = term120.
Proof. exact (MK_COMB (@lem1635584 d1 d2) (@lem1635585)). Qed.
Lemma lem1635587 (d1 : real) (d2 : real) (e : real) (h1 : term143 d1 d2 e) : term120.
Proof. exact (EQ_MP (@lem1635586 d1 d2) (@lem1635553 d1 d2 e h1)). Qed.
Lemma lem1635589 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1635590 : term120 = term121.
Proof. exact (@lem1635589 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1635591 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1635592 : term120 = False.
Proof. exact (TRANS (@lem1635590) (@lem1635591)). Qed.
Lemma lem1635593 (d1 : real) (d2 : real) (e : real) (h1 : term143 d1 d2 e) : False.
Proof. exact (EQ_MP (@lem1635592) (@lem1635587 d1 d2 e h1)). Qed.
Lemma lem1635594 (d1 : real) (d2 : real) (e : real) (h1 : term85 d1 d2 e) : False.
Proof. exact (or_elim (@lem1635324 d1 d2 e h1) (fun h0 : term122 d2 d1 e => @lem1635422 d2 d1 e h0) (fun h0 : term143 d1 d2 e => @lem1635593 d1 d2 e h0)). Qed.
Lemma lem1635595 (d1 : real) (d2 : real) (e : real) (h1 : term87 d1 d2 e) : False.
Proof. exact (or_elim (@lem1635243 d1 d2 e h1) (fun h0 : term88 d2 d1 e => @lem1635323 d2 d1 e h0) (fun h0 : term85 d1 d2 e => @lem1635594 d1 d2 e h0)). Qed.
Lemma lem1635597 (d1 : real) (d2 : real) (e : real) (h1 : term87 d1 d2 e) : term87 d1 d2 e.
Proof. exact (h1). Qed.
Lemma lem1635598 (d1 : real) (d2 : real) (e : real) (h1 : term87 d1 d2 e) : (term87 d1 d2 e) = False.
Proof. exact (prop_ext (fun h2 : term87 d1 d2 e => @lem1635595 d1 d2 e h1) (fun h2 : False => @lem1635597 d1 d2 e h1)). Qed.
Lemma lem1635599 (d1 : real) (d2 : real) (e : real) (h1 : term87 d1 d2 e) : False.
Proof. exact (EQ_MP (@lem1635598 d1 d2 e h1) (@lem1635597 d1 d2 e h1)). Qed.
Lemma lem1635600 (d1 : real) (e : real) (d2 : real) (h1 : term35 d1 e d2) : term35 d1 e d2.
Proof. exact (h1). Qed.
Lemma lem1635601 (d1 : real) (e : real) (d2 : real) (h1 : term35 d1 e d2) : term87 d1 d2 e.
Proof. exact (EQ_MP (@lem1635227 d1 d2 e) (@lem1635600 d1 e d2 h1)). Qed.
Lemma lem1635602 (d1 : real) (e : real) (d2 : real) (h1 : term35 d1 e d2) : (term87 d1 d2 e) = False.
Proof. exact (prop_ext (fun h2 : term87 d1 d2 e => @lem1635599 d1 d2 e h2) (fun h2 : False => @lem1635601 d1 e d2 h1)). Qed.
Lemma lem1635603 (d1 : real) (e : real) (d2 : real) (h1 : term35 d1 e d2) : False.
Proof. exact (EQ_MP (@lem1635602 d1 e d2 h1) (@lem1635601 d1 e d2 h1)). Qed.
Lemma lem1635604 (d1 : real) (e : real) (d2 : real) : term154 d1 e d2.
Proof. exact (fun h0 : term35 d1 e d2 => @lem1635603 d1 e d2 h0). Qed.
Lemma lem1635605 (d1 : real) (e : real) (d2 : real) : term155 d1 e d2.
Proof. exact (@lem1386578 (term156 d1 e d2)). Qed.
Lemma lem1635606 (d1 : real) (e : real) (d2 : real) : term156 d1 e d2.
Proof. exact (@lem1635605 d1 e d2 (@lem1635604 d1 e d2)). Qed.
Lemma lem1635648 (d1 : real) (e : real) (d2 : real) : (term25 d1 e d2) = (term26 d1 e d2).
Proof. exact (@lem17045 (real_lt e d1) (real_lt e d2)). Qed.
Lemma lem1635650 (e : real) : (term27 e) = (term27 e).
Proof. exact (eq_refl (term27 e)). Qed.
Lemma lem1635651 (d1 : real) (e : real) (d2 : real) : (term28 d1 e d2) = (term29 d1 e d2).
Proof. exact (MK_COMB (@lem1635650 e) (@lem1635648 d1 e d2)). Qed.
Lemma lem1635652 (d1 : real) (e : real) (d2 : real) : (term30 d1 e d2) = (term28 d1 e d2).
Proof. exact (@lem17045 (term7 e) (term31 d1 e d2)). Qed.
Lemma lem1635653 (d1 : real) (e : real) (d2 : real) : (term30 d1 e d2) = (term29 d1 e d2).
Proof. exact (TRANS (@lem1635652 d1 e d2) (@lem1635651 d1 e d2)). Qed.
Lemma lem1635655 (e : real) (d2 : real) (d1 : real) : (term157 e d2 d1) = (term157 e d2 d1).
Proof. exact (eq_refl (term157 e d2 d1)). Qed.
Lemma lem1635656 (d1 : real) (e : real) (d2 : real) : (term158 d1 e d2) = (term159 d1 e d2).
Proof. exact (MK_COMB (@lem1635655 e d2 d1) (@lem1635653 d1 e d2)). Qed.
Lemma lem1635657 (d1 : real) (e : real) (d2 : real) : (term160 d1 e d2) = (term158 d1 e d2).
Proof. exact (@lem17362 (term24 e d2 d1) (term36 d1 e d2)). Qed.
Lemma lem1635695 (d1 : real) (e : real) (d2 : real) : (term160 d1 e d2) = (term159 d1 e d2).
Proof. exact (TRANS (@lem1635657 d1 e d2) (@lem1635656 d1 e d2)). Qed.
Lemma lem1635696 (d2 : real) (e : real) : (real_lt e d2) = (term37 d2 e).
Proof. exact (@lem1483521 d2 e). Qed.
Lemma lem1635709 (d2 : real) (e : real) : (real_sub d2 e) = (term38 d2 e).
Proof. exact (@lem1483519 d2 e). Qed.
Lemma lem1635710 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1635711 (d2 : real) (e : real) : (term39 d2 e) = (term40 d2 e).
Proof. exact (MK_COMB (@lem1635710) (@lem1635709 d2 e)). Qed.
Lemma lem1635712 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635713 (d2 : real) (e : real) : (term37 d2 e) = (term42 d2 e).
Proof. exact (MK_COMB (@lem1635711 d2 e) (@lem1635712)). Qed.
Lemma lem1635714 (d2 : real) (e : real) : (real_lt e d2) = (term42 d2 e).
Proof. exact (TRANS (@lem1635696 d2 e) (@lem1635713 d2 e)). Qed.
Lemma lem1635715 (e : real) : (term7 e) = (term43 e).
Proof. exact (@lem1483521 e term41). Qed.
Lemma lem1635721 (e : real) : (term44 e) = (term45 e).
Proof. exact (@lem1483519 e term41). Qed.
Lemma lem1635723 (x : nat) : (term46 x) = term41.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1635724 : term47 = term41.
Proof. exact (@lem1635723 term48). Qed.
Lemma lem1635725 (e : real) : (real_add e) = (real_add e).
Proof. exact (eq_refl (real_add e)). Qed.
Lemma lem1635726 (e : real) : (term45 e) = (term49 e).
Proof. exact (MK_COMB (@lem1635725 e) (@lem1635724)). Qed.
Lemma lem1635727 (e : real) : (term49 e) = e.
Proof. exact (@lem1483450 e). Qed.
Lemma lem1635728 (e : real) : (term45 e) = e.
Proof. exact (TRANS (@lem1635726 e) (@lem1635727 e)). Qed.
Lemma lem1635730 (e : real) : (term44 e) = e.
Proof. exact (TRANS (@lem1635721 e) (@lem1635728 e)). Qed.
Lemma lem1635731 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1635732 (e : real) : (term50 e) = (real_gt e).
Proof. exact (MK_COMB (@lem1635731) (@lem1635730 e)). Qed.
Lemma lem1635733 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635734 (e : real) : (term43 e) = (term51 e).
Proof. exact (MK_COMB (@lem1635732 e) (@lem1635733)). Qed.
Lemma lem1635735 (e : real) : (term7 e) = (term51 e).
Proof. exact (TRANS (@lem1635715 e) (@lem1635734 e)). Qed.
Lemma lem1635736 (d1 : real) (d2 : real) : (real_le d2 d1) = (term52 d1 d2).
Proof. exact (@lem1483523 d1 d2). Qed.
Lemma lem1635749 (d1 : real) (d2 : real) : (real_sub d1 d2) = (term38 d1 d2).
Proof. exact (@lem1483519 d1 d2). Qed.
Lemma lem1635750 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1635751 (d1 : real) (d2 : real) : (term55 d1 d2) = (term161 d1 d2).
Proof. exact (MK_COMB (@lem1635750) (@lem1635749 d1 d2)). Qed.
Lemma lem1635752 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635753 (d1 : real) (d2 : real) : (term52 d1 d2) = (term162 d1 d2).
Proof. exact (MK_COMB (@lem1635751 d1 d2) (@lem1635752)). Qed.
Lemma lem1635754 (d1 : real) (d2 : real) : (real_le d2 d1) = (term162 d1 d2).
Proof. exact (TRANS (@lem1635736 d1 d2) (@lem1635753 d1 d2)). Qed.
Lemma lem1635755 (d2 : real) : (term7 d2) = (term43 d2).
Proof. exact (@lem1483521 d2 term41). Qed.
Lemma lem1635761 (d2 : real) : (term44 d2) = (term45 d2).
Proof. exact (@lem1483519 d2 term41). Qed.
Lemma lem1635763 (x : nat) : (term46 x) = term41.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1635764 : term47 = term41.
Proof. exact (@lem1635763 term48). Qed.
Lemma lem1635765 (d2 : real) : (real_add d2) = (real_add d2).
Proof. exact (eq_refl (real_add d2)). Qed.
Lemma lem1635766 (d2 : real) : (term45 d2) = (term49 d2).
Proof. exact (MK_COMB (@lem1635765 d2) (@lem1635764)). Qed.
Lemma lem1635767 (d2 : real) : (term49 d2) = d2.
Proof. exact (@lem1483450 d2). Qed.
Lemma lem1635768 (d2 : real) : (term45 d2) = d2.
Proof. exact (TRANS (@lem1635766 d2) (@lem1635767 d2)). Qed.
Lemma lem1635770 (d2 : real) : (term44 d2) = d2.
Proof. exact (TRANS (@lem1635761 d2) (@lem1635768 d2)). Qed.
Lemma lem1635771 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1635772 (d2 : real) : (term50 d2) = (real_gt d2).
Proof. exact (MK_COMB (@lem1635771) (@lem1635770 d2)). Qed.
Lemma lem1635773 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635774 (d2 : real) : (term43 d2) = (term51 d2).
Proof. exact (MK_COMB (@lem1635772 d2) (@lem1635773)). Qed.
Lemma lem1635775 (d2 : real) : (term7 d2) = (term51 d2).
Proof. exact (TRANS (@lem1635755 d2) (@lem1635774 d2)). Qed.
Lemma lem1635776 (d1 : real) : (term7 d1) = (term43 d1).
Proof. exact (@lem1483521 d1 term41). Qed.
Lemma lem1635782 (d1 : real) : (term44 d1) = (term45 d1).
Proof. exact (@lem1483519 d1 term41). Qed.
Lemma lem1635784 (x : nat) : (term46 x) = term41.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1635785 : term47 = term41.
Proof. exact (@lem1635784 term48). Qed.
Lemma lem1635786 (d1 : real) : (real_add d1) = (real_add d1).
Proof. exact (eq_refl (real_add d1)). Qed.
Lemma lem1635787 (d1 : real) : (term45 d1) = (term49 d1).
Proof. exact (MK_COMB (@lem1635786 d1) (@lem1635785)). Qed.
Lemma lem1635788 (d1 : real) : (term49 d1) = d1.
Proof. exact (@lem1483450 d1). Qed.
Lemma lem1635789 (d1 : real) : (term45 d1) = d1.
Proof. exact (TRANS (@lem1635787 d1) (@lem1635788 d1)). Qed.
Lemma lem1635791 (d1 : real) : (term44 d1) = d1.
Proof. exact (TRANS (@lem1635782 d1) (@lem1635789 d1)). Qed.
Lemma lem1635792 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1635793 (d1 : real) : (term50 d1) = (real_gt d1).
Proof. exact (MK_COMB (@lem1635792) (@lem1635791 d1)). Qed.
Lemma lem1635794 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635795 (d1 : real) : (term43 d1) = (term51 d1).
Proof. exact (MK_COMB (@lem1635793 d1) (@lem1635794)). Qed.
Lemma lem1635796 (d1 : real) : (term7 d1) = (term51 d1).
Proof. exact (TRANS (@lem1635776 d1) (@lem1635795 d1)). Qed.
Lemma lem1635797 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1635798 (d2 : real) : (term58 d2) = (term59 d2).
Proof. exact (MK_COMB (@lem1635797) (@lem1635775 d2)). Qed.
Lemma lem1635799 (d2 : real) (d1 : real) : (term6 d2 d1) = (term60 d2 d1).
Proof. exact (MK_COMB (@lem1635798 d2) (@lem1635796 d1)). Qed.
Lemma lem1635800 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1635801 (d1 : real) (d2 : real) : (term61 d2 d1) = (term163 d1 d2).
Proof. exact (MK_COMB (@lem1635800) (@lem1635754 d1 d2)). Qed.
Lemma lem1635802 (d2 : real) (d1 : real) : (term22 d2 d1) = (term164 d2 d1).
Proof. exact (MK_COMB (@lem1635801 d1 d2) (@lem1635799 d2 d1)). Qed.
Lemma lem1635803 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1635804 (e : real) : (term58 e) = (term59 e).
Proof. exact (MK_COMB (@lem1635803) (@lem1635735 e)). Qed.
Lemma lem1635805 (e : real) (d2 : real) (d1 : real) : (term23 e d2 d1) = (term165 e d2 d1).
Proof. exact (MK_COMB (@lem1635804 e) (@lem1635802 d2 d1)). Qed.
Lemma lem1635806 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1635807 (d2 : real) (e : real) : (term65 e d2) = (term66 d2 e).
Proof. exact (MK_COMB (@lem1635806) (@lem1635714 d2 e)). Qed.
Lemma lem1635808 (e : real) (d2 : real) (d1 : real) : (term24 e d2 d1) = (term166 e d2 d1).
Proof. exact (MK_COMB (@lem1635807 d2 e) (@lem1635805 e d2 d1)). Qed.
Lemma lem1635809 (e : real) : (term68 e) = (term69 e).
Proof. exact (@lem1483531 term41 e). Qed.
Lemma lem1635815 (e : real) : (term70 e) = (term71 e).
Proof. exact (@lem1483519 term41 e). Qed.
Lemma lem1635820 (e : real) : (term71 e) = (term54 e).
Proof. exact (@lem1483448 (term54 e)). Qed.
Lemma lem1635822 (e : real) : (term70 e) = (term54 e).
Proof. exact (TRANS (@lem1635815 e) (@lem1635820 e)). Qed.
Lemma lem1635823 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1635824 (e : real) : (term72 e) = (term73 e).
Proof. exact (MK_COMB (@lem1635823) (@lem1635822 e)). Qed.
Lemma lem1635825 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635826 (e : real) : (term69 e) = (term74 e).
Proof. exact (MK_COMB (@lem1635824 e) (@lem1635825)). Qed.
Lemma lem1635827 (e : real) : (term68 e) = (term74 e).
Proof. exact (TRANS (@lem1635809 e) (@lem1635826 e)). Qed.
Lemma lem1635828 (e : real) (d1 : real) : (term75 e d1) = (term52 e d1).
Proof. exact (@lem1483531 e d1). Qed.
Lemma lem1635834 (e : real) (d1 : real) : (real_sub e d1) = (term38 e d1).
Proof. exact (@lem1483519 e d1). Qed.
Lemma lem1635839 (d1 : real) (e : real) : (term38 e d1) = (term53 d1 e).
Proof. exact (@lem1483488 (term54 d1) e). Qed.
Lemma lem1635841 (d1 : real) (e : real) : (real_sub e d1) = (term53 d1 e).
Proof. exact (TRANS (@lem1635834 e d1) (@lem1635839 d1 e)). Qed.
Lemma lem1635842 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1635843 (d1 : real) (e : real) : (term55 e d1) = (term56 d1 e).
Proof. exact (MK_COMB (@lem1635842) (@lem1635841 d1 e)). Qed.
Lemma lem1635844 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635845 (d1 : real) (e : real) : (term52 e d1) = (term57 d1 e).
Proof. exact (MK_COMB (@lem1635843 d1 e) (@lem1635844)). Qed.
Lemma lem1635846 (d1 : real) (e : real) : (term75 e d1) = (term57 d1 e).
Proof. exact (TRANS (@lem1635828 e d1) (@lem1635845 d1 e)). Qed.
Lemma lem1635847 (e : real) (d2 : real) : (term75 e d2) = (term52 e d2).
Proof. exact (@lem1483531 e d2). Qed.
Lemma lem1635853 (e : real) (d2 : real) : (real_sub e d2) = (term38 e d2).
Proof. exact (@lem1483519 e d2). Qed.
Lemma lem1635858 (d2 : real) (e : real) : (term38 e d2) = (term53 d2 e).
Proof. exact (@lem1483488 (term54 d2) e). Qed.
Lemma lem1635860 (d2 : real) (e : real) : (real_sub e d2) = (term53 d2 e).
Proof. exact (TRANS (@lem1635853 e d2) (@lem1635858 d2 e)). Qed.
Lemma lem1635861 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1635862 (d2 : real) (e : real) : (term55 e d2) = (term56 d2 e).
Proof. exact (MK_COMB (@lem1635861) (@lem1635860 d2 e)). Qed.
Lemma lem1635863 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635864 (d2 : real) (e : real) : (term52 e d2) = (term57 d2 e).
Proof. exact (MK_COMB (@lem1635862 d2 e) (@lem1635863)). Qed.
Lemma lem1635865 (d2 : real) (e : real) : (term75 e d2) = (term57 d2 e).
Proof. exact (TRANS (@lem1635847 e d2) (@lem1635864 d2 e)). Qed.
Lemma lem1635866 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1635867 (d1 : real) (e : real) : (term76 e d1) = (term77 d1 e).
Proof. exact (MK_COMB (@lem1635866) (@lem1635846 d1 e)). Qed.
Lemma lem1635868 (d1 : real) (d2 : real) (e : real) : (term26 d1 e d2) = (term78 d1 d2 e).
Proof. exact (MK_COMB (@lem1635867 d1 e) (@lem1635865 d2 e)). Qed.
Lemma lem1635869 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1635870 (e : real) : (term27 e) = (term79 e).
Proof. exact (MK_COMB (@lem1635869) (@lem1635827 e)). Qed.
Lemma lem1635871 (d1 : real) (d2 : real) (e : real) : (term29 d1 e d2) = (term80 d1 d2 e).
Proof. exact (MK_COMB (@lem1635870 e) (@lem1635868 d1 d2 e)). Qed.
Lemma lem1635872 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1635873 (e : real) (d2 : real) (d1 : real) : (term157 e d2 d1) = (term167 e d2 d1).
Proof. exact (MK_COMB (@lem1635872) (@lem1635808 e d2 d1)). Qed.
Lemma lem1635874 (d1 : real) (d2 : real) (e : real) : (term159 d1 e d2) = (term168 d1 d2 e).
Proof. exact (MK_COMB (@lem1635873 e d2 d1) (@lem1635871 d1 d2 e)). Qed.
Lemma lem1635881 (d1 : real) (d2 : real) (e : real) : (term160 d1 e d2) = (term168 d1 d2 e).
Proof. exact (TRANS (@lem1635695 d1 e d2) (@lem1635874 d1 d2 e)). Qed.
Lemma lem1635919 (d1 : real) (d2 : real) (e : real) : (term168 d1 d2 e) = (term169 d1 d2 e).
Proof. exact (@lem19158 (term74 e) (term166 e d2 d1) (term78 d1 d2 e)). Qed.
Lemma lem1635926 (d1 : real) (d2 : real) (e : real) : (term170 d1 d2 e) = (term171 d1 d2 e).
Proof. exact (@lem19158 (term57 d1 e) (term166 e d2 d1) (term57 d2 e)). Qed.
Lemma lem1635929 (d2 : real) (d1 : real) (e : real) : (term172 d2 d1 e) = (term172 d2 d1 e).
Proof. exact (eq_refl (term172 d2 d1 e)). Qed.
Lemma lem1635930 (d1 : real) (d2 : real) (e : real) : (term169 d1 d2 e) = (term173 d1 d2 e).
Proof. exact (MK_COMB (@lem1635929 d2 d1 e) (@lem1635926 d1 d2 e)). Qed.
Lemma lem1635932 (d1 : real) (d2 : real) (e : real) : (term168 d1 d2 e) = (term173 d1 d2 e).
Proof. exact (TRANS (@lem1635919 d1 d2 e) (@lem1635930 d1 d2 e)). Qed.
Lemma lem1635933 (d1 : real) (d2 : real) (e : real) : (term160 d1 e d2) = (term173 d1 d2 e).
Proof. exact (TRANS (@lem1635881 d1 d2 e) (@lem1635932 d1 d2 e)). Qed.
Lemma lem1635949 (d1 : real) (d2 : real) (e : real) (h1 : term173 d1 d2 e) : term173 d1 d2 e.
Proof. exact (h1). Qed.
Lemma lem1635950 (d2 : real) (d1 : real) (e : real) (h1 : term174 d2 d1 e) : term174 d2 d1 e.
Proof. exact (h1). Qed.
Lemma lem1635951 (d2 : real) (d1 : real) (e : real) (h1 : term174 d2 d1 e) : term74 e.
Proof. exact (proj2 (@lem1635950 d2 d1 e h1)). Qed.
Lemma lem1635952 (d2 : real) (d1 : real) (e : real) (h1 : term174 d2 d1 e) : term166 e d2 d1.
Proof. exact (proj1 (@lem1635950 d2 d1 e h1)). Qed.
Lemma lem1635953 (d2 : real) (d1 : real) (e : real) (h1 : term174 d2 d1 e) : term165 e d2 d1.
Proof. exact (proj2 (@lem1635952 d2 d1 e h1)). Qed.
Lemma lem1635956 (d2 : real) (d1 : real) (e : real) (h1 : term174 d2 d1 e) : term51 e.
Proof. exact (proj1 (@lem1635953 d2 d1 e h1)). Qed.
Lemma lem1635962 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1635963 : term90 = term91.
Proof. exact (@lem1635962 (NUMERAL 0) term48). Qed.
Lemma lem1635964 : term92 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1635965 (h1 : term92 = (BIT1 0)) : term91 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1635966 : (term92 = (BIT1 0)) = (term91 = True).
Proof. exact (prop_ext (fun h1 : term92 = (BIT1 0) => @lem1635965 h1) (fun h1 : term91 = True => @lem1635964)). Qed.
Lemma lem1635967 : term91 = True.
Proof. exact (EQ_MP (@lem1635966) (@lem1635964)). Qed.
Lemma lem1635968 : term90 = True.
Proof. exact (TRANS (@lem1635963) (@lem1635967)). Qed.
Lemma lem1635969 : True = term90.
Proof. exact (SYM (@lem1635968)). Qed.
Lemma lem1635970 : term90.
Proof. exact (EQ_MP (@lem1635969) (@lem0)). Qed.
Lemma lem1635971 (d2 : real) (d1 : real) (e : real) (h1 : term174 d2 d1 e) : term93 e.
Proof. exact (conj (@lem1635970) (@lem1635951 d2 d1 e h1)). Qed.
Lemma lem1635973 (x : real) (y : real) : term94 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1635974 (e : real) : term95 e.
Proof. exact (@lem1635973 term96 (term54 e)). Qed.
Lemma lem1635975 (d2 : real) (d1 : real) (e : real) (h1 : term174 d2 d1 e) : term97 e.
Proof. exact (@lem1635974 e (@lem1635971 d2 d1 e h1)). Qed.
Lemma lem1635976 (e : real) : (term98 e) = (term54 e).
Proof. exact (@lem1483460 (term54 e)). Qed.
Lemma lem1635977 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1635978 (e : real) : (term99 e) = (term73 e).
Proof. exact (MK_COMB (@lem1635977) (@lem1635976 e)). Qed.
Lemma lem1635979 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1635980 (e : real) : (term97 e) = (term74 e).
Proof. exact (MK_COMB (@lem1635978 e) (@lem1635979)). Qed.
Lemma lem1635981 (d2 : real) (d1 : real) (e : real) (h1 : term174 d2 d1 e) : term74 e.
Proof. exact (EQ_MP (@lem1635980 e) (@lem1635975 d2 d1 e h1)). Qed.
Lemma lem1635983 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1635984 : term90 = term91.
Proof. exact (@lem1635983 (NUMERAL 0) term48). Qed.
Lemma lem1635985 : term92 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1635986 (h1 : term92 = (BIT1 0)) : term91 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1635987 : (term92 = (BIT1 0)) = (term91 = True).
Proof. exact (prop_ext (fun h1 : term92 = (BIT1 0) => @lem1635986 h1) (fun h1 : term91 = True => @lem1635985)). Qed.
Lemma lem1635988 : term91 = True.
Proof. exact (EQ_MP (@lem1635987) (@lem1635985)). Qed.
Lemma lem1635989 : term90 = True.
Proof. exact (TRANS (@lem1635984) (@lem1635988)). Qed.
Lemma lem1635990 : True = term90.
Proof. exact (SYM (@lem1635989)). Qed.
Lemma lem1635991 : term90.
Proof. exact (EQ_MP (@lem1635990) (@lem0)). Qed.
Lemma lem1635992 (d2 : real) (d1 : real) (e : real) (h1 : term174 d2 d1 e) : term100 e.
Proof. exact (conj (@lem1635991) (@lem1635956 d2 d1 e h1)). Qed.
Lemma lem1635994 (x : real) (y : real) : term101 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1635995 (e : real) : term102 e.
Proof. exact (@lem1635994 term96 e). Qed.
Lemma lem1635996 (d2 : real) (d1 : real) (e : real) (h1 : term174 d2 d1 e) : term103 e.
Proof. exact (@lem1635995 e (@lem1635992 d2 d1 e h1)). Qed.
Lemma lem1635997 (e : real) : (term104 e) = e.
Proof. exact (@lem1483460 e). Qed.
Lemma lem1635998 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1635999 (e : real) : (term105 e) = (real_gt e).
Proof. exact (MK_COMB (@lem1635998) (@lem1635997 e)). Qed.
Lemma lem1636000 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1636001 (e : real) : (term103 e) = (term51 e).
Proof. exact (MK_COMB (@lem1635999 e) (@lem1636000)). Qed.
Lemma lem1636002 (d2 : real) (d1 : real) (e : real) (h1 : term174 d2 d1 e) : term51 e.
Proof. exact (EQ_MP (@lem1636001 e) (@lem1635996 d2 d1 e h1)). Qed.
Lemma lem1636003 (d2 : real) (d1 : real) (e : real) (h1 : term174 d2 d1 e) : term106 e.
Proof. exact (conj (@lem1636002 d2 d1 e h1) (@lem1635981 d2 d1 e h1)). Qed.
Lemma lem1636005 (x : real) (y : real) : term107 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1636006 (e : real) : term108 e.
Proof. exact (@lem1636005 e (term54 e)). Qed.
Lemma lem1636007 (d2 : real) (d1 : real) (e : real) (h1 : term174 d2 d1 e) : term109 e.
Proof. exact (@lem1636006 e (@lem1636003 d2 d1 e h1)). Qed.
Lemma lem1636008 (e : real) : (term110 e) = (term111 e).
Proof. exact (@lem1483442 term112 e). Qed.
Lemma lem1636010 (m : nat) : (term113 m) = term41.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1636011 : term114 = term41.
Proof. exact (@lem1636010 term48). Qed.
Lemma lem1636012 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1636013 : term115 = term116.
Proof. exact (MK_COMB (@lem1636012) (@lem1636011)). Qed.
Lemma lem1636014 (e : real) : e = e.
Proof. exact (eq_refl e). Qed.
Lemma lem1636015 (e : real) : (term111 e) = (term117 e).
Proof. exact (MK_COMB (@lem1636013) (@lem1636014 e)). Qed.
Lemma lem1636016 (e : real) : (term110 e) = (term117 e).
Proof. exact (TRANS (@lem1636008 e) (@lem1636015 e)). Qed.
Lemma lem1636017 (e : real) : (term117 e) = term41.
Proof. exact (@lem1483446 e). Qed.
Lemma lem1636018 (e : real) : (term110 e) = term41.
Proof. exact (TRANS (@lem1636016 e) (@lem1636017 e)). Qed.
Lemma lem1636019 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1636020 (e : real) : (term118 e) = term119.
Proof. exact (MK_COMB (@lem1636019) (@lem1636018 e)). Qed.
Lemma lem1636021 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1636022 (e : real) : (term109 e) = term120.
Proof. exact (MK_COMB (@lem1636020 e) (@lem1636021)). Qed.
Lemma lem1636023 (d2 : real) (d1 : real) (e : real) (h1 : term174 d2 d1 e) : term120.
Proof. exact (EQ_MP (@lem1636022 e) (@lem1636007 d2 d1 e h1)). Qed.
Lemma lem1636025 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1636026 : term120 = term121.
Proof. exact (@lem1636025 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1636027 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1636028 : term120 = False.
Proof. exact (TRANS (@lem1636026) (@lem1636027)). Qed.
Lemma lem1636029 (d2 : real) (d1 : real) (e : real) (h1 : term174 d2 d1 e) : False.
Proof. exact (EQ_MP (@lem1636028) (@lem1636023 d2 d1 e h1)). Qed.
Lemma lem1636030 (d1 : real) (d2 : real) (e : real) (h1 : term171 d1 d2 e) : term171 d1 d2 e.
Proof. exact (h1). Qed.
Lemma lem1636031 (d2 : real) (d1 : real) (e : real) (h1 : term175 d2 d1 e) : term175 d2 d1 e.
Proof. exact (h1). Qed.
Lemma lem1636032 (d2 : real) (d1 : real) (e : real) (h1 : term175 d2 d1 e) : term57 d1 e.
Proof. exact (proj2 (@lem1636031 d2 d1 e h1)). Qed.
Lemma lem1636033 (d2 : real) (d1 : real) (e : real) (h1 : term175 d2 d1 e) : term166 e d2 d1.
Proof. exact (proj1 (@lem1636031 d2 d1 e h1)). Qed.
Lemma lem1636034 (d2 : real) (d1 : real) (e : real) (h1 : term175 d2 d1 e) : term165 e d2 d1.
Proof. exact (proj2 (@lem1636033 d2 d1 e h1)). Qed.
Lemma lem1636035 (d2 : real) (d1 : real) (e : real) (h1 : term175 d2 d1 e) : term42 d2 e.
Proof. exact (proj1 (@lem1636033 d2 d1 e h1)). Qed.
Lemma lem1636036 (d2 : real) (d1 : real) (e : real) (h1 : term175 d2 d1 e) : term164 d2 d1.
Proof. exact (proj2 (@lem1636034 d2 d1 e h1)). Qed.
Lemma lem1636039 (d2 : real) (d1 : real) (e : real) (h1 : term175 d2 d1 e) : term162 d1 d2.
Proof. exact (proj1 (@lem1636036 d2 d1 e h1)). Qed.
Lemma lem1636043 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1636044 : term90 = term91.
Proof. exact (@lem1636043 (NUMERAL 0) term48). Qed.
Lemma lem1636045 : term92 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1636046 (h1 : term92 = (BIT1 0)) : term91 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1636047 : (term92 = (BIT1 0)) = (term91 = True).
Proof. exact (prop_ext (fun h1 : term92 = (BIT1 0) => @lem1636046 h1) (fun h1 : term91 = True => @lem1636045)). Qed.
Lemma lem1636048 : term91 = True.
Proof. exact (EQ_MP (@lem1636047) (@lem1636045)). Qed.
Lemma lem1636049 : term90 = True.
Proof. exact (TRANS (@lem1636044) (@lem1636048)). Qed.
Lemma lem1636050 : True = term90.
Proof. exact (SYM (@lem1636049)). Qed.
Lemma lem1636051 : term90.
Proof. exact (EQ_MP (@lem1636050) (@lem0)). Qed.
Lemma lem1636052 (d2 : real) (d1 : real) (e : real) (h1 : term175 d2 d1 e) : term176 d1 d2.
Proof. exact (conj (@lem1636051) (@lem1636039 d2 d1 e h1)). Qed.
Lemma lem1636054 (x : real) (y : real) : term94 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1636055 (d1 : real) (d2 : real) : term177 d1 d2.
Proof. exact (@lem1636054 term96 (term38 d1 d2)). Qed.
Lemma lem1636056 (d2 : real) (d1 : real) (e : real) (h1 : term175 d2 d1 e) : term178 d1 d2.
Proof. exact (@lem1636055 d1 d2 (@lem1636052 d2 d1 e h1)). Qed.
Lemma lem1636057 (d1 : real) (d2 : real) : (term131 d1 d2) = (term38 d1 d2).
Proof. exact (@lem1483460 (term38 d1 d2)). Qed.
Lemma lem1636058 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1636059 (d1 : real) (d2 : real) : (term179 d1 d2) = (term161 d1 d2).
Proof. exact (MK_COMB (@lem1636058) (@lem1636057 d1 d2)). Qed.
Lemma lem1636060 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1636061 (d1 : real) (d2 : real) : (term178 d1 d2) = (term162 d1 d2).
Proof. exact (MK_COMB (@lem1636059 d1 d2) (@lem1636060)). Qed.
Lemma lem1636062 (d2 : real) (d1 : real) (e : real) (h1 : term175 d2 d1 e) : term162 d1 d2.
Proof. exact (EQ_MP (@lem1636061 d1 d2) (@lem1636056 d2 d1 e h1)). Qed.
Lemma lem1636064 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1636065 : term90 = term91.
Proof. exact (@lem1636064 (NUMERAL 0) term48). Qed.
Lemma lem1636066 : term92 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1636067 (h1 : term92 = (BIT1 0)) : term91 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1636068 : (term92 = (BIT1 0)) = (term91 = True).
Proof. exact (prop_ext (fun h1 : term92 = (BIT1 0) => @lem1636067 h1) (fun h1 : term91 = True => @lem1636066)). Qed.
Lemma lem1636069 : term91 = True.
Proof. exact (EQ_MP (@lem1636068) (@lem1636066)). Qed.
Lemma lem1636070 : term90 = True.
Proof. exact (TRANS (@lem1636065) (@lem1636069)). Qed.
Lemma lem1636071 : True = term90.
Proof. exact (SYM (@lem1636070)). Qed.
Lemma lem1636072 : term90.
Proof. exact (EQ_MP (@lem1636071) (@lem0)). Qed.
Lemma lem1636073 (d2 : real) (d1 : real) (e : real) (h1 : term175 d2 d1 e) : term123 d1 e.
Proof. exact (conj (@lem1636072) (@lem1636032 d2 d1 e h1)). Qed.
Lemma lem1636075 (x : real) (y : real) : term94 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1636076 (d1 : real) (e : real) : term124 d1 e.
Proof. exact (@lem1636075 term96 (term53 d1 e)). Qed.
Lemma lem1636077 (d2 : real) (d1 : real) (e : real) (h1 : term175 d2 d1 e) : term125 d1 e.
Proof. exact (@lem1636076 d1 e (@lem1636073 d2 d1 e h1)). Qed.
Lemma lem1636078 (d1 : real) (e : real) : (term126 d1 e) = (term53 d1 e).
Proof. exact (@lem1483460 (term53 d1 e)). Qed.
Lemma lem1636079 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1636080 (d1 : real) (e : real) : (term127 d1 e) = (term56 d1 e).
Proof. exact (MK_COMB (@lem1636079) (@lem1636078 d1 e)). Qed.
Lemma lem1636081 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1636082 (d1 : real) (e : real) : (term125 d1 e) = (term57 d1 e).
Proof. exact (MK_COMB (@lem1636080 d1 e) (@lem1636081)). Qed.
Lemma lem1636083 (d2 : real) (d1 : real) (e : real) (h1 : term175 d2 d1 e) : term57 d1 e.
Proof. exact (EQ_MP (@lem1636082 d1 e) (@lem1636077 d2 d1 e h1)). Qed.
Lemma lem1636085 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1636086 : term90 = term91.
Proof. exact (@lem1636085 (NUMERAL 0) term48). Qed.
Lemma lem1636087 : term92 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1636088 (h1 : term92 = (BIT1 0)) : term91 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1636089 : (term92 = (BIT1 0)) = (term91 = True).
Proof. exact (prop_ext (fun h1 : term92 = (BIT1 0) => @lem1636088 h1) (fun h1 : term91 = True => @lem1636087)). Qed.
Lemma lem1636090 : term91 = True.
Proof. exact (EQ_MP (@lem1636089) (@lem1636087)). Qed.
Lemma lem1636091 : term90 = True.
Proof. exact (TRANS (@lem1636086) (@lem1636090)). Qed.
Lemma lem1636092 : True = term90.
Proof. exact (SYM (@lem1636091)). Qed.
Lemma lem1636093 : term90.
Proof. exact (EQ_MP (@lem1636092) (@lem0)). Qed.
Lemma lem1636094 (d2 : real) (d1 : real) (e : real) (h1 : term175 d2 d1 e) : term128 d2 e.
Proof. exact (conj (@lem1636093) (@lem1636035 d2 d1 e h1)). Qed.
Lemma lem1636096 (x : real) (y : real) : term101 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1636097 (d2 : real) (e : real) : term129 d2 e.
Proof. exact (@lem1636096 term96 (term38 d2 e)). Qed.
Lemma lem1636098 (d2 : real) (d1 : real) (e : real) (h1 : term175 d2 d1 e) : term130 d2 e.
Proof. exact (@lem1636097 d2 e (@lem1636094 d2 d1 e h1)). Qed.
Lemma lem1636099 (d2 : real) (e : real) : (term131 d2 e) = (term38 d2 e).
Proof. exact (@lem1483460 (term38 d2 e)). Qed.
Lemma lem1636100 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1636101 (d2 : real) (e : real) : (term132 d2 e) = (term40 d2 e).
Proof. exact (MK_COMB (@lem1636100) (@lem1636099 d2 e)). Qed.
Lemma lem1636102 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1636103 (d2 : real) (e : real) : (term130 d2 e) = (term42 d2 e).
Proof. exact (MK_COMB (@lem1636101 d2 e) (@lem1636102)). Qed.
Lemma lem1636104 (d2 : real) (d1 : real) (e : real) (h1 : term175 d2 d1 e) : term42 d2 e.
Proof. exact (EQ_MP (@lem1636103 d2 e) (@lem1636098 d2 d1 e h1)). Qed.
Lemma lem1636105 (d2 : real) (d1 : real) (e : real) (h1 : term175 d2 d1 e) : term144 d2 d1 e.
Proof. exact (conj (@lem1636104 d2 d1 e h1) (@lem1636083 d2 d1 e h1)). Qed.
Lemma lem1636107 (x : real) (y : real) : term107 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1636108 (d2 : real) (d1 : real) (e : real) : term145 d2 d1 e.
Proof. exact (@lem1636107 (term38 d2 e) (term53 d1 e)). Qed.
Lemma lem1636109 (d2 : real) (d1 : real) (e : real) (h1 : term175 d2 d1 e) : term146 d2 d1 e.
Proof. exact (@lem1636108 d2 d1 e (@lem1636105 d2 d1 e h1)). Qed.
Lemma lem1636110 (d1 : real) (d2 : real) (e : real) : (term147 d2 d1 e) = (term180 d1 d2 e).
Proof. exact (@lem1483484 (term54 d1) (term38 d2 e) e). Qed.
Lemma lem1636111 (d2 : real) (e : real) : (term181 d2 e) = (term182 d2 e).
Proof. exact (@lem1483482 d2 (term54 e) e). Qed.
Lemma lem1636112 (e : real) : (term140 e) = (term111 e).
Proof. exact (@lem1483440 term112 e). Qed.
Lemma lem1636114 (m : nat) : (term113 m) = term41.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1636115 : term114 = term41.
Proof. exact (@lem1636114 term48). Qed.
Lemma lem1636116 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1636117 : term115 = term116.
Proof. exact (MK_COMB (@lem1636116) (@lem1636115)). Qed.
Lemma lem1636118 (e : real) : e = e.
Proof. exact (eq_refl e). Qed.
Lemma lem1636119 (e : real) : (term111 e) = (term117 e).
Proof. exact (MK_COMB (@lem1636117) (@lem1636118 e)). Qed.
Lemma lem1636120 (e : real) : (term140 e) = (term117 e).
Proof. exact (TRANS (@lem1636112 e) (@lem1636119 e)). Qed.
Lemma lem1636121 (e : real) : (term117 e) = term41.
Proof. exact (@lem1483446 e). Qed.
Lemma lem1636122 (e : real) : (term140 e) = term41.
Proof. exact (TRANS (@lem1636120 e) (@lem1636121 e)). Qed.
Lemma lem1636123 (d2 : real) : (real_add d2) = (real_add d2).
Proof. exact (eq_refl (real_add d2)). Qed.
Lemma lem1636124 (e : real) (d2 : real) : (term182 d2 e) = (term49 d2).
Proof. exact (MK_COMB (@lem1636123 d2) (@lem1636122 e)). Qed.
Lemma lem1636125 (e : real) (d2 : real) : (term181 d2 e) = (term49 d2).
Proof. exact (TRANS (@lem1636111 d2 e) (@lem1636124 e d2)). Qed.
Lemma lem1636126 (d2 : real) : (term49 d2) = d2.
Proof. exact (@lem1483450 d2). Qed.
Lemma lem1636127 (e : real) (d2 : real) : (term181 d2 e) = d2.
Proof. exact (TRANS (@lem1636125 e d2) (@lem1636126 d2)). Qed.
Lemma lem1636128 (d1 : real) : (term151 d1) = (term151 d1).
Proof. exact (eq_refl (term151 d1)). Qed.
Lemma lem1636129 (e : real) (d1 : real) (d2 : real) : (term180 d1 d2 e) = (term53 d1 d2).
Proof. exact (MK_COMB (@lem1636128 d1) (@lem1636127 e d2)). Qed.
Lemma lem1636130 (e : real) (d1 : real) (d2 : real) : (term147 d2 d1 e) = (term53 d1 d2).
Proof. exact (TRANS (@lem1636110 d1 d2 e) (@lem1636129 e d1 d2)). Qed.
Lemma lem1636131 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1636132 (e : real) (d1 : real) (d2 : real) : (term153 d2 d1 e) = (term183 d1 d2).
Proof. exact (MK_COMB (@lem1636131) (@lem1636130 e d1 d2)). Qed.
Lemma lem1636133 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1636134 (e : real) (d1 : real) (d2 : real) : (term146 d2 d1 e) = (term184 d1 d2).
Proof. exact (MK_COMB (@lem1636132 e d1 d2) (@lem1636133)). Qed.
Lemma lem1636135 (d2 : real) (d1 : real) (e : real) (h1 : term175 d2 d1 e) : term184 d1 d2.
Proof. exact (EQ_MP (@lem1636134 e d1 d2) (@lem1636109 d2 d1 e h1)). Qed.
Lemma lem1636137 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1636138 : term90 = term91.
Proof. exact (@lem1636137 (NUMERAL 0) term48). Qed.
Lemma lem1636139 : term92 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1636140 (h1 : term92 = (BIT1 0)) : term91 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1636141 : (term92 = (BIT1 0)) = (term91 = True).
Proof. exact (prop_ext (fun h1 : term92 = (BIT1 0) => @lem1636140 h1) (fun h1 : term91 = True => @lem1636139)). Qed.
Lemma lem1636142 : term91 = True.
Proof. exact (EQ_MP (@lem1636141) (@lem1636139)). Qed.
Lemma lem1636143 : term90 = True.
Proof. exact (TRANS (@lem1636138) (@lem1636142)). Qed.
Lemma lem1636144 : True = term90.
Proof. exact (SYM (@lem1636143)). Qed.
Lemma lem1636145 : term90.
Proof. exact (EQ_MP (@lem1636144) (@lem0)). Qed.
Lemma lem1636146 (d2 : real) (d1 : real) (e : real) (h1 : term175 d2 d1 e) : term185 d1 d2.
Proof. exact (conj (@lem1636145) (@lem1636135 d2 d1 e h1)). Qed.
Lemma lem1636148 (x : real) (y : real) : term101 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1636149 (d1 : real) (d2 : real) : term186 d1 d2.
Proof. exact (@lem1636148 term96 (term53 d1 d2)). Qed.
Lemma lem1636150 (d2 : real) (d1 : real) (e : real) (h1 : term175 d2 d1 e) : term187 d1 d2.
Proof. exact (@lem1636149 d1 d2 (@lem1636146 d2 d1 e h1)). Qed.
Lemma lem1636151 (d1 : real) (d2 : real) : (term126 d1 d2) = (term53 d1 d2).
Proof. exact (@lem1483460 (term53 d1 d2)). Qed.
Lemma lem1636152 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1636153 (d1 : real) (d2 : real) : (term188 d1 d2) = (term183 d1 d2).
Proof. exact (MK_COMB (@lem1636152) (@lem1636151 d1 d2)). Qed.
Lemma lem1636154 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1636155 (d1 : real) (d2 : real) : (term187 d1 d2) = (term184 d1 d2).
Proof. exact (MK_COMB (@lem1636153 d1 d2) (@lem1636154)). Qed.
Lemma lem1636156 (d2 : real) (d1 : real) (e : real) (h1 : term175 d2 d1 e) : term184 d1 d2.
Proof. exact (EQ_MP (@lem1636155 d1 d2) (@lem1636150 d2 d1 e h1)). Qed.
Lemma lem1636157 (d2 : real) (d1 : real) (e : real) (h1 : term175 d2 d1 e) : term189 d1 d2.
Proof. exact (conj (@lem1636156 d2 d1 e h1) (@lem1636062 d2 d1 e h1)). Qed.
Lemma lem1636159 (x : real) (y : real) : term107 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1636160 (d1 : real) (d2 : real) : term190 d1 d2.
Proof. exact (@lem1636159 (term53 d1 d2) (term38 d1 d2)). Qed.
Lemma lem1636161 (d2 : real) (d1 : real) (e : real) (h1 : term175 d2 d1 e) : term191 d1 d2.
Proof. exact (@lem1636160 d1 d2 (@lem1636157 d2 d1 e h1)). Qed.
Lemma lem1636162 (d1 : real) (d2 : real) : (term192 d1 d2) = (term193 d1 d2).
Proof. exact (@lem1483480 (term54 d1) d1 d2 (term54 d2)). Qed.
Lemma lem1636163 (d1 : real) : (term140 d1) = (term111 d1).
Proof. exact (@lem1483440 term112 d1). Qed.
Lemma lem1636165 (m : nat) : (term113 m) = term41.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1636166 : term114 = term41.
Proof. exact (@lem1636165 term48). Qed.
Lemma lem1636167 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1636168 : term115 = term116.
Proof. exact (MK_COMB (@lem1636167) (@lem1636166)). Qed.
Lemma lem1636169 (d1 : real) : d1 = d1.
Proof. exact (eq_refl d1). Qed.
Lemma lem1636170 (d1 : real) : (term111 d1) = (term117 d1).
Proof. exact (MK_COMB (@lem1636168) (@lem1636169 d1)). Qed.
Lemma lem1636171 (d1 : real) : (term140 d1) = (term117 d1).
Proof. exact (TRANS (@lem1636163 d1) (@lem1636170 d1)). Qed.
Lemma lem1636172 (d1 : real) : (term117 d1) = term41.
Proof. exact (@lem1483446 d1). Qed.
Lemma lem1636173 (d1 : real) : (term140 d1) = term41.
Proof. exact (TRANS (@lem1636171 d1) (@lem1636172 d1)). Qed.
Lemma lem1636174 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1636175 (d1 : real) : (term194 d1) = term139.
Proof. exact (MK_COMB (@lem1636174) (@lem1636173 d1)). Qed.
Lemma lem1636176 (d2 : real) : (term110 d2) = (term111 d2).
Proof. exact (@lem1483442 term112 d2). Qed.
Lemma lem1636178 (m : nat) : (term113 m) = term41.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1636179 : term114 = term41.
Proof. exact (@lem1636178 term48). Qed.
Lemma lem1636180 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1636181 : term115 = term116.
Proof. exact (MK_COMB (@lem1636180) (@lem1636179)). Qed.
Lemma lem1636182 (d2 : real) : d2 = d2.
Proof. exact (eq_refl d2). Qed.
Lemma lem1636183 (d2 : real) : (term111 d2) = (term117 d2).
Proof. exact (MK_COMB (@lem1636181) (@lem1636182 d2)). Qed.
Lemma lem1636184 (d2 : real) : (term110 d2) = (term117 d2).
Proof. exact (TRANS (@lem1636176 d2) (@lem1636183 d2)). Qed.
Lemma lem1636185 (d2 : real) : (term117 d2) = term41.
Proof. exact (@lem1483446 d2). Qed.
Lemma lem1636186 (d2 : real) : (term110 d2) = term41.
Proof. exact (TRANS (@lem1636184 d2) (@lem1636185 d2)). Qed.
Lemma lem1636187 (d1 : real) (d2 : real) : (term193 d1 d2) = term141.
Proof. exact (MK_COMB (@lem1636175 d1) (@lem1636186 d2)). Qed.
Lemma lem1636188 (d1 : real) (d2 : real) : (term192 d1 d2) = term141.
Proof. exact (TRANS (@lem1636162 d1 d2) (@lem1636187 d1 d2)). Qed.
Lemma lem1636189 : term141 = term41.
Proof. exact (@lem1483448 term41). Qed.
Lemma lem1636190 (d1 : real) (d2 : real) : (term192 d1 d2) = term41.
Proof. exact (TRANS (@lem1636188 d1 d2) (@lem1636189)). Qed.
Lemma lem1636191 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1636192 (d1 : real) (d2 : real) : (term195 d1 d2) = term119.
Proof. exact (MK_COMB (@lem1636191) (@lem1636190 d1 d2)). Qed.
Lemma lem1636193 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1636194 (d1 : real) (d2 : real) : (term191 d1 d2) = term120.
Proof. exact (MK_COMB (@lem1636192 d1 d2) (@lem1636193)). Qed.
Lemma lem1636195 (d2 : real) (d1 : real) (e : real) (h1 : term175 d2 d1 e) : term120.
Proof. exact (EQ_MP (@lem1636194 d1 d2) (@lem1636161 d2 d1 e h1)). Qed.
Lemma lem1636197 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1636198 : term120 = term121.
Proof. exact (@lem1636197 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1636199 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1636200 : term120 = False.
Proof. exact (TRANS (@lem1636198) (@lem1636199)). Qed.
Lemma lem1636201 (d2 : real) (d1 : real) (e : real) (h1 : term175 d2 d1 e) : False.
Proof. exact (EQ_MP (@lem1636200) (@lem1636195 d2 d1 e h1)). Qed.
Lemma lem1636202 (d1 : real) (d2 : real) (e : real) (h1 : term196 d1 d2 e) : term196 d1 d2 e.
Proof. exact (h1). Qed.
Lemma lem1636203 (d1 : real) (d2 : real) (e : real) (h1 : term196 d1 d2 e) : term57 d2 e.
Proof. exact (proj2 (@lem1636202 d1 d2 e h1)). Qed.
Lemma lem1636204 (d1 : real) (d2 : real) (e : real) (h1 : term196 d1 d2 e) : term166 e d2 d1.
Proof. exact (proj1 (@lem1636202 d1 d2 e h1)). Qed.
Lemma lem1636206 (d1 : real) (d2 : real) (e : real) (h1 : term196 d1 d2 e) : term42 d2 e.
Proof. exact (proj1 (@lem1636204 d1 d2 e h1)). Qed.
Lemma lem1636214 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1636215 : term90 = term91.
Proof. exact (@lem1636214 (NUMERAL 0) term48). Qed.
Lemma lem1636216 : term92 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1636217 (h1 : term92 = (BIT1 0)) : term91 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1636218 : (term92 = (BIT1 0)) = (term91 = True).
Proof. exact (prop_ext (fun h1 : term92 = (BIT1 0) => @lem1636217 h1) (fun h1 : term91 = True => @lem1636216)). Qed.
Lemma lem1636219 : term91 = True.
Proof. exact (EQ_MP (@lem1636218) (@lem1636216)). Qed.
Lemma lem1636220 : term90 = True.
Proof. exact (TRANS (@lem1636215) (@lem1636219)). Qed.
Lemma lem1636221 : True = term90.
Proof. exact (SYM (@lem1636220)). Qed.
Lemma lem1636222 : term90.
Proof. exact (EQ_MP (@lem1636221) (@lem0)). Qed.
Lemma lem1636223 (d1 : real) (d2 : real) (e : real) (h1 : term196 d1 d2 e) : term123 d2 e.
Proof. exact (conj (@lem1636222) (@lem1636203 d1 d2 e h1)). Qed.
Lemma lem1636225 (x : real) (y : real) : term94 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1636226 (d2 : real) (e : real) : term124 d2 e.
Proof. exact (@lem1636225 term96 (term53 d2 e)). Qed.
Lemma lem1636227 (d1 : real) (d2 : real) (e : real) (h1 : term196 d1 d2 e) : term125 d2 e.
Proof. exact (@lem1636226 d2 e (@lem1636223 d1 d2 e h1)). Qed.
Lemma lem1636228 (d2 : real) (e : real) : (term126 d2 e) = (term53 d2 e).
Proof. exact (@lem1483460 (term53 d2 e)). Qed.
Lemma lem1636229 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1636230 (d2 : real) (e : real) : (term127 d2 e) = (term56 d2 e).
Proof. exact (MK_COMB (@lem1636229) (@lem1636228 d2 e)). Qed.
Lemma lem1636231 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1636232 (d2 : real) (e : real) : (term125 d2 e) = (term57 d2 e).
Proof. exact (MK_COMB (@lem1636230 d2 e) (@lem1636231)). Qed.
Lemma lem1636233 (d1 : real) (d2 : real) (e : real) (h1 : term196 d1 d2 e) : term57 d2 e.
Proof. exact (EQ_MP (@lem1636232 d2 e) (@lem1636227 d1 d2 e h1)). Qed.
Lemma lem1636235 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1636236 : term90 = term91.
Proof. exact (@lem1636235 (NUMERAL 0) term48). Qed.
Lemma lem1636237 : term92 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1636238 (h1 : term92 = (BIT1 0)) : term91 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1636239 : (term92 = (BIT1 0)) = (term91 = True).
Proof. exact (prop_ext (fun h1 : term92 = (BIT1 0) => @lem1636238 h1) (fun h1 : term91 = True => @lem1636237)). Qed.
Lemma lem1636240 : term91 = True.
Proof. exact (EQ_MP (@lem1636239) (@lem1636237)). Qed.
Lemma lem1636241 : term90 = True.
Proof. exact (TRANS (@lem1636236) (@lem1636240)). Qed.
Lemma lem1636242 : True = term90.
Proof. exact (SYM (@lem1636241)). Qed.
Lemma lem1636243 : term90.
Proof. exact (EQ_MP (@lem1636242) (@lem0)). Qed.
Lemma lem1636244 (d1 : real) (d2 : real) (e : real) (h1 : term196 d1 d2 e) : term128 d2 e.
Proof. exact (conj (@lem1636243) (@lem1636206 d1 d2 e h1)). Qed.
Lemma lem1636246 (x : real) (y : real) : term101 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1636247 (d2 : real) (e : real) : term129 d2 e.
Proof. exact (@lem1636246 term96 (term38 d2 e)). Qed.
Lemma lem1636248 (d1 : real) (d2 : real) (e : real) (h1 : term196 d1 d2 e) : term130 d2 e.
Proof. exact (@lem1636247 d2 e (@lem1636244 d1 d2 e h1)). Qed.
Lemma lem1636249 (d2 : real) (e : real) : (term131 d2 e) = (term38 d2 e).
Proof. exact (@lem1483460 (term38 d2 e)). Qed.
Lemma lem1636250 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1636251 (d2 : real) (e : real) : (term132 d2 e) = (term40 d2 e).
Proof. exact (MK_COMB (@lem1636250) (@lem1636249 d2 e)). Qed.
Lemma lem1636252 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1636253 (d2 : real) (e : real) : (term130 d2 e) = (term42 d2 e).
Proof. exact (MK_COMB (@lem1636251 d2 e) (@lem1636252)). Qed.
Lemma lem1636254 (d1 : real) (d2 : real) (e : real) (h1 : term196 d1 d2 e) : term42 d2 e.
Proof. exact (EQ_MP (@lem1636253 d2 e) (@lem1636248 d1 d2 e h1)). Qed.
Lemma lem1636255 (d1 : real) (d2 : real) (e : real) (h1 : term196 d1 d2 e) : term133 d2 e.
Proof. exact (conj (@lem1636254 d1 d2 e h1) (@lem1636233 d1 d2 e h1)). Qed.
Lemma lem1636257 (x : real) (y : real) : term107 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1636258 (d2 : real) (e : real) : term134 d2 e.
Proof. exact (@lem1636257 (term38 d2 e) (term53 d2 e)). Qed.
Lemma lem1636259 (d1 : real) (d2 : real) (e : real) (h1 : term196 d1 d2 e) : term135 d2 e.
Proof. exact (@lem1636258 d2 e (@lem1636255 d1 d2 e h1)). Qed.
Lemma lem1636260 (d2 : real) (e : real) : (term136 d2 e) = (term137 d2 e).
Proof. exact (@lem1483480 d2 (term54 d2) (term54 e) e). Qed.
Lemma lem1636261 (d2 : real) : (term110 d2) = (term111 d2).
Proof. exact (@lem1483442 term112 d2). Qed.
Lemma lem1636263 (m : nat) : (term113 m) = term41.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1636264 : term114 = term41.
Proof. exact (@lem1636263 term48). Qed.
Lemma lem1636265 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1636266 : term115 = term116.
Proof. exact (MK_COMB (@lem1636265) (@lem1636264)). Qed.
Lemma lem1636267 (d2 : real) : d2 = d2.
Proof. exact (eq_refl d2). Qed.
Lemma lem1636268 (d2 : real) : (term111 d2) = (term117 d2).
Proof. exact (MK_COMB (@lem1636266) (@lem1636267 d2)). Qed.
Lemma lem1636269 (d2 : real) : (term110 d2) = (term117 d2).
Proof. exact (TRANS (@lem1636261 d2) (@lem1636268 d2)). Qed.
Lemma lem1636270 (d2 : real) : (term117 d2) = term41.
Proof. exact (@lem1483446 d2). Qed.
Lemma lem1636271 (d2 : real) : (term110 d2) = term41.
Proof. exact (TRANS (@lem1636269 d2) (@lem1636270 d2)). Qed.
Lemma lem1636272 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1636273 (d2 : real) : (term138 d2) = term139.
Proof. exact (MK_COMB (@lem1636272) (@lem1636271 d2)). Qed.
Lemma lem1636274 (e : real) : (term140 e) = (term111 e).
Proof. exact (@lem1483440 term112 e). Qed.
Lemma lem1636276 (m : nat) : (term113 m) = term41.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1636277 : term114 = term41.
Proof. exact (@lem1636276 term48). Qed.
Lemma lem1636278 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1636279 : term115 = term116.
Proof. exact (MK_COMB (@lem1636278) (@lem1636277)). Qed.
Lemma lem1636280 (e : real) : e = e.
Proof. exact (eq_refl e). Qed.
Lemma lem1636281 (e : real) : (term111 e) = (term117 e).
Proof. exact (MK_COMB (@lem1636279) (@lem1636280 e)). Qed.
Lemma lem1636282 (e : real) : (term140 e) = (term117 e).
Proof. exact (TRANS (@lem1636274 e) (@lem1636281 e)). Qed.
Lemma lem1636283 (e : real) : (term117 e) = term41.
Proof. exact (@lem1483446 e). Qed.
Lemma lem1636284 (e : real) : (term140 e) = term41.
Proof. exact (TRANS (@lem1636282 e) (@lem1636283 e)). Qed.
Lemma lem1636285 (d2 : real) (e : real) : (term137 d2 e) = term141.
Proof. exact (MK_COMB (@lem1636273 d2) (@lem1636284 e)). Qed.
Lemma lem1636286 (d2 : real) (e : real) : (term136 d2 e) = term141.
Proof. exact (TRANS (@lem1636260 d2 e) (@lem1636285 d2 e)). Qed.
Lemma lem1636287 : term141 = term41.
Proof. exact (@lem1483448 term41). Qed.
Lemma lem1636288 (d2 : real) (e : real) : (term136 d2 e) = term41.
Proof. exact (TRANS (@lem1636286 d2 e) (@lem1636287)). Qed.
Lemma lem1636289 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1636290 (d2 : real) (e : real) : (term142 d2 e) = term119.
Proof. exact (MK_COMB (@lem1636289) (@lem1636288 d2 e)). Qed.
Lemma lem1636291 : term41 = term41.
Proof. exact (eq_refl term41). Qed.
Lemma lem1636292 (d2 : real) (e : real) : (term135 d2 e) = term120.
Proof. exact (MK_COMB (@lem1636290 d2 e) (@lem1636291)). Qed.
Lemma lem1636293 (d1 : real) (d2 : real) (e : real) (h1 : term196 d1 d2 e) : term120.
Proof. exact (EQ_MP (@lem1636292 d2 e) (@lem1636259 d1 d2 e h1)). Qed.
Lemma lem1636295 (n : nat) (m : nat) : (term89 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1636296 : term120 = term121.
Proof. exact (@lem1636295 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1636297 : term121 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1636298 : term120 = False.
Proof. exact (TRANS (@lem1636296) (@lem1636297)). Qed.
Lemma lem1636299 (d1 : real) (d2 : real) (e : real) (h1 : term196 d1 d2 e) : False.
Proof. exact (EQ_MP (@lem1636298) (@lem1636293 d1 d2 e h1)). Qed.
Lemma lem1636300 (d1 : real) (d2 : real) (e : real) (h1 : term171 d1 d2 e) : False.
Proof. exact (or_elim (@lem1636030 d1 d2 e h1) (fun h0 : term175 d2 d1 e => @lem1636201 d2 d1 e h0) (fun h0 : term196 d1 d2 e => @lem1636299 d1 d2 e h0)). Qed.
Lemma lem1636301 (d1 : real) (d2 : real) (e : real) (h1 : term173 d1 d2 e) : False.
Proof. exact (or_elim (@lem1635949 d1 d2 e h1) (fun h0 : term174 d2 d1 e => @lem1636029 d2 d1 e h0) (fun h0 : term171 d1 d2 e => @lem1636300 d1 d2 e h0)). Qed.
Lemma lem1636303 (d1 : real) (d2 : real) (e : real) (h1 : term173 d1 d2 e) : term173 d1 d2 e.
Proof. exact (h1). Qed.
Lemma lem1636304 (d1 : real) (d2 : real) (e : real) (h1 : term173 d1 d2 e) : (term173 d1 d2 e) = False.
Proof. exact (prop_ext (fun h2 : term173 d1 d2 e => @lem1636301 d1 d2 e h1) (fun h2 : False => @lem1636303 d1 d2 e h1)). Qed.
Lemma lem1636305 (d1 : real) (d2 : real) (e : real) (h1 : term173 d1 d2 e) : False.
Proof. exact (EQ_MP (@lem1636304 d1 d2 e h1) (@lem1636303 d1 d2 e h1)). Qed.
Lemma lem1636306 (d1 : real) (e : real) (d2 : real) (h1 : term160 d1 e d2) : term160 d1 e d2.
Proof. exact (h1). Qed.
Lemma lem1636307 (d1 : real) (e : real) (d2 : real) (h1 : term160 d1 e d2) : term173 d1 d2 e.
Proof. exact (EQ_MP (@lem1635933 d1 d2 e) (@lem1636306 d1 e d2 h1)). Qed.
Lemma lem1636308 (d1 : real) (e : real) (d2 : real) (h1 : term160 d1 e d2) : (term173 d1 d2 e) = False.
Proof. exact (prop_ext (fun h2 : term173 d1 d2 e => @lem1636305 d1 d2 e h2) (fun h2 : False => @lem1636307 d1 e d2 h1)). Qed.
Lemma lem1636309 (d1 : real) (e : real) (d2 : real) (h1 : term160 d1 e d2) : False.
Proof. exact (EQ_MP (@lem1636308 d1 e d2 h1) (@lem1636307 d1 e d2 h1)). Qed.
Lemma lem1636310 (d1 : real) (e : real) (d2 : real) : term197 d1 e d2.
Proof. exact (fun h0 : term160 d1 e d2 => @lem1636309 d1 e d2 h0). Qed.
Lemma lem1636311 (d1 : real) (e : real) (d2 : real) : term198 d1 e d2.
Proof. exact (@lem1386578 (term199 d1 e d2)). Qed.
Lemma lem1636312 (d1 : real) (e : real) (d2 : real) : term199 d1 e d2.
Proof. exact (@lem1636311 d1 e d2 (@lem1636310 d1 e d2)). Qed.
Lemma lem1636313 (d1 : real) (d2 : real) (e : real) (h1 : real_le d2 d1) (h2 : real_lt e d2) (h3 : term7 d1) (h4 : term7 d2) (h5 : term7 e) : term36 d1 e d2.
Proof. exact (@lem1636312 d1 e d2 (@lem1634900 d1 d2 e h1 h2 h3 h4 h5)). Qed.
Lemma lem1636314 (d1 : real) (d2 : real) (e : real) (h1 : real_le d1 d2) (h2 : real_lt e d1) (h3 : term7 d1) (h4 : term7 d2) (h5 : term7 e) : term36 d1 e d2.
Proof. exact (@lem1635606 d1 e d2 (@lem1634896 d1 d2 e h1 h2 h3 h4 h5)). Qed.
Lemma lem1636315 (d1 : real) (d2 : real) (e : real) (h1 : real_le d2 d1) (h2 : real_lt e d2) (h3 : term7 d1) (h4 : term7 d2) (h5 : term7 e) : term13 d1 d2.
Proof. exact (ex_intro (term200 d1 d2) e (@lem1636313 d1 d2 e h1 h2 h3 h4 h5)). Qed.
Lemma lem1636316 (d1 : real) (d2 : real) (e : real) (h1 : real_le d1 d2) (h2 : real_lt e d1) (h3 : term7 d1) (h4 : term7 d2) (h5 : term7 e) : term13 d1 d2.
Proof. exact (ex_intro (term200 d1 d2) e (@lem1636314 d1 d2 e h1 h2 h3 h4 h5)). Qed.
Lemma lem1636317 (e : real) (d2 : real) (h1 : term18 e d2) : real_lt e d2.
Proof. exact (proj2 (@lem1634890 e d2 h1)). Qed.
Lemma lem1636318 (e : real) (d2 : real) (h1 : term18 e d2) : term7 e.
Proof. exact (proj1 (@lem1634890 e d2 h1)). Qed.
Lemma lem1636319 (d1 : real) (d2 : real) (e : real) (h1 : real_le d2 d1) (h2 : real_lt e d2) (h3 : term7 d1) (h4 : term7 d2) (h5 : term7 e) : (real_lt e d2) = (term13 d1 d2).
Proof. exact (prop_ext (fun h6 : real_lt e d2 => @lem1636315 d1 d2 e h1 h2 h3 h4 h5) (fun h6 : term13 d1 d2 => @lem1634891 e d2 h2)). Qed.
Lemma lem1636320 (d1 : real) (d2 : real) (e : real) (h1 : real_le d2 d1) (h2 : real_lt e d2) (h3 : term7 d1) (h4 : term7 d2) (h5 : term7 e) : term13 d1 d2.
Proof. exact (EQ_MP (@lem1636319 d1 d2 e h1 h2 h3 h4 h5) (@lem1634891 e d2 h2)). Qed.
Lemma lem1636321 (d1 : real) (d2 : real) (e : real) (h1 : real_le d2 d1) (h2 : real_lt e d2) (h3 : term7 d1) (h4 : term7 d2) (h5 : term7 e) : (term7 e) = (term13 d1 d2).
Proof. exact (prop_ext (fun h6 : term7 e => @lem1636320 d1 d2 e h1 h2 h3 h4 h5) (fun h6 : term13 d1 d2 => @lem1634892 e h5)). Qed.
Lemma lem1636322 (d1 : real) (d2 : real) (e : real) (h1 : real_le d2 d1) (h2 : real_lt e d2) (h3 : term7 d1) (h4 : term7 d2) (h5 : term7 e) : term13 d1 d2.
Proof. exact (EQ_MP (@lem1636321 d1 d2 e h1 h2 h3 h4 h5) (@lem1634892 e h5)). Qed.
Lemma lem1636323 (d1 : real) (d2 : real) (e : real) (h1 : term18 e d2) (h2 : real_le d2 d1) (h3 : term7 d1) (h4 : term7 d2) (h5 : term7 e) : (real_lt e d2) = (term13 d1 d2).
Proof. exact (prop_ext (fun h6 : real_lt e d2 => @lem1636322 d1 d2 e h2 h6 h3 h4 h5) (fun h6 : term13 d1 d2 => @lem1636317 e d2 h1)). Qed.
Lemma lem1636324 (d1 : real) (d2 : real) (e : real) (h1 : term18 e d2) (h2 : real_le d2 d1) (h3 : term7 d1) (h4 : term7 d2) (h5 : term7 e) : term13 d1 d2.
Proof. exact (EQ_MP (@lem1636323 d1 d2 e h1 h2 h3 h4 h5) (@lem1636317 e d2 h1)). Qed.
Lemma lem1636325 (e : real) (d1 : real) (d2 : real) (h1 : term18 e d2) (h2 : real_le d2 d1) (h3 : term7 d1) (h4 : term7 d2) : (term7 e) = (term13 d1 d2).
Proof. exact (prop_ext (fun h5 : term7 e => @lem1636324 d1 d2 e h1 h2 h3 h4 h5) (fun h5 : term13 d1 d2 => @lem1636318 e d2 h1)). Qed.
Lemma lem1636326 (e : real) (d1 : real) (d2 : real) (h1 : term18 e d2) (h2 : real_le d2 d1) (h3 : term7 d1) (h4 : term7 d2) : term13 d1 d2.
Proof. exact (EQ_MP (@lem1636325 e d1 d2 h1 h2 h3 h4) (@lem1636318 e d2 h1)). Qed.
Lemma lem1636327 (d1 : real) (d2 : real) (h1 : term9 d2) (h2 : real_le d2 d1) (h3 : term7 d1) (h4 : term7 d2) : term13 d1 d2.
Proof. exact (ex_elim (@lem1634889 d2 h1) (fun e : real => fun h0 : term201 d2 e => @lem1636326 e d1 d2 h0 h2 h3 h4)). Qed.
Lemma lem1636328 (d1 : real) (d2 : real) (h1 : real_le d2 d1) (h2 : term7 d1) (h3 : term7 d2) : term17 d1 d2.
Proof. exact (fun h0 : term9 d2 => @lem1636327 d1 d2 h0 h1 h2 h3). Qed.
Lemma lem1636329 (e : real) (d1 : real) (h1 : term18 e d1) : real_lt e d1.
Proof. exact (proj2 (@lem1634886 e d1 h1)). Qed.
Lemma lem1636330 (e : real) (d1 : real) (h1 : term18 e d1) : term7 e.
Proof. exact (proj1 (@lem1634886 e d1 h1)). Qed.
Lemma lem1636331 (d1 : real) (d2 : real) (e : real) (h1 : real_le d1 d2) (h2 : real_lt e d1) (h3 : term7 d1) (h4 : term7 d2) (h5 : term7 e) : (real_lt e d1) = (term13 d1 d2).
Proof. exact (prop_ext (fun h6 : real_lt e d1 => @lem1636316 d1 d2 e h1 h2 h3 h4 h5) (fun h6 : term13 d1 d2 => @lem1634887 e d1 h2)). Qed.
Lemma lem1636332 (d1 : real) (d2 : real) (e : real) (h1 : real_le d1 d2) (h2 : real_lt e d1) (h3 : term7 d1) (h4 : term7 d2) (h5 : term7 e) : term13 d1 d2.
Proof. exact (EQ_MP (@lem1636331 d1 d2 e h1 h2 h3 h4 h5) (@lem1634887 e d1 h2)). Qed.
Lemma lem1636333 (d1 : real) (d2 : real) (e : real) (h1 : real_le d1 d2) (h2 : real_lt e d1) (h3 : term7 d1) (h4 : term7 d2) (h5 : term7 e) : (term7 e) = (term13 d1 d2).
Proof. exact (prop_ext (fun h6 : term7 e => @lem1636332 d1 d2 e h1 h2 h3 h4 h5) (fun h6 : term13 d1 d2 => @lem1634888 e h5)). Qed.
Lemma lem1636334 (d1 : real) (d2 : real) (e : real) (h1 : real_le d1 d2) (h2 : real_lt e d1) (h3 : term7 d1) (h4 : term7 d2) (h5 : term7 e) : term13 d1 d2.
Proof. exact (EQ_MP (@lem1636333 d1 d2 e h1 h2 h3 h4 h5) (@lem1634888 e h5)). Qed.
Lemma lem1636335 (d1 : real) (d2 : real) (e : real) (h1 : term18 e d1) (h2 : real_le d1 d2) (h3 : term7 d1) (h4 : term7 d2) (h5 : term7 e) : (real_lt e d1) = (term13 d1 d2).
Proof. exact (prop_ext (fun h6 : real_lt e d1 => @lem1636334 d1 d2 e h2 h6 h3 h4 h5) (fun h6 : term13 d1 d2 => @lem1636329 e d1 h1)). Qed.
Lemma lem1636336 (d1 : real) (d2 : real) (e : real) (h1 : term18 e d1) (h2 : real_le d1 d2) (h3 : term7 d1) (h4 : term7 d2) (h5 : term7 e) : term13 d1 d2.
Proof. exact (EQ_MP (@lem1636335 d1 d2 e h1 h2 h3 h4 h5) (@lem1636329 e d1 h1)). Qed.
Lemma lem1636337 (e : real) (d1 : real) (d2 : real) (h1 : term18 e d1) (h2 : real_le d1 d2) (h3 : term7 d1) (h4 : term7 d2) : (term7 e) = (term13 d1 d2).
Proof. exact (prop_ext (fun h5 : term7 e => @lem1636336 d1 d2 e h1 h2 h3 h4 h5) (fun h5 : term13 d1 d2 => @lem1636330 e d1 h1)). Qed.
Lemma lem1636338 (e : real) (d1 : real) (d2 : real) (h1 : term18 e d1) (h2 : real_le d1 d2) (h3 : term7 d1) (h4 : term7 d2) : term13 d1 d2.
Proof. exact (EQ_MP (@lem1636337 e d1 d2 h1 h2 h3 h4) (@lem1636330 e d1 h1)). Qed.
Lemma lem1636339 (d1 : real) (d2 : real) (h1 : term9 d1) (h2 : real_le d1 d2) (h3 : term7 d1) (h4 : term7 d2) : term13 d1 d2.
Proof. exact (ex_elim (@lem1634885 d1 h1) (fun e : real => fun h0 : term201 d1 e => @lem1636338 e d1 d2 h0 h2 h3 h4)). Qed.
Lemma lem1636340 (d1 : real) (d2 : real) (h1 : real_le d1 d2) (h2 : term7 d1) (h3 : term7 d2) : term15 d1 d2.
Proof. exact (fun h0 : term9 d1 => @lem1636339 d1 d2 h0 h1 h2 h3). Qed.
Lemma lem1636341 (d1 : real) (d2 : real) (h1 : real_le d2 d1) (h2 : term7 d1) (h3 : term7 d2) : term16 d1 d2.
Proof. exact (EQ_MP (@lem1634884 d1 d2 h3) (@lem1636328 d1 d2 h1 h2 h3)). Qed.
Lemma lem1636342 (d1 : real) (d2 : real) (h1 : real_le d1 d2) (h2 : term7 d1) (h3 : term7 d2) : term14 d1 d2.
Proof. exact (EQ_MP (@lem1634837 d2 d1 h2) (@lem1636340 d1 d2 h1 h2 h3)). Qed.
Lemma lem1636343 (d1 : real) (d2 : real) (h1 : real_le d2 d1) (h2 : term7 d1) (h3 : term7 d2) : term13 d1 d2.
Proof. exact (@lem1636341 d1 d2 h1 h2 h3 (@lem1634776 d2)). Qed.
Lemma lem1636344 (d1 : real) (d2 : real) (h1 : real_le d1 d2) (h2 : term7 d1) (h3 : term7 d2) : term13 d1 d2.
Proof. exact (@lem1636342 d1 d2 h1 h2 h3 (@lem1634779 d1)). Qed.
Lemma lem1636345 (d1 : real) (d2 : real) (h1 : term7 d1) (h2 : term7 d2) : term13 d1 d2.
Proof. exact (or_elim (@lem1634785 d2 d1) (fun h0 : real_le d1 d2 => @lem1636344 d1 d2 h0 h1 h2) (fun h0 : real_le d2 d1 => @lem1636343 d1 d2 h0 h1 h2)). Qed.
Lemma lem1636346 (d1 : real) (d2 : real) (h1 : term6 d1 d2) : term7 d2.
Proof. exact (proj2 (@lem1634788 d1 d2 h1)). Qed.
Lemma lem1636347 (d1 : real) (d2 : real) (h1 : term6 d1 d2) : term7 d1.
Proof. exact (proj1 (@lem1634788 d1 d2 h1)). Qed.
Lemma lem1636348 (d1 : real) (d2 : real) (h1 : term7 d1) (h2 : term7 d2) : (term7 d2) = (term13 d1 d2).
Proof. exact (prop_ext (fun h3 : term7 d2 => @lem1636345 d1 d2 h1 h2) (fun h3 : term13 d1 d2 => @lem1634789 d2 h2)). Qed.
Lemma lem1636349 (d1 : real) (d2 : real) (h1 : term7 d1) (h2 : term7 d2) : term13 d1 d2.
Proof. exact (EQ_MP (@lem1636348 d1 d2 h1 h2) (@lem1634789 d2 h2)). Qed.
Lemma lem1636350 (d1 : real) (d2 : real) (h1 : term7 d1) (h2 : term7 d2) : (term7 d1) = (term13 d1 d2).
Proof. exact (prop_ext (fun h3 : term7 d1 => @lem1636349 d1 d2 h1 h2) (fun h3 : term13 d1 d2 => @lem1634790 d1 h1)). Qed.
Lemma lem1636351 (d1 : real) (d2 : real) (h1 : term7 d1) (h2 : term7 d2) : term13 d1 d2.
Proof. exact (EQ_MP (@lem1636350 d1 d2 h1 h2) (@lem1634790 d1 h1)). Qed.
Lemma lem1636352 (d2 : real) (d1 : real) (h1 : term6 d1 d2) (h2 : term7 d1) : (term7 d2) = (term13 d1 d2).
Proof. exact (prop_ext (fun h3 : term7 d2 => @lem1636351 d1 d2 h2 h3) (fun h3 : term13 d1 d2 => @lem1636346 d1 d2 h1)). Qed.
Lemma lem1636353 (d2 : real) (d1 : real) (h1 : term6 d1 d2) (h2 : term7 d1) : term13 d1 d2.
Proof. exact (EQ_MP (@lem1636352 d2 d1 h1 h2) (@lem1636346 d1 d2 h1)). Qed.
Lemma lem1636354 (d1 : real) (d2 : real) (h1 : term6 d1 d2) : (term7 d1) = (term13 d1 d2).
Proof. exact (prop_ext (fun h2 : term7 d1 => @lem1636353 d2 d1 h1 h2) (fun h2 : term13 d1 d2 => @lem1636347 d1 d2 h1)). Qed.
Lemma lem1636355 (d1 : real) (d2 : real) (h1 : term6 d1 d2) : term13 d1 d2.
Proof. exact (EQ_MP (@lem1636354 d1 d2 h1) (@lem1636347 d1 d2 h1)). Qed.
Lemma lem1636356 (d1 : real) (d2 : real) : term202 d1 d2.
Proof. exact (fun h0 : term6 d1 d2 => @lem1636355 d1 d2 h0). Qed.
Lemma lem1636361 (d1 : real) : term203 d1.
Proof. exact (fun d2 : real => @lem1636356 d1 d2). Qed.
Lemma lem1636366 : term204.
Proof. exact (fun d1 : real => @lem1636361 d1). Qed.
