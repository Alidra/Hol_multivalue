Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_DIV_EQ_1_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_DIV_LMUL_spec.
Require Import REAL_DIV_REFL_spec.
Require Import REAL_MUL_LZERO_spec.
Require Import REAL_MUL_RID_spec.
Require Import REAL_MUL_RZERO_spec.
Require Import TREAL_INV_0_spec.
Require Import real_div_spec.
Require Import thm0_spec.
Require Import thm1340072_spec.
Require Import thm1340231_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm4211_spec.
Require Import thm521920_spec.
Require Import thm522075_spec.
Require Import thm82_spec.
Lemma lem1593227 (y : real) : (real_mul y) = (real_mul y).
Proof. exact (eq_refl (real_mul y)). Qed.
Lemma lem1593230 (x : real) (y : real) (h1 : (real_div x y) = (term0 x y)) : (real_div x y) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem1593231 (x : real) (y : real) (h1 : (real_div x y) = (term0 x y)) : (term0 x y) = (real_div x y).
Proof. exact (SYM (@lem1593230 x y h1)). Qed.
Lemma lem1593232 (x : real) (y : real) (h1 : (term0 x y) = (real_div x y)) : (term0 x y) = (real_div x y).
Proof. exact (h1). Qed.
Lemma lem1593233 (x : real) (y : real) (h1 : (term0 x y) = (real_div x y)) : (real_div x y) = (term0 x y).
Proof. exact (SYM (@lem1593232 x y h1)). Qed.
Lemma lem1593234 (x : real) (y : real) : ((real_div x y) = (term0 x y)) = ((term0 x y) = (real_div x y)).
Proof. exact (prop_ext (fun h1 : (real_div x y) = (term0 x y) => @lem1593231 x y h1) (fun h1 : (term0 x y) = (real_div x y) => @lem1593233 x y h1)). Qed.
Lemma lem1593235 (x : real) : (term1 x) = (term2 x).
Proof. exact (fun_ext (fun y : real => @lem1593234 x y)). Qed.
Lemma lem1593236 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1593237 (x : real) : (term3 x) = (term4 x).
Proof. exact (MK_COMB (@lem1593236) (@lem1593235 x)). Qed.
Lemma lem1593238 : term5 = term6.
Proof. exact (fun_ext (fun x : real => @lem1593237 x)). Qed.
Lemma lem1593239 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1593240 : term7 = term8.
Proof. exact (MK_COMB (@lem1593239) (@lem1593238)). Qed.
Lemma lem1593241 : term8.
Proof. exact (EQ_MP (@lem1593240) (@lem1344936)). Qed.
Lemma lem1593575 : term9.
Proof. exact (EQ_MP (@lem521920) (@lem522075)). Qed.
Lemma lem1593576 : term10.
Proof. exact (proj2 (@lem1593575)). Qed.
Lemma lem1593577 : term11.
Proof. exact (proj2 (@lem1593576)). Qed.
Lemma lem1593578 : term12.
Proof. exact (proj2 (@lem1593577)). Qed.
Lemma lem1593579 : term13.
Proof. exact (proj2 (@lem1593578)). Qed.
Lemma lem1593580 : term14.
Proof. exact (proj2 (@lem1593579)). Qed.
Lemma lem1593612 : term15.
Proof. exact (proj1 (@lem1593580)). Qed.
Lemma lem1593613 (n : nat) : term16 n.
Proof. exact (@lem1593612 n). Qed.
Lemma lem1593614 (n : nat) : (term16 n) = ((0 = (BIT1 n)) = False).
Proof. exact (eq_refl (term16 n)). Qed.
Lemma lem1593629 : term17.
Proof. exact (proj1 (@lem1593575)). Qed.
Lemma lem1593630 (m : nat) : term18 m.
Proof. exact (@lem1593629 m). Qed.
Lemma lem1593631 (m : nat) : (term18 m) = (term19 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem1593632 (m : nat) : term19 m.
Proof. exact (EQ_MP (@lem1593631 m) (@lem1593630 m)). Qed.
Lemma lem1593633 (m : nat) (n : nat) : term20 m n.
Proof. exact (@lem1593632 m n). Qed.
Lemma lem1593634 (m : nat) (n : nat) : (term20 m n) = (((NUMERAL m) = (NUMERAL n)) = (m = n)).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem1593886 (m : nat) : term21 m.
Proof. exact (@lem1340231 m). Qed.
Lemma lem1593887 (m : nat) : (term21 m) = (term22 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem1593888 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem1593887 m) (@lem1593886 m)). Qed.
Lemma lem1593889 (m : nat) (n : nat) : term23 m n.
Proof. exact (@lem1593888 m n). Qed.
Lemma lem1593890 (m : nat) (n : nat) : (term23 m n) = (((real_of_num m) = (real_of_num n)) = (m = n)).
Proof. exact (eq_refl (term23 m n)). Qed.
Lemma lem1593892 (y : real) : term24 y.
Proof. exact (@lem9784 (y = term25)). Qed.
Lemma lem1593893 (y : real) : (term24 y) = (term26 y).
Proof. exact (eq_refl (term24 y)). Qed.
Lemma lem1593894 (y : real) : term26 y.
Proof. exact (EQ_MP (@lem1593893 y) (@lem1593892 y)). Qed.
Lemma lem1593896 (y : real) (h1 : term27 y) : term27 y.
Proof. exact (h1). Qed.
Lemma lem1593897 (x : real) : term24 x.
Proof. exact (@lem9784 (x = term25)). Qed.
Lemma lem1593898 (x : real) : (term24 x) = (term26 x).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem1593899 (x : real) : term26 x.
Proof. exact (EQ_MP (@lem1593898 x) (@lem1593897 x)). Qed.
Lemma lem1593901 (x : real) (h1 : term27 x) : term27 x.
Proof. exact (h1). Qed.
Lemma lem1593902 (x : real) : term28 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1593903 (x : real) : (term28 x) = (term3 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem1593904 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem1593903 x) (@lem1593902 x)). Qed.
Lemma lem1593905 (x : real) (y : real) : term29 x y.
Proof. exact (@lem1593904 x y). Qed.
Lemma lem1593906 (x : real) (y : real) : (term29 x y) = ((real_div x y) = (term0 x y)).
Proof. exact (eq_refl (term29 x y)). Qed.
Lemma lem1593913 (x : real) (y : real) : (real_div x y) = (term0 x y).
Proof. exact (EQ_MP (@lem1593906 x y) (@lem1593905 x y)). Qed.
Lemma lem1593914 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1593915 (x : real) (y : real) : (term30 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem1593914) (@lem1593913 x y)). Qed.
Lemma lem1593916 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1593917 (x : real) (y : real) : ((real_div x y) = term32) = ((term0 x y) = term32).
Proof. exact (MK_COMB (@lem1593915 x y) (@lem1593916)). Qed.
Lemma lem1593920 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1593921 (x : real) (y : real) : (term33 x y) = (term34 x y).
Proof. exact (MK_COMB (@lem1593920) (@lem1593917 x y)). Qed.
Lemma lem1593932 (x : real) (y : real) : (term35 x y) = (term35 x y).
Proof. exact (eq_refl (term35 x y)). Qed.
Lemma lem1593933 (x : real) (y : real) : (((real_div x y) = term32) = (term35 x y)) = (((term0 x y) = term32) = (term35 x y)).
Proof. exact (MK_COMB (@lem1593921 x y) (@lem1593932 x y)). Qed.
Lemma lem1593936 (x : real) (y : real) : (((term0 x y) = term32) = (term35 x y)) = (((real_div x y) = term32) = (term35 x y)).
Proof. exact (SYM (@lem1593933 x y)). Qed.
Lemma lem1593937 (x : real) : term36 x.
Proof. exact (@lem1357243 x). Qed.
Lemma lem1593938 (x : real) : (term36 x) = ((term37 x) = term25).
Proof. exact (eq_refl (term36 x)). Qed.
Lemma lem1593945 (x : real) (h1 : x = term25) : x = term25.
Proof. exact (h1). Qed.
Lemma lem1593946 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1593947 (x : real) (h1 : x = term25) : (real_mul x) = term38.
Proof. exact (MK_COMB (@lem1593946) (@lem1593945 x h1)). Qed.
Lemma lem1593948 (y : real) : (real_inv y) = (real_inv y).
Proof. exact (eq_refl (real_inv y)). Qed.
Lemma lem1593949 (y : real) (x : real) (h1 : x = term25) : (term0 x y) = (term39 y).
Proof. exact (MK_COMB (@lem1593947 x h1) (@lem1593948 y)). Qed.
Lemma lem1593951 (x : real) : (term37 x) = term25.
Proof. exact (EQ_MP (@lem1593938 x) (@lem1593937 x)). Qed.
Lemma lem1593952 (y : real) : (term39 y) = term25.
Proof. exact (@lem1593951 (real_inv y)). Qed.
Lemma lem1593953 (y : real) (x : real) (h1 : x = term25) : (term0 x y) = term25.
Proof. exact (TRANS (@lem1593949 y x h1) (@lem1593952 y)). Qed.
Lemma lem1593954 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1593955 (y : real) (x : real) (h1 : x = term25) : (term31 x y) = term40.
Proof. exact (MK_COMB (@lem1593954) (@lem1593953 y x h1)). Qed.
Lemma lem1593956 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1593957 (y : real) (x : real) (h1 : x = term25) : ((term0 x y) = term32) = (term25 = term32).
Proof. exact (MK_COMB (@lem1593955 y x h1) (@lem1593956)). Qed.
Lemma lem1593960 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1593961 (y : real) (x : real) (h1 : x = term25) : (term34 x y) = term41.
Proof. exact (MK_COMB (@lem1593960) (@lem1593957 y x h1)). Qed.
Lemma lem1593967 (x : real) (h1 : x = term25) : x = term25.
Proof. exact (h1). Qed.
Lemma lem1593968 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1593969 (x : real) (h1 : x = term25) : (@eq real x) = term40.
Proof. exact (MK_COMB (@lem1593968) (@lem1593967 x h1)). Qed.
Lemma lem1593970 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1593971 (y : real) (x : real) (h1 : x = term25) : (x = y) = (term25 = y).
Proof. exact (MK_COMB (@lem1593969 x h1) (@lem1593970 y)). Qed.
Lemma lem1593974 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1593975 (y : real) (x : real) (h1 : x = term25) : (term42 x y) = (term43 y).
Proof. exact (MK_COMB (@lem1593974) (@lem1593971 y x h1)). Qed.
Lemma lem1593981 (x : real) (h1 : x = term25) : x = term25.
Proof. exact (h1). Qed.
Lemma lem1593982 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1593983 (x : real) (h1 : x = term25) : (@eq real x) = term40.
Proof. exact (MK_COMB (@lem1593982) (@lem1593981 x h1)). Qed.
Lemma lem1593984 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem1593985 (x : real) (h1 : x = term25) : (x = term25) = (term25 = term25).
Proof. exact (MK_COMB (@lem1593983 x h1) (@lem1593984)). Qed.
Lemma lem1593987 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1593988 (x : real) : (x = x) = True.
Proof. exact (@lem1593987 real x). Qed.
Lemma lem1593989 : (term25 = term25) = True.
Proof. exact (@lem1593988 term25). Qed.
Lemma lem1593990 (x : real) (h1 : x = term25) : (x = term25) = True.
Proof. exact (TRANS (@lem1593985 x h1) (@lem1593989)). Qed.
Lemma lem1593991 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1593992 (x : real) (h1 : x = term25) : (term27 x) = (~ True).
Proof. exact (MK_COMB (@lem1593991) (@lem1593990 x h1)). Qed.
Lemma lem1593994 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1593995 (x : real) (h1 : x = term25) : (term27 x) = False.
Proof. exact (TRANS (@lem1593992 x h1) (@lem1593994)). Qed.
Lemma lem1593996 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1593997 (x : real) (h1 : x = term25) : (term44 x) = (and False).
Proof. exact (MK_COMB (@lem1593996) (@lem1593995 x h1)). Qed.
Lemma lem1594000 (y : real) : (term27 y) = (term27 y).
Proof. exact (eq_refl (term27 y)). Qed.
Lemma lem1594001 (y : real) (x : real) (h1 : x = term25) : (term45 x y) = (term46 y).
Proof. exact (MK_COMB (@lem1593997 x h1) (@lem1594000 y)). Qed.
Lemma lem1594003 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1594004 (y : real) : (term46 y) = False.
Proof. exact (@lem1594003 (term27 y)). Qed.
Lemma lem1594005 (y : real) (x : real) (h1 : x = term25) : (term45 x y) = False.
Proof. exact (TRANS (@lem1594001 y x h1) (@lem1594004 y)). Qed.
Lemma lem1594006 (y : real) (x : real) (h1 : x = term25) : (term35 x y) = (term47 y).
Proof. exact (MK_COMB (@lem1593975 y x h1) (@lem1594005 y x h1)). Qed.
Lemma lem1594008 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1594009 (y : real) : (term47 y) = False.
Proof. exact (@lem1594008 (term25 = y)). Qed.
Lemma lem1594010 (y : real) (x : real) (h1 : x = term25) : (term35 x y) = False.
Proof. exact (TRANS (@lem1594006 y x h1) (@lem1594009 y)). Qed.
Lemma lem1594011 (y : real) (x : real) (h1 : x = term25) : (((term0 x y) = term32) = (term35 x y)) = ((term25 = term32) = False).
Proof. exact (MK_COMB (@lem1593961 y x h1) (@lem1594010 y x h1)). Qed.
Lemma lem1594013 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem1594014 : ((term25 = term32) = False) = term48.
Proof. exact (@lem1594013 (term25 = term32)). Qed.
Lemma lem1594017 (y : real) (x : real) (h1 : x = term25) : (((term0 x y) = term32) = (term35 x y)) = term48.
Proof. exact (TRANS (@lem1594011 y x h1) (@lem1594014)). Qed.
Lemma lem1594018 (y : real) (x : real) (h1 : x = term25) : term48 = (((term0 x y) = term32) = (term35 x y)).
Proof. exact (SYM (@lem1594017 y x h1)). Qed.
Lemma lem1594022 (x : real) : term49 x.
Proof. exact (@lem82 (x = term25)). Qed.
Lemma lem1594046 (x : real) (h1 : term27 x) : (x = term25) = False.
Proof. exact (@lem1594022 x (@lem1593901 x h1)). Qed.
Lemma lem1594047 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1594048 (x : real) (h1 : term27 x) : (term27 x) = (~ False).
Proof. exact (MK_COMB (@lem1594047) (@lem1594046 x h1)). Qed.
Lemma lem1594050 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1594051 (x : real) (h1 : term27 x) : (term27 x) = True.
Proof. exact (TRANS (@lem1594048 x h1) (@lem1594050)). Qed.
Lemma lem1594052 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1594053 (x : real) (h1 : term27 x) : (term44 x) = (and True).
Proof. exact (MK_COMB (@lem1594052) (@lem1594051 x h1)). Qed.
Lemma lem1594056 (y : real) : (term27 y) = (term27 y).
Proof. exact (eq_refl (term27 y)). Qed.
Lemma lem1594057 (y : real) (x : real) (h1 : term27 x) : (term45 x y) = (term50 y).
Proof. exact (MK_COMB (@lem1594053 x h1) (@lem1594056 y)). Qed.
Lemma lem1594059 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1594060 (y : real) : (term50 y) = (term27 y).
Proof. exact (@lem1594059 (term27 y)). Qed.
Lemma lem1594063 (y : real) (x : real) (h1 : term27 x) : (term45 x y) = (term27 y).
Proof. exact (TRANS (@lem1594057 y x h1) (@lem1594060 y)). Qed.
Lemma lem1594064 (x : real) (y : real) : (term42 x y) = (term42 x y).
Proof. exact (eq_refl (term42 x y)). Qed.
Lemma lem1594065 (y : real) (x : real) (h1 : term27 x) : (term35 x y) = (term51 x y).
Proof. exact (MK_COMB (@lem1594064 x y) (@lem1594063 y x h1)). Qed.
Lemma lem1594068 (x : real) (y : real) : (term34 x y) = (term34 x y).
Proof. exact (eq_refl (term34 x y)). Qed.
Lemma lem1594069 (y : real) (x : real) (h1 : term27 x) : (((term0 x y) = term32) = (term35 x y)) = (((term0 x y) = term32) = (term51 x y)).
Proof. exact (MK_COMB (@lem1594068 x y) (@lem1594065 y x h1)). Qed.
Lemma lem1594072 (y : real) (x : real) (h1 : term27 x) : (((term0 x y) = term32) = (term51 x y)) = (((term0 x y) = term32) = (term35 x y)).
Proof. exact (SYM (@lem1594069 y x h1)). Qed.
Lemma lem1594100 (x : real) : term52 x.
Proof. exact (@lem1356740 x). Qed.
Lemma lem1594101 (x : real) : (term52 x) = ((term53 x) = term25).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem1594103 (x : real) : term49 x.
Proof. exact (@lem82 (x = term25)). Qed.
Lemma lem1594121 (y : real) (h1 : y = term25) : y = term25.
Proof. exact (h1). Qed.
Lemma lem1594122 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1594123 (y : real) (h1 : y = term25) : (real_inv y) = term54.
Proof. exact (MK_COMB (@lem1594122) (@lem1594121 y h1)). Qed.
Lemma lem1594125 : term54 = term25.
Proof. exact (EQ_MP (@lem1340072) (@lem1331743)). Qed.
Lemma lem1594126 (y : real) (h1 : y = term25) : (real_inv y) = term25.
Proof. exact (TRANS (@lem1594123 y h1) (@lem1594125)). Qed.
Lemma lem1594127 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1594128 (x : real) (y : real) (h1 : y = term25) : (term0 x y) = (term53 x).
Proof. exact (MK_COMB (@lem1594127 x) (@lem1594126 y h1)). Qed.
Lemma lem1594130 (x : real) : (term53 x) = term25.
Proof. exact (EQ_MP (@lem1594101 x) (@lem1594100 x)). Qed.
Lemma lem1594131 (x : real) (y : real) (h1 : y = term25) : (term0 x y) = term25.
Proof. exact (TRANS (@lem1594128 x y h1) (@lem1594130 x)). Qed.
Lemma lem1594132 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1594133 (x : real) (y : real) (h1 : y = term25) : (term31 x y) = term40.
Proof. exact (MK_COMB (@lem1594132) (@lem1594131 x y h1)). Qed.
Lemma lem1594134 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1594135 (x : real) (y : real) (h1 : y = term25) : ((term0 x y) = term32) = (term25 = term32).
Proof. exact (MK_COMB (@lem1594133 x y h1) (@lem1594134)). Qed.
Lemma lem1594138 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1594139 (x : real) (y : real) (h1 : y = term25) : (term34 x y) = term41.
Proof. exact (MK_COMB (@lem1594138) (@lem1594135 x y h1)). Qed.
Lemma lem1594145 (y : real) (h1 : y = term25) : y = term25.
Proof. exact (h1). Qed.
Lemma lem1594146 (x : real) : (@eq real x) = (@eq real x).
Proof. exact (eq_refl (@eq real x)). Qed.
Lemma lem1594147 (x : real) (y : real) (h1 : y = term25) : (x = y) = (x = term25).
Proof. exact (MK_COMB (@lem1594146 x) (@lem1594145 y h1)). Qed.
Lemma lem1594149 (x : real) (h1 : term27 x) : (x = term25) = False.
Proof. exact (@lem1594103 x (@lem1593901 x h1)). Qed.
Lemma lem1594150 (x : real) (y : real) (h1 : term27 x) (h2 : y = term25) : (x = y) = False.
Proof. exact (TRANS (@lem1594147 x y h2) (@lem1594149 x h1)). Qed.
Lemma lem1594151 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1594152 (x : real) (y : real) (h1 : term27 x) (h2 : y = term25) : (term42 x y) = (and False).
Proof. exact (MK_COMB (@lem1594151) (@lem1594150 x y h1 h2)). Qed.
Lemma lem1594156 (y : real) (h1 : y = term25) : y = term25.
Proof. exact (h1). Qed.
Lemma lem1594157 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1594158 (y : real) (h1 : y = term25) : (@eq real y) = term40.
Proof. exact (MK_COMB (@lem1594157) (@lem1594156 y h1)). Qed.
Lemma lem1594159 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem1594160 (y : real) (h1 : y = term25) : (y = term25) = (term25 = term25).
Proof. exact (MK_COMB (@lem1594158 y h1) (@lem1594159)). Qed.
Lemma lem1594162 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1594163 (x : real) : (x = x) = True.
Proof. exact (@lem1594162 real x). Qed.
Lemma lem1594164 : (term25 = term25) = True.
Proof. exact (@lem1594163 term25). Qed.
Lemma lem1594165 (y : real) (h1 : y = term25) : (y = term25) = True.
Proof. exact (TRANS (@lem1594160 y h1) (@lem1594164)). Qed.
Lemma lem1594166 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1594167 (y : real) (h1 : y = term25) : (term27 y) = (~ True).
Proof. exact (MK_COMB (@lem1594166) (@lem1594165 y h1)). Qed.
Lemma lem1594169 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1594170 (y : real) (h1 : y = term25) : (term27 y) = False.
Proof. exact (TRANS (@lem1594167 y h1) (@lem1594169)). Qed.
Lemma lem1594171 (x : real) (y : real) (h1 : term27 x) (h2 : y = term25) : (term51 x y) = (False /\ False).
Proof. exact (MK_COMB (@lem1594152 x y h1 h2) (@lem1594170 y h2)). Qed.
Lemma lem1594173 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1594174 : (False /\ False) = False.
Proof. exact (@lem1594173 False). Qed.
Lemma lem1594175 (x : real) (y : real) (h1 : term27 x) (h2 : y = term25) : (term51 x y) = False.
Proof. exact (TRANS (@lem1594171 x y h1 h2) (@lem1594174)). Qed.
Lemma lem1594176 (x : real) (y : real) (h1 : term27 x) (h2 : y = term25) : (((term0 x y) = term32) = (term51 x y)) = ((term25 = term32) = False).
Proof. exact (MK_COMB (@lem1594139 x y h2) (@lem1594175 x y h1 h2)). Qed.
Lemma lem1594178 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem1594179 : ((term25 = term32) = False) = term48.
Proof. exact (@lem1594178 (term25 = term32)). Qed.
Lemma lem1594182 (x : real) (y : real) (h1 : term27 x) (h2 : y = term25) : (((term0 x y) = term32) = (term51 x y)) = term48.
Proof. exact (TRANS (@lem1594176 x y h1 h2) (@lem1594179)). Qed.
Lemma lem1594183 (x : real) (y : real) (h1 : term27 x) (h2 : y = term25) : term48 = (((term0 x y) = term32) = (term51 x y)).
Proof. exact (SYM (@lem1594182 x y h1 h2)). Qed.
Lemma lem1594200 (y : real) : term49 y.
Proof. exact (@lem82 (y = term25)). Qed.
Lemma lem1594222 (y : real) (h1 : term27 y) : (y = term25) = False.
Proof. exact (@lem1594200 y (@lem1593896 y h1)). Qed.
Lemma lem1594223 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1594224 (y : real) (h1 : term27 y) : (term27 y) = (~ False).
Proof. exact (MK_COMB (@lem1594223) (@lem1594222 y h1)). Qed.
Lemma lem1594226 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1594227 (y : real) (h1 : term27 y) : (term27 y) = True.
Proof. exact (TRANS (@lem1594224 y h1) (@lem1594226)). Qed.
Lemma lem1594228 (x : real) (y : real) : (term42 x y) = (term42 x y).
Proof. exact (eq_refl (term42 x y)). Qed.
Lemma lem1594229 (x : real) (y : real) (h1 : term27 y) : (term51 x y) = (term55 x y).
Proof. exact (MK_COMB (@lem1594228 x y) (@lem1594227 y h1)). Qed.
Lemma lem1594231 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1594232 (x : real) (y : real) : (term55 x y) = (x = y).
Proof. exact (@lem1594231 (x = y)). Qed.
Lemma lem1594235 (x : real) (y : real) (h1 : term27 y) : (term51 x y) = (x = y).
Proof. exact (TRANS (@lem1594229 x y h1) (@lem1594232 x y)). Qed.
Lemma lem1594236 (x : real) (y : real) : (term34 x y) = (term34 x y).
Proof. exact (eq_refl (term34 x y)). Qed.
Lemma lem1594237 (x : real) (y : real) (h1 : term27 y) : (((term0 x y) = term32) = (term51 x y)) = (((term0 x y) = term32) = (x = y)).
Proof. exact (MK_COMB (@lem1594236 x y) (@lem1594235 x y h1)). Qed.
Lemma lem1594240 (x : real) (y : real) (h1 : term27 y) : (((term0 x y) = term32) = (x = y)) = (((term0 x y) = term32) = (term51 x y)).
Proof. exact (SYM (@lem1594237 x y h1)). Qed.
Lemma lem1594242 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem1593890 m n) (@lem1593889 m n)). Qed.
Lemma lem1594243 : (term25 = term32) = ((NUMERAL 0) = term56).
Proof. exact (@lem1594242 (NUMERAL 0) term56). Qed.
Lemma lem1594245 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem1593634 m n) (@lem1593633 m n)). Qed.
Lemma lem1594246 : ((NUMERAL 0) = term56) = (0 = (BIT1 0)).
Proof. exact (@lem1594245 0 (BIT1 0)). Qed.
Lemma lem1594248 (n : nat) : (0 = (BIT1 n)) = False.
Proof. exact (EQ_MP (@lem1593614 n) (@lem1593613 n)). Qed.
Lemma lem1594249 : (0 = (BIT1 0)) = False.
Proof. exact (@lem1594248 0). Qed.
Lemma lem1594250 : ((NUMERAL 0) = term56) = False.
Proof. exact (TRANS (@lem1594246) (@lem1594249)). Qed.
Lemma lem1594251 : (term25 = term32) = False.
Proof. exact (TRANS (@lem1594243) (@lem1594250)). Qed.
Lemma lem1594252 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1594253 : term48 = (~ False).
Proof. exact (MK_COMB (@lem1594252) (@lem1594251)). Qed.
Lemma lem1594255 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1594256 : term48 = True.
Proof. exact (TRANS (@lem1594253) (@lem1594255)). Qed.
Lemma lem1594257 : True = term48.
Proof. exact (SYM (@lem1594256)). Qed.
Lemma lem1594260 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem1593890 m n) (@lem1593889 m n)). Qed.
Lemma lem1594261 : (term25 = term32) = ((NUMERAL 0) = term56).
Proof. exact (@lem1594260 (NUMERAL 0) term56). Qed.
Lemma lem1594263 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem1593634 m n) (@lem1593633 m n)). Qed.
Lemma lem1594264 : ((NUMERAL 0) = term56) = (0 = (BIT1 0)).
Proof. exact (@lem1594263 0 (BIT1 0)). Qed.
Lemma lem1594266 (n : nat) : (0 = (BIT1 n)) = False.
Proof. exact (EQ_MP (@lem1593614 n) (@lem1593613 n)). Qed.
Lemma lem1594267 : (0 = (BIT1 0)) = False.
Proof. exact (@lem1594266 0). Qed.
Lemma lem1594268 : ((NUMERAL 0) = term56) = False.
Proof. exact (TRANS (@lem1594264) (@lem1594267)). Qed.
Lemma lem1594269 : (term25 = term32) = False.
Proof. exact (TRANS (@lem1594261) (@lem1594268)). Qed.
Lemma lem1594270 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1594271 : term48 = (~ False).
Proof. exact (MK_COMB (@lem1594270) (@lem1594269)). Qed.
Lemma lem1594273 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1594274 : term48 = True.
Proof. exact (TRANS (@lem1594271) (@lem1594273)). Qed.
Lemma lem1594275 : True = term48.
Proof. exact (SYM (@lem1594274)). Qed.
Lemma lem1594278 (m : nat) (n : nat) : ((real_of_num m) = (real_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem1593890 m n) (@lem1593889 m n)). Qed.
Lemma lem1594279 : (term25 = term32) = ((NUMERAL 0) = term56).
Proof. exact (@lem1594278 (NUMERAL 0) term56). Qed.
Lemma lem1594281 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem1593634 m n) (@lem1593633 m n)). Qed.
Lemma lem1594282 : ((NUMERAL 0) = term56) = (0 = (BIT1 0)).
Proof. exact (@lem1594281 0 (BIT1 0)). Qed.
Lemma lem1594284 (n : nat) : (0 = (BIT1 n)) = False.
Proof. exact (EQ_MP (@lem1593614 n) (@lem1593613 n)). Qed.
Lemma lem1594285 : (0 = (BIT1 0)) = False.
Proof. exact (@lem1594284 0). Qed.
Lemma lem1594286 : ((NUMERAL 0) = term56) = False.
Proof. exact (TRANS (@lem1594282) (@lem1594285)). Qed.
Lemma lem1594287 : (term25 = term32) = False.
Proof. exact (TRANS (@lem1594279) (@lem1594286)). Qed.
Lemma lem1594288 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1594289 : term48 = (~ False).
Proof. exact (MK_COMB (@lem1594288) (@lem1594287)). Qed.
Lemma lem1594291 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1594292 : term48 = True.
Proof. exact (TRANS (@lem1594289) (@lem1594291)). Qed.
Lemma lem1594293 : True = term48.
Proof. exact (SYM (@lem1594292)). Qed.
Lemma lem1594294 : term48.
Proof. exact (EQ_MP (@lem1594293) (@lem0)). Qed.
Lemma lem1594313 (x : real) : term57 x.
Proof. exact (@lem1593241 x). Qed.
Lemma lem1594314 (x : real) : (term57 x) = (term4 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem1594315 (x : real) : term4 x.
Proof. exact (EQ_MP (@lem1594314 x) (@lem1594313 x)). Qed.
Lemma lem1594316 (x : real) (y : real) : term58 x y.
Proof. exact (@lem1594315 x y). Qed.
Lemma lem1594317 (x : real) (y : real) : (term58 x y) = ((term0 x y) = (real_div x y)).
Proof. exact (eq_refl (term58 x y)). Qed.
Lemma lem1594350 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term59 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1594351 (p : Prop) (q : Prop) (p' : Prop) : term60 p q p'.
Proof. exact (fun q' : Prop => @lem1594350 p q p' q'). Qed.
Lemma lem1594352 (p : Prop) (q : Prop) : term61 p q.
Proof. exact (fun p' : Prop => @lem1594351 p q p'). Qed.
Lemma lem1594353 (x : real) (y : real) : term62 x y.
Proof. exact (@lem1594352 ((term0 x y) = term32) (x = y)). Qed.
Lemma lem1594354 (x : real) (y : real) (p' : Prop) : term63 x y p'.
Proof. exact (@lem1594353 x y p'). Qed.
Lemma lem1594355 (x : real) (y : real) (p' : Prop) : (term63 x y p') = (term64 x y p').
Proof. exact (eq_refl (term63 x y p')). Qed.
Lemma lem1594356 (x : real) (y : real) (p' : Prop) : term64 x y p'.
Proof. exact (EQ_MP (@lem1594355 x y p') (@lem1594354 x y p')). Qed.
Lemma lem1594357 (x : real) (y : real) (p' : Prop) (q' : Prop) : term65 x y p' q'.
Proof. exact (@lem1594356 x y p' q'). Qed.
Lemma lem1594358 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term65 x y p' q') = (term66 x y p' q').
Proof. exact (eq_refl (term65 x y p' q')). Qed.
Lemma lem1594359 (x : real) (y : real) (p' : Prop) (q' : Prop) : term66 x y p' q'.
Proof. exact (EQ_MP (@lem1594358 x y p' q') (@lem1594357 x y p' q')). Qed.
Lemma lem1594363 (x : real) (y : real) : (term0 x y) = (real_div x y).
Proof. exact (EQ_MP (@lem1594317 x y) (@lem1594316 x y)). Qed.
Lemma lem1594366 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1594367 (x : real) (y : real) : (term31 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1594366) (@lem1594363 x y)). Qed.
Lemma lem1594370 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1594371 (x : real) (y : real) : ((term0 x y) = term32) = ((real_div x y) = term32).
Proof. exact (MK_COMB (@lem1594367 x y) (@lem1594370)). Qed.
Lemma lem1594376 (x : real) (y : real) (q' : Prop) : term67 x y q'.
Proof. exact (@lem1594359 x y ((real_div x y) = term32) q'). Qed.
Lemma lem1594377 (x : real) (y : real) (q' : Prop) : term68 x y q'.
Proof. exact (@lem1594376 x y q' (@lem1594371 x y)). Qed.
Lemma lem1594381 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1594382 (x : real) (y : real) : term69 x y.
Proof. exact (fun h0 : (real_div x y) = term32 => @lem1594381 x y). Qed.
Lemma lem1594383 (x : real) (y : real) : term70 x y.
Proof. exact (@lem1594377 x y (x = y)). Qed.
Lemma lem1594384 (x : real) (y : real) : (term71 x y) = (term72 x y).
Proof. exact (@lem1594383 x y (@lem1594382 x y)). Qed.
Lemma lem1594420 (x : real) (y : real) : (term72 x y) = (term71 x y).
Proof. exact (SYM (@lem1594384 x y)). Qed.
Lemma lem1594421 (x : real) : term73 x.
Proof. exact (@lem1593003 x). Qed.
Lemma lem1594422 (x : real) : (term73 x) = (term74 x).
Proof. exact (eq_refl (term73 x)). Qed.
Lemma lem1594423 (x : real) : term74 x.
Proof. exact (EQ_MP (@lem1594422 x) (@lem1594421 x)). Qed.
Lemma lem1594424 (x : real) (h1 : term27 x) : term27 x.
Proof. exact (h1). Qed.
Lemma lem1594425 (x : real) (h1 : term27 x) : (real_div x x) = term32.
Proof. exact (@lem1594423 x (@lem1594424 x h1)). Qed.
Lemma lem1594431 (x : real) : term57 x.
Proof. exact (@lem1593241 x). Qed.
Lemma lem1594432 (x : real) : (term57 x) = (term4 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem1594433 (x : real) : term4 x.
Proof. exact (EQ_MP (@lem1594432 x) (@lem1594431 x)). Qed.
Lemma lem1594434 (x : real) (y : real) : term58 x y.
Proof. exact (@lem1594433 x y). Qed.
Lemma lem1594435 (x : real) (y : real) : (term58 x y) = ((term0 x y) = (real_div x y)).
Proof. exact (eq_refl (term58 x y)). Qed.
Lemma lem1594450 (y : real) : term49 y.
Proof. exact (@lem82 (y = term25)). Qed.
Lemma lem1594468 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term59 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1594469 (p : Prop) (q : Prop) (p' : Prop) : term60 p q p'.
Proof. exact (fun q' : Prop => @lem1594468 p q p' q'). Qed.
Lemma lem1594470 (p : Prop) (q : Prop) : term61 p q.
Proof. exact (fun p' : Prop => @lem1594469 p q p'). Qed.
Lemma lem1594471 (x : real) (y : real) : term75 x y.
Proof. exact (@lem1594470 (x = y) ((term0 x y) = term32)). Qed.
Lemma lem1594472 (x : real) (y : real) (p' : Prop) : term76 x y p'.
Proof. exact (@lem1594471 x y p'). Qed.
Lemma lem1594473 (x : real) (y : real) (p' : Prop) : (term76 x y p') = (term77 x y p').
Proof. exact (eq_refl (term76 x y p')). Qed.
Lemma lem1594474 (x : real) (y : real) (p' : Prop) : term77 x y p'.
Proof. exact (EQ_MP (@lem1594473 x y p') (@lem1594472 x y p')). Qed.
Lemma lem1594475 (x : real) (y : real) (p' : Prop) (q' : Prop) : term78 x y p' q'.
Proof. exact (@lem1594474 x y p' q'). Qed.
Lemma lem1594476 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term78 x y p' q') = (term79 x y p' q').
Proof. exact (eq_refl (term78 x y p' q')). Qed.
Lemma lem1594477 (x : real) (y : real) (p' : Prop) (q' : Prop) : term79 x y p' q'.
Proof. exact (EQ_MP (@lem1594476 x y p' q') (@lem1594475 x y p' q')). Qed.
Lemma lem1594480 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1594481 (x : real) (y : real) (q' : Prop) : term80 x y q'.
Proof. exact (@lem1594477 x y (x = y) q'). Qed.
Lemma lem1594482 (x : real) (y : real) (q' : Prop) : term81 x y q'.
Proof. exact (@lem1594481 x y q' (@lem1594480 x y)). Qed.
Lemma lem1594487 (x : real) (y : real) : (term0 x y) = (real_div x y).
Proof. exact (EQ_MP (@lem1594435 x y) (@lem1594434 x y)). Qed.
Lemma lem1594491 (x : real) (y : real) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1594492 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem1594493 (x : real) (y : real) (h1 : x = y) : (real_div x) = (real_div y).
Proof. exact (MK_COMB (@lem1594492) (@lem1594491 x y h1)). Qed.
Lemma lem1594494 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1594495 (x : real) (y : real) (h1 : x = y) : (real_div x y) = (real_div y y).
Proof. exact (MK_COMB (@lem1594493 x y h1) (@lem1594494 y)). Qed.
Lemma lem1594497 (x : real) : term74 x.
Proof. exact (fun h0 : term27 x => @lem1594425 x h0). Qed.
Lemma lem1594498 (y : real) : term74 y.
Proof. exact (@lem1594497 y). Qed.
Lemma lem1594500 (y : real) (h1 : term27 y) : (y = term25) = False.
Proof. exact (@lem1594450 y (@lem1593896 y h1)). Qed.
Lemma lem1594501 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1594502 (y : real) (h1 : term27 y) : (term27 y) = (~ False).
Proof. exact (MK_COMB (@lem1594501) (@lem1594500 y h1)). Qed.
Lemma lem1594504 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1594505 (y : real) (h1 : term27 y) : (term27 y) = True.
Proof. exact (TRANS (@lem1594502 y h1) (@lem1594504)). Qed.
Lemma lem1594506 (y : real) (h1 : term27 y) : True = (term27 y).
Proof. exact (SYM (@lem1594505 y h1)). Qed.
Lemma lem1594507 (y : real) (h1 : term27 y) : term27 y.
Proof. exact (EQ_MP (@lem1594506 y h1) (@lem0)). Qed.
Lemma lem1594508 (y : real) (h1 : term27 y) : (real_div y y) = term32.
Proof. exact (@lem1594498 y (@lem1594507 y h1)). Qed.
Lemma lem1594509 (x : real) (y : real) (h1 : term27 y) (h2 : x = y) : (real_div x y) = term32.
Proof. exact (TRANS (@lem1594495 x y h2) (@lem1594508 y h1)). Qed.
Lemma lem1594510 (x : real) (y : real) (h1 : term27 y) (h2 : x = y) : (term0 x y) = term32.
Proof. exact (TRANS (@lem1594487 x y) (@lem1594509 x y h1 h2)). Qed.
Lemma lem1594511 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1594512 (x : real) (y : real) (h1 : term27 y) (h2 : x = y) : (term31 x y) = term82.
Proof. exact (MK_COMB (@lem1594511) (@lem1594510 x y h1 h2)). Qed.
Lemma lem1594513 : term32 = term32.
Proof. exact (eq_refl term32). Qed.
Lemma lem1594514 (x : real) (y : real) (h1 : term27 y) (h2 : x = y) : ((term0 x y) = term32) = (term32 = term32).
Proof. exact (MK_COMB (@lem1594512 x y h1 h2) (@lem1594513)). Qed.
Lemma lem1594516 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1594517 (x : real) : (x = x) = True.
Proof. exact (@lem1594516 real x). Qed.
Lemma lem1594518 : (term32 = term32) = True.
Proof. exact (@lem1594517 term32). Qed.
Lemma lem1594519 (x : real) (y : real) (h1 : term27 y) (h2 : x = y) : ((term0 x y) = term32) = True.
Proof. exact (TRANS (@lem1594514 x y h1 h2) (@lem1594518)). Qed.
Lemma lem1594520 (x : real) (y : real) (h1 : term27 y) : term83 x y.
Proof. exact (fun h0 : x = y => @lem1594519 x y h1 h0). Qed.
Lemma lem1594521 (x : real) (y : real) : term84 x y.
Proof. exact (@lem1594482 x y True). Qed.
Lemma lem1594522 (x : real) (y : real) (h1 : term27 y) : (term85 x y) = (term86 x y).
Proof. exact (@lem1594521 x y (@lem1594520 x y h1)). Qed.
Lemma lem1594526 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1594527 (x : real) (y : real) : (term86 x y) = True.
Proof. exact (@lem1594526 (x = y)). Qed.
Lemma lem1594528 (x : real) (y : real) (h1 : term27 y) : (term85 x y) = True.
Proof. exact (TRANS (@lem1594522 x y h1) (@lem1594527 x y)). Qed.
Lemma lem1594529 (x : real) (y : real) (h1 : term27 y) : True = (term85 x y).
Proof. exact (SYM (@lem1594528 x y h1)). Qed.
Lemma lem1594530 (x : real) (y : real) (h1 : term27 y) : term85 x y.
Proof. exact (EQ_MP (@lem1594529 x y h1) (@lem0)). Qed.
Lemma lem1594531 (x : real) (y : real) (h1 : (real_div x y) = term32) : (real_div x y) = term32.
Proof. exact (h1). Qed.
Lemma lem1594532 (x : real) (y : real) (h1 : (real_div x y) = term32) : (term87 x y) = (term88 y).
Proof. exact (MK_COMB (@lem1593227 y) (@lem1594531 x y h1)). Qed.
Lemma lem1594533 (x : real) : term89 x.
Proof. exact (@lem1383409 x). Qed.
Lemma lem1594534 (x : real) : (term89 x) = ((term88 x) = x).
Proof. exact (eq_refl (term89 x)). Qed.
Lemma lem1594536 (x : real) : term90 x.
Proof. exact (@lem1593226 x). Qed.
Lemma lem1594537 (x : real) : (term90 x) = (term91 x).
Proof. exact (eq_refl (term90 x)). Qed.
Lemma lem1594538 (x : real) : term91 x.
Proof. exact (EQ_MP (@lem1594537 x) (@lem1594536 x)). Qed.
Lemma lem1594539 (x : real) (y : real) : term92 x y.
Proof. exact (@lem1594538 x y). Qed.
Lemma lem1594540 (y : real) (x : real) : (term92 x y) = (term93 y x).
Proof. exact (eq_refl (term92 x y)). Qed.
Lemma lem1594541 (y : real) (x : real) : term93 y x.
Proof. exact (EQ_MP (@lem1594540 y x) (@lem1594539 x y)). Qed.
Lemma lem1594542 (y : real) (h1 : term27 y) : term27 y.
Proof. exact (h1). Qed.
Lemma lem1594543 (x : real) (y : real) (h1 : term27 y) : (term87 x y) = x.
Proof. exact (@lem1594541 y x (@lem1594542 y h1)). Qed.
Lemma lem1594562 (y : real) : term49 y.
Proof. exact (@lem82 (y = term25)). Qed.
Lemma lem1594580 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term59 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1594581 (p : Prop) (q : Prop) (p' : Prop) : term60 p q p'.
Proof. exact (fun q' : Prop => @lem1594580 p q p' q'). Qed.
Lemma lem1594582 (p : Prop) (q : Prop) : term61 p q.
Proof. exact (fun p' : Prop => @lem1594581 p q p'). Qed.
Lemma lem1594583 (x : real) (y : real) : term94 x y.
Proof. exact (@lem1594582 ((term87 x y) = (term88 y)) (x = y)). Qed.
Lemma lem1594584 (x : real) (y : real) (p' : Prop) : term95 x y p'.
Proof. exact (@lem1594583 x y p'). Qed.
Lemma lem1594585 (x : real) (y : real) (p' : Prop) : (term95 x y p') = (term96 x y p').
Proof. exact (eq_refl (term95 x y p')). Qed.
Lemma lem1594586 (x : real) (y : real) (p' : Prop) : term96 x y p'.
Proof. exact (EQ_MP (@lem1594585 x y p') (@lem1594584 x y p')). Qed.
Lemma lem1594587 (x : real) (y : real) (p' : Prop) (q' : Prop) : term97 x y p' q'.
Proof. exact (@lem1594586 x y p' q'). Qed.
Lemma lem1594588 (x : real) (y : real) (p' : Prop) (q' : Prop) : (term97 x y p' q') = (term98 x y p' q').
Proof. exact (eq_refl (term97 x y p' q')). Qed.
Lemma lem1594589 (x : real) (y : real) (p' : Prop) (q' : Prop) : term98 x y p' q'.
Proof. exact (EQ_MP (@lem1594588 x y p' q') (@lem1594587 x y p' q')). Qed.
Lemma lem1594593 (y : real) (x : real) : term93 y x.
Proof. exact (fun h0 : term27 y => @lem1594543 x y h0). Qed.
Lemma lem1594595 (y : real) (h1 : term27 y) : (y = term25) = False.
Proof. exact (@lem1594562 y (@lem1593896 y h1)). Qed.
Lemma lem1594596 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1594597 (y : real) (h1 : term27 y) : (term27 y) = (~ False).
Proof. exact (MK_COMB (@lem1594596) (@lem1594595 y h1)). Qed.
Lemma lem1594599 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1594600 (y : real) (h1 : term27 y) : (term27 y) = True.
Proof. exact (TRANS (@lem1594597 y h1) (@lem1594599)). Qed.
Lemma lem1594601 (y : real) (h1 : term27 y) : True = (term27 y).
Proof. exact (SYM (@lem1594600 y h1)). Qed.
Lemma lem1594602 (y : real) (h1 : term27 y) : term27 y.
Proof. exact (EQ_MP (@lem1594601 y h1) (@lem0)). Qed.
Lemma lem1594603 (x : real) (y : real) (h1 : term27 y) : (term87 x y) = x.
Proof. exact (@lem1594593 y x (@lem1594602 y h1)). Qed.
Lemma lem1594604 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1594605 (x : real) (y : real) (h1 : term27 y) : (term99 x y) = (@eq real x).
Proof. exact (MK_COMB (@lem1594604) (@lem1594603 x y h1)). Qed.
Lemma lem1594607 (x : real) : (term88 x) = x.
Proof. exact (EQ_MP (@lem1594534 x) (@lem1594533 x)). Qed.
Lemma lem1594608 (y : real) : (term88 y) = y.
Proof. exact (@lem1594607 y). Qed.
Lemma lem1594609 (x : real) (y : real) (h1 : term27 y) : ((term87 x y) = (term88 y)) = (x = y).
Proof. exact (MK_COMB (@lem1594605 x y h1) (@lem1594608 y)). Qed.
Lemma lem1594612 (x : real) (y : real) (q' : Prop) : term100 x y q'.
Proof. exact (@lem1594589 x y (x = y) q'). Qed.
Lemma lem1594613 (x : real) (q' : Prop) (y : real) (h1 : term27 y) : term101 x y q'.
Proof. exact (@lem1594612 x y q' (@lem1594609 x y h1)). Qed.
Lemma lem1594618 (x : real) (y : real) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1594619 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1594620 (x : real) (y : real) (h1 : x = y) : (@eq real x) = (@eq real y).
Proof. exact (MK_COMB (@lem1594619) (@lem1594618 x y h1)). Qed.
Lemma lem1594621 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1594622 (x : real) (y : real) (h1 : x = y) : (x = y) = (y = y).
Proof. exact (MK_COMB (@lem1594620 x y h1) (@lem1594621 y)). Qed.
Lemma lem1594624 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1594625 (x : real) : (x = x) = True.
Proof. exact (@lem1594624 real x). Qed.
Lemma lem1594626 (y : real) : (y = y) = True.
Proof. exact (@lem1594625 y). Qed.
Lemma lem1594627 (x : real) (y : real) (h1 : x = y) : (x = y) = True.
Proof. exact (TRANS (@lem1594622 x y h1) (@lem1594626 y)). Qed.
Lemma lem1594628 (x : real) (y : real) : term102 x y.
Proof. exact (fun h0 : x = y => @lem1594627 x y h0). Qed.
Lemma lem1594629 (x : real) (y : real) (h1 : term27 y) : term103 x y.
Proof. exact (@lem1594613 x True y h1). Qed.
Lemma lem1594630 (x : real) (y : real) (h1 : term27 y) : (term104 x y) = (term86 x y).
Proof. exact (@lem1594629 x y h1 (@lem1594628 x y)). Qed.
Lemma lem1594634 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1594635 (x : real) (y : real) : (term86 x y) = True.
Proof. exact (@lem1594634 (x = y)). Qed.
Lemma lem1594636 (x : real) (y : real) (h1 : term27 y) : (term104 x y) = True.
Proof. exact (TRANS (@lem1594630 x y h1) (@lem1594635 x y)). Qed.
Lemma lem1594637 (x : real) (y : real) (h1 : term27 y) : True = (term104 x y).
Proof. exact (SYM (@lem1594636 x y h1)). Qed.
Lemma lem1594638 (x : real) (y : real) (h1 : term27 y) : term104 x y.
Proof. exact (EQ_MP (@lem1594637 x y h1) (@lem0)). Qed.
Lemma lem1594639 (x : real) (y : real) (h1 : term27 y) (h2 : (real_div x y) = term32) : x = y.
Proof. exact (@lem1594638 x y h1 (@lem1594532 x y h2)). Qed.
Lemma lem1594640 (x : real) (y : real) (h1 : term27 y) : term72 x y.
Proof. exact (fun h0 : (real_div x y) = term32 => @lem1594639 x y h1 h0). Qed.
Lemma lem1594641 (x : real) (y : real) (h1 : term27 y) : term71 x y.
Proof. exact (EQ_MP (@lem1594420 x y) (@lem1594640 x y h1)). Qed.
Lemma lem1594642 (x : real) (y : real) (h1 : term27 y) : term105 x y.
Proof. exact (conj (@lem1594641 x y h1) (@lem1594530 x y h1)). Qed.
Lemma lem1594643 (x : real) (y : real) : (term105 x y) = (((term0 x y) = term32) = (x = y)).
Proof. exact (@lem32 ((term0 x y) = term32) (x = y)). Qed.
Lemma lem1594645 (x : real) (y : real) (h1 : term27 y) : ((term0 x y) = term32) = (x = y).
Proof. exact (EQ_MP (@lem1594643 x y) (@lem1594642 x y h1)). Qed.
Lemma lem1594646 (x : real) (y : real) (h1 : term27 y) : ((term0 x y) = term32) = (term51 x y).
Proof. exact (EQ_MP (@lem1594240 x y h1) (@lem1594645 x y h1)). Qed.
Lemma lem1594647 (x : real) (y : real) (h1 : term27 x) (h2 : y = term25) : ((term0 x y) = term32) = (term51 x y).
Proof. exact (EQ_MP (@lem1594183 x y h1 h2) (@lem1594294)). Qed.
Lemma lem1594648 : term48.
Proof. exact (EQ_MP (@lem1594275) (@lem0)). Qed.
Lemma lem1594649 : term48.
Proof. exact (EQ_MP (@lem1594257) (@lem0)). Qed.
Lemma lem1594650 (y : real) (x : real) (h1 : term27 x) : ((term0 x y) = term32) = (term51 x y).
Proof. exact (or_elim (@lem1593894 y) (fun h0 : y = term25 => @lem1594647 x y h1 h0) (fun h0 : term27 y => @lem1594646 x y h0)). Qed.
Lemma lem1594651 : term48.
Proof. exact (or_elim (@lem1593894 (@el real)) (fun h0 : (@el real) = term25 => @lem1594649) (fun h0 : term106 => @lem1594648)). Qed.
Lemma lem1594652 (y : real) (x : real) (h1 : term27 x) : ((term0 x y) = term32) = (term35 x y).
Proof. exact (EQ_MP (@lem1594072 y x h1) (@lem1594650 y x h1)). Qed.
Lemma lem1594653 (y : real) (x : real) (h1 : x = term25) : ((term0 x y) = term32) = (term35 x y).
Proof. exact (EQ_MP (@lem1594018 y x h1) (@lem1594651)). Qed.
Lemma lem1594654 (x : real) (y : real) : ((term0 x y) = term32) = (term35 x y).
Proof. exact (or_elim (@lem1593899 x) (fun h0 : x = term25 => @lem1594653 y x h0) (fun h0 : term27 x => @lem1594652 y x h0)). Qed.
Lemma lem1594655 (x : real) (y : real) : ((real_div x y) = term32) = (term35 x y).
Proof. exact (EQ_MP (@lem1593936 x y) (@lem1594654 x y)). Qed.
Lemma lem1594660 (x : real) : term107 x.
Proof. exact (fun y : real => @lem1594655 x y). Qed.
Lemma lem1594665 : term108.
Proof. exact (fun x : real => @lem1594660 x). Qed.
