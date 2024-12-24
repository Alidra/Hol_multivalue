Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7930003_term_abbrevs.
Require Import CONSTR_REC_spec.
Require Import thm1066568_spec.
Require Import thm1066569_spec.
Require Import thm7928419_spec.
Require Import thm7928450_spec.
Require Import thm7928454_spec.
Require Import thm7929765_spec.
Require Import thm9102_spec.
Lemma lem7929852 {A Z : Type'} (fn : type1350 A Z) (fn' : type1328 A Z) (h1 : fn = (term0 A Z fn')) : fn = (term0 A Z fn').
Proof. exact (h1). Qed.
Lemma lem7929853 {A Z : Type'} (a : type6 A) (_103802' : type39 A) (fn : type1350 A Z) (fn' : type1328 A Z) (h1 : _103802' = (term1 A)) (h2 : fn = (term0 A Z fn')) : (term2 A Z fn a) = (term3 A Z fn' _103802' a).
Proof. exact (MK_COMB (@lem7929852 A Z fn fn' h2) (@lem7929765 A a _103802' h1)). Qed.
Lemma lem7929854 {A Z : Type'} (fn : type1328 A Z) (_103802' : type39 A) (a : type6 A) : (term3 A Z fn _103802' a) = (term4 A Z fn _103802' a).
Proof. exact (eq_refl (term3 A Z fn _103802' a)). Qed.
Lemma lem7929855 {A Z : Type'} (a : type6 A) (_103802' : type39 A) (fn : type1350 A Z) (fn' : type1328 A Z) (h1 : _103802' = (term1 A)) (h2 : fn = (term0 A Z fn')) : (term2 A Z fn a) = (term4 A Z fn' _103802' a).
Proof. exact (TRANS (@lem7929853 A Z a _103802' fn fn' h1 h2) (@lem7929854 A Z fn' _103802' a)). Qed.
Lemma lem7929863 {A : Type'} (a : type6 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : tybit1' = (term5 A _103802')) : term6 A tybit1' _103802' a.
Proof. exact (@lem7928419 A tybit1' _103802' h1 a). Qed.
Lemma lem7929864 {A : Type'} (tybit1' : type1329 A) (_103802' : type39 A) (a : type6 A) : (term6 A tybit1' _103802' a) = (term7 A tybit1' _103802' a).
Proof. exact (eq_refl (term6 A tybit1' _103802' a)). Qed.
Lemma lem7929867 {A : Type'} (a : type6 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : tybit1' = (term5 A _103802')) : term7 A tybit1' _103802' a.
Proof. exact (EQ_MP (@lem7929864 A tybit1' _103802' a) (@lem7929863 A a tybit1' _103802' h1)). Qed.
Lemma lem7929868 {A : Type'} (a : type6 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : tybit1' = (term5 A _103802')) : term7 A tybit1' _103802' a.
Proof. exact (@lem7929867 A a tybit1' _103802' h1). Qed.
Lemma lem7929870 {A : Type'} (r : type1675 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : _103802' = (term1 A)) (h2 : tybit1' = (term5 A _103802')) : (tybit1' r) = ((term8 A r) = r).
Proof. exact (TRANS (@lem7928454 A r tybit1' _103802' h1 h2) (@lem7928450 A r)). Qed.
Lemma lem7929871 {A : Type'} (r : type1675 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : _103802' = (term1 A)) (h2 : tybit1' = (term5 A _103802')) : (tybit1' r) = ((term8 A r) = r).
Proof. exact (@lem7929870 A r tybit1' _103802' h1 h2). Qed.
Lemma lem7929872 {A : Type'} (a : type6 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : _103802' = (term1 A)) (h2 : tybit1' = (term5 A _103802')) : (term7 A tybit1' _103802' a) = ((term9 A _103802' a) = (_103802' a)).
Proof. exact (@lem7929871 A (_103802' a) tybit1' _103802' h1 h2). Qed.
Lemma lem7929873 {A : Type'} (a : type6 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : _103802' = (term1 A)) (h2 : tybit1' = (term5 A _103802')) : (term9 A _103802' a) = (_103802' a).
Proof. exact (EQ_MP (@lem7929872 A a tybit1' _103802' h1 h2) (@lem7929868 A a tybit1' _103802' h2)). Qed.
Lemma lem7929874 {A Z : Type'} (fn : type1328 A Z) : fn = fn.
Proof. exact (eq_refl fn). Qed.
Lemma lem7929875 {A Z : Type'} (fn : type1328 A Z) (a : type6 A) (tybit1' : type1329 A) (_103802' : type39 A) (h1 : _103802' = (term1 A)) (h2 : tybit1' = (term5 A _103802')) : (term4 A Z fn _103802' a) = (term10 A Z fn _103802' a).
Proof. exact (MK_COMB (@lem7929874 A Z fn) (@lem7929873 A a tybit1' _103802' h1 h2)). Qed.
Lemma lem7929876 {A Z : Type'} (a : type6 A) (tybit1' : type1329 A) (_103802' : type39 A) (fn : type1350 A Z) (fn' : type1328 A Z) (h1 : _103802' = (term1 A)) (h2 : tybit1' = (term5 A _103802')) (h3 : fn = (term0 A Z fn')) : (term2 A Z fn a) = (term10 A Z fn' _103802' a).
Proof. exact (TRANS (@lem7929855 A Z a _103802' fn fn' h1 h3) (@lem7929875 A Z fn' a tybit1' _103802' h1 h2)). Qed.
Lemma lem7929877 {A : Type'} (_103802' : type39 A) (h1 : _103802' = (term1 A)) : _103802' = (term1 A).
Proof. exact (h1). Qed.
Lemma lem7929878 {A : Type'} (a : type6 A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem7929879 {A : Type'} (a : type6 A) (_103802' : type39 A) (h1 : _103802' = (term1 A)) : (_103802' a) = (term11 A a).
Proof. exact (MK_COMB (@lem7929877 A _103802' h1) (@lem7929878 A a)). Qed.
Lemma lem7929880 {A : Type'} (a : type6 A) : (term11 A a) = (term12 A a).
Proof. exact (eq_refl (term11 A a)). Qed.
Lemma lem7929881 {A : Type'} (_103802' : type39 A) (a : type6 A) : (term13 A _103802' a) = (term13 A _103802' a).
Proof. exact (eq_refl (term13 A _103802' a)). Qed.
Lemma lem7929882 {A : Type'} (_103802' : type39 A) (a : type6 A) : ((_103802' a) = (term11 A a)) = ((_103802' a) = (term12 A a)).
Proof. exact (MK_COMB (@lem7929881 A _103802' a) (@lem7929880 A a)). Qed.
Lemma lem7929883 {A : Type'} (a : type6 A) (_103802' : type39 A) (h1 : _103802' = (term1 A)) : (_103802' a) = (term12 A a).
Proof. exact (EQ_MP (@lem7929882 A _103802' a) (@lem7929879 A a _103802' h1)). Qed.
Lemma lem7929884 {A Z : Type'} (fn : type1328 A Z) : fn = fn.
Proof. exact (eq_refl fn). Qed.
Lemma lem7929885 {A Z : Type'} (fn : type1328 A Z) (a : type6 A) (_103802' : type39 A) (h1 : _103802' = (term1 A)) : (term10 A Z fn _103802' a) = (term14 A Z fn a).
Proof. exact (MK_COMB (@lem7929884 A Z fn) (@lem7929883 A a _103802' h1)). Qed.
Lemma lem7929886 {A Z : Type'} (a : type6 A) (tybit1' : type1329 A) (_103802' : type39 A) (fn : type1350 A Z) (fn' : type1328 A Z) (h1 : _103802' = (term1 A)) (h2 : tybit1' = (term5 A _103802')) (h3 : fn = (term0 A Z fn')) : (term2 A Z fn a) = (term14 A Z fn' a).
Proof. exact (TRANS (@lem7929876 A Z a tybit1' _103802' fn fn' h1 h2 h3) (@lem7929885 A Z fn' a _103802' h1)). Qed.
Lemma lem7929887 {A Z : Type'} (tybit1' : type1329 A) (a : type6 A) (_103802' : type39 A) (fn : type1350 A Z) (fn' : type1328 A Z) (h1 : _103802' = (term1 A)) (h2 : fn = (term0 A Z fn')) : term15 A Z tybit1' _103802' fn fn' a.
Proof. exact (fun h0 : tybit1' = (term5 A _103802') => @lem7929886 A Z a tybit1' _103802' fn fn' h1 h0 h2). Qed.
Lemma lem7929888 {A : Type'} : (term1 A) = (term1 A).
Proof. exact (eq_refl (term1 A)). Qed.
Lemma lem7929889 {A Z : Type'} (tybit1' : type1329 A) (_103802' : type39 A) (a : type6 A) (fn : type1350 A Z) (fn' : type1328 A Z) (h1 : fn = (term0 A Z fn')) : term16 A Z tybit1' _103802' fn fn' a.
Proof. exact (fun h0 : _103802' = (term1 A) => @lem7929887 A Z tybit1' a _103802' fn fn' h0 h1). Qed.
Lemma lem7929890 {A Z : Type'} (tybit1' : type1329 A) (a : type6 A) (fn : type1350 A Z) (fn' : type1328 A Z) (h1 : fn = (term0 A Z fn')) : term17 A Z tybit1' fn fn' a.
Proof. exact (@lem7929889 A Z tybit1' (term1 A) a fn fn' h1). Qed.
Lemma lem7929891 {A Z : Type'} (tybit1' : type1329 A) (a : type6 A) (fn : type1350 A Z) (fn' : type1328 A Z) (h1 : fn = (term0 A Z fn')) : term18 A Z tybit1' fn fn' a.
Proof. exact (@lem7929890 A Z tybit1' a fn fn' h1 (@lem7929888 A)). Qed.
Lemma lem7929892 {A : Type'} (tybit1' : type1329 A) (h1 : tybit1' = (term19 A)) : tybit1' = (term19 A).
Proof. exact (h1). Qed.
Lemma lem7929893 {A Z : Type'} (a : type6 A) (tybit1' : type1329 A) (fn : type1350 A Z) (fn' : type1328 A Z) (h1 : tybit1' = (term19 A)) (h2 : fn = (term0 A Z fn')) : (term2 A Z fn a) = (term14 A Z fn' a).
Proof. exact (@lem7929891 A Z tybit1' a fn fn' h2 (@lem7929892 A tybit1' h1)). Qed.
Lemma lem7929894 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (eq_refl (term19 A)). Qed.
Lemma lem7929895 {A Z : Type'} (tybit1' : type1329 A) (a : type6 A) (fn : type1350 A Z) (fn' : type1328 A Z) (h1 : fn = (term0 A Z fn')) : term18 A Z tybit1' fn fn' a.
Proof. exact (fun h0 : tybit1' = (term19 A) => @lem7929893 A Z a tybit1' fn fn' h0 h1). Qed.
Lemma lem7929896 {A Z : Type'} (a : type6 A) (fn : type1350 A Z) (fn' : type1328 A Z) (h1 : fn = (term0 A Z fn')) : term20 A Z fn fn' a.
Proof. exact (@lem7929895 A Z (term19 A) a fn fn' h1). Qed.
Lemma lem7929897 {A Z : Type'} (a : type6 A) (fn : type1350 A Z) (fn' : type1328 A Z) (h1 : fn = (term0 A Z fn')) : (term2 A Z fn a) = (term14 A Z fn' a).
Proof. exact (@lem7929896 A Z a fn fn' h1 (@lem7929894 A)). Qed.
Lemma lem7929899 {A Z : Type'} : term21 A Z.
Proof. exact (@lem1065430 (type6 A) Z). Qed.
Lemma lem7929900 {A Z : Type'} (_103802' : type41 A Z) : term22 A Z _103802'.
Proof. exact (@lem7929899 A Z (term23 A Z _103802')). Qed.
Lemma lem7929901 {A Z : Type'} (_103802' : type41 A Z) : (term22 A Z _103802') = (term24 A Z _103802').
Proof. exact (eq_refl (term22 A Z _103802')). Qed.
Lemma lem7929902 {A Z : Type'} (_103802' : type41 A Z) : term24 A Z _103802'.
Proof. exact (EQ_MP (@lem7929901 A Z _103802') (@lem7929900 A Z _103802')). Qed.
Lemma lem7929903 {A Z : Type'} (_103802' : type41 A Z) (fn : type1328 A Z) (h1 : term25 A Z _103802' fn) : term25 A Z _103802' fn.
Proof. exact (h1). Qed.
Lemma lem7929904 {A Z : Type'} (c : nat) (_103802' : type41 A Z) (fn : type1328 A Z) (h1 : term25 A Z _103802' fn) : term26 A Z _103802' fn c.
Proof. exact (@lem7929903 A Z _103802' fn h1 c). Qed.
Lemma lem7929905 {A Z : Type'} (_103802' : type41 A Z) (c : nat) (fn : type1328 A Z) : (term26 A Z _103802' fn c) = (term27 A Z _103802' c fn).
Proof. exact (eq_refl (term26 A Z _103802' fn c)). Qed.
Lemma lem7929906 {A Z : Type'} (c : nat) (_103802' : type41 A Z) (fn : type1328 A Z) (h1 : term25 A Z _103802' fn) : term27 A Z _103802' c fn.
Proof. exact (EQ_MP (@lem7929905 A Z _103802' c fn) (@lem7929904 A Z c _103802' fn h1)). Qed.
Lemma lem7929907 {A Z : Type'} (c : nat) (i : type6 A) (_103802' : type41 A Z) (fn : type1328 A Z) (h1 : term25 A Z _103802' fn) : term28 A Z _103802' c fn i.
Proof. exact (@lem7929906 A Z c _103802' fn h1 i). Qed.
Lemma lem7929908 {A Z : Type'} (_103802' : type41 A Z) (c : nat) (i : type6 A) (fn : type1328 A Z) : (term28 A Z _103802' c fn i) = (term29 A Z _103802' c i fn).
Proof. exact (eq_refl (term28 A Z _103802' c fn i)). Qed.
Lemma lem7929909 {A Z : Type'} (c : nat) (i : type6 A) (_103802' : type41 A Z) (fn : type1328 A Z) (h1 : term25 A Z _103802' fn) : term29 A Z _103802' c i fn.
Proof. exact (EQ_MP (@lem7929908 A Z _103802' c i fn) (@lem7929907 A Z c i _103802' fn h1)). Qed.
Lemma lem7929910 {A Z : Type'} (c : nat) (i : type6 A) (r : type1610 A) (_103802' : type41 A Z) (fn : type1328 A Z) (h1 : term25 A Z _103802' fn) : term30 A Z _103802' c i fn r.
Proof. exact (@lem7929909 A Z c i _103802' fn h1 r). Qed.
Lemma lem7929911 {A Z : Type'} (_103802' : type41 A Z) (c : nat) (i : type6 A) (fn : type1328 A Z) (r : type1610 A) : (term30 A Z _103802' c i fn r) = ((term31 A Z fn c i r) = (term32 A Z _103802' c i fn r)).
Proof. exact (eq_refl (term30 A Z _103802' c i fn r)). Qed.
Lemma lem7929957 {A Z : Type'} (c : nat) (i : type6 A) (r : type1610 A) (_103802' : type41 A Z) (fn : type1328 A Z) (h1 : term25 A Z _103802' fn) : (term31 A Z fn c i r) = (term32 A Z _103802' c i fn r).
Proof. exact (EQ_MP (@lem7929911 A Z _103802' c i fn r) (@lem7929910 A Z c i r _103802' fn h1)). Qed.
Lemma lem7929958 {A Z : Type'} (c : nat) (i : type6 A) (r : type1610 A) (_103802' : type41 A Z) (fn : type1328 A Z) (h1 : term25 A Z _103802' fn) : (term31 A Z fn c i r) = (term32 A Z _103802' c i fn r).
Proof. exact (@lem7929957 A Z c i r _103802' fn h1). Qed.
Lemma lem7929959 {A Z : Type'} (a : type6 A) (_103802' : type41 A Z) (fn : type1328 A Z) (h1 : term25 A Z _103802' fn) : (term14 A Z fn a) = (term33 A Z _103802' a fn).
Proof. exact (@lem7929958 A Z (NUMERAL 0) a (term34 A) _103802' fn h1). Qed.
Lemma lem7929960 {A Z : Type'} (a : type6 A) (_103802' : type41 A Z) (fn : type1350 A Z) (fn' : type1328 A Z) (h1 : term25 A Z _103802' fn') (h2 : fn = (term0 A Z fn')) : (term2 A Z fn a) = (term33 A Z _103802' a fn').
Proof. exact (TRANS (@lem7929897 A Z a fn fn' h2) (@lem7929959 A Z a _103802' fn' h1)). Qed.
Lemma lem7929962 {A : Type'} (f : nat -> A) (a : A) : (term35 A a f) = a.
Proof. exact (EQ_MP (@lem1066569 A f a) (@lem1066568 A a f)). Qed.
Lemma lem7929963 {A Z : Type'} (f : type1561 A Z) (a : type38 A Z) : (term36 A Z a f) = a.
Proof. exact (@lem7929962 (type38 A Z) f a). Qed.
Lemma lem7929966 {A Z : Type'} (_103802' : type41 A Z) : (term37 A Z _103802') = (term38 A Z _103802').
Proof. exact (@lem7929963 A Z (@FNIL ((finite_sum (finite_sum A A) unit) -> (nat -> recspace (finite_sum (finite_sum A A) unit)) -> (nat -> Z) -> Z)) (term38 A Z _103802')). Qed.
Lemma lem7929967 {A : Type'} (a : type6 A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem7929968 {A Z : Type'} (_103802' : type41 A Z) (a : type6 A) : (term39 A Z _103802' a) = (term40 A Z _103802' a).
Proof. exact (MK_COMB (@lem7929966 A Z _103802') (@lem7929967 A a)). Qed.
Lemma lem7929969 {A : Type'} : (term34 A) = (term34 A).
Proof. exact (eq_refl (term34 A)). Qed.
Lemma lem7929970 {A Z : Type'} (_103802' : type41 A Z) (a : type6 A) : (term41 A Z _103802' a) = (term42 A Z _103802' a).
Proof. exact (MK_COMB (@lem7929968 A Z _103802' a) (@lem7929969 A)). Qed.
Lemma lem7929971 {A Z : Type'} (fn : type1328 A Z) : (term43 A Z fn) = (term43 A Z fn).
Proof. exact (eq_refl (term43 A Z fn)). Qed.
Lemma lem7929972 {A Z : Type'} (_103802' : type41 A Z) (a : type6 A) (fn : type1328 A Z) : (term33 A Z _103802' a fn) = (term44 A Z _103802' a fn).
Proof. exact (MK_COMB (@lem7929970 A Z _103802' a) (@lem7929971 A Z fn)). Qed.
Lemma lem7929973 {A Z : Type'} (a : type6 A) (_103802' : type41 A Z) (fn : type1350 A Z) (fn' : type1328 A Z) (h1 : term25 A Z _103802' fn') (h2 : fn = (term0 A Z fn')) : (term2 A Z fn a) = (term44 A Z _103802' a fn').
Proof. exact (TRANS (@lem7929960 A Z a _103802' fn fn' h1 h2) (@lem7929972 A Z _103802' a fn')). Qed.
Lemma lem7929974 {A Z : Type'} (_103802' : type41 A Z) (a : type6 A) : (term40 A Z _103802' a) = (term45 A Z _103802' a).
Proof. exact (eq_refl (term40 A Z _103802' a)). Qed.
Lemma lem7929975 {A : Type'} : (term34 A) = (term34 A).
Proof. exact (eq_refl (term34 A)). Qed.
Lemma lem7929976 {A Z : Type'} (_103802' : type41 A Z) (a : type6 A) : (term42 A Z _103802' a) = (term46 A Z _103802' a).
Proof. exact (MK_COMB (@lem7929974 A Z _103802' a) (@lem7929975 A)). Qed.
Lemma lem7929977 {A Z : Type'} (fn : type1328 A Z) : (term43 A Z fn) = (term43 A Z fn).
Proof. exact (eq_refl (term43 A Z fn)). Qed.
Lemma lem7929978 {A Z : Type'} (_103802' : type41 A Z) (a : type6 A) (fn : type1328 A Z) : (term44 A Z _103802' a fn) = (term47 A Z _103802' a fn).
Proof. exact (MK_COMB (@lem7929976 A Z _103802' a) (@lem7929977 A Z fn)). Qed.
Lemma lem7929979 {A Z : Type'} (a : type6 A) (_103802' : type41 A Z) (fn : type1350 A Z) (fn' : type1328 A Z) (h1 : term25 A Z _103802' fn') (h2 : fn = (term0 A Z fn')) : (term2 A Z fn a) = (term47 A Z _103802' a fn').
Proof. exact (TRANS (@lem7929973 A Z a _103802' fn fn' h1 h2) (@lem7929978 A Z _103802' a fn')). Qed.
Lemma lem7929980 {A Z : Type'} (_103802' : type41 A Z) (a : type6 A) : (term46 A Z _103802' a) = (term48 A Z _103802' a).
Proof. exact (eq_refl (term46 A Z _103802' a)). Qed.
Lemma lem7929981 {A Z : Type'} (fn : type1328 A Z) : (term43 A Z fn) = (term43 A Z fn).
Proof. exact (eq_refl (term43 A Z fn)). Qed.
Lemma lem7929982 {A Z : Type'} (_103802' : type41 A Z) (a : type6 A) (fn : type1328 A Z) : (term47 A Z _103802' a fn) = (term49 A Z _103802' a fn).
Proof. exact (MK_COMB (@lem7929980 A Z _103802' a) (@lem7929981 A Z fn)). Qed.
Lemma lem7929983 {A Z : Type'} (a : type6 A) (_103802' : type41 A Z) (fn : type1350 A Z) (fn' : type1328 A Z) (h1 : term25 A Z _103802' fn') (h2 : fn = (term0 A Z fn')) : (term2 A Z fn a) = (term49 A Z _103802' a fn').
Proof. exact (TRANS (@lem7929979 A Z a _103802' fn fn' h1 h2) (@lem7929982 A Z _103802' a fn')). Qed.
Lemma lem7929984 {A Z : Type'} (fn : type1328 A Z) (_103802' : type41 A Z) (a : type6 A) : (term49 A Z _103802' a fn) = (_103802' a).
Proof. exact (eq_refl (term49 A Z _103802' a fn)). Qed.
Lemma lem7929987 {A Z : Type'} (a : type6 A) (_103802' : type41 A Z) (fn : type1350 A Z) (fn' : type1328 A Z) (h1 : term25 A Z _103802' fn') (h2 : fn = (term0 A Z fn')) : (term2 A Z fn a) = (_103802' a).
Proof. exact (TRANS (@lem7929983 A Z a _103802' fn fn' h1 h2) (@lem7929984 A Z fn' _103802' a)). Qed.
Lemma lem7929988 {A Z : Type'} (_103802' : type41 A Z) (fn : type1350 A Z) (fn' : type1328 A Z) (h1 : term25 A Z _103802' fn') (h2 : fn = (term0 A Z fn')) : term50 A Z fn _103802'.
Proof. exact (fun a : type6 A => @lem7929987 A Z a _103802' fn fn' h1 h2). Qed.
Lemma lem7929989 {A Z : Type'} (fn : type1350 A Z) (_103802' : type41 A Z) : (term51 A Z _103802' fn) = (term50 A Z fn _103802').
Proof. exact (eq_refl (term51 A Z _103802' fn)). Qed.
Lemma lem7929990 {A Z : Type'} : term52 A Z.
Proof. exact (@lem9102 (type1350 A Z)). Qed.
Lemma lem7929991 {A Z : Type'} (_103802' : type41 A Z) : term53 A Z _103802'.
Proof. exact (@lem7929990 A Z (term54 A Z _103802')). Qed.
Lemma lem7929992 {A Z : Type'} (_103802' : type41 A Z) : (term53 A Z _103802') = (term55 A Z _103802').
Proof. exact (eq_refl (term53 A Z _103802')). Qed.
Lemma lem7929993 {A Z : Type'} (_103802' : type41 A Z) : term55 A Z _103802'.
Proof. exact (EQ_MP (@lem7929992 A Z _103802') (@lem7929991 A Z _103802')). Qed.
Lemma lem7929994 {A Z : Type'} (_103802' : type41 A Z) (fn : type1328 A Z) : term56 A Z _103802' fn.
Proof. exact (@lem7929993 A Z _103802' (term0 A Z fn)). Qed.
Lemma lem7929995 {A Z : Type'} (fn : type1328 A Z) (_103802' : type41 A Z) : (term56 A Z _103802' fn) = (term57 A Z fn _103802').
Proof. exact (eq_refl (term56 A Z _103802' fn)). Qed.
Lemma lem7929996 {A Z : Type'} (fn : type1328 A Z) (_103802' : type41 A Z) : term57 A Z fn _103802'.
Proof. exact (EQ_MP (@lem7929995 A Z fn _103802') (@lem7929994 A Z _103802' fn)). Qed.
Lemma lem7929997 {A Z : Type'} (_103802' : type41 A Z) (fn : type1350 A Z) : (term50 A Z fn _103802') = (term51 A Z _103802' fn).
Proof. exact (SYM (@lem7929989 A Z fn _103802')). Qed.
Lemma lem7929998 {A Z : Type'} (_103802' : type41 A Z) (fn : type1350 A Z) (fn' : type1328 A Z) (h1 : term25 A Z _103802' fn') (h2 : fn = (term0 A Z fn')) : term51 A Z _103802' fn.
Proof. exact (EQ_MP (@lem7929997 A Z _103802' fn) (@lem7929988 A Z _103802' fn fn' h1 h2)). Qed.
Lemma lem7929999 {A Z : Type'} (fn : type1350 A Z) (_103802' : type41 A Z) (fn' : type1328 A Z) (h1 : term25 A Z _103802' fn') : term58 A Z fn' _103802' fn.
Proof. exact (fun h0 : fn = (term0 A Z fn') => @lem7929998 A Z _103802' fn fn' h1 h0). Qed.
Lemma lem7930000 {A Z : Type'} (_103802' : type41 A Z) (fn : type1328 A Z) (h1 : term25 A Z _103802' fn) : term59 A Z fn _103802'.
Proof. exact (fun fn' : type1350 A Z => @lem7929999 A Z fn' _103802' fn h1). Qed.
Lemma lem7930001 {A Z : Type'} (_103802' : type41 A Z) (fn : type1328 A Z) (h1 : term25 A Z _103802' fn) : term60 A Z _103802'.
Proof. exact (@lem7929996 A Z fn _103802' (@lem7930000 A Z _103802' fn h1)). Qed.
Lemma lem7930002 {A Z : Type'} (_103802' : type41 A Z) : term60 A Z _103802'.
Proof. exact (ex_elim (@lem7929902 A Z _103802') (fun fn : type1328 A Z => fun h0 : term61 A Z _103802' fn => @lem7930001 A Z _103802' fn h0)). Qed.
Lemma lem7930003 {A Z : Type'} : term62 A Z.
Proof. exact (fun _103802' : type41 A Z => @lem7930002 A Z _103802'). Qed.
