Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_1_term_abbrevs.
Require Import REAL_MUL_RID_spec.
Require Import thm0_spec.
Require Import thm1005477_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1344313_spec.
Require Import thm1344314_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm912739_spec.
Lemma lem1630934 (x : real) : term0 x.
Proof. exact (@lem1383409 x). Qed.
Lemma lem1630935 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1630937 (x : real) : term2 x.
Proof. exact (EQ_MP (@lem1344314 x) (@lem1344313 x)). Qed.
Lemma lem1630938 (x : real) (n : nat) : term3 x n.
Proof. exact (@lem1630937 x n). Qed.
Lemma lem1630939 (x : real) (n : nat) : (term3 x n) = ((term4 x n) = (term5 x n)).
Proof. exact (eq_refl (term3 x n)). Qed.
Lemma lem1630942 : term6 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1630943 : (term6 = (BIT1 0)) = (term7 = term8).
Proof. exact (@lem1005477 0 (BIT1 0)). Qed.
Lemma lem1630944 : term7 = term8.
Proof. exact (EQ_MP (@lem1630943) (@lem1630942)). Qed.
Lemma lem1630953 : term8 = term7.
Proof. exact (SYM (@lem1630944)). Qed.
Lemma lem1630954 (x : real) : (real_pow x) = (real_pow x).
Proof. exact (eq_refl (real_pow x)). Qed.
Lemma lem1630955 (x : real) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem1630954 x) (@lem1630953)). Qed.
Lemma lem1630956 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1630957 (x : real) : (term11 x) = (term12 x).
Proof. exact (MK_COMB (@lem1630956) (@lem1630955 x)). Qed.
Lemma lem1630958 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1630959 (x : real) : ((term9 x) = x) = ((term10 x) = x).
Proof. exact (MK_COMB (@lem1630957 x) (@lem1630958 x)). Qed.
Lemma lem1630962 : term13 = term14.
Proof. exact (fun_ext (fun x : real => @lem1630959 x)). Qed.
Lemma lem1630963 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1630964 : term15 = term16.
Proof. exact (MK_COMB (@lem1630963) (@lem1630962)). Qed.
Lemma lem1630969 : term16 = term15.
Proof. exact (SYM (@lem1630964)). Qed.
Lemma lem1630977 (x : real) (n : nat) : (term4 x n) = (term5 x n).
Proof. exact (EQ_MP (@lem1630939 x n) (@lem1630938 x n)). Qed.
Lemma lem1630978 (x : real) : (term10 x) = (term17 x).
Proof. exact (@lem1630977 x (NUMERAL 0)). Qed.
Lemma lem1630980 (x : real) : (term18 x) = term19.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1630981 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1630982 (x : real) : (term17 x) = (term1 x).
Proof. exact (MK_COMB (@lem1630981 x) (@lem1630980 x)). Qed.
Lemma lem1630984 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem1630935 x) (@lem1630934 x)). Qed.
Lemma lem1630985 (x : real) : (term17 x) = x.
Proof. exact (TRANS (@lem1630982 x) (@lem1630984 x)). Qed.
Lemma lem1630986 (x : real) : (term10 x) = x.
Proof. exact (TRANS (@lem1630978 x) (@lem1630985 x)). Qed.
Lemma lem1630987 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1630988 (x : real) : (term12 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1630987) (@lem1630986 x)). Qed.
Lemma lem1630989 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1630990 (x : real) : ((term10 x) = x) = (x = x).
Proof. exact (MK_COMB (@lem1630988 x) (@lem1630989 x)). Qed.
Lemma lem1630992 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1630993 (x : real) : (x = x) = True.
Proof. exact (@lem1630992 real x). Qed.
Lemma lem1630994 (x : real) : ((term10 x) = x) = True.
Proof. exact (TRANS (@lem1630990 x) (@lem1630993 x)). Qed.
Lemma lem1630995 : term14 = term20.
Proof. exact (fun_ext (fun x : real => @lem1630994 x)). Qed.
Lemma lem1630996 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1630997 : term16 = term21.
Proof. exact (MK_COMB (@lem1630996) (@lem1630995)). Qed.
Lemma lem1630999 {A : Type'} (t : Prop) : (term22 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1631000 (t : Prop) : (term23 t) = t.
Proof. exact (@lem1630999 real t). Qed.
Lemma lem1631001 : term21 = True.
Proof. exact (@lem1631000 True). Qed.
Lemma lem1631002 : term16 = True.
Proof. exact (TRANS (@lem1630997) (@lem1631001)). Qed.
Lemma lem1631003 : True = term16.
Proof. exact (SYM (@lem1631002)). Qed.
Lemma lem1631004 : term16.
Proof. exact (EQ_MP (@lem1631003) (@lem0)). Qed.
Lemma lem1631005 : term15.
Proof. exact (EQ_MP (@lem1630969) (@lem1631004)). Qed.
