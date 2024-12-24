Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_DIV_1_term_abbrevs.
Require Import REAL_MUL_RID_spec.
Require Import real_div_spec.
Require Import thm0_spec.
Require Import thm1592014_spec.
Require Import thm1592030_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1592922 (x : real) : term0 x.
Proof. exact (@lem1383409 x). Qed.
Lemma lem1592923 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1592925 (x : real) : term2 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1592926 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1592927 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem1592926 x) (@lem1592925 x)). Qed.
Lemma lem1592928 (x : real) (y : real) : term4 x y.
Proof. exact (@lem1592927 x y). Qed.
Lemma lem1592929 (x : real) (y : real) : (term4 x y) = ((real_div x y) = (term5 x y)).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1592938 (x : real) (y : real) : (real_div x y) = (term5 x y).
Proof. exact (EQ_MP (@lem1592929 x y) (@lem1592928 x y)). Qed.
Lemma lem1592939 (x : real) : (term6 x) = (term7 x).
Proof. exact (@lem1592938 x term8). Qed.
Lemma lem1592941 : term9 = term8.
Proof. exact (@lem1592014 (@lem1592030)). Qed.
Lemma lem1592942 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1592943 (x : real) : (term7 x) = (term1 x).
Proof. exact (MK_COMB (@lem1592942 x) (@lem1592941)). Qed.
Lemma lem1592945 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem1592923 x) (@lem1592922 x)). Qed.
Lemma lem1592946 (x : real) : (term7 x) = x.
Proof. exact (TRANS (@lem1592943 x) (@lem1592945 x)). Qed.
Lemma lem1592947 (x : real) : (term6 x) = x.
Proof. exact (TRANS (@lem1592939 x) (@lem1592946 x)). Qed.
Lemma lem1592948 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1592949 (x : real) : (term10 x) = (@eq real x).
Proof. exact (MK_COMB (@lem1592948) (@lem1592947 x)). Qed.
Lemma lem1592950 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1592951 (x : real) : ((term6 x) = x) = (x = x).
Proof. exact (MK_COMB (@lem1592949 x) (@lem1592950 x)). Qed.
Lemma lem1592953 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1592954 (x : real) : (x = x) = True.
Proof. exact (@lem1592953 real x). Qed.
Lemma lem1592955 (x : real) : ((term6 x) = x) = True.
Proof. exact (TRANS (@lem1592951 x) (@lem1592954 x)). Qed.
Lemma lem1592956 : term11 = term12.
Proof. exact (fun_ext (fun x : real => @lem1592955 x)). Qed.
Lemma lem1592957 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1592958 : term13 = term14.
Proof. exact (MK_COMB (@lem1592957) (@lem1592956)). Qed.
Lemma lem1592960 {A : Type'} (t : Prop) : (term15 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1592961 (t : Prop) : (term16 t) = t.
Proof. exact (@lem1592960 real t). Qed.
Lemma lem1592962 : term14 = True.
Proof. exact (@lem1592961 True). Qed.
Lemma lem1592963 : term13 = True.
Proof. exact (TRANS (@lem1592958) (@lem1592962)). Qed.
Lemma lem1592964 : True = term13.
Proof. exact (SYM (@lem1592963)). Qed.
Lemma lem1592965 : term13.
Proof. exact (EQ_MP (@lem1592964) (@lem0)). Qed.
