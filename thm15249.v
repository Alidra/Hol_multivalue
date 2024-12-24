Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm15249_term_abbrevs.
Require Import thm12653_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem15227 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem15228 {_2982 : Type'} (x : _2982) : (x = x) = True.
Proof. exact (@lem15227 _2982 x). Qed.
Lemma lem15229 {_2975 : Type'} : (@COND _2975) = (@COND _2975).
Proof. exact (eq_refl (@COND _2975)). Qed.
Lemma lem15230 {_2975 _2982 : Type'} (x : _2982) : (term0 _2975 _2982 x) = (@COND _2975 True).
Proof. exact (MK_COMB (@lem15229 _2975) (@lem15228 _2982 x)). Qed.
Lemma lem15231 {_2975 : Type'} (y : _2975) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem15232 {_2975 _2982 : Type'} (x : _2982) (y : _2975) : (term1 _2975 _2982 x y) = (@COND _2975 True y).
Proof. exact (MK_COMB (@lem15230 _2975 _2982 x) (@lem15231 _2975 y)). Qed.
Lemma lem15233 {_2975 : Type'} (z : _2975) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem15234 {_2975 _2982 : Type'} (x : _2982) (y : _2975) (z : _2975) : (term2 _2975 _2982 x y z) = (@COND _2975 True y z).
Proof. exact (MK_COMB (@lem15232 _2975 _2982 x y) (@lem15233 _2975 z)). Qed.
Lemma lem15236 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem15237 {_2975 : Type'} (t2 : _2975) (t1 : _2975) : (@COND _2975 True t1 t2) = t1.
Proof. exact (@lem15236 _2975 t2 t1). Qed.
Lemma lem15238 {_2975 : Type'} (z : _2975) (y : _2975) : (@COND _2975 True y z) = y.
Proof. exact (@lem15237 _2975 z y). Qed.
Lemma lem15239 {_2975 _2982 : Type'} (x : _2982) (z : _2975) (y : _2975) : (term2 _2975 _2982 x y z) = y.
Proof. exact (TRANS (@lem15234 _2975 _2982 x y z) (@lem15238 _2975 z y)). Qed.
Lemma lem15240 {_2975 : Type'} : (@eq _2975) = (@eq _2975).
Proof. exact (eq_refl (@eq _2975)). Qed.
Lemma lem15241 {_2975 _2982 : Type'} (x : _2982) (z : _2975) (y : _2975) : (term3 _2975 _2982 x y z) = (@eq _2975 y).
Proof. exact (MK_COMB (@lem15240 _2975) (@lem15239 _2975 _2982 x z y)). Qed.
Lemma lem15242 {_2975 : Type'} (y : _2975) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem15243 {_2975 _2982 : Type'} (x : _2982) (z : _2975) (y : _2975) : ((term2 _2975 _2982 x y z) = y) = (y = y).
Proof. exact (MK_COMB (@lem15241 _2975 _2982 x z y) (@lem15242 _2975 y)). Qed.
Lemma lem15245 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem15246 {_2975 : Type'} (x : _2975) : (x = x) = True.
Proof. exact (@lem15245 _2975 x). Qed.
Lemma lem15247 {_2975 : Type'} (y : _2975) : (y = y) = True.
Proof. exact (@lem15246 _2975 y). Qed.
Lemma lem15248 {_2975 _2982 : Type'} (x : _2982) (z : _2975) (y : _2975) : ((term2 _2975 _2982 x y z) = y) = True.
Proof. exact (TRANS (@lem15243 _2975 _2982 x z y) (@lem15247 _2975 y)). Qed.
Lemma lem15249 {_2975 _2982 : Type'} (x : _2982) (z : _2975) (y : _2975) : True = ((term2 _2975 _2982 x y z) = y).
Proof. exact (SYM (@lem15248 _2975 _2982 x z y)). Qed.
