Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7932353_term_abbrevs.
Require Import thm9102_spec.
Require Import tybit1_INDUCT_spec.
Lemma lem7932319 {A : Type'} (P : type1351 A) : term0 A P.
Proof. exact (@lem7931309 A P). Qed.
Lemma lem7932320 {A : Type'} (P : type1351 A) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem7932321 {A : Type'} (P : type1351 A) : term1 A P.
Proof. exact (EQ_MP (@lem7932320 A P) (@lem7932319 A P)). Qed.
Lemma lem7932322 {A : Type'} : term2 A.
Proof. exact (@lem7932321 A (term3 A)). Qed.
Lemma lem7932323 {A : Type'} (a : type6 A) : (term4 A a) = (term5 A a).
Proof. exact (eq_refl (term4 A a)). Qed.
Lemma lem7932324 {A : Type'} : (term6 A) = (term7 A).
Proof. exact (fun_ext (fun a : type6 A => @lem7932323 A a)). Qed.
Lemma lem7932325 {A : Type'} : (@all (finite_sum (finite_sum A A) unit)) = (@all (finite_sum (finite_sum A A) unit)).
Proof. exact (eq_refl (@all (finite_sum (finite_sum A A) unit))). Qed.
Lemma lem7932326 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (MK_COMB (@lem7932325 A) (@lem7932324 A)). Qed.
Lemma lem7932327 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7932328 {A : Type'} : (term10 A) = (term11 A).
Proof. exact (MK_COMB (@lem7932327) (@lem7932326 A)). Qed.
Lemma lem7932329 {A : Type'} (x : tybit1 A) : (term12 A x) = (term13 A x).
Proof. exact (eq_refl (term12 A x)). Qed.
Lemma lem7932330 {A : Type'} : (term14 A) = (term3 A).
Proof. exact (fun_ext (fun x : tybit1 A => @lem7932329 A x)). Qed.
Lemma lem7932331 {A : Type'} : (@all (tybit1 A)) = (@all (tybit1 A)).
Proof. exact (eq_refl (@all (tybit1 A))). Qed.
Lemma lem7932332 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (MK_COMB (@lem7932331 A) (@lem7932330 A)). Qed.
Lemma lem7932333 {A : Type'} : (term2 A) = (term17 A).
Proof. exact (MK_COMB (@lem7932328 A) (@lem7932332 A)). Qed.
Lemma lem7932334 {A : Type'} : term17 A.
Proof. exact (EQ_MP (@lem7932333 A) (@lem7932322 A)). Qed.
Lemma lem7932335 {A : Type'} (a' : type6 A) (a : type6 A) (h1 : a' = a) : a' = a.
Proof. exact (h1). Qed.
Lemma lem7932336 {A : Type'} : (@mktybit1 A) = (@mktybit1 A).
Proof. exact (eq_refl (@mktybit1 A)). Qed.
Lemma lem7932337 {A : Type'} (a' : type6 A) (a : type6 A) (h1 : a' = a) : (@mktybit1 A a') = (@mktybit1 A a).
Proof. exact (MK_COMB (@lem7932336 A) (@lem7932335 A a' a h1)). Qed.
Lemma lem7932338 {A : Type'} (a' : type6 A) (a : type6 A) (h1 : a' = a) : (@mktybit1 A a) = (@mktybit1 A a').
Proof. exact (SYM (@lem7932337 A a' a h1)). Qed.
Lemma lem7932339 {A : Type'} (a : type6 A) (a' : type6 A) : (term18 A a a') = ((@mktybit1 A a) = (@mktybit1 A a')).
Proof. exact (eq_refl (term18 A a a')). Qed.
Lemma lem7932340 {A : Type'} : term19 A.
Proof. exact (@lem9102 (type6 A)). Qed.
Lemma lem7932341 {A : Type'} (a : type6 A) : term20 A a.
Proof. exact (@lem7932340 A (term21 A a)). Qed.
Lemma lem7932342 {A : Type'} (a : type6 A) : (term20 A a) = (term22 A a).
Proof. exact (eq_refl (term20 A a)). Qed.
Lemma lem7932343 {A : Type'} (a : type6 A) : term22 A a.
Proof. exact (EQ_MP (@lem7932342 A a) (@lem7932341 A a)). Qed.
Lemma lem7932344 {A : Type'} (a : type6 A) : term23 A a.
Proof. exact (@lem7932343 A a a). Qed.
Lemma lem7932345 {A : Type'} (a : type6 A) : (term23 A a) = (term24 A a).
Proof. exact (eq_refl (term23 A a)). Qed.
Lemma lem7932346 {A : Type'} (a : type6 A) : term24 A a.
Proof. exact (EQ_MP (@lem7932345 A a) (@lem7932344 A a)). Qed.
Lemma lem7932347 {A : Type'} (a : type6 A) (a' : type6 A) : ((@mktybit1 A a) = (@mktybit1 A a')) = (term18 A a a').
Proof. exact (SYM (@lem7932339 A a a')). Qed.
Lemma lem7932348 {A : Type'} (a' : type6 A) (a : type6 A) (h1 : a' = a) : term18 A a a'.
Proof. exact (EQ_MP (@lem7932347 A a a') (@lem7932338 A a' a h1)). Qed.
Lemma lem7932349 {A : Type'} (a : type6 A) (a' : type6 A) : term25 A a a'.
Proof. exact (fun h0 : a' = a => @lem7932348 A a' a h0). Qed.
Lemma lem7932350 {A : Type'} (a : type6 A) : term26 A a.
Proof. exact (fun a' : type6 A => @lem7932349 A a a'). Qed.
Lemma lem7932351 {A : Type'} (a : type6 A) : term5 A a.
Proof. exact (@lem7932346 A a (@lem7932350 A a)). Qed.
Lemma lem7932352 {A : Type'} : term9 A.
Proof. exact (fun a : type6 A => @lem7932351 A a). Qed.
Lemma lem7932353 {A : Type'} : term16 A.
Proof. exact (@lem7932334 A (@lem7932352 A)). Qed.
