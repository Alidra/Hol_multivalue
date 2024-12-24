Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SHRINK_EQ_term_abbrevs.
Require Import REAL_SHRINK_LE_spec.
Require Import thm0_spec.
Require Import thm1339379_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem2227299 (x : real) (y : real) (h1 : (term0 y x) = (x = y)) : (term0 y x) = (x = y).
Proof. exact (h1). Qed.
Lemma lem2227300 (x : real) (y : real) (h1 : (term0 y x) = (x = y)) : (x = y) = (term0 y x).
Proof. exact (SYM (@lem2227299 x y h1)). Qed.
Lemma lem2227301 (y : real) (x : real) (h1 : (x = y) = (term0 y x)) : (x = y) = (term0 y x).
Proof. exact (h1). Qed.
Lemma lem2227302 (y : real) (x : real) (h1 : (x = y) = (term0 y x)) : (term0 y x) = (x = y).
Proof. exact (SYM (@lem2227301 y x h1)). Qed.
Lemma lem2227303 (y : real) (x : real) : ((term0 y x) = (x = y)) = ((x = y) = (term0 y x)).
Proof. exact (prop_ext (fun h1 : (term0 y x) = (x = y) => @lem2227300 x y h1) (fun h1 : (x = y) = (term0 y x) => @lem2227302 y x h1)). Qed.
Lemma lem2227304 (x : real) : (term1 x) = (term2 x).
Proof. exact (fun_ext (fun y : real => @lem2227303 y x)). Qed.
Lemma lem2227305 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2227306 (x : real) : (term3 x) = (term4 x).
Proof. exact (MK_COMB (@lem2227305) (@lem2227304 x)). Qed.
Lemma lem2227307 : term5 = term6.
Proof. exact (fun_ext (fun x : real => @lem2227306 x)). Qed.
Lemma lem2227308 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2227309 : term7 = term8.
Proof. exact (MK_COMB (@lem2227308) (@lem2227307)). Qed.
Lemma lem2227310 : term8.
Proof. exact (EQ_MP (@lem2227309) (@lem1339379)). Qed.
Lemma lem2227311 (x : real) : term9 x.
Proof. exact (@lem2227296 x). Qed.
Lemma lem2227312 (x : real) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem2227313 (x : real) : term10 x.
Proof. exact (EQ_MP (@lem2227312 x) (@lem2227311 x)). Qed.
Lemma lem2227314 (x : real) (y : real) : term11 x y.
Proof. exact (@lem2227313 x y). Qed.
Lemma lem2227315 (x : real) (y : real) : (term11 x y) = ((term12 x y) = (real_le x y)).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem2227317 (x : real) : term13 x.
Proof. exact (@lem2227310 x). Qed.
Lemma lem2227318 (x : real) : (term13 x) = (term4 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem2227319 (x : real) : term4 x.
Proof. exact (EQ_MP (@lem2227318 x) (@lem2227317 x)). Qed.
Lemma lem2227320 (x : real) (y : real) : term14 x y.
Proof. exact (@lem2227319 x y). Qed.
Lemma lem2227321 (y : real) (x : real) : (term14 x y) = ((x = y) = (term0 y x)).
Proof. exact (eq_refl (term14 x y)). Qed.
Lemma lem2227338 (y : real) (x : real) : (x = y) = (term0 y x).
Proof. exact (EQ_MP (@lem2227321 y x) (@lem2227320 x y)). Qed.
Lemma lem2227339 (y : real) (x : real) : ((term15 x) = (term15 y)) = (term16 y x).
Proof. exact (@lem2227338 (term15 y) (term15 x)). Qed.
Lemma lem2227343 (x : real) (y : real) : (term12 x y) = (real_le x y).
Proof. exact (EQ_MP (@lem2227315 x y) (@lem2227314 x y)). Qed.
Lemma lem2227344 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2227345 (x : real) (y : real) : (term17 x y) = (term18 x y).
Proof. exact (MK_COMB (@lem2227344) (@lem2227343 x y)). Qed.
Lemma lem2227347 (x : real) (y : real) : (term12 x y) = (real_le x y).
Proof. exact (EQ_MP (@lem2227315 x y) (@lem2227314 x y)). Qed.
Lemma lem2227348 (y : real) (x : real) : (term12 y x) = (real_le y x).
Proof. exact (@lem2227347 y x). Qed.
Lemma lem2227349 (y : real) (x : real) : (term16 y x) = (term0 y x).
Proof. exact (MK_COMB (@lem2227345 x y) (@lem2227348 y x)). Qed.
Lemma lem2227352 (y : real) (x : real) : ((term15 x) = (term15 y)) = (term0 y x).
Proof. exact (TRANS (@lem2227339 y x) (@lem2227349 y x)). Qed.
Lemma lem2227353 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2227354 (y : real) (x : real) : (term19 x y) = (term20 y x).
Proof. exact (MK_COMB (@lem2227353) (@lem2227352 y x)). Qed.
Lemma lem2227358 (y : real) (x : real) : (x = y) = (term0 y x).
Proof. exact (EQ_MP (@lem2227321 y x) (@lem2227320 x y)). Qed.
Lemma lem2227361 (y : real) (x : real) : (((term15 x) = (term15 y)) = (x = y)) = ((term0 y x) = (term0 y x)).
Proof. exact (MK_COMB (@lem2227354 y x) (@lem2227358 y x)). Qed.
Lemma lem2227363 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2227364 (x : Prop) : (x = x) = True.
Proof. exact (@lem2227363 Prop x). Qed.
Lemma lem2227365 (y : real) (x : real) : ((term0 y x) = (term0 y x)) = True.
Proof. exact (@lem2227364 (term0 y x)). Qed.
Lemma lem2227366 (x : real) (y : real) : (((term15 x) = (term15 y)) = (x = y)) = True.
Proof. exact (TRANS (@lem2227361 y x) (@lem2227365 y x)). Qed.
Lemma lem2227367 (x : real) : (term21 x) = term22.
Proof. exact (fun_ext (fun y : real => @lem2227366 x y)). Qed.
Lemma lem2227368 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2227369 (x : real) : (term23 x) = term24.
Proof. exact (MK_COMB (@lem2227368) (@lem2227367 x)). Qed.
Lemma lem2227371 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2227372 (t : Prop) : (term26 t) = t.
Proof. exact (@lem2227371 real t). Qed.
Lemma lem2227373 : term24 = True.
Proof. exact (@lem2227372 True). Qed.
Lemma lem2227374 (x : real) : (term23 x) = True.
Proof. exact (TRANS (@lem2227369 x) (@lem2227373)). Qed.
Lemma lem2227375 : term27 = term22.
Proof. exact (fun_ext (fun x : real => @lem2227374 x)). Qed.
Lemma lem2227376 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2227377 : term28 = term24.
Proof. exact (MK_COMB (@lem2227376) (@lem2227375)). Qed.
Lemma lem2227379 {A : Type'} (t : Prop) : (term25 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2227380 (t : Prop) : (term26 t) = t.
Proof. exact (@lem2227379 real t). Qed.
Lemma lem2227381 : term24 = True.
Proof. exact (@lem2227380 True). Qed.
Lemma lem2227382 : term28 = True.
Proof. exact (TRANS (@lem2227377) (@lem2227381)). Qed.
Lemma lem2227383 : True = term28.
Proof. exact (SYM (@lem2227382)). Qed.
Lemma lem2227384 : term28.
Proof. exact (EQ_MP (@lem2227383) (@lem0)). Qed.
