Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CURRY_DEF_term_abbrevs.
Lemma lem48308 {A B C : Type'} : (@CURRY A B C) = (term0 A B C).
Proof. exact (@CURRY_def A B C). Qed.
Lemma lem48309 {A B C : Type'} (_1283 : type1209 A B C) : _1283 = _1283.
Proof. exact (eq_refl _1283). Qed.
Lemma lem48310 {A B C : Type'} (_1283 : type1209 A B C) : (@CURRY A B C _1283) = (term1 A B C _1283).
Proof. exact (MK_COMB (@lem48308 A B C) (@lem48309 A B C _1283)). Qed.
Lemma lem48311 {A B C : Type'} (_1283 : type1209 A B C) : (term1 A B C _1283) = (term2 A B C _1283).
Proof. exact (eq_refl (term1 A B C _1283)). Qed.
Lemma lem48312 {A B C : Type'} (_1283 : type1209 A B C) : (@CURRY A B C _1283) = (term2 A B C _1283).
Proof. exact (TRANS (@lem48310 A B C _1283) (@lem48311 A B C _1283)). Qed.
Lemma lem48313 {A : Type'} (_1284 : A) : _1284 = _1284.
Proof. exact (eq_refl _1284). Qed.
Lemma lem48314 {A B C : Type'} (_1283 : type1209 A B C) (_1284 : A) : (@CURRY A B C _1283 _1284) = (term3 A B C _1283 _1284).
Proof. exact (MK_COMB (@lem48312 A B C _1283) (@lem48313 A _1284)). Qed.
Lemma lem48315 {A B C : Type'} (_1283 : type1209 A B C) (_1284 : A) : (term3 A B C _1283 _1284) = (term4 A B C _1283 _1284).
Proof. exact (eq_refl (term3 A B C _1283 _1284)). Qed.
Lemma lem48316 {A B C : Type'} (_1283 : type1209 A B C) (_1284 : A) : (@CURRY A B C _1283 _1284) = (term4 A B C _1283 _1284).
Proof. exact (TRANS (@lem48314 A B C _1283 _1284) (@lem48315 A B C _1283 _1284)). Qed.
Lemma lem48317 {B : Type'} (_1285 : B) : _1285 = _1285.
Proof. exact (eq_refl _1285). Qed.
Lemma lem48318 {A B C : Type'} (_1283 : type1209 A B C) (_1284 : A) (_1285 : B) : (@CURRY A B C _1283 _1284 _1285) = (term5 A B C _1283 _1284 _1285).
Proof. exact (MK_COMB (@lem48316 A B C _1283 _1284) (@lem48317 B _1285)). Qed.
Lemma lem48319 {A B C : Type'} (_1283 : type1209 A B C) (_1284 : A) (_1285 : B) : (term5 A B C _1283 _1284 _1285) = (term6 A B C _1283 _1284 _1285).
Proof. exact (eq_refl (term5 A B C _1283 _1284 _1285)). Qed.
Lemma lem48320 {A B C : Type'} (_1283 : type1209 A B C) (_1284 : A) (_1285 : B) : (@CURRY A B C _1283 _1284 _1285) = (term6 A B C _1283 _1284 _1285).
Proof. exact (TRANS (@lem48318 A B C _1283 _1284 _1285) (@lem48319 A B C _1283 _1284 _1285)). Qed.
Lemma lem48321 {A B C : Type'} (_1283 : type1209 A B C) (_1284 : A) : term7 A B C _1283 _1284.
Proof. exact (fun _1285 : B => @lem48320 A B C _1283 _1284 _1285). Qed.
Lemma lem48322 {A B C : Type'} (_1283 : type1209 A B C) : term8 A B C _1283.
Proof. exact (fun _1284 : A => @lem48321 A B C _1283 _1284). Qed.
Lemma lem48323 {A B C : Type'} : term9 A B C.
Proof. exact (fun _1283 : type1209 A B C => @lem48322 A B C _1283). Qed.
Lemma lem48324 {A B C : Type'} (_1283 : type1209 A B C) : term10 A B C _1283.
Proof. exact (@lem48323 A B C _1283). Qed.
Lemma lem48325 {A B C : Type'} (_1283 : type1209 A B C) : (term10 A B C _1283) = (term8 A B C _1283).
Proof. exact (eq_refl (term10 A B C _1283)). Qed.
Lemma lem48326 {A B C : Type'} (_1283 : type1209 A B C) : term8 A B C _1283.
Proof. exact (EQ_MP (@lem48325 A B C _1283) (@lem48324 A B C _1283)). Qed.
Lemma lem48327 {A B C : Type'} (_1283 : type1209 A B C) (_1284 : A) : term11 A B C _1283 _1284.
Proof. exact (@lem48326 A B C _1283 _1284). Qed.
Lemma lem48328 {A B C : Type'} (_1283 : type1209 A B C) (_1284 : A) : (term11 A B C _1283 _1284) = (term7 A B C _1283 _1284).
Proof. exact (eq_refl (term11 A B C _1283 _1284)). Qed.
Lemma lem48329 {A B C : Type'} (_1283 : type1209 A B C) (_1284 : A) : term7 A B C _1283 _1284.
Proof. exact (EQ_MP (@lem48328 A B C _1283 _1284) (@lem48327 A B C _1283 _1284)). Qed.
Lemma lem48330 {A B C : Type'} (_1283 : type1209 A B C) (_1284 : A) (_1285 : B) : term12 A B C _1283 _1284 _1285.
Proof. exact (@lem48329 A B C _1283 _1284 _1285). Qed.
Lemma lem48331 {A B C : Type'} (_1283 : type1209 A B C) (_1284 : A) (_1285 : B) : (term12 A B C _1283 _1284 _1285) = ((@CURRY A B C _1283 _1284 _1285) = (term6 A B C _1283 _1284 _1285)).
Proof. exact (eq_refl (term12 A B C _1283 _1284 _1285)). Qed.
Lemma lem48332 {A B C : Type'} (_1283 : type1209 A B C) (_1284 : A) (_1285 : B) : (@CURRY A B C _1283 _1284 _1285) = (term6 A B C _1283 _1284 _1285).
Proof. exact (EQ_MP (@lem48331 A B C _1283 _1284 _1285) (@lem48330 A B C _1283 _1284 _1285)). Qed.
Lemma lem48388 {A B C : Type'} (f : type1209 A B C) (x : A) (y : B) : (@CURRY A B C f x y) = (term6 A B C f x y).
Proof. exact (@lem48332 A B C f x y). Qed.
Lemma lem48389 {A B C : Type'} (f : type1209 A B C) (x : A) : term7 A B C f x.
Proof. exact (fun y : B => @lem48388 A B C f x y). Qed.
Lemma lem48390 {A B C : Type'} (f : type1209 A B C) : term8 A B C f.
Proof. exact (fun x : A => @lem48389 A B C f x). Qed.
Lemma lem48391 {A B C : Type'} : term9 A B C.
Proof. exact (fun f : type1209 A B C => @lem48390 A B C f). Qed.
