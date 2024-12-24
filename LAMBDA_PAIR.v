Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LAMBDA_PAIR_term_abbrevs.
Require Import LAMBDA_PAIR_THM_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm48213_spec.
Require Import thm48214_spec.
Require Import thm48219_spec.
Require Import thm48220_spec.
Lemma lem51292 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : term0 _5146 _5153 _5154 t.
Proof. exact (@lem51291 _5146 _5153 _5154 t). Qed.
Lemma lem51293 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : (term0 _5146 _5153 _5154 t) = ((term1 _5146 _5153 _5154 t) = (term2 _5146 _5153 _5154 t)).
Proof. exact (eq_refl (term0 _5146 _5153 _5154 t)). Qed.
Lemma lem51318 {_5146 _5153 _5154 : Type'} (t : type1228 _5146 _5153 _5154) : (term1 _5146 _5153 _5154 t) = (term2 _5146 _5153 _5154 t).
Proof. exact (EQ_MP (@lem51293 _5146 _5153 _5154 t) (@lem51292 _5146 _5153 _5154 t)). Qed.
Lemma lem51319 {A B C : Type'} (t : type1209 A B C) : (term3 A B C t) = (term4 A B C t).
Proof. exact (@lem51318 C B A t). Qed.
Lemma lem51320 {A B C : Type'} (f : type1412 A B C) : (term5 A B C f) = (term6 A B C f).
Proof. exact (@lem51319 A B C (term7 A B C f)). Qed.
Lemma lem51321 {A B C : Type'} (f : type1412 A B C) (p : prod A B) : (term8 A B C f p) = (term9 A B C f p).
Proof. exact (eq_refl (term8 A B C f p)). Qed.
Lemma lem51322 {A B C : Type'} (f : type1412 A B C) : (term5 A B C f) = (term7 A B C f).
Proof. exact (fun_ext (fun p : prod A B => @lem51321 A B C f p)). Qed.
Lemma lem51323 {A B C : Type'} : (@eq ((prod A B) -> C)) = (@eq ((prod A B) -> C)).
Proof. exact (eq_refl (@eq ((prod A B) -> C))). Qed.
Lemma lem51324 {A B C : Type'} (f : type1412 A B C) : (term10 A B C f) = (term11 A B C f).
Proof. exact (MK_COMB (@lem51323 A B C) (@lem51322 A B C f)). Qed.
Lemma lem51325 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term12 A B C f x y) = (term13 A B C f x y).
Proof. exact (eq_refl (term12 A B C f x y)). Qed.
Lemma lem51326 {A B C : Type'} (f : type1209 A B C) (x : A) (y : B) : (term14 A B C f x y) = (term14 A B C f x y).
Proof. exact (eq_refl (term14 A B C f x y)). Qed.
Lemma lem51327 {A B C : Type'} (f : type1209 A B C) (f' : type1412 A B C) (x : A) (y : B) : (term15 A B C f f' x y) = (term16 A B C f f' x y).
Proof. exact (MK_COMB (@lem51326 A B C f x y) (@lem51325 A B C f' x y)). Qed.
Lemma lem51328 {A B C : Type'} (f : type1209 A B C) (f' : type1412 A B C) (x : A) : (term17 A B C f f' x) = (term18 A B C f f' x).
Proof. exact (fun_ext (fun y : B => @lem51327 A B C f f' x y)). Qed.
Lemma lem51329 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem51330 {A B C : Type'} (f : type1209 A B C) (f' : type1412 A B C) (x : A) : (term19 A B C f f' x) = (term20 A B C f f' x).
Proof. exact (MK_COMB (@lem51329 B) (@lem51328 A B C f f' x)). Qed.
Lemma lem51331 {A B C : Type'} (f : type1209 A B C) (f' : type1412 A B C) : (term21 A B C f f') = (term22 A B C f f').
Proof. exact (fun_ext (fun x : A => @lem51330 A B C f f' x)). Qed.
Lemma lem51332 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem51333 {A B C : Type'} (f : type1209 A B C) (f' : type1412 A B C) : (term23 A B C f f') = (term24 A B C f f').
Proof. exact (MK_COMB (@lem51332 A) (@lem51331 A B C f f')). Qed.
Lemma lem51334 {A B C : Type'} (f : type1412 A B C) : (term25 A B C f) = (term26 A B C f).
Proof. exact (fun_ext (fun f' : type1209 A B C => @lem51333 A B C f' f)). Qed.
Lemma lem51335 {A B C : Type'} : (@GABS ((prod A B) -> C)) = (@GABS ((prod A B) -> C)).
Proof. exact (eq_refl (@GABS ((prod A B) -> C))). Qed.
Lemma lem51336 {A B C : Type'} (f : type1412 A B C) : (term6 A B C f) = (term27 A B C f).
Proof. exact (MK_COMB (@lem51335 A B C) (@lem51334 A B C f)). Qed.
Lemma lem51337 {A B C : Type'} (f : type1412 A B C) : ((term5 A B C f) = (term6 A B C f)) = ((term7 A B C f) = (term27 A B C f)).
Proof. exact (MK_COMB (@lem51324 A B C f) (@lem51336 A B C f)). Qed.
Lemma lem51338 {A B C : Type'} (f : type1412 A B C) : (term7 A B C f) = (term27 A B C f).
Proof. exact (EQ_MP (@lem51337 A B C f) (@lem51320 A B C f)). Qed.
Lemma lem51354 {A B : Type'} (y : B) (x : A) : (term28 A B x y) = x.
Proof. exact (EQ_MP (@lem48220 A B y x) (@lem48219 A B x y)). Qed.
Lemma lem51355 {A B : Type'} (y : B) (x : A) : (term28 A B x y) = x.
Proof. exact (@lem51354 A B y x). Qed.
Lemma lem51356 {A B C : Type'} (f : type1412 A B C) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem51357 {A B C : Type'} (y : B) (f : type1412 A B C) (x : A) : (term29 A B C f x y) = (f x).
Proof. exact (MK_COMB (@lem51356 A B C f) (@lem51355 A B y x)). Qed.
Lemma lem51359 {A B : Type'} (x : A) (y : B) : (term30 A B x y) = y.
Proof. exact (EQ_MP (@lem48214 A B x y) (@lem48213 A B x y)). Qed.
Lemma lem51360 {A B : Type'} (x : A) (y : B) : (term30 A B x y) = y.
Proof. exact (@lem51359 A B x y). Qed.
Lemma lem51361 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term13 A B C f x y) = (f x y).
Proof. exact (MK_COMB (@lem51357 A B C y f x) (@lem51360 A B x y)). Qed.
Lemma lem51362 {A B C : Type'} (f : type1209 A B C) (x : A) (y : B) : (term14 A B C f x y) = (term14 A B C f x y).
Proof. exact (eq_refl (term14 A B C f x y)). Qed.
Lemma lem51363 {A B C : Type'} (f : type1209 A B C) (f' : type1412 A B C) (x : A) (y : B) : (term16 A B C f f' x y) = (term31 A B C f f' x y).
Proof. exact (MK_COMB (@lem51362 A B C f x y) (@lem51361 A B C f' x y)). Qed.
Lemma lem51364 {A B C : Type'} (f : type1209 A B C) (f' : type1412 A B C) (x : A) : (term18 A B C f f' x) = (term32 A B C f f' x).
Proof. exact (fun_ext (fun y : B => @lem51363 A B C f f' x y)). Qed.
Lemma lem51367 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem51368 {A B C : Type'} (f : type1209 A B C) (f' : type1412 A B C) (x : A) : (term20 A B C f f' x) = (term33 A B C f f' x).
Proof. exact (MK_COMB (@lem51367 B) (@lem51364 A B C f f' x)). Qed.
Lemma lem51373 {A B C : Type'} (f : type1209 A B C) (f' : type1412 A B C) : (term22 A B C f f') = (term34 A B C f f').
Proof. exact (fun_ext (fun x : A => @lem51368 A B C f f' x)). Qed.
Lemma lem51376 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem51377 {A B C : Type'} (f : type1209 A B C) (f' : type1412 A B C) : (term24 A B C f f') = (term35 A B C f f').
Proof. exact (MK_COMB (@lem51376 A) (@lem51373 A B C f f')). Qed.
Lemma lem51382 {A B C : Type'} (f : type1412 A B C) : (term26 A B C f) = (term36 A B C f).
Proof. exact (fun_ext (fun f' : type1209 A B C => @lem51377 A B C f' f)). Qed.
Lemma lem51385 {A B C : Type'} : (@GABS ((prod A B) -> C)) = (@GABS ((prod A B) -> C)).
Proof. exact (eq_refl (@GABS ((prod A B) -> C))). Qed.
Lemma lem51386 {A B C : Type'} (f : type1412 A B C) : (term27 A B C f) = (term37 A B C f).
Proof. exact (MK_COMB (@lem51385 A B C) (@lem51382 A B C f)). Qed.
Lemma lem51387 {A B C : Type'} (f : type1412 A B C) : (term7 A B C f) = (term37 A B C f).
Proof. exact (TRANS (@lem51338 A B C f) (@lem51386 A B C f)). Qed.
Lemma lem51388 {A B C : Type'} (f : type1412 A B C) : (term38 A B C f) = (term38 A B C f).
Proof. exact (eq_refl (term38 A B C f)). Qed.
Lemma lem51389 {A B C : Type'} (f : type1412 A B C) : ((term37 A B C f) = (term7 A B C f)) = ((term37 A B C f) = (term37 A B C f)).
Proof. exact (MK_COMB (@lem51388 A B C f) (@lem51387 A B C f)). Qed.
Lemma lem51391 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem51392 {A B C : Type'} (x : type1209 A B C) : (x = x) = True.
Proof. exact (@lem51391 (type1209 A B C) x). Qed.
Lemma lem51393 {A B C : Type'} (f : type1412 A B C) : ((term37 A B C f) = (term37 A B C f)) = True.
Proof. exact (@lem51392 A B C (term37 A B C f)). Qed.
Lemma lem51394 {A B C : Type'} (f : type1412 A B C) : ((term37 A B C f) = (term7 A B C f)) = True.
Proof. exact (TRANS (@lem51389 A B C f) (@lem51393 A B C f)). Qed.
Lemma lem51395 {A B C : Type'} : (term39 A B C) = (term40 A B C).
Proof. exact (fun_ext (fun f : type1412 A B C => @lem51394 A B C f)). Qed.
Lemma lem51398 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem51399 {A B C : Type'} : (term41 A B C) = (term42 A B C).
Proof. exact (MK_COMB (@lem51398 A B C) (@lem51395 A B C)). Qed.
Lemma lem51401 {A : Type'} (t : Prop) : (term43 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem51402 {A B C : Type'} (t : Prop) : (term44 A B C t) = t.
Proof. exact (@lem51401 (type1412 A B C) t). Qed.
Lemma lem51403 {A B C : Type'} : (term42 A B C) = True.
Proof. exact (@lem51402 A B C True). Qed.
Lemma lem51404 {A B C : Type'} : (term41 A B C) = True.
Proof. exact (TRANS (@lem51399 A B C) (@lem51403 A B C)). Qed.
Lemma lem51405 {A B C : Type'} : True = (term41 A B C).
Proof. exact (SYM (@lem51404 A B C)). Qed.
Lemma lem51406 {A B C : Type'} : term41 A B C.
Proof. exact (EQ_MP (@lem51405 A B C) (@lem0)). Qed.
