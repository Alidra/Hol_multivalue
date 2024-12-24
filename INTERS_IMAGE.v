Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTERS_IMAGE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import EXTENSION_spec.
Require Import IN_IMAGE_spec.
Require Import IN_INTERS_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Lemma lem3452303 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3452304 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3452305 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3452304 t1) (@lem3452303 t1)). Qed.
Lemma lem3452306 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3452305 t1 t2). Qed.
Lemma lem3452307 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3452308 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3452307 t1 t2) (@lem3452306 t1 t2)). Qed.
Lemma lem3452309 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3452308 t1 t2 t3). Qed.
Lemma lem3452310 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3452311 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3452310 t1 t2 t3) (@lem3452309 t1 t2 t3)). Qed.
Lemma lem3452312 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3452311 t1 t2 t3)). Qed.
Lemma lem3452337 {_83095 : Type'} : term7 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem3452338 {_83095 : Type'} (p : _83095 -> Prop) : term8 _83095 p.
Proof. exact (@lem3452337 _83095 p). Qed.
Lemma lem3452339 {_83095 : Type'} (p : _83095 -> Prop) : (term8 _83095 p) = (term9 _83095 p).
Proof. exact (eq_refl (term8 _83095 p)). Qed.
Lemma lem3452340 {_83095 : Type'} (p : _83095 -> Prop) : term9 _83095 p.
Proof. exact (EQ_MP (@lem3452339 _83095 p) (@lem3452338 _83095 p)). Qed.
Lemma lem3452341 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term10 _83095 p x.
Proof. exact (@lem3452340 _83095 p x). Qed.
Lemma lem3452342 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term10 _83095 p x) = ((term11 _83095 x p) = (p x)).
Proof. exact (eq_refl (term10 _83095 p x)). Qed.
Lemma lem3452351 {A B : Type'} (y : B) : term12 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem3452352 {A B : Type'} (y : B) : (term12 A B y) = (term13 A B y).
Proof. exact (eq_refl (term12 A B y)). Qed.
Lemma lem3452353 {A B : Type'} (y : B) : term13 A B y.
Proof. exact (EQ_MP (@lem3452352 A B y) (@lem3452351 A B y)). Qed.
Lemma lem3452354 {A B : Type'} (y : B) (s : A -> Prop) : term14 A B y s.
Proof. exact (@lem3452353 A B y s). Qed.
Lemma lem3452355 {A B : Type'} (y : B) (s : A -> Prop) : (term14 A B y s) = (term15 A B y s).
Proof. exact (eq_refl (term14 A B y s)). Qed.
Lemma lem3452356 {A B : Type'} (y : B) (s : A -> Prop) : term15 A B y s.
Proof. exact (EQ_MP (@lem3452355 A B y s) (@lem3452354 A B y s)). Qed.
Lemma lem3452357 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term16 A B y s f.
Proof. exact (@lem3452356 A B y s f). Qed.
Lemma lem3452358 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term16 A B y s f) = ((term17 A B y f s) = (term18 A B y f s)).
Proof. exact (eq_refl (term16 A B y s f)). Qed.
Lemma lem3452360 {A : Type'} (s : type686 A) : term19 A s.
Proof. exact (@lem3205364 A s). Qed.
Lemma lem3452361 {A : Type'} (s : type686 A) : (term19 A s) = (term20 A s).
Proof. exact (eq_refl (term19 A s)). Qed.
Lemma lem3452362 {A : Type'} (s : type686 A) : term20 A s.
Proof. exact (EQ_MP (@lem3452361 A s) (@lem3452360 A s)). Qed.
Lemma lem3452363 {A : Type'} (s : type686 A) (x : A) : term21 A s x.
Proof. exact (@lem3452362 A s x). Qed.
Lemma lem3452364 {A : Type'} (s : type686 A) (x : A) : (term21 A s x) = ((term22 A x s) = (term23 A s x)).
Proof. exact (eq_refl (term21 A s x)). Qed.
Lemma lem3452366 {A : Type'} (s : A -> Prop) : term24 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem3452367 {A : Type'} (s : A -> Prop) : (term24 A s) = (term25 A s).
Proof. exact (eq_refl (term24 A s)). Qed.
Lemma lem3452368 {A : Type'} (s : A -> Prop) : term25 A s.
Proof. exact (EQ_MP (@lem3452367 A s) (@lem3452366 A s)). Qed.
Lemma lem3452369 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term26 A s t.
Proof. exact (@lem3452368 A s t). Qed.
Lemma lem3452370 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term26 A s t) = ((s = t) = (term27 A s t)).
Proof. exact (eq_refl (term26 A s t)). Qed.
Lemma lem3452373 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term27 A s t).
Proof. exact (EQ_MP (@lem3452370 A s t) (@lem3452369 A s t)). Qed.
Lemma lem3452374 {_89465 : Type'} (s : _89465 -> Prop) (t : _89465 -> Prop) : (s = t) = (term27 _89465 s t).
Proof. exact (@lem3452373 _89465 s t). Qed.
Lemma lem3452375 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : ((term28 _89465 _89481 f s) = (term29 _89465 _89481 s f)) = (term30 _89465 _89481 s f).
Proof. exact (@lem3452374 _89465 (term28 _89465 _89481 f s) (term29 _89465 _89481 s f)). Qed.
Lemma lem3452376 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : (term30 _89465 _89481 s f) = ((term28 _89465 _89481 f s) = (term29 _89465 _89481 s f)).
Proof. exact (SYM (@lem3452375 _89465 _89481 s f)). Qed.
Lemma lem3452384 {A : Type'} (s : type686 A) (x : A) : (term22 A x s) = (term23 A s x).
Proof. exact (EQ_MP (@lem3452364 A s x) (@lem3452363 A s x)). Qed.
Lemma lem3452385 {_89465 : Type'} (s : type686 _89465) (x : _89465) : (term22 _89465 x s) = (term23 _89465 s x).
Proof. exact (@lem3452384 _89465 s x). Qed.
Lemma lem3452386 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term31 _89465 _89481 x f s) = (term32 _89465 _89481 f s x).
Proof. exact (@lem3452385 _89465 (@IMAGE _89481 (_89465 -> Prop) f s) x). Qed.
Lemma lem3452394 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term17 A B y f s) = (term18 A B y f s).
Proof. exact (EQ_MP (@lem3452358 A B y f s) (@lem3452357 A B y s f)). Qed.
Lemma lem3452395 {_89465 _89481 : Type'} (y : _89465 -> Prop) (f : type1470 _89465 _89481) (s : _89481 -> Prop) : (term33 _89465 _89481 y f s) = (term34 _89465 _89481 y f s).
Proof. exact (@lem3452394 _89481 (_89465 -> Prop) y f s). Qed.
Lemma lem3452396 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (s : _89481 -> Prop) : (term33 _89465 _89481 t f s) = (term34 _89465 _89481 t f s).
Proof. exact (@lem3452395 _89465 _89481 t f s). Qed.
Lemma lem3452405 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3452406 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (s : _89481 -> Prop) : (term35 _89465 _89481 t f s) = (term36 _89465 _89481 t f s).
Proof. exact (MK_COMB (@lem3452405) (@lem3452396 _89465 _89481 t f s)). Qed.
Lemma lem3452407 {_89465 : Type'} (x : _89465) (t : _89465 -> Prop) : (@IN _89465 x t) = (@IN _89465 x t).
Proof. exact (eq_refl (@IN _89465 x t)). Qed.
Lemma lem3452408 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term37 _89465 _89481 f s x t) = (term38 _89465 _89481 f s x t).
Proof. exact (MK_COMB (@lem3452406 _89465 _89481 t f s) (@lem3452407 _89465 x t)). Qed.
Lemma lem3452411 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term39 _89465 _89481 f s x) = (term40 _89465 _89481 f s x).
Proof. exact (fun_ext (fun t : _89465 -> Prop => @lem3452408 _89465 _89481 f s x t)). Qed.
Lemma lem3452412 {_89465 : Type'} : (@all (_89465 -> Prop)) = (@all (_89465 -> Prop)).
Proof. exact (eq_refl (@all (_89465 -> Prop))). Qed.
Lemma lem3452413 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term32 _89465 _89481 f s x) = (term41 _89465 _89481 f s x).
Proof. exact (MK_COMB (@lem3452412 _89465) (@lem3452411 _89465 _89481 f s x)). Qed.
Lemma lem3452418 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term31 _89465 _89481 x f s) = (term41 _89465 _89481 f s x).
Proof. exact (TRANS (@lem3452386 _89465 _89481 f s x) (@lem3452413 _89465 _89481 f s x)). Qed.
Lemma lem3452419 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3452420 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term42 _89465 _89481 x f s) = (term43 _89465 _89481 f s x).
Proof. exact (MK_COMB (@lem3452419) (@lem3452418 _89465 _89481 f s x)). Qed.
Lemma lem3452422 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term11 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3452342 _83095 p x) (@lem3452341 _83095 p x)). Qed.
Lemma lem3452423 {_89465 : Type'} (p : _89465 -> Prop) (x : _89465) : (term11 _89465 x p) = (p x).
Proof. exact (@lem3452422 _89465 p x). Qed.
Lemma lem3452424 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) (x : _89465) : (term44 _89465 _89481 x s f) = (term45 _89465 _89481 s f x).
Proof. exact (@lem3452423 _89465 (term46 _89465 _89481 s f) x). Qed.
Lemma lem3452425 {_89465 _89481 : Type'} (s : _89481 -> Prop) (y : _89465) (f : type1470 _89465 _89481) : (term45 _89465 _89481 s f y) = (term47 _89465 _89481 s y f).
Proof. exact (eq_refl (term45 _89465 _89481 s f y)). Qed.
Lemma lem3452426 {_89465 : Type'} (GEN_PVAR_48 : _89465) : (@SETSPEC _89465 GEN_PVAR_48) = (@SETSPEC _89465 GEN_PVAR_48).
Proof. exact (eq_refl (@SETSPEC _89465 GEN_PVAR_48)). Qed.
Lemma lem3452427 {_89465 _89481 : Type'} (GEN_PVAR_48 : _89465) (s : _89481 -> Prop) (y : _89465) (f : type1470 _89465 _89481) : (term48 _89465 _89481 GEN_PVAR_48 s f y) = (term49 _89465 _89481 GEN_PVAR_48 s y f).
Proof. exact (MK_COMB (@lem3452426 _89465 GEN_PVAR_48) (@lem3452425 _89465 _89481 s y f)). Qed.
Lemma lem3452428 {_89465 : Type'} (y : _89465) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem3452429 {_89465 _89481 : Type'} (GEN_PVAR_48 : _89465) (s : _89481 -> Prop) (f : type1470 _89465 _89481) (y : _89465) : (term50 _89465 _89481 GEN_PVAR_48 s f y) = (term51 _89465 _89481 GEN_PVAR_48 s f y).
Proof. exact (MK_COMB (@lem3452427 _89465 _89481 GEN_PVAR_48 s y f) (@lem3452428 _89465 y)). Qed.
Lemma lem3452430 {_89465 _89481 : Type'} (GEN_PVAR_48 : _89465) (s : _89481 -> Prop) (f : type1470 _89465 _89481) : (term52 _89465 _89481 GEN_PVAR_48 s f) = (term53 _89465 _89481 GEN_PVAR_48 s f).
Proof. exact (fun_ext (fun y : _89465 => @lem3452429 _89465 _89481 GEN_PVAR_48 s f y)). Qed.
Lemma lem3452431 {_89465 : Type'} : (@ex _89465) = (@ex _89465).
Proof. exact (eq_refl (@ex _89465)). Qed.
Lemma lem3452432 {_89465 _89481 : Type'} (GEN_PVAR_48 : _89465) (s : _89481 -> Prop) (f : type1470 _89465 _89481) : (term54 _89465 _89481 GEN_PVAR_48 s f) = (term55 _89465 _89481 GEN_PVAR_48 s f).
Proof. exact (MK_COMB (@lem3452431 _89465) (@lem3452430 _89465 _89481 GEN_PVAR_48 s f)). Qed.
Lemma lem3452433 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : (term56 _89465 _89481 s f) = (term57 _89465 _89481 s f).
Proof. exact (fun_ext (fun GEN_PVAR_48 : _89465 => @lem3452432 _89465 _89481 GEN_PVAR_48 s f)). Qed.
Lemma lem3452434 {_89465 : Type'} : (@GSPEC _89465) = (@GSPEC _89465).
Proof. exact (eq_refl (@GSPEC _89465)). Qed.
Lemma lem3452435 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : (term58 _89465 _89481 s f) = (term29 _89465 _89481 s f).
Proof. exact (MK_COMB (@lem3452434 _89465) (@lem3452433 _89465 _89481 s f)). Qed.
Lemma lem3452436 {_89465 : Type'} (x : _89465) : (@IN _89465 x) = (@IN _89465 x).
Proof. exact (eq_refl (@IN _89465 x)). Qed.
Lemma lem3452437 {_89465 _89481 : Type'} (x : _89465) (s : _89481 -> Prop) (f : type1470 _89465 _89481) : (term44 _89465 _89481 x s f) = (term59 _89465 _89481 x s f).
Proof. exact (MK_COMB (@lem3452436 _89465 x) (@lem3452435 _89465 _89481 s f)). Qed.
Lemma lem3452438 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3452439 {_89465 _89481 : Type'} (x : _89465) (s : _89481 -> Prop) (f : type1470 _89465 _89481) : (term60 _89465 _89481 x s f) = (term61 _89465 _89481 x s f).
Proof. exact (MK_COMB (@lem3452438) (@lem3452437 _89465 _89481 x s f)). Qed.
Lemma lem3452440 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term45 _89465 _89481 s f x) = (term47 _89465 _89481 s x f).
Proof. exact (eq_refl (term45 _89465 _89481 s f x)). Qed.
Lemma lem3452441 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : ((term44 _89465 _89481 x s f) = (term45 _89465 _89481 s f x)) = ((term59 _89465 _89481 x s f) = (term47 _89465 _89481 s x f)).
Proof. exact (MK_COMB (@lem3452439 _89465 _89481 x s f) (@lem3452440 _89465 _89481 s x f)). Qed.
Lemma lem3452442 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term59 _89465 _89481 x s f) = (term47 _89465 _89481 s x f).
Proof. exact (EQ_MP (@lem3452441 _89465 _89481 s x f) (@lem3452424 _89465 _89481 s f x)). Qed.
Lemma lem3452449 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : ((term31 _89465 _89481 x f s) = (term59 _89465 _89481 x s f)) = ((term41 _89465 _89481 f s x) = (term47 _89465 _89481 s x f)).
Proof. exact (MK_COMB (@lem3452420 _89465 _89481 f s x) (@lem3452442 _89465 _89481 s x f)). Qed.
Lemma lem3452452 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : (term62 _89465 _89481 s f) = (term63 _89465 _89481 s f).
Proof. exact (fun_ext (fun x : _89465 => @lem3452449 _89465 _89481 s x f)). Qed.
Lemma lem3452453 {_89465 : Type'} : (@all _89465) = (@all _89465).
Proof. exact (eq_refl (@all _89465)). Qed.
Lemma lem3452454 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : (term30 _89465 _89481 s f) = (term64 _89465 _89481 s f).
Proof. exact (MK_COMB (@lem3452453 _89465) (@lem3452452 _89465 _89481 s f)). Qed.
Lemma lem3452459 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : (term64 _89465 _89481 s f) = (term30 _89465 _89481 s f).
Proof. exact (SYM (@lem3452454 _89465 _89481 s f)). Qed.
Lemma lem3452461 (p : Prop) : p = (term65 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3452462 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : (term64 _89465 _89481 s f) = (term66 _89465 _89481 s f).
Proof. exact (@lem3452461 (term64 _89465 _89481 s f)). Qed.
Lemma lem3452463 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : (term66 _89465 _89481 s f) = (term64 _89465 _89481 s f).
Proof. exact (SYM (@lem3452462 _89465 _89481 s f)). Qed.
Lemma lem3452464 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) (h1 : term67 _89465 _89481 s f) : term67 _89465 _89481 s f.
Proof. exact (h1). Qed.
Lemma lem3452467 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) (h1 : term66 _89465 _89481 s f) : term66 _89465 _89481 s f.
Proof. exact (h1). Qed.
Lemma lem3452468 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : term68 _89465 _89481 s f.
Proof. exact (fun h0 : term66 _89465 _89481 s f => @lem3452467 _89465 _89481 s f h0). Qed.
Lemma lem3452469 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) (h1 : term68 _89465 _89481 s f) : term68 _89465 _89481 s f.
Proof. exact (h1). Qed.
Lemma lem3452470 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) (h1 : term66 _89465 _89481 s f) : term66 _89465 _89481 s f.
Proof. exact (h1). Qed.
Lemma lem3452471 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) (h1 : term66 _89465 _89481 s f) (h2 : term68 _89465 _89481 s f) : term66 _89465 _89481 s f.
Proof. exact (@lem3452469 _89465 _89481 s f h2 (@lem3452470 _89465 _89481 s f h1)). Qed.
Lemma lem3452472 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) (h1 : term66 _89465 _89481 s f) : term69 _89465 _89481 s f.
Proof. exact (fun h0 : term68 _89465 _89481 s f => @lem3452471 _89465 _89481 s f h1 h0). Qed.
Lemma lem3452473 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) (h1 : term68 _89465 _89481 s f) : term68 _89465 _89481 s f.
Proof. exact (h1). Qed.
Lemma lem3452474 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) (h1 : term66 _89465 _89481 s f) (h2 : term68 _89465 _89481 s f) : term66 _89465 _89481 s f.
Proof. exact (@lem3452472 _89465 _89481 s f h1 (@lem3452473 _89465 _89481 s f h2)). Qed.
Lemma lem3452475 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) (h1 : term68 _89465 _89481 s f) : term68 _89465 _89481 s f.
Proof. exact (fun h0 : term66 _89465 _89481 s f => @lem3452474 _89465 _89481 s f h0 h1). Qed.
Lemma lem3452476 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : term70 _89465 _89481 s f.
Proof. exact (fun h0 : term68 _89465 _89481 s f => @lem3452475 _89465 _89481 s f h0). Qed.
Lemma lem3452479 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : term68 _89465 _89481 s f.
Proof. exact (@lem3452476 _89465 _89481 s f (@lem3452468 _89465 _89481 s f)). Qed.
Lemma lem3452480 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : term68 _89465 _89481 s f.
Proof. exact (@lem3452479 _89465 _89481 s f). Qed.
Lemma lem3452490 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3452491 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : (term66 _89465 _89481 s f) = (term71 _89465 _89481 s f).
Proof. exact (@lem3452490 (term67 _89465 _89481 s f)). Qed.
Lemma lem3452493 (t : Prop) : (term72 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3452494 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : (term71 _89465 _89481 s f) = (term64 _89465 _89481 s f).
Proof. exact (@lem3452493 (term64 _89465 _89481 s f)). Qed.
Lemma lem3452499 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : (term66 _89465 _89481 s f) = (term64 _89465 _89481 s f).
Proof. exact (TRANS (@lem3452491 _89465 _89481 s f) (@lem3452494 _89465 _89481 s f)). Qed.
Lemma lem3452562 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) : (term73 _89465 _89481 f) = (term74 _89465 _89481 f).
Proof. exact (fun_ext (fun s : _89481 -> Prop => @lem3452499 _89465 _89481 s f)). Qed.
Lemma lem3452563 {_89481 : Type'} : (@all (_89481 -> Prop)) = (@all (_89481 -> Prop)).
Proof. exact (eq_refl (@all (_89481 -> Prop))). Qed.
Lemma lem3452564 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) : (term75 _89465 _89481 f) = (term76 _89465 _89481 f).
Proof. exact (MK_COMB (@lem3452563 _89481) (@lem3452562 _89465 _89481 f)). Qed.
Lemma lem3452569 {_89465 _89481 : Type'} : (term77 _89465 _89481) = (term78 _89465 _89481).
Proof. exact (fun_ext (fun f : type1470 _89465 _89481 => @lem3452564 _89465 _89481 f)). Qed.
Lemma lem3452570 {_89465 _89481 : Type'} : (@all (_89481 -> _89465 -> Prop)) = (@all (_89481 -> _89465 -> Prop)).
Proof. exact (eq_refl (@all (_89481 -> _89465 -> Prop))). Qed.
Lemma lem3452579 {_89465 _89481 : Type'} : (term79 _89465 _89481) = (term80 _89465 _89481).
Proof. exact (MK_COMB (@lem3452570 _89465 _89481) (@lem3452569 _89465 _89481)). Qed.
Lemma lem3452584 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) : (term81 _89465 _89481 s x f x') = (term81 _89465 _89481 s x f x').
Proof. exact (eq_refl (term81 _89465 _89481 s x f x')). Qed.
Lemma lem3452585 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term82 _89465 _89481 s x f) = (term82 _89465 _89481 s x f).
Proof. exact (fun_ext (fun x' : _89481 => @lem3452584 _89465 _89481 s x f x')). Qed.
Lemma lem3452586 {_89481 : Type'} : (@all _89481) = (@all _89481).
Proof. exact (eq_refl (@all _89481)). Qed.
Lemma lem3452587 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term47 _89465 _89481 s x f) = (term47 _89465 _89481 s x f).
Proof. exact (MK_COMB (@lem3452586 _89481) (@lem3452585 _89465 _89481 s x f)). Qed.
Lemma lem3452588 {_89465 : Type'} (x : _89465) (t : _89465 -> Prop) : (@IN _89465 x t) = (@IN _89465 x t).
Proof. exact (eq_refl (@IN _89465 x t)). Qed.
Lemma lem3452593 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (x : _89481) (s : _89481 -> Prop) : (term83 _89465 _89481 t f x s) = (term83 _89465 _89481 t f x s).
Proof. exact (eq_refl (term83 _89465 _89481 t f x s)). Qed.
Lemma lem3452594 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (s : _89481 -> Prop) : (term84 _89465 _89481 t f s) = (term84 _89465 _89481 t f s).
Proof. exact (fun_ext (fun x : _89481 => @lem3452593 _89465 _89481 t f x s)). Qed.
Lemma lem3452595 {_89481 : Type'} : (@ex _89481) = (@ex _89481).
Proof. exact (eq_refl (@ex _89481)). Qed.
Lemma lem3452596 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (s : _89481 -> Prop) : (term34 _89465 _89481 t f s) = (term34 _89465 _89481 t f s).
Proof. exact (MK_COMB (@lem3452595 _89481) (@lem3452594 _89465 _89481 t f s)). Qed.
Lemma lem3452597 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3452598 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (s : _89481 -> Prop) : (term36 _89465 _89481 t f s) = (term36 _89465 _89481 t f s).
Proof. exact (MK_COMB (@lem3452597) (@lem3452596 _89465 _89481 t f s)). Qed.
Lemma lem3452599 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term38 _89465 _89481 f s x t) = (term38 _89465 _89481 f s x t).
Proof. exact (MK_COMB (@lem3452598 _89465 _89481 t f s) (@lem3452588 _89465 x t)). Qed.
Lemma lem3452600 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term40 _89465 _89481 f s x) = (term40 _89465 _89481 f s x).
Proof. exact (fun_ext (fun t : _89465 -> Prop => @lem3452599 _89465 _89481 f s x t)). Qed.
Lemma lem3452601 {_89465 : Type'} : (@all (_89465 -> Prop)) = (@all (_89465 -> Prop)).
Proof. exact (eq_refl (@all (_89465 -> Prop))). Qed.
Lemma lem3452602 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term41 _89465 _89481 f s x) = (term41 _89465 _89481 f s x).
Proof. exact (MK_COMB (@lem3452601 _89465) (@lem3452600 _89465 _89481 f s x)). Qed.
Lemma lem3452603 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3452604 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term43 _89465 _89481 f s x) = (term43 _89465 _89481 f s x).
Proof. exact (MK_COMB (@lem3452603) (@lem3452602 _89465 _89481 f s x)). Qed.
Lemma lem3452605 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : ((term41 _89465 _89481 f s x) = (term47 _89465 _89481 s x f)) = ((term41 _89465 _89481 f s x) = (term47 _89465 _89481 s x f)).
Proof. exact (MK_COMB (@lem3452604 _89465 _89481 f s x) (@lem3452587 _89465 _89481 s x f)). Qed.
Lemma lem3452606 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : (term63 _89465 _89481 s f) = (term63 _89465 _89481 s f).
Proof. exact (fun_ext (fun x : _89465 => @lem3452605 _89465 _89481 s x f)). Qed.
Lemma lem3452607 {_89465 : Type'} : (@all _89465) = (@all _89465).
Proof. exact (eq_refl (@all _89465)). Qed.
Lemma lem3452608 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : (term64 _89465 _89481 s f) = (term64 _89465 _89481 s f).
Proof. exact (MK_COMB (@lem3452607 _89465) (@lem3452606 _89465 _89481 s f)). Qed.
Lemma lem3452609 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) : (term74 _89465 _89481 f) = (term74 _89465 _89481 f).
Proof. exact (fun_ext (fun s : _89481 -> Prop => @lem3452608 _89465 _89481 s f)). Qed.
Lemma lem3452610 {_89481 : Type'} : (@all (_89481 -> Prop)) = (@all (_89481 -> Prop)).
Proof. exact (eq_refl (@all (_89481 -> Prop))). Qed.
Lemma lem3452611 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) : (term76 _89465 _89481 f) = (term76 _89465 _89481 f).
Proof. exact (MK_COMB (@lem3452610 _89481) (@lem3452609 _89465 _89481 f)). Qed.
Lemma lem3452612 {_89465 _89481 : Type'} : (term78 _89465 _89481) = (term78 _89465 _89481).
Proof. exact (fun_ext (fun f : type1470 _89465 _89481 => @lem3452611 _89465 _89481 f)). Qed.
Lemma lem3452613 {_89465 _89481 : Type'} : (@all (_89481 -> _89465 -> Prop)) = (@all (_89481 -> _89465 -> Prop)).
Proof. exact (eq_refl (@all (_89481 -> _89465 -> Prop))). Qed.
Lemma lem3452614 {_89465 _89481 : Type'} : (term80 _89465 _89481) = (term80 _89465 _89481).
Proof. exact (MK_COMB (@lem3452613 _89465 _89481) (@lem3452612 _89465 _89481)). Qed.
Lemma lem3452659 {_89465 _89481 : Type'} : (term79 _89465 _89481) = (term80 _89465 _89481).
Proof. exact (TRANS (@lem3452579 _89465 _89481) (@lem3452614 _89465 _89481)). Qed.
Lemma lem3452660 {_89465 _89481 : Type'} : (term80 _89465 _89481) = (term79 _89465 _89481).
Proof. exact (SYM (@lem3452659 _89465 _89481)). Qed.
Lemma lem3452662 (p : Prop) : p = (term65 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3452663 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : ((term41 _89465 _89481 f s x) = (term47 _89465 _89481 s x f)) = (term85 _89465 _89481 s x f).
Proof. exact (@lem3452662 ((term41 _89465 _89481 f s x) = (term47 _89465 _89481 s x f))). Qed.
Lemma lem3452664 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term85 _89465 _89481 s x f) = ((term41 _89465 _89481 f s x) = (term47 _89465 _89481 s x f)).
Proof. exact (SYM (@lem3452663 _89465 _89481 s x f)). Qed.
Lemma lem3452665 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term86 _89465 _89481 s x f) : term86 _89465 _89481 s x f.
Proof. exact (h1). Qed.
Lemma lem3452674 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (x : _89481) (s : _89481 -> Prop) : (term87 _89465 _89481 t f x s) = (term88 _89465 _89481 t f x s).
Proof. exact (@lem17045 (t = (f x)) (@IN _89481 x s)). Qed.
Lemma lem3452677 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (x : _89481) (s : _89481 -> Prop) : (term83 _89465 _89481 t f x s) = (term83 _89465 _89481 t f x s).
Proof. exact (eq_refl (term83 _89465 _89481 t f x s)). Qed.
Lemma lem3452678 {_89481 : Type'} (P : _89481 -> Prop) : (term89 _89481 P) = (term90 _89481 P).
Proof. exact (@lem18394 _89481 P). Qed.
Lemma lem3452679 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (s : _89481 -> Prop) : (term91 _89465 _89481 t f s) = (term92 _89465 _89481 t f s).
Proof. exact (@lem3452678 _89481 (term84 _89465 _89481 t f s)). Qed.
Lemma lem3452680 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (x : _89481) (s : _89481 -> Prop) : (term93 _89465 _89481 t f s x) = (term83 _89465 _89481 t f x s).
Proof. exact (eq_refl (term93 _89465 _89481 t f s x)). Qed.
Lemma lem3452681 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3452682 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (x : _89481) (s : _89481 -> Prop) : (term94 _89465 _89481 t f s x) = (term87 _89465 _89481 t f x s).
Proof. exact (MK_COMB (@lem3452681) (@lem3452680 _89465 _89481 t f x s)). Qed.
Lemma lem3452683 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (x : _89481) (s : _89481 -> Prop) : (term94 _89465 _89481 t f s x) = (term88 _89465 _89481 t f x s).
Proof. exact (TRANS (@lem3452682 _89465 _89481 t f x s) (@lem3452674 _89465 _89481 t f x s)). Qed.
Lemma lem3452684 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (s : _89481 -> Prop) : (term95 _89465 _89481 t f s) = (term96 _89465 _89481 t f s).
Proof. exact (fun_ext (fun x : _89481 => @lem3452683 _89465 _89481 t f x s)). Qed.
Lemma lem3452685 {_89481 : Type'} : (@all _89481) = (@all _89481).
Proof. exact (eq_refl (@all _89481)). Qed.
Lemma lem3452686 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (s : _89481 -> Prop) : (term92 _89465 _89481 t f s) = (term97 _89465 _89481 t f s).
Proof. exact (MK_COMB (@lem3452685 _89481) (@lem3452684 _89465 _89481 t f s)). Qed.
Lemma lem3452687 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (s : _89481 -> Prop) : (term91 _89465 _89481 t f s) = (term97 _89465 _89481 t f s).
Proof. exact (TRANS (@lem3452679 _89465 _89481 t f s) (@lem3452686 _89465 _89481 t f s)). Qed.
Lemma lem3452688 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (s : _89481 -> Prop) : (term84 _89465 _89481 t f s) = (term84 _89465 _89481 t f s).
Proof. exact (fun_ext (fun x : _89481 => @lem3452677 _89465 _89481 t f x s)). Qed.
Lemma lem3452689 {_89481 : Type'} : (@ex _89481) = (@ex _89481).
Proof. exact (eq_refl (@ex _89481)). Qed.
Lemma lem3452690 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (s : _89481 -> Prop) : (term34 _89465 _89481 t f s) = (term34 _89465 _89481 t f s).
Proof. exact (MK_COMB (@lem3452689 _89481) (@lem3452688 _89465 _89481 t f s)). Qed.
Lemma lem3452691 {_89465 : Type'} (x : _89465) (t : _89465 -> Prop) : (term98 _89465 x t) = (term98 _89465 x t).
Proof. exact (eq_refl (term98 _89465 x t)). Qed.
Lemma lem3452692 {_89465 : Type'} (x : _89465) (t : _89465 -> Prop) : (@IN _89465 x t) = (@IN _89465 x t).
Proof. exact (eq_refl (@IN _89465 x t)). Qed.
Lemma lem3452693 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3452694 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (s : _89481 -> Prop) : (term99 _89465 _89481 t f s) = (term99 _89465 _89481 t f s).
Proof. exact (MK_COMB (@lem3452693) (@lem3452690 _89465 _89481 t f s)). Qed.
Lemma lem3452695 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term100 _89465 _89481 f s x t) = (term100 _89465 _89481 f s x t).
Proof. exact (MK_COMB (@lem3452694 _89465 _89481 t f s) (@lem3452691 _89465 x t)). Qed.
Lemma lem3452696 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term101 _89465 _89481 f s x t) = (term100 _89465 _89481 f s x t).
Proof. exact (@lem17362 (term34 _89465 _89481 t f s) (@IN _89465 x t)). Qed.
Lemma lem3452697 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term101 _89465 _89481 f s x t) = (term100 _89465 _89481 f s x t).
Proof. exact (TRANS (@lem3452696 _89465 _89481 f s x t) (@lem3452695 _89465 _89481 f s x t)). Qed.
Lemma lem3452698 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3452699 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (s : _89481 -> Prop) : (term102 _89465 _89481 t f s) = (term103 _89465 _89481 t f s).
Proof. exact (MK_COMB (@lem3452698) (@lem3452687 _89465 _89481 t f s)). Qed.
Lemma lem3452700 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term104 _89465 _89481 f s x t) = (term105 _89465 _89481 f s x t).
Proof. exact (MK_COMB (@lem3452699 _89465 _89481 t f s) (@lem3452692 _89465 x t)). Qed.
Lemma lem3452701 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term38 _89465 _89481 f s x t) = (term104 _89465 _89481 f s x t).
Proof. exact (@lem17265 (term34 _89465 _89481 t f s) (@IN _89465 x t)). Qed.
Lemma lem3452702 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term38 _89465 _89481 f s x t) = (term105 _89465 _89481 f s x t).
Proof. exact (TRANS (@lem3452701 _89465 _89481 f s x t) (@lem3452700 _89465 _89481 f s x t)). Qed.
Lemma lem3452703 {_89465 : Type'} (P : type686 _89465) : (term106 _89465 P) = (term107 _89465 P).
Proof. exact (@lem18392 (_89465 -> Prop) P). Qed.
Lemma lem3452704 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term108 _89465 _89481 f s x) = (term109 _89465 _89481 f s x).
Proof. exact (@lem3452703 _89465 (term40 _89465 _89481 f s x)). Qed.
Lemma lem3452705 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term110 _89465 _89481 f s x t) = (term38 _89465 _89481 f s x t).
Proof. exact (eq_refl (term110 _89465 _89481 f s x t)). Qed.
Lemma lem3452706 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3452707 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term111 _89465 _89481 f s x t) = (term101 _89465 _89481 f s x t).
Proof. exact (MK_COMB (@lem3452706) (@lem3452705 _89465 _89481 f s x t)). Qed.
Lemma lem3452708 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term111 _89465 _89481 f s x t) = (term100 _89465 _89481 f s x t).
Proof. exact (TRANS (@lem3452707 _89465 _89481 f s x t) (@lem3452697 _89465 _89481 f s x t)). Qed.
Lemma lem3452709 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term112 _89465 _89481 f s x) = (term113 _89465 _89481 f s x).
Proof. exact (fun_ext (fun t : _89465 -> Prop => @lem3452708 _89465 _89481 f s x t)). Qed.
Lemma lem3452710 {_89465 : Type'} : (@ex (_89465 -> Prop)) = (@ex (_89465 -> Prop)).
Proof. exact (eq_refl (@ex (_89465 -> Prop))). Qed.
Lemma lem3452711 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term109 _89465 _89481 f s x) = (term114 _89465 _89481 f s x).
Proof. exact (MK_COMB (@lem3452710 _89465) (@lem3452709 _89465 _89481 f s x)). Qed.
Lemma lem3452712 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term108 _89465 _89481 f s x) = (term114 _89465 _89481 f s x).
Proof. exact (TRANS (@lem3452704 _89465 _89481 f s x) (@lem3452711 _89465 _89481 f s x)). Qed.
Lemma lem3452713 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term40 _89465 _89481 f s x) = (term115 _89465 _89481 f s x).
Proof. exact (fun_ext (fun t : _89465 -> Prop => @lem3452702 _89465 _89481 f s x t)). Qed.
Lemma lem3452714 {_89465 : Type'} : (@all (_89465 -> Prop)) = (@all (_89465 -> Prop)).
Proof. exact (eq_refl (@all (_89465 -> Prop))). Qed.
Lemma lem3452715 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term41 _89465 _89481 f s x) = (term116 _89465 _89481 f s x).
Proof. exact (MK_COMB (@lem3452714 _89465) (@lem3452713 _89465 _89481 f s x)). Qed.
Lemma lem3452724 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) : (term117 _89465 _89481 s x f x') = (term118 _89465 _89481 s x f x').
Proof. exact (@lem17362 (@IN _89481 x' s) (term119 _89465 _89481 x f x')). Qed.
Lemma lem3452729 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) : (term81 _89465 _89481 s x f x') = (term120 _89465 _89481 s x f x').
Proof. exact (@lem17265 (@IN _89481 x' s) (term119 _89465 _89481 x f x')). Qed.
Lemma lem3452730 {_89481 : Type'} (P : _89481 -> Prop) : (term121 _89481 P) = (term122 _89481 P).
Proof. exact (@lem18392 _89481 P). Qed.
Lemma lem3452731 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term123 _89465 _89481 s x f) = (term124 _89465 _89481 s x f).
Proof. exact (@lem3452730 _89481 (term82 _89465 _89481 s x f)). Qed.
Lemma lem3452732 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) : (term125 _89465 _89481 s x f x') = (term81 _89465 _89481 s x f x').
Proof. exact (eq_refl (term125 _89465 _89481 s x f x')). Qed.
Lemma lem3452733 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3452734 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) : (term126 _89465 _89481 s x f x') = (term117 _89465 _89481 s x f x').
Proof. exact (MK_COMB (@lem3452733) (@lem3452732 _89465 _89481 s x f x')). Qed.
Lemma lem3452735 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) : (term126 _89465 _89481 s x f x') = (term118 _89465 _89481 s x f x').
Proof. exact (TRANS (@lem3452734 _89465 _89481 s x f x') (@lem3452724 _89465 _89481 s x f x')). Qed.
Lemma lem3452736 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term127 _89465 _89481 s x f) = (term128 _89465 _89481 s x f).
Proof. exact (fun_ext (fun x' : _89481 => @lem3452735 _89465 _89481 s x f x')). Qed.
Lemma lem3452737 {_89481 : Type'} : (@ex _89481) = (@ex _89481).
Proof. exact (eq_refl (@ex _89481)). Qed.
Lemma lem3452738 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term124 _89465 _89481 s x f) = (term129 _89465 _89481 s x f).
Proof. exact (MK_COMB (@lem3452737 _89481) (@lem3452736 _89465 _89481 s x f)). Qed.
Lemma lem3452739 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term123 _89465 _89481 s x f) = (term129 _89465 _89481 s x f).
Proof. exact (TRANS (@lem3452731 _89465 _89481 s x f) (@lem3452738 _89465 _89481 s x f)). Qed.
Lemma lem3452740 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term82 _89465 _89481 s x f) = (term130 _89465 _89481 s x f).
Proof. exact (fun_ext (fun x' : _89481 => @lem3452729 _89465 _89481 s x f x')). Qed.
Lemma lem3452741 {_89481 : Type'} : (@all _89481) = (@all _89481).
Proof. exact (eq_refl (@all _89481)). Qed.
Lemma lem3452742 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term47 _89465 _89481 s x f) = (term131 _89465 _89481 s x f).
Proof. exact (MK_COMB (@lem3452741 _89481) (@lem3452740 _89465 _89481 s x f)). Qed.
Lemma lem3452743 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3452744 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term132 _89465 _89481 f s x) = (term133 _89465 _89481 f s x).
Proof. exact (MK_COMB (@lem3452743) (@lem3452712 _89465 _89481 f s x)). Qed.
Lemma lem3452745 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term134 _89465 _89481 s x f) = (term135 _89465 _89481 s x f).
Proof. exact (MK_COMB (@lem3452744 _89465 _89481 f s x) (@lem3452742 _89465 _89481 s x f)). Qed.
Lemma lem3452746 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3452747 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term136 _89465 _89481 f s x) = (term137 _89465 _89481 f s x).
Proof. exact (MK_COMB (@lem3452746) (@lem3452715 _89465 _89481 f s x)). Qed.
Lemma lem3452748 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term138 _89465 _89481 s x f) = (term139 _89465 _89481 s x f).
Proof. exact (MK_COMB (@lem3452747 _89465 _89481 f s x) (@lem3452739 _89465 _89481 s x f)). Qed.
Lemma lem3452749 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3452750 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term140 _89465 _89481 s x f) = (term141 _89465 _89481 s x f).
Proof. exact (MK_COMB (@lem3452749) (@lem3452748 _89465 _89481 s x f)). Qed.
Lemma lem3452751 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term142 _89465 _89481 s x f) = (term143 _89465 _89481 s x f).
Proof. exact (MK_COMB (@lem3452750 _89465 _89481 s x f) (@lem3452745 _89465 _89481 s x f)). Qed.
Lemma lem3452752 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term86 _89465 _89481 s x f) = (term142 _89465 _89481 s x f).
Proof. exact (@lem17646 (term41 _89465 _89481 f s x) (term47 _89465 _89481 s x f)). Qed.
Lemma lem3452753 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term86 _89465 _89481 s x f) = (term143 _89465 _89481 s x f).
Proof. exact (TRANS (@lem3452752 _89465 _89481 s x f) (@lem3452751 _89465 _89481 s x f)). Qed.
Lemma lem3453044 {A : Type'} (P : Prop) (Q : A -> Prop) : (term144 A P Q) = (term145 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3453045 {_89481 : Type'} (P : Prop) (Q : _89481 -> Prop) : (term144 _89481 P Q) = (term145 _89481 P Q).
Proof. exact (@lem3453044 _89481 P Q). Qed.
Lemma lem3453046 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term146 _89465 _89481 s x f) = (term147 _89465 _89481 s x f).
Proof. exact (@lem3453045 _89481 (term116 _89465 _89481 f s x) (term128 _89465 _89481 s x f)). Qed.
Lemma lem3453047 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) : (term148 _89465 _89481 s x f x') = (term118 _89465 _89481 s x f x').
Proof. exact (eq_refl (term148 _89465 _89481 s x f x')). Qed.
Lemma lem3453048 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term149 _89465 _89481 s x f) = (term128 _89465 _89481 s x f).
Proof. exact (fun_ext (fun x' : _89481 => @lem3453047 _89465 _89481 s x f x')). Qed.
Lemma lem3453049 {_89481 : Type'} : (@ex _89481) = (@ex _89481).
Proof. exact (eq_refl (@ex _89481)). Qed.
Lemma lem3453050 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term150 _89465 _89481 s x f) = (term129 _89465 _89481 s x f).
Proof. exact (MK_COMB (@lem3453049 _89481) (@lem3453048 _89465 _89481 s x f)). Qed.
Lemma lem3453051 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term137 _89465 _89481 f s x) = (term137 _89465 _89481 f s x).
Proof. exact (eq_refl (term137 _89465 _89481 f s x)). Qed.
Lemma lem3453052 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term146 _89465 _89481 s x f) = (term139 _89465 _89481 s x f).
Proof. exact (MK_COMB (@lem3453051 _89465 _89481 f s x) (@lem3453050 _89465 _89481 s x f)). Qed.
Lemma lem3453053 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3453054 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term151 _89465 _89481 s x f) = (term152 _89465 _89481 s x f).
Proof. exact (MK_COMB (@lem3453053) (@lem3453052 _89465 _89481 s x f)). Qed.
Lemma lem3453055 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) : (term148 _89465 _89481 s x f x') = (term118 _89465 _89481 s x f x').
Proof. exact (eq_refl (term148 _89465 _89481 s x f x')). Qed.
Lemma lem3453056 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term137 _89465 _89481 f s x) = (term137 _89465 _89481 f s x).
Proof. exact (eq_refl (term137 _89465 _89481 f s x)). Qed.
Lemma lem3453057 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) : (term153 _89465 _89481 s x f x') = (term154 _89465 _89481 s x f x').
Proof. exact (MK_COMB (@lem3453056 _89465 _89481 f s x) (@lem3453055 _89465 _89481 s x f x')). Qed.
Lemma lem3453058 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term155 _89465 _89481 s x f) = (term156 _89465 _89481 s x f).
Proof. exact (fun_ext (fun x' : _89481 => @lem3453057 _89465 _89481 s x f x')). Qed.
Lemma lem3453059 {_89481 : Type'} : (@ex _89481) = (@ex _89481).
Proof. exact (eq_refl (@ex _89481)). Qed.
Lemma lem3453060 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term147 _89465 _89481 s x f) = (term157 _89465 _89481 s x f).
Proof. exact (MK_COMB (@lem3453059 _89481) (@lem3453058 _89465 _89481 s x f)). Qed.
Lemma lem3453061 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : ((term146 _89465 _89481 s x f) = (term147 _89465 _89481 s x f)) = ((term139 _89465 _89481 s x f) = (term157 _89465 _89481 s x f)).
Proof. exact (MK_COMB (@lem3453054 _89465 _89481 s x f) (@lem3453060 _89465 _89481 s x f)). Qed.
Lemma lem3453062 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term139 _89465 _89481 s x f) = (term157 _89465 _89481 s x f).
Proof. exact (EQ_MP (@lem3453061 _89465 _89481 s x f) (@lem3453046 _89465 _89481 s x f)). Qed.
Lemma lem3453063 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3453064 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term141 _89465 _89481 s x f) = (term158 _89465 _89481 s x f).
Proof. exact (MK_COMB (@lem3453063) (@lem3453062 _89465 _89481 s x f)). Qed.
Lemma lem3453066 {A : Type'} (P : A -> Prop) (Q : Prop) : (term159 A P Q) = (term160 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3453067 {_89481 : Type'} (P : _89481 -> Prop) (Q : Prop) : (term159 _89481 P Q) = (term160 _89481 P Q).
Proof. exact (@lem3453066 _89481 P Q). Qed.
Lemma lem3453068 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term161 _89465 _89481 f s x t) = (term162 _89465 _89481 f s x t).
Proof. exact (@lem3453067 _89481 (term84 _89465 _89481 t f s) (term98 _89465 x t)). Qed.
Lemma lem3453069 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (x : _89481) (s : _89481 -> Prop) : (term93 _89465 _89481 t f s x) = (term83 _89465 _89481 t f x s).
Proof. exact (eq_refl (term93 _89465 _89481 t f s x)). Qed.
Lemma lem3453070 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (s : _89481 -> Prop) : (term163 _89465 _89481 t f s) = (term84 _89465 _89481 t f s).
Proof. exact (fun_ext (fun x : _89481 => @lem3453069 _89465 _89481 t f x s)). Qed.
Lemma lem3453071 {_89481 : Type'} : (@ex _89481) = (@ex _89481).
Proof. exact (eq_refl (@ex _89481)). Qed.
Lemma lem3453072 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (s : _89481 -> Prop) : (term164 _89465 _89481 t f s) = (term34 _89465 _89481 t f s).
Proof. exact (MK_COMB (@lem3453071 _89481) (@lem3453070 _89465 _89481 t f s)). Qed.
Lemma lem3453073 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3453074 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (s : _89481 -> Prop) : (term165 _89465 _89481 t f s) = (term99 _89465 _89481 t f s).
Proof. exact (MK_COMB (@lem3453073) (@lem3453072 _89465 _89481 t f s)). Qed.
Lemma lem3453075 {_89465 : Type'} (x : _89465) (t : _89465 -> Prop) : (term98 _89465 x t) = (term98 _89465 x t).
Proof. exact (eq_refl (term98 _89465 x t)). Qed.
Lemma lem3453076 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term161 _89465 _89481 f s x t) = (term100 _89465 _89481 f s x t).
Proof. exact (MK_COMB (@lem3453074 _89465 _89481 t f s) (@lem3453075 _89465 x t)). Qed.
Lemma lem3453077 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3453078 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term166 _89465 _89481 f s x t) = (term167 _89465 _89481 f s x t).
Proof. exact (MK_COMB (@lem3453077) (@lem3453076 _89465 _89481 f s x t)). Qed.
Lemma lem3453079 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (x : _89481) (s : _89481 -> Prop) : (term93 _89465 _89481 t f s x) = (term83 _89465 _89481 t f x s).
Proof. exact (eq_refl (term93 _89465 _89481 t f s x)). Qed.
Lemma lem3453080 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3453081 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (x : _89481) (s : _89481 -> Prop) : (term168 _89465 _89481 t f s x) = (term169 _89465 _89481 t f x s).
Proof. exact (MK_COMB (@lem3453080) (@lem3453079 _89465 _89481 t f x s)). Qed.
Lemma lem3453082 {_89465 : Type'} (x : _89465) (t : _89465 -> Prop) : (term98 _89465 x t) = (term98 _89465 x t).
Proof. exact (eq_refl (term98 _89465 x t)). Qed.
Lemma lem3453083 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (x : _89481) (s : _89481 -> Prop) (x' : _89465) (t : _89465 -> Prop) : (term170 _89465 _89481 f s x x' t) = (term171 _89465 _89481 f x s x' t).
Proof. exact (MK_COMB (@lem3453081 _89465 _89481 t f x s) (@lem3453082 _89465 x' t)). Qed.
Lemma lem3453084 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term172 _89465 _89481 f s x t) = (term173 _89465 _89481 f s x t).
Proof. exact (fun_ext (fun x' : _89481 => @lem3453083 _89465 _89481 f x' s x t)). Qed.
Lemma lem3453085 {_89481 : Type'} : (@ex _89481) = (@ex _89481).
Proof. exact (eq_refl (@ex _89481)). Qed.
Lemma lem3453086 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term162 _89465 _89481 f s x t) = (term174 _89465 _89481 f s x t).
Proof. exact (MK_COMB (@lem3453085 _89481) (@lem3453084 _89465 _89481 f s x t)). Qed.
Lemma lem3453087 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : ((term161 _89465 _89481 f s x t) = (term162 _89465 _89481 f s x t)) = ((term100 _89465 _89481 f s x t) = (term174 _89465 _89481 f s x t)).
Proof. exact (MK_COMB (@lem3453078 _89465 _89481 f s x t) (@lem3453086 _89465 _89481 f s x t)). Qed.
Lemma lem3453088 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term100 _89465 _89481 f s x t) = (term174 _89465 _89481 f s x t).
Proof. exact (EQ_MP (@lem3453087 _89465 _89481 f s x t) (@lem3453068 _89465 _89481 f s x t)). Qed.
Lemma lem3453089 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term113 _89465 _89481 f s x) = (term175 _89465 _89481 f s x).
Proof. exact (fun_ext (fun t : _89465 -> Prop => @lem3453088 _89465 _89481 f s x t)). Qed.
Lemma lem3453090 {_89465 : Type'} : (@ex (_89465 -> Prop)) = (@ex (_89465 -> Prop)).
Proof. exact (eq_refl (@ex (_89465 -> Prop))). Qed.
Lemma lem3453091 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term114 _89465 _89481 f s x) = (term176 _89465 _89481 f s x).
Proof. exact (MK_COMB (@lem3453090 _89465) (@lem3453089 _89465 _89481 f s x)). Qed.
Lemma lem3453092 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3453093 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term133 _89465 _89481 f s x) = (term177 _89465 _89481 f s x).
Proof. exact (MK_COMB (@lem3453092) (@lem3453091 _89465 _89481 f s x)). Qed.
Lemma lem3453094 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term131 _89465 _89481 s x f) = (term131 _89465 _89481 s x f).
Proof. exact (eq_refl (term131 _89465 _89481 s x f)). Qed.
Lemma lem3453095 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term135 _89465 _89481 s x f) = (term178 _89465 _89481 s x f).
Proof. exact (MK_COMB (@lem3453093 _89465 _89481 f s x) (@lem3453094 _89465 _89481 s x f)). Qed.
Lemma lem3453097 {A : Type'} (P : A -> Prop) (Q : Prop) : (term159 A P Q) = (term160 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3453098 {_89465 : Type'} (P : type686 _89465) (Q : Prop) : (term179 _89465 P Q) = (term180 _89465 P Q).
Proof. exact (@lem3453097 (_89465 -> Prop) P Q). Qed.
Lemma lem3453099 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term181 _89465 _89481 s x f) = (term182 _89465 _89481 s x f).
Proof. exact (@lem3453098 _89465 (term175 _89465 _89481 f s x) (term131 _89465 _89481 s x f)). Qed.
Lemma lem3453100 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term183 _89465 _89481 f s x t) = (term174 _89465 _89481 f s x t).
Proof. exact (eq_refl (term183 _89465 _89481 f s x t)). Qed.
Lemma lem3453101 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term184 _89465 _89481 f s x) = (term175 _89465 _89481 f s x).
Proof. exact (fun_ext (fun t : _89465 -> Prop => @lem3453100 _89465 _89481 f s x t)). Qed.
Lemma lem3453102 {_89465 : Type'} : (@ex (_89465 -> Prop)) = (@ex (_89465 -> Prop)).
Proof. exact (eq_refl (@ex (_89465 -> Prop))). Qed.
Lemma lem3453103 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term185 _89465 _89481 f s x) = (term176 _89465 _89481 f s x).
Proof. exact (MK_COMB (@lem3453102 _89465) (@lem3453101 _89465 _89481 f s x)). Qed.
Lemma lem3453104 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3453105 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term186 _89465 _89481 f s x) = (term177 _89465 _89481 f s x).
Proof. exact (MK_COMB (@lem3453104) (@lem3453103 _89465 _89481 f s x)). Qed.
Lemma lem3453106 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term131 _89465 _89481 s x f) = (term131 _89465 _89481 s x f).
Proof. exact (eq_refl (term131 _89465 _89481 s x f)). Qed.
Lemma lem3453107 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term181 _89465 _89481 s x f) = (term178 _89465 _89481 s x f).
Proof. exact (MK_COMB (@lem3453105 _89465 _89481 f s x) (@lem3453106 _89465 _89481 s x f)). Qed.
Lemma lem3453108 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3453109 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term187 _89465 _89481 s x f) = (term188 _89465 _89481 s x f).
Proof. exact (MK_COMB (@lem3453108) (@lem3453107 _89465 _89481 s x f)). Qed.
Lemma lem3453110 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term183 _89465 _89481 f s x t) = (term174 _89465 _89481 f s x t).
Proof. exact (eq_refl (term183 _89465 _89481 f s x t)). Qed.
Lemma lem3453111 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3453112 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term189 _89465 _89481 f s x t) = (term190 _89465 _89481 f s x t).
Proof. exact (MK_COMB (@lem3453111) (@lem3453110 _89465 _89481 f s x t)). Qed.
Lemma lem3453113 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term131 _89465 _89481 s x f) = (term131 _89465 _89481 s x f).
Proof. exact (eq_refl (term131 _89465 _89481 s x f)). Qed.
Lemma lem3453114 {_89465 _89481 : Type'} (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term191 _89465 _89481 t s x f) = (term192 _89465 _89481 t s x f).
Proof. exact (MK_COMB (@lem3453112 _89465 _89481 f s x t) (@lem3453113 _89465 _89481 s x f)). Qed.
Lemma lem3453115 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term193 _89465 _89481 s x f) = (term194 _89465 _89481 s x f).
Proof. exact (fun_ext (fun t : _89465 -> Prop => @lem3453114 _89465 _89481 t s x f)). Qed.
Lemma lem3453116 {_89465 : Type'} : (@ex (_89465 -> Prop)) = (@ex (_89465 -> Prop)).
Proof. exact (eq_refl (@ex (_89465 -> Prop))). Qed.
Lemma lem3453117 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term182 _89465 _89481 s x f) = (term195 _89465 _89481 s x f).
Proof. exact (MK_COMB (@lem3453116 _89465) (@lem3453115 _89465 _89481 s x f)). Qed.
Lemma lem3453118 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : ((term181 _89465 _89481 s x f) = (term182 _89465 _89481 s x f)) = ((term178 _89465 _89481 s x f) = (term195 _89465 _89481 s x f)).
Proof. exact (MK_COMB (@lem3453109 _89465 _89481 s x f) (@lem3453117 _89465 _89481 s x f)). Qed.
Lemma lem3453119 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term178 _89465 _89481 s x f) = (term195 _89465 _89481 s x f).
Proof. exact (EQ_MP (@lem3453118 _89465 _89481 s x f) (@lem3453099 _89465 _89481 s x f)). Qed.
Lemma lem3453121 {A : Type'} (P : A -> Prop) (Q : Prop) : (term159 A P Q) = (term160 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3453122 {_89481 : Type'} (P : _89481 -> Prop) (Q : Prop) : (term159 _89481 P Q) = (term160 _89481 P Q).
Proof. exact (@lem3453121 _89481 P Q). Qed.
Lemma lem3453123 {_89465 _89481 : Type'} (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term196 _89465 _89481 t s x f) = (term197 _89465 _89481 t s x f).
Proof. exact (@lem3453122 _89481 (term173 _89465 _89481 f s x t) (term131 _89465 _89481 s x f)). Qed.
Lemma lem3453124 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (x : _89481) (s : _89481 -> Prop) (x' : _89465) (t : _89465 -> Prop) : (term198 _89465 _89481 f s x' t x) = (term171 _89465 _89481 f x s x' t).
Proof. exact (eq_refl (term198 _89465 _89481 f s x' t x)). Qed.
Lemma lem3453125 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term199 _89465 _89481 f s x t) = (term173 _89465 _89481 f s x t).
Proof. exact (fun_ext (fun x' : _89481 => @lem3453124 _89465 _89481 f x' s x t)). Qed.
Lemma lem3453126 {_89481 : Type'} : (@ex _89481) = (@ex _89481).
Proof. exact (eq_refl (@ex _89481)). Qed.
Lemma lem3453127 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term200 _89465 _89481 f s x t) = (term174 _89465 _89481 f s x t).
Proof. exact (MK_COMB (@lem3453126 _89481) (@lem3453125 _89465 _89481 f s x t)). Qed.
Lemma lem3453128 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3453129 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term201 _89465 _89481 f s x t) = (term190 _89465 _89481 f s x t).
Proof. exact (MK_COMB (@lem3453128) (@lem3453127 _89465 _89481 f s x t)). Qed.
Lemma lem3453130 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term131 _89465 _89481 s x f) = (term131 _89465 _89481 s x f).
Proof. exact (eq_refl (term131 _89465 _89481 s x f)). Qed.
Lemma lem3453131 {_89465 _89481 : Type'} (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term196 _89465 _89481 t s x f) = (term192 _89465 _89481 t s x f).
Proof. exact (MK_COMB (@lem3453129 _89465 _89481 f s x t) (@lem3453130 _89465 _89481 s x f)). Qed.
Lemma lem3453132 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3453133 {_89465 _89481 : Type'} (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term202 _89465 _89481 t s x f) = (term203 _89465 _89481 t s x f).
Proof. exact (MK_COMB (@lem3453132) (@lem3453131 _89465 _89481 t s x f)). Qed.
Lemma lem3453134 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (x : _89481) (s : _89481 -> Prop) (x' : _89465) (t : _89465 -> Prop) : (term198 _89465 _89481 f s x' t x) = (term171 _89465 _89481 f x s x' t).
Proof. exact (eq_refl (term198 _89465 _89481 f s x' t x)). Qed.
Lemma lem3453135 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3453136 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (x : _89481) (s : _89481 -> Prop) (x' : _89465) (t : _89465 -> Prop) : (term204 _89465 _89481 f s x' t x) = (term205 _89465 _89481 f x s x' t).
Proof. exact (MK_COMB (@lem3453135) (@lem3453134 _89465 _89481 f x s x' t)). Qed.
Lemma lem3453137 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term131 _89465 _89481 s x f) = (term131 _89465 _89481 s x f).
Proof. exact (eq_refl (term131 _89465 _89481 s x f)). Qed.
Lemma lem3453138 {_89465 _89481 : Type'} (x : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x' : _89465) (f : type1470 _89465 _89481) : (term206 _89465 _89481 t x s x' f) = (term207 _89465 _89481 x t s x' f).
Proof. exact (MK_COMB (@lem3453136 _89465 _89481 f x s x' t) (@lem3453137 _89465 _89481 s x' f)). Qed.
Lemma lem3453139 {_89465 _89481 : Type'} (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term208 _89465 _89481 t s x f) = (term209 _89465 _89481 t s x f).
Proof. exact (fun_ext (fun x' : _89481 => @lem3453138 _89465 _89481 x' t s x f)). Qed.
Lemma lem3453140 {_89481 : Type'} : (@ex _89481) = (@ex _89481).
Proof. exact (eq_refl (@ex _89481)). Qed.
Lemma lem3453141 {_89465 _89481 : Type'} (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term197 _89465 _89481 t s x f) = (term210 _89465 _89481 t s x f).
Proof. exact (MK_COMB (@lem3453140 _89481) (@lem3453139 _89465 _89481 t s x f)). Qed.
Lemma lem3453142 {_89465 _89481 : Type'} (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : ((term196 _89465 _89481 t s x f) = (term197 _89465 _89481 t s x f)) = ((term192 _89465 _89481 t s x f) = (term210 _89465 _89481 t s x f)).
Proof. exact (MK_COMB (@lem3453133 _89465 _89481 t s x f) (@lem3453141 _89465 _89481 t s x f)). Qed.
Lemma lem3453143 {_89465 _89481 : Type'} (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term192 _89465 _89481 t s x f) = (term210 _89465 _89481 t s x f).
Proof. exact (EQ_MP (@lem3453142 _89465 _89481 t s x f) (@lem3453123 _89465 _89481 t s x f)). Qed.
Lemma lem3453144 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term194 _89465 _89481 s x f) = (term211 _89465 _89481 s x f).
Proof. exact (fun_ext (fun t : _89465 -> Prop => @lem3453143 _89465 _89481 t s x f)). Qed.
Lemma lem3453145 {_89465 : Type'} : (@ex (_89465 -> Prop)) = (@ex (_89465 -> Prop)).
Proof. exact (eq_refl (@ex (_89465 -> Prop))). Qed.
Lemma lem3453146 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term195 _89465 _89481 s x f) = (term212 _89465 _89481 s x f).
Proof. exact (MK_COMB (@lem3453145 _89465) (@lem3453144 _89465 _89481 s x f)). Qed.
Lemma lem3453147 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term178 _89465 _89481 s x f) = (term212 _89465 _89481 s x f).
Proof. exact (TRANS (@lem3453119 _89465 _89481 s x f) (@lem3453146 _89465 _89481 s x f)). Qed.
Lemma lem3453148 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term135 _89465 _89481 s x f) = (term212 _89465 _89481 s x f).
Proof. exact (TRANS (@lem3453095 _89465 _89481 s x f) (@lem3453147 _89465 _89481 s x f)). Qed.
Lemma lem3453149 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term143 _89465 _89481 s x f) = (term213 _89465 _89481 s x f).
Proof. exact (MK_COMB (@lem3453064 _89465 _89481 s x f) (@lem3453148 _89465 _89481 s x f)). Qed.
Lemma lem3453153 {A : Type'} (P : A -> Prop) (Q : Prop) : (term214 A P Q) = (term215 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3453154 {_89481 : Type'} (P : _89481 -> Prop) (Q : Prop) : (term214 _89481 P Q) = (term215 _89481 P Q).
Proof. exact (@lem3453153 _89481 P Q). Qed.
Lemma lem3453155 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term216 _89465 _89481 s x f) = (term217 _89465 _89481 s x f).
Proof. exact (@lem3453154 _89481 (term156 _89465 _89481 s x f) (term212 _89465 _89481 s x f)). Qed.
Lemma lem3453156 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) : (term218 _89465 _89481 s x f x') = (term154 _89465 _89481 s x f x').
Proof. exact (eq_refl (term218 _89465 _89481 s x f x')). Qed.
Lemma lem3453157 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term219 _89465 _89481 s x f) = (term156 _89465 _89481 s x f).
Proof. exact (fun_ext (fun x' : _89481 => @lem3453156 _89465 _89481 s x f x')). Qed.
Lemma lem3453158 {_89481 : Type'} : (@ex _89481) = (@ex _89481).
Proof. exact (eq_refl (@ex _89481)). Qed.
Lemma lem3453159 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term220 _89465 _89481 s x f) = (term157 _89465 _89481 s x f).
Proof. exact (MK_COMB (@lem3453158 _89481) (@lem3453157 _89465 _89481 s x f)). Qed.
Lemma lem3453160 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3453161 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term221 _89465 _89481 s x f) = (term158 _89465 _89481 s x f).
Proof. exact (MK_COMB (@lem3453160) (@lem3453159 _89465 _89481 s x f)). Qed.
Lemma lem3453162 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term212 _89465 _89481 s x f) = (term212 _89465 _89481 s x f).
Proof. exact (eq_refl (term212 _89465 _89481 s x f)). Qed.
Lemma lem3453163 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term216 _89465 _89481 s x f) = (term213 _89465 _89481 s x f).
Proof. exact (MK_COMB (@lem3453161 _89465 _89481 s x f) (@lem3453162 _89465 _89481 s x f)). Qed.
Lemma lem3453164 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3453165 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term222 _89465 _89481 s x f) = (term223 _89465 _89481 s x f).
Proof. exact (MK_COMB (@lem3453164) (@lem3453163 _89465 _89481 s x f)). Qed.
Lemma lem3453166 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) : (term218 _89465 _89481 s x f x') = (term154 _89465 _89481 s x f x').
Proof. exact (eq_refl (term218 _89465 _89481 s x f x')). Qed.
Lemma lem3453167 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3453168 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) : (term224 _89465 _89481 s x f x') = (term225 _89465 _89481 s x f x').
Proof. exact (MK_COMB (@lem3453167) (@lem3453166 _89465 _89481 s x f x')). Qed.
Lemma lem3453169 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term212 _89465 _89481 s x f) = (term212 _89465 _89481 s x f).
Proof. exact (eq_refl (term212 _89465 _89481 s x f)). Qed.
Lemma lem3453170 {_89465 _89481 : Type'} (x : _89481) (s : _89481 -> Prop) (x' : _89465) (f : type1470 _89465 _89481) : (term226 _89465 _89481 x s x' f) = (term227 _89465 _89481 x s x' f).
Proof. exact (MK_COMB (@lem3453168 _89465 _89481 s x' f x) (@lem3453169 _89465 _89481 s x' f)). Qed.
Lemma lem3453171 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term228 _89465 _89481 s x f) = (term229 _89465 _89481 s x f).
Proof. exact (fun_ext (fun x' : _89481 => @lem3453170 _89465 _89481 x' s x f)). Qed.
Lemma lem3453172 {_89481 : Type'} : (@ex _89481) = (@ex _89481).
Proof. exact (eq_refl (@ex _89481)). Qed.
Lemma lem3453173 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term217 _89465 _89481 s x f) = (term230 _89465 _89481 s x f).
Proof. exact (MK_COMB (@lem3453172 _89481) (@lem3453171 _89465 _89481 s x f)). Qed.
Lemma lem3453174 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : ((term216 _89465 _89481 s x f) = (term217 _89465 _89481 s x f)) = ((term213 _89465 _89481 s x f) = (term230 _89465 _89481 s x f)).
Proof. exact (MK_COMB (@lem3453165 _89465 _89481 s x f) (@lem3453173 _89465 _89481 s x f)). Qed.
Lemma lem3453175 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term213 _89465 _89481 s x f) = (term230 _89465 _89481 s x f).
Proof. exact (EQ_MP (@lem3453174 _89465 _89481 s x f) (@lem3453155 _89465 _89481 s x f)). Qed.
Lemma lem3453177 {A : Type'} (P : Prop) (Q : A -> Prop) : (term231 A P Q) = (term232 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3453178 {_89465 : Type'} (P : Prop) (Q : type686 _89465) : (term233 _89465 P Q) = (term234 _89465 P Q).
Proof. exact (@lem3453177 (_89465 -> Prop) P Q). Qed.
Lemma lem3453179 {_89465 _89481 : Type'} (x : _89481) (s : _89481 -> Prop) (x' : _89465) (f : type1470 _89465 _89481) : (term235 _89465 _89481 x s x' f) = (term236 _89465 _89481 x s x' f).
Proof. exact (@lem3453178 _89465 (term154 _89465 _89481 s x' f x) (term211 _89465 _89481 s x' f)). Qed.
Lemma lem3453180 {_89465 _89481 : Type'} (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term237 _89465 _89481 s x f t) = (term210 _89465 _89481 t s x f).
Proof. exact (eq_refl (term237 _89465 _89481 s x f t)). Qed.
Lemma lem3453181 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term238 _89465 _89481 s x f) = (term211 _89465 _89481 s x f).
Proof. exact (fun_ext (fun t : _89465 -> Prop => @lem3453180 _89465 _89481 t s x f)). Qed.
Lemma lem3453182 {_89465 : Type'} : (@ex (_89465 -> Prop)) = (@ex (_89465 -> Prop)).
Proof. exact (eq_refl (@ex (_89465 -> Prop))). Qed.
Lemma lem3453183 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term239 _89465 _89481 s x f) = (term212 _89465 _89481 s x f).
Proof. exact (MK_COMB (@lem3453182 _89465) (@lem3453181 _89465 _89481 s x f)). Qed.
Lemma lem3453184 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) : (term225 _89465 _89481 s x f x') = (term225 _89465 _89481 s x f x').
Proof. exact (eq_refl (term225 _89465 _89481 s x f x')). Qed.
Lemma lem3453185 {_89465 _89481 : Type'} (x : _89481) (s : _89481 -> Prop) (x' : _89465) (f : type1470 _89465 _89481) : (term235 _89465 _89481 x s x' f) = (term227 _89465 _89481 x s x' f).
Proof. exact (MK_COMB (@lem3453184 _89465 _89481 s x' f x) (@lem3453183 _89465 _89481 s x' f)). Qed.
Lemma lem3453186 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3453187 {_89465 _89481 : Type'} (x : _89481) (s : _89481 -> Prop) (x' : _89465) (f : type1470 _89465 _89481) : (term240 _89465 _89481 x s x' f) = (term241 _89465 _89481 x s x' f).
Proof. exact (MK_COMB (@lem3453186) (@lem3453185 _89465 _89481 x s x' f)). Qed.
Lemma lem3453188 {_89465 _89481 : Type'} (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term237 _89465 _89481 s x f t) = (term210 _89465 _89481 t s x f).
Proof. exact (eq_refl (term237 _89465 _89481 s x f t)). Qed.
Lemma lem3453189 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) : (term225 _89465 _89481 s x f x') = (term225 _89465 _89481 s x f x').
Proof. exact (eq_refl (term225 _89465 _89481 s x f x')). Qed.
Lemma lem3453190 {_89465 _89481 : Type'} (x : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x' : _89465) (f : type1470 _89465 _89481) : (term242 _89465 _89481 x s x' f t) = (term243 _89465 _89481 x t s x' f).
Proof. exact (MK_COMB (@lem3453189 _89465 _89481 s x' f x) (@lem3453188 _89465 _89481 t s x' f)). Qed.
Lemma lem3453191 {_89465 _89481 : Type'} (x : _89481) (s : _89481 -> Prop) (x' : _89465) (f : type1470 _89465 _89481) : (term244 _89465 _89481 x s x' f) = (term245 _89465 _89481 x s x' f).
Proof. exact (fun_ext (fun t : _89465 -> Prop => @lem3453190 _89465 _89481 x t s x' f)). Qed.
Lemma lem3453192 {_89465 : Type'} : (@ex (_89465 -> Prop)) = (@ex (_89465 -> Prop)).
Proof. exact (eq_refl (@ex (_89465 -> Prop))). Qed.
Lemma lem3453193 {_89465 _89481 : Type'} (x : _89481) (s : _89481 -> Prop) (x' : _89465) (f : type1470 _89465 _89481) : (term236 _89465 _89481 x s x' f) = (term246 _89465 _89481 x s x' f).
Proof. exact (MK_COMB (@lem3453192 _89465) (@lem3453191 _89465 _89481 x s x' f)). Qed.
Lemma lem3453194 {_89465 _89481 : Type'} (x : _89481) (s : _89481 -> Prop) (x' : _89465) (f : type1470 _89465 _89481) : ((term235 _89465 _89481 x s x' f) = (term236 _89465 _89481 x s x' f)) = ((term227 _89465 _89481 x s x' f) = (term246 _89465 _89481 x s x' f)).
Proof. exact (MK_COMB (@lem3453187 _89465 _89481 x s x' f) (@lem3453193 _89465 _89481 x s x' f)). Qed.
Lemma lem3453195 {_89465 _89481 : Type'} (x : _89481) (s : _89481 -> Prop) (x' : _89465) (f : type1470 _89465 _89481) : (term227 _89465 _89481 x s x' f) = (term246 _89465 _89481 x s x' f).
Proof. exact (EQ_MP (@lem3453194 _89465 _89481 x s x' f) (@lem3453179 _89465 _89481 x s x' f)). Qed.
Lemma lem3453197 {A : Type'} (P : Prop) (Q : A -> Prop) : (term231 A P Q) = (term232 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3453198 {_89481 : Type'} (P : Prop) (Q : _89481 -> Prop) : (term231 _89481 P Q) = (term232 _89481 P Q).
Proof. exact (@lem3453197 _89481 P Q). Qed.
Lemma lem3453199 {_89465 _89481 : Type'} (x : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x' : _89465) (f : type1470 _89465 _89481) : (term247 _89465 _89481 x t s x' f) = (term248 _89465 _89481 x t s x' f).
Proof. exact (@lem3453198 _89481 (term154 _89465 _89481 s x' f x) (term209 _89465 _89481 t s x' f)). Qed.
Lemma lem3453200 {_89465 _89481 : Type'} (x : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x' : _89465) (f : type1470 _89465 _89481) : (term249 _89465 _89481 t s x' f x) = (term207 _89465 _89481 x t s x' f).
Proof. exact (eq_refl (term249 _89465 _89481 t s x' f x)). Qed.
Lemma lem3453201 {_89465 _89481 : Type'} (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term250 _89465 _89481 t s x f) = (term209 _89465 _89481 t s x f).
Proof. exact (fun_ext (fun x' : _89481 => @lem3453200 _89465 _89481 x' t s x f)). Qed.
Lemma lem3453202 {_89481 : Type'} : (@ex _89481) = (@ex _89481).
Proof. exact (eq_refl (@ex _89481)). Qed.
Lemma lem3453203 {_89465 _89481 : Type'} (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term251 _89465 _89481 t s x f) = (term210 _89465 _89481 t s x f).
Proof. exact (MK_COMB (@lem3453202 _89481) (@lem3453201 _89465 _89481 t s x f)). Qed.
Lemma lem3453204 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) : (term225 _89465 _89481 s x f x') = (term225 _89465 _89481 s x f x').
Proof. exact (eq_refl (term225 _89465 _89481 s x f x')). Qed.
Lemma lem3453205 {_89465 _89481 : Type'} (x : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x' : _89465) (f : type1470 _89465 _89481) : (term247 _89465 _89481 x t s x' f) = (term243 _89465 _89481 x t s x' f).
Proof. exact (MK_COMB (@lem3453204 _89465 _89481 s x' f x) (@lem3453203 _89465 _89481 t s x' f)). Qed.
Lemma lem3453206 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3453207 {_89465 _89481 : Type'} (x : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x' : _89465) (f : type1470 _89465 _89481) : (term252 _89465 _89481 x t s x' f) = (term253 _89465 _89481 x t s x' f).
Proof. exact (MK_COMB (@lem3453206) (@lem3453205 _89465 _89481 x t s x' f)). Qed.
Lemma lem3453208 {_89465 _89481 : Type'} (x' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term249 _89465 _89481 t s x f x') = (term207 _89465 _89481 x' t s x f).
Proof. exact (eq_refl (term249 _89465 _89481 t s x f x')). Qed.
Lemma lem3453209 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) : (term225 _89465 _89481 s x f x') = (term225 _89465 _89481 s x f x').
Proof. exact (eq_refl (term225 _89465 _89481 s x f x')). Qed.
Lemma lem3453210 {_89465 _89481 : Type'} (x : _89481) (x' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x'' : _89465) (f : type1470 _89465 _89481) : (term254 _89465 _89481 x t s x'' f x') = (term255 _89465 _89481 x x' t s x'' f).
Proof. exact (MK_COMB (@lem3453209 _89465 _89481 s x'' f x) (@lem3453208 _89465 _89481 x' t s x'' f)). Qed.
Lemma lem3453211 {_89465 _89481 : Type'} (x : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x' : _89465) (f : type1470 _89465 _89481) : (term256 _89465 _89481 x t s x' f) = (term257 _89465 _89481 x t s x' f).
Proof. exact (fun_ext (fun x'' : _89481 => @lem3453210 _89465 _89481 x x'' t s x' f)). Qed.
Lemma lem3453212 {_89481 : Type'} : (@ex _89481) = (@ex _89481).
Proof. exact (eq_refl (@ex _89481)). Qed.
Lemma lem3453213 {_89465 _89481 : Type'} (x : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x' : _89465) (f : type1470 _89465 _89481) : (term248 _89465 _89481 x t s x' f) = (term258 _89465 _89481 x t s x' f).
Proof. exact (MK_COMB (@lem3453212 _89481) (@lem3453211 _89465 _89481 x t s x' f)). Qed.
Lemma lem3453214 {_89465 _89481 : Type'} (x : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x' : _89465) (f : type1470 _89465 _89481) : ((term247 _89465 _89481 x t s x' f) = (term248 _89465 _89481 x t s x' f)) = ((term243 _89465 _89481 x t s x' f) = (term258 _89465 _89481 x t s x' f)).
Proof. exact (MK_COMB (@lem3453207 _89465 _89481 x t s x' f) (@lem3453213 _89465 _89481 x t s x' f)). Qed.
Lemma lem3453215 {_89465 _89481 : Type'} (x : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x' : _89465) (f : type1470 _89465 _89481) : (term243 _89465 _89481 x t s x' f) = (term258 _89465 _89481 x t s x' f).
Proof. exact (EQ_MP (@lem3453214 _89465 _89481 x t s x' f) (@lem3453199 _89465 _89481 x t s x' f)). Qed.
Lemma lem3453216 {_89465 _89481 : Type'} (x : _89481) (s : _89481 -> Prop) (x' : _89465) (f : type1470 _89465 _89481) : (term245 _89465 _89481 x s x' f) = (term259 _89465 _89481 x s x' f).
Proof. exact (fun_ext (fun t : _89465 -> Prop => @lem3453215 _89465 _89481 x t s x' f)). Qed.
Lemma lem3453217 {_89465 : Type'} : (@ex (_89465 -> Prop)) = (@ex (_89465 -> Prop)).
Proof. exact (eq_refl (@ex (_89465 -> Prop))). Qed.
Lemma lem3453218 {_89465 _89481 : Type'} (x : _89481) (s : _89481 -> Prop) (x' : _89465) (f : type1470 _89465 _89481) : (term246 _89465 _89481 x s x' f) = (term260 _89465 _89481 x s x' f).
Proof. exact (MK_COMB (@lem3453217 _89465) (@lem3453216 _89465 _89481 x s x' f)). Qed.
Lemma lem3453219 {_89465 _89481 : Type'} (x : _89481) (s : _89481 -> Prop) (x' : _89465) (f : type1470 _89465 _89481) : (term227 _89465 _89481 x s x' f) = (term260 _89465 _89481 x s x' f).
Proof. exact (TRANS (@lem3453195 _89465 _89481 x s x' f) (@lem3453218 _89465 _89481 x s x' f)). Qed.
Lemma lem3453220 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term229 _89465 _89481 s x f) = (term261 _89465 _89481 s x f).
Proof. exact (fun_ext (fun x' : _89481 => @lem3453219 _89465 _89481 x' s x f)). Qed.
Lemma lem3453221 {_89481 : Type'} : (@ex _89481) = (@ex _89481).
Proof. exact (eq_refl (@ex _89481)). Qed.
Lemma lem3453222 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term230 _89465 _89481 s x f) = (term262 _89465 _89481 s x f).
Proof. exact (MK_COMB (@lem3453221 _89481) (@lem3453220 _89465 _89481 s x f)). Qed.
Lemma lem3453223 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term213 _89465 _89481 s x f) = (term262 _89465 _89481 s x f).
Proof. exact (TRANS (@lem3453175 _89465 _89481 s x f) (@lem3453222 _89465 _89481 s x f)). Qed.
Lemma lem3453225 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term143 _89465 _89481 s x f) = (term262 _89465 _89481 s x f).
Proof. exact (TRANS (@lem3453149 _89465 _89481 s x f) (@lem3453223 _89465 _89481 s x f)). Qed.
Lemma lem3453226 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term86 _89465 _89481 s x f) = (term262 _89465 _89481 s x f).
Proof. exact (TRANS (@lem3452753 _89465 _89481 s x f) (@lem3453225 _89465 _89481 s x f)). Qed.
Lemma lem3453227 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term86 _89465 _89481 s x f) : term262 _89465 _89481 s x f.
Proof. exact (EQ_MP (@lem3453226 _89465 _89481 s x f) (@lem3452665 _89465 _89481 s x f h1)). Qed.
Lemma lem3453228 {_89465 _89481 : Type'} (x' : _89481) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term260 _89465 _89481 x' s x f) : term260 _89465 _89481 x' s x f.
Proof. exact (h1). Qed.
Lemma lem3453229 {_89465 _89481 : Type'} (x' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term258 _89465 _89481 x' t s x f) : term258 _89465 _89481 x' t s x f.
Proof. exact (h1). Qed.
Lemma lem3453230 {_89465 _89481 : Type'} (x' : _89481) (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term255 _89465 _89481 x' x'' t s x f) : term255 _89465 _89481 x' x'' t s x f.
Proof. exact (h1). Qed.
Lemma lem3453247 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) : (term120 _89465 _89481 s x f x') = (term120 _89465 _89481 s x f x').
Proof. exact (eq_refl (term120 _89465 _89481 s x f x')). Qed.
Lemma lem3453248 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term130 _89465 _89481 s x f) = (term130 _89465 _89481 s x f).
Proof. exact (fun_ext (fun x' : _89481 => @lem3453247 _89465 _89481 s x f x')). Qed.
Lemma lem3453249 {_89481 : Type'} : (@all _89481) = (@all _89481).
Proof. exact (eq_refl (@all _89481)). Qed.
Lemma lem3453250 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term131 _89465 _89481 s x f) = (term131 _89465 _89481 s x f).
Proof. exact (MK_COMB (@lem3453249 _89481) (@lem3453248 _89465 _89481 s x f)). Qed.
Lemma lem3453277 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (x'' : _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term205 _89465 _89481 f x'' s x t) = (term205 _89465 _89481 f x'' s x t).
Proof. exact (eq_refl (term205 _89465 _89481 f x'' s x t)). Qed.
Lemma lem3453278 {_89465 _89481 : Type'} (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term207 _89465 _89481 x'' t s x f) = (term207 _89465 _89481 x'' t s x f).
Proof. exact (MK_COMB (@lem3453277 _89465 _89481 f x'' s x t) (@lem3453250 _89465 _89481 s x f)). Qed.
Lemma lem3453295 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) : (term118 _89465 _89481 s x f x') = (term118 _89465 _89481 s x f x').
Proof. exact (eq_refl (term118 _89465 _89481 s x f x')). Qed.
Lemma lem3453300 {_89465 : Type'} (x : _89465) (t : _89465 -> Prop) : (@IN _89465 x t) = (@IN _89465 x t).
Proof. exact (eq_refl (@IN _89465 x t)). Qed.
Lemma lem3453319 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (x : _89481) (s : _89481 -> Prop) : (term88 _89465 _89481 t f x s) = (term88 _89465 _89481 t f x s).
Proof. exact (eq_refl (term88 _89465 _89481 t f x s)). Qed.
Lemma lem3453320 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (s : _89481 -> Prop) : (term96 _89465 _89481 t f s) = (term96 _89465 _89481 t f s).
Proof. exact (fun_ext (fun x : _89481 => @lem3453319 _89465 _89481 t f x s)). Qed.
Lemma lem3453321 {_89481 : Type'} : (@all _89481) = (@all _89481).
Proof. exact (eq_refl (@all _89481)). Qed.
Lemma lem3453322 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (s : _89481 -> Prop) : (term97 _89465 _89481 t f s) = (term97 _89465 _89481 t f s).
Proof. exact (MK_COMB (@lem3453321 _89481) (@lem3453320 _89465 _89481 t f s)). Qed.
Lemma lem3453323 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3453324 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (s : _89481 -> Prop) : (term103 _89465 _89481 t f s) = (term103 _89465 _89481 t f s).
Proof. exact (MK_COMB (@lem3453323) (@lem3453322 _89465 _89481 t f s)). Qed.
Lemma lem3453325 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term105 _89465 _89481 f s x t) = (term105 _89465 _89481 f s x t).
Proof. exact (MK_COMB (@lem3453324 _89465 _89481 t f s) (@lem3453300 _89465 x t)). Qed.
Lemma lem3453326 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term115 _89465 _89481 f s x) = (term115 _89465 _89481 f s x).
Proof. exact (fun_ext (fun t : _89465 -> Prop => @lem3453325 _89465 _89481 f s x t)). Qed.
Lemma lem3453327 {_89465 : Type'} : (@all (_89465 -> Prop)) = (@all (_89465 -> Prop)).
Proof. exact (eq_refl (@all (_89465 -> Prop))). Qed.
Lemma lem3453328 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term116 _89465 _89481 f s x) = (term116 _89465 _89481 f s x).
Proof. exact (MK_COMB (@lem3453327 _89465) (@lem3453326 _89465 _89481 f s x)). Qed.
Lemma lem3453329 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3453330 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term137 _89465 _89481 f s x) = (term137 _89465 _89481 f s x).
Proof. exact (MK_COMB (@lem3453329) (@lem3453328 _89465 _89481 f s x)). Qed.
Lemma lem3453331 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) : (term154 _89465 _89481 s x f x') = (term154 _89465 _89481 s x f x').
Proof. exact (MK_COMB (@lem3453330 _89465 _89481 f s x) (@lem3453295 _89465 _89481 s x f x')). Qed.
Lemma lem3453332 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3453333 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) : (term225 _89465 _89481 s x f x') = (term225 _89465 _89481 s x f x').
Proof. exact (MK_COMB (@lem3453332) (@lem3453331 _89465 _89481 s x f x')). Qed.
Lemma lem3453334 {_89465 _89481 : Type'} (x' : _89481) (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term255 _89465 _89481 x' x'' t s x f) = (term255 _89465 _89481 x' x'' t s x f).
Proof. exact (MK_COMB (@lem3453333 _89465 _89481 s x f x') (@lem3453278 _89465 _89481 x'' t s x f)). Qed.
Lemma lem3453335 {_89465 _89481 : Type'} (x' : _89481) (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term255 _89465 _89481 x' x'' t s x f) : term255 _89465 _89481 x' x'' t s x f.
Proof. exact (EQ_MP (@lem3453334 _89465 _89481 x' x'' t s x f) (@lem3453230 _89465 _89481 x' x'' t s x f h1)). Qed.
Lemma lem3453336 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) (h1 : term154 _89465 _89481 s x f x') : term154 _89465 _89481 s x f x'.
Proof. exact (h1). Qed.
Lemma lem3453337 {_89465 _89481 : Type'} (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term207 _89465 _89481 x'' t s x f) : term207 _89465 _89481 x'' t s x f.
Proof. exact (h1). Qed.
Lemma lem3453338 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) (h1 : term154 _89465 _89481 s x f x') : term118 _89465 _89481 s x f x'.
Proof. exact (proj2 (@lem3453336 _89465 _89481 s x f x' h1)). Qed.
Lemma lem3453339 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) (h1 : term154 _89465 _89481 s x f x') : term116 _89465 _89481 f s x.
Proof. exact (proj1 (@lem3453336 _89465 _89481 s x f x' h1)). Qed.
Lemma lem3453342 {_89465 _89481 : Type'} (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term207 _89465 _89481 x'' t s x f) : term131 _89465 _89481 s x f.
Proof. exact (proj2 (@lem3453337 _89465 _89481 x'' t s x f h1)). Qed.
Lemma lem3453343 {_89465 _89481 : Type'} (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term207 _89465 _89481 x'' t s x f) : term171 _89465 _89481 f x'' s x t.
Proof. exact (proj1 (@lem3453337 _89465 _89481 x'' t s x f h1)). Qed.
Lemma lem3453345 {_89465 _89481 : Type'} (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term207 _89465 _89481 x'' t s x f) : term83 _89465 _89481 t f x'' s.
Proof. exact (proj1 (@lem3453343 _89465 _89481 x'' t s x f h1)). Qed.
Lemma lem3453349 {A : Type'} (P : A -> Prop) (Q : Prop) : (term263 A P Q) = (term264 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3453350 {_89481 : Type'} (P : _89481 -> Prop) (Q : Prop) : (term263 _89481 P Q) = (term264 _89481 P Q).
Proof. exact (@lem3453349 _89481 P Q). Qed.
Lemma lem3453351 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term265 _89465 _89481 f s x t) = (term266 _89465 _89481 f s x t).
Proof. exact (@lem3453350 _89481 (term96 _89465 _89481 t f s) (@IN _89465 x t)). Qed.
Lemma lem3453352 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (x : _89481) (s : _89481 -> Prop) : (term267 _89465 _89481 t f s x) = (term88 _89465 _89481 t f x s).
Proof. exact (eq_refl (term267 _89465 _89481 t f s x)). Qed.
Lemma lem3453353 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (s : _89481 -> Prop) : (term268 _89465 _89481 t f s) = (term96 _89465 _89481 t f s).
Proof. exact (fun_ext (fun x : _89481 => @lem3453352 _89465 _89481 t f x s)). Qed.
Lemma lem3453354 {_89481 : Type'} : (@all _89481) = (@all _89481).
Proof. exact (eq_refl (@all _89481)). Qed.
Lemma lem3453355 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (s : _89481 -> Prop) : (term269 _89465 _89481 t f s) = (term97 _89465 _89481 t f s).
Proof. exact (MK_COMB (@lem3453354 _89481) (@lem3453353 _89465 _89481 t f s)). Qed.
Lemma lem3453356 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3453357 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (s : _89481 -> Prop) : (term270 _89465 _89481 t f s) = (term103 _89465 _89481 t f s).
Proof. exact (MK_COMB (@lem3453356) (@lem3453355 _89465 _89481 t f s)). Qed.
Lemma lem3453358 {_89465 : Type'} (x : _89465) (t : _89465 -> Prop) : (@IN _89465 x t) = (@IN _89465 x t).
Proof. exact (eq_refl (@IN _89465 x t)). Qed.
Lemma lem3453359 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term265 _89465 _89481 f s x t) = (term105 _89465 _89481 f s x t).
Proof. exact (MK_COMB (@lem3453357 _89465 _89481 t f s) (@lem3453358 _89465 x t)). Qed.
Lemma lem3453360 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3453361 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term271 _89465 _89481 f s x t) = (term272 _89465 _89481 f s x t).
Proof. exact (MK_COMB (@lem3453360) (@lem3453359 _89465 _89481 f s x t)). Qed.
Lemma lem3453362 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (x : _89481) (s : _89481 -> Prop) : (term267 _89465 _89481 t f s x) = (term88 _89465 _89481 t f x s).
Proof. exact (eq_refl (term267 _89465 _89481 t f s x)). Qed.
Lemma lem3453363 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3453364 {_89465 _89481 : Type'} (t : _89465 -> Prop) (f : type1470 _89465 _89481) (x : _89481) (s : _89481 -> Prop) : (term273 _89465 _89481 t f s x) = (term274 _89465 _89481 t f x s).
Proof. exact (MK_COMB (@lem3453363) (@lem3453362 _89465 _89481 t f x s)). Qed.
Lemma lem3453365 {_89465 : Type'} (x : _89465) (t : _89465 -> Prop) : (@IN _89465 x t) = (@IN _89465 x t).
Proof. exact (eq_refl (@IN _89465 x t)). Qed.
Lemma lem3453366 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (x : _89481) (s : _89481 -> Prop) (x' : _89465) (t : _89465 -> Prop) : (term275 _89465 _89481 f s x x' t) = (term276 _89465 _89481 f x s x' t).
Proof. exact (MK_COMB (@lem3453364 _89465 _89481 t f x s) (@lem3453365 _89465 x' t)). Qed.
Lemma lem3453367 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term277 _89465 _89481 f s x t) = (term278 _89465 _89481 f s x t).
Proof. exact (fun_ext (fun x' : _89481 => @lem3453366 _89465 _89481 f x' s x t)). Qed.
Lemma lem3453368 {_89481 : Type'} : (@all _89481) = (@all _89481).
Proof. exact (eq_refl (@all _89481)). Qed.
Lemma lem3453369 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term266 _89465 _89481 f s x t) = (term279 _89465 _89481 f s x t).
Proof. exact (MK_COMB (@lem3453368 _89481) (@lem3453367 _89465 _89481 f s x t)). Qed.
Lemma lem3453370 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : ((term265 _89465 _89481 f s x t) = (term266 _89465 _89481 f s x t)) = ((term105 _89465 _89481 f s x t) = (term279 _89465 _89481 f s x t)).
Proof. exact (MK_COMB (@lem3453361 _89465 _89481 f s x t) (@lem3453369 _89465 _89481 f s x t)). Qed.
Lemma lem3453371 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term105 _89465 _89481 f s x t) = (term279 _89465 _89481 f s x t).
Proof. exact (EQ_MP (@lem3453370 _89465 _89481 f s x t) (@lem3453351 _89465 _89481 f s x t)). Qed.
Lemma lem3453372 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term115 _89465 _89481 f s x) = (term280 _89465 _89481 f s x).
Proof. exact (fun_ext (fun t : _89465 -> Prop => @lem3453371 _89465 _89481 f s x t)). Qed.
Lemma lem3453373 {_89465 : Type'} : (@all (_89465 -> Prop)) = (@all (_89465 -> Prop)).
Proof. exact (eq_refl (@all (_89465 -> Prop))). Qed.
Lemma lem3453374 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term116 _89465 _89481 f s x) = (term281 _89465 _89481 f s x).
Proof. exact (MK_COMB (@lem3453373 _89465) (@lem3453372 _89465 _89481 f s x)). Qed.
Lemma lem3453387 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (x : _89481) (s : _89481 -> Prop) (x' : _89465) (t : _89465 -> Prop) : (term276 _89465 _89481 f x s x' t) = (term276 _89465 _89481 f x s x' t).
Proof. exact (eq_refl (term276 _89465 _89481 f x s x' t)). Qed.
Lemma lem3453388 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term278 _89465 _89481 f s x t) = (term278 _89465 _89481 f s x t).
Proof. exact (fun_ext (fun x' : _89481 => @lem3453387 _89465 _89481 f x' s x t)). Qed.
Lemma lem3453389 {_89481 : Type'} : (@all _89481) = (@all _89481).
Proof. exact (eq_refl (@all _89481)). Qed.
Lemma lem3453390 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (t : _89465 -> Prop) : (term279 _89465 _89481 f s x t) = (term279 _89465 _89481 f s x t).
Proof. exact (MK_COMB (@lem3453389 _89481) (@lem3453388 _89465 _89481 f s x t)). Qed.
Lemma lem3453391 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term280 _89465 _89481 f s x) = (term280 _89465 _89481 f s x).
Proof. exact (fun_ext (fun t : _89465 -> Prop => @lem3453390 _89465 _89481 f s x t)). Qed.
Lemma lem3453392 {_89465 : Type'} : (@all (_89465 -> Prop)) = (@all (_89465 -> Prop)).
Proof. exact (eq_refl (@all (_89465 -> Prop))). Qed.
Lemma lem3453393 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term281 _89465 _89481 f s x) = (term281 _89465 _89481 f s x).
Proof. exact (MK_COMB (@lem3453392 _89465) (@lem3453391 _89465 _89481 f s x)). Qed.
Lemma lem3453394 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) : (term116 _89465 _89481 f s x) = (term281 _89465 _89481 f s x).
Proof. exact (TRANS (@lem3453374 _89465 _89481 f s x) (@lem3453393 _89465 _89481 f s x)). Qed.
Lemma lem3453395 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) (h1 : term154 _89465 _89481 s x f x') : term281 _89465 _89481 f s x.
Proof. exact (EQ_MP (@lem3453394 _89465 _89481 f s x) (@lem3453339 _89465 _89481 s x f x' h1)). Qed.
Lemma lem3453411 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) : (term120 _89465 _89481 s x f x') = (term120 _89465 _89481 s x f x').
Proof. exact (eq_refl (term120 _89465 _89481 s x f x')). Qed.
Lemma lem3453412 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term130 _89465 _89481 s x f) = (term130 _89465 _89481 s x f).
Proof. exact (fun_ext (fun x' : _89481 => @lem3453411 _89465 _89481 s x f x')). Qed.
Lemma lem3453413 {_89481 : Type'} : (@all _89481) = (@all _89481).
Proof. exact (eq_refl (@all _89481)). Qed.
Lemma lem3453415 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term131 _89465 _89481 s x f) = (term131 _89465 _89481 s x f).
Proof. exact (MK_COMB (@lem3453413 _89481) (@lem3453412 _89465 _89481 s x f)). Qed.
Lemma lem3453416 {_89465 _89481 : Type'} (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term207 _89465 _89481 x'' t s x f) : term131 _89465 _89481 s x f.
Proof. exact (EQ_MP (@lem3453415 _89465 _89481 s x f) (@lem3453342 _89465 _89481 x'' t s x f h1)). Qed.
Lemma lem3453429 {_89465 _89481 : Type'} (_36412 : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) (h1 : term154 _89465 _89481 s x f x') : term282 _89465 _89481 f s x _36412.
Proof. exact (@lem3453395 _89465 _89481 s x f x' h1 _36412). Qed.
Lemma lem3453430 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) (x : _89465) (_36412 : _89465 -> Prop) : (term282 _89465 _89481 f s x _36412) = (term279 _89465 _89481 f s x _36412).
Proof. exact (eq_refl (term282 _89465 _89481 f s x _36412)). Qed.
Lemma lem3453431 {_89465 _89481 : Type'} (_36412 : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) (h1 : term154 _89465 _89481 s x f x') : term279 _89465 _89481 f s x _36412.
Proof. exact (EQ_MP (@lem3453430 _89465 _89481 f s x _36412) (@lem3453429 _89465 _89481 _36412 s x f x' h1)). Qed.
Lemma lem3453432 {_89465 _89481 : Type'} (_36412 : _89465 -> Prop) (_36413 : _89481) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) (h1 : term154 _89465 _89481 s x f x') : term283 _89465 _89481 f s x _36412 _36413.
Proof. exact (@lem3453431 _89465 _89481 _36412 s x f x' h1 _36413). Qed.
Lemma lem3453433 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (_36413 : _89481) (s : _89481 -> Prop) (x : _89465) (_36412 : _89465 -> Prop) : (term283 _89465 _89481 f s x _36412 _36413) = (term276 _89465 _89481 f _36413 s x _36412).
Proof. exact (eq_refl (term283 _89465 _89481 f s x _36412 _36413)). Qed.
Lemma lem3453434 {_89465 _89481 : Type'} (_36413 : _89481) (_36412 : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) (h1 : term154 _89465 _89481 s x f x') : term276 _89465 _89481 f _36413 s x _36412.
Proof. exact (EQ_MP (@lem3453433 _89465 _89481 f _36413 s x _36412) (@lem3453432 _89465 _89481 _36412 _36413 s x f x' h1)). Qed.
Lemma lem3453435 {_89465 _89481 : Type'} (_36414 : _89481) (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term207 _89465 _89481 x'' t s x f) : term284 _89465 _89481 s x f _36414.
Proof. exact (@lem3453416 _89465 _89481 x'' t s x f h1 _36414). Qed.
Lemma lem3453436 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (_36414 : _89481) : (term284 _89465 _89481 s x f _36414) = (term120 _89465 _89481 s x f _36414).
Proof. exact (eq_refl (term284 _89465 _89481 s x f _36414)). Qed.
Lemma lem3453448 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (_36413 : _89481) (s : _89481 -> Prop) (x : _89465) (_36412 : _89465 -> Prop) : (term276 _89465 _89481 f _36413 s x _36412) = (term285 _89465 _89481 f _36413 s x _36412).
Proof. exact (@lem3452312 (term286 _89465 _89481 _36412 f _36413) (term98 _89481 _36413 s) (@IN _89465 x _36412)). Qed.
Lemma lem3453449 {_89465 _89481 : Type'} (_36413 : _89481) (_36412 : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) (h1 : term154 _89465 _89481 s x f x') : term285 _89465 _89481 f _36413 s x _36412.
Proof. exact (EQ_MP (@lem3453448 _89465 _89481 f _36413 s x _36412) (@lem3453434 _89465 _89481 _36413 _36412 s x f x' h1)). Qed.
Lemma lem3453453 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) (h1 : term154 _89465 _89481 s x f x') : term287 _89465 _89481 x f x'.
Proof. exact (proj2 (@lem3453338 _89465 _89481 s x f x' h1)). Qed.
Lemma lem3453461 {_89465 _89481 : Type'} (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term207 _89465 _89481 x'' t s x f) : term98 _89465 x t.
Proof. exact (proj2 (@lem3453343 _89465 _89481 x'' t s x f h1)). Qed.
Lemma lem3453463 {_89465 _89481 : Type'} (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term207 _89465 _89481 x'' t s x f) : t = (f x'').
Proof. exact (proj1 (@lem3453345 _89465 _89481 x'' t s x f h1)). Qed.
Lemma lem3453493 {_89465 _89481 : Type'} (_36414 : _89481) (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term207 _89465 _89481 x'' t s x f) : term120 _89465 _89481 s x f _36414.
Proof. exact (EQ_MP (@lem3453436 _89465 _89481 s x f _36414) (@lem3453435 _89465 _89481 _36414 x'' t s x f h1)). Qed.
Lemma lem3453494 {_89465 : Type'} (x : _89465) : (term288 _89465 x) = (term288 _89465 x).
Proof. exact (eq_refl (term288 _89465 x)). Qed.
Lemma lem3453495 {_89465 _89481 : Type'} (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term207 _89465 _89481 x'' t s x f) : (term289 _89465 x t) = (term290 _89465 _89481 x f x'').
Proof. exact (MK_COMB (@lem3453494 _89465 x) (@lem3453463 _89465 _89481 x'' t s x f h1)). Qed.
Lemma lem3453496 {_89465 _89481 : Type'} (x : _89465) (f : type1470 _89465 _89481) (x'' : _89481) : (term290 _89465 _89481 x f x'') = (term287 _89465 _89481 x f x'').
Proof. exact (eq_refl (term290 _89465 _89481 x f x'')). Qed.
Lemma lem3453497 {_89465 : Type'} (x : _89465) (t : _89465 -> Prop) : (term291 _89465 x t) = (term291 _89465 x t).
Proof. exact (eq_refl (term291 _89465 x t)). Qed.
Lemma lem3453498 {_89465 _89481 : Type'} (t : _89465 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x'' : _89481) : ((term289 _89465 x t) = (term290 _89465 _89481 x f x'')) = ((term289 _89465 x t) = (term287 _89465 _89481 x f x'')).
Proof. exact (MK_COMB (@lem3453497 _89465 x t) (@lem3453496 _89465 _89481 x f x'')). Qed.
Lemma lem3453499 {_89465 : Type'} (x : _89465) (t : _89465 -> Prop) : (term289 _89465 x t) = (term98 _89465 x t).
Proof. exact (eq_refl (term289 _89465 x t)). Qed.
Lemma lem3453500 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3453501 {_89465 : Type'} (x : _89465) (t : _89465 -> Prop) : (term291 _89465 x t) = (term292 _89465 x t).
Proof. exact (MK_COMB (@lem3453500) (@lem3453499 _89465 x t)). Qed.
Lemma lem3453502 {_89465 _89481 : Type'} (x : _89465) (f : type1470 _89465 _89481) (x'' : _89481) : (term287 _89465 _89481 x f x'') = (term287 _89465 _89481 x f x'').
Proof. exact (eq_refl (term287 _89465 _89481 x f x'')). Qed.
Lemma lem3453503 {_89465 _89481 : Type'} (t : _89465 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x'' : _89481) : ((term289 _89465 x t) = (term287 _89465 _89481 x f x'')) = ((term98 _89465 x t) = (term287 _89465 _89481 x f x'')).
Proof. exact (MK_COMB (@lem3453501 _89465 x t) (@lem3453502 _89465 _89481 x f x'')). Qed.
Lemma lem3453504 {_89465 _89481 : Type'} (t : _89465 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x'' : _89481) : ((term289 _89465 x t) = (term290 _89465 _89481 x f x'')) = ((term98 _89465 x t) = (term287 _89465 _89481 x f x'')).
Proof. exact (TRANS (@lem3453498 _89465 _89481 t x f x'') (@lem3453503 _89465 _89481 t x f x'')). Qed.
Lemma lem3453505 {_89465 _89481 : Type'} (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term207 _89465 _89481 x'' t s x f) : (term98 _89465 x t) = (term287 _89465 _89481 x f x'').
Proof. exact (EQ_MP (@lem3453504 _89465 _89481 t x f x'') (@lem3453495 _89465 _89481 x'' t s x f h1)). Qed.
Lemma lem3453506 {_89465 _89481 : Type'} (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term207 _89465 _89481 x'' t s x f) : term287 _89465 _89481 x f x''.
Proof. exact (EQ_MP (@lem3453505 _89465 _89481 x'' t s x f h1) (@lem3453461 _89465 _89481 x'' t s x f h1)). Qed.
Lemma lem3453576 {_89465 : Type'} (x : _89465 -> Prop) : x = x.
Proof. exact (@lem21386 (_89465 -> Prop) x). Qed.
Lemma lem3453577 {_89465 : Type'} (x : _89465 -> Prop) : x = x.
Proof. exact (@lem3453576 _89465 x). Qed.
Lemma lem3453578 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (x' : _89481) : (f x') = (f x').
Proof. exact (@lem3453577 _89465 (f x')). Qed.
Lemma lem3453579 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (x' : _89481) : term293 _89465 _89481 f x'.
Proof. exact (fun h0 : term294 _89465 _89481 f x' => @lem3453578 _89465 _89481 f x'). Qed.
Lemma lem3453581 (p : Prop) : (term295 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3453582 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (x' : _89481) : (term293 _89465 _89481 f x') = ((f x') = (f x')).
Proof. exact (@lem3453581 ((f x') = (f x'))). Qed.
Lemma lem3453583 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (x' : _89481) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3453582 _89465 _89481 f x') (@lem3453579 _89465 _89481 f x')). Qed.
Lemma lem3453585 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) (h1 : term154 _89465 _89481 s x f x') : @IN _89481 x' s.
Proof. exact (proj1 (@lem3453338 _89465 _89481 s x f x' h1)). Qed.
Lemma lem3453586 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) (h1 : term154 _89465 _89481 s x f x') : term296 _89481 x' s.
Proof. exact (fun h0 : term98 _89481 x' s => @lem3453585 _89465 _89481 s x f x' h1). Qed.
Lemma lem3453588 (p : Prop) : (term295 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3453589 {_89481 : Type'} (x' : _89481) (s : _89481 -> Prop) : (term296 _89481 x' s) = (@IN _89481 x' s).
Proof. exact (@lem3453588 (@IN _89481 x' s)). Qed.
Lemma lem3453590 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) (h1 : term154 _89465 _89481 s x f x') : @IN _89481 x' s.
Proof. exact (EQ_MP (@lem3453589 _89481 x' s) (@lem3453586 _89465 _89481 s x f x' h1)). Qed.
Lemma lem3453608 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3453609 {_89465 _89481 : Type'} (x : _89465) (_36412 : _89465 -> Prop) (_36413 : _89481) (s : _89481 -> Prop) : (term297 _89465 _89481 _36413 s x _36412) = (term298 _89465 _89481 x _36412 _36413 s).
Proof. exact (@lem3453608 (@IN _89465 x _36412) (term98 _89481 _36413 s)). Qed.
Lemma lem3453615 {_89465 _89481 : Type'} (_36412 : _89465 -> Prop) (f : type1470 _89465 _89481) (_36413 : _89481) : (term299 _89465 _89481 _36412 f _36413) = (term299 _89465 _89481 _36412 f _36413).
Proof. exact (eq_refl (term299 _89465 _89481 _36412 f _36413)). Qed.
Lemma lem3453616 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (x : _89465) (_36412 : _89465 -> Prop) (_36413 : _89481) (s : _89481 -> Prop) : (term285 _89465 _89481 f _36413 s x _36412) = (term300 _89465 _89481 f x _36412 _36413 s).
Proof. exact (MK_COMB (@lem3453615 _89465 _89481 _36412 f _36413) (@lem3453609 _89465 _89481 x _36412 _36413 s)). Qed.
Lemma lem3453620 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3453621 {_89465 _89481 : Type'} (x : _89465) (_36412 : _89465 -> Prop) (f : type1470 _89465 _89481) (_36413 : _89481) (s : _89481 -> Prop) : (term300 _89465 _89481 f x _36412 _36413 s) = (term301 _89465 _89481 x _36412 f _36413 s).
Proof. exact (@lem3453620 (@IN _89465 x _36412) (term286 _89465 _89481 _36412 f _36413) (term98 _89481 _36413 s)). Qed.
Lemma lem3453639 {_89465 _89481 : Type'} (x : _89465) (_36412 : _89465 -> Prop) (f : type1470 _89465 _89481) (_36413 : _89481) (s : _89481 -> Prop) : (term285 _89465 _89481 f _36413 s x _36412) = (term301 _89465 _89481 x _36412 f _36413 s).
Proof. exact (TRANS (@lem3453616 _89465 _89481 f x _36412 _36413 s) (@lem3453621 _89465 _89481 x _36412 f _36413 s)). Qed.
Lemma lem3453640 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3453641 {_89465 _89481 : Type'} (x : _89465) (_36412 : _89465 -> Prop) (f : type1470 _89465 _89481) (_36413 : _89481) (s : _89481 -> Prop) : (term302 _89465 _89481 f _36413 s x _36412) = (term303 _89465 _89481 x _36412 f _36413 s).
Proof. exact (MK_COMB (@lem3453640) (@lem3453639 _89465 _89481 x _36412 f _36413 s)). Qed.
Lemma lem3453659 {_89465 _89481 : Type'} (x : _89465) (_36412 : _89465 -> Prop) (f : type1470 _89465 _89481) (_36413 : _89481) (s : _89481 -> Prop) : (term301 _89465 _89481 x _36412 f _36413 s) = (term301 _89465 _89481 x _36412 f _36413 s).
Proof. exact (eq_refl (term301 _89465 _89481 x _36412 f _36413 s)). Qed.
Lemma lem3453660 {_89465 _89481 : Type'} (x : _89465) (_36412 : _89465 -> Prop) (f : type1470 _89465 _89481) (_36413 : _89481) (s : _89481 -> Prop) : ((term285 _89465 _89481 f _36413 s x _36412) = (term301 _89465 _89481 x _36412 f _36413 s)) = ((term301 _89465 _89481 x _36412 f _36413 s) = (term301 _89465 _89481 x _36412 f _36413 s)).
Proof. exact (MK_COMB (@lem3453641 _89465 _89481 x _36412 f _36413 s) (@lem3453659 _89465 _89481 x _36412 f _36413 s)). Qed.
Lemma lem3453662 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3453663 (x : Prop) : (x = x) = True.
Proof. exact (@lem3453662 Prop x). Qed.
Lemma lem3453664 {_89465 _89481 : Type'} (x : _89465) (_36412 : _89465 -> Prop) (f : type1470 _89465 _89481) (_36413 : _89481) (s : _89481 -> Prop) : ((term301 _89465 _89481 x _36412 f _36413 s) = (term301 _89465 _89481 x _36412 f _36413 s)) = True.
Proof. exact (@lem3453663 (term301 _89465 _89481 x _36412 f _36413 s)). Qed.
Lemma lem3453665 {_89465 _89481 : Type'} (x : _89465) (_36412 : _89465 -> Prop) (f : type1470 _89465 _89481) (_36413 : _89481) (s : _89481 -> Prop) : ((term285 _89465 _89481 f _36413 s x _36412) = (term301 _89465 _89481 x _36412 f _36413 s)) = True.
Proof. exact (TRANS (@lem3453660 _89465 _89481 x _36412 f _36413 s) (@lem3453664 _89465 _89481 x _36412 f _36413 s)). Qed.
Lemma lem3453666 {_89465 _89481 : Type'} (x : _89465) (_36412 : _89465 -> Prop) (f : type1470 _89465 _89481) (_36413 : _89481) (s : _89481 -> Prop) : True = ((term285 _89465 _89481 f _36413 s x _36412) = (term301 _89465 _89481 x _36412 f _36413 s)).
Proof. exact (SYM (@lem3453665 _89465 _89481 x _36412 f _36413 s)). Qed.
Lemma lem3453667 {_89465 _89481 : Type'} (x : _89465) (_36412 : _89465 -> Prop) (f : type1470 _89465 _89481) (_36413 : _89481) (s : _89481 -> Prop) : (term285 _89465 _89481 f _36413 s x _36412) = (term301 _89465 _89481 x _36412 f _36413 s).
Proof. exact (EQ_MP (@lem3453666 _89465 _89481 x _36412 f _36413 s) (@lem0)). Qed.
Lemma lem3453668 {_89465 _89481 : Type'} (_36412 : _89465 -> Prop) (_36413 : _89481) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) (h1 : term154 _89465 _89481 s x f x') : term301 _89465 _89481 x _36412 f _36413 s.
Proof. exact (EQ_MP (@lem3453667 _89465 _89481 x _36412 f _36413 s) (@lem3453449 _89465 _89481 _36413 _36412 s x f x' h1)). Qed.
Lemma lem3453670 (b : Prop) (a : Prop) : (a \/ b) = (term304 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3453671 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (_36413 : _89481) (s : _89481 -> Prop) (x : _89465) (_36412 : _89465 -> Prop) : (term301 _89465 _89481 x _36412 f _36413 s) = (term305 _89465 _89481 f _36413 s x _36412).
Proof. exact (@lem3453670 (term88 _89465 _89481 _36412 f _36413 s) (@IN _89465 x _36412)). Qed.
Lemma lem3453673 (a : Prop) (b : Prop) : (term306 a b) = (term307 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3453674 {_89465 _89481 : Type'} (_36412 : _89465 -> Prop) (f : type1470 _89465 _89481) (_36413 : _89481) (s : _89481 -> Prop) : (term308 _89465 _89481 _36412 f _36413 s) = (term309 _89465 _89481 _36412 f _36413 s).
Proof. exact (@lem3453673 (term286 _89465 _89481 _36412 f _36413) (term98 _89481 _36413 s)). Qed.
Lemma lem3453676 (a : Prop) : (term72 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3453677 {_89465 _89481 : Type'} (_36412 : _89465 -> Prop) (f : type1470 _89465 _89481) (_36413 : _89481) : (term310 _89465 _89481 _36412 f _36413) = (_36412 = (f _36413)).
Proof. exact (@lem3453676 (_36412 = (f _36413))). Qed.
Lemma lem3453678 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3453679 {_89465 _89481 : Type'} (_36412 : _89465 -> Prop) (f : type1470 _89465 _89481) (_36413 : _89481) : (term311 _89465 _89481 _36412 f _36413) = (term312 _89465 _89481 _36412 f _36413).
Proof. exact (MK_COMB (@lem3453678) (@lem3453677 _89465 _89481 _36412 f _36413)). Qed.
Lemma lem3453681 (a : Prop) : (term72 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3453682 {_89481 : Type'} (_36413 : _89481) (s : _89481 -> Prop) : (term313 _89481 _36413 s) = (@IN _89481 _36413 s).
Proof. exact (@lem3453681 (@IN _89481 _36413 s)). Qed.
Lemma lem3453683 {_89465 _89481 : Type'} (_36412 : _89465 -> Prop) (f : type1470 _89465 _89481) (_36413 : _89481) (s : _89481 -> Prop) : (term309 _89465 _89481 _36412 f _36413 s) = (term83 _89465 _89481 _36412 f _36413 s).
Proof. exact (MK_COMB (@lem3453679 _89465 _89481 _36412 f _36413) (@lem3453682 _89481 _36413 s)). Qed.
Lemma lem3453684 {_89465 _89481 : Type'} (_36412 : _89465 -> Prop) (f : type1470 _89465 _89481) (_36413 : _89481) (s : _89481 -> Prop) : (term308 _89465 _89481 _36412 f _36413 s) = (term83 _89465 _89481 _36412 f _36413 s).
Proof. exact (TRANS (@lem3453674 _89465 _89481 _36412 f _36413 s) (@lem3453683 _89465 _89481 _36412 f _36413 s)). Qed.
Lemma lem3453685 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3453686 {_89465 _89481 : Type'} (_36412 : _89465 -> Prop) (f : type1470 _89465 _89481) (_36413 : _89481) (s : _89481 -> Prop) : (term314 _89465 _89481 _36412 f _36413 s) = (term315 _89465 _89481 _36412 f _36413 s).
Proof. exact (MK_COMB (@lem3453685) (@lem3453684 _89465 _89481 _36412 f _36413 s)). Qed.
Lemma lem3453687 {_89465 : Type'} (x : _89465) (_36412 : _89465 -> Prop) : (@IN _89465 x _36412) = (@IN _89465 x _36412).
Proof. exact (eq_refl (@IN _89465 x _36412)). Qed.
Lemma lem3453688 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (_36413 : _89481) (s : _89481 -> Prop) (x : _89465) (_36412 : _89465 -> Prop) : (term305 _89465 _89481 f _36413 s x _36412) = (term316 _89465 _89481 f _36413 s x _36412).
Proof. exact (MK_COMB (@lem3453686 _89465 _89481 _36412 f _36413 s) (@lem3453687 _89465 x _36412)). Qed.
Lemma lem3453689 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (_36413 : _89481) (s : _89481 -> Prop) (x : _89465) (_36412 : _89465 -> Prop) : (term301 _89465 _89481 x _36412 f _36413 s) = (term316 _89465 _89481 f _36413 s x _36412).
Proof. exact (TRANS (@lem3453671 _89465 _89481 f _36413 s x _36412) (@lem3453688 _89465 _89481 f _36413 s x _36412)). Qed.
Lemma lem3453691 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) (h1 : term154 _89465 _89481 s x f x') : term317 _89465 _89481 f x' s.
Proof. exact (conj (@lem3453583 _89465 _89481 f x') (@lem3453590 _89465 _89481 s x f x' h1)). Qed.
Lemma lem3453693 {_89465 _89481 : Type'} (_36413 : _89481) (_36412 : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) (h1 : term154 _89465 _89481 s x f x') : term316 _89465 _89481 f _36413 s x _36412.
Proof. exact (EQ_MP (@lem3453689 _89465 _89481 f _36413 s x _36412) (@lem3453668 _89465 _89481 _36412 _36413 s x f x' h1)). Qed.
Lemma lem3453694 {_89465 _89481 : Type'} (_36413 : _89481) (_36412 : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) (h1 : term154 _89465 _89481 s x f x') : term316 _89465 _89481 f _36413 s x _36412.
Proof. exact (@lem3453693 _89465 _89481 _36413 _36412 s x f x' h1). Qed.
Lemma lem3453695 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) (h1 : term154 _89465 _89481 s x f x') : term318 _89465 _89481 s x f x'.
Proof. exact (@lem3453694 _89465 _89481 x' (f x') s x f x' h1). Qed.
Lemma lem3453698 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) (h1 : term154 _89465 _89481 s x f x') : term119 _89465 _89481 x f x'.
Proof. exact (@lem3453695 _89465 _89481 s x f x' h1 (@lem3453691 _89465 _89481 s x f x' h1)). Qed.
Lemma lem3453699 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) (h1 : term154 _89465 _89481 s x f x') : term319 _89465 _89481 x f x'.
Proof. exact (fun h0 : term287 _89465 _89481 x f x' => @lem3453698 _89465 _89481 s x f x' h1). Qed.
Lemma lem3453701 (p : Prop) : (term295 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3453702 {_89465 _89481 : Type'} (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) : (term319 _89465 _89481 x f x') = (term119 _89465 _89481 x f x').
Proof. exact (@lem3453701 (term119 _89465 _89481 x f x')). Qed.
Lemma lem3453703 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) (h1 : term154 _89465 _89481 s x f x') : term119 _89465 _89481 x f x'.
Proof. exact (EQ_MP (@lem3453702 _89465 _89481 x f x') (@lem3453699 _89465 _89481 s x f x' h1)). Qed.
Lemma lem3453706 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3453708 {_89465 _89481 : Type'} (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) : (term287 _89465 _89481 x f x') = (term320 _89465 _89481 x f x').
Proof. exact (@lem3453706 (term119 _89465 _89481 x f x')). Qed.
Lemma lem3453711 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) (h1 : term154 _89465 _89481 s x f x') : term320 _89465 _89481 x f x'.
Proof. exact (EQ_MP (@lem3453708 _89465 _89481 x f x') (@lem3453453 _89465 _89481 s x f x' h1)). Qed.
Lemma lem3453714 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) (h1 : term154 _89465 _89481 s x f x') : False.
Proof. exact (@lem3453711 _89465 _89481 s x f x' h1 (@lem3453703 _89465 _89481 s x f x' h1)). Qed.
Lemma lem3453715 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) (h1 : term154 _89465 _89481 s x f x') : term321.
Proof. exact (fun h0 : ~ False => @lem3453714 _89465 _89481 s x f x' h1). Qed.
Lemma lem3453717 (p : Prop) : (term295 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3453718 : term321 = False.
Proof. exact (@lem3453717 False). Qed.
Lemma lem3453719 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (x' : _89481) (h1 : term154 _89465 _89481 s x f x') : False.
Proof. exact (EQ_MP (@lem3453718) (@lem3453715 _89465 _89481 s x f x' h1)). Qed.
Lemma lem3453721 {_89465 _89481 : Type'} (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term207 _89465 _89481 x'' t s x f) : @IN _89481 x'' s.
Proof. exact (proj2 (@lem3453345 _89465 _89481 x'' t s x f h1)). Qed.
Lemma lem3453722 {_89465 _89481 : Type'} (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term207 _89465 _89481 x'' t s x f) : term296 _89481 x'' s.
Proof. exact (fun h0 : term98 _89481 x'' s => @lem3453721 _89465 _89481 x'' t s x f h1). Qed.
Lemma lem3453724 (p : Prop) : (term295 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3453725 {_89481 : Type'} (x'' : _89481) (s : _89481 -> Prop) : (term296 _89481 x'' s) = (@IN _89481 x'' s).
Proof. exact (@lem3453724 (@IN _89481 x'' s)). Qed.
Lemma lem3453726 {_89465 _89481 : Type'} (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term207 _89465 _89481 x'' t s x f) : @IN _89481 x'' s.
Proof. exact (EQ_MP (@lem3453725 _89481 x'' s) (@lem3453722 _89465 _89481 x'' t s x f h1)). Qed.
Lemma lem3453732 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3453733 {_89465 _89481 : Type'} (x : _89465) (f : type1470 _89465 _89481) (_36414 : _89481) (s : _89481 -> Prop) : (term120 _89465 _89481 s x f _36414) = (term322 _89465 _89481 x f _36414 s).
Proof. exact (@lem3453732 (term119 _89465 _89481 x f _36414) (term98 _89481 _36414 s)). Qed.
Lemma lem3453739 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3453740 {_89465 _89481 : Type'} (x : _89465) (f : type1470 _89465 _89481) (_36414 : _89481) (s : _89481 -> Prop) : (term323 _89465 _89481 s x f _36414) = (term324 _89465 _89481 x f _36414 s).
Proof. exact (MK_COMB (@lem3453739) (@lem3453733 _89465 _89481 x f _36414 s)). Qed.
Lemma lem3453746 {_89465 _89481 : Type'} (x : _89465) (f : type1470 _89465 _89481) (_36414 : _89481) (s : _89481 -> Prop) : (term322 _89465 _89481 x f _36414 s) = (term322 _89465 _89481 x f _36414 s).
Proof. exact (eq_refl (term322 _89465 _89481 x f _36414 s)). Qed.
Lemma lem3453747 {_89465 _89481 : Type'} (x : _89465) (f : type1470 _89465 _89481) (_36414 : _89481) (s : _89481 -> Prop) : ((term120 _89465 _89481 s x f _36414) = (term322 _89465 _89481 x f _36414 s)) = ((term322 _89465 _89481 x f _36414 s) = (term322 _89465 _89481 x f _36414 s)).
Proof. exact (MK_COMB (@lem3453740 _89465 _89481 x f _36414 s) (@lem3453746 _89465 _89481 x f _36414 s)). Qed.
Lemma lem3453749 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3453750 (x : Prop) : (x = x) = True.
Proof. exact (@lem3453749 Prop x). Qed.
Lemma lem3453751 {_89465 _89481 : Type'} (x : _89465) (f : type1470 _89465 _89481) (_36414 : _89481) (s : _89481 -> Prop) : ((term322 _89465 _89481 x f _36414 s) = (term322 _89465 _89481 x f _36414 s)) = True.
Proof. exact (@lem3453750 (term322 _89465 _89481 x f _36414 s)). Qed.
Lemma lem3453752 {_89465 _89481 : Type'} (x : _89465) (f : type1470 _89465 _89481) (_36414 : _89481) (s : _89481 -> Prop) : ((term120 _89465 _89481 s x f _36414) = (term322 _89465 _89481 x f _36414 s)) = True.
Proof. exact (TRANS (@lem3453747 _89465 _89481 x f _36414 s) (@lem3453751 _89465 _89481 x f _36414 s)). Qed.
Lemma lem3453753 {_89465 _89481 : Type'} (x : _89465) (f : type1470 _89465 _89481) (_36414 : _89481) (s : _89481 -> Prop) : True = ((term120 _89465 _89481 s x f _36414) = (term322 _89465 _89481 x f _36414 s)).
Proof. exact (SYM (@lem3453752 _89465 _89481 x f _36414 s)). Qed.
Lemma lem3453754 {_89465 _89481 : Type'} (x : _89465) (f : type1470 _89465 _89481) (_36414 : _89481) (s : _89481 -> Prop) : (term120 _89465 _89481 s x f _36414) = (term322 _89465 _89481 x f _36414 s).
Proof. exact (EQ_MP (@lem3453753 _89465 _89481 x f _36414 s) (@lem0)). Qed.
Lemma lem3453755 {_89465 _89481 : Type'} (_36414 : _89481) (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term207 _89465 _89481 x'' t s x f) : term322 _89465 _89481 x f _36414 s.
Proof. exact (EQ_MP (@lem3453754 _89465 _89481 x f _36414 s) (@lem3453493 _89465 _89481 _36414 x'' t s x f h1)). Qed.
Lemma lem3453757 (b : Prop) (a : Prop) : (a \/ b) = (term304 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3453758 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (_36414 : _89481) : (term322 _89465 _89481 x f _36414 s) = (term325 _89465 _89481 s x f _36414).
Proof. exact (@lem3453757 (term98 _89481 _36414 s) (term119 _89465 _89481 x f _36414)). Qed.
Lemma lem3453760 (a : Prop) : (term72 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3453761 {_89481 : Type'} (_36414 : _89481) (s : _89481 -> Prop) : (term313 _89481 _36414 s) = (@IN _89481 _36414 s).
Proof. exact (@lem3453760 (@IN _89481 _36414 s)). Qed.
Lemma lem3453762 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3453763 {_89481 : Type'} (_36414 : _89481) (s : _89481 -> Prop) : (term326 _89481 _36414 s) = (term327 _89481 _36414 s).
Proof. exact (MK_COMB (@lem3453762) (@lem3453761 _89481 _36414 s)). Qed.
Lemma lem3453764 {_89465 _89481 : Type'} (x : _89465) (f : type1470 _89465 _89481) (_36414 : _89481) : (term119 _89465 _89481 x f _36414) = (term119 _89465 _89481 x f _36414).
Proof. exact (eq_refl (term119 _89465 _89481 x f _36414)). Qed.
Lemma lem3453765 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (_36414 : _89481) : (term325 _89465 _89481 s x f _36414) = (term81 _89465 _89481 s x f _36414).
Proof. exact (MK_COMB (@lem3453763 _89481 _36414 s) (@lem3453764 _89465 _89481 x f _36414)). Qed.
Lemma lem3453766 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (_36414 : _89481) : (term322 _89465 _89481 x f _36414 s) = (term81 _89465 _89481 s x f _36414).
Proof. exact (TRANS (@lem3453758 _89465 _89481 s x f _36414) (@lem3453765 _89465 _89481 s x f _36414)). Qed.
Lemma lem3453769 {_89465 _89481 : Type'} (_36414 : _89481) (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term207 _89465 _89481 x'' t s x f) : term81 _89465 _89481 s x f _36414.
Proof. exact (EQ_MP (@lem3453766 _89465 _89481 s x f _36414) (@lem3453755 _89465 _89481 _36414 x'' t s x f h1)). Qed.
Lemma lem3453770 {_89465 _89481 : Type'} (_36414 : _89481) (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term207 _89465 _89481 x'' t s x f) : term81 _89465 _89481 s x f _36414.
Proof. exact (@lem3453769 _89465 _89481 _36414 x'' t s x f h1). Qed.
Lemma lem3453771 {_89465 _89481 : Type'} (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term207 _89465 _89481 x'' t s x f) : term81 _89465 _89481 s x f x''.
Proof. exact (@lem3453770 _89465 _89481 x'' x'' t s x f h1). Qed.
Lemma lem3453774 {_89465 _89481 : Type'} (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term207 _89465 _89481 x'' t s x f) : term119 _89465 _89481 x f x''.
Proof. exact (@lem3453771 _89465 _89481 x'' t s x f h1 (@lem3453726 _89465 _89481 x'' t s x f h1)). Qed.
Lemma lem3453775 {_89465 _89481 : Type'} (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term207 _89465 _89481 x'' t s x f) : term319 _89465 _89481 x f x''.
Proof. exact (fun h0 : term287 _89465 _89481 x f x'' => @lem3453774 _89465 _89481 x'' t s x f h1). Qed.
Lemma lem3453777 (p : Prop) : (term295 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3453778 {_89465 _89481 : Type'} (x : _89465) (f : type1470 _89465 _89481) (x'' : _89481) : (term319 _89465 _89481 x f x'') = (term119 _89465 _89481 x f x'').
Proof. exact (@lem3453777 (term119 _89465 _89481 x f x'')). Qed.
Lemma lem3453779 {_89465 _89481 : Type'} (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term207 _89465 _89481 x'' t s x f) : term119 _89465 _89481 x f x''.
Proof. exact (EQ_MP (@lem3453778 _89465 _89481 x f x'') (@lem3453775 _89465 _89481 x'' t s x f h1)). Qed.
Lemma lem3453782 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3453784 {_89465 _89481 : Type'} (x : _89465) (f : type1470 _89465 _89481) (x'' : _89481) : (term287 _89465 _89481 x f x'') = (term320 _89465 _89481 x f x'').
Proof. exact (@lem3453782 (term119 _89465 _89481 x f x'')). Qed.
Lemma lem3453787 {_89465 _89481 : Type'} (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term207 _89465 _89481 x'' t s x f) : term320 _89465 _89481 x f x''.
Proof. exact (EQ_MP (@lem3453784 _89465 _89481 x f x'') (@lem3453506 _89465 _89481 x'' t s x f h1)). Qed.
Lemma lem3453790 {_89465 _89481 : Type'} (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term207 _89465 _89481 x'' t s x f) : False.
Proof. exact (@lem3453787 _89465 _89481 x'' t s x f h1 (@lem3453779 _89465 _89481 x'' t s x f h1)). Qed.
Lemma lem3453791 {_89465 _89481 : Type'} (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term207 _89465 _89481 x'' t s x f) : term321.
Proof. exact (fun h0 : ~ False => @lem3453790 _89465 _89481 x'' t s x f h1). Qed.
Lemma lem3453793 (p : Prop) : (term295 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3453794 : term321 = False.
Proof. exact (@lem3453793 False). Qed.
Lemma lem3453796 {_89465 _89481 : Type'} (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term207 _89465 _89481 x'' t s x f) : False.
Proof. exact (EQ_MP (@lem3453794) (@lem3453791 _89465 _89481 x'' t s x f h1)). Qed.
Lemma lem3453797 {_89465 _89481 : Type'} (x' : _89481) (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term255 _89465 _89481 x' x'' t s x f) : False.
Proof. exact (or_elim (@lem3453335 _89465 _89481 x' x'' t s x f h1) (fun h0 : term154 _89465 _89481 s x f x' => @lem3453719 _89465 _89481 s x f x' h0) (fun h0 : term207 _89465 _89481 x'' t s x f => @lem3453796 _89465 _89481 x'' t s x f h0)). Qed.
Lemma lem3453798 {_89465 _89481 : Type'} (x' : _89481) (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term255 _89465 _89481 x' x'' t s x f) : (term255 _89465 _89481 x' x'' t s x f) = False.
Proof. exact (prop_ext (fun h2 : term255 _89465 _89481 x' x'' t s x f => @lem3453797 _89465 _89481 x' x'' t s x f h1) (fun h2 : False => @lem3453335 _89465 _89481 x' x'' t s x f h1)). Qed.
Lemma lem3453799 {_89465 _89481 : Type'} (x' : _89481) (x'' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term255 _89465 _89481 x' x'' t s x f) : False.
Proof. exact (EQ_MP (@lem3453798 _89465 _89481 x' x'' t s x f h1) (@lem3453335 _89465 _89481 x' x'' t s x f h1)). Qed.
Lemma lem3453800 {_89465 _89481 : Type'} (x' : _89481) (t : _89465 -> Prop) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term258 _89465 _89481 x' t s x f) : False.
Proof. exact (ex_elim (@lem3453229 _89465 _89481 x' t s x f h1) (fun x'' : _89481 => fun h0 : term257 _89465 _89481 x' t s x f x'' => @lem3453799 _89465 _89481 x' x'' t s x f h0)). Qed.
Lemma lem3453801 {_89465 _89481 : Type'} (x' : _89481) (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term260 _89465 _89481 x' s x f) : False.
Proof. exact (ex_elim (@lem3453228 _89465 _89481 x' s x f h1) (fun t : _89465 -> Prop => fun h0 : term259 _89465 _89481 x' s x f t => @lem3453800 _89465 _89481 x' t s x f h0)). Qed.
Lemma lem3453802 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term86 _89465 _89481 s x f) : False.
Proof. exact (ex_elim (@lem3453227 _89465 _89481 s x f h1) (fun x' : _89481 => fun h0 : term261 _89465 _89481 s x f x' => @lem3453801 _89465 _89481 x' s x f h0)). Qed.
Lemma lem3453803 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term86 _89465 _89481 s x f) : (term86 _89465 _89481 s x f) = False.
Proof. exact (prop_ext (fun h2 : term86 _89465 _89481 s x f => @lem3453802 _89465 _89481 s x f h1) (fun h2 : False => @lem3452665 _89465 _89481 s x f h1)). Qed.
Lemma lem3453804 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) (h1 : term86 _89465 _89481 s x f) : False.
Proof. exact (EQ_MP (@lem3453803 _89465 _89481 s x f h1) (@lem3452665 _89465 _89481 s x f h1)). Qed.
Lemma lem3453805 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : term85 _89465 _89481 s x f.
Proof. exact (fun h0 : term86 _89465 _89481 s x f => @lem3453804 _89465 _89481 s x f h0). Qed.
Lemma lem3453806 {_89465 _89481 : Type'} (s : _89481 -> Prop) (x : _89465) (f : type1470 _89465 _89481) : (term41 _89465 _89481 f s x) = (term47 _89465 _89481 s x f).
Proof. exact (EQ_MP (@lem3452664 _89465 _89481 s x f) (@lem3453805 _89465 _89481 s x f)). Qed.
Lemma lem3453811 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : term64 _89465 _89481 s f.
Proof. exact (fun x : _89465 => @lem3453806 _89465 _89481 s x f). Qed.
Lemma lem3453816 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) : term76 _89465 _89481 f.
Proof. exact (fun s : _89481 -> Prop => @lem3453811 _89465 _89481 s f). Qed.
Lemma lem3453821 {_89465 _89481 : Type'} : term80 _89465 _89481.
Proof. exact (fun f : type1470 _89465 _89481 => @lem3453816 _89465 _89481 f). Qed.
Lemma lem3453822 {_89465 _89481 : Type'} : term79 _89465 _89481.
Proof. exact (EQ_MP (@lem3452660 _89465 _89481) (@lem3453821 _89465 _89481)). Qed.
Lemma lem3453823 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) : term328 _89465 _89481 f.
Proof. exact (@lem3453822 _89465 _89481 f). Qed.
Lemma lem3453824 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) : (term328 _89465 _89481 f) = (term75 _89465 _89481 f).
Proof. exact (eq_refl (term328 _89465 _89481 f)). Qed.
Lemma lem3453825 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) : term75 _89465 _89481 f.
Proof. exact (EQ_MP (@lem3453824 _89465 _89481 f) (@lem3453823 _89465 _89481 f)). Qed.
Lemma lem3453826 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) (s : _89481 -> Prop) : term329 _89465 _89481 f s.
Proof. exact (@lem3453825 _89465 _89481 f s). Qed.
Lemma lem3453827 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : (term329 _89465 _89481 f s) = (term66 _89465 _89481 s f).
Proof. exact (eq_refl (term329 _89465 _89481 f s)). Qed.
Lemma lem3453828 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : term66 _89465 _89481 s f.
Proof. exact (EQ_MP (@lem3453827 _89465 _89481 s f) (@lem3453826 _89465 _89481 f s)). Qed.
Lemma lem3453830 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : term66 _89465 _89481 s f.
Proof. exact (@lem3452480 _89465 _89481 s f (@lem3453828 _89465 _89481 s f)). Qed.
Lemma lem3453831 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) (h1 : term67 _89465 _89481 s f) : False.
Proof. exact (@lem3453830 _89465 _89481 s f (@lem3452464 _89465 _89481 s f h1)). Qed.
Lemma lem3453832 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) (h1 : term67 _89465 _89481 s f) : (term67 _89465 _89481 s f) = False.
Proof. exact (prop_ext (fun h2 : term67 _89465 _89481 s f => @lem3453831 _89465 _89481 s f h1) (fun h2 : False => @lem3452464 _89465 _89481 s f h1)). Qed.
Lemma lem3453833 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) (h1 : term67 _89465 _89481 s f) : False.
Proof. exact (EQ_MP (@lem3453832 _89465 _89481 s f h1) (@lem3452464 _89465 _89481 s f h1)). Qed.
Lemma lem3453834 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : term66 _89465 _89481 s f.
Proof. exact (fun h0 : term67 _89465 _89481 s f => @lem3453833 _89465 _89481 s f h0). Qed.
Lemma lem3453835 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : term64 _89465 _89481 s f.
Proof. exact (EQ_MP (@lem3452463 _89465 _89481 s f) (@lem3453834 _89465 _89481 s f)). Qed.
Lemma lem3453836 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : term30 _89465 _89481 s f.
Proof. exact (EQ_MP (@lem3452459 _89465 _89481 s f) (@lem3453835 _89465 _89481 s f)). Qed.
Lemma lem3453837 {_89465 _89481 : Type'} (s : _89481 -> Prop) (f : type1470 _89465 _89481) : (term28 _89465 _89481 f s) = (term29 _89465 _89481 s f).
Proof. exact (EQ_MP (@lem3452376 _89465 _89481 s f) (@lem3453836 _89465 _89481 s f)). Qed.
Lemma lem3453842 {_89465 _89481 : Type'} (f : type1470 _89465 _89481) : term330 _89465 _89481 f.
Proof. exact (fun s : _89481 -> Prop => @lem3453837 _89465 _89481 s f). Qed.
Lemma lem3453847 {_89465 _89481 : Type'} : term331 _89465 _89481.
Proof. exact (fun f : type1470 _89465 _89481 => @lem3453842 _89465 _89481 f). Qed.
