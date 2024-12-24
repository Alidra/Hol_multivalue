Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_POS_LE_term_abbrevs.
Require Import EXCLUDED_MIDDLE_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import SUM_0_spec.
Require Import SUM_DEGENERATE_spec.
Require Import SUM_LE_spec.
Require Import SUM_SUPPORT_spec.
Require Import support_spec.
Require Import thm0_spec.
Require Import thm1339240_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm7064171_spec.
Require Import thm7065437_spec.
Require Import thm82_spec.
Lemma lem7085324 {A : Type'} : term0 A.
Proof. exact (@lem7071845 A). Qed.
Lemma lem7085325 {A : Type'} : term1 A.
Proof. exact (@lem7085324 A (term2 A)). Qed.
Lemma lem7085326 {A : Type'} : (term1 A) = (term3 A).
Proof. exact (eq_refl (term1 A)). Qed.
Lemma lem7085327 {A : Type'} : term3 A.
Proof. exact (EQ_MP (@lem7085326 A) (@lem7085325 A)). Qed.
Lemma lem7085328 {A : Type'} (f : A -> real) : term4 A f.
Proof. exact (@lem7085327 A f). Qed.
Lemma lem7085329 {A : Type'} (f : A -> real) : (term4 A f) = (term5 A f).
Proof. exact (eq_refl (term4 A f)). Qed.
Lemma lem7085330 {A : Type'} (f : A -> real) : term5 A f.
Proof. exact (EQ_MP (@lem7085329 A f) (@lem7085328 A f)). Qed.
Lemma lem7085331 {A : Type'} (s : A -> Prop) (f : A -> real) : term6 A s f.
Proof. exact (@lem7085330 A f (term7 A s f)). Qed.
Lemma lem7085332 {A : Type'} (s : A -> Prop) (f : A -> real) : (term6 A s f) = (term8 A s f).
Proof. exact (eq_refl (term6 A s f)). Qed.
Lemma lem7085333 {A : Type'} (s : A -> Prop) (f : A -> real) : term8 A s f.
Proof. exact (EQ_MP (@lem7085332 A s f) (@lem7085331 A s f)). Qed.
Lemma lem7085334 {A B : Type'} (s : A -> Prop) : term9 A B s.
Proof. exact (@lem5716761 A B s). Qed.
Lemma lem7085335 {A B : Type'} (s : A -> Prop) : (term9 A B s) = (term10 A B s).
Proof. exact (eq_refl (term9 A B s)). Qed.
Lemma lem7085336 {A B : Type'} (s : A -> Prop) : term10 A B s.
Proof. exact (EQ_MP (@lem7085335 A B s) (@lem7085334 A B s)). Qed.
Lemma lem7085337 {A B : Type'} (s : A -> Prop) (f : A -> B) : term11 A B s f.
Proof. exact (@lem7085336 A B s f). Qed.
Lemma lem7085338 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term11 A B s f) = (term12 A B s f).
Proof. exact (eq_refl (term11 A B s f)). Qed.
Lemma lem7085339 {A B : Type'} (s : A -> Prop) (f : A -> B) : term12 A B s f.
Proof. exact (EQ_MP (@lem7085338 A B s f) (@lem7085337 A B s f)). Qed.
Lemma lem7085340 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : term13 A B s f op.
Proof. exact (@lem7085339 A B s f op). Qed.
Lemma lem7085341 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term13 A B s f op) = ((@support A B op f s) = (term14 A B s f op)).
Proof. exact (eq_refl (term13 A B s f op)). Qed.
Lemma lem7085345 {_131679 : Type'} (s : _131679 -> Prop) (f : _131679 -> real) (h1 : (term15 _131679 s f) = (@sum _131679 s f)) : (term15 _131679 s f) = (@sum _131679 s f).
Proof. exact (h1). Qed.
Lemma lem7085346 {_131679 : Type'} (s : _131679 -> Prop) (f : _131679 -> real) (h1 : (term15 _131679 s f) = (@sum _131679 s f)) : (@sum _131679 s f) = (term15 _131679 s f).
Proof. exact (SYM (@lem7085345 _131679 s f h1)). Qed.
Lemma lem7085347 {_131679 : Type'} (s : _131679 -> Prop) (f : _131679 -> real) (h1 : (@sum _131679 s f) = (term15 _131679 s f)) : (@sum _131679 s f) = (term15 _131679 s f).
Proof. exact (h1). Qed.
Lemma lem7085348 {_131679 : Type'} (s : _131679 -> Prop) (f : _131679 -> real) (h1 : (@sum _131679 s f) = (term15 _131679 s f)) : (term15 _131679 s f) = (@sum _131679 s f).
Proof. exact (SYM (@lem7085347 _131679 s f h1)). Qed.
Lemma lem7085349 {_131679 : Type'} (s : _131679 -> Prop) (f : _131679 -> real) : ((term15 _131679 s f) = (@sum _131679 s f)) = ((@sum _131679 s f) = (term15 _131679 s f)).
Proof. exact (prop_ext (fun h1 : (term15 _131679 s f) = (@sum _131679 s f) => @lem7085346 _131679 s f h1) (fun h1 : (@sum _131679 s f) = (term15 _131679 s f) => @lem7085348 _131679 s f h1)). Qed.
Lemma lem7085350 {_131679 : Type'} (f : _131679 -> real) : (term16 _131679 f) = (term17 _131679 f).
Proof. exact (fun_ext (fun s : _131679 -> Prop => @lem7085349 _131679 s f)). Qed.
Lemma lem7085351 {_131679 : Type'} : (@all (_131679 -> Prop)) = (@all (_131679 -> Prop)).
Proof. exact (eq_refl (@all (_131679 -> Prop))). Qed.
Lemma lem7085352 {_131679 : Type'} (f : _131679 -> real) : (term18 _131679 f) = (term19 _131679 f).
Proof. exact (MK_COMB (@lem7085351 _131679) (@lem7085350 _131679 f)). Qed.
Lemma lem7085353 {_131679 : Type'} : (term20 _131679) = (term21 _131679).
Proof. exact (fun_ext (fun f : _131679 -> real => @lem7085352 _131679 f)). Qed.
Lemma lem7085354 {_131679 : Type'} : (@all (_131679 -> real)) = (@all (_131679 -> real)).
Proof. exact (eq_refl (@all (_131679 -> real))). Qed.
Lemma lem7085355 {_131679 : Type'} : (term22 _131679) = (term23 _131679).
Proof. exact (MK_COMB (@lem7085354 _131679) (@lem7085353 _131679)). Qed.
Lemma lem7085356 {_131679 : Type'} : term23 _131679.
Proof. exact (EQ_MP (@lem7085355 _131679) (@lem7068649 _131679)). Qed.
Lemma lem7085357 {_131679 : Type'} (f : _131679 -> real) : term24 _131679 f.
Proof. exact (@lem7085356 _131679 f). Qed.
Lemma lem7085358 {_131679 : Type'} (f : _131679 -> real) : (term24 _131679 f) = (term19 _131679 f).
Proof. exact (eq_refl (term24 _131679 f)). Qed.
Lemma lem7085359 {_131679 : Type'} (f : _131679 -> real) : term19 _131679 f.
Proof. exact (EQ_MP (@lem7085358 _131679 f) (@lem7085357 _131679 f)). Qed.
Lemma lem7085360 {_131679 : Type'} (f : _131679 -> real) (s : _131679 -> Prop) : term25 _131679 f s.
Proof. exact (@lem7085359 _131679 f s). Qed.
Lemma lem7085361 {_131679 : Type'} (s : _131679 -> Prop) (f : _131679 -> real) : (term25 _131679 f s) = ((@sum _131679 s f) = (term15 _131679 s f)).
Proof. exact (eq_refl (term25 _131679 f s)). Qed.
Lemma lem7085363 {A : Type'} (s : A -> Prop) (f : A -> real) : term26 A s f.
Proof. exact (@lem9784 (term27 A s f)). Qed.
Lemma lem7085364 {A : Type'} (s : A -> Prop) (f : A -> real) : (term26 A s f) = (term28 A s f).
Proof. exact (eq_refl (term26 A s f)). Qed.
Lemma lem7085365 {A : Type'} (s : A -> Prop) (f : A -> real) : term28 A s f.
Proof. exact (EQ_MP (@lem7085364 A s f) (@lem7085363 A s f)). Qed.
Lemma lem7085366 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term27 A s f) : term27 A s f.
Proof. exact (h1). Qed.
Lemma lem7085367 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term29 A s f) : term29 A s f.
Proof. exact (h1). Qed.
Lemma lem7085368 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) : term30 A s f.
Proof. exact (h1). Qed.
Lemma lem7085417 (x : real) : term31 x.
Proof. exact (@lem1339240 x). Qed.
Lemma lem7085418 (x : real) : (term31 x) = (real_le x x).
Proof. exact (eq_refl (term31 x)). Qed.
Lemma lem7085419 (x : real) : real_le x x.
Proof. exact (EQ_MP (@lem7085418 x) (@lem7085417 x)). Qed.
Lemma lem7085420 (x : real) : (real_le x x) = ((real_le x x) = True).
Proof. exact (@lem7 (real_le x x)). Qed.
Lemma lem7085422 {_131446 : Type'} (f : _131446 -> real) : term32 _131446 f.
Proof. exact (@lem7067459 _131446 f). Qed.
Lemma lem7085423 {_131446 : Type'} (f : _131446 -> real) : (term32 _131446 f) = (term33 _131446 f).
Proof. exact (eq_refl (term32 _131446 f)). Qed.
Lemma lem7085424 {_131446 : Type'} (f : _131446 -> real) : term33 _131446 f.
Proof. exact (EQ_MP (@lem7085423 _131446 f) (@lem7085422 _131446 f)). Qed.
Lemma lem7085425 {_131446 : Type'} (f : _131446 -> real) (s : _131446 -> Prop) : term34 _131446 f s.
Proof. exact (@lem7085424 _131446 f s). Qed.
Lemma lem7085426 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : (term34 _131446 f s) = (term35 _131446 s f).
Proof. exact (eq_refl (term34 _131446 f s)). Qed.
Lemma lem7085427 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : term35 _131446 s f.
Proof. exact (EQ_MP (@lem7085426 _131446 s f) (@lem7085425 _131446 f s)). Qed.
Lemma lem7085428 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) (h1 : term29 _131446 s f) : term29 _131446 s f.
Proof. exact (h1). Qed.
Lemma lem7085429 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) (h1 : term29 _131446 s f) : (@sum _131446 s f) = term36.
Proof. exact (@lem7085427 _131446 s f (@lem7085428 _131446 s f h1)). Qed.
Lemma lem7085447 {A : Type'} (s : A -> Prop) (f : A -> real) : term37 A s f.
Proof. exact (@lem82 (term27 A s f)). Qed.
Lemma lem7085452 {_131446 : Type'} (s : _131446 -> Prop) (f : _131446 -> real) : term35 _131446 s f.
Proof. exact (fun h0 : term29 _131446 s f => @lem7085429 _131446 s f h0). Qed.
Lemma lem7085453 {A : Type'} (s : A -> Prop) (f : A -> real) : term35 A s f.
Proof. exact (@lem7085452 A s f). Qed.
Lemma lem7085455 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term29 A s f) : (term27 A s f) = False.
Proof. exact (@lem7085447 A s f (@lem7085367 A s f h1)). Qed.
Lemma lem7085456 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term29 A s f) : (term27 A s f) = False.
Proof. exact (@lem7085455 A s f h1). Qed.
Lemma lem7085457 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7085458 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term29 A s f) : (term29 A s f) = (~ False).
Proof. exact (MK_COMB (@lem7085457) (@lem7085456 A s f h1)). Qed.
Lemma lem7085460 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem7085461 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term29 A s f) : (term29 A s f) = True.
Proof. exact (TRANS (@lem7085458 A s f h1) (@lem7085460)). Qed.
Lemma lem7085462 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term29 A s f) : True = (term29 A s f).
Proof. exact (SYM (@lem7085461 A s f h1)). Qed.
Lemma lem7085463 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term29 A s f) : term29 A s f.
Proof. exact (EQ_MP (@lem7085462 A s f h1) (@lem0)). Qed.
Lemma lem7085464 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term29 A s f) : (@sum A s f) = term36.
Proof. exact (@lem7085453 A s f (@lem7085463 A s f h1)). Qed.
Lemma lem7085465 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem7085466 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term29 A s f) : (term39 A s f) = term40.
Proof. exact (MK_COMB (@lem7085465) (@lem7085464 A s f h1)). Qed.
Lemma lem7085468 (x : real) : (real_le x x) = True.
Proof. exact (EQ_MP (@lem7085420 x) (@lem7085419 x)). Qed.
Lemma lem7085469 : term40 = True.
Proof. exact (@lem7085468 term36). Qed.
Lemma lem7085470 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term29 A s f) : (term39 A s f) = True.
Proof. exact (TRANS (@lem7085466 A s f h1) (@lem7085469)). Qed.
Lemma lem7085471 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term29 A s f) : True = (term39 A s f).
Proof. exact (SYM (@lem7085470 A s f h1)). Qed.
Lemma lem7085472 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term29 A s f) : term39 A s f.
Proof. exact (EQ_MP (@lem7085471 A s f h1) (@lem0)). Qed.
Lemma lem7085474 {_131679 : Type'} (s : _131679 -> Prop) (f : _131679 -> real) : (@sum _131679 s f) = (term15 _131679 s f).
Proof. exact (EQ_MP (@lem7085361 _131679 s f) (@lem7085360 _131679 f s)). Qed.
Lemma lem7085475 {A : Type'} (s : A -> Prop) (f : A -> real) : (@sum A s f) = (term15 A s f).
Proof. exact (@lem7085474 A s f). Qed.
Lemma lem7085476 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem7085477 {A : Type'} (s : A -> Prop) (f : A -> real) : (term39 A s f) = (term41 A s f).
Proof. exact (MK_COMB (@lem7085476) (@lem7085475 A s f)). Qed.
Lemma lem7085478 {A : Type'} (s : A -> Prop) (f : A -> real) : (term41 A s f) = (term39 A s f).
Proof. exact (SYM (@lem7085477 A s f)). Qed.
Lemma lem7085480 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@support A B op f s) = (term14 A B s f op).
Proof. exact (EQ_MP (@lem7085341 A B s f op) (@lem7085340 A B s f op)). Qed.
Lemma lem7085481 {A : Type'} (s : A -> Prop) (f : A -> real) (op : type1627) : (@support A real op f s) = (term42 A s f op).
Proof. exact (@lem7085480 A real s f op). Qed.
Lemma lem7085482 {A : Type'} (s : A -> Prop) (f : A -> real) : (@support A real real_add f s) = (term43 A s f).
Proof. exact (@lem7085481 A s f real_add). Qed.
Lemma lem7085492 : (@neutral real real_add) = term36.
Proof. exact (EQ_MP (@lem7064171) (@lem7065437)). Qed.
Lemma lem7085493 {A : Type'} (f : A -> real) (x : A) : (term44 A f x) = (term44 A f x).
Proof. exact (eq_refl (term44 A f x)). Qed.
Lemma lem7085494 {A : Type'} (f : A -> real) (x : A) : ((f x) = (@neutral real real_add)) = ((f x) = term36).
Proof. exact (MK_COMB (@lem7085493 A f x) (@lem7085492)). Qed.
Lemma lem7085497 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7085498 {A : Type'} (f : A -> real) (x : A) : (term45 A f x) = (term46 A f x).
Proof. exact (MK_COMB (@lem7085497) (@lem7085494 A f x)). Qed.
Lemma lem7085499 {A : Type'} (x : A) (s : A -> Prop) : (term47 A x s) = (term47 A x s).
Proof. exact (eq_refl (term47 A x s)). Qed.
Lemma lem7085500 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term48 A s f x) = (term49 A s f x).
Proof. exact (MK_COMB (@lem7085499 A x s) (@lem7085498 A f x)). Qed.
Lemma lem7085503 {A : Type'} (GEN_PVAR_237 : A) : (@SETSPEC A GEN_PVAR_237) = (@SETSPEC A GEN_PVAR_237).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_237)). Qed.
Lemma lem7085504 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> real) (x : A) : (term50 A GEN_PVAR_237 s f x) = (term51 A GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem7085503 A GEN_PVAR_237) (@lem7085500 A s f x)). Qed.
Lemma lem7085505 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7085506 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> real) (x : A) : (term52 A GEN_PVAR_237 s f x) = (term53 A GEN_PVAR_237 s f x).
Proof. exact (MK_COMB (@lem7085504 A GEN_PVAR_237 s f x) (@lem7085505 A x)). Qed.
Lemma lem7085507 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> real) : (term54 A GEN_PVAR_237 s f) = (term55 A GEN_PVAR_237 s f).
Proof. exact (fun_ext (fun x : A => @lem7085506 A GEN_PVAR_237 s f x)). Qed.
Lemma lem7085508 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7085509 {A : Type'} (GEN_PVAR_237 : A) (s : A -> Prop) (f : A -> real) : (term56 A GEN_PVAR_237 s f) = (term57 A GEN_PVAR_237 s f).
Proof. exact (MK_COMB (@lem7085508 A) (@lem7085507 A GEN_PVAR_237 s f)). Qed.
Lemma lem7085514 {A : Type'} (s : A -> Prop) (f : A -> real) : (term58 A s f) = (term59 A s f).
Proof. exact (fun_ext (fun GEN_PVAR_237 : A => @lem7085509 A GEN_PVAR_237 s f)). Qed.
Lemma lem7085515 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem7085516 {A : Type'} (s : A -> Prop) (f : A -> real) : (term43 A s f) = (term7 A s f).
Proof. exact (MK_COMB (@lem7085515 A) (@lem7085514 A s f)). Qed.
Lemma lem7085517 {A : Type'} (s : A -> Prop) (f : A -> real) : (@support A real real_add f s) = (term7 A s f).
Proof. exact (TRANS (@lem7085482 A s f) (@lem7085516 A s f)). Qed.
Lemma lem7085518 {A : Type'} : (@sum A) = (@sum A).
Proof. exact (eq_refl (@sum A)). Qed.
Lemma lem7085519 {A : Type'} (s : A -> Prop) (f : A -> real) : (term60 A f s) = (term61 A s f).
Proof. exact (MK_COMB (@lem7085518 A) (@lem7085517 A s f)). Qed.
Lemma lem7085520 {A : Type'} (f : A -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7085521 {A : Type'} (s : A -> Prop) (f : A -> real) : (term15 A s f) = (term62 A s f).
Proof. exact (MK_COMB (@lem7085519 A s f) (@lem7085520 A f)). Qed.
Lemma lem7085522 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem7085523 {A : Type'} (s : A -> Prop) (f : A -> real) : (term41 A s f) = (term63 A s f).
Proof. exact (MK_COMB (@lem7085522) (@lem7085521 A s f)). Qed.
Lemma lem7085524 {A : Type'} (s : A -> Prop) (f : A -> real) : (term63 A s f) = (term41 A s f).
Proof. exact (SYM (@lem7085523 A s f)). Qed.
Lemma lem7085549 {_83095 : Type'} : term64 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem7085550 {_83095 : Type'} (p : _83095 -> Prop) : term65 _83095 p.
Proof. exact (@lem7085549 _83095 p). Qed.
Lemma lem7085551 {_83095 : Type'} (p : _83095 -> Prop) : (term65 _83095 p) = (term66 _83095 p).
Proof. exact (eq_refl (term65 _83095 p)). Qed.
Lemma lem7085552 {_83095 : Type'} (p : _83095 -> Prop) : term66 _83095 p.
Proof. exact (EQ_MP (@lem7085551 _83095 p) (@lem7085550 _83095 p)). Qed.
Lemma lem7085553 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term67 _83095 p x.
Proof. exact (@lem7085552 _83095 p x). Qed.
Lemma lem7085554 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term67 _83095 p x) = ((term68 _83095 x p) = (p x)).
Proof. exact (eq_refl (term67 _83095 p x)). Qed.
Lemma lem7085563 {A : Type'} (s : A -> Prop) : term69 A s.
Proof. exact (@lem7069399 A s). Qed.
Lemma lem7085564 {A : Type'} (s : A -> Prop) : (term69 A s) = ((term70 A s) = term36).
Proof. exact (eq_refl (term69 A s)). Qed.
Lemma lem7085566 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) : term71 A s f x.
Proof. exact (@lem7085368 A s f h1 x). Qed.
Lemma lem7085567 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term71 A s f x) = (term72 A s f x).
Proof. exact (eq_refl (term71 A s f x)). Qed.
Lemma lem7085568 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) : term72 A s f x.
Proof. exact (EQ_MP (@lem7085567 A s f x) (@lem7085566 A x s f h1)). Qed.
Lemma lem7085569 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem7085570 {A : Type'} (f : A -> real) (x : A) (s : A -> Prop) (h1 : term30 A s f) (h2 : @IN A x s) : term73 A f x.
Proof. exact (@lem7085568 A x s f h1 (@lem7085569 A x s h2)). Qed.
Lemma lem7085571 {A : Type'} (f : A -> real) (x : A) : (term73 A f x) = ((term73 A f x) = True).
Proof. exact (@lem7 (term73 A f x)). Qed.
Lemma lem7085572 {A : Type'} (f : A -> real) (x : A) (s : A -> Prop) (h1 : term30 A s f) (h2 : @IN A x s) : (term73 A f x) = True.
Proof. exact (EQ_MP (@lem7085571 A f x) (@lem7085570 A f x s h1 h2)). Qed.
Lemma lem7085578 {A : Type'} (s : A -> Prop) (f : A -> real) : (term27 A s f) = ((term27 A s f) = True).
Proof. exact (@lem7 (term27 A s f)). Qed.
Lemma lem7085583 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term74 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7085584 (p : Prop) (q : Prop) (p' : Prop) : term75 p q p'.
Proof. exact (fun q' : Prop => @lem7085583 p q p' q'). Qed.
Lemma lem7085585 (p : Prop) (q : Prop) : term76 p q.
Proof. exact (fun p' : Prop => @lem7085584 p q p'). Qed.
Lemma lem7085586 {A : Type'} (s : A -> Prop) (f : A -> real) : term77 A s f.
Proof. exact (@lem7085585 (term8 A s f) (term63 A s f)). Qed.
Lemma lem7085587 {A : Type'} (s : A -> Prop) (f : A -> real) (p' : Prop) : term78 A s f p'.
Proof. exact (@lem7085586 A s f p'). Qed.
Lemma lem7085588 {A : Type'} (s : A -> Prop) (f : A -> real) (p' : Prop) : (term78 A s f p') = (term79 A s f p').
Proof. exact (eq_refl (term78 A s f p')). Qed.
Lemma lem7085589 {A : Type'} (s : A -> Prop) (f : A -> real) (p' : Prop) : term79 A s f p'.
Proof. exact (EQ_MP (@lem7085588 A s f p') (@lem7085587 A s f p')). Qed.
Lemma lem7085590 {A : Type'} (s : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : term80 A s f p' q'.
Proof. exact (@lem7085589 A s f p' q'). Qed.
Lemma lem7085591 {A : Type'} (s : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : (term80 A s f p' q') = (term81 A s f p' q').
Proof. exact (eq_refl (term80 A s f p' q')). Qed.
Lemma lem7085592 {A : Type'} (s : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : term81 A s f p' q'.
Proof. exact (EQ_MP (@lem7085591 A s f p' q') (@lem7085590 A s f p' q')). Qed.
Lemma lem7085596 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term74 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7085597 (p : Prop) (q : Prop) (p' : Prop) : term75 p q p'.
Proof. exact (fun q' : Prop => @lem7085596 p q p' q'). Qed.
Lemma lem7085598 (p : Prop) (q : Prop) : term76 p q.
Proof. exact (fun p' : Prop => @lem7085597 p q p'). Qed.
Lemma lem7085599 {A : Type'} (s : A -> Prop) (f : A -> real) : term82 A s f.
Proof. exact (@lem7085598 (term83 A s f) (term84 A s f)). Qed.
Lemma lem7085600 {A : Type'} (s : A -> Prop) (f : A -> real) (p' : Prop) : term85 A s f p'.
Proof. exact (@lem7085599 A s f p'). Qed.
Lemma lem7085601 {A : Type'} (s : A -> Prop) (f : A -> real) (p' : Prop) : (term85 A s f p') = (term86 A s f p').
Proof. exact (eq_refl (term85 A s f p')). Qed.
Lemma lem7085602 {A : Type'} (s : A -> Prop) (f : A -> real) (p' : Prop) : term86 A s f p'.
Proof. exact (EQ_MP (@lem7085601 A s f p') (@lem7085600 A s f p')). Qed.
Lemma lem7085603 {A : Type'} (s : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : term87 A s f p' q'.
Proof. exact (@lem7085602 A s f p' q'). Qed.
Lemma lem7085604 {A : Type'} (s : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : (term87 A s f p' q') = (term88 A s f p' q').
Proof. exact (eq_refl (term87 A s f p' q')). Qed.
Lemma lem7085605 {A : Type'} (s : A -> Prop) (f : A -> real) (p' : Prop) (q' : Prop) : term88 A s f p' q'.
Proof. exact (EQ_MP (@lem7085604 A s f p' q') (@lem7085603 A s f p' q')). Qed.
Lemma lem7085609 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term27 A s f) : (term27 A s f) = True.
Proof. exact (EQ_MP (@lem7085578 A s f) (@lem7085366 A s f h1)). Qed.
Lemma lem7085610 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term27 A s f) : (term27 A s f) = True.
Proof. exact (@lem7085609 A s f h1). Qed.
Lemma lem7085611 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7085612 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term27 A s f) : (term89 A s f) = (and True).
Proof. exact (MK_COMB (@lem7085611) (@lem7085610 A s f h1)). Qed.
Lemma lem7085620 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term74 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7085621 (p : Prop) (q : Prop) (p' : Prop) : term75 p q p'.
Proof. exact (fun q' : Prop => @lem7085620 p q p' q'). Qed.
Lemma lem7085622 (p : Prop) (q : Prop) : term76 p q.
Proof. exact (fun p' : Prop => @lem7085621 p q p'). Qed.
Lemma lem7085623 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : term90 A s f x.
Proof. exact (@lem7085622 (term91 A x s f) (term92 A f x)). Qed.
Lemma lem7085624 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (p' : Prop) : term93 A s f x p'.
Proof. exact (@lem7085623 A s f x p'). Qed.
Lemma lem7085625 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (p' : Prop) : (term93 A s f x p') = (term94 A s f x p').
Proof. exact (eq_refl (term93 A s f x p')). Qed.
Lemma lem7085626 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (p' : Prop) : term94 A s f x p'.
Proof. exact (EQ_MP (@lem7085625 A s f x p') (@lem7085624 A s f x p')). Qed.
Lemma lem7085627 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : term95 A s f x p' q'.
Proof. exact (@lem7085626 A s f x p' q'). Qed.
Lemma lem7085628 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : (term95 A s f x p' q') = (term96 A s f x p' q').
Proof. exact (eq_refl (term95 A s f x p' q')). Qed.
Lemma lem7085629 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (p' : Prop) (q' : Prop) : term96 A s f x p' q'.
Proof. exact (EQ_MP (@lem7085628 A s f x p' q') (@lem7085627 A s f x p' q')). Qed.
Lemma lem7085631 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term68 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem7085554 _83095 p x) (@lem7085553 _83095 p x)). Qed.
Lemma lem7085632 {A : Type'} (p : A -> Prop) (x : A) : (term68 A x p) = (p x).
Proof. exact (@lem7085631 A p x). Qed.
Lemma lem7085633 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term97 A x s f) = (term98 A s f x).
Proof. exact (@lem7085632 A (term99 A s f) x). Qed.
Lemma lem7085634 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term98 A s f x) = (term49 A s f x).
Proof. exact (eq_refl (term98 A s f x)). Qed.
Lemma lem7085635 {A : Type'} (GEN_PVAR_314 : A) : (@SETSPEC A GEN_PVAR_314) = (@SETSPEC A GEN_PVAR_314).
Proof. exact (eq_refl (@SETSPEC A GEN_PVAR_314)). Qed.
Lemma lem7085636 {A : Type'} (GEN_PVAR_314 : A) (s : A -> Prop) (f : A -> real) (x : A) : (term100 A GEN_PVAR_314 s f x) = (term51 A GEN_PVAR_314 s f x).
Proof. exact (MK_COMB (@lem7085635 A GEN_PVAR_314) (@lem7085634 A s f x)). Qed.
Lemma lem7085637 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7085638 {A : Type'} (GEN_PVAR_314 : A) (s : A -> Prop) (f : A -> real) (x : A) : (term101 A GEN_PVAR_314 s f x) = (term53 A GEN_PVAR_314 s f x).
Proof. exact (MK_COMB (@lem7085636 A GEN_PVAR_314 s f x) (@lem7085637 A x)). Qed.
Lemma lem7085639 {A : Type'} (GEN_PVAR_314 : A) (s : A -> Prop) (f : A -> real) : (term102 A GEN_PVAR_314 s f) = (term55 A GEN_PVAR_314 s f).
Proof. exact (fun_ext (fun x : A => @lem7085638 A GEN_PVAR_314 s f x)). Qed.
Lemma lem7085640 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7085641 {A : Type'} (GEN_PVAR_314 : A) (s : A -> Prop) (f : A -> real) : (term103 A GEN_PVAR_314 s f) = (term57 A GEN_PVAR_314 s f).
Proof. exact (MK_COMB (@lem7085640 A) (@lem7085639 A GEN_PVAR_314 s f)). Qed.
Lemma lem7085642 {A : Type'} (s : A -> Prop) (f : A -> real) : (term104 A s f) = (term59 A s f).
Proof. exact (fun_ext (fun GEN_PVAR_314 : A => @lem7085641 A GEN_PVAR_314 s f)). Qed.
Lemma lem7085643 {A : Type'} : (@GSPEC A) = (@GSPEC A).
Proof. exact (eq_refl (@GSPEC A)). Qed.
Lemma lem7085644 {A : Type'} (s : A -> Prop) (f : A -> real) : (term105 A s f) = (term7 A s f).
Proof. exact (MK_COMB (@lem7085643 A) (@lem7085642 A s f)). Qed.
Lemma lem7085645 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem7085646 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term97 A x s f) = (term91 A x s f).
Proof. exact (MK_COMB (@lem7085645 A x) (@lem7085644 A s f)). Qed.
Lemma lem7085647 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7085648 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term106 A x s f) = (term107 A x s f).
Proof. exact (MK_COMB (@lem7085647) (@lem7085646 A x s f)). Qed.
Lemma lem7085649 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term98 A s f x) = (term49 A s f x).
Proof. exact (eq_refl (term98 A s f x)). Qed.
Lemma lem7085650 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : ((term97 A x s f) = (term98 A s f x)) = ((term91 A x s f) = (term49 A s f x)).
Proof. exact (MK_COMB (@lem7085648 A x s f) (@lem7085649 A s f x)). Qed.
Lemma lem7085651 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term91 A x s f) = (term49 A s f x).
Proof. exact (EQ_MP (@lem7085650 A s f x) (@lem7085633 A s f x)). Qed.
Lemma lem7085656 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (q' : Prop) : term108 A s f x q'.
Proof. exact (@lem7085629 A s f x (term49 A s f x) q'). Qed.
Lemma lem7085657 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (q' : Prop) : term109 A s f x q'.
Proof. exact (@lem7085656 A s f x q' (@lem7085651 A s f x)). Qed.
Lemma lem7085658 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term49 A s f x) : term49 A s f x.
Proof. exact (h1). Qed.
Lemma lem7085673 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term49 A s f x) : @IN A x s.
Proof. exact (proj1 (@lem7085658 A s f x h1)). Qed.
Lemma lem7085674 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = ((@IN A x s) = True).
Proof. exact (@lem7 (@IN A x s)). Qed.
Lemma lem7085677 {A B : Type'} (f : A -> B) (y : A) : (term110 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7085678 {A : Type'} (f : A -> real) (y : A) : (term111 A f y) = (f y).
Proof. exact (@lem7085677 A real f y). Qed.
Lemma lem7085679 {A : Type'} (x : A) : (term112 A x) = (term113 A x).
Proof. exact (@lem7085678 A (term2 A) x). Qed.
Lemma lem7085680 {A : Type'} (x : A) : (term113 A x) = term36.
Proof. exact (eq_refl (term113 A x)). Qed.
Lemma lem7085681 {A : Type'} : (term114 A) = (term2 A).
Proof. exact (fun_ext (fun x : A => @lem7085680 A x)). Qed.
Lemma lem7085682 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7085683 {A : Type'} (x : A) : (term112 A x) = (term113 A x).
Proof. exact (MK_COMB (@lem7085681 A) (@lem7085682 A x)). Qed.
Lemma lem7085684 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7085685 {A : Type'} (x : A) : (term115 A x) = (term116 A x).
Proof. exact (MK_COMB (@lem7085684) (@lem7085683 A x)). Qed.
Lemma lem7085686 {A : Type'} (x : A) : (term113 A x) = term36.
Proof. exact (eq_refl (term113 A x)). Qed.
Lemma lem7085687 {A : Type'} (x : A) : ((term112 A x) = (term113 A x)) = ((term113 A x) = term36).
Proof. exact (MK_COMB (@lem7085685 A x) (@lem7085686 A x)). Qed.
Lemma lem7085688 {A : Type'} (x : A) : (term113 A x) = term36.
Proof. exact (EQ_MP (@lem7085687 A x) (@lem7085679 A x)). Qed.
Lemma lem7085689 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7085690 {A : Type'} (x : A) : (term117 A x) = term38.
Proof. exact (MK_COMB (@lem7085689) (@lem7085688 A x)). Qed.
Lemma lem7085691 {A : Type'} (f : A -> real) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem7085692 {A : Type'} (f : A -> real) (x : A) : (term92 A f x) = (term73 A f x).
Proof. exact (MK_COMB (@lem7085690 A x) (@lem7085691 A f x)). Qed.
Lemma lem7085694 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) : term118 A s f x.
Proof. exact (fun h0 : @IN A x s => @lem7085572 A f x s h1 h0). Qed.
Lemma lem7085695 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) : term118 A s f x.
Proof. exact (@lem7085694 A x s f h1). Qed.
Lemma lem7085697 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term49 A s f x) : (@IN A x s) = True.
Proof. exact (EQ_MP (@lem7085674 A x s) (@lem7085673 A s f x h1)). Qed.
Lemma lem7085698 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term49 A s f x) : True = (@IN A x s).
Proof. exact (SYM (@lem7085697 A s f x h1)). Qed.
Lemma lem7085699 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term49 A s f x) : @IN A x s.
Proof. exact (EQ_MP (@lem7085698 A s f x h1) (@lem0)). Qed.
Lemma lem7085700 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term30 A s f) (h2 : term49 A s f x) : (term73 A f x) = True.
Proof. exact (@lem7085695 A x s f h1 (@lem7085699 A s f x h2)). Qed.
Lemma lem7085701 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) (h1 : term30 A s f) (h2 : term49 A s f x) : (term92 A f x) = True.
Proof. exact (TRANS (@lem7085692 A f x) (@lem7085700 A s f x h1 h2)). Qed.
Lemma lem7085702 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) : term119 A s f x.
Proof. exact (fun h0 : term49 A s f x => @lem7085701 A s f x h1 h0). Qed.
Lemma lem7085703 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : term120 A s f x.
Proof. exact (@lem7085657 A s f x True). Qed.
Lemma lem7085704 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) : (term121 A s f x) = (term122 A s f x).
Proof. exact (@lem7085703 A s f x (@lem7085702 A x s f h1)). Qed.
Lemma lem7085706 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7085707 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term122 A s f x) = True.
Proof. exact (@lem7085706 (term49 A s f x)). Qed.
Lemma lem7085708 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) : (term121 A s f x) = True.
Proof. exact (TRANS (@lem7085704 A x s f h1) (@lem7085707 A s f x)). Qed.
Lemma lem7085709 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) : (term123 A s f) = (term124 A).
Proof. exact (fun_ext (fun x : A => @lem7085708 A x s f h1)). Qed.
Lemma lem7085710 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7085711 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) : (term125 A s f) = (term126 A).
Proof. exact (MK_COMB (@lem7085710 A) (@lem7085709 A s f h1)). Qed.
Lemma lem7085713 {A : Type'} (t : Prop) : (term127 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7085714 {A : Type'} (t : Prop) : (term127 A t) = t.
Proof. exact (@lem7085713 A t). Qed.
Lemma lem7085715 {A : Type'} : (term126 A) = True.
Proof. exact (@lem7085714 A True). Qed.
Lemma lem7085716 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) : (term125 A s f) = True.
Proof. exact (TRANS (@lem7085711 A s f h1) (@lem7085715 A)). Qed.
Lemma lem7085717 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) (h2 : term27 A s f) : (term83 A s f) = (True /\ True).
Proof. exact (MK_COMB (@lem7085612 A s f h2) (@lem7085716 A s f h1)). Qed.
Lemma lem7085719 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7085720 : (True /\ True) = True.
Proof. exact (@lem7085719 True). Qed.
Lemma lem7085721 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) (h2 : term27 A s f) : (term83 A s f) = True.
Proof. exact (TRANS (@lem7085717 A s f h1 h2) (@lem7085720)). Qed.
Lemma lem7085722 {A : Type'} (s : A -> Prop) (f : A -> real) (q' : Prop) : term128 A s f q'.
Proof. exact (@lem7085605 A s f True q'). Qed.
Lemma lem7085723 {A : Type'} (q' : Prop) (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) (h2 : term27 A s f) : term129 A s f q'.
Proof. exact (@lem7085722 A s f q' (@lem7085721 A s f h1 h2)). Qed.
Lemma lem7085730 {A : Type'} (s : A -> Prop) : (term70 A s) = term36.
Proof. exact (EQ_MP (@lem7085564 A s) (@lem7085563 A s)). Qed.
Lemma lem7085731 {A : Type'} (s : A -> Prop) : (term70 A s) = term36.
Proof. exact (@lem7085730 A s). Qed.
Lemma lem7085732 {A : Type'} (s : A -> Prop) (f : A -> real) : (term130 A s f) = term36.
Proof. exact (@lem7085731 A (term7 A s f)). Qed.
Lemma lem7085733 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7085734 {A : Type'} (s : A -> Prop) (f : A -> real) : (term131 A s f) = term38.
Proof. exact (MK_COMB (@lem7085733) (@lem7085732 A s f)). Qed.
Lemma lem7085743 {A : Type'} (s : A -> Prop) (f : A -> real) : (term62 A s f) = (term62 A s f).
Proof. exact (eq_refl (term62 A s f)). Qed.
Lemma lem7085744 {A : Type'} (s : A -> Prop) (f : A -> real) : (term84 A s f) = (term63 A s f).
Proof. exact (MK_COMB (@lem7085734 A s f) (@lem7085743 A s f)). Qed.
Lemma lem7085753 {A : Type'} (s : A -> Prop) (f : A -> real) : term132 A s f.
Proof. exact (fun h0 : True => @lem7085744 A s f). Qed.
Lemma lem7085754 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) (h2 : term27 A s f) : term133 A s f.
Proof. exact (@lem7085723 A (term63 A s f) s f h1 h2). Qed.
Lemma lem7085755 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) (h2 : term27 A s f) : (term8 A s f) = (term134 A s f).
Proof. exact (@lem7085754 A s f h1 h2 (@lem7085753 A s f)). Qed.
Lemma lem7085757 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem7085758 {A : Type'} (s : A -> Prop) (f : A -> real) : (term134 A s f) = (term63 A s f).
Proof. exact (@lem7085757 (term63 A s f)). Qed.
Lemma lem7085767 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) (h2 : term27 A s f) : (term8 A s f) = (term63 A s f).
Proof. exact (TRANS (@lem7085755 A s f h1 h2) (@lem7085758 A s f)). Qed.
Lemma lem7085768 {A : Type'} (s : A -> Prop) (f : A -> real) (q' : Prop) : term135 A s f q'.
Proof. exact (@lem7085592 A s f (term63 A s f) q'). Qed.
Lemma lem7085769 {A : Type'} (q' : Prop) (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) (h2 : term27 A s f) : term136 A s f q'.
Proof. exact (@lem7085768 A s f q' (@lem7085767 A s f h1 h2)). Qed.
Lemma lem7085770 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term63 A s f) : term63 A s f.
Proof. exact (h1). Qed.
Lemma lem7085771 {A : Type'} (s : A -> Prop) (f : A -> real) : (term63 A s f) = ((term63 A s f) = True).
Proof. exact (@lem7 (term63 A s f)). Qed.
Lemma lem7085774 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term63 A s f) : (term63 A s f) = True.
Proof. exact (EQ_MP (@lem7085771 A s f) (@lem7085770 A s f h1)). Qed.
Lemma lem7085775 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term63 A s f) : (term63 A s f) = True.
Proof. exact (@lem7085774 A s f h1). Qed.
Lemma lem7085776 {A : Type'} (s : A -> Prop) (f : A -> real) : term137 A s f.
Proof. exact (fun h0 : term63 A s f => @lem7085775 A s f h0). Qed.
Lemma lem7085777 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) (h2 : term27 A s f) : term138 A s f.
Proof. exact (@lem7085769 A True s f h1 h2). Qed.
Lemma lem7085778 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) (h2 : term27 A s f) : (term139 A s f) = (term140 A s f).
Proof. exact (@lem7085777 A s f h1 h2 (@lem7085776 A s f)). Qed.
Lemma lem7085780 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7085781 {A : Type'} (s : A -> Prop) (f : A -> real) : (term140 A s f) = True.
Proof. exact (@lem7085780 (term63 A s f)). Qed.
Lemma lem7085782 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) (h2 : term27 A s f) : (term139 A s f) = True.
Proof. exact (TRANS (@lem7085778 A s f h1 h2) (@lem7085781 A s f)). Qed.
Lemma lem7085783 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) (h2 : term27 A s f) : True = (term139 A s f).
Proof. exact (SYM (@lem7085782 A s f h1 h2)). Qed.
Lemma lem7085784 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) (h2 : term27 A s f) : term139 A s f.
Proof. exact (EQ_MP (@lem7085783 A s f h1 h2) (@lem0)). Qed.
Lemma lem7085785 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) (h2 : term27 A s f) : term63 A s f.
Proof. exact (@lem7085784 A s f h1 h2 (@lem7085333 A s f)). Qed.
Lemma lem7085786 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) (h2 : term27 A s f) : term41 A s f.
Proof. exact (EQ_MP (@lem7085524 A s f) (@lem7085785 A s f h1 h2)). Qed.
Lemma lem7085788 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) (h2 : term27 A s f) : term39 A s f.
Proof. exact (EQ_MP (@lem7085478 A s f) (@lem7085786 A s f h1 h2)). Qed.
Lemma lem7085789 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) : term39 A s f.
Proof. exact (or_elim (@lem7085365 A s f) (fun h0 : term27 A s f => @lem7085788 A s f h1 h0) (fun h0 : term29 A s f => @lem7085472 A s f h0)). Qed.
Lemma lem7085790 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) : (term30 A s f) = (term39 A s f).
Proof. exact (prop_ext (fun h2 : term30 A s f => @lem7085789 A s f h1) (fun h2 : term39 A s f => @lem7085368 A s f h1)). Qed.
Lemma lem7085791 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term30 A s f) : term39 A s f.
Proof. exact (EQ_MP (@lem7085790 A s f h1) (@lem7085368 A s f h1)). Qed.
Lemma lem7085792 {A : Type'} (s : A -> Prop) (f : A -> real) : term141 A s f.
Proof. exact (fun h0 : term30 A s f => @lem7085791 A s f h0). Qed.
Lemma lem7085797 {A : Type'} (f : A -> real) : term142 A f.
Proof. exact (fun s : A -> Prop => @lem7085792 A s f). Qed.
