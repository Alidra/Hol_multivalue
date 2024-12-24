Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_IN_CLAUSES_term_abbrevs.
Require Import IN_INSERT_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1857_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19699_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm82_spec.
Lemma lem5031275 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem5031276 {A : Type'} (x : A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem5031277 {A : Type'} (x : A) : term1 A x.
Proof. exact (EQ_MP (@lem5031276 A x) (@lem5031275 A x)). Qed.
Lemma lem5031278 {A : Type'} (x : A) : term2 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem5031280 {A : Type'} (x : A) : term3 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem5031281 {A : Type'} (x : A) : (term3 A x) = (term4 A x).
Proof. exact (eq_refl (term3 A x)). Qed.
Lemma lem5031282 {A : Type'} (x : A) : term4 A x.
Proof. exact (EQ_MP (@lem5031281 A x) (@lem5031280 A x)). Qed.
Lemma lem5031283 {A : Type'} (x : A) (y : A) : term5 A x y.
Proof. exact (@lem5031282 A x y). Qed.
Lemma lem5031284 {A : Type'} (y : A) (x : A) : (term5 A x y) = (term6 A y x).
Proof. exact (eq_refl (term5 A x y)). Qed.
Lemma lem5031285 {A : Type'} (y : A) (x : A) : term6 A y x.
Proof. exact (EQ_MP (@lem5031284 A y x) (@lem5031283 A x y)). Qed.
Lemma lem5031286 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term7 A y x s.
Proof. exact (@lem5031285 A y x s). Qed.
Lemma lem5031287 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term7 A y x s) = ((term8 A x y s) = (term9 A y x s)).
Proof. exact (eq_refl (term7 A y x s)). Qed.
Lemma lem5031296 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem5031297 {_113540 : Type'} (P : _113540 -> Prop) : ((term10 _113540 P) = False) = (term11 _113540 P).
Proof. exact (@lem5031296 (term10 _113540 P)). Qed.
Lemma lem5031305 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem5031278 A x (@lem5031277 A x)). Qed.
Lemma lem5031306 {_113540 : Type'} (x : _113540) : (@IN _113540 x (@EMPTY _113540)) = False.
Proof. exact (@lem5031305 _113540 x). Qed.
Lemma lem5031307 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5031308 {_113540 : Type'} (x : _113540) : (term12 _113540 x) = (and False).
Proof. exact (MK_COMB (@lem5031307) (@lem5031306 _113540 x)). Qed.
Lemma lem5031309 {_113540 : Type'} (P : _113540 -> Prop) (x : _113540) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem5031310 {_113540 : Type'} (P : _113540 -> Prop) (x : _113540) : (term13 _113540 P x) = (term14 _113540 P x).
Proof. exact (MK_COMB (@lem5031308 _113540 x) (@lem5031309 _113540 P x)). Qed.
Lemma lem5031312 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem5031313 {_113540 : Type'} (P : _113540 -> Prop) (x : _113540) : (term14 _113540 P x) = False.
Proof. exact (@lem5031312 (P x)). Qed.
Lemma lem5031314 {_113540 : Type'} (P : _113540 -> Prop) (x : _113540) : (term13 _113540 P x) = False.
Proof. exact (TRANS (@lem5031310 _113540 P x) (@lem5031313 _113540 P x)). Qed.
Lemma lem5031315 {_113540 : Type'} (P : _113540 -> Prop) : (term15 _113540 P) = (term16 _113540).
Proof. exact (fun_ext (fun x : _113540 => @lem5031314 _113540 P x)). Qed.
Lemma lem5031316 {_113540 : Type'} : (@ex _113540) = (@ex _113540).
Proof. exact (eq_refl (@ex _113540)). Qed.
Lemma lem5031317 {_113540 : Type'} (P : _113540 -> Prop) : (term10 _113540 P) = (term17 _113540).
Proof. exact (MK_COMB (@lem5031316 _113540) (@lem5031315 _113540 P)). Qed.
Lemma lem5031319 {A : Type'} (t : Prop) : (term18 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem5031320 {_113540 : Type'} (t : Prop) : (term18 _113540 t) = t.
Proof. exact (@lem5031319 _113540 t). Qed.
Lemma lem5031321 {_113540 : Type'} : (term17 _113540) = False.
Proof. exact (@lem5031320 _113540 False). Qed.
Lemma lem5031322 {_113540 : Type'} (P : _113540 -> Prop) : (term10 _113540 P) = False.
Proof. exact (TRANS (@lem5031317 _113540 P) (@lem5031321 _113540)). Qed.
Lemma lem5031323 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5031324 {_113540 : Type'} (P : _113540 -> Prop) : (term11 _113540 P) = (~ False).
Proof. exact (MK_COMB (@lem5031323) (@lem5031322 _113540 P)). Qed.
Lemma lem5031326 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem5031327 {_113540 : Type'} (P : _113540 -> Prop) : (term11 _113540 P) = True.
Proof. exact (TRANS (@lem5031324 _113540 P) (@lem5031326)). Qed.
Lemma lem5031328 {_113540 : Type'} (P : _113540 -> Prop) : ((term10 _113540 P) = False) = True.
Proof. exact (TRANS (@lem5031297 _113540 P) (@lem5031327 _113540 P)). Qed.
Lemma lem5031329 {_113540 : Type'} : (term19 _113540) = (term20 _113540).
Proof. exact (fun_ext (fun P : _113540 -> Prop => @lem5031328 _113540 P)). Qed.
Lemma lem5031330 {_113540 : Type'} : (@all (_113540 -> Prop)) = (@all (_113540 -> Prop)).
Proof. exact (eq_refl (@all (_113540 -> Prop))). Qed.
Lemma lem5031331 {_113540 : Type'} : (term21 _113540) = (term22 _113540).
Proof. exact (MK_COMB (@lem5031330 _113540) (@lem5031329 _113540)). Qed.
Lemma lem5031333 {A : Type'} (t : Prop) : (term23 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5031334 {_113540 : Type'} (t : Prop) : (term24 _113540 t) = t.
Proof. exact (@lem5031333 (_113540 -> Prop) t). Qed.
Lemma lem5031335 {_113540 : Type'} : (term22 _113540) = True.
Proof. exact (@lem5031334 _113540 True). Qed.
Lemma lem5031336 {_113540 : Type'} : (term21 _113540) = True.
Proof. exact (TRANS (@lem5031331 _113540) (@lem5031335 _113540)). Qed.
Lemma lem5031337 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5031338 {_113540 : Type'} : (term25 _113540) = (and True).
Proof. exact (MK_COMB (@lem5031337) (@lem5031336 _113540)). Qed.
Lemma lem5031360 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A x y s) = (term9 A y x s).
Proof. exact (EQ_MP (@lem5031287 A y x s) (@lem5031286 A y x s)). Qed.
Lemma lem5031361 {_113580 : Type'} (y : _113580) (x : _113580) (s : _113580 -> Prop) : (term8 _113580 x y s) = (term9 _113580 y x s).
Proof. exact (@lem5031360 _113580 y x s). Qed.
Lemma lem5031362 {_113580 : Type'} (a : _113580) (x : _113580) (s : _113580 -> Prop) : (term8 _113580 x a s) = (term9 _113580 a x s).
Proof. exact (@lem5031361 _113580 a x s). Qed.
Lemma lem5031367 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5031368 {_113580 : Type'} (a : _113580) (x : _113580) (s : _113580 -> Prop) : (term26 _113580 x a s) = (term27 _113580 a x s).
Proof. exact (MK_COMB (@lem5031367) (@lem5031362 _113580 a x s)). Qed.
Lemma lem5031369 {_113580 : Type'} (P : _113580 -> Prop) (x : _113580) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem5031370 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term28 _113580 a s P x) = (term29 _113580 a s P x).
Proof. exact (MK_COMB (@lem5031368 _113580 a x s) (@lem5031369 _113580 P x)). Qed.
Lemma lem5031373 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term30 _113580 a s P) = (term31 _113580 a s P).
Proof. exact (fun_ext (fun x : _113580 => @lem5031370 _113580 a s P x)). Qed.
Lemma lem5031374 {_113580 : Type'} : (@ex _113580) = (@ex _113580).
Proof. exact (eq_refl (@ex _113580)). Qed.
Lemma lem5031375 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term32 _113580 a s P) = (term33 _113580 a s P).
Proof. exact (MK_COMB (@lem5031374 _113580) (@lem5031373 _113580 a s P)). Qed.
Lemma lem5031380 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5031381 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term34 _113580 a s P) = (term35 _113580 a s P).
Proof. exact (MK_COMB (@lem5031380) (@lem5031375 _113580 a s P)). Qed.
Lemma lem5031390 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term36 _113580 a s P) = (term36 _113580 a s P).
Proof. exact (eq_refl (term36 _113580 a s P)). Qed.
Lemma lem5031391 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : ((term32 _113580 a s P) = (term36 _113580 a s P)) = ((term33 _113580 a s P) = (term36 _113580 a s P)).
Proof. exact (MK_COMB (@lem5031381 _113580 a s P) (@lem5031390 _113580 a s P)). Qed.
Lemma lem5031394 {_113580 : Type'} (a : _113580) (P : _113580 -> Prop) : (term37 _113580 a P) = (term38 _113580 a P).
Proof. exact (fun_ext (fun s : _113580 -> Prop => @lem5031391 _113580 a s P)). Qed.
Lemma lem5031395 {_113580 : Type'} : (@all (_113580 -> Prop)) = (@all (_113580 -> Prop)).
Proof. exact (eq_refl (@all (_113580 -> Prop))). Qed.
Lemma lem5031396 {_113580 : Type'} (a : _113580) (P : _113580 -> Prop) : (term39 _113580 a P) = (term40 _113580 a P).
Proof. exact (MK_COMB (@lem5031395 _113580) (@lem5031394 _113580 a P)). Qed.
Lemma lem5031401 {_113580 : Type'} (P : _113580 -> Prop) : (term41 _113580 P) = (term42 _113580 P).
Proof. exact (fun_ext (fun a : _113580 => @lem5031396 _113580 a P)). Qed.
Lemma lem5031402 {_113580 : Type'} : (@all _113580) = (@all _113580).
Proof. exact (eq_refl (@all _113580)). Qed.
Lemma lem5031403 {_113580 : Type'} (P : _113580 -> Prop) : (term43 _113580 P) = (term44 _113580 P).
Proof. exact (MK_COMB (@lem5031402 _113580) (@lem5031401 _113580 P)). Qed.
Lemma lem5031408 {_113580 : Type'} : (term45 _113580) = (term46 _113580).
Proof. exact (fun_ext (fun P : _113580 -> Prop => @lem5031403 _113580 P)). Qed.
Lemma lem5031409 {_113580 : Type'} : (@all (_113580 -> Prop)) = (@all (_113580 -> Prop)).
Proof. exact (eq_refl (@all (_113580 -> Prop))). Qed.
Lemma lem5031410 {_113580 : Type'} : (term47 _113580) = (term48 _113580).
Proof. exact (MK_COMB (@lem5031409 _113580) (@lem5031408 _113580)). Qed.
Lemma lem5031415 {_113540 _113580 : Type'} : (term49 _113540 _113580) = (term50 _113580).
Proof. exact (MK_COMB (@lem5031338 _113540) (@lem5031410 _113580)). Qed.
Lemma lem5031417 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5031418 {_113580 : Type'} : (term50 _113580) = (term48 _113580).
Proof. exact (@lem5031417 (term48 _113580)). Qed.
Lemma lem5031451 {_113540 _113580 : Type'} : (term49 _113540 _113580) = (term48 _113580).
Proof. exact (TRANS (@lem5031415 _113540 _113580) (@lem5031418 _113580)). Qed.
Lemma lem5031452 {_113540 _113580 : Type'} : (term48 _113580) = (term49 _113540 _113580).
Proof. exact (SYM (@lem5031451 _113540 _113580)). Qed.
Lemma lem5031454 (p : Prop) : p = (term51 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5031455 {_113580 : Type'} : (term48 _113580) = (term52 _113580).
Proof. exact (@lem5031454 (term48 _113580)). Qed.
Lemma lem5031456 {_113580 : Type'} : (term52 _113580) = (term48 _113580).
Proof. exact (SYM (@lem5031455 _113580)). Qed.
Lemma lem5031457 {_113580 : Type'} (h1 : term53 _113580) : term53 _113580.
Proof. exact (h1). Qed.
Lemma lem5031460 {_113580 : Type'} (h1 : term52 _113580) : term52 _113580.
Proof. exact (h1). Qed.
Lemma lem5031461 {_113580 : Type'} : term54 _113580.
Proof. exact (fun h0 : term52 _113580 => @lem5031460 _113580 h0). Qed.
Lemma lem5031462 {_113580 : Type'} (h1 : term54 _113580) : term54 _113580.
Proof. exact (h1). Qed.
Lemma lem5031463 {_113580 : Type'} (h1 : term52 _113580) : term52 _113580.
Proof. exact (h1). Qed.
Lemma lem5031464 {_113580 : Type'} (h1 : term52 _113580) (h2 : term54 _113580) : term52 _113580.
Proof. exact (@lem5031462 _113580 h2 (@lem5031463 _113580 h1)). Qed.
Lemma lem5031465 {_113580 : Type'} (h1 : term52 _113580) : term55 _113580.
Proof. exact (fun h0 : term54 _113580 => @lem5031464 _113580 h1 h0). Qed.
Lemma lem5031466 {_113580 : Type'} (h1 : term54 _113580) : term54 _113580.
Proof. exact (h1). Qed.
Lemma lem5031467 {_113580 : Type'} (h1 : term52 _113580) (h2 : term54 _113580) : term52 _113580.
Proof. exact (@lem5031465 _113580 h1 (@lem5031466 _113580 h2)). Qed.
Lemma lem5031468 {_113580 : Type'} (h1 : term54 _113580) : term54 _113580.
Proof. exact (fun h0 : term52 _113580 => @lem5031467 _113580 h0 h1). Qed.
Lemma lem5031469 {_113580 : Type'} : term56 _113580.
Proof. exact (fun h0 : term54 _113580 => @lem5031468 _113580 h0). Qed.
Lemma lem5031472 {_113580 : Type'} : term54 _113580.
Proof. exact (@lem5031469 _113580 (@lem5031461 _113580)). Qed.
Lemma lem5031473 {_113580 : Type'} : term54 _113580.
Proof. exact (@lem5031472 _113580). Qed.
Lemma lem5031475 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5031476 {_113580 : Type'} : (term52 _113580) = (term57 _113580).
Proof. exact (@lem5031475 (term53 _113580)). Qed.
Lemma lem5031478 (t : Prop) : (term58 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5031479 {_113580 : Type'} : (term57 _113580) = (term48 _113580).
Proof. exact (@lem5031478 (term48 _113580)). Qed.
Lemma lem5031568 {_113580 : Type'} : (term52 _113580) = (term48 _113580).
Proof. exact (TRANS (@lem5031476 _113580) (@lem5031479 _113580)). Qed.
Lemma lem5031573 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term59 _113580 s P x) = (term59 _113580 s P x).
Proof. exact (eq_refl (term59 _113580 s P x)). Qed.
Lemma lem5031574 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) : (term60 _113580 s P) = (term60 _113580 s P).
Proof. exact (fun_ext (fun x : _113580 => @lem5031573 _113580 s P x)). Qed.
Lemma lem5031575 {_113580 : Type'} : (@ex _113580) = (@ex _113580).
Proof. exact (eq_refl (@ex _113580)). Qed.
Lemma lem5031576 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) : (term61 _113580 s P) = (term61 _113580 s P).
Proof. exact (MK_COMB (@lem5031575 _113580) (@lem5031574 _113580 s P)). Qed.
Lemma lem5031579 {_113580 : Type'} (P : _113580 -> Prop) (a : _113580) : (term62 _113580 P a) = (term62 _113580 P a).
Proof. exact (eq_refl (term62 _113580 P a)). Qed.
Lemma lem5031580 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term36 _113580 a s P) = (term36 _113580 a s P).
Proof. exact (MK_COMB (@lem5031579 _113580 P a) (@lem5031576 _113580 s P)). Qed.
Lemma lem5031589 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term29 _113580 a s P x) = (term29 _113580 a s P x).
Proof. exact (eq_refl (term29 _113580 a s P x)). Qed.
Lemma lem5031590 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term31 _113580 a s P) = (term31 _113580 a s P).
Proof. exact (fun_ext (fun x : _113580 => @lem5031589 _113580 a s P x)). Qed.
Lemma lem5031591 {_113580 : Type'} : (@ex _113580) = (@ex _113580).
Proof. exact (eq_refl (@ex _113580)). Qed.
Lemma lem5031592 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term33 _113580 a s P) = (term33 _113580 a s P).
Proof. exact (MK_COMB (@lem5031591 _113580) (@lem5031590 _113580 a s P)). Qed.
Lemma lem5031593 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5031594 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term35 _113580 a s P) = (term35 _113580 a s P).
Proof. exact (MK_COMB (@lem5031593) (@lem5031592 _113580 a s P)). Qed.
Lemma lem5031595 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : ((term33 _113580 a s P) = (term36 _113580 a s P)) = ((term33 _113580 a s P) = (term36 _113580 a s P)).
Proof. exact (MK_COMB (@lem5031594 _113580 a s P) (@lem5031580 _113580 a s P)). Qed.
Lemma lem5031596 {_113580 : Type'} (a : _113580) (P : _113580 -> Prop) : (term38 _113580 a P) = (term38 _113580 a P).
Proof. exact (fun_ext (fun s : _113580 -> Prop => @lem5031595 _113580 a s P)). Qed.
Lemma lem5031597 {_113580 : Type'} : (@all (_113580 -> Prop)) = (@all (_113580 -> Prop)).
Proof. exact (eq_refl (@all (_113580 -> Prop))). Qed.
Lemma lem5031598 {_113580 : Type'} (a : _113580) (P : _113580 -> Prop) : (term40 _113580 a P) = (term40 _113580 a P).
Proof. exact (MK_COMB (@lem5031597 _113580) (@lem5031596 _113580 a P)). Qed.
Lemma lem5031599 {_113580 : Type'} (P : _113580 -> Prop) : (term42 _113580 P) = (term42 _113580 P).
Proof. exact (fun_ext (fun a : _113580 => @lem5031598 _113580 a P)). Qed.
Lemma lem5031600 {_113580 : Type'} : (@all _113580) = (@all _113580).
Proof. exact (eq_refl (@all _113580)). Qed.
Lemma lem5031601 {_113580 : Type'} (P : _113580 -> Prop) : (term44 _113580 P) = (term44 _113580 P).
Proof. exact (MK_COMB (@lem5031600 _113580) (@lem5031599 _113580 P)). Qed.
Lemma lem5031602 {_113580 : Type'} : (term46 _113580) = (term46 _113580).
Proof. exact (fun_ext (fun P : _113580 -> Prop => @lem5031601 _113580 P)). Qed.
Lemma lem5031603 {_113580 : Type'} : (@all (_113580 -> Prop)) = (@all (_113580 -> Prop)).
Proof. exact (eq_refl (@all (_113580 -> Prop))). Qed.
Lemma lem5031604 {_113580 : Type'} : (term48 _113580) = (term48 _113580).
Proof. exact (MK_COMB (@lem5031603 _113580) (@lem5031602 _113580)). Qed.
Lemma lem5031645 {_113580 : Type'} : (term52 _113580) = (term48 _113580).
Proof. exact (TRANS (@lem5031568 _113580) (@lem5031604 _113580)). Qed.
Lemma lem5031646 {_113580 : Type'} : (term48 _113580) = (term52 _113580).
Proof. exact (SYM (@lem5031645 _113580)). Qed.
Lemma lem5031648 (p : Prop) : p = (term51 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5031649 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : ((term33 _113580 a s P) = (term36 _113580 a s P)) = (term63 _113580 a s P).
Proof. exact (@lem5031648 ((term33 _113580 a s P) = (term36 _113580 a s P))). Qed.
Lemma lem5031650 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term63 _113580 a s P) = ((term33 _113580 a s P) = (term36 _113580 a s P)).
Proof. exact (SYM (@lem5031649 _113580 a s P)). Qed.
Lemma lem5031651 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (h1 : term64 _113580 a s P) : term64 _113580 a s P.
Proof. exact (h1). Qed.
Lemma lem5031660 {_113580 : Type'} (a : _113580) (x : _113580) (s : _113580 -> Prop) : (term65 _113580 a x s) = (term66 _113580 a x s).
Proof. exact (@lem17160 (x = a) (@IN _113580 x s)). Qed.
Lemma lem5031664 {_113580 : Type'} (P : _113580 -> Prop) (x : _113580) : (term67 _113580 P x) = (term67 _113580 P x).
Proof. exact (eq_refl (term67 _113580 P x)). Qed.
Lemma lem5031666 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5031667 {_113580 : Type'} (a : _113580) (x : _113580) (s : _113580 -> Prop) : (term68 _113580 a x s) = (term69 _113580 a x s).
Proof. exact (MK_COMB (@lem5031666) (@lem5031660 _113580 a x s)). Qed.
Lemma lem5031668 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term70 _113580 a s P x) = (term71 _113580 a s P x).
Proof. exact (MK_COMB (@lem5031667 _113580 a x s) (@lem5031664 _113580 P x)). Qed.
Lemma lem5031669 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term72 _113580 a s P x) = (term70 _113580 a s P x).
Proof. exact (@lem17045 (term9 _113580 a x s) (P x)). Qed.
Lemma lem5031670 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term72 _113580 a s P x) = (term71 _113580 a s P x).
Proof. exact (TRANS (@lem5031669 _113580 a s P x) (@lem5031668 _113580 a s P x)). Qed.
Lemma lem5031673 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term29 _113580 a s P x) = (term29 _113580 a s P x).
Proof. exact (eq_refl (term29 _113580 a s P x)). Qed.
Lemma lem5031674 {_113580 : Type'} (P : _113580 -> Prop) : (term73 _113580 P) = (term74 _113580 P).
Proof. exact (@lem18394 _113580 P). Qed.
Lemma lem5031675 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term75 _113580 a s P) = (term76 _113580 a s P).
Proof. exact (@lem5031674 _113580 (term31 _113580 a s P)). Qed.
Lemma lem5031676 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term77 _113580 a s P x) = (term29 _113580 a s P x).
Proof. exact (eq_refl (term77 _113580 a s P x)). Qed.
Lemma lem5031677 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5031678 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term78 _113580 a s P x) = (term72 _113580 a s P x).
Proof. exact (MK_COMB (@lem5031677) (@lem5031676 _113580 a s P x)). Qed.
Lemma lem5031679 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term78 _113580 a s P x) = (term71 _113580 a s P x).
Proof. exact (TRANS (@lem5031678 _113580 a s P x) (@lem5031670 _113580 a s P x)). Qed.
Lemma lem5031680 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term79 _113580 a s P) = (term80 _113580 a s P).
Proof. exact (fun_ext (fun x : _113580 => @lem5031679 _113580 a s P x)). Qed.
Lemma lem5031681 {_113580 : Type'} : (@all _113580) = (@all _113580).
Proof. exact (eq_refl (@all _113580)). Qed.
Lemma lem5031682 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term76 _113580 a s P) = (term81 _113580 a s P).
Proof. exact (MK_COMB (@lem5031681 _113580) (@lem5031680 _113580 a s P)). Qed.
Lemma lem5031683 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term75 _113580 a s P) = (term81 _113580 a s P).
Proof. exact (TRANS (@lem5031675 _113580 a s P) (@lem5031682 _113580 a s P)). Qed.
Lemma lem5031684 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term31 _113580 a s P) = (term31 _113580 a s P).
Proof. exact (fun_ext (fun x : _113580 => @lem5031673 _113580 a s P x)). Qed.
Lemma lem5031685 {_113580 : Type'} : (@ex _113580) = (@ex _113580).
Proof. exact (eq_refl (@ex _113580)). Qed.
Lemma lem5031686 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term33 _113580 a s P) = (term33 _113580 a s P).
Proof. exact (MK_COMB (@lem5031685 _113580) (@lem5031684 _113580 a s P)). Qed.
Lemma lem5031697 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term82 _113580 s P x) = (term83 _113580 s P x).
Proof. exact (@lem17045 (@IN _113580 x s) (P x)). Qed.
Lemma lem5031700 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term59 _113580 s P x) = (term59 _113580 s P x).
Proof. exact (eq_refl (term59 _113580 s P x)). Qed.
Lemma lem5031701 {_113580 : Type'} (P : _113580 -> Prop) : (term73 _113580 P) = (term74 _113580 P).
Proof. exact (@lem18394 _113580 P). Qed.
Lemma lem5031702 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) : (term84 _113580 s P) = (term85 _113580 s P).
Proof. exact (@lem5031701 _113580 (term60 _113580 s P)). Qed.
Lemma lem5031703 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term86 _113580 s P x) = (term59 _113580 s P x).
Proof. exact (eq_refl (term86 _113580 s P x)). Qed.
Lemma lem5031704 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5031705 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term87 _113580 s P x) = (term82 _113580 s P x).
Proof. exact (MK_COMB (@lem5031704) (@lem5031703 _113580 s P x)). Qed.
Lemma lem5031706 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term87 _113580 s P x) = (term83 _113580 s P x).
Proof. exact (TRANS (@lem5031705 _113580 s P x) (@lem5031697 _113580 s P x)). Qed.
Lemma lem5031707 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) : (term88 _113580 s P) = (term89 _113580 s P).
Proof. exact (fun_ext (fun x : _113580 => @lem5031706 _113580 s P x)). Qed.
Lemma lem5031708 {_113580 : Type'} : (@all _113580) = (@all _113580).
Proof. exact (eq_refl (@all _113580)). Qed.
Lemma lem5031709 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) : (term85 _113580 s P) = (term90 _113580 s P).
Proof. exact (MK_COMB (@lem5031708 _113580) (@lem5031707 _113580 s P)). Qed.
Lemma lem5031710 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) : (term84 _113580 s P) = (term90 _113580 s P).
Proof. exact (TRANS (@lem5031702 _113580 s P) (@lem5031709 _113580 s P)). Qed.
Lemma lem5031711 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) : (term60 _113580 s P) = (term60 _113580 s P).
Proof. exact (fun_ext (fun x : _113580 => @lem5031700 _113580 s P x)). Qed.
Lemma lem5031712 {_113580 : Type'} : (@ex _113580) = (@ex _113580).
Proof. exact (eq_refl (@ex _113580)). Qed.
Lemma lem5031713 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) : (term61 _113580 s P) = (term61 _113580 s P).
Proof. exact (MK_COMB (@lem5031712 _113580) (@lem5031711 _113580 s P)). Qed.
Lemma lem5031715 {_113580 : Type'} (P : _113580 -> Prop) (a : _113580) : (term91 _113580 P a) = (term91 _113580 P a).
Proof. exact (eq_refl (term91 _113580 P a)). Qed.
Lemma lem5031716 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term92 _113580 a s P) = (term93 _113580 a s P).
Proof. exact (MK_COMB (@lem5031715 _113580 P a) (@lem5031710 _113580 s P)). Qed.
Lemma lem5031717 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term94 _113580 a s P) = (term92 _113580 a s P).
Proof. exact (@lem17160 (P a) (term61 _113580 s P)). Qed.
Lemma lem5031718 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term94 _113580 a s P) = (term93 _113580 a s P).
Proof. exact (TRANS (@lem5031717 _113580 a s P) (@lem5031716 _113580 a s P)). Qed.
Lemma lem5031720 {_113580 : Type'} (P : _113580 -> Prop) (a : _113580) : (term62 _113580 P a) = (term62 _113580 P a).
Proof. exact (eq_refl (term62 _113580 P a)). Qed.
Lemma lem5031721 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term36 _113580 a s P) = (term36 _113580 a s P).
Proof. exact (MK_COMB (@lem5031720 _113580 P a) (@lem5031713 _113580 s P)). Qed.
Lemma lem5031722 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5031723 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term95 _113580 a s P) = (term96 _113580 a s P).
Proof. exact (MK_COMB (@lem5031722) (@lem5031683 _113580 a s P)). Qed.
Lemma lem5031724 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term97 _113580 a s P) = (term98 _113580 a s P).
Proof. exact (MK_COMB (@lem5031723 _113580 a s P) (@lem5031721 _113580 a s P)). Qed.
Lemma lem5031725 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5031726 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term99 _113580 a s P) = (term99 _113580 a s P).
Proof. exact (MK_COMB (@lem5031725) (@lem5031686 _113580 a s P)). Qed.
Lemma lem5031727 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term100 _113580 a s P) = (term101 _113580 a s P).
Proof. exact (MK_COMB (@lem5031726 _113580 a s P) (@lem5031718 _113580 a s P)). Qed.
Lemma lem5031728 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5031729 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term102 _113580 a s P) = (term103 _113580 a s P).
Proof. exact (MK_COMB (@lem5031728) (@lem5031727 _113580 a s P)). Qed.
Lemma lem5031730 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term104 _113580 a s P) = (term105 _113580 a s P).
Proof. exact (MK_COMB (@lem5031729 _113580 a s P) (@lem5031724 _113580 a s P)). Qed.
Lemma lem5031731 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term64 _113580 a s P) = (term104 _113580 a s P).
Proof. exact (@lem17646 (term33 _113580 a s P) (term36 _113580 a s P)). Qed.
Lemma lem5031732 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term64 _113580 a s P) = (term105 _113580 a s P).
Proof. exact (TRANS (@lem5031731 _113580 a s P) (@lem5031730 _113580 a s P)). Qed.
Lemma lem5031895 {A : Type'} (P : A -> Prop) (Q : Prop) : (term106 A P Q) = (term107 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5031896 {_113580 : Type'} (P : _113580 -> Prop) (Q : Prop) : (term106 _113580 P Q) = (term107 _113580 P Q).
Proof. exact (@lem5031895 _113580 P Q). Qed.
Lemma lem5031897 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term108 _113580 a s P) = (term109 _113580 a s P).
Proof. exact (@lem5031896 _113580 (term31 _113580 a s P) (term93 _113580 a s P)). Qed.
Lemma lem5031898 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term77 _113580 a s P x) = (term29 _113580 a s P x).
Proof. exact (eq_refl (term77 _113580 a s P x)). Qed.
Lemma lem5031899 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term110 _113580 a s P) = (term31 _113580 a s P).
Proof. exact (fun_ext (fun x : _113580 => @lem5031898 _113580 a s P x)). Qed.
Lemma lem5031900 {_113580 : Type'} : (@ex _113580) = (@ex _113580).
Proof. exact (eq_refl (@ex _113580)). Qed.
Lemma lem5031901 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term111 _113580 a s P) = (term33 _113580 a s P).
Proof. exact (MK_COMB (@lem5031900 _113580) (@lem5031899 _113580 a s P)). Qed.
Lemma lem5031902 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5031903 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term112 _113580 a s P) = (term99 _113580 a s P).
Proof. exact (MK_COMB (@lem5031902) (@lem5031901 _113580 a s P)). Qed.
Lemma lem5031904 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term93 _113580 a s P) = (term93 _113580 a s P).
Proof. exact (eq_refl (term93 _113580 a s P)). Qed.
Lemma lem5031905 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term108 _113580 a s P) = (term101 _113580 a s P).
Proof. exact (MK_COMB (@lem5031903 _113580 a s P) (@lem5031904 _113580 a s P)). Qed.
Lemma lem5031906 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5031907 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term113 _113580 a s P) = (term114 _113580 a s P).
Proof. exact (MK_COMB (@lem5031906) (@lem5031905 _113580 a s P)). Qed.
Lemma lem5031908 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term77 _113580 a s P x) = (term29 _113580 a s P x).
Proof. exact (eq_refl (term77 _113580 a s P x)). Qed.
Lemma lem5031909 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5031910 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term115 _113580 a s P x) = (term116 _113580 a s P x).
Proof. exact (MK_COMB (@lem5031909) (@lem5031908 _113580 a s P x)). Qed.
Lemma lem5031911 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term93 _113580 a s P) = (term93 _113580 a s P).
Proof. exact (eq_refl (term93 _113580 a s P)). Qed.
Lemma lem5031912 {_113580 : Type'} (x : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term117 _113580 x a s P) = (term118 _113580 x a s P).
Proof. exact (MK_COMB (@lem5031910 _113580 a s P x) (@lem5031911 _113580 a s P)). Qed.
Lemma lem5031913 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term119 _113580 a s P) = (term120 _113580 a s P).
Proof. exact (fun_ext (fun x : _113580 => @lem5031912 _113580 x a s P)). Qed.
Lemma lem5031914 {_113580 : Type'} : (@ex _113580) = (@ex _113580).
Proof. exact (eq_refl (@ex _113580)). Qed.
Lemma lem5031915 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term109 _113580 a s P) = (term121 _113580 a s P).
Proof. exact (MK_COMB (@lem5031914 _113580) (@lem5031913 _113580 a s P)). Qed.
Lemma lem5031916 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : ((term108 _113580 a s P) = (term109 _113580 a s P)) = ((term101 _113580 a s P) = (term121 _113580 a s P)).
Proof. exact (MK_COMB (@lem5031907 _113580 a s P) (@lem5031915 _113580 a s P)). Qed.
Lemma lem5031917 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term101 _113580 a s P) = (term121 _113580 a s P).
Proof. exact (EQ_MP (@lem5031916 _113580 a s P) (@lem5031897 _113580 a s P)). Qed.
Lemma lem5031918 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5031919 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term103 _113580 a s P) = (term122 _113580 a s P).
Proof. exact (MK_COMB (@lem5031918) (@lem5031917 _113580 a s P)). Qed.
Lemma lem5031921 {A : Type'} (P : Prop) (Q : A -> Prop) : (term123 A P Q) = (term124 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5031922 {_113580 : Type'} (P : Prop) (Q : _113580 -> Prop) : (term123 _113580 P Q) = (term124 _113580 P Q).
Proof. exact (@lem5031921 _113580 P Q). Qed.
Lemma lem5031923 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term125 _113580 a s P) = (term126 _113580 a s P).
Proof. exact (@lem5031922 _113580 (P a) (term60 _113580 s P)). Qed.
Lemma lem5031924 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term86 _113580 s P x) = (term59 _113580 s P x).
Proof. exact (eq_refl (term86 _113580 s P x)). Qed.
Lemma lem5031925 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) : (term127 _113580 s P) = (term60 _113580 s P).
Proof. exact (fun_ext (fun x : _113580 => @lem5031924 _113580 s P x)). Qed.
Lemma lem5031926 {_113580 : Type'} : (@ex _113580) = (@ex _113580).
Proof. exact (eq_refl (@ex _113580)). Qed.
Lemma lem5031927 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) : (term128 _113580 s P) = (term61 _113580 s P).
Proof. exact (MK_COMB (@lem5031926 _113580) (@lem5031925 _113580 s P)). Qed.
Lemma lem5031928 {_113580 : Type'} (P : _113580 -> Prop) (a : _113580) : (term62 _113580 P a) = (term62 _113580 P a).
Proof. exact (eq_refl (term62 _113580 P a)). Qed.
Lemma lem5031929 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term125 _113580 a s P) = (term36 _113580 a s P).
Proof. exact (MK_COMB (@lem5031928 _113580 P a) (@lem5031927 _113580 s P)). Qed.
Lemma lem5031930 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5031931 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term129 _113580 a s P) = (term130 _113580 a s P).
Proof. exact (MK_COMB (@lem5031930) (@lem5031929 _113580 a s P)). Qed.
Lemma lem5031932 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term86 _113580 s P x) = (term59 _113580 s P x).
Proof. exact (eq_refl (term86 _113580 s P x)). Qed.
Lemma lem5031933 {_113580 : Type'} (P : _113580 -> Prop) (a : _113580) : (term62 _113580 P a) = (term62 _113580 P a).
Proof. exact (eq_refl (term62 _113580 P a)). Qed.
Lemma lem5031934 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term131 _113580 a s P x) = (term132 _113580 a s P x).
Proof. exact (MK_COMB (@lem5031933 _113580 P a) (@lem5031932 _113580 s P x)). Qed.
Lemma lem5031935 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term133 _113580 a s P) = (term134 _113580 a s P).
Proof. exact (fun_ext (fun x : _113580 => @lem5031934 _113580 a s P x)). Qed.
Lemma lem5031936 {_113580 : Type'} : (@ex _113580) = (@ex _113580).
Proof. exact (eq_refl (@ex _113580)). Qed.
Lemma lem5031937 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term126 _113580 a s P) = (term135 _113580 a s P).
Proof. exact (MK_COMB (@lem5031936 _113580) (@lem5031935 _113580 a s P)). Qed.
Lemma lem5031938 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : ((term125 _113580 a s P) = (term126 _113580 a s P)) = ((term36 _113580 a s P) = (term135 _113580 a s P)).
Proof. exact (MK_COMB (@lem5031931 _113580 a s P) (@lem5031937 _113580 a s P)). Qed.
Lemma lem5031939 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term36 _113580 a s P) = (term135 _113580 a s P).
Proof. exact (EQ_MP (@lem5031938 _113580 a s P) (@lem5031923 _113580 a s P)). Qed.
Lemma lem5031940 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term96 _113580 a s P) = (term96 _113580 a s P).
Proof. exact (eq_refl (term96 _113580 a s P)). Qed.
Lemma lem5031941 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term98 _113580 a s P) = (term136 _113580 a s P).
Proof. exact (MK_COMB (@lem5031940 _113580 a s P) (@lem5031939 _113580 a s P)). Qed.
Lemma lem5031943 {A : Type'} (P : Prop) (Q : A -> Prop) : (term137 A P Q) = (term138 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5031944 {_113580 : Type'} (P : Prop) (Q : _113580 -> Prop) : (term137 _113580 P Q) = (term138 _113580 P Q).
Proof. exact (@lem5031943 _113580 P Q). Qed.
Lemma lem5031945 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term139 _113580 a s P) = (term140 _113580 a s P).
Proof. exact (@lem5031944 _113580 (term81 _113580 a s P) (term134 _113580 a s P)). Qed.
Lemma lem5031946 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term141 _113580 a s P x) = (term132 _113580 a s P x).
Proof. exact (eq_refl (term141 _113580 a s P x)). Qed.
Lemma lem5031947 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term142 _113580 a s P) = (term134 _113580 a s P).
Proof. exact (fun_ext (fun x : _113580 => @lem5031946 _113580 a s P x)). Qed.
Lemma lem5031948 {_113580 : Type'} : (@ex _113580) = (@ex _113580).
Proof. exact (eq_refl (@ex _113580)). Qed.
Lemma lem5031949 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term143 _113580 a s P) = (term135 _113580 a s P).
Proof. exact (MK_COMB (@lem5031948 _113580) (@lem5031947 _113580 a s P)). Qed.
Lemma lem5031950 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term96 _113580 a s P) = (term96 _113580 a s P).
Proof. exact (eq_refl (term96 _113580 a s P)). Qed.
Lemma lem5031951 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term139 _113580 a s P) = (term136 _113580 a s P).
Proof. exact (MK_COMB (@lem5031950 _113580 a s P) (@lem5031949 _113580 a s P)). Qed.
Lemma lem5031952 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5031953 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term144 _113580 a s P) = (term145 _113580 a s P).
Proof. exact (MK_COMB (@lem5031952) (@lem5031951 _113580 a s P)). Qed.
Lemma lem5031954 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term141 _113580 a s P x) = (term132 _113580 a s P x).
Proof. exact (eq_refl (term141 _113580 a s P x)). Qed.
Lemma lem5031955 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term96 _113580 a s P) = (term96 _113580 a s P).
Proof. exact (eq_refl (term96 _113580 a s P)). Qed.
Lemma lem5031956 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term146 _113580 a s P x) = (term147 _113580 a s P x).
Proof. exact (MK_COMB (@lem5031955 _113580 a s P) (@lem5031954 _113580 a s P x)). Qed.
Lemma lem5031957 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term148 _113580 a s P) = (term149 _113580 a s P).
Proof. exact (fun_ext (fun x : _113580 => @lem5031956 _113580 a s P x)). Qed.
Lemma lem5031958 {_113580 : Type'} : (@ex _113580) = (@ex _113580).
Proof. exact (eq_refl (@ex _113580)). Qed.
Lemma lem5031959 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term140 _113580 a s P) = (term150 _113580 a s P).
Proof. exact (MK_COMB (@lem5031958 _113580) (@lem5031957 _113580 a s P)). Qed.
Lemma lem5031960 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : ((term139 _113580 a s P) = (term140 _113580 a s P)) = ((term136 _113580 a s P) = (term150 _113580 a s P)).
Proof. exact (MK_COMB (@lem5031953 _113580 a s P) (@lem5031959 _113580 a s P)). Qed.
Lemma lem5031961 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term136 _113580 a s P) = (term150 _113580 a s P).
Proof. exact (EQ_MP (@lem5031960 _113580 a s P) (@lem5031945 _113580 a s P)). Qed.
Lemma lem5031962 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term98 _113580 a s P) = (term150 _113580 a s P).
Proof. exact (TRANS (@lem5031941 _113580 a s P) (@lem5031961 _113580 a s P)). Qed.
Lemma lem5031963 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term105 _113580 a s P) = (term151 _113580 a s P).
Proof. exact (MK_COMB (@lem5031919 _113580 a s P) (@lem5031962 _113580 a s P)). Qed.
Lemma lem5031965 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term152 A P Q) = (term153 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5031966 {_113580 : Type'} (P : _113580 -> Prop) (Q : _113580 -> Prop) : (term152 _113580 P Q) = (term153 _113580 P Q).
Proof. exact (@lem5031965 _113580 P Q). Qed.
Lemma lem5031967 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term154 _113580 a s P) = (term155 _113580 a s P).
Proof. exact (@lem5031966 _113580 (term120 _113580 a s P) (term149 _113580 a s P)). Qed.
Lemma lem5031968 {_113580 : Type'} (x : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term156 _113580 a s P x) = (term118 _113580 x a s P).
Proof. exact (eq_refl (term156 _113580 a s P x)). Qed.
Lemma lem5031969 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term157 _113580 a s P) = (term120 _113580 a s P).
Proof. exact (fun_ext (fun x : _113580 => @lem5031968 _113580 x a s P)). Qed.
Lemma lem5031970 {_113580 : Type'} : (@ex _113580) = (@ex _113580).
Proof. exact (eq_refl (@ex _113580)). Qed.
Lemma lem5031971 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term158 _113580 a s P) = (term121 _113580 a s P).
Proof. exact (MK_COMB (@lem5031970 _113580) (@lem5031969 _113580 a s P)). Qed.
Lemma lem5031972 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5031973 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term159 _113580 a s P) = (term122 _113580 a s P).
Proof. exact (MK_COMB (@lem5031972) (@lem5031971 _113580 a s P)). Qed.
Lemma lem5031974 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term160 _113580 a s P x) = (term147 _113580 a s P x).
Proof. exact (eq_refl (term160 _113580 a s P x)). Qed.
Lemma lem5031975 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term161 _113580 a s P) = (term149 _113580 a s P).
Proof. exact (fun_ext (fun x : _113580 => @lem5031974 _113580 a s P x)). Qed.
Lemma lem5031976 {_113580 : Type'} : (@ex _113580) = (@ex _113580).
Proof. exact (eq_refl (@ex _113580)). Qed.
Lemma lem5031977 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term162 _113580 a s P) = (term150 _113580 a s P).
Proof. exact (MK_COMB (@lem5031976 _113580) (@lem5031975 _113580 a s P)). Qed.
Lemma lem5031978 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term154 _113580 a s P) = (term151 _113580 a s P).
Proof. exact (MK_COMB (@lem5031973 _113580 a s P) (@lem5031977 _113580 a s P)). Qed.
Lemma lem5031979 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5031980 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term163 _113580 a s P) = (term164 _113580 a s P).
Proof. exact (MK_COMB (@lem5031979) (@lem5031978 _113580 a s P)). Qed.
Lemma lem5031981 {_113580 : Type'} (x : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term156 _113580 a s P x) = (term118 _113580 x a s P).
Proof. exact (eq_refl (term156 _113580 a s P x)). Qed.
Lemma lem5031982 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5031983 {_113580 : Type'} (x : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term165 _113580 a s P x) = (term166 _113580 x a s P).
Proof. exact (MK_COMB (@lem5031982) (@lem5031981 _113580 x a s P)). Qed.
Lemma lem5031984 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term160 _113580 a s P x) = (term147 _113580 a s P x).
Proof. exact (eq_refl (term160 _113580 a s P x)). Qed.
Lemma lem5031985 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term167 _113580 a s P x) = (term168 _113580 a s P x).
Proof. exact (MK_COMB (@lem5031983 _113580 x a s P) (@lem5031984 _113580 a s P x)). Qed.
Lemma lem5031986 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term169 _113580 a s P) = (term170 _113580 a s P).
Proof. exact (fun_ext (fun x : _113580 => @lem5031985 _113580 a s P x)). Qed.
Lemma lem5031987 {_113580 : Type'} : (@ex _113580) = (@ex _113580).
Proof. exact (eq_refl (@ex _113580)). Qed.
Lemma lem5031988 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term155 _113580 a s P) = (term171 _113580 a s P).
Proof. exact (MK_COMB (@lem5031987 _113580) (@lem5031986 _113580 a s P)). Qed.
Lemma lem5031989 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : ((term154 _113580 a s P) = (term155 _113580 a s P)) = ((term151 _113580 a s P) = (term171 _113580 a s P)).
Proof. exact (MK_COMB (@lem5031980 _113580 a s P) (@lem5031988 _113580 a s P)). Qed.
Lemma lem5031990 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term151 _113580 a s P) = (term171 _113580 a s P).
Proof. exact (EQ_MP (@lem5031989 _113580 a s P) (@lem5031967 _113580 a s P)). Qed.
Lemma lem5031992 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term105 _113580 a s P) = (term171 _113580 a s P).
Proof. exact (TRANS (@lem5031963 _113580 a s P) (@lem5031990 _113580 a s P)). Qed.
Lemma lem5031993 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term64 _113580 a s P) = (term171 _113580 a s P).
Proof. exact (TRANS (@lem5031732 _113580 a s P) (@lem5031992 _113580 a s P)). Qed.
Lemma lem5031994 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (h1 : term64 _113580 a s P) : term171 _113580 a s P.
Proof. exact (EQ_MP (@lem5031993 _113580 a s P) (@lem5031651 _113580 a s P h1)). Qed.
Lemma lem5031995 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term168 _113580 a s P x) : term168 _113580 a s P x.
Proof. exact (h1). Qed.
Lemma lem5032012 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term132 _113580 a s P x) = (term132 _113580 a s P x).
Proof. exact (eq_refl (term132 _113580 a s P x)). Qed.
Lemma lem5032037 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term71 _113580 a s P x) = (term71 _113580 a s P x).
Proof. exact (eq_refl (term71 _113580 a s P x)). Qed.
Lemma lem5032038 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term80 _113580 a s P) = (term80 _113580 a s P).
Proof. exact (fun_ext (fun x : _113580 => @lem5032037 _113580 a s P x)). Qed.
Lemma lem5032039 {_113580 : Type'} : (@all _113580) = (@all _113580).
Proof. exact (eq_refl (@all _113580)). Qed.
Lemma lem5032040 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term81 _113580 a s P) = (term81 _113580 a s P).
Proof. exact (MK_COMB (@lem5032039 _113580) (@lem5032038 _113580 a s P)). Qed.
Lemma lem5032041 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5032042 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term96 _113580 a s P) = (term96 _113580 a s P).
Proof. exact (MK_COMB (@lem5032041) (@lem5032040 _113580 a s P)). Qed.
Lemma lem5032043 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term147 _113580 a s P x) = (term147 _113580 a s P x).
Proof. exact (MK_COMB (@lem5032042 _113580 a s P) (@lem5032012 _113580 a s P x)). Qed.
Lemma lem5032058 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term83 _113580 s P x) = (term83 _113580 s P x).
Proof. exact (eq_refl (term83 _113580 s P x)). Qed.
Lemma lem5032059 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) : (term89 _113580 s P) = (term89 _113580 s P).
Proof. exact (fun_ext (fun x : _113580 => @lem5032058 _113580 s P x)). Qed.
Lemma lem5032060 {_113580 : Type'} : (@all _113580) = (@all _113580).
Proof. exact (eq_refl (@all _113580)). Qed.
Lemma lem5032061 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) : (term90 _113580 s P) = (term90 _113580 s P).
Proof. exact (MK_COMB (@lem5032060 _113580) (@lem5032059 _113580 s P)). Qed.
Lemma lem5032068 {_113580 : Type'} (P : _113580 -> Prop) (a : _113580) : (term91 _113580 P a) = (term91 _113580 P a).
Proof. exact (eq_refl (term91 _113580 P a)). Qed.
Lemma lem5032069 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term93 _113580 a s P) = (term93 _113580 a s P).
Proof. exact (MK_COMB (@lem5032068 _113580 P a) (@lem5032061 _113580 s P)). Qed.
Lemma lem5032090 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term116 _113580 a s P x) = (term116 _113580 a s P x).
Proof. exact (eq_refl (term116 _113580 a s P x)). Qed.
Lemma lem5032091 {_113580 : Type'} (x : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term118 _113580 x a s P) = (term118 _113580 x a s P).
Proof. exact (MK_COMB (@lem5032090 _113580 a s P x) (@lem5032069 _113580 a s P)). Qed.
Lemma lem5032092 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5032093 {_113580 : Type'} (x : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term166 _113580 x a s P) = (term166 _113580 x a s P).
Proof. exact (MK_COMB (@lem5032092) (@lem5032091 _113580 x a s P)). Qed.
Lemma lem5032094 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term168 _113580 a s P x) = (term168 _113580 a s P x).
Proof. exact (MK_COMB (@lem5032093 _113580 x a s P) (@lem5032043 _113580 a s P x)). Qed.
Lemma lem5032095 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term168 _113580 a s P x) : term168 _113580 a s P x.
Proof. exact (EQ_MP (@lem5032094 _113580 a s P x) (@lem5031995 _113580 a s P x h1)). Qed.
Lemma lem5032096 {_113580 : Type'} (x : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (h1 : term118 _113580 x a s P) : term118 _113580 x a s P.
Proof. exact (h1). Qed.
Lemma lem5032097 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term147 _113580 a s P x) : term147 _113580 a s P x.
Proof. exact (h1). Qed.
Lemma lem5032098 {_113580 : Type'} (x : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (h1 : term118 _113580 x a s P) : term93 _113580 a s P.
Proof. exact (proj2 (@lem5032096 _113580 x a s P h1)). Qed.
Lemma lem5032099 {_113580 : Type'} (x : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (h1 : term118 _113580 x a s P) : term29 _113580 a s P x.
Proof. exact (proj1 (@lem5032096 _113580 x a s P h1)). Qed.
Lemma lem5032100 {_113580 : Type'} (x : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (h1 : term118 _113580 x a s P) : term90 _113580 s P.
Proof. exact (proj2 (@lem5032098 _113580 x a s P h1)). Qed.
Lemma lem5032103 {_113580 : Type'} (x : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (h1 : term118 _113580 x a s P) : term9 _113580 a x s.
Proof. exact (proj1 (@lem5032099 _113580 x a s P h1)). Qed.
Lemma lem5032106 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term147 _113580 a s P x) : term132 _113580 a s P x.
Proof. exact (proj2 (@lem5032097 _113580 a s P x h1)). Qed.
Lemma lem5032107 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term147 _113580 a s P x) : term81 _113580 a s P.
Proof. exact (proj1 (@lem5032097 _113580 a s P x h1)). Qed.
Lemma lem5032109 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term59 _113580 s P x) : term59 _113580 s P x.
Proof. exact (h1). Qed.
Lemma lem5032136 {_113580 : Type'} (x : _113580) (a : _113580) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem5032148 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term83 _113580 s P x) = (term83 _113580 s P x).
Proof. exact (eq_refl (term83 _113580 s P x)). Qed.
Lemma lem5032149 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) : (term89 _113580 s P) = (term89 _113580 s P).
Proof. exact (fun_ext (fun x : _113580 => @lem5032148 _113580 s P x)). Qed.
Lemma lem5032150 {_113580 : Type'} : (@all _113580) = (@all _113580).
Proof. exact (eq_refl (@all _113580)). Qed.
Lemma lem5032152 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) : (term90 _113580 s P) = (term90 _113580 s P).
Proof. exact (MK_COMB (@lem5032150 _113580) (@lem5032149 _113580 s P)). Qed.
Lemma lem5032153 {_113580 : Type'} (x : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (h1 : term118 _113580 x a s P) : term90 _113580 s P.
Proof. exact (EQ_MP (@lem5032152 _113580 s P) (@lem5032100 _113580 x a s P h1)). Qed.
Lemma lem5032161 {_113580 : Type'} (x : _113580) (s : _113580 -> Prop) (h1 : @IN _113580 x s) : @IN _113580 x s.
Proof. exact (h1). Qed.
Lemma lem5032179 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term71 _113580 a s P x) = (term172 _113580 a s P x).
Proof. exact (@lem19699 (term173 _113580 x a) (term174 _113580 x s) (term67 _113580 P x)). Qed.
Lemma lem5032180 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term80 _113580 a s P) = (term175 _113580 a s P).
Proof. exact (fun_ext (fun x : _113580 => @lem5032179 _113580 a s P x)). Qed.
Lemma lem5032181 {_113580 : Type'} : (@all _113580) = (@all _113580).
Proof. exact (eq_refl (@all _113580)). Qed.
Lemma lem5032183 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term81 _113580 a s P) = (term176 _113580 a s P).
Proof. exact (MK_COMB (@lem5032181 _113580) (@lem5032180 _113580 a s P)). Qed.
Lemma lem5032184 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term147 _113580 a s P x) : term176 _113580 a s P.
Proof. exact (EQ_MP (@lem5032183 _113580 a s P) (@lem5032107 _113580 a s P x h1)). Qed.
Lemma lem5032188 {_113580 : Type'} (P : _113580 -> Prop) (a : _113580) (h1 : P a) : P a.
Proof. exact (h1). Qed.
Lemma lem5032206 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) : (term71 _113580 a s P x) = (term172 _113580 a s P x).
Proof. exact (@lem19699 (term173 _113580 x a) (term174 _113580 x s) (term67 _113580 P x)). Qed.
Lemma lem5032207 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term80 _113580 a s P) = (term175 _113580 a s P).
Proof. exact (fun_ext (fun x : _113580 => @lem5032206 _113580 a s P x)). Qed.
Lemma lem5032208 {_113580 : Type'} : (@all _113580) = (@all _113580).
Proof. exact (eq_refl (@all _113580)). Qed.
Lemma lem5032210 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term81 _113580 a s P) = (term176 _113580 a s P).
Proof. exact (MK_COMB (@lem5032208 _113580) (@lem5032207 _113580 a s P)). Qed.
Lemma lem5032211 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term147 _113580 a s P x) : term176 _113580 a s P.
Proof. exact (EQ_MP (@lem5032210 _113580 a s P) (@lem5032107 _113580 a s P x h1)). Qed.
Lemma lem5032223 {_113580 : Type'} (_64669 : _113580) (x : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (h1 : term118 _113580 x a s P) : term177 _113580 s P _64669.
Proof. exact (@lem5032153 _113580 x a s P h1 _64669). Qed.
Lemma lem5032224 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (_64669 : _113580) : (term177 _113580 s P _64669) = (term83 _113580 s P _64669).
Proof. exact (eq_refl (term177 _113580 s P _64669)). Qed.
Lemma lem5032226 {_113580 : Type'} (_64670 : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term147 _113580 a s P x) : term178 _113580 a s P _64670.
Proof. exact (@lem5032184 _113580 a s P x h1 _64670). Qed.
Lemma lem5032227 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (_64670 : _113580) : (term178 _113580 a s P _64670) = (term172 _113580 a s P _64670).
Proof. exact (eq_refl (term178 _113580 a s P _64670)). Qed.
Lemma lem5032228 {_113580 : Type'} (_64670 : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term147 _113580 a s P x) : term172 _113580 a s P _64670.
Proof. exact (EQ_MP (@lem5032227 _113580 a s P _64670) (@lem5032226 _113580 _64670 a s P x h1)). Qed.
Lemma lem5032229 {_113580 : Type'} (_64671 : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term147 _113580 a s P x) : term178 _113580 a s P _64671.
Proof. exact (@lem5032211 _113580 a s P x h1 _64671). Qed.
Lemma lem5032230 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (_64671 : _113580) : (term178 _113580 a s P _64671) = (term172 _113580 a s P _64671).
Proof. exact (eq_refl (term178 _113580 a s P _64671)). Qed.
Lemma lem5032231 {_113580 : Type'} (_64671 : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term147 _113580 a s P x) : term172 _113580 a s P _64671.
Proof. exact (EQ_MP (@lem5032230 _113580 a s P _64671) (@lem5032229 _113580 _64671 a s P x h1)). Qed.
Lemma lem5032245 {_113580 : Type'} (x : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (h1 : term118 _113580 x a s P) : P x.
Proof. exact (proj2 (@lem5032099 _113580 x a s P h1)). Qed.
Lemma lem5032247 {_113580 : Type'} (x : _113580) (a : _113580) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem5032255 {_113580 : Type'} (_64669 : _113580) (x : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (h1 : term118 _113580 x a s P) : term83 _113580 s P _64669.
Proof. exact (EQ_MP (@lem5032224 _113580 s P _64669) (@lem5032223 _113580 _64669 x a s P h1)). Qed.
Lemma lem5032259 {_113580 : Type'} (x : _113580) (s : _113580 -> Prop) (h1 : @IN _113580 x s) : @IN _113580 x s.
Proof. exact (h1). Qed.
Lemma lem5032261 {_113580 : Type'} (P : _113580 -> Prop) (a : _113580) (h1 : P a) : P a.
Proof. exact (h1). Qed.
Lemma lem5032267 {_113580 : Type'} (_64670 : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term147 _113580 a s P x) : term179 _113580 a P _64670.
Proof. exact (proj1 (@lem5032228 _113580 _64670 a s P x h1)). Qed.
Lemma lem5032289 {_113580 : Type'} (_64671 : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term147 _113580 a s P x) : term83 _113580 s P _64671.
Proof. exact (proj2 (@lem5032231 _113580 _64671 a s P x h1)). Qed.
Lemma lem5032317 {_113580 : Type'} (x : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (h1 : term118 _113580 x a s P) : term67 _113580 P a.
Proof. exact (proj1 (@lem5032098 _113580 x a s P h1)). Qed.
Lemma lem5032332 {_113580 : Type'} (P : _113580 -> Prop) : (term180 _113580 P) = (term180 _113580 P).
Proof. exact (eq_refl (term180 _113580 P)). Qed.
Lemma lem5032333 {_113580 : Type'} (P : _113580 -> Prop) (x : _113580) (a : _113580) (h1 : x = a) : (term181 _113580 P x) = (term181 _113580 P a).
Proof. exact (MK_COMB (@lem5032332 _113580 P) (@lem5032247 _113580 x a h1)). Qed.
Lemma lem5032334 {_113580 : Type'} (P : _113580 -> Prop) (a : _113580) : (term181 _113580 P a) = (P a).
Proof. exact (eq_refl (term181 _113580 P a)). Qed.
Lemma lem5032335 {_113580 : Type'} (P : _113580 -> Prop) (x : _113580) : (term182 _113580 P x) = (term182 _113580 P x).
Proof. exact (eq_refl (term182 _113580 P x)). Qed.
Lemma lem5032336 {_113580 : Type'} (x : _113580) (P : _113580 -> Prop) (a : _113580) : ((term181 _113580 P x) = (term181 _113580 P a)) = ((term181 _113580 P x) = (P a)).
Proof. exact (MK_COMB (@lem5032335 _113580 P x) (@lem5032334 _113580 P a)). Qed.
Lemma lem5032337 {_113580 : Type'} (P : _113580 -> Prop) (x : _113580) : (term181 _113580 P x) = (P x).
Proof. exact (eq_refl (term181 _113580 P x)). Qed.
Lemma lem5032338 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5032339 {_113580 : Type'} (P : _113580 -> Prop) (x : _113580) : (term182 _113580 P x) = (term183 _113580 P x).
Proof. exact (MK_COMB (@lem5032338) (@lem5032337 _113580 P x)). Qed.
Lemma lem5032340 {_113580 : Type'} (P : _113580 -> Prop) (a : _113580) : (P a) = (P a).
Proof. exact (eq_refl (P a)). Qed.
Lemma lem5032341 {_113580 : Type'} (x : _113580) (P : _113580 -> Prop) (a : _113580) : ((term181 _113580 P x) = (P a)) = ((P x) = (P a)).
Proof. exact (MK_COMB (@lem5032339 _113580 P x) (@lem5032340 _113580 P a)). Qed.
Lemma lem5032342 {_113580 : Type'} (x : _113580) (P : _113580 -> Prop) (a : _113580) : ((term181 _113580 P x) = (term181 _113580 P a)) = ((P x) = (P a)).
Proof. exact (TRANS (@lem5032336 _113580 x P a) (@lem5032341 _113580 x P a)). Qed.
Lemma lem5032343 {_113580 : Type'} (P : _113580 -> Prop) (x : _113580) (a : _113580) (h1 : x = a) : (P x) = (P a).
Proof. exact (EQ_MP (@lem5032342 _113580 x P a) (@lem5032333 _113580 P x a h1)). Qed.
Lemma lem5032346 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (a : _113580) (h1 : term118 _113580 x a s P) (h2 : x = a) : P a.
Proof. exact (EQ_MP (@lem5032343 _113580 P x a h2) (@lem5032245 _113580 x a s P h1)). Qed.
Lemma lem5032347 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (a : _113580) (h1 : term118 _113580 x a s P) (h2 : x = a) : term184 _113580 P a.
Proof. exact (fun h0 : term67 _113580 P a => @lem5032346 _113580 s P x a h1 h2). Qed.
Lemma lem5032349 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5032350 {_113580 : Type'} (P : _113580 -> Prop) (a : _113580) : (term184 _113580 P a) = (P a).
Proof. exact (@lem5032349 (P a)). Qed.
Lemma lem5032351 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (a : _113580) (h1 : term118 _113580 x a s P) (h2 : x = a) : P a.
Proof. exact (EQ_MP (@lem5032350 _113580 P a) (@lem5032347 _113580 s P x a h1 h2)). Qed.
Lemma lem5032354 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5032356 {_113580 : Type'} (P : _113580 -> Prop) (a : _113580) : (term67 _113580 P a) = (term186 _113580 P a).
Proof. exact (@lem5032354 (P a)). Qed.
Lemma lem5032359 {_113580 : Type'} (x : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (h1 : term118 _113580 x a s P) : term186 _113580 P a.
Proof. exact (EQ_MP (@lem5032356 _113580 P a) (@lem5032317 _113580 x a s P h1)). Qed.
Lemma lem5032362 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (a : _113580) (h1 : term118 _113580 x a s P) (h2 : x = a) : False.
Proof. exact (@lem5032359 _113580 x a s P h1 (@lem5032351 _113580 s P x a h1 h2)). Qed.
Lemma lem5032363 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (a : _113580) (h1 : term118 _113580 x a s P) (h2 : x = a) : term187.
Proof. exact (fun h0 : ~ False => @lem5032362 _113580 s P x a h1 h2). Qed.
Lemma lem5032365 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5032366 : term187 = False.
Proof. exact (@lem5032365 False). Qed.
Lemma lem5032369 {_113580 : Type'} (x : _113580) (s : _113580 -> Prop) (h1 : @IN _113580 x s) : @IN _113580 x s.
Proof. exact (h1). Qed.
Lemma lem5032370 {_113580 : Type'} (x : _113580) (s : _113580 -> Prop) (h1 : @IN _113580 x s) : term188 _113580 x s.
Proof. exact (fun h0 : term174 _113580 x s => @lem5032369 _113580 x s h1). Qed.
Lemma lem5032372 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5032373 {_113580 : Type'} (x : _113580) (s : _113580 -> Prop) : (term188 _113580 x s) = (@IN _113580 x s).
Proof. exact (@lem5032372 (@IN _113580 x s)). Qed.
Lemma lem5032374 {_113580 : Type'} (x : _113580) (s : _113580 -> Prop) (h1 : @IN _113580 x s) : @IN _113580 x s.
Proof. exact (EQ_MP (@lem5032373 _113580 x s) (@lem5032370 _113580 x s h1)). Qed.
Lemma lem5032376 {_113580 : Type'} (x : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (h1 : term118 _113580 x a s P) : P x.
Proof. exact (proj2 (@lem5032099 _113580 x a s P h1)). Qed.
Lemma lem5032377 {_113580 : Type'} (x : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (h1 : term118 _113580 x a s P) : term184 _113580 P x.
Proof. exact (fun h0 : term67 _113580 P x => @lem5032376 _113580 x a s P h1). Qed.
Lemma lem5032379 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5032380 {_113580 : Type'} (P : _113580 -> Prop) (x : _113580) : (term184 _113580 P x) = (P x).
Proof. exact (@lem5032379 (P x)). Qed.
Lemma lem5032381 {_113580 : Type'} (x : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (h1 : term118 _113580 x a s P) : P x.
Proof. exact (EQ_MP (@lem5032380 _113580 P x) (@lem5032377 _113580 x a s P h1)). Qed.
Lemma lem5032383 (a : Prop) (b : Prop) : (term189 a b) = (term190 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5032384 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (_64669 : _113580) : (term83 _113580 s P _64669) = (term82 _113580 s P _64669).
Proof. exact (@lem5032383 (@IN _113580 _64669 s) (P _64669)). Qed.
Lemma lem5032386 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5032387 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (_64669 : _113580) : (term82 _113580 s P _64669) = (term191 _113580 s P _64669).
Proof. exact (@lem5032386 (term59 _113580 s P _64669)). Qed.
Lemma lem5032388 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (_64669 : _113580) : (term83 _113580 s P _64669) = (term191 _113580 s P _64669).
Proof. exact (TRANS (@lem5032384 _113580 s P _64669) (@lem5032387 _113580 s P _64669)). Qed.
Lemma lem5032390 {_113580 : Type'} (a : _113580) (P : _113580 -> Prop) (x : _113580) (s : _113580 -> Prop) (h1 : term118 _113580 x a s P) (h2 : @IN _113580 x s) : term59 _113580 s P x.
Proof. exact (conj (@lem5032374 _113580 x s h2) (@lem5032381 _113580 x a s P h1)). Qed.
Lemma lem5032392 {_113580 : Type'} (_64669 : _113580) (x : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (h1 : term118 _113580 x a s P) : term191 _113580 s P _64669.
Proof. exact (EQ_MP (@lem5032388 _113580 s P _64669) (@lem5032255 _113580 _64669 x a s P h1)). Qed.
Lemma lem5032393 {_113580 : Type'} (_64669 : _113580) (x : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (h1 : term118 _113580 x a s P) : term191 _113580 s P _64669.
Proof. exact (@lem5032392 _113580 _64669 x a s P h1). Qed.
Lemma lem5032394 {_113580 : Type'} (x : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (h1 : term118 _113580 x a s P) : term191 _113580 s P x.
Proof. exact (@lem5032393 _113580 x x a s P h1). Qed.
Lemma lem5032397 {_113580 : Type'} (a : _113580) (P : _113580 -> Prop) (x : _113580) (s : _113580 -> Prop) (h1 : term118 _113580 x a s P) (h2 : @IN _113580 x s) : False.
Proof. exact (@lem5032394 _113580 x a s P h1 (@lem5032390 _113580 a P x s h1 h2)). Qed.
Lemma lem5032398 {_113580 : Type'} (a : _113580) (P : _113580 -> Prop) (x : _113580) (s : _113580 -> Prop) (h1 : term118 _113580 x a s P) (h2 : @IN _113580 x s) : term187.
Proof. exact (fun h0 : ~ False => @lem5032397 _113580 a P x s h1 h2). Qed.
Lemma lem5032400 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5032401 : term187 = False.
Proof. exact (@lem5032400 False). Qed.
Lemma lem5032402 {_113580 : Type'} (a : _113580) (P : _113580 -> Prop) (x : _113580) (s : _113580 -> Prop) (h1 : term118 _113580 x a s P) (h2 : @IN _113580 x s) : False.
Proof. exact (EQ_MP (@lem5032401) (@lem5032398 _113580 a P x s h1 h2)). Qed.
Lemma lem5032439 {_113580 : Type'} (x : _113580) : x = x.
Proof. exact (@lem21386 _113580 x). Qed.
Lemma lem5032440 {_113580 : Type'} (x : _113580) : x = x.
Proof. exact (@lem5032439 _113580 x). Qed.
Lemma lem5032441 {_113580 : Type'} (a : _113580) : a = a.
Proof. exact (@lem5032440 _113580 a). Qed.
Lemma lem5032442 {_113580 : Type'} (a : _113580) : term192 _113580 a.
Proof. exact (fun h0 : term193 _113580 a => @lem5032441 _113580 a). Qed.
Lemma lem5032444 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5032445 {_113580 : Type'} (a : _113580) : (term192 _113580 a) = (a = a).
Proof. exact (@lem5032444 (a = a)). Qed.
Lemma lem5032446 {_113580 : Type'} (a : _113580) : a = a.
Proof. exact (EQ_MP (@lem5032445 _113580 a) (@lem5032442 _113580 a)). Qed.
Lemma lem5032448 {_113580 : Type'} (P : _113580 -> Prop) (a : _113580) (h1 : P a) : P a.
Proof. exact (h1). Qed.
Lemma lem5032449 {_113580 : Type'} (P : _113580 -> Prop) (a : _113580) (h1 : P a) : term184 _113580 P a.
Proof. exact (fun h0 : term67 _113580 P a => @lem5032448 _113580 P a h1). Qed.
Lemma lem5032451 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5032452 {_113580 : Type'} (P : _113580 -> Prop) (a : _113580) : (term184 _113580 P a) = (P a).
Proof. exact (@lem5032451 (P a)). Qed.
Lemma lem5032453 {_113580 : Type'} (P : _113580 -> Prop) (a : _113580) (h1 : P a) : P a.
Proof. exact (EQ_MP (@lem5032452 _113580 P a) (@lem5032449 _113580 P a h1)). Qed.
Lemma lem5032455 (a : Prop) (b : Prop) : (term189 a b) = (term190 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5032456 {_113580 : Type'} (a : _113580) (P : _113580 -> Prop) (_64670 : _113580) : (term179 _113580 a P _64670) = (term194 _113580 a P _64670).
Proof. exact (@lem5032455 (_64670 = a) (P _64670)). Qed.
Lemma lem5032458 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5032459 {_113580 : Type'} (a : _113580) (P : _113580 -> Prop) (_64670 : _113580) : (term194 _113580 a P _64670) = (term195 _113580 a P _64670).
Proof. exact (@lem5032458 (term196 _113580 a P _64670)). Qed.
Lemma lem5032460 {_113580 : Type'} (a : _113580) (P : _113580 -> Prop) (_64670 : _113580) : (term179 _113580 a P _64670) = (term195 _113580 a P _64670).
Proof. exact (TRANS (@lem5032456 _113580 a P _64670) (@lem5032459 _113580 a P _64670)). Qed.
Lemma lem5032462 {_113580 : Type'} (P : _113580 -> Prop) (a : _113580) (h1 : P a) : term197 _113580 P a.
Proof. exact (conj (@lem5032446 _113580 a) (@lem5032453 _113580 P a h1)). Qed.
Lemma lem5032464 {_113580 : Type'} (_64670 : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term147 _113580 a s P x) : term195 _113580 a P _64670.
Proof. exact (EQ_MP (@lem5032460 _113580 a P _64670) (@lem5032267 _113580 _64670 a s P x h1)). Qed.
Lemma lem5032465 {_113580 : Type'} (_64670 : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term147 _113580 a s P x) : term195 _113580 a P _64670.
Proof. exact (@lem5032464 _113580 _64670 a s P x h1). Qed.
Lemma lem5032466 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term147 _113580 a s P x) : term198 _113580 P a.
Proof. exact (@lem5032465 _113580 a a s P x h1). Qed.
Lemma lem5032469 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : P a) (h2 : term147 _113580 a s P x) : False.
Proof. exact (@lem5032466 _113580 a s P x h2 (@lem5032462 _113580 P a h1)). Qed.
Lemma lem5032470 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : P a) (h2 : term147 _113580 a s P x) : term187.
Proof. exact (fun h0 : ~ False => @lem5032469 _113580 a s P x h1 h2). Qed.
Lemma lem5032472 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5032473 : term187 = False.
Proof. exact (@lem5032472 False). Qed.
Lemma lem5032474 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : P a) (h2 : term147 _113580 a s P x) : False.
Proof. exact (EQ_MP (@lem5032473) (@lem5032470 _113580 a s P x h1 h2)). Qed.
Lemma lem5032511 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term59 _113580 s P x) : @IN _113580 x s.
Proof. exact (proj1 (@lem5032109 _113580 s P x h1)). Qed.
Lemma lem5032512 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term59 _113580 s P x) : term188 _113580 x s.
Proof. exact (fun h0 : term174 _113580 x s => @lem5032511 _113580 s P x h1). Qed.
Lemma lem5032514 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5032515 {_113580 : Type'} (x : _113580) (s : _113580 -> Prop) : (term188 _113580 x s) = (@IN _113580 x s).
Proof. exact (@lem5032514 (@IN _113580 x s)). Qed.
Lemma lem5032516 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term59 _113580 s P x) : @IN _113580 x s.
Proof. exact (EQ_MP (@lem5032515 _113580 x s) (@lem5032512 _113580 s P x h1)). Qed.
Lemma lem5032518 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term59 _113580 s P x) : P x.
Proof. exact (proj2 (@lem5032109 _113580 s P x h1)). Qed.
Lemma lem5032519 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term59 _113580 s P x) : term184 _113580 P x.
Proof. exact (fun h0 : term67 _113580 P x => @lem5032518 _113580 s P x h1). Qed.
Lemma lem5032521 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5032522 {_113580 : Type'} (P : _113580 -> Prop) (x : _113580) : (term184 _113580 P x) = (P x).
Proof. exact (@lem5032521 (P x)). Qed.
Lemma lem5032523 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term59 _113580 s P x) : P x.
Proof. exact (EQ_MP (@lem5032522 _113580 P x) (@lem5032519 _113580 s P x h1)). Qed.
Lemma lem5032525 (a : Prop) (b : Prop) : (term189 a b) = (term190 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5032526 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (_64671 : _113580) : (term83 _113580 s P _64671) = (term82 _113580 s P _64671).
Proof. exact (@lem5032525 (@IN _113580 _64671 s) (P _64671)). Qed.
Lemma lem5032528 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5032529 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (_64671 : _113580) : (term82 _113580 s P _64671) = (term191 _113580 s P _64671).
Proof. exact (@lem5032528 (term59 _113580 s P _64671)). Qed.
Lemma lem5032530 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (_64671 : _113580) : (term83 _113580 s P _64671) = (term191 _113580 s P _64671).
Proof. exact (TRANS (@lem5032526 _113580 s P _64671) (@lem5032529 _113580 s P _64671)). Qed.
Lemma lem5032532 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term59 _113580 s P x) : term59 _113580 s P x.
Proof. exact (conj (@lem5032516 _113580 s P x h1) (@lem5032523 _113580 s P x h1)). Qed.
Lemma lem5032534 {_113580 : Type'} (_64671 : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term147 _113580 a s P x) : term191 _113580 s P _64671.
Proof. exact (EQ_MP (@lem5032530 _113580 s P _64671) (@lem5032289 _113580 _64671 a s P x h1)). Qed.
Lemma lem5032535 {_113580 : Type'} (_64671 : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term147 _113580 a s P x) : term191 _113580 s P _64671.
Proof. exact (@lem5032534 _113580 _64671 a s P x h1). Qed.
Lemma lem5032536 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term147 _113580 a s P x) : term191 _113580 s P x.
Proof. exact (@lem5032535 _113580 x a s P x h1). Qed.
Lemma lem5032539 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term147 _113580 a s P x) (h2 : term59 _113580 s P x) : False.
Proof. exact (@lem5032536 _113580 a s P x h1 (@lem5032532 _113580 s P x h2)). Qed.
Lemma lem5032540 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term147 _113580 a s P x) (h2 : term59 _113580 s P x) : term187.
Proof. exact (fun h0 : ~ False => @lem5032539 _113580 a s P x h1 h2). Qed.
Lemma lem5032542 (p : Prop) : (term185 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5032543 : term187 = False.
Proof. exact (@lem5032542 False). Qed.
Lemma lem5032544 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term147 _113580 a s P x) (h2 : term59 _113580 s P x) : False.
Proof. exact (EQ_MP (@lem5032543) (@lem5032540 _113580 a s P x h1 h2)). Qed.
Lemma lem5032545 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (a : _113580) (h1 : term118 _113580 x a s P) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem5032366) (@lem5032363 _113580 s P x a h1 h2)). Qed.
Lemma lem5032546 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : P a) (h2 : term147 _113580 a s P x) : (P a) = False.
Proof. exact (prop_ext (fun h3 : P a => @lem5032474 _113580 a s P x h1 h2) (fun h3 : False => @lem5032261 _113580 P a h1)). Qed.
Lemma lem5032547 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : P a) (h2 : term147 _113580 a s P x) : False.
Proof. exact (EQ_MP (@lem5032546 _113580 a s P x h1 h2) (@lem5032261 _113580 P a h1)). Qed.
Lemma lem5032548 {_113580 : Type'} (a : _113580) (P : _113580 -> Prop) (x : _113580) (s : _113580 -> Prop) (h1 : term118 _113580 x a s P) (h2 : @IN _113580 x s) : (@IN _113580 x s) = False.
Proof. exact (prop_ext (fun h3 : @IN _113580 x s => @lem5032402 _113580 a P x s h1 h2) (fun h3 : False => @lem5032259 _113580 x s h2)). Qed.
Lemma lem5032549 {_113580 : Type'} (a : _113580) (P : _113580 -> Prop) (x : _113580) (s : _113580 -> Prop) (h1 : term118 _113580 x a s P) (h2 : @IN _113580 x s) : False.
Proof. exact (EQ_MP (@lem5032548 _113580 a P x s h1 h2) (@lem5032259 _113580 x s h2)). Qed.
Lemma lem5032550 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (a : _113580) (h1 : term118 _113580 x a s P) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem5032545 _113580 s P x a h1 h2) (fun h3 : False => @lem5032247 _113580 x a h2)). Qed.
Lemma lem5032551 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (a : _113580) (h1 : term118 _113580 x a s P) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem5032550 _113580 s P x a h1 h2) (@lem5032247 _113580 x a h2)). Qed.
Lemma lem5032552 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : P a) (h2 : term147 _113580 a s P x) : (P a) = False.
Proof. exact (prop_ext (fun h3 : P a => @lem5032547 _113580 a s P x h1 h2) (fun h3 : False => @lem5032188 _113580 P a h1)). Qed.
Lemma lem5032553 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : P a) (h2 : term147 _113580 a s P x) : False.
Proof. exact (EQ_MP (@lem5032552 _113580 a s P x h1 h2) (@lem5032188 _113580 P a h1)). Qed.
Lemma lem5032554 {_113580 : Type'} (a : _113580) (P : _113580 -> Prop) (x : _113580) (s : _113580 -> Prop) (h1 : term118 _113580 x a s P) (h2 : @IN _113580 x s) : (@IN _113580 x s) = False.
Proof. exact (prop_ext (fun h3 : @IN _113580 x s => @lem5032549 _113580 a P x s h1 h2) (fun h3 : False => @lem5032161 _113580 x s h2)). Qed.
Lemma lem5032555 {_113580 : Type'} (a : _113580) (P : _113580 -> Prop) (x : _113580) (s : _113580 -> Prop) (h1 : term118 _113580 x a s P) (h2 : @IN _113580 x s) : False.
Proof. exact (EQ_MP (@lem5032554 _113580 a P x s h1 h2) (@lem5032161 _113580 x s h2)). Qed.
Lemma lem5032556 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (a : _113580) (h1 : term118 _113580 x a s P) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem5032551 _113580 s P x a h1 h2) (fun h3 : False => @lem5032136 _113580 x a h2)). Qed.
Lemma lem5032557 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (a : _113580) (h1 : term118 _113580 x a s P) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem5032556 _113580 s P x a h1 h2) (@lem5032136 _113580 x a h2)). Qed.
Lemma lem5032558 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : P a) (h2 : term147 _113580 a s P x) : (P a) = False.
Proof. exact (prop_ext (fun h3 : P a => @lem5032553 _113580 a s P x h1 h2) (fun h3 : False => @lem5032188 _113580 P a h1)). Qed.
Lemma lem5032559 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : P a) (h2 : term147 _113580 a s P x) : False.
Proof. exact (EQ_MP (@lem5032558 _113580 a s P x h1 h2) (@lem5032188 _113580 P a h1)). Qed.
Lemma lem5032560 {_113580 : Type'} (a : _113580) (P : _113580 -> Prop) (x : _113580) (s : _113580 -> Prop) (h1 : term118 _113580 x a s P) (h2 : @IN _113580 x s) : (@IN _113580 x s) = False.
Proof. exact (prop_ext (fun h3 : @IN _113580 x s => @lem5032555 _113580 a P x s h1 h2) (fun h3 : False => @lem5032161 _113580 x s h2)). Qed.
Lemma lem5032561 {_113580 : Type'} (a : _113580) (P : _113580 -> Prop) (x : _113580) (s : _113580 -> Prop) (h1 : term118 _113580 x a s P) (h2 : @IN _113580 x s) : False.
Proof. exact (EQ_MP (@lem5032560 _113580 a P x s h1 h2) (@lem5032161 _113580 x s h2)). Qed.
Lemma lem5032562 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (a : _113580) (h1 : term118 _113580 x a s P) (h2 : x = a) : (x = a) = False.
Proof. exact (prop_ext (fun h3 : x = a => @lem5032557 _113580 s P x a h1 h2) (fun h3 : False => @lem5032136 _113580 x a h2)). Qed.
Lemma lem5032563 {_113580 : Type'} (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (a : _113580) (h1 : term118 _113580 x a s P) (h2 : x = a) : False.
Proof. exact (EQ_MP (@lem5032562 _113580 s P x a h1 h2) (@lem5032136 _113580 x a h2)). Qed.
Lemma lem5032564 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term147 _113580 a s P x) : False.
Proof. exact (or_elim (@lem5032106 _113580 a s P x h1) (fun h0 : P a => @lem5032559 _113580 a s P x h0 h1) (fun h0 : term59 _113580 s P x => @lem5032544 _113580 a s P x h1 h0)). Qed.
Lemma lem5032565 {_113580 : Type'} (x : _113580) (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (h1 : term118 _113580 x a s P) : False.
Proof. exact (or_elim (@lem5032103 _113580 x a s P h1) (fun h0 : x = a => @lem5032563 _113580 s P x a h1 h0) (fun h0 : @IN _113580 x s => @lem5032561 _113580 a P x s h1 h0)). Qed.
Lemma lem5032566 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term168 _113580 a s P x) : False.
Proof. exact (or_elim (@lem5032095 _113580 a s P x h1) (fun h0 : term118 _113580 x a s P => @lem5032565 _113580 x a s P h0) (fun h0 : term147 _113580 a s P x => @lem5032564 _113580 a s P x h0)). Qed.
Lemma lem5032567 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term168 _113580 a s P x) : (term168 _113580 a s P x) = False.
Proof. exact (prop_ext (fun h2 : term168 _113580 a s P x => @lem5032566 _113580 a s P x h1) (fun h2 : False => @lem5032095 _113580 a s P x h1)). Qed.
Lemma lem5032568 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (x : _113580) (h1 : term168 _113580 a s P x) : False.
Proof. exact (EQ_MP (@lem5032567 _113580 a s P x h1) (@lem5032095 _113580 a s P x h1)). Qed.
Lemma lem5032569 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (h1 : term64 _113580 a s P) : False.
Proof. exact (ex_elim (@lem5031994 _113580 a s P h1) (fun x : _113580 => fun h0 : term170 _113580 a s P x => @lem5032568 _113580 a s P x h0)). Qed.
Lemma lem5032570 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (h1 : term64 _113580 a s P) : (term64 _113580 a s P) = False.
Proof. exact (prop_ext (fun h2 : term64 _113580 a s P => @lem5032569 _113580 a s P h1) (fun h2 : False => @lem5031651 _113580 a s P h1)). Qed.
Lemma lem5032571 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) (h1 : term64 _113580 a s P) : False.
Proof. exact (EQ_MP (@lem5032570 _113580 a s P h1) (@lem5031651 _113580 a s P h1)). Qed.
Lemma lem5032572 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : term63 _113580 a s P.
Proof. exact (fun h0 : term64 _113580 a s P => @lem5032571 _113580 a s P h0). Qed.
Lemma lem5032573 {_113580 : Type'} (a : _113580) (s : _113580 -> Prop) (P : _113580 -> Prop) : (term33 _113580 a s P) = (term36 _113580 a s P).
Proof. exact (EQ_MP (@lem5031650 _113580 a s P) (@lem5032572 _113580 a s P)). Qed.
Lemma lem5032578 {_113580 : Type'} (a : _113580) (P : _113580 -> Prop) : term40 _113580 a P.
Proof. exact (fun s : _113580 -> Prop => @lem5032573 _113580 a s P). Qed.
Lemma lem5032583 {_113580 : Type'} (P : _113580 -> Prop) : term44 _113580 P.
Proof. exact (fun a : _113580 => @lem5032578 _113580 a P). Qed.
Lemma lem5032588 {_113580 : Type'} : term48 _113580.
Proof. exact (fun P : _113580 -> Prop => @lem5032583 _113580 P). Qed.
Lemma lem5032589 {_113580 : Type'} : term52 _113580.
Proof. exact (EQ_MP (@lem5031646 _113580) (@lem5032588 _113580)). Qed.
Lemma lem5032591 {_113580 : Type'} : term52 _113580.
Proof. exact (@lem5031473 _113580 (@lem5032589 _113580)). Qed.
Lemma lem5032592 {_113580 : Type'} (h1 : term53 _113580) : False.
Proof. exact (@lem5032591 _113580 (@lem5031457 _113580 h1)). Qed.
Lemma lem5032593 {_113580 : Type'} (h1 : term53 _113580) : (term53 _113580) = False.
Proof. exact (prop_ext (fun h2 : term53 _113580 => @lem5032592 _113580 h1) (fun h2 : False => @lem5031457 _113580 h1)). Qed.
Lemma lem5032594 {_113580 : Type'} (h1 : term53 _113580) : False.
Proof. exact (EQ_MP (@lem5032593 _113580 h1) (@lem5031457 _113580 h1)). Qed.
Lemma lem5032595 {_113580 : Type'} : term52 _113580.
Proof. exact (fun h0 : term53 _113580 => @lem5032594 _113580 h0). Qed.
Lemma lem5032596 {_113580 : Type'} : term48 _113580.
Proof. exact (EQ_MP (@lem5031456 _113580) (@lem5032595 _113580)). Qed.
Lemma lem5032597 {_113540 _113580 : Type'} : term49 _113540 _113580.
Proof. exact (EQ_MP (@lem5031452 _113540 _113580) (@lem5032596 _113580)). Qed.
