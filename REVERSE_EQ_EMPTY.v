Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REVERSE_EQ_EMPTY_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REVERSE_spec.
Require Import REVERSE_REVERSE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16445_spec.
Require Import thm16446_spec.
Require Import thm16457_spec.
Require Import thm16458_spec.
Require Import thm16474_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
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
Require Import thm21385_spec.
Require Import thm69_spec.
Lemma lem1112281 {A : Type'} (l : list A) : term0 A l.
Proof. exact (fun x : A => @lem1096526 A l x). Qed.
Lemma lem1112282 {A : Type'} : term1 A.
Proof. exact (fun l : list A => @lem1112281 A l). Qed.
Lemma lem1112284 (p : Prop) : p = (term2 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1112285 {A : Type'} : (term3 A) = (term4 A).
Proof. exact (@lem1112284 (term3 A)). Qed.
Lemma lem1112286 {A : Type'} : (term4 A) = (term3 A).
Proof. exact (SYM (@lem1112285 A)). Qed.
Lemma lem1112287 {A : Type'} (h1 : term5 A) : term5 A.
Proof. exact (h1). Qed.
Lemma lem1112288 {A : Type'} : term6 A.
Proof. exact (@lem1112270 A). Qed.
Lemma lem1112290 {A : Type'} : term1 A.
Proof. exact (@lem1112282 A). Qed.
Lemma lem1112295 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (h1). Qed.
Lemma lem1112296 {A : Type'} : term8 A.
Proof. exact (fun h0 : term7 A => @lem1112295 A h0). Qed.
Lemma lem1112297 {A : Type'} (h1 : term8 A) : term8 A.
Proof. exact (h1). Qed.
Lemma lem1112298 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (h1). Qed.
Lemma lem1112299 {A : Type'} (h1 : term7 A) (h2 : term8 A) : term7 A.
Proof. exact (@lem1112297 A h2 (@lem1112298 A h1)). Qed.
Lemma lem1112300 {A : Type'} (h1 : term7 A) : term9 A.
Proof. exact (fun h0 : term8 A => @lem1112299 A h1 h0). Qed.
Lemma lem1112301 {A : Type'} (h1 : term8 A) : term8 A.
Proof. exact (h1). Qed.
Lemma lem1112302 {A : Type'} (h1 : term7 A) (h2 : term8 A) : term7 A.
Proof. exact (@lem1112300 A h1 (@lem1112301 A h2)). Qed.
Lemma lem1112303 {A : Type'} (h1 : term8 A) : term8 A.
Proof. exact (fun h0 : term7 A => @lem1112302 A h0 h1). Qed.
Lemma lem1112304 {A : Type'} : term10 A.
Proof. exact (fun h0 : term8 A => @lem1112303 A h0). Qed.
Lemma lem1112307 {A : Type'} : term8 A.
Proof. exact (@lem1112304 A (@lem1112296 A)). Qed.
Lemma lem1112308 {A : Type'} : term8 A.
Proof. exact (@lem1112307 A). Qed.
Lemma lem1112322 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term11 A P Q) = (term12 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem1112323 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term11 A P Q) = (term12 A P Q).
Proof. exact (@lem1112322 A P Q). Qed.
Lemma lem1112324 {A : Type'} (l : list A) : (term13 A l) = (term14 A l).
Proof. exact (@lem1112323 A (term15 A) (term16 A l)). Qed.
Lemma lem1112325 {A : Type'} (x : A) : (term17 A x) = ((@List.rev A (@nil A)) = (@nil A)).
Proof. exact (eq_refl (term17 A x)). Qed.
Lemma lem1112326 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1112327 {A : Type'} (x : A) : (term18 A x) = (term19 A).
Proof. exact (MK_COMB (@lem1112326) (@lem1112325 A x)). Qed.
Lemma lem1112328 {A : Type'} (l : list A) (x : A) : (term20 A l x) = ((term21 A x l) = (term22 A l x)).
Proof. exact (eq_refl (term20 A l x)). Qed.
Lemma lem1112329 {A : Type'} (l : list A) (x : A) : (term23 A l x) = (term24 A l x).
Proof. exact (MK_COMB (@lem1112327 A x) (@lem1112328 A l x)). Qed.
Lemma lem1112330 {A : Type'} (l : list A) : (term25 A l) = (term26 A l).
Proof. exact (fun_ext (fun x : A => @lem1112329 A l x)). Qed.
Lemma lem1112331 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1112332 {A : Type'} (l : list A) : (term13 A l) = (term0 A l).
Proof. exact (MK_COMB (@lem1112331 A) (@lem1112330 A l)). Qed.
Lemma lem1112333 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1112334 {A : Type'} (l : list A) : (term27 A l) = (term28 A l).
Proof. exact (MK_COMB (@lem1112333) (@lem1112332 A l)). Qed.
Lemma lem1112335 {A : Type'} (x : A) : (term17 A x) = ((@List.rev A (@nil A)) = (@nil A)).
Proof. exact (eq_refl (term17 A x)). Qed.
Lemma lem1112336 {A : Type'} : (term29 A) = (term15 A).
Proof. exact (fun_ext (fun x : A => @lem1112335 A x)). Qed.
Lemma lem1112337 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1112338 {A : Type'} : (term30 A) = (term31 A).
Proof. exact (MK_COMB (@lem1112337 A) (@lem1112336 A)). Qed.
Lemma lem1112339 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1112340 {A : Type'} : (term32 A) = (term33 A).
Proof. exact (MK_COMB (@lem1112339) (@lem1112338 A)). Qed.
Lemma lem1112341 {A : Type'} (l : list A) (x : A) : (term20 A l x) = ((term21 A x l) = (term22 A l x)).
Proof. exact (eq_refl (term20 A l x)). Qed.
Lemma lem1112342 {A : Type'} (l : list A) : (term34 A l) = (term16 A l).
Proof. exact (fun_ext (fun x : A => @lem1112341 A l x)). Qed.
Lemma lem1112343 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1112344 {A : Type'} (l : list A) : (term35 A l) = (term36 A l).
Proof. exact (MK_COMB (@lem1112343 A) (@lem1112342 A l)). Qed.
Lemma lem1112345 {A : Type'} (l : list A) : (term14 A l) = (term37 A l).
Proof. exact (MK_COMB (@lem1112340 A) (@lem1112344 A l)). Qed.
Lemma lem1112346 {A : Type'} (l : list A) : ((term13 A l) = (term14 A l)) = ((term0 A l) = (term37 A l)).
Proof. exact (MK_COMB (@lem1112334 A l) (@lem1112345 A l)). Qed.
Lemma lem1112347 {A : Type'} (l : list A) : (term0 A l) = (term37 A l).
Proof. exact (EQ_MP (@lem1112346 A l) (@lem1112324 A l)). Qed.
Lemma lem1112351 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem16458 A t) (@lem16457 A t)). Qed.
Lemma lem1112352 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (@lem1112351 A t). Qed.
Lemma lem1112353 {A : Type'} : (term31 A) = ((@List.rev A (@nil A)) = (@nil A)).
Proof. exact (@lem1112352 A ((@List.rev A (@nil A)) = (@nil A))). Qed.
Lemma lem1112354 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1112355 {A : Type'} : (term33 A) = (term19 A).
Proof. exact (MK_COMB (@lem1112354) (@lem1112353 A)). Qed.
Lemma lem1112360 {A : Type'} (l : list A) : (term36 A l) = (term36 A l).
Proof. exact (eq_refl (term36 A l)). Qed.
Lemma lem1112361 {A : Type'} (l : list A) : (term37 A l) = (term39 A l).
Proof. exact (MK_COMB (@lem1112355 A) (@lem1112360 A l)). Qed.
Lemma lem1112364 {A : Type'} (l : list A) : (term0 A l) = (term39 A l).
Proof. exact (TRANS (@lem1112347 A l) (@lem1112361 A l)). Qed.
Lemma lem1112365 {A : Type'} : (term40 A) = (term41 A).
Proof. exact (fun_ext (fun l : list A => @lem1112364 A l)). Qed.
Lemma lem1112366 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1112367 {A : Type'} : (term1 A) = (term42 A).
Proof. exact (MK_COMB (@lem1112366 A) (@lem1112365 A)). Qed.
Lemma lem1112369 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term11 A P Q) = (term12 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem1112370 {A : Type'} (P : type1143 A) (Q : type1143 A) : (term43 A P Q) = (term44 A P Q).
Proof. exact (@lem1112369 (list A) P Q). Qed.
Lemma lem1112371 {A : Type'} : (term45 A) = (term46 A).
Proof. exact (@lem1112370 A (term47 A) (term48 A)). Qed.
Lemma lem1112372 {A : Type'} (l : list A) : (term49 A l) = ((@List.rev A (@nil A)) = (@nil A)).
Proof. exact (eq_refl (term49 A l)). Qed.
Lemma lem1112373 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1112374 {A : Type'} (l : list A) : (term50 A l) = (term19 A).
Proof. exact (MK_COMB (@lem1112373) (@lem1112372 A l)). Qed.
Lemma lem1112375 {A : Type'} (l : list A) : (term51 A l) = (term36 A l).
Proof. exact (eq_refl (term51 A l)). Qed.
Lemma lem1112376 {A : Type'} (l : list A) : (term52 A l) = (term39 A l).
Proof. exact (MK_COMB (@lem1112374 A l) (@lem1112375 A l)). Qed.
Lemma lem1112377 {A : Type'} : (term53 A) = (term41 A).
Proof. exact (fun_ext (fun l : list A => @lem1112376 A l)). Qed.
Lemma lem1112378 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1112379 {A : Type'} : (term45 A) = (term42 A).
Proof. exact (MK_COMB (@lem1112378 A) (@lem1112377 A)). Qed.
Lemma lem1112380 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1112381 {A : Type'} : (term54 A) = (term55 A).
Proof. exact (MK_COMB (@lem1112380) (@lem1112379 A)). Qed.
Lemma lem1112382 {A : Type'} (l : list A) : (term49 A l) = ((@List.rev A (@nil A)) = (@nil A)).
Proof. exact (eq_refl (term49 A l)). Qed.
Lemma lem1112383 {A : Type'} : (term56 A) = (term47 A).
Proof. exact (fun_ext (fun l : list A => @lem1112382 A l)). Qed.
Lemma lem1112384 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1112385 {A : Type'} : (term57 A) = (term58 A).
Proof. exact (MK_COMB (@lem1112384 A) (@lem1112383 A)). Qed.
Lemma lem1112386 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1112387 {A : Type'} : (term59 A) = (term60 A).
Proof. exact (MK_COMB (@lem1112386) (@lem1112385 A)). Qed.
Lemma lem1112388 {A : Type'} (l : list A) : (term51 A l) = (term36 A l).
Proof. exact (eq_refl (term51 A l)). Qed.
Lemma lem1112389 {A : Type'} : (term61 A) = (term48 A).
Proof. exact (fun_ext (fun l : list A => @lem1112388 A l)). Qed.
Lemma lem1112390 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1112391 {A : Type'} : (term62 A) = (term63 A).
Proof. exact (MK_COMB (@lem1112390 A) (@lem1112389 A)). Qed.
Lemma lem1112392 {A : Type'} : (term46 A) = (term64 A).
Proof. exact (MK_COMB (@lem1112387 A) (@lem1112391 A)). Qed.
Lemma lem1112393 {A : Type'} : ((term45 A) = (term46 A)) = ((term42 A) = (term64 A)).
Proof. exact (MK_COMB (@lem1112381 A) (@lem1112392 A)). Qed.
Lemma lem1112394 {A : Type'} : (term42 A) = (term64 A).
Proof. exact (EQ_MP (@lem1112393 A) (@lem1112371 A)). Qed.
Lemma lem1112398 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem16458 A t) (@lem16457 A t)). Qed.
Lemma lem1112399 {A : Type'} (t : Prop) : (term65 A t) = t.
Proof. exact (@lem1112398 (list A) t). Qed.
Lemma lem1112400 {A : Type'} : (term58 A) = ((@List.rev A (@nil A)) = (@nil A)).
Proof. exact (@lem1112399 A ((@List.rev A (@nil A)) = (@nil A))). Qed.
Lemma lem1112401 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1112402 {A : Type'} : (term60 A) = (term19 A).
Proof. exact (MK_COMB (@lem1112401) (@lem1112400 A)). Qed.
Lemma lem1112411 {A : Type'} : (term63 A) = (term63 A).
Proof. exact (eq_refl (term63 A)). Qed.
Lemma lem1112412 {A : Type'} : (term64 A) = (term66 A).
Proof. exact (MK_COMB (@lem1112402 A) (@lem1112411 A)). Qed.
Lemma lem1112415 {A : Type'} : (term42 A) = (term66 A).
Proof. exact (TRANS (@lem1112394 A) (@lem1112412 A)). Qed.
Lemma lem1112416 {A : Type'} : (term1 A) = (term66 A).
Proof. exact (TRANS (@lem1112367 A) (@lem1112415 A)). Qed.
Lemma lem1112417 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1112418 {A : Type'} : (term67 A) = (term68 A).
Proof. exact (MK_COMB (@lem1112417) (@lem1112416 A)). Qed.
Lemma lem1112420 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1112421 {A : Type'} : (term69 A) = (term70 A).
Proof. exact (@lem1112420 (term6 A)). Qed.
Lemma lem1112426 {A : Type'} : (term71 A) = (term72 A).
Proof. exact (MK_COMB (@lem1112418 A) (@lem1112421 A)). Qed.
Lemma lem1112429 {A : Type'} : (term73 A) = (term73 A).
Proof. exact (eq_refl (term73 A)). Qed.
Lemma lem1112436 {A : Type'} : (term7 A) = (term74 A).
Proof. exact (MK_COMB (@lem1112429 A) (@lem1112426 A)). Qed.
Lemma lem1112437 {A : Type'} (l : list A) : ((term75 A l) = l) = ((term75 A l) = l).
Proof. exact (eq_refl ((term75 A l) = l)). Qed.
Lemma lem1112438 {A : Type'} : (term76 A) = (term76 A).
Proof. exact (fun_ext (fun l : list A => @lem1112437 A l)). Qed.
Lemma lem1112439 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1112440 {A : Type'} : (term6 A) = (term6 A).
Proof. exact (MK_COMB (@lem1112439 A) (@lem1112438 A)). Qed.
Lemma lem1112441 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1112442 {A : Type'} : (term70 A) = (term70 A).
Proof. exact (MK_COMB (@lem1112441) (@lem1112440 A)). Qed.
Lemma lem1112443 {A : Type'} (l : list A) (x : A) : ((term21 A x l) = (term22 A l x)) = ((term21 A x l) = (term22 A l x)).
Proof. exact (eq_refl ((term21 A x l) = (term22 A l x))). Qed.
Lemma lem1112444 {A : Type'} (l : list A) : (term16 A l) = (term16 A l).
Proof. exact (fun_ext (fun x : A => @lem1112443 A l x)). Qed.
Lemma lem1112445 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1112446 {A : Type'} (l : list A) : (term36 A l) = (term36 A l).
Proof. exact (MK_COMB (@lem1112445 A) (@lem1112444 A l)). Qed.
Lemma lem1112447 {A : Type'} : (term48 A) = (term48 A).
Proof. exact (fun_ext (fun l : list A => @lem1112446 A l)). Qed.
Lemma lem1112448 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1112449 {A : Type'} : (term63 A) = (term63 A).
Proof. exact (MK_COMB (@lem1112448 A) (@lem1112447 A)). Qed.
Lemma lem1112452 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (eq_refl (term19 A)). Qed.
Lemma lem1112453 {A : Type'} : (term66 A) = (term66 A).
Proof. exact (MK_COMB (@lem1112452 A) (@lem1112449 A)). Qed.
Lemma lem1112454 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1112455 {A : Type'} : (term68 A) = (term68 A).
Proof. exact (MK_COMB (@lem1112454) (@lem1112453 A)). Qed.
Lemma lem1112456 {A : Type'} : (term72 A) = (term72 A).
Proof. exact (MK_COMB (@lem1112455 A) (@lem1112442 A)). Qed.
Lemma lem1112461 {A : Type'} (l : list A) : (((@List.rev A l) = (@nil A)) = (l = (@nil A))) = (((@List.rev A l) = (@nil A)) = (l = (@nil A))).
Proof. exact (eq_refl (((@List.rev A l) = (@nil A)) = (l = (@nil A)))). Qed.
Lemma lem1112462 {A : Type'} : (term77 A) = (term77 A).
Proof. exact (fun_ext (fun l : list A => @lem1112461 A l)). Qed.
Lemma lem1112463 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1112464 {A : Type'} : (term3 A) = (term3 A).
Proof. exact (MK_COMB (@lem1112463 A) (@lem1112462 A)). Qed.
Lemma lem1112465 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1112466 {A : Type'} : (term5 A) = (term5 A).
Proof. exact (MK_COMB (@lem1112465) (@lem1112464 A)). Qed.
Lemma lem1112467 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1112468 {A : Type'} : (term73 A) = (term73 A).
Proof. exact (MK_COMB (@lem1112467) (@lem1112466 A)). Qed.
Lemma lem1112469 {A : Type'} : (term74 A) = (term74 A).
Proof. exact (MK_COMB (@lem1112468 A) (@lem1112456 A)). Qed.
Lemma lem1112502 {A : Type'} : (term7 A) = (term74 A).
Proof. exact (TRANS (@lem1112436 A) (@lem1112469 A)). Qed.
Lemma lem1112503 {A : Type'} : (term74 A) = (term7 A).
Proof. exact (SYM (@lem1112502 A)). Qed.
Lemma lem1112504 {A : Type'} (h1 : term5 A) : term5 A.
Proof. exact (h1). Qed.
Lemma lem1112505 {A : Type'} (h1 : term66 A) : term66 A.
Proof. exact (h1). Qed.
Lemma lem1112506 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (h1). Qed.
Lemma lem1112521 {A : Type'} (l : list A) : (term78 A l) = (term79 A l).
Proof. exact (@lem17646 ((@List.rev A l) = (@nil A)) (l = (@nil A))). Qed.
Lemma lem1112522 {A : Type'} (P : type1143 A) : (term80 A P) = (term81 A P).
Proof. exact (@lem18392 (list A) P). Qed.
Lemma lem1112523 {A : Type'} : (term5 A) = (term82 A).
Proof. exact (@lem1112522 A (term77 A)). Qed.
Lemma lem1112524 {A : Type'} (l : list A) : (term83 A l) = (((@List.rev A l) = (@nil A)) = (l = (@nil A))).
Proof. exact (eq_refl (term83 A l)). Qed.
Lemma lem1112525 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1112526 {A : Type'} (l : list A) : (term84 A l) = (term78 A l).
Proof. exact (MK_COMB (@lem1112525) (@lem1112524 A l)). Qed.
Lemma lem1112527 {A : Type'} (l : list A) : (term84 A l) = (term79 A l).
Proof. exact (TRANS (@lem1112526 A l) (@lem1112521 A l)). Qed.
Lemma lem1112528 {A : Type'} : (term85 A) = (term86 A).
Proof. exact (fun_ext (fun l : list A => @lem1112527 A l)). Qed.
Lemma lem1112529 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1112530 {A : Type'} : (term82 A) = (term87 A).
Proof. exact (MK_COMB (@lem1112529 A) (@lem1112528 A)). Qed.
Lemma lem1112531 {A : Type'} : (term5 A) = (term87 A).
Proof. exact (TRANS (@lem1112523 A) (@lem1112530 A)). Qed.
Lemma lem1112533 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term89 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1112534 {A : Type'} (P : type1143 A) (Q : type1143 A) : (term90 A P Q) = (term91 A P Q).
Proof. exact (@lem1112533 (list A) P Q). Qed.
Lemma lem1112535 {A : Type'} : (term92 A) = (term93 A).
Proof. exact (@lem1112534 A (term94 A) (term95 A)). Qed.
Lemma lem1112536 {A : Type'} (l : list A) : (term96 A l) = (term97 A l).
Proof. exact (eq_refl (term96 A l)). Qed.
Lemma lem1112537 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1112538 {A : Type'} (l : list A) : (term98 A l) = (term99 A l).
Proof. exact (MK_COMB (@lem1112537) (@lem1112536 A l)). Qed.
Lemma lem1112539 {A : Type'} (l : list A) : (term100 A l) = (term101 A l).
Proof. exact (eq_refl (term100 A l)). Qed.
Lemma lem1112540 {A : Type'} (l : list A) : (term102 A l) = (term79 A l).
Proof. exact (MK_COMB (@lem1112538 A l) (@lem1112539 A l)). Qed.
Lemma lem1112541 {A : Type'} : (term103 A) = (term86 A).
Proof. exact (fun_ext (fun l : list A => @lem1112540 A l)). Qed.
Lemma lem1112542 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1112543 {A : Type'} : (term92 A) = (term87 A).
Proof. exact (MK_COMB (@lem1112542 A) (@lem1112541 A)). Qed.
Lemma lem1112544 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1112545 {A : Type'} : (term104 A) = (term105 A).
Proof. exact (MK_COMB (@lem1112544) (@lem1112543 A)). Qed.
Lemma lem1112546 {A : Type'} (l : list A) : (term96 A l) = (term97 A l).
Proof. exact (eq_refl (term96 A l)). Qed.
Lemma lem1112547 {A : Type'} : (term106 A) = (term94 A).
Proof. exact (fun_ext (fun l : list A => @lem1112546 A l)). Qed.
Lemma lem1112548 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1112549 {A : Type'} : (term107 A) = (term108 A).
Proof. exact (MK_COMB (@lem1112548 A) (@lem1112547 A)). Qed.
Lemma lem1112550 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1112551 {A : Type'} : (term109 A) = (term110 A).
Proof. exact (MK_COMB (@lem1112550) (@lem1112549 A)). Qed.
Lemma lem1112552 {A : Type'} (l : list A) : (term100 A l) = (term101 A l).
Proof. exact (eq_refl (term100 A l)). Qed.
Lemma lem1112553 {A : Type'} : (term111 A) = (term95 A).
Proof. exact (fun_ext (fun l : list A => @lem1112552 A l)). Qed.
Lemma lem1112554 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1112555 {A : Type'} : (term112 A) = (term113 A).
Proof. exact (MK_COMB (@lem1112554 A) (@lem1112553 A)). Qed.
Lemma lem1112556 {A : Type'} : (term93 A) = (term114 A).
Proof. exact (MK_COMB (@lem1112551 A) (@lem1112555 A)). Qed.
Lemma lem1112557 {A : Type'} : ((term92 A) = (term93 A)) = ((term87 A) = (term114 A)).
Proof. exact (MK_COMB (@lem1112545 A) (@lem1112556 A)). Qed.
Lemma lem1112558 {A : Type'} : (term87 A) = (term114 A).
Proof. exact (EQ_MP (@lem1112557 A) (@lem1112535 A)). Qed.
Lemma lem1112656 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term89 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1112657 {A : Type'} (P : type1143 A) (Q : type1143 A) : (term91 A P Q) = (term90 A P Q).
Proof. exact (@lem1112656 (list A) P Q). Qed.
Lemma lem1112658 {A : Type'} : (term93 A) = (term92 A).
Proof. exact (@lem1112657 A (term94 A) (term95 A)). Qed.
Lemma lem1112659 {A : Type'} (l : list A) : (term96 A l) = (term97 A l).
Proof. exact (eq_refl (term96 A l)). Qed.
Lemma lem1112660 {A : Type'} : (term106 A) = (term94 A).
Proof. exact (fun_ext (fun l : list A => @lem1112659 A l)). Qed.
Lemma lem1112661 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1112662 {A : Type'} : (term107 A) = (term108 A).
Proof. exact (MK_COMB (@lem1112661 A) (@lem1112660 A)). Qed.
Lemma lem1112663 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1112664 {A : Type'} : (term109 A) = (term110 A).
Proof. exact (MK_COMB (@lem1112663) (@lem1112662 A)). Qed.
Lemma lem1112665 {A : Type'} (l : list A) : (term100 A l) = (term101 A l).
Proof. exact (eq_refl (term100 A l)). Qed.
Lemma lem1112666 {A : Type'} : (term111 A) = (term95 A).
Proof. exact (fun_ext (fun l : list A => @lem1112665 A l)). Qed.
Lemma lem1112667 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1112668 {A : Type'} : (term112 A) = (term113 A).
Proof. exact (MK_COMB (@lem1112667 A) (@lem1112666 A)). Qed.
Lemma lem1112669 {A : Type'} : (term93 A) = (term114 A).
Proof. exact (MK_COMB (@lem1112664 A) (@lem1112668 A)). Qed.
Lemma lem1112670 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1112671 {A : Type'} : (term115 A) = (term116 A).
Proof. exact (MK_COMB (@lem1112670) (@lem1112669 A)). Qed.
Lemma lem1112672 {A : Type'} (l : list A) : (term96 A l) = (term97 A l).
Proof. exact (eq_refl (term96 A l)). Qed.
Lemma lem1112673 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1112674 {A : Type'} (l : list A) : (term98 A l) = (term99 A l).
Proof. exact (MK_COMB (@lem1112673) (@lem1112672 A l)). Qed.
Lemma lem1112675 {A : Type'} (l : list A) : (term100 A l) = (term101 A l).
Proof. exact (eq_refl (term100 A l)). Qed.
Lemma lem1112676 {A : Type'} (l : list A) : (term102 A l) = (term79 A l).
Proof. exact (MK_COMB (@lem1112674 A l) (@lem1112675 A l)). Qed.
Lemma lem1112677 {A : Type'} : (term103 A) = (term86 A).
Proof. exact (fun_ext (fun l : list A => @lem1112676 A l)). Qed.
Lemma lem1112678 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1112679 {A : Type'} : (term92 A) = (term87 A).
Proof. exact (MK_COMB (@lem1112678 A) (@lem1112677 A)). Qed.
Lemma lem1112680 {A : Type'} : ((term93 A) = (term92 A)) = ((term114 A) = (term87 A)).
Proof. exact (MK_COMB (@lem1112671 A) (@lem1112679 A)). Qed.
Lemma lem1112681 {A : Type'} : (term114 A) = (term87 A).
Proof. exact (EQ_MP (@lem1112680 A) (@lem1112658 A)). Qed.
Lemma lem1112682 {A : Type'} : (term87 A) = (term87 A).
Proof. exact (TRANS (@lem1112558 A) (@lem1112681 A)). Qed.
Lemma lem1112683 {A : Type'} : (term5 A) = (term87 A).
Proof. exact (TRANS (@lem1112531 A) (@lem1112682 A)). Qed.
Lemma lem1112684 {A : Type'} (h1 : term5 A) : term87 A.
Proof. exact (EQ_MP (@lem1112683 A) (@lem1112504 A h1)). Qed.
Lemma lem1112686 {A : Type'} (l : list A) (x : A) : ((term21 A x l) = (term22 A l x)) = ((term21 A x l) = (term22 A l x)).
Proof. exact (eq_refl ((term21 A x l) = (term22 A l x))). Qed.
Lemma lem1112687 {A : Type'} (l : list A) : (term16 A l) = (term16 A l).
Proof. exact (fun_ext (fun x : A => @lem1112686 A l x)). Qed.
Lemma lem1112688 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1112689 {A : Type'} (l : list A) : (term36 A l) = (term36 A l).
Proof. exact (MK_COMB (@lem1112688 A) (@lem1112687 A l)). Qed.
Lemma lem1112690 {A : Type'} : (term48 A) = (term48 A).
Proof. exact (fun_ext (fun l : list A => @lem1112689 A l)). Qed.
Lemma lem1112691 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1112692 {A : Type'} : (term63 A) = (term63 A).
Proof. exact (MK_COMB (@lem1112691 A) (@lem1112690 A)). Qed.
Lemma lem1112694 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (eq_refl (term19 A)). Qed.
Lemma lem1112707 {A : Type'} : (term66 A) = (term66 A).
Proof. exact (MK_COMB (@lem1112694 A) (@lem1112692 A)). Qed.
Lemma lem1112708 {A : Type'} (h1 : term66 A) : term66 A.
Proof. exact (EQ_MP (@lem1112707 A) (@lem1112505 A h1)). Qed.
Lemma lem1112709 {A : Type'} (l : list A) : ((term75 A l) = l) = ((term75 A l) = l).
Proof. exact (eq_refl ((term75 A l) = l)). Qed.
Lemma lem1112710 {A : Type'} : (term76 A) = (term76 A).
Proof. exact (fun_ext (fun l : list A => @lem1112709 A l)). Qed.
Lemma lem1112711 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1112720 {A : Type'} : (term6 A) = (term6 A).
Proof. exact (MK_COMB (@lem1112711 A) (@lem1112710 A)). Qed.
Lemma lem1112721 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (EQ_MP (@lem1112720 A) (@lem1112506 A h1)). Qed.
Lemma lem1112743 {A : Type'} (l : list A) (x : A) : ((term21 A x l) = (term22 A l x)) = ((term21 A x l) = (term22 A l x)).
Proof. exact (eq_refl ((term21 A x l) = (term22 A l x))). Qed.
Lemma lem1112744 {A : Type'} (l : list A) : (term16 A l) = (term16 A l).
Proof. exact (fun_ext (fun x : A => @lem1112743 A l x)). Qed.
Lemma lem1112745 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1112746 {A : Type'} (l : list A) : (term36 A l) = (term36 A l).
Proof. exact (MK_COMB (@lem1112745 A) (@lem1112744 A l)). Qed.
Lemma lem1112747 {A : Type'} : (term48 A) = (term48 A).
Proof. exact (fun_ext (fun l : list A => @lem1112746 A l)). Qed.
Lemma lem1112748 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1112749 {A : Type'} : (term63 A) = (term63 A).
Proof. exact (MK_COMB (@lem1112748 A) (@lem1112747 A)). Qed.
Lemma lem1112758 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (eq_refl (term19 A)). Qed.
Lemma lem1112759 {A : Type'} : (term66 A) = (term66 A).
Proof. exact (MK_COMB (@lem1112758 A) (@lem1112749 A)). Qed.
Lemma lem1112760 {A : Type'} (h1 : term66 A) : term66 A.
Proof. exact (EQ_MP (@lem1112759 A) (@lem1112708 A h1)). Qed.
Lemma lem1112769 {A : Type'} (l : list A) : ((term75 A l) = l) = ((term75 A l) = l).
Proof. exact (eq_refl ((term75 A l) = l)). Qed.
Lemma lem1112770 {A : Type'} : (term76 A) = (term76 A).
Proof. exact (fun_ext (fun l : list A => @lem1112769 A l)). Qed.
Lemma lem1112771 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1112772 {A : Type'} : (term6 A) = (term6 A).
Proof. exact (MK_COMB (@lem1112771 A) (@lem1112770 A)). Qed.
Lemma lem1112773 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (EQ_MP (@lem1112772 A) (@lem1112721 A h1)). Qed.
Lemma lem1112811 {A : Type'} (l : list A) (h1 : term79 A l) : term79 A l.
Proof. exact (h1). Qed.
Lemma lem1112814 {A : Type'} (l : list A) (h1 : term97 A l) : term97 A l.
Proof. exact (h1). Qed.
Lemma lem1112815 {A : Type'} (l : list A) (h1 : term101 A l) : term101 A l.
Proof. exact (h1). Qed.
Lemma lem1112821 {A : Type'} (l : list A) : ((term75 A l) = l) = ((term75 A l) = l).
Proof. exact (eq_refl ((term75 A l) = l)). Qed.
Lemma lem1112822 {A : Type'} : (term76 A) = (term76 A).
Proof. exact (fun_ext (fun l : list A => @lem1112821 A l)). Qed.
Lemma lem1112823 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1112825 {A : Type'} : (term6 A) = (term6 A).
Proof. exact (MK_COMB (@lem1112823 A) (@lem1112822 A)). Qed.
Lemma lem1112826 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (EQ_MP (@lem1112825 A) (@lem1112773 A h1)). Qed.
Lemma lem1112878 {A : Type'} (_18065 : list A) (h1 : term6 A) : term117 A _18065.
Proof. exact (@lem1112826 A h1 _18065). Qed.
Lemma lem1112879 {A : Type'} (_18065 : list A) : (term117 A _18065) = ((term75 A _18065) = _18065).
Proof. exact (eq_refl (term117 A _18065)). Qed.
Lemma lem1112899 {A : Type'} (h1 : term66 A) : (@List.rev A (@nil A)) = (@nil A).
Proof. exact (proj1 (@lem1112760 A h1)). Qed.
Lemma lem1112903 {A : Type'} (l : list A) (h1 : term97 A l) : (@List.rev A l) = (@nil A).
Proof. exact (proj1 (@lem1112814 A l h1)). Qed.
Lemma lem1112905 {A : Type'} (l : list A) (h1 : term97 A l) : term118 A l.
Proof. exact (proj2 (@lem1112814 A l h1)). Qed.
Lemma lem1112913 {A : Type'} (l : list A) (h1 : term101 A l) : term119 A l.
Proof. exact (proj1 (@lem1112815 A l h1)). Qed.
Lemma lem1112915 {A : Type'} (l : list A) (h1 : term101 A l) : l = (@nil A).
Proof. exact (proj2 (@lem1112815 A l h1)). Qed.
Lemma lem1112916 {A : Type'} (l : list A) (h1 : term97 A l) : (@nil A) = (@List.rev A l).
Proof. exact (SYM (@lem1112903 A l h1)). Qed.
Lemma lem1112945 {A : Type'} : (term120 A) = (term120 A).
Proof. exact (eq_refl (term120 A)). Qed.
Lemma lem1112946 {A : Type'} (l : list A) (h1 : term97 A l) : (term121 A) = (term122 A l).
Proof. exact (MK_COMB (@lem1112945 A) (@lem1112916 A l h1)). Qed.
Lemma lem1112947 {A : Type'} (l : list A) : (term122 A l) = ((term75 A l) = (@List.rev A l)).
Proof. exact (eq_refl (term122 A l)). Qed.
Lemma lem1112948 {A : Type'} : (term123 A) = (term123 A).
Proof. exact (eq_refl (term123 A)). Qed.
Lemma lem1112949 {A : Type'} (l : list A) : ((term121 A) = (term122 A l)) = ((term121 A) = ((term75 A l) = (@List.rev A l))).
Proof. exact (MK_COMB (@lem1112948 A) (@lem1112947 A l)). Qed.
Lemma lem1112950 {A : Type'} : (term121 A) = ((@List.rev A (@nil A)) = (@nil A)).
Proof. exact (eq_refl (term121 A)). Qed.
Lemma lem1112951 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1112952 {A : Type'} : (term123 A) = (term124 A).
Proof. exact (MK_COMB (@lem1112951) (@lem1112950 A)). Qed.
Lemma lem1112953 {A : Type'} (l : list A) : ((term75 A l) = (@List.rev A l)) = ((term75 A l) = (@List.rev A l)).
Proof. exact (eq_refl ((term75 A l) = (@List.rev A l))). Qed.
Lemma lem1112954 {A : Type'} (l : list A) : ((term121 A) = ((term75 A l) = (@List.rev A l))) = (((@List.rev A (@nil A)) = (@nil A)) = ((term75 A l) = (@List.rev A l))).
Proof. exact (MK_COMB (@lem1112952 A) (@lem1112953 A l)). Qed.
Lemma lem1112955 {A : Type'} (l : list A) : ((term121 A) = (term122 A l)) = (((@List.rev A (@nil A)) = (@nil A)) = ((term75 A l) = (@List.rev A l))).
Proof. exact (TRANS (@lem1112949 A l) (@lem1112954 A l)). Qed.
Lemma lem1112956 {A : Type'} (l : list A) (h1 : term97 A l) : ((@List.rev A (@nil A)) = (@nil A)) = ((term75 A l) = (@List.rev A l)).
Proof. exact (EQ_MP (@lem1112955 A l) (@lem1112946 A l h1)). Qed.
Lemma lem1112971 {A : Type'} (l : list A) : (term125 A l) = (term125 A l).
Proof. exact (eq_refl (term125 A l)). Qed.
Lemma lem1112972 {A : Type'} (l : list A) (h1 : term97 A l) : (term126 A l) = (term127 A l).
Proof. exact (MK_COMB (@lem1112971 A l) (@lem1112916 A l h1)). Qed.
Lemma lem1112973 {A : Type'} (l : list A) : (term127 A l) = (term128 A l).
Proof. exact (eq_refl (term127 A l)). Qed.
Lemma lem1112974 {A : Type'} (l : list A) : (term129 A l) = (term129 A l).
Proof. exact (eq_refl (term129 A l)). Qed.
Lemma lem1112975 {A : Type'} (l : list A) : ((term126 A l) = (term127 A l)) = ((term126 A l) = (term128 A l)).
Proof. exact (MK_COMB (@lem1112974 A l) (@lem1112973 A l)). Qed.
Lemma lem1112976 {A : Type'} (l : list A) : (term126 A l) = (term118 A l).
Proof. exact (eq_refl (term126 A l)). Qed.
Lemma lem1112977 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1112978 {A : Type'} (l : list A) : (term129 A l) = (term130 A l).
Proof. exact (MK_COMB (@lem1112977) (@lem1112976 A l)). Qed.
Lemma lem1112979 {A : Type'} (l : list A) : (term128 A l) = (term128 A l).
Proof. exact (eq_refl (term128 A l)). Qed.
Lemma lem1112980 {A : Type'} (l : list A) : ((term126 A l) = (term128 A l)) = ((term118 A l) = (term128 A l)).
Proof. exact (MK_COMB (@lem1112978 A l) (@lem1112979 A l)). Qed.
Lemma lem1112981 {A : Type'} (l : list A) : ((term126 A l) = (term127 A l)) = ((term118 A l) = (term128 A l)).
Proof. exact (TRANS (@lem1112975 A l) (@lem1112980 A l)). Qed.
Lemma lem1112982 {A : Type'} (l : list A) (h1 : term97 A l) : (term118 A l) = (term128 A l).
Proof. exact (EQ_MP (@lem1112981 A l) (@lem1112972 A l h1)). Qed.
Lemma lem1112983 {A : Type'} (l : list A) (h1 : term97 A l) : term128 A l.
Proof. exact (EQ_MP (@lem1112982 A l h1) (@lem1112905 A l h1)). Qed.
Lemma lem1113040 {A : Type'} : (term131 A) = (term131 A).
Proof. exact (eq_refl (term131 A)). Qed.
Lemma lem1113041 {A : Type'} (l : list A) (h1 : term101 A l) : (term132 A l) = (term133 A).
Proof. exact (MK_COMB (@lem1113040 A) (@lem1112915 A l h1)). Qed.
Lemma lem1113042 {A : Type'} : (term133 A) = (term134 A).
Proof. exact (eq_refl (term133 A)). Qed.
Lemma lem1113043 {A : Type'} (l : list A) : (term135 A l) = (term135 A l).
Proof. exact (eq_refl (term135 A l)). Qed.
Lemma lem1113044 {A : Type'} (l : list A) : ((term132 A l) = (term133 A)) = ((term132 A l) = (term134 A)).
Proof. exact (MK_COMB (@lem1113043 A l) (@lem1113042 A)). Qed.
Lemma lem1113045 {A : Type'} (l : list A) : (term132 A l) = (term119 A l).
Proof. exact (eq_refl (term132 A l)). Qed.
Lemma lem1113046 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1113047 {A : Type'} (l : list A) : (term135 A l) = (term136 A l).
Proof. exact (MK_COMB (@lem1113046) (@lem1113045 A l)). Qed.
Lemma lem1113048 {A : Type'} : (term134 A) = (term134 A).
Proof. exact (eq_refl (term134 A)). Qed.
Lemma lem1113049 {A : Type'} (l : list A) : ((term132 A l) = (term134 A)) = ((term119 A l) = (term134 A)).
Proof. exact (MK_COMB (@lem1113047 A l) (@lem1113048 A)). Qed.
Lemma lem1113050 {A : Type'} (l : list A) : ((term132 A l) = (term133 A)) = ((term119 A l) = (term134 A)).
Proof. exact (TRANS (@lem1113044 A l) (@lem1113049 A l)). Qed.
Lemma lem1113051 {A : Type'} (l : list A) (h1 : term101 A l) : (term119 A l) = (term134 A).
Proof. exact (EQ_MP (@lem1113050 A l) (@lem1113041 A l h1)). Qed.
Lemma lem1113052 {A : Type'} (l : list A) (h1 : term101 A l) : term134 A.
Proof. exact (EQ_MP (@lem1113051 A l h1) (@lem1112913 A l h1)). Qed.
Lemma lem1113092 {A : Type'} (x : list A) (y : list A) (z : list A) : term137 A x y z.
Proof. exact (@lem21385 (list A) x y z). Qed.
Lemma lem1113096 {A : Type'} (_18065 : list A) (h1 : term6 A) : (term75 A _18065) = _18065.
Proof. exact (EQ_MP (@lem1112879 A _18065) (@lem1112878 A _18065 h1)). Qed.
Lemma lem1113097 {A : Type'} (_18065 : list A) (h1 : term6 A) : (term75 A _18065) = _18065.
Proof. exact (@lem1113096 A _18065 h1). Qed.
Lemma lem1113098 {A : Type'} (l : list A) (h1 : term6 A) : (term75 A l) = l.
Proof. exact (@lem1113097 A l h1). Qed.
Lemma lem1113099 {A : Type'} (l : list A) (h1 : term6 A) : term138 A l.
Proof. exact (fun h0 : term139 A l => @lem1113098 A l h1). Qed.
Lemma lem1113101 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1113102 {A : Type'} (l : list A) : (term138 A l) = ((term75 A l) = l).
Proof. exact (@lem1113101 ((term75 A l) = l)). Qed.
Lemma lem1113103 {A : Type'} (l : list A) (h1 : term6 A) : (term75 A l) = l.
Proof. exact (EQ_MP (@lem1113102 A l) (@lem1113099 A l h1)). Qed.
Lemma lem1113105 {A : Type'} (l : list A) (h1 : term66 A) (h2 : term97 A l) : (term75 A l) = (@List.rev A l).
Proof. exact (EQ_MP (@lem1112956 A l h2) (@lem1112899 A h1)). Qed.
Lemma lem1113106 {A : Type'} (l : list A) (h1 : term66 A) (h2 : term97 A l) : term141 A l.
Proof. exact (fun h0 : term142 A l => @lem1113105 A l h1 h2). Qed.
Lemma lem1113108 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1113109 {A : Type'} (l : list A) : (term141 A l) = ((term75 A l) = (@List.rev A l)).
Proof. exact (@lem1113108 ((term75 A l) = (@List.rev A l))). Qed.
Lemma lem1113110 {A : Type'} (l : list A) (h1 : term66 A) (h2 : term97 A l) : (term75 A l) = (@List.rev A l).
Proof. exact (EQ_MP (@lem1113109 A l) (@lem1113106 A l h1 h2)). Qed.
Lemma lem1113128 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1113129 {A : Type'} (y : list A) (x : list A) (z : list A) : (term143 A x y z) = (term144 A y x z).
Proof. exact (@lem1113128 (y = z) (term145 A x z)). Qed.
Lemma lem1113139 {A : Type'} (x : list A) (y : list A) : (term146 A x y) = (term146 A x y).
Proof. exact (eq_refl (term146 A x y)). Qed.
Lemma lem1113140 {A : Type'} (y : list A) (x : list A) (z : list A) : (term137 A x y z) = (term147 A y x z).
Proof. exact (MK_COMB (@lem1113139 A x y) (@lem1113129 A y x z)). Qed.
Lemma lem1113144 (q : Prop) (p : Prop) (r : Prop) : (term148 p q r) = (term148 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1113145 {A : Type'} (y : list A) (x : list A) (z : list A) : (term147 A y x z) = (term149 A y x z).
Proof. exact (@lem1113144 (y = z) (term145 A x y) (term145 A x z)). Qed.
Lemma lem1113167 {A : Type'} (y : list A) (x : list A) (z : list A) : (term137 A x y z) = (term149 A y x z).
Proof. exact (TRANS (@lem1113140 A y x z) (@lem1113145 A y x z)). Qed.
Lemma lem1113168 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1113169 {A : Type'} (y : list A) (x : list A) (z : list A) : (term150 A x y z) = (term151 A y x z).
Proof. exact (MK_COMB (@lem1113168) (@lem1113167 A y x z)). Qed.
Lemma lem1113191 {A : Type'} (y : list A) (x : list A) (z : list A) : (term149 A y x z) = (term149 A y x z).
Proof. exact (eq_refl (term149 A y x z)). Qed.
Lemma lem1113192 {A : Type'} (y : list A) (x : list A) (z : list A) : ((term137 A x y z) = (term149 A y x z)) = ((term149 A y x z) = (term149 A y x z)).
Proof. exact (MK_COMB (@lem1113169 A y x z) (@lem1113191 A y x z)). Qed.
Lemma lem1113194 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1113195 (x : Prop) : (x = x) = True.
Proof. exact (@lem1113194 Prop x). Qed.
Lemma lem1113196 {A : Type'} (y : list A) (x : list A) (z : list A) : ((term149 A y x z) = (term149 A y x z)) = True.
Proof. exact (@lem1113195 (term149 A y x z)). Qed.
Lemma lem1113197 {A : Type'} (y : list A) (x : list A) (z : list A) : ((term137 A x y z) = (term149 A y x z)) = True.
Proof. exact (TRANS (@lem1113192 A y x z) (@lem1113196 A y x z)). Qed.
Lemma lem1113198 {A : Type'} (y : list A) (x : list A) (z : list A) : True = ((term137 A x y z) = (term149 A y x z)).
Proof. exact (SYM (@lem1113197 A y x z)). Qed.
Lemma lem1113199 {A : Type'} (y : list A) (x : list A) (z : list A) : (term137 A x y z) = (term149 A y x z).
Proof. exact (EQ_MP (@lem1113198 A y x z) (@lem0)). Qed.
Lemma lem1113200 {A : Type'} (y : list A) (x : list A) (z : list A) : term149 A y x z.
Proof. exact (EQ_MP (@lem1113199 A y x z) (@lem1113092 A x y z)). Qed.
Lemma lem1113202 (b : Prop) (a : Prop) : (a \/ b) = (term152 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1113203 {A : Type'} (x : list A) (y : list A) (z : list A) : (term149 A y x z) = (term153 A x y z).
Proof. exact (@lem1113202 (term154 A y x z) (y = z)). Qed.
Lemma lem1113205 (a : Prop) (b : Prop) : (term155 a b) = (term156 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1113206 {A : Type'} (y : list A) (x : list A) (z : list A) : (term157 A y x z) = (term158 A y x z).
Proof. exact (@lem1113205 (term145 A x y) (term145 A x z)). Qed.
Lemma lem1113208 (a : Prop) : (term159 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1113209 {A : Type'} (x : list A) (y : list A) : (term160 A x y) = (x = y).
Proof. exact (@lem1113208 (x = y)). Qed.
Lemma lem1113210 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1113211 {A : Type'} (x : list A) (y : list A) : (term161 A x y) = (term162 A x y).
Proof. exact (MK_COMB (@lem1113210) (@lem1113209 A x y)). Qed.
Lemma lem1113213 (a : Prop) : (term159 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1113214 {A : Type'} (x : list A) (z : list A) : (term160 A x z) = (x = z).
Proof. exact (@lem1113213 (x = z)). Qed.
Lemma lem1113215 {A : Type'} (y : list A) (x : list A) (z : list A) : (term158 A y x z) = (term163 A y x z).
Proof. exact (MK_COMB (@lem1113211 A x y) (@lem1113214 A x z)). Qed.
Lemma lem1113216 {A : Type'} (y : list A) (x : list A) (z : list A) : (term157 A y x z) = (term163 A y x z).
Proof. exact (TRANS (@lem1113206 A y x z) (@lem1113215 A y x z)). Qed.
Lemma lem1113217 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1113218 {A : Type'} (y : list A) (x : list A) (z : list A) : (term164 A y x z) = (term165 A y x z).
Proof. exact (MK_COMB (@lem1113217) (@lem1113216 A y x z)). Qed.
Lemma lem1113219 {A : Type'} (y : list A) (z : list A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1113220 {A : Type'} (x : list A) (y : list A) (z : list A) : (term153 A x y z) = (term166 A x y z).
Proof. exact (MK_COMB (@lem1113218 A y x z) (@lem1113219 A y z)). Qed.
Lemma lem1113221 {A : Type'} (x : list A) (y : list A) (z : list A) : (term149 A y x z) = (term166 A x y z).
Proof. exact (TRANS (@lem1113203 A x y z) (@lem1113220 A x y z)). Qed.
Lemma lem1113223 {A : Type'} (l : list A) (h1 : term6 A) (h2 : term66 A) (h3 : term97 A l) : term167 A l.
Proof. exact (conj (@lem1113103 A l h1) (@lem1113110 A l h2 h3)). Qed.
Lemma lem1113225 {A : Type'} (x : list A) (y : list A) (z : list A) : term166 A x y z.
Proof. exact (EQ_MP (@lem1113221 A x y z) (@lem1113200 A y x z)). Qed.
Lemma lem1113226 {A : Type'} (x : list A) (y : list A) (z : list A) : term166 A x y z.
Proof. exact (@lem1113225 A x y z). Qed.
Lemma lem1113227 {A : Type'} (l : list A) : term168 A l.
Proof. exact (@lem1113226 A (term75 A l) l (@List.rev A l)). Qed.
Lemma lem1113230 {A : Type'} (l : list A) (h1 : term6 A) (h2 : term66 A) (h3 : term97 A l) : l = (@List.rev A l).
Proof. exact (@lem1113227 A l (@lem1113223 A l h1 h2 h3)). Qed.
Lemma lem1113231 {A : Type'} (l : list A) (h1 : term6 A) (h2 : term66 A) (h3 : term97 A l) : term169 A l.
Proof. exact (fun h0 : term128 A l => @lem1113230 A l h1 h2 h3). Qed.
Lemma lem1113233 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1113234 {A : Type'} (l : list A) : (term169 A l) = (l = (@List.rev A l)).
Proof. exact (@lem1113233 (l = (@List.rev A l))). Qed.
Lemma lem1113235 {A : Type'} (l : list A) (h1 : term6 A) (h2 : term66 A) (h3 : term97 A l) : l = (@List.rev A l).
Proof. exact (EQ_MP (@lem1113234 A l) (@lem1113231 A l h1 h2 h3)). Qed.
Lemma lem1113238 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1113240 {A : Type'} (l : list A) : (term128 A l) = (term170 A l).
Proof. exact (@lem1113238 (l = (@List.rev A l))). Qed.
Lemma lem1113243 {A : Type'} (l : list A) (h1 : term97 A l) : term170 A l.
Proof. exact (EQ_MP (@lem1113240 A l) (@lem1112983 A l h1)). Qed.
Lemma lem1113246 {A : Type'} (l : list A) (h1 : term6 A) (h2 : term66 A) (h3 : term97 A l) : False.
Proof. exact (@lem1113243 A l h3 (@lem1113235 A l h1 h2 h3)). Qed.
Lemma lem1113247 {A : Type'} (l : list A) (h1 : term6 A) (h2 : term66 A) (h3 : term97 A l) : term171.
Proof. exact (fun h0 : ~ False => @lem1113246 A l h1 h2 h3). Qed.
Lemma lem1113249 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1113250 : term171 = False.
Proof. exact (@lem1113249 False). Qed.
Lemma lem1113295 {A : Type'} (h1 : term66 A) : (@List.rev A (@nil A)) = (@nil A).
Proof. exact (proj1 (@lem1112760 A h1)). Qed.
Lemma lem1113296 {A : Type'} (h1 : term66 A) : term172 A.
Proof. exact (fun h0 : term134 A => @lem1113295 A h1). Qed.
Lemma lem1113298 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1113299 {A : Type'} : (term172 A) = ((@List.rev A (@nil A)) = (@nil A)).
Proof. exact (@lem1113298 ((@List.rev A (@nil A)) = (@nil A))). Qed.
Lemma lem1113300 {A : Type'} (h1 : term66 A) : (@List.rev A (@nil A)) = (@nil A).
Proof. exact (EQ_MP (@lem1113299 A) (@lem1113296 A h1)). Qed.
Lemma lem1113303 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1113305 {A : Type'} : (term134 A) = (term173 A).
Proof. exact (@lem1113303 ((@List.rev A (@nil A)) = (@nil A))). Qed.
Lemma lem1113308 {A : Type'} (l : list A) (h1 : term101 A l) : term173 A.
Proof. exact (EQ_MP (@lem1113305 A) (@lem1113052 A l h1)). Qed.
Lemma lem1113311 {A : Type'} (l : list A) (h1 : term101 A l) (h2 : term66 A) : False.
Proof. exact (@lem1113308 A l h1 (@lem1113300 A h2)). Qed.
Lemma lem1113312 {A : Type'} (l : list A) (h1 : term101 A l) (h2 : term66 A) : term171.
Proof. exact (fun h0 : ~ False => @lem1113311 A l h1 h2). Qed.
Lemma lem1113314 (p : Prop) : (term140 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1113315 : term171 = False.
Proof. exact (@lem1113314 False). Qed.
Lemma lem1113317 {A : Type'} (l : list A) (h1 : term101 A l) (h2 : term66 A) : False.
Proof. exact (EQ_MP (@lem1113315) (@lem1113312 A l h1 h2)). Qed.
Lemma lem1113318 {A : Type'} (l : list A) (h1 : term6 A) (h2 : term66 A) (h3 : term97 A l) : False.
Proof. exact (EQ_MP (@lem1113250) (@lem1113247 A l h1 h2 h3)). Qed.
Lemma lem1113319 {A : Type'} (l : list A) (h1 : term6 A) (h2 : term66 A) (h3 : term97 A l) : (term6 A) = False.
Proof. exact (prop_ext (fun h4 : term6 A => @lem1113318 A l h1 h2 h3) (fun h4 : False => @lem1112826 A h1)). Qed.
Lemma lem1113320 {A : Type'} (l : list A) (h1 : term6 A) (h2 : term66 A) (h3 : term97 A l) : False.
Proof. exact (EQ_MP (@lem1113319 A l h1 h2 h3) (@lem1112826 A h1)). Qed.
Lemma lem1113321 {A : Type'} (l : list A) (h1 : term6 A) (h2 : term66 A) (h3 : term79 A l) : False.
Proof. exact (or_elim (@lem1112811 A l h3) (fun h0 : term97 A l => @lem1113320 A l h1 h2 h0) (fun h0 : term101 A l => @lem1113317 A l h0 h2)). Qed.
Lemma lem1113322 {A : Type'} (l : list A) (h1 : term6 A) (h2 : term66 A) (h3 : term79 A l) : (term79 A l) = False.
Proof. exact (prop_ext (fun h4 : term79 A l => @lem1113321 A l h1 h2 h3) (fun h4 : False => @lem1112811 A l h3)). Qed.
Lemma lem1113323 {A : Type'} (l : list A) (h1 : term6 A) (h2 : term66 A) (h3 : term79 A l) : False.
Proof. exact (EQ_MP (@lem1113322 A l h1 h2 h3) (@lem1112811 A l h3)). Qed.
Lemma lem1113324 {A : Type'} (l : list A) (h1 : term6 A) (h2 : term66 A) (h3 : term79 A l) : (term6 A) = False.
Proof. exact (prop_ext (fun h4 : term6 A => @lem1113323 A l h1 h2 h3) (fun h4 : False => @lem1112773 A h1)). Qed.
Lemma lem1113325 {A : Type'} (l : list A) (h1 : term6 A) (h2 : term66 A) (h3 : term79 A l) : False.
Proof. exact (EQ_MP (@lem1113324 A l h1 h2 h3) (@lem1112773 A h1)). Qed.
Lemma lem1113326 {A : Type'} (l : list A) (h1 : term6 A) (h2 : term66 A) (h3 : term79 A l) : (term66 A) = False.
Proof. exact (prop_ext (fun h4 : term66 A => @lem1113325 A l h1 h2 h3) (fun h4 : False => @lem1112760 A h2)). Qed.
Lemma lem1113327 {A : Type'} (l : list A) (h1 : term6 A) (h2 : term66 A) (h3 : term79 A l) : False.
Proof. exact (EQ_MP (@lem1113326 A l h1 h2 h3) (@lem1112760 A h2)). Qed.
Lemma lem1113328 {A : Type'} (h1 : term6 A) (h2 : term5 A) (h3 : term66 A) : False.
Proof. exact (ex_elim (@lem1112684 A h2) (fun l : list A => fun h0 : term86 A l => @lem1113327 A l h1 h3 h0)). Qed.
Lemma lem1113329 {A : Type'} (h1 : term6 A) (h2 : term5 A) (h3 : term66 A) : (term6 A) = False.
Proof. exact (prop_ext (fun h4 : term6 A => @lem1113328 A h1 h2 h3) (fun h4 : False => @lem1112721 A h1)). Qed.
Lemma lem1113330 {A : Type'} (h1 : term6 A) (h2 : term5 A) (h3 : term66 A) : False.
Proof. exact (EQ_MP (@lem1113329 A h1 h2 h3) (@lem1112721 A h1)). Qed.
Lemma lem1113331 {A : Type'} (h1 : term6 A) (h2 : term5 A) (h3 : term66 A) : (term66 A) = False.
Proof. exact (prop_ext (fun h4 : term66 A => @lem1113330 A h1 h2 h3) (fun h4 : False => @lem1112708 A h3)). Qed.
Lemma lem1113332 {A : Type'} (h1 : term6 A) (h2 : term5 A) (h3 : term66 A) : False.
Proof. exact (EQ_MP (@lem1113331 A h1 h2 h3) (@lem1112708 A h3)). Qed.
Lemma lem1113333 {A : Type'} (h1 : term5 A) (h2 : term66 A) : term69 A.
Proof. exact (fun h0 : term6 A => @lem1113332 A h0 h1 h2). Qed.
Lemma lem1113334 {A : Type'} : (term69 A) = (term70 A).
Proof. exact (@lem69 (term6 A)). Qed.
Lemma lem1113335 {A : Type'} (h1 : term5 A) (h2 : term66 A) : term70 A.
Proof. exact (EQ_MP (@lem1113334 A) (@lem1113333 A h1 h2)). Qed.
Lemma lem1113336 {A : Type'} (h1 : term5 A) : term72 A.
Proof. exact (fun h0 : term66 A => @lem1113335 A h1 h0). Qed.
Lemma lem1113337 {A : Type'} : term74 A.
Proof. exact (fun h0 : term5 A => @lem1113336 A h0). Qed.
Lemma lem1113338 {A : Type'} : term7 A.
Proof. exact (EQ_MP (@lem1112503 A) (@lem1113337 A)). Qed.
Lemma lem1113340 {A : Type'} : term7 A.
Proof. exact (@lem1112308 A (@lem1113338 A)). Qed.
Lemma lem1113341 {A : Type'} (h1 : term5 A) : term71 A.
Proof. exact (@lem1113340 A (@lem1112287 A h1)). Qed.
Lemma lem1113342 {A : Type'} (h1 : term5 A) : term69 A.
Proof. exact (@lem1113341 A h1 (@lem1112290 A)). Qed.
Lemma lem1113343 {A : Type'} (h1 : term5 A) : False.
Proof. exact (@lem1113342 A h1 (@lem1112288 A)). Qed.
Lemma lem1113344 {A : Type'} (h1 : term5 A) : (term5 A) = False.
Proof. exact (prop_ext (fun h2 : term5 A => @lem1113343 A h1) (fun h2 : False => @lem1112287 A h1)). Qed.
Lemma lem1113345 {A : Type'} (h1 : term5 A) : False.
Proof. exact (EQ_MP (@lem1113344 A h1) (@lem1112287 A h1)). Qed.
Lemma lem1113346 {A : Type'} : term4 A.
Proof. exact (fun h0 : term5 A => @lem1113345 A h0). Qed.
Lemma lem1113347 {A : Type'} : term3 A.
Proof. exact (EQ_MP (@lem1112286 A) (@lem1113346 A)). Qed.
