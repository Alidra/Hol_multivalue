Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1094488_term_abbrevs.
Require Import SKOLEM_THM_spec.
Require Import list_RECURSION_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1094382 {A : Type'} (HD' : type1141 A) (h1 : term0 A HD') : term0 A HD'.
Proof. exact (h1). Qed.
Lemma lem1094383 {A : Type'} (h : A) (HD' : type1141 A) (h1 : term0 A HD') : term1 A HD' h.
Proof. exact (@lem1094382 A HD' h1 h). Qed.
Lemma lem1094384 {A : Type'} (HD' : type1141 A) (h : A) : (term1 A HD' h) = (term2 A HD' h).
Proof. exact (eq_refl (term1 A HD' h)). Qed.
Lemma lem1094385 {A : Type'} (h : A) (HD' : type1141 A) (h1 : term0 A HD') : term2 A HD' h.
Proof. exact (EQ_MP (@lem1094384 A HD' h) (@lem1094383 A h HD' h1)). Qed.
Lemma lem1094386 {A : Type'} (h : A) (t : list A) (HD' : type1141 A) (h1 : term0 A HD') : term3 A HD' h t.
Proof. exact (@lem1094385 A h HD' h1 t). Qed.
Lemma lem1094387 {A : Type'} (HD' : type1141 A) (t : list A) (h : A) : (term3 A HD' h t) = ((term4 A HD' h t) = h).
Proof. exact (eq_refl (term3 A HD' h t)). Qed.
Lemma lem1094388 {A : Type'} (t : list A) (h : A) (HD' : type1141 A) (h1 : term0 A HD') : (term4 A HD' h t) = h.
Proof. exact (EQ_MP (@lem1094387 A HD' t h) (@lem1094386 A h t HD' h1)). Qed.
Lemma lem1094389 {A : Type'} (t : list A) (HD' : type1141 A) (h1 : term0 A HD') : term5 A HD' t.
Proof. exact (fun h : A => @lem1094388 A t h HD' h1). Qed.
Lemma lem1094390 {A : Type'} (HD' : type1141 A) (h1 : term0 A HD') : term6 A HD'.
Proof. exact (fun t : list A => @lem1094389 A t HD' h1). Qed.
Lemma lem1094391 {A : Type'} (HD' : type1141 A) (h1 : term0 A HD') : term0 A HD'.
Proof. exact (h1). Qed.
Lemma lem1094392 {A : Type'} (HD' : type1141 A) (h1 : term0 A HD') : (term0 A HD') = (term6 A HD').
Proof. exact (prop_ext (fun h2 : term0 A HD' => @lem1094390 A HD' h1) (fun h2 : term6 A HD' => @lem1094391 A HD' h1)). Qed.
Lemma lem1094393 {A : Type'} (HD' : type1141 A) (h1 : term0 A HD') : term6 A HD'.
Proof. exact (EQ_MP (@lem1094392 A HD' h1) (@lem1094391 A HD' h1)). Qed.
Lemma lem1094394 {A Z : Type'} (NIL' : Z) : term7 A Z NIL'.
Proof. exact (@lem1072128 A Z NIL'). Qed.
Lemma lem1094395 {A Z : Type'} (NIL' : Z) : (term7 A Z NIL') = (term8 A Z NIL').
Proof. exact (eq_refl (term7 A Z NIL')). Qed.
Lemma lem1094396 {A Z : Type'} (NIL' : Z) : term8 A Z NIL'.
Proof. exact (EQ_MP (@lem1094395 A Z NIL') (@lem1094394 A Z NIL')). Qed.
Lemma lem1094397 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term9 A Z NIL' CONS'.
Proof. exact (@lem1094396 A Z NIL' CONS'). Qed.
Lemma lem1094398 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : (term9 A Z NIL' CONS') = (term10 A Z NIL' CONS').
Proof. exact (eq_refl (term9 A Z NIL' CONS')). Qed.
Lemma lem1094399 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term10 A Z NIL' CONS'.
Proof. exact (EQ_MP (@lem1094398 A Z NIL' CONS') (@lem1094397 A Z NIL' CONS')). Qed.
Lemma lem1094400 {A : Type'} (NIL' : A) (CONS' : type1393 A) : term11 A NIL' CONS'.
Proof. exact (@lem1094399 A A NIL' CONS'). Qed.
Lemma lem1094401 {A : Type'} (NIL' : A) : term12 A NIL'.
Proof. exact (@lem1094400 A NIL' (term13 A)). Qed.
Lemma lem1094402 {A : Type'} (a0 : A) : (term14 A a0) = (term15 A a0).
Proof. exact (eq_refl (term14 A a0)). Qed.
Lemma lem1094403 {A : Type'} (a1 : list A) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1094404 {A : Type'} (a0 : A) (a1 : list A) : (term16 A a0 a1) = (term17 A a0 a1).
Proof. exact (MK_COMB (@lem1094402 A a0) (@lem1094403 A a1)). Qed.
Lemma lem1094405 {A : Type'} (a1 : list A) (a0 : A) : (term17 A a0 a1) = (term18 A a0).
Proof. exact (eq_refl (term17 A a0 a1)). Qed.
Lemma lem1094406 {A : Type'} (a1 : list A) (a0 : A) : (term16 A a0 a1) = (term18 A a0).
Proof. exact (TRANS (@lem1094404 A a0 a1) (@lem1094405 A a1 a0)). Qed.
Lemma lem1094407 {A : Type'} (fn : type1141 A) (a1 : list A) : (fn a1) = (fn a1).
Proof. exact (eq_refl (fn a1)). Qed.
Lemma lem1094408 {A : Type'} (a0 : A) (fn : type1141 A) (a1 : list A) : (term19 A a0 fn a1) = (term20 A a0 fn a1).
Proof. exact (MK_COMB (@lem1094406 A a1 a0) (@lem1094407 A fn a1)). Qed.
Lemma lem1094409 {A : Type'} (fn : type1141 A) (a1 : list A) (a0 : A) : (term20 A a0 fn a1) = a0.
Proof. exact (eq_refl (term20 A a0 fn a1)). Qed.
Lemma lem1094410 {A : Type'} (fn : type1141 A) (a1 : list A) (a0 : A) : (term19 A a0 fn a1) = a0.
Proof. exact (TRANS (@lem1094408 A a0 fn a1) (@lem1094409 A fn a1 a0)). Qed.
Lemma lem1094411 {A : Type'} (fn : type1141 A) (a0 : A) (a1 : list A) : (term21 A fn a0 a1) = (term21 A fn a0 a1).
Proof. exact (eq_refl (term21 A fn a0 a1)). Qed.
Lemma lem1094412 {A : Type'} (fn : type1141 A) (a1 : list A) (a0 : A) : ((term4 A fn a0 a1) = (term19 A a0 fn a1)) = ((term4 A fn a0 a1) = a0).
Proof. exact (MK_COMB (@lem1094411 A fn a0 a1) (@lem1094410 A fn a1 a0)). Qed.
Lemma lem1094413 {A : Type'} (fn : type1141 A) (a0 : A) : (term22 A a0 fn) = (term23 A fn a0).
Proof. exact (fun_ext (fun a1 : list A => @lem1094412 A fn a1 a0)). Qed.
Lemma lem1094414 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1094415 {A : Type'} (fn : type1141 A) (a0 : A) : (term24 A a0 fn) = (term2 A fn a0).
Proof. exact (MK_COMB (@lem1094414 A) (@lem1094413 A fn a0)). Qed.
Lemma lem1094416 {A : Type'} (fn : type1141 A) : (term25 A fn) = (term26 A fn).
Proof. exact (fun_ext (fun a0 : A => @lem1094415 A fn a0)). Qed.
Lemma lem1094417 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1094418 {A : Type'} (fn : type1141 A) : (term27 A fn) = (term0 A fn).
Proof. exact (MK_COMB (@lem1094417 A) (@lem1094416 A fn)). Qed.
Lemma lem1094419 {A : Type'} (fn : type1141 A) (NIL' : A) : (term28 A fn NIL') = (term28 A fn NIL').
Proof. exact (eq_refl (term28 A fn NIL')). Qed.
Lemma lem1094420 {A : Type'} (NIL' : A) (fn : type1141 A) : (term29 A NIL' fn) = (term30 A NIL' fn).
Proof. exact (MK_COMB (@lem1094419 A fn NIL') (@lem1094418 A fn)). Qed.
Lemma lem1094421 {A : Type'} (NIL' : A) : (term31 A NIL') = (term32 A NIL').
Proof. exact (fun_ext (fun fn : type1141 A => @lem1094420 A NIL' fn)). Qed.
Lemma lem1094422 {A : Type'} : (@ex ((list A) -> A)) = (@ex ((list A) -> A)).
Proof. exact (eq_refl (@ex ((list A) -> A))). Qed.
Lemma lem1094423 {A : Type'} (NIL' : A) : (term12 A NIL') = (term33 A NIL').
Proof. exact (MK_COMB (@lem1094422 A) (@lem1094421 A NIL')). Qed.
Lemma lem1094424 {A : Type'} (NIL' : A) : term33 A NIL'.
Proof. exact (EQ_MP (@lem1094423 A NIL') (@lem1094401 A NIL')). Qed.
Lemma lem1094425 {A : Type'} (NIL' : A) (HD' : type1141 A) (h1 : term30 A NIL' HD') : term30 A NIL' HD'.
Proof. exact (h1). Qed.
Lemma lem1094426 {A : Type'} (NIL' : A) (HD' : type1141 A) (h1 : term30 A NIL' HD') : term0 A HD'.
Proof. exact (proj2 (@lem1094425 A NIL' HD' h1)). Qed.
Lemma lem1094428 {A : Type'} (NIL' : A) (HD' : type1141 A) (h1 : term30 A NIL' HD') : term34 A.
Proof. exact (ex_intro (term35 A) HD' (@lem1094426 A NIL' HD' h1)). Qed.
Lemma lem1094429 {A : Type'} (NIL' : A) (h1 : term33 A NIL') : term33 A NIL'.
Proof. exact (h1). Qed.
Lemma lem1094430 {A : Type'} (NIL' : A) (h1 : term33 A NIL') : term34 A.
Proof. exact (ex_elim (@lem1094429 A NIL' h1) (fun HD' : type1141 A => fun h0 : term32 A NIL' HD' => @lem1094428 A NIL' HD' h0)). Qed.
Lemma lem1094431 {A : Type'} (NIL' : A) : (term33 A NIL') = (term34 A).
Proof. exact (prop_ext (fun h1 : term33 A NIL' => @lem1094430 A NIL' h1) (fun h1 : term34 A => @lem1094424 A NIL')). Qed.
Lemma lem1094432 {A : Type'} : term34 A.
Proof. exact (EQ_MP (@lem1094431 A (@el A)) (@lem1094424 A (@el A))). Qed.
Lemma lem1094433 {A : Type'} (HD' : type1141 A) (h1 : term0 A HD') : term36 A.
Proof. exact (ex_intro (term37 A) HD' (@lem1094393 A HD' h1)). Qed.
Lemma lem1094434 {A : Type'} (h1 : term34 A) : term34 A.
Proof. exact (h1). Qed.
Lemma lem1094435 {A : Type'} (h1 : term34 A) : term36 A.
Proof. exact (ex_elim (@lem1094434 A h1) (fun HD' : type1141 A => fun h0 : term35 A HD' => @lem1094433 A HD' h0)). Qed.
Lemma lem1094436 {A : Type'} : (term34 A) = (term36 A).
Proof. exact (prop_ext (fun h1 : term34 A => @lem1094435 A h1) (fun h1 : term36 A => @lem1094432 A)). Qed.
Lemma lem1094437 {A : Type'} : term36 A.
Proof. exact (EQ_MP (@lem1094436 A) (@lem1094432 A)). Qed.
Lemma lem1094440 {A : Type'} (HD' : type1141 A) (h1 : term6 A HD') : term6 A HD'.
Proof. exact (h1). Qed.
Lemma lem1094441 {A : Type'} (HD' : type1141 A) (h1 : term6 A HD') : term36 A.
Proof. exact (ex_intro (term37 A) HD' (@lem1094440 A HD' h1)). Qed.
Lemma lem1094442 {A : Type'} (h1 : term36 A) : term36 A.
Proof. exact (h1). Qed.
Lemma lem1094443 {A : Type'} (h1 : term36 A) : term36 A.
Proof. exact (ex_elim (@lem1094442 A h1) (fun HD' : type1141 A => fun h0 : term37 A HD' => @lem1094441 A HD' h0)). Qed.
Lemma lem1094444 {A : Type'} : (term36 A) = (term36 A).
Proof. exact (prop_ext (fun h1 : term36 A => @lem1094443 A h1) (fun h1 : term36 A => @lem1094437 A)). Qed.
Lemma lem1094445 {A : Type'} : term36 A.
Proof. exact (EQ_MP (@lem1094444 A) (@lem1094437 A)). Qed.
Lemma lem1094446 {A : Type'} : term38 A.
Proof. exact (fun _17927 : prod nat nat => @lem1094445 A). Qed.
Lemma lem1094447 {A B : Type'} (P : type1413 A B) : term39 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1094448 {A B : Type'} (P : type1413 A B) : (term39 A B P) = ((term40 A B P) = (term41 A B P)).
Proof. exact (eq_refl (term39 A B P)). Qed.
Lemma lem1094451 {A B : Type'} (P : type1413 A B) : (term40 A B P) = (term41 A B P).
Proof. exact (EQ_MP (@lem1094448 A B P) (@lem1094447 A B P)). Qed.
Lemma lem1094452 {A : Type'} (P : type1316 A) : (term42 A P) = (term43 A P).
Proof. exact (@lem1094451 (prod nat nat) (type1141 A) P). Qed.
Lemma lem1094453 {A : Type'} : (term44 A) = (term45 A).
Proof. exact (@lem1094452 A (term46 A)). Qed.
Lemma lem1094454 {A : Type'} (_17927 : prod nat nat) : (term47 A _17927) = (term37 A).
Proof. exact (eq_refl (term47 A _17927)). Qed.
Lemma lem1094455 {A : Type'} (HD' : type1141 A) : HD' = HD'.
Proof. exact (eq_refl HD'). Qed.
Lemma lem1094456 {A : Type'} (_17927 : prod nat nat) (HD' : type1141 A) : (term48 A _17927 HD') = (term49 A HD').
Proof. exact (MK_COMB (@lem1094454 A _17927) (@lem1094455 A HD')). Qed.
Lemma lem1094457 {A : Type'} (HD' : type1141 A) : (term49 A HD') = (term6 A HD').
Proof. exact (eq_refl (term49 A HD')). Qed.
Lemma lem1094458 {A : Type'} (_17927 : prod nat nat) (HD' : type1141 A) : (term48 A _17927 HD') = (term6 A HD').
Proof. exact (TRANS (@lem1094456 A _17927 HD') (@lem1094457 A HD')). Qed.
Lemma lem1094459 {A : Type'} (_17927 : prod nat nat) : (term50 A _17927) = (term37 A).
Proof. exact (fun_ext (fun HD' : type1141 A => @lem1094458 A _17927 HD')). Qed.
Lemma lem1094460 {A : Type'} : (@ex ((list A) -> A)) = (@ex ((list A) -> A)).
Proof. exact (eq_refl (@ex ((list A) -> A))). Qed.
Lemma lem1094461 {A : Type'} (_17927 : prod nat nat) : (term51 A _17927) = (term36 A).
Proof. exact (MK_COMB (@lem1094460 A) (@lem1094459 A _17927)). Qed.
Lemma lem1094462 {A : Type'} : (term52 A) = (term53 A).
Proof. exact (fun_ext (fun _17927 : prod nat nat => @lem1094461 A _17927)). Qed.
Lemma lem1094463 : (@all (prod nat nat)) = (@all (prod nat nat)).
Proof. exact (eq_refl (@all (prod nat nat))). Qed.
Lemma lem1094464 {A : Type'} : (term44 A) = (term38 A).
Proof. exact (MK_COMB (@lem1094463) (@lem1094462 A)). Qed.
Lemma lem1094465 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1094466 {A : Type'} : (term54 A) = (term55 A).
Proof. exact (MK_COMB (@lem1094465) (@lem1094464 A)). Qed.
Lemma lem1094467 {A : Type'} (_17927 : prod nat nat) : (term47 A _17927) = (term37 A).
Proof. exact (eq_refl (term47 A _17927)). Qed.
Lemma lem1094468 {A : Type'} (HD' : type1321 A) (_17927 : prod nat nat) : (HD' _17927) = (HD' _17927).
Proof. exact (eq_refl (HD' _17927)). Qed.
Lemma lem1094469 {A : Type'} (HD' : type1321 A) (_17927 : prod nat nat) : (term56 A HD' _17927) = (term57 A HD' _17927).
Proof. exact (MK_COMB (@lem1094467 A _17927) (@lem1094468 A HD' _17927)). Qed.
Lemma lem1094470 {A : Type'} (HD' : type1321 A) (_17927 : prod nat nat) : (term57 A HD' _17927) = (term58 A HD' _17927).
Proof. exact (eq_refl (term57 A HD' _17927)). Qed.
Lemma lem1094471 {A : Type'} (HD' : type1321 A) (_17927 : prod nat nat) : (term56 A HD' _17927) = (term58 A HD' _17927).
Proof. exact (TRANS (@lem1094469 A HD' _17927) (@lem1094470 A HD' _17927)). Qed.
Lemma lem1094472 {A : Type'} (HD' : type1321 A) : (term59 A HD') = (term60 A HD').
Proof. exact (fun_ext (fun _17927 : prod nat nat => @lem1094471 A HD' _17927)). Qed.
Lemma lem1094473 : (@all (prod nat nat)) = (@all (prod nat nat)).
Proof. exact (eq_refl (@all (prod nat nat))). Qed.
Lemma lem1094474 {A : Type'} (HD' : type1321 A) : (term61 A HD') = (term62 A HD').
Proof. exact (MK_COMB (@lem1094473) (@lem1094472 A HD')). Qed.
Lemma lem1094475 {A : Type'} : (term63 A) = (term64 A).
Proof. exact (fun_ext (fun HD' : type1321 A => @lem1094474 A HD')). Qed.
Lemma lem1094476 {A : Type'} : (@ex ((prod nat nat) -> (list A) -> A)) = (@ex ((prod nat nat) -> (list A) -> A)).
Proof. exact (eq_refl (@ex ((prod nat nat) -> (list A) -> A))). Qed.
Lemma lem1094477 {A : Type'} : (term45 A) = (term65 A).
Proof. exact (MK_COMB (@lem1094476 A) (@lem1094475 A)). Qed.
Lemma lem1094478 {A : Type'} : ((term44 A) = (term45 A)) = ((term38 A) = (term65 A)).
Proof. exact (MK_COMB (@lem1094466 A) (@lem1094477 A)). Qed.
Lemma lem1094479 {A : Type'} : (term38 A) = (term65 A).
Proof. exact (EQ_MP (@lem1094478 A) (@lem1094453 A)). Qed.
Lemma lem1094480 {A : Type'} : term65 A.
Proof. exact (EQ_MP (@lem1094479 A) (@lem1094446 A)). Qed.
Lemma lem1094482 {A : Type'} : (@ex A) = (term66 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1094483 {A : Type'} : (@ex ((prod nat nat) -> (list A) -> A)) = (term67 A).
Proof. exact (@lem1094482 (type1321 A)). Qed.
Lemma lem1094484 {A : Type'} : (term64 A) = (term64 A).
Proof. exact (eq_refl (term64 A)). Qed.
Lemma lem1094485 {A : Type'} : (term65 A) = (term68 A).
Proof. exact (MK_COMB (@lem1094483 A) (@lem1094484 A)). Qed.
Lemma lem1094486 {A : Type'} : (term68 A) = (term69 A).
Proof. exact (eq_refl (term68 A)). Qed.
Lemma lem1094487 {A : Type'} : (term65 A) = (term69 A).
Proof. exact (TRANS (@lem1094485 A) (@lem1094486 A)). Qed.
Lemma lem1094488 {A : Type'} : term69 A.
Proof. exact (EQ_MP (@lem1094487 A) (@lem1094480 A)). Qed.
