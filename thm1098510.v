Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1098510_term_abbrevs.
Require Import SKOLEM_THM_spec.
Require Import list_RECURSION_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1098397 {_25251 : Type'} (BUTLAST' : type1138 _25251) (h1 : (BUTLAST' (@nil _25251)) = (@nil _25251)) : (BUTLAST' (@nil _25251)) = (@nil _25251).
Proof. exact (h1). Qed.
Lemma lem1098398 {_25251 : Type'} (BUTLAST' : type1138 _25251) (h1 : term0 _25251 BUTLAST') : term0 _25251 BUTLAST'.
Proof. exact (h1). Qed.
Lemma lem1098399 {_25251 : Type'} (h : _25251) (BUTLAST' : type1138 _25251) (h1 : term0 _25251 BUTLAST') : term1 _25251 BUTLAST' h.
Proof. exact (@lem1098398 _25251 BUTLAST' h1 h). Qed.
Lemma lem1098400 {_25251 : Type'} (h : _25251) (BUTLAST' : type1138 _25251) : (term1 _25251 BUTLAST' h) = (term2 _25251 h BUTLAST').
Proof. exact (eq_refl (term1 _25251 BUTLAST' h)). Qed.
Lemma lem1098401 {_25251 : Type'} (h : _25251) (BUTLAST' : type1138 _25251) (h1 : term0 _25251 BUTLAST') : term2 _25251 h BUTLAST'.
Proof. exact (EQ_MP (@lem1098400 _25251 h BUTLAST') (@lem1098399 _25251 h BUTLAST' h1)). Qed.
Lemma lem1098402 {_25251 : Type'} (h : _25251) (t : list _25251) (BUTLAST' : type1138 _25251) (h1 : term0 _25251 BUTLAST') : term3 _25251 h BUTLAST' t.
Proof. exact (@lem1098401 _25251 h BUTLAST' h1 t). Qed.
Lemma lem1098403 {_25251 : Type'} (h : _25251) (BUTLAST' : type1138 _25251) (t : list _25251) : (term3 _25251 h BUTLAST' t) = ((term4 _25251 BUTLAST' h t) = (term5 _25251 h BUTLAST' t)).
Proof. exact (eq_refl (term3 _25251 h BUTLAST' t)). Qed.
Lemma lem1098404 {_25251 : Type'} (h : _25251) (t : list _25251) (BUTLAST' : type1138 _25251) (h1 : term0 _25251 BUTLAST') : (term4 _25251 BUTLAST' h t) = (term5 _25251 h BUTLAST' t).
Proof. exact (EQ_MP (@lem1098403 _25251 h BUTLAST' t) (@lem1098402 _25251 h t BUTLAST' h1)). Qed.
Lemma lem1098405 {_25251 : Type'} (h : _25251) (BUTLAST' : type1138 _25251) (h1 : term0 _25251 BUTLAST') : term2 _25251 h BUTLAST'.
Proof. exact (fun t : list _25251 => @lem1098404 _25251 h t BUTLAST' h1). Qed.
Lemma lem1098406 {_25251 : Type'} (BUTLAST' : type1138 _25251) (h1 : term0 _25251 BUTLAST') : term0 _25251 BUTLAST'.
Proof. exact (fun h : _25251 => @lem1098405 _25251 h BUTLAST' h1). Qed.
Lemma lem1098407 {_25251 : Type'} (BUTLAST' : type1138 _25251) (h1 : term6 _25251 BUTLAST') : term6 _25251 BUTLAST'.
Proof. exact (h1). Qed.
Lemma lem1098408 {_25251 : Type'} (BUTLAST' : type1138 _25251) (h1 : term6 _25251 BUTLAST') : term0 _25251 BUTLAST'.
Proof. exact (proj2 (@lem1098407 _25251 BUTLAST' h1)). Qed.
Lemma lem1098409 {_25251 : Type'} (BUTLAST' : type1138 _25251) (h1 : term6 _25251 BUTLAST') : (BUTLAST' (@nil _25251)) = (@nil _25251).
Proof. exact (proj1 (@lem1098407 _25251 BUTLAST' h1)). Qed.
Lemma lem1098410 {_25251 : Type'} (BUTLAST' : type1138 _25251) (h1 : term6 _25251 BUTLAST') : ((BUTLAST' (@nil _25251)) = (@nil _25251)) = ((BUTLAST' (@nil _25251)) = (@nil _25251)).
Proof. exact (prop_ext (fun h2 : (BUTLAST' (@nil _25251)) = (@nil _25251) => @lem1098397 _25251 BUTLAST' h2) (fun h2 : (BUTLAST' (@nil _25251)) = (@nil _25251) => @lem1098409 _25251 BUTLAST' h1)). Qed.
Lemma lem1098411 {_25251 : Type'} (BUTLAST' : type1138 _25251) (h1 : term6 _25251 BUTLAST') : (BUTLAST' (@nil _25251)) = (@nil _25251).
Proof. exact (EQ_MP (@lem1098410 _25251 BUTLAST' h1) (@lem1098409 _25251 BUTLAST' h1)). Qed.
Lemma lem1098412 {_25251 : Type'} (BUTLAST' : type1138 _25251) (h1 : term6 _25251 BUTLAST') : (term0 _25251 BUTLAST') = (term0 _25251 BUTLAST').
Proof. exact (prop_ext (fun h2 : term0 _25251 BUTLAST' => @lem1098406 _25251 BUTLAST' h2) (fun h2 : term0 _25251 BUTLAST' => @lem1098408 _25251 BUTLAST' h1)). Qed.
Lemma lem1098413 {_25251 : Type'} (BUTLAST' : type1138 _25251) (h1 : term6 _25251 BUTLAST') : term0 _25251 BUTLAST'.
Proof. exact (EQ_MP (@lem1098412 _25251 BUTLAST' h1) (@lem1098408 _25251 BUTLAST' h1)). Qed.
Lemma lem1098414 {_25251 : Type'} (BUTLAST' : type1138 _25251) (h1 : term6 _25251 BUTLAST') : term6 _25251 BUTLAST'.
Proof. exact (conj (@lem1098411 _25251 BUTLAST' h1) (@lem1098413 _25251 BUTLAST' h1)). Qed.
Lemma lem1098415 {A Z : Type'} (NIL' : Z) : term7 A Z NIL'.
Proof. exact (@lem1072128 A Z NIL'). Qed.
Lemma lem1098416 {A Z : Type'} (NIL' : Z) : (term7 A Z NIL') = (term8 A Z NIL').
Proof. exact (eq_refl (term7 A Z NIL')). Qed.
Lemma lem1098417 {A Z : Type'} (NIL' : Z) : term8 A Z NIL'.
Proof. exact (EQ_MP (@lem1098416 A Z NIL') (@lem1098415 A Z NIL')). Qed.
Lemma lem1098418 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term9 A Z NIL' CONS'.
Proof. exact (@lem1098417 A Z NIL' CONS'). Qed.
Lemma lem1098419 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : (term9 A Z NIL' CONS') = (term10 A Z NIL' CONS').
Proof. exact (eq_refl (term9 A Z NIL' CONS')). Qed.
Lemma lem1098420 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term10 A Z NIL' CONS'.
Proof. exact (EQ_MP (@lem1098419 A Z NIL' CONS') (@lem1098418 A Z NIL' CONS')). Qed.
Lemma lem1098421 {_25251 : Type'} (NIL' : list _25251) (CONS' : type1391 _25251) : term11 _25251 NIL' CONS'.
Proof. exact (@lem1098420 _25251 (list _25251) NIL' CONS'). Qed.
Lemma lem1098422 {_25251 : Type'} : term12 _25251.
Proof. exact (@lem1098421 _25251 (@nil _25251) (term13 _25251)). Qed.
Lemma lem1098423 {_25251 : Type'} (a0 : _25251) : (term14 _25251 a0) = (term15 _25251 a0).
Proof. exact (eq_refl (term14 _25251 a0)). Qed.
Lemma lem1098424 {_25251 : Type'} (a1 : list _25251) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1098425 {_25251 : Type'} (a0 : _25251) (a1 : list _25251) : (term16 _25251 a0 a1) = (term17 _25251 a0 a1).
Proof. exact (MK_COMB (@lem1098423 _25251 a0) (@lem1098424 _25251 a1)). Qed.
Lemma lem1098426 {_25251 : Type'} (a1 : list _25251) (a0 : _25251) : (term17 _25251 a0 a1) = (term18 _25251 a1 a0).
Proof. exact (eq_refl (term17 _25251 a0 a1)). Qed.
Lemma lem1098427 {_25251 : Type'} (a1 : list _25251) (a0 : _25251) : (term16 _25251 a0 a1) = (term18 _25251 a1 a0).
Proof. exact (TRANS (@lem1098425 _25251 a0 a1) (@lem1098426 _25251 a1 a0)). Qed.
Lemma lem1098428 {_25251 : Type'} (fn : type1138 _25251) (a1 : list _25251) : (fn a1) = (fn a1).
Proof. exact (eq_refl (fn a1)). Qed.
Lemma lem1098429 {_25251 : Type'} (a0 : _25251) (fn : type1138 _25251) (a1 : list _25251) : (term19 _25251 a0 fn a1) = (term20 _25251 a0 fn a1).
Proof. exact (MK_COMB (@lem1098427 _25251 a1 a0) (@lem1098428 _25251 fn a1)). Qed.
Lemma lem1098430 {_25251 : Type'} (a0 : _25251) (fn : type1138 _25251) (a1 : list _25251) : (term20 _25251 a0 fn a1) = (term5 _25251 a0 fn a1).
Proof. exact (eq_refl (term20 _25251 a0 fn a1)). Qed.
Lemma lem1098431 {_25251 : Type'} (a0 : _25251) (fn : type1138 _25251) (a1 : list _25251) : (term19 _25251 a0 fn a1) = (term5 _25251 a0 fn a1).
Proof. exact (TRANS (@lem1098429 _25251 a0 fn a1) (@lem1098430 _25251 a0 fn a1)). Qed.
Lemma lem1098432 {_25251 : Type'} (fn : type1138 _25251) (a0 : _25251) (a1 : list _25251) : (term21 _25251 fn a0 a1) = (term21 _25251 fn a0 a1).
Proof. exact (eq_refl (term21 _25251 fn a0 a1)). Qed.
Lemma lem1098433 {_25251 : Type'} (a0 : _25251) (fn : type1138 _25251) (a1 : list _25251) : ((term4 _25251 fn a0 a1) = (term19 _25251 a0 fn a1)) = ((term4 _25251 fn a0 a1) = (term5 _25251 a0 fn a1)).
Proof. exact (MK_COMB (@lem1098432 _25251 fn a0 a1) (@lem1098431 _25251 a0 fn a1)). Qed.
Lemma lem1098434 {_25251 : Type'} (a0 : _25251) (fn : type1138 _25251) : (term22 _25251 a0 fn) = (term23 _25251 a0 fn).
Proof. exact (fun_ext (fun a1 : list _25251 => @lem1098433 _25251 a0 fn a1)). Qed.
Lemma lem1098435 {_25251 : Type'} : (@all (list _25251)) = (@all (list _25251)).
Proof. exact (eq_refl (@all (list _25251))). Qed.
Lemma lem1098436 {_25251 : Type'} (a0 : _25251) (fn : type1138 _25251) : (term24 _25251 a0 fn) = (term2 _25251 a0 fn).
Proof. exact (MK_COMB (@lem1098435 _25251) (@lem1098434 _25251 a0 fn)). Qed.
Lemma lem1098437 {_25251 : Type'} (fn : type1138 _25251) : (term25 _25251 fn) = (term26 _25251 fn).
Proof. exact (fun_ext (fun a0 : _25251 => @lem1098436 _25251 a0 fn)). Qed.
Lemma lem1098438 {_25251 : Type'} : (@all _25251) = (@all _25251).
Proof. exact (eq_refl (@all _25251)). Qed.
Lemma lem1098439 {_25251 : Type'} (fn : type1138 _25251) : (term27 _25251 fn) = (term0 _25251 fn).
Proof. exact (MK_COMB (@lem1098438 _25251) (@lem1098437 _25251 fn)). Qed.
Lemma lem1098440 {_25251 : Type'} (fn : type1138 _25251) : (term28 _25251 fn) = (term28 _25251 fn).
Proof. exact (eq_refl (term28 _25251 fn)). Qed.
Lemma lem1098441 {_25251 : Type'} (fn : type1138 _25251) : (term29 _25251 fn) = (term6 _25251 fn).
Proof. exact (MK_COMB (@lem1098440 _25251 fn) (@lem1098439 _25251 fn)). Qed.
Lemma lem1098442 {_25251 : Type'} : (term30 _25251) = (term31 _25251).
Proof. exact (fun_ext (fun fn : type1138 _25251 => @lem1098441 _25251 fn)). Qed.
Lemma lem1098443 {_25251 : Type'} : (@ex ((list _25251) -> list _25251)) = (@ex ((list _25251) -> list _25251)).
Proof. exact (eq_refl (@ex ((list _25251) -> list _25251))). Qed.
Lemma lem1098444 {_25251 : Type'} : (term12 _25251) = (term32 _25251).
Proof. exact (MK_COMB (@lem1098443 _25251) (@lem1098442 _25251)). Qed.
Lemma lem1098445 {_25251 : Type'} : term32 _25251.
Proof. exact (EQ_MP (@lem1098444 _25251) (@lem1098422 _25251)). Qed.
Lemma lem1098446 {_25251 : Type'} (BUTLAST' : type1138 _25251) (h1 : term6 _25251 BUTLAST') : term6 _25251 BUTLAST'.
Proof. exact (h1). Qed.
Lemma lem1098447 {_25251 : Type'} (BUTLAST' : type1138 _25251) (h1 : term6 _25251 BUTLAST') : term0 _25251 BUTLAST'.
Proof. exact (proj2 (@lem1098446 _25251 BUTLAST' h1)). Qed.
Lemma lem1098448 {_25251 : Type'} (BUTLAST' : type1138 _25251) (h1 : term6 _25251 BUTLAST') : (BUTLAST' (@nil _25251)) = (@nil _25251).
Proof. exact (proj1 (@lem1098446 _25251 BUTLAST' h1)). Qed.
Lemma lem1098449 {_25251 : Type'} (BUTLAST' : type1138 _25251) (h1 : term6 _25251 BUTLAST') : term6 _25251 BUTLAST'.
Proof. exact (conj (@lem1098448 _25251 BUTLAST' h1) (@lem1098447 _25251 BUTLAST' h1)). Qed.
Lemma lem1098450 {_25251 : Type'} (BUTLAST' : type1138 _25251) (h1 : term6 _25251 BUTLAST') : term32 _25251.
Proof. exact (ex_intro (term31 _25251) BUTLAST' (@lem1098449 _25251 BUTLAST' h1)). Qed.
Lemma lem1098451 {_25251 : Type'} (h1 : term32 _25251) : term32 _25251.
Proof. exact (h1). Qed.
Lemma lem1098452 {_25251 : Type'} (h1 : term32 _25251) : term32 _25251.
Proof. exact (ex_elim (@lem1098451 _25251 h1) (fun BUTLAST' : type1138 _25251 => fun h0 : term31 _25251 BUTLAST' => @lem1098450 _25251 BUTLAST' h0)). Qed.
Lemma lem1098453 {_25251 : Type'} : (term32 _25251) = (term32 _25251).
Proof. exact (prop_ext (fun h1 : term32 _25251 => @lem1098452 _25251 h1) (fun h1 : term32 _25251 => @lem1098445 _25251)). Qed.
Lemma lem1098454 {_25251 : Type'} : term32 _25251.
Proof. exact (EQ_MP (@lem1098453 _25251) (@lem1098445 _25251)). Qed.
Lemma lem1098455 {_25251 : Type'} (BUTLAST' : type1138 _25251) (h1 : term6 _25251 BUTLAST') : term32 _25251.
Proof. exact (ex_intro (term31 _25251) BUTLAST' (@lem1098414 _25251 BUTLAST' h1)). Qed.
Lemma lem1098456 {_25251 : Type'} (h1 : term32 _25251) : term32 _25251.
Proof. exact (h1). Qed.
Lemma lem1098457 {_25251 : Type'} (h1 : term32 _25251) : term32 _25251.
Proof. exact (ex_elim (@lem1098456 _25251 h1) (fun BUTLAST' : type1138 _25251 => fun h0 : term31 _25251 BUTLAST' => @lem1098455 _25251 BUTLAST' h0)). Qed.
Lemma lem1098458 {_25251 : Type'} : (term32 _25251) = (term32 _25251).
Proof. exact (prop_ext (fun h1 : term32 _25251 => @lem1098457 _25251 h1) (fun h1 : term32 _25251 => @lem1098454 _25251)). Qed.
Lemma lem1098459 {_25251 : Type'} : term32 _25251.
Proof. exact (EQ_MP (@lem1098458 _25251) (@lem1098454 _25251)). Qed.
Lemma lem1098462 {_25251 : Type'} (BUTLAST' : type1138 _25251) (h1 : term6 _25251 BUTLAST') : term6 _25251 BUTLAST'.
Proof. exact (h1). Qed.
Lemma lem1098463 {_25251 : Type'} (BUTLAST' : type1138 _25251) (h1 : term6 _25251 BUTLAST') : term32 _25251.
Proof. exact (ex_intro (term31 _25251) BUTLAST' (@lem1098462 _25251 BUTLAST' h1)). Qed.
Lemma lem1098464 {_25251 : Type'} (h1 : term32 _25251) : term32 _25251.
Proof. exact (h1). Qed.
Lemma lem1098465 {_25251 : Type'} (h1 : term32 _25251) : term32 _25251.
Proof. exact (ex_elim (@lem1098464 _25251 h1) (fun BUTLAST' : type1138 _25251 => fun h0 : term31 _25251 BUTLAST' => @lem1098463 _25251 BUTLAST' h0)). Qed.
Lemma lem1098466 {_25251 : Type'} : (term32 _25251) = (term32 _25251).
Proof. exact (prop_ext (fun h1 : term32 _25251 => @lem1098465 _25251 h1) (fun h1 : term32 _25251 => @lem1098459 _25251)). Qed.
Lemma lem1098467 {_25251 : Type'} : term32 _25251.
Proof. exact (EQ_MP (@lem1098466 _25251) (@lem1098459 _25251)). Qed.
Lemma lem1098468 {_25251 : Type'} : term33 _25251.
Proof. exact (fun _17958 : type1670 => @lem1098467 _25251). Qed.
Lemma lem1098469 {A B : Type'} (P : type1413 A B) : term34 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1098470 {A B : Type'} (P : type1413 A B) : (term34 A B P) = ((term35 A B P) = (term36 A B P)).
Proof. exact (eq_refl (term34 A B P)). Qed.
Lemma lem1098473 {A B : Type'} (P : type1413 A B) : (term35 A B P) = (term36 A B P).
Proof. exact (EQ_MP (@lem1098470 A B P) (@lem1098469 A B P)). Qed.
Lemma lem1098474 {_25251 : Type'} (P : type1253 _25251) : (term37 _25251 P) = (term38 _25251 P).
Proof. exact (@lem1098473 type1670 (type1138 _25251) P). Qed.
Lemma lem1098475 {_25251 : Type'} : (term39 _25251) = (term40 _25251).
Proof. exact (@lem1098474 _25251 (term41 _25251)). Qed.
Lemma lem1098476 {_25251 : Type'} (_17958 : type1670) : (term42 _25251 _17958) = (term31 _25251).
Proof. exact (eq_refl (term42 _25251 _17958)). Qed.
Lemma lem1098477 {_25251 : Type'} (BUTLAST' : type1138 _25251) : BUTLAST' = BUTLAST'.
Proof. exact (eq_refl BUTLAST'). Qed.
Lemma lem1098478 {_25251 : Type'} (_17958 : type1670) (BUTLAST' : type1138 _25251) : (term43 _25251 _17958 BUTLAST') = (term44 _25251 BUTLAST').
Proof. exact (MK_COMB (@lem1098476 _25251 _17958) (@lem1098477 _25251 BUTLAST')). Qed.
Lemma lem1098479 {_25251 : Type'} (BUTLAST' : type1138 _25251) : (term44 _25251 BUTLAST') = (term6 _25251 BUTLAST').
Proof. exact (eq_refl (term44 _25251 BUTLAST')). Qed.
Lemma lem1098480 {_25251 : Type'} (_17958 : type1670) (BUTLAST' : type1138 _25251) : (term43 _25251 _17958 BUTLAST') = (term6 _25251 BUTLAST').
Proof. exact (TRANS (@lem1098478 _25251 _17958 BUTLAST') (@lem1098479 _25251 BUTLAST')). Qed.
Lemma lem1098481 {_25251 : Type'} (_17958 : type1670) : (term45 _25251 _17958) = (term31 _25251).
Proof. exact (fun_ext (fun BUTLAST' : type1138 _25251 => @lem1098480 _25251 _17958 BUTLAST')). Qed.
Lemma lem1098482 {_25251 : Type'} : (@ex ((list _25251) -> list _25251)) = (@ex ((list _25251) -> list _25251)).
Proof. exact (eq_refl (@ex ((list _25251) -> list _25251))). Qed.
Lemma lem1098483 {_25251 : Type'} (_17958 : type1670) : (term46 _25251 _17958) = (term32 _25251).
Proof. exact (MK_COMB (@lem1098482 _25251) (@lem1098481 _25251 _17958)). Qed.
Lemma lem1098484 {_25251 : Type'} : (term47 _25251) = (term48 _25251).
Proof. exact (fun_ext (fun _17958 : type1670 => @lem1098483 _25251 _17958)). Qed.
Lemma lem1098485 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))). Qed.
Lemma lem1098486 {_25251 : Type'} : (term39 _25251) = (term33 _25251).
Proof. exact (MK_COMB (@lem1098485) (@lem1098484 _25251)). Qed.
Lemma lem1098487 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1098488 {_25251 : Type'} : (term49 _25251) = (term50 _25251).
Proof. exact (MK_COMB (@lem1098487) (@lem1098486 _25251)). Qed.
Lemma lem1098489 {_25251 : Type'} (_17958 : type1670) : (term42 _25251 _17958) = (term31 _25251).
Proof. exact (eq_refl (term42 _25251 _17958)). Qed.
Lemma lem1098490 {_25251 : Type'} (BUTLAST' : type1258 _25251) (_17958 : type1670) : (BUTLAST' _17958) = (BUTLAST' _17958).
Proof. exact (eq_refl (BUTLAST' _17958)). Qed.
Lemma lem1098491 {_25251 : Type'} (BUTLAST' : type1258 _25251) (_17958 : type1670) : (term51 _25251 BUTLAST' _17958) = (term52 _25251 BUTLAST' _17958).
Proof. exact (MK_COMB (@lem1098489 _25251 _17958) (@lem1098490 _25251 BUTLAST' _17958)). Qed.
Lemma lem1098492 {_25251 : Type'} (BUTLAST' : type1258 _25251) (_17958 : type1670) : (term52 _25251 BUTLAST' _17958) = (term53 _25251 BUTLAST' _17958).
Proof. exact (eq_refl (term52 _25251 BUTLAST' _17958)). Qed.
Lemma lem1098493 {_25251 : Type'} (BUTLAST' : type1258 _25251) (_17958 : type1670) : (term51 _25251 BUTLAST' _17958) = (term53 _25251 BUTLAST' _17958).
Proof. exact (TRANS (@lem1098491 _25251 BUTLAST' _17958) (@lem1098492 _25251 BUTLAST' _17958)). Qed.
Lemma lem1098494 {_25251 : Type'} (BUTLAST' : type1258 _25251) : (term54 _25251 BUTLAST') = (term55 _25251 BUTLAST').
Proof. exact (fun_ext (fun _17958 : type1670 => @lem1098493 _25251 BUTLAST' _17958)). Qed.
Lemma lem1098495 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))))). Qed.
Lemma lem1098496 {_25251 : Type'} (BUTLAST' : type1258 _25251) : (term56 _25251 BUTLAST') = (term57 _25251 BUTLAST').
Proof. exact (MK_COMB (@lem1098495) (@lem1098494 _25251 BUTLAST')). Qed.
Lemma lem1098497 {_25251 : Type'} : (term58 _25251) = (term59 _25251).
Proof. exact (fun_ext (fun BUTLAST' : type1258 _25251 => @lem1098496 _25251 BUTLAST')). Qed.
Lemma lem1098498 {_25251 : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (list _25251) -> list _25251)) = (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (list _25251) -> list _25251)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (list _25251) -> list _25251))). Qed.
Lemma lem1098499 {_25251 : Type'} : (term40 _25251) = (term60 _25251).
Proof. exact (MK_COMB (@lem1098498 _25251) (@lem1098497 _25251)). Qed.
Lemma lem1098500 {_25251 : Type'} : ((term39 _25251) = (term40 _25251)) = ((term33 _25251) = (term60 _25251)).
Proof. exact (MK_COMB (@lem1098488 _25251) (@lem1098499 _25251)). Qed.
Lemma lem1098501 {_25251 : Type'} : (term33 _25251) = (term60 _25251).
Proof. exact (EQ_MP (@lem1098500 _25251) (@lem1098475 _25251)). Qed.
Lemma lem1098502 {_25251 : Type'} : term60 _25251.
Proof. exact (EQ_MP (@lem1098501 _25251) (@lem1098468 _25251)). Qed.
Lemma lem1098504 {A : Type'} : (@ex A) = (term61 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1098505 {_25251 : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) -> (list _25251) -> list _25251)) = (term62 _25251).
Proof. exact (@lem1098504 (type1258 _25251)). Qed.
Lemma lem1098506 {_25251 : Type'} : (term59 _25251) = (term59 _25251).
Proof. exact (eq_refl (term59 _25251)). Qed.
Lemma lem1098507 {_25251 : Type'} : (term60 _25251) = (term63 _25251).
Proof. exact (MK_COMB (@lem1098505 _25251) (@lem1098506 _25251)). Qed.
Lemma lem1098508 {_25251 : Type'} : (term63 _25251) = (term64 _25251).
Proof. exact (eq_refl (term63 _25251)). Qed.
Lemma lem1098509 {_25251 : Type'} : (term60 _25251) = (term64 _25251).
Proof. exact (TRANS (@lem1098507 _25251) (@lem1098508 _25251)). Qed.
Lemma lem1098510 {_25251 : Type'} : term64 _25251.
Proof. exact (EQ_MP (@lem1098509 _25251) (@lem1098502 _25251)). Qed.
