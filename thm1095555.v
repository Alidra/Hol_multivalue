Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1095555_term_abbrevs.
Require Import SKOLEM_THM_spec.
Require Import list_RECURSION_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1095428 {A : Type'} (APPEND' : type1132 A) (h1 : (APPEND' (@nil A)) = (term0 A)) : (APPEND' (@nil A)) = (term0 A).
Proof. exact (h1). Qed.
Lemma lem1095429 {A : Type'} (l : list A) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem1095430 {A : Type'} (l : list A) (APPEND' : type1132 A) (h1 : (APPEND' (@nil A)) = (term0 A)) : (APPEND' (@nil A) l) = (term1 A l).
Proof. exact (MK_COMB (@lem1095428 A APPEND' h1) (@lem1095429 A l)). Qed.
Lemma lem1095431 {A : Type'} (l : list A) : (term1 A l) = l.
Proof. exact (eq_refl (term1 A l)). Qed.
Lemma lem1095432 {A : Type'} (APPEND' : type1132 A) (l : list A) : (term2 A APPEND' l) = (term2 A APPEND' l).
Proof. exact (eq_refl (term2 A APPEND' l)). Qed.
Lemma lem1095433 {A : Type'} (APPEND' : type1132 A) (l : list A) : ((APPEND' (@nil A) l) = (term1 A l)) = ((APPEND' (@nil A) l) = l).
Proof. exact (MK_COMB (@lem1095432 A APPEND' l) (@lem1095431 A l)). Qed.
Lemma lem1095434 {A : Type'} (l : list A) (APPEND' : type1132 A) (h1 : (APPEND' (@nil A)) = (term0 A)) : (APPEND' (@nil A) l) = l.
Proof. exact (EQ_MP (@lem1095433 A APPEND' l) (@lem1095430 A l APPEND' h1)). Qed.
Lemma lem1095435 {A : Type'} (APPEND' : type1132 A) (h1 : (APPEND' (@nil A)) = (term0 A)) : term3 A APPEND'.
Proof. exact (fun l : list A => @lem1095434 A l APPEND' h1). Qed.
Lemma lem1095436 {A : Type'} (APPEND' : type1132 A) (h1 : term4 A APPEND') : term4 A APPEND'.
Proof. exact (h1). Qed.
Lemma lem1095437 {A : Type'} (h : A) (APPEND' : type1132 A) (h1 : term4 A APPEND') : term5 A APPEND' h.
Proof. exact (@lem1095436 A APPEND' h1 h). Qed.
Lemma lem1095438 {A : Type'} (h : A) (APPEND' : type1132 A) : (term5 A APPEND' h) = (term6 A h APPEND').
Proof. exact (eq_refl (term5 A APPEND' h)). Qed.
Lemma lem1095439 {A : Type'} (h : A) (APPEND' : type1132 A) (h1 : term4 A APPEND') : term6 A h APPEND'.
Proof. exact (EQ_MP (@lem1095438 A h APPEND') (@lem1095437 A h APPEND' h1)). Qed.
Lemma lem1095440 {A : Type'} (h : A) (t : list A) (APPEND' : type1132 A) (h1 : term4 A APPEND') : term7 A h APPEND' t.
Proof. exact (@lem1095439 A h APPEND' h1 t). Qed.
Lemma lem1095441 {A : Type'} (h : A) (APPEND' : type1132 A) (t : list A) : (term7 A h APPEND' t) = ((term8 A APPEND' h t) = (term9 A h APPEND' t)).
Proof. exact (eq_refl (term7 A h APPEND' t)). Qed.
Lemma lem1095442 {A : Type'} (h : A) (t : list A) (APPEND' : type1132 A) (h1 : term4 A APPEND') : (term8 A APPEND' h t) = (term9 A h APPEND' t).
Proof. exact (EQ_MP (@lem1095441 A h APPEND' t) (@lem1095440 A h t APPEND' h1)). Qed.
Lemma lem1095443 {A : Type'} (l : list A) : l = l.
Proof. exact (eq_refl l). Qed.
Lemma lem1095444 {A : Type'} (h : A) (t : list A) (l : list A) (APPEND' : type1132 A) (h1 : term4 A APPEND') : (term10 A APPEND' h t l) = (term11 A h APPEND' t l).
Proof. exact (MK_COMB (@lem1095442 A h t APPEND' h1) (@lem1095443 A l)). Qed.
Lemma lem1095445 {A : Type'} (h : A) (APPEND' : type1132 A) (t : list A) (l : list A) : (term11 A h APPEND' t l) = (term12 A h APPEND' t l).
Proof. exact (eq_refl (term11 A h APPEND' t l)). Qed.
Lemma lem1095446 {A : Type'} (APPEND' : type1132 A) (h : A) (t : list A) (l : list A) : (term13 A APPEND' h t l) = (term13 A APPEND' h t l).
Proof. exact (eq_refl (term13 A APPEND' h t l)). Qed.
Lemma lem1095447 {A : Type'} (h : A) (APPEND' : type1132 A) (t : list A) (l : list A) : ((term10 A APPEND' h t l) = (term11 A h APPEND' t l)) = ((term10 A APPEND' h t l) = (term12 A h APPEND' t l)).
Proof. exact (MK_COMB (@lem1095446 A APPEND' h t l) (@lem1095445 A h APPEND' t l)). Qed.
Lemma lem1095448 {A : Type'} (h : A) (t : list A) (l : list A) (APPEND' : type1132 A) (h1 : term4 A APPEND') : (term10 A APPEND' h t l) = (term12 A h APPEND' t l).
Proof. exact (EQ_MP (@lem1095447 A h APPEND' t l) (@lem1095444 A h t l APPEND' h1)). Qed.
Lemma lem1095449 {A : Type'} (h : A) (t : list A) (APPEND' : type1132 A) (h1 : term4 A APPEND') : term14 A h APPEND' t.
Proof. exact (fun l : list A => @lem1095448 A h t l APPEND' h1). Qed.
Lemma lem1095450 {A : Type'} (h : A) (APPEND' : type1132 A) (h1 : term4 A APPEND') : term15 A h APPEND'.
Proof. exact (fun t : list A => @lem1095449 A h t APPEND' h1). Qed.
Lemma lem1095451 {A : Type'} (APPEND' : type1132 A) (h1 : term4 A APPEND') : term16 A APPEND'.
Proof. exact (fun h : A => @lem1095450 A h APPEND' h1). Qed.
Lemma lem1095452 {A : Type'} (APPEND' : type1132 A) (h1 : term17 A APPEND') : term17 A APPEND'.
Proof. exact (h1). Qed.
Lemma lem1095453 {A : Type'} (APPEND' : type1132 A) (h1 : term17 A APPEND') : term4 A APPEND'.
Proof. exact (proj2 (@lem1095452 A APPEND' h1)). Qed.
Lemma lem1095454 {A : Type'} (APPEND' : type1132 A) (h1 : term17 A APPEND') : (APPEND' (@nil A)) = (term0 A).
Proof. exact (proj1 (@lem1095452 A APPEND' h1)). Qed.
Lemma lem1095455 {A : Type'} (APPEND' : type1132 A) (h1 : term17 A APPEND') : ((APPEND' (@nil A)) = (term0 A)) = (term3 A APPEND').
Proof. exact (prop_ext (fun h2 : (APPEND' (@nil A)) = (term0 A) => @lem1095435 A APPEND' h2) (fun h2 : term3 A APPEND' => @lem1095454 A APPEND' h1)). Qed.
Lemma lem1095456 {A : Type'} (APPEND' : type1132 A) (h1 : term17 A APPEND') : term3 A APPEND'.
Proof. exact (EQ_MP (@lem1095455 A APPEND' h1) (@lem1095454 A APPEND' h1)). Qed.
Lemma lem1095457 {A : Type'} (APPEND' : type1132 A) (h1 : term17 A APPEND') : (term4 A APPEND') = (term16 A APPEND').
Proof. exact (prop_ext (fun h2 : term4 A APPEND' => @lem1095451 A APPEND' h2) (fun h2 : term16 A APPEND' => @lem1095453 A APPEND' h1)). Qed.
Lemma lem1095458 {A : Type'} (APPEND' : type1132 A) (h1 : term17 A APPEND') : term16 A APPEND'.
Proof. exact (EQ_MP (@lem1095457 A APPEND' h1) (@lem1095453 A APPEND' h1)). Qed.
Lemma lem1095459 {A : Type'} (APPEND' : type1132 A) (h1 : term17 A APPEND') : term18 A APPEND'.
Proof. exact (conj (@lem1095456 A APPEND' h1) (@lem1095458 A APPEND' h1)). Qed.
Lemma lem1095460 {A Z : Type'} (NIL' : Z) : term19 A Z NIL'.
Proof. exact (@lem1072128 A Z NIL'). Qed.
Lemma lem1095461 {A Z : Type'} (NIL' : Z) : (term19 A Z NIL') = (term20 A Z NIL').
Proof. exact (eq_refl (term19 A Z NIL')). Qed.
Lemma lem1095462 {A Z : Type'} (NIL' : Z) : term20 A Z NIL'.
Proof. exact (EQ_MP (@lem1095461 A Z NIL') (@lem1095460 A Z NIL')). Qed.
Lemma lem1095463 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term21 A Z NIL' CONS'.
Proof. exact (@lem1095462 A Z NIL' CONS'). Qed.
Lemma lem1095464 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : (term21 A Z NIL' CONS') = (term22 A Z NIL' CONS').
Proof. exact (eq_refl (term21 A Z NIL' CONS')). Qed.
Lemma lem1095465 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term22 A Z NIL' CONS'.
Proof. exact (EQ_MP (@lem1095464 A Z NIL' CONS') (@lem1095463 A Z NIL' CONS')). Qed.
Lemma lem1095466 {A : Type'} (NIL' : type1138 A) (CONS' : type1388 A) : term23 A NIL' CONS'.
Proof. exact (@lem1095465 A (type1138 A) NIL' CONS'). Qed.
Lemma lem1095467 {A : Type'} : term24 A.
Proof. exact (@lem1095466 A (term0 A) (term25 A)). Qed.
Lemma lem1095468 {A : Type'} (a0 : A) : (term26 A a0) = (term27 A a0).
Proof. exact (eq_refl (term26 A a0)). Qed.
Lemma lem1095469 {A : Type'} (a1 : list A) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1095470 {A : Type'} (a0 : A) (a1 : list A) : (term28 A a0 a1) = (term29 A a0 a1).
Proof. exact (MK_COMB (@lem1095468 A a0) (@lem1095469 A a1)). Qed.
Lemma lem1095471 {A : Type'} (a1 : list A) (a0 : A) : (term29 A a0 a1) = (term30 A a0).
Proof. exact (eq_refl (term29 A a0 a1)). Qed.
Lemma lem1095472 {A : Type'} (a1 : list A) (a0 : A) : (term28 A a0 a1) = (term30 A a0).
Proof. exact (TRANS (@lem1095470 A a0 a1) (@lem1095471 A a1 a0)). Qed.
Lemma lem1095473 {A : Type'} (fn : type1132 A) (a1 : list A) : (fn a1) = (fn a1).
Proof. exact (eq_refl (fn a1)). Qed.
Lemma lem1095474 {A : Type'} (a0 : A) (fn : type1132 A) (a1 : list A) : (term31 A a0 fn a1) = (term32 A a0 fn a1).
Proof. exact (MK_COMB (@lem1095472 A a1 a0) (@lem1095473 A fn a1)). Qed.
Lemma lem1095475 {A : Type'} (a0 : A) (fn : type1132 A) (a1 : list A) : (term32 A a0 fn a1) = (term9 A a0 fn a1).
Proof. exact (eq_refl (term32 A a0 fn a1)). Qed.
Lemma lem1095476 {A : Type'} (a0 : A) (fn : type1132 A) (a1 : list A) : (term31 A a0 fn a1) = (term9 A a0 fn a1).
Proof. exact (TRANS (@lem1095474 A a0 fn a1) (@lem1095475 A a0 fn a1)). Qed.
Lemma lem1095477 {A : Type'} (fn : type1132 A) (a0 : A) (a1 : list A) : (term33 A fn a0 a1) = (term33 A fn a0 a1).
Proof. exact (eq_refl (term33 A fn a0 a1)). Qed.
Lemma lem1095478 {A : Type'} (a0 : A) (fn : type1132 A) (a1 : list A) : ((term8 A fn a0 a1) = (term31 A a0 fn a1)) = ((term8 A fn a0 a1) = (term9 A a0 fn a1)).
Proof. exact (MK_COMB (@lem1095477 A fn a0 a1) (@lem1095476 A a0 fn a1)). Qed.
Lemma lem1095479 {A : Type'} (a0 : A) (fn : type1132 A) : (term34 A a0 fn) = (term35 A a0 fn).
Proof. exact (fun_ext (fun a1 : list A => @lem1095478 A a0 fn a1)). Qed.
Lemma lem1095480 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1095481 {A : Type'} (a0 : A) (fn : type1132 A) : (term36 A a0 fn) = (term6 A a0 fn).
Proof. exact (MK_COMB (@lem1095480 A) (@lem1095479 A a0 fn)). Qed.
Lemma lem1095482 {A : Type'} (fn : type1132 A) : (term37 A fn) = (term38 A fn).
Proof. exact (fun_ext (fun a0 : A => @lem1095481 A a0 fn)). Qed.
Lemma lem1095483 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1095484 {A : Type'} (fn : type1132 A) : (term39 A fn) = (term4 A fn).
Proof. exact (MK_COMB (@lem1095483 A) (@lem1095482 A fn)). Qed.
Lemma lem1095485 {A : Type'} (fn : type1132 A) : (term40 A fn) = (term40 A fn).
Proof. exact (eq_refl (term40 A fn)). Qed.
Lemma lem1095486 {A : Type'} (fn : type1132 A) : (term41 A fn) = (term17 A fn).
Proof. exact (MK_COMB (@lem1095485 A fn) (@lem1095484 A fn)). Qed.
Lemma lem1095487 {A : Type'} : (term42 A) = (term43 A).
Proof. exact (fun_ext (fun fn : type1132 A => @lem1095486 A fn)). Qed.
Lemma lem1095488 {A : Type'} : (@ex ((list A) -> (list A) -> list A)) = (@ex ((list A) -> (list A) -> list A)).
Proof. exact (eq_refl (@ex ((list A) -> (list A) -> list A))). Qed.
Lemma lem1095489 {A : Type'} : (term24 A) = (term44 A).
Proof. exact (MK_COMB (@lem1095488 A) (@lem1095487 A)). Qed.
Lemma lem1095490 {A : Type'} : term44 A.
Proof. exact (EQ_MP (@lem1095489 A) (@lem1095467 A)). Qed.
Lemma lem1095491 {A : Type'} (APPEND' : type1132 A) (h1 : term17 A APPEND') : term17 A APPEND'.
Proof. exact (h1). Qed.
Lemma lem1095492 {A : Type'} (APPEND' : type1132 A) (h1 : term17 A APPEND') : term4 A APPEND'.
Proof. exact (proj2 (@lem1095491 A APPEND' h1)). Qed.
Lemma lem1095493 {A : Type'} (APPEND' : type1132 A) (h1 : term17 A APPEND') : (APPEND' (@nil A)) = (term0 A).
Proof. exact (proj1 (@lem1095491 A APPEND' h1)). Qed.
Lemma lem1095494 {A : Type'} (APPEND' : type1132 A) (h1 : term17 A APPEND') : term17 A APPEND'.
Proof. exact (conj (@lem1095493 A APPEND' h1) (@lem1095492 A APPEND' h1)). Qed.
Lemma lem1095495 {A : Type'} (APPEND' : type1132 A) (h1 : term17 A APPEND') : term44 A.
Proof. exact (ex_intro (term43 A) APPEND' (@lem1095494 A APPEND' h1)). Qed.
Lemma lem1095496 {A : Type'} (h1 : term44 A) : term44 A.
Proof. exact (h1). Qed.
Lemma lem1095497 {A : Type'} (h1 : term44 A) : term44 A.
Proof. exact (ex_elim (@lem1095496 A h1) (fun APPEND' : type1132 A => fun h0 : term43 A APPEND' => @lem1095495 A APPEND' h0)). Qed.
Lemma lem1095498 {A : Type'} : (term44 A) = (term44 A).
Proof. exact (prop_ext (fun h1 : term44 A => @lem1095497 A h1) (fun h1 : term44 A => @lem1095490 A)). Qed.
Lemma lem1095499 {A : Type'} : term44 A.
Proof. exact (EQ_MP (@lem1095498 A) (@lem1095490 A)). Qed.
Lemma lem1095500 {A : Type'} (APPEND' : type1132 A) (h1 : term17 A APPEND') : term45 A.
Proof. exact (ex_intro (term46 A) APPEND' (@lem1095459 A APPEND' h1)). Qed.
Lemma lem1095501 {A : Type'} (h1 : term44 A) : term44 A.
Proof. exact (h1). Qed.
Lemma lem1095502 {A : Type'} (h1 : term44 A) : term45 A.
Proof. exact (ex_elim (@lem1095501 A h1) (fun APPEND' : type1132 A => fun h0 : term43 A APPEND' => @lem1095500 A APPEND' h0)). Qed.
Lemma lem1095503 {A : Type'} : (term44 A) = (term45 A).
Proof. exact (prop_ext (fun h1 : term44 A => @lem1095502 A h1) (fun h1 : term45 A => @lem1095499 A)). Qed.
Lemma lem1095504 {A : Type'} : term45 A.
Proof. exact (EQ_MP (@lem1095503 A) (@lem1095499 A)). Qed.
Lemma lem1095507 {A : Type'} (APPEND' : type1132 A) (h1 : term18 A APPEND') : term18 A APPEND'.
Proof. exact (h1). Qed.
Lemma lem1095508 {A : Type'} (APPEND' : type1132 A) (h1 : term18 A APPEND') : term45 A.
Proof. exact (ex_intro (term46 A) APPEND' (@lem1095507 A APPEND' h1)). Qed.
Lemma lem1095509 {A : Type'} (h1 : term45 A) : term45 A.
Proof. exact (h1). Qed.
Lemma lem1095510 {A : Type'} (h1 : term45 A) : term45 A.
Proof. exact (ex_elim (@lem1095509 A h1) (fun APPEND' : type1132 A => fun h0 : term46 A APPEND' => @lem1095508 A APPEND' h0)). Qed.
Lemma lem1095511 {A : Type'} : (term45 A) = (term45 A).
Proof. exact (prop_ext (fun h1 : term45 A => @lem1095510 A h1) (fun h1 : term45 A => @lem1095504 A)). Qed.
Lemma lem1095512 {A : Type'} : term45 A.
Proof. exact (EQ_MP (@lem1095511 A) (@lem1095504 A)). Qed.
Lemma lem1095513 {A : Type'} : term47 A.
Proof. exact (fun _17935 : type1671 => @lem1095512 A). Qed.
Lemma lem1095514 {A B : Type'} (P : type1413 A B) : term48 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1095515 {A B : Type'} (P : type1413 A B) : (term48 A B P) = ((term49 A B P) = (term50 A B P)).
Proof. exact (eq_refl (term48 A B P)). Qed.
Lemma lem1095518 {A B : Type'} (P : type1413 A B) : (term49 A B P) = (term50 A B P).
Proof. exact (EQ_MP (@lem1095515 A B P) (@lem1095514 A B P)). Qed.
Lemma lem1095519 {A : Type'} (P : type1264 A) : (term51 A P) = (term52 A P).
Proof. exact (@lem1095518 type1671 (type1132 A) P). Qed.
Lemma lem1095520 {A : Type'} : (term53 A) = (term54 A).
Proof. exact (@lem1095519 A (term55 A)). Qed.
Lemma lem1095521 {A : Type'} (_17935 : type1671) : (term56 A _17935) = (term46 A).
Proof. exact (eq_refl (term56 A _17935)). Qed.
Lemma lem1095522 {A : Type'} (APPEND' : type1132 A) : APPEND' = APPEND'.
Proof. exact (eq_refl APPEND'). Qed.
Lemma lem1095523 {A : Type'} (_17935 : type1671) (APPEND' : type1132 A) : (term57 A _17935 APPEND') = (term58 A APPEND').
Proof. exact (MK_COMB (@lem1095521 A _17935) (@lem1095522 A APPEND')). Qed.
Lemma lem1095524 {A : Type'} (APPEND' : type1132 A) : (term58 A APPEND') = (term18 A APPEND').
Proof. exact (eq_refl (term58 A APPEND')). Qed.
Lemma lem1095525 {A : Type'} (_17935 : type1671) (APPEND' : type1132 A) : (term57 A _17935 APPEND') = (term18 A APPEND').
Proof. exact (TRANS (@lem1095523 A _17935 APPEND') (@lem1095524 A APPEND')). Qed.
Lemma lem1095526 {A : Type'} (_17935 : type1671) : (term59 A _17935) = (term46 A).
Proof. exact (fun_ext (fun APPEND' : type1132 A => @lem1095525 A _17935 APPEND')). Qed.
Lemma lem1095527 {A : Type'} : (@ex ((list A) -> (list A) -> list A)) = (@ex ((list A) -> (list A) -> list A)).
Proof. exact (eq_refl (@ex ((list A) -> (list A) -> list A))). Qed.
Lemma lem1095528 {A : Type'} (_17935 : type1671) : (term60 A _17935) = (term45 A).
Proof. exact (MK_COMB (@lem1095527 A) (@lem1095526 A _17935)). Qed.
Lemma lem1095529 {A : Type'} : (term61 A) = (term62 A).
Proof. exact (fun_ext (fun _17935 : type1671 => @lem1095528 A _17935)). Qed.
Lemma lem1095530 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))). Qed.
Lemma lem1095531 {A : Type'} : (term53 A) = (term47 A).
Proof. exact (MK_COMB (@lem1095530) (@lem1095529 A)). Qed.
Lemma lem1095532 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1095533 {A : Type'} : (term63 A) = (term64 A).
Proof. exact (MK_COMB (@lem1095532) (@lem1095531 A)). Qed.
Lemma lem1095534 {A : Type'} (_17935 : type1671) : (term56 A _17935) = (term46 A).
Proof. exact (eq_refl (term56 A _17935)). Qed.
Lemma lem1095535 {A : Type'} (APPEND' : type1270 A) (_17935 : type1671) : (APPEND' _17935) = (APPEND' _17935).
Proof. exact (eq_refl (APPEND' _17935)). Qed.
Lemma lem1095536 {A : Type'} (APPEND' : type1270 A) (_17935 : type1671) : (term65 A APPEND' _17935) = (term66 A APPEND' _17935).
Proof. exact (MK_COMB (@lem1095534 A _17935) (@lem1095535 A APPEND' _17935)). Qed.
Lemma lem1095537 {A : Type'} (APPEND' : type1270 A) (_17935 : type1671) : (term66 A APPEND' _17935) = (term67 A APPEND' _17935).
Proof. exact (eq_refl (term66 A APPEND' _17935)). Qed.
Lemma lem1095538 {A : Type'} (APPEND' : type1270 A) (_17935 : type1671) : (term65 A APPEND' _17935) = (term67 A APPEND' _17935).
Proof. exact (TRANS (@lem1095536 A APPEND' _17935) (@lem1095537 A APPEND' _17935)). Qed.
Lemma lem1095539 {A : Type'} (APPEND' : type1270 A) : (term68 A APPEND') = (term69 A APPEND').
Proof. exact (fun_ext (fun _17935 : type1671 => @lem1095538 A APPEND' _17935)). Qed.
Lemma lem1095540 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))). Qed.
Lemma lem1095541 {A : Type'} (APPEND' : type1270 A) : (term70 A APPEND') = (term71 A APPEND').
Proof. exact (MK_COMB (@lem1095540) (@lem1095539 A APPEND')). Qed.
Lemma lem1095542 {A : Type'} : (term72 A) = (term73 A).
Proof. exact (fun_ext (fun APPEND' : type1270 A => @lem1095541 A APPEND')). Qed.
Lemma lem1095543 {A : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (list A) -> (list A) -> list A)) = (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (list A) -> (list A) -> list A)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (list A) -> (list A) -> list A))). Qed.
Lemma lem1095544 {A : Type'} : (term54 A) = (term74 A).
Proof. exact (MK_COMB (@lem1095543 A) (@lem1095542 A)). Qed.
Lemma lem1095545 {A : Type'} : ((term53 A) = (term54 A)) = ((term47 A) = (term74 A)).
Proof. exact (MK_COMB (@lem1095533 A) (@lem1095544 A)). Qed.
Lemma lem1095546 {A : Type'} : (term47 A) = (term74 A).
Proof. exact (EQ_MP (@lem1095545 A) (@lem1095520 A)). Qed.
Lemma lem1095547 {A : Type'} : term74 A.
Proof. exact (EQ_MP (@lem1095546 A) (@lem1095513 A)). Qed.
Lemma lem1095549 {A : Type'} : (@ex A) = (term75 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1095550 {A : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (list A) -> (list A) -> list A)) = (term76 A).
Proof. exact (@lem1095549 (type1270 A)). Qed.
Lemma lem1095551 {A : Type'} : (term73 A) = (term73 A).
Proof. exact (eq_refl (term73 A)). Qed.
Lemma lem1095552 {A : Type'} : (term74 A) = (term77 A).
Proof. exact (MK_COMB (@lem1095550 A) (@lem1095551 A)). Qed.
Lemma lem1095553 {A : Type'} : (term77 A) = (term78 A).
Proof. exact (eq_refl (term77 A)). Qed.
Lemma lem1095554 {A : Type'} : (term74 A) = (term78 A).
Proof. exact (TRANS (@lem1095552 A) (@lem1095553 A)). Qed.
Lemma lem1095555 {A : Type'} : term78 A.
Proof. exact (EQ_MP (@lem1095554 A) (@lem1095547 A)). Qed.
