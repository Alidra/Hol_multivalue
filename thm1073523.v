Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1073523_term_abbrevs.
Require Import list_RECURSION_spec.
Require Import thm0_spec.
Require Import thm1012671_spec.
Require Import thm1073392_spec.
Require Import thm912739_spec.
Lemma lem1073415 {A : Type'} (_17534 : type1144 A) (h1 : (_17534 (@nil A)) = (NUMERAL 0)) : (_17534 (@nil A)) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1073416 {A : Type'} (_17534 : type1144 A) (h1 : term0 A _17534) : term0 A _17534.
Proof. exact (h1). Qed.
Lemma lem1073417 {A : Type'} (a0 : A) (_17534 : type1144 A) (h1 : term0 A _17534) : term1 A _17534 a0.
Proof. exact (@lem1073416 A _17534 h1 a0). Qed.
Lemma lem1073418 {A : Type'} (_17534 : type1144 A) (a0 : A) : (term1 A _17534 a0) = (term2 A _17534 a0).
Proof. exact (eq_refl (term1 A _17534 a0)). Qed.
Lemma lem1073419 {A : Type'} (a0 : A) (_17534 : type1144 A) (h1 : term0 A _17534) : term2 A _17534 a0.
Proof. exact (EQ_MP (@lem1073418 A _17534 a0) (@lem1073417 A a0 _17534 h1)). Qed.
Lemma lem1073420 {A : Type'} (a0 : A) (a1 : list A) (_17534 : type1144 A) (h1 : term0 A _17534) : term3 A _17534 a0 a1.
Proof. exact (@lem1073419 A a0 _17534 h1 a1). Qed.
Lemma lem1073421 {A : Type'} (_17534 : type1144 A) (a0 : A) (a1 : list A) : (term3 A _17534 a0 a1) = ((term4 A _17534 a0 a1) = term5).
Proof. exact (eq_refl (term3 A _17534 a0 a1)). Qed.
Lemma lem1073422 {A : Type'} (a0 : A) (a1 : list A) (_17534 : type1144 A) (h1 : term0 A _17534) : (term4 A _17534 a0 a1) = term5.
Proof. exact (EQ_MP (@lem1073421 A _17534 a0 a1) (@lem1073420 A a0 a1 _17534 h1)). Qed.
Lemma lem1073423 {A : Type'} (a0 : A) (_17534 : type1144 A) (h1 : term0 A _17534) : term2 A _17534 a0.
Proof. exact (fun a1 : list A => @lem1073422 A a0 a1 _17534 h1). Qed.
Lemma lem1073424 {A : Type'} (_17534 : type1144 A) (h1 : term0 A _17534) : term0 A _17534.
Proof. exact (fun a0 : A => @lem1073423 A a0 _17534 h1). Qed.
Lemma lem1073425 {A : Type'} (_17534 : type1144 A) (h1 : term6 A _17534) : term6 A _17534.
Proof. exact (h1). Qed.
Lemma lem1073426 {A : Type'} (_17534 : type1144 A) (h1 : term6 A _17534) : term0 A _17534.
Proof. exact (proj2 (@lem1073425 A _17534 h1)). Qed.
Lemma lem1073427 {A : Type'} (_17534 : type1144 A) (h1 : term6 A _17534) : (_17534 (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1073425 A _17534 h1)). Qed.
Lemma lem1073428 {A : Type'} (_17534 : type1144 A) (h1 : term6 A _17534) : ((_17534 (@nil A)) = (NUMERAL 0)) = ((_17534 (@nil A)) = (NUMERAL 0)).
Proof. exact (prop_ext (fun h2 : (_17534 (@nil A)) = (NUMERAL 0) => @lem1073415 A _17534 h2) (fun h2 : (_17534 (@nil A)) = (NUMERAL 0) => @lem1073427 A _17534 h1)). Qed.
Lemma lem1073429 {A : Type'} (_17534 : type1144 A) (h1 : term6 A _17534) : (_17534 (@nil A)) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1073428 A _17534 h1) (@lem1073427 A _17534 h1)). Qed.
Lemma lem1073430 {A : Type'} (_17534 : type1144 A) (h1 : term6 A _17534) : (term0 A _17534) = (term0 A _17534).
Proof. exact (prop_ext (fun h2 : term0 A _17534 => @lem1073424 A _17534 h2) (fun h2 : term0 A _17534 => @lem1073426 A _17534 h1)). Qed.
Lemma lem1073431 {A : Type'} (_17534 : type1144 A) (h1 : term6 A _17534) : term0 A _17534.
Proof. exact (EQ_MP (@lem1073430 A _17534 h1) (@lem1073426 A _17534 h1)). Qed.
Lemma lem1073432 {A : Type'} (_17534 : type1144 A) (h1 : term6 A _17534) : term6 A _17534.
Proof. exact (conj (@lem1073429 A _17534 h1) (@lem1073431 A _17534 h1)). Qed.
Lemma lem1073433 {A Z : Type'} (NIL' : Z) : term7 A Z NIL'.
Proof. exact (@lem1072128 A Z NIL'). Qed.
Lemma lem1073434 {A Z : Type'} (NIL' : Z) : (term7 A Z NIL') = (term8 A Z NIL').
Proof. exact (eq_refl (term7 A Z NIL')). Qed.
Lemma lem1073435 {A Z : Type'} (NIL' : Z) : term8 A Z NIL'.
Proof. exact (EQ_MP (@lem1073434 A Z NIL') (@lem1073433 A Z NIL')). Qed.
Lemma lem1073436 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term9 A Z NIL' CONS'.
Proof. exact (@lem1073435 A Z NIL' CONS'). Qed.
Lemma lem1073437 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : (term9 A Z NIL' CONS') = (term10 A Z NIL' CONS').
Proof. exact (eq_refl (term9 A Z NIL' CONS')). Qed.
Lemma lem1073438 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term10 A Z NIL' CONS'.
Proof. exact (EQ_MP (@lem1073437 A Z NIL' CONS') (@lem1073436 A Z NIL' CONS')). Qed.
Lemma lem1073439 {A : Type'} (NIL' : nat) (CONS' : type1396 A) : term11 A NIL' CONS'.
Proof. exact (@lem1073438 A nat NIL' CONS'). Qed.
Lemma lem1073440 {A : Type'} : term12 A.
Proof. exact (@lem1073439 A (NUMERAL 0) (term13 A)). Qed.
Lemma lem1073441 {A : Type'} (a0 : A) : (term14 A a0) = (term15 A).
Proof. exact (eq_refl (term14 A a0)). Qed.
Lemma lem1073442 {A : Type'} (a1 : list A) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1073443 {A : Type'} (a0 : A) (a1 : list A) : (term16 A a0 a1) = (term17 A a1).
Proof. exact (MK_COMB (@lem1073441 A a0) (@lem1073442 A a1)). Qed.
Lemma lem1073444 {A : Type'} (a1 : list A) : (term17 A a1) = term18.
Proof. exact (eq_refl (term17 A a1)). Qed.
Lemma lem1073445 {A : Type'} (a0 : A) (a1 : list A) : (term16 A a0 a1) = term18.
Proof. exact (TRANS (@lem1073443 A a0 a1) (@lem1073444 A a1)). Qed.
Lemma lem1073446 {A : Type'} (fn : type1144 A) (a1 : list A) : (fn a1) = (fn a1).
Proof. exact (eq_refl (fn a1)). Qed.
Lemma lem1073447 {A : Type'} (a0 : A) (fn : type1144 A) (a1 : list A) : (term19 A a0 fn a1) = (term20 A fn a1).
Proof. exact (MK_COMB (@lem1073445 A a0 a1) (@lem1073446 A fn a1)). Qed.
Lemma lem1073448 {A : Type'} (fn : type1144 A) (a1 : list A) : (term20 A fn a1) = term5.
Proof. exact (eq_refl (term20 A fn a1)). Qed.
Lemma lem1073449 {A : Type'} (a0 : A) (fn : type1144 A) (a1 : list A) : (term19 A a0 fn a1) = term5.
Proof. exact (TRANS (@lem1073447 A a0 fn a1) (@lem1073448 A fn a1)). Qed.
Lemma lem1073450 {A : Type'} (fn : type1144 A) (a0 : A) (a1 : list A) : (term21 A fn a0 a1) = (term21 A fn a0 a1).
Proof. exact (eq_refl (term21 A fn a0 a1)). Qed.
Lemma lem1073451 {A : Type'} (fn : type1144 A) (a0 : A) (a1 : list A) : ((term4 A fn a0 a1) = (term19 A a0 fn a1)) = ((term4 A fn a0 a1) = term5).
Proof. exact (MK_COMB (@lem1073450 A fn a0 a1) (@lem1073449 A a0 fn a1)). Qed.
Lemma lem1073452 {A : Type'} (fn : type1144 A) (a0 : A) : (term22 A a0 fn) = (term23 A fn a0).
Proof. exact (fun_ext (fun a1 : list A => @lem1073451 A fn a0 a1)). Qed.
Lemma lem1073453 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1073454 {A : Type'} (fn : type1144 A) (a0 : A) : (term24 A a0 fn) = (term2 A fn a0).
Proof. exact (MK_COMB (@lem1073453 A) (@lem1073452 A fn a0)). Qed.
Lemma lem1073455 {A : Type'} (fn : type1144 A) : (term25 A fn) = (term26 A fn).
Proof. exact (fun_ext (fun a0 : A => @lem1073454 A fn a0)). Qed.
Lemma lem1073456 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1073457 {A : Type'} (fn : type1144 A) : (term27 A fn) = (term0 A fn).
Proof. exact (MK_COMB (@lem1073456 A) (@lem1073455 A fn)). Qed.
Lemma lem1073458 {A : Type'} (fn : type1144 A) : (term28 A fn) = (term28 A fn).
Proof. exact (eq_refl (term28 A fn)). Qed.
Lemma lem1073459 {A : Type'} (fn : type1144 A) : (term29 A fn) = (term6 A fn).
Proof. exact (MK_COMB (@lem1073458 A fn) (@lem1073457 A fn)). Qed.
Lemma lem1073460 {A : Type'} : (term30 A) = (term31 A).
Proof. exact (fun_ext (fun fn : type1144 A => @lem1073459 A fn)). Qed.
Lemma lem1073461 {A : Type'} : (@ex ((list A) -> nat)) = (@ex ((list A) -> nat)).
Proof. exact (eq_refl (@ex ((list A) -> nat))). Qed.
Lemma lem1073462 {A : Type'} : (term12 A) = (term32 A).
Proof. exact (MK_COMB (@lem1073461 A) (@lem1073460 A)). Qed.
Lemma lem1073463 {A : Type'} : term32 A.
Proof. exact (EQ_MP (@lem1073462 A) (@lem1073440 A)). Qed.
Lemma lem1073464 {A : Type'} (_17534 : type1144 A) (h1 : term6 A _17534) : term6 A _17534.
Proof. exact (h1). Qed.
Lemma lem1073465 {A : Type'} (_17534 : type1144 A) (h1 : term6 A _17534) : term0 A _17534.
Proof. exact (proj2 (@lem1073464 A _17534 h1)). Qed.
Lemma lem1073466 {A : Type'} (_17534 : type1144 A) (h1 : term6 A _17534) : (_17534 (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1073464 A _17534 h1)). Qed.
Lemma lem1073467 {A : Type'} (_17534 : type1144 A) (h1 : term6 A _17534) : term6 A _17534.
Proof. exact (conj (@lem1073466 A _17534 h1) (@lem1073465 A _17534 h1)). Qed.
Lemma lem1073468 {A : Type'} (_17534 : type1144 A) (h1 : term6 A _17534) : term32 A.
Proof. exact (ex_intro (term31 A) _17534 (@lem1073467 A _17534 h1)). Qed.
Lemma lem1073469 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem1073470 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (ex_elim (@lem1073469 A h1) (fun _17534 : type1144 A => fun h0 : term31 A _17534 => @lem1073468 A _17534 h0)). Qed.
Lemma lem1073471 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (prop_ext (fun h1 : term32 A => @lem1073470 A h1) (fun h1 : term32 A => @lem1073463 A)). Qed.
Lemma lem1073472 {A : Type'} : term32 A.
Proof. exact (EQ_MP (@lem1073471 A) (@lem1073463 A)). Qed.
Lemma lem1073473 {A : Type'} (_17534 : type1144 A) (h1 : term6 A _17534) : term32 A.
Proof. exact (ex_intro (term31 A) _17534 (@lem1073432 A _17534 h1)). Qed.
Lemma lem1073474 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem1073475 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (ex_elim (@lem1073474 A h1) (fun _17534 : type1144 A => fun h0 : term31 A _17534 => @lem1073473 A _17534 h0)). Qed.
Lemma lem1073476 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (prop_ext (fun h1 : term32 A => @lem1073475 A h1) (fun h1 : term32 A => @lem1073472 A)). Qed.
Lemma lem1073477 {A : Type'} : term32 A.
Proof. exact (EQ_MP (@lem1073476 A) (@lem1073472 A)). Qed.
Lemma lem1073480 {A : Type'} (_17534 : type1144 A) (h1 : term6 A _17534) : term6 A _17534.
Proof. exact (h1). Qed.
Lemma lem1073481 {A : Type'} (_17534 : type1144 A) (h1 : term6 A _17534) : term32 A.
Proof. exact (ex_intro (term31 A) _17534 (@lem1073480 A _17534 h1)). Qed.
Lemma lem1073482 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem1073483 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (ex_elim (@lem1073482 A h1) (fun _17534 : type1144 A => fun h0 : term31 A _17534 => @lem1073481 A _17534 h0)). Qed.
Lemma lem1073484 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (prop_ext (fun h1 : term32 A => @lem1073483 A h1) (fun h1 : term32 A => @lem1073477 A)). Qed.
Lemma lem1073485 {A : Type'} : term32 A.
Proof. exact (EQ_MP (@lem1073484 A) (@lem1073477 A)). Qed.
Lemma lem1073486 {A : Type'} (_17534 : type1144 A) (h1 : term6 A _17534) : term6 A _17534.
Proof. exact (h1). Qed.
Lemma lem1073487 {A : Type'} (_17534 : type1144 A) (h1 : term6 A _17534) : term0 A _17534.
Proof. exact (proj2 (@lem1073486 A _17534 h1)). Qed.
Lemma lem1073489 {A : Type'} (a0 : A) (_17534 : type1144 A) (h1 : term6 A _17534) : term1 A _17534 a0.
Proof. exact (@lem1073487 A _17534 h1 a0). Qed.
Lemma lem1073490 {A : Type'} (_17534 : type1144 A) (a0 : A) : (term1 A _17534 a0) = (term2 A _17534 a0).
Proof. exact (eq_refl (term1 A _17534 a0)). Qed.
Lemma lem1073491 {A : Type'} (a0 : A) (_17534 : type1144 A) (h1 : term6 A _17534) : term2 A _17534 a0.
Proof. exact (EQ_MP (@lem1073490 A _17534 a0) (@lem1073489 A a0 _17534 h1)). Qed.
Lemma lem1073492 {A : Type'} (a0 : A) (a1 : list A) (_17534 : type1144 A) (h1 : term6 A _17534) : term3 A _17534 a0 a1.
Proof. exact (@lem1073491 A a0 _17534 h1 a1). Qed.
Lemma lem1073493 {A : Type'} (_17534 : type1144 A) (a0 : A) (a1 : list A) : (term3 A _17534 a0 a1) = ((term4 A _17534 a0 a1) = term5).
Proof. exact (eq_refl (term3 A _17534 a0 a1)). Qed.
Lemma lem1073495 {A : Type'} (_17534 : type1144 A) : _17534 = _17534.
Proof. exact (eq_refl _17534). Qed.
Lemma lem1073496 {A : Type'} (a0' : A) (a1' : list A) (h1 : (@nil A) = (@cons A a0' a1')) : (@nil A) = (@cons A a0' a1').
Proof. exact (h1). Qed.
Lemma lem1073497 {A : Type'} (_17534 : type1144 A) (a0' : A) (a1' : list A) (h1 : (@nil A) = (@cons A a0' a1')) : (_17534 (@nil A)) = (term4 A _17534 a0' a1').
Proof. exact (MK_COMB (@lem1073495 A _17534) (@lem1073496 A a0' a1' h1)). Qed.
Lemma lem1073499 {A : Type'} (_17534 : type1144 A) (h1 : term6 A _17534) : (_17534 (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1073486 A _17534 h1)). Qed.
Lemma lem1073500 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1073501 {A : Type'} (_17534 : type1144 A) (h1 : term6 A _17534) : (term33 A _17534) = term34.
Proof. exact (MK_COMB (@lem1073500) (@lem1073499 A _17534 h1)). Qed.
Lemma lem1073503 {A : Type'} (a0 : A) (a1 : list A) (_17534 : type1144 A) (h1 : term6 A _17534) : (term4 A _17534 a0 a1) = term5.
Proof. exact (EQ_MP (@lem1073493 A _17534 a0 a1) (@lem1073492 A a0 a1 _17534 h1)). Qed.
Lemma lem1073504 {A : Type'} (a0 : A) (a1 : list A) (_17534 : type1144 A) (h1 : term6 A _17534) : (term4 A _17534 a0 a1) = term5.
Proof. exact (@lem1073503 A a0 a1 _17534 h1). Qed.
Lemma lem1073505 {A : Type'} (a0' : A) (a1' : list A) (_17534 : type1144 A) (h1 : term6 A _17534) : (term4 A _17534 a0' a1') = term5.
Proof. exact (@lem1073504 A a0' a1' _17534 h1). Qed.
Lemma lem1073506 {A : Type'} (a0' : A) (a1' : list A) (_17534 : type1144 A) (h1 : term6 A _17534) : ((_17534 (@nil A)) = (term4 A _17534 a0' a1')) = ((NUMERAL 0) = term5).
Proof. exact (MK_COMB (@lem1073501 A _17534 h1) (@lem1073505 A a0' a1' _17534 h1)). Qed.
Lemma lem1073507 {A : Type'} (_17534 : type1144 A) (a0' : A) (a1' : list A) (h1 : term6 A _17534) (h2 : (@nil A) = (@cons A a0' a1')) : (NUMERAL 0) = term5.
Proof. exact (EQ_MP (@lem1073506 A a0' a1' _17534 h1) (@lem1073497 A _17534 a0' a1' h2)). Qed.
Lemma lem1073508 : term35 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1073509 (h1 : term35 = (BIT1 0)) : ((NUMERAL 0) = term5) = False.
Proof. exact (@lem1012671 0 0 (BIT1 0) h1). Qed.
Lemma lem1073510 : (term35 = (BIT1 0)) = (((NUMERAL 0) = term5) = False).
Proof. exact (prop_ext (fun h1 : term35 = (BIT1 0) => @lem1073509 h1) (fun h1 : ((NUMERAL 0) = term5) = False => @lem1073508)). Qed.
Lemma lem1073511 : ((NUMERAL 0) = term5) = False.
Proof. exact (EQ_MP (@lem1073510) (@lem1073508)). Qed.
Lemma lem1073512 {A : Type'} (_17534 : type1144 A) (a0' : A) (a1' : list A) (h1 : term6 A _17534) (h2 : (@nil A) = (@cons A a0' a1')) : False.
Proof. exact (EQ_MP (@lem1073511) (@lem1073507 A _17534 a0' a1' h1 h2)). Qed.
Lemma lem1073513 {A : Type'} (a0' : A) (a1' : list A) (_17534 : type1144 A) (h1 : term6 A _17534) : term36 A a0' a1'.
Proof. exact (fun h0 : (@nil A) = (@cons A a0' a1') => @lem1073512 A _17534 a0' a1' h1 h0). Qed.
Lemma lem1073515 (a : Prop) : (a -> False) = (~ a).
Proof. exact (EQ_MP (@lem1073392 a) (@lem0)). Qed.
Lemma lem1073516 {A : Type'} (a0' : A) (a1' : list A) : (term36 A a0' a1') = (term37 A a0' a1').
Proof. exact (@lem1073515 ((@nil A) = (@cons A a0' a1'))). Qed.
Lemma lem1073517 {A : Type'} (a0' : A) (a1' : list A) (_17534 : type1144 A) (h1 : term6 A _17534) : term37 A a0' a1'.
Proof. exact (EQ_MP (@lem1073516 A a0' a1') (@lem1073513 A a0' a1' _17534 h1)). Qed.
Lemma lem1073518 {A : Type'} (a0' : A) (_17534 : type1144 A) (h1 : term6 A _17534) : term38 A a0'.
Proof. exact (fun a1' : list A => @lem1073517 A a0' a1' _17534 h1). Qed.
Lemma lem1073519 {A : Type'} (_17534 : type1144 A) (h1 : term6 A _17534) : term39 A.
Proof. exact (fun a0' : A => @lem1073518 A a0' _17534 h1). Qed.
Lemma lem1073520 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem1073521 {A : Type'} (h1 : term32 A) : term39 A.
Proof. exact (ex_elim (@lem1073520 A h1) (fun _17534 : type1144 A => fun h0 : term31 A _17534 => @lem1073519 A _17534 h0)). Qed.
Lemma lem1073522 {A : Type'} : (term32 A) = (term39 A).
Proof. exact (prop_ext (fun h1 : term32 A => @lem1073521 A h1) (fun h1 : term39 A => @lem1073485 A)). Qed.
Lemma lem1073523 {A : Type'} : term39 A.
Proof. exact (EQ_MP (@lem1073522 A) (@lem1073485 A)). Qed.
