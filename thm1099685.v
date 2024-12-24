Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1099685_term_abbrevs.
Require Import SKOLEM_THM_spec.
Require Import list_RECURSION_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1099572 {_25287 : Type'} (NULL' : type1143 _25287) (h1 : (NULL' (@nil _25287)) = True) : (NULL' (@nil _25287)) = True.
Proof. exact (h1). Qed.
Lemma lem1099573 {_25287 : Type'} (NULL' : type1143 _25287) (h1 : term0 _25287 NULL') : term0 _25287 NULL'.
Proof. exact (h1). Qed.
Lemma lem1099574 {_25287 : Type'} (h : _25287) (NULL' : type1143 _25287) (h1 : term0 _25287 NULL') : term1 _25287 NULL' h.
Proof. exact (@lem1099573 _25287 NULL' h1 h). Qed.
Lemma lem1099575 {_25287 : Type'} (NULL' : type1143 _25287) (h : _25287) : (term1 _25287 NULL' h) = (term2 _25287 NULL' h).
Proof. exact (eq_refl (term1 _25287 NULL' h)). Qed.
Lemma lem1099576 {_25287 : Type'} (h : _25287) (NULL' : type1143 _25287) (h1 : term0 _25287 NULL') : term2 _25287 NULL' h.
Proof. exact (EQ_MP (@lem1099575 _25287 NULL' h) (@lem1099574 _25287 h NULL' h1)). Qed.
Lemma lem1099577 {_25287 : Type'} (h : _25287) (t : list _25287) (NULL' : type1143 _25287) (h1 : term0 _25287 NULL') : term3 _25287 NULL' h t.
Proof. exact (@lem1099576 _25287 h NULL' h1 t). Qed.
Lemma lem1099578 {_25287 : Type'} (NULL' : type1143 _25287) (h : _25287) (t : list _25287) : (term3 _25287 NULL' h t) = ((term4 _25287 NULL' h t) = False).
Proof. exact (eq_refl (term3 _25287 NULL' h t)). Qed.
Lemma lem1099579 {_25287 : Type'} (h : _25287) (t : list _25287) (NULL' : type1143 _25287) (h1 : term0 _25287 NULL') : (term4 _25287 NULL' h t) = False.
Proof. exact (EQ_MP (@lem1099578 _25287 NULL' h t) (@lem1099577 _25287 h t NULL' h1)). Qed.
Lemma lem1099580 {_25287 : Type'} (h : _25287) (NULL' : type1143 _25287) (h1 : term0 _25287 NULL') : term2 _25287 NULL' h.
Proof. exact (fun t : list _25287 => @lem1099579 _25287 h t NULL' h1). Qed.
Lemma lem1099581 {_25287 : Type'} (NULL' : type1143 _25287) (h1 : term0 _25287 NULL') : term0 _25287 NULL'.
Proof. exact (fun h : _25287 => @lem1099580 _25287 h NULL' h1). Qed.
Lemma lem1099582 {_25287 : Type'} (NULL' : type1143 _25287) (h1 : term5 _25287 NULL') : term5 _25287 NULL'.
Proof. exact (h1). Qed.
Lemma lem1099583 {_25287 : Type'} (NULL' : type1143 _25287) (h1 : term5 _25287 NULL') : term0 _25287 NULL'.
Proof. exact (proj2 (@lem1099582 _25287 NULL' h1)). Qed.
Lemma lem1099584 {_25287 : Type'} (NULL' : type1143 _25287) (h1 : term5 _25287 NULL') : (NULL' (@nil _25287)) = True.
Proof. exact (proj1 (@lem1099582 _25287 NULL' h1)). Qed.
Lemma lem1099585 {_25287 : Type'} (NULL' : type1143 _25287) (h1 : term5 _25287 NULL') : ((NULL' (@nil _25287)) = True) = ((NULL' (@nil _25287)) = True).
Proof. exact (prop_ext (fun h2 : (NULL' (@nil _25287)) = True => @lem1099572 _25287 NULL' h2) (fun h2 : (NULL' (@nil _25287)) = True => @lem1099584 _25287 NULL' h1)). Qed.
Lemma lem1099586 {_25287 : Type'} (NULL' : type1143 _25287) (h1 : term5 _25287 NULL') : (NULL' (@nil _25287)) = True.
Proof. exact (EQ_MP (@lem1099585 _25287 NULL' h1) (@lem1099584 _25287 NULL' h1)). Qed.
Lemma lem1099587 {_25287 : Type'} (NULL' : type1143 _25287) (h1 : term5 _25287 NULL') : (term0 _25287 NULL') = (term0 _25287 NULL').
Proof. exact (prop_ext (fun h2 : term0 _25287 NULL' => @lem1099581 _25287 NULL' h2) (fun h2 : term0 _25287 NULL' => @lem1099583 _25287 NULL' h1)). Qed.
Lemma lem1099588 {_25287 : Type'} (NULL' : type1143 _25287) (h1 : term5 _25287 NULL') : term0 _25287 NULL'.
Proof. exact (EQ_MP (@lem1099587 _25287 NULL' h1) (@lem1099583 _25287 NULL' h1)). Qed.
Lemma lem1099589 {_25287 : Type'} (NULL' : type1143 _25287) (h1 : term5 _25287 NULL') : term5 _25287 NULL'.
Proof. exact (conj (@lem1099586 _25287 NULL' h1) (@lem1099588 _25287 NULL' h1)). Qed.
Lemma lem1099590 {A Z : Type'} (NIL' : Z) : term6 A Z NIL'.
Proof. exact (@lem1072128 A Z NIL'). Qed.
Lemma lem1099591 {A Z : Type'} (NIL' : Z) : (term6 A Z NIL') = (term7 A Z NIL').
Proof. exact (eq_refl (term6 A Z NIL')). Qed.
Lemma lem1099592 {A Z : Type'} (NIL' : Z) : term7 A Z NIL'.
Proof. exact (EQ_MP (@lem1099591 A Z NIL') (@lem1099590 A Z NIL')). Qed.
Lemma lem1099593 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term8 A Z NIL' CONS'.
Proof. exact (@lem1099592 A Z NIL' CONS'). Qed.
Lemma lem1099594 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : (term8 A Z NIL' CONS') = (term9 A Z NIL' CONS').
Proof. exact (eq_refl (term8 A Z NIL' CONS')). Qed.
Lemma lem1099595 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term9 A Z NIL' CONS'.
Proof. exact (EQ_MP (@lem1099594 A Z NIL' CONS') (@lem1099593 A Z NIL' CONS')). Qed.
Lemma lem1099596 {_25287 : Type'} (NIL' : Prop) (CONS' : type1395 _25287) : term10 _25287 NIL' CONS'.
Proof. exact (@lem1099595 _25287 Prop NIL' CONS'). Qed.
Lemma lem1099597 {_25287 : Type'} : term11 _25287.
Proof. exact (@lem1099596 _25287 True (term12 _25287)). Qed.
Lemma lem1099598 {_25287 : Type'} (a0 : _25287) : (term13 _25287 a0) = (term14 _25287).
Proof. exact (eq_refl (term13 _25287 a0)). Qed.
Lemma lem1099599 {_25287 : Type'} (a1 : list _25287) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1099600 {_25287 : Type'} (a0 : _25287) (a1 : list _25287) : (term15 _25287 a0 a1) = (term16 _25287 a1).
Proof. exact (MK_COMB (@lem1099598 _25287 a0) (@lem1099599 _25287 a1)). Qed.
Lemma lem1099601 {_25287 : Type'} (a1 : list _25287) : (term16 _25287 a1) = term17.
Proof. exact (eq_refl (term16 _25287 a1)). Qed.
Lemma lem1099602 {_25287 : Type'} (a0 : _25287) (a1 : list _25287) : (term15 _25287 a0 a1) = term17.
Proof. exact (TRANS (@lem1099600 _25287 a0 a1) (@lem1099601 _25287 a1)). Qed.
Lemma lem1099603 {_25287 : Type'} (fn : type1143 _25287) (a1 : list _25287) : (fn a1) = (fn a1).
Proof. exact (eq_refl (fn a1)). Qed.
Lemma lem1099604 {_25287 : Type'} (a0 : _25287) (fn : type1143 _25287) (a1 : list _25287) : (term18 _25287 a0 fn a1) = (term19 _25287 fn a1).
Proof. exact (MK_COMB (@lem1099602 _25287 a0 a1) (@lem1099603 _25287 fn a1)). Qed.
Lemma lem1099605 {_25287 : Type'} (fn : type1143 _25287) (a1 : list _25287) : (term19 _25287 fn a1) = False.
Proof. exact (eq_refl (term19 _25287 fn a1)). Qed.
Lemma lem1099606 {_25287 : Type'} (a0 : _25287) (fn : type1143 _25287) (a1 : list _25287) : (term18 _25287 a0 fn a1) = False.
Proof. exact (TRANS (@lem1099604 _25287 a0 fn a1) (@lem1099605 _25287 fn a1)). Qed.
Lemma lem1099607 {_25287 : Type'} (fn : type1143 _25287) (a0 : _25287) (a1 : list _25287) : (term20 _25287 fn a0 a1) = (term20 _25287 fn a0 a1).
Proof. exact (eq_refl (term20 _25287 fn a0 a1)). Qed.
Lemma lem1099608 {_25287 : Type'} (fn : type1143 _25287) (a0 : _25287) (a1 : list _25287) : ((term4 _25287 fn a0 a1) = (term18 _25287 a0 fn a1)) = ((term4 _25287 fn a0 a1) = False).
Proof. exact (MK_COMB (@lem1099607 _25287 fn a0 a1) (@lem1099606 _25287 a0 fn a1)). Qed.
Lemma lem1099609 {_25287 : Type'} (fn : type1143 _25287) (a0 : _25287) : (term21 _25287 a0 fn) = (term22 _25287 fn a0).
Proof. exact (fun_ext (fun a1 : list _25287 => @lem1099608 _25287 fn a0 a1)). Qed.
Lemma lem1099610 {_25287 : Type'} : (@all (list _25287)) = (@all (list _25287)).
Proof. exact (eq_refl (@all (list _25287))). Qed.
Lemma lem1099611 {_25287 : Type'} (fn : type1143 _25287) (a0 : _25287) : (term23 _25287 a0 fn) = (term2 _25287 fn a0).
Proof. exact (MK_COMB (@lem1099610 _25287) (@lem1099609 _25287 fn a0)). Qed.
Lemma lem1099612 {_25287 : Type'} (fn : type1143 _25287) : (term24 _25287 fn) = (term25 _25287 fn).
Proof. exact (fun_ext (fun a0 : _25287 => @lem1099611 _25287 fn a0)). Qed.
Lemma lem1099613 {_25287 : Type'} : (@all _25287) = (@all _25287).
Proof. exact (eq_refl (@all _25287)). Qed.
Lemma lem1099614 {_25287 : Type'} (fn : type1143 _25287) : (term26 _25287 fn) = (term0 _25287 fn).
Proof. exact (MK_COMB (@lem1099613 _25287) (@lem1099612 _25287 fn)). Qed.
Lemma lem1099615 {_25287 : Type'} (fn : type1143 _25287) : (term27 _25287 fn) = (term27 _25287 fn).
Proof. exact (eq_refl (term27 _25287 fn)). Qed.
Lemma lem1099616 {_25287 : Type'} (fn : type1143 _25287) : (term28 _25287 fn) = (term5 _25287 fn).
Proof. exact (MK_COMB (@lem1099615 _25287 fn) (@lem1099614 _25287 fn)). Qed.
Lemma lem1099617 {_25287 : Type'} : (term29 _25287) = (term30 _25287).
Proof. exact (fun_ext (fun fn : type1143 _25287 => @lem1099616 _25287 fn)). Qed.
Lemma lem1099618 {_25287 : Type'} : (@ex ((list _25287) -> Prop)) = (@ex ((list _25287) -> Prop)).
Proof. exact (eq_refl (@ex ((list _25287) -> Prop))). Qed.
Lemma lem1099619 {_25287 : Type'} : (term11 _25287) = (term31 _25287).
Proof. exact (MK_COMB (@lem1099618 _25287) (@lem1099617 _25287)). Qed.
Lemma lem1099620 {_25287 : Type'} : term31 _25287.
Proof. exact (EQ_MP (@lem1099619 _25287) (@lem1099597 _25287)). Qed.
Lemma lem1099621 {_25287 : Type'} (NULL' : type1143 _25287) (h1 : term5 _25287 NULL') : term5 _25287 NULL'.
Proof. exact (h1). Qed.
Lemma lem1099622 {_25287 : Type'} (NULL' : type1143 _25287) (h1 : term5 _25287 NULL') : term0 _25287 NULL'.
Proof. exact (proj2 (@lem1099621 _25287 NULL' h1)). Qed.
Lemma lem1099623 {_25287 : Type'} (NULL' : type1143 _25287) (h1 : term5 _25287 NULL') : (NULL' (@nil _25287)) = True.
Proof. exact (proj1 (@lem1099621 _25287 NULL' h1)). Qed.
Lemma lem1099624 {_25287 : Type'} (NULL' : type1143 _25287) (h1 : term5 _25287 NULL') : term5 _25287 NULL'.
Proof. exact (conj (@lem1099623 _25287 NULL' h1) (@lem1099622 _25287 NULL' h1)). Qed.
Lemma lem1099625 {_25287 : Type'} (NULL' : type1143 _25287) (h1 : term5 _25287 NULL') : term31 _25287.
Proof. exact (ex_intro (term30 _25287) NULL' (@lem1099624 _25287 NULL' h1)). Qed.
Lemma lem1099626 {_25287 : Type'} (h1 : term31 _25287) : term31 _25287.
Proof. exact (h1). Qed.
Lemma lem1099627 {_25287 : Type'} (h1 : term31 _25287) : term31 _25287.
Proof. exact (ex_elim (@lem1099626 _25287 h1) (fun NULL' : type1143 _25287 => fun h0 : term30 _25287 NULL' => @lem1099625 _25287 NULL' h0)). Qed.
Lemma lem1099628 {_25287 : Type'} : (term31 _25287) = (term31 _25287).
Proof. exact (prop_ext (fun h1 : term31 _25287 => @lem1099627 _25287 h1) (fun h1 : term31 _25287 => @lem1099620 _25287)). Qed.
Lemma lem1099629 {_25287 : Type'} : term31 _25287.
Proof. exact (EQ_MP (@lem1099628 _25287) (@lem1099620 _25287)). Qed.
Lemma lem1099630 {_25287 : Type'} (NULL' : type1143 _25287) (h1 : term5 _25287 NULL') : term31 _25287.
Proof. exact (ex_intro (term30 _25287) NULL' (@lem1099589 _25287 NULL' h1)). Qed.
Lemma lem1099631 {_25287 : Type'} (h1 : term31 _25287) : term31 _25287.
Proof. exact (h1). Qed.
Lemma lem1099632 {_25287 : Type'} (h1 : term31 _25287) : term31 _25287.
Proof. exact (ex_elim (@lem1099631 _25287 h1) (fun NULL' : type1143 _25287 => fun h0 : term30 _25287 NULL' => @lem1099630 _25287 NULL' h0)). Qed.
Lemma lem1099633 {_25287 : Type'} : (term31 _25287) = (term31 _25287).
Proof. exact (prop_ext (fun h1 : term31 _25287 => @lem1099632 _25287 h1) (fun h1 : term31 _25287 => @lem1099629 _25287)). Qed.
Lemma lem1099634 {_25287 : Type'} : term31 _25287.
Proof. exact (EQ_MP (@lem1099633 _25287) (@lem1099629 _25287)). Qed.
Lemma lem1099637 {_25287 : Type'} (NULL' : type1143 _25287) (h1 : term5 _25287 NULL') : term5 _25287 NULL'.
Proof. exact (h1). Qed.
Lemma lem1099638 {_25287 : Type'} (NULL' : type1143 _25287) (h1 : term5 _25287 NULL') : term31 _25287.
Proof. exact (ex_intro (term30 _25287) NULL' (@lem1099637 _25287 NULL' h1)). Qed.
Lemma lem1099639 {_25287 : Type'} (h1 : term31 _25287) : term31 _25287.
Proof. exact (h1). Qed.
Lemma lem1099640 {_25287 : Type'} (h1 : term31 _25287) : term31 _25287.
Proof. exact (ex_elim (@lem1099639 _25287 h1) (fun NULL' : type1143 _25287 => fun h0 : term30 _25287 NULL' => @lem1099638 _25287 NULL' h0)). Qed.
Lemma lem1099641 {_25287 : Type'} : (term31 _25287) = (term31 _25287).
Proof. exact (prop_ext (fun h1 : term31 _25287 => @lem1099640 _25287 h1) (fun h1 : term31 _25287 => @lem1099634 _25287)). Qed.
Lemma lem1099642 {_25287 : Type'} : term31 _25287.
Proof. exact (EQ_MP (@lem1099641 _25287) (@lem1099634 _25287)). Qed.
Lemma lem1099643 {_25287 : Type'} : term32 _25287.
Proof. exact (fun _17966 : type1673 => @lem1099642 _25287). Qed.
Lemma lem1099644 {A B : Type'} (P : type1413 A B) : term33 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1099645 {A B : Type'} (P : type1413 A B) : (term33 A B P) = ((term34 A B P) = (term35 A B P)).
Proof. exact (eq_refl (term33 A B P)). Qed.
Lemma lem1099648 {A B : Type'} (P : type1413 A B) : (term34 A B P) = (term35 A B P).
Proof. exact (EQ_MP (@lem1099645 A B P) (@lem1099644 A B P)). Qed.
Lemma lem1099649 {_25287 : Type'} (P : type1284 _25287) : (term36 _25287 P) = (term37 _25287 P).
Proof. exact (@lem1099648 type1673 (type1143 _25287) P). Qed.
Lemma lem1099650 {_25287 : Type'} : (term38 _25287) = (term39 _25287).
Proof. exact (@lem1099649 _25287 (term40 _25287)). Qed.
Lemma lem1099651 {_25287 : Type'} (_17966 : type1673) : (term41 _25287 _17966) = (term30 _25287).
Proof. exact (eq_refl (term41 _25287 _17966)). Qed.
Lemma lem1099652 {_25287 : Type'} (NULL' : type1143 _25287) : NULL' = NULL'.
Proof. exact (eq_refl NULL'). Qed.
Lemma lem1099653 {_25287 : Type'} (_17966 : type1673) (NULL' : type1143 _25287) : (term42 _25287 _17966 NULL') = (term43 _25287 NULL').
Proof. exact (MK_COMB (@lem1099651 _25287 _17966) (@lem1099652 _25287 NULL')). Qed.
Lemma lem1099654 {_25287 : Type'} (NULL' : type1143 _25287) : (term43 _25287 NULL') = (term5 _25287 NULL').
Proof. exact (eq_refl (term43 _25287 NULL')). Qed.
Lemma lem1099655 {_25287 : Type'} (_17966 : type1673) (NULL' : type1143 _25287) : (term42 _25287 _17966 NULL') = (term5 _25287 NULL').
Proof. exact (TRANS (@lem1099653 _25287 _17966 NULL') (@lem1099654 _25287 NULL')). Qed.
Lemma lem1099656 {_25287 : Type'} (_17966 : type1673) : (term44 _25287 _17966) = (term30 _25287).
Proof. exact (fun_ext (fun NULL' : type1143 _25287 => @lem1099655 _25287 _17966 NULL')). Qed.
Lemma lem1099657 {_25287 : Type'} : (@ex ((list _25287) -> Prop)) = (@ex ((list _25287) -> Prop)).
Proof. exact (eq_refl (@ex ((list _25287) -> Prop))). Qed.
Lemma lem1099658 {_25287 : Type'} (_17966 : type1673) : (term45 _25287 _17966) = (term31 _25287).
Proof. exact (MK_COMB (@lem1099657 _25287) (@lem1099656 _25287 _17966)). Qed.
Lemma lem1099659 {_25287 : Type'} : (term46 _25287) = (term47 _25287).
Proof. exact (fun_ext (fun _17966 : type1673 => @lem1099658 _25287 _17966)). Qed.
Lemma lem1099660 : (@all (prod nat (prod nat (prod nat nat)))) = (@all (prod nat (prod nat (prod nat nat)))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat nat))))). Qed.
Lemma lem1099661 {_25287 : Type'} : (term38 _25287) = (term32 _25287).
Proof. exact (MK_COMB (@lem1099660) (@lem1099659 _25287)). Qed.
Lemma lem1099662 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1099663 {_25287 : Type'} : (term48 _25287) = (term49 _25287).
Proof. exact (MK_COMB (@lem1099662) (@lem1099661 _25287)). Qed.
Lemma lem1099664 {_25287 : Type'} (_17966 : type1673) : (term41 _25287 _17966) = (term30 _25287).
Proof. exact (eq_refl (term41 _25287 _17966)). Qed.
Lemma lem1099665 {_25287 : Type'} (NULL' : type1290 _25287) (_17966 : type1673) : (NULL' _17966) = (NULL' _17966).
Proof. exact (eq_refl (NULL' _17966)). Qed.
Lemma lem1099666 {_25287 : Type'} (NULL' : type1290 _25287) (_17966 : type1673) : (term50 _25287 NULL' _17966) = (term51 _25287 NULL' _17966).
Proof. exact (MK_COMB (@lem1099664 _25287 _17966) (@lem1099665 _25287 NULL' _17966)). Qed.
Lemma lem1099667 {_25287 : Type'} (NULL' : type1290 _25287) (_17966 : type1673) : (term51 _25287 NULL' _17966) = (term52 _25287 NULL' _17966).
Proof. exact (eq_refl (term51 _25287 NULL' _17966)). Qed.
Lemma lem1099668 {_25287 : Type'} (NULL' : type1290 _25287) (_17966 : type1673) : (term50 _25287 NULL' _17966) = (term52 _25287 NULL' _17966).
Proof. exact (TRANS (@lem1099666 _25287 NULL' _17966) (@lem1099667 _25287 NULL' _17966)). Qed.
Lemma lem1099669 {_25287 : Type'} (NULL' : type1290 _25287) : (term53 _25287 NULL') = (term54 _25287 NULL').
Proof. exact (fun_ext (fun _17966 : type1673 => @lem1099668 _25287 NULL' _17966)). Qed.
Lemma lem1099670 : (@all (prod nat (prod nat (prod nat nat)))) = (@all (prod nat (prod nat (prod nat nat)))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat nat))))). Qed.
Lemma lem1099671 {_25287 : Type'} (NULL' : type1290 _25287) : (term55 _25287 NULL') = (term56 _25287 NULL').
Proof. exact (MK_COMB (@lem1099670) (@lem1099669 _25287 NULL')). Qed.
Lemma lem1099672 {_25287 : Type'} : (term57 _25287) = (term58 _25287).
Proof. exact (fun_ext (fun NULL' : type1290 _25287 => @lem1099671 _25287 NULL')). Qed.
Lemma lem1099673 {_25287 : Type'} : (@ex ((prod nat (prod nat (prod nat nat))) -> (list _25287) -> Prop)) = (@ex ((prod nat (prod nat (prod nat nat))) -> (list _25287) -> Prop)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat (prod nat nat))) -> (list _25287) -> Prop))). Qed.
Lemma lem1099674 {_25287 : Type'} : (term39 _25287) = (term59 _25287).
Proof. exact (MK_COMB (@lem1099673 _25287) (@lem1099672 _25287)). Qed.
Lemma lem1099675 {_25287 : Type'} : ((term38 _25287) = (term39 _25287)) = ((term32 _25287) = (term59 _25287)).
Proof. exact (MK_COMB (@lem1099663 _25287) (@lem1099674 _25287)). Qed.
Lemma lem1099676 {_25287 : Type'} : (term32 _25287) = (term59 _25287).
Proof. exact (EQ_MP (@lem1099675 _25287) (@lem1099650 _25287)). Qed.
Lemma lem1099677 {_25287 : Type'} : term59 _25287.
Proof. exact (EQ_MP (@lem1099676 _25287) (@lem1099643 _25287)). Qed.
Lemma lem1099679 {A : Type'} : (@ex A) = (term60 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1099680 {_25287 : Type'} : (@ex ((prod nat (prod nat (prod nat nat))) -> (list _25287) -> Prop)) = (term61 _25287).
Proof. exact (@lem1099679 (type1290 _25287)). Qed.
Lemma lem1099681 {_25287 : Type'} : (term58 _25287) = (term58 _25287).
Proof. exact (eq_refl (term58 _25287)). Qed.
Lemma lem1099682 {_25287 : Type'} : (term59 _25287) = (term62 _25287).
Proof. exact (MK_COMB (@lem1099680 _25287) (@lem1099681 _25287)). Qed.
Lemma lem1099683 {_25287 : Type'} : (term62 _25287) = (term63 _25287).
Proof. exact (eq_refl (term62 _25287)). Qed.
Lemma lem1099684 {_25287 : Type'} : (term59 _25287) = (term63 _25287).
Proof. exact (TRANS (@lem1099682 _25287) (@lem1099683 _25287)). Qed.
Lemma lem1099685 {_25287 : Type'} : term63 _25287.
Proof. exact (EQ_MP (@lem1099684 _25287) (@lem1099677 _25287)). Qed.
