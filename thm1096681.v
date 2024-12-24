Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1096681_term_abbrevs.
Require Import SKOLEM_THM_spec.
Require Import list_RECURSION_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1096568 {A : Type'} (LENGTH' : type1144 A) (h1 : (LENGTH' (@nil A)) = (NUMERAL 0)) : (LENGTH' (@nil A)) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1096569 {A : Type'} (LENGTH' : type1144 A) (h1 : term0 A LENGTH') : term0 A LENGTH'.
Proof. exact (h1). Qed.
Lemma lem1096570 {A : Type'} (h : A) (LENGTH' : type1144 A) (h1 : term0 A LENGTH') : term1 A LENGTH' h.
Proof. exact (@lem1096569 A LENGTH' h1 h). Qed.
Lemma lem1096571 {A : Type'} (h : A) (LENGTH' : type1144 A) : (term1 A LENGTH' h) = (term2 A h LENGTH').
Proof. exact (eq_refl (term1 A LENGTH' h)). Qed.
Lemma lem1096572 {A : Type'} (h : A) (LENGTH' : type1144 A) (h1 : term0 A LENGTH') : term2 A h LENGTH'.
Proof. exact (EQ_MP (@lem1096571 A h LENGTH') (@lem1096570 A h LENGTH' h1)). Qed.
Lemma lem1096573 {A : Type'} (h : A) (t : list A) (LENGTH' : type1144 A) (h1 : term0 A LENGTH') : term3 A h LENGTH' t.
Proof. exact (@lem1096572 A h LENGTH' h1 t). Qed.
Lemma lem1096574 {A : Type'} (h : A) (LENGTH' : type1144 A) (t : list A) : (term3 A h LENGTH' t) = ((term4 A LENGTH' h t) = (term5 A LENGTH' t)).
Proof. exact (eq_refl (term3 A h LENGTH' t)). Qed.
Lemma lem1096575 {A : Type'} (h : A) (t : list A) (LENGTH' : type1144 A) (h1 : term0 A LENGTH') : (term4 A LENGTH' h t) = (term5 A LENGTH' t).
Proof. exact (EQ_MP (@lem1096574 A h LENGTH' t) (@lem1096573 A h t LENGTH' h1)). Qed.
Lemma lem1096576 {A : Type'} (h : A) (LENGTH' : type1144 A) (h1 : term0 A LENGTH') : term2 A h LENGTH'.
Proof. exact (fun t : list A => @lem1096575 A h t LENGTH' h1). Qed.
Lemma lem1096577 {A : Type'} (LENGTH' : type1144 A) (h1 : term0 A LENGTH') : term0 A LENGTH'.
Proof. exact (fun h : A => @lem1096576 A h LENGTH' h1). Qed.
Lemma lem1096578 {A : Type'} (LENGTH' : type1144 A) (h1 : term6 A LENGTH') : term6 A LENGTH'.
Proof. exact (h1). Qed.
Lemma lem1096579 {A : Type'} (LENGTH' : type1144 A) (h1 : term6 A LENGTH') : term0 A LENGTH'.
Proof. exact (proj2 (@lem1096578 A LENGTH' h1)). Qed.
Lemma lem1096580 {A : Type'} (LENGTH' : type1144 A) (h1 : term6 A LENGTH') : (LENGTH' (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1096578 A LENGTH' h1)). Qed.
Lemma lem1096581 {A : Type'} (LENGTH' : type1144 A) (h1 : term6 A LENGTH') : ((LENGTH' (@nil A)) = (NUMERAL 0)) = ((LENGTH' (@nil A)) = (NUMERAL 0)).
Proof. exact (prop_ext (fun h2 : (LENGTH' (@nil A)) = (NUMERAL 0) => @lem1096568 A LENGTH' h2) (fun h2 : (LENGTH' (@nil A)) = (NUMERAL 0) => @lem1096580 A LENGTH' h1)). Qed.
Lemma lem1096582 {A : Type'} (LENGTH' : type1144 A) (h1 : term6 A LENGTH') : (LENGTH' (@nil A)) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1096581 A LENGTH' h1) (@lem1096580 A LENGTH' h1)). Qed.
Lemma lem1096583 {A : Type'} (LENGTH' : type1144 A) (h1 : term6 A LENGTH') : (term0 A LENGTH') = (term0 A LENGTH').
Proof. exact (prop_ext (fun h2 : term0 A LENGTH' => @lem1096577 A LENGTH' h2) (fun h2 : term0 A LENGTH' => @lem1096579 A LENGTH' h1)). Qed.
Lemma lem1096584 {A : Type'} (LENGTH' : type1144 A) (h1 : term6 A LENGTH') : term0 A LENGTH'.
Proof. exact (EQ_MP (@lem1096583 A LENGTH' h1) (@lem1096579 A LENGTH' h1)). Qed.
Lemma lem1096585 {A : Type'} (LENGTH' : type1144 A) (h1 : term6 A LENGTH') : term6 A LENGTH'.
Proof. exact (conj (@lem1096582 A LENGTH' h1) (@lem1096584 A LENGTH' h1)). Qed.
Lemma lem1096586 {A Z : Type'} (NIL' : Z) : term7 A Z NIL'.
Proof. exact (@lem1072128 A Z NIL'). Qed.
Lemma lem1096587 {A Z : Type'} (NIL' : Z) : (term7 A Z NIL') = (term8 A Z NIL').
Proof. exact (eq_refl (term7 A Z NIL')). Qed.
Lemma lem1096588 {A Z : Type'} (NIL' : Z) : term8 A Z NIL'.
Proof. exact (EQ_MP (@lem1096587 A Z NIL') (@lem1096586 A Z NIL')). Qed.
Lemma lem1096589 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term9 A Z NIL' CONS'.
Proof. exact (@lem1096588 A Z NIL' CONS'). Qed.
Lemma lem1096590 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : (term9 A Z NIL' CONS') = (term10 A Z NIL' CONS').
Proof. exact (eq_refl (term9 A Z NIL' CONS')). Qed.
Lemma lem1096591 {A Z : Type'} (NIL' : Z) (CONS' : type1394 A Z) : term10 A Z NIL' CONS'.
Proof. exact (EQ_MP (@lem1096590 A Z NIL' CONS') (@lem1096589 A Z NIL' CONS')). Qed.
Lemma lem1096592 {A : Type'} (NIL' : nat) (CONS' : type1396 A) : term11 A NIL' CONS'.
Proof. exact (@lem1096591 A nat NIL' CONS'). Qed.
Lemma lem1096593 {A : Type'} : term12 A.
Proof. exact (@lem1096592 A (NUMERAL 0) (term13 A)). Qed.
Lemma lem1096594 {A : Type'} (a0 : A) : (term14 A a0) = (term15 A).
Proof. exact (eq_refl (term14 A a0)). Qed.
Lemma lem1096595 {A : Type'} (a1 : list A) : a1 = a1.
Proof. exact (eq_refl a1). Qed.
Lemma lem1096596 {A : Type'} (a0 : A) (a1 : list A) : (term16 A a0 a1) = (term17 A a1).
Proof. exact (MK_COMB (@lem1096594 A a0) (@lem1096595 A a1)). Qed.
Lemma lem1096597 {A : Type'} (a1 : list A) : (term17 A a1) = term18.
Proof. exact (eq_refl (term17 A a1)). Qed.
Lemma lem1096598 {A : Type'} (a0 : A) (a1 : list A) : (term16 A a0 a1) = term18.
Proof. exact (TRANS (@lem1096596 A a0 a1) (@lem1096597 A a1)). Qed.
Lemma lem1096599 {A : Type'} (fn : type1144 A) (a1 : list A) : (fn a1) = (fn a1).
Proof. exact (eq_refl (fn a1)). Qed.
Lemma lem1096600 {A : Type'} (a0 : A) (fn : type1144 A) (a1 : list A) : (term19 A a0 fn a1) = (term20 A fn a1).
Proof. exact (MK_COMB (@lem1096598 A a0 a1) (@lem1096599 A fn a1)). Qed.
Lemma lem1096601 {A : Type'} (fn : type1144 A) (a1 : list A) : (term20 A fn a1) = (term5 A fn a1).
Proof. exact (eq_refl (term20 A fn a1)). Qed.
Lemma lem1096602 {A : Type'} (a0 : A) (fn : type1144 A) (a1 : list A) : (term19 A a0 fn a1) = (term5 A fn a1).
Proof. exact (TRANS (@lem1096600 A a0 fn a1) (@lem1096601 A fn a1)). Qed.
Lemma lem1096603 {A : Type'} (fn : type1144 A) (a0 : A) (a1 : list A) : (term21 A fn a0 a1) = (term21 A fn a0 a1).
Proof. exact (eq_refl (term21 A fn a0 a1)). Qed.
Lemma lem1096604 {A : Type'} (a0 : A) (fn : type1144 A) (a1 : list A) : ((term4 A fn a0 a1) = (term19 A a0 fn a1)) = ((term4 A fn a0 a1) = (term5 A fn a1)).
Proof. exact (MK_COMB (@lem1096603 A fn a0 a1) (@lem1096602 A a0 fn a1)). Qed.
Lemma lem1096605 {A : Type'} (a0 : A) (fn : type1144 A) : (term22 A a0 fn) = (term23 A a0 fn).
Proof. exact (fun_ext (fun a1 : list A => @lem1096604 A a0 fn a1)). Qed.
Lemma lem1096606 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1096607 {A : Type'} (a0 : A) (fn : type1144 A) : (term24 A a0 fn) = (term2 A a0 fn).
Proof. exact (MK_COMB (@lem1096606 A) (@lem1096605 A a0 fn)). Qed.
Lemma lem1096608 {A : Type'} (fn : type1144 A) : (term25 A fn) = (term26 A fn).
Proof. exact (fun_ext (fun a0 : A => @lem1096607 A a0 fn)). Qed.
Lemma lem1096609 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1096610 {A : Type'} (fn : type1144 A) : (term27 A fn) = (term0 A fn).
Proof. exact (MK_COMB (@lem1096609 A) (@lem1096608 A fn)). Qed.
Lemma lem1096611 {A : Type'} (fn : type1144 A) : (term28 A fn) = (term28 A fn).
Proof. exact (eq_refl (term28 A fn)). Qed.
Lemma lem1096612 {A : Type'} (fn : type1144 A) : (term29 A fn) = (term6 A fn).
Proof. exact (MK_COMB (@lem1096611 A fn) (@lem1096610 A fn)). Qed.
Lemma lem1096613 {A : Type'} : (term30 A) = (term31 A).
Proof. exact (fun_ext (fun fn : type1144 A => @lem1096612 A fn)). Qed.
Lemma lem1096614 {A : Type'} : (@ex ((list A) -> nat)) = (@ex ((list A) -> nat)).
Proof. exact (eq_refl (@ex ((list A) -> nat))). Qed.
Lemma lem1096615 {A : Type'} : (term12 A) = (term32 A).
Proof. exact (MK_COMB (@lem1096614 A) (@lem1096613 A)). Qed.
Lemma lem1096616 {A : Type'} : term32 A.
Proof. exact (EQ_MP (@lem1096615 A) (@lem1096593 A)). Qed.
Lemma lem1096617 {A : Type'} (LENGTH' : type1144 A) (h1 : term6 A LENGTH') : term6 A LENGTH'.
Proof. exact (h1). Qed.
Lemma lem1096618 {A : Type'} (LENGTH' : type1144 A) (h1 : term6 A LENGTH') : term0 A LENGTH'.
Proof. exact (proj2 (@lem1096617 A LENGTH' h1)). Qed.
Lemma lem1096619 {A : Type'} (LENGTH' : type1144 A) (h1 : term6 A LENGTH') : (LENGTH' (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1096617 A LENGTH' h1)). Qed.
Lemma lem1096620 {A : Type'} (LENGTH' : type1144 A) (h1 : term6 A LENGTH') : term6 A LENGTH'.
Proof. exact (conj (@lem1096619 A LENGTH' h1) (@lem1096618 A LENGTH' h1)). Qed.
Lemma lem1096621 {A : Type'} (LENGTH' : type1144 A) (h1 : term6 A LENGTH') : term32 A.
Proof. exact (ex_intro (term31 A) LENGTH' (@lem1096620 A LENGTH' h1)). Qed.
Lemma lem1096622 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem1096623 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (ex_elim (@lem1096622 A h1) (fun LENGTH' : type1144 A => fun h0 : term31 A LENGTH' => @lem1096621 A LENGTH' h0)). Qed.
Lemma lem1096624 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (prop_ext (fun h1 : term32 A => @lem1096623 A h1) (fun h1 : term32 A => @lem1096616 A)). Qed.
Lemma lem1096625 {A : Type'} : term32 A.
Proof. exact (EQ_MP (@lem1096624 A) (@lem1096616 A)). Qed.
Lemma lem1096626 {A : Type'} (LENGTH' : type1144 A) (h1 : term6 A LENGTH') : term32 A.
Proof. exact (ex_intro (term31 A) LENGTH' (@lem1096585 A LENGTH' h1)). Qed.
Lemma lem1096627 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem1096628 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (ex_elim (@lem1096627 A h1) (fun LENGTH' : type1144 A => fun h0 : term31 A LENGTH' => @lem1096626 A LENGTH' h0)). Qed.
Lemma lem1096629 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (prop_ext (fun h1 : term32 A => @lem1096628 A h1) (fun h1 : term32 A => @lem1096625 A)). Qed.
Lemma lem1096630 {A : Type'} : term32 A.
Proof. exact (EQ_MP (@lem1096629 A) (@lem1096625 A)). Qed.
Lemma lem1096633 {A : Type'} (LENGTH' : type1144 A) (h1 : term6 A LENGTH') : term6 A LENGTH'.
Proof. exact (h1). Qed.
Lemma lem1096634 {A : Type'} (LENGTH' : type1144 A) (h1 : term6 A LENGTH') : term32 A.
Proof. exact (ex_intro (term31 A) LENGTH' (@lem1096633 A LENGTH' h1)). Qed.
Lemma lem1096635 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem1096636 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (ex_elim (@lem1096635 A h1) (fun LENGTH' : type1144 A => fun h0 : term31 A LENGTH' => @lem1096634 A LENGTH' h0)). Qed.
Lemma lem1096637 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (prop_ext (fun h1 : term32 A => @lem1096636 A h1) (fun h1 : term32 A => @lem1096630 A)). Qed.
Lemma lem1096638 {A : Type'} : term32 A.
Proof. exact (EQ_MP (@lem1096637 A) (@lem1096630 A)). Qed.
Lemma lem1096639 {A : Type'} : term33 A.
Proof. exact (fun _17943 : type1671 => @lem1096638 A). Qed.
Lemma lem1096640 {A B : Type'} (P : type1413 A B) : term34 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1096641 {A B : Type'} (P : type1413 A B) : (term34 A B P) = ((term35 A B P) = (term36 A B P)).
Proof. exact (eq_refl (term34 A B P)). Qed.
Lemma lem1096644 {A B : Type'} (P : type1413 A B) : (term35 A B P) = (term36 A B P).
Proof. exact (EQ_MP (@lem1096641 A B P) (@lem1096640 A B P)). Qed.
Lemma lem1096645 {A : Type'} (P : type1265 A) : (term37 A P) = (term38 A P).
Proof. exact (@lem1096644 type1671 (type1144 A) P). Qed.
Lemma lem1096646 {A : Type'} : (term39 A) = (term40 A).
Proof. exact (@lem1096645 A (term41 A)). Qed.
Lemma lem1096647 {A : Type'} (_17943 : type1671) : (term42 A _17943) = (term31 A).
Proof. exact (eq_refl (term42 A _17943)). Qed.
Lemma lem1096648 {A : Type'} (LENGTH' : type1144 A) : LENGTH' = LENGTH'.
Proof. exact (eq_refl LENGTH'). Qed.
Lemma lem1096649 {A : Type'} (_17943 : type1671) (LENGTH' : type1144 A) : (term43 A _17943 LENGTH') = (term44 A LENGTH').
Proof. exact (MK_COMB (@lem1096647 A _17943) (@lem1096648 A LENGTH')). Qed.
Lemma lem1096650 {A : Type'} (LENGTH' : type1144 A) : (term44 A LENGTH') = (term6 A LENGTH').
Proof. exact (eq_refl (term44 A LENGTH')). Qed.
Lemma lem1096651 {A : Type'} (_17943 : type1671) (LENGTH' : type1144 A) : (term43 A _17943 LENGTH') = (term6 A LENGTH').
Proof. exact (TRANS (@lem1096649 A _17943 LENGTH') (@lem1096650 A LENGTH')). Qed.
Lemma lem1096652 {A : Type'} (_17943 : type1671) : (term45 A _17943) = (term31 A).
Proof. exact (fun_ext (fun LENGTH' : type1144 A => @lem1096651 A _17943 LENGTH')). Qed.
Lemma lem1096653 {A : Type'} : (@ex ((list A) -> nat)) = (@ex ((list A) -> nat)).
Proof. exact (eq_refl (@ex ((list A) -> nat))). Qed.
Lemma lem1096654 {A : Type'} (_17943 : type1671) : (term46 A _17943) = (term32 A).
Proof. exact (MK_COMB (@lem1096653 A) (@lem1096652 A _17943)). Qed.
Lemma lem1096655 {A : Type'} : (term47 A) = (term48 A).
Proof. exact (fun_ext (fun _17943 : type1671 => @lem1096654 A _17943)). Qed.
Lemma lem1096656 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))). Qed.
Lemma lem1096657 {A : Type'} : (term39 A) = (term33 A).
Proof. exact (MK_COMB (@lem1096656) (@lem1096655 A)). Qed.
Lemma lem1096658 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1096659 {A : Type'} : (term49 A) = (term50 A).
Proof. exact (MK_COMB (@lem1096658) (@lem1096657 A)). Qed.
Lemma lem1096660 {A : Type'} (_17943 : type1671) : (term42 A _17943) = (term31 A).
Proof. exact (eq_refl (term42 A _17943)). Qed.
Lemma lem1096661 {A : Type'} (LENGTH' : type1271 A) (_17943 : type1671) : (LENGTH' _17943) = (LENGTH' _17943).
Proof. exact (eq_refl (LENGTH' _17943)). Qed.
Lemma lem1096662 {A : Type'} (LENGTH' : type1271 A) (_17943 : type1671) : (term51 A LENGTH' _17943) = (term52 A LENGTH' _17943).
Proof. exact (MK_COMB (@lem1096660 A _17943) (@lem1096661 A LENGTH' _17943)). Qed.
Lemma lem1096663 {A : Type'} (LENGTH' : type1271 A) (_17943 : type1671) : (term52 A LENGTH' _17943) = (term53 A LENGTH' _17943).
Proof. exact (eq_refl (term52 A LENGTH' _17943)). Qed.
Lemma lem1096664 {A : Type'} (LENGTH' : type1271 A) (_17943 : type1671) : (term51 A LENGTH' _17943) = (term53 A LENGTH' _17943).
Proof. exact (TRANS (@lem1096662 A LENGTH' _17943) (@lem1096663 A LENGTH' _17943)). Qed.
Lemma lem1096665 {A : Type'} (LENGTH' : type1271 A) : (term54 A LENGTH') = (term55 A LENGTH').
Proof. exact (fun_ext (fun _17943 : type1671 => @lem1096664 A LENGTH' _17943)). Qed.
Lemma lem1096666 : (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))) = (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat)))))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))). Qed.
Lemma lem1096667 {A : Type'} (LENGTH' : type1271 A) : (term56 A LENGTH') = (term57 A LENGTH').
Proof. exact (MK_COMB (@lem1096666) (@lem1096665 A LENGTH')). Qed.
Lemma lem1096668 {A : Type'} : (term58 A) = (term59 A).
Proof. exact (fun_ext (fun LENGTH' : type1271 A => @lem1096667 A LENGTH')). Qed.
Lemma lem1096669 {A : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (list A) -> nat)) = (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (list A) -> nat)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (list A) -> nat))). Qed.
Lemma lem1096670 {A : Type'} : (term40 A) = (term60 A).
Proof. exact (MK_COMB (@lem1096669 A) (@lem1096668 A)). Qed.
Lemma lem1096671 {A : Type'} : ((term39 A) = (term40 A)) = ((term33 A) = (term60 A)).
Proof. exact (MK_COMB (@lem1096659 A) (@lem1096670 A)). Qed.
Lemma lem1096672 {A : Type'} : (term33 A) = (term60 A).
Proof. exact (EQ_MP (@lem1096671 A) (@lem1096646 A)). Qed.
Lemma lem1096673 {A : Type'} : term60 A.
Proof. exact (EQ_MP (@lem1096672 A) (@lem1096639 A)). Qed.
Lemma lem1096675 {A : Type'} : (@ex A) = (term61 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1096676 {A : Type'} : (@ex ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (list A) -> nat)) = (term62 A).
Proof. exact (@lem1096675 (type1271 A)). Qed.
Lemma lem1096677 {A : Type'} : (term59 A) = (term59 A).
Proof. exact (eq_refl (term59 A)). Qed.
Lemma lem1096678 {A : Type'} : (term60 A) = (term63 A).
Proof. exact (MK_COMB (@lem1096676 A) (@lem1096677 A)). Qed.
Lemma lem1096679 {A : Type'} : (term63 A) = (term64 A).
Proof. exact (eq_refl (term63 A)). Qed.
Lemma lem1096680 {A : Type'} : (term60 A) = (term64 A).
Proof. exact (TRANS (@lem1096678 A) (@lem1096679 A)). Qed.
Lemma lem1096681 {A : Type'} : term64 A.
Proof. exact (EQ_MP (@lem1096680 A) (@lem1096673 A)). Qed.
