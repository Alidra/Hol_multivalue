Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1068659_term_abbrevs.
Require Import SKOLEM_THM_spec.
Require Import sum_RECURSION_spec.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem1068568 {A B : Type'} (OUTR' : type8 A B) (h1 : term0 A B OUTR') : term0 A B OUTR'.
Proof. exact (h1). Qed.
Lemma lem1068569 {A B : Type'} (y : B) (OUTR' : type8 A B) (h1 : term0 A B OUTR') : term1 A B OUTR' y.
Proof. exact (@lem1068568 A B OUTR' h1 y). Qed.
Lemma lem1068570 {A B : Type'} (OUTR' : type8 A B) (y : B) : (term1 A B OUTR' y) = ((term2 A B OUTR' y) = y).
Proof. exact (eq_refl (term1 A B OUTR' y)). Qed.
Lemma lem1068571 {A B : Type'} (y : B) (OUTR' : type8 A B) (h1 : term0 A B OUTR') : (term2 A B OUTR' y) = y.
Proof. exact (EQ_MP (@lem1068570 A B OUTR' y) (@lem1068569 A B y OUTR' h1)). Qed.
Lemma lem1068572 {A B : Type'} (OUTR' : type8 A B) (h1 : term0 A B OUTR') : term0 A B OUTR'.
Proof. exact (fun y : B => @lem1068571 A B y OUTR' h1). Qed.
Lemma lem1068573 {A B : Type'} (OUTR' : type8 A B) (h1 : term0 A B OUTR') : term0 A B OUTR'.
Proof. exact (h1). Qed.
Lemma lem1068574 {A B : Type'} (OUTR' : type8 A B) : (term0 A B OUTR') = (term0 A B OUTR').
Proof. exact (prop_ext (fun h1 : term0 A B OUTR' => @lem1068572 A B OUTR' h1) (fun h1 : term0 A B OUTR' => @lem1068573 A B OUTR' h1)). Qed.
Lemma lem1068575 {A B : Type'} (OUTR' : type8 A B) (h1 : term0 A B OUTR') : term0 A B OUTR'.
Proof. exact (EQ_MP (@lem1068574 A B OUTR') (@lem1068573 A B OUTR' h1)). Qed.
Lemma lem1068576 {A B Z : Type'} (INL' : A -> Z) : term3 A B Z INL'.
Proof. exact (@lem1068060 A B Z INL'). Qed.
Lemma lem1068577 {A B Z : Type'} (INL' : A -> Z) : (term3 A B Z INL') = (term4 A B Z INL').
Proof. exact (eq_refl (term3 A B Z INL')). Qed.
Lemma lem1068578 {A B Z : Type'} (INL' : A -> Z) : term4 A B Z INL'.
Proof. exact (EQ_MP (@lem1068577 A B Z INL') (@lem1068576 A B Z INL')). Qed.
Lemma lem1068579 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) : term5 A B Z INL' INR'.
Proof. exact (@lem1068578 A B Z INL' INR'). Qed.
Lemma lem1068580 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) : (term5 A B Z INL' INR') = (term6 A B Z INL' INR').
Proof. exact (eq_refl (term5 A B Z INL' INR')). Qed.
Lemma lem1068581 {A B Z : Type'} (INL' : A -> Z) (INR' : B -> Z) : term6 A B Z INL' INR'.
Proof. exact (EQ_MP (@lem1068580 A B Z INL' INR') (@lem1068579 A B Z INL' INR')). Qed.
Lemma lem1068582 {A B : Type'} (INL' : A -> B) (INR' : B -> B) : term7 A B INL' INR'.
Proof. exact (@lem1068581 A B B INL' INR'). Qed.
Lemma lem1068583 {A B : Type'} (INL' : A -> B) : term8 A B INL'.
Proof. exact (@lem1068582 A B INL' (term9 B)). Qed.
Lemma lem1068584 {B : Type'} (a : B) : (term10 B a) = a.
Proof. exact (eq_refl (term10 B a)). Qed.
Lemma lem1068585 {A B : Type'} (fn : type8 A B) (a : B) : (term11 A B fn a) = (term11 A B fn a).
Proof. exact (eq_refl (term11 A B fn a)). Qed.
Lemma lem1068586 {A B : Type'} (fn : type8 A B) (a : B) : ((term2 A B fn a) = (term10 B a)) = ((term2 A B fn a) = a).
Proof. exact (MK_COMB (@lem1068585 A B fn a) (@lem1068584 B a)). Qed.
Lemma lem1068587 {A B : Type'} (fn : type8 A B) : (term12 A B fn) = (term13 A B fn).
Proof. exact (fun_ext (fun a : B => @lem1068586 A B fn a)). Qed.
Lemma lem1068588 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem1068589 {A B : Type'} (fn : type8 A B) : (term14 A B fn) = (term0 A B fn).
Proof. exact (MK_COMB (@lem1068588 B) (@lem1068587 A B fn)). Qed.
Lemma lem1068590 {A B : Type'} (fn : type8 A B) (INL' : A -> B) : (term15 A B fn INL') = (term15 A B fn INL').
Proof. exact (eq_refl (term15 A B fn INL')). Qed.
Lemma lem1068591 {A B : Type'} (INL' : A -> B) (fn : type8 A B) : (term16 A B INL' fn) = (term17 A B INL' fn).
Proof. exact (MK_COMB (@lem1068590 A B fn INL') (@lem1068589 A B fn)). Qed.
Lemma lem1068592 {A B : Type'} (INL' : A -> B) : (term18 A B INL') = (term19 A B INL').
Proof. exact (fun_ext (fun fn : type8 A B => @lem1068591 A B INL' fn)). Qed.
Lemma lem1068593 {A B : Type'} : (@ex ((Datatypes.sum A B) -> B)) = (@ex ((Datatypes.sum A B) -> B)).
Proof. exact (eq_refl (@ex ((Datatypes.sum A B) -> B))). Qed.
Lemma lem1068594 {A B : Type'} (INL' : A -> B) : (term8 A B INL') = (term20 A B INL').
Proof. exact (MK_COMB (@lem1068593 A B) (@lem1068592 A B INL')). Qed.
Lemma lem1068595 {A B : Type'} (INL' : A -> B) : term20 A B INL'.
Proof. exact (EQ_MP (@lem1068594 A B INL') (@lem1068583 A B INL')). Qed.
Lemma lem1068596 {A B : Type'} (INL' : A -> B) (OUTR' : type8 A B) (h1 : term17 A B INL' OUTR') : term17 A B INL' OUTR'.
Proof. exact (h1). Qed.
Lemma lem1068597 {A B : Type'} (INL' : A -> B) (OUTR' : type8 A B) (h1 : term17 A B INL' OUTR') : term0 A B OUTR'.
Proof. exact (proj2 (@lem1068596 A B INL' OUTR' h1)). Qed.
Lemma lem1068599 {A B : Type'} (INL' : A -> B) (OUTR' : type8 A B) (h1 : term17 A B INL' OUTR') : term21 A B.
Proof. exact (ex_intro (term22 A B) OUTR' (@lem1068597 A B INL' OUTR' h1)). Qed.
Lemma lem1068600 {A B : Type'} (INL' : A -> B) (h1 : term20 A B INL') : term20 A B INL'.
Proof. exact (h1). Qed.
Lemma lem1068601 {A B : Type'} (INL' : A -> B) (h1 : term20 A B INL') : term21 A B.
Proof. exact (ex_elim (@lem1068600 A B INL' h1) (fun OUTR' : type8 A B => fun h0 : term19 A B INL' OUTR' => @lem1068599 A B INL' OUTR' h0)). Qed.
Lemma lem1068602 {A B : Type'} (INL' : A -> B) : (term20 A B INL') = (term21 A B).
Proof. exact (prop_ext (fun h1 : term20 A B INL' => @lem1068601 A B INL' h1) (fun h1 : term21 A B => @lem1068595 A B INL')). Qed.
Lemma lem1068603 {A B : Type'} : term21 A B.
Proof. exact (EQ_MP (@lem1068602 A B (@el (A -> B))) (@lem1068595 A B (@el (A -> B)))). Qed.
Lemma lem1068604 {A B : Type'} (OUTR' : type8 A B) (h1 : term0 A B OUTR') : term21 A B.
Proof. exact (ex_intro (term22 A B) OUTR' (@lem1068575 A B OUTR' h1)). Qed.
Lemma lem1068605 {A B : Type'} (h1 : term21 A B) : term21 A B.
Proof. exact (h1). Qed.
Lemma lem1068606 {A B : Type'} (h1 : term21 A B) : term21 A B.
Proof. exact (ex_elim (@lem1068605 A B h1) (fun OUTR' : type8 A B => fun h0 : term22 A B OUTR' => @lem1068604 A B OUTR' h0)). Qed.
Lemma lem1068607 {A B : Type'} : (term21 A B) = (term21 A B).
Proof. exact (prop_ext (fun h1 : term21 A B => @lem1068606 A B h1) (fun h1 : term21 A B => @lem1068603 A B)). Qed.
Lemma lem1068608 {A B : Type'} : term21 A B.
Proof. exact (EQ_MP (@lem1068607 A B) (@lem1068603 A B)). Qed.
Lemma lem1068611 {A B : Type'} (OUTR' : type8 A B) (h1 : term0 A B OUTR') : term0 A B OUTR'.
Proof. exact (h1). Qed.
Lemma lem1068612 {A B : Type'} (OUTR' : type8 A B) (h1 : term0 A B OUTR') : term21 A B.
Proof. exact (ex_intro (term22 A B) OUTR' (@lem1068611 A B OUTR' h1)). Qed.
Lemma lem1068613 {A B : Type'} (h1 : term21 A B) : term21 A B.
Proof. exact (h1). Qed.
Lemma lem1068614 {A B : Type'} (h1 : term21 A B) : term21 A B.
Proof. exact (ex_elim (@lem1068613 A B h1) (fun OUTR' : type8 A B => fun h0 : term22 A B OUTR' => @lem1068612 A B OUTR' h0)). Qed.
Lemma lem1068615 {A B : Type'} : (term21 A B) = (term21 A B).
Proof. exact (prop_ext (fun h1 : term21 A B => @lem1068614 A B h1) (fun h1 : term21 A B => @lem1068608 A B)). Qed.
Lemma lem1068616 {A B : Type'} : term21 A B.
Proof. exact (EQ_MP (@lem1068615 A B) (@lem1068608 A B)). Qed.
Lemma lem1068617 {A B : Type'} : term23 A B.
Proof. exact (fun _17488 : type1673 => @lem1068616 A B). Qed.
Lemma lem1068618 {A B : Type'} (P : type1413 A B) : term24 A B P.
Proof. exact (@lem13546 A B P). Qed.
Lemma lem1068619 {A B : Type'} (P : type1413 A B) : (term24 A B P) = ((term25 A B P) = (term26 A B P)).
Proof. exact (eq_refl (term24 A B P)). Qed.
Lemma lem1068622 {A B : Type'} (P : type1413 A B) : (term25 A B P) = (term26 A B P).
Proof. exact (EQ_MP (@lem1068619 A B P) (@lem1068618 A B P)). Qed.
Lemma lem1068623 {A B : Type'} (P : type1280 A B) : (term27 A B P) = (term28 A B P).
Proof. exact (@lem1068622 type1673 (type8 A B) P). Qed.
Lemma lem1068624 {A B : Type'} : (term29 A B) = (term30 A B).
Proof. exact (@lem1068623 A B (term31 A B)). Qed.
Lemma lem1068625 {A B : Type'} (_17488 : type1673) : (term32 A B _17488) = (term22 A B).
Proof. exact (eq_refl (term32 A B _17488)). Qed.
Lemma lem1068626 {A B : Type'} (OUTR' : type8 A B) : OUTR' = OUTR'.
Proof. exact (eq_refl OUTR'). Qed.
Lemma lem1068627 {A B : Type'} (_17488 : type1673) (OUTR' : type8 A B) : (term33 A B _17488 OUTR') = (term34 A B OUTR').
Proof. exact (MK_COMB (@lem1068625 A B _17488) (@lem1068626 A B OUTR')). Qed.
Lemma lem1068628 {A B : Type'} (OUTR' : type8 A B) : (term34 A B OUTR') = (term0 A B OUTR').
Proof. exact (eq_refl (term34 A B OUTR')). Qed.
Lemma lem1068629 {A B : Type'} (_17488 : type1673) (OUTR' : type8 A B) : (term33 A B _17488 OUTR') = (term0 A B OUTR').
Proof. exact (TRANS (@lem1068627 A B _17488 OUTR') (@lem1068628 A B OUTR')). Qed.
Lemma lem1068630 {A B : Type'} (_17488 : type1673) : (term35 A B _17488) = (term22 A B).
Proof. exact (fun_ext (fun OUTR' : type8 A B => @lem1068629 A B _17488 OUTR')). Qed.
Lemma lem1068631 {A B : Type'} : (@ex ((Datatypes.sum A B) -> B)) = (@ex ((Datatypes.sum A B) -> B)).
Proof. exact (eq_refl (@ex ((Datatypes.sum A B) -> B))). Qed.
Lemma lem1068632 {A B : Type'} (_17488 : type1673) : (term36 A B _17488) = (term21 A B).
Proof. exact (MK_COMB (@lem1068631 A B) (@lem1068630 A B _17488)). Qed.
Lemma lem1068633 {A B : Type'} : (term37 A B) = (term38 A B).
Proof. exact (fun_ext (fun _17488 : type1673 => @lem1068632 A B _17488)). Qed.
Lemma lem1068634 : (@all (prod nat (prod nat (prod nat nat)))) = (@all (prod nat (prod nat (prod nat nat)))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat nat))))). Qed.
Lemma lem1068635 {A B : Type'} : (term29 A B) = (term23 A B).
Proof. exact (MK_COMB (@lem1068634) (@lem1068633 A B)). Qed.
Lemma lem1068636 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1068637 {A B : Type'} : (term39 A B) = (term40 A B).
Proof. exact (MK_COMB (@lem1068636) (@lem1068635 A B)). Qed.
Lemma lem1068638 {A B : Type'} (_17488 : type1673) : (term32 A B _17488) = (term22 A B).
Proof. exact (eq_refl (term32 A B _17488)). Qed.
Lemma lem1068639 {A B : Type'} (OUTR' : type1278 A B) (_17488 : type1673) : (OUTR' _17488) = (OUTR' _17488).
Proof. exact (eq_refl (OUTR' _17488)). Qed.
Lemma lem1068640 {A B : Type'} (OUTR' : type1278 A B) (_17488 : type1673) : (term41 A B OUTR' _17488) = (term42 A B OUTR' _17488).
Proof. exact (MK_COMB (@lem1068638 A B _17488) (@lem1068639 A B OUTR' _17488)). Qed.
Lemma lem1068641 {A B : Type'} (OUTR' : type1278 A B) (_17488 : type1673) : (term42 A B OUTR' _17488) = (term43 A B OUTR' _17488).
Proof. exact (eq_refl (term42 A B OUTR' _17488)). Qed.
Lemma lem1068642 {A B : Type'} (OUTR' : type1278 A B) (_17488 : type1673) : (term41 A B OUTR' _17488) = (term43 A B OUTR' _17488).
Proof. exact (TRANS (@lem1068640 A B OUTR' _17488) (@lem1068641 A B OUTR' _17488)). Qed.
Lemma lem1068643 {A B : Type'} (OUTR' : type1278 A B) : (term44 A B OUTR') = (term45 A B OUTR').
Proof. exact (fun_ext (fun _17488 : type1673 => @lem1068642 A B OUTR' _17488)). Qed.
Lemma lem1068644 : (@all (prod nat (prod nat (prod nat nat)))) = (@all (prod nat (prod nat (prod nat nat)))).
Proof. exact (eq_refl (@all (prod nat (prod nat (prod nat nat))))). Qed.
Lemma lem1068645 {A B : Type'} (OUTR' : type1278 A B) : (term46 A B OUTR') = (term47 A B OUTR').
Proof. exact (MK_COMB (@lem1068644) (@lem1068643 A B OUTR')). Qed.
Lemma lem1068646 {A B : Type'} : (term48 A B) = (term49 A B).
Proof. exact (fun_ext (fun OUTR' : type1278 A B => @lem1068645 A B OUTR')). Qed.
Lemma lem1068647 {A B : Type'} : (@ex ((prod nat (prod nat (prod nat nat))) -> (Datatypes.sum A B) -> B)) = (@ex ((prod nat (prod nat (prod nat nat))) -> (Datatypes.sum A B) -> B)).
Proof. exact (eq_refl (@ex ((prod nat (prod nat (prod nat nat))) -> (Datatypes.sum A B) -> B))). Qed.
Lemma lem1068648 {A B : Type'} : (term30 A B) = (term50 A B).
Proof. exact (MK_COMB (@lem1068647 A B) (@lem1068646 A B)). Qed.
Lemma lem1068649 {A B : Type'} : ((term29 A B) = (term30 A B)) = ((term23 A B) = (term50 A B)).
Proof. exact (MK_COMB (@lem1068637 A B) (@lem1068648 A B)). Qed.
Lemma lem1068650 {A B : Type'} : (term23 A B) = (term50 A B).
Proof. exact (EQ_MP (@lem1068649 A B) (@lem1068624 A B)). Qed.
Lemma lem1068651 {A B : Type'} : term50 A B.
Proof. exact (EQ_MP (@lem1068650 A B) (@lem1068617 A B)). Qed.
Lemma lem1068653 {A : Type'} : (@ex A) = (term51 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
Lemma lem1068654 {A B : Type'} : (@ex ((prod nat (prod nat (prod nat nat))) -> (Datatypes.sum A B) -> B)) = (term52 A B).
Proof. exact (@lem1068653 (type1278 A B)). Qed.
Lemma lem1068655 {A B : Type'} : (term49 A B) = (term49 A B).
Proof. exact (eq_refl (term49 A B)). Qed.
Lemma lem1068656 {A B : Type'} : (term50 A B) = (term53 A B).
Proof. exact (MK_COMB (@lem1068654 A B) (@lem1068655 A B)). Qed.
Lemma lem1068657 {A B : Type'} : (term53 A B) = (term54 A B).
Proof. exact (eq_refl (term53 A B)). Qed.
Lemma lem1068658 {A B : Type'} : (term50 A B) = (term54 A B).
Proof. exact (TRANS (@lem1068656 A B) (@lem1068657 A B)). Qed.
Lemma lem1068659 {A B : Type'} : term54 A B.
Proof. exact (EQ_MP (@lem1068658 A B) (@lem1068651 A B)). Qed.
