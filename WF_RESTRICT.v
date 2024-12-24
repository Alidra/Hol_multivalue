Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_RESTRICT_term_abbrevs.
Require Import WF_SUBSET_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem359537 (p : Prop) (q : Prop) (r : Prop) : (term0 p q r) = (term1 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem359538 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) : (term2 A lt3 lt2) = (term3 A lt3 lt2).
Proof. exact (@lem359537 (term4 A lt2 lt3) (@WF A lt3) (@WF A lt2)). Qed.
Lemma lem359553 {A : Type'} (lt2 : type1402 A) : (term5 A lt2) = (term6 A lt2).
Proof. exact (fun_ext (fun lt3 : type1402 A => @lem359538 A lt3 lt2)). Qed.
Lemma lem359554 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem359555 {A : Type'} (lt2 : type1402 A) : (term7 A lt2) = (term8 A lt2).
Proof. exact (MK_COMB (@lem359554 A) (@lem359553 A lt2)). Qed.
Lemma lem359560 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem359555 A lt2)). Qed.
Lemma lem359561 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem359562 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (MK_COMB (@lem359561 A) (@lem359560 A)). Qed.
Lemma lem359567 {A : Type'} : term12 A.
Proof. exact (EQ_MP (@lem359562 A) (@lem359527 A)). Qed.
Lemma lem359568 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem359569 {A : Type'} (lt2 : type1402 A) (h1 : term12 A) : term13 A lt2.
Proof. exact (@lem359568 A h1 lt2). Qed.
Lemma lem359570 {A : Type'} (lt2 : type1402 A) : (term13 A lt2) = (term8 A lt2).
Proof. exact (eq_refl (term13 A lt2)). Qed.
Lemma lem359571 {A : Type'} (lt2 : type1402 A) (h1 : term12 A) : term8 A lt2.
Proof. exact (EQ_MP (@lem359570 A lt2) (@lem359569 A lt2 h1)). Qed.
Lemma lem359572 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term12 A) : term14 A lt2 lt3.
Proof. exact (@lem359571 A lt2 h1 lt3). Qed.
Lemma lem359573 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) : (term14 A lt2 lt3) = (term3 A lt3 lt2).
Proof. exact (eq_refl (term14 A lt2 lt3)). Qed.
Lemma lem359574 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (h1 : term12 A) : term3 A lt3 lt2.
Proof. exact (EQ_MP (@lem359573 A lt3 lt2) (@lem359572 A lt2 lt3 h1)). Qed.
Lemma lem359575 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term4 A lt2 lt3) : term4 A lt2 lt3.
Proof. exact (h1). Qed.
Lemma lem359576 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term4 A lt2 lt3) (h2 : term12 A) : term15 A lt3 lt2.
Proof. exact (@lem359574 A lt3 lt2 h2 (@lem359575 A lt2 lt3 h1)). Qed.
Lemma lem359577 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term4 A lt2 lt3) : term16 A lt3 lt2.
Proof. exact (fun h0 : term12 A => @lem359576 A lt2 lt3 h1 h0). Qed.
Lemma lem359578 {A : Type'} (h1 : term12 A) : term12 A.
Proof. exact (h1). Qed.
Lemma lem359579 {A : Type'} (lt2 : type1402 A) (lt3 : type1402 A) (h1 : term4 A lt2 lt3) (h2 : term12 A) : term15 A lt3 lt2.
Proof. exact (@lem359577 A lt2 lt3 h1 (@lem359578 A h2)). Qed.
Lemma lem359580 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) (h1 : term12 A) : term3 A lt3 lt2.
Proof. exact (fun h0 : term4 A lt2 lt3 => @lem359579 A lt2 lt3 h0 h1). Qed.
Lemma lem359581 {A : Type'} (lt3 : type1402 A) (h1 : term12 A) : term17 A lt3.
Proof. exact (fun lt2 : type1402 A => @lem359580 A lt3 lt2 h1). Qed.
Lemma lem359582 {A : Type'} (h1 : term12 A) : term18 A.
Proof. exact (fun lt3 : type1402 A => @lem359581 A lt3 h1). Qed.
Lemma lem359583 {A : Type'} : term19 A.
Proof. exact (fun h0 : term12 A => @lem359582 A h0). Qed.
Lemma lem359584 {A : Type'} : term18 A.
Proof. exact (@lem359583 A (@lem359567 A)). Qed.
Lemma lem359585 {A : Type'} (lt3 : type1402 A) : term20 A lt3.
Proof. exact (@lem359584 A lt3). Qed.
Lemma lem359586 {A : Type'} (lt3 : type1402 A) : (term20 A lt3) = (term17 A lt3).
Proof. exact (eq_refl (term20 A lt3)). Qed.
Lemma lem359587 {A : Type'} (lt3 : type1402 A) : term17 A lt3.
Proof. exact (EQ_MP (@lem359586 A lt3) (@lem359585 A lt3)). Qed.
Lemma lem359588 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) : term21 A lt3 lt2.
Proof. exact (@lem359587 A lt3 lt2). Qed.
Lemma lem359589 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) : (term21 A lt3 lt2) = (term3 A lt3 lt2).
Proof. exact (eq_refl (term21 A lt3 lt2)). Qed.
Lemma lem359592 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) : term3 A lt3 lt2.
Proof. exact (EQ_MP (@lem359589 A lt3 lt2) (@lem359588 A lt3 lt2)). Qed.
Lemma lem359593 {A : Type'} (lt3 : type1402 A) (lt2 : type1402 A) : term3 A lt3 lt2.
Proof. exact (@lem359592 A lt3 lt2). Qed.
Lemma lem359594 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : term22 A P lt2.
Proof. exact (@lem359593 A lt2 (term23 A P lt2)). Qed.
Lemma lem359606 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term24 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem359607 (p : Prop) (q : Prop) (p' : Prop) : term25 p q p'.
Proof. exact (fun q' : Prop => @lem359606 p q p' q'). Qed.
Lemma lem359608 (p : Prop) (q : Prop) : term26 p q.
Proof. exact (fun p' : Prop => @lem359607 p q p'). Qed.
Lemma lem359609 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) : term27 A P lt2 x y.
Proof. exact (@lem359608 (term28 A P lt2 x y) (lt2 x y)). Qed.
Lemma lem359610 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) (p' : Prop) : term29 A P lt2 x y p'.
Proof. exact (@lem359609 A P lt2 x y p'). Qed.
Lemma lem359611 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) (p' : Prop) : (term29 A P lt2 x y p') = (term30 A P lt2 x y p').
Proof. exact (eq_refl (term29 A P lt2 x y p')). Qed.
Lemma lem359612 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) (p' : Prop) : term30 A P lt2 x y p'.
Proof. exact (EQ_MP (@lem359611 A P lt2 x y p') (@lem359610 A P lt2 x y p')). Qed.
Lemma lem359613 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) (p' : Prop) (q' : Prop) : term31 A P lt2 x y p' q'.
Proof. exact (@lem359612 A P lt2 x y p' q'). Qed.
Lemma lem359614 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) (p' : Prop) (q' : Prop) : (term31 A P lt2 x y p' q') = (term32 A P lt2 x y p' q').
Proof. exact (eq_refl (term31 A P lt2 x y p' q')). Qed.
Lemma lem359615 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) (p' : Prop) (q' : Prop) : term32 A P lt2 x y p' q'.
Proof. exact (EQ_MP (@lem359614 A P lt2 x y p' q') (@lem359613 A P lt2 x y p' q')). Qed.
Lemma lem359617 {A B : Type'} (f : A -> B) (y : A) : (term33 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem359618 {A : Type'} (f : type1402 A) (y : A) : (term34 A f y) = (f y).
Proof. exact (@lem359617 A (A -> Prop) f y). Qed.
Lemma lem359619 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term35 A P lt2 x) = (term36 A P lt2 x).
Proof. exact (@lem359618 A (term23 A P lt2) x). Qed.
Lemma lem359620 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term36 A P lt2 x) = (term37 A P lt2 x).
Proof. exact (eq_refl (term36 A P lt2 x)). Qed.
Lemma lem359621 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term38 A P lt2) = (term23 A P lt2).
Proof. exact (fun_ext (fun x : A => @lem359620 A P lt2 x)). Qed.
Lemma lem359622 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem359623 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term35 A P lt2 x) = (term36 A P lt2 x).
Proof. exact (MK_COMB (@lem359621 A P lt2) (@lem359622 A x)). Qed.
Lemma lem359624 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem359625 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term39 A P lt2 x) = (term40 A P lt2 x).
Proof. exact (MK_COMB (@lem359624 A) (@lem359623 A P lt2 x)). Qed.
Lemma lem359626 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term36 A P lt2 x) = (term37 A P lt2 x).
Proof. exact (eq_refl (term36 A P lt2 x)). Qed.
Lemma lem359627 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : ((term35 A P lt2 x) = (term36 A P lt2 x)) = ((term36 A P lt2 x) = (term37 A P lt2 x)).
Proof. exact (MK_COMB (@lem359625 A P lt2 x) (@lem359626 A P lt2 x)). Qed.
Lemma lem359628 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term36 A P lt2 x) = (term37 A P lt2 x).
Proof. exact (EQ_MP (@lem359627 A P lt2 x) (@lem359619 A P lt2 x)). Qed.
Lemma lem359633 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem359634 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) : (term28 A P lt2 x y) = (term41 A P lt2 x y).
Proof. exact (MK_COMB (@lem359628 A P lt2 x) (@lem359633 A y)). Qed.
Lemma lem359636 {A B : Type'} (f : A -> B) (y : A) : (term33 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem359637 {A : Type'} (f : A -> Prop) (y : A) : (term42 A f y) = (f y).
Proof. exact (@lem359636 A Prop f y). Qed.
Lemma lem359638 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) : (term43 A P lt2 x y) = (term41 A P lt2 x y).
Proof. exact (@lem359637 A (term37 A P lt2 x) y). Qed.
Lemma lem359639 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) : (term41 A P lt2 x y) = (term44 A P lt2 x y).
Proof. exact (eq_refl (term41 A P lt2 x y)). Qed.
Lemma lem359640 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term45 A P lt2 x) = (term37 A P lt2 x).
Proof. exact (fun_ext (fun y : A => @lem359639 A P lt2 x y)). Qed.
Lemma lem359641 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem359642 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) : (term43 A P lt2 x y) = (term41 A P lt2 x y).
Proof. exact (MK_COMB (@lem359640 A P lt2 x) (@lem359641 A y)). Qed.
Lemma lem359643 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem359644 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) : (term46 A P lt2 x y) = (term47 A P lt2 x y).
Proof. exact (MK_COMB (@lem359643) (@lem359642 A P lt2 x y)). Qed.
Lemma lem359645 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) : (term41 A P lt2 x y) = (term44 A P lt2 x y).
Proof. exact (eq_refl (term41 A P lt2 x y)). Qed.
Lemma lem359646 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) : ((term43 A P lt2 x y) = (term41 A P lt2 x y)) = ((term41 A P lt2 x y) = (term44 A P lt2 x y)).
Proof. exact (MK_COMB (@lem359644 A P lt2 x y) (@lem359645 A P lt2 x y)). Qed.
Lemma lem359647 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) : (term41 A P lt2 x y) = (term44 A P lt2 x y).
Proof. exact (EQ_MP (@lem359646 A P lt2 x y) (@lem359638 A P lt2 x y)). Qed.
Lemma lem359652 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) : (term28 A P lt2 x y) = (term44 A P lt2 x y).
Proof. exact (TRANS (@lem359634 A P lt2 x y) (@lem359647 A P lt2 x y)). Qed.
Lemma lem359653 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) (q' : Prop) : term48 A P lt2 x y q'.
Proof. exact (@lem359615 A P lt2 x y (term44 A P lt2 x y) q'). Qed.
Lemma lem359654 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) (q' : Prop) : term49 A P lt2 x y q'.
Proof. exact (@lem359653 A P lt2 x y q' (@lem359652 A P lt2 x y)). Qed.
Lemma lem359655 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) (h1 : term44 A P lt2 x y) : term44 A P lt2 x y.
Proof. exact (h1). Qed.
Lemma lem359656 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) (h1 : term44 A P lt2 x y) : term50 A P lt2 x y.
Proof. exact (proj2 (@lem359655 A P lt2 x y h1)). Qed.
Lemma lem359657 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) (h1 : term44 A P lt2 x y) : lt2 x y.
Proof. exact (proj2 (@lem359656 A P lt2 x y h1)). Qed.
Lemma lem359658 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (lt2 x y) = ((lt2 x y) = True).
Proof. exact (@lem7 (lt2 x y)). Qed.
Lemma lem359667 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) (h1 : term44 A P lt2 x y) : (lt2 x y) = True.
Proof. exact (EQ_MP (@lem359658 A lt2 x y) (@lem359657 A P lt2 x y h1)). Qed.
Lemma lem359668 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) : term51 A P lt2 x y.
Proof. exact (fun h0 : term44 A P lt2 x y => @lem359667 A P lt2 x y h0). Qed.
Lemma lem359669 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) : term52 A P lt2 x y.
Proof. exact (@lem359654 A P lt2 x y True). Qed.
Lemma lem359670 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) : (term53 A P lt2 x y) = (term54 A P lt2 x y).
Proof. exact (@lem359669 A P lt2 x y (@lem359668 A P lt2 x y)). Qed.
Lemma lem359672 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem359673 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) : (term54 A P lt2 x y) = True.
Proof. exact (@lem359672 (term44 A P lt2 x y)). Qed.
Lemma lem359674 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) (y : A) : (term53 A P lt2 x y) = True.
Proof. exact (TRANS (@lem359670 A P lt2 x y) (@lem359673 A P lt2 x y)). Qed.
Lemma lem359675 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term55 A P lt2 x) = (term56 A).
Proof. exact (fun_ext (fun y : A => @lem359674 A P lt2 x y)). Qed.
Lemma lem359676 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem359677 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term57 A P lt2 x) = (term58 A).
Proof. exact (MK_COMB (@lem359676 A) (@lem359675 A P lt2 x)). Qed.
Lemma lem359679 {A : Type'} (t : Prop) : (term59 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem359680 {A : Type'} (t : Prop) : (term59 A t) = t.
Proof. exact (@lem359679 A t). Qed.
Lemma lem359681 {A : Type'} : (term58 A) = True.
Proof. exact (@lem359680 A True). Qed.
Lemma lem359682 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) (x : A) : (term57 A P lt2 x) = True.
Proof. exact (TRANS (@lem359677 A P lt2 x) (@lem359681 A)). Qed.
Lemma lem359683 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term60 A P lt2) = (term56 A).
Proof. exact (fun_ext (fun x : A => @lem359682 A P lt2 x)). Qed.
Lemma lem359684 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem359685 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term61 A P lt2) = (term58 A).
Proof. exact (MK_COMB (@lem359684 A) (@lem359683 A P lt2)). Qed.
Lemma lem359687 {A : Type'} (t : Prop) : (term59 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem359688 {A : Type'} (t : Prop) : (term59 A t) = t.
Proof. exact (@lem359687 A t). Qed.
Lemma lem359689 {A : Type'} : (term58 A) = True.
Proof. exact (@lem359688 A True). Qed.
Lemma lem359690 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : (term61 A P lt2) = True.
Proof. exact (TRANS (@lem359685 A P lt2) (@lem359689 A)). Qed.
Lemma lem359691 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : True = (term61 A P lt2).
Proof. exact (SYM (@lem359690 A P lt2)). Qed.
Lemma lem359692 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : term61 A P lt2.
Proof. exact (EQ_MP (@lem359691 A P lt2) (@lem0)). Qed.
Lemma lem359693 {A : Type'} (P : A -> Prop) (lt2 : type1402 A) : term62 A P lt2.
Proof. exact (@lem359594 A P lt2 (@lem359692 A P lt2)). Qed.
Lemma lem359698 {A : Type'} (lt2 : type1402 A) : term63 A lt2.
Proof. exact (fun P : A -> Prop => @lem359693 A P lt2). Qed.
Lemma lem359703 {A : Type'} : term64 A.
Proof. exact (fun lt2 : type1402 A => @lem359698 A lt2). Qed.
