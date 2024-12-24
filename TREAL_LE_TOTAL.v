Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_LE_TOTAL_term_abbrevs.
Require Import FORALL_PAIR_THM_spec.
Require Import thm0_spec.
Require Import thm1319496_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Require Import treal_le_spec.
Lemma lem1330545 (x : hreal) : term0 x.
Proof. exact (@lem1319496 x). Qed.
Lemma lem1330546 (x : hreal) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1330547 (x : hreal) : term1 x.
Proof. exact (EQ_MP (@lem1330546 x) (@lem1330545 x)). Qed.
Lemma lem1330548 (x : hreal) (y : hreal) : term2 x y.
Proof. exact (@lem1330547 x y). Qed.
Lemma lem1330549 (y : hreal) (x : hreal) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1330550 (y : hreal) (x : hreal) : term3 y x.
Proof. exact (EQ_MP (@lem1330549 y x) (@lem1330548 x y)). Qed.
Lemma lem1330551 (y : hreal) (x : hreal) : (term3 y x) = ((term3 y x) = True).
Proof. exact (@lem7 (term3 y x)). Qed.
Lemma lem1330553 (x1 : hreal) : term4 x1.
Proof. exact (@lem1324956 x1). Qed.
Lemma lem1330554 (x1 : hreal) : (term4 x1) = (term5 x1).
Proof. exact (eq_refl (term4 x1)). Qed.
Lemma lem1330555 (x1 : hreal) : term5 x1.
Proof. exact (EQ_MP (@lem1330554 x1) (@lem1330553 x1)). Qed.
Lemma lem1330556 (x1 : hreal) (y2 : hreal) : term6 x1 y2.
Proof. exact (@lem1330555 x1 y2). Qed.
Lemma lem1330557 (x1 : hreal) (y2 : hreal) : (term6 x1 y2) = (term7 x1 y2).
Proof. exact (eq_refl (term6 x1 y2)). Qed.
Lemma lem1330558 (x1 : hreal) (y2 : hreal) : term7 x1 y2.
Proof. exact (EQ_MP (@lem1330557 x1 y2) (@lem1330556 x1 y2)). Qed.
Lemma lem1330559 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term8 x1 y2 x2.
Proof. exact (@lem1330558 x1 y2 x2). Qed.
Lemma lem1330560 (x1 : hreal) (y2 : hreal) (x2 : hreal) : (term8 x1 y2 x2) = (term9 x1 y2 x2).
Proof. exact (eq_refl (term8 x1 y2 x2)). Qed.
Lemma lem1330561 (x1 : hreal) (y2 : hreal) (x2 : hreal) : term9 x1 y2 x2.
Proof. exact (EQ_MP (@lem1330560 x1 y2 x2) (@lem1330559 x1 y2 x2)). Qed.
Lemma lem1330562 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : term10 x1 y2 x2 y1.
Proof. exact (@lem1330561 x1 y2 x2 y1). Qed.
Lemma lem1330563 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term10 x1 y2 x2 y1) = ((term11 x1 y1 x2 y2) = (term12 x1 y2 x2 y1)).
Proof. exact (eq_refl (term10 x1 y2 x2 y1)). Qed.
Lemma lem1330565 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term13 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem1330566 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term13 _5106 _5107 P) = ((term14 _5106 _5107 P) = (term15 _5106 _5107 P)).
Proof. exact (eq_refl (term13 _5106 _5107 P)). Qed.
Lemma lem1330573 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term14 _5106 _5107 P) = (term15 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1330566 _5106 _5107 P) (@lem1330565 _5106 _5107 P)). Qed.
Lemma lem1330574 (P : type1233) : (term16 P) = (term17 P).
Proof. exact (@lem1330573 hreal hreal P). Qed.
Lemma lem1330575 : term18 = term19.
Proof. exact (@lem1330574 term20). Qed.
Lemma lem1330576 (x : prod hreal hreal) : (term21 x) = (term22 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1330577 : term23 = term20.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1330576 x)). Qed.
Lemma lem1330578 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1330579 : term18 = term24.
Proof. exact (MK_COMB (@lem1330578) (@lem1330577)). Qed.
Lemma lem1330580 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1330581 : term25 = term26.
Proof. exact (MK_COMB (@lem1330580) (@lem1330579)). Qed.
Lemma lem1330582 (p1 : hreal) (p2 : hreal) : (term27 p1 p2) = (term28 p1 p2).
Proof. exact (eq_refl (term27 p1 p2)). Qed.
Lemma lem1330583 (p1 : hreal) : (term29 p1) = (term30 p1).
Proof. exact (fun_ext (fun p2 : hreal => @lem1330582 p1 p2)). Qed.
Lemma lem1330584 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330585 (p1 : hreal) : (term31 p1) = (term32 p1).
Proof. exact (MK_COMB (@lem1330584) (@lem1330583 p1)). Qed.
Lemma lem1330586 : term33 = term34.
Proof. exact (fun_ext (fun p1 : hreal => @lem1330585 p1)). Qed.
Lemma lem1330587 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330588 : term19 = term35.
Proof. exact (MK_COMB (@lem1330587) (@lem1330586)). Qed.
Lemma lem1330589 : (term18 = term19) = (term24 = term35).
Proof. exact (MK_COMB (@lem1330581) (@lem1330588)). Qed.
Lemma lem1330590 : term24 = term35.
Proof. exact (EQ_MP (@lem1330589) (@lem1330575)). Qed.
Lemma lem1330608 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term14 _5106 _5107 P) = (term15 _5106 _5107 P).
Proof. exact (EQ_MP (@lem1330566 _5106 _5107 P) (@lem1330565 _5106 _5107 P)). Qed.
Lemma lem1330609 (P : type1233) : (term16 P) = (term17 P).
Proof. exact (@lem1330608 hreal hreal P). Qed.
Lemma lem1330610 (p1 : hreal) (p2 : hreal) : (term36 p1 p2) = (term37 p1 p2).
Proof. exact (@lem1330609 (term38 p1 p2)). Qed.
Lemma lem1330611 (y : prod hreal hreal) (p1 : hreal) (p2 : hreal) : (term39 p1 p2 y) = (term40 y p1 p2).
Proof. exact (eq_refl (term39 p1 p2 y)). Qed.
Lemma lem1330612 (p1 : hreal) (p2 : hreal) : (term41 p1 p2) = (term38 p1 p2).
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1330611 y p1 p2)). Qed.
Lemma lem1330613 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1330614 (p1 : hreal) (p2 : hreal) : (term36 p1 p2) = (term28 p1 p2).
Proof. exact (MK_COMB (@lem1330613) (@lem1330612 p1 p2)). Qed.
Lemma lem1330615 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1330616 (p1 : hreal) (p2 : hreal) : (term42 p1 p2) = (term43 p1 p2).
Proof. exact (MK_COMB (@lem1330615) (@lem1330614 p1 p2)). Qed.
Lemma lem1330617 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term44 p1 p2 p1' p2') = (term45 p1' p2' p1 p2).
Proof. exact (eq_refl (term44 p1 p2 p1' p2')). Qed.
Lemma lem1330618 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term46 p1 p2 p1') = (term47 p1' p1 p2).
Proof. exact (fun_ext (fun p2' : hreal => @lem1330617 p1' p2' p1 p2)). Qed.
Lemma lem1330619 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330620 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term48 p1 p2 p1') = (term49 p1' p1 p2).
Proof. exact (MK_COMB (@lem1330619) (@lem1330618 p1' p1 p2)). Qed.
Lemma lem1330621 (p1 : hreal) (p2 : hreal) : (term50 p1 p2) = (term51 p1 p2).
Proof. exact (fun_ext (fun p1' : hreal => @lem1330620 p1' p1 p2)). Qed.
Lemma lem1330622 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330623 (p1 : hreal) (p2 : hreal) : (term37 p1 p2) = (term52 p1 p2).
Proof. exact (MK_COMB (@lem1330622) (@lem1330621 p1 p2)). Qed.
Lemma lem1330624 (p1 : hreal) (p2 : hreal) : ((term36 p1 p2) = (term37 p1 p2)) = ((term28 p1 p2) = (term52 p1 p2)).
Proof. exact (MK_COMB (@lem1330616 p1 p2) (@lem1330623 p1 p2)). Qed.
Lemma lem1330625 (p1 : hreal) (p2 : hreal) : (term28 p1 p2) = (term52 p1 p2).
Proof. exact (EQ_MP (@lem1330624 p1 p2) (@lem1330610 p1 p2)). Qed.
Lemma lem1330641 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term11 x1 y1 x2 y2) = (term12 x1 y2 x2 y1).
Proof. exact (EQ_MP (@lem1330563 x1 y2 x2 y1) (@lem1330562 x1 y2 x2 y1)). Qed.
Lemma lem1330642 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term11 p1 p2 p1' p2') = (term12 p1 p2' p1' p2).
Proof. exact (@lem1330641 p1 p2' p1' p2). Qed.
Lemma lem1330643 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1330644 (p1 : hreal) (p2' : hreal) (p1' : hreal) (p2 : hreal) : (term53 p1 p2 p1' p2') = (term54 p1 p2' p1' p2).
Proof. exact (MK_COMB (@lem1330643) (@lem1330642 p1 p2' p1' p2)). Qed.
Lemma lem1330646 (x1 : hreal) (y2 : hreal) (x2 : hreal) (y1 : hreal) : (term11 x1 y1 x2 y2) = (term12 x1 y2 x2 y1).
Proof. exact (EQ_MP (@lem1330563 x1 y2 x2 y1) (@lem1330562 x1 y2 x2 y1)). Qed.
Lemma lem1330647 (p1' : hreal) (p2 : hreal) (p1 : hreal) (p2' : hreal) : (term11 p1' p2' p1 p2) = (term12 p1' p2 p1 p2').
Proof. exact (@lem1330646 p1' p2 p1 p2'). Qed.
Lemma lem1330648 (p1' : hreal) (p2 : hreal) (p1 : hreal) (p2' : hreal) : (term45 p1' p2' p1 p2) = (term55 p1' p2 p1 p2').
Proof. exact (MK_COMB (@lem1330644 p1 p2' p1' p2) (@lem1330647 p1' p2 p1 p2')). Qed.
Lemma lem1330650 (y : hreal) (x : hreal) : (term3 y x) = True.
Proof. exact (EQ_MP (@lem1330551 y x) (@lem1330550 y x)). Qed.
Lemma lem1330651 (p1' : hreal) (p2 : hreal) (p1 : hreal) (p2' : hreal) : (term55 p1' p2 p1 p2') = True.
Proof. exact (@lem1330650 (hreal_add p1' p2) (hreal_add p1 p2')). Qed.
Lemma lem1330652 (p1' : hreal) (p2' : hreal) (p1 : hreal) (p2 : hreal) : (term45 p1' p2' p1 p2) = True.
Proof. exact (TRANS (@lem1330648 p1' p2 p1 p2') (@lem1330651 p1' p2 p1 p2')). Qed.
Lemma lem1330653 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term47 p1' p1 p2) = term56.
Proof. exact (fun_ext (fun p2' : hreal => @lem1330652 p1' p2' p1 p2)). Qed.
Lemma lem1330654 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330655 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term49 p1' p1 p2) = term57.
Proof. exact (MK_COMB (@lem1330654) (@lem1330653 p1' p1 p2)). Qed.
Lemma lem1330657 {A : Type'} (t : Prop) : (term58 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1330658 (t : Prop) : (term59 t) = t.
Proof. exact (@lem1330657 hreal t). Qed.
Lemma lem1330659 : term57 = True.
Proof. exact (@lem1330658 True). Qed.
Lemma lem1330660 (p1' : hreal) (p1 : hreal) (p2 : hreal) : (term49 p1' p1 p2) = True.
Proof. exact (TRANS (@lem1330655 p1' p1 p2) (@lem1330659)). Qed.
Lemma lem1330661 (p1 : hreal) (p2 : hreal) : (term51 p1 p2) = term56.
Proof. exact (fun_ext (fun p1' : hreal => @lem1330660 p1' p1 p2)). Qed.
Lemma lem1330662 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330663 (p1 : hreal) (p2 : hreal) : (term52 p1 p2) = term57.
Proof. exact (MK_COMB (@lem1330662) (@lem1330661 p1 p2)). Qed.
Lemma lem1330665 {A : Type'} (t : Prop) : (term58 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1330666 (t : Prop) : (term59 t) = t.
Proof. exact (@lem1330665 hreal t). Qed.
Lemma lem1330667 : term57 = True.
Proof. exact (@lem1330666 True). Qed.
Lemma lem1330668 (p1 : hreal) (p2 : hreal) : (term52 p1 p2) = True.
Proof. exact (TRANS (@lem1330663 p1 p2) (@lem1330667)). Qed.
Lemma lem1330669 (p1 : hreal) (p2 : hreal) : (term28 p1 p2) = True.
Proof. exact (TRANS (@lem1330625 p1 p2) (@lem1330668 p1 p2)). Qed.
Lemma lem1330670 (p1 : hreal) : (term30 p1) = term56.
Proof. exact (fun_ext (fun p2 : hreal => @lem1330669 p1 p2)). Qed.
Lemma lem1330671 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330672 (p1 : hreal) : (term32 p1) = term57.
Proof. exact (MK_COMB (@lem1330671) (@lem1330670 p1)). Qed.
Lemma lem1330674 {A : Type'} (t : Prop) : (term58 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1330675 (t : Prop) : (term59 t) = t.
Proof. exact (@lem1330674 hreal t). Qed.
Lemma lem1330676 : term57 = True.
Proof. exact (@lem1330675 True). Qed.
Lemma lem1330677 (p1 : hreal) : (term32 p1) = True.
Proof. exact (TRANS (@lem1330672 p1) (@lem1330676)). Qed.
Lemma lem1330678 : term34 = term56.
Proof. exact (fun_ext (fun p1 : hreal => @lem1330677 p1)). Qed.
Lemma lem1330679 : (@all hreal) = (@all hreal).
Proof. exact (eq_refl (@all hreal)). Qed.
Lemma lem1330680 : term35 = term57.
Proof. exact (MK_COMB (@lem1330679) (@lem1330678)). Qed.
Lemma lem1330682 {A : Type'} (t : Prop) : (term58 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1330683 (t : Prop) : (term59 t) = t.
Proof. exact (@lem1330682 hreal t). Qed.
Lemma lem1330684 : term57 = True.
Proof. exact (@lem1330683 True). Qed.
Lemma lem1330685 : term35 = True.
Proof. exact (TRANS (@lem1330680) (@lem1330684)). Qed.
Lemma lem1330686 : term24 = True.
Proof. exact (TRANS (@lem1330590) (@lem1330685)). Qed.
Lemma lem1330687 : True = term24.
Proof. exact (SYM (@lem1330686)). Qed.
Lemma lem1330688 : term24.
Proof. exact (EQ_MP (@lem1330687) (@lem0)). Qed.
