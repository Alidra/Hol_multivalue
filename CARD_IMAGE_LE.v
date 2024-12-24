Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_IMAGE_LE_term_abbrevs.
Require Import CARD_CLAUSES_spec.
Require Import FINITE_IMAGE_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import IMAGE_CLAUSES_spec.
Require Import INT_POS_spec.
Require Import LE_REFL_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm12653_spec.
Require Import thm13473_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367770_spec.
Require Import thm1367771_spec.
Require Import thm1386578_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1842_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm2318495_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm2841416_spec.
Require Import thm2841417_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Require Import thm996238_spec.
Lemma lem4004560 (n : nat) : term0 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem4004561 (n : nat) : (term0 n) = (Peano.le n n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem4004562 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem4004561 n) (@lem4004560 n)). Qed.
Lemma lem4004563 (n : nat) : (Peano.le n n) = ((Peano.le n n) = True).
Proof. exact (@lem7 (Peano.le n n)). Qed.
Lemma lem4004565 {A B : Type'} (f : A -> B) : term1 A B f.
Proof. exact (@lem3615104 A B f). Qed.
Lemma lem4004566 {A B : Type'} (f : A -> B) : (term1 A B f) = (term2 A B f).
Proof. exact (eq_refl (term1 A B f)). Qed.
Lemma lem4004567 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (EQ_MP (@lem4004566 A B f) (@lem4004565 A B f)). Qed.
Lemma lem4004568 {A B : Type'} (f : A -> B) (s : A -> Prop) : term3 A B f s.
Proof. exact (@lem4004567 A B f s). Qed.
Lemma lem4004569 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term3 A B f s) = (term4 A B f s).
Proof. exact (eq_refl (term3 A B f s)). Qed.
Lemma lem4004570 {A B : Type'} (f : A -> B) (s : A -> Prop) : term4 A B f s.
Proof. exact (EQ_MP (@lem4004569 A B f s) (@lem4004568 A B f s)). Qed.
Lemma lem4004571 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4004572 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term5 A B f s.
Proof. exact (@lem4004570 A B f s (@lem4004571 A s h1)). Qed.
Lemma lem4004573 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term5 A B f s) = ((term5 A B f s) = True).
Proof. exact (@lem7 (term5 A B f s)). Qed.
Lemma lem4004574 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term5 A B f s) = True.
Proof. exact (EQ_MP (@lem4004573 A B f s) (@lem4004572 A B f s h1)). Qed.
Lemma lem4004580 {A : Type'} : term6 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem4004581 {A : Type'} (x : A) : term7 A x.
Proof. exact (@lem4004580 A x). Qed.
Lemma lem4004582 {A : Type'} (x : A) : (term7 A x) = (term8 A x).
Proof. exact (eq_refl (term7 A x)). Qed.
Lemma lem4004583 {A : Type'} (x : A) : term8 A x.
Proof. exact (EQ_MP (@lem4004582 A x) (@lem4004581 A x)). Qed.
Lemma lem4004584 {A : Type'} (x : A) (s : A -> Prop) : term9 A x s.
Proof. exact (@lem4004583 A x s). Qed.
Lemma lem4004585 {A : Type'} (x : A) (s : A -> Prop) : (term9 A x s) = (term10 A x s).
Proof. exact (eq_refl (term9 A x s)). Qed.
Lemma lem4004586 {A : Type'} (x : A) (s : A -> Prop) : term10 A x s.
Proof. exact (EQ_MP (@lem4004585 A x s) (@lem4004584 A x s)). Qed.
Lemma lem4004587 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4004588 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term11 A x s) = (term12 A x s).
Proof. exact (@lem4004586 A x s (@lem4004587 A s h1)). Qed.
Lemma lem4004597 {A : Type'} (h1 : term13 A) : term13 A.
Proof. exact (h1). Qed.
Lemma lem4004598 {A : Type'} (P : type686 A) (h1 : term13 A) : term14 A P.
Proof. exact (@lem4004597 A h1 P). Qed.
Lemma lem4004599 {A : Type'} (P : type686 A) : (term14 A P) = (term15 A P).
Proof. exact (eq_refl (term14 A P)). Qed.
Lemma lem4004600 {A : Type'} (P : type686 A) (h1 : term13 A) : term15 A P.
Proof. exact (EQ_MP (@lem4004599 A P) (@lem4004598 A P h1)). Qed.
Lemma lem4004601 {A : Type'} (P : type686 A) (h1 : term16 A P) : term16 A P.
Proof. exact (h1). Qed.
Lemma lem4004602 {A : Type'} (P : type686 A) (h1 : term13 A) (h2 : term16 A P) : term17 A P.
Proof. exact (@lem4004600 A P h1 (@lem4004601 A P h2)). Qed.
Lemma lem4004603 {A : Type'} (P : type686 A) (h1 : term16 A P) : term18 A P.
Proof. exact (fun h0 : term13 A => @lem4004602 A P h0 h1). Qed.
Lemma lem4004604 {A : Type'} (h1 : term13 A) : term13 A.
Proof. exact (h1). Qed.
Lemma lem4004605 {A : Type'} (P : type686 A) (h1 : term13 A) (h2 : term16 A P) : term17 A P.
Proof. exact (@lem4004603 A P h2 (@lem4004604 A h1)). Qed.
Lemma lem4004606 {A : Type'} (P : type686 A) (h1 : term13 A) : term15 A P.
Proof. exact (fun h0 : term16 A P => @lem4004605 A P h1 h0). Qed.
Lemma lem4004607 {A : Type'} (h1 : term13 A) : term13 A.
Proof. exact (fun P : type686 A => @lem4004606 A P h1). Qed.
Lemma lem4004608 {A : Type'} : term19 A.
Proof. exact (fun h0 : term13 A => @lem4004607 A h0). Qed.
Lemma lem4004609 {A : Type'} : term13 A.
Proof. exact (@lem4004608 A (@lem3558722 A)). Qed.
Lemma lem4004610 {A : Type'} (P : type686 A) : term14 A P.
Proof. exact (@lem4004609 A P). Qed.
Lemma lem4004611 {A : Type'} (P : type686 A) : (term14 A P) = (term15 A P).
Proof. exact (eq_refl (term14 A P)). Qed.
Lemma lem4004614 {A : Type'} (P : type686 A) : term15 A P.
Proof. exact (EQ_MP (@lem4004611 A P) (@lem4004610 A P)). Qed.
Lemma lem4004615 {A : Type'} (P : type686 A) : term15 A P.
Proof. exact (@lem4004614 A P). Qed.
Lemma lem4004616 {A B : Type'} (f : A -> B) : term20 A B f.
Proof. exact (@lem4004615 A (term21 A B f)). Qed.
Lemma lem4004617 {A B : Type'} (f : A -> B) : (term22 A B f) = (term23 A B f).
Proof. exact (eq_refl (term22 A B f)). Qed.
Lemma lem4004618 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4004619 {A B : Type'} (f : A -> B) : (term24 A B f) = (term25 A B f).
Proof. exact (MK_COMB (@lem4004618) (@lem4004617 A B f)). Qed.
Lemma lem4004620 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term26 A B f s) = (term27 A B f s).
Proof. exact (eq_refl (term26 A B f s)). Qed.
Lemma lem4004621 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4004622 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term28 A B f s) = (term29 A B f s).
Proof. exact (MK_COMB (@lem4004621) (@lem4004620 A B f s)). Qed.
Lemma lem4004623 {A : Type'} (x : A) (s : A -> Prop) : (term30 A x s) = (term30 A x s).
Proof. exact (eq_refl (term30 A x s)). Qed.
Lemma lem4004624 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term31 A B f x s) = (term32 A B f x s).
Proof. exact (MK_COMB (@lem4004622 A B f s) (@lem4004623 A x s)). Qed.
Lemma lem4004625 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4004626 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term33 A B f x s) = (term34 A B f x s).
Proof. exact (MK_COMB (@lem4004625) (@lem4004624 A B f x s)). Qed.
Lemma lem4004627 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term35 A B f x s) = (term36 A B f x s).
Proof. exact (eq_refl (term35 A B f x s)). Qed.
Lemma lem4004628 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term37 A B f x s) = (term38 A B f x s).
Proof. exact (MK_COMB (@lem4004626 A B f x s) (@lem4004627 A B f x s)). Qed.
Lemma lem4004629 {A B : Type'} (f : A -> B) (x : A) : (term39 A B f x) = (term40 A B f x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4004628 A B f x s)). Qed.
Lemma lem4004630 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4004631 {A B : Type'} (f : A -> B) (x : A) : (term41 A B f x) = (term42 A B f x).
Proof. exact (MK_COMB (@lem4004630 A) (@lem4004629 A B f x)). Qed.
Lemma lem4004632 {A B : Type'} (f : A -> B) : (term43 A B f) = (term44 A B f).
Proof. exact (fun_ext (fun x : A => @lem4004631 A B f x)). Qed.
Lemma lem4004633 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4004634 {A B : Type'} (f : A -> B) : (term45 A B f) = (term46 A B f).
Proof. exact (MK_COMB (@lem4004633 A) (@lem4004632 A B f)). Qed.
Lemma lem4004635 {A B : Type'} (f : A -> B) : (term47 A B f) = (term48 A B f).
Proof. exact (MK_COMB (@lem4004619 A B f) (@lem4004634 A B f)). Qed.
Lemma lem4004636 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4004637 {A B : Type'} (f : A -> B) : (term49 A B f) = (term50 A B f).
Proof. exact (MK_COMB (@lem4004636) (@lem4004635 A B f)). Qed.
Lemma lem4004638 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term26 A B f s) = (term27 A B f s).
Proof. exact (eq_refl (term26 A B f s)). Qed.
Lemma lem4004639 {A : Type'} (s : A -> Prop) : (term51 A s) = (term51 A s).
Proof. exact (eq_refl (term51 A s)). Qed.
Lemma lem4004640 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term52 A B f s) = (term53 A B f s).
Proof. exact (MK_COMB (@lem4004639 A s) (@lem4004638 A B f s)). Qed.
Lemma lem4004641 {A B : Type'} (f : A -> B) : (term54 A B f) = (term55 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4004640 A B f s)). Qed.
Lemma lem4004642 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4004643 {A B : Type'} (f : A -> B) : (term56 A B f) = (term57 A B f).
Proof. exact (MK_COMB (@lem4004642 A) (@lem4004641 A B f)). Qed.
Lemma lem4004644 {A B : Type'} (f : A -> B) : (term20 A B f) = (term58 A B f).
Proof. exact (MK_COMB (@lem4004637 A B f) (@lem4004643 A B f)). Qed.
Lemma lem4004645 {A B : Type'} (f : A -> B) : term58 A B f.
Proof. exact (EQ_MP (@lem4004644 A B f) (@lem4004616 A B f)). Qed.
Lemma lem4004651 {_87477 _87481 : Type'} (f : _87477 -> _87481) : (@IMAGE _87477 _87481 f (@EMPTY _87477)) = (@EMPTY _87481).
Proof. exact (proj1 (@lem3366870 _87477 _87481 (@el _87477) f (@el (_87477 -> Prop)))). Qed.
Lemma lem4004652 {A B : Type'} (f : A -> B) : (@IMAGE A B f (@EMPTY A)) = (@EMPTY B).
Proof. exact (@lem4004651 A B f). Qed.
Lemma lem4004653 {B : Type'} : (@CARD B) = (@CARD B).
Proof. exact (eq_refl (@CARD B)). Qed.
Lemma lem4004654 {A B : Type'} (f : A -> B) : (term59 A B f) = (@CARD B (@EMPTY B)).
Proof. exact (MK_COMB (@lem4004653 B) (@lem4004652 A B f)). Qed.
Lemma lem4004656 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem4004657 {B : Type'} : (@CARD B (@EMPTY B)) = (NUMERAL 0).
Proof. exact (@lem4004656 B). Qed.
Lemma lem4004658 {A B : Type'} (f : A -> B) : (term59 A B f) = (NUMERAL 0).
Proof. exact (TRANS (@lem4004654 A B f) (@lem4004657 B)). Qed.
Lemma lem4004659 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem4004660 {A B : Type'} (f : A -> B) : (term60 A B f) = term61.
Proof. exact (MK_COMB (@lem4004659) (@lem4004658 A B f)). Qed.
Lemma lem4004662 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem4004663 {A B : Type'} (f : A -> B) : (term23 A B f) = term62.
Proof. exact (MK_COMB (@lem4004660 A B f) (@lem4004662 A)). Qed.
Lemma lem4004665 (n : nat) : (Peano.le n n) = True.
Proof. exact (EQ_MP (@lem4004563 n) (@lem4004562 n)). Qed.
Lemma lem4004666 : term62 = True.
Proof. exact (@lem4004665 (NUMERAL 0)). Qed.
Lemma lem4004667 {A B : Type'} (f : A -> B) : (term23 A B f) = True.
Proof. exact (TRANS (@lem4004663 A B f) (@lem4004666)). Qed.
Lemma lem4004668 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4004669 {A B : Type'} (f : A -> B) : (term25 A B f) = (and True).
Proof. exact (MK_COMB (@lem4004668) (@lem4004667 A B f)). Qed.
Lemma lem4004681 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term63 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4004682 (p : Prop) (q : Prop) (p' : Prop) : term64 p q p'.
Proof. exact (fun q' : Prop => @lem4004681 p q p' q'). Qed.
Lemma lem4004683 (p : Prop) (q : Prop) : term65 p q.
Proof. exact (fun p' : Prop => @lem4004682 p q p'). Qed.
Lemma lem4004684 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : term66 A B f x s.
Proof. exact (@lem4004683 (term32 A B f x s) (term36 A B f x s)). Qed.
Lemma lem4004685 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (p' : Prop) : term67 A B f x s p'.
Proof. exact (@lem4004684 A B f x s p'). Qed.
Lemma lem4004686 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (p' : Prop) : (term67 A B f x s p') = (term68 A B f x s p').
Proof. exact (eq_refl (term67 A B f x s p')). Qed.
Lemma lem4004687 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (p' : Prop) : term68 A B f x s p'.
Proof. exact (EQ_MP (@lem4004686 A B f x s p') (@lem4004685 A B f x s p')). Qed.
Lemma lem4004688 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term69 A B f x s p' q'.
Proof. exact (@lem4004687 A B f x s p' q'). Qed.
Lemma lem4004689 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : (term69 A B f x s p' q') = (term70 A B f x s p' q').
Proof. exact (eq_refl (term69 A B f x s p' q')). Qed.
Lemma lem4004690 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (p' : Prop) (q' : Prop) : term70 A B f x s p' q'.
Proof. exact (EQ_MP (@lem4004689 A B f x s p' q') (@lem4004688 A B f x s p' q')). Qed.
Lemma lem4004697 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) : (term32 A B f x s) = (term32 A B f x s).
Proof. exact (eq_refl (term32 A B f x s)). Qed.
Lemma lem4004698 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (q' : Prop) : term71 A B f x s q'.
Proof. exact (@lem4004690 A B f x s (term32 A B f x s) q'). Qed.
Lemma lem4004699 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (q' : Prop) : term72 A B f x s q'.
Proof. exact (@lem4004698 A B f x s q' (@lem4004697 A B f x s)). Qed.
Lemma lem4004700 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : term32 A B f x s.
Proof. exact (h1). Qed.
Lemma lem4004701 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : term30 A x s.
Proof. exact (proj2 (@lem4004700 A B f x s h1)). Qed.
Lemma lem4004702 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : @FINITE A s.
Proof. exact (proj2 (@lem4004701 A B f x s h1)). Qed.
Lemma lem4004703 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem4004705 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : term73 A x s.
Proof. exact (proj1 (@lem4004701 A B f x s h1)). Qed.
Lemma lem4004706 {A : Type'} (x : A) (s : A -> Prop) : term74 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem4004714 {_87477 _87481 : Type'} (x : _87477) (f : _87477 -> _87481) (s : _87477 -> Prop) : (term75 _87477 _87481 f x s) = (term76 _87477 _87481 x f s).
Proof. exact (proj2 (@lem3366870 _87477 _87481 x f s)). Qed.
Lemma lem4004715 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term75 A B f x s) = (term76 A B x f s).
Proof. exact (@lem4004714 A B x f s). Qed.
Lemma lem4004716 {B : Type'} : (@CARD B) = (@CARD B).
Proof. exact (eq_refl (@CARD B)). Qed.
Lemma lem4004717 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term77 A B f x s) = (term78 A B x f s).
Proof. exact (MK_COMB (@lem4004716 B) (@lem4004715 A B x f s)). Qed.
Lemma lem4004719 {A : Type'} (x : A) (s : A -> Prop) : term10 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem4004588 A x s h0). Qed.
Lemma lem4004720 {B : Type'} (x : B) (s : B -> Prop) : term10 B x s.
Proof. exact (@lem4004719 B x s). Qed.
Lemma lem4004721 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term79 A B x f s.
Proof. exact (@lem4004720 B (f x) (@IMAGE A B f s)). Qed.
Lemma lem4004723 {A B : Type'} (f : A -> B) (s : A -> Prop) : term80 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem4004574 A B f s h0). Qed.
Lemma lem4004724 {A B : Type'} (f : A -> B) (s : A -> Prop) : term80 A B f s.
Proof. exact (@lem4004723 A B f s). Qed.
Lemma lem4004726 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem4004703 A s) (@lem4004702 A B f x s h1)). Qed.
Lemma lem4004727 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : True = (@FINITE A s).
Proof. exact (SYM (@lem4004726 A B f x s h1)). Qed.
Lemma lem4004728 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : @FINITE A s.
Proof. exact (EQ_MP (@lem4004727 A B f x s h1) (@lem0)). Qed.
Lemma lem4004729 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : (term5 A B f s) = True.
Proof. exact (@lem4004724 A B f s (@lem4004728 A B f x s h1)). Qed.
Lemma lem4004730 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : True = (term5 A B f s).
Proof. exact (SYM (@lem4004729 A B f x s h1)). Qed.
Lemma lem4004731 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : term5 A B f s.
Proof. exact (EQ_MP (@lem4004730 A B f x s h1) (@lem0)). Qed.
Lemma lem4004732 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : (term78 A B x f s) = (term81 A B x f s).
Proof. exact (@lem4004721 A B x f s (@lem4004731 A B f x s h1)). Qed.
Lemma lem4004766 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : (term77 A B f x s) = (term81 A B x f s).
Proof. exact (TRANS (@lem4004717 A B x f s) (@lem4004732 A B f x s h1)). Qed.
Lemma lem4004767 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem4004768 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : (term82 A B f x s) = (term83 A B x f s).
Proof. exact (MK_COMB (@lem4004767) (@lem4004766 A B f x s h1)). Qed.
Lemma lem4004803 {A : Type'} (x : A) (s : A -> Prop) : term10 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem4004588 A x s h0). Qed.
Lemma lem4004804 {A : Type'} (x : A) (s : A -> Prop) : term10 A x s.
Proof. exact (@lem4004803 A x s). Qed.
Lemma lem4004806 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem4004703 A s) (@lem4004702 A B f x s h1)). Qed.
Lemma lem4004807 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : True = (@FINITE A s).
Proof. exact (SYM (@lem4004806 A B f x s h1)). Qed.
Lemma lem4004808 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : @FINITE A s.
Proof. exact (EQ_MP (@lem4004807 A B f x s h1) (@lem0)). Qed.
Lemma lem4004809 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : (term11 A x s) = (term12 A x s).
Proof. exact (@lem4004804 A x s (@lem4004808 A B f x s h1)). Qed.
Lemma lem4004811 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term84 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem4004812 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term85 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem4004811 _2963 g t e g' t' e'). Qed.
Lemma lem4004813 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term86 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem4004812 _2963 g t e g' t'). Qed.
Lemma lem4004814 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term87 _2963 g t e.
Proof. exact (fun g' : Prop => @lem4004813 _2963 g t e g'). Qed.
Lemma lem4004815 (g : Prop) (t : nat) (e : nat) : term88 g t e.
Proof. exact (@lem4004814 nat g t e). Qed.
Lemma lem4004816 {A : Type'} (x : A) (s : A -> Prop) : term89 A x s.
Proof. exact (@lem4004815 (@IN A x s) (@CARD A s) (term90 A s)). Qed.
Lemma lem4004817 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) : term91 A x s g'.
Proof. exact (@lem4004816 A x s g'). Qed.
Lemma lem4004818 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) : (term91 A x s g') = (term92 A x s g').
Proof. exact (eq_refl (term91 A x s g')). Qed.
Lemma lem4004819 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) : term92 A x s g'.
Proof. exact (EQ_MP (@lem4004818 A x s g') (@lem4004817 A x s g')). Qed.
Lemma lem4004820 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) : term93 A x s g' t'.
Proof. exact (@lem4004819 A x s g' t'). Qed.
Lemma lem4004821 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) : (term93 A x s g' t') = (term94 A x s g' t').
Proof. exact (eq_refl (term93 A x s g' t')). Qed.
Lemma lem4004822 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) : term94 A x s g' t'.
Proof. exact (EQ_MP (@lem4004821 A x s g' t') (@lem4004820 A x s g' t')). Qed.
Lemma lem4004823 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term95 A x s g' t' e'.
Proof. exact (@lem4004822 A x s g' t' e'). Qed.
Lemma lem4004824 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : (term95 A x s g' t' e') = (term96 A x s g' t' e').
Proof. exact (eq_refl (term95 A x s g' t' e')). Qed.
Lemma lem4004825 {A : Type'} (x : A) (s : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term96 A x s g' t' e'.
Proof. exact (EQ_MP (@lem4004824 A x s g' t' e') (@lem4004823 A x s g' t' e')). Qed.
Lemma lem4004827 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : (@IN A x s) = False.
Proof. exact (@lem4004706 A x s (@lem4004705 A B f x s h1)). Qed.
Lemma lem4004828 {A : Type'} (x : A) (s : A -> Prop) (t' : nat) (e' : nat) : term97 A x s t' e'.
Proof. exact (@lem4004825 A x s False t' e'). Qed.
Lemma lem4004829 {A B : Type'} (t' : nat) (e' : nat) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : term98 A x s t' e'.
Proof. exact (@lem4004828 A x s t' e' (@lem4004827 A B f x s h1)). Qed.
Lemma lem4004833 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@CARD A s).
Proof. exact (eq_refl (@CARD A s)). Qed.
Lemma lem4004834 {A : Type'} (s : A -> Prop) : term99 A s.
Proof. exact (fun h0 : False => @lem4004833 A s). Qed.
Lemma lem4004835 {A B : Type'} (e' : nat) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : term100 A x s e'.
Proof. exact (@lem4004829 A B (@CARD A s) e' f x s h1). Qed.
Lemma lem4004836 {A B : Type'} (e' : nat) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : term101 A x s e'.
Proof. exact (@lem4004835 A B e' f x s h1 (@lem4004834 A s)). Qed.
Lemma lem4004842 {A : Type'} (s : A -> Prop) : (term90 A s) = (term90 A s).
Proof. exact (eq_refl (term90 A s)). Qed.
Lemma lem4004843 {A : Type'} (s : A -> Prop) : term102 A s.
Proof. exact (fun h0 : ~ False => @lem4004842 A s). Qed.
Lemma lem4004844 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : term103 A x s.
Proof. exact (@lem4004836 A B (term90 A s) f x s h1). Qed.
Lemma lem4004845 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : (term12 A x s) = (term104 A s).
Proof. exact (@lem4004844 A B f x s h1 (@lem4004843 A s)). Qed.
Lemma lem4004847 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4004848 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem4004847 nat t1 t2). Qed.
Lemma lem4004849 {A : Type'} (s : A -> Prop) : (term104 A s) = (term90 A s).
Proof. exact (@lem4004848 (@CARD A s) (term90 A s)). Qed.
Lemma lem4004850 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : (term12 A x s) = (term90 A s).
Proof. exact (TRANS (@lem4004845 A B f x s h1) (@lem4004849 A s)). Qed.
Lemma lem4004851 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : (term11 A x s) = (term90 A s).
Proof. exact (TRANS (@lem4004809 A B f x s h1) (@lem4004850 A B f x s h1)). Qed.
Lemma lem4004852 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : (term36 A B f x s) = (term105 A B x f s).
Proof. exact (MK_COMB (@lem4004768 A B f x s h1) (@lem4004851 A B f x s h1)). Qed.
Lemma lem4004888 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term106 A B x f s.
Proof. exact (fun h0 : term32 A B f x s => @lem4004852 A B f x s h0). Qed.
Lemma lem4004889 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term107 A B x f s.
Proof. exact (@lem4004699 A B f x s (term105 A B x f s)). Qed.
Lemma lem4004890 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term38 A B f x s) = (term108 A B x f s).
Proof. exact (@lem4004889 A B x f s (@lem4004888 A B x f s)). Qed.
Lemma lem4005004 {A B : Type'} (x : A) (f : A -> B) : (term40 A B f x) = (term109 A B x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4004890 A B x f s)). Qed.
Lemma lem4005118 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4005119 {A B : Type'} (x : A) (f : A -> B) : (term42 A B f x) = (term110 A B x f).
Proof. exact (MK_COMB (@lem4005118 A) (@lem4005004 A B x f)). Qed.
Lemma lem4005237 {A B : Type'} (f : A -> B) : (term44 A B f) = (term111 A B f).
Proof. exact (fun_ext (fun x : A => @lem4005119 A B x f)). Qed.
Lemma lem4005355 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4005356 {A B : Type'} (f : A -> B) : (term46 A B f) = (term112 A B f).
Proof. exact (MK_COMB (@lem4005355 A) (@lem4005237 A B f)). Qed.
Lemma lem4005478 {A B : Type'} (f : A -> B) : (term48 A B f) = (term113 A B f).
Proof. exact (MK_COMB (@lem4004669 A B f) (@lem4005356 A B f)). Qed.
Lemma lem4005480 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4005481 {A B : Type'} (f : A -> B) : (term113 A B f) = (term112 A B f).
Proof. exact (@lem4005480 (term112 A B f)). Qed.
Lemma lem4005603 {A B : Type'} (f : A -> B) : (term48 A B f) = (term112 A B f).
Proof. exact (TRANS (@lem4005478 A B f) (@lem4005481 A B f)). Qed.
Lemma lem4005604 {A B : Type'} (f : A -> B) : (term112 A B f) = (term48 A B f).
Proof. exact (SYM (@lem4005603 A B f)). Qed.
Lemma lem4005605 (_474 : nat) (_475 : Prop) (_476 : nat -> Prop) (_477 : nat) : (term114 _476 _475 _474 _477) = (term115 _474 _475 _476 _477).
Proof. exact (@lem13473 nat _474 _475 _476 _477). Qed.
Lemma lem4005606 {A B : Type'} (_474 : nat) (_475 : Prop) (f : A -> B) (x : A) (s : A -> Prop) (_477 : nat) : (term116 A B f x s _475 _474 _477) = (term117 A B _474 _475 f x s _477).
Proof. exact (@lem4005605 _474 _475 (term118 A B f x s) _477). Qed.
Lemma lem4005607 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term119 A B x f s) = (term120 A B x f s).
Proof. exact (@lem4005606 A B (term121 A B f s) (term122 A B x f s) f x s (term123 A B f s)). Qed.
Lemma lem4005608 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term124 A B x f s) = (term125 A B x f s).
Proof. exact (eq_refl (term124 A B x f s)). Qed.
Lemma lem4005609 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term126 A B x f s) = (term126 A B x f s).
Proof. exact (eq_refl (term126 A B x f s)). Qed.
Lemma lem4005610 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term127 A B x f s) = (term128 A B x f s).
Proof. exact (MK_COMB (@lem4005609 A B x f s) (@lem4005608 A B x f s)). Qed.
Lemma lem4005611 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term129 A B x f s) = (term130 A B x f s).
Proof. exact (eq_refl (term129 A B x f s)). Qed.
Lemma lem4005612 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term131 A B x f s) = (term131 A B x f s).
Proof. exact (eq_refl (term131 A B x f s)). Qed.
Lemma lem4005613 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term132 A B x f s) = (term133 A B x f s).
Proof. exact (MK_COMB (@lem4005612 A B x f s) (@lem4005611 A B x f s)). Qed.
Lemma lem4005614 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4005615 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term134 A B x f s) = (term135 A B x f s).
Proof. exact (MK_COMB (@lem4005614) (@lem4005613 A B x f s)). Qed.
Lemma lem4005616 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term120 A B x f s) = (term136 A B x f s).
Proof. exact (MK_COMB (@lem4005615 A B x f s) (@lem4005610 A B x f s)). Qed.
Lemma lem4005617 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term119 A B x f s) = (term108 A B x f s).
Proof. exact (eq_refl (term119 A B x f s)). Qed.
Lemma lem4005618 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4005619 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term137 A B x f s) = (term138 A B x f s).
Proof. exact (MK_COMB (@lem4005618) (@lem4005617 A B x f s)). Qed.
Lemma lem4005620 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : ((term119 A B x f s) = (term120 A B x f s)) = ((term108 A B x f s) = (term136 A B x f s)).
Proof. exact (MK_COMB (@lem4005619 A B x f s) (@lem4005616 A B x f s)). Qed.
Lemma lem4005621 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term108 A B x f s) = (term136 A B x f s).
Proof. exact (EQ_MP (@lem4005620 A B x f s) (@lem4005607 A B x f s)). Qed.
Lemma lem4005622 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : (term136 A B x f s) = (term108 A B x f s).
Proof. exact (SYM (@lem4005621 A B x f s)). Qed.
Lemma lem4005657 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : term32 A B f x s.
Proof. exact (h1). Qed.
Lemma lem4005658 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : term27 A B f s.
Proof. exact (proj1 (@lem4005657 A B f x s h1)). Qed.
Lemma lem4005659 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : term32 A B f x s.
Proof. exact (h1). Qed.
Lemma lem4005660 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : term27 A B f s.
Proof. exact (proj1 (@lem4005659 A B f x s h1)). Qed.
Lemma lem4005685 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term139 A B f s) = (term140 A B f s).
Proof. exact (@lem17265 (term27 A B f s) (term141 A B f s)). Qed.
Lemma lem4005687 (m : nat) : (S m) = (term142 m).
Proof. exact (EQ_MP (@lem2841417 m) (@lem2841416 m)). Qed.
Lemma lem4005688 {A : Type'} (s : A -> Prop) : (term90 A s) = (term143 A s).
Proof. exact (@lem4005687 (@CARD A s)). Qed.
Lemma lem4005689 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term144 A B f s) = (term144 A B f s).
Proof. exact (eq_refl (term144 A B f s)). Qed.
Lemma lem4005690 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term141 A B f s) = (term145 A B f s).
Proof. exact (MK_COMB (@lem4005689 A B f s) (@lem4005688 A s)). Qed.
Lemma lem4005691 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term146 A B f s) = (term146 A B f s).
Proof. exact (eq_refl (term146 A B f s)). Qed.
Lemma lem4005692 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term140 A B f s) = (term147 A B f s).
Proof. exact (MK_COMB (@lem4005691 A B f s) (@lem4005690 A B f s)). Qed.
Lemma lem4005717 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term139 A B f s) = (term147 A B f s).
Proof. exact (TRANS (@lem4005685 A B f s) (@lem4005692 A B f s)). Qed.
Lemma lem4005719 (m : nat) (n : nat) : (Peano.le m n) = (term148 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem4005720 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term27 A B f s) = (term149 A B f s).
Proof. exact (@lem4005719 (term121 A B f s) (@CARD A s)). Qed.
Lemma lem4005721 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4005722 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term150 A B f s) = (term151 A B f s).
Proof. exact (MK_COMB (@lem4005721) (@lem4005720 A B f s)). Qed.
Lemma lem4005723 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4005724 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term146 A B f s) = (term152 A B f s).
Proof. exact (MK_COMB (@lem4005723) (@lem4005722 A B f s)). Qed.
Lemma lem4005726 (m : nat) (n : nat) : (Peano.le m n) = (term148 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem4005727 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term145 A B f s) = (term153 A B f s).
Proof. exact (@lem4005726 (term121 A B f s) (term143 A s)). Qed.
Lemma lem4005729 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem4005730 {A : Type'} (s : A -> Prop) : (term156 A s) = (term157 A s).
Proof. exact (@lem4005729 (@CARD A s) term158). Qed.
Lemma lem4005731 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term159 A B f s) = (term159 A B f s).
Proof. exact (eq_refl (term159 A B f s)). Qed.
Lemma lem4005732 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term153 A B f s) = (term160 A B f s).
Proof. exact (MK_COMB (@lem4005731 A B f s) (@lem4005730 A s)). Qed.
Lemma lem4005733 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term145 A B f s) = (term160 A B f s).
Proof. exact (TRANS (@lem4005727 A B f s) (@lem4005732 A B f s)). Qed.
Lemma lem4005734 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term147 A B f s) = (term161 A B f s).
Proof. exact (MK_COMB (@lem4005724 A B f s) (@lem4005733 A B f s)). Qed.
Lemma lem4005735 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term139 A B f s) = (term161 A B f s).
Proof. exact (TRANS (@lem4005717 A B f s) (@lem4005734 A B f s)). Qed.
Lemma lem4005736 {A : Type'} (s : A -> Prop) : term162 A s.
Proof. exact (@lem2307535 (@CARD A s)). Qed.
Lemma lem4005737 {A : Type'} (s : A -> Prop) : (term162 A s) = (term163 A s).
Proof. exact (eq_refl (term162 A s)). Qed.
Lemma lem4005738 {A : Type'} (s : A -> Prop) : term163 A s.
Proof. exact (EQ_MP (@lem4005737 A s) (@lem4005736 A s)). Qed.
Lemma lem4005739 {A B : Type'} (f : A -> B) (s : A -> Prop) : term164 A B f s.
Proof. exact (@lem2307535 (term121 A B f s)). Qed.
Lemma lem4005740 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term164 A B f s) = (term165 A B f s).
Proof. exact (eq_refl (term164 A B f s)). Qed.
Lemma lem4005741 {A B : Type'} (f : A -> B) (s : A -> Prop) : term165 A B f s.
Proof. exact (EQ_MP (@lem4005740 A B f s) (@lem4005739 A B f s)). Qed.
Lemma lem4005742 (_46263 : int) (_46262 : int) : (term166 _46263 _46262) = (term167 _46263 _46262).
Proof. exact (@lem2318604 (term167 _46263 _46262)). Qed.
Lemma lem4005758 (_46263 : int) (_46262 : int) : (term168 _46263 _46262) = (int_le _46263 _46262).
Proof. exact (@lem16933 (int_le _46263 _46262)). Qed.
Lemma lem4005759 (_46263 : int) (_46262 : int) : (term169 _46263 _46262) = (term169 _46263 _46262).
Proof. exact (eq_refl (term169 _46263 _46262)). Qed.
Lemma lem4005760 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4005761 (_46263 : int) (_46262 : int) : (term170 _46263 _46262) = (term171 _46263 _46262).
Proof. exact (MK_COMB (@lem4005760) (@lem4005758 _46263 _46262)). Qed.
Lemma lem4005762 (_46263 : int) (_46262 : int) : (term172 _46263 _46262) = (term173 _46263 _46262).
Proof. exact (MK_COMB (@lem4005761 _46263 _46262) (@lem4005759 _46263 _46262)). Qed.
Lemma lem4005763 (_46263 : int) (_46262 : int) : (term174 _46263 _46262) = (term172 _46263 _46262).
Proof. exact (@lem17160 (term175 _46263 _46262) (term176 _46263 _46262)). Qed.
Lemma lem4005764 (_46263 : int) (_46262 : int) : (term174 _46263 _46262) = (term173 _46263 _46262).
Proof. exact (TRANS (@lem4005763 _46263 _46262) (@lem4005762 _46263 _46262)). Qed.
Lemma lem4005766 (_46263 : int) : (term177 _46263) = (term177 _46263).
Proof. exact (eq_refl (term177 _46263)). Qed.
Lemma lem4005767 (_46263 : int) (_46262 : int) : (term178 _46263 _46262) = (term179 _46263 _46262).
Proof. exact (MK_COMB (@lem4005766 _46263) (@lem4005764 _46263 _46262)). Qed.
Lemma lem4005768 (_46263 : int) (_46262 : int) : (term180 _46263 _46262) = (term178 _46263 _46262).
Proof. exact (@lem17362 (term181 _46263) (term182 _46263 _46262)). Qed.
Lemma lem4005769 (_46263 : int) (_46262 : int) : (term180 _46263 _46262) = (term179 _46263 _46262).
Proof. exact (TRANS (@lem4005768 _46263 _46262) (@lem4005767 _46263 _46262)). Qed.
Lemma lem4005771 (_46262 : int) : (term177 _46262) = (term177 _46262).
Proof. exact (eq_refl (term177 _46262)). Qed.
Lemma lem4005772 (_46263 : int) (_46262 : int) : (term183 _46263 _46262) = (term184 _46263 _46262).
Proof. exact (MK_COMB (@lem4005771 _46262) (@lem4005769 _46263 _46262)). Qed.
Lemma lem4005773 (_46263 : int) (_46262 : int) : (term185 _46263 _46262) = (term183 _46263 _46262).
Proof. exact (@lem17362 (term181 _46262) (term186 _46263 _46262)). Qed.
Lemma lem4005791 (_46263 : int) (_46262 : int) : (term185 _46263 _46262) = (term184 _46263 _46262).
Proof. exact (TRANS (@lem4005773 _46263 _46262) (@lem4005772 _46263 _46262)). Qed.
Lemma lem4005794 (x : int) (y : int) : (int_le x y) = (term187 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4005795 (_46262 : int) : (term181 _46262) = (term188 _46262).
Proof. exact (@lem4005794 term189 _46262). Qed.
Lemma lem4005797 (n : nat) : (term190 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4005798 : term191 = term192.
Proof. exact (@lem4005797 (NUMERAL 0)). Qed.
Lemma lem4005799 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4005800 : term193 = term194.
Proof. exact (MK_COMB (@lem4005799) (@lem4005798)). Qed.
Lemma lem4005801 (_46262 : int) : (real_of_int _46262) = (real_of_int _46262).
Proof. exact (eq_refl (real_of_int _46262)). Qed.
Lemma lem4005802 (_46262 : int) : (term188 _46262) = (term195 _46262).
Proof. exact (MK_COMB (@lem4005800) (@lem4005801 _46262)). Qed.
Lemma lem4005804 (_46262 : int) : (term181 _46262) = (term195 _46262).
Proof. exact (TRANS (@lem4005795 _46262) (@lem4005802 _46262)). Qed.
Lemma lem4005807 (x : int) (y : int) : (int_le x y) = (term187 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4005808 (_46263 : int) : (term181 _46263) = (term188 _46263).
Proof. exact (@lem4005807 term189 _46263). Qed.
Lemma lem4005810 (n : nat) : (term190 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4005811 : term191 = term192.
Proof. exact (@lem4005810 (NUMERAL 0)). Qed.
Lemma lem4005812 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4005813 : term193 = term194.
Proof. exact (MK_COMB (@lem4005812) (@lem4005811)). Qed.
Lemma lem4005814 (_46263 : int) : (real_of_int _46263) = (real_of_int _46263).
Proof. exact (eq_refl (real_of_int _46263)). Qed.
Lemma lem4005815 (_46263 : int) : (term188 _46263) = (term195 _46263).
Proof. exact (MK_COMB (@lem4005813) (@lem4005814 _46263)). Qed.
Lemma lem4005817 (_46263 : int) : (term181 _46263) = (term195 _46263).
Proof. exact (TRANS (@lem4005808 _46263) (@lem4005815 _46263)). Qed.
Lemma lem4005820 (x : int) (y : int) : (int_le x y) = (term187 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4005822 (_46263 : int) (_46262 : int) : (int_le _46263 _46262) = (term187 _46263 _46262).
Proof. exact (@lem4005820 _46263 _46262). Qed.
Lemma lem4005824 (y : int) (x : int) : (term175 x y) = (term196 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem4005825 (_46262 : int) (_46263 : int) : (term169 _46263 _46262) = (term197 _46262 _46263).
Proof. exact (@lem4005824 (term198 _46262) _46263). Qed.
Lemma lem4005827 (x : int) (y : int) : (int_le x y) = (term187 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4005828 (_46262 : int) (_46263 : int) : (term197 _46262 _46263) = (term199 _46262 _46263).
Proof. exact (@lem4005827 (term200 _46262) _46263). Qed.
Lemma lem4005830 (x : int) (y : int) : (term201 x y) = (term202 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem4005831 (_46262 : int) : (term203 _46262) = (term204 _46262).
Proof. exact (@lem4005830 (term198 _46262) term205). Qed.
Lemma lem4005833 (x : int) (y : int) : (term201 x y) = (term202 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem4005834 (_46262 : int) : (term206 _46262) = (term207 _46262).
Proof. exact (@lem4005833 _46262 term205). Qed.
Lemma lem4005836 (n : nat) : (term190 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4005837 : term208 = term209.
Proof. exact (@lem4005836 term158). Qed.
Lemma lem4005838 (_46262 : int) : (term210 _46262) = (term210 _46262).
Proof. exact (eq_refl (term210 _46262)). Qed.
Lemma lem4005839 (_46262 : int) : (term207 _46262) = (term211 _46262).
Proof. exact (MK_COMB (@lem4005838 _46262) (@lem4005837)). Qed.
Lemma lem4005840 (_46262 : int) : (term206 _46262) = (term211 _46262).
Proof. exact (TRANS (@lem4005834 _46262) (@lem4005839 _46262)). Qed.
Lemma lem4005841 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4005842 (_46262 : int) : (term212 _46262) = (term213 _46262).
Proof. exact (MK_COMB (@lem4005841) (@lem4005840 _46262)). Qed.
Lemma lem4005844 (n : nat) : (term190 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4005845 : term208 = term209.
Proof. exact (@lem4005844 term158). Qed.
Lemma lem4005846 (_46262 : int) : (term204 _46262) = (term214 _46262).
Proof. exact (MK_COMB (@lem4005842 _46262) (@lem4005845)). Qed.
Lemma lem4005847 (_46262 : int) : (term203 _46262) = (term214 _46262).
Proof. exact (TRANS (@lem4005831 _46262) (@lem4005846 _46262)). Qed.
Lemma lem4005848 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4005849 (_46262 : int) : (term215 _46262) = (term216 _46262).
Proof. exact (MK_COMB (@lem4005848) (@lem4005847 _46262)). Qed.
Lemma lem4005850 (_46263 : int) : (real_of_int _46263) = (real_of_int _46263).
Proof. exact (eq_refl (real_of_int _46263)). Qed.
Lemma lem4005851 (_46262 : int) (_46263 : int) : (term199 _46262 _46263) = (term217 _46262 _46263).
Proof. exact (MK_COMB (@lem4005849 _46262) (@lem4005850 _46263)). Qed.
Lemma lem4005852 (_46262 : int) (_46263 : int) : (term197 _46262 _46263) = (term217 _46262 _46263).
Proof. exact (TRANS (@lem4005828 _46262 _46263) (@lem4005851 _46262 _46263)). Qed.
Lemma lem4005853 (_46262 : int) (_46263 : int) : (term169 _46263 _46262) = (term217 _46262 _46263).
Proof. exact (TRANS (@lem4005825 _46262 _46263) (@lem4005852 _46262 _46263)). Qed.
Lemma lem4005854 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4005855 (_46263 : int) (_46262 : int) : (term171 _46263 _46262) = (term218 _46263 _46262).
Proof. exact (MK_COMB (@lem4005854) (@lem4005822 _46263 _46262)). Qed.
Lemma lem4005856 (_46262 : int) (_46263 : int) : (term173 _46263 _46262) = (term219 _46262 _46263).
Proof. exact (MK_COMB (@lem4005855 _46263 _46262) (@lem4005853 _46262 _46263)). Qed.
Lemma lem4005857 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4005858 (_46263 : int) : (term177 _46263) = (term220 _46263).
Proof. exact (MK_COMB (@lem4005857) (@lem4005817 _46263)). Qed.
Lemma lem4005859 (_46262 : int) (_46263 : int) : (term179 _46263 _46262) = (term221 _46262 _46263).
Proof. exact (MK_COMB (@lem4005858 _46263) (@lem4005856 _46262 _46263)). Qed.
Lemma lem4005860 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4005861 (_46262 : int) : (term177 _46262) = (term220 _46262).
Proof. exact (MK_COMB (@lem4005860) (@lem4005804 _46262)). Qed.
Lemma lem4005862 (_46262 : int) (_46263 : int) : (term184 _46263 _46262) = (term222 _46262 _46263).
Proof. exact (MK_COMB (@lem4005861 _46262) (@lem4005859 _46262 _46263)). Qed.
Lemma lem4005863 (_46262 : int) (_46263 : int) : (term185 _46263 _46262) = (term222 _46262 _46263).
Proof. exact (TRANS (@lem4005791 _46263 _46262) (@lem4005862 _46262 _46263)). Qed.
Lemma lem4005867 (t : Prop) : (term223 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4005903 (_46262 : int) (_46263 : int) : (term224 _46262 _46263) = (term222 _46262 _46263).
Proof. exact (@lem4005867 (term222 _46262 _46263)). Qed.
Lemma lem4005904 (_46262 : int) : (term195 _46262) = (term225 _46262).
Proof. exact (@lem1988287 (real_of_int _46262) term192). Qed.
Lemma lem4005910 (_46262 : int) : (term226 _46262) = (term227 _46262).
Proof. exact (@lem1982792 (real_of_int _46262) term192). Qed.
Lemma lem4005912 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4005913 : term192 = term229.
Proof. exact (@lem4005912 (NUMERAL 0)). Qed.
Lemma lem4005915 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4005916 : term232 = term233.
Proof. exact (@lem4005915 term158). Qed.
Lemma lem4005917 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4005918 : term234 = term235.
Proof. exact (MK_COMB (@lem4005917) (@lem4005916)). Qed.
Lemma lem4005919 : term236 = term237.
Proof. exact (MK_COMB (@lem4005918) (@lem4005913)). Qed.
Lemma lem4005920 : term237 = term238.
Proof. exact (@lem1981613 term232 term192 term209 term209). Qed.
Lemma lem4005922 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4005923 : term241 = term242.
Proof. exact (@lem4005922 term158 term158). Qed.
Lemma lem4005924 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4005925 : term244 = term158.
Proof. exact (EQ_MP (@lem4005924) (@lem940073)). Qed.
Lemma lem4005926 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4005927 : term242 = term209.
Proof. exact (MK_COMB (@lem4005926) (@lem4005925)). Qed.
Lemma lem4005928 : term241 = term209.
Proof. exact (TRANS (@lem4005923) (@lem4005927)). Qed.
Lemma lem4005930 (x : nat) : (term245 x) = term192.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem4005931 : term236 = term192.
Proof. exact (@lem4005930 term158). Qed.
Lemma lem4005932 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4005933 : term246 = term247.
Proof. exact (MK_COMB (@lem4005932) (@lem4005931)). Qed.
Lemma lem4005934 : term238 = term229.
Proof. exact (MK_COMB (@lem4005933) (@lem4005928)). Qed.
Lemma lem4005935 : term237 = term229.
Proof. exact (TRANS (@lem4005920) (@lem4005934)). Qed.
Lemma lem4005936 : term236 = term229.
Proof. exact (TRANS (@lem4005919) (@lem4005935)). Qed.
Lemma lem4005938 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4005939 : term229 = term192.
Proof. exact (@lem4005938 term192). Qed.
Lemma lem4005940 : term236 = term192.
Proof. exact (TRANS (@lem4005936) (@lem4005939)). Qed.
Lemma lem4005941 (_46262 : int) : (term210 _46262) = (term210 _46262).
Proof. exact (eq_refl (term210 _46262)). Qed.
Lemma lem4005942 (_46262 : int) : (term227 _46262) = (term249 _46262).
Proof. exact (MK_COMB (@lem4005941 _46262) (@lem4005940)). Qed.
Lemma lem4005943 (_46262 : int) : (term249 _46262) = (real_of_int _46262).
Proof. exact (@lem1982723 (real_of_int _46262)). Qed.
Lemma lem4005944 (_46262 : int) : (term227 _46262) = (real_of_int _46262).
Proof. exact (TRANS (@lem4005942 _46262) (@lem4005943 _46262)). Qed.
Lemma lem4005946 (_46262 : int) : (term226 _46262) = (real_of_int _46262).
Proof. exact (TRANS (@lem4005910 _46262) (@lem4005944 _46262)). Qed.
Lemma lem4005947 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4005948 (_46262 : int) : (term250 _46262) = (term251 _46262).
Proof. exact (MK_COMB (@lem4005947) (@lem4005946 _46262)). Qed.
Lemma lem4005949 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem4005950 (_46262 : int) : (term225 _46262) = (term252 _46262).
Proof. exact (MK_COMB (@lem4005948 _46262) (@lem4005949)). Qed.
Lemma lem4005951 (_46262 : int) : (term195 _46262) = (term252 _46262).
Proof. exact (TRANS (@lem4005904 _46262) (@lem4005950 _46262)). Qed.
Lemma lem4005952 (_46263 : int) : (term195 _46263) = (term225 _46263).
Proof. exact (@lem1988287 (real_of_int _46263) term192). Qed.
Lemma lem4005958 (_46263 : int) : (term226 _46263) = (term227 _46263).
Proof. exact (@lem1982792 (real_of_int _46263) term192). Qed.
Lemma lem4005960 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4005961 : term192 = term229.
Proof. exact (@lem4005960 (NUMERAL 0)). Qed.
Lemma lem4005963 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4005964 : term232 = term233.
Proof. exact (@lem4005963 term158). Qed.
Lemma lem4005965 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4005966 : term234 = term235.
Proof. exact (MK_COMB (@lem4005965) (@lem4005964)). Qed.
Lemma lem4005967 : term236 = term237.
Proof. exact (MK_COMB (@lem4005966) (@lem4005961)). Qed.
Lemma lem4005968 : term237 = term238.
Proof. exact (@lem1981613 term232 term192 term209 term209). Qed.
Lemma lem4005970 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4005971 : term241 = term242.
Proof. exact (@lem4005970 term158 term158). Qed.
Lemma lem4005972 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4005973 : term244 = term158.
Proof. exact (EQ_MP (@lem4005972) (@lem940073)). Qed.
Lemma lem4005974 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4005975 : term242 = term209.
Proof. exact (MK_COMB (@lem4005974) (@lem4005973)). Qed.
Lemma lem4005976 : term241 = term209.
Proof. exact (TRANS (@lem4005971) (@lem4005975)). Qed.
Lemma lem4005978 (x : nat) : (term245 x) = term192.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem4005979 : term236 = term192.
Proof. exact (@lem4005978 term158). Qed.
Lemma lem4005980 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4005981 : term246 = term247.
Proof. exact (MK_COMB (@lem4005980) (@lem4005979)). Qed.
Lemma lem4005982 : term238 = term229.
Proof. exact (MK_COMB (@lem4005981) (@lem4005976)). Qed.
Lemma lem4005983 : term237 = term229.
Proof. exact (TRANS (@lem4005968) (@lem4005982)). Qed.
Lemma lem4005984 : term236 = term229.
Proof. exact (TRANS (@lem4005967) (@lem4005983)). Qed.
Lemma lem4005986 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4005987 : term229 = term192.
Proof. exact (@lem4005986 term192). Qed.
Lemma lem4005988 : term236 = term192.
Proof. exact (TRANS (@lem4005984) (@lem4005987)). Qed.
Lemma lem4005989 (_46263 : int) : (term210 _46263) = (term210 _46263).
Proof. exact (eq_refl (term210 _46263)). Qed.
Lemma lem4005990 (_46263 : int) : (term227 _46263) = (term249 _46263).
Proof. exact (MK_COMB (@lem4005989 _46263) (@lem4005988)). Qed.
Lemma lem4005991 (_46263 : int) : (term249 _46263) = (real_of_int _46263).
Proof. exact (@lem1982723 (real_of_int _46263)). Qed.
Lemma lem4005992 (_46263 : int) : (term227 _46263) = (real_of_int _46263).
Proof. exact (TRANS (@lem4005990 _46263) (@lem4005991 _46263)). Qed.
Lemma lem4005994 (_46263 : int) : (term226 _46263) = (real_of_int _46263).
Proof. exact (TRANS (@lem4005958 _46263) (@lem4005992 _46263)). Qed.
Lemma lem4005995 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4005996 (_46263 : int) : (term250 _46263) = (term251 _46263).
Proof. exact (MK_COMB (@lem4005995) (@lem4005994 _46263)). Qed.
Lemma lem4005997 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem4005998 (_46263 : int) : (term225 _46263) = (term252 _46263).
Proof. exact (MK_COMB (@lem4005996 _46263) (@lem4005997)). Qed.
Lemma lem4005999 (_46263 : int) : (term195 _46263) = (term252 _46263).
Proof. exact (TRANS (@lem4005952 _46263) (@lem4005998 _46263)). Qed.
Lemma lem4006000 (_46262 : int) (_46263 : int) : (term187 _46263 _46262) = (term253 _46262 _46263).
Proof. exact (@lem1988287 (real_of_int _46262) (real_of_int _46263)). Qed.
Lemma lem4006013 (_46262 : int) (_46263 : int) : (term254 _46262 _46263) = (term255 _46262 _46263).
Proof. exact (@lem1982792 (real_of_int _46262) (real_of_int _46263)). Qed.
Lemma lem4006014 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4006015 (_46262 : int) (_46263 : int) : (term256 _46262 _46263) = (term257 _46262 _46263).
Proof. exact (MK_COMB (@lem4006014) (@lem4006013 _46262 _46263)). Qed.
Lemma lem4006016 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem4006017 (_46262 : int) (_46263 : int) : (term253 _46262 _46263) = (term258 _46262 _46263).
Proof. exact (MK_COMB (@lem4006015 _46262 _46263) (@lem4006016)). Qed.
Lemma lem4006018 (_46262 : int) (_46263 : int) : (term187 _46263 _46262) = (term258 _46262 _46263).
Proof. exact (TRANS (@lem4006000 _46262 _46263) (@lem4006017 _46262 _46263)). Qed.
Lemma lem4006019 (_46263 : int) (_46262 : int) : (term217 _46262 _46263) = (term259 _46263 _46262).
Proof. exact (@lem1988287 (real_of_int _46263) (term214 _46262)). Qed.
Lemma lem4006031 (_46262 : int) : (term214 _46262) = (term260 _46262).
Proof. exact (@lem1982755 (real_of_int _46262) term209 term209). Qed.
Lemma lem4006033 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4006034 : term209 = term261.
Proof. exact (@lem4006033 term158). Qed.
Lemma lem4006036 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4006037 : term209 = term261.
Proof. exact (@lem4006036 term158). Qed.
Lemma lem4006038 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4006039 : term262 = term263.
Proof. exact (MK_COMB (@lem4006038) (@lem4006037)). Qed.
Lemma lem4006040 : term264 = term265.
Proof. exact (MK_COMB (@lem4006039) (@lem4006034)). Qed.
Lemma lem4006041 : term266.
Proof. exact (@lem1981473 term209 term209 term209 term209 term267 term209). Qed.
Lemma lem4006043 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4006044 : term269 = term270.
Proof. exact (@lem4006043 (NUMERAL 0) term158). Qed.
Lemma lem4006045 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4006046 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4006047 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4006046 h1) (fun h1 : term270 = True => @lem4006045)). Qed.
Lemma lem4006048 : term270 = True.
Proof. exact (EQ_MP (@lem4006047) (@lem4006045)). Qed.
Lemma lem4006049 : term269 = True.
Proof. exact (TRANS (@lem4006044) (@lem4006048)). Qed.
Lemma lem4006050 : True = term269.
Proof. exact (SYM (@lem4006049)). Qed.
Lemma lem4006051 : term269.
Proof. exact (EQ_MP (@lem4006050) (@lem0)). Qed.
Lemma lem4006052 : term272.
Proof. exact (@lem4006041 (@lem4006051)). Qed.
Lemma lem4006054 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4006055 : term269 = term270.
Proof. exact (@lem4006054 (NUMERAL 0) term158). Qed.
Lemma lem4006056 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4006057 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4006058 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4006057 h1) (fun h1 : term270 = True => @lem4006056)). Qed.
Lemma lem4006059 : term270 = True.
Proof. exact (EQ_MP (@lem4006058) (@lem4006056)). Qed.
Lemma lem4006060 : term269 = True.
Proof. exact (TRANS (@lem4006055) (@lem4006059)). Qed.
Lemma lem4006061 : True = term269.
Proof. exact (SYM (@lem4006060)). Qed.
Lemma lem4006062 : term269.
Proof. exact (EQ_MP (@lem4006061) (@lem0)). Qed.
Lemma lem4006063 : term273.
Proof. exact (@lem4006052 (@lem4006062)). Qed.
Lemma lem4006065 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4006066 : term269 = term270.
Proof. exact (@lem4006065 (NUMERAL 0) term158). Qed.
Lemma lem4006067 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4006068 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4006069 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4006068 h1) (fun h1 : term270 = True => @lem4006067)). Qed.
Lemma lem4006070 : term270 = True.
Proof. exact (EQ_MP (@lem4006069) (@lem4006067)). Qed.
Lemma lem4006071 : term269 = True.
Proof. exact (TRANS (@lem4006066) (@lem4006070)). Qed.
Lemma lem4006072 : True = term269.
Proof. exact (SYM (@lem4006071)). Qed.
Lemma lem4006073 : term269.
Proof. exact (EQ_MP (@lem4006072) (@lem0)). Qed.
Lemma lem4006074 : term274.
Proof. exact (@lem4006063 (@lem4006073)). Qed.
Lemma lem4006076 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4006077 : term241 = term242.
Proof. exact (@lem4006076 term158 term158). Qed.
Lemma lem4006078 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4006079 : term244 = term158.
Proof. exact (EQ_MP (@lem4006078) (@lem940073)). Qed.
Lemma lem4006080 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4006081 : term242 = term209.
Proof. exact (MK_COMB (@lem4006080) (@lem4006079)). Qed.
Lemma lem4006082 : term241 = term209.
Proof. exact (TRANS (@lem4006077) (@lem4006081)). Qed.
Lemma lem4006084 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4006085 : term241 = term242.
Proof. exact (@lem4006084 term158 term158). Qed.
Lemma lem4006086 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4006087 : term244 = term158.
Proof. exact (EQ_MP (@lem4006086) (@lem940073)). Qed.
Lemma lem4006088 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4006089 : term242 = term209.
Proof. exact (MK_COMB (@lem4006088) (@lem4006087)). Qed.
Lemma lem4006090 : term241 = term209.
Proof. exact (TRANS (@lem4006085) (@lem4006089)). Qed.
Lemma lem4006091 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4006092 : term275 = term262.
Proof. exact (MK_COMB (@lem4006091) (@lem4006090)). Qed.
Lemma lem4006093 : term276 = term264.
Proof. exact (MK_COMB (@lem4006092) (@lem4006082)). Qed.
Lemma lem4006094 : term264 = term277.
Proof. exact (@lem1367770 term158 term158). Qed.
Lemma lem4006095 : term278 = term279.
Proof. exact (@lem706885). Qed.
Lemma lem4006096 : (term278 = term279) = (term280 = term281).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term279). Qed.
Lemma lem4006097 : term280 = term281.
Proof. exact (EQ_MP (@lem4006096) (@lem4006095)). Qed.
Lemma lem4006098 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4006099 : term277 = term267.
Proof. exact (MK_COMB (@lem4006098) (@lem4006097)). Qed.
Lemma lem4006100 : term264 = term267.
Proof. exact (TRANS (@lem4006094) (@lem4006099)). Qed.
Lemma lem4006101 : term276 = term267.
Proof. exact (TRANS (@lem4006093) (@lem4006100)). Qed.
Lemma lem4006102 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4006103 : term282 = term283.
Proof. exact (MK_COMB (@lem4006102) (@lem4006101)). Qed.
Lemma lem4006104 : term209 = term209.
Proof. exact (eq_refl term209). Qed.
Lemma lem4006105 : term284 = term285.
Proof. exact (MK_COMB (@lem4006103) (@lem4006104)). Qed.
Lemma lem4006107 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4006108 : term285 = term286.
Proof. exact (@lem4006107 term281 term158). Qed.
Lemma lem4006109 : term287 = term279.
Proof. exact (@lem996237 term279). Qed.
Lemma lem4006110 : (term287 = term279) = (term288 = term281).
Proof. exact (@lem1007663 term279 (BIT1 0) term279). Qed.
Lemma lem4006111 : term288 = term281.
Proof. exact (EQ_MP (@lem4006110) (@lem4006109)). Qed.
Lemma lem4006112 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4006113 : term286 = term267.
Proof. exact (MK_COMB (@lem4006112) (@lem4006111)). Qed.
Lemma lem4006114 : term285 = term267.
Proof. exact (TRANS (@lem4006108) (@lem4006113)). Qed.
Lemma lem4006115 : term284 = term267.
Proof. exact (TRANS (@lem4006105) (@lem4006114)). Qed.
Lemma lem4006117 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4006118 : term241 = term242.
Proof. exact (@lem4006117 term158 term158). Qed.
Lemma lem4006119 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4006120 : term244 = term158.
Proof. exact (EQ_MP (@lem4006119) (@lem940073)). Qed.
Lemma lem4006121 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4006122 : term242 = term209.
Proof. exact (MK_COMB (@lem4006121) (@lem4006120)). Qed.
Lemma lem4006123 : term241 = term209.
Proof. exact (TRANS (@lem4006118) (@lem4006122)). Qed.
Lemma lem4006124 : term283 = term283.
Proof. exact (eq_refl term283). Qed.
Lemma lem4006125 : term289 = term285.
Proof. exact (MK_COMB (@lem4006124) (@lem4006123)). Qed.
Lemma lem4006127 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4006128 : term285 = term286.
Proof. exact (@lem4006127 term281 term158). Qed.
Lemma lem4006129 : term287 = term279.
Proof. exact (@lem996237 term279). Qed.
Lemma lem4006130 : (term287 = term279) = (term288 = term281).
Proof. exact (@lem1007663 term279 (BIT1 0) term279). Qed.
Lemma lem4006131 : term288 = term281.
Proof. exact (EQ_MP (@lem4006130) (@lem4006129)). Qed.
Lemma lem4006132 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4006133 : term286 = term267.
Proof. exact (MK_COMB (@lem4006132) (@lem4006131)). Qed.
Lemma lem4006134 : term285 = term267.
Proof. exact (TRANS (@lem4006128) (@lem4006133)). Qed.
Lemma lem4006135 : term289 = term267.
Proof. exact (TRANS (@lem4006125) (@lem4006134)). Qed.
Lemma lem4006136 : term267 = term289.
Proof. exact (SYM (@lem4006135)). Qed.
Lemma lem4006137 : term284 = term289.
Proof. exact (TRANS (@lem4006115) (@lem4006136)). Qed.
Lemma lem4006138 : term265 = term290.
Proof. exact (@lem4006074 (@lem4006137)). Qed.
Lemma lem4006139 : term264 = term290.
Proof. exact (TRANS (@lem4006040) (@lem4006138)). Qed.
Lemma lem4006141 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4006142 : term290 = term267.
Proof. exact (@lem4006141 term267). Qed.
Lemma lem4006143 : term264 = term267.
Proof. exact (TRANS (@lem4006139) (@lem4006142)). Qed.
Lemma lem4006144 (_46262 : int) : (term210 _46262) = (term210 _46262).
Proof. exact (eq_refl (term210 _46262)). Qed.
Lemma lem4006145 (_46262 : int) : (term260 _46262) = (term291 _46262).
Proof. exact (MK_COMB (@lem4006144 _46262) (@lem4006143)). Qed.
Lemma lem4006147 (_46262 : int) : (term214 _46262) = (term291 _46262).
Proof. exact (TRANS (@lem4006031 _46262) (@lem4006145 _46262)). Qed.
Lemma lem4006150 (_46263 : int) : (term292 _46263) = (term292 _46263).
Proof. exact (eq_refl (term292 _46263)). Qed.
Lemma lem4006151 (_46263 : int) (_46262 : int) : (term293 _46263 _46262) = (term294 _46263 _46262).
Proof. exact (MK_COMB (@lem4006150 _46263) (@lem4006147 _46262)). Qed.
Lemma lem4006152 (_46263 : int) (_46262 : int) : (term294 _46263 _46262) = (term295 _46263 _46262).
Proof. exact (@lem1982792 (real_of_int _46263) (term291 _46262)). Qed.
Lemma lem4006153 (_46262 : int) : (term296 _46262) = (term297 _46262).
Proof. exact (@lem1982781 (real_of_int _46262) term232 term267). Qed.
Lemma lem4006155 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4006156 : term267 = term290.
Proof. exact (@lem4006155 term281). Qed.
Lemma lem4006158 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4006159 : term232 = term233.
Proof. exact (@lem4006158 term158). Qed.
Lemma lem4006160 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4006161 : term234 = term235.
Proof. exact (MK_COMB (@lem4006160) (@lem4006159)). Qed.
Lemma lem4006162 : term298 = term299.
Proof. exact (MK_COMB (@lem4006161) (@lem4006156)). Qed.
Lemma lem4006163 : term299 = term300.
Proof. exact (@lem1981613 term232 term267 term209 term209). Qed.
Lemma lem4006165 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4006166 : term241 = term242.
Proof. exact (@lem4006165 term158 term158). Qed.
Lemma lem4006167 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4006168 : term244 = term158.
Proof. exact (EQ_MP (@lem4006167) (@lem940073)). Qed.
Lemma lem4006169 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4006170 : term242 = term209.
Proof. exact (MK_COMB (@lem4006169) (@lem4006168)). Qed.
Lemma lem4006171 : term241 = term209.
Proof. exact (TRANS (@lem4006166) (@lem4006170)). Qed.
Lemma lem4006173 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4006174 : term298 = term303.
Proof. exact (@lem4006173 term158 term281). Qed.
Lemma lem4006175 : term304 = term279.
Proof. exact (@lem996238 term279). Qed.
Lemma lem4006176 : (term304 = term279) = (term305 = term281).
Proof. exact (@lem1007663 (BIT1 0) term279 term279). Qed.
Lemma lem4006177 : term305 = term281.
Proof. exact (EQ_MP (@lem4006176) (@lem4006175)). Qed.
Lemma lem4006178 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4006179 : term306 = term267.
Proof. exact (MK_COMB (@lem4006178) (@lem4006177)). Qed.
Lemma lem4006180 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4006181 : term303 = term307.
Proof. exact (MK_COMB (@lem4006180) (@lem4006179)). Qed.
Lemma lem4006182 : term298 = term307.
Proof. exact (TRANS (@lem4006174) (@lem4006181)). Qed.
Lemma lem4006183 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4006184 : term308 = term309.
Proof. exact (MK_COMB (@lem4006183) (@lem4006182)). Qed.
Lemma lem4006185 : term300 = term310.
Proof. exact (MK_COMB (@lem4006184) (@lem4006171)). Qed.
Lemma lem4006186 : term299 = term310.
Proof. exact (TRANS (@lem4006163) (@lem4006185)). Qed.
Lemma lem4006187 : term298 = term310.
Proof. exact (TRANS (@lem4006162) (@lem4006186)). Qed.
Lemma lem4006189 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4006190 : term310 = term307.
Proof. exact (@lem4006189 term307). Qed.
Lemma lem4006191 : term298 = term307.
Proof. exact (TRANS (@lem4006187) (@lem4006190)). Qed.
Lemma lem4006194 (_46262 : int) : (term311 _46262) = (term311 _46262).
Proof. exact (eq_refl (term311 _46262)). Qed.
Lemma lem4006195 (_46262 : int) : (term297 _46262) = (term312 _46262).
Proof. exact (MK_COMB (@lem4006194 _46262) (@lem4006191)). Qed.
Lemma lem4006196 (_46262 : int) : (term296 _46262) = (term312 _46262).
Proof. exact (TRANS (@lem4006153 _46262) (@lem4006195 _46262)). Qed.
Lemma lem4006197 (_46263 : int) : (term210 _46263) = (term210 _46263).
Proof. exact (eq_refl (term210 _46263)). Qed.
Lemma lem4006198 (_46263 : int) (_46262 : int) : (term295 _46263 _46262) = (term313 _46263 _46262).
Proof. exact (MK_COMB (@lem4006197 _46263) (@lem4006196 _46262)). Qed.
Lemma lem4006203 (_46262 : int) (_46263 : int) : (term313 _46263 _46262) = (term314 _46262 _46263).
Proof. exact (@lem1982757 (term315 _46262) (real_of_int _46263) term307). Qed.
Lemma lem4006204 (_46262 : int) (_46263 : int) : (term295 _46263 _46262) = (term314 _46262 _46263).
Proof. exact (TRANS (@lem4006198 _46263 _46262) (@lem4006203 _46262 _46263)). Qed.
Lemma lem4006205 (_46262 : int) (_46263 : int) : (term294 _46263 _46262) = (term314 _46262 _46263).
Proof. exact (TRANS (@lem4006152 _46263 _46262) (@lem4006204 _46262 _46263)). Qed.
Lemma lem4006206 (_46262 : int) (_46263 : int) : (term293 _46263 _46262) = (term314 _46262 _46263).
Proof. exact (TRANS (@lem4006151 _46263 _46262) (@lem4006205 _46262 _46263)). Qed.
Lemma lem4006207 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4006208 (_46262 : int) (_46263 : int) : (term316 _46263 _46262) = (term317 _46262 _46263).
Proof. exact (MK_COMB (@lem4006207) (@lem4006206 _46262 _46263)). Qed.
Lemma lem4006209 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem4006210 (_46262 : int) (_46263 : int) : (term259 _46263 _46262) = (term318 _46262 _46263).
Proof. exact (MK_COMB (@lem4006208 _46262 _46263) (@lem4006209)). Qed.
Lemma lem4006211 (_46262 : int) (_46263 : int) : (term217 _46262 _46263) = (term318 _46262 _46263).
Proof. exact (TRANS (@lem4006019 _46263 _46262) (@lem4006210 _46262 _46263)). Qed.
Lemma lem4006212 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4006213 (_46262 : int) (_46263 : int) : (term218 _46263 _46262) = (term319 _46262 _46263).
Proof. exact (MK_COMB (@lem4006212) (@lem4006018 _46262 _46263)). Qed.
Lemma lem4006214 (_46262 : int) (_46263 : int) : (term219 _46262 _46263) = (term320 _46262 _46263).
Proof. exact (MK_COMB (@lem4006213 _46262 _46263) (@lem4006211 _46262 _46263)). Qed.
Lemma lem4006215 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4006216 (_46263 : int) : (term220 _46263) = (term321 _46263).
Proof. exact (MK_COMB (@lem4006215) (@lem4005999 _46263)). Qed.
Lemma lem4006217 (_46262 : int) (_46263 : int) : (term221 _46262 _46263) = (term322 _46262 _46263).
Proof. exact (MK_COMB (@lem4006216 _46263) (@lem4006214 _46262 _46263)). Qed.
Lemma lem4006218 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4006219 (_46262 : int) : (term220 _46262) = (term321 _46262).
Proof. exact (MK_COMB (@lem4006218) (@lem4005951 _46262)). Qed.
Lemma lem4006220 (_46262 : int) (_46263 : int) : (term222 _46262 _46263) = (term323 _46262 _46263).
Proof. exact (MK_COMB (@lem4006219 _46262) (@lem4006217 _46262 _46263)). Qed.
Lemma lem4006247 (_46262 : int) (_46263 : int) : (term224 _46262 _46263) = (term323 _46262 _46263).
Proof. exact (TRANS (@lem4005903 _46262 _46263) (@lem4006220 _46262 _46263)). Qed.
Lemma lem4006251 (_46262 : int) (_46263 : int) (h1 : term323 _46262 _46263) : term323 _46262 _46263.
Proof. exact (h1). Qed.
Lemma lem4006252 (_46262 : int) (_46263 : int) (h1 : term323 _46262 _46263) : term322 _46262 _46263.
Proof. exact (proj2 (@lem4006251 _46262 _46263 h1)). Qed.
Lemma lem4006254 (_46262 : int) (_46263 : int) (h1 : term323 _46262 _46263) : term320 _46262 _46263.
Proof. exact (proj2 (@lem4006252 _46262 _46263 h1)). Qed.
Lemma lem4006256 (_46262 : int) (_46263 : int) (h1 : term323 _46262 _46263) : term318 _46262 _46263.
Proof. exact (proj2 (@lem4006254 _46262 _46263 h1)). Qed.
Lemma lem4006257 (_46262 : int) (_46263 : int) (h1 : term323 _46262 _46263) : term258 _46262 _46263.
Proof. exact (proj1 (@lem4006254 _46262 _46263 h1)). Qed.
Lemma lem4006259 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4006260 : term324 = term269.
Proof. exact (@lem4006259 term192 term209). Qed.
Lemma lem4006262 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4006263 : term209 = term261.
Proof. exact (@lem4006262 term158). Qed.
Lemma lem4006265 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4006266 : term192 = term229.
Proof. exact (@lem4006265 (NUMERAL 0)). Qed.
Lemma lem4006267 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4006268 : term325 = term326.
Proof. exact (MK_COMB (@lem4006267) (@lem4006266)). Qed.
Lemma lem4006269 : term269 = term327.
Proof. exact (MK_COMB (@lem4006268) (@lem4006263)). Qed.
Lemma lem4006270 : term328.
Proof. exact (@lem1980255 term192 term209 term209 term209). Qed.
Lemma lem4006272 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4006273 : term269 = term270.
Proof. exact (@lem4006272 (NUMERAL 0) term158). Qed.
Lemma lem4006274 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4006275 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4006276 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4006275 h1) (fun h1 : term270 = True => @lem4006274)). Qed.
Lemma lem4006277 : term270 = True.
Proof. exact (EQ_MP (@lem4006276) (@lem4006274)). Qed.
Lemma lem4006278 : term269 = True.
Proof. exact (TRANS (@lem4006273) (@lem4006277)). Qed.
Lemma lem4006279 : True = term269.
Proof. exact (SYM (@lem4006278)). Qed.
Lemma lem4006280 : term269.
Proof. exact (EQ_MP (@lem4006279) (@lem0)). Qed.
Lemma lem4006281 : term329.
Proof. exact (@lem4006270 (@lem4006280)). Qed.
Lemma lem4006283 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4006284 : term269 = term270.
Proof. exact (@lem4006283 (NUMERAL 0) term158). Qed.
Lemma lem4006285 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4006286 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4006287 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4006286 h1) (fun h1 : term270 = True => @lem4006285)). Qed.
Lemma lem4006288 : term270 = True.
Proof. exact (EQ_MP (@lem4006287) (@lem4006285)). Qed.
Lemma lem4006289 : term269 = True.
Proof. exact (TRANS (@lem4006284) (@lem4006288)). Qed.
Lemma lem4006290 : True = term269.
Proof. exact (SYM (@lem4006289)). Qed.
Lemma lem4006291 : term269.
Proof. exact (EQ_MP (@lem4006290) (@lem0)). Qed.
Lemma lem4006292 : term327 = term330.
Proof. exact (@lem4006281 (@lem4006291)). Qed.
Lemma lem4006294 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4006295 : term241 = term242.
Proof. exact (@lem4006294 term158 term158). Qed.
Lemma lem4006296 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4006297 : term244 = term158.
Proof. exact (EQ_MP (@lem4006296) (@lem940073)). Qed.
Lemma lem4006298 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4006299 : term242 = term209.
Proof. exact (MK_COMB (@lem4006298) (@lem4006297)). Qed.
Lemma lem4006300 : term241 = term209.
Proof. exact (TRANS (@lem4006295) (@lem4006299)). Qed.
Lemma lem4006302 (x : nat) : (term331 x) = term192.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4006303 : term332 = term192.
Proof. exact (@lem4006302 term158). Qed.
Lemma lem4006304 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4006305 : term333 = term325.
Proof. exact (MK_COMB (@lem4006304) (@lem4006303)). Qed.
Lemma lem4006306 : term330 = term269.
Proof. exact (MK_COMB (@lem4006305) (@lem4006300)). Qed.
Lemma lem4006308 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4006309 : term269 = term270.
Proof. exact (@lem4006308 (NUMERAL 0) term158). Qed.
Lemma lem4006310 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4006311 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4006312 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4006311 h1) (fun h1 : term270 = True => @lem4006310)). Qed.
Lemma lem4006313 : term270 = True.
Proof. exact (EQ_MP (@lem4006312) (@lem4006310)). Qed.
Lemma lem4006314 : term269 = True.
Proof. exact (TRANS (@lem4006309) (@lem4006313)). Qed.
Lemma lem4006315 : term330 = True.
Proof. exact (TRANS (@lem4006306) (@lem4006314)). Qed.
Lemma lem4006316 : term327 = True.
Proof. exact (TRANS (@lem4006292) (@lem4006315)). Qed.
Lemma lem4006317 : term269 = True.
Proof. exact (TRANS (@lem4006269) (@lem4006316)). Qed.
Lemma lem4006318 : term324 = True.
Proof. exact (TRANS (@lem4006260) (@lem4006317)). Qed.
Lemma lem4006319 : True = term324.
Proof. exact (SYM (@lem4006318)). Qed.
Lemma lem4006320 : term324.
Proof. exact (EQ_MP (@lem4006319) (@lem0)). Qed.
Lemma lem4006321 (_46262 : int) (_46263 : int) (h1 : term323 _46262 _46263) : term334 _46262 _46263.
Proof. exact (conj (@lem4006320) (@lem4006257 _46262 _46263 h1)). Qed.
Lemma lem4006323 (x : real) (y : real) : term335 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4006324 (_46262 : int) (_46263 : int) : term336 _46262 _46263.
Proof. exact (@lem4006323 term209 (term255 _46262 _46263)). Qed.
Lemma lem4006325 (_46262 : int) (_46263 : int) (h1 : term323 _46262 _46263) : term337 _46262 _46263.
Proof. exact (@lem4006324 _46262 _46263 (@lem4006321 _46262 _46263 h1)). Qed.
Lemma lem4006326 (_46262 : int) (_46263 : int) : (term338 _46262 _46263) = (term255 _46262 _46263).
Proof. exact (@lem1982733 (term255 _46262 _46263)). Qed.
Lemma lem4006327 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4006328 (_46262 : int) (_46263 : int) : (term339 _46262 _46263) = (term257 _46262 _46263).
Proof. exact (MK_COMB (@lem4006327) (@lem4006326 _46262 _46263)). Qed.
Lemma lem4006329 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem4006330 (_46262 : int) (_46263 : int) : (term337 _46262 _46263) = (term258 _46262 _46263).
Proof. exact (MK_COMB (@lem4006328 _46262 _46263) (@lem4006329)). Qed.
Lemma lem4006331 (_46262 : int) (_46263 : int) (h1 : term323 _46262 _46263) : term258 _46262 _46263.
Proof. exact (EQ_MP (@lem4006330 _46262 _46263) (@lem4006325 _46262 _46263 h1)). Qed.
Lemma lem4006333 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4006334 : term324 = term269.
Proof. exact (@lem4006333 term192 term209). Qed.
Lemma lem4006336 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4006337 : term209 = term261.
Proof. exact (@lem4006336 term158). Qed.
Lemma lem4006339 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4006340 : term192 = term229.
Proof. exact (@lem4006339 (NUMERAL 0)). Qed.
Lemma lem4006341 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4006342 : term325 = term326.
Proof. exact (MK_COMB (@lem4006341) (@lem4006340)). Qed.
Lemma lem4006343 : term269 = term327.
Proof. exact (MK_COMB (@lem4006342) (@lem4006337)). Qed.
Lemma lem4006344 : term328.
Proof. exact (@lem1980255 term192 term209 term209 term209). Qed.
Lemma lem4006346 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4006347 : term269 = term270.
Proof. exact (@lem4006346 (NUMERAL 0) term158). Qed.
Lemma lem4006348 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4006349 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4006350 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4006349 h1) (fun h1 : term270 = True => @lem4006348)). Qed.
Lemma lem4006351 : term270 = True.
Proof. exact (EQ_MP (@lem4006350) (@lem4006348)). Qed.
Lemma lem4006352 : term269 = True.
Proof. exact (TRANS (@lem4006347) (@lem4006351)). Qed.
Lemma lem4006353 : True = term269.
Proof. exact (SYM (@lem4006352)). Qed.
Lemma lem4006354 : term269.
Proof. exact (EQ_MP (@lem4006353) (@lem0)). Qed.
Lemma lem4006355 : term329.
Proof. exact (@lem4006344 (@lem4006354)). Qed.
Lemma lem4006357 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4006358 : term269 = term270.
Proof. exact (@lem4006357 (NUMERAL 0) term158). Qed.
Lemma lem4006359 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4006360 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4006361 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4006360 h1) (fun h1 : term270 = True => @lem4006359)). Qed.
Lemma lem4006362 : term270 = True.
Proof. exact (EQ_MP (@lem4006361) (@lem4006359)). Qed.
Lemma lem4006363 : term269 = True.
Proof. exact (TRANS (@lem4006358) (@lem4006362)). Qed.
Lemma lem4006364 : True = term269.
Proof. exact (SYM (@lem4006363)). Qed.
Lemma lem4006365 : term269.
Proof. exact (EQ_MP (@lem4006364) (@lem0)). Qed.
Lemma lem4006366 : term327 = term330.
Proof. exact (@lem4006355 (@lem4006365)). Qed.
Lemma lem4006368 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4006369 : term241 = term242.
Proof. exact (@lem4006368 term158 term158). Qed.
Lemma lem4006370 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4006371 : term244 = term158.
Proof. exact (EQ_MP (@lem4006370) (@lem940073)). Qed.
Lemma lem4006372 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4006373 : term242 = term209.
Proof. exact (MK_COMB (@lem4006372) (@lem4006371)). Qed.
Lemma lem4006374 : term241 = term209.
Proof. exact (TRANS (@lem4006369) (@lem4006373)). Qed.
Lemma lem4006376 (x : nat) : (term331 x) = term192.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4006377 : term332 = term192.
Proof. exact (@lem4006376 term158). Qed.
Lemma lem4006378 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4006379 : term333 = term325.
Proof. exact (MK_COMB (@lem4006378) (@lem4006377)). Qed.
Lemma lem4006380 : term330 = term269.
Proof. exact (MK_COMB (@lem4006379) (@lem4006374)). Qed.
Lemma lem4006382 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4006383 : term269 = term270.
Proof. exact (@lem4006382 (NUMERAL 0) term158). Qed.
Lemma lem4006384 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4006385 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4006386 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4006385 h1) (fun h1 : term270 = True => @lem4006384)). Qed.
Lemma lem4006387 : term270 = True.
Proof. exact (EQ_MP (@lem4006386) (@lem4006384)). Qed.
Lemma lem4006388 : term269 = True.
Proof. exact (TRANS (@lem4006383) (@lem4006387)). Qed.
Lemma lem4006389 : term330 = True.
Proof. exact (TRANS (@lem4006380) (@lem4006388)). Qed.
Lemma lem4006390 : term327 = True.
Proof. exact (TRANS (@lem4006366) (@lem4006389)). Qed.
Lemma lem4006391 : term269 = True.
Proof. exact (TRANS (@lem4006343) (@lem4006390)). Qed.
Lemma lem4006392 : term324 = True.
Proof. exact (TRANS (@lem4006334) (@lem4006391)). Qed.
Lemma lem4006393 : True = term324.
Proof. exact (SYM (@lem4006392)). Qed.
Lemma lem4006394 : term324.
Proof. exact (EQ_MP (@lem4006393) (@lem0)). Qed.
Lemma lem4006395 (_46262 : int) (_46263 : int) (h1 : term323 _46262 _46263) : term340 _46262 _46263.
Proof. exact (conj (@lem4006394) (@lem4006256 _46262 _46263 h1)). Qed.
Lemma lem4006397 (x : real) (y : real) : term335 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4006398 (_46262 : int) (_46263 : int) : term341 _46262 _46263.
Proof. exact (@lem4006397 term209 (term314 _46262 _46263)). Qed.
Lemma lem4006399 (_46262 : int) (_46263 : int) (h1 : term323 _46262 _46263) : term342 _46262 _46263.
Proof. exact (@lem4006398 _46262 _46263 (@lem4006395 _46262 _46263 h1)). Qed.
Lemma lem4006400 (_46262 : int) (_46263 : int) : (term343 _46262 _46263) = (term314 _46262 _46263).
Proof. exact (@lem1982733 (term314 _46262 _46263)). Qed.
Lemma lem4006401 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4006402 (_46262 : int) (_46263 : int) : (term344 _46262 _46263) = (term317 _46262 _46263).
Proof. exact (MK_COMB (@lem4006401) (@lem4006400 _46262 _46263)). Qed.
Lemma lem4006403 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem4006404 (_46262 : int) (_46263 : int) : (term342 _46262 _46263) = (term318 _46262 _46263).
Proof. exact (MK_COMB (@lem4006402 _46262 _46263) (@lem4006403)). Qed.
Lemma lem4006405 (_46262 : int) (_46263 : int) (h1 : term323 _46262 _46263) : term318 _46262 _46263.
Proof. exact (EQ_MP (@lem4006404 _46262 _46263) (@lem4006399 _46262 _46263 h1)). Qed.
Lemma lem4006406 (_46262 : int) (_46263 : int) (h1 : term323 _46262 _46263) : term345 _46262 _46263.
Proof. exact (conj (@lem4006405 _46262 _46263 h1) (@lem4006331 _46262 _46263 h1)). Qed.
Lemma lem4006408 (x : real) (y : real) : term346 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem4006409 (_46262 : int) (_46263 : int) : term347 _46262 _46263.
Proof. exact (@lem4006408 (term314 _46262 _46263) (term255 _46262 _46263)). Qed.
Lemma lem4006410 (_46262 : int) (_46263 : int) (h1 : term323 _46262 _46263) : term348 _46262 _46263.
Proof. exact (@lem4006409 _46262 _46263 (@lem4006406 _46262 _46263 h1)). Qed.
Lemma lem4006411 (_46262 : int) (_46263 : int) : (term349 _46262 _46263) = (term350 _46262 _46263).
Proof. exact (@lem1982753 (term315 _46262) (real_of_int _46262) (term351 _46263) (term315 _46263)). Qed.
Lemma lem4006412 (_46262 : int) : (term352 _46262) = (term353 _46262).
Proof. exact (@lem1982713 term232 (real_of_int _46262)). Qed.
Lemma lem4006414 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4006415 : term209 = term261.
Proof. exact (@lem4006414 term158). Qed.
Lemma lem4006417 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4006418 : term232 = term233.
Proof. exact (@lem4006417 term158). Qed.
Lemma lem4006419 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4006420 : term354 = term355.
Proof. exact (MK_COMB (@lem4006419) (@lem4006418)). Qed.
Lemma lem4006421 : term356 = term357.
Proof. exact (MK_COMB (@lem4006420) (@lem4006415)). Qed.
Lemma lem4006422 : term358.
Proof. exact (@lem1981473 term232 term209 term209 term209 term192 term209). Qed.
Lemma lem4006424 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4006425 : term269 = term270.
Proof. exact (@lem4006424 (NUMERAL 0) term158). Qed.
Lemma lem4006426 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4006427 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4006428 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4006427 h1) (fun h1 : term270 = True => @lem4006426)). Qed.
Lemma lem4006429 : term270 = True.
Proof. exact (EQ_MP (@lem4006428) (@lem4006426)). Qed.
Lemma lem4006430 : term269 = True.
Proof. exact (TRANS (@lem4006425) (@lem4006429)). Qed.
Lemma lem4006431 : True = term269.
Proof. exact (SYM (@lem4006430)). Qed.
Lemma lem4006432 : term269.
Proof. exact (EQ_MP (@lem4006431) (@lem0)). Qed.
Lemma lem4006433 : term359.
Proof. exact (@lem4006422 (@lem4006432)). Qed.
Lemma lem4006435 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4006436 : term269 = term270.
Proof. exact (@lem4006435 (NUMERAL 0) term158). Qed.
Lemma lem4006437 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4006438 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4006439 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4006438 h1) (fun h1 : term270 = True => @lem4006437)). Qed.
Lemma lem4006440 : term270 = True.
Proof. exact (EQ_MP (@lem4006439) (@lem4006437)). Qed.
Lemma lem4006441 : term269 = True.
Proof. exact (TRANS (@lem4006436) (@lem4006440)). Qed.
Lemma lem4006442 : True = term269.
Proof. exact (SYM (@lem4006441)). Qed.
Lemma lem4006443 : term269.
Proof. exact (EQ_MP (@lem4006442) (@lem0)). Qed.
Lemma lem4006444 : term360.
Proof. exact (@lem4006433 (@lem4006443)). Qed.
Lemma lem4006446 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4006447 : term269 = term270.
Proof. exact (@lem4006446 (NUMERAL 0) term158). Qed.
Lemma lem4006448 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4006449 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4006450 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4006449 h1) (fun h1 : term270 = True => @lem4006448)). Qed.
Lemma lem4006451 : term270 = True.
Proof. exact (EQ_MP (@lem4006450) (@lem4006448)). Qed.
Lemma lem4006452 : term269 = True.
Proof. exact (TRANS (@lem4006447) (@lem4006451)). Qed.
Lemma lem4006453 : True = term269.
Proof. exact (SYM (@lem4006452)). Qed.
Lemma lem4006454 : term269.
Proof. exact (EQ_MP (@lem4006453) (@lem0)). Qed.
Lemma lem4006455 : term361.
Proof. exact (@lem4006444 (@lem4006454)). Qed.
Lemma lem4006457 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4006458 : term241 = term242.
Proof. exact (@lem4006457 term158 term158). Qed.
Lemma lem4006459 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4006460 : term244 = term158.
Proof. exact (EQ_MP (@lem4006459) (@lem940073)). Qed.
Lemma lem4006461 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4006462 : term242 = term209.
Proof. exact (MK_COMB (@lem4006461) (@lem4006460)). Qed.
Lemma lem4006463 : term241 = term209.
Proof. exact (TRANS (@lem4006458) (@lem4006462)). Qed.
Lemma lem4006465 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4006466 : term362 = term363.
Proof. exact (@lem4006465 term158 term158). Qed.
Lemma lem4006467 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4006468 : term244 = term158.
Proof. exact (EQ_MP (@lem4006467) (@lem940073)). Qed.
Lemma lem4006469 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4006470 : term242 = term209.
Proof. exact (MK_COMB (@lem4006469) (@lem4006468)). Qed.
Lemma lem4006471 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4006472 : term363 = term232.
Proof. exact (MK_COMB (@lem4006471) (@lem4006470)). Qed.
Lemma lem4006473 : term362 = term232.
Proof. exact (TRANS (@lem4006466) (@lem4006472)). Qed.
Lemma lem4006474 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4006475 : term364 = term354.
Proof. exact (MK_COMB (@lem4006474) (@lem4006473)). Qed.
Lemma lem4006476 : term365 = term356.
Proof. exact (MK_COMB (@lem4006475) (@lem4006463)). Qed.
Lemma lem4006478 (m : nat) : (term366 m) = term192.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4006479 : term356 = term192.
Proof. exact (@lem4006478 term158). Qed.
Lemma lem4006480 : term365 = term192.
Proof. exact (TRANS (@lem4006476) (@lem4006479)). Qed.
Lemma lem4006481 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4006482 : term367 = term368.
Proof. exact (MK_COMB (@lem4006481) (@lem4006480)). Qed.
Lemma lem4006483 : term209 = term209.
Proof. exact (eq_refl term209). Qed.
Lemma lem4006484 : term369 = term332.
Proof. exact (MK_COMB (@lem4006482) (@lem4006483)). Qed.
Lemma lem4006486 (x : nat) : (term331 x) = term192.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4006487 : term332 = term192.
Proof. exact (@lem4006486 term158). Qed.
Lemma lem4006488 : term369 = term192.
Proof. exact (TRANS (@lem4006484) (@lem4006487)). Qed.
Lemma lem4006490 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4006491 : term241 = term242.
Proof. exact (@lem4006490 term158 term158). Qed.
Lemma lem4006492 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4006493 : term244 = term158.
Proof. exact (EQ_MP (@lem4006492) (@lem940073)). Qed.
Lemma lem4006494 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4006495 : term242 = term209.
Proof. exact (MK_COMB (@lem4006494) (@lem4006493)). Qed.
Lemma lem4006496 : term241 = term209.
Proof. exact (TRANS (@lem4006491) (@lem4006495)). Qed.
Lemma lem4006497 : term368 = term368.
Proof. exact (eq_refl term368). Qed.
Lemma lem4006498 : term370 = term332.
Proof. exact (MK_COMB (@lem4006497) (@lem4006496)). Qed.
Lemma lem4006500 (x : nat) : (term331 x) = term192.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4006501 : term332 = term192.
Proof. exact (@lem4006500 term158). Qed.
Lemma lem4006502 : term370 = term192.
Proof. exact (TRANS (@lem4006498) (@lem4006501)). Qed.
Lemma lem4006503 : term192 = term370.
Proof. exact (SYM (@lem4006502)). Qed.
Lemma lem4006504 : term369 = term370.
Proof. exact (TRANS (@lem4006488) (@lem4006503)). Qed.
Lemma lem4006505 : term357 = term229.
Proof. exact (@lem4006455 (@lem4006504)). Qed.
Lemma lem4006506 : term356 = term229.
Proof. exact (TRANS (@lem4006421) (@lem4006505)). Qed.
Lemma lem4006508 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4006509 : term229 = term192.
Proof. exact (@lem4006508 term192). Qed.
Lemma lem4006510 : term356 = term192.
Proof. exact (TRANS (@lem4006506) (@lem4006509)). Qed.
Lemma lem4006511 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4006512 : term371 = term368.
Proof. exact (MK_COMB (@lem4006511) (@lem4006510)). Qed.
Lemma lem4006513 (_46262 : int) : (real_of_int _46262) = (real_of_int _46262).
Proof. exact (eq_refl (real_of_int _46262)). Qed.
Lemma lem4006514 (_46262 : int) : (term353 _46262) = (term372 _46262).
Proof. exact (MK_COMB (@lem4006512) (@lem4006513 _46262)). Qed.
Lemma lem4006515 (_46262 : int) : (term352 _46262) = (term372 _46262).
Proof. exact (TRANS (@lem4006412 _46262) (@lem4006514 _46262)). Qed.
Lemma lem4006516 (_46262 : int) : (term372 _46262) = term192.
Proof. exact (@lem1982719 (real_of_int _46262)). Qed.
Lemma lem4006517 (_46262 : int) : (term352 _46262) = term192.
Proof. exact (TRANS (@lem4006515 _46262) (@lem4006516 _46262)). Qed.
Lemma lem4006518 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4006519 (_46262 : int) : (term373 _46262) = term374.
Proof. exact (MK_COMB (@lem4006518) (@lem4006517 _46262)). Qed.
Lemma lem4006520 (_46263 : int) : (term375 _46263) = (term376 _46263).
Proof. exact (@lem1982759 (real_of_int _46263) (term315 _46263) term307). Qed.
Lemma lem4006521 (_46263 : int) : (term377 _46263) = (term353 _46263).
Proof. exact (@lem1982715 term232 (real_of_int _46263)). Qed.
Lemma lem4006523 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4006524 : term209 = term261.
Proof. exact (@lem4006523 term158). Qed.
Lemma lem4006526 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4006527 : term232 = term233.
Proof. exact (@lem4006526 term158). Qed.
Lemma lem4006528 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4006529 : term354 = term355.
Proof. exact (MK_COMB (@lem4006528) (@lem4006527)). Qed.
Lemma lem4006530 : term356 = term357.
Proof. exact (MK_COMB (@lem4006529) (@lem4006524)). Qed.
Lemma lem4006531 : term358.
Proof. exact (@lem1981473 term232 term209 term209 term209 term192 term209). Qed.
Lemma lem4006533 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4006534 : term269 = term270.
Proof. exact (@lem4006533 (NUMERAL 0) term158). Qed.
Lemma lem4006535 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4006536 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4006537 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4006536 h1) (fun h1 : term270 = True => @lem4006535)). Qed.
Lemma lem4006538 : term270 = True.
Proof. exact (EQ_MP (@lem4006537) (@lem4006535)). Qed.
Lemma lem4006539 : term269 = True.
Proof. exact (TRANS (@lem4006534) (@lem4006538)). Qed.
Lemma lem4006540 : True = term269.
Proof. exact (SYM (@lem4006539)). Qed.
Lemma lem4006541 : term269.
Proof. exact (EQ_MP (@lem4006540) (@lem0)). Qed.
Lemma lem4006542 : term359.
Proof. exact (@lem4006531 (@lem4006541)). Qed.
Lemma lem4006544 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4006545 : term269 = term270.
Proof. exact (@lem4006544 (NUMERAL 0) term158). Qed.
Lemma lem4006546 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4006547 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4006548 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4006547 h1) (fun h1 : term270 = True => @lem4006546)). Qed.
Lemma lem4006549 : term270 = True.
Proof. exact (EQ_MP (@lem4006548) (@lem4006546)). Qed.
Lemma lem4006550 : term269 = True.
Proof. exact (TRANS (@lem4006545) (@lem4006549)). Qed.
Lemma lem4006551 : True = term269.
Proof. exact (SYM (@lem4006550)). Qed.
Lemma lem4006552 : term269.
Proof. exact (EQ_MP (@lem4006551) (@lem0)). Qed.
Lemma lem4006553 : term360.
Proof. exact (@lem4006542 (@lem4006552)). Qed.
Lemma lem4006555 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4006556 : term269 = term270.
Proof. exact (@lem4006555 (NUMERAL 0) term158). Qed.
Lemma lem4006557 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4006558 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4006559 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4006558 h1) (fun h1 : term270 = True => @lem4006557)). Qed.
Lemma lem4006560 : term270 = True.
Proof. exact (EQ_MP (@lem4006559) (@lem4006557)). Qed.
Lemma lem4006561 : term269 = True.
Proof. exact (TRANS (@lem4006556) (@lem4006560)). Qed.
Lemma lem4006562 : True = term269.
Proof. exact (SYM (@lem4006561)). Qed.
Lemma lem4006563 : term269.
Proof. exact (EQ_MP (@lem4006562) (@lem0)). Qed.
Lemma lem4006564 : term361.
Proof. exact (@lem4006553 (@lem4006563)). Qed.
Lemma lem4006566 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4006567 : term241 = term242.
Proof. exact (@lem4006566 term158 term158). Qed.
Lemma lem4006568 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4006569 : term244 = term158.
Proof. exact (EQ_MP (@lem4006568) (@lem940073)). Qed.
Lemma lem4006570 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4006571 : term242 = term209.
Proof. exact (MK_COMB (@lem4006570) (@lem4006569)). Qed.
Lemma lem4006572 : term241 = term209.
Proof. exact (TRANS (@lem4006567) (@lem4006571)). Qed.
Lemma lem4006574 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4006575 : term362 = term363.
Proof. exact (@lem4006574 term158 term158). Qed.
Lemma lem4006576 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4006577 : term244 = term158.
Proof. exact (EQ_MP (@lem4006576) (@lem940073)). Qed.
Lemma lem4006578 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4006579 : term242 = term209.
Proof. exact (MK_COMB (@lem4006578) (@lem4006577)). Qed.
Lemma lem4006580 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4006581 : term363 = term232.
Proof. exact (MK_COMB (@lem4006580) (@lem4006579)). Qed.
Lemma lem4006582 : term362 = term232.
Proof. exact (TRANS (@lem4006575) (@lem4006581)). Qed.
Lemma lem4006583 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4006584 : term364 = term354.
Proof. exact (MK_COMB (@lem4006583) (@lem4006582)). Qed.
Lemma lem4006585 : term365 = term356.
Proof. exact (MK_COMB (@lem4006584) (@lem4006572)). Qed.
Lemma lem4006587 (m : nat) : (term366 m) = term192.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4006588 : term356 = term192.
Proof. exact (@lem4006587 term158). Qed.
Lemma lem4006589 : term365 = term192.
Proof. exact (TRANS (@lem4006585) (@lem4006588)). Qed.
Lemma lem4006590 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4006591 : term367 = term368.
Proof. exact (MK_COMB (@lem4006590) (@lem4006589)). Qed.
Lemma lem4006592 : term209 = term209.
Proof. exact (eq_refl term209). Qed.
Lemma lem4006593 : term369 = term332.
Proof. exact (MK_COMB (@lem4006591) (@lem4006592)). Qed.
Lemma lem4006595 (x : nat) : (term331 x) = term192.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4006596 : term332 = term192.
Proof. exact (@lem4006595 term158). Qed.
Lemma lem4006597 : term369 = term192.
Proof. exact (TRANS (@lem4006593) (@lem4006596)). Qed.
Lemma lem4006599 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4006600 : term241 = term242.
Proof. exact (@lem4006599 term158 term158). Qed.
Lemma lem4006601 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4006602 : term244 = term158.
Proof. exact (EQ_MP (@lem4006601) (@lem940073)). Qed.
Lemma lem4006603 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4006604 : term242 = term209.
Proof. exact (MK_COMB (@lem4006603) (@lem4006602)). Qed.
Lemma lem4006605 : term241 = term209.
Proof. exact (TRANS (@lem4006600) (@lem4006604)). Qed.
Lemma lem4006606 : term368 = term368.
Proof. exact (eq_refl term368). Qed.
Lemma lem4006607 : term370 = term332.
Proof. exact (MK_COMB (@lem4006606) (@lem4006605)). Qed.
Lemma lem4006609 (x : nat) : (term331 x) = term192.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4006610 : term332 = term192.
Proof. exact (@lem4006609 term158). Qed.
Lemma lem4006611 : term370 = term192.
Proof. exact (TRANS (@lem4006607) (@lem4006610)). Qed.
Lemma lem4006612 : term192 = term370.
Proof. exact (SYM (@lem4006611)). Qed.
Lemma lem4006613 : term369 = term370.
Proof. exact (TRANS (@lem4006597) (@lem4006612)). Qed.
Lemma lem4006614 : term357 = term229.
Proof. exact (@lem4006564 (@lem4006613)). Qed.
Lemma lem4006615 : term356 = term229.
Proof. exact (TRANS (@lem4006530) (@lem4006614)). Qed.
Lemma lem4006617 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4006618 : term229 = term192.
Proof. exact (@lem4006617 term192). Qed.
Lemma lem4006619 : term356 = term192.
Proof. exact (TRANS (@lem4006615) (@lem4006618)). Qed.
Lemma lem4006620 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4006621 : term371 = term368.
Proof. exact (MK_COMB (@lem4006620) (@lem4006619)). Qed.
Lemma lem4006622 (_46263 : int) : (real_of_int _46263) = (real_of_int _46263).
Proof. exact (eq_refl (real_of_int _46263)). Qed.
Lemma lem4006623 (_46263 : int) : (term353 _46263) = (term372 _46263).
Proof. exact (MK_COMB (@lem4006621) (@lem4006622 _46263)). Qed.
Lemma lem4006624 (_46263 : int) : (term377 _46263) = (term372 _46263).
Proof. exact (TRANS (@lem4006521 _46263) (@lem4006623 _46263)). Qed.
Lemma lem4006625 (_46263 : int) : (term372 _46263) = term192.
Proof. exact (@lem1982719 (real_of_int _46263)). Qed.
Lemma lem4006626 (_46263 : int) : (term377 _46263) = term192.
Proof. exact (TRANS (@lem4006624 _46263) (@lem4006625 _46263)). Qed.
Lemma lem4006627 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4006628 (_46263 : int) : (term378 _46263) = term374.
Proof. exact (MK_COMB (@lem4006627) (@lem4006626 _46263)). Qed.
Lemma lem4006629 : term307 = term307.
Proof. exact (eq_refl term307). Qed.
Lemma lem4006630 (_46263 : int) : (term376 _46263) = term379.
Proof. exact (MK_COMB (@lem4006628 _46263) (@lem4006629)). Qed.
Lemma lem4006631 (_46263 : int) : (term375 _46263) = term379.
Proof. exact (TRANS (@lem4006520 _46263) (@lem4006630 _46263)). Qed.
Lemma lem4006632 : term379 = term307.
Proof. exact (@lem1982721 term307). Qed.
Lemma lem4006633 (_46263 : int) : (term375 _46263) = term307.
Proof. exact (TRANS (@lem4006631 _46263) (@lem4006632)). Qed.
Lemma lem4006634 (_46262 : int) (_46263 : int) : (term350 _46262 _46263) = term379.
Proof. exact (MK_COMB (@lem4006519 _46262) (@lem4006633 _46263)). Qed.
Lemma lem4006635 (_46262 : int) (_46263 : int) : (term349 _46262 _46263) = term379.
Proof. exact (TRANS (@lem4006411 _46262 _46263) (@lem4006634 _46262 _46263)). Qed.
Lemma lem4006636 : term379 = term307.
Proof. exact (@lem1982721 term307). Qed.
Lemma lem4006637 (_46262 : int) (_46263 : int) : (term349 _46262 _46263) = term307.
Proof. exact (TRANS (@lem4006635 _46262 _46263) (@lem4006636)). Qed.
Lemma lem4006638 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4006639 (_46262 : int) (_46263 : int) : (term380 _46262 _46263) = term381.
Proof. exact (MK_COMB (@lem4006638) (@lem4006637 _46262 _46263)). Qed.
Lemma lem4006640 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem4006641 (_46262 : int) (_46263 : int) : (term348 _46262 _46263) = term382.
Proof. exact (MK_COMB (@lem4006639 _46262 _46263) (@lem4006640)). Qed.
Lemma lem4006642 (_46262 : int) (_46263 : int) (h1 : term323 _46262 _46263) : term382.
Proof. exact (EQ_MP (@lem4006641 _46262 _46263) (@lem4006410 _46262 _46263 h1)). Qed.
Lemma lem4006644 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem4006645 : term382 = term383.
Proof. exact (@lem4006644 term192 term307). Qed.
Lemma lem4006647 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4006648 : term307 = term310.
Proof. exact (@lem4006647 term281). Qed.
Lemma lem4006650 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4006651 : term192 = term229.
Proof. exact (@lem4006650 (NUMERAL 0)). Qed.
Lemma lem4006652 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4006653 : term194 = term384.
Proof. exact (MK_COMB (@lem4006652) (@lem4006651)). Qed.
Lemma lem4006654 : term383 = term385.
Proof. exact (MK_COMB (@lem4006653) (@lem4006648)). Qed.
Lemma lem4006655 : term386.
Proof. exact (@lem1980026 term192 term209 term307 term209). Qed.
Lemma lem4006657 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4006658 : term269 = term270.
Proof. exact (@lem4006657 (NUMERAL 0) term158). Qed.
Lemma lem4006659 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4006660 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4006661 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4006660 h1) (fun h1 : term270 = True => @lem4006659)). Qed.
Lemma lem4006662 : term270 = True.
Proof. exact (EQ_MP (@lem4006661) (@lem4006659)). Qed.
Lemma lem4006663 : term269 = True.
Proof. exact (TRANS (@lem4006658) (@lem4006662)). Qed.
Lemma lem4006664 : True = term269.
Proof. exact (SYM (@lem4006663)). Qed.
Lemma lem4006665 : term269.
Proof. exact (EQ_MP (@lem4006664) (@lem0)). Qed.
Lemma lem4006666 : term387.
Proof. exact (@lem4006655 (@lem4006665)). Qed.
Lemma lem4006668 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4006669 : term269 = term270.
Proof. exact (@lem4006668 (NUMERAL 0) term158). Qed.
Lemma lem4006670 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4006671 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4006672 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4006671 h1) (fun h1 : term270 = True => @lem4006670)). Qed.
Lemma lem4006673 : term270 = True.
Proof. exact (EQ_MP (@lem4006672) (@lem4006670)). Qed.
Lemma lem4006674 : term269 = True.
Proof. exact (TRANS (@lem4006669) (@lem4006673)). Qed.
Lemma lem4006675 : True = term269.
Proof. exact (SYM (@lem4006674)). Qed.
Lemma lem4006676 : term269.
Proof. exact (EQ_MP (@lem4006675) (@lem0)). Qed.
Lemma lem4006677 : term385 = term388.
Proof. exact (@lem4006666 (@lem4006676)). Qed.
Lemma lem4006679 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4006680 : term389 = term390.
Proof. exact (@lem4006679 term281 term158). Qed.
Lemma lem4006681 : term287 = term279.
Proof. exact (@lem996237 term279). Qed.
Lemma lem4006682 : (term287 = term279) = (term288 = term281).
Proof. exact (@lem1007663 term279 (BIT1 0) term279). Qed.
Lemma lem4006683 : term288 = term281.
Proof. exact (EQ_MP (@lem4006682) (@lem4006681)). Qed.
Lemma lem4006684 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4006685 : term286 = term267.
Proof. exact (MK_COMB (@lem4006684) (@lem4006683)). Qed.
Lemma lem4006686 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4006687 : term390 = term307.
Proof. exact (MK_COMB (@lem4006686) (@lem4006685)). Qed.
Lemma lem4006688 : term389 = term307.
Proof. exact (TRANS (@lem4006680) (@lem4006687)). Qed.
Lemma lem4006690 (x : nat) : (term331 x) = term192.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4006691 : term332 = term192.
Proof. exact (@lem4006690 term158). Qed.
Lemma lem4006692 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4006693 : term391 = term194.
Proof. exact (MK_COMB (@lem4006692) (@lem4006691)). Qed.
Lemma lem4006694 : term388 = term383.
Proof. exact (MK_COMB (@lem4006693) (@lem4006688)). Qed.
Lemma lem4006696 (m : nat) (n : nat) : (term392 m n) = (term393 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem4006697 : term383 = term394.
Proof. exact (@lem4006696 (NUMERAL 0) term281). Qed.
Lemma lem4006698 : term395 = term279.
Proof. exact (@lem912803). Qed.
Lemma lem4006699 (h1 : term395 = term279) : (term281 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term279 h1). Qed.
Lemma lem4006700 : (term395 = term279) = ((term281 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term395 = term279 => @lem4006699 h1) (fun h1 : (term281 = (NUMERAL 0)) = False => @lem4006698)). Qed.
Lemma lem4006701 : (term281 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem4006700) (@lem4006698)). Qed.
Lemma lem4006702 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem4006703 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4006704 : term396 = (and True).
Proof. exact (MK_COMB (@lem4006703) (@lem4006702)). Qed.
Lemma lem4006705 : term394 = (True /\ False).
Proof. exact (MK_COMB (@lem4006704) (@lem4006701)). Qed.
Lemma lem4006707 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem4006708 : term394 = False.
Proof. exact (TRANS (@lem4006705) (@lem4006707)). Qed.
Lemma lem4006709 : term383 = False.
Proof. exact (TRANS (@lem4006697) (@lem4006708)). Qed.
Lemma lem4006710 : term388 = False.
Proof. exact (TRANS (@lem4006694) (@lem4006709)). Qed.
Lemma lem4006711 : term385 = False.
Proof. exact (TRANS (@lem4006677) (@lem4006710)). Qed.
Lemma lem4006712 : term383 = False.
Proof. exact (TRANS (@lem4006654) (@lem4006711)). Qed.
Lemma lem4006713 : term382 = False.
Proof. exact (TRANS (@lem4006645) (@lem4006712)). Qed.
Lemma lem4006714 (_46262 : int) (_46263 : int) (h1 : term323 _46262 _46263) : False.
Proof. exact (EQ_MP (@lem4006713) (@lem4006642 _46262 _46263 h1)). Qed.
Lemma lem4006716 (_46262 : int) (_46263 : int) (h1 : term323 _46262 _46263) : term323 _46262 _46263.
Proof. exact (h1). Qed.
Lemma lem4006717 (_46262 : int) (_46263 : int) (h1 : term323 _46262 _46263) : (term323 _46262 _46263) = False.
Proof. exact (prop_ext (fun h2 : term323 _46262 _46263 => @lem4006714 _46262 _46263 h1) (fun h2 : False => @lem4006716 _46262 _46263 h1)). Qed.
Lemma lem4006718 (_46262 : int) (_46263 : int) (h1 : term323 _46262 _46263) : False.
Proof. exact (EQ_MP (@lem4006717 _46262 _46263 h1) (@lem4006716 _46262 _46263 h1)). Qed.
Lemma lem4006719 (_46262 : int) (_46263 : int) (h1 : term224 _46262 _46263) : term224 _46262 _46263.
Proof. exact (h1). Qed.
Lemma lem4006720 (_46262 : int) (_46263 : int) (h1 : term224 _46262 _46263) : term323 _46262 _46263.
Proof. exact (EQ_MP (@lem4006247 _46262 _46263) (@lem4006719 _46262 _46263 h1)). Qed.
Lemma lem4006721 (_46262 : int) (_46263 : int) (h1 : term224 _46262 _46263) : (term323 _46262 _46263) = False.
Proof. exact (prop_ext (fun h2 : term323 _46262 _46263 => @lem4006718 _46262 _46263 h2) (fun h2 : False => @lem4006720 _46262 _46263 h1)). Qed.
Lemma lem4006722 (_46262 : int) (_46263 : int) (h1 : term224 _46262 _46263) : False.
Proof. exact (EQ_MP (@lem4006721 _46262 _46263 h1) (@lem4006720 _46262 _46263 h1)). Qed.
Lemma lem4006723 (_46262 : int) (_46263 : int) : term397 _46262 _46263.
Proof. exact (fun h0 : term224 _46262 _46263 => @lem4006722 _46262 _46263 h0). Qed.
Lemma lem4006724 (_46262 : int) (_46263 : int) : term398 _46262 _46263.
Proof. exact (@lem1386578 (term399 _46262 _46263)). Qed.
Lemma lem4006727 (_46262 : int) (_46263 : int) : term399 _46262 _46263.
Proof. exact (@lem4006724 _46262 _46263 (@lem4006723 _46262 _46263)). Qed.
Lemma lem4006728 (_46263 : int) (_46262 : int) : (term222 _46262 _46263) = (term185 _46263 _46262).
Proof. exact (SYM (@lem4005863 _46262 _46263)). Qed.
Lemma lem4006729 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4006730 (_46263 : int) (_46262 : int) : (term399 _46262 _46263) = (term166 _46263 _46262).
Proof. exact (MK_COMB (@lem4006729) (@lem4006728 _46263 _46262)). Qed.
Lemma lem4006731 (_46263 : int) (_46262 : int) : term166 _46263 _46262.
Proof. exact (EQ_MP (@lem4006730 _46263 _46262) (@lem4006727 _46262 _46263)). Qed.
Lemma lem4006732 (_46263 : int) (_46262 : int) : term167 _46263 _46262.
Proof. exact (EQ_MP (@lem4005742 _46263 _46262) (@lem4006731 _46263 _46262)). Qed.
Lemma lem4006733 {A B : Type'} (f : A -> B) (s : A -> Prop) : term400 A B f s.
Proof. exact (@lem4006732 (term401 A B f s) (term402 A s)). Qed.
Lemma lem4006734 {A B : Type'} (f : A -> B) (s : A -> Prop) : term403 A B f s.
Proof. exact (@lem4006733 A B f s (@lem4005738 A s)). Qed.
Lemma lem4006735 {A B : Type'} (f : A -> B) (s : A -> Prop) : term161 A B f s.
Proof. exact (@lem4006734 A B f s (@lem4005741 A B f s)). Qed.
Lemma lem4006736 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term161 A B f s) = (term139 A B f s).
Proof. exact (SYM (@lem4005735 A B f s)). Qed.
Lemma lem4006737 {A B : Type'} (f : A -> B) (s : A -> Prop) : term139 A B f s.
Proof. exact (EQ_MP (@lem4006736 A B f s) (@lem4006735 A B f s)). Qed.
Lemma lem4006738 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term139 A B f s) = ((term139 A B f s) = True).
Proof. exact (@lem7 (term139 A B f s)). Qed.
Lemma lem4006739 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term139 A B f s) = True.
Proof. exact (EQ_MP (@lem4006738 A B f s) (@lem4006737 A B f s)). Qed.
Lemma lem4006740 {A B : Type'} (f : A -> B) (s : A -> Prop) : True = (term139 A B f s).
Proof. exact (SYM (@lem4006739 A B f s)). Qed.
Lemma lem4006741 {A B : Type'} (f : A -> B) (s : A -> Prop) : term139 A B f s.
Proof. exact (EQ_MP (@lem4006740 A B f s) (@lem0)). Qed.
Lemma lem4006766 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term404 A B f s) = (term405 A B f s).
Proof. exact (@lem17265 (term27 A B f s) (term406 A B f s)). Qed.
Lemma lem4006768 (m : nat) : (S m) = (term142 m).
Proof. exact (EQ_MP (@lem2841417 m) (@lem2841416 m)). Qed.
Lemma lem4006769 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term123 A B f s) = (term407 A B f s).
Proof. exact (@lem4006768 (term121 A B f s)). Qed.
Lemma lem4006770 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem4006771 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term408 A B f s) = (term409 A B f s).
Proof. exact (MK_COMB (@lem4006770) (@lem4006769 A B f s)). Qed.
Lemma lem4006773 (m : nat) : (S m) = (term142 m).
Proof. exact (EQ_MP (@lem2841417 m) (@lem2841416 m)). Qed.
Lemma lem4006774 {A : Type'} (s : A -> Prop) : (term90 A s) = (term143 A s).
Proof. exact (@lem4006773 (@CARD A s)). Qed.
Lemma lem4006775 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term406 A B f s) = (term410 A B f s).
Proof. exact (MK_COMB (@lem4006771 A B f s) (@lem4006774 A s)). Qed.
Lemma lem4006776 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term146 A B f s) = (term146 A B f s).
Proof. exact (eq_refl (term146 A B f s)). Qed.
Lemma lem4006777 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term405 A B f s) = (term411 A B f s).
Proof. exact (MK_COMB (@lem4006776 A B f s) (@lem4006775 A B f s)). Qed.
Lemma lem4006808 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term404 A B f s) = (term411 A B f s).
Proof. exact (TRANS (@lem4006766 A B f s) (@lem4006777 A B f s)). Qed.
Lemma lem4006810 (m : nat) (n : nat) : (Peano.le m n) = (term148 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem4006811 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term27 A B f s) = (term149 A B f s).
Proof. exact (@lem4006810 (term121 A B f s) (@CARD A s)). Qed.
Lemma lem4006812 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4006813 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term150 A B f s) = (term151 A B f s).
Proof. exact (MK_COMB (@lem4006812) (@lem4006811 A B f s)). Qed.
Lemma lem4006814 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4006815 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term146 A B f s) = (term152 A B f s).
Proof. exact (MK_COMB (@lem4006814) (@lem4006813 A B f s)). Qed.
Lemma lem4006817 (m : nat) (n : nat) : (Peano.le m n) = (term148 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem4006818 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term410 A B f s) = (term412 A B f s).
Proof. exact (@lem4006817 (term407 A B f s) (term143 A s)). Qed.
Lemma lem4006820 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem4006821 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term413 A B f s) = (term414 A B f s).
Proof. exact (@lem4006820 (term121 A B f s) term158). Qed.
Lemma lem4006822 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem4006823 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term415 A B f s) = (term416 A B f s).
Proof. exact (MK_COMB (@lem4006822) (@lem4006821 A B f s)). Qed.
Lemma lem4006825 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem4006826 {A : Type'} (s : A -> Prop) : (term156 A s) = (term157 A s).
Proof. exact (@lem4006825 (@CARD A s) term158). Qed.
Lemma lem4006827 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term412 A B f s) = (term417 A B f s).
Proof. exact (MK_COMB (@lem4006823 A B f s) (@lem4006826 A s)). Qed.
Lemma lem4006828 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term410 A B f s) = (term417 A B f s).
Proof. exact (TRANS (@lem4006818 A B f s) (@lem4006827 A B f s)). Qed.
Lemma lem4006829 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term411 A B f s) = (term418 A B f s).
Proof. exact (MK_COMB (@lem4006815 A B f s) (@lem4006828 A B f s)). Qed.
Lemma lem4006830 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term404 A B f s) = (term418 A B f s).
Proof. exact (TRANS (@lem4006808 A B f s) (@lem4006829 A B f s)). Qed.
Lemma lem4006831 {A : Type'} (s : A -> Prop) : term162 A s.
Proof. exact (@lem2307535 (@CARD A s)). Qed.
Lemma lem4006832 {A : Type'} (s : A -> Prop) : (term162 A s) = (term163 A s).
Proof. exact (eq_refl (term162 A s)). Qed.
Lemma lem4006833 {A : Type'} (s : A -> Prop) : term163 A s.
Proof. exact (EQ_MP (@lem4006832 A s) (@lem4006831 A s)). Qed.
Lemma lem4006834 {A B : Type'} (f : A -> B) (s : A -> Prop) : term164 A B f s.
Proof. exact (@lem2307535 (term121 A B f s)). Qed.
Lemma lem4006835 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term164 A B f s) = (term165 A B f s).
Proof. exact (eq_refl (term164 A B f s)). Qed.
Lemma lem4006836 {A B : Type'} (f : A -> B) (s : A -> Prop) : term165 A B f s.
Proof. exact (EQ_MP (@lem4006835 A B f s) (@lem4006834 A B f s)). Qed.
Lemma lem4006837 (_46267 : int) (_46266 : int) : (term419 _46267 _46266) = (term420 _46267 _46266).
Proof. exact (@lem2318604 (term420 _46267 _46266)). Qed.
Lemma lem4006853 (_46267 : int) (_46266 : int) : (term168 _46267 _46266) = (int_le _46267 _46266).
Proof. exact (@lem16933 (int_le _46267 _46266)). Qed.
Lemma lem4006854 (_46267 : int) (_46266 : int) : (term421 _46267 _46266) = (term421 _46267 _46266).
Proof. exact (eq_refl (term421 _46267 _46266)). Qed.
Lemma lem4006855 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4006856 (_46267 : int) (_46266 : int) : (term170 _46267 _46266) = (term171 _46267 _46266).
Proof. exact (MK_COMB (@lem4006855) (@lem4006853 _46267 _46266)). Qed.
Lemma lem4006857 (_46267 : int) (_46266 : int) : (term422 _46267 _46266) = (term423 _46267 _46266).
Proof. exact (MK_COMB (@lem4006856 _46267 _46266) (@lem4006854 _46267 _46266)). Qed.
Lemma lem4006858 (_46267 : int) (_46266 : int) : (term424 _46267 _46266) = (term422 _46267 _46266).
Proof. exact (@lem17160 (term175 _46267 _46266) (term425 _46267 _46266)). Qed.
Lemma lem4006859 (_46267 : int) (_46266 : int) : (term424 _46267 _46266) = (term423 _46267 _46266).
Proof. exact (TRANS (@lem4006858 _46267 _46266) (@lem4006857 _46267 _46266)). Qed.
Lemma lem4006861 (_46267 : int) : (term177 _46267) = (term177 _46267).
Proof. exact (eq_refl (term177 _46267)). Qed.
Lemma lem4006862 (_46267 : int) (_46266 : int) : (term426 _46267 _46266) = (term427 _46267 _46266).
Proof. exact (MK_COMB (@lem4006861 _46267) (@lem4006859 _46267 _46266)). Qed.
Lemma lem4006863 (_46267 : int) (_46266 : int) : (term428 _46267 _46266) = (term426 _46267 _46266).
Proof. exact (@lem17362 (term181 _46267) (term429 _46267 _46266)). Qed.
Lemma lem4006864 (_46267 : int) (_46266 : int) : (term428 _46267 _46266) = (term427 _46267 _46266).
Proof. exact (TRANS (@lem4006863 _46267 _46266) (@lem4006862 _46267 _46266)). Qed.
Lemma lem4006866 (_46266 : int) : (term177 _46266) = (term177 _46266).
Proof. exact (eq_refl (term177 _46266)). Qed.
Lemma lem4006867 (_46267 : int) (_46266 : int) : (term430 _46267 _46266) = (term431 _46267 _46266).
Proof. exact (MK_COMB (@lem4006866 _46266) (@lem4006864 _46267 _46266)). Qed.
Lemma lem4006868 (_46267 : int) (_46266 : int) : (term432 _46267 _46266) = (term430 _46267 _46266).
Proof. exact (@lem17362 (term181 _46266) (term433 _46267 _46266)). Qed.
Lemma lem4006886 (_46267 : int) (_46266 : int) : (term432 _46267 _46266) = (term431 _46267 _46266).
Proof. exact (TRANS (@lem4006868 _46267 _46266) (@lem4006867 _46267 _46266)). Qed.
Lemma lem4006889 (x : int) (y : int) : (int_le x y) = (term187 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4006890 (_46266 : int) : (term181 _46266) = (term188 _46266).
Proof. exact (@lem4006889 term189 _46266). Qed.
Lemma lem4006892 (n : nat) : (term190 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4006893 : term191 = term192.
Proof. exact (@lem4006892 (NUMERAL 0)). Qed.
Lemma lem4006894 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4006895 : term193 = term194.
Proof. exact (MK_COMB (@lem4006894) (@lem4006893)). Qed.
Lemma lem4006896 (_46266 : int) : (real_of_int _46266) = (real_of_int _46266).
Proof. exact (eq_refl (real_of_int _46266)). Qed.
Lemma lem4006897 (_46266 : int) : (term188 _46266) = (term195 _46266).
Proof. exact (MK_COMB (@lem4006895) (@lem4006896 _46266)). Qed.
Lemma lem4006899 (_46266 : int) : (term181 _46266) = (term195 _46266).
Proof. exact (TRANS (@lem4006890 _46266) (@lem4006897 _46266)). Qed.
Lemma lem4006902 (x : int) (y : int) : (int_le x y) = (term187 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4006903 (_46267 : int) : (term181 _46267) = (term188 _46267).
Proof. exact (@lem4006902 term189 _46267). Qed.
Lemma lem4006905 (n : nat) : (term190 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4006906 : term191 = term192.
Proof. exact (@lem4006905 (NUMERAL 0)). Qed.
Lemma lem4006907 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4006908 : term193 = term194.
Proof. exact (MK_COMB (@lem4006907) (@lem4006906)). Qed.
Lemma lem4006909 (_46267 : int) : (real_of_int _46267) = (real_of_int _46267).
Proof. exact (eq_refl (real_of_int _46267)). Qed.
Lemma lem4006910 (_46267 : int) : (term188 _46267) = (term195 _46267).
Proof. exact (MK_COMB (@lem4006908) (@lem4006909 _46267)). Qed.
Lemma lem4006912 (_46267 : int) : (term181 _46267) = (term195 _46267).
Proof. exact (TRANS (@lem4006903 _46267) (@lem4006910 _46267)). Qed.
Lemma lem4006915 (x : int) (y : int) : (int_le x y) = (term187 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4006917 (_46267 : int) (_46266 : int) : (int_le _46267 _46266) = (term187 _46267 _46266).
Proof. exact (@lem4006915 _46267 _46266). Qed.
Lemma lem4006919 (y : int) (x : int) : (term175 x y) = (term196 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem4006920 (_46266 : int) (_46267 : int) : (term421 _46267 _46266) = (term434 _46266 _46267).
Proof. exact (@lem4006919 (term198 _46266) (term198 _46267)). Qed.
Lemma lem4006922 (x : int) (y : int) : (int_le x y) = (term187 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem4006923 (_46266 : int) (_46267 : int) : (term434 _46266 _46267) = (term435 _46266 _46267).
Proof. exact (@lem4006922 (term200 _46266) (term198 _46267)). Qed.
Lemma lem4006925 (x : int) (y : int) : (term201 x y) = (term202 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem4006926 (_46266 : int) : (term203 _46266) = (term204 _46266).
Proof. exact (@lem4006925 (term198 _46266) term205). Qed.
Lemma lem4006928 (x : int) (y : int) : (term201 x y) = (term202 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem4006929 (_46266 : int) : (term206 _46266) = (term207 _46266).
Proof. exact (@lem4006928 _46266 term205). Qed.
Lemma lem4006931 (n : nat) : (term190 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4006932 : term208 = term209.
Proof. exact (@lem4006931 term158). Qed.
Lemma lem4006933 (_46266 : int) : (term210 _46266) = (term210 _46266).
Proof. exact (eq_refl (term210 _46266)). Qed.
Lemma lem4006934 (_46266 : int) : (term207 _46266) = (term211 _46266).
Proof. exact (MK_COMB (@lem4006933 _46266) (@lem4006932)). Qed.
Lemma lem4006935 (_46266 : int) : (term206 _46266) = (term211 _46266).
Proof. exact (TRANS (@lem4006929 _46266) (@lem4006934 _46266)). Qed.
Lemma lem4006936 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4006937 (_46266 : int) : (term212 _46266) = (term213 _46266).
Proof. exact (MK_COMB (@lem4006936) (@lem4006935 _46266)). Qed.
Lemma lem4006939 (n : nat) : (term190 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4006940 : term208 = term209.
Proof. exact (@lem4006939 term158). Qed.
Lemma lem4006941 (_46266 : int) : (term204 _46266) = (term214 _46266).
Proof. exact (MK_COMB (@lem4006937 _46266) (@lem4006940)). Qed.
Lemma lem4006942 (_46266 : int) : (term203 _46266) = (term214 _46266).
Proof. exact (TRANS (@lem4006926 _46266) (@lem4006941 _46266)). Qed.
Lemma lem4006943 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4006944 (_46266 : int) : (term215 _46266) = (term216 _46266).
Proof. exact (MK_COMB (@lem4006943) (@lem4006942 _46266)). Qed.
Lemma lem4006946 (x : int) (y : int) : (term201 x y) = (term202 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem4006947 (_46267 : int) : (term206 _46267) = (term207 _46267).
Proof. exact (@lem4006946 _46267 term205). Qed.
Lemma lem4006949 (n : nat) : (term190 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem4006950 : term208 = term209.
Proof. exact (@lem4006949 term158). Qed.
Lemma lem4006951 (_46267 : int) : (term210 _46267) = (term210 _46267).
Proof. exact (eq_refl (term210 _46267)). Qed.
Lemma lem4006952 (_46267 : int) : (term207 _46267) = (term211 _46267).
Proof. exact (MK_COMB (@lem4006951 _46267) (@lem4006950)). Qed.
Lemma lem4006953 (_46267 : int) : (term206 _46267) = (term211 _46267).
Proof. exact (TRANS (@lem4006947 _46267) (@lem4006952 _46267)). Qed.
Lemma lem4006954 (_46266 : int) (_46267 : int) : (term435 _46266 _46267) = (term436 _46266 _46267).
Proof. exact (MK_COMB (@lem4006944 _46266) (@lem4006953 _46267)). Qed.
Lemma lem4006955 (_46266 : int) (_46267 : int) : (term434 _46266 _46267) = (term436 _46266 _46267).
Proof. exact (TRANS (@lem4006923 _46266 _46267) (@lem4006954 _46266 _46267)). Qed.
Lemma lem4006956 (_46266 : int) (_46267 : int) : (term421 _46267 _46266) = (term436 _46266 _46267).
Proof. exact (TRANS (@lem4006920 _46266 _46267) (@lem4006955 _46266 _46267)). Qed.
Lemma lem4006957 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4006958 (_46267 : int) (_46266 : int) : (term171 _46267 _46266) = (term218 _46267 _46266).
Proof. exact (MK_COMB (@lem4006957) (@lem4006917 _46267 _46266)). Qed.
Lemma lem4006959 (_46266 : int) (_46267 : int) : (term423 _46267 _46266) = (term437 _46266 _46267).
Proof. exact (MK_COMB (@lem4006958 _46267 _46266) (@lem4006956 _46266 _46267)). Qed.
Lemma lem4006960 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4006961 (_46267 : int) : (term177 _46267) = (term220 _46267).
Proof. exact (MK_COMB (@lem4006960) (@lem4006912 _46267)). Qed.
Lemma lem4006962 (_46266 : int) (_46267 : int) : (term427 _46267 _46266) = (term438 _46266 _46267).
Proof. exact (MK_COMB (@lem4006961 _46267) (@lem4006959 _46266 _46267)). Qed.
Lemma lem4006963 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4006964 (_46266 : int) : (term177 _46266) = (term220 _46266).
Proof. exact (MK_COMB (@lem4006963) (@lem4006899 _46266)). Qed.
Lemma lem4006965 (_46266 : int) (_46267 : int) : (term431 _46267 _46266) = (term439 _46266 _46267).
Proof. exact (MK_COMB (@lem4006964 _46266) (@lem4006962 _46266 _46267)). Qed.
Lemma lem4006966 (_46266 : int) (_46267 : int) : (term432 _46267 _46266) = (term439 _46266 _46267).
Proof. exact (TRANS (@lem4006886 _46267 _46266) (@lem4006965 _46266 _46267)). Qed.
Lemma lem4006970 (t : Prop) : (term223 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4007006 (_46266 : int) (_46267 : int) : (term440 _46266 _46267) = (term439 _46266 _46267).
Proof. exact (@lem4006970 (term439 _46266 _46267)). Qed.
Lemma lem4007007 (_46266 : int) : (term195 _46266) = (term225 _46266).
Proof. exact (@lem1988287 (real_of_int _46266) term192). Qed.
Lemma lem4007013 (_46266 : int) : (term226 _46266) = (term227 _46266).
Proof. exact (@lem1982792 (real_of_int _46266) term192). Qed.
Lemma lem4007015 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4007016 : term192 = term229.
Proof. exact (@lem4007015 (NUMERAL 0)). Qed.
Lemma lem4007018 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4007019 : term232 = term233.
Proof. exact (@lem4007018 term158). Qed.
Lemma lem4007020 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4007021 : term234 = term235.
Proof. exact (MK_COMB (@lem4007020) (@lem4007019)). Qed.
Lemma lem4007022 : term236 = term237.
Proof. exact (MK_COMB (@lem4007021) (@lem4007016)). Qed.
Lemma lem4007023 : term237 = term238.
Proof. exact (@lem1981613 term232 term192 term209 term209). Qed.
Lemma lem4007025 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4007026 : term241 = term242.
Proof. exact (@lem4007025 term158 term158). Qed.
Lemma lem4007027 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4007028 : term244 = term158.
Proof. exact (EQ_MP (@lem4007027) (@lem940073)). Qed.
Lemma lem4007029 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4007030 : term242 = term209.
Proof. exact (MK_COMB (@lem4007029) (@lem4007028)). Qed.
Lemma lem4007031 : term241 = term209.
Proof. exact (TRANS (@lem4007026) (@lem4007030)). Qed.
Lemma lem4007033 (x : nat) : (term245 x) = term192.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem4007034 : term236 = term192.
Proof. exact (@lem4007033 term158). Qed.
Lemma lem4007035 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4007036 : term246 = term247.
Proof. exact (MK_COMB (@lem4007035) (@lem4007034)). Qed.
Lemma lem4007037 : term238 = term229.
Proof. exact (MK_COMB (@lem4007036) (@lem4007031)). Qed.
Lemma lem4007038 : term237 = term229.
Proof. exact (TRANS (@lem4007023) (@lem4007037)). Qed.
Lemma lem4007039 : term236 = term229.
Proof. exact (TRANS (@lem4007022) (@lem4007038)). Qed.
Lemma lem4007041 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4007042 : term229 = term192.
Proof. exact (@lem4007041 term192). Qed.
Lemma lem4007043 : term236 = term192.
Proof. exact (TRANS (@lem4007039) (@lem4007042)). Qed.
Lemma lem4007044 (_46266 : int) : (term210 _46266) = (term210 _46266).
Proof. exact (eq_refl (term210 _46266)). Qed.
Lemma lem4007045 (_46266 : int) : (term227 _46266) = (term249 _46266).
Proof. exact (MK_COMB (@lem4007044 _46266) (@lem4007043)). Qed.
Lemma lem4007046 (_46266 : int) : (term249 _46266) = (real_of_int _46266).
Proof. exact (@lem1982723 (real_of_int _46266)). Qed.
Lemma lem4007047 (_46266 : int) : (term227 _46266) = (real_of_int _46266).
Proof. exact (TRANS (@lem4007045 _46266) (@lem4007046 _46266)). Qed.
Lemma lem4007049 (_46266 : int) : (term226 _46266) = (real_of_int _46266).
Proof. exact (TRANS (@lem4007013 _46266) (@lem4007047 _46266)). Qed.
Lemma lem4007050 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4007051 (_46266 : int) : (term250 _46266) = (term251 _46266).
Proof. exact (MK_COMB (@lem4007050) (@lem4007049 _46266)). Qed.
Lemma lem4007052 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem4007053 (_46266 : int) : (term225 _46266) = (term252 _46266).
Proof. exact (MK_COMB (@lem4007051 _46266) (@lem4007052)). Qed.
Lemma lem4007054 (_46266 : int) : (term195 _46266) = (term252 _46266).
Proof. exact (TRANS (@lem4007007 _46266) (@lem4007053 _46266)). Qed.
Lemma lem4007055 (_46267 : int) : (term195 _46267) = (term225 _46267).
Proof. exact (@lem1988287 (real_of_int _46267) term192). Qed.
Lemma lem4007061 (_46267 : int) : (term226 _46267) = (term227 _46267).
Proof. exact (@lem1982792 (real_of_int _46267) term192). Qed.
Lemma lem4007063 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4007064 : term192 = term229.
Proof. exact (@lem4007063 (NUMERAL 0)). Qed.
Lemma lem4007066 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4007067 : term232 = term233.
Proof. exact (@lem4007066 term158). Qed.
Lemma lem4007068 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4007069 : term234 = term235.
Proof. exact (MK_COMB (@lem4007068) (@lem4007067)). Qed.
Lemma lem4007070 : term236 = term237.
Proof. exact (MK_COMB (@lem4007069) (@lem4007064)). Qed.
Lemma lem4007071 : term237 = term238.
Proof. exact (@lem1981613 term232 term192 term209 term209). Qed.
Lemma lem4007073 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4007074 : term241 = term242.
Proof. exact (@lem4007073 term158 term158). Qed.
Lemma lem4007075 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4007076 : term244 = term158.
Proof. exact (EQ_MP (@lem4007075) (@lem940073)). Qed.
Lemma lem4007077 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4007078 : term242 = term209.
Proof. exact (MK_COMB (@lem4007077) (@lem4007076)). Qed.
Lemma lem4007079 : term241 = term209.
Proof. exact (TRANS (@lem4007074) (@lem4007078)). Qed.
Lemma lem4007081 (x : nat) : (term245 x) = term192.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem4007082 : term236 = term192.
Proof. exact (@lem4007081 term158). Qed.
Lemma lem4007083 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4007084 : term246 = term247.
Proof. exact (MK_COMB (@lem4007083) (@lem4007082)). Qed.
Lemma lem4007085 : term238 = term229.
Proof. exact (MK_COMB (@lem4007084) (@lem4007079)). Qed.
Lemma lem4007086 : term237 = term229.
Proof. exact (TRANS (@lem4007071) (@lem4007085)). Qed.
Lemma lem4007087 : term236 = term229.
Proof. exact (TRANS (@lem4007070) (@lem4007086)). Qed.
Lemma lem4007089 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4007090 : term229 = term192.
Proof. exact (@lem4007089 term192). Qed.
Lemma lem4007091 : term236 = term192.
Proof. exact (TRANS (@lem4007087) (@lem4007090)). Qed.
Lemma lem4007092 (_46267 : int) : (term210 _46267) = (term210 _46267).
Proof. exact (eq_refl (term210 _46267)). Qed.
Lemma lem4007093 (_46267 : int) : (term227 _46267) = (term249 _46267).
Proof. exact (MK_COMB (@lem4007092 _46267) (@lem4007091)). Qed.
Lemma lem4007094 (_46267 : int) : (term249 _46267) = (real_of_int _46267).
Proof. exact (@lem1982723 (real_of_int _46267)). Qed.
Lemma lem4007095 (_46267 : int) : (term227 _46267) = (real_of_int _46267).
Proof. exact (TRANS (@lem4007093 _46267) (@lem4007094 _46267)). Qed.
Lemma lem4007097 (_46267 : int) : (term226 _46267) = (real_of_int _46267).
Proof. exact (TRANS (@lem4007061 _46267) (@lem4007095 _46267)). Qed.
Lemma lem4007098 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4007099 (_46267 : int) : (term250 _46267) = (term251 _46267).
Proof. exact (MK_COMB (@lem4007098) (@lem4007097 _46267)). Qed.
Lemma lem4007100 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem4007101 (_46267 : int) : (term225 _46267) = (term252 _46267).
Proof. exact (MK_COMB (@lem4007099 _46267) (@lem4007100)). Qed.
Lemma lem4007102 (_46267 : int) : (term195 _46267) = (term252 _46267).
Proof. exact (TRANS (@lem4007055 _46267) (@lem4007101 _46267)). Qed.
Lemma lem4007103 (_46266 : int) (_46267 : int) : (term187 _46267 _46266) = (term253 _46266 _46267).
Proof. exact (@lem1988287 (real_of_int _46266) (real_of_int _46267)). Qed.
Lemma lem4007116 (_46266 : int) (_46267 : int) : (term254 _46266 _46267) = (term255 _46266 _46267).
Proof. exact (@lem1982792 (real_of_int _46266) (real_of_int _46267)). Qed.
Lemma lem4007117 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4007118 (_46266 : int) (_46267 : int) : (term256 _46266 _46267) = (term257 _46266 _46267).
Proof. exact (MK_COMB (@lem4007117) (@lem4007116 _46266 _46267)). Qed.
Lemma lem4007119 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem4007120 (_46266 : int) (_46267 : int) : (term253 _46266 _46267) = (term258 _46266 _46267).
Proof. exact (MK_COMB (@lem4007118 _46266 _46267) (@lem4007119)). Qed.
Lemma lem4007121 (_46266 : int) (_46267 : int) : (term187 _46267 _46266) = (term258 _46266 _46267).
Proof. exact (TRANS (@lem4007103 _46266 _46267) (@lem4007120 _46266 _46267)). Qed.
Lemma lem4007122 (_46267 : int) (_46266 : int) : (term436 _46266 _46267) = (term441 _46267 _46266).
Proof. exact (@lem1988287 (term211 _46267) (term214 _46266)). Qed.
Lemma lem4007134 (_46266 : int) : (term214 _46266) = (term260 _46266).
Proof. exact (@lem1982755 (real_of_int _46266) term209 term209). Qed.
Lemma lem4007136 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4007137 : term209 = term261.
Proof. exact (@lem4007136 term158). Qed.
Lemma lem4007139 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4007140 : term209 = term261.
Proof. exact (@lem4007139 term158). Qed.
Lemma lem4007141 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4007142 : term262 = term263.
Proof. exact (MK_COMB (@lem4007141) (@lem4007140)). Qed.
Lemma lem4007143 : term264 = term265.
Proof. exact (MK_COMB (@lem4007142) (@lem4007137)). Qed.
Lemma lem4007144 : term266.
Proof. exact (@lem1981473 term209 term209 term209 term209 term267 term209). Qed.
Lemma lem4007146 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4007147 : term269 = term270.
Proof. exact (@lem4007146 (NUMERAL 0) term158). Qed.
Lemma lem4007148 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4007149 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4007150 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4007149 h1) (fun h1 : term270 = True => @lem4007148)). Qed.
Lemma lem4007151 : term270 = True.
Proof. exact (EQ_MP (@lem4007150) (@lem4007148)). Qed.
Lemma lem4007152 : term269 = True.
Proof. exact (TRANS (@lem4007147) (@lem4007151)). Qed.
Lemma lem4007153 : True = term269.
Proof. exact (SYM (@lem4007152)). Qed.
Lemma lem4007154 : term269.
Proof. exact (EQ_MP (@lem4007153) (@lem0)). Qed.
Lemma lem4007155 : term272.
Proof. exact (@lem4007144 (@lem4007154)). Qed.
Lemma lem4007157 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4007158 : term269 = term270.
Proof. exact (@lem4007157 (NUMERAL 0) term158). Qed.
Lemma lem4007159 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4007160 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4007161 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4007160 h1) (fun h1 : term270 = True => @lem4007159)). Qed.
Lemma lem4007162 : term270 = True.
Proof. exact (EQ_MP (@lem4007161) (@lem4007159)). Qed.
Lemma lem4007163 : term269 = True.
Proof. exact (TRANS (@lem4007158) (@lem4007162)). Qed.
Lemma lem4007164 : True = term269.
Proof. exact (SYM (@lem4007163)). Qed.
Lemma lem4007165 : term269.
Proof. exact (EQ_MP (@lem4007164) (@lem0)). Qed.
Lemma lem4007166 : term273.
Proof. exact (@lem4007155 (@lem4007165)). Qed.
Lemma lem4007168 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4007169 : term269 = term270.
Proof. exact (@lem4007168 (NUMERAL 0) term158). Qed.
Lemma lem4007170 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4007171 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4007172 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4007171 h1) (fun h1 : term270 = True => @lem4007170)). Qed.
Lemma lem4007173 : term270 = True.
Proof. exact (EQ_MP (@lem4007172) (@lem4007170)). Qed.
Lemma lem4007174 : term269 = True.
Proof. exact (TRANS (@lem4007169) (@lem4007173)). Qed.
Lemma lem4007175 : True = term269.
Proof. exact (SYM (@lem4007174)). Qed.
Lemma lem4007176 : term269.
Proof. exact (EQ_MP (@lem4007175) (@lem0)). Qed.
Lemma lem4007177 : term274.
Proof. exact (@lem4007166 (@lem4007176)). Qed.
Lemma lem4007179 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4007180 : term241 = term242.
Proof. exact (@lem4007179 term158 term158). Qed.
Lemma lem4007181 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4007182 : term244 = term158.
Proof. exact (EQ_MP (@lem4007181) (@lem940073)). Qed.
Lemma lem4007183 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4007184 : term242 = term209.
Proof. exact (MK_COMB (@lem4007183) (@lem4007182)). Qed.
Lemma lem4007185 : term241 = term209.
Proof. exact (TRANS (@lem4007180) (@lem4007184)). Qed.
Lemma lem4007187 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4007188 : term241 = term242.
Proof. exact (@lem4007187 term158 term158). Qed.
Lemma lem4007189 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4007190 : term244 = term158.
Proof. exact (EQ_MP (@lem4007189) (@lem940073)). Qed.
Lemma lem4007191 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4007192 : term242 = term209.
Proof. exact (MK_COMB (@lem4007191) (@lem4007190)). Qed.
Lemma lem4007193 : term241 = term209.
Proof. exact (TRANS (@lem4007188) (@lem4007192)). Qed.
Lemma lem4007194 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4007195 : term275 = term262.
Proof. exact (MK_COMB (@lem4007194) (@lem4007193)). Qed.
Lemma lem4007196 : term276 = term264.
Proof. exact (MK_COMB (@lem4007195) (@lem4007185)). Qed.
Lemma lem4007197 : term264 = term277.
Proof. exact (@lem1367770 term158 term158). Qed.
Lemma lem4007198 : term278 = term279.
Proof. exact (@lem706885). Qed.
Lemma lem4007199 : (term278 = term279) = (term280 = term281).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term279). Qed.
Lemma lem4007200 : term280 = term281.
Proof. exact (EQ_MP (@lem4007199) (@lem4007198)). Qed.
Lemma lem4007201 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4007202 : term277 = term267.
Proof. exact (MK_COMB (@lem4007201) (@lem4007200)). Qed.
Lemma lem4007203 : term264 = term267.
Proof. exact (TRANS (@lem4007197) (@lem4007202)). Qed.
Lemma lem4007204 : term276 = term267.
Proof. exact (TRANS (@lem4007196) (@lem4007203)). Qed.
Lemma lem4007205 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4007206 : term282 = term283.
Proof. exact (MK_COMB (@lem4007205) (@lem4007204)). Qed.
Lemma lem4007207 : term209 = term209.
Proof. exact (eq_refl term209). Qed.
Lemma lem4007208 : term284 = term285.
Proof. exact (MK_COMB (@lem4007206) (@lem4007207)). Qed.
Lemma lem4007210 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4007211 : term285 = term286.
Proof. exact (@lem4007210 term281 term158). Qed.
Lemma lem4007212 : term287 = term279.
Proof. exact (@lem996237 term279). Qed.
Lemma lem4007213 : (term287 = term279) = (term288 = term281).
Proof. exact (@lem1007663 term279 (BIT1 0) term279). Qed.
Lemma lem4007214 : term288 = term281.
Proof. exact (EQ_MP (@lem4007213) (@lem4007212)). Qed.
Lemma lem4007215 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4007216 : term286 = term267.
Proof. exact (MK_COMB (@lem4007215) (@lem4007214)). Qed.
Lemma lem4007217 : term285 = term267.
Proof. exact (TRANS (@lem4007211) (@lem4007216)). Qed.
Lemma lem4007218 : term284 = term267.
Proof. exact (TRANS (@lem4007208) (@lem4007217)). Qed.
Lemma lem4007220 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4007221 : term241 = term242.
Proof. exact (@lem4007220 term158 term158). Qed.
Lemma lem4007222 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4007223 : term244 = term158.
Proof. exact (EQ_MP (@lem4007222) (@lem940073)). Qed.
Lemma lem4007224 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4007225 : term242 = term209.
Proof. exact (MK_COMB (@lem4007224) (@lem4007223)). Qed.
Lemma lem4007226 : term241 = term209.
Proof. exact (TRANS (@lem4007221) (@lem4007225)). Qed.
Lemma lem4007227 : term283 = term283.
Proof. exact (eq_refl term283). Qed.
Lemma lem4007228 : term289 = term285.
Proof. exact (MK_COMB (@lem4007227) (@lem4007226)). Qed.
Lemma lem4007230 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4007231 : term285 = term286.
Proof. exact (@lem4007230 term281 term158). Qed.
Lemma lem4007232 : term287 = term279.
Proof. exact (@lem996237 term279). Qed.
Lemma lem4007233 : (term287 = term279) = (term288 = term281).
Proof. exact (@lem1007663 term279 (BIT1 0) term279). Qed.
Lemma lem4007234 : term288 = term281.
Proof. exact (EQ_MP (@lem4007233) (@lem4007232)). Qed.
Lemma lem4007235 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4007236 : term286 = term267.
Proof. exact (MK_COMB (@lem4007235) (@lem4007234)). Qed.
Lemma lem4007237 : term285 = term267.
Proof. exact (TRANS (@lem4007231) (@lem4007236)). Qed.
Lemma lem4007238 : term289 = term267.
Proof. exact (TRANS (@lem4007228) (@lem4007237)). Qed.
Lemma lem4007239 : term267 = term289.
Proof. exact (SYM (@lem4007238)). Qed.
Lemma lem4007240 : term284 = term289.
Proof. exact (TRANS (@lem4007218) (@lem4007239)). Qed.
Lemma lem4007241 : term265 = term290.
Proof. exact (@lem4007177 (@lem4007240)). Qed.
Lemma lem4007242 : term264 = term290.
Proof. exact (TRANS (@lem4007143) (@lem4007241)). Qed.
Lemma lem4007244 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4007245 : term290 = term267.
Proof. exact (@lem4007244 term267). Qed.
Lemma lem4007246 : term264 = term267.
Proof. exact (TRANS (@lem4007242) (@lem4007245)). Qed.
Lemma lem4007247 (_46266 : int) : (term210 _46266) = (term210 _46266).
Proof. exact (eq_refl (term210 _46266)). Qed.
Lemma lem4007248 (_46266 : int) : (term260 _46266) = (term291 _46266).
Proof. exact (MK_COMB (@lem4007247 _46266) (@lem4007246)). Qed.
Lemma lem4007250 (_46266 : int) : (term214 _46266) = (term291 _46266).
Proof. exact (TRANS (@lem4007134 _46266) (@lem4007248 _46266)). Qed.
Lemma lem4007259 (_46267 : int) : (term442 _46267) = (term442 _46267).
Proof. exact (eq_refl (term442 _46267)). Qed.
Lemma lem4007260 (_46267 : int) (_46266 : int) : (term443 _46267 _46266) = (term444 _46267 _46266).
Proof. exact (MK_COMB (@lem4007259 _46267) (@lem4007250 _46266)). Qed.
Lemma lem4007261 (_46267 : int) (_46266 : int) : (term444 _46267 _46266) = (term445 _46267 _46266).
Proof. exact (@lem1982792 (term211 _46267) (term291 _46266)). Qed.
Lemma lem4007262 (_46266 : int) : (term296 _46266) = (term297 _46266).
Proof. exact (@lem1982781 (real_of_int _46266) term232 term267). Qed.
Lemma lem4007264 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4007265 : term267 = term290.
Proof. exact (@lem4007264 term281). Qed.
Lemma lem4007267 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4007268 : term232 = term233.
Proof. exact (@lem4007267 term158). Qed.
Lemma lem4007269 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4007270 : term234 = term235.
Proof. exact (MK_COMB (@lem4007269) (@lem4007268)). Qed.
Lemma lem4007271 : term298 = term299.
Proof. exact (MK_COMB (@lem4007270) (@lem4007265)). Qed.
Lemma lem4007272 : term299 = term300.
Proof. exact (@lem1981613 term232 term267 term209 term209). Qed.
Lemma lem4007274 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4007275 : term241 = term242.
Proof. exact (@lem4007274 term158 term158). Qed.
Lemma lem4007276 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4007277 : term244 = term158.
Proof. exact (EQ_MP (@lem4007276) (@lem940073)). Qed.
Lemma lem4007278 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4007279 : term242 = term209.
Proof. exact (MK_COMB (@lem4007278) (@lem4007277)). Qed.
Lemma lem4007280 : term241 = term209.
Proof. exact (TRANS (@lem4007275) (@lem4007279)). Qed.
Lemma lem4007282 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4007283 : term298 = term303.
Proof. exact (@lem4007282 term158 term281). Qed.
Lemma lem4007284 : term304 = term279.
Proof. exact (@lem996238 term279). Qed.
Lemma lem4007285 : (term304 = term279) = (term305 = term281).
Proof. exact (@lem1007663 (BIT1 0) term279 term279). Qed.
Lemma lem4007286 : term305 = term281.
Proof. exact (EQ_MP (@lem4007285) (@lem4007284)). Qed.
Lemma lem4007287 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4007288 : term306 = term267.
Proof. exact (MK_COMB (@lem4007287) (@lem4007286)). Qed.
Lemma lem4007289 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4007290 : term303 = term307.
Proof. exact (MK_COMB (@lem4007289) (@lem4007288)). Qed.
Lemma lem4007291 : term298 = term307.
Proof. exact (TRANS (@lem4007283) (@lem4007290)). Qed.
Lemma lem4007292 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem4007293 : term308 = term309.
Proof. exact (MK_COMB (@lem4007292) (@lem4007291)). Qed.
Lemma lem4007294 : term300 = term310.
Proof. exact (MK_COMB (@lem4007293) (@lem4007280)). Qed.
Lemma lem4007295 : term299 = term310.
Proof. exact (TRANS (@lem4007272) (@lem4007294)). Qed.
Lemma lem4007296 : term298 = term310.
Proof. exact (TRANS (@lem4007271) (@lem4007295)). Qed.
Lemma lem4007298 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem4007299 : term310 = term307.
Proof. exact (@lem4007298 term307). Qed.
Lemma lem4007300 : term298 = term307.
Proof. exact (TRANS (@lem4007296) (@lem4007299)). Qed.
Lemma lem4007303 (_46266 : int) : (term311 _46266) = (term311 _46266).
Proof. exact (eq_refl (term311 _46266)). Qed.
Lemma lem4007304 (_46266 : int) : (term297 _46266) = (term312 _46266).
Proof. exact (MK_COMB (@lem4007303 _46266) (@lem4007300)). Qed.
Lemma lem4007305 (_46266 : int) : (term296 _46266) = (term312 _46266).
Proof. exact (TRANS (@lem4007262 _46266) (@lem4007304 _46266)). Qed.
Lemma lem4007306 (_46267 : int) : (term213 _46267) = (term213 _46267).
Proof. exact (eq_refl (term213 _46267)). Qed.
Lemma lem4007307 (_46267 : int) (_46266 : int) : (term445 _46267 _46266) = (term446 _46267 _46266).
Proof. exact (MK_COMB (@lem4007306 _46267) (@lem4007305 _46266)). Qed.
Lemma lem4007308 (_46266 : int) (_46267 : int) : (term446 _46267 _46266) = (term447 _46266 _46267).
Proof. exact (@lem1982757 (term315 _46266) (term211 _46267) term307). Qed.
Lemma lem4007309 (_46267 : int) : (term448 _46267) = (term449 _46267).
Proof. exact (@lem1982755 (real_of_int _46267) term209 term307). Qed.
Lemma lem4007311 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4007312 : term307 = term310.
Proof. exact (@lem4007311 term281). Qed.
Lemma lem4007314 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4007315 : term209 = term261.
Proof. exact (@lem4007314 term158). Qed.
Lemma lem4007316 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4007317 : term262 = term263.
Proof. exact (MK_COMB (@lem4007316) (@lem4007315)). Qed.
Lemma lem4007318 : term450 = term451.
Proof. exact (MK_COMB (@lem4007317) (@lem4007312)). Qed.
Lemma lem4007319 : term452.
Proof. exact (@lem1981473 term209 term209 term307 term209 term232 term209). Qed.
Lemma lem4007321 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4007322 : term269 = term270.
Proof. exact (@lem4007321 (NUMERAL 0) term158). Qed.
Lemma lem4007323 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4007324 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4007325 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4007324 h1) (fun h1 : term270 = True => @lem4007323)). Qed.
Lemma lem4007326 : term270 = True.
Proof. exact (EQ_MP (@lem4007325) (@lem4007323)). Qed.
Lemma lem4007327 : term269 = True.
Proof. exact (TRANS (@lem4007322) (@lem4007326)). Qed.
Lemma lem4007328 : True = term269.
Proof. exact (SYM (@lem4007327)). Qed.
Lemma lem4007329 : term269.
Proof. exact (EQ_MP (@lem4007328) (@lem0)). Qed.
Lemma lem4007330 : term453.
Proof. exact (@lem4007319 (@lem4007329)). Qed.
Lemma lem4007332 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4007333 : term269 = term270.
Proof. exact (@lem4007332 (NUMERAL 0) term158). Qed.
Lemma lem4007334 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4007335 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4007336 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4007335 h1) (fun h1 : term270 = True => @lem4007334)). Qed.
Lemma lem4007337 : term270 = True.
Proof. exact (EQ_MP (@lem4007336) (@lem4007334)). Qed.
Lemma lem4007338 : term269 = True.
Proof. exact (TRANS (@lem4007333) (@lem4007337)). Qed.
Lemma lem4007339 : True = term269.
Proof. exact (SYM (@lem4007338)). Qed.
Lemma lem4007340 : term269.
Proof. exact (EQ_MP (@lem4007339) (@lem0)). Qed.
Lemma lem4007341 : term454.
Proof. exact (@lem4007330 (@lem4007340)). Qed.
Lemma lem4007343 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4007344 : term269 = term270.
Proof. exact (@lem4007343 (NUMERAL 0) term158). Qed.
Lemma lem4007345 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4007346 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4007347 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4007346 h1) (fun h1 : term270 = True => @lem4007345)). Qed.
Lemma lem4007348 : term270 = True.
Proof. exact (EQ_MP (@lem4007347) (@lem4007345)). Qed.
Lemma lem4007349 : term269 = True.
Proof. exact (TRANS (@lem4007344) (@lem4007348)). Qed.
Lemma lem4007350 : True = term269.
Proof. exact (SYM (@lem4007349)). Qed.
Lemma lem4007351 : term269.
Proof. exact (EQ_MP (@lem4007350) (@lem0)). Qed.
Lemma lem4007352 : term455.
Proof. exact (@lem4007341 (@lem4007351)). Qed.
Lemma lem4007354 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4007355 : term389 = term390.
Proof. exact (@lem4007354 term281 term158). Qed.
Lemma lem4007356 : term287 = term279.
Proof. exact (@lem996237 term279). Qed.
Lemma lem4007357 : (term287 = term279) = (term288 = term281).
Proof. exact (@lem1007663 term279 (BIT1 0) term279). Qed.
Lemma lem4007358 : term288 = term281.
Proof. exact (EQ_MP (@lem4007357) (@lem4007356)). Qed.
Lemma lem4007359 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4007360 : term286 = term267.
Proof. exact (MK_COMB (@lem4007359) (@lem4007358)). Qed.
Lemma lem4007361 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4007362 : term390 = term307.
Proof. exact (MK_COMB (@lem4007361) (@lem4007360)). Qed.
Lemma lem4007363 : term389 = term307.
Proof. exact (TRANS (@lem4007355) (@lem4007362)). Qed.
Lemma lem4007365 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4007366 : term241 = term242.
Proof. exact (@lem4007365 term158 term158). Qed.
Lemma lem4007367 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4007368 : term244 = term158.
Proof. exact (EQ_MP (@lem4007367) (@lem940073)). Qed.
Lemma lem4007369 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4007370 : term242 = term209.
Proof. exact (MK_COMB (@lem4007369) (@lem4007368)). Qed.
Lemma lem4007371 : term241 = term209.
Proof. exact (TRANS (@lem4007366) (@lem4007370)). Qed.
Lemma lem4007372 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4007373 : term275 = term262.
Proof. exact (MK_COMB (@lem4007372) (@lem4007371)). Qed.
Lemma lem4007374 : term456 = term450.
Proof. exact (MK_COMB (@lem4007373) (@lem4007363)). Qed.
Lemma lem4007377 : term457 = term232.
Proof. exact (@lem1367771 term158 term158). Qed.
Lemma lem4007378 : term278 = term279.
Proof. exact (@lem706885). Qed.
Lemma lem4007379 : (term278 = term279) = (term280 = term281).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term279). Qed.
Lemma lem4007380 : term280 = term281.
Proof. exact (EQ_MP (@lem4007379) (@lem4007378)). Qed.
Lemma lem4007381 : term281 = term280.
Proof. exact (SYM (@lem4007380)). Qed.
Lemma lem4007382 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4007383 : term267 = term277.
Proof. exact (MK_COMB (@lem4007382) (@lem4007381)). Qed.
Lemma lem4007384 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4007385 : term307 = term458.
Proof. exact (MK_COMB (@lem4007384) (@lem4007383)). Qed.
Lemma lem4007386 : term262 = term262.
Proof. exact (eq_refl term262). Qed.
Lemma lem4007387 : term450 = term457.
Proof. exact (MK_COMB (@lem4007386) (@lem4007385)). Qed.
Lemma lem4007388 : term450 = term232.
Proof. exact (TRANS (@lem4007387) (@lem4007377)). Qed.
Lemma lem4007389 : term456 = term232.
Proof. exact (TRANS (@lem4007374) (@lem4007388)). Qed.
Lemma lem4007390 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4007391 : term459 = term234.
Proof. exact (MK_COMB (@lem4007390) (@lem4007389)). Qed.
Lemma lem4007392 : term209 = term209.
Proof. exact (eq_refl term209). Qed.
Lemma lem4007393 : term460 = term362.
Proof. exact (MK_COMB (@lem4007391) (@lem4007392)). Qed.
Lemma lem4007395 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4007396 : term362 = term363.
Proof. exact (@lem4007395 term158 term158). Qed.
Lemma lem4007397 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4007398 : term244 = term158.
Proof. exact (EQ_MP (@lem4007397) (@lem940073)). Qed.
Lemma lem4007399 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4007400 : term242 = term209.
Proof. exact (MK_COMB (@lem4007399) (@lem4007398)). Qed.
Lemma lem4007401 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4007402 : term363 = term232.
Proof. exact (MK_COMB (@lem4007401) (@lem4007400)). Qed.
Lemma lem4007403 : term362 = term232.
Proof. exact (TRANS (@lem4007396) (@lem4007402)). Qed.
Lemma lem4007404 : term460 = term232.
Proof. exact (TRANS (@lem4007393) (@lem4007403)). Qed.
Lemma lem4007406 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4007407 : term241 = term242.
Proof. exact (@lem4007406 term158 term158). Qed.
Lemma lem4007408 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4007409 : term244 = term158.
Proof. exact (EQ_MP (@lem4007408) (@lem940073)). Qed.
Lemma lem4007410 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4007411 : term242 = term209.
Proof. exact (MK_COMB (@lem4007410) (@lem4007409)). Qed.
Lemma lem4007412 : term241 = term209.
Proof. exact (TRANS (@lem4007407) (@lem4007411)). Qed.
Lemma lem4007413 : term234 = term234.
Proof. exact (eq_refl term234). Qed.
Lemma lem4007414 : term461 = term362.
Proof. exact (MK_COMB (@lem4007413) (@lem4007412)). Qed.
Lemma lem4007416 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4007417 : term362 = term363.
Proof. exact (@lem4007416 term158 term158). Qed.
Lemma lem4007418 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4007419 : term244 = term158.
Proof. exact (EQ_MP (@lem4007418) (@lem940073)). Qed.
Lemma lem4007420 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4007421 : term242 = term209.
Proof. exact (MK_COMB (@lem4007420) (@lem4007419)). Qed.
Lemma lem4007422 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4007423 : term363 = term232.
Proof. exact (MK_COMB (@lem4007422) (@lem4007421)). Qed.
Lemma lem4007424 : term362 = term232.
Proof. exact (TRANS (@lem4007417) (@lem4007423)). Qed.
Lemma lem4007425 : term461 = term232.
Proof. exact (TRANS (@lem4007414) (@lem4007424)). Qed.
Lemma lem4007426 : term232 = term461.
Proof. exact (SYM (@lem4007425)). Qed.
Lemma lem4007427 : term460 = term461.
Proof. exact (TRANS (@lem4007404) (@lem4007426)). Qed.
Lemma lem4007428 : term451 = term233.
Proof. exact (@lem4007352 (@lem4007427)). Qed.
Lemma lem4007429 : term450 = term233.
Proof. exact (TRANS (@lem4007318) (@lem4007428)). Qed.
Lemma lem4007431 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4007432 : term233 = term232.
Proof. exact (@lem4007431 term232). Qed.
Lemma lem4007433 : term450 = term232.
Proof. exact (TRANS (@lem4007429) (@lem4007432)). Qed.
Lemma lem4007434 (_46267 : int) : (term210 _46267) = (term210 _46267).
Proof. exact (eq_refl (term210 _46267)). Qed.
Lemma lem4007435 (_46267 : int) : (term449 _46267) = (term462 _46267).
Proof. exact (MK_COMB (@lem4007434 _46267) (@lem4007433)). Qed.
Lemma lem4007436 (_46267 : int) : (term448 _46267) = (term462 _46267).
Proof. exact (TRANS (@lem4007309 _46267) (@lem4007435 _46267)). Qed.
Lemma lem4007437 (_46266 : int) : (term311 _46266) = (term311 _46266).
Proof. exact (eq_refl (term311 _46266)). Qed.
Lemma lem4007438 (_46266 : int) (_46267 : int) : (term447 _46266 _46267) = (term463 _46266 _46267).
Proof. exact (MK_COMB (@lem4007437 _46266) (@lem4007436 _46267)). Qed.
Lemma lem4007439 (_46266 : int) (_46267 : int) : (term446 _46267 _46266) = (term463 _46266 _46267).
Proof. exact (TRANS (@lem4007308 _46266 _46267) (@lem4007438 _46266 _46267)). Qed.
Lemma lem4007440 (_46266 : int) (_46267 : int) : (term445 _46267 _46266) = (term463 _46266 _46267).
Proof. exact (TRANS (@lem4007307 _46267 _46266) (@lem4007439 _46266 _46267)). Qed.
Lemma lem4007441 (_46266 : int) (_46267 : int) : (term444 _46267 _46266) = (term463 _46266 _46267).
Proof. exact (TRANS (@lem4007261 _46267 _46266) (@lem4007440 _46266 _46267)). Qed.
Lemma lem4007442 (_46266 : int) (_46267 : int) : (term443 _46267 _46266) = (term463 _46266 _46267).
Proof. exact (TRANS (@lem4007260 _46267 _46266) (@lem4007441 _46266 _46267)). Qed.
Lemma lem4007443 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4007444 (_46266 : int) (_46267 : int) : (term464 _46267 _46266) = (term465 _46266 _46267).
Proof. exact (MK_COMB (@lem4007443) (@lem4007442 _46266 _46267)). Qed.
Lemma lem4007445 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem4007446 (_46266 : int) (_46267 : int) : (term441 _46267 _46266) = (term466 _46266 _46267).
Proof. exact (MK_COMB (@lem4007444 _46266 _46267) (@lem4007445)). Qed.
Lemma lem4007447 (_46266 : int) (_46267 : int) : (term436 _46266 _46267) = (term466 _46266 _46267).
Proof. exact (TRANS (@lem4007122 _46267 _46266) (@lem4007446 _46266 _46267)). Qed.
Lemma lem4007448 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4007449 (_46266 : int) (_46267 : int) : (term218 _46267 _46266) = (term319 _46266 _46267).
Proof. exact (MK_COMB (@lem4007448) (@lem4007121 _46266 _46267)). Qed.
Lemma lem4007450 (_46266 : int) (_46267 : int) : (term437 _46266 _46267) = (term467 _46266 _46267).
Proof. exact (MK_COMB (@lem4007449 _46266 _46267) (@lem4007447 _46266 _46267)). Qed.
Lemma lem4007451 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4007452 (_46267 : int) : (term220 _46267) = (term321 _46267).
Proof. exact (MK_COMB (@lem4007451) (@lem4007102 _46267)). Qed.
Lemma lem4007453 (_46266 : int) (_46267 : int) : (term438 _46266 _46267) = (term468 _46266 _46267).
Proof. exact (MK_COMB (@lem4007452 _46267) (@lem4007450 _46266 _46267)). Qed.
Lemma lem4007454 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4007455 (_46266 : int) : (term220 _46266) = (term321 _46266).
Proof. exact (MK_COMB (@lem4007454) (@lem4007054 _46266)). Qed.
Lemma lem4007456 (_46266 : int) (_46267 : int) : (term439 _46266 _46267) = (term469 _46266 _46267).
Proof. exact (MK_COMB (@lem4007455 _46266) (@lem4007453 _46266 _46267)). Qed.
Lemma lem4007483 (_46266 : int) (_46267 : int) : (term440 _46266 _46267) = (term469 _46266 _46267).
Proof. exact (TRANS (@lem4007006 _46266 _46267) (@lem4007456 _46266 _46267)). Qed.
Lemma lem4007487 (_46266 : int) (_46267 : int) (h1 : term469 _46266 _46267) : term469 _46266 _46267.
Proof. exact (h1). Qed.
Lemma lem4007488 (_46266 : int) (_46267 : int) (h1 : term469 _46266 _46267) : term468 _46266 _46267.
Proof. exact (proj2 (@lem4007487 _46266 _46267 h1)). Qed.
Lemma lem4007490 (_46266 : int) (_46267 : int) (h1 : term469 _46266 _46267) : term467 _46266 _46267.
Proof. exact (proj2 (@lem4007488 _46266 _46267 h1)). Qed.
Lemma lem4007492 (_46266 : int) (_46267 : int) (h1 : term469 _46266 _46267) : term466 _46266 _46267.
Proof. exact (proj2 (@lem4007490 _46266 _46267 h1)). Qed.
Lemma lem4007493 (_46266 : int) (_46267 : int) (h1 : term469 _46266 _46267) : term258 _46266 _46267.
Proof. exact (proj1 (@lem4007490 _46266 _46267 h1)). Qed.
Lemma lem4007495 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4007496 : term324 = term269.
Proof. exact (@lem4007495 term192 term209). Qed.
Lemma lem4007498 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4007499 : term209 = term261.
Proof. exact (@lem4007498 term158). Qed.
Lemma lem4007501 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4007502 : term192 = term229.
Proof. exact (@lem4007501 (NUMERAL 0)). Qed.
Lemma lem4007503 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4007504 : term325 = term326.
Proof. exact (MK_COMB (@lem4007503) (@lem4007502)). Qed.
Lemma lem4007505 : term269 = term327.
Proof. exact (MK_COMB (@lem4007504) (@lem4007499)). Qed.
Lemma lem4007506 : term328.
Proof. exact (@lem1980255 term192 term209 term209 term209). Qed.
Lemma lem4007508 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4007509 : term269 = term270.
Proof. exact (@lem4007508 (NUMERAL 0) term158). Qed.
Lemma lem4007510 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4007511 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4007512 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4007511 h1) (fun h1 : term270 = True => @lem4007510)). Qed.
Lemma lem4007513 : term270 = True.
Proof. exact (EQ_MP (@lem4007512) (@lem4007510)). Qed.
Lemma lem4007514 : term269 = True.
Proof. exact (TRANS (@lem4007509) (@lem4007513)). Qed.
Lemma lem4007515 : True = term269.
Proof. exact (SYM (@lem4007514)). Qed.
Lemma lem4007516 : term269.
Proof. exact (EQ_MP (@lem4007515) (@lem0)). Qed.
Lemma lem4007517 : term329.
Proof. exact (@lem4007506 (@lem4007516)). Qed.
Lemma lem4007519 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4007520 : term269 = term270.
Proof. exact (@lem4007519 (NUMERAL 0) term158). Qed.
Lemma lem4007521 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4007522 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4007523 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4007522 h1) (fun h1 : term270 = True => @lem4007521)). Qed.
Lemma lem4007524 : term270 = True.
Proof. exact (EQ_MP (@lem4007523) (@lem4007521)). Qed.
Lemma lem4007525 : term269 = True.
Proof. exact (TRANS (@lem4007520) (@lem4007524)). Qed.
Lemma lem4007526 : True = term269.
Proof. exact (SYM (@lem4007525)). Qed.
Lemma lem4007527 : term269.
Proof. exact (EQ_MP (@lem4007526) (@lem0)). Qed.
Lemma lem4007528 : term327 = term330.
Proof. exact (@lem4007517 (@lem4007527)). Qed.
Lemma lem4007530 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4007531 : term241 = term242.
Proof. exact (@lem4007530 term158 term158). Qed.
Lemma lem4007532 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4007533 : term244 = term158.
Proof. exact (EQ_MP (@lem4007532) (@lem940073)). Qed.
Lemma lem4007534 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4007535 : term242 = term209.
Proof. exact (MK_COMB (@lem4007534) (@lem4007533)). Qed.
Lemma lem4007536 : term241 = term209.
Proof. exact (TRANS (@lem4007531) (@lem4007535)). Qed.
Lemma lem4007538 (x : nat) : (term331 x) = term192.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4007539 : term332 = term192.
Proof. exact (@lem4007538 term158). Qed.
Lemma lem4007540 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4007541 : term333 = term325.
Proof. exact (MK_COMB (@lem4007540) (@lem4007539)). Qed.
Lemma lem4007542 : term330 = term269.
Proof. exact (MK_COMB (@lem4007541) (@lem4007536)). Qed.
Lemma lem4007544 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4007545 : term269 = term270.
Proof. exact (@lem4007544 (NUMERAL 0) term158). Qed.
Lemma lem4007546 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4007547 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4007548 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4007547 h1) (fun h1 : term270 = True => @lem4007546)). Qed.
Lemma lem4007549 : term270 = True.
Proof. exact (EQ_MP (@lem4007548) (@lem4007546)). Qed.
Lemma lem4007550 : term269 = True.
Proof. exact (TRANS (@lem4007545) (@lem4007549)). Qed.
Lemma lem4007551 : term330 = True.
Proof. exact (TRANS (@lem4007542) (@lem4007550)). Qed.
Lemma lem4007552 : term327 = True.
Proof. exact (TRANS (@lem4007528) (@lem4007551)). Qed.
Lemma lem4007553 : term269 = True.
Proof. exact (TRANS (@lem4007505) (@lem4007552)). Qed.
Lemma lem4007554 : term324 = True.
Proof. exact (TRANS (@lem4007496) (@lem4007553)). Qed.
Lemma lem4007555 : True = term324.
Proof. exact (SYM (@lem4007554)). Qed.
Lemma lem4007556 : term324.
Proof. exact (EQ_MP (@lem4007555) (@lem0)). Qed.
Lemma lem4007557 (_46266 : int) (_46267 : int) (h1 : term469 _46266 _46267) : term334 _46266 _46267.
Proof. exact (conj (@lem4007556) (@lem4007493 _46266 _46267 h1)). Qed.
Lemma lem4007559 (x : real) (y : real) : term335 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4007560 (_46266 : int) (_46267 : int) : term336 _46266 _46267.
Proof. exact (@lem4007559 term209 (term255 _46266 _46267)). Qed.
Lemma lem4007561 (_46266 : int) (_46267 : int) (h1 : term469 _46266 _46267) : term337 _46266 _46267.
Proof. exact (@lem4007560 _46266 _46267 (@lem4007557 _46266 _46267 h1)). Qed.
Lemma lem4007562 (_46266 : int) (_46267 : int) : (term338 _46266 _46267) = (term255 _46266 _46267).
Proof. exact (@lem1982733 (term255 _46266 _46267)). Qed.
Lemma lem4007563 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4007564 (_46266 : int) (_46267 : int) : (term339 _46266 _46267) = (term257 _46266 _46267).
Proof. exact (MK_COMB (@lem4007563) (@lem4007562 _46266 _46267)). Qed.
Lemma lem4007565 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem4007566 (_46266 : int) (_46267 : int) : (term337 _46266 _46267) = (term258 _46266 _46267).
Proof. exact (MK_COMB (@lem4007564 _46266 _46267) (@lem4007565)). Qed.
Lemma lem4007567 (_46266 : int) (_46267 : int) (h1 : term469 _46266 _46267) : term258 _46266 _46267.
Proof. exact (EQ_MP (@lem4007566 _46266 _46267) (@lem4007561 _46266 _46267 h1)). Qed.
Lemma lem4007569 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem4007570 : term324 = term269.
Proof. exact (@lem4007569 term192 term209). Qed.
Lemma lem4007572 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4007573 : term209 = term261.
Proof. exact (@lem4007572 term158). Qed.
Lemma lem4007575 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4007576 : term192 = term229.
Proof. exact (@lem4007575 (NUMERAL 0)). Qed.
Lemma lem4007577 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4007578 : term325 = term326.
Proof. exact (MK_COMB (@lem4007577) (@lem4007576)). Qed.
Lemma lem4007579 : term269 = term327.
Proof. exact (MK_COMB (@lem4007578) (@lem4007573)). Qed.
Lemma lem4007580 : term328.
Proof. exact (@lem1980255 term192 term209 term209 term209). Qed.
Lemma lem4007582 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4007583 : term269 = term270.
Proof. exact (@lem4007582 (NUMERAL 0) term158). Qed.
Lemma lem4007584 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4007585 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4007586 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4007585 h1) (fun h1 : term270 = True => @lem4007584)). Qed.
Lemma lem4007587 : term270 = True.
Proof. exact (EQ_MP (@lem4007586) (@lem4007584)). Qed.
Lemma lem4007588 : term269 = True.
Proof. exact (TRANS (@lem4007583) (@lem4007587)). Qed.
Lemma lem4007589 : True = term269.
Proof. exact (SYM (@lem4007588)). Qed.
Lemma lem4007590 : term269.
Proof. exact (EQ_MP (@lem4007589) (@lem0)). Qed.
Lemma lem4007591 : term329.
Proof. exact (@lem4007580 (@lem4007590)). Qed.
Lemma lem4007593 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4007594 : term269 = term270.
Proof. exact (@lem4007593 (NUMERAL 0) term158). Qed.
Lemma lem4007595 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4007596 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4007597 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4007596 h1) (fun h1 : term270 = True => @lem4007595)). Qed.
Lemma lem4007598 : term270 = True.
Proof. exact (EQ_MP (@lem4007597) (@lem4007595)). Qed.
Lemma lem4007599 : term269 = True.
Proof. exact (TRANS (@lem4007594) (@lem4007598)). Qed.
Lemma lem4007600 : True = term269.
Proof. exact (SYM (@lem4007599)). Qed.
Lemma lem4007601 : term269.
Proof. exact (EQ_MP (@lem4007600) (@lem0)). Qed.
Lemma lem4007602 : term327 = term330.
Proof. exact (@lem4007591 (@lem4007601)). Qed.
Lemma lem4007604 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4007605 : term241 = term242.
Proof. exact (@lem4007604 term158 term158). Qed.
Lemma lem4007606 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4007607 : term244 = term158.
Proof. exact (EQ_MP (@lem4007606) (@lem940073)). Qed.
Lemma lem4007608 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4007609 : term242 = term209.
Proof. exact (MK_COMB (@lem4007608) (@lem4007607)). Qed.
Lemma lem4007610 : term241 = term209.
Proof. exact (TRANS (@lem4007605) (@lem4007609)). Qed.
Lemma lem4007612 (x : nat) : (term331 x) = term192.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4007613 : term332 = term192.
Proof. exact (@lem4007612 term158). Qed.
Lemma lem4007614 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem4007615 : term333 = term325.
Proof. exact (MK_COMB (@lem4007614) (@lem4007613)). Qed.
Lemma lem4007616 : term330 = term269.
Proof. exact (MK_COMB (@lem4007615) (@lem4007610)). Qed.
Lemma lem4007618 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4007619 : term269 = term270.
Proof. exact (@lem4007618 (NUMERAL 0) term158). Qed.
Lemma lem4007620 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4007621 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4007622 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4007621 h1) (fun h1 : term270 = True => @lem4007620)). Qed.
Lemma lem4007623 : term270 = True.
Proof. exact (EQ_MP (@lem4007622) (@lem4007620)). Qed.
Lemma lem4007624 : term269 = True.
Proof. exact (TRANS (@lem4007619) (@lem4007623)). Qed.
Lemma lem4007625 : term330 = True.
Proof. exact (TRANS (@lem4007616) (@lem4007624)). Qed.
Lemma lem4007626 : term327 = True.
Proof. exact (TRANS (@lem4007602) (@lem4007625)). Qed.
Lemma lem4007627 : term269 = True.
Proof. exact (TRANS (@lem4007579) (@lem4007626)). Qed.
Lemma lem4007628 : term324 = True.
Proof. exact (TRANS (@lem4007570) (@lem4007627)). Qed.
Lemma lem4007629 : True = term324.
Proof. exact (SYM (@lem4007628)). Qed.
Lemma lem4007630 : term324.
Proof. exact (EQ_MP (@lem4007629) (@lem0)). Qed.
Lemma lem4007631 (_46266 : int) (_46267 : int) (h1 : term469 _46266 _46267) : term470 _46266 _46267.
Proof. exact (conj (@lem4007630) (@lem4007492 _46266 _46267 h1)). Qed.
Lemma lem4007633 (x : real) (y : real) : term335 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem4007634 (_46266 : int) (_46267 : int) : term471 _46266 _46267.
Proof. exact (@lem4007633 term209 (term463 _46266 _46267)). Qed.
Lemma lem4007635 (_46266 : int) (_46267 : int) (h1 : term469 _46266 _46267) : term472 _46266 _46267.
Proof. exact (@lem4007634 _46266 _46267 (@lem4007631 _46266 _46267 h1)). Qed.
Lemma lem4007636 (_46266 : int) (_46267 : int) : (term473 _46266 _46267) = (term463 _46266 _46267).
Proof. exact (@lem1982733 (term463 _46266 _46267)). Qed.
Lemma lem4007637 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4007638 (_46266 : int) (_46267 : int) : (term474 _46266 _46267) = (term465 _46266 _46267).
Proof. exact (MK_COMB (@lem4007637) (@lem4007636 _46266 _46267)). Qed.
Lemma lem4007639 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem4007640 (_46266 : int) (_46267 : int) : (term472 _46266 _46267) = (term466 _46266 _46267).
Proof. exact (MK_COMB (@lem4007638 _46266 _46267) (@lem4007639)). Qed.
Lemma lem4007641 (_46266 : int) (_46267 : int) (h1 : term469 _46266 _46267) : term466 _46266 _46267.
Proof. exact (EQ_MP (@lem4007640 _46266 _46267) (@lem4007635 _46266 _46267 h1)). Qed.
Lemma lem4007642 (_46266 : int) (_46267 : int) (h1 : term469 _46266 _46267) : term475 _46266 _46267.
Proof. exact (conj (@lem4007641 _46266 _46267 h1) (@lem4007567 _46266 _46267 h1)). Qed.
Lemma lem4007644 (x : real) (y : real) : term346 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem4007645 (_46266 : int) (_46267 : int) : term476 _46266 _46267.
Proof. exact (@lem4007644 (term463 _46266 _46267) (term255 _46266 _46267)). Qed.
Lemma lem4007646 (_46266 : int) (_46267 : int) (h1 : term469 _46266 _46267) : term477 _46266 _46267.
Proof. exact (@lem4007645 _46266 _46267 (@lem4007642 _46266 _46267 h1)). Qed.
Lemma lem4007647 (_46266 : int) (_46267 : int) : (term478 _46266 _46267) = (term479 _46266 _46267).
Proof. exact (@lem1982753 (term315 _46266) (real_of_int _46266) (term462 _46267) (term315 _46267)). Qed.
Lemma lem4007648 (_46266 : int) : (term352 _46266) = (term353 _46266).
Proof. exact (@lem1982713 term232 (real_of_int _46266)). Qed.
Lemma lem4007650 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4007651 : term209 = term261.
Proof. exact (@lem4007650 term158). Qed.
Lemma lem4007653 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4007654 : term232 = term233.
Proof. exact (@lem4007653 term158). Qed.
Lemma lem4007655 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4007656 : term354 = term355.
Proof. exact (MK_COMB (@lem4007655) (@lem4007654)). Qed.
Lemma lem4007657 : term356 = term357.
Proof. exact (MK_COMB (@lem4007656) (@lem4007651)). Qed.
Lemma lem4007658 : term358.
Proof. exact (@lem1981473 term232 term209 term209 term209 term192 term209). Qed.
Lemma lem4007660 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4007661 : term269 = term270.
Proof. exact (@lem4007660 (NUMERAL 0) term158). Qed.
Lemma lem4007662 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4007663 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4007664 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4007663 h1) (fun h1 : term270 = True => @lem4007662)). Qed.
Lemma lem4007665 : term270 = True.
Proof. exact (EQ_MP (@lem4007664) (@lem4007662)). Qed.
Lemma lem4007666 : term269 = True.
Proof. exact (TRANS (@lem4007661) (@lem4007665)). Qed.
Lemma lem4007667 : True = term269.
Proof. exact (SYM (@lem4007666)). Qed.
Lemma lem4007668 : term269.
Proof. exact (EQ_MP (@lem4007667) (@lem0)). Qed.
Lemma lem4007669 : term359.
Proof. exact (@lem4007658 (@lem4007668)). Qed.
Lemma lem4007671 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4007672 : term269 = term270.
Proof. exact (@lem4007671 (NUMERAL 0) term158). Qed.
Lemma lem4007673 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4007674 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4007675 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4007674 h1) (fun h1 : term270 = True => @lem4007673)). Qed.
Lemma lem4007676 : term270 = True.
Proof. exact (EQ_MP (@lem4007675) (@lem4007673)). Qed.
Lemma lem4007677 : term269 = True.
Proof. exact (TRANS (@lem4007672) (@lem4007676)). Qed.
Lemma lem4007678 : True = term269.
Proof. exact (SYM (@lem4007677)). Qed.
Lemma lem4007679 : term269.
Proof. exact (EQ_MP (@lem4007678) (@lem0)). Qed.
Lemma lem4007680 : term360.
Proof. exact (@lem4007669 (@lem4007679)). Qed.
Lemma lem4007682 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4007683 : term269 = term270.
Proof. exact (@lem4007682 (NUMERAL 0) term158). Qed.
Lemma lem4007684 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4007685 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4007686 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4007685 h1) (fun h1 : term270 = True => @lem4007684)). Qed.
Lemma lem4007687 : term270 = True.
Proof. exact (EQ_MP (@lem4007686) (@lem4007684)). Qed.
Lemma lem4007688 : term269 = True.
Proof. exact (TRANS (@lem4007683) (@lem4007687)). Qed.
Lemma lem4007689 : True = term269.
Proof. exact (SYM (@lem4007688)). Qed.
Lemma lem4007690 : term269.
Proof. exact (EQ_MP (@lem4007689) (@lem0)). Qed.
Lemma lem4007691 : term361.
Proof. exact (@lem4007680 (@lem4007690)). Qed.
Lemma lem4007693 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4007694 : term241 = term242.
Proof. exact (@lem4007693 term158 term158). Qed.
Lemma lem4007695 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4007696 : term244 = term158.
Proof. exact (EQ_MP (@lem4007695) (@lem940073)). Qed.
Lemma lem4007697 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4007698 : term242 = term209.
Proof. exact (MK_COMB (@lem4007697) (@lem4007696)). Qed.
Lemma lem4007699 : term241 = term209.
Proof. exact (TRANS (@lem4007694) (@lem4007698)). Qed.
Lemma lem4007701 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4007702 : term362 = term363.
Proof. exact (@lem4007701 term158 term158). Qed.
Lemma lem4007703 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4007704 : term244 = term158.
Proof. exact (EQ_MP (@lem4007703) (@lem940073)). Qed.
Lemma lem4007705 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4007706 : term242 = term209.
Proof. exact (MK_COMB (@lem4007705) (@lem4007704)). Qed.
Lemma lem4007707 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4007708 : term363 = term232.
Proof. exact (MK_COMB (@lem4007707) (@lem4007706)). Qed.
Lemma lem4007709 : term362 = term232.
Proof. exact (TRANS (@lem4007702) (@lem4007708)). Qed.
Lemma lem4007710 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4007711 : term364 = term354.
Proof. exact (MK_COMB (@lem4007710) (@lem4007709)). Qed.
Lemma lem4007712 : term365 = term356.
Proof. exact (MK_COMB (@lem4007711) (@lem4007699)). Qed.
Lemma lem4007714 (m : nat) : (term366 m) = term192.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4007715 : term356 = term192.
Proof. exact (@lem4007714 term158). Qed.
Lemma lem4007716 : term365 = term192.
Proof. exact (TRANS (@lem4007712) (@lem4007715)). Qed.
Lemma lem4007717 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4007718 : term367 = term368.
Proof. exact (MK_COMB (@lem4007717) (@lem4007716)). Qed.
Lemma lem4007719 : term209 = term209.
Proof. exact (eq_refl term209). Qed.
Lemma lem4007720 : term369 = term332.
Proof. exact (MK_COMB (@lem4007718) (@lem4007719)). Qed.
Lemma lem4007722 (x : nat) : (term331 x) = term192.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4007723 : term332 = term192.
Proof. exact (@lem4007722 term158). Qed.
Lemma lem4007724 : term369 = term192.
Proof. exact (TRANS (@lem4007720) (@lem4007723)). Qed.
Lemma lem4007726 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4007727 : term241 = term242.
Proof. exact (@lem4007726 term158 term158). Qed.
Lemma lem4007728 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4007729 : term244 = term158.
Proof. exact (EQ_MP (@lem4007728) (@lem940073)). Qed.
Lemma lem4007730 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4007731 : term242 = term209.
Proof. exact (MK_COMB (@lem4007730) (@lem4007729)). Qed.
Lemma lem4007732 : term241 = term209.
Proof. exact (TRANS (@lem4007727) (@lem4007731)). Qed.
Lemma lem4007733 : term368 = term368.
Proof. exact (eq_refl term368). Qed.
Lemma lem4007734 : term370 = term332.
Proof. exact (MK_COMB (@lem4007733) (@lem4007732)). Qed.
Lemma lem4007736 (x : nat) : (term331 x) = term192.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4007737 : term332 = term192.
Proof. exact (@lem4007736 term158). Qed.
Lemma lem4007738 : term370 = term192.
Proof. exact (TRANS (@lem4007734) (@lem4007737)). Qed.
Lemma lem4007739 : term192 = term370.
Proof. exact (SYM (@lem4007738)). Qed.
Lemma lem4007740 : term369 = term370.
Proof. exact (TRANS (@lem4007724) (@lem4007739)). Qed.
Lemma lem4007741 : term357 = term229.
Proof. exact (@lem4007691 (@lem4007740)). Qed.
Lemma lem4007742 : term356 = term229.
Proof. exact (TRANS (@lem4007657) (@lem4007741)). Qed.
Lemma lem4007744 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4007745 : term229 = term192.
Proof. exact (@lem4007744 term192). Qed.
Lemma lem4007746 : term356 = term192.
Proof. exact (TRANS (@lem4007742) (@lem4007745)). Qed.
Lemma lem4007747 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4007748 : term371 = term368.
Proof. exact (MK_COMB (@lem4007747) (@lem4007746)). Qed.
Lemma lem4007749 (_46266 : int) : (real_of_int _46266) = (real_of_int _46266).
Proof. exact (eq_refl (real_of_int _46266)). Qed.
Lemma lem4007750 (_46266 : int) : (term353 _46266) = (term372 _46266).
Proof. exact (MK_COMB (@lem4007748) (@lem4007749 _46266)). Qed.
Lemma lem4007751 (_46266 : int) : (term352 _46266) = (term372 _46266).
Proof. exact (TRANS (@lem4007648 _46266) (@lem4007750 _46266)). Qed.
Lemma lem4007752 (_46266 : int) : (term372 _46266) = term192.
Proof. exact (@lem1982719 (real_of_int _46266)). Qed.
Lemma lem4007753 (_46266 : int) : (term352 _46266) = term192.
Proof. exact (TRANS (@lem4007751 _46266) (@lem4007752 _46266)). Qed.
Lemma lem4007754 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4007755 (_46266 : int) : (term373 _46266) = term374.
Proof. exact (MK_COMB (@lem4007754) (@lem4007753 _46266)). Qed.
Lemma lem4007756 (_46267 : int) : (term480 _46267) = (term481 _46267).
Proof. exact (@lem1982759 (real_of_int _46267) (term315 _46267) term232). Qed.
Lemma lem4007757 (_46267 : int) : (term377 _46267) = (term353 _46267).
Proof. exact (@lem1982715 term232 (real_of_int _46267)). Qed.
Lemma lem4007759 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4007760 : term209 = term261.
Proof. exact (@lem4007759 term158). Qed.
Lemma lem4007762 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4007763 : term232 = term233.
Proof. exact (@lem4007762 term158). Qed.
Lemma lem4007764 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4007765 : term354 = term355.
Proof. exact (MK_COMB (@lem4007764) (@lem4007763)). Qed.
Lemma lem4007766 : term356 = term357.
Proof. exact (MK_COMB (@lem4007765) (@lem4007760)). Qed.
Lemma lem4007767 : term358.
Proof. exact (@lem1981473 term232 term209 term209 term209 term192 term209). Qed.
Lemma lem4007769 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4007770 : term269 = term270.
Proof. exact (@lem4007769 (NUMERAL 0) term158). Qed.
Lemma lem4007771 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4007772 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4007773 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4007772 h1) (fun h1 : term270 = True => @lem4007771)). Qed.
Lemma lem4007774 : term270 = True.
Proof. exact (EQ_MP (@lem4007773) (@lem4007771)). Qed.
Lemma lem4007775 : term269 = True.
Proof. exact (TRANS (@lem4007770) (@lem4007774)). Qed.
Lemma lem4007776 : True = term269.
Proof. exact (SYM (@lem4007775)). Qed.
Lemma lem4007777 : term269.
Proof. exact (EQ_MP (@lem4007776) (@lem0)). Qed.
Lemma lem4007778 : term359.
Proof. exact (@lem4007767 (@lem4007777)). Qed.
Lemma lem4007780 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4007781 : term269 = term270.
Proof. exact (@lem4007780 (NUMERAL 0) term158). Qed.
Lemma lem4007782 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4007783 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4007784 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4007783 h1) (fun h1 : term270 = True => @lem4007782)). Qed.
Lemma lem4007785 : term270 = True.
Proof. exact (EQ_MP (@lem4007784) (@lem4007782)). Qed.
Lemma lem4007786 : term269 = True.
Proof. exact (TRANS (@lem4007781) (@lem4007785)). Qed.
Lemma lem4007787 : True = term269.
Proof. exact (SYM (@lem4007786)). Qed.
Lemma lem4007788 : term269.
Proof. exact (EQ_MP (@lem4007787) (@lem0)). Qed.
Lemma lem4007789 : term360.
Proof. exact (@lem4007778 (@lem4007788)). Qed.
Lemma lem4007791 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4007792 : term269 = term270.
Proof. exact (@lem4007791 (NUMERAL 0) term158). Qed.
Lemma lem4007793 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4007794 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4007795 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4007794 h1) (fun h1 : term270 = True => @lem4007793)). Qed.
Lemma lem4007796 : term270 = True.
Proof. exact (EQ_MP (@lem4007795) (@lem4007793)). Qed.
Lemma lem4007797 : term269 = True.
Proof. exact (TRANS (@lem4007792) (@lem4007796)). Qed.
Lemma lem4007798 : True = term269.
Proof. exact (SYM (@lem4007797)). Qed.
Lemma lem4007799 : term269.
Proof. exact (EQ_MP (@lem4007798) (@lem0)). Qed.
Lemma lem4007800 : term361.
Proof. exact (@lem4007789 (@lem4007799)). Qed.
Lemma lem4007802 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4007803 : term241 = term242.
Proof. exact (@lem4007802 term158 term158). Qed.
Lemma lem4007804 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4007805 : term244 = term158.
Proof. exact (EQ_MP (@lem4007804) (@lem940073)). Qed.
Lemma lem4007806 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4007807 : term242 = term209.
Proof. exact (MK_COMB (@lem4007806) (@lem4007805)). Qed.
Lemma lem4007808 : term241 = term209.
Proof. exact (TRANS (@lem4007803) (@lem4007807)). Qed.
Lemma lem4007810 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4007811 : term362 = term363.
Proof. exact (@lem4007810 term158 term158). Qed.
Lemma lem4007812 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4007813 : term244 = term158.
Proof. exact (EQ_MP (@lem4007812) (@lem940073)). Qed.
Lemma lem4007814 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4007815 : term242 = term209.
Proof. exact (MK_COMB (@lem4007814) (@lem4007813)). Qed.
Lemma lem4007816 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4007817 : term363 = term232.
Proof. exact (MK_COMB (@lem4007816) (@lem4007815)). Qed.
Lemma lem4007818 : term362 = term232.
Proof. exact (TRANS (@lem4007811) (@lem4007817)). Qed.
Lemma lem4007819 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4007820 : term364 = term354.
Proof. exact (MK_COMB (@lem4007819) (@lem4007818)). Qed.
Lemma lem4007821 : term365 = term356.
Proof. exact (MK_COMB (@lem4007820) (@lem4007808)). Qed.
Lemma lem4007823 (m : nat) : (term366 m) = term192.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem4007824 : term356 = term192.
Proof. exact (@lem4007823 term158). Qed.
Lemma lem4007825 : term365 = term192.
Proof. exact (TRANS (@lem4007821) (@lem4007824)). Qed.
Lemma lem4007826 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4007827 : term367 = term368.
Proof. exact (MK_COMB (@lem4007826) (@lem4007825)). Qed.
Lemma lem4007828 : term209 = term209.
Proof. exact (eq_refl term209). Qed.
Lemma lem4007829 : term369 = term332.
Proof. exact (MK_COMB (@lem4007827) (@lem4007828)). Qed.
Lemma lem4007831 (x : nat) : (term331 x) = term192.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4007832 : term332 = term192.
Proof. exact (@lem4007831 term158). Qed.
Lemma lem4007833 : term369 = term192.
Proof. exact (TRANS (@lem4007829) (@lem4007832)). Qed.
Lemma lem4007835 (m : nat) (n : nat) : (term239 m n) = (term240 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem4007836 : term241 = term242.
Proof. exact (@lem4007835 term158 term158). Qed.
Lemma lem4007837 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4007838 : term244 = term158.
Proof. exact (EQ_MP (@lem4007837) (@lem940073)). Qed.
Lemma lem4007839 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4007840 : term242 = term209.
Proof. exact (MK_COMB (@lem4007839) (@lem4007838)). Qed.
Lemma lem4007841 : term241 = term209.
Proof. exact (TRANS (@lem4007836) (@lem4007840)). Qed.
Lemma lem4007842 : term368 = term368.
Proof. exact (eq_refl term368). Qed.
Lemma lem4007843 : term370 = term332.
Proof. exact (MK_COMB (@lem4007842) (@lem4007841)). Qed.
Lemma lem4007845 (x : nat) : (term331 x) = term192.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4007846 : term332 = term192.
Proof. exact (@lem4007845 term158). Qed.
Lemma lem4007847 : term370 = term192.
Proof. exact (TRANS (@lem4007843) (@lem4007846)). Qed.
Lemma lem4007848 : term192 = term370.
Proof. exact (SYM (@lem4007847)). Qed.
Lemma lem4007849 : term369 = term370.
Proof. exact (TRANS (@lem4007833) (@lem4007848)). Qed.
Lemma lem4007850 : term357 = term229.
Proof. exact (@lem4007800 (@lem4007849)). Qed.
Lemma lem4007851 : term356 = term229.
Proof. exact (TRANS (@lem4007766) (@lem4007850)). Qed.
Lemma lem4007853 (x : real) : (term248 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem4007854 : term229 = term192.
Proof. exact (@lem4007853 term192). Qed.
Lemma lem4007855 : term356 = term192.
Proof. exact (TRANS (@lem4007851) (@lem4007854)). Qed.
Lemma lem4007856 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem4007857 : term371 = term368.
Proof. exact (MK_COMB (@lem4007856) (@lem4007855)). Qed.
Lemma lem4007858 (_46267 : int) : (real_of_int _46267) = (real_of_int _46267).
Proof. exact (eq_refl (real_of_int _46267)). Qed.
Lemma lem4007859 (_46267 : int) : (term353 _46267) = (term372 _46267).
Proof. exact (MK_COMB (@lem4007857) (@lem4007858 _46267)). Qed.
Lemma lem4007860 (_46267 : int) : (term377 _46267) = (term372 _46267).
Proof. exact (TRANS (@lem4007757 _46267) (@lem4007859 _46267)). Qed.
Lemma lem4007861 (_46267 : int) : (term372 _46267) = term192.
Proof. exact (@lem1982719 (real_of_int _46267)). Qed.
Lemma lem4007862 (_46267 : int) : (term377 _46267) = term192.
Proof. exact (TRANS (@lem4007860 _46267) (@lem4007861 _46267)). Qed.
Lemma lem4007863 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem4007864 (_46267 : int) : (term378 _46267) = term374.
Proof. exact (MK_COMB (@lem4007863) (@lem4007862 _46267)). Qed.
Lemma lem4007865 : term232 = term232.
Proof. exact (eq_refl term232). Qed.
Lemma lem4007866 (_46267 : int) : (term481 _46267) = term482.
Proof. exact (MK_COMB (@lem4007864 _46267) (@lem4007865)). Qed.
Lemma lem4007867 (_46267 : int) : (term480 _46267) = term482.
Proof. exact (TRANS (@lem4007756 _46267) (@lem4007866 _46267)). Qed.
Lemma lem4007868 : term482 = term232.
Proof. exact (@lem1982721 term232). Qed.
Lemma lem4007869 (_46267 : int) : (term480 _46267) = term232.
Proof. exact (TRANS (@lem4007867 _46267) (@lem4007868)). Qed.
Lemma lem4007870 (_46266 : int) (_46267 : int) : (term479 _46266 _46267) = term482.
Proof. exact (MK_COMB (@lem4007755 _46266) (@lem4007869 _46267)). Qed.
Lemma lem4007871 (_46266 : int) (_46267 : int) : (term478 _46266 _46267) = term482.
Proof. exact (TRANS (@lem4007647 _46266 _46267) (@lem4007870 _46266 _46267)). Qed.
Lemma lem4007872 : term482 = term232.
Proof. exact (@lem1982721 term232). Qed.
Lemma lem4007873 (_46266 : int) (_46267 : int) : (term478 _46266 _46267) = term232.
Proof. exact (TRANS (@lem4007871 _46266 _46267) (@lem4007872)). Qed.
Lemma lem4007874 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem4007875 (_46266 : int) (_46267 : int) : (term483 _46266 _46267) = term484.
Proof. exact (MK_COMB (@lem4007874) (@lem4007873 _46266 _46267)). Qed.
Lemma lem4007876 : term192 = term192.
Proof. exact (eq_refl term192). Qed.
Lemma lem4007877 (_46266 : int) (_46267 : int) : (term477 _46266 _46267) = term485.
Proof. exact (MK_COMB (@lem4007875 _46266 _46267) (@lem4007876)). Qed.
Lemma lem4007878 (_46266 : int) (_46267 : int) (h1 : term469 _46266 _46267) : term485.
Proof. exact (EQ_MP (@lem4007877 _46266 _46267) (@lem4007646 _46266 _46267 h1)). Qed.
Lemma lem4007880 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem4007881 : term485 = term486.
Proof. exact (@lem4007880 term192 term232). Qed.
Lemma lem4007883 (x : nat) : (term230 x) = (term231 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem4007884 : term232 = term233.
Proof. exact (@lem4007883 term158). Qed.
Lemma lem4007886 (x : nat) : (real_of_num x) = (term228 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem4007887 : term192 = term229.
Proof. exact (@lem4007886 (NUMERAL 0)). Qed.
Lemma lem4007888 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4007889 : term194 = term384.
Proof. exact (MK_COMB (@lem4007888) (@lem4007887)). Qed.
Lemma lem4007890 : term486 = term487.
Proof. exact (MK_COMB (@lem4007889) (@lem4007884)). Qed.
Lemma lem4007891 : term488.
Proof. exact (@lem1980026 term192 term209 term232 term209). Qed.
Lemma lem4007893 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4007894 : term269 = term270.
Proof. exact (@lem4007893 (NUMERAL 0) term158). Qed.
Lemma lem4007895 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4007896 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4007897 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4007896 h1) (fun h1 : term270 = True => @lem4007895)). Qed.
Lemma lem4007898 : term270 = True.
Proof. exact (EQ_MP (@lem4007897) (@lem4007895)). Qed.
Lemma lem4007899 : term269 = True.
Proof. exact (TRANS (@lem4007894) (@lem4007898)). Qed.
Lemma lem4007900 : True = term269.
Proof. exact (SYM (@lem4007899)). Qed.
Lemma lem4007901 : term269.
Proof. exact (EQ_MP (@lem4007900) (@lem0)). Qed.
Lemma lem4007902 : term489.
Proof. exact (@lem4007891 (@lem4007901)). Qed.
Lemma lem4007904 (m : nat) (n : nat) : (term268 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem4007905 : term269 = term270.
Proof. exact (@lem4007904 (NUMERAL 0) term158). Qed.
Lemma lem4007906 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4007907 (h1 : term271 = (BIT1 0)) : term270 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem4007908 : (term271 = (BIT1 0)) = (term270 = True).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4007907 h1) (fun h1 : term270 = True => @lem4007906)). Qed.
Lemma lem4007909 : term270 = True.
Proof. exact (EQ_MP (@lem4007908) (@lem4007906)). Qed.
Lemma lem4007910 : term269 = True.
Proof. exact (TRANS (@lem4007905) (@lem4007909)). Qed.
Lemma lem4007911 : True = term269.
Proof. exact (SYM (@lem4007910)). Qed.
Lemma lem4007912 : term269.
Proof. exact (EQ_MP (@lem4007911) (@lem0)). Qed.
Lemma lem4007913 : term487 = term490.
Proof. exact (@lem4007902 (@lem4007912)). Qed.
Lemma lem4007915 (m : nat) (n : nat) : (term301 m n) = (term302 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem4007916 : term362 = term363.
Proof. exact (@lem4007915 term158 term158). Qed.
Lemma lem4007917 : (term243 = (BIT1 0)) = (term244 = term158).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem4007918 : term244 = term158.
Proof. exact (EQ_MP (@lem4007917) (@lem940073)). Qed.
Lemma lem4007919 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem4007920 : term242 = term209.
Proof. exact (MK_COMB (@lem4007919) (@lem4007918)). Qed.
Lemma lem4007921 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem4007922 : term363 = term232.
Proof. exact (MK_COMB (@lem4007921) (@lem4007920)). Qed.
Lemma lem4007923 : term362 = term232.
Proof. exact (TRANS (@lem4007916) (@lem4007922)). Qed.
Lemma lem4007925 (x : nat) : (term331 x) = term192.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem4007926 : term332 = term192.
Proof. exact (@lem4007925 term158). Qed.
Lemma lem4007927 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem4007928 : term391 = term194.
Proof. exact (MK_COMB (@lem4007927) (@lem4007926)). Qed.
Lemma lem4007929 : term490 = term486.
Proof. exact (MK_COMB (@lem4007928) (@lem4007923)). Qed.
Lemma lem4007931 (m : nat) (n : nat) : (term392 m n) = (term393 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem4007932 : term486 = term491.
Proof. exact (@lem4007931 (NUMERAL 0) term158). Qed.
Lemma lem4007933 : term271 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem4007934 (h1 : term271 = (BIT1 0)) : (term158 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem4007935 : (term271 = (BIT1 0)) = ((term158 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term271 = (BIT1 0) => @lem4007934 h1) (fun h1 : (term158 = (NUMERAL 0)) = False => @lem4007933)). Qed.
Lemma lem4007936 : (term158 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem4007935) (@lem4007933)). Qed.
Lemma lem4007937 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem4007938 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4007939 : term396 = (and True).
Proof. exact (MK_COMB (@lem4007938) (@lem4007937)). Qed.
Lemma lem4007940 : term491 = (True /\ False).
Proof. exact (MK_COMB (@lem4007939) (@lem4007936)). Qed.
Lemma lem4007942 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem4007943 : term491 = False.
Proof. exact (TRANS (@lem4007940) (@lem4007942)). Qed.
Lemma lem4007944 : term486 = False.
Proof. exact (TRANS (@lem4007932) (@lem4007943)). Qed.
Lemma lem4007945 : term490 = False.
Proof. exact (TRANS (@lem4007929) (@lem4007944)). Qed.
Lemma lem4007946 : term487 = False.
Proof. exact (TRANS (@lem4007913) (@lem4007945)). Qed.
Lemma lem4007947 : term486 = False.
Proof. exact (TRANS (@lem4007890) (@lem4007946)). Qed.
Lemma lem4007948 : term485 = False.
Proof. exact (TRANS (@lem4007881) (@lem4007947)). Qed.
Lemma lem4007949 (_46266 : int) (_46267 : int) (h1 : term469 _46266 _46267) : False.
Proof. exact (EQ_MP (@lem4007948) (@lem4007878 _46266 _46267 h1)). Qed.
Lemma lem4007951 (_46266 : int) (_46267 : int) (h1 : term469 _46266 _46267) : term469 _46266 _46267.
Proof. exact (h1). Qed.
Lemma lem4007952 (_46266 : int) (_46267 : int) (h1 : term469 _46266 _46267) : (term469 _46266 _46267) = False.
Proof. exact (prop_ext (fun h2 : term469 _46266 _46267 => @lem4007949 _46266 _46267 h1) (fun h2 : False => @lem4007951 _46266 _46267 h1)). Qed.
Lemma lem4007953 (_46266 : int) (_46267 : int) (h1 : term469 _46266 _46267) : False.
Proof. exact (EQ_MP (@lem4007952 _46266 _46267 h1) (@lem4007951 _46266 _46267 h1)). Qed.
Lemma lem4007954 (_46266 : int) (_46267 : int) (h1 : term440 _46266 _46267) : term440 _46266 _46267.
Proof. exact (h1). Qed.
Lemma lem4007955 (_46266 : int) (_46267 : int) (h1 : term440 _46266 _46267) : term469 _46266 _46267.
Proof. exact (EQ_MP (@lem4007483 _46266 _46267) (@lem4007954 _46266 _46267 h1)). Qed.
Lemma lem4007956 (_46266 : int) (_46267 : int) (h1 : term440 _46266 _46267) : (term469 _46266 _46267) = False.
Proof. exact (prop_ext (fun h2 : term469 _46266 _46267 => @lem4007953 _46266 _46267 h2) (fun h2 : False => @lem4007955 _46266 _46267 h1)). Qed.
Lemma lem4007957 (_46266 : int) (_46267 : int) (h1 : term440 _46266 _46267) : False.
Proof. exact (EQ_MP (@lem4007956 _46266 _46267 h1) (@lem4007955 _46266 _46267 h1)). Qed.
Lemma lem4007958 (_46266 : int) (_46267 : int) : term492 _46266 _46267.
Proof. exact (fun h0 : term440 _46266 _46267 => @lem4007957 _46266 _46267 h0). Qed.
Lemma lem4007959 (_46266 : int) (_46267 : int) : term493 _46266 _46267.
Proof. exact (@lem1386578 (term494 _46266 _46267)). Qed.
Lemma lem4007962 (_46266 : int) (_46267 : int) : term494 _46266 _46267.
Proof. exact (@lem4007959 _46266 _46267 (@lem4007958 _46266 _46267)). Qed.
Lemma lem4007963 (_46267 : int) (_46266 : int) : (term439 _46266 _46267) = (term432 _46267 _46266).
Proof. exact (SYM (@lem4006966 _46266 _46267)). Qed.
Lemma lem4007964 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4007965 (_46267 : int) (_46266 : int) : (term494 _46266 _46267) = (term419 _46267 _46266).
Proof. exact (MK_COMB (@lem4007964) (@lem4007963 _46267 _46266)). Qed.
Lemma lem4007966 (_46267 : int) (_46266 : int) : term419 _46267 _46266.
Proof. exact (EQ_MP (@lem4007965 _46267 _46266) (@lem4007962 _46266 _46267)). Qed.
Lemma lem4007967 (_46267 : int) (_46266 : int) : term420 _46267 _46266.
Proof. exact (EQ_MP (@lem4006837 _46267 _46266) (@lem4007966 _46267 _46266)). Qed.
Lemma lem4007968 {A B : Type'} (f : A -> B) (s : A -> Prop) : term495 A B f s.
Proof. exact (@lem4007967 (term401 A B f s) (term402 A s)). Qed.
Lemma lem4007969 {A B : Type'} (f : A -> B) (s : A -> Prop) : term496 A B f s.
Proof. exact (@lem4007968 A B f s (@lem4006833 A s)). Qed.
Lemma lem4007970 {A B : Type'} (f : A -> B) (s : A -> Prop) : term418 A B f s.
Proof. exact (@lem4007969 A B f s (@lem4006836 A B f s)). Qed.
Lemma lem4007971 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term418 A B f s) = (term404 A B f s).
Proof. exact (SYM (@lem4006830 A B f s)). Qed.
Lemma lem4007972 {A B : Type'} (f : A -> B) (s : A -> Prop) : term404 A B f s.
Proof. exact (EQ_MP (@lem4007971 A B f s) (@lem4007970 A B f s)). Qed.
Lemma lem4007973 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term404 A B f s) = ((term404 A B f s) = True).
Proof. exact (@lem7 (term404 A B f s)). Qed.
Lemma lem4007974 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term404 A B f s) = True.
Proof. exact (EQ_MP (@lem4007973 A B f s) (@lem4007972 A B f s)). Qed.
Lemma lem4007975 {A B : Type'} (f : A -> B) (s : A -> Prop) : True = (term404 A B f s).
Proof. exact (SYM (@lem4007974 A B f s)). Qed.
Lemma lem4007976 {A B : Type'} (f : A -> B) (s : A -> Prop) : term404 A B f s.
Proof. exact (EQ_MP (@lem4007975 A B f s) (@lem0)). Qed.
Lemma lem4007977 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : term406 A B f s.
Proof. exact (@lem4007976 A B f s (@lem4005660 A B f x s h1)). Qed.
Lemma lem4007979 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : term32 A B f x s) : term141 A B f s.
Proof. exact (@lem4006741 A B f s (@lem4005658 A B f x s h1)). Qed.
Lemma lem4007981 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term125 A B x f s.
Proof. exact (fun h0 : term32 A B f x s => @lem4007977 A B f x s h0). Qed.
Lemma lem4007982 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term128 A B x f s.
Proof. exact (fun h0 : term497 A B x f s => @lem4007981 A B x f s). Qed.
Lemma lem4007983 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term130 A B x f s.
Proof. exact (fun h0 : term32 A B f x s => @lem4007979 A B f x s h0). Qed.
Lemma lem4007984 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term133 A B x f s.
Proof. exact (fun h0 : term122 A B x f s => @lem4007983 A B x f s). Qed.
Lemma lem4007985 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term136 A B x f s.
Proof. exact (conj (@lem4007984 A B x f s) (@lem4007982 A B x f s)). Qed.
Lemma lem4007986 {A B : Type'} (x : A) (f : A -> B) (s : A -> Prop) : term108 A B x f s.
Proof. exact (EQ_MP (@lem4005622 A B x f s) (@lem4007985 A B x f s)). Qed.
Lemma lem4007991 {A B : Type'} (x : A) (f : A -> B) : term110 A B x f.
Proof. exact (fun s : A -> Prop => @lem4007986 A B x f s). Qed.
Lemma lem4007996 {A B : Type'} (f : A -> B) : term112 A B f.
Proof. exact (fun x : A => @lem4007991 A B x f). Qed.
Lemma lem4007997 {A B : Type'} (f : A -> B) : term48 A B f.
Proof. exact (EQ_MP (@lem4005604 A B f) (@lem4007996 A B f)). Qed.
Lemma lem4007998 {A B : Type'} (f : A -> B) : term57 A B f.
Proof. exact (@lem4004645 A B f (@lem4007997 A B f)). Qed.
Lemma lem4008003 {A B : Type'} : term498 A B.
Proof. exact (fun f : A -> B => @lem4007998 A B f). Qed.
