Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_FINITE_SUBSET_IMAGE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EXISTS_FINITE_SUBSET_IMAGE_INJ_spec.
Require Import FINITE_IMAGE_spec.
Require Import IMAGE_SUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18394_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm32_spec.
Require Import thm69_spec.
Lemma lem3689570 {_93670 _93677 : Type'} (P : type686 _93677) : term0 _93670 _93677 P.
Proof. exact (@lem3688903 _93670 _93677 P). Qed.
Lemma lem3689571 {_93670 _93677 : Type'} (P : type686 _93677) : (term0 _93670 _93677 P) = (term1 _93670 _93677 P).
Proof. exact (eq_refl (term0 _93670 _93677 P)). Qed.
Lemma lem3689572 {_93670 _93677 : Type'} (P : type686 _93677) : term1 _93670 _93677 P.
Proof. exact (EQ_MP (@lem3689571 _93670 _93677 P) (@lem3689570 _93670 _93677 P)). Qed.
Lemma lem3689573 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) : term2 _93670 _93677 P f.
Proof. exact (@lem3689572 _93670 _93677 P f). Qed.
Lemma lem3689574 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) : (term2 _93670 _93677 P f) = (term3 _93670 _93677 P f).
Proof. exact (eq_refl (term2 _93670 _93677 P f)). Qed.
Lemma lem3689575 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) : term3 _93670 _93677 P f.
Proof. exact (EQ_MP (@lem3689574 _93670 _93677 P f) (@lem3689573 _93670 _93677 P f)). Qed.
Lemma lem3689576 {_93670 _93677 : Type'} (P : type686 _93677) (f : _93670 -> _93677) (s : _93670 -> Prop) : term4 _93670 _93677 P f s.
Proof. exact (@lem3689575 _93670 _93677 P f s). Qed.
Lemma lem3689577 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) : (term4 _93670 _93677 P f s) = ((term5 _93670 _93677 f s P) = (term6 _93670 _93677 s P f)).
Proof. exact (eq_refl (term4 _93670 _93677 P f s)). Qed.
Lemma lem3689582 {_93670 _93677 : Type'} (s : _93670 -> Prop) (P : type686 _93677) (f : _93670 -> _93677) : (term5 _93670 _93677 f s P) = (term6 _93670 _93677 s P f).
Proof. exact (EQ_MP (@lem3689577 _93670 _93677 s P f) (@lem3689576 _93670 _93677 P f s)). Qed.
Lemma lem3689583 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term5 _93804 _93824 f s P) = (term6 _93804 _93824 s P f).
Proof. exact (@lem3689582 _93804 _93824 s P f). Qed.
Lemma lem3689612 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3689613 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term7 _93804 _93824 f s P) = (term8 _93804 _93824 s P f).
Proof. exact (MK_COMB (@lem3689612) (@lem3689583 _93804 _93824 s P f)). Qed.
Lemma lem3689622 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term9 _93804 _93824 s P f) = (term9 _93804 _93824 s P f).
Proof. exact (eq_refl (term9 _93804 _93824 s P f)). Qed.
Lemma lem3689623 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term10 _93804 _93824 s P f) = (term11 _93804 _93824 s P f).
Proof. exact (MK_COMB (@lem3689613 _93804 _93824 s P f) (@lem3689622 _93804 _93824 s P f)). Qed.
Lemma lem3689626 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term11 _93804 _93824 s P f) = (term10 _93804 _93824 s P f).
Proof. exact (SYM (@lem3689623 _93804 _93824 s P f)). Qed.
Lemma lem3689628 (p : Prop) : p = (term12 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3689629 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term11 _93804 _93824 s P f) = (term13 _93804 _93824 s P f).
Proof. exact (@lem3689628 (term11 _93804 _93824 s P f)). Qed.
Lemma lem3689630 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term13 _93804 _93824 s P f) = (term11 _93804 _93824 s P f).
Proof. exact (SYM (@lem3689629 _93804 _93824 s P f)). Qed.
Lemma lem3689631 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term14 _93804 _93824 s P f) : term14 _93804 _93824 s P f.
Proof. exact (h1). Qed.
Lemma lem3689634 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term13 _93804 _93824 s P f) : term13 _93804 _93824 s P f.
Proof. exact (h1). Qed.
Lemma lem3689635 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : term15 _93804 _93824 s P f.
Proof. exact (fun h0 : term13 _93804 _93824 s P f => @lem3689634 _93804 _93824 s P f h0). Qed.
Lemma lem3689636 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term15 _93804 _93824 s P f) : term15 _93804 _93824 s P f.
Proof. exact (h1). Qed.
Lemma lem3689637 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term13 _93804 _93824 s P f) : term13 _93804 _93824 s P f.
Proof. exact (h1). Qed.
Lemma lem3689638 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term13 _93804 _93824 s P f) (h2 : term15 _93804 _93824 s P f) : term13 _93804 _93824 s P f.
Proof. exact (@lem3689636 _93804 _93824 s P f h2 (@lem3689637 _93804 _93824 s P f h1)). Qed.
Lemma lem3689639 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term13 _93804 _93824 s P f) : term16 _93804 _93824 s P f.
Proof. exact (fun h0 : term15 _93804 _93824 s P f => @lem3689638 _93804 _93824 s P f h1 h0). Qed.
Lemma lem3689640 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term15 _93804 _93824 s P f) : term15 _93804 _93824 s P f.
Proof. exact (h1). Qed.
Lemma lem3689641 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term13 _93804 _93824 s P f) (h2 : term15 _93804 _93824 s P f) : term13 _93804 _93824 s P f.
Proof. exact (@lem3689639 _93804 _93824 s P f h1 (@lem3689640 _93804 _93824 s P f h2)). Qed.
Lemma lem3689642 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term15 _93804 _93824 s P f) : term15 _93804 _93824 s P f.
Proof. exact (fun h0 : term13 _93804 _93824 s P f => @lem3689641 _93804 _93824 s P f h0 h1). Qed.
Lemma lem3689643 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : term17 _93804 _93824 s P f.
Proof. exact (fun h0 : term15 _93804 _93824 s P f => @lem3689642 _93804 _93824 s P f h0). Qed.
Lemma lem3689646 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : term15 _93804 _93824 s P f.
Proof. exact (@lem3689643 _93804 _93824 s P f (@lem3689635 _93804 _93824 s P f)). Qed.
Lemma lem3689647 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : term15 _93804 _93824 s P f.
Proof. exact (@lem3689646 _93804 _93824 s P f). Qed.
Lemma lem3689661 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3689662 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term13 _93804 _93824 s P f) = (term18 _93804 _93824 s P f).
Proof. exact (@lem3689661 (term14 _93804 _93824 s P f)). Qed.
Lemma lem3689664 (t : Prop) : (term19 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3689665 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term18 _93804 _93824 s P f) = (term11 _93804 _93824 s P f).
Proof. exact (@lem3689664 (term11 _93804 _93824 s P f)). Qed.
Lemma lem3689668 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term13 _93804 _93824 s P f) = (term11 _93804 _93824 s P f).
Proof. exact (TRANS (@lem3689662 _93804 _93824 s P f) (@lem3689665 _93804 _93824 s P f)). Qed.
Lemma lem3689747 {_93804 _93824 : Type'} (P : type686 _93824) (f : _93804 -> _93824) : (term20 _93804 _93824 P f) = (term21 _93804 _93824 P f).
Proof. exact (fun_ext (fun s : _93804 -> Prop => @lem3689668 _93804 _93824 s P f)). Qed.
Lemma lem3689748 {_93804 : Type'} : (@all (_93804 -> Prop)) = (@all (_93804 -> Prop)).
Proof. exact (eq_refl (@all (_93804 -> Prop))). Qed.
Lemma lem3689749 {_93804 _93824 : Type'} (P : type686 _93824) (f : _93804 -> _93824) : (term22 _93804 _93824 P f) = (term23 _93804 _93824 P f).
Proof. exact (MK_COMB (@lem3689748 _93804) (@lem3689747 _93804 _93824 P f)). Qed.
Lemma lem3689754 {_93804 _93824 : Type'} (f : _93804 -> _93824) : (term24 _93804 _93824 f) = (term25 _93804 _93824 f).
Proof. exact (fun_ext (fun P : type686 _93824 => @lem3689749 _93804 _93824 P f)). Qed.
Lemma lem3689755 {_93824 : Type'} : (@all ((_93824 -> Prop) -> Prop)) = (@all ((_93824 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_93824 -> Prop) -> Prop))). Qed.
Lemma lem3689756 {_93804 _93824 : Type'} (f : _93804 -> _93824) : (term26 _93804 _93824 f) = (term27 _93804 _93824 f).
Proof. exact (MK_COMB (@lem3689755 _93824) (@lem3689754 _93804 _93824 f)). Qed.
Lemma lem3689761 {_93804 _93824 : Type'} : (term28 _93804 _93824) = (term29 _93804 _93824).
Proof. exact (fun_ext (fun f : _93804 -> _93824 => @lem3689756 _93804 _93824 f)). Qed.
Lemma lem3689762 {_93804 _93824 : Type'} : (@all (_93804 -> _93824)) = (@all (_93804 -> _93824)).
Proof. exact (eq_refl (@all (_93804 -> _93824))). Qed.
Lemma lem3689771 {_93804 _93824 : Type'} : (term30 _93804 _93824) = (term31 _93804 _93824).
Proof. exact (MK_COMB (@lem3689762 _93804 _93824) (@lem3689761 _93804 _93824)). Qed.
Lemma lem3689780 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term32 _93804 _93824 s P f t) = (term32 _93804 _93824 s P f t).
Proof. exact (eq_refl (term32 _93804 _93824 s P f t)). Qed.
Lemma lem3689781 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term33 _93804 _93824 s P f) = (term33 _93804 _93824 s P f).
Proof. exact (fun_ext (fun t : _93804 -> Prop => @lem3689780 _93804 _93824 s P f t)). Qed.
Lemma lem3689782 {_93804 : Type'} : (@ex (_93804 -> Prop)) = (@ex (_93804 -> Prop)).
Proof. exact (eq_refl (@ex (_93804 -> Prop))). Qed.
Lemma lem3689783 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term9 _93804 _93824 s P f) = (term9 _93804 _93824 s P f).
Proof. exact (MK_COMB (@lem3689782 _93804) (@lem3689781 _93804 _93824 s P f)). Qed.
Lemma lem3689784 {_93804 _93824 : Type'} (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term34 _93804 _93824 P f t) = (term34 _93804 _93824 P f t).
Proof. exact (eq_refl (term34 _93804 _93824 P f t)). Qed.
Lemma lem3689797 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (x : _93804) (y : _93804) : (term35 _93804 _93824 t f x y) = (term35 _93804 _93824 t f x y).
Proof. exact (eq_refl (term35 _93804 _93824 t f x y)). Qed.
Lemma lem3689798 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (x : _93804) : (term36 _93804 _93824 t f x) = (term36 _93804 _93824 t f x).
Proof. exact (fun_ext (fun y : _93804 => @lem3689797 _93804 _93824 t f x y)). Qed.
Lemma lem3689799 {_93804 : Type'} : (@all _93804) = (@all _93804).
Proof. exact (eq_refl (@all _93804)). Qed.
Lemma lem3689800 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (x : _93804) : (term37 _93804 _93824 t f x) = (term37 _93804 _93824 t f x).
Proof. exact (MK_COMB (@lem3689799 _93804) (@lem3689798 _93804 _93824 t f x)). Qed.
Lemma lem3689801 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) : (term38 _93804 _93824 t f) = (term38 _93804 _93824 t f).
Proof. exact (fun_ext (fun x : _93804 => @lem3689800 _93804 _93824 t f x)). Qed.
Lemma lem3689802 {_93804 : Type'} : (@all _93804) = (@all _93804).
Proof. exact (eq_refl (@all _93804)). Qed.
Lemma lem3689803 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) : (term39 _93804 _93824 t f) = (term39 _93804 _93824 t f).
Proof. exact (MK_COMB (@lem3689802 _93804) (@lem3689801 _93804 _93824 t f)). Qed.
Lemma lem3689804 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3689805 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) : (term40 _93804 _93824 t f) = (term40 _93804 _93824 t f).
Proof. exact (MK_COMB (@lem3689804) (@lem3689803 _93804 _93824 t f)). Qed.
Lemma lem3689806 {_93804 _93824 : Type'} (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term41 _93804 _93824 P f t) = (term41 _93804 _93824 P f t).
Proof. exact (MK_COMB (@lem3689805 _93804 _93824 t f) (@lem3689784 _93804 _93824 P f t)). Qed.
Lemma lem3689809 {_93804 : Type'} (t : _93804 -> Prop) (s : _93804 -> Prop) : (term42 _93804 t s) = (term42 _93804 t s).
Proof. exact (eq_refl (term42 _93804 t s)). Qed.
Lemma lem3689810 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term43 _93804 _93824 s P f t) = (term43 _93804 _93824 s P f t).
Proof. exact (MK_COMB (@lem3689809 _93804 t s) (@lem3689806 _93804 _93824 P f t)). Qed.
Lemma lem3689813 {_93804 : Type'} (t : _93804 -> Prop) : (term44 _93804 t) = (term44 _93804 t).
Proof. exact (eq_refl (term44 _93804 t)). Qed.
Lemma lem3689814 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term45 _93804 _93824 s P f t) = (term45 _93804 _93824 s P f t).
Proof. exact (MK_COMB (@lem3689813 _93804 t) (@lem3689810 _93804 _93824 s P f t)). Qed.
Lemma lem3689815 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term46 _93804 _93824 s P f) = (term46 _93804 _93824 s P f).
Proof. exact (fun_ext (fun t : _93804 -> Prop => @lem3689814 _93804 _93824 s P f t)). Qed.
Lemma lem3689816 {_93804 : Type'} : (@ex (_93804 -> Prop)) = (@ex (_93804 -> Prop)).
Proof. exact (eq_refl (@ex (_93804 -> Prop))). Qed.
Lemma lem3689817 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term6 _93804 _93824 s P f) = (term6 _93804 _93824 s P f).
Proof. exact (MK_COMB (@lem3689816 _93804) (@lem3689815 _93804 _93824 s P f)). Qed.
Lemma lem3689818 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3689819 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term8 _93804 _93824 s P f) = (term8 _93804 _93824 s P f).
Proof. exact (MK_COMB (@lem3689818) (@lem3689817 _93804 _93824 s P f)). Qed.
Lemma lem3689820 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term11 _93804 _93824 s P f) = (term11 _93804 _93824 s P f).
Proof. exact (MK_COMB (@lem3689819 _93804 _93824 s P f) (@lem3689783 _93804 _93824 s P f)). Qed.
Lemma lem3689821 {_93804 _93824 : Type'} (P : type686 _93824) (f : _93804 -> _93824) : (term21 _93804 _93824 P f) = (term21 _93804 _93824 P f).
Proof. exact (fun_ext (fun s : _93804 -> Prop => @lem3689820 _93804 _93824 s P f)). Qed.
Lemma lem3689822 {_93804 : Type'} : (@all (_93804 -> Prop)) = (@all (_93804 -> Prop)).
Proof. exact (eq_refl (@all (_93804 -> Prop))). Qed.
Lemma lem3689823 {_93804 _93824 : Type'} (P : type686 _93824) (f : _93804 -> _93824) : (term23 _93804 _93824 P f) = (term23 _93804 _93824 P f).
Proof. exact (MK_COMB (@lem3689822 _93804) (@lem3689821 _93804 _93824 P f)). Qed.
Lemma lem3689824 {_93804 _93824 : Type'} (f : _93804 -> _93824) : (term25 _93804 _93824 f) = (term25 _93804 _93824 f).
Proof. exact (fun_ext (fun P : type686 _93824 => @lem3689823 _93804 _93824 P f)). Qed.
Lemma lem3689825 {_93824 : Type'} : (@all ((_93824 -> Prop) -> Prop)) = (@all ((_93824 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_93824 -> Prop) -> Prop))). Qed.
Lemma lem3689826 {_93804 _93824 : Type'} (f : _93804 -> _93824) : (term27 _93804 _93824 f) = (term27 _93804 _93824 f).
Proof. exact (MK_COMB (@lem3689825 _93824) (@lem3689824 _93804 _93824 f)). Qed.
Lemma lem3689827 {_93804 _93824 : Type'} : (term29 _93804 _93824) = (term29 _93804 _93824).
Proof. exact (fun_ext (fun f : _93804 -> _93824 => @lem3689826 _93804 _93824 f)). Qed.
Lemma lem3689828 {_93804 _93824 : Type'} : (@all (_93804 -> _93824)) = (@all (_93804 -> _93824)).
Proof. exact (eq_refl (@all (_93804 -> _93824))). Qed.
Lemma lem3689829 {_93804 _93824 : Type'} : (term31 _93804 _93824) = (term31 _93804 _93824).
Proof. exact (MK_COMB (@lem3689828 _93804 _93824) (@lem3689827 _93804 _93824)). Qed.
Lemma lem3689890 {_93804 _93824 : Type'} : (term30 _93804 _93824) = (term31 _93804 _93824).
Proof. exact (TRANS (@lem3689771 _93804 _93824) (@lem3689829 _93804 _93824)). Qed.
Lemma lem3689891 {_93804 _93824 : Type'} : (term31 _93804 _93824) = (term30 _93804 _93824).
Proof. exact (SYM (@lem3689890 _93804 _93824)). Qed.
Lemma lem3689892 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term6 _93804 _93824 s P f) : term6 _93804 _93824 s P f.
Proof. exact (h1). Qed.
Lemma lem3689894 (p : Prop) : p = (term12 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3689895 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term9 _93804 _93824 s P f) = (term47 _93804 _93824 s P f).
Proof. exact (@lem3689894 (term9 _93804 _93824 s P f)). Qed.
Lemma lem3689896 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term47 _93804 _93824 s P f) = (term9 _93804 _93824 s P f).
Proof. exact (SYM (@lem3689895 _93804 _93824 s P f)). Qed.
Lemma lem3689897 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term48 _93804 _93824 s P f) : term48 _93804 _93824 s P f.
Proof. exact (h1). Qed.
Lemma lem3689906 {_93804 : Type'} (x : _93804) (y : _93804) (t : _93804 -> Prop) : (term49 _93804 x y t) = (term50 _93804 x y t).
Proof. exact (@lem17045 (@IN _93804 x t) (@IN _93804 y t)). Qed.
Lemma lem3689921 {_93804 _93824 : Type'} (f : _93804 -> _93824) (x : _93804) (y : _93804) : (((f x) = (f y)) = (x = y)) = (term51 _93804 _93824 f x y).
Proof. exact (@lem17784 ((f x) = (f y)) (x = y)). Qed.
Lemma lem3689922 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3689923 {_93804 : Type'} (x : _93804) (y : _93804) (t : _93804 -> Prop) : (term52 _93804 x y t) = (term53 _93804 x y t).
Proof. exact (MK_COMB (@lem3689922) (@lem3689906 _93804 x y t)). Qed.
Lemma lem3689924 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (x : _93804) (y : _93804) : (term54 _93804 _93824 t f x y) = (term55 _93804 _93824 t f x y).
Proof. exact (MK_COMB (@lem3689923 _93804 x y t) (@lem3689921 _93804 _93824 f x y)). Qed.
Lemma lem3689925 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (x : _93804) (y : _93804) : (term35 _93804 _93824 t f x y) = (term54 _93804 _93824 t f x y).
Proof. exact (@lem17265 (term56 _93804 x y t) (((f x) = (f y)) = (x = y))). Qed.
Lemma lem3689926 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (x : _93804) (y : _93804) : (term35 _93804 _93824 t f x y) = (term55 _93804 _93824 t f x y).
Proof. exact (TRANS (@lem3689925 _93804 _93824 t f x y) (@lem3689924 _93804 _93824 t f x y)). Qed.
Lemma lem3689927 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (x : _93804) : (term36 _93804 _93824 t f x) = (term57 _93804 _93824 t f x).
Proof. exact (fun_ext (fun y : _93804 => @lem3689926 _93804 _93824 t f x y)). Qed.
Lemma lem3689928 {_93804 : Type'} : (@all _93804) = (@all _93804).
Proof. exact (eq_refl (@all _93804)). Qed.
Lemma lem3689929 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (x : _93804) : (term37 _93804 _93824 t f x) = (term58 _93804 _93824 t f x).
Proof. exact (MK_COMB (@lem3689928 _93804) (@lem3689927 _93804 _93824 t f x)). Qed.
Lemma lem3689930 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) : (term38 _93804 _93824 t f) = (term59 _93804 _93824 t f).
Proof. exact (fun_ext (fun x : _93804 => @lem3689929 _93804 _93824 t f x)). Qed.
Lemma lem3689931 {_93804 : Type'} : (@all _93804) = (@all _93804).
Proof. exact (eq_refl (@all _93804)). Qed.
Lemma lem3689932 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) : (term39 _93804 _93824 t f) = (term60 _93804 _93824 t f).
Proof. exact (MK_COMB (@lem3689931 _93804) (@lem3689930 _93804 _93824 t f)). Qed.
Lemma lem3689933 {_93804 _93824 : Type'} (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term34 _93804 _93824 P f t) = (term34 _93804 _93824 P f t).
Proof. exact (eq_refl (term34 _93804 _93824 P f t)). Qed.
Lemma lem3689934 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3689935 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) : (term40 _93804 _93824 t f) = (term61 _93804 _93824 t f).
Proof. exact (MK_COMB (@lem3689934) (@lem3689932 _93804 _93824 t f)). Qed.
Lemma lem3689936 {_93804 _93824 : Type'} (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term41 _93804 _93824 P f t) = (term62 _93804 _93824 P f t).
Proof. exact (MK_COMB (@lem3689935 _93804 _93824 t f) (@lem3689933 _93804 _93824 P f t)). Qed.
Lemma lem3689938 {_93804 : Type'} (t : _93804 -> Prop) (s : _93804 -> Prop) : (term42 _93804 t s) = (term42 _93804 t s).
Proof. exact (eq_refl (term42 _93804 t s)). Qed.
Lemma lem3689939 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term43 _93804 _93824 s P f t) = (term63 _93804 _93824 s P f t).
Proof. exact (MK_COMB (@lem3689938 _93804 t s) (@lem3689936 _93804 _93824 P f t)). Qed.
Lemma lem3689941 {_93804 : Type'} (t : _93804 -> Prop) : (term44 _93804 t) = (term44 _93804 t).
Proof. exact (eq_refl (term44 _93804 t)). Qed.
Lemma lem3689942 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term45 _93804 _93824 s P f t) = (term64 _93804 _93824 s P f t).
Proof. exact (MK_COMB (@lem3689941 _93804 t) (@lem3689939 _93804 _93824 s P f t)). Qed.
Lemma lem3689943 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term46 _93804 _93824 s P f) = (term65 _93804 _93824 s P f).
Proof. exact (fun_ext (fun t : _93804 -> Prop => @lem3689942 _93804 _93824 s P f t)). Qed.
Lemma lem3689944 {_93804 : Type'} : (@ex (_93804 -> Prop)) = (@ex (_93804 -> Prop)).
Proof. exact (eq_refl (@ex (_93804 -> Prop))). Qed.
Lemma lem3690029 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term6 _93804 _93824 s P f) = (term66 _93804 _93824 s P f).
Proof. exact (MK_COMB (@lem3689944 _93804) (@lem3689943 _93804 _93824 s P f)). Qed.
Lemma lem3690030 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term6 _93804 _93824 s P f) : term66 _93804 _93824 s P f.
Proof. exact (EQ_MP (@lem3690029 _93804 _93824 s P f) (@lem3689892 _93804 _93824 s P f h1)). Qed.
Lemma lem3690038 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term67 _93804 _93824 s P f t) = (term68 _93804 _93824 s P f t).
Proof. exact (@lem17045 (@SUBSET _93804 t s) (term34 _93804 _93824 P f t)). Qed.
Lemma lem3690040 {_93804 : Type'} (t : _93804 -> Prop) : (term69 _93804 t) = (term69 _93804 t).
Proof. exact (eq_refl (term69 _93804 t)). Qed.
Lemma lem3690041 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term70 _93804 _93824 s P f t) = (term71 _93804 _93824 s P f t).
Proof. exact (MK_COMB (@lem3690040 _93804 t) (@lem3690038 _93804 _93824 s P f t)). Qed.
Lemma lem3690042 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term72 _93804 _93824 s P f t) = (term70 _93804 _93824 s P f t).
Proof. exact (@lem17045 (@FINITE _93804 t) (term73 _93804 _93824 s P f t)). Qed.
Lemma lem3690043 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term72 _93804 _93824 s P f t) = (term71 _93804 _93824 s P f t).
Proof. exact (TRANS (@lem3690042 _93804 _93824 s P f t) (@lem3690041 _93804 _93824 s P f t)). Qed.
Lemma lem3690044 {_93804 : Type'} (P : type686 _93804) : (term74 _93804 P) = (term75 _93804 P).
Proof. exact (@lem18394 (_93804 -> Prop) P). Qed.
Lemma lem3690045 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term48 _93804 _93824 s P f) = (term76 _93804 _93824 s P f).
Proof. exact (@lem3690044 _93804 (term33 _93804 _93824 s P f)). Qed.
Lemma lem3690046 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term77 _93804 _93824 s P f t) = (term32 _93804 _93824 s P f t).
Proof. exact (eq_refl (term77 _93804 _93824 s P f t)). Qed.
Lemma lem3690047 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3690048 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term78 _93804 _93824 s P f t) = (term72 _93804 _93824 s P f t).
Proof. exact (MK_COMB (@lem3690047) (@lem3690046 _93804 _93824 s P f t)). Qed.
Lemma lem3690049 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term78 _93804 _93824 s P f t) = (term71 _93804 _93824 s P f t).
Proof. exact (TRANS (@lem3690048 _93804 _93824 s P f t) (@lem3690043 _93804 _93824 s P f t)). Qed.
Lemma lem3690050 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term79 _93804 _93824 s P f) = (term80 _93804 _93824 s P f).
Proof. exact (fun_ext (fun t : _93804 -> Prop => @lem3690049 _93804 _93824 s P f t)). Qed.
Lemma lem3690051 {_93804 : Type'} : (@all (_93804 -> Prop)) = (@all (_93804 -> Prop)).
Proof. exact (eq_refl (@all (_93804 -> Prop))). Qed.
Lemma lem3690052 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term76 _93804 _93824 s P f) = (term81 _93804 _93824 s P f).
Proof. exact (MK_COMB (@lem3690051 _93804) (@lem3690050 _93804 _93824 s P f)). Qed.
Lemma lem3690105 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term48 _93804 _93824 s P f) = (term81 _93804 _93824 s P f).
Proof. exact (TRANS (@lem3690045 _93804 _93824 s P f) (@lem3690052 _93804 _93824 s P f)). Qed.
Lemma lem3690106 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term48 _93804 _93824 s P f) : term81 _93804 _93824 s P f.
Proof. exact (EQ_MP (@lem3690105 _93804 _93824 s P f) (@lem3689897 _93804 _93824 s P f h1)). Qed.
Lemma lem3690107 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) (h1 : term64 _93804 _93824 s P f t) : term64 _93804 _93824 s P f t.
Proof. exact (h1). Qed.
Lemma lem3690134 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term71 _93804 _93824 s P f t) = (term71 _93804 _93824 s P f t).
Proof. exact (eq_refl (term71 _93804 _93824 s P f t)). Qed.
Lemma lem3690135 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term80 _93804 _93824 s P f) = (term80 _93804 _93824 s P f).
Proof. exact (fun_ext (fun t : _93804 -> Prop => @lem3690134 _93804 _93824 s P f t)). Qed.
Lemma lem3690136 {_93804 : Type'} : (@all (_93804 -> Prop)) = (@all (_93804 -> Prop)).
Proof. exact (eq_refl (@all (_93804 -> Prop))). Qed.
Lemma lem3690137 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term81 _93804 _93824 s P f) = (term81 _93804 _93824 s P f).
Proof. exact (MK_COMB (@lem3690136 _93804) (@lem3690135 _93804 _93824 s P f)). Qed.
Lemma lem3690138 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term48 _93804 _93824 s P f) : term81 _93804 _93824 s P f.
Proof. exact (EQ_MP (@lem3690137 _93804 _93824 s P f) (@lem3690106 _93804 _93824 s P f h1)). Qed.
Lemma lem3690145 {_93804 _93824 : Type'} (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term34 _93804 _93824 P f t) = (term34 _93804 _93824 P f t).
Proof. exact (eq_refl (term34 _93804 _93824 P f t)). Qed.
Lemma lem3690150 {_93804 : Type'} (x : _93804) (y : _93804) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem3690151 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3690152 {_93824 : Type'} : (@eq _93824) = (@eq _93824).
Proof. exact (eq_refl (@eq _93824)). Qed.
Lemma lem3690157 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3690159 {_93804 _93824 : Type'} (f : _93804 -> _93824) (x : _93804) : (f x) = (@I (_93804 -> _93824) f x).
Proof. exact (@lem3690157 _93804 _93824 f x). Qed.
Lemma lem3690164 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3690165 {_93804 _93824 : Type'} (f : _93804 -> _93824) (x : _93804) : (f x) = (@I (_93804 -> _93824) f x).
Proof. exact (@lem3690164 _93804 _93824 f x). Qed.
Lemma lem3690167 {_93804 _93824 : Type'} (f : _93804 -> _93824) (y : _93804) : (f y) = (@I (_93804 -> _93824) f y).
Proof. exact (@lem3690165 _93804 _93824 f y). Qed.
Lemma lem3690168 {_93804 _93824 : Type'} (f : _93804 -> _93824) (x : _93804) : (term82 _93804 _93824 f x) = (term83 _93804 _93824 f x).
Proof. exact (MK_COMB (@lem3690152 _93824) (@lem3690159 _93804 _93824 f x)). Qed.
Lemma lem3690169 {_93804 _93824 : Type'} (x : _93804) (f : _93804 -> _93824) (y : _93804) : ((f x) = (f y)) = ((@I (_93804 -> _93824) f x) = (@I (_93804 -> _93824) f y)).
Proof. exact (MK_COMB (@lem3690168 _93804 _93824 f x) (@lem3690167 _93804 _93824 f y)). Qed.
Lemma lem3690170 {_93804 _93824 : Type'} (x : _93804) (f : _93804 -> _93824) (y : _93804) : (term84 _93804 _93824 x f y) = (term85 _93804 _93824 x f y).
Proof. exact (MK_COMB (@lem3690151) (@lem3690169 _93804 _93824 x f y)). Qed.
Lemma lem3690171 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3690172 {_93804 _93824 : Type'} (x : _93804) (f : _93804 -> _93824) (y : _93804) : (term86 _93804 _93824 x f y) = (term87 _93804 _93824 x f y).
Proof. exact (MK_COMB (@lem3690171) (@lem3690170 _93804 _93824 x f y)). Qed.
Lemma lem3690173 {_93804 _93824 : Type'} (f : _93804 -> _93824) (x : _93804) (y : _93804) : (term88 _93804 _93824 f x y) = (term89 _93804 _93824 f x y).
Proof. exact (MK_COMB (@lem3690172 _93804 _93824 x f y) (@lem3690150 _93804 x y)). Qed.
Lemma lem3690180 {_93804 : Type'} (x : _93804) (y : _93804) : (term90 _93804 x y) = (term90 _93804 x y).
Proof. exact (eq_refl (term90 _93804 x y)). Qed.
Lemma lem3690181 {_93824 : Type'} : (@eq _93824) = (@eq _93824).
Proof. exact (eq_refl (@eq _93824)). Qed.
Lemma lem3690186 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3690188 {_93804 _93824 : Type'} (f : _93804 -> _93824) (x : _93804) : (f x) = (@I (_93804 -> _93824) f x).
Proof. exact (@lem3690186 _93804 _93824 f x). Qed.
Lemma lem3690193 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3690194 {_93804 _93824 : Type'} (f : _93804 -> _93824) (x : _93804) : (f x) = (@I (_93804 -> _93824) f x).
Proof. exact (@lem3690193 _93804 _93824 f x). Qed.
Lemma lem3690196 {_93804 _93824 : Type'} (f : _93804 -> _93824) (y : _93804) : (f y) = (@I (_93804 -> _93824) f y).
Proof. exact (@lem3690194 _93804 _93824 f y). Qed.
Lemma lem3690197 {_93804 _93824 : Type'} (f : _93804 -> _93824) (x : _93804) : (term82 _93804 _93824 f x) = (term83 _93804 _93824 f x).
Proof. exact (MK_COMB (@lem3690181 _93824) (@lem3690188 _93804 _93824 f x)). Qed.
Lemma lem3690198 {_93804 _93824 : Type'} (x : _93804) (f : _93804 -> _93824) (y : _93804) : ((f x) = (f y)) = ((@I (_93804 -> _93824) f x) = (@I (_93804 -> _93824) f y)).
Proof. exact (MK_COMB (@lem3690197 _93804 _93824 f x) (@lem3690196 _93804 _93824 f y)). Qed.
Lemma lem3690199 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3690200 {_93804 _93824 : Type'} (x : _93804) (f : _93804 -> _93824) (y : _93804) : (term91 _93804 _93824 x f y) = (term92 _93804 _93824 x f y).
Proof. exact (MK_COMB (@lem3690199) (@lem3690198 _93804 _93824 x f y)). Qed.
Lemma lem3690201 {_93804 _93824 : Type'} (f : _93804 -> _93824) (x : _93804) (y : _93804) : (term93 _93804 _93824 f x y) = (term94 _93804 _93824 f x y).
Proof. exact (MK_COMB (@lem3690200 _93804 _93824 x f y) (@lem3690180 _93804 x y)). Qed.
Lemma lem3690202 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3690203 {_93804 _93824 : Type'} (f : _93804 -> _93824) (x : _93804) (y : _93804) : (term95 _93804 _93824 f x y) = (term96 _93804 _93824 f x y).
Proof. exact (MK_COMB (@lem3690202) (@lem3690201 _93804 _93824 f x y)). Qed.
Lemma lem3690204 {_93804 _93824 : Type'} (f : _93804 -> _93824) (x : _93804) (y : _93804) : (term51 _93804 _93824 f x y) = (term97 _93804 _93824 f x y).
Proof. exact (MK_COMB (@lem3690203 _93804 _93824 f x y) (@lem3690173 _93804 _93824 f x y)). Qed.
Lemma lem3690223 {_93804 : Type'} (x : _93804) (y : _93804) (t : _93804 -> Prop) : (term53 _93804 x y t) = (term53 _93804 x y t).
Proof. exact (eq_refl (term53 _93804 x y t)). Qed.
Lemma lem3690224 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (x : _93804) (y : _93804) : (term55 _93804 _93824 t f x y) = (term98 _93804 _93824 t f x y).
Proof. exact (MK_COMB (@lem3690223 _93804 x y t) (@lem3690204 _93804 _93824 f x y)). Qed.
Lemma lem3690225 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (x : _93804) : (term57 _93804 _93824 t f x) = (term99 _93804 _93824 t f x).
Proof. exact (fun_ext (fun y : _93804 => @lem3690224 _93804 _93824 t f x y)). Qed.
Lemma lem3690226 {_93804 : Type'} : (@all _93804) = (@all _93804).
Proof. exact (eq_refl (@all _93804)). Qed.
Lemma lem3690227 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (x : _93804) : (term58 _93804 _93824 t f x) = (term100 _93804 _93824 t f x).
Proof. exact (MK_COMB (@lem3690226 _93804) (@lem3690225 _93804 _93824 t f x)). Qed.
Lemma lem3690228 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) : (term59 _93804 _93824 t f) = (term101 _93804 _93824 t f).
Proof. exact (fun_ext (fun x : _93804 => @lem3690227 _93804 _93824 t f x)). Qed.
Lemma lem3690229 {_93804 : Type'} : (@all _93804) = (@all _93804).
Proof. exact (eq_refl (@all _93804)). Qed.
Lemma lem3690230 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) : (term60 _93804 _93824 t f) = (term102 _93804 _93824 t f).
Proof. exact (MK_COMB (@lem3690229 _93804) (@lem3690228 _93804 _93824 t f)). Qed.
Lemma lem3690231 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3690232 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) : (term61 _93804 _93824 t f) = (term103 _93804 _93824 t f).
Proof. exact (MK_COMB (@lem3690231) (@lem3690230 _93804 _93824 t f)). Qed.
Lemma lem3690233 {_93804 _93824 : Type'} (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term62 _93804 _93824 P f t) = (term104 _93804 _93824 P f t).
Proof. exact (MK_COMB (@lem3690232 _93804 _93824 t f) (@lem3690145 _93804 _93824 P f t)). Qed.
Lemma lem3690240 {_93804 : Type'} (t : _93804 -> Prop) (s : _93804 -> Prop) : (term42 _93804 t s) = (term42 _93804 t s).
Proof. exact (eq_refl (term42 _93804 t s)). Qed.
Lemma lem3690241 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term63 _93804 _93824 s P f t) = (term105 _93804 _93824 s P f t).
Proof. exact (MK_COMB (@lem3690240 _93804 t s) (@lem3690233 _93804 _93824 P f t)). Qed.
Lemma lem3690246 {_93804 : Type'} (t : _93804 -> Prop) : (term44 _93804 t) = (term44 _93804 t).
Proof. exact (eq_refl (term44 _93804 t)). Qed.
Lemma lem3690247 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term64 _93804 _93824 s P f t) = (term106 _93804 _93824 s P f t).
Proof. exact (MK_COMB (@lem3690246 _93804 t) (@lem3690241 _93804 _93824 s P f t)). Qed.
Lemma lem3690248 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) (h1 : term64 _93804 _93824 s P f t) : term106 _93804 _93824 s P f t.
Proof. exact (EQ_MP (@lem3690247 _93804 _93824 s P f t) (@lem3690107 _93804 _93824 s P f t h1)). Qed.
Lemma lem3690249 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) (h1 : term64 _93804 _93824 s P f t) : term105 _93804 _93824 s P f t.
Proof. exact (proj2 (@lem3690248 _93804 _93824 s P f t h1)). Qed.
Lemma lem3690251 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) (h1 : term64 _93804 _93824 s P f t) : term104 _93804 _93824 P f t.
Proof. exact (proj2 (@lem3690249 _93804 _93824 s P f t h1)). Qed.
Lemma lem3690268 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term71 _93804 _93824 s P f t) = (term71 _93804 _93824 s P f t).
Proof. exact (eq_refl (term71 _93804 _93824 s P f t)). Qed.
Lemma lem3690269 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term80 _93804 _93824 s P f) = (term80 _93804 _93824 s P f).
Proof. exact (fun_ext (fun t : _93804 -> Prop => @lem3690268 _93804 _93824 s P f t)). Qed.
Lemma lem3690270 {_93804 : Type'} : (@all (_93804 -> Prop)) = (@all (_93804 -> Prop)).
Proof. exact (eq_refl (@all (_93804 -> Prop))). Qed.
Lemma lem3690272 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term81 _93804 _93824 s P f) = (term81 _93804 _93824 s P f).
Proof. exact (MK_COMB (@lem3690270 _93804) (@lem3690269 _93804 _93824 s P f)). Qed.
Lemma lem3690273 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term48 _93804 _93824 s P f) : term81 _93804 _93824 s P f.
Proof. exact (EQ_MP (@lem3690272 _93804 _93824 s P f) (@lem3690138 _93804 _93824 s P f h1)). Qed.
Lemma lem3690330 {_93804 _93824 : Type'} (_42426 : _93804 -> Prop) (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term48 _93804 _93824 s P f) : term107 _93804 _93824 s P f _42426.
Proof. exact (@lem3690273 _93804 _93824 s P f h1 _42426). Qed.
Lemma lem3690331 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (_42426 : _93804 -> Prop) : (term107 _93804 _93824 s P f _42426) = (term71 _93804 _93824 s P f _42426).
Proof. exact (eq_refl (term107 _93804 _93824 s P f _42426)). Qed.
Lemma lem3690350 {_93804 _93824 : Type'} (_42426 : _93804 -> Prop) (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term48 _93804 _93824 s P f) : term71 _93804 _93824 s P f _42426.
Proof. exact (EQ_MP (@lem3690331 _93804 _93824 s P f _42426) (@lem3690330 _93804 _93824 _42426 s P f h1)). Qed.
Lemma lem3690492 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) (h1 : term64 _93804 _93824 s P f t) : @FINITE _93804 t.
Proof. exact (proj1 (@lem3690248 _93804 _93824 s P f t h1)). Qed.
Lemma lem3690493 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) (h1 : term64 _93804 _93824 s P f t) : term108 _93804 t.
Proof. exact (fun h0 : term109 _93804 t => @lem3690492 _93804 _93824 s P f t h1). Qed.
Lemma lem3690495 (p : Prop) : (term110 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3690496 {_93804 : Type'} (t : _93804 -> Prop) : (term108 _93804 t) = (@FINITE _93804 t).
Proof. exact (@lem3690495 (@FINITE _93804 t)). Qed.
Lemma lem3690497 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) (h1 : term64 _93804 _93824 s P f t) : @FINITE _93804 t.
Proof. exact (EQ_MP (@lem3690496 _93804 t) (@lem3690493 _93804 _93824 s P f t h1)). Qed.
Lemma lem3690499 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) (h1 : term64 _93804 _93824 s P f t) : @SUBSET _93804 t s.
Proof. exact (proj1 (@lem3690249 _93804 _93824 s P f t h1)). Qed.
Lemma lem3690500 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) (h1 : term64 _93804 _93824 s P f t) : term111 _93804 t s.
Proof. exact (fun h0 : term112 _93804 t s => @lem3690499 _93804 _93824 s P f t h1). Qed.
Lemma lem3690502 (p : Prop) : (term110 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3690503 {_93804 : Type'} (t : _93804 -> Prop) (s : _93804 -> Prop) : (term111 _93804 t s) = (@SUBSET _93804 t s).
Proof. exact (@lem3690502 (@SUBSET _93804 t s)). Qed.
Lemma lem3690504 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) (h1 : term64 _93804 _93824 s P f t) : @SUBSET _93804 t s.
Proof. exact (EQ_MP (@lem3690503 _93804 t s) (@lem3690500 _93804 _93824 s P f t h1)). Qed.
Lemma lem3690506 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) (h1 : term64 _93804 _93824 s P f t) : term34 _93804 _93824 P f t.
Proof. exact (proj2 (@lem3690251 _93804 _93824 s P f t h1)). Qed.
Lemma lem3690507 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) (h1 : term64 _93804 _93824 s P f t) : term113 _93804 _93824 P f t.
Proof. exact (fun h0 : term114 _93804 _93824 P f t => @lem3690506 _93804 _93824 s P f t h1). Qed.
Lemma lem3690509 (p : Prop) : (term110 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3690510 {_93804 _93824 : Type'} (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term113 _93804 _93824 P f t) = (term34 _93804 _93824 P f t).
Proof. exact (@lem3690509 (term34 _93804 _93824 P f t)). Qed.
Lemma lem3690511 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) (h1 : term64 _93804 _93824 s P f t) : term34 _93804 _93824 P f t.
Proof. exact (EQ_MP (@lem3690510 _93804 _93824 P f t) (@lem3690507 _93804 _93824 s P f t h1)). Qed.
Lemma lem3690513 (a : Prop) (b : Prop) : (term115 a b) = (term116 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3690514 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (_42426 : _93804 -> Prop) : (term68 _93804 _93824 s P f _42426) = (term67 _93804 _93824 s P f _42426).
Proof. exact (@lem3690513 (@SUBSET _93804 _42426 s) (term34 _93804 _93824 P f _42426)). Qed.
Lemma lem3690515 {_93804 : Type'} (_42426 : _93804 -> Prop) : (term69 _93804 _42426) = (term69 _93804 _42426).
Proof. exact (eq_refl (term69 _93804 _42426)). Qed.
Lemma lem3690516 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (_42426 : _93804 -> Prop) : (term71 _93804 _93824 s P f _42426) = (term70 _93804 _93824 s P f _42426).
Proof. exact (MK_COMB (@lem3690515 _93804 _42426) (@lem3690514 _93804 _93824 s P f _42426)). Qed.
Lemma lem3690518 (a : Prop) (b : Prop) : (term115 a b) = (term116 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3690519 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (_42426 : _93804 -> Prop) : (term70 _93804 _93824 s P f _42426) = (term72 _93804 _93824 s P f _42426).
Proof. exact (@lem3690518 (@FINITE _93804 _42426) (term73 _93804 _93824 s P f _42426)). Qed.
Lemma lem3690520 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (_42426 : _93804 -> Prop) : (term71 _93804 _93824 s P f _42426) = (term72 _93804 _93824 s P f _42426).
Proof. exact (TRANS (@lem3690516 _93804 _93824 s P f _42426) (@lem3690519 _93804 _93824 s P f _42426)). Qed.
Lemma lem3690522 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3690523 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (_42426 : _93804 -> Prop) : (term72 _93804 _93824 s P f _42426) = (term117 _93804 _93824 s P f _42426).
Proof. exact (@lem3690522 (term32 _93804 _93824 s P f _42426)). Qed.
Lemma lem3690524 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (_42426 : _93804 -> Prop) : (term71 _93804 _93824 s P f _42426) = (term117 _93804 _93824 s P f _42426).
Proof. exact (TRANS (@lem3690520 _93804 _93824 s P f _42426) (@lem3690523 _93804 _93824 s P f _42426)). Qed.
Lemma lem3690526 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) (h1 : term64 _93804 _93824 s P f t) : term73 _93804 _93824 s P f t.
Proof. exact (conj (@lem3690504 _93804 _93824 s P f t h1) (@lem3690511 _93804 _93824 s P f t h1)). Qed.
Lemma lem3690527 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) (h1 : term64 _93804 _93824 s P f t) : term32 _93804 _93824 s P f t.
Proof. exact (conj (@lem3690497 _93804 _93824 s P f t h1) (@lem3690526 _93804 _93824 s P f t h1)). Qed.
Lemma lem3690529 {_93804 _93824 : Type'} (_42426 : _93804 -> Prop) (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term48 _93804 _93824 s P f) : term117 _93804 _93824 s P f _42426.
Proof. exact (EQ_MP (@lem3690524 _93804 _93824 s P f _42426) (@lem3690350 _93804 _93824 _42426 s P f h1)). Qed.
Lemma lem3690530 {_93804 _93824 : Type'} (_42426 : _93804 -> Prop) (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term48 _93804 _93824 s P f) : term117 _93804 _93824 s P f _42426.
Proof. exact (@lem3690529 _93804 _93824 _42426 s P f h1). Qed.
Lemma lem3690531 {_93804 _93824 : Type'} (t : _93804 -> Prop) (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term48 _93804 _93824 s P f) : term117 _93804 _93824 s P f t.
Proof. exact (@lem3690530 _93804 _93824 t s P f h1). Qed.
Lemma lem3690534 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) (h1 : term48 _93804 _93824 s P f) (h2 : term64 _93804 _93824 s P f t) : False.
Proof. exact (@lem3690531 _93804 _93824 t s P f h1 (@lem3690527 _93804 _93824 s P f t h2)). Qed.
Lemma lem3690535 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) (h1 : term48 _93804 _93824 s P f) (h2 : term64 _93804 _93824 s P f t) : term118.
Proof. exact (fun h0 : ~ False => @lem3690534 _93804 _93824 s P f t h1 h2). Qed.
Lemma lem3690537 (p : Prop) : (term110 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3690538 : term118 = False.
Proof. exact (@lem3690537 False). Qed.
Lemma lem3690539 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) (h1 : term48 _93804 _93824 s P f) (h2 : term64 _93804 _93824 s P f t) : False.
Proof. exact (EQ_MP (@lem3690538) (@lem3690535 _93804 _93824 s P f t h1 h2)). Qed.
Lemma lem3690540 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term6 _93804 _93824 s P f) (h2 : term48 _93804 _93824 s P f) : False.
Proof. exact (ex_elim (@lem3690030 _93804 _93824 s P f h1) (fun t : _93804 -> Prop => fun h0 : term65 _93804 _93824 s P f t => @lem3690539 _93804 _93824 s P f t h2 h0)). Qed.
Lemma lem3690541 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term6 _93804 _93824 s P f) (h2 : term48 _93804 _93824 s P f) : (term48 _93804 _93824 s P f) = False.
Proof. exact (prop_ext (fun h3 : term48 _93804 _93824 s P f => @lem3690540 _93804 _93824 s P f h1 h2) (fun h3 : False => @lem3689897 _93804 _93824 s P f h2)). Qed.
Lemma lem3690542 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term6 _93804 _93824 s P f) (h2 : term48 _93804 _93824 s P f) : False.
Proof. exact (EQ_MP (@lem3690541 _93804 _93824 s P f h1 h2) (@lem3689897 _93804 _93824 s P f h2)). Qed.
Lemma lem3690543 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term6 _93804 _93824 s P f) : term47 _93804 _93824 s P f.
Proof. exact (fun h0 : term48 _93804 _93824 s P f => @lem3690542 _93804 _93824 s P f h1 h0). Qed.
Lemma lem3690544 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term6 _93804 _93824 s P f) : term9 _93804 _93824 s P f.
Proof. exact (EQ_MP (@lem3689896 _93804 _93824 s P f) (@lem3690543 _93804 _93824 s P f h1)). Qed.
Lemma lem3690545 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : term11 _93804 _93824 s P f.
Proof. exact (fun h0 : term6 _93804 _93824 s P f => @lem3690544 _93804 _93824 s P f h0). Qed.
Lemma lem3690550 {_93804 _93824 : Type'} (P : type686 _93824) (f : _93804 -> _93824) : term23 _93804 _93824 P f.
Proof. exact (fun s : _93804 -> Prop => @lem3690545 _93804 _93824 s P f). Qed.
Lemma lem3690555 {_93804 _93824 : Type'} (f : _93804 -> _93824) : term27 _93804 _93824 f.
Proof. exact (fun P : type686 _93824 => @lem3690550 _93804 _93824 P f). Qed.
Lemma lem3690560 {_93804 _93824 : Type'} : term31 _93804 _93824.
Proof. exact (fun f : _93804 -> _93824 => @lem3690555 _93804 _93824 f). Qed.
Lemma lem3690561 {_93804 _93824 : Type'} : term30 _93804 _93824.
Proof. exact (EQ_MP (@lem3689891 _93804 _93824) (@lem3690560 _93804 _93824)). Qed.
Lemma lem3690562 {_93804 _93824 : Type'} (f : _93804 -> _93824) : term119 _93804 _93824 f.
Proof. exact (@lem3690561 _93804 _93824 f). Qed.
Lemma lem3690563 {_93804 _93824 : Type'} (f : _93804 -> _93824) : (term119 _93804 _93824 f) = (term26 _93804 _93824 f).
Proof. exact (eq_refl (term119 _93804 _93824 f)). Qed.
Lemma lem3690564 {_93804 _93824 : Type'} (f : _93804 -> _93824) : term26 _93804 _93824 f.
Proof. exact (EQ_MP (@lem3690563 _93804 _93824 f) (@lem3690562 _93804 _93824 f)). Qed.
Lemma lem3690565 {_93804 _93824 : Type'} (f : _93804 -> _93824) (P : type686 _93824) : term120 _93804 _93824 f P.
Proof. exact (@lem3690564 _93804 _93824 f P). Qed.
Lemma lem3690566 {_93804 _93824 : Type'} (P : type686 _93824) (f : _93804 -> _93824) : (term120 _93804 _93824 f P) = (term22 _93804 _93824 P f).
Proof. exact (eq_refl (term120 _93804 _93824 f P)). Qed.
Lemma lem3690567 {_93804 _93824 : Type'} (P : type686 _93824) (f : _93804 -> _93824) : term22 _93804 _93824 P f.
Proof. exact (EQ_MP (@lem3690566 _93804 _93824 P f) (@lem3690565 _93804 _93824 f P)). Qed.
Lemma lem3690568 {_93804 _93824 : Type'} (P : type686 _93824) (f : _93804 -> _93824) (s : _93804 -> Prop) : term121 _93804 _93824 P f s.
Proof. exact (@lem3690567 _93804 _93824 P f s). Qed.
Lemma lem3690569 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term121 _93804 _93824 P f s) = (term13 _93804 _93824 s P f).
Proof. exact (eq_refl (term121 _93804 _93824 P f s)). Qed.
Lemma lem3690570 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : term13 _93804 _93824 s P f.
Proof. exact (EQ_MP (@lem3690569 _93804 _93824 s P f) (@lem3690568 _93804 _93824 P f s)). Qed.
Lemma lem3690572 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : term13 _93804 _93824 s P f.
Proof. exact (@lem3689647 _93804 _93824 s P f (@lem3690570 _93804 _93824 s P f)). Qed.
Lemma lem3690573 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term14 _93804 _93824 s P f) : False.
Proof. exact (@lem3690572 _93804 _93824 s P f (@lem3689631 _93804 _93824 s P f h1)). Qed.
Lemma lem3690574 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term14 _93804 _93824 s P f) : (term14 _93804 _93824 s P f) = False.
Proof. exact (prop_ext (fun h2 : term14 _93804 _93824 s P f => @lem3690573 _93804 _93824 s P f h1) (fun h2 : False => @lem3689631 _93804 _93824 s P f h1)). Qed.
Lemma lem3690575 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (h1 : term14 _93804 _93824 s P f) : False.
Proof. exact (EQ_MP (@lem3690574 _93804 _93824 s P f h1) (@lem3689631 _93804 _93824 s P f h1)). Qed.
Lemma lem3690576 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : term13 _93804 _93824 s P f.
Proof. exact (fun h0 : term14 _93804 _93824 s P f => @lem3690575 _93804 _93824 s P f h0). Qed.
Lemma lem3690577 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : term11 _93804 _93824 s P f.
Proof. exact (EQ_MP (@lem3689630 _93804 _93824 s P f) (@lem3690576 _93804 _93824 s P f)). Qed.
Lemma lem3690578 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : term10 _93804 _93824 s P f.
Proof. exact (EQ_MP (@lem3689626 _93804 _93824 s P f) (@lem3690577 _93804 _93824 s P f)). Qed.
Lemma lem3690580 (p : Prop) : p = (term12 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3690581 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term122 _93804 _93824 f s P) = (term123 _93804 _93824 f s P).
Proof. exact (@lem3690580 (term122 _93804 _93824 f s P)). Qed.
Lemma lem3690582 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term123 _93804 _93824 f s P) = (term122 _93804 _93824 f s P).
Proof. exact (SYM (@lem3690581 _93804 _93824 f s P)). Qed.
Lemma lem3690583 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term124 _93804 _93824 f s P) : term124 _93804 _93824 f s P.
Proof. exact (h1). Qed.
Lemma lem3690584 {_93804 B : Type'} : term125 _93804 B.
Proof. exact (@lem3615104 _93804 B). Qed.
Lemma lem3690585 {_93824 B : Type'} : term125 _93824 B.
Proof. exact (@lem3615104 _93824 B). Qed.
Lemma lem3690586 {_93804 A : Type'} : term126 _93804 A.
Proof. exact (@lem3615104 A _93804). Qed.
Lemma lem3690587 {_93824 A : Type'} : term126 _93824 A.
Proof. exact (@lem3615104 A _93824). Qed.
Lemma lem3690588 {_93804 _93824 : Type'} : term125 _93804 _93824.
Proof. exact (@lem3615104 _93804 _93824). Qed.
Lemma lem3690589 {_87604 _93804 : Type'} : term127 _87604 _93804.
Proof. exact (@lem3371475 _93804 _87604). Qed.
Lemma lem3690590 {_87604 _93824 : Type'} : term127 _87604 _93824.
Proof. exact (@lem3371475 _93824 _87604). Qed.
Lemma lem3690591 {_87593 _93804 : Type'} : term128 _87593 _93804.
Proof. exact (@lem3371475 _87593 _93804). Qed.
Lemma lem3690592 {_87593 _93824 : Type'} : term128 _87593 _93824.
Proof. exact (@lem3371475 _87593 _93824). Qed.
Lemma lem3690593 {_93804 _93824 : Type'} : term128 _93804 _93824.
Proof. exact (@lem3371475 _93804 _93824). Qed.
Lemma lem3690594 {_93824 A : Type'} : term127 _93824 A.
Proof. exact (@lem3371475 A _93824). Qed.
Lemma lem3690595 {_93804 A : Type'} : term127 _93804 A.
Proof. exact (@lem3371475 A _93804). Qed.
Lemma lem3690596 {_93824 B : Type'} : term128 _93824 B.
Proof. exact (@lem3371475 _93824 B). Qed.
Lemma lem3690597 {_93804 B : Type'} : term128 _93804 B.
Proof. exact (@lem3371475 _93804 B). Qed.
Lemma lem3690600 {_87593 _87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term129 _87593 _87604 _93804 _93824 A B f s P) : term129 _87593 _87604 _93804 _93824 A B f s P.
Proof. exact (h1). Qed.
Lemma lem3690601 {_87593 _87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : term130 _87593 _87604 _93804 _93824 A B f s P.
Proof. exact (fun h0 : term129 _87593 _87604 _93804 _93824 A B f s P => @lem3690600 _87593 _87604 _93804 _93824 A B f s P h0). Qed.
Lemma lem3690602 {_87593 _87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term130 _87593 _87604 _93804 _93824 A B f s P) : term130 _87593 _87604 _93804 _93824 A B f s P.
Proof. exact (h1). Qed.
Lemma lem3690603 {_87593 _87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term129 _87593 _87604 _93804 _93824 A B f s P) : term129 _87593 _87604 _93804 _93824 A B f s P.
Proof. exact (h1). Qed.
Lemma lem3690604 {_87593 _87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term129 _87593 _87604 _93804 _93824 A B f s P) (h2 : term130 _87593 _87604 _93804 _93824 A B f s P) : term129 _87593 _87604 _93804 _93824 A B f s P.
Proof. exact (@lem3690602 _87593 _87604 _93804 _93824 A B f s P h2 (@lem3690603 _87593 _87604 _93804 _93824 A B f s P h1)). Qed.
Lemma lem3690605 {_87593 _87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term129 _87593 _87604 _93804 _93824 A B f s P) : term131 _87593 _87604 _93804 _93824 A B f s P.
Proof. exact (fun h0 : term130 _87593 _87604 _93804 _93824 A B f s P => @lem3690604 _87593 _87604 _93804 _93824 A B f s P h1 h0). Qed.
Lemma lem3690606 {_87593 _87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term130 _87593 _87604 _93804 _93824 A B f s P) : term130 _87593 _87604 _93804 _93824 A B f s P.
Proof. exact (h1). Qed.
Lemma lem3690607 {_87593 _87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term129 _87593 _87604 _93804 _93824 A B f s P) (h2 : term130 _87593 _87604 _93804 _93824 A B f s P) : term129 _87593 _87604 _93804 _93824 A B f s P.
Proof. exact (@lem3690605 _87593 _87604 _93804 _93824 A B f s P h1 (@lem3690606 _87593 _87604 _93804 _93824 A B f s P h2)). Qed.
Lemma lem3690608 {_87593 _87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term130 _87593 _87604 _93804 _93824 A B f s P) : term130 _87593 _87604 _93804 _93824 A B f s P.
Proof. exact (fun h0 : term129 _87593 _87604 _93804 _93824 A B f s P => @lem3690607 _87593 _87604 _93804 _93824 A B f s P h0 h1). Qed.
Lemma lem3690609 {_87593 _87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : term132 _87593 _87604 _93804 _93824 A B f s P.
Proof. exact (fun h0 : term130 _87593 _87604 _93804 _93824 A B f s P => @lem3690608 _87593 _87604 _93804 _93824 A B f s P h0). Qed.
Lemma lem3690612 {_87593 _87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : term130 _87593 _87604 _93804 _93824 A B f s P.
Proof. exact (@lem3690609 _87593 _87604 _93804 _93824 A B f s P (@lem3690601 _87593 _87604 _93804 _93824 A B f s P)). Qed.
Lemma lem3690613 {_87593 _87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : term130 _87593 _87604 _93804 _93824 A B f s P.
Proof. exact (@lem3690612 _87593 _87604 _93804 _93824 A B f s P). Qed.
Lemma lem3690887 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3690888 {_93824 A : Type'} : (term133 _93824 A) = (term134 _93824 A).
Proof. exact (@lem3690887 (term126 _93824 A)). Qed.
Lemma lem3690899 {_93804 A : Type'} : (term135 _93804 A) = (term135 _93804 A).
Proof. exact (eq_refl (term135 _93804 A)). Qed.
Lemma lem3690900 {_93804 _93824 A : Type'} : (term136 _93804 _93824 A) = (term137 _93804 _93824 A).
Proof. exact (MK_COMB (@lem3690899 _93804 A) (@lem3690888 _93824 A)). Qed.
Lemma lem3690903 {_93824 B : Type'} : (term138 _93824 B) = (term138 _93824 B).
Proof. exact (eq_refl (term138 _93824 B)). Qed.
Lemma lem3690904 {_93804 _93824 A B : Type'} : (term139 _93804 _93824 A B) = (term140 _93804 _93824 A B).
Proof. exact (MK_COMB (@lem3690903 _93824 B) (@lem3690900 _93804 _93824 A)). Qed.
Lemma lem3690907 {_93804 B : Type'} : (term138 _93804 B) = (term138 _93804 B).
Proof. exact (eq_refl (term138 _93804 B)). Qed.
Lemma lem3690908 {_93804 _93824 A B : Type'} : (term141 _93804 _93824 A B) = (term142 _93804 _93824 A B).
Proof. exact (MK_COMB (@lem3690907 _93804 B) (@lem3690904 _93804 _93824 A B)). Qed.
Lemma lem3690911 {_93804 _93824 : Type'} : (term138 _93804 _93824) = (term138 _93804 _93824).
Proof. exact (eq_refl (term138 _93804 _93824)). Qed.
Lemma lem3690912 {_93804 _93824 A B : Type'} : (term143 _93804 _93824 A B) = (term144 _93804 _93824 A B).
Proof. exact (MK_COMB (@lem3690911 _93804 _93824) (@lem3690908 _93804 _93824 A B)). Qed.
Lemma lem3690915 {_93824 A : Type'} : (term145 _93824 A) = (term145 _93824 A).
Proof. exact (eq_refl (term145 _93824 A)). Qed.
Lemma lem3690916 {_93804 _93824 A B : Type'} : (term146 _93804 _93824 A B) = (term147 _93804 _93824 A B).
Proof. exact (MK_COMB (@lem3690915 _93824 A) (@lem3690912 _93804 _93824 A B)). Qed.
Lemma lem3690919 {_93804 A : Type'} : (term145 _93804 A) = (term145 _93804 A).
Proof. exact (eq_refl (term145 _93804 A)). Qed.
Lemma lem3690920 {_93804 _93824 A B : Type'} : (term148 _93804 _93824 A B) = (term149 _93804 _93824 A B).
Proof. exact (MK_COMB (@lem3690919 _93804 A) (@lem3690916 _93804 _93824 A B)). Qed.
Lemma lem3690923 {_93824 B : Type'} : (term150 _93824 B) = (term150 _93824 B).
Proof. exact (eq_refl (term150 _93824 B)). Qed.
Lemma lem3690924 {_93804 _93824 A B : Type'} : (term151 _93804 _93824 A B) = (term152 _93804 _93824 A B).
Proof. exact (MK_COMB (@lem3690923 _93824 B) (@lem3690920 _93804 _93824 A B)). Qed.
Lemma lem3690927 {_87604 _93824 : Type'} : (term145 _87604 _93824) = (term145 _87604 _93824).
Proof. exact (eq_refl (term145 _87604 _93824)). Qed.
Lemma lem3690928 {_87604 _93804 _93824 A B : Type'} : (term153 _87604 _93804 _93824 A B) = (term154 _87604 _93804 _93824 A B).
Proof. exact (MK_COMB (@lem3690927 _87604 _93824) (@lem3690924 _93804 _93824 A B)). Qed.
Lemma lem3690931 {_93804 B : Type'} : (term150 _93804 B) = (term150 _93804 B).
Proof. exact (eq_refl (term150 _93804 B)). Qed.
Lemma lem3690932 {_87604 _93804 _93824 A B : Type'} : (term155 _87604 _93804 _93824 A B) = (term156 _87604 _93804 _93824 A B).
Proof. exact (MK_COMB (@lem3690931 _93804 B) (@lem3690928 _87604 _93804 _93824 A B)). Qed.
Lemma lem3690935 {_93804 _93824 : Type'} : (term150 _93804 _93824) = (term150 _93804 _93824).
Proof. exact (eq_refl (term150 _93804 _93824)). Qed.
Lemma lem3690936 {_87604 _93804 _93824 A B : Type'} : (term157 _87604 _93804 _93824 A B) = (term158 _87604 _93804 _93824 A B).
Proof. exact (MK_COMB (@lem3690935 _93804 _93824) (@lem3690932 _87604 _93804 _93824 A B)). Qed.
Lemma lem3690939 {_87604 _93804 : Type'} : (term145 _87604 _93804) = (term145 _87604 _93804).
Proof. exact (eq_refl (term145 _87604 _93804)). Qed.
Lemma lem3690940 {_87604 _93804 _93824 A B : Type'} : (term159 _87604 _93804 _93824 A B) = (term160 _87604 _93804 _93824 A B).
Proof. exact (MK_COMB (@lem3690939 _87604 _93804) (@lem3690936 _87604 _93804 _93824 A B)). Qed.
Lemma lem3690943 {_87593 _93824 : Type'} : (term150 _87593 _93824) = (term150 _87593 _93824).
Proof. exact (eq_refl (term150 _87593 _93824)). Qed.
Lemma lem3690944 {_87593 _87604 _93804 _93824 A B : Type'} : (term161 _87593 _87604 _93804 _93824 A B) = (term162 _87593 _87604 _93804 _93824 A B).
Proof. exact (MK_COMB (@lem3690943 _87593 _93824) (@lem3690940 _87604 _93804 _93824 A B)). Qed.
Lemma lem3690947 {_87593 _93804 : Type'} : (term150 _87593 _93804) = (term150 _87593 _93804).
Proof. exact (eq_refl (term150 _87593 _93804)). Qed.
Lemma lem3690948 {_87593 _87604 _93804 _93824 A B : Type'} : (term163 _87593 _87604 _93804 _93824 A B) = (term164 _87593 _87604 _93804 _93824 A B).
Proof. exact (MK_COMB (@lem3690947 _87593 _93804) (@lem3690944 _87593 _87604 _93804 _93824 A B)). Qed.
Lemma lem3690951 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term165 _93804 _93824 f s P) = (term165 _93804 _93824 f s P).
Proof. exact (eq_refl (term165 _93804 _93824 f s P)). Qed.
Lemma lem3690952 {_87593 _87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term129 _87593 _87604 _93804 _93824 A B f s P) = (term166 _87593 _87604 _93804 _93824 A B f s P).
Proof. exact (MK_COMB (@lem3690951 _93804 _93824 f s P) (@lem3690948 _87593 _87604 _93804 _93824 A B)). Qed.
Lemma lem3690955 {_87593 _87604 _93804 _93824 A B : Type'} (s : _93804 -> Prop) (P : type686 _93824) : (term167 _87593 _87604 _93804 _93824 A B s P) = (term168 _87593 _87604 _93804 _93824 A B s P).
Proof. exact (fun_ext (fun f : _93804 -> _93824 => @lem3690952 _87593 _87604 _93804 _93824 A B f s P)). Qed.
Lemma lem3690956 {_93804 _93824 : Type'} : (@all (_93804 -> _93824)) = (@all (_93804 -> _93824)).
Proof. exact (eq_refl (@all (_93804 -> _93824))). Qed.
Lemma lem3690957 {_87593 _87604 _93804 _93824 A B : Type'} (s : _93804 -> Prop) (P : type686 _93824) : (term169 _87593 _87604 _93804 _93824 A B s P) = (term170 _87593 _87604 _93804 _93824 A B s P).
Proof. exact (MK_COMB (@lem3690956 _93804 _93824) (@lem3690955 _87593 _87604 _93804 _93824 A B s P)). Qed.
Lemma lem3690962 {_87593 _87604 _93804 _93824 A B : Type'} (P : type686 _93824) : (term171 _87593 _87604 _93804 _93824 A B P) = (term172 _87593 _87604 _93804 _93824 A B P).
Proof. exact (fun_ext (fun s : _93804 -> Prop => @lem3690957 _87593 _87604 _93804 _93824 A B s P)). Qed.
Lemma lem3690963 {_93804 : Type'} : (@all (_93804 -> Prop)) = (@all (_93804 -> Prop)).
Proof. exact (eq_refl (@all (_93804 -> Prop))). Qed.
Lemma lem3690964 {_87593 _87604 _93804 _93824 A B : Type'} (P : type686 _93824) : (term173 _87593 _87604 _93804 _93824 A B P) = (term174 _87593 _87604 _93804 _93824 A B P).
Proof. exact (MK_COMB (@lem3690963 _93804) (@lem3690962 _87593 _87604 _93804 _93824 A B P)). Qed.
Lemma lem3690969 {_87593 _87604 _93804 _93824 A B : Type'} : (term175 _87593 _87604 _93804 _93824 A B) = (term176 _87593 _87604 _93804 _93824 A B).
Proof. exact (fun_ext (fun P : type686 _93824 => @lem3690964 _87593 _87604 _93804 _93824 A B P)). Qed.
Lemma lem3690970 {_93824 : Type'} : (@all ((_93824 -> Prop) -> Prop)) = (@all ((_93824 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_93824 -> Prop) -> Prop))). Qed.
Lemma lem3690979 {_87593 _87604 _93804 _93824 A B : Type'} : (term177 _87593 _87604 _93804 _93824 A B) = (term178 _87593 _87604 _93804 _93824 A B).
Proof. exact (MK_COMB (@lem3690970 _93824) (@lem3690969 _87593 _87604 _93804 _93824 A B)). Qed.
Lemma lem3690984 {_93824 A : Type'} (f : A -> _93824) (s : A -> Prop) : (term179 _93824 A f s) = (term179 _93824 A f s).
Proof. exact (eq_refl (term179 _93824 A f s)). Qed.
Lemma lem3690985 {_93824 A : Type'} (f : A -> _93824) : (term180 _93824 A f) = (term180 _93824 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3690984 _93824 A f s)). Qed.
Lemma lem3690986 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3690987 {_93824 A : Type'} (f : A -> _93824) : (term181 _93824 A f) = (term181 _93824 A f).
Proof. exact (MK_COMB (@lem3690986 A) (@lem3690985 _93824 A f)). Qed.
Lemma lem3690988 {_93824 A : Type'} : (term182 _93824 A) = (term182 _93824 A).
Proof. exact (fun_ext (fun f : A -> _93824 => @lem3690987 _93824 A f)). Qed.
Lemma lem3690989 {_93824 A : Type'} : (@all (A -> _93824)) = (@all (A -> _93824)).
Proof. exact (eq_refl (@all (A -> _93824))). Qed.
Lemma lem3690990 {_93824 A : Type'} : (term126 _93824 A) = (term126 _93824 A).
Proof. exact (MK_COMB (@lem3690989 _93824 A) (@lem3690988 _93824 A)). Qed.
Lemma lem3690991 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3690992 {_93824 A : Type'} : (term134 _93824 A) = (term134 _93824 A).
Proof. exact (MK_COMB (@lem3690991) (@lem3690990 _93824 A)). Qed.
Lemma lem3690997 {_93804 A : Type'} (f : A -> _93804) (s : A -> Prop) : (term179 _93804 A f s) = (term179 _93804 A f s).
Proof. exact (eq_refl (term179 _93804 A f s)). Qed.
Lemma lem3690998 {_93804 A : Type'} (f : A -> _93804) : (term180 _93804 A f) = (term180 _93804 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3690997 _93804 A f s)). Qed.
Lemma lem3690999 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3691000 {_93804 A : Type'} (f : A -> _93804) : (term181 _93804 A f) = (term181 _93804 A f).
Proof. exact (MK_COMB (@lem3690999 A) (@lem3690998 _93804 A f)). Qed.
Lemma lem3691001 {_93804 A : Type'} : (term182 _93804 A) = (term182 _93804 A).
Proof. exact (fun_ext (fun f : A -> _93804 => @lem3691000 _93804 A f)). Qed.
Lemma lem3691002 {_93804 A : Type'} : (@all (A -> _93804)) = (@all (A -> _93804)).
Proof. exact (eq_refl (@all (A -> _93804))). Qed.
Lemma lem3691003 {_93804 A : Type'} : (term126 _93804 A) = (term126 _93804 A).
Proof. exact (MK_COMB (@lem3691002 _93804 A) (@lem3691001 _93804 A)). Qed.
Lemma lem3691004 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3691005 {_93804 A : Type'} : (term135 _93804 A) = (term135 _93804 A).
Proof. exact (MK_COMB (@lem3691004) (@lem3691003 _93804 A)). Qed.
Lemma lem3691006 {_93804 _93824 A : Type'} : (term137 _93804 _93824 A) = (term137 _93804 _93824 A).
Proof. exact (MK_COMB (@lem3691005 _93804 A) (@lem3690992 _93824 A)). Qed.
Lemma lem3691011 {_93824 B : Type'} (f : _93824 -> B) (s : _93824 -> Prop) : (term183 _93824 B f s) = (term183 _93824 B f s).
Proof. exact (eq_refl (term183 _93824 B f s)). Qed.
Lemma lem3691012 {_93824 B : Type'} (f : _93824 -> B) : (term184 _93824 B f) = (term184 _93824 B f).
Proof. exact (fun_ext (fun s : _93824 -> Prop => @lem3691011 _93824 B f s)). Qed.
Lemma lem3691013 {_93824 : Type'} : (@all (_93824 -> Prop)) = (@all (_93824 -> Prop)).
Proof. exact (eq_refl (@all (_93824 -> Prop))). Qed.
Lemma lem3691014 {_93824 B : Type'} (f : _93824 -> B) : (term185 _93824 B f) = (term185 _93824 B f).
Proof. exact (MK_COMB (@lem3691013 _93824) (@lem3691012 _93824 B f)). Qed.
Lemma lem3691015 {_93824 B : Type'} : (term186 _93824 B) = (term186 _93824 B).
Proof. exact (fun_ext (fun f : _93824 -> B => @lem3691014 _93824 B f)). Qed.
Lemma lem3691016 {_93824 B : Type'} : (@all (_93824 -> B)) = (@all (_93824 -> B)).
Proof. exact (eq_refl (@all (_93824 -> B))). Qed.
Lemma lem3691017 {_93824 B : Type'} : (term125 _93824 B) = (term125 _93824 B).
Proof. exact (MK_COMB (@lem3691016 _93824 B) (@lem3691015 _93824 B)). Qed.
Lemma lem3691018 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3691019 {_93824 B : Type'} : (term138 _93824 B) = (term138 _93824 B).
Proof. exact (MK_COMB (@lem3691018) (@lem3691017 _93824 B)). Qed.
Lemma lem3691020 {_93804 _93824 A B : Type'} : (term140 _93804 _93824 A B) = (term140 _93804 _93824 A B).
Proof. exact (MK_COMB (@lem3691019 _93824 B) (@lem3691006 _93804 _93824 A)). Qed.
Lemma lem3691025 {_93804 B : Type'} (f : _93804 -> B) (s : _93804 -> Prop) : (term183 _93804 B f s) = (term183 _93804 B f s).
Proof. exact (eq_refl (term183 _93804 B f s)). Qed.
Lemma lem3691026 {_93804 B : Type'} (f : _93804 -> B) : (term184 _93804 B f) = (term184 _93804 B f).
Proof. exact (fun_ext (fun s : _93804 -> Prop => @lem3691025 _93804 B f s)). Qed.
Lemma lem3691027 {_93804 : Type'} : (@all (_93804 -> Prop)) = (@all (_93804 -> Prop)).
Proof. exact (eq_refl (@all (_93804 -> Prop))). Qed.
Lemma lem3691028 {_93804 B : Type'} (f : _93804 -> B) : (term185 _93804 B f) = (term185 _93804 B f).
Proof. exact (MK_COMB (@lem3691027 _93804) (@lem3691026 _93804 B f)). Qed.
Lemma lem3691029 {_93804 B : Type'} : (term186 _93804 B) = (term186 _93804 B).
Proof. exact (fun_ext (fun f : _93804 -> B => @lem3691028 _93804 B f)). Qed.
Lemma lem3691030 {_93804 B : Type'} : (@all (_93804 -> B)) = (@all (_93804 -> B)).
Proof. exact (eq_refl (@all (_93804 -> B))). Qed.
Lemma lem3691031 {_93804 B : Type'} : (term125 _93804 B) = (term125 _93804 B).
Proof. exact (MK_COMB (@lem3691030 _93804 B) (@lem3691029 _93804 B)). Qed.
Lemma lem3691032 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3691033 {_93804 B : Type'} : (term138 _93804 B) = (term138 _93804 B).
Proof. exact (MK_COMB (@lem3691032) (@lem3691031 _93804 B)). Qed.
Lemma lem3691034 {_93804 _93824 A B : Type'} : (term142 _93804 _93824 A B) = (term142 _93804 _93824 A B).
Proof. exact (MK_COMB (@lem3691033 _93804 B) (@lem3691020 _93804 _93824 A B)). Qed.
Lemma lem3691039 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) : (term183 _93804 _93824 f s) = (term183 _93804 _93824 f s).
Proof. exact (eq_refl (term183 _93804 _93824 f s)). Qed.
Lemma lem3691040 {_93804 _93824 : Type'} (f : _93804 -> _93824) : (term184 _93804 _93824 f) = (term184 _93804 _93824 f).
Proof. exact (fun_ext (fun s : _93804 -> Prop => @lem3691039 _93804 _93824 f s)). Qed.
Lemma lem3691041 {_93804 : Type'} : (@all (_93804 -> Prop)) = (@all (_93804 -> Prop)).
Proof. exact (eq_refl (@all (_93804 -> Prop))). Qed.
Lemma lem3691042 {_93804 _93824 : Type'} (f : _93804 -> _93824) : (term185 _93804 _93824 f) = (term185 _93804 _93824 f).
Proof. exact (MK_COMB (@lem3691041 _93804) (@lem3691040 _93804 _93824 f)). Qed.
Lemma lem3691043 {_93804 _93824 : Type'} : (term186 _93804 _93824) = (term186 _93804 _93824).
Proof. exact (fun_ext (fun f : _93804 -> _93824 => @lem3691042 _93804 _93824 f)). Qed.
Lemma lem3691044 {_93804 _93824 : Type'} : (@all (_93804 -> _93824)) = (@all (_93804 -> _93824)).
Proof. exact (eq_refl (@all (_93804 -> _93824))). Qed.
Lemma lem3691045 {_93804 _93824 : Type'} : (term125 _93804 _93824) = (term125 _93804 _93824).
Proof. exact (MK_COMB (@lem3691044 _93804 _93824) (@lem3691043 _93804 _93824)). Qed.
Lemma lem3691046 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3691047 {_93804 _93824 : Type'} : (term138 _93804 _93824) = (term138 _93804 _93824).
Proof. exact (MK_COMB (@lem3691046) (@lem3691045 _93804 _93824)). Qed.
Lemma lem3691048 {_93804 _93824 A B : Type'} : (term144 _93804 _93824 A B) = (term144 _93804 _93824 A B).
Proof. exact (MK_COMB (@lem3691047 _93804 _93824) (@lem3691034 _93804 _93824 A B)). Qed.
Lemma lem3691053 {_93824 A : Type'} (s : A -> Prop) (f : A -> _93824) (t : A -> Prop) : (term187 _93824 A s f t) = (term187 _93824 A s f t).
Proof. exact (eq_refl (term187 _93824 A s f t)). Qed.
Lemma lem3691054 {_93824 A : Type'} (s : A -> Prop) (f : A -> _93824) : (term188 _93824 A s f) = (term188 _93824 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3691053 _93824 A s f t)). Qed.
Lemma lem3691055 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3691056 {_93824 A : Type'} (s : A -> Prop) (f : A -> _93824) : (term189 _93824 A s f) = (term189 _93824 A s f).
Proof. exact (MK_COMB (@lem3691055 A) (@lem3691054 _93824 A s f)). Qed.
Lemma lem3691057 {_93824 A : Type'} (f : A -> _93824) : (term190 _93824 A f) = (term190 _93824 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3691056 _93824 A s f)). Qed.
Lemma lem3691058 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3691059 {_93824 A : Type'} (f : A -> _93824) : (term191 _93824 A f) = (term191 _93824 A f).
Proof. exact (MK_COMB (@lem3691058 A) (@lem3691057 _93824 A f)). Qed.
Lemma lem3691060 {_93824 A : Type'} : (term192 _93824 A) = (term192 _93824 A).
Proof. exact (fun_ext (fun f : A -> _93824 => @lem3691059 _93824 A f)). Qed.
Lemma lem3691061 {_93824 A : Type'} : (@all (A -> _93824)) = (@all (A -> _93824)).
Proof. exact (eq_refl (@all (A -> _93824))). Qed.
Lemma lem3691062 {_93824 A : Type'} : (term127 _93824 A) = (term127 _93824 A).
Proof. exact (MK_COMB (@lem3691061 _93824 A) (@lem3691060 _93824 A)). Qed.
Lemma lem3691063 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3691064 {_93824 A : Type'} : (term145 _93824 A) = (term145 _93824 A).
Proof. exact (MK_COMB (@lem3691063) (@lem3691062 _93824 A)). Qed.
Lemma lem3691065 {_93804 _93824 A B : Type'} : (term147 _93804 _93824 A B) = (term147 _93804 _93824 A B).
Proof. exact (MK_COMB (@lem3691064 _93824 A) (@lem3691048 _93804 _93824 A B)). Qed.
Lemma lem3691070 {_93804 A : Type'} (s : A -> Prop) (f : A -> _93804) (t : A -> Prop) : (term187 _93804 A s f t) = (term187 _93804 A s f t).
Proof. exact (eq_refl (term187 _93804 A s f t)). Qed.
Lemma lem3691071 {_93804 A : Type'} (s : A -> Prop) (f : A -> _93804) : (term188 _93804 A s f) = (term188 _93804 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3691070 _93804 A s f t)). Qed.
Lemma lem3691072 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3691073 {_93804 A : Type'} (s : A -> Prop) (f : A -> _93804) : (term189 _93804 A s f) = (term189 _93804 A s f).
Proof. exact (MK_COMB (@lem3691072 A) (@lem3691071 _93804 A s f)). Qed.
Lemma lem3691074 {_93804 A : Type'} (f : A -> _93804) : (term190 _93804 A f) = (term190 _93804 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3691073 _93804 A s f)). Qed.
Lemma lem3691075 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3691076 {_93804 A : Type'} (f : A -> _93804) : (term191 _93804 A f) = (term191 _93804 A f).
Proof. exact (MK_COMB (@lem3691075 A) (@lem3691074 _93804 A f)). Qed.
Lemma lem3691077 {_93804 A : Type'} : (term192 _93804 A) = (term192 _93804 A).
Proof. exact (fun_ext (fun f : A -> _93804 => @lem3691076 _93804 A f)). Qed.
Lemma lem3691078 {_93804 A : Type'} : (@all (A -> _93804)) = (@all (A -> _93804)).
Proof. exact (eq_refl (@all (A -> _93804))). Qed.
Lemma lem3691079 {_93804 A : Type'} : (term127 _93804 A) = (term127 _93804 A).
Proof. exact (MK_COMB (@lem3691078 _93804 A) (@lem3691077 _93804 A)). Qed.
Lemma lem3691080 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3691081 {_93804 A : Type'} : (term145 _93804 A) = (term145 _93804 A).
Proof. exact (MK_COMB (@lem3691080) (@lem3691079 _93804 A)). Qed.
Lemma lem3691082 {_93804 _93824 A B : Type'} : (term149 _93804 _93824 A B) = (term149 _93804 _93824 A B).
Proof. exact (MK_COMB (@lem3691081 _93804 A) (@lem3691065 _93804 _93824 A B)). Qed.
Lemma lem3691087 {_93824 B : Type'} (s : _93824 -> Prop) (f : _93824 -> B) (t : _93824 -> Prop) : (term193 _93824 B s f t) = (term193 _93824 B s f t).
Proof. exact (eq_refl (term193 _93824 B s f t)). Qed.
Lemma lem3691088 {_93824 B : Type'} (s : _93824 -> Prop) (f : _93824 -> B) : (term194 _93824 B s f) = (term194 _93824 B s f).
Proof. exact (fun_ext (fun t : _93824 -> Prop => @lem3691087 _93824 B s f t)). Qed.
Lemma lem3691089 {_93824 : Type'} : (@all (_93824 -> Prop)) = (@all (_93824 -> Prop)).
Proof. exact (eq_refl (@all (_93824 -> Prop))). Qed.
Lemma lem3691090 {_93824 B : Type'} (s : _93824 -> Prop) (f : _93824 -> B) : (term195 _93824 B s f) = (term195 _93824 B s f).
Proof. exact (MK_COMB (@lem3691089 _93824) (@lem3691088 _93824 B s f)). Qed.
Lemma lem3691091 {_93824 B : Type'} (f : _93824 -> B) : (term196 _93824 B f) = (term196 _93824 B f).
Proof. exact (fun_ext (fun s : _93824 -> Prop => @lem3691090 _93824 B s f)). Qed.
Lemma lem3691092 {_93824 : Type'} : (@all (_93824 -> Prop)) = (@all (_93824 -> Prop)).
Proof. exact (eq_refl (@all (_93824 -> Prop))). Qed.
Lemma lem3691093 {_93824 B : Type'} (f : _93824 -> B) : (term197 _93824 B f) = (term197 _93824 B f).
Proof. exact (MK_COMB (@lem3691092 _93824) (@lem3691091 _93824 B f)). Qed.
Lemma lem3691094 {_93824 B : Type'} : (term198 _93824 B) = (term198 _93824 B).
Proof. exact (fun_ext (fun f : _93824 -> B => @lem3691093 _93824 B f)). Qed.
Lemma lem3691095 {_93824 B : Type'} : (@all (_93824 -> B)) = (@all (_93824 -> B)).
Proof. exact (eq_refl (@all (_93824 -> B))). Qed.
Lemma lem3691096 {_93824 B : Type'} : (term128 _93824 B) = (term128 _93824 B).
Proof. exact (MK_COMB (@lem3691095 _93824 B) (@lem3691094 _93824 B)). Qed.
Lemma lem3691097 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3691098 {_93824 B : Type'} : (term150 _93824 B) = (term150 _93824 B).
Proof. exact (MK_COMB (@lem3691097) (@lem3691096 _93824 B)). Qed.
Lemma lem3691099 {_93804 _93824 A B : Type'} : (term152 _93804 _93824 A B) = (term152 _93804 _93824 A B).
Proof. exact (MK_COMB (@lem3691098 _93824 B) (@lem3691082 _93804 _93824 A B)). Qed.
Lemma lem3691104 {_87604 _93824 : Type'} (s : _93824 -> Prop) (f : _93824 -> _87604) (t : _93824 -> Prop) : (term187 _87604 _93824 s f t) = (term187 _87604 _93824 s f t).
Proof. exact (eq_refl (term187 _87604 _93824 s f t)). Qed.
Lemma lem3691105 {_87604 _93824 : Type'} (s : _93824 -> Prop) (f : _93824 -> _87604) : (term188 _87604 _93824 s f) = (term188 _87604 _93824 s f).
Proof. exact (fun_ext (fun t : _93824 -> Prop => @lem3691104 _87604 _93824 s f t)). Qed.
Lemma lem3691106 {_93824 : Type'} : (@all (_93824 -> Prop)) = (@all (_93824 -> Prop)).
Proof. exact (eq_refl (@all (_93824 -> Prop))). Qed.
Lemma lem3691107 {_87604 _93824 : Type'} (s : _93824 -> Prop) (f : _93824 -> _87604) : (term189 _87604 _93824 s f) = (term189 _87604 _93824 s f).
Proof. exact (MK_COMB (@lem3691106 _93824) (@lem3691105 _87604 _93824 s f)). Qed.
Lemma lem3691108 {_87604 _93824 : Type'} (f : _93824 -> _87604) : (term190 _87604 _93824 f) = (term190 _87604 _93824 f).
Proof. exact (fun_ext (fun s : _93824 -> Prop => @lem3691107 _87604 _93824 s f)). Qed.
Lemma lem3691109 {_93824 : Type'} : (@all (_93824 -> Prop)) = (@all (_93824 -> Prop)).
Proof. exact (eq_refl (@all (_93824 -> Prop))). Qed.
Lemma lem3691110 {_87604 _93824 : Type'} (f : _93824 -> _87604) : (term191 _87604 _93824 f) = (term191 _87604 _93824 f).
Proof. exact (MK_COMB (@lem3691109 _93824) (@lem3691108 _87604 _93824 f)). Qed.
Lemma lem3691111 {_87604 _93824 : Type'} : (term192 _87604 _93824) = (term192 _87604 _93824).
Proof. exact (fun_ext (fun f : _93824 -> _87604 => @lem3691110 _87604 _93824 f)). Qed.
Lemma lem3691112 {_87604 _93824 : Type'} : (@all (_93824 -> _87604)) = (@all (_93824 -> _87604)).
Proof. exact (eq_refl (@all (_93824 -> _87604))). Qed.
Lemma lem3691113 {_87604 _93824 : Type'} : (term127 _87604 _93824) = (term127 _87604 _93824).
Proof. exact (MK_COMB (@lem3691112 _87604 _93824) (@lem3691111 _87604 _93824)). Qed.
Lemma lem3691114 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3691115 {_87604 _93824 : Type'} : (term145 _87604 _93824) = (term145 _87604 _93824).
Proof. exact (MK_COMB (@lem3691114) (@lem3691113 _87604 _93824)). Qed.
Lemma lem3691116 {_87604 _93804 _93824 A B : Type'} : (term154 _87604 _93804 _93824 A B) = (term154 _87604 _93804 _93824 A B).
Proof. exact (MK_COMB (@lem3691115 _87604 _93824) (@lem3691099 _93804 _93824 A B)). Qed.
Lemma lem3691121 {_93804 B : Type'} (s : _93804 -> Prop) (f : _93804 -> B) (t : _93804 -> Prop) : (term193 _93804 B s f t) = (term193 _93804 B s f t).
Proof. exact (eq_refl (term193 _93804 B s f t)). Qed.
Lemma lem3691122 {_93804 B : Type'} (s : _93804 -> Prop) (f : _93804 -> B) : (term194 _93804 B s f) = (term194 _93804 B s f).
Proof. exact (fun_ext (fun t : _93804 -> Prop => @lem3691121 _93804 B s f t)). Qed.
Lemma lem3691123 {_93804 : Type'} : (@all (_93804 -> Prop)) = (@all (_93804 -> Prop)).
Proof. exact (eq_refl (@all (_93804 -> Prop))). Qed.
Lemma lem3691124 {_93804 B : Type'} (s : _93804 -> Prop) (f : _93804 -> B) : (term195 _93804 B s f) = (term195 _93804 B s f).
Proof. exact (MK_COMB (@lem3691123 _93804) (@lem3691122 _93804 B s f)). Qed.
Lemma lem3691125 {_93804 B : Type'} (f : _93804 -> B) : (term196 _93804 B f) = (term196 _93804 B f).
Proof. exact (fun_ext (fun s : _93804 -> Prop => @lem3691124 _93804 B s f)). Qed.
Lemma lem3691126 {_93804 : Type'} : (@all (_93804 -> Prop)) = (@all (_93804 -> Prop)).
Proof. exact (eq_refl (@all (_93804 -> Prop))). Qed.
Lemma lem3691127 {_93804 B : Type'} (f : _93804 -> B) : (term197 _93804 B f) = (term197 _93804 B f).
Proof. exact (MK_COMB (@lem3691126 _93804) (@lem3691125 _93804 B f)). Qed.
Lemma lem3691128 {_93804 B : Type'} : (term198 _93804 B) = (term198 _93804 B).
Proof. exact (fun_ext (fun f : _93804 -> B => @lem3691127 _93804 B f)). Qed.
Lemma lem3691129 {_93804 B : Type'} : (@all (_93804 -> B)) = (@all (_93804 -> B)).
Proof. exact (eq_refl (@all (_93804 -> B))). Qed.
Lemma lem3691130 {_93804 B : Type'} : (term128 _93804 B) = (term128 _93804 B).
Proof. exact (MK_COMB (@lem3691129 _93804 B) (@lem3691128 _93804 B)). Qed.
Lemma lem3691131 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3691132 {_93804 B : Type'} : (term150 _93804 B) = (term150 _93804 B).
Proof. exact (MK_COMB (@lem3691131) (@lem3691130 _93804 B)). Qed.
Lemma lem3691133 {_87604 _93804 _93824 A B : Type'} : (term156 _87604 _93804 _93824 A B) = (term156 _87604 _93804 _93824 A B).
Proof. exact (MK_COMB (@lem3691132 _93804 B) (@lem3691116 _87604 _93804 _93824 A B)). Qed.
Lemma lem3691138 {_93804 _93824 : Type'} (s : _93804 -> Prop) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term193 _93804 _93824 s f t) = (term193 _93804 _93824 s f t).
Proof. exact (eq_refl (term193 _93804 _93824 s f t)). Qed.
Lemma lem3691139 {_93804 _93824 : Type'} (s : _93804 -> Prop) (f : _93804 -> _93824) : (term194 _93804 _93824 s f) = (term194 _93804 _93824 s f).
Proof. exact (fun_ext (fun t : _93804 -> Prop => @lem3691138 _93804 _93824 s f t)). Qed.
Lemma lem3691140 {_93804 : Type'} : (@all (_93804 -> Prop)) = (@all (_93804 -> Prop)).
Proof. exact (eq_refl (@all (_93804 -> Prop))). Qed.
Lemma lem3691141 {_93804 _93824 : Type'} (s : _93804 -> Prop) (f : _93804 -> _93824) : (term195 _93804 _93824 s f) = (term195 _93804 _93824 s f).
Proof. exact (MK_COMB (@lem3691140 _93804) (@lem3691139 _93804 _93824 s f)). Qed.
Lemma lem3691142 {_93804 _93824 : Type'} (f : _93804 -> _93824) : (term196 _93804 _93824 f) = (term196 _93804 _93824 f).
Proof. exact (fun_ext (fun s : _93804 -> Prop => @lem3691141 _93804 _93824 s f)). Qed.
Lemma lem3691143 {_93804 : Type'} : (@all (_93804 -> Prop)) = (@all (_93804 -> Prop)).
Proof. exact (eq_refl (@all (_93804 -> Prop))). Qed.
Lemma lem3691144 {_93804 _93824 : Type'} (f : _93804 -> _93824) : (term197 _93804 _93824 f) = (term197 _93804 _93824 f).
Proof. exact (MK_COMB (@lem3691143 _93804) (@lem3691142 _93804 _93824 f)). Qed.
Lemma lem3691145 {_93804 _93824 : Type'} : (term198 _93804 _93824) = (term198 _93804 _93824).
Proof. exact (fun_ext (fun f : _93804 -> _93824 => @lem3691144 _93804 _93824 f)). Qed.
Lemma lem3691146 {_93804 _93824 : Type'} : (@all (_93804 -> _93824)) = (@all (_93804 -> _93824)).
Proof. exact (eq_refl (@all (_93804 -> _93824))). Qed.
Lemma lem3691147 {_93804 _93824 : Type'} : (term128 _93804 _93824) = (term128 _93804 _93824).
Proof. exact (MK_COMB (@lem3691146 _93804 _93824) (@lem3691145 _93804 _93824)). Qed.
Lemma lem3691148 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3691149 {_93804 _93824 : Type'} : (term150 _93804 _93824) = (term150 _93804 _93824).
Proof. exact (MK_COMB (@lem3691148) (@lem3691147 _93804 _93824)). Qed.
Lemma lem3691150 {_87604 _93804 _93824 A B : Type'} : (term158 _87604 _93804 _93824 A B) = (term158 _87604 _93804 _93824 A B).
Proof. exact (MK_COMB (@lem3691149 _93804 _93824) (@lem3691133 _87604 _93804 _93824 A B)). Qed.
Lemma lem3691155 {_87604 _93804 : Type'} (s : _93804 -> Prop) (f : _93804 -> _87604) (t : _93804 -> Prop) : (term187 _87604 _93804 s f t) = (term187 _87604 _93804 s f t).
Proof. exact (eq_refl (term187 _87604 _93804 s f t)). Qed.
Lemma lem3691156 {_87604 _93804 : Type'} (s : _93804 -> Prop) (f : _93804 -> _87604) : (term188 _87604 _93804 s f) = (term188 _87604 _93804 s f).
Proof. exact (fun_ext (fun t : _93804 -> Prop => @lem3691155 _87604 _93804 s f t)). Qed.
Lemma lem3691157 {_93804 : Type'} : (@all (_93804 -> Prop)) = (@all (_93804 -> Prop)).
Proof. exact (eq_refl (@all (_93804 -> Prop))). Qed.
Lemma lem3691158 {_87604 _93804 : Type'} (s : _93804 -> Prop) (f : _93804 -> _87604) : (term189 _87604 _93804 s f) = (term189 _87604 _93804 s f).
Proof. exact (MK_COMB (@lem3691157 _93804) (@lem3691156 _87604 _93804 s f)). Qed.
Lemma lem3691159 {_87604 _93804 : Type'} (f : _93804 -> _87604) : (term190 _87604 _93804 f) = (term190 _87604 _93804 f).
Proof. exact (fun_ext (fun s : _93804 -> Prop => @lem3691158 _87604 _93804 s f)). Qed.
Lemma lem3691160 {_93804 : Type'} : (@all (_93804 -> Prop)) = (@all (_93804 -> Prop)).
Proof. exact (eq_refl (@all (_93804 -> Prop))). Qed.
Lemma lem3691161 {_87604 _93804 : Type'} (f : _93804 -> _87604) : (term191 _87604 _93804 f) = (term191 _87604 _93804 f).
Proof. exact (MK_COMB (@lem3691160 _93804) (@lem3691159 _87604 _93804 f)). Qed.
Lemma lem3691162 {_87604 _93804 : Type'} : (term192 _87604 _93804) = (term192 _87604 _93804).
Proof. exact (fun_ext (fun f : _93804 -> _87604 => @lem3691161 _87604 _93804 f)). Qed.
Lemma lem3691163 {_87604 _93804 : Type'} : (@all (_93804 -> _87604)) = (@all (_93804 -> _87604)).
Proof. exact (eq_refl (@all (_93804 -> _87604))). Qed.
Lemma lem3691164 {_87604 _93804 : Type'} : (term127 _87604 _93804) = (term127 _87604 _93804).
Proof. exact (MK_COMB (@lem3691163 _87604 _93804) (@lem3691162 _87604 _93804)). Qed.
Lemma lem3691165 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3691166 {_87604 _93804 : Type'} : (term145 _87604 _93804) = (term145 _87604 _93804).
Proof. exact (MK_COMB (@lem3691165) (@lem3691164 _87604 _93804)). Qed.
Lemma lem3691167 {_87604 _93804 _93824 A B : Type'} : (term160 _87604 _93804 _93824 A B) = (term160 _87604 _93804 _93824 A B).
Proof. exact (MK_COMB (@lem3691166 _87604 _93804) (@lem3691150 _87604 _93804 _93824 A B)). Qed.
Lemma lem3691172 {_87593 _93824 : Type'} (s : _87593 -> Prop) (f : _87593 -> _93824) (t : _87593 -> Prop) : (term193 _87593 _93824 s f t) = (term193 _87593 _93824 s f t).
Proof. exact (eq_refl (term193 _87593 _93824 s f t)). Qed.
Lemma lem3691173 {_87593 _93824 : Type'} (s : _87593 -> Prop) (f : _87593 -> _93824) : (term194 _87593 _93824 s f) = (term194 _87593 _93824 s f).
Proof. exact (fun_ext (fun t : _87593 -> Prop => @lem3691172 _87593 _93824 s f t)). Qed.
Lemma lem3691174 {_87593 : Type'} : (@all (_87593 -> Prop)) = (@all (_87593 -> Prop)).
Proof. exact (eq_refl (@all (_87593 -> Prop))). Qed.
Lemma lem3691175 {_87593 _93824 : Type'} (s : _87593 -> Prop) (f : _87593 -> _93824) : (term195 _87593 _93824 s f) = (term195 _87593 _93824 s f).
Proof. exact (MK_COMB (@lem3691174 _87593) (@lem3691173 _87593 _93824 s f)). Qed.
Lemma lem3691176 {_87593 _93824 : Type'} (f : _87593 -> _93824) : (term196 _87593 _93824 f) = (term196 _87593 _93824 f).
Proof. exact (fun_ext (fun s : _87593 -> Prop => @lem3691175 _87593 _93824 s f)). Qed.
Lemma lem3691177 {_87593 : Type'} : (@all (_87593 -> Prop)) = (@all (_87593 -> Prop)).
Proof. exact (eq_refl (@all (_87593 -> Prop))). Qed.
Lemma lem3691178 {_87593 _93824 : Type'} (f : _87593 -> _93824) : (term197 _87593 _93824 f) = (term197 _87593 _93824 f).
Proof. exact (MK_COMB (@lem3691177 _87593) (@lem3691176 _87593 _93824 f)). Qed.
Lemma lem3691179 {_87593 _93824 : Type'} : (term198 _87593 _93824) = (term198 _87593 _93824).
Proof. exact (fun_ext (fun f : _87593 -> _93824 => @lem3691178 _87593 _93824 f)). Qed.
Lemma lem3691180 {_87593 _93824 : Type'} : (@all (_87593 -> _93824)) = (@all (_87593 -> _93824)).
Proof. exact (eq_refl (@all (_87593 -> _93824))). Qed.
Lemma lem3691181 {_87593 _93824 : Type'} : (term128 _87593 _93824) = (term128 _87593 _93824).
Proof. exact (MK_COMB (@lem3691180 _87593 _93824) (@lem3691179 _87593 _93824)). Qed.
Lemma lem3691182 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3691183 {_87593 _93824 : Type'} : (term150 _87593 _93824) = (term150 _87593 _93824).
Proof. exact (MK_COMB (@lem3691182) (@lem3691181 _87593 _93824)). Qed.
Lemma lem3691184 {_87593 _87604 _93804 _93824 A B : Type'} : (term162 _87593 _87604 _93804 _93824 A B) = (term162 _87593 _87604 _93804 _93824 A B).
Proof. exact (MK_COMB (@lem3691183 _87593 _93824) (@lem3691167 _87604 _93804 _93824 A B)). Qed.
Lemma lem3691189 {_87593 _93804 : Type'} (s : _87593 -> Prop) (f : _87593 -> _93804) (t : _87593 -> Prop) : (term193 _87593 _93804 s f t) = (term193 _87593 _93804 s f t).
Proof. exact (eq_refl (term193 _87593 _93804 s f t)). Qed.
Lemma lem3691190 {_87593 _93804 : Type'} (s : _87593 -> Prop) (f : _87593 -> _93804) : (term194 _87593 _93804 s f) = (term194 _87593 _93804 s f).
Proof. exact (fun_ext (fun t : _87593 -> Prop => @lem3691189 _87593 _93804 s f t)). Qed.
Lemma lem3691191 {_87593 : Type'} : (@all (_87593 -> Prop)) = (@all (_87593 -> Prop)).
Proof. exact (eq_refl (@all (_87593 -> Prop))). Qed.
Lemma lem3691192 {_87593 _93804 : Type'} (s : _87593 -> Prop) (f : _87593 -> _93804) : (term195 _87593 _93804 s f) = (term195 _87593 _93804 s f).
Proof. exact (MK_COMB (@lem3691191 _87593) (@lem3691190 _87593 _93804 s f)). Qed.
Lemma lem3691193 {_87593 _93804 : Type'} (f : _87593 -> _93804) : (term196 _87593 _93804 f) = (term196 _87593 _93804 f).
Proof. exact (fun_ext (fun s : _87593 -> Prop => @lem3691192 _87593 _93804 s f)). Qed.
Lemma lem3691194 {_87593 : Type'} : (@all (_87593 -> Prop)) = (@all (_87593 -> Prop)).
Proof. exact (eq_refl (@all (_87593 -> Prop))). Qed.
Lemma lem3691195 {_87593 _93804 : Type'} (f : _87593 -> _93804) : (term197 _87593 _93804 f) = (term197 _87593 _93804 f).
Proof. exact (MK_COMB (@lem3691194 _87593) (@lem3691193 _87593 _93804 f)). Qed.
Lemma lem3691196 {_87593 _93804 : Type'} : (term198 _87593 _93804) = (term198 _87593 _93804).
Proof. exact (fun_ext (fun f : _87593 -> _93804 => @lem3691195 _87593 _93804 f)). Qed.
Lemma lem3691197 {_87593 _93804 : Type'} : (@all (_87593 -> _93804)) = (@all (_87593 -> _93804)).
Proof. exact (eq_refl (@all (_87593 -> _93804))). Qed.
Lemma lem3691198 {_87593 _93804 : Type'} : (term128 _87593 _93804) = (term128 _87593 _93804).
Proof. exact (MK_COMB (@lem3691197 _87593 _93804) (@lem3691196 _87593 _93804)). Qed.
Lemma lem3691199 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3691200 {_87593 _93804 : Type'} : (term150 _87593 _93804) = (term150 _87593 _93804).
Proof. exact (MK_COMB (@lem3691199) (@lem3691198 _87593 _93804)). Qed.
Lemma lem3691201 {_87593 _87604 _93804 _93824 A B : Type'} : (term164 _87593 _87604 _93804 _93824 A B) = (term164 _87593 _87604 _93804 _93824 A B).
Proof. exact (MK_COMB (@lem3691200 _87593 _93804) (@lem3691184 _87593 _87604 _93804 _93824 A B)). Qed.
Lemma lem3691210 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (t : _93824 -> Prop) : (term199 _93804 _93824 f s P t) = (term199 _93804 _93824 f s P t).
Proof. exact (eq_refl (term199 _93804 _93824 f s P t)). Qed.
Lemma lem3691211 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term200 _93804 _93824 f s P) = (term200 _93804 _93824 f s P).
Proof. exact (fun_ext (fun t : _93824 -> Prop => @lem3691210 _93804 _93824 f s P t)). Qed.
Lemma lem3691212 {_93824 : Type'} : (@ex (_93824 -> Prop)) = (@ex (_93824 -> Prop)).
Proof. exact (eq_refl (@ex (_93824 -> Prop))). Qed.
Lemma lem3691213 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term5 _93804 _93824 f s P) = (term5 _93804 _93824 f s P).
Proof. exact (MK_COMB (@lem3691212 _93824) (@lem3691211 _93804 _93824 f s P)). Qed.
Lemma lem3691222 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term32 _93804 _93824 s P f t) = (term32 _93804 _93824 s P f t).
Proof. exact (eq_refl (term32 _93804 _93824 s P f t)). Qed.
Lemma lem3691223 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term33 _93804 _93824 s P f) = (term33 _93804 _93824 s P f).
Proof. exact (fun_ext (fun t : _93804 -> Prop => @lem3691222 _93804 _93824 s P f t)). Qed.
Lemma lem3691224 {_93804 : Type'} : (@ex (_93804 -> Prop)) = (@ex (_93804 -> Prop)).
Proof. exact (eq_refl (@ex (_93804 -> Prop))). Qed.
Lemma lem3691225 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term9 _93804 _93824 s P f) = (term9 _93804 _93824 s P f).
Proof. exact (MK_COMB (@lem3691224 _93804) (@lem3691223 _93804 _93824 s P f)). Qed.
Lemma lem3691226 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3691227 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term201 _93804 _93824 s P f) = (term201 _93804 _93824 s P f).
Proof. exact (MK_COMB (@lem3691226) (@lem3691225 _93804 _93824 s P f)). Qed.
Lemma lem3691228 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term122 _93804 _93824 f s P) = (term122 _93804 _93824 f s P).
Proof. exact (MK_COMB (@lem3691227 _93804 _93824 s P f) (@lem3691213 _93804 _93824 f s P)). Qed.
Lemma lem3691229 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3691230 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term124 _93804 _93824 f s P) = (term124 _93804 _93824 f s P).
Proof. exact (MK_COMB (@lem3691229) (@lem3691228 _93804 _93824 f s P)). Qed.
Lemma lem3691231 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3691232 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term165 _93804 _93824 f s P) = (term165 _93804 _93824 f s P).
Proof. exact (MK_COMB (@lem3691231) (@lem3691230 _93804 _93824 f s P)). Qed.
Lemma lem3691233 {_87593 _87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term166 _87593 _87604 _93804 _93824 A B f s P) = (term166 _87593 _87604 _93804 _93824 A B f s P).
Proof. exact (MK_COMB (@lem3691232 _93804 _93824 f s P) (@lem3691201 _87593 _87604 _93804 _93824 A B)). Qed.
Lemma lem3691234 {_87593 _87604 _93804 _93824 A B : Type'} (s : _93804 -> Prop) (P : type686 _93824) : (term168 _87593 _87604 _93804 _93824 A B s P) = (term168 _87593 _87604 _93804 _93824 A B s P).
Proof. exact (fun_ext (fun f : _93804 -> _93824 => @lem3691233 _87593 _87604 _93804 _93824 A B f s P)). Qed.
Lemma lem3691235 {_93804 _93824 : Type'} : (@all (_93804 -> _93824)) = (@all (_93804 -> _93824)).
Proof. exact (eq_refl (@all (_93804 -> _93824))). Qed.
Lemma lem3691236 {_87593 _87604 _93804 _93824 A B : Type'} (s : _93804 -> Prop) (P : type686 _93824) : (term170 _87593 _87604 _93804 _93824 A B s P) = (term170 _87593 _87604 _93804 _93824 A B s P).
Proof. exact (MK_COMB (@lem3691235 _93804 _93824) (@lem3691234 _87593 _87604 _93804 _93824 A B s P)). Qed.
Lemma lem3691237 {_87593 _87604 _93804 _93824 A B : Type'} (P : type686 _93824) : (term172 _87593 _87604 _93804 _93824 A B P) = (term172 _87593 _87604 _93804 _93824 A B P).
Proof. exact (fun_ext (fun s : _93804 -> Prop => @lem3691236 _87593 _87604 _93804 _93824 A B s P)). Qed.
Lemma lem3691238 {_93804 : Type'} : (@all (_93804 -> Prop)) = (@all (_93804 -> Prop)).
Proof. exact (eq_refl (@all (_93804 -> Prop))). Qed.
Lemma lem3691239 {_87593 _87604 _93804 _93824 A B : Type'} (P : type686 _93824) : (term174 _87593 _87604 _93804 _93824 A B P) = (term174 _87593 _87604 _93804 _93824 A B P).
Proof. exact (MK_COMB (@lem3691238 _93804) (@lem3691237 _87593 _87604 _93804 _93824 A B P)). Qed.
Lemma lem3691240 {_87593 _87604 _93804 _93824 A B : Type'} : (term176 _87593 _87604 _93804 _93824 A B) = (term176 _87593 _87604 _93804 _93824 A B).
Proof. exact (fun_ext (fun P : type686 _93824 => @lem3691239 _87593 _87604 _93804 _93824 A B P)). Qed.
Lemma lem3691241 {_93824 : Type'} : (@all ((_93824 -> Prop) -> Prop)) = (@all ((_93824 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_93824 -> Prop) -> Prop))). Qed.
Lemma lem3691242 {_87593 _87604 _93804 _93824 A B : Type'} : (term178 _87593 _87604 _93804 _93824 A B) = (term178 _87593 _87604 _93804 _93824 A B).
Proof. exact (MK_COMB (@lem3691241 _93824) (@lem3691240 _87593 _87604 _93804 _93824 A B)). Qed.
Lemma lem3691563 {_87593 _87604 _93804 _93824 A B : Type'} : (term177 _87593 _87604 _93804 _93824 A B) = (term178 _87593 _87604 _93804 _93824 A B).
Proof. exact (TRANS (@lem3690979 _87593 _87604 _93804 _93824 A B) (@lem3691242 _87593 _87604 _93804 _93824 A B)). Qed.
Lemma lem3691564 {_87593 _87604 _93804 _93824 A B : Type'} : (term178 _87593 _87604 _93804 _93824 A B) = (term177 _87593 _87604 _93804 _93824 A B).
Proof. exact (SYM (@lem3691563 _87593 _87604 _93804 _93824 A B)). Qed.
Lemma lem3691565 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term124 _93804 _93824 f s P) : term124 _93804 _93824 f s P.
Proof. exact (h1). Qed.
Lemma lem3691569 {_93804 _93824 : Type'} (h1 : term128 _93804 _93824) : term128 _93804 _93824.
Proof. exact (h1). Qed.
Lemma lem3691575 {_93804 _93824 : Type'} (h1 : term125 _93804 _93824) : term125 _93804 _93824.
Proof. exact (h1). Qed.
Lemma lem3691588 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term32 _93804 _93824 s P f t) = (term32 _93804 _93824 s P f t).
Proof. exact (eq_refl (term32 _93804 _93824 s P f t)). Qed.
Lemma lem3691589 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term33 _93804 _93824 s P f) = (term33 _93804 _93824 s P f).
Proof. exact (fun_ext (fun t : _93804 -> Prop => @lem3691588 _93804 _93824 s P f t)). Qed.
Lemma lem3691590 {_93804 : Type'} : (@ex (_93804 -> Prop)) = (@ex (_93804 -> Prop)).
Proof. exact (eq_refl (@ex (_93804 -> Prop))). Qed.
Lemma lem3691591 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term9 _93804 _93824 s P f) = (term9 _93804 _93824 s P f).
Proof. exact (MK_COMB (@lem3691590 _93804) (@lem3691589 _93804 _93824 s P f)). Qed.
Lemma lem3691599 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (t : _93824 -> Prop) : (term202 _93804 _93824 f s P t) = (term203 _93804 _93824 f s P t).
Proof. exact (@lem17045 (term204 _93804 _93824 t f s) (P t)). Qed.
Lemma lem3691601 {_93824 : Type'} (t : _93824 -> Prop) : (term69 _93824 t) = (term69 _93824 t).
Proof. exact (eq_refl (term69 _93824 t)). Qed.
Lemma lem3691602 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (t : _93824 -> Prop) : (term205 _93804 _93824 f s P t) = (term206 _93804 _93824 f s P t).
Proof. exact (MK_COMB (@lem3691601 _93824 t) (@lem3691599 _93804 _93824 f s P t)). Qed.
Lemma lem3691603 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (t : _93824 -> Prop) : (term207 _93804 _93824 f s P t) = (term205 _93804 _93824 f s P t).
Proof. exact (@lem17045 (@FINITE _93824 t) (term208 _93804 _93824 f s P t)). Qed.
Lemma lem3691604 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (t : _93824 -> Prop) : (term207 _93804 _93824 f s P t) = (term206 _93804 _93824 f s P t).
Proof. exact (TRANS (@lem3691603 _93804 _93824 f s P t) (@lem3691602 _93804 _93824 f s P t)). Qed.
Lemma lem3691605 {_93824 : Type'} (P : type686 _93824) : (term74 _93824 P) = (term75 _93824 P).
Proof. exact (@lem18394 (_93824 -> Prop) P). Qed.
Lemma lem3691606 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term209 _93804 _93824 f s P) = (term210 _93804 _93824 f s P).
Proof. exact (@lem3691605 _93824 (term200 _93804 _93824 f s P)). Qed.
Lemma lem3691607 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (t : _93824 -> Prop) : (term211 _93804 _93824 f s P t) = (term199 _93804 _93824 f s P t).
Proof. exact (eq_refl (term211 _93804 _93824 f s P t)). Qed.
Lemma lem3691608 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3691609 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (t : _93824 -> Prop) : (term212 _93804 _93824 f s P t) = (term207 _93804 _93824 f s P t).
Proof. exact (MK_COMB (@lem3691608) (@lem3691607 _93804 _93824 f s P t)). Qed.
Lemma lem3691610 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (t : _93824 -> Prop) : (term212 _93804 _93824 f s P t) = (term206 _93804 _93824 f s P t).
Proof. exact (TRANS (@lem3691609 _93804 _93824 f s P t) (@lem3691604 _93804 _93824 f s P t)). Qed.
Lemma lem3691611 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term213 _93804 _93824 f s P) = (term214 _93804 _93824 f s P).
Proof. exact (fun_ext (fun t : _93824 -> Prop => @lem3691610 _93804 _93824 f s P t)). Qed.
Lemma lem3691612 {_93824 : Type'} : (@all (_93824 -> Prop)) = (@all (_93824 -> Prop)).
Proof. exact (eq_refl (@all (_93824 -> Prop))). Qed.
Lemma lem3691613 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term210 _93804 _93824 f s P) = (term215 _93804 _93824 f s P).
Proof. exact (MK_COMB (@lem3691612 _93824) (@lem3691611 _93804 _93824 f s P)). Qed.
Lemma lem3691614 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term209 _93804 _93824 f s P) = (term215 _93804 _93824 f s P).
Proof. exact (TRANS (@lem3691606 _93804 _93824 f s P) (@lem3691613 _93804 _93824 f s P)). Qed.
Lemma lem3691615 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3691616 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term216 _93804 _93824 s P f) = (term216 _93804 _93824 s P f).
Proof. exact (MK_COMB (@lem3691615) (@lem3691591 _93804 _93824 s P f)). Qed.
Lemma lem3691617 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term217 _93804 _93824 f s P) = (term218 _93804 _93824 f s P).
Proof. exact (MK_COMB (@lem3691616 _93804 _93824 s P f) (@lem3691614 _93804 _93824 f s P)). Qed.
Lemma lem3691618 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term124 _93804 _93824 f s P) = (term217 _93804 _93824 f s P).
Proof. exact (@lem17362 (term9 _93804 _93824 s P f) (term5 _93804 _93824 f s P)). Qed.
Lemma lem3691619 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term124 _93804 _93824 f s P) = (term218 _93804 _93824 f s P).
Proof. exact (TRANS (@lem3691618 _93804 _93824 f s P) (@lem3691617 _93804 _93824 f s P)). Qed.
Lemma lem3691698 {A : Type'} (P : A -> Prop) (Q : Prop) : (term219 A P Q) = (term220 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3691699 {_93804 : Type'} (P : type686 _93804) (Q : Prop) : (term221 _93804 P Q) = (term222 _93804 P Q).
Proof. exact (@lem3691698 (_93804 -> Prop) P Q). Qed.
Lemma lem3691700 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term223 _93804 _93824 f s P) = (term224 _93804 _93824 f s P).
Proof. exact (@lem3691699 _93804 (term33 _93804 _93824 s P f) (term215 _93804 _93824 f s P)). Qed.
Lemma lem3691701 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term77 _93804 _93824 s P f t) = (term32 _93804 _93824 s P f t).
Proof. exact (eq_refl (term77 _93804 _93824 s P f t)). Qed.
Lemma lem3691702 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term225 _93804 _93824 s P f) = (term33 _93804 _93824 s P f).
Proof. exact (fun_ext (fun t : _93804 -> Prop => @lem3691701 _93804 _93824 s P f t)). Qed.
Lemma lem3691703 {_93804 : Type'} : (@ex (_93804 -> Prop)) = (@ex (_93804 -> Prop)).
Proof. exact (eq_refl (@ex (_93804 -> Prop))). Qed.
Lemma lem3691704 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term226 _93804 _93824 s P f) = (term9 _93804 _93824 s P f).
Proof. exact (MK_COMB (@lem3691703 _93804) (@lem3691702 _93804 _93824 s P f)). Qed.
Lemma lem3691705 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3691706 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term227 _93804 _93824 s P f) = (term216 _93804 _93824 s P f).
Proof. exact (MK_COMB (@lem3691705) (@lem3691704 _93804 _93824 s P f)). Qed.
Lemma lem3691707 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term215 _93804 _93824 f s P) = (term215 _93804 _93824 f s P).
Proof. exact (eq_refl (term215 _93804 _93824 f s P)). Qed.
Lemma lem3691708 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term223 _93804 _93824 f s P) = (term218 _93804 _93824 f s P).
Proof. exact (MK_COMB (@lem3691706 _93804 _93824 s P f) (@lem3691707 _93804 _93824 f s P)). Qed.
Lemma lem3691709 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3691710 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term228 _93804 _93824 f s P) = (term229 _93804 _93824 f s P).
Proof. exact (MK_COMB (@lem3691709) (@lem3691708 _93804 _93824 f s P)). Qed.
Lemma lem3691711 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term77 _93804 _93824 s P f t) = (term32 _93804 _93824 s P f t).
Proof. exact (eq_refl (term77 _93804 _93824 s P f t)). Qed.
Lemma lem3691712 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3691713 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term230 _93804 _93824 s P f t) = (term231 _93804 _93824 s P f t).
Proof. exact (MK_COMB (@lem3691712) (@lem3691711 _93804 _93824 s P f t)). Qed.
Lemma lem3691714 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term215 _93804 _93824 f s P) = (term215 _93804 _93824 f s P).
Proof. exact (eq_refl (term215 _93804 _93824 f s P)). Qed.
Lemma lem3691715 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term232 _93804 _93824 t f s P) = (term233 _93804 _93824 t f s P).
Proof. exact (MK_COMB (@lem3691713 _93804 _93824 s P f t) (@lem3691714 _93804 _93824 f s P)). Qed.
Lemma lem3691716 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term234 _93804 _93824 f s P) = (term235 _93804 _93824 f s P).
Proof. exact (fun_ext (fun t : _93804 -> Prop => @lem3691715 _93804 _93824 t f s P)). Qed.
Lemma lem3691717 {_93804 : Type'} : (@ex (_93804 -> Prop)) = (@ex (_93804 -> Prop)).
Proof. exact (eq_refl (@ex (_93804 -> Prop))). Qed.
Lemma lem3691718 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term224 _93804 _93824 f s P) = (term236 _93804 _93824 f s P).
Proof. exact (MK_COMB (@lem3691717 _93804) (@lem3691716 _93804 _93824 f s P)). Qed.
Lemma lem3691719 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : ((term223 _93804 _93824 f s P) = (term224 _93804 _93824 f s P)) = ((term218 _93804 _93824 f s P) = (term236 _93804 _93824 f s P)).
Proof. exact (MK_COMB (@lem3691710 _93804 _93824 f s P) (@lem3691718 _93804 _93824 f s P)). Qed.
Lemma lem3691721 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term218 _93804 _93824 f s P) = (term236 _93804 _93824 f s P).
Proof. exact (EQ_MP (@lem3691719 _93804 _93824 f s P) (@lem3691700 _93804 _93824 f s P)). Qed.
Lemma lem3691722 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term124 _93804 _93824 f s P) = (term236 _93804 _93824 f s P).
Proof. exact (TRANS (@lem3691619 _93804 _93824 f s P) (@lem3691721 _93804 _93824 f s P)). Qed.
Lemma lem3691723 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term124 _93804 _93824 f s P) : term236 _93804 _93824 f s P.
Proof. exact (EQ_MP (@lem3691722 _93804 _93824 f s P) (@lem3691565 _93804 _93824 f s P h1)). Qed.
Lemma lem3691961 {_93804 _93824 : Type'} (s : _93804 -> Prop) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term193 _93804 _93824 s f t) = (term237 _93804 _93824 s f t).
Proof. exact (@lem17265 (@SUBSET _93804 s t) (term238 _93804 _93824 s f t)). Qed.
Lemma lem3691962 {_93804 _93824 : Type'} (s : _93804 -> Prop) (f : _93804 -> _93824) : (term194 _93804 _93824 s f) = (term239 _93804 _93824 s f).
Proof. exact (fun_ext (fun t : _93804 -> Prop => @lem3691961 _93804 _93824 s f t)). Qed.
Lemma lem3691963 {_93804 : Type'} : (@all (_93804 -> Prop)) = (@all (_93804 -> Prop)).
Proof. exact (eq_refl (@all (_93804 -> Prop))). Qed.
Lemma lem3691964 {_93804 _93824 : Type'} (s : _93804 -> Prop) (f : _93804 -> _93824) : (term195 _93804 _93824 s f) = (term240 _93804 _93824 s f).
Proof. exact (MK_COMB (@lem3691963 _93804) (@lem3691962 _93804 _93824 s f)). Qed.
Lemma lem3691965 {_93804 _93824 : Type'} (f : _93804 -> _93824) : (term196 _93804 _93824 f) = (term241 _93804 _93824 f).
Proof. exact (fun_ext (fun s : _93804 -> Prop => @lem3691964 _93804 _93824 s f)). Qed.
Lemma lem3691966 {_93804 : Type'} : (@all (_93804 -> Prop)) = (@all (_93804 -> Prop)).
Proof. exact (eq_refl (@all (_93804 -> Prop))). Qed.
Lemma lem3691967 {_93804 _93824 : Type'} (f : _93804 -> _93824) : (term197 _93804 _93824 f) = (term242 _93804 _93824 f).
Proof. exact (MK_COMB (@lem3691966 _93804) (@lem3691965 _93804 _93824 f)). Qed.
Lemma lem3691968 {_93804 _93824 : Type'} : (term198 _93804 _93824) = (term243 _93804 _93824).
Proof. exact (fun_ext (fun f : _93804 -> _93824 => @lem3691967 _93804 _93824 f)). Qed.
Lemma lem3691969 {_93804 _93824 : Type'} : (@all (_93804 -> _93824)) = (@all (_93804 -> _93824)).
Proof. exact (eq_refl (@all (_93804 -> _93824))). Qed.
Lemma lem3692030 {_93804 _93824 : Type'} : (term128 _93804 _93824) = (term244 _93804 _93824).
Proof. exact (MK_COMB (@lem3691969 _93804 _93824) (@lem3691968 _93804 _93824)). Qed.
Lemma lem3692031 {_93804 _93824 : Type'} (h1 : term128 _93804 _93824) : term244 _93804 _93824.
Proof. exact (EQ_MP (@lem3692030 _93804 _93824) (@lem3691569 _93804 _93824 h1)). Qed.
Lemma lem3692423 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) : (term183 _93804 _93824 f s) = (term245 _93804 _93824 f s).
Proof. exact (@lem17265 (@FINITE _93804 s) (term246 _93804 _93824 f s)). Qed.
Lemma lem3692424 {_93804 _93824 : Type'} (f : _93804 -> _93824) : (term184 _93804 _93824 f) = (term247 _93804 _93824 f).
Proof. exact (fun_ext (fun s : _93804 -> Prop => @lem3692423 _93804 _93824 f s)). Qed.
Lemma lem3692425 {_93804 : Type'} : (@all (_93804 -> Prop)) = (@all (_93804 -> Prop)).
Proof. exact (eq_refl (@all (_93804 -> Prop))). Qed.
Lemma lem3692426 {_93804 _93824 : Type'} (f : _93804 -> _93824) : (term185 _93804 _93824 f) = (term248 _93804 _93824 f).
Proof. exact (MK_COMB (@lem3692425 _93804) (@lem3692424 _93804 _93824 f)). Qed.
Lemma lem3692427 {_93804 _93824 : Type'} : (term186 _93804 _93824) = (term249 _93804 _93824).
Proof. exact (fun_ext (fun f : _93804 -> _93824 => @lem3692426 _93804 _93824 f)). Qed.
Lemma lem3692428 {_93804 _93824 : Type'} : (@all (_93804 -> _93824)) = (@all (_93804 -> _93824)).
Proof. exact (eq_refl (@all (_93804 -> _93824))). Qed.
Lemma lem3692485 {_93804 _93824 : Type'} : (term125 _93804 _93824) = (term250 _93804 _93824).
Proof. exact (MK_COMB (@lem3692428 _93804 _93824) (@lem3692427 _93804 _93824)). Qed.
Lemma lem3692486 {_93804 _93824 : Type'} (h1 : term125 _93804 _93824) : term250 _93804 _93824.
Proof. exact (EQ_MP (@lem3692485 _93804 _93824) (@lem3691575 _93804 _93824 h1)). Qed.
Lemma lem3692767 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term233 _93804 _93824 t f s P) : term233 _93804 _93824 t f s P.
Proof. exact (h1). Qed.
Lemma lem3692889 {_93804 _93824 : Type'} (s : _93804 -> Prop) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term237 _93804 _93824 s f t) = (term237 _93804 _93824 s f t).
Proof. exact (eq_refl (term237 _93804 _93824 s f t)). Qed.
Lemma lem3692890 {_93804 _93824 : Type'} (s : _93804 -> Prop) (f : _93804 -> _93824) : (term239 _93804 _93824 s f) = (term239 _93804 _93824 s f).
Proof. exact (fun_ext (fun t : _93804 -> Prop => @lem3692889 _93804 _93824 s f t)). Qed.
Lemma lem3692891 {_93804 : Type'} : (@all (_93804 -> Prop)) = (@all (_93804 -> Prop)).
Proof. exact (eq_refl (@all (_93804 -> Prop))). Qed.
Lemma lem3692892 {_93804 _93824 : Type'} (s : _93804 -> Prop) (f : _93804 -> _93824) : (term240 _93804 _93824 s f) = (term240 _93804 _93824 s f).
Proof. exact (MK_COMB (@lem3692891 _93804) (@lem3692890 _93804 _93824 s f)). Qed.
Lemma lem3692893 {_93804 _93824 : Type'} (f : _93804 -> _93824) : (term241 _93804 _93824 f) = (term241 _93804 _93824 f).
Proof. exact (fun_ext (fun s : _93804 -> Prop => @lem3692892 _93804 _93824 s f)). Qed.
Lemma lem3692894 {_93804 : Type'} : (@all (_93804 -> Prop)) = (@all (_93804 -> Prop)).
Proof. exact (eq_refl (@all (_93804 -> Prop))). Qed.
Lemma lem3692895 {_93804 _93824 : Type'} (f : _93804 -> _93824) : (term242 _93804 _93824 f) = (term242 _93804 _93824 f).
Proof. exact (MK_COMB (@lem3692894 _93804) (@lem3692893 _93804 _93824 f)). Qed.
Lemma lem3692896 {_93804 _93824 : Type'} : (term243 _93804 _93824) = (term243 _93804 _93824).
Proof. exact (fun_ext (fun f : _93804 -> _93824 => @lem3692895 _93804 _93824 f)). Qed.
Lemma lem3692897 {_93804 _93824 : Type'} : (@all (_93804 -> _93824)) = (@all (_93804 -> _93824)).
Proof. exact (eq_refl (@all (_93804 -> _93824))). Qed.
Lemma lem3692898 {_93804 _93824 : Type'} : (term244 _93804 _93824) = (term244 _93804 _93824).
Proof. exact (MK_COMB (@lem3692897 _93804 _93824) (@lem3692896 _93804 _93824)). Qed.
Lemma lem3692899 {_93804 _93824 : Type'} (h1 : term128 _93804 _93824) : term244 _93804 _93824.
Proof. exact (EQ_MP (@lem3692898 _93804 _93824) (@lem3692031 _93804 _93824 h1)). Qed.
Lemma lem3693079 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) : (term245 _93804 _93824 f s) = (term245 _93804 _93824 f s).
Proof. exact (eq_refl (term245 _93804 _93824 f s)). Qed.
Lemma lem3693080 {_93804 _93824 : Type'} (f : _93804 -> _93824) : (term247 _93804 _93824 f) = (term247 _93804 _93824 f).
Proof. exact (fun_ext (fun s : _93804 -> Prop => @lem3693079 _93804 _93824 f s)). Qed.
Lemma lem3693081 {_93804 : Type'} : (@all (_93804 -> Prop)) = (@all (_93804 -> Prop)).
Proof. exact (eq_refl (@all (_93804 -> Prop))). Qed.
Lemma lem3693082 {_93804 _93824 : Type'} (f : _93804 -> _93824) : (term248 _93804 _93824 f) = (term248 _93804 _93824 f).
Proof. exact (MK_COMB (@lem3693081 _93804) (@lem3693080 _93804 _93824 f)). Qed.
Lemma lem3693083 {_93804 _93824 : Type'} : (term249 _93804 _93824) = (term249 _93804 _93824).
Proof. exact (fun_ext (fun f : _93804 -> _93824 => @lem3693082 _93804 _93824 f)). Qed.
Lemma lem3693084 {_93804 _93824 : Type'} : (@all (_93804 -> _93824)) = (@all (_93804 -> _93824)).
Proof. exact (eq_refl (@all (_93804 -> _93824))). Qed.
Lemma lem3693085 {_93804 _93824 : Type'} : (term250 _93804 _93824) = (term250 _93804 _93824).
Proof. exact (MK_COMB (@lem3693084 _93804 _93824) (@lem3693083 _93804 _93824)). Qed.
Lemma lem3693086 {_93804 _93824 : Type'} (h1 : term125 _93804 _93824) : term250 _93804 _93824.
Proof. exact (EQ_MP (@lem3693085 _93804 _93824) (@lem3692486 _93804 _93824 h1)). Qed.
Lemma lem3693201 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (t : _93824 -> Prop) : (term206 _93804 _93824 f s P t) = (term206 _93804 _93824 f s P t).
Proof. exact (eq_refl (term206 _93804 _93824 f s P t)). Qed.
Lemma lem3693202 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term214 _93804 _93824 f s P) = (term214 _93804 _93824 f s P).
Proof. exact (fun_ext (fun t : _93824 -> Prop => @lem3693201 _93804 _93824 f s P t)). Qed.
Lemma lem3693203 {_93824 : Type'} : (@all (_93824 -> Prop)) = (@all (_93824 -> Prop)).
Proof. exact (eq_refl (@all (_93824 -> Prop))). Qed.
Lemma lem3693204 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term215 _93804 _93824 f s P) = (term215 _93804 _93824 f s P).
Proof. exact (MK_COMB (@lem3693203 _93824) (@lem3693202 _93804 _93824 f s P)). Qed.
Lemma lem3693227 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term231 _93804 _93824 s P f t) = (term231 _93804 _93824 s P f t).
Proof. exact (eq_refl (term231 _93804 _93824 s P f t)). Qed.
Lemma lem3693228 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term233 _93804 _93824 t f s P) = (term233 _93804 _93824 t f s P).
Proof. exact (MK_COMB (@lem3693227 _93804 _93824 s P f t) (@lem3693204 _93804 _93824 f s P)). Qed.
Lemma lem3693229 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term233 _93804 _93824 t f s P) : term233 _93804 _93824 t f s P.
Proof. exact (EQ_MP (@lem3693228 _93804 _93824 t f s P) (@lem3692767 _93804 _93824 t f s P h1)). Qed.
Lemma lem3693230 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term233 _93804 _93824 t f s P) : term215 _93804 _93824 f s P.
Proof. exact (proj2 (@lem3693229 _93804 _93824 t f s P h1)). Qed.
Lemma lem3693231 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term233 _93804 _93824 t f s P) : term32 _93804 _93824 s P f t.
Proof. exact (proj1 (@lem3693229 _93804 _93824 t f s P h1)). Qed.
Lemma lem3693232 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term233 _93804 _93824 t f s P) : term73 _93804 _93824 s P f t.
Proof. exact (proj2 (@lem3693231 _93804 _93824 t f s P h1)). Qed.
Lemma lem3693300 {_93804 _93824 : Type'} (s : _93804 -> Prop) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term237 _93804 _93824 s f t) = (term237 _93804 _93824 s f t).
Proof. exact (eq_refl (term237 _93804 _93824 s f t)). Qed.
Lemma lem3693301 {_93804 _93824 : Type'} (s : _93804 -> Prop) (f : _93804 -> _93824) : (term239 _93804 _93824 s f) = (term239 _93804 _93824 s f).
Proof. exact (fun_ext (fun t : _93804 -> Prop => @lem3693300 _93804 _93824 s f t)). Qed.
Lemma lem3693302 {_93804 : Type'} : (@all (_93804 -> Prop)) = (@all (_93804 -> Prop)).
Proof. exact (eq_refl (@all (_93804 -> Prop))). Qed.
Lemma lem3693303 {_93804 _93824 : Type'} (s : _93804 -> Prop) (f : _93804 -> _93824) : (term240 _93804 _93824 s f) = (term240 _93804 _93824 s f).
Proof. exact (MK_COMB (@lem3693302 _93804) (@lem3693301 _93804 _93824 s f)). Qed.
Lemma lem3693304 {_93804 _93824 : Type'} (f : _93804 -> _93824) : (term241 _93804 _93824 f) = (term241 _93804 _93824 f).
Proof. exact (fun_ext (fun s : _93804 -> Prop => @lem3693303 _93804 _93824 s f)). Qed.
Lemma lem3693305 {_93804 : Type'} : (@all (_93804 -> Prop)) = (@all (_93804 -> Prop)).
Proof. exact (eq_refl (@all (_93804 -> Prop))). Qed.
Lemma lem3693306 {_93804 _93824 : Type'} (f : _93804 -> _93824) : (term242 _93804 _93824 f) = (term242 _93804 _93824 f).
Proof. exact (MK_COMB (@lem3693305 _93804) (@lem3693304 _93804 _93824 f)). Qed.
Lemma lem3693307 {_93804 _93824 : Type'} : (term243 _93804 _93824) = (term243 _93804 _93824).
Proof. exact (fun_ext (fun f : _93804 -> _93824 => @lem3693306 _93804 _93824 f)). Qed.
Lemma lem3693308 {_93804 _93824 : Type'} : (@all (_93804 -> _93824)) = (@all (_93804 -> _93824)).
Proof. exact (eq_refl (@all (_93804 -> _93824))). Qed.
Lemma lem3693310 {_93804 _93824 : Type'} : (term244 _93804 _93824) = (term244 _93804 _93824).
Proof. exact (MK_COMB (@lem3693308 _93804 _93824) (@lem3693307 _93804 _93824)). Qed.
Lemma lem3693311 {_93804 _93824 : Type'} (h1 : term128 _93804 _93824) : term244 _93804 _93824.
Proof. exact (EQ_MP (@lem3693310 _93804 _93824) (@lem3692899 _93804 _93824 h1)). Qed.
Lemma lem3693414 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) : (term245 _93804 _93824 f s) = (term245 _93804 _93824 f s).
Proof. exact (eq_refl (term245 _93804 _93824 f s)). Qed.
Lemma lem3693415 {_93804 _93824 : Type'} (f : _93804 -> _93824) : (term247 _93804 _93824 f) = (term247 _93804 _93824 f).
Proof. exact (fun_ext (fun s : _93804 -> Prop => @lem3693414 _93804 _93824 f s)). Qed.
Lemma lem3693416 {_93804 : Type'} : (@all (_93804 -> Prop)) = (@all (_93804 -> Prop)).
Proof. exact (eq_refl (@all (_93804 -> Prop))). Qed.
Lemma lem3693417 {_93804 _93824 : Type'} (f : _93804 -> _93824) : (term248 _93804 _93824 f) = (term248 _93804 _93824 f).
Proof. exact (MK_COMB (@lem3693416 _93804) (@lem3693415 _93804 _93824 f)). Qed.
Lemma lem3693418 {_93804 _93824 : Type'} : (term249 _93804 _93824) = (term249 _93804 _93824).
Proof. exact (fun_ext (fun f : _93804 -> _93824 => @lem3693417 _93804 _93824 f)). Qed.
Lemma lem3693419 {_93804 _93824 : Type'} : (@all (_93804 -> _93824)) = (@all (_93804 -> _93824)).
Proof. exact (eq_refl (@all (_93804 -> _93824))). Qed.
Lemma lem3693421 {_93804 _93824 : Type'} : (term250 _93804 _93824) = (term250 _93804 _93824).
Proof. exact (MK_COMB (@lem3693419 _93804 _93824) (@lem3693418 _93804 _93824)). Qed.
Lemma lem3693422 {_93804 _93824 : Type'} (h1 : term125 _93804 _93824) : term250 _93804 _93824.
Proof. exact (EQ_MP (@lem3693421 _93804 _93824) (@lem3693086 _93804 _93824 h1)). Qed.
Lemma lem3693500 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (t : _93824 -> Prop) : (term206 _93804 _93824 f s P t) = (term206 _93804 _93824 f s P t).
Proof. exact (eq_refl (term206 _93804 _93824 f s P t)). Qed.
Lemma lem3693501 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term214 _93804 _93824 f s P) = (term214 _93804 _93824 f s P).
Proof. exact (fun_ext (fun t : _93824 -> Prop => @lem3693500 _93804 _93824 f s P t)). Qed.
Lemma lem3693502 {_93824 : Type'} : (@all (_93824 -> Prop)) = (@all (_93824 -> Prop)).
Proof. exact (eq_refl (@all (_93824 -> Prop))). Qed.
Lemma lem3693504 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term215 _93804 _93824 f s P) = (term215 _93804 _93824 f s P).
Proof. exact (MK_COMB (@lem3693502 _93824) (@lem3693501 _93804 _93824 f s P)). Qed.
Lemma lem3693505 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term233 _93804 _93824 t f s P) : term215 _93804 _93824 f s P.
Proof. exact (EQ_MP (@lem3693504 _93804 _93824 f s P) (@lem3693230 _93804 _93824 t f s P h1)). Qed.
Lemma lem3693545 {_93804 _93824 : Type'} (_42458 : _93804 -> _93824) (h1 : term128 _93804 _93824) : term251 _93804 _93824 _42458.
Proof. exact (@lem3693311 _93804 _93824 h1 _42458). Qed.
Lemma lem3693546 {_93804 _93824 : Type'} (_42458 : _93804 -> _93824) : (term251 _93804 _93824 _42458) = (term242 _93804 _93824 _42458).
Proof. exact (eq_refl (term251 _93804 _93824 _42458)). Qed.
Lemma lem3693547 {_93804 _93824 : Type'} (_42458 : _93804 -> _93824) (h1 : term128 _93804 _93824) : term242 _93804 _93824 _42458.
Proof. exact (EQ_MP (@lem3693546 _93804 _93824 _42458) (@lem3693545 _93804 _93824 _42458 h1)). Qed.
Lemma lem3693548 {_93804 _93824 : Type'} (_42458 : _93804 -> _93824) (_42459 : _93804 -> Prop) (h1 : term128 _93804 _93824) : term252 _93804 _93824 _42458 _42459.
Proof. exact (@lem3693547 _93804 _93824 _42458 h1 _42459). Qed.
Lemma lem3693549 {_93804 _93824 : Type'} (_42459 : _93804 -> Prop) (_42458 : _93804 -> _93824) : (term252 _93804 _93824 _42458 _42459) = (term240 _93804 _93824 _42459 _42458).
Proof. exact (eq_refl (term252 _93804 _93824 _42458 _42459)). Qed.
Lemma lem3693550 {_93804 _93824 : Type'} (_42459 : _93804 -> Prop) (_42458 : _93804 -> _93824) (h1 : term128 _93804 _93824) : term240 _93804 _93824 _42459 _42458.
Proof. exact (EQ_MP (@lem3693549 _93804 _93824 _42459 _42458) (@lem3693548 _93804 _93824 _42458 _42459 h1)). Qed.
Lemma lem3693551 {_93804 _93824 : Type'} (_42459 : _93804 -> Prop) (_42458 : _93804 -> _93824) (_42460 : _93804 -> Prop) (h1 : term128 _93804 _93824) : term253 _93804 _93824 _42459 _42458 _42460.
Proof. exact (@lem3693550 _93804 _93824 _42459 _42458 h1 _42460). Qed.
Lemma lem3693552 {_93804 _93824 : Type'} (_42459 : _93804 -> Prop) (_42458 : _93804 -> _93824) (_42460 : _93804 -> Prop) : (term253 _93804 _93824 _42459 _42458 _42460) = (term237 _93804 _93824 _42459 _42458 _42460).
Proof. exact (eq_refl (term253 _93804 _93824 _42459 _42458 _42460)). Qed.
Lemma lem3693599 {_93804 _93824 : Type'} (_42476 : _93804 -> _93824) (h1 : term125 _93804 _93824) : term254 _93804 _93824 _42476.
Proof. exact (@lem3693422 _93804 _93824 h1 _42476). Qed.
Lemma lem3693600 {_93804 _93824 : Type'} (_42476 : _93804 -> _93824) : (term254 _93804 _93824 _42476) = (term248 _93804 _93824 _42476).
Proof. exact (eq_refl (term254 _93804 _93824 _42476)). Qed.
Lemma lem3693601 {_93804 _93824 : Type'} (_42476 : _93804 -> _93824) (h1 : term125 _93804 _93824) : term248 _93804 _93824 _42476.
Proof. exact (EQ_MP (@lem3693600 _93804 _93824 _42476) (@lem3693599 _93804 _93824 _42476 h1)). Qed.
Lemma lem3693602 {_93804 _93824 : Type'} (_42476 : _93804 -> _93824) (_42477 : _93804 -> Prop) (h1 : term125 _93804 _93824) : term255 _93804 _93824 _42476 _42477.
Proof. exact (@lem3693601 _93804 _93824 _42476 h1 _42477). Qed.
Lemma lem3693603 {_93804 _93824 : Type'} (_42476 : _93804 -> _93824) (_42477 : _93804 -> Prop) : (term255 _93804 _93824 _42476 _42477) = (term245 _93804 _93824 _42476 _42477).
Proof. exact (eq_refl (term255 _93804 _93824 _42476 _42477)). Qed.
Lemma lem3693629 {_93804 _93824 : Type'} (_42486 : _93824 -> Prop) (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term233 _93804 _93824 t f s P) : term256 _93804 _93824 f s P _42486.
Proof. exact (@lem3693505 _93804 _93824 t f s P h1 _42486). Qed.
Lemma lem3693630 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (_42486 : _93824 -> Prop) : (term256 _93804 _93824 f s P _42486) = (term206 _93804 _93824 f s P _42486).
Proof. exact (eq_refl (term256 _93804 _93824 f s P _42486)). Qed.
Lemma lem3693655 {_93804 _93824 : Type'} (_42459 : _93804 -> Prop) (_42458 : _93804 -> _93824) (_42460 : _93804 -> Prop) (h1 : term128 _93804 _93824) : term237 _93804 _93824 _42459 _42458 _42460.
Proof. exact (EQ_MP (@lem3693552 _93804 _93824 _42459 _42458 _42460) (@lem3693551 _93804 _93824 _42459 _42458 _42460 h1)). Qed.
Lemma lem3693691 {_93804 _93824 : Type'} (_42476 : _93804 -> _93824) (_42477 : _93804 -> Prop) (h1 : term125 _93804 _93824) : term245 _93804 _93824 _42476 _42477.
Proof. exact (EQ_MP (@lem3693603 _93804 _93824 _42476 _42477) (@lem3693602 _93804 _93824 _42476 _42477 h1)). Qed.
Lemma lem3693725 {_93804 _93824 : Type'} (_42486 : _93824 -> Prop) (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term233 _93804 _93824 t f s P) : term206 _93804 _93824 f s P _42486.
Proof. exact (EQ_MP (@lem3693630 _93804 _93824 f s P _42486) (@lem3693629 _93804 _93824 _42486 t f s P h1)). Qed.
Lemma lem3693733 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term233 _93804 _93824 t f s P) : @FINITE _93804 t.
Proof. exact (proj1 (@lem3693231 _93804 _93824 t f s P h1)). Qed.
Lemma lem3693734 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term233 _93804 _93824 t f s P) : term108 _93804 t.
Proof. exact (fun h0 : term109 _93804 t => @lem3693733 _93804 _93824 t f s P h1). Qed.
Lemma lem3693736 (p : Prop) : (term110 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3693737 {_93804 : Type'} (t : _93804 -> Prop) : (term108 _93804 t) = (@FINITE _93804 t).
Proof. exact (@lem3693736 (@FINITE _93804 t)). Qed.
Lemma lem3693738 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term233 _93804 _93824 t f s P) : @FINITE _93804 t.
Proof. exact (EQ_MP (@lem3693737 _93804 t) (@lem3693734 _93804 _93824 t f s P h1)). Qed.
Lemma lem3693744 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3693745 {_93804 _93824 : Type'} (_42476 : _93804 -> _93824) (_42477 : _93804 -> Prop) : (term245 _93804 _93824 _42476 _42477) = (term257 _93804 _93824 _42476 _42477).
Proof. exact (@lem3693744 (term246 _93804 _93824 _42476 _42477) (term109 _93804 _42477)). Qed.
Lemma lem3693751 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3693752 {_93804 _93824 : Type'} (_42476 : _93804 -> _93824) (_42477 : _93804 -> Prop) : (term258 _93804 _93824 _42476 _42477) = (term259 _93804 _93824 _42476 _42477).
Proof. exact (MK_COMB (@lem3693751) (@lem3693745 _93804 _93824 _42476 _42477)). Qed.
Lemma lem3693758 {_93804 _93824 : Type'} (_42476 : _93804 -> _93824) (_42477 : _93804 -> Prop) : (term257 _93804 _93824 _42476 _42477) = (term257 _93804 _93824 _42476 _42477).
Proof. exact (eq_refl (term257 _93804 _93824 _42476 _42477)). Qed.
Lemma lem3693759 {_93804 _93824 : Type'} (_42476 : _93804 -> _93824) (_42477 : _93804 -> Prop) : ((term245 _93804 _93824 _42476 _42477) = (term257 _93804 _93824 _42476 _42477)) = ((term257 _93804 _93824 _42476 _42477) = (term257 _93804 _93824 _42476 _42477)).
Proof. exact (MK_COMB (@lem3693752 _93804 _93824 _42476 _42477) (@lem3693758 _93804 _93824 _42476 _42477)). Qed.
Lemma lem3693761 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3693762 (x : Prop) : (x = x) = True.
Proof. exact (@lem3693761 Prop x). Qed.
Lemma lem3693763 {_93804 _93824 : Type'} (_42476 : _93804 -> _93824) (_42477 : _93804 -> Prop) : ((term257 _93804 _93824 _42476 _42477) = (term257 _93804 _93824 _42476 _42477)) = True.
Proof. exact (@lem3693762 (term257 _93804 _93824 _42476 _42477)). Qed.
Lemma lem3693764 {_93804 _93824 : Type'} (_42476 : _93804 -> _93824) (_42477 : _93804 -> Prop) : ((term245 _93804 _93824 _42476 _42477) = (term257 _93804 _93824 _42476 _42477)) = True.
Proof. exact (TRANS (@lem3693759 _93804 _93824 _42476 _42477) (@lem3693763 _93804 _93824 _42476 _42477)). Qed.
Lemma lem3693765 {_93804 _93824 : Type'} (_42476 : _93804 -> _93824) (_42477 : _93804 -> Prop) : True = ((term245 _93804 _93824 _42476 _42477) = (term257 _93804 _93824 _42476 _42477)).
Proof. exact (SYM (@lem3693764 _93804 _93824 _42476 _42477)). Qed.
Lemma lem3693766 {_93804 _93824 : Type'} (_42476 : _93804 -> _93824) (_42477 : _93804 -> Prop) : (term245 _93804 _93824 _42476 _42477) = (term257 _93804 _93824 _42476 _42477).
Proof. exact (EQ_MP (@lem3693765 _93804 _93824 _42476 _42477) (@lem0)). Qed.
Lemma lem3693767 {_93804 _93824 : Type'} (_42476 : _93804 -> _93824) (_42477 : _93804 -> Prop) (h1 : term125 _93804 _93824) : term257 _93804 _93824 _42476 _42477.
Proof. exact (EQ_MP (@lem3693766 _93804 _93824 _42476 _42477) (@lem3693691 _93804 _93824 _42476 _42477 h1)). Qed.
Lemma lem3693769 (b : Prop) (a : Prop) : (a \/ b) = (term260 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3693770 {_93804 _93824 : Type'} (_42476 : _93804 -> _93824) (_42477 : _93804 -> Prop) : (term257 _93804 _93824 _42476 _42477) = (term261 _93804 _93824 _42476 _42477).
Proof. exact (@lem3693769 (term109 _93804 _42477) (term246 _93804 _93824 _42476 _42477)). Qed.
Lemma lem3693772 (a : Prop) : (term19 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3693773 {_93804 : Type'} (_42477 : _93804 -> Prop) : (term262 _93804 _42477) = (@FINITE _93804 _42477).
Proof. exact (@lem3693772 (@FINITE _93804 _42477)). Qed.
Lemma lem3693774 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3693775 {_93804 : Type'} (_42477 : _93804 -> Prop) : (term263 _93804 _42477) = (term264 _93804 _42477).
Proof. exact (MK_COMB (@lem3693774) (@lem3693773 _93804 _42477)). Qed.
Lemma lem3693776 {_93804 _93824 : Type'} (_42476 : _93804 -> _93824) (_42477 : _93804 -> Prop) : (term246 _93804 _93824 _42476 _42477) = (term246 _93804 _93824 _42476 _42477).
Proof. exact (eq_refl (term246 _93804 _93824 _42476 _42477)). Qed.
Lemma lem3693777 {_93804 _93824 : Type'} (_42476 : _93804 -> _93824) (_42477 : _93804 -> Prop) : (term261 _93804 _93824 _42476 _42477) = (term183 _93804 _93824 _42476 _42477).
Proof. exact (MK_COMB (@lem3693775 _93804 _42477) (@lem3693776 _93804 _93824 _42476 _42477)). Qed.
Lemma lem3693778 {_93804 _93824 : Type'} (_42476 : _93804 -> _93824) (_42477 : _93804 -> Prop) : (term257 _93804 _93824 _42476 _42477) = (term183 _93804 _93824 _42476 _42477).
Proof. exact (TRANS (@lem3693770 _93804 _93824 _42476 _42477) (@lem3693777 _93804 _93824 _42476 _42477)). Qed.
Lemma lem3693781 {_93804 _93824 : Type'} (_42476 : _93804 -> _93824) (_42477 : _93804 -> Prop) (h1 : term125 _93804 _93824) : term183 _93804 _93824 _42476 _42477.
Proof. exact (EQ_MP (@lem3693778 _93804 _93824 _42476 _42477) (@lem3693767 _93804 _93824 _42476 _42477 h1)). Qed.
Lemma lem3693782 {_93804 _93824 : Type'} (_42476 : _93804 -> _93824) (_42477 : _93804 -> Prop) (h1 : term125 _93804 _93824) : term183 _93804 _93824 _42476 _42477.
Proof. exact (@lem3693781 _93804 _93824 _42476 _42477 h1). Qed.
Lemma lem3693783 {_93804 _93824 : Type'} (_42476 : _93804 -> _93824) (t : _93804 -> Prop) (h1 : term125 _93804 _93824) : term183 _93804 _93824 _42476 t.
Proof. exact (@lem3693782 _93804 _93824 _42476 t h1). Qed.
Lemma lem3693786 {_93804 _93824 : Type'} (_42476 : _93804 -> _93824) (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term125 _93804 _93824) (h2 : term233 _93804 _93824 t f s P) : term246 _93804 _93824 _42476 t.
Proof. exact (@lem3693783 _93804 _93824 _42476 t h1 (@lem3693738 _93804 _93824 t f s P h2)). Qed.
Lemma lem3693787 {_93804 _93824 : Type'} (_42476 : _93804 -> _93824) (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term125 _93804 _93824) (h2 : term233 _93804 _93824 t f s P) : term246 _93804 _93824 _42476 t.
Proof. exact (@lem3693786 _93804 _93824 _42476 t f s P h1 h2). Qed.
Lemma lem3693788 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term125 _93804 _93824) (h2 : term233 _93804 _93824 t f s P) : term246 _93804 _93824 f t.
Proof. exact (@lem3693787 _93804 _93824 f t f s P h1 h2). Qed.
Lemma lem3693789 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term125 _93804 _93824) (h2 : term233 _93804 _93824 t f s P) : term265 _93804 _93824 f t.
Proof. exact (fun h0 : term266 _93804 _93824 f t => @lem3693788 _93804 _93824 t f s P h1 h2). Qed.
Lemma lem3693791 (p : Prop) : (term110 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3693792 {_93804 _93824 : Type'} (f : _93804 -> _93824) (t : _93804 -> Prop) : (term265 _93804 _93824 f t) = (term246 _93804 _93824 f t).
Proof. exact (@lem3693791 (term246 _93804 _93824 f t)). Qed.
Lemma lem3693793 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term125 _93804 _93824) (h2 : term233 _93804 _93824 t f s P) : term246 _93804 _93824 f t.
Proof. exact (EQ_MP (@lem3693792 _93804 _93824 f t) (@lem3693789 _93804 _93824 t f s P h1 h2)). Qed.
Lemma lem3693795 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term233 _93804 _93824 t f s P) : @SUBSET _93804 t s.
Proof. exact (proj1 (@lem3693232 _93804 _93824 t f s P h1)). Qed.
Lemma lem3693796 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term233 _93804 _93824 t f s P) : term111 _93804 t s.
Proof. exact (fun h0 : term112 _93804 t s => @lem3693795 _93804 _93824 t f s P h1). Qed.
Lemma lem3693798 (p : Prop) : (term110 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3693799 {_93804 : Type'} (t : _93804 -> Prop) (s : _93804 -> Prop) : (term111 _93804 t s) = (@SUBSET _93804 t s).
Proof. exact (@lem3693798 (@SUBSET _93804 t s)). Qed.
Lemma lem3693800 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term233 _93804 _93824 t f s P) : @SUBSET _93804 t s.
Proof. exact (EQ_MP (@lem3693799 _93804 t s) (@lem3693796 _93804 _93824 t f s P h1)). Qed.
Lemma lem3693806 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3693807 {_93804 _93824 : Type'} (_42458 : _93804 -> _93824) (_42459 : _93804 -> Prop) (_42460 : _93804 -> Prop) : (term237 _93804 _93824 _42459 _42458 _42460) = (term267 _93804 _93824 _42458 _42459 _42460).
Proof. exact (@lem3693806 (term238 _93804 _93824 _42459 _42458 _42460) (term112 _93804 _42459 _42460)). Qed.
Lemma lem3693813 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3693814 {_93804 _93824 : Type'} (_42458 : _93804 -> _93824) (_42459 : _93804 -> Prop) (_42460 : _93804 -> Prop) : (term268 _93804 _93824 _42459 _42458 _42460) = (term269 _93804 _93824 _42458 _42459 _42460).
Proof. exact (MK_COMB (@lem3693813) (@lem3693807 _93804 _93824 _42458 _42459 _42460)). Qed.
Lemma lem3693820 {_93804 _93824 : Type'} (_42458 : _93804 -> _93824) (_42459 : _93804 -> Prop) (_42460 : _93804 -> Prop) : (term267 _93804 _93824 _42458 _42459 _42460) = (term267 _93804 _93824 _42458 _42459 _42460).
Proof. exact (eq_refl (term267 _93804 _93824 _42458 _42459 _42460)). Qed.
Lemma lem3693821 {_93804 _93824 : Type'} (_42458 : _93804 -> _93824) (_42459 : _93804 -> Prop) (_42460 : _93804 -> Prop) : ((term237 _93804 _93824 _42459 _42458 _42460) = (term267 _93804 _93824 _42458 _42459 _42460)) = ((term267 _93804 _93824 _42458 _42459 _42460) = (term267 _93804 _93824 _42458 _42459 _42460)).
Proof. exact (MK_COMB (@lem3693814 _93804 _93824 _42458 _42459 _42460) (@lem3693820 _93804 _93824 _42458 _42459 _42460)). Qed.
Lemma lem3693823 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3693824 (x : Prop) : (x = x) = True.
Proof. exact (@lem3693823 Prop x). Qed.
Lemma lem3693825 {_93804 _93824 : Type'} (_42458 : _93804 -> _93824) (_42459 : _93804 -> Prop) (_42460 : _93804 -> Prop) : ((term267 _93804 _93824 _42458 _42459 _42460) = (term267 _93804 _93824 _42458 _42459 _42460)) = True.
Proof. exact (@lem3693824 (term267 _93804 _93824 _42458 _42459 _42460)). Qed.
Lemma lem3693826 {_93804 _93824 : Type'} (_42458 : _93804 -> _93824) (_42459 : _93804 -> Prop) (_42460 : _93804 -> Prop) : ((term237 _93804 _93824 _42459 _42458 _42460) = (term267 _93804 _93824 _42458 _42459 _42460)) = True.
Proof. exact (TRANS (@lem3693821 _93804 _93824 _42458 _42459 _42460) (@lem3693825 _93804 _93824 _42458 _42459 _42460)). Qed.
Lemma lem3693827 {_93804 _93824 : Type'} (_42458 : _93804 -> _93824) (_42459 : _93804 -> Prop) (_42460 : _93804 -> Prop) : True = ((term237 _93804 _93824 _42459 _42458 _42460) = (term267 _93804 _93824 _42458 _42459 _42460)).
Proof. exact (SYM (@lem3693826 _93804 _93824 _42458 _42459 _42460)). Qed.
Lemma lem3693828 {_93804 _93824 : Type'} (_42458 : _93804 -> _93824) (_42459 : _93804 -> Prop) (_42460 : _93804 -> Prop) : (term237 _93804 _93824 _42459 _42458 _42460) = (term267 _93804 _93824 _42458 _42459 _42460).
Proof. exact (EQ_MP (@lem3693827 _93804 _93824 _42458 _42459 _42460) (@lem0)). Qed.
Lemma lem3693829 {_93804 _93824 : Type'} (_42458 : _93804 -> _93824) (_42459 : _93804 -> Prop) (_42460 : _93804 -> Prop) (h1 : term128 _93804 _93824) : term267 _93804 _93824 _42458 _42459 _42460.
Proof. exact (EQ_MP (@lem3693828 _93804 _93824 _42458 _42459 _42460) (@lem3693655 _93804 _93824 _42459 _42458 _42460 h1)). Qed.
Lemma lem3693831 (b : Prop) (a : Prop) : (a \/ b) = (term260 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3693832 {_93804 _93824 : Type'} (_42459 : _93804 -> Prop) (_42458 : _93804 -> _93824) (_42460 : _93804 -> Prop) : (term267 _93804 _93824 _42458 _42459 _42460) = (term270 _93804 _93824 _42459 _42458 _42460).
Proof. exact (@lem3693831 (term112 _93804 _42459 _42460) (term238 _93804 _93824 _42459 _42458 _42460)). Qed.
Lemma lem3693834 (a : Prop) : (term19 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3693835 {_93804 : Type'} (_42459 : _93804 -> Prop) (_42460 : _93804 -> Prop) : (term271 _93804 _42459 _42460) = (@SUBSET _93804 _42459 _42460).
Proof. exact (@lem3693834 (@SUBSET _93804 _42459 _42460)). Qed.
Lemma lem3693836 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3693837 {_93804 : Type'} (_42459 : _93804 -> Prop) (_42460 : _93804 -> Prop) : (term272 _93804 _42459 _42460) = (term273 _93804 _42459 _42460).
Proof. exact (MK_COMB (@lem3693836) (@lem3693835 _93804 _42459 _42460)). Qed.
Lemma lem3693838 {_93804 _93824 : Type'} (_42459 : _93804 -> Prop) (_42458 : _93804 -> _93824) (_42460 : _93804 -> Prop) : (term238 _93804 _93824 _42459 _42458 _42460) = (term238 _93804 _93824 _42459 _42458 _42460).
Proof. exact (eq_refl (term238 _93804 _93824 _42459 _42458 _42460)). Qed.
Lemma lem3693839 {_93804 _93824 : Type'} (_42459 : _93804 -> Prop) (_42458 : _93804 -> _93824) (_42460 : _93804 -> Prop) : (term270 _93804 _93824 _42459 _42458 _42460) = (term193 _93804 _93824 _42459 _42458 _42460).
Proof. exact (MK_COMB (@lem3693837 _93804 _42459 _42460) (@lem3693838 _93804 _93824 _42459 _42458 _42460)). Qed.
Lemma lem3693840 {_93804 _93824 : Type'} (_42459 : _93804 -> Prop) (_42458 : _93804 -> _93824) (_42460 : _93804 -> Prop) : (term267 _93804 _93824 _42458 _42459 _42460) = (term193 _93804 _93824 _42459 _42458 _42460).
Proof. exact (TRANS (@lem3693832 _93804 _93824 _42459 _42458 _42460) (@lem3693839 _93804 _93824 _42459 _42458 _42460)). Qed.
Lemma lem3693843 {_93804 _93824 : Type'} (_42459 : _93804 -> Prop) (_42458 : _93804 -> _93824) (_42460 : _93804 -> Prop) (h1 : term128 _93804 _93824) : term193 _93804 _93824 _42459 _42458 _42460.
Proof. exact (EQ_MP (@lem3693840 _93804 _93824 _42459 _42458 _42460) (@lem3693829 _93804 _93824 _42458 _42459 _42460 h1)). Qed.
Lemma lem3693844 {_93804 _93824 : Type'} (_42459 : _93804 -> Prop) (_42458 : _93804 -> _93824) (_42460 : _93804 -> Prop) (h1 : term128 _93804 _93824) : term193 _93804 _93824 _42459 _42458 _42460.
Proof. exact (@lem3693843 _93804 _93824 _42459 _42458 _42460 h1). Qed.
Lemma lem3693845 {_93804 _93824 : Type'} (t : _93804 -> Prop) (_42458 : _93804 -> _93824) (s : _93804 -> Prop) (h1 : term128 _93804 _93824) : term193 _93804 _93824 t _42458 s.
Proof. exact (@lem3693844 _93804 _93824 t _42458 s h1). Qed.
Lemma lem3693848 {_93804 _93824 : Type'} (_42458 : _93804 -> _93824) (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term128 _93804 _93824) (h2 : term233 _93804 _93824 t f s P) : term238 _93804 _93824 t _42458 s.
Proof. exact (@lem3693845 _93804 _93824 t _42458 s h1 (@lem3693800 _93804 _93824 t f s P h2)). Qed.
Lemma lem3693849 {_93804 _93824 : Type'} (_42458 : _93804 -> _93824) (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term128 _93804 _93824) (h2 : term233 _93804 _93824 t f s P) : term238 _93804 _93824 t _42458 s.
Proof. exact (@lem3693848 _93804 _93824 _42458 t f s P h1 h2). Qed.
Lemma lem3693850 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term128 _93804 _93824) (h2 : term233 _93804 _93824 t f s P) : term238 _93804 _93824 t f s.
Proof. exact (@lem3693849 _93804 _93824 f t f s P h1 h2). Qed.
Lemma lem3693851 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term128 _93804 _93824) (h2 : term233 _93804 _93824 t f s P) : term274 _93804 _93824 t f s.
Proof. exact (fun h0 : term275 _93804 _93824 t f s => @lem3693850 _93804 _93824 t f s P h1 h2). Qed.
Lemma lem3693853 (p : Prop) : (term110 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3693854 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) : (term274 _93804 _93824 t f s) = (term238 _93804 _93824 t f s).
Proof. exact (@lem3693853 (term238 _93804 _93824 t f s)). Qed.
Lemma lem3693855 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term128 _93804 _93824) (h2 : term233 _93804 _93824 t f s P) : term238 _93804 _93824 t f s.
Proof. exact (EQ_MP (@lem3693854 _93804 _93824 t f s) (@lem3693851 _93804 _93824 t f s P h1 h2)). Qed.
Lemma lem3693857 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term233 _93804 _93824 t f s P) : term34 _93804 _93824 P f t.
Proof. exact (proj2 (@lem3693232 _93804 _93824 t f s P h1)). Qed.
Lemma lem3693858 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term233 _93804 _93824 t f s P) : term113 _93804 _93824 P f t.
Proof. exact (fun h0 : term114 _93804 _93824 P f t => @lem3693857 _93804 _93824 t f s P h1). Qed.
Lemma lem3693860 (p : Prop) : (term110 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3693861 {_93804 _93824 : Type'} (P : type686 _93824) (f : _93804 -> _93824) (t : _93804 -> Prop) : (term113 _93804 _93824 P f t) = (term34 _93804 _93824 P f t).
Proof. exact (@lem3693860 (term34 _93804 _93824 P f t)). Qed.
Lemma lem3693862 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term233 _93804 _93824 t f s P) : term34 _93804 _93824 P f t.
Proof. exact (EQ_MP (@lem3693861 _93804 _93824 P f t) (@lem3693858 _93804 _93824 t f s P h1)). Qed.
Lemma lem3693864 (a : Prop) (b : Prop) : (term115 a b) = (term116 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3693865 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (_42486 : _93824 -> Prop) : (term203 _93804 _93824 f s P _42486) = (term202 _93804 _93824 f s P _42486).
Proof. exact (@lem3693864 (term204 _93804 _93824 _42486 f s) (P _42486)). Qed.
Lemma lem3693866 {_93824 : Type'} (_42486 : _93824 -> Prop) : (term69 _93824 _42486) = (term69 _93824 _42486).
Proof. exact (eq_refl (term69 _93824 _42486)). Qed.
Lemma lem3693867 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (_42486 : _93824 -> Prop) : (term206 _93804 _93824 f s P _42486) = (term205 _93804 _93824 f s P _42486).
Proof. exact (MK_COMB (@lem3693866 _93824 _42486) (@lem3693865 _93804 _93824 f s P _42486)). Qed.
Lemma lem3693869 (a : Prop) (b : Prop) : (term115 a b) = (term116 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3693870 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (_42486 : _93824 -> Prop) : (term205 _93804 _93824 f s P _42486) = (term207 _93804 _93824 f s P _42486).
Proof. exact (@lem3693869 (@FINITE _93824 _42486) (term208 _93804 _93824 f s P _42486)). Qed.
Lemma lem3693871 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (_42486 : _93824 -> Prop) : (term206 _93804 _93824 f s P _42486) = (term207 _93804 _93824 f s P _42486).
Proof. exact (TRANS (@lem3693867 _93804 _93824 f s P _42486) (@lem3693870 _93804 _93824 f s P _42486)). Qed.
Lemma lem3693873 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3693874 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (_42486 : _93824 -> Prop) : (term207 _93804 _93824 f s P _42486) = (term276 _93804 _93824 f s P _42486).
Proof. exact (@lem3693873 (term199 _93804 _93824 f s P _42486)). Qed.
Lemma lem3693875 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (_42486 : _93824 -> Prop) : (term206 _93804 _93824 f s P _42486) = (term276 _93804 _93824 f s P _42486).
Proof. exact (TRANS (@lem3693871 _93804 _93824 f s P _42486) (@lem3693874 _93804 _93824 f s P _42486)). Qed.
Lemma lem3693877 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term128 _93804 _93824) (h2 : term233 _93804 _93824 t f s P) : term277 _93804 _93824 s P f t.
Proof. exact (conj (@lem3693855 _93804 _93824 t f s P h1 h2) (@lem3693862 _93804 _93824 t f s P h2)). Qed.
Lemma lem3693878 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term128 _93804 _93824) (h2 : term125 _93804 _93824) (h3 : term233 _93804 _93824 t f s P) : term278 _93804 _93824 s P f t.
Proof. exact (conj (@lem3693793 _93804 _93824 t f s P h2 h3) (@lem3693877 _93804 _93824 t f s P h1 h3)). Qed.
Lemma lem3693880 {_93804 _93824 : Type'} (_42486 : _93824 -> Prop) (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term233 _93804 _93824 t f s P) : term276 _93804 _93824 f s P _42486.
Proof. exact (EQ_MP (@lem3693875 _93804 _93824 f s P _42486) (@lem3693725 _93804 _93824 _42486 t f s P h1)). Qed.
Lemma lem3693881 {_93804 _93824 : Type'} (_42486 : _93824 -> Prop) (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term233 _93804 _93824 t f s P) : term276 _93804 _93824 f s P _42486.
Proof. exact (@lem3693880 _93804 _93824 _42486 t f s P h1). Qed.
Lemma lem3693882 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term233 _93804 _93824 t f s P) : term279 _93804 _93824 s P f t.
Proof. exact (@lem3693881 _93804 _93824 (@IMAGE _93804 _93824 f t) t f s P h1). Qed.
Lemma lem3693885 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term128 _93804 _93824) (h2 : term125 _93804 _93824) (h3 : term233 _93804 _93824 t f s P) : False.
Proof. exact (@lem3693882 _93804 _93824 t f s P h3 (@lem3693878 _93804 _93824 t f s P h1 h2 h3)). Qed.
Lemma lem3693886 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term128 _93804 _93824) (h2 : term125 _93804 _93824) (h3 : term233 _93804 _93824 t f s P) : term118.
Proof. exact (fun h0 : ~ False => @lem3693885 _93804 _93824 t f s P h1 h2 h3). Qed.
Lemma lem3693888 (p : Prop) : (term110 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3693889 : term118 = False.
Proof. exact (@lem3693888 False). Qed.
Lemma lem3693890 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term128 _93804 _93824) (h2 : term125 _93804 _93824) (h3 : term233 _93804 _93824 t f s P) : False.
Proof. exact (EQ_MP (@lem3693889) (@lem3693886 _93804 _93824 t f s P h1 h2 h3)). Qed.
Lemma lem3693891 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term128 _93804 _93824) (h2 : term125 _93804 _93824) (h3 : term233 _93804 _93824 t f s P) : (term233 _93804 _93824 t f s P) = False.
Proof. exact (prop_ext (fun h4 : term233 _93804 _93824 t f s P => @lem3693890 _93804 _93824 t f s P h1 h2 h3) (fun h4 : False => @lem3693229 _93804 _93824 t f s P h3)). Qed.
Lemma lem3693892 {_93804 _93824 : Type'} (t : _93804 -> Prop) (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term128 _93804 _93824) (h2 : term125 _93804 _93824) (h3 : term233 _93804 _93824 t f s P) : False.
Proof. exact (EQ_MP (@lem3693891 _93804 _93824 t f s P h1 h2 h3) (@lem3693229 _93804 _93824 t f s P h3)). Qed.
Lemma lem3693893 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term128 _93804 _93824) (h2 : term125 _93804 _93824) (h3 : term124 _93804 _93824 f s P) : False.
Proof. exact (ex_elim (@lem3691723 _93804 _93824 f s P h3) (fun t : _93804 -> Prop => fun h0 : term235 _93804 _93824 f s P t => @lem3693892 _93804 _93824 t f s P h1 h2 h0)). Qed.
Lemma lem3693894 {_93804 _93824 A : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term128 _93804 _93824) (h2 : term125 _93804 _93824) (h3 : term124 _93804 _93824 f s P) : term133 _93824 A.
Proof. exact (fun h0 : term126 _93824 A => @lem3693893 _93804 _93824 f s P h1 h2 h3). Qed.
Lemma lem3693895 {_93824 A : Type'} : (term133 _93824 A) = (term134 _93824 A).
Proof. exact (@lem69 (term126 _93824 A)). Qed.
Lemma lem3693896 {_93804 _93824 A : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term128 _93804 _93824) (h2 : term125 _93804 _93824) (h3 : term124 _93804 _93824 f s P) : term134 _93824 A.
Proof. exact (EQ_MP (@lem3693895 _93824 A) (@lem3693894 _93804 _93824 A f s P h1 h2 h3)). Qed.
Lemma lem3693897 {_93804 _93824 A : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term128 _93804 _93824) (h2 : term125 _93804 _93824) (h3 : term124 _93804 _93824 f s P) : term137 _93804 _93824 A.
Proof. exact (fun h0 : term126 _93804 A => @lem3693896 _93804 _93824 A f s P h1 h2 h3). Qed.
Lemma lem3693898 {_93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term128 _93804 _93824) (h2 : term125 _93804 _93824) (h3 : term124 _93804 _93824 f s P) : term140 _93804 _93824 A B.
Proof. exact (fun h0 : term125 _93824 B => @lem3693897 _93804 _93824 A f s P h1 h2 h3). Qed.
Lemma lem3693899 {_93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term128 _93804 _93824) (h2 : term125 _93804 _93824) (h3 : term124 _93804 _93824 f s P) : term142 _93804 _93824 A B.
Proof. exact (fun h0 : term125 _93804 B => @lem3693898 _93804 _93824 A B f s P h1 h2 h3). Qed.
Lemma lem3693900 {_93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term128 _93804 _93824) (h2 : term124 _93804 _93824 f s P) : term144 _93804 _93824 A B.
Proof. exact (fun h0 : term125 _93804 _93824 => @lem3693899 _93804 _93824 A B f s P h1 h0 h2). Qed.
Lemma lem3693901 {_93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term128 _93804 _93824) (h2 : term124 _93804 _93824 f s P) : term147 _93804 _93824 A B.
Proof. exact (fun h0 : term127 _93824 A => @lem3693900 _93804 _93824 A B f s P h1 h2). Qed.
Lemma lem3693902 {_93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term128 _93804 _93824) (h2 : term124 _93804 _93824 f s P) : term149 _93804 _93824 A B.
Proof. exact (fun h0 : term127 _93804 A => @lem3693901 _93804 _93824 A B f s P h1 h2). Qed.
Lemma lem3693903 {_93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term128 _93804 _93824) (h2 : term124 _93804 _93824 f s P) : term152 _93804 _93824 A B.
Proof. exact (fun h0 : term128 _93824 B => @lem3693902 _93804 _93824 A B f s P h1 h2). Qed.
Lemma lem3693904 {_87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term128 _93804 _93824) (h2 : term124 _93804 _93824 f s P) : term154 _87604 _93804 _93824 A B.
Proof. exact (fun h0 : term127 _87604 _93824 => @lem3693903 _93804 _93824 A B f s P h1 h2). Qed.
Lemma lem3693905 {_87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term128 _93804 _93824) (h2 : term124 _93804 _93824 f s P) : term156 _87604 _93804 _93824 A B.
Proof. exact (fun h0 : term128 _93804 B => @lem3693904 _87604 _93804 _93824 A B f s P h1 h2). Qed.
Lemma lem3693906 {_87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term124 _93804 _93824 f s P) : term158 _87604 _93804 _93824 A B.
Proof. exact (fun h0 : term128 _93804 _93824 => @lem3693905 _87604 _93804 _93824 A B f s P h0 h1). Qed.
Lemma lem3693907 {_87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term124 _93804 _93824 f s P) : term160 _87604 _93804 _93824 A B.
Proof. exact (fun h0 : term127 _87604 _93804 => @lem3693906 _87604 _93804 _93824 A B f s P h1). Qed.
Lemma lem3693908 {_87593 _87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term124 _93804 _93824 f s P) : term162 _87593 _87604 _93804 _93824 A B.
Proof. exact (fun h0 : term128 _87593 _93824 => @lem3693907 _87604 _93804 _93824 A B f s P h1). Qed.
Lemma lem3693909 {_87593 _87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term124 _93804 _93824 f s P) : term164 _87593 _87604 _93804 _93824 A B.
Proof. exact (fun h0 : term128 _87593 _93804 => @lem3693908 _87593 _87604 _93804 _93824 A B f s P h1). Qed.
Lemma lem3693910 {_87593 _87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : term166 _87593 _87604 _93804 _93824 A B f s P.
Proof. exact (fun h0 : term124 _93804 _93824 f s P => @lem3693909 _87593 _87604 _93804 _93824 A B f s P h0). Qed.
Lemma lem3693915 {_87593 _87604 _93804 _93824 A B : Type'} (s : _93804 -> Prop) (P : type686 _93824) : term170 _87593 _87604 _93804 _93824 A B s P.
Proof. exact (fun f : _93804 -> _93824 => @lem3693910 _87593 _87604 _93804 _93824 A B f s P). Qed.
Lemma lem3693920 {_87593 _87604 _93804 _93824 A B : Type'} (P : type686 _93824) : term174 _87593 _87604 _93804 _93824 A B P.
Proof. exact (fun s : _93804 -> Prop => @lem3693915 _87593 _87604 _93804 _93824 A B s P). Qed.
Lemma lem3693925 {_87593 _87604 _93804 _93824 A B : Type'} : term178 _87593 _87604 _93804 _93824 A B.
Proof. exact (fun P : type686 _93824 => @lem3693920 _87593 _87604 _93804 _93824 A B P). Qed.
Lemma lem3693926 {_87593 _87604 _93804 _93824 A B : Type'} : term177 _87593 _87604 _93804 _93824 A B.
Proof. exact (EQ_MP (@lem3691564 _87593 _87604 _93804 _93824 A B) (@lem3693925 _87593 _87604 _93804 _93824 A B)). Qed.
Lemma lem3693927 {_87593 _87604 _93804 _93824 A B : Type'} (P : type686 _93824) : term280 _87593 _87604 _93804 _93824 A B P.
Proof. exact (@lem3693926 _87593 _87604 _93804 _93824 A B P). Qed.
Lemma lem3693928 {_87593 _87604 _93804 _93824 A B : Type'} (P : type686 _93824) : (term280 _87593 _87604 _93804 _93824 A B P) = (term173 _87593 _87604 _93804 _93824 A B P).
Proof. exact (eq_refl (term280 _87593 _87604 _93804 _93824 A B P)). Qed.
Lemma lem3693929 {_87593 _87604 _93804 _93824 A B : Type'} (P : type686 _93824) : term173 _87593 _87604 _93804 _93824 A B P.
Proof. exact (EQ_MP (@lem3693928 _87593 _87604 _93804 _93824 A B P) (@lem3693927 _87593 _87604 _93804 _93824 A B P)). Qed.
Lemma lem3693930 {_87593 _87604 _93804 _93824 A B : Type'} (P : type686 _93824) (s : _93804 -> Prop) : term281 _87593 _87604 _93804 _93824 A B P s.
Proof. exact (@lem3693929 _87593 _87604 _93804 _93824 A B P s). Qed.
Lemma lem3693931 {_87593 _87604 _93804 _93824 A B : Type'} (s : _93804 -> Prop) (P : type686 _93824) : (term281 _87593 _87604 _93804 _93824 A B P s) = (term169 _87593 _87604 _93804 _93824 A B s P).
Proof. exact (eq_refl (term281 _87593 _87604 _93804 _93824 A B P s)). Qed.
Lemma lem3693932 {_87593 _87604 _93804 _93824 A B : Type'} (s : _93804 -> Prop) (P : type686 _93824) : term169 _87593 _87604 _93804 _93824 A B s P.
Proof. exact (EQ_MP (@lem3693931 _87593 _87604 _93804 _93824 A B s P) (@lem3693930 _87593 _87604 _93804 _93824 A B P s)). Qed.
Lemma lem3693933 {_87593 _87604 _93804 _93824 A B : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : term282 _87593 _87604 _93804 _93824 A B s P f.
Proof. exact (@lem3693932 _87593 _87604 _93804 _93824 A B s P f). Qed.
Lemma lem3693934 {_87593 _87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : (term282 _87593 _87604 _93804 _93824 A B s P f) = (term129 _87593 _87604 _93804 _93824 A B f s P).
Proof. exact (eq_refl (term282 _87593 _87604 _93804 _93824 A B s P f)). Qed.
Lemma lem3693935 {_87593 _87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : term129 _87593 _87604 _93804 _93824 A B f s P.
Proof. exact (EQ_MP (@lem3693934 _87593 _87604 _93804 _93824 A B f s P) (@lem3693933 _87593 _87604 _93804 _93824 A B s P f)). Qed.
Lemma lem3693937 {_87593 _87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : term129 _87593 _87604 _93804 _93824 A B f s P.
Proof. exact (@lem3690613 _87593 _87604 _93804 _93824 A B f s P (@lem3693935 _87593 _87604 _93804 _93824 A B f s P)). Qed.
Lemma lem3693938 {_87593 _87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term124 _93804 _93824 f s P) : term163 _87593 _87604 _93804 _93824 A B.
Proof. exact (@lem3693937 _87593 _87604 _93804 _93824 A B f s P (@lem3690583 _93804 _93824 f s P h1)). Qed.
Lemma lem3693939 {_87593 _87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term124 _93804 _93824 f s P) : term161 _87593 _87604 _93804 _93824 A B.
Proof. exact (@lem3693938 _87593 _87604 _93804 _93824 A B f s P h1 (@lem3690591 _87593 _93804)). Qed.
Lemma lem3693940 {_87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term124 _93804 _93824 f s P) : term159 _87604 _93804 _93824 A B.
Proof. exact (@lem3693939 Prop _87604 _93804 _93824 A B f s P h1 (@lem3690592 Prop _93824)). Qed.
Lemma lem3693941 {_87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term124 _93804 _93824 f s P) : term157 _87604 _93804 _93824 A B.
Proof. exact (@lem3693940 _87604 _93804 _93824 A B f s P h1 (@lem3690589 _87604 _93804)). Qed.
Lemma lem3693942 {_87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term124 _93804 _93824 f s P) : term155 _87604 _93804 _93824 A B.
Proof. exact (@lem3693941 _87604 _93804 _93824 A B f s P h1 (@lem3690593 _93804 _93824)). Qed.
Lemma lem3693943 {_87604 _93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term124 _93804 _93824 f s P) : term153 _87604 _93804 _93824 A B.
Proof. exact (@lem3693942 _87604 _93804 _93824 A B f s P h1 (@lem3690597 _93804 B)). Qed.
Lemma lem3693944 {_93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term124 _93804 _93824 f s P) : term151 _93804 _93824 A B.
Proof. exact (@lem3693943 Prop _93804 _93824 A B f s P h1 (@lem3690590 Prop _93824)). Qed.
Lemma lem3693945 {_93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term124 _93804 _93824 f s P) : term148 _93804 _93824 A B.
Proof. exact (@lem3693944 _93804 _93824 A B f s P h1 (@lem3690596 _93824 B)). Qed.
Lemma lem3693946 {_93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term124 _93804 _93824 f s P) : term146 _93804 _93824 A B.
Proof. exact (@lem3693945 _93804 _93824 A B f s P h1 (@lem3690595 _93804 A)). Qed.
Lemma lem3693947 {_93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term124 _93804 _93824 f s P) : term143 _93804 _93824 A B.
Proof. exact (@lem3693946 _93804 _93824 A B f s P h1 (@lem3690594 _93824 A)). Qed.
Lemma lem3693948 {_93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term124 _93804 _93824 f s P) : term141 _93804 _93824 A B.
Proof. exact (@lem3693947 _93804 _93824 A B f s P h1 (@lem3690588 _93804 _93824)). Qed.
Lemma lem3693949 {_93804 _93824 A B : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term124 _93804 _93824 f s P) : term139 _93804 _93824 A B.
Proof. exact (@lem3693948 _93804 _93824 A B f s P h1 (@lem3690584 _93804 B)). Qed.
Lemma lem3693950 {_93804 _93824 A : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term124 _93804 _93824 f s P) : term136 _93804 _93824 A.
Proof. exact (@lem3693949 _93804 _93824 A Prop f s P h1 (@lem3690585 _93824 Prop)). Qed.
Lemma lem3693951 {_93804 _93824 A : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term124 _93804 _93824 f s P) : term133 _93824 A.
Proof. exact (@lem3693950 _93804 _93824 A f s P h1 (@lem3690586 _93804 A)). Qed.
Lemma lem3693952 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term124 _93804 _93824 f s P) : False.
Proof. exact (@lem3693951 _93804 _93824 Prop f s P h1 (@lem3690587 _93824 Prop)). Qed.
Lemma lem3693953 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term124 _93804 _93824 f s P) : (term124 _93804 _93824 f s P) = False.
Proof. exact (prop_ext (fun h2 : term124 _93804 _93824 f s P => @lem3693952 _93804 _93824 f s P h1) (fun h2 : False => @lem3690583 _93804 _93824 f s P h1)). Qed.
Lemma lem3693954 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) (h1 : term124 _93804 _93824 f s P) : False.
Proof. exact (EQ_MP (@lem3693953 _93804 _93824 f s P h1) (@lem3690583 _93804 _93824 f s P h1)). Qed.
Lemma lem3693955 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : term123 _93804 _93824 f s P.
Proof. exact (fun h0 : term124 _93804 _93824 f s P => @lem3693954 _93804 _93824 f s P h0). Qed.
Lemma lem3693956 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : term122 _93804 _93824 f s P.
Proof. exact (EQ_MP (@lem3690582 _93804 _93824 f s P) (@lem3693955 _93804 _93824 f s P)). Qed.
Lemma lem3693957 {_93804 _93824 : Type'} (f : _93804 -> _93824) (s : _93804 -> Prop) (P : type686 _93824) : term283 _93804 _93824 f s P.
Proof. exact (conj (@lem3690578 _93804 _93824 s P f) (@lem3693956 _93804 _93824 f s P)). Qed.
Lemma lem3693958 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term283 _93804 _93824 f s P) = ((term5 _93804 _93824 f s P) = (term9 _93804 _93824 s P f)).
Proof. exact (@lem32 (term5 _93804 _93824 f s P) (term9 _93804 _93824 s P f)). Qed.
Lemma lem3693959 {_93804 _93824 : Type'} (s : _93804 -> Prop) (P : type686 _93824) (f : _93804 -> _93824) : (term5 _93804 _93824 f s P) = (term9 _93804 _93824 s P f).
Proof. exact (EQ_MP (@lem3693958 _93804 _93824 s P f) (@lem3693957 _93804 _93824 f s P)). Qed.
Lemma lem3693964 {_93804 _93824 : Type'} (P : type686 _93824) (f : _93804 -> _93824) : term284 _93804 _93824 P f.
Proof. exact (fun s : _93804 -> Prop => @lem3693959 _93804 _93824 s P f). Qed.
Lemma lem3693969 {_93804 _93824 : Type'} (P : type686 _93824) : term285 _93804 _93824 P.
Proof. exact (fun f : _93804 -> _93824 => @lem3693964 _93804 _93824 P f). Qed.
Lemma lem3693974 {_93804 _93824 : Type'} : term286 _93804 _93824.
Proof. exact (fun P : type686 _93824 => @lem3693969 _93804 _93824 P). Qed.
