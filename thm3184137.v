Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3184137_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Lemma lem3183588 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3183589 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : ((term1 _83095 p x) = (p x)) = (term2 _83095 p x).
Proof. exact (@lem3183588 ((term1 _83095 p x) = (p x))). Qed.
Lemma lem3183590 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term2 _83095 p x) = ((term1 _83095 p x) = (p x)).
Proof. exact (SYM (@lem3183589 _83095 p x)). Qed.
Lemma lem3183591 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term3 _83095 p x) : term3 _83095 p x.
Proof. exact (h1). Qed.
Lemma lem3183594 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term2 _83095 p x) : term2 _83095 p x.
Proof. exact (h1). Qed.
Lemma lem3183595 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term4 _83095 p x.
Proof. exact (fun h0 : term2 _83095 p x => @lem3183594 _83095 p x h0). Qed.
Lemma lem3183596 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term4 _83095 p x) : term4 _83095 p x.
Proof. exact (h1). Qed.
Lemma lem3183597 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term2 _83095 p x) : term2 _83095 p x.
Proof. exact (h1). Qed.
Lemma lem3183598 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term2 _83095 p x) (h2 : term4 _83095 p x) : term2 _83095 p x.
Proof. exact (@lem3183596 _83095 p x h2 (@lem3183597 _83095 p x h1)). Qed.
Lemma lem3183599 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term2 _83095 p x) : term5 _83095 p x.
Proof. exact (fun h0 : term4 _83095 p x => @lem3183598 _83095 p x h1 h0). Qed.
Lemma lem3183600 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term4 _83095 p x) : term4 _83095 p x.
Proof. exact (h1). Qed.
Lemma lem3183601 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term2 _83095 p x) (h2 : term4 _83095 p x) : term2 _83095 p x.
Proof. exact (@lem3183599 _83095 p x h1 (@lem3183600 _83095 p x h2)). Qed.
Lemma lem3183602 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term4 _83095 p x) : term4 _83095 p x.
Proof. exact (fun h0 : term2 _83095 p x => @lem3183601 _83095 p x h0 h1). Qed.
Lemma lem3183603 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term6 _83095 p x.
Proof. exact (fun h0 : term4 _83095 p x => @lem3183602 _83095 p x h0). Qed.
Lemma lem3183606 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term4 _83095 p x.
Proof. exact (@lem3183603 _83095 p x (@lem3183595 _83095 p x)). Qed.
Lemma lem3183607 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term4 _83095 p x.
Proof. exact (@lem3183606 _83095 p x). Qed.
Lemma lem3183617 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3183618 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term2 _83095 p x) = (term7 _83095 p x).
Proof. exact (@lem3183617 (term3 _83095 p x)). Qed.
Lemma lem3183620 (t : Prop) : (term8 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3183621 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term7 _83095 p x) = ((term1 _83095 p x) = (p x)).
Proof. exact (@lem3183620 ((term1 _83095 p x) = (p x))). Qed.
Lemma lem3183622 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term2 _83095 p x) = ((term1 _83095 p x) = (p x)).
Proof. exact (TRANS (@lem3183618 _83095 p x) (@lem3183621 _83095 p x)). Qed.
Lemma lem3183653 {_83095 : Type'} (x : _83095) : (term9 _83095 x) = (term10 _83095 x).
Proof. exact (fun_ext (fun p : _83095 -> Prop => @lem3183622 _83095 p x)). Qed.
Lemma lem3183654 {_83095 : Type'} : (@all (_83095 -> Prop)) = (@all (_83095 -> Prop)).
Proof. exact (eq_refl (@all (_83095 -> Prop))). Qed.
Lemma lem3183655 {_83095 : Type'} (x : _83095) : (term11 _83095 x) = (term12 _83095 x).
Proof. exact (MK_COMB (@lem3183654 _83095) (@lem3183653 _83095 x)). Qed.
Lemma lem3183660 {_83095 : Type'} : (term13 _83095) = (term14 _83095).
Proof. exact (fun_ext (fun x : _83095 => @lem3183655 _83095 x)). Qed.
Lemma lem3183661 {_83095 : Type'} : (@all _83095) = (@all _83095).
Proof. exact (eq_refl (@all _83095)). Qed.
Lemma lem3183670 {_83095 : Type'} : (term15 _83095) = (term16 _83095).
Proof. exact (MK_COMB (@lem3183661 _83095) (@lem3183660 _83095)). Qed.
Lemma lem3183671 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (p x) = (p x).
Proof. exact (eq_refl (p x)). Qed.
Lemma lem3183676 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (y : _83095) : (term17 _83095 p x y) = (term17 _83095 p x y).
Proof. exact (eq_refl (term17 _83095 p x y)). Qed.
Lemma lem3183677 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term18 _83095 p x) = (term18 _83095 p x).
Proof. exact (fun_ext (fun y : _83095 => @lem3183676 _83095 p x y)). Qed.
Lemma lem3183678 {_83095 : Type'} : (@ex _83095) = (@ex _83095).
Proof. exact (eq_refl (@ex _83095)). Qed.
Lemma lem3183679 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term1 _83095 p x) = (term1 _83095 p x).
Proof. exact (MK_COMB (@lem3183678 _83095) (@lem3183677 _83095 p x)). Qed.
Lemma lem3183680 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3183681 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term19 _83095 p x) = (term19 _83095 p x).
Proof. exact (MK_COMB (@lem3183680) (@lem3183679 _83095 p x)). Qed.
Lemma lem3183682 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : ((term1 _83095 p x) = (p x)) = ((term1 _83095 p x) = (p x)).
Proof. exact (MK_COMB (@lem3183681 _83095 p x) (@lem3183671 _83095 p x)). Qed.
Lemma lem3183683 {_83095 : Type'} (x : _83095) : (term10 _83095 x) = (term10 _83095 x).
Proof. exact (fun_ext (fun p : _83095 -> Prop => @lem3183682 _83095 p x)). Qed.
Lemma lem3183684 {_83095 : Type'} : (@all (_83095 -> Prop)) = (@all (_83095 -> Prop)).
Proof. exact (eq_refl (@all (_83095 -> Prop))). Qed.
Lemma lem3183685 {_83095 : Type'} (x : _83095) : (term12 _83095 x) = (term12 _83095 x).
Proof. exact (MK_COMB (@lem3183684 _83095) (@lem3183683 _83095 x)). Qed.
Lemma lem3183686 {_83095 : Type'} : (term14 _83095) = (term14 _83095).
Proof. exact (fun_ext (fun x : _83095 => @lem3183685 _83095 x)). Qed.
Lemma lem3183687 {_83095 : Type'} : (@all _83095) = (@all _83095).
Proof. exact (eq_refl (@all _83095)). Qed.
Lemma lem3183688 {_83095 : Type'} : (term16 _83095) = (term16 _83095).
Proof. exact (MK_COMB (@lem3183687 _83095) (@lem3183686 _83095)). Qed.
Lemma lem3183711 {_83095 : Type'} : (term15 _83095) = (term16 _83095).
Proof. exact (TRANS (@lem3183670 _83095) (@lem3183688 _83095)). Qed.
Lemma lem3183712 {_83095 : Type'} : (term16 _83095) = (term15 _83095).
Proof. exact (SYM (@lem3183711 _83095)). Qed.
Lemma lem3183714 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3183715 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : ((term1 _83095 p x) = (p x)) = (term2 _83095 p x).
Proof. exact (@lem3183714 ((term1 _83095 p x) = (p x))). Qed.
Lemma lem3183716 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term2 _83095 p x) = ((term1 _83095 p x) = (p x)).
Proof. exact (SYM (@lem3183715 _83095 p x)). Qed.
Lemma lem3183717 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term3 _83095 p x) : term3 _83095 p x.
Proof. exact (h1). Qed.
Lemma lem3183726 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (y : _83095) : (term20 _83095 p x y) = (term21 _83095 p x y).
Proof. exact (@lem17045 (p y) (x = y)). Qed.
Lemma lem3183729 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (y : _83095) : (term17 _83095 p x y) = (term17 _83095 p x y).
Proof. exact (eq_refl (term17 _83095 p x y)). Qed.
Lemma lem3183730 {_83095 : Type'} (P : _83095 -> Prop) : (term22 _83095 P) = (term23 _83095 P).
Proof. exact (@lem18394 _83095 P). Qed.
Lemma lem3183731 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term24 _83095 p x) = (term25 _83095 p x).
Proof. exact (@lem3183730 _83095 (term18 _83095 p x)). Qed.
Lemma lem3183732 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (y : _83095) : (term26 _83095 p x y) = (term17 _83095 p x y).
Proof. exact (eq_refl (term26 _83095 p x y)). Qed.
Lemma lem3183733 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3183734 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (y : _83095) : (term27 _83095 p x y) = (term20 _83095 p x y).
Proof. exact (MK_COMB (@lem3183733) (@lem3183732 _83095 p x y)). Qed.
Lemma lem3183735 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (y : _83095) : (term27 _83095 p x y) = (term21 _83095 p x y).
Proof. exact (TRANS (@lem3183734 _83095 p x y) (@lem3183726 _83095 p x y)). Qed.
Lemma lem3183736 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term28 _83095 p x) = (term29 _83095 p x).
Proof. exact (fun_ext (fun y : _83095 => @lem3183735 _83095 p x y)). Qed.
Lemma lem3183737 {_83095 : Type'} : (@all _83095) = (@all _83095).
Proof. exact (eq_refl (@all _83095)). Qed.
Lemma lem3183738 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term25 _83095 p x) = (term30 _83095 p x).
Proof. exact (MK_COMB (@lem3183737 _83095) (@lem3183736 _83095 p x)). Qed.
Lemma lem3183739 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term24 _83095 p x) = (term30 _83095 p x).
Proof. exact (TRANS (@lem3183731 _83095 p x) (@lem3183738 _83095 p x)). Qed.
Lemma lem3183740 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term18 _83095 p x) = (term18 _83095 p x).
Proof. exact (fun_ext (fun y : _83095 => @lem3183729 _83095 p x y)). Qed.
Lemma lem3183741 {_83095 : Type'} : (@ex _83095) = (@ex _83095).
Proof. exact (eq_refl (@ex _83095)). Qed.
Lemma lem3183742 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term1 _83095 p x) = (term1 _83095 p x).
Proof. exact (MK_COMB (@lem3183741 _83095) (@lem3183740 _83095 p x)). Qed.
Lemma lem3183743 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term31 _83095 p x) = (term31 _83095 p x).
Proof. exact (eq_refl (term31 _83095 p x)). Qed.
Lemma lem3183744 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (p x) = (p x).
Proof. exact (eq_refl (p x)). Qed.
Lemma lem3183745 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3183746 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term32 _83095 p x) = (term33 _83095 p x).
Proof. exact (MK_COMB (@lem3183745) (@lem3183739 _83095 p x)). Qed.
Lemma lem3183747 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term34 _83095 p x) = (term35 _83095 p x).
Proof. exact (MK_COMB (@lem3183746 _83095 p x) (@lem3183744 _83095 p x)). Qed.
Lemma lem3183748 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3183749 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term36 _83095 p x) = (term36 _83095 p x).
Proof. exact (MK_COMB (@lem3183748) (@lem3183742 _83095 p x)). Qed.
Lemma lem3183750 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term37 _83095 p x) = (term37 _83095 p x).
Proof. exact (MK_COMB (@lem3183749 _83095 p x) (@lem3183743 _83095 p x)). Qed.
Lemma lem3183751 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3183752 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term38 _83095 p x) = (term38 _83095 p x).
Proof. exact (MK_COMB (@lem3183751) (@lem3183750 _83095 p x)). Qed.
Lemma lem3183753 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term39 _83095 p x) = (term40 _83095 p x).
Proof. exact (MK_COMB (@lem3183752 _83095 p x) (@lem3183747 _83095 p x)). Qed.
Lemma lem3183754 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term3 _83095 p x) = (term39 _83095 p x).
Proof. exact (@lem17646 (term1 _83095 p x) (p x)). Qed.
Lemma lem3183755 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term3 _83095 p x) = (term40 _83095 p x).
Proof. exact (TRANS (@lem3183754 _83095 p x) (@lem3183753 _83095 p x)). Qed.
Lemma lem3183834 {A : Type'} (P : A -> Prop) (Q : Prop) : (term41 A P Q) = (term42 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3183835 {_83095 : Type'} (P : _83095 -> Prop) (Q : Prop) : (term41 _83095 P Q) = (term42 _83095 P Q).
Proof. exact (@lem3183834 _83095 P Q). Qed.
Lemma lem3183836 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term43 _83095 p x) = (term44 _83095 p x).
Proof. exact (@lem3183835 _83095 (term18 _83095 p x) (term31 _83095 p x)). Qed.
Lemma lem3183837 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (y : _83095) : (term26 _83095 p x y) = (term17 _83095 p x y).
Proof. exact (eq_refl (term26 _83095 p x y)). Qed.
Lemma lem3183838 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term45 _83095 p x) = (term18 _83095 p x).
Proof. exact (fun_ext (fun y : _83095 => @lem3183837 _83095 p x y)). Qed.
Lemma lem3183839 {_83095 : Type'} : (@ex _83095) = (@ex _83095).
Proof. exact (eq_refl (@ex _83095)). Qed.
Lemma lem3183840 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term46 _83095 p x) = (term1 _83095 p x).
Proof. exact (MK_COMB (@lem3183839 _83095) (@lem3183838 _83095 p x)). Qed.
Lemma lem3183841 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3183842 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term47 _83095 p x) = (term36 _83095 p x).
Proof. exact (MK_COMB (@lem3183841) (@lem3183840 _83095 p x)). Qed.
Lemma lem3183843 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term31 _83095 p x) = (term31 _83095 p x).
Proof. exact (eq_refl (term31 _83095 p x)). Qed.
Lemma lem3183844 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term43 _83095 p x) = (term37 _83095 p x).
Proof. exact (MK_COMB (@lem3183842 _83095 p x) (@lem3183843 _83095 p x)). Qed.
Lemma lem3183845 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3183846 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term48 _83095 p x) = (term49 _83095 p x).
Proof. exact (MK_COMB (@lem3183845) (@lem3183844 _83095 p x)). Qed.
Lemma lem3183847 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (y : _83095) : (term26 _83095 p x y) = (term17 _83095 p x y).
Proof. exact (eq_refl (term26 _83095 p x y)). Qed.
Lemma lem3183848 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3183849 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (y : _83095) : (term50 _83095 p x y) = (term51 _83095 p x y).
Proof. exact (MK_COMB (@lem3183848) (@lem3183847 _83095 p x y)). Qed.
Lemma lem3183850 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term31 _83095 p x) = (term31 _83095 p x).
Proof. exact (eq_refl (term31 _83095 p x)). Qed.
Lemma lem3183851 {_83095 : Type'} (y : _83095) (p : _83095 -> Prop) (x : _83095) : (term52 _83095 y p x) = (term53 _83095 y p x).
Proof. exact (MK_COMB (@lem3183849 _83095 p x y) (@lem3183850 _83095 p x)). Qed.
Lemma lem3183852 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term54 _83095 p x) = (term55 _83095 p x).
Proof. exact (fun_ext (fun y : _83095 => @lem3183851 _83095 y p x)). Qed.
Lemma lem3183853 {_83095 : Type'} : (@ex _83095) = (@ex _83095).
Proof. exact (eq_refl (@ex _83095)). Qed.
Lemma lem3183854 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term44 _83095 p x) = (term56 _83095 p x).
Proof. exact (MK_COMB (@lem3183853 _83095) (@lem3183852 _83095 p x)). Qed.
Lemma lem3183855 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : ((term43 _83095 p x) = (term44 _83095 p x)) = ((term37 _83095 p x) = (term56 _83095 p x)).
Proof. exact (MK_COMB (@lem3183846 _83095 p x) (@lem3183854 _83095 p x)). Qed.
Lemma lem3183856 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term37 _83095 p x) = (term56 _83095 p x).
Proof. exact (EQ_MP (@lem3183855 _83095 p x) (@lem3183836 _83095 p x)). Qed.
Lemma lem3183857 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3183858 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term38 _83095 p x) = (term57 _83095 p x).
Proof. exact (MK_COMB (@lem3183857) (@lem3183856 _83095 p x)). Qed.
Lemma lem3183859 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term35 _83095 p x) = (term35 _83095 p x).
Proof. exact (eq_refl (term35 _83095 p x)). Qed.
Lemma lem3183860 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term40 _83095 p x) = (term58 _83095 p x).
Proof. exact (MK_COMB (@lem3183858 _83095 p x) (@lem3183859 _83095 p x)). Qed.
Lemma lem3183862 {A : Type'} (P : A -> Prop) (Q : Prop) : (term59 A P Q) = (term60 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3183863 {_83095 : Type'} (P : _83095 -> Prop) (Q : Prop) : (term59 _83095 P Q) = (term60 _83095 P Q).
Proof. exact (@lem3183862 _83095 P Q). Qed.
Lemma lem3183864 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term61 _83095 p x) = (term62 _83095 p x).
Proof. exact (@lem3183863 _83095 (term55 _83095 p x) (term35 _83095 p x)). Qed.
Lemma lem3183865 {_83095 : Type'} (y : _83095) (p : _83095 -> Prop) (x : _83095) : (term63 _83095 p x y) = (term53 _83095 y p x).
Proof. exact (eq_refl (term63 _83095 p x y)). Qed.
Lemma lem3183866 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term64 _83095 p x) = (term55 _83095 p x).
Proof. exact (fun_ext (fun y : _83095 => @lem3183865 _83095 y p x)). Qed.
Lemma lem3183867 {_83095 : Type'} : (@ex _83095) = (@ex _83095).
Proof. exact (eq_refl (@ex _83095)). Qed.
Lemma lem3183868 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term65 _83095 p x) = (term56 _83095 p x).
Proof. exact (MK_COMB (@lem3183867 _83095) (@lem3183866 _83095 p x)). Qed.
Lemma lem3183869 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3183870 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term66 _83095 p x) = (term57 _83095 p x).
Proof. exact (MK_COMB (@lem3183869) (@lem3183868 _83095 p x)). Qed.
Lemma lem3183871 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term35 _83095 p x) = (term35 _83095 p x).
Proof. exact (eq_refl (term35 _83095 p x)). Qed.
Lemma lem3183872 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term61 _83095 p x) = (term58 _83095 p x).
Proof. exact (MK_COMB (@lem3183870 _83095 p x) (@lem3183871 _83095 p x)). Qed.
Lemma lem3183873 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3183874 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term67 _83095 p x) = (term68 _83095 p x).
Proof. exact (MK_COMB (@lem3183873) (@lem3183872 _83095 p x)). Qed.
Lemma lem3183875 {_83095 : Type'} (y : _83095) (p : _83095 -> Prop) (x : _83095) : (term63 _83095 p x y) = (term53 _83095 y p x).
Proof. exact (eq_refl (term63 _83095 p x y)). Qed.
Lemma lem3183876 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3183877 {_83095 : Type'} (y : _83095) (p : _83095 -> Prop) (x : _83095) : (term69 _83095 p x y) = (term70 _83095 y p x).
Proof. exact (MK_COMB (@lem3183876) (@lem3183875 _83095 y p x)). Qed.
Lemma lem3183878 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term35 _83095 p x) = (term35 _83095 p x).
Proof. exact (eq_refl (term35 _83095 p x)). Qed.
Lemma lem3183879 {_83095 : Type'} (y : _83095) (p : _83095 -> Prop) (x : _83095) : (term71 _83095 y p x) = (term72 _83095 y p x).
Proof. exact (MK_COMB (@lem3183877 _83095 y p x) (@lem3183878 _83095 p x)). Qed.
Lemma lem3183880 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term73 _83095 p x) = (term74 _83095 p x).
Proof. exact (fun_ext (fun y : _83095 => @lem3183879 _83095 y p x)). Qed.
Lemma lem3183881 {_83095 : Type'} : (@ex _83095) = (@ex _83095).
Proof. exact (eq_refl (@ex _83095)). Qed.
Lemma lem3183882 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term62 _83095 p x) = (term75 _83095 p x).
Proof. exact (MK_COMB (@lem3183881 _83095) (@lem3183880 _83095 p x)). Qed.
Lemma lem3183883 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : ((term61 _83095 p x) = (term62 _83095 p x)) = ((term58 _83095 p x) = (term75 _83095 p x)).
Proof. exact (MK_COMB (@lem3183874 _83095 p x) (@lem3183882 _83095 p x)). Qed.
Lemma lem3183884 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term58 _83095 p x) = (term75 _83095 p x).
Proof. exact (EQ_MP (@lem3183883 _83095 p x) (@lem3183864 _83095 p x)). Qed.
Lemma lem3183886 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term40 _83095 p x) = (term75 _83095 p x).
Proof. exact (TRANS (@lem3183860 _83095 p x) (@lem3183884 _83095 p x)). Qed.
Lemma lem3183887 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term3 _83095 p x) = (term75 _83095 p x).
Proof. exact (TRANS (@lem3183755 _83095 p x) (@lem3183886 _83095 p x)). Qed.
Lemma lem3183888 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term3 _83095 p x) : term75 _83095 p x.
Proof. exact (EQ_MP (@lem3183887 _83095 p x) (@lem3183717 _83095 p x h1)). Qed.
Lemma lem3183889 {_83095 : Type'} (y : _83095) (p : _83095 -> Prop) (x : _83095) (h1 : term72 _83095 y p x) : term72 _83095 y p x.
Proof. exact (h1). Qed.
Lemma lem3183892 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (p x) = (p x).
Proof. exact (eq_refl (p x)). Qed.
Lemma lem3183907 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (y : _83095) : (term21 _83095 p x y) = (term21 _83095 p x y).
Proof. exact (eq_refl (term21 _83095 p x y)). Qed.
Lemma lem3183908 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term29 _83095 p x) = (term29 _83095 p x).
Proof. exact (fun_ext (fun y : _83095 => @lem3183907 _83095 p x y)). Qed.
Lemma lem3183909 {_83095 : Type'} : (@all _83095) = (@all _83095).
Proof. exact (eq_refl (@all _83095)). Qed.
Lemma lem3183910 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term30 _83095 p x) = (term30 _83095 p x).
Proof. exact (MK_COMB (@lem3183909 _83095) (@lem3183908 _83095 p x)). Qed.
Lemma lem3183911 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3183912 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term33 _83095 p x) = (term33 _83095 p x).
Proof. exact (MK_COMB (@lem3183911) (@lem3183910 _83095 p x)). Qed.
Lemma lem3183913 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term35 _83095 p x) = (term35 _83095 p x).
Proof. exact (MK_COMB (@lem3183912 _83095 p x) (@lem3183892 _83095 p x)). Qed.
Lemma lem3183934 {_83095 : Type'} (y : _83095) (p : _83095 -> Prop) (x : _83095) : (term70 _83095 y p x) = (term70 _83095 y p x).
Proof. exact (eq_refl (term70 _83095 y p x)). Qed.
Lemma lem3183935 {_83095 : Type'} (y : _83095) (p : _83095 -> Prop) (x : _83095) : (term72 _83095 y p x) = (term72 _83095 y p x).
Proof. exact (MK_COMB (@lem3183934 _83095 y p x) (@lem3183913 _83095 p x)). Qed.
Lemma lem3183936 {_83095 : Type'} (y : _83095) (p : _83095 -> Prop) (x : _83095) (h1 : term72 _83095 y p x) : term72 _83095 y p x.
Proof. exact (EQ_MP (@lem3183935 _83095 y p x) (@lem3183889 _83095 y p x h1)). Qed.
Lemma lem3183937 {_83095 : Type'} (y : _83095) (p : _83095 -> Prop) (x : _83095) (h1 : term53 _83095 y p x) : term53 _83095 y p x.
Proof. exact (h1). Qed.
Lemma lem3183938 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term35 _83095 p x) : term35 _83095 p x.
Proof. exact (h1). Qed.
Lemma lem3183940 {_83095 : Type'} (y : _83095) (p : _83095 -> Prop) (x : _83095) (h1 : term53 _83095 y p x) : term17 _83095 p x y.
Proof. exact (proj1 (@lem3183937 _83095 y p x h1)). Qed.
Lemma lem3183944 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term35 _83095 p x) : term30 _83095 p x.
Proof. exact (proj1 (@lem3183938 _83095 p x h1)). Qed.
Lemma lem3183964 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (y : _83095) : (term21 _83095 p x y) = (term21 _83095 p x y).
Proof. exact (eq_refl (term21 _83095 p x y)). Qed.
Lemma lem3183965 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term29 _83095 p x) = (term29 _83095 p x).
Proof. exact (fun_ext (fun y : _83095 => @lem3183964 _83095 p x y)). Qed.
Lemma lem3183966 {_83095 : Type'} : (@all _83095) = (@all _83095).
Proof. exact (eq_refl (@all _83095)). Qed.
Lemma lem3183968 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term30 _83095 p x) = (term30 _83095 p x).
Proof. exact (MK_COMB (@lem3183966 _83095) (@lem3183965 _83095 p x)). Qed.
Lemma lem3183969 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term35 _83095 p x) : term30 _83095 p x.
Proof. exact (EQ_MP (@lem3183968 _83095 p x) (@lem3183944 _83095 p x h1)). Qed.
Lemma lem3183974 {_83095 : Type'} (_32721 : _83095) (p : _83095 -> Prop) (x : _83095) (h1 : term35 _83095 p x) : term76 _83095 p x _32721.
Proof. exact (@lem3183969 _83095 p x h1 _32721). Qed.
Lemma lem3183975 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (_32721 : _83095) : (term76 _83095 p x _32721) = (term21 _83095 p x _32721).
Proof. exact (eq_refl (term76 _83095 p x _32721)). Qed.
Lemma lem3183978 {_83095 : Type'} (y : _83095) (p : _83095 -> Prop) (x : _83095) (h1 : term53 _83095 y p x) : term31 _83095 p x.
Proof. exact (proj2 (@lem3183937 _83095 y p x h1)). Qed.
Lemma lem3183982 {_83095 : Type'} (y : _83095) (p : _83095 -> Prop) (x : _83095) (h1 : term53 _83095 y p x) : x = y.
Proof. exact (proj2 (@lem3183940 _83095 y p x h1)). Qed.
Lemma lem3183988 {_83095 : Type'} (_32721 : _83095) (p : _83095 -> Prop) (x : _83095) (h1 : term35 _83095 p x) : term21 _83095 p x _32721.
Proof. exact (EQ_MP (@lem3183975 _83095 p x _32721) (@lem3183974 _83095 _32721 p x h1)). Qed.
Lemma lem3184005 {_83095 : Type'} (p : _83095 -> Prop) : (term77 _83095 p) = (term77 _83095 p).
Proof. exact (eq_refl (term77 _83095 p)). Qed.
Lemma lem3184006 {_83095 : Type'} (y : _83095) (p : _83095 -> Prop) (x : _83095) (h1 : term53 _83095 y p x) : (term78 _83095 p x) = (term78 _83095 p y).
Proof. exact (MK_COMB (@lem3184005 _83095 p) (@lem3183982 _83095 y p x h1)). Qed.
Lemma lem3184007 {_83095 : Type'} (p : _83095 -> Prop) (y : _83095) : (term78 _83095 p y) = (term31 _83095 p y).
Proof. exact (eq_refl (term78 _83095 p y)). Qed.
Lemma lem3184008 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term79 _83095 p x) = (term79 _83095 p x).
Proof. exact (eq_refl (term79 _83095 p x)). Qed.
Lemma lem3184009 {_83095 : Type'} (x : _83095) (p : _83095 -> Prop) (y : _83095) : ((term78 _83095 p x) = (term78 _83095 p y)) = ((term78 _83095 p x) = (term31 _83095 p y)).
Proof. exact (MK_COMB (@lem3184008 _83095 p x) (@lem3184007 _83095 p y)). Qed.
Lemma lem3184010 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term78 _83095 p x) = (term31 _83095 p x).
Proof. exact (eq_refl (term78 _83095 p x)). Qed.
Lemma lem3184011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3184012 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term79 _83095 p x) = (term80 _83095 p x).
Proof. exact (MK_COMB (@lem3184011) (@lem3184010 _83095 p x)). Qed.
Lemma lem3184013 {_83095 : Type'} (p : _83095 -> Prop) (y : _83095) : (term31 _83095 p y) = (term31 _83095 p y).
Proof. exact (eq_refl (term31 _83095 p y)). Qed.
Lemma lem3184014 {_83095 : Type'} (x : _83095) (p : _83095 -> Prop) (y : _83095) : ((term78 _83095 p x) = (term31 _83095 p y)) = ((term31 _83095 p x) = (term31 _83095 p y)).
Proof. exact (MK_COMB (@lem3184012 _83095 p x) (@lem3184013 _83095 p y)). Qed.
Lemma lem3184015 {_83095 : Type'} (x : _83095) (p : _83095 -> Prop) (y : _83095) : ((term78 _83095 p x) = (term78 _83095 p y)) = ((term31 _83095 p x) = (term31 _83095 p y)).
Proof. exact (TRANS (@lem3184009 _83095 x p y) (@lem3184014 _83095 x p y)). Qed.
Lemma lem3184016 {_83095 : Type'} (y : _83095) (p : _83095 -> Prop) (x : _83095) (h1 : term53 _83095 y p x) : (term31 _83095 p x) = (term31 _83095 p y).
Proof. exact (EQ_MP (@lem3184015 _83095 x p y) (@lem3184006 _83095 y p x h1)). Qed.
Lemma lem3184017 {_83095 : Type'} (y : _83095) (p : _83095 -> Prop) (x : _83095) (h1 : term53 _83095 y p x) : term31 _83095 p y.
Proof. exact (EQ_MP (@lem3184016 _83095 y p x h1) (@lem3183978 _83095 y p x h1)). Qed.
Lemma lem3184033 {_83095 : Type'} (y : _83095) (p : _83095 -> Prop) (x : _83095) (h1 : term53 _83095 y p x) : p y.
Proof. exact (proj1 (@lem3183940 _83095 y p x h1)). Qed.
Lemma lem3184034 {_83095 : Type'} (y : _83095) (p : _83095 -> Prop) (x : _83095) (h1 : term53 _83095 y p x) : term81 _83095 p y.
Proof. exact (fun h0 : term31 _83095 p y => @lem3184033 _83095 y p x h1). Qed.
Lemma lem3184036 (p : Prop) : (term82 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3184037 {_83095 : Type'} (p : _83095 -> Prop) (y : _83095) : (term81 _83095 p y) = (p y).
Proof. exact (@lem3184036 (p y)). Qed.
Lemma lem3184038 {_83095 : Type'} (y : _83095) (p : _83095 -> Prop) (x : _83095) (h1 : term53 _83095 y p x) : p y.
Proof. exact (EQ_MP (@lem3184037 _83095 p y) (@lem3184034 _83095 y p x h1)). Qed.
Lemma lem3184041 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3184043 {_83095 : Type'} (p : _83095 -> Prop) (y : _83095) : (term31 _83095 p y) = (term83 _83095 p y).
Proof. exact (@lem3184041 (p y)). Qed.
Lemma lem3184046 {_83095 : Type'} (y : _83095) (p : _83095 -> Prop) (x : _83095) (h1 : term53 _83095 y p x) : term83 _83095 p y.
Proof. exact (EQ_MP (@lem3184043 _83095 p y) (@lem3184017 _83095 y p x h1)). Qed.
Lemma lem3184049 {_83095 : Type'} (y : _83095) (p : _83095 -> Prop) (x : _83095) (h1 : term53 _83095 y p x) : False.
Proof. exact (@lem3184046 _83095 y p x h1 (@lem3184038 _83095 y p x h1)). Qed.
Lemma lem3184050 {_83095 : Type'} (y : _83095) (p : _83095 -> Prop) (x : _83095) (h1 : term53 _83095 y p x) : term84.
Proof. exact (fun h0 : ~ False => @lem3184049 _83095 y p x h1). Qed.
Lemma lem3184052 (p : Prop) : (term82 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3184053 : term84 = False.
Proof. exact (@lem3184052 False). Qed.
Lemma lem3184070 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term35 _83095 p x) : p x.
Proof. exact (proj2 (@lem3183938 _83095 p x h1)). Qed.
Lemma lem3184071 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term35 _83095 p x) : term81 _83095 p x.
Proof. exact (fun h0 : term31 _83095 p x => @lem3184070 _83095 p x h1). Qed.
Lemma lem3184073 (p : Prop) : (term82 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3184074 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term81 _83095 p x) = (p x).
Proof. exact (@lem3184073 (p x)). Qed.
Lemma lem3184075 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term35 _83095 p x) : p x.
Proof. exact (EQ_MP (@lem3184074 _83095 p x) (@lem3184071 _83095 p x h1)). Qed.
Lemma lem3184077 {_83095 : Type'} (x : _83095) : x = x.
Proof. exact (@lem21386 _83095 x). Qed.
Lemma lem3184078 {_83095 : Type'} (x : _83095) : x = x.
Proof. exact (@lem3184077 _83095 x). Qed.
Lemma lem3184079 {_83095 : Type'} (x : _83095) : term85 _83095 x.
Proof. exact (fun h0 : term86 _83095 x => @lem3184078 _83095 x). Qed.
Lemma lem3184081 (p : Prop) : (term82 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3184082 {_83095 : Type'} (x : _83095) : (term85 _83095 x) = (x = x).
Proof. exact (@lem3184081 (x = x)). Qed.
Lemma lem3184083 {_83095 : Type'} (x : _83095) : x = x.
Proof. exact (EQ_MP (@lem3184082 _83095 x) (@lem3184079 _83095 x)). Qed.
Lemma lem3184085 (a : Prop) (b : Prop) : (term87 a b) = (term88 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3184086 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (_32721 : _83095) : (term21 _83095 p x _32721) = (term20 _83095 p x _32721).
Proof. exact (@lem3184085 (p _32721) (x = _32721)). Qed.
Lemma lem3184088 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3184089 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (_32721 : _83095) : (term20 _83095 p x _32721) = (term89 _83095 p x _32721).
Proof. exact (@lem3184088 (term17 _83095 p x _32721)). Qed.
Lemma lem3184090 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (_32721 : _83095) : (term21 _83095 p x _32721) = (term89 _83095 p x _32721).
Proof. exact (TRANS (@lem3184086 _83095 p x _32721) (@lem3184089 _83095 p x _32721)). Qed.
Lemma lem3184092 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term35 _83095 p x) : term90 _83095 p x.
Proof. exact (conj (@lem3184075 _83095 p x h1) (@lem3184083 _83095 x)). Qed.
Lemma lem3184094 {_83095 : Type'} (_32721 : _83095) (p : _83095 -> Prop) (x : _83095) (h1 : term35 _83095 p x) : term89 _83095 p x _32721.
Proof. exact (EQ_MP (@lem3184090 _83095 p x _32721) (@lem3183988 _83095 _32721 p x h1)). Qed.
Lemma lem3184095 {_83095 : Type'} (_32721 : _83095) (p : _83095 -> Prop) (x : _83095) (h1 : term35 _83095 p x) : term89 _83095 p x _32721.
Proof. exact (@lem3184094 _83095 _32721 p x h1). Qed.
Lemma lem3184096 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term35 _83095 p x) : term91 _83095 p x.
Proof. exact (@lem3184095 _83095 x p x h1). Qed.
Lemma lem3184099 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term35 _83095 p x) : False.
Proof. exact (@lem3184096 _83095 p x h1 (@lem3184092 _83095 p x h1)). Qed.
Lemma lem3184100 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term35 _83095 p x) : term84.
Proof. exact (fun h0 : ~ False => @lem3184099 _83095 p x h1). Qed.
Lemma lem3184102 (p : Prop) : (term82 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3184103 : term84 = False.
Proof. exact (@lem3184102 False). Qed.
Lemma lem3184104 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term35 _83095 p x) : False.
Proof. exact (EQ_MP (@lem3184103) (@lem3184100 _83095 p x h1)). Qed.
Lemma lem3184105 {_83095 : Type'} (y : _83095) (p : _83095 -> Prop) (x : _83095) (h1 : term53 _83095 y p x) : False.
Proof. exact (EQ_MP (@lem3184053) (@lem3184050 _83095 y p x h1)). Qed.
Lemma lem3184106 {_83095 : Type'} (y : _83095) (p : _83095 -> Prop) (x : _83095) (h1 : term72 _83095 y p x) : False.
Proof. exact (or_elim (@lem3183936 _83095 y p x h1) (fun h0 : term53 _83095 y p x => @lem3184105 _83095 y p x h0) (fun h0 : term35 _83095 p x => @lem3184104 _83095 p x h0)). Qed.
Lemma lem3184107 {_83095 : Type'} (y : _83095) (p : _83095 -> Prop) (x : _83095) (h1 : term72 _83095 y p x) : (term72 _83095 y p x) = False.
Proof. exact (prop_ext (fun h2 : term72 _83095 y p x => @lem3184106 _83095 y p x h1) (fun h2 : False => @lem3183936 _83095 y p x h1)). Qed.
Lemma lem3184108 {_83095 : Type'} (y : _83095) (p : _83095 -> Prop) (x : _83095) (h1 : term72 _83095 y p x) : False.
Proof. exact (EQ_MP (@lem3184107 _83095 y p x h1) (@lem3183936 _83095 y p x h1)). Qed.
Lemma lem3184109 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term3 _83095 p x) : False.
Proof. exact (ex_elim (@lem3183888 _83095 p x h1) (fun y : _83095 => fun h0 : term74 _83095 p x y => @lem3184108 _83095 y p x h0)). Qed.
Lemma lem3184110 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term3 _83095 p x) : (term3 _83095 p x) = False.
Proof. exact (prop_ext (fun h2 : term3 _83095 p x => @lem3184109 _83095 p x h1) (fun h2 : False => @lem3183717 _83095 p x h1)). Qed.
Lemma lem3184111 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term3 _83095 p x) : False.
Proof. exact (EQ_MP (@lem3184110 _83095 p x h1) (@lem3183717 _83095 p x h1)). Qed.
Lemma lem3184112 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term2 _83095 p x.
Proof. exact (fun h0 : term3 _83095 p x => @lem3184111 _83095 p x h0). Qed.
Lemma lem3184113 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term1 _83095 p x) = (p x).
Proof. exact (EQ_MP (@lem3183716 _83095 p x) (@lem3184112 _83095 p x)). Qed.
Lemma lem3184118 {_83095 : Type'} (x : _83095) : term12 _83095 x.
Proof. exact (fun p : _83095 -> Prop => @lem3184113 _83095 p x). Qed.
Lemma lem3184123 {_83095 : Type'} : term16 _83095.
Proof. exact (fun x : _83095 => @lem3184118 _83095 x). Qed.
Lemma lem3184124 {_83095 : Type'} : term15 _83095.
Proof. exact (EQ_MP (@lem3183712 _83095) (@lem3184123 _83095)). Qed.
Lemma lem3184125 {_83095 : Type'} (x : _83095) : term92 _83095 x.
Proof. exact (@lem3184124 _83095 x). Qed.
Lemma lem3184126 {_83095 : Type'} (x : _83095) : (term92 _83095 x) = (term11 _83095 x).
Proof. exact (eq_refl (term92 _83095 x)). Qed.
Lemma lem3184127 {_83095 : Type'} (x : _83095) : term11 _83095 x.
Proof. exact (EQ_MP (@lem3184126 _83095 x) (@lem3184125 _83095 x)). Qed.
Lemma lem3184128 {_83095 : Type'} (x : _83095) (p : _83095 -> Prop) : term93 _83095 x p.
Proof. exact (@lem3184127 _83095 x p). Qed.
Lemma lem3184129 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term93 _83095 x p) = (term2 _83095 p x).
Proof. exact (eq_refl (term93 _83095 x p)). Qed.
Lemma lem3184130 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term2 _83095 p x.
Proof. exact (EQ_MP (@lem3184129 _83095 p x) (@lem3184128 _83095 x p)). Qed.
Lemma lem3184132 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term2 _83095 p x.
Proof. exact (@lem3183607 _83095 p x (@lem3184130 _83095 p x)). Qed.
Lemma lem3184133 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term3 _83095 p x) : False.
Proof. exact (@lem3184132 _83095 p x (@lem3183591 _83095 p x h1)). Qed.
Lemma lem3184134 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term3 _83095 p x) : (term3 _83095 p x) = False.
Proof. exact (prop_ext (fun h2 : term3 _83095 p x => @lem3184133 _83095 p x h1) (fun h2 : False => @lem3183591 _83095 p x h1)). Qed.
Lemma lem3184135 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) (h1 : term3 _83095 p x) : False.
Proof. exact (EQ_MP (@lem3184134 _83095 p x h1) (@lem3183591 _83095 p x h1)). Qed.
Lemma lem3184136 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term2 _83095 p x.
Proof. exact (fun h0 : term3 _83095 p x => @lem3184135 _83095 p x h0). Qed.
Lemma lem3184137 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term1 _83095 p x) = (p x).
Proof. exact (EQ_MP (@lem3183590 _83095 p x) (@lem3184136 _83095 p x)). Qed.
