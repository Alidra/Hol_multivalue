Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1073760_term_abbrevs.
Require Import option_RECURSION_spec.
Require Import thm0_spec.
Require Import thm1012671_spec.
Require Import thm1073392_spec.
Require Import thm912739_spec.
Lemma lem1073671 {A : Type'} (_17542 : type1161 A) (h1 : (_17542 (@None A)) = (NUMERAL 0)) : (_17542 (@None A)) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1073672 {A : Type'} (_17542 : type1161 A) (h1 : term0 A _17542) : term0 A _17542.
Proof. exact (h1). Qed.
Lemma lem1073673 {A : Type'} (a : A) (_17542 : type1161 A) (h1 : term0 A _17542) : term1 A _17542 a.
Proof. exact (@lem1073672 A _17542 h1 a). Qed.
Lemma lem1073674 {A : Type'} (_17542 : type1161 A) (a : A) : (term1 A _17542 a) = ((term2 A _17542 a) = term3).
Proof. exact (eq_refl (term1 A _17542 a)). Qed.
Lemma lem1073675 {A : Type'} (a : A) (_17542 : type1161 A) (h1 : term0 A _17542) : (term2 A _17542 a) = term3.
Proof. exact (EQ_MP (@lem1073674 A _17542 a) (@lem1073673 A a _17542 h1)). Qed.
Lemma lem1073676 {A : Type'} (_17542 : type1161 A) (h1 : term0 A _17542) : term0 A _17542.
Proof. exact (fun a : A => @lem1073675 A a _17542 h1). Qed.
Lemma lem1073677 {A : Type'} (_17542 : type1161 A) (h1 : term4 A _17542) : term4 A _17542.
Proof. exact (h1). Qed.
Lemma lem1073678 {A : Type'} (_17542 : type1161 A) (h1 : term4 A _17542) : term0 A _17542.
Proof. exact (proj2 (@lem1073677 A _17542 h1)). Qed.
Lemma lem1073679 {A : Type'} (_17542 : type1161 A) (h1 : term4 A _17542) : (_17542 (@None A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1073677 A _17542 h1)). Qed.
Lemma lem1073680 {A : Type'} (_17542 : type1161 A) (h1 : term4 A _17542) : ((_17542 (@None A)) = (NUMERAL 0)) = ((_17542 (@None A)) = (NUMERAL 0)).
Proof. exact (prop_ext (fun h2 : (_17542 (@None A)) = (NUMERAL 0) => @lem1073671 A _17542 h2) (fun h2 : (_17542 (@None A)) = (NUMERAL 0) => @lem1073679 A _17542 h1)). Qed.
Lemma lem1073681 {A : Type'} (_17542 : type1161 A) (h1 : term4 A _17542) : (_17542 (@None A)) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1073680 A _17542 h1) (@lem1073679 A _17542 h1)). Qed.
Lemma lem1073682 {A : Type'} (_17542 : type1161 A) (h1 : term4 A _17542) : (term0 A _17542) = (term0 A _17542).
Proof. exact (prop_ext (fun h2 : term0 A _17542 => @lem1073676 A _17542 h2) (fun h2 : term0 A _17542 => @lem1073678 A _17542 h1)). Qed.
Lemma lem1073683 {A : Type'} (_17542 : type1161 A) (h1 : term4 A _17542) : term0 A _17542.
Proof. exact (EQ_MP (@lem1073682 A _17542 h1) (@lem1073678 A _17542 h1)). Qed.
Lemma lem1073684 {A : Type'} (_17542 : type1161 A) (h1 : term4 A _17542) : term4 A _17542.
Proof. exact (conj (@lem1073681 A _17542 h1) (@lem1073683 A _17542 h1)). Qed.
Lemma lem1073685 {A Z : Type'} (NONE' : Z) : term5 A Z NONE'.
Proof. exact (@lem1070449 A Z NONE'). Qed.
Lemma lem1073686 {A Z : Type'} (NONE' : Z) : (term5 A Z NONE') = (term6 A Z NONE').
Proof. exact (eq_refl (term5 A Z NONE')). Qed.
Lemma lem1073687 {A Z : Type'} (NONE' : Z) : term6 A Z NONE'.
Proof. exact (EQ_MP (@lem1073686 A Z NONE') (@lem1073685 A Z NONE')). Qed.
Lemma lem1073688 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) : term7 A Z NONE' SOME'.
Proof. exact (@lem1073687 A Z NONE' SOME'). Qed.
Lemma lem1073689 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) : (term7 A Z NONE' SOME') = (term8 A Z NONE' SOME').
Proof. exact (eq_refl (term7 A Z NONE' SOME')). Qed.
Lemma lem1073690 {A Z : Type'} (NONE' : Z) (SOME' : A -> Z) : term8 A Z NONE' SOME'.
Proof. exact (EQ_MP (@lem1073689 A Z NONE' SOME') (@lem1073688 A Z NONE' SOME')). Qed.
Lemma lem1073691 {A : Type'} (NONE' : nat) (SOME' : A -> nat) : term9 A NONE' SOME'.
Proof. exact (@lem1073690 A nat NONE' SOME'). Qed.
Lemma lem1073692 {A : Type'} : term10 A.
Proof. exact (@lem1073691 A (NUMERAL 0) (term11 A)). Qed.
Lemma lem1073693 {A : Type'} (a : A) : (term12 A a) = term3.
Proof. exact (eq_refl (term12 A a)). Qed.
Lemma lem1073694 {A : Type'} (fn : type1161 A) (a : A) : (term13 A fn a) = (term13 A fn a).
Proof. exact (eq_refl (term13 A fn a)). Qed.
Lemma lem1073695 {A : Type'} (fn : type1161 A) (a : A) : ((term2 A fn a) = (term12 A a)) = ((term2 A fn a) = term3).
Proof. exact (MK_COMB (@lem1073694 A fn a) (@lem1073693 A a)). Qed.
Lemma lem1073696 {A : Type'} (fn : type1161 A) : (term14 A fn) = (term15 A fn).
Proof. exact (fun_ext (fun a : A => @lem1073695 A fn a)). Qed.
Lemma lem1073697 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1073698 {A : Type'} (fn : type1161 A) : (term16 A fn) = (term0 A fn).
Proof. exact (MK_COMB (@lem1073697 A) (@lem1073696 A fn)). Qed.
Lemma lem1073699 {A : Type'} (fn : type1161 A) : (term17 A fn) = (term17 A fn).
Proof. exact (eq_refl (term17 A fn)). Qed.
Lemma lem1073700 {A : Type'} (fn : type1161 A) : (term18 A fn) = (term4 A fn).
Proof. exact (MK_COMB (@lem1073699 A fn) (@lem1073698 A fn)). Qed.
Lemma lem1073701 {A : Type'} : (term19 A) = (term20 A).
Proof. exact (fun_ext (fun fn : type1161 A => @lem1073700 A fn)). Qed.
Lemma lem1073702 {A : Type'} : (@ex ((option A) -> nat)) = (@ex ((option A) -> nat)).
Proof. exact (eq_refl (@ex ((option A) -> nat))). Qed.
Lemma lem1073703 {A : Type'} : (term10 A) = (term21 A).
Proof. exact (MK_COMB (@lem1073702 A) (@lem1073701 A)). Qed.
Lemma lem1073704 {A : Type'} : term21 A.
Proof. exact (EQ_MP (@lem1073703 A) (@lem1073692 A)). Qed.
Lemma lem1073705 {A : Type'} (_17542 : type1161 A) (h1 : term4 A _17542) : term4 A _17542.
Proof. exact (h1). Qed.
Lemma lem1073706 {A : Type'} (_17542 : type1161 A) (h1 : term4 A _17542) : term0 A _17542.
Proof. exact (proj2 (@lem1073705 A _17542 h1)). Qed.
Lemma lem1073707 {A : Type'} (_17542 : type1161 A) (h1 : term4 A _17542) : (_17542 (@None A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1073705 A _17542 h1)). Qed.
Lemma lem1073708 {A : Type'} (_17542 : type1161 A) (h1 : term4 A _17542) : term4 A _17542.
Proof. exact (conj (@lem1073707 A _17542 h1) (@lem1073706 A _17542 h1)). Qed.
Lemma lem1073709 {A : Type'} (_17542 : type1161 A) (h1 : term4 A _17542) : term21 A.
Proof. exact (ex_intro (term20 A) _17542 (@lem1073708 A _17542 h1)). Qed.
Lemma lem1073710 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (h1). Qed.
Lemma lem1073711 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (ex_elim (@lem1073710 A h1) (fun _17542 : type1161 A => fun h0 : term20 A _17542 => @lem1073709 A _17542 h0)). Qed.
Lemma lem1073712 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (prop_ext (fun h1 : term21 A => @lem1073711 A h1) (fun h1 : term21 A => @lem1073704 A)). Qed.
Lemma lem1073713 {A : Type'} : term21 A.
Proof. exact (EQ_MP (@lem1073712 A) (@lem1073704 A)). Qed.
Lemma lem1073714 {A : Type'} (_17542 : type1161 A) (h1 : term4 A _17542) : term21 A.
Proof. exact (ex_intro (term20 A) _17542 (@lem1073684 A _17542 h1)). Qed.
Lemma lem1073715 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (h1). Qed.
Lemma lem1073716 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (ex_elim (@lem1073715 A h1) (fun _17542 : type1161 A => fun h0 : term20 A _17542 => @lem1073714 A _17542 h0)). Qed.
Lemma lem1073717 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (prop_ext (fun h1 : term21 A => @lem1073716 A h1) (fun h1 : term21 A => @lem1073713 A)). Qed.
Lemma lem1073718 {A : Type'} : term21 A.
Proof. exact (EQ_MP (@lem1073717 A) (@lem1073713 A)). Qed.
Lemma lem1073721 {A : Type'} (_17542 : type1161 A) (h1 : term4 A _17542) : term4 A _17542.
Proof. exact (h1). Qed.
Lemma lem1073722 {A : Type'} (_17542 : type1161 A) (h1 : term4 A _17542) : term21 A.
Proof. exact (ex_intro (term20 A) _17542 (@lem1073721 A _17542 h1)). Qed.
Lemma lem1073723 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (h1). Qed.
Lemma lem1073724 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (ex_elim (@lem1073723 A h1) (fun _17542 : type1161 A => fun h0 : term20 A _17542 => @lem1073722 A _17542 h0)). Qed.
Lemma lem1073725 {A : Type'} : (term21 A) = (term21 A).
Proof. exact (prop_ext (fun h1 : term21 A => @lem1073724 A h1) (fun h1 : term21 A => @lem1073718 A)). Qed.
Lemma lem1073726 {A : Type'} : term21 A.
Proof. exact (EQ_MP (@lem1073725 A) (@lem1073718 A)). Qed.
Lemma lem1073727 {A : Type'} (_17542 : type1161 A) (h1 : term4 A _17542) : term4 A _17542.
Proof. exact (h1). Qed.
Lemma lem1073728 {A : Type'} (_17542 : type1161 A) (h1 : term4 A _17542) : term0 A _17542.
Proof. exact (proj2 (@lem1073727 A _17542 h1)). Qed.
Lemma lem1073730 {A : Type'} (a : A) (_17542 : type1161 A) (h1 : term4 A _17542) : term1 A _17542 a.
Proof. exact (@lem1073728 A _17542 h1 a). Qed.
Lemma lem1073731 {A : Type'} (_17542 : type1161 A) (a : A) : (term1 A _17542 a) = ((term2 A _17542 a) = term3).
Proof. exact (eq_refl (term1 A _17542 a)). Qed.
Lemma lem1073733 {A : Type'} (_17542 : type1161 A) : _17542 = _17542.
Proof. exact (eq_refl _17542). Qed.
Lemma lem1073734 {A : Type'} (a' : A) (h1 : (@None A) = (@Some A a')) : (@None A) = (@Some A a').
Proof. exact (h1). Qed.
Lemma lem1073735 {A : Type'} (_17542 : type1161 A) (a' : A) (h1 : (@None A) = (@Some A a')) : (_17542 (@None A)) = (term2 A _17542 a').
Proof. exact (MK_COMB (@lem1073733 A _17542) (@lem1073734 A a' h1)). Qed.
Lemma lem1073737 {A : Type'} (_17542 : type1161 A) (h1 : term4 A _17542) : (_17542 (@None A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1073727 A _17542 h1)). Qed.
Lemma lem1073738 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1073739 {A : Type'} (_17542 : type1161 A) (h1 : term4 A _17542) : (term22 A _17542) = term23.
Proof. exact (MK_COMB (@lem1073738) (@lem1073737 A _17542 h1)). Qed.
Lemma lem1073741 {A : Type'} (a : A) (_17542 : type1161 A) (h1 : term4 A _17542) : (term2 A _17542 a) = term3.
Proof. exact (EQ_MP (@lem1073731 A _17542 a) (@lem1073730 A a _17542 h1)). Qed.
Lemma lem1073742 {A : Type'} (a : A) (_17542 : type1161 A) (h1 : term4 A _17542) : (term2 A _17542 a) = term3.
Proof. exact (@lem1073741 A a _17542 h1). Qed.
Lemma lem1073743 {A : Type'} (a' : A) (_17542 : type1161 A) (h1 : term4 A _17542) : (term2 A _17542 a') = term3.
Proof. exact (@lem1073742 A a' _17542 h1). Qed.
Lemma lem1073744 {A : Type'} (a' : A) (_17542 : type1161 A) (h1 : term4 A _17542) : ((_17542 (@None A)) = (term2 A _17542 a')) = ((NUMERAL 0) = term3).
Proof. exact (MK_COMB (@lem1073739 A _17542 h1) (@lem1073743 A a' _17542 h1)). Qed.
Lemma lem1073745 {A : Type'} (_17542 : type1161 A) (a' : A) (h1 : term4 A _17542) (h2 : (@None A) = (@Some A a')) : (NUMERAL 0) = term3.
Proof. exact (EQ_MP (@lem1073744 A a' _17542 h1) (@lem1073735 A _17542 a' h2)). Qed.
Lemma lem1073746 : term24 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1073747 (h1 : term24 = (BIT1 0)) : ((NUMERAL 0) = term3) = False.
Proof. exact (@lem1012671 0 0 (BIT1 0) h1). Qed.
Lemma lem1073748 : (term24 = (BIT1 0)) = (((NUMERAL 0) = term3) = False).
Proof. exact (prop_ext (fun h1 : term24 = (BIT1 0) => @lem1073747 h1) (fun h1 : ((NUMERAL 0) = term3) = False => @lem1073746)). Qed.
Lemma lem1073749 : ((NUMERAL 0) = term3) = False.
Proof. exact (EQ_MP (@lem1073748) (@lem1073746)). Qed.
Lemma lem1073750 {A : Type'} (_17542 : type1161 A) (a' : A) (h1 : term4 A _17542) (h2 : (@None A) = (@Some A a')) : False.
Proof. exact (EQ_MP (@lem1073749) (@lem1073745 A _17542 a' h1 h2)). Qed.
Lemma lem1073751 {A : Type'} (a' : A) (_17542 : type1161 A) (h1 : term4 A _17542) : term25 A a'.
Proof. exact (fun h0 : (@None A) = (@Some A a') => @lem1073750 A _17542 a' h1 h0). Qed.
Lemma lem1073753 (a : Prop) : (a -> False) = (~ a).
Proof. exact (EQ_MP (@lem1073392 a) (@lem0)). Qed.
Lemma lem1073754 {A : Type'} (a' : A) : (term25 A a') = (term26 A a').
Proof. exact (@lem1073753 ((@None A) = (@Some A a'))). Qed.
Lemma lem1073755 {A : Type'} (a' : A) (_17542 : type1161 A) (h1 : term4 A _17542) : term26 A a'.
Proof. exact (EQ_MP (@lem1073754 A a') (@lem1073751 A a' _17542 h1)). Qed.
Lemma lem1073756 {A : Type'} (_17542 : type1161 A) (h1 : term4 A _17542) : term27 A.
Proof. exact (fun a' : A => @lem1073755 A a' _17542 h1). Qed.
Lemma lem1073757 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (h1). Qed.
Lemma lem1073758 {A : Type'} (h1 : term21 A) : term27 A.
Proof. exact (ex_elim (@lem1073757 A h1) (fun _17542 : type1161 A => fun h0 : term20 A _17542 => @lem1073756 A _17542 h0)). Qed.
Lemma lem1073759 {A : Type'} : (term21 A) = (term27 A).
Proof. exact (prop_ext (fun h1 : term21 A => @lem1073758 A h1) (fun h1 : term27 A => @lem1073726 A)). Qed.
Lemma lem1073760 {A : Type'} : term27 A.
Proof. exact (EQ_MP (@lem1073759 A) (@lem1073726 A)). Qed.
