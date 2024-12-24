Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_SMALL_SUBSET_IMAGE_term_abbrevs.
Require Import CONJ_ASSOC_spec.
Require Import EXISTS_SMALL_SUBSET_IMAGE_spec.
Require Import NOT_IMP_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Lemma lem4074681 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term0 t1 t2 t3) = (term1 t1 t2 t3)) : (term0 t1 t2 t3) = (term1 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem4074682 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term0 t1 t2 t3) = (term1 t1 t2 t3)) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (SYM (@lem4074681 t1 t2 t3 h1)). Qed.
Lemma lem4074683 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term1 t1 t2 t3) = (term0 t1 t2 t3)) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem4074684 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term1 t1 t2 t3) = (term0 t1 t2 t3)) : (term0 t1 t2 t3) = (term1 t1 t2 t3).
Proof. exact (SYM (@lem4074683 t1 t2 t3 h1)). Qed.
Lemma lem4074685 (t1 : Prop) (t2 : Prop) (t3 : Prop) : ((term0 t1 t2 t3) = (term1 t1 t2 t3)) = ((term1 t1 t2 t3) = (term0 t1 t2 t3)).
Proof. exact (prop_ext (fun h1 : (term0 t1 t2 t3) = (term1 t1 t2 t3) => @lem4074682 t1 t2 t3 h1) (fun h1 : (term1 t1 t2 t3) = (term0 t1 t2 t3) => @lem4074684 t1 t2 t3 h1)). Qed.
Lemma lem4074686 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (fun_ext (fun t3 : Prop => @lem4074685 t1 t2 t3)). Qed.
Lemma lem4074687 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem4074688 (t1 : Prop) (t2 : Prop) : (term4 t1 t2) = (term5 t1 t2).
Proof. exact (MK_COMB (@lem4074687) (@lem4074686 t1 t2)). Qed.
Lemma lem4074689 (t1 : Prop) : (term6 t1) = (term7 t1).
Proof. exact (fun_ext (fun t2 : Prop => @lem4074688 t1 t2)). Qed.
Lemma lem4074690 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem4074691 (t1 : Prop) : (term8 t1) = (term9 t1).
Proof. exact (MK_COMB (@lem4074690) (@lem4074689 t1)). Qed.
Lemma lem4074692 : term10 = term11.
Proof. exact (fun_ext (fun t1 : Prop => @lem4074691 t1)). Qed.
Lemma lem4074693 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem4074694 : term12 = term13.
Proof. exact (MK_COMB (@lem4074693) (@lem4074692)). Qed.
Lemma lem4074695 : term13.
Proof. exact (EQ_MP (@lem4074694) (@lem512)). Qed.
Lemma lem4074696 (t1 : Prop) : term14 t1.
Proof. exact (@lem4074695 t1). Qed.
Lemma lem4074697 (t1 : Prop) : (term14 t1) = (term9 t1).
Proof. exact (eq_refl (term14 t1)). Qed.
Lemma lem4074698 (t1 : Prop) : term9 t1.
Proof. exact (EQ_MP (@lem4074697 t1) (@lem4074696 t1)). Qed.
Lemma lem4074699 (t1 : Prop) (t2 : Prop) : term15 t1 t2.
Proof. exact (@lem4074698 t1 t2). Qed.
Lemma lem4074700 (t1 : Prop) (t2 : Prop) : (term15 t1 t2) = (term5 t1 t2).
Proof. exact (eq_refl (term15 t1 t2)). Qed.
Lemma lem4074701 (t1 : Prop) (t2 : Prop) : term5 t1 t2.
Proof. exact (EQ_MP (@lem4074700 t1 t2) (@lem4074699 t1 t2)). Qed.
Lemma lem4074702 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term16 t1 t2 t3.
Proof. exact (@lem4074701 t1 t2 t3). Qed.
Lemma lem4074703 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term16 t1 t2 t3) = ((term1 t1 t2 t3) = (term0 t1 t2 t3)).
Proof. exact (eq_refl (term16 t1 t2 t3)). Qed.
Lemma lem4074705 {_102289 _102316 : Type'} (P : type686 _102316) : term17 _102289 _102316 P.
Proof. exact (@lem4074677 _102289 _102316 P). Qed.
Lemma lem4074706 {_102289 _102316 : Type'} (P : type686 _102316) : (term17 _102289 _102316 P) = (term18 _102289 _102316 P).
Proof. exact (eq_refl (term17 _102289 _102316 P)). Qed.
Lemma lem4074707 {_102289 _102316 : Type'} (P : type686 _102316) : term18 _102289 _102316 P.
Proof. exact (EQ_MP (@lem4074706 _102289 _102316 P) (@lem4074705 _102289 _102316 P)). Qed.
Lemma lem4074708 {_102289 _102316 : Type'} (P : type686 _102316) (f : _102289 -> _102316) : term19 _102289 _102316 P f.
Proof. exact (@lem4074707 _102289 _102316 P f). Qed.
Lemma lem4074709 {_102289 _102316 : Type'} (P : type686 _102316) (f : _102289 -> _102316) : (term19 _102289 _102316 P f) = (term20 _102289 _102316 P f).
Proof. exact (eq_refl (term19 _102289 _102316 P f)). Qed.
Lemma lem4074710 {_102289 _102316 : Type'} (P : type686 _102316) (f : _102289 -> _102316) : term20 _102289 _102316 P f.
Proof. exact (EQ_MP (@lem4074709 _102289 _102316 P f) (@lem4074708 _102289 _102316 P f)). Qed.
Lemma lem4074711 {_102289 _102316 : Type'} (P : type686 _102316) (f : _102289 -> _102316) (s : _102289 -> Prop) : term21 _102289 _102316 P f s.
Proof. exact (@lem4074710 _102289 _102316 P f s). Qed.
Lemma lem4074712 {_102289 _102316 : Type'} (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term21 _102289 _102316 P f s) = (term22 _102289 _102316 s P f).
Proof. exact (eq_refl (term21 _102289 _102316 P f s)). Qed.
Lemma lem4074713 {_102289 _102316 : Type'} (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : term22 _102289 _102316 s P f.
Proof. exact (EQ_MP (@lem4074712 _102289 _102316 s P f) (@lem4074711 _102289 _102316 P f s)). Qed.
Lemma lem4074714 {_102289 _102316 : Type'} (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) (n : nat) : term23 _102289 _102316 s P f n.
Proof. exact (@lem4074713 _102289 _102316 s P f n). Qed.
Lemma lem4074715 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term23 _102289 _102316 s P f n) = ((term24 _102289 _102316 n f s P) = (term25 _102289 _102316 n s P f)).
Proof. exact (eq_refl (term23 _102289 _102316 s P f n)). Qed.
Lemma lem4074717 (t1 : Prop) : term26 t1.
Proof. exact (@lem10299 t1). Qed.
Lemma lem4074718 (t1 : Prop) : (term26 t1) = (term27 t1).
Proof. exact (eq_refl (term26 t1)). Qed.
Lemma lem4074719 (t1 : Prop) : term27 t1.
Proof. exact (EQ_MP (@lem4074718 t1) (@lem4074717 t1)). Qed.
Lemma lem4074720 (t1 : Prop) (t2 : Prop) : term28 t1 t2.
Proof. exact (@lem4074719 t1 t2). Qed.
Lemma lem4074721 (t1 : Prop) (t2 : Prop) : (term28 t1 t2) = ((term29 t1 t2) = (term30 t1 t2)).
Proof. exact (eq_refl (term28 t1 t2)). Qed.
Lemma lem4074734 (p : Prop) : p = (term31 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4074735 {_102331 : Type'} (p : _102331 -> Prop) : ((term32 _102331 p) = (term33 _102331 p)) = (term34 _102331 p).
Proof. exact (@lem4074734 ((term32 _102331 p) = (term33 _102331 p))). Qed.
Lemma lem4074736 {_102331 : Type'} (p : _102331 -> Prop) : (term34 _102331 p) = ((term32 _102331 p) = (term33 _102331 p)).
Proof. exact (SYM (@lem4074735 _102331 p)). Qed.
Lemma lem4074737 {_102331 : Type'} (p : _102331 -> Prop) (h1 : term35 _102331 p) : term35 _102331 p.
Proof. exact (h1). Qed.
Lemma lem4074740 {_102331 : Type'} (p : _102331 -> Prop) (h1 : term34 _102331 p) : term34 _102331 p.
Proof. exact (h1). Qed.
Lemma lem4074741 {_102331 : Type'} (p : _102331 -> Prop) : term36 _102331 p.
Proof. exact (fun h0 : term34 _102331 p => @lem4074740 _102331 p h0). Qed.
Lemma lem4074742 {_102331 : Type'} (p : _102331 -> Prop) (h1 : term36 _102331 p) : term36 _102331 p.
Proof. exact (h1). Qed.
Lemma lem4074743 {_102331 : Type'} (p : _102331 -> Prop) (h1 : term34 _102331 p) : term34 _102331 p.
Proof. exact (h1). Qed.
Lemma lem4074744 {_102331 : Type'} (p : _102331 -> Prop) (h1 : term34 _102331 p) (h2 : term36 _102331 p) : term34 _102331 p.
Proof. exact (@lem4074742 _102331 p h2 (@lem4074743 _102331 p h1)). Qed.
Lemma lem4074745 {_102331 : Type'} (p : _102331 -> Prop) (h1 : term34 _102331 p) : term37 _102331 p.
Proof. exact (fun h0 : term36 _102331 p => @lem4074744 _102331 p h1 h0). Qed.
Lemma lem4074746 {_102331 : Type'} (p : _102331 -> Prop) (h1 : term36 _102331 p) : term36 _102331 p.
Proof. exact (h1). Qed.
Lemma lem4074747 {_102331 : Type'} (p : _102331 -> Prop) (h1 : term34 _102331 p) (h2 : term36 _102331 p) : term34 _102331 p.
Proof. exact (@lem4074745 _102331 p h1 (@lem4074746 _102331 p h2)). Qed.
Lemma lem4074748 {_102331 : Type'} (p : _102331 -> Prop) (h1 : term36 _102331 p) : term36 _102331 p.
Proof. exact (fun h0 : term34 _102331 p => @lem4074747 _102331 p h0 h1). Qed.
Lemma lem4074749 {_102331 : Type'} (p : _102331 -> Prop) : term38 _102331 p.
Proof. exact (fun h0 : term36 _102331 p => @lem4074748 _102331 p h0). Qed.
Lemma lem4074752 {_102331 : Type'} (p : _102331 -> Prop) : term36 _102331 p.
Proof. exact (@lem4074749 _102331 p (@lem4074741 _102331 p)). Qed.
Lemma lem4074753 {_102331 : Type'} (p : _102331 -> Prop) : term36 _102331 p.
Proof. exact (@lem4074752 _102331 p). Qed.
Lemma lem4074759 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4074760 {_102331 : Type'} (p : _102331 -> Prop) : (term34 _102331 p) = (term39 _102331 p).
Proof. exact (@lem4074759 (term35 _102331 p)). Qed.
Lemma lem4074762 (t : Prop) : (term40 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4074763 {_102331 : Type'} (p : _102331 -> Prop) : (term39 _102331 p) = ((term32 _102331 p) = (term33 _102331 p)).
Proof. exact (@lem4074762 ((term32 _102331 p) = (term33 _102331 p))). Qed.
Lemma lem4074764 {_102331 : Type'} (p : _102331 -> Prop) : (term34 _102331 p) = ((term32 _102331 p) = (term33 _102331 p)).
Proof. exact (TRANS (@lem4074760 _102331 p) (@lem4074763 _102331 p)). Qed.
Lemma lem4074773 {_102331 : Type'} : (term41 _102331) = (term42 _102331).
Proof. exact (fun_ext (fun p : _102331 -> Prop => @lem4074764 _102331 p)). Qed.
Lemma lem4074774 {_102331 : Type'} : (@all (_102331 -> Prop)) = (@all (_102331 -> Prop)).
Proof. exact (eq_refl (@all (_102331 -> Prop))). Qed.
Lemma lem4074783 {_102331 : Type'} : (term43 _102331) = (term44 _102331).
Proof. exact (MK_COMB (@lem4074774 _102331) (@lem4074773 _102331)). Qed.
Lemma lem4074786 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (term45 _102331 p t) = (term45 _102331 p t).
Proof. exact (eq_refl (term45 _102331 p t)). Qed.
Lemma lem4074787 {_102331 : Type'} (p : _102331 -> Prop) : (term46 _102331 p) = (term46 _102331 p).
Proof. exact (fun_ext (fun t : _102331 => @lem4074786 _102331 p t)). Qed.
Lemma lem4074788 {_102331 : Type'} : (@ex _102331) = (@ex _102331).
Proof. exact (eq_refl (@ex _102331)). Qed.
Lemma lem4074789 {_102331 : Type'} (p : _102331 -> Prop) : (term47 _102331 p) = (term47 _102331 p).
Proof. exact (MK_COMB (@lem4074788 _102331) (@lem4074787 _102331 p)). Qed.
Lemma lem4074790 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4074791 {_102331 : Type'} (p : _102331 -> Prop) : (term33 _102331 p) = (term33 _102331 p).
Proof. exact (MK_COMB (@lem4074790) (@lem4074789 _102331 p)). Qed.
Lemma lem4074792 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (p t) = (p t).
Proof. exact (eq_refl (p t)). Qed.
Lemma lem4074793 {_102331 : Type'} (p : _102331 -> Prop) : (term48 _102331 p) = (term48 _102331 p).
Proof. exact (fun_ext (fun t : _102331 => @lem4074792 _102331 p t)). Qed.
Lemma lem4074794 {_102331 : Type'} : (@all _102331) = (@all _102331).
Proof. exact (eq_refl (@all _102331)). Qed.
Lemma lem4074795 {_102331 : Type'} (p : _102331 -> Prop) : (term32 _102331 p) = (term32 _102331 p).
Proof. exact (MK_COMB (@lem4074794 _102331) (@lem4074793 _102331 p)). Qed.
Lemma lem4074796 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4074797 {_102331 : Type'} (p : _102331 -> Prop) : (term49 _102331 p) = (term49 _102331 p).
Proof. exact (MK_COMB (@lem4074796) (@lem4074795 _102331 p)). Qed.
Lemma lem4074798 {_102331 : Type'} (p : _102331 -> Prop) : ((term32 _102331 p) = (term33 _102331 p)) = ((term32 _102331 p) = (term33 _102331 p)).
Proof. exact (MK_COMB (@lem4074797 _102331 p) (@lem4074791 _102331 p)). Qed.
Lemma lem4074799 {_102331 : Type'} : (term42 _102331) = (term42 _102331).
Proof. exact (fun_ext (fun p : _102331 -> Prop => @lem4074798 _102331 p)). Qed.
Lemma lem4074800 {_102331 : Type'} : (@all (_102331 -> Prop)) = (@all (_102331 -> Prop)).
Proof. exact (eq_refl (@all (_102331 -> Prop))). Qed.
Lemma lem4074801 {_102331 : Type'} : (term44 _102331) = (term44 _102331).
Proof. exact (MK_COMB (@lem4074800 _102331) (@lem4074799 _102331)). Qed.
Lemma lem4074822 {_102331 : Type'} : (term43 _102331) = (term44 _102331).
Proof. exact (TRANS (@lem4074783 _102331) (@lem4074801 _102331)). Qed.
Lemma lem4074823 {_102331 : Type'} : (term44 _102331) = (term43 _102331).
Proof. exact (SYM (@lem4074822 _102331)). Qed.
Lemma lem4074825 (p : Prop) : p = (term31 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4074826 {_102331 : Type'} (p : _102331 -> Prop) : ((term32 _102331 p) = (term33 _102331 p)) = (term34 _102331 p).
Proof. exact (@lem4074825 ((term32 _102331 p) = (term33 _102331 p))). Qed.
Lemma lem4074827 {_102331 : Type'} (p : _102331 -> Prop) : (term34 _102331 p) = ((term32 _102331 p) = (term33 _102331 p)).
Proof. exact (SYM (@lem4074826 _102331 p)). Qed.
Lemma lem4074828 {_102331 : Type'} (p : _102331 -> Prop) (h1 : term35 _102331 p) : term35 _102331 p.
Proof. exact (h1). Qed.
Lemma lem4074830 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (p t) = (p t).
Proof. exact (eq_refl (p t)). Qed.
Lemma lem4074831 {_102331 : Type'} (P : _102331 -> Prop) : (term50 _102331 P) = (term47 _102331 P).
Proof. exact (@lem18392 _102331 P). Qed.
Lemma lem4074832 {_102331 : Type'} (p : _102331 -> Prop) : (term51 _102331 p) = (term52 _102331 p).
Proof. exact (@lem4074831 _102331 (term48 _102331 p)). Qed.
Lemma lem4074833 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (term53 _102331 p t) = (p t).
Proof. exact (eq_refl (term53 _102331 p t)). Qed.
Lemma lem4074834 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4074836 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (term54 _102331 p t) = (term45 _102331 p t).
Proof. exact (MK_COMB (@lem4074834) (@lem4074833 _102331 p t)). Qed.
Lemma lem4074837 {_102331 : Type'} (p : _102331 -> Prop) : (term55 _102331 p) = (term46 _102331 p).
Proof. exact (fun_ext (fun t : _102331 => @lem4074836 _102331 p t)). Qed.
Lemma lem4074838 {_102331 : Type'} : (@ex _102331) = (@ex _102331).
Proof. exact (eq_refl (@ex _102331)). Qed.
Lemma lem4074839 {_102331 : Type'} (p : _102331 -> Prop) : (term52 _102331 p) = (term47 _102331 p).
Proof. exact (MK_COMB (@lem4074838 _102331) (@lem4074837 _102331 p)). Qed.
Lemma lem4074840 {_102331 : Type'} (p : _102331 -> Prop) : (term51 _102331 p) = (term47 _102331 p).
Proof. exact (TRANS (@lem4074832 _102331 p) (@lem4074839 _102331 p)). Qed.
Lemma lem4074841 {_102331 : Type'} (p : _102331 -> Prop) : (term48 _102331 p) = (term48 _102331 p).
Proof. exact (fun_ext (fun t : _102331 => @lem4074830 _102331 p t)). Qed.
Lemma lem4074842 {_102331 : Type'} : (@all _102331) = (@all _102331).
Proof. exact (eq_refl (@all _102331)). Qed.
Lemma lem4074843 {_102331 : Type'} (p : _102331 -> Prop) : (term32 _102331 p) = (term32 _102331 p).
Proof. exact (MK_COMB (@lem4074842 _102331) (@lem4074841 _102331 p)). Qed.
Lemma lem4074844 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (term45 _102331 p t) = (term45 _102331 p t).
Proof. exact (eq_refl (term45 _102331 p t)). Qed.
Lemma lem4074847 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (term56 _102331 p t) = (p t).
Proof. exact (@lem16933 (p t)). Qed.
Lemma lem4074848 {_102331 : Type'} (P : _102331 -> Prop) : (term57 _102331 P) = (term58 _102331 P).
Proof. exact (@lem18394 _102331 P). Qed.
Lemma lem4074849 {_102331 : Type'} (p : _102331 -> Prop) : (term33 _102331 p) = (term59 _102331 p).
Proof. exact (@lem4074848 _102331 (term46 _102331 p)). Qed.
Lemma lem4074850 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (term60 _102331 p t) = (term45 _102331 p t).
Proof. exact (eq_refl (term60 _102331 p t)). Qed.
Lemma lem4074851 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4074852 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (term61 _102331 p t) = (term56 _102331 p t).
Proof. exact (MK_COMB (@lem4074851) (@lem4074850 _102331 p t)). Qed.
Lemma lem4074853 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (term61 _102331 p t) = (p t).
Proof. exact (TRANS (@lem4074852 _102331 p t) (@lem4074847 _102331 p t)). Qed.
Lemma lem4074854 {_102331 : Type'} (p : _102331 -> Prop) : (term62 _102331 p) = (term48 _102331 p).
Proof. exact (fun_ext (fun t : _102331 => @lem4074853 _102331 p t)). Qed.
Lemma lem4074855 {_102331 : Type'} : (@all _102331) = (@all _102331).
Proof. exact (eq_refl (@all _102331)). Qed.
Lemma lem4074856 {_102331 : Type'} (p : _102331 -> Prop) : (term59 _102331 p) = (term32 _102331 p).
Proof. exact (MK_COMB (@lem4074855 _102331) (@lem4074854 _102331 p)). Qed.
Lemma lem4074857 {_102331 : Type'} (p : _102331 -> Prop) : (term33 _102331 p) = (term32 _102331 p).
Proof. exact (TRANS (@lem4074849 _102331 p) (@lem4074856 _102331 p)). Qed.
Lemma lem4074858 {_102331 : Type'} (p : _102331 -> Prop) : (term46 _102331 p) = (term46 _102331 p).
Proof. exact (fun_ext (fun t : _102331 => @lem4074844 _102331 p t)). Qed.
Lemma lem4074859 {_102331 : Type'} : (@ex _102331) = (@ex _102331).
Proof. exact (eq_refl (@ex _102331)). Qed.
Lemma lem4074860 {_102331 : Type'} (p : _102331 -> Prop) : (term47 _102331 p) = (term47 _102331 p).
Proof. exact (MK_COMB (@lem4074859 _102331) (@lem4074858 _102331 p)). Qed.
Lemma lem4074861 {_102331 : Type'} (p : _102331 -> Prop) : (term63 _102331 p) = (term47 _102331 p).
Proof. exact (@lem16933 (term47 _102331 p)). Qed.
Lemma lem4074862 {_102331 : Type'} (p : _102331 -> Prop) : (term63 _102331 p) = (term47 _102331 p).
Proof. exact (TRANS (@lem4074861 _102331 p) (@lem4074860 _102331 p)). Qed.
Lemma lem4074863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4074864 {_102331 : Type'} (p : _102331 -> Prop) : (term64 _102331 p) = (term65 _102331 p).
Proof. exact (MK_COMB (@lem4074863) (@lem4074840 _102331 p)). Qed.
Lemma lem4074865 {_102331 : Type'} (p : _102331 -> Prop) : (term66 _102331 p) = (term67 _102331 p).
Proof. exact (MK_COMB (@lem4074864 _102331 p) (@lem4074857 _102331 p)). Qed.
Lemma lem4074866 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4074867 {_102331 : Type'} (p : _102331 -> Prop) : (term68 _102331 p) = (term68 _102331 p).
Proof. exact (MK_COMB (@lem4074866) (@lem4074843 _102331 p)). Qed.
Lemma lem4074868 {_102331 : Type'} (p : _102331 -> Prop) : (term69 _102331 p) = (term70 _102331 p).
Proof. exact (MK_COMB (@lem4074867 _102331 p) (@lem4074862 _102331 p)). Qed.
Lemma lem4074869 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4074870 {_102331 : Type'} (p : _102331 -> Prop) : (term71 _102331 p) = (term72 _102331 p).
Proof. exact (MK_COMB (@lem4074869) (@lem4074868 _102331 p)). Qed.
Lemma lem4074871 {_102331 : Type'} (p : _102331 -> Prop) : (term73 _102331 p) = (term74 _102331 p).
Proof. exact (MK_COMB (@lem4074870 _102331 p) (@lem4074865 _102331 p)). Qed.
Lemma lem4074872 {_102331 : Type'} (p : _102331 -> Prop) : (term35 _102331 p) = (term73 _102331 p).
Proof. exact (@lem17646 (term32 _102331 p) (term33 _102331 p)). Qed.
Lemma lem4074873 {_102331 : Type'} (p : _102331 -> Prop) : (term35 _102331 p) = (term74 _102331 p).
Proof. exact (TRANS (@lem4074872 _102331 p) (@lem4074871 _102331 p)). Qed.
Lemma lem4074892 {A : Type'} (P : Prop) (Q : A -> Prop) : (term75 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4074893 {_102331 : Type'} (P : Prop) (Q : _102331 -> Prop) : (term75 _102331 P Q) = (term76 _102331 P Q).
Proof. exact (@lem4074892 _102331 P Q). Qed.
Lemma lem4074894 {_102331 : Type'} (p : _102331 -> Prop) : (term77 _102331 p) = (term78 _102331 p).
Proof. exact (@lem4074893 _102331 (term32 _102331 p) (term46 _102331 p)). Qed.
Lemma lem4074895 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (term60 _102331 p t) = (term45 _102331 p t).
Proof. exact (eq_refl (term60 _102331 p t)). Qed.
Lemma lem4074896 {_102331 : Type'} (p : _102331 -> Prop) : (term79 _102331 p) = (term46 _102331 p).
Proof. exact (fun_ext (fun t : _102331 => @lem4074895 _102331 p t)). Qed.
Lemma lem4074897 {_102331 : Type'} : (@ex _102331) = (@ex _102331).
Proof. exact (eq_refl (@ex _102331)). Qed.
Lemma lem4074898 {_102331 : Type'} (p : _102331 -> Prop) : (term80 _102331 p) = (term47 _102331 p).
Proof. exact (MK_COMB (@lem4074897 _102331) (@lem4074896 _102331 p)). Qed.
Lemma lem4074899 {_102331 : Type'} (p : _102331 -> Prop) : (term68 _102331 p) = (term68 _102331 p).
Proof. exact (eq_refl (term68 _102331 p)). Qed.
Lemma lem4074900 {_102331 : Type'} (p : _102331 -> Prop) : (term77 _102331 p) = (term70 _102331 p).
Proof. exact (MK_COMB (@lem4074899 _102331 p) (@lem4074898 _102331 p)). Qed.
Lemma lem4074901 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4074902 {_102331 : Type'} (p : _102331 -> Prop) : (term81 _102331 p) = (term82 _102331 p).
Proof. exact (MK_COMB (@lem4074901) (@lem4074900 _102331 p)). Qed.
Lemma lem4074903 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (term60 _102331 p t) = (term45 _102331 p t).
Proof. exact (eq_refl (term60 _102331 p t)). Qed.
Lemma lem4074904 {_102331 : Type'} (p : _102331 -> Prop) : (term68 _102331 p) = (term68 _102331 p).
Proof. exact (eq_refl (term68 _102331 p)). Qed.
Lemma lem4074905 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (term83 _102331 p t) = (term84 _102331 p t).
Proof. exact (MK_COMB (@lem4074904 _102331 p) (@lem4074903 _102331 p t)). Qed.
Lemma lem4074906 {_102331 : Type'} (p : _102331 -> Prop) : (term85 _102331 p) = (term86 _102331 p).
Proof. exact (fun_ext (fun t : _102331 => @lem4074905 _102331 p t)). Qed.
Lemma lem4074907 {_102331 : Type'} : (@ex _102331) = (@ex _102331).
Proof. exact (eq_refl (@ex _102331)). Qed.
Lemma lem4074908 {_102331 : Type'} (p : _102331 -> Prop) : (term78 _102331 p) = (term87 _102331 p).
Proof. exact (MK_COMB (@lem4074907 _102331) (@lem4074906 _102331 p)). Qed.
Lemma lem4074909 {_102331 : Type'} (p : _102331 -> Prop) : ((term77 _102331 p) = (term78 _102331 p)) = ((term70 _102331 p) = (term87 _102331 p)).
Proof. exact (MK_COMB (@lem4074902 _102331 p) (@lem4074908 _102331 p)). Qed.
Lemma lem4074910 {_102331 : Type'} (p : _102331 -> Prop) : (term70 _102331 p) = (term87 _102331 p).
Proof. exact (EQ_MP (@lem4074909 _102331 p) (@lem4074894 _102331 p)). Qed.
Lemma lem4074911 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4074912 {_102331 : Type'} (p : _102331 -> Prop) : (term72 _102331 p) = (term88 _102331 p).
Proof. exact (MK_COMB (@lem4074911) (@lem4074910 _102331 p)). Qed.
Lemma lem4074914 {A : Type'} (P : A -> Prop) (Q : Prop) : (term89 A P Q) = (term90 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4074915 {_102331 : Type'} (P : _102331 -> Prop) (Q : Prop) : (term89 _102331 P Q) = (term90 _102331 P Q).
Proof. exact (@lem4074914 _102331 P Q). Qed.
Lemma lem4074916 {_102331 : Type'} (p : _102331 -> Prop) : (term91 _102331 p) = (term92 _102331 p).
Proof. exact (@lem4074915 _102331 (term46 _102331 p) (term32 _102331 p)). Qed.
Lemma lem4074917 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (term60 _102331 p t) = (term45 _102331 p t).
Proof. exact (eq_refl (term60 _102331 p t)). Qed.
Lemma lem4074918 {_102331 : Type'} (p : _102331 -> Prop) : (term79 _102331 p) = (term46 _102331 p).
Proof. exact (fun_ext (fun t : _102331 => @lem4074917 _102331 p t)). Qed.
Lemma lem4074919 {_102331 : Type'} : (@ex _102331) = (@ex _102331).
Proof. exact (eq_refl (@ex _102331)). Qed.
Lemma lem4074920 {_102331 : Type'} (p : _102331 -> Prop) : (term80 _102331 p) = (term47 _102331 p).
Proof. exact (MK_COMB (@lem4074919 _102331) (@lem4074918 _102331 p)). Qed.
Lemma lem4074921 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4074922 {_102331 : Type'} (p : _102331 -> Prop) : (term93 _102331 p) = (term65 _102331 p).
Proof. exact (MK_COMB (@lem4074921) (@lem4074920 _102331 p)). Qed.
Lemma lem4074923 {_102331 : Type'} (p : _102331 -> Prop) : (term32 _102331 p) = (term32 _102331 p).
Proof. exact (eq_refl (term32 _102331 p)). Qed.
Lemma lem4074924 {_102331 : Type'} (p : _102331 -> Prop) : (term91 _102331 p) = (term67 _102331 p).
Proof. exact (MK_COMB (@lem4074922 _102331 p) (@lem4074923 _102331 p)). Qed.
Lemma lem4074925 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4074926 {_102331 : Type'} (p : _102331 -> Prop) : (term94 _102331 p) = (term95 _102331 p).
Proof. exact (MK_COMB (@lem4074925) (@lem4074924 _102331 p)). Qed.
Lemma lem4074927 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (term60 _102331 p t) = (term45 _102331 p t).
Proof. exact (eq_refl (term60 _102331 p t)). Qed.
Lemma lem4074928 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4074929 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (term96 _102331 p t) = (term97 _102331 p t).
Proof. exact (MK_COMB (@lem4074928) (@lem4074927 _102331 p t)). Qed.
Lemma lem4074930 {_102331 : Type'} (p : _102331 -> Prop) : (term32 _102331 p) = (term32 _102331 p).
Proof. exact (eq_refl (term32 _102331 p)). Qed.
Lemma lem4074931 {_102331 : Type'} (t : _102331) (p : _102331 -> Prop) : (term98 _102331 t p) = (term99 _102331 t p).
Proof. exact (MK_COMB (@lem4074929 _102331 p t) (@lem4074930 _102331 p)). Qed.
Lemma lem4074932 {_102331 : Type'} (p : _102331 -> Prop) : (term100 _102331 p) = (term101 _102331 p).
Proof. exact (fun_ext (fun t : _102331 => @lem4074931 _102331 t p)). Qed.
Lemma lem4074933 {_102331 : Type'} : (@ex _102331) = (@ex _102331).
Proof. exact (eq_refl (@ex _102331)). Qed.
Lemma lem4074934 {_102331 : Type'} (p : _102331 -> Prop) : (term92 _102331 p) = (term102 _102331 p).
Proof. exact (MK_COMB (@lem4074933 _102331) (@lem4074932 _102331 p)). Qed.
Lemma lem4074935 {_102331 : Type'} (p : _102331 -> Prop) : ((term91 _102331 p) = (term92 _102331 p)) = ((term67 _102331 p) = (term102 _102331 p)).
Proof. exact (MK_COMB (@lem4074926 _102331 p) (@lem4074934 _102331 p)). Qed.
Lemma lem4074936 {_102331 : Type'} (p : _102331 -> Prop) : (term67 _102331 p) = (term102 _102331 p).
Proof. exact (EQ_MP (@lem4074935 _102331 p) (@lem4074916 _102331 p)). Qed.
Lemma lem4074937 {_102331 : Type'} (p : _102331 -> Prop) : (term74 _102331 p) = (term103 _102331 p).
Proof. exact (MK_COMB (@lem4074912 _102331 p) (@lem4074936 _102331 p)). Qed.
Lemma lem4074939 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term104 A P Q) = (term105 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4074940 {_102331 : Type'} (P : _102331 -> Prop) (Q : _102331 -> Prop) : (term104 _102331 P Q) = (term105 _102331 P Q).
Proof. exact (@lem4074939 _102331 P Q). Qed.
Lemma lem4074941 {_102331 : Type'} (p : _102331 -> Prop) : (term106 _102331 p) = (term107 _102331 p).
Proof. exact (@lem4074940 _102331 (term86 _102331 p) (term101 _102331 p)). Qed.
Lemma lem4074942 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (term108 _102331 p t) = (term84 _102331 p t).
Proof. exact (eq_refl (term108 _102331 p t)). Qed.
Lemma lem4074943 {_102331 : Type'} (p : _102331 -> Prop) : (term109 _102331 p) = (term86 _102331 p).
Proof. exact (fun_ext (fun t : _102331 => @lem4074942 _102331 p t)). Qed.
Lemma lem4074944 {_102331 : Type'} : (@ex _102331) = (@ex _102331).
Proof. exact (eq_refl (@ex _102331)). Qed.
Lemma lem4074945 {_102331 : Type'} (p : _102331 -> Prop) : (term110 _102331 p) = (term87 _102331 p).
Proof. exact (MK_COMB (@lem4074944 _102331) (@lem4074943 _102331 p)). Qed.
Lemma lem4074946 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4074947 {_102331 : Type'} (p : _102331 -> Prop) : (term111 _102331 p) = (term88 _102331 p).
Proof. exact (MK_COMB (@lem4074946) (@lem4074945 _102331 p)). Qed.
Lemma lem4074948 {_102331 : Type'} (t : _102331) (p : _102331 -> Prop) : (term112 _102331 p t) = (term99 _102331 t p).
Proof. exact (eq_refl (term112 _102331 p t)). Qed.
Lemma lem4074949 {_102331 : Type'} (p : _102331 -> Prop) : (term113 _102331 p) = (term101 _102331 p).
Proof. exact (fun_ext (fun t : _102331 => @lem4074948 _102331 t p)). Qed.
Lemma lem4074950 {_102331 : Type'} : (@ex _102331) = (@ex _102331).
Proof. exact (eq_refl (@ex _102331)). Qed.
Lemma lem4074951 {_102331 : Type'} (p : _102331 -> Prop) : (term114 _102331 p) = (term102 _102331 p).
Proof. exact (MK_COMB (@lem4074950 _102331) (@lem4074949 _102331 p)). Qed.
Lemma lem4074952 {_102331 : Type'} (p : _102331 -> Prop) : (term106 _102331 p) = (term103 _102331 p).
Proof. exact (MK_COMB (@lem4074947 _102331 p) (@lem4074951 _102331 p)). Qed.
Lemma lem4074953 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4074954 {_102331 : Type'} (p : _102331 -> Prop) : (term115 _102331 p) = (term116 _102331 p).
Proof. exact (MK_COMB (@lem4074953) (@lem4074952 _102331 p)). Qed.
Lemma lem4074955 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (term108 _102331 p t) = (term84 _102331 p t).
Proof. exact (eq_refl (term108 _102331 p t)). Qed.
Lemma lem4074956 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4074957 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (term117 _102331 p t) = (term118 _102331 p t).
Proof. exact (MK_COMB (@lem4074956) (@lem4074955 _102331 p t)). Qed.
Lemma lem4074958 {_102331 : Type'} (t : _102331) (p : _102331 -> Prop) : (term112 _102331 p t) = (term99 _102331 t p).
Proof. exact (eq_refl (term112 _102331 p t)). Qed.
Lemma lem4074959 {_102331 : Type'} (t : _102331) (p : _102331 -> Prop) : (term119 _102331 p t) = (term120 _102331 t p).
Proof. exact (MK_COMB (@lem4074957 _102331 p t) (@lem4074958 _102331 t p)). Qed.
Lemma lem4074960 {_102331 : Type'} (p : _102331 -> Prop) : (term121 _102331 p) = (term122 _102331 p).
Proof. exact (fun_ext (fun t : _102331 => @lem4074959 _102331 t p)). Qed.
Lemma lem4074961 {_102331 : Type'} : (@ex _102331) = (@ex _102331).
Proof. exact (eq_refl (@ex _102331)). Qed.
Lemma lem4074962 {_102331 : Type'} (p : _102331 -> Prop) : (term107 _102331 p) = (term123 _102331 p).
Proof. exact (MK_COMB (@lem4074961 _102331) (@lem4074960 _102331 p)). Qed.
Lemma lem4074963 {_102331 : Type'} (p : _102331 -> Prop) : ((term106 _102331 p) = (term107 _102331 p)) = ((term103 _102331 p) = (term123 _102331 p)).
Proof. exact (MK_COMB (@lem4074954 _102331 p) (@lem4074962 _102331 p)). Qed.
Lemma lem4074964 {_102331 : Type'} (p : _102331 -> Prop) : (term103 _102331 p) = (term123 _102331 p).
Proof. exact (EQ_MP (@lem4074963 _102331 p) (@lem4074941 _102331 p)). Qed.
Lemma lem4074966 {_102331 : Type'} (p : _102331 -> Prop) : (term74 _102331 p) = (term123 _102331 p).
Proof. exact (TRANS (@lem4074937 _102331 p) (@lem4074964 _102331 p)). Qed.
Lemma lem4074967 {_102331 : Type'} (p : _102331 -> Prop) : (term35 _102331 p) = (term123 _102331 p).
Proof. exact (TRANS (@lem4074873 _102331 p) (@lem4074966 _102331 p)). Qed.
Lemma lem4074968 {_102331 : Type'} (p : _102331 -> Prop) (h1 : term35 _102331 p) : term123 _102331 p.
Proof. exact (EQ_MP (@lem4074967 _102331 p) (@lem4074828 _102331 p h1)). Qed.
Lemma lem4074969 {_102331 : Type'} (t : _102331) (p : _102331 -> Prop) (h1 : term120 _102331 t p) : term120 _102331 t p.
Proof. exact (h1). Qed.
Lemma lem4074972 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (p t) = (p t).
Proof. exact (eq_refl (p t)). Qed.
Lemma lem4074973 {_102331 : Type'} (p : _102331 -> Prop) : (term48 _102331 p) = (term48 _102331 p).
Proof. exact (fun_ext (fun t : _102331 => @lem4074972 _102331 p t)). Qed.
Lemma lem4074974 {_102331 : Type'} : (@all _102331) = (@all _102331).
Proof. exact (eq_refl (@all _102331)). Qed.
Lemma lem4074975 {_102331 : Type'} (p : _102331 -> Prop) : (term32 _102331 p) = (term32 _102331 p).
Proof. exact (MK_COMB (@lem4074974 _102331) (@lem4074973 _102331 p)). Qed.
Lemma lem4074982 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (term97 _102331 p t) = (term97 _102331 p t).
Proof. exact (eq_refl (term97 _102331 p t)). Qed.
Lemma lem4074983 {_102331 : Type'} (t : _102331) (p : _102331 -> Prop) : (term99 _102331 t p) = (term99 _102331 t p).
Proof. exact (MK_COMB (@lem4074982 _102331 p t) (@lem4074975 _102331 p)). Qed.
Lemma lem4074988 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (term45 _102331 p t) = (term45 _102331 p t).
Proof. exact (eq_refl (term45 _102331 p t)). Qed.
Lemma lem4074991 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (p t) = (p t).
Proof. exact (eq_refl (p t)). Qed.
Lemma lem4074992 {_102331 : Type'} (p : _102331 -> Prop) : (term48 _102331 p) = (term48 _102331 p).
Proof. exact (fun_ext (fun t : _102331 => @lem4074991 _102331 p t)). Qed.
Lemma lem4074993 {_102331 : Type'} : (@all _102331) = (@all _102331).
Proof. exact (eq_refl (@all _102331)). Qed.
Lemma lem4074994 {_102331 : Type'} (p : _102331 -> Prop) : (term32 _102331 p) = (term32 _102331 p).
Proof. exact (MK_COMB (@lem4074993 _102331) (@lem4074992 _102331 p)). Qed.
Lemma lem4074995 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4074996 {_102331 : Type'} (p : _102331 -> Prop) : (term68 _102331 p) = (term68 _102331 p).
Proof. exact (MK_COMB (@lem4074995) (@lem4074994 _102331 p)). Qed.
Lemma lem4074997 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (term84 _102331 p t) = (term84 _102331 p t).
Proof. exact (MK_COMB (@lem4074996 _102331 p) (@lem4074988 _102331 p t)). Qed.
Lemma lem4074998 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4074999 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (term118 _102331 p t) = (term118 _102331 p t).
Proof. exact (MK_COMB (@lem4074998) (@lem4074997 _102331 p t)). Qed.
Lemma lem4075000 {_102331 : Type'} (t : _102331) (p : _102331 -> Prop) : (term120 _102331 t p) = (term120 _102331 t p).
Proof. exact (MK_COMB (@lem4074999 _102331 p t) (@lem4074983 _102331 t p)). Qed.
Lemma lem4075001 {_102331 : Type'} (t : _102331) (p : _102331 -> Prop) (h1 : term120 _102331 t p) : term120 _102331 t p.
Proof. exact (EQ_MP (@lem4075000 _102331 t p) (@lem4074969 _102331 t p h1)). Qed.
Lemma lem4075002 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) (h1 : term84 _102331 p t) : term84 _102331 p t.
Proof. exact (h1). Qed.
Lemma lem4075003 {_102331 : Type'} (t : _102331) (p : _102331 -> Prop) (h1 : term99 _102331 t p) : term99 _102331 t p.
Proof. exact (h1). Qed.
Lemma lem4075005 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) (h1 : term84 _102331 p t) : term32 _102331 p.
Proof. exact (proj1 (@lem4075002 _102331 p t h1)). Qed.
Lemma lem4075006 {_102331 : Type'} (t : _102331) (p : _102331 -> Prop) (h1 : term99 _102331 t p) : term32 _102331 p.
Proof. exact (proj2 (@lem4075003 _102331 t p h1)). Qed.
Lemma lem4075009 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (p t) = (p t).
Proof. exact (eq_refl (p t)). Qed.
Lemma lem4075010 {_102331 : Type'} (p : _102331 -> Prop) : (term48 _102331 p) = (term48 _102331 p).
Proof. exact (fun_ext (fun t : _102331 => @lem4075009 _102331 p t)). Qed.
Lemma lem4075011 {_102331 : Type'} : (@all _102331) = (@all _102331).
Proof. exact (eq_refl (@all _102331)). Qed.
Lemma lem4075013 {_102331 : Type'} (p : _102331 -> Prop) : (term32 _102331 p) = (term32 _102331 p).
Proof. exact (MK_COMB (@lem4075011 _102331) (@lem4075010 _102331 p)). Qed.
Lemma lem4075014 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) (h1 : term84 _102331 p t) : term32 _102331 p.
Proof. exact (EQ_MP (@lem4075013 _102331 p) (@lem4075005 _102331 p t h1)). Qed.
Lemma lem4075024 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (p t) = (p t).
Proof. exact (eq_refl (p t)). Qed.
Lemma lem4075025 {_102331 : Type'} (p : _102331 -> Prop) : (term48 _102331 p) = (term48 _102331 p).
Proof. exact (fun_ext (fun t : _102331 => @lem4075024 _102331 p t)). Qed.
Lemma lem4075026 {_102331 : Type'} : (@all _102331) = (@all _102331).
Proof. exact (eq_refl (@all _102331)). Qed.
Lemma lem4075028 {_102331 : Type'} (p : _102331 -> Prop) : (term32 _102331 p) = (term32 _102331 p).
Proof. exact (MK_COMB (@lem4075026 _102331) (@lem4075025 _102331 p)). Qed.
Lemma lem4075029 {_102331 : Type'} (t : _102331) (p : _102331 -> Prop) (h1 : term99 _102331 t p) : term32 _102331 p.
Proof. exact (EQ_MP (@lem4075028 _102331 p) (@lem4075006 _102331 t p h1)). Qed.
Lemma lem4075030 {_102331 : Type'} (_47865 : _102331) (p : _102331 -> Prop) (t : _102331) (h1 : term84 _102331 p t) : term53 _102331 p _47865.
Proof. exact (@lem4075014 _102331 p t h1 _47865). Qed.
Lemma lem4075031 {_102331 : Type'} (p : _102331 -> Prop) (_47865 : _102331) : (term53 _102331 p _47865) = (p _47865).
Proof. exact (eq_refl (term53 _102331 p _47865)). Qed.
Lemma lem4075033 {_102331 : Type'} (_47866 : _102331) (t : _102331) (p : _102331 -> Prop) (h1 : term99 _102331 t p) : term53 _102331 p _47866.
Proof. exact (@lem4075029 _102331 t p h1 _47866). Qed.
Lemma lem4075034 {_102331 : Type'} (p : _102331 -> Prop) (_47866 : _102331) : (term53 _102331 p _47866) = (p _47866).
Proof. exact (eq_refl (term53 _102331 p _47866)). Qed.
Lemma lem4075039 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) (h1 : term84 _102331 p t) : term45 _102331 p t.
Proof. exact (proj2 (@lem4075002 _102331 p t h1)). Qed.
Lemma lem4075041 {_102331 : Type'} (t : _102331) (p : _102331 -> Prop) (h1 : term99 _102331 t p) : term45 _102331 p t.
Proof. exact (proj1 (@lem4075003 _102331 t p h1)). Qed.
Lemma lem4075045 {_102331 : Type'} (_47865 : _102331) (p : _102331 -> Prop) (t : _102331) (h1 : term84 _102331 p t) : p _47865.
Proof. exact (EQ_MP (@lem4075031 _102331 p _47865) (@lem4075030 _102331 _47865 p t h1)). Qed.
Lemma lem4075046 {_102331 : Type'} (_47865 : _102331) (p : _102331 -> Prop) (t : _102331) (h1 : term84 _102331 p t) : p _47865.
Proof. exact (@lem4075045 _102331 _47865 p t h1). Qed.
Lemma lem4075047 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) (h1 : term84 _102331 p t) : p t.
Proof. exact (@lem4075046 _102331 t p t h1). Qed.
Lemma lem4075048 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) (h1 : term84 _102331 p t) : term124 _102331 p t.
Proof. exact (fun h0 : term45 _102331 p t => @lem4075047 _102331 p t h1). Qed.
Lemma lem4075050 (p : Prop) : (term125 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4075051 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (term124 _102331 p t) = (p t).
Proof. exact (@lem4075050 (p t)). Qed.
Lemma lem4075052 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) (h1 : term84 _102331 p t) : p t.
Proof. exact (EQ_MP (@lem4075051 _102331 p t) (@lem4075048 _102331 p t h1)). Qed.
Lemma lem4075055 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4075057 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (term45 _102331 p t) = (term126 _102331 p t).
Proof. exact (@lem4075055 (p t)). Qed.
Lemma lem4075060 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) (h1 : term84 _102331 p t) : term126 _102331 p t.
Proof. exact (EQ_MP (@lem4075057 _102331 p t) (@lem4075039 _102331 p t h1)). Qed.
Lemma lem4075063 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) (h1 : term84 _102331 p t) : False.
Proof. exact (@lem4075060 _102331 p t h1 (@lem4075052 _102331 p t h1)). Qed.
Lemma lem4075064 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) (h1 : term84 _102331 p t) : term127.
Proof. exact (fun h0 : ~ False => @lem4075063 _102331 p t h1). Qed.
Lemma lem4075066 (p : Prop) : (term125 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4075067 : term127 = False.
Proof. exact (@lem4075066 False). Qed.
Lemma lem4075068 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) (h1 : term84 _102331 p t) : False.
Proof. exact (EQ_MP (@lem4075067) (@lem4075064 _102331 p t h1)). Qed.
Lemma lem4075070 {_102331 : Type'} (_47866 : _102331) (t : _102331) (p : _102331 -> Prop) (h1 : term99 _102331 t p) : p _47866.
Proof. exact (EQ_MP (@lem4075034 _102331 p _47866) (@lem4075033 _102331 _47866 t p h1)). Qed.
Lemma lem4075071 {_102331 : Type'} (_47866 : _102331) (t : _102331) (p : _102331 -> Prop) (h1 : term99 _102331 t p) : p _47866.
Proof. exact (@lem4075070 _102331 _47866 t p h1). Qed.
Lemma lem4075072 {_102331 : Type'} (t : _102331) (p : _102331 -> Prop) (h1 : term99 _102331 t p) : p t.
Proof. exact (@lem4075071 _102331 t t p h1). Qed.
Lemma lem4075073 {_102331 : Type'} (t : _102331) (p : _102331 -> Prop) (h1 : term99 _102331 t p) : term124 _102331 p t.
Proof. exact (fun h0 : term45 _102331 p t => @lem4075072 _102331 t p h1). Qed.
Lemma lem4075075 (p : Prop) : (term125 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4075076 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (term124 _102331 p t) = (p t).
Proof. exact (@lem4075075 (p t)). Qed.
Lemma lem4075077 {_102331 : Type'} (t : _102331) (p : _102331 -> Prop) (h1 : term99 _102331 t p) : p t.
Proof. exact (EQ_MP (@lem4075076 _102331 p t) (@lem4075073 _102331 t p h1)). Qed.
Lemma lem4075080 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4075082 {_102331 : Type'} (p : _102331 -> Prop) (t : _102331) : (term45 _102331 p t) = (term126 _102331 p t).
Proof. exact (@lem4075080 (p t)). Qed.
Lemma lem4075085 {_102331 : Type'} (t : _102331) (p : _102331 -> Prop) (h1 : term99 _102331 t p) : term126 _102331 p t.
Proof. exact (EQ_MP (@lem4075082 _102331 p t) (@lem4075041 _102331 t p h1)). Qed.
Lemma lem4075088 {_102331 : Type'} (t : _102331) (p : _102331 -> Prop) (h1 : term99 _102331 t p) : False.
Proof. exact (@lem4075085 _102331 t p h1 (@lem4075077 _102331 t p h1)). Qed.
Lemma lem4075089 {_102331 : Type'} (t : _102331) (p : _102331 -> Prop) (h1 : term99 _102331 t p) : term127.
Proof. exact (fun h0 : ~ False => @lem4075088 _102331 t p h1). Qed.
Lemma lem4075091 (p : Prop) : (term125 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4075092 : term127 = False.
Proof. exact (@lem4075091 False). Qed.
Lemma lem4075093 {_102331 : Type'} (t : _102331) (p : _102331 -> Prop) (h1 : term99 _102331 t p) : False.
Proof. exact (EQ_MP (@lem4075092) (@lem4075089 _102331 t p h1)). Qed.
Lemma lem4075094 {_102331 : Type'} (t : _102331) (p : _102331 -> Prop) (h1 : term120 _102331 t p) : False.
Proof. exact (or_elim (@lem4075001 _102331 t p h1) (fun h0 : term84 _102331 p t => @lem4075068 _102331 p t h0) (fun h0 : term99 _102331 t p => @lem4075093 _102331 t p h0)). Qed.
Lemma lem4075095 {_102331 : Type'} (t : _102331) (p : _102331 -> Prop) (h1 : term120 _102331 t p) : (term120 _102331 t p) = False.
Proof. exact (prop_ext (fun h2 : term120 _102331 t p => @lem4075094 _102331 t p h1) (fun h2 : False => @lem4075001 _102331 t p h1)). Qed.
Lemma lem4075096 {_102331 : Type'} (t : _102331) (p : _102331 -> Prop) (h1 : term120 _102331 t p) : False.
Proof. exact (EQ_MP (@lem4075095 _102331 t p h1) (@lem4075001 _102331 t p h1)). Qed.
Lemma lem4075097 {_102331 : Type'} (p : _102331 -> Prop) (h1 : term35 _102331 p) : False.
Proof. exact (ex_elim (@lem4074968 _102331 p h1) (fun t : _102331 => fun h0 : term122 _102331 p t => @lem4075096 _102331 t p h0)). Qed.
Lemma lem4075098 {_102331 : Type'} (p : _102331 -> Prop) (h1 : term35 _102331 p) : (term35 _102331 p) = False.
Proof. exact (prop_ext (fun h2 : term35 _102331 p => @lem4075097 _102331 p h1) (fun h2 : False => @lem4074828 _102331 p h1)). Qed.
Lemma lem4075099 {_102331 : Type'} (p : _102331 -> Prop) (h1 : term35 _102331 p) : False.
Proof. exact (EQ_MP (@lem4075098 _102331 p h1) (@lem4074828 _102331 p h1)). Qed.
Lemma lem4075100 {_102331 : Type'} (p : _102331 -> Prop) : term34 _102331 p.
Proof. exact (fun h0 : term35 _102331 p => @lem4075099 _102331 p h0). Qed.
Lemma lem4075101 {_102331 : Type'} (p : _102331 -> Prop) : (term32 _102331 p) = (term33 _102331 p).
Proof. exact (EQ_MP (@lem4074827 _102331 p) (@lem4075100 _102331 p)). Qed.
Lemma lem4075106 {_102331 : Type'} : term44 _102331.
Proof. exact (fun p : _102331 -> Prop => @lem4075101 _102331 p). Qed.
Lemma lem4075107 {_102331 : Type'} : term43 _102331.
Proof. exact (EQ_MP (@lem4074823 _102331) (@lem4075106 _102331)). Qed.
Lemma lem4075108 {_102331 : Type'} (p : _102331 -> Prop) : term128 _102331 p.
Proof. exact (@lem4075107 _102331 p). Qed.
Lemma lem4075109 {_102331 : Type'} (p : _102331 -> Prop) : (term128 _102331 p) = (term34 _102331 p).
Proof. exact (eq_refl (term128 _102331 p)). Qed.
Lemma lem4075110 {_102331 : Type'} (p : _102331 -> Prop) : term34 _102331 p.
Proof. exact (EQ_MP (@lem4075109 _102331 p) (@lem4075108 _102331 p)). Qed.
Lemma lem4075112 {_102331 : Type'} (p : _102331 -> Prop) : term34 _102331 p.
Proof. exact (@lem4074753 _102331 p (@lem4075110 _102331 p)). Qed.
Lemma lem4075113 {_102331 : Type'} (p : _102331 -> Prop) (h1 : term35 _102331 p) : False.
Proof. exact (@lem4075112 _102331 p (@lem4074737 _102331 p h1)). Qed.
Lemma lem4075114 {_102331 : Type'} (p : _102331 -> Prop) (h1 : term35 _102331 p) : (term35 _102331 p) = False.
Proof. exact (prop_ext (fun h2 : term35 _102331 p => @lem4075113 _102331 p h1) (fun h2 : False => @lem4074737 _102331 p h1)). Qed.
Lemma lem4075115 {_102331 : Type'} (p : _102331 -> Prop) (h1 : term35 _102331 p) : False.
Proof. exact (EQ_MP (@lem4075114 _102331 p h1) (@lem4074737 _102331 p h1)). Qed.
Lemma lem4075116 {_102331 : Type'} (p : _102331 -> Prop) : term34 _102331 p.
Proof. exact (fun h0 : term35 _102331 p => @lem4075115 _102331 p h0). Qed.
Lemma lem4075125 {_102331 : Type'} (p : _102331 -> Prop) : (term32 _102331 p) = (term33 _102331 p).
Proof. exact (EQ_MP (@lem4074736 _102331 p) (@lem4075116 _102331 p)). Qed.
Lemma lem4075126 {_102400 : Type'} (p : type686 _102400) : (term129 _102400 p) = (term130 _102400 p).
Proof. exact (@lem4075125 (_102400 -> Prop) p). Qed.
Lemma lem4075127 {_102373 _102400 : Type'} (n : nat) (f : _102373 -> _102400) (s : _102373 -> Prop) (P : type686 _102400) : (term131 _102373 _102400 n f s P) = (term132 _102373 _102400 n f s P).
Proof. exact (@lem4075126 _102400 (term133 _102373 _102400 n f s P)). Qed.
Lemma lem4075128 {_102373 _102400 : Type'} (n : nat) (f : _102373 -> _102400) (s : _102373 -> Prop) (P : type686 _102400) (t : _102400 -> Prop) : (term134 _102373 _102400 n f s P t) = (term135 _102373 _102400 n f s P t).
Proof. exact (eq_refl (term134 _102373 _102400 n f s P t)). Qed.
Lemma lem4075129 {_102373 _102400 : Type'} (n : nat) (f : _102373 -> _102400) (s : _102373 -> Prop) (P : type686 _102400) : (term136 _102373 _102400 n f s P) = (term133 _102373 _102400 n f s P).
Proof. exact (fun_ext (fun t : _102400 -> Prop => @lem4075128 _102373 _102400 n f s P t)). Qed.
Lemma lem4075130 {_102400 : Type'} : (@all (_102400 -> Prop)) = (@all (_102400 -> Prop)).
Proof. exact (eq_refl (@all (_102400 -> Prop))). Qed.
Lemma lem4075131 {_102373 _102400 : Type'} (n : nat) (f : _102373 -> _102400) (s : _102373 -> Prop) (P : type686 _102400) : (term131 _102373 _102400 n f s P) = (term137 _102373 _102400 n f s P).
Proof. exact (MK_COMB (@lem4075130 _102400) (@lem4075129 _102373 _102400 n f s P)). Qed.
Lemma lem4075132 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4075133 {_102373 _102400 : Type'} (n : nat) (f : _102373 -> _102400) (s : _102373 -> Prop) (P : type686 _102400) : (term138 _102373 _102400 n f s P) = (term139 _102373 _102400 n f s P).
Proof. exact (MK_COMB (@lem4075132) (@lem4075131 _102373 _102400 n f s P)). Qed.
Lemma lem4075134 {_102373 _102400 : Type'} (n : nat) (f : _102373 -> _102400) (s : _102373 -> Prop) (P : type686 _102400) (t : _102400 -> Prop) : (term134 _102373 _102400 n f s P t) = (term135 _102373 _102400 n f s P t).
Proof. exact (eq_refl (term134 _102373 _102400 n f s P t)). Qed.
Lemma lem4075135 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4075136 {_102373 _102400 : Type'} (n : nat) (f : _102373 -> _102400) (s : _102373 -> Prop) (P : type686 _102400) (t : _102400 -> Prop) : (term140 _102373 _102400 n f s P t) = (term141 _102373 _102400 n f s P t).
Proof. exact (MK_COMB (@lem4075135) (@lem4075134 _102373 _102400 n f s P t)). Qed.
Lemma lem4075137 {_102373 _102400 : Type'} (n : nat) (f : _102373 -> _102400) (s : _102373 -> Prop) (P : type686 _102400) : (term142 _102373 _102400 n f s P) = (term143 _102373 _102400 n f s P).
Proof. exact (fun_ext (fun t : _102400 -> Prop => @lem4075136 _102373 _102400 n f s P t)). Qed.
Lemma lem4075138 {_102400 : Type'} : (@ex (_102400 -> Prop)) = (@ex (_102400 -> Prop)).
Proof. exact (eq_refl (@ex (_102400 -> Prop))). Qed.
Lemma lem4075139 {_102373 _102400 : Type'} (n : nat) (f : _102373 -> _102400) (s : _102373 -> Prop) (P : type686 _102400) : (term144 _102373 _102400 n f s P) = (term145 _102373 _102400 n f s P).
Proof. exact (MK_COMB (@lem4075138 _102400) (@lem4075137 _102373 _102400 n f s P)). Qed.
Lemma lem4075140 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4075141 {_102373 _102400 : Type'} (n : nat) (f : _102373 -> _102400) (s : _102373 -> Prop) (P : type686 _102400) : (term132 _102373 _102400 n f s P) = (term146 _102373 _102400 n f s P).
Proof. exact (MK_COMB (@lem4075140) (@lem4075139 _102373 _102400 n f s P)). Qed.
Lemma lem4075142 {_102373 _102400 : Type'} (n : nat) (f : _102373 -> _102400) (s : _102373 -> Prop) (P : type686 _102400) : ((term131 _102373 _102400 n f s P) = (term132 _102373 _102400 n f s P)) = ((term137 _102373 _102400 n f s P) = (term146 _102373 _102400 n f s P)).
Proof. exact (MK_COMB (@lem4075133 _102373 _102400 n f s P) (@lem4075141 _102373 _102400 n f s P)). Qed.
Lemma lem4075143 {_102373 _102400 : Type'} (n : nat) (f : _102373 -> _102400) (s : _102373 -> Prop) (P : type686 _102400) : (term137 _102373 _102400 n f s P) = (term146 _102373 _102400 n f s P).
Proof. exact (EQ_MP (@lem4075142 _102373 _102400 n f s P) (@lem4075127 _102373 _102400 n f s P)). Qed.
Lemma lem4075144 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4075145 {_102373 _102400 : Type'} (n : nat) (f : _102373 -> _102400) (s : _102373 -> Prop) (P : type686 _102400) : (term139 _102373 _102400 n f s P) = (term147 _102373 _102400 n f s P).
Proof. exact (MK_COMB (@lem4075144) (@lem4075143 _102373 _102400 n f s P)). Qed.
Lemma lem4075151 {_102331 : Type'} (p : _102331 -> Prop) : (term32 _102331 p) = (term33 _102331 p).
Proof. exact (EQ_MP (@lem4074736 _102331 p) (@lem4075116 _102331 p)). Qed.
Lemma lem4075152 {_102373 : Type'} (p : type686 _102373) : (term129 _102373 p) = (term130 _102373 p).
Proof. exact (@lem4075151 (_102373 -> Prop) p). Qed.
Lemma lem4075153 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : (term148 _102373 _102400 n s P f) = (term149 _102373 _102400 n s P f).
Proof. exact (@lem4075152 _102373 (term150 _102373 _102400 n s P f)). Qed.
Lemma lem4075154 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) (t : _102373 -> Prop) : (term151 _102373 _102400 n s P f t) = (term152 _102373 _102400 n s P f t).
Proof. exact (eq_refl (term151 _102373 _102400 n s P f t)). Qed.
Lemma lem4075155 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : (term153 _102373 _102400 n s P f) = (term150 _102373 _102400 n s P f).
Proof. exact (fun_ext (fun t : _102373 -> Prop => @lem4075154 _102373 _102400 n s P f t)). Qed.
Lemma lem4075156 {_102373 : Type'} : (@all (_102373 -> Prop)) = (@all (_102373 -> Prop)).
Proof. exact (eq_refl (@all (_102373 -> Prop))). Qed.
Lemma lem4075157 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : (term148 _102373 _102400 n s P f) = (term154 _102373 _102400 n s P f).
Proof. exact (MK_COMB (@lem4075156 _102373) (@lem4075155 _102373 _102400 n s P f)). Qed.
Lemma lem4075158 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4075159 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : (term155 _102373 _102400 n s P f) = (term156 _102373 _102400 n s P f).
Proof. exact (MK_COMB (@lem4075158) (@lem4075157 _102373 _102400 n s P f)). Qed.
Lemma lem4075160 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) (t : _102373 -> Prop) : (term151 _102373 _102400 n s P f t) = (term152 _102373 _102400 n s P f t).
Proof. exact (eq_refl (term151 _102373 _102400 n s P f t)). Qed.
Lemma lem4075161 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4075162 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) (t : _102373 -> Prop) : (term157 _102373 _102400 n s P f t) = (term158 _102373 _102400 n s P f t).
Proof. exact (MK_COMB (@lem4075161) (@lem4075160 _102373 _102400 n s P f t)). Qed.
Lemma lem4075163 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : (term159 _102373 _102400 n s P f) = (term160 _102373 _102400 n s P f).
Proof. exact (fun_ext (fun t : _102373 -> Prop => @lem4075162 _102373 _102400 n s P f t)). Qed.
Lemma lem4075164 {_102373 : Type'} : (@ex (_102373 -> Prop)) = (@ex (_102373 -> Prop)).
Proof. exact (eq_refl (@ex (_102373 -> Prop))). Qed.
Lemma lem4075165 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : (term161 _102373 _102400 n s P f) = (term162 _102373 _102400 n s P f).
Proof. exact (MK_COMB (@lem4075164 _102373) (@lem4075163 _102373 _102400 n s P f)). Qed.
Lemma lem4075166 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4075167 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : (term149 _102373 _102400 n s P f) = (term163 _102373 _102400 n s P f).
Proof. exact (MK_COMB (@lem4075166) (@lem4075165 _102373 _102400 n s P f)). Qed.
Lemma lem4075168 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : ((term148 _102373 _102400 n s P f) = (term149 _102373 _102400 n s P f)) = ((term154 _102373 _102400 n s P f) = (term163 _102373 _102400 n s P f)).
Proof. exact (MK_COMB (@lem4075159 _102373 _102400 n s P f) (@lem4075167 _102373 _102400 n s P f)). Qed.
Lemma lem4075169 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : (term154 _102373 _102400 n s P f) = (term163 _102373 _102400 n s P f).
Proof. exact (EQ_MP (@lem4075168 _102373 _102400 n s P f) (@lem4075153 _102373 _102400 n s P f)). Qed.
Lemma lem4075170 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : ((term137 _102373 _102400 n f s P) = (term154 _102373 _102400 n s P f)) = ((term146 _102373 _102400 n f s P) = (term163 _102373 _102400 n s P f)).
Proof. exact (MK_COMB (@lem4075145 _102373 _102400 n f s P) (@lem4075169 _102373 _102400 n s P f)). Qed.
Lemma lem4075171 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : ((term146 _102373 _102400 n f s P) = (term163 _102373 _102400 n s P f)) = ((term137 _102373 _102400 n f s P) = (term154 _102373 _102400 n s P f)).
Proof. exact (SYM (@lem4075170 _102373 _102400 n s P f)). Qed.
Lemma lem4075179 (t1 : Prop) (t2 : Prop) : (term29 t1 t2) = (term30 t1 t2).
Proof. exact (EQ_MP (@lem4074721 t1 t2) (@lem4074720 t1 t2)). Qed.
Lemma lem4075180 {_102373 _102400 : Type'} (n : nat) (f : _102373 -> _102400) (s : _102373 -> Prop) (P : type686 _102400) (t : _102400 -> Prop) : (term141 _102373 _102400 n f s P t) = (term164 _102373 _102400 n f s P t).
Proof. exact (@lem4075179 (term165 _102373 _102400 n t f s) (P t)). Qed.
Lemma lem4075182 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (EQ_MP (@lem4074703 t1 t2 t3) (@lem4074702 t1 t2 t3)). Qed.
Lemma lem4075183 {_102373 _102400 : Type'} (n : nat) (f : _102373 -> _102400) (s : _102373 -> Prop) (P : type686 _102400) (t : _102400 -> Prop) : (term164 _102373 _102400 n f s P t) = (term166 _102373 _102400 n f s P t).
Proof. exact (@lem4075182 (@FINITE _102400 t) (term167 _102373 _102400 n t f s) (term168 _102400 P t)). Qed.
Lemma lem4075186 {_102373 _102400 : Type'} (n : nat) (f : _102373 -> _102400) (s : _102373 -> Prop) (P : type686 _102400) (t : _102400 -> Prop) : (term141 _102373 _102400 n f s P t) = (term166 _102373 _102400 n f s P t).
Proof. exact (TRANS (@lem4075180 _102373 _102400 n f s P t) (@lem4075183 _102373 _102400 n f s P t)). Qed.
Lemma lem4075188 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (EQ_MP (@lem4074703 t1 t2 t3) (@lem4074702 t1 t2 t3)). Qed.
Lemma lem4075189 {_102373 _102400 : Type'} (n : nat) (f : _102373 -> _102400) (s : _102373 -> Prop) (P : type686 _102400) (t : _102400 -> Prop) : (term169 _102373 _102400 n f s P t) = (term170 _102373 _102400 n f s P t).
Proof. exact (@lem4075188 (term171 _102400 t n) (term172 _102373 _102400 t f s) (term168 _102400 P t)). Qed.
Lemma lem4075194 {_102400 : Type'} (t : _102400 -> Prop) : (term173 _102400 t) = (term173 _102400 t).
Proof. exact (eq_refl (term173 _102400 t)). Qed.
Lemma lem4075195 {_102373 _102400 : Type'} (n : nat) (f : _102373 -> _102400) (s : _102373 -> Prop) (P : type686 _102400) (t : _102400 -> Prop) : (term166 _102373 _102400 n f s P t) = (term174 _102373 _102400 n f s P t).
Proof. exact (MK_COMB (@lem4075194 _102400 t) (@lem4075189 _102373 _102400 n f s P t)). Qed.
Lemma lem4075198 {_102373 _102400 : Type'} (n : nat) (f : _102373 -> _102400) (s : _102373 -> Prop) (P : type686 _102400) (t : _102400 -> Prop) : (term141 _102373 _102400 n f s P t) = (term174 _102373 _102400 n f s P t).
Proof. exact (TRANS (@lem4075186 _102373 _102400 n f s P t) (@lem4075195 _102373 _102400 n f s P t)). Qed.
Lemma lem4075199 {_102373 _102400 : Type'} (n : nat) (f : _102373 -> _102400) (s : _102373 -> Prop) (P : type686 _102400) : (term143 _102373 _102400 n f s P) = (term175 _102373 _102400 n f s P).
Proof. exact (fun_ext (fun t : _102400 -> Prop => @lem4075198 _102373 _102400 n f s P t)). Qed.
Lemma lem4075200 {_102400 : Type'} : (@ex (_102400 -> Prop)) = (@ex (_102400 -> Prop)).
Proof. exact (eq_refl (@ex (_102400 -> Prop))). Qed.
Lemma lem4075201 {_102373 _102400 : Type'} (n : nat) (f : _102373 -> _102400) (s : _102373 -> Prop) (P : type686 _102400) : (term145 _102373 _102400 n f s P) = (term176 _102373 _102400 n f s P).
Proof. exact (MK_COMB (@lem4075200 _102400) (@lem4075199 _102373 _102400 n f s P)). Qed.
Lemma lem4075203 {_102289 _102316 : Type'} (n : nat) (s : _102289 -> Prop) (P : type686 _102316) (f : _102289 -> _102316) : (term24 _102289 _102316 n f s P) = (term25 _102289 _102316 n s P f).
Proof. exact (EQ_MP (@lem4074715 _102289 _102316 n s P f) (@lem4074714 _102289 _102316 s P f n)). Qed.
Lemma lem4075204 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : (term24 _102373 _102400 n f s P) = (term25 _102373 _102400 n s P f).
Proof. exact (@lem4075203 _102373 _102400 n s P f). Qed.
Lemma lem4075205 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : (term177 _102373 _102400 n f s P) = (term178 _102373 _102400 n s P f).
Proof. exact (@lem4075204 _102373 _102400 n s (term179 _102400 P) f). Qed.
Lemma lem4075206 {_102400 : Type'} (P : type686 _102400) (t : _102400 -> Prop) : (term180 _102400 P t) = (term168 _102400 P t).
Proof. exact (eq_refl (term180 _102400 P t)). Qed.
Lemma lem4075207 {_102373 _102400 : Type'} (t : _102400 -> Prop) (f : _102373 -> _102400) (s : _102373 -> Prop) : (term181 _102373 _102400 t f s) = (term181 _102373 _102400 t f s).
Proof. exact (eq_refl (term181 _102373 _102400 t f s)). Qed.
Lemma lem4075208 {_102373 _102400 : Type'} (f : _102373 -> _102400) (s : _102373 -> Prop) (P : type686 _102400) (t : _102400 -> Prop) : (term182 _102373 _102400 f s P t) = (term183 _102373 _102400 f s P t).
Proof. exact (MK_COMB (@lem4075207 _102373 _102400 t f s) (@lem4075206 _102400 P t)). Qed.
Lemma lem4075209 {_102400 : Type'} (t : _102400 -> Prop) (n : nat) : (term184 _102400 t n) = (term184 _102400 t n).
Proof. exact (eq_refl (term184 _102400 t n)). Qed.
Lemma lem4075210 {_102373 _102400 : Type'} (n : nat) (f : _102373 -> _102400) (s : _102373 -> Prop) (P : type686 _102400) (t : _102400 -> Prop) : (term185 _102373 _102400 n f s P t) = (term170 _102373 _102400 n f s P t).
Proof. exact (MK_COMB (@lem4075209 _102400 t n) (@lem4075208 _102373 _102400 f s P t)). Qed.
Lemma lem4075211 {_102400 : Type'} (t : _102400 -> Prop) : (term173 _102400 t) = (term173 _102400 t).
Proof. exact (eq_refl (term173 _102400 t)). Qed.
Lemma lem4075212 {_102373 _102400 : Type'} (n : nat) (f : _102373 -> _102400) (s : _102373 -> Prop) (P : type686 _102400) (t : _102400 -> Prop) : (term186 _102373 _102400 n f s P t) = (term174 _102373 _102400 n f s P t).
Proof. exact (MK_COMB (@lem4075211 _102400 t) (@lem4075210 _102373 _102400 n f s P t)). Qed.
Lemma lem4075213 {_102373 _102400 : Type'} (n : nat) (f : _102373 -> _102400) (s : _102373 -> Prop) (P : type686 _102400) : (term187 _102373 _102400 n f s P) = (term175 _102373 _102400 n f s P).
Proof. exact (fun_ext (fun t : _102400 -> Prop => @lem4075212 _102373 _102400 n f s P t)). Qed.
Lemma lem4075214 {_102400 : Type'} : (@ex (_102400 -> Prop)) = (@ex (_102400 -> Prop)).
Proof. exact (eq_refl (@ex (_102400 -> Prop))). Qed.
Lemma lem4075215 {_102373 _102400 : Type'} (n : nat) (f : _102373 -> _102400) (s : _102373 -> Prop) (P : type686 _102400) : (term177 _102373 _102400 n f s P) = (term176 _102373 _102400 n f s P).
Proof. exact (MK_COMB (@lem4075214 _102400) (@lem4075213 _102373 _102400 n f s P)). Qed.
Lemma lem4075216 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4075217 {_102373 _102400 : Type'} (n : nat) (f : _102373 -> _102400) (s : _102373 -> Prop) (P : type686 _102400) : (term188 _102373 _102400 n f s P) = (term189 _102373 _102400 n f s P).
Proof. exact (MK_COMB (@lem4075216) (@lem4075215 _102373 _102400 n f s P)). Qed.
Lemma lem4075218 {_102373 _102400 : Type'} (P : type686 _102400) (f : _102373 -> _102400) (t : _102373 -> Prop) : (term190 _102373 _102400 P f t) = (term191 _102373 _102400 P f t).
Proof. exact (eq_refl (term190 _102373 _102400 P f t)). Qed.
Lemma lem4075219 {_102373 : Type'} (t : _102373 -> Prop) (s : _102373 -> Prop) : (term192 _102373 t s) = (term192 _102373 t s).
Proof. exact (eq_refl (term192 _102373 t s)). Qed.
Lemma lem4075220 {_102373 _102400 : Type'} (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) (t : _102373 -> Prop) : (term193 _102373 _102400 s P f t) = (term194 _102373 _102400 s P f t).
Proof. exact (MK_COMB (@lem4075219 _102373 t s) (@lem4075218 _102373 _102400 P f t)). Qed.
Lemma lem4075221 {_102373 : Type'} (t : _102373 -> Prop) (n : nat) : (term184 _102373 t n) = (term184 _102373 t n).
Proof. exact (eq_refl (term184 _102373 t n)). Qed.
Lemma lem4075222 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) (t : _102373 -> Prop) : (term195 _102373 _102400 n s P f t) = (term196 _102373 _102400 n s P f t).
Proof. exact (MK_COMB (@lem4075221 _102373 t n) (@lem4075220 _102373 _102400 s P f t)). Qed.
Lemma lem4075223 {_102373 : Type'} (t : _102373 -> Prop) : (term173 _102373 t) = (term173 _102373 t).
Proof. exact (eq_refl (term173 _102373 t)). Qed.
Lemma lem4075224 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) (t : _102373 -> Prop) : (term197 _102373 _102400 n s P f t) = (term198 _102373 _102400 n s P f t).
Proof. exact (MK_COMB (@lem4075223 _102373 t) (@lem4075222 _102373 _102400 n s P f t)). Qed.
Lemma lem4075225 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : (term199 _102373 _102400 n s P f) = (term200 _102373 _102400 n s P f).
Proof. exact (fun_ext (fun t : _102373 -> Prop => @lem4075224 _102373 _102400 n s P f t)). Qed.
Lemma lem4075226 {_102373 : Type'} : (@ex (_102373 -> Prop)) = (@ex (_102373 -> Prop)).
Proof. exact (eq_refl (@ex (_102373 -> Prop))). Qed.
Lemma lem4075227 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : (term178 _102373 _102400 n s P f) = (term201 _102373 _102400 n s P f).
Proof. exact (MK_COMB (@lem4075226 _102373) (@lem4075225 _102373 _102400 n s P f)). Qed.
Lemma lem4075228 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : ((term177 _102373 _102400 n f s P) = (term178 _102373 _102400 n s P f)) = ((term176 _102373 _102400 n f s P) = (term201 _102373 _102400 n s P f)).
Proof. exact (MK_COMB (@lem4075217 _102373 _102400 n f s P) (@lem4075227 _102373 _102400 n s P f)). Qed.
Lemma lem4075229 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : (term176 _102373 _102400 n f s P) = (term201 _102373 _102400 n s P f).
Proof. exact (EQ_MP (@lem4075228 _102373 _102400 n s P f) (@lem4075205 _102373 _102400 n s P f)). Qed.
Lemma lem4075240 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : (term145 _102373 _102400 n f s P) = (term201 _102373 _102400 n s P f).
Proof. exact (TRANS (@lem4075201 _102373 _102400 n f s P) (@lem4075229 _102373 _102400 n s P f)). Qed.
Lemma lem4075241 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4075242 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : (term146 _102373 _102400 n f s P) = (term202 _102373 _102400 n s P f).
Proof. exact (MK_COMB (@lem4075241) (@lem4075240 _102373 _102400 n s P f)). Qed.
Lemma lem4075243 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4075244 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : (term147 _102373 _102400 n f s P) = (term203 _102373 _102400 n s P f).
Proof. exact (MK_COMB (@lem4075243) (@lem4075242 _102373 _102400 n s P f)). Qed.
Lemma lem4075250 (t1 : Prop) (t2 : Prop) : (term29 t1 t2) = (term30 t1 t2).
Proof. exact (EQ_MP (@lem4074721 t1 t2) (@lem4074720 t1 t2)). Qed.
Lemma lem4075251 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) (t : _102373 -> Prop) : (term158 _102373 _102400 n s P f t) = (term204 _102373 _102400 n s P f t).
Proof. exact (@lem4075250 (term205 _102373 n t s) (term206 _102373 _102400 P f t)). Qed.
Lemma lem4075253 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (EQ_MP (@lem4074703 t1 t2 t3) (@lem4074702 t1 t2 t3)). Qed.
Lemma lem4075254 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) (t : _102373 -> Prop) : (term204 _102373 _102400 n s P f t) = (term207 _102373 _102400 n s P f t).
Proof. exact (@lem4075253 (@FINITE _102373 t) (term208 _102373 n t s) (term191 _102373 _102400 P f t)). Qed.
Lemma lem4075257 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) (t : _102373 -> Prop) : (term158 _102373 _102400 n s P f t) = (term207 _102373 _102400 n s P f t).
Proof. exact (TRANS (@lem4075251 _102373 _102400 n s P f t) (@lem4075254 _102373 _102400 n s P f t)). Qed.
Lemma lem4075259 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (EQ_MP (@lem4074703 t1 t2 t3) (@lem4074702 t1 t2 t3)). Qed.
Lemma lem4075260 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) (t : _102373 -> Prop) : (term209 _102373 _102400 n s P f t) = (term196 _102373 _102400 n s P f t).
Proof. exact (@lem4075259 (term171 _102373 t n) (@SUBSET _102373 t s) (term191 _102373 _102400 P f t)). Qed.
Lemma lem4075265 {_102373 : Type'} (t : _102373 -> Prop) : (term173 _102373 t) = (term173 _102373 t).
Proof. exact (eq_refl (term173 _102373 t)). Qed.
Lemma lem4075266 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) (t : _102373 -> Prop) : (term207 _102373 _102400 n s P f t) = (term198 _102373 _102400 n s P f t).
Proof. exact (MK_COMB (@lem4075265 _102373 t) (@lem4075260 _102373 _102400 n s P f t)). Qed.
Lemma lem4075269 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) (t : _102373 -> Prop) : (term158 _102373 _102400 n s P f t) = (term198 _102373 _102400 n s P f t).
Proof. exact (TRANS (@lem4075257 _102373 _102400 n s P f t) (@lem4075266 _102373 _102400 n s P f t)). Qed.
Lemma lem4075270 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : (term160 _102373 _102400 n s P f) = (term200 _102373 _102400 n s P f).
Proof. exact (fun_ext (fun t : _102373 -> Prop => @lem4075269 _102373 _102400 n s P f t)). Qed.
Lemma lem4075271 {_102373 : Type'} : (@ex (_102373 -> Prop)) = (@ex (_102373 -> Prop)).
Proof. exact (eq_refl (@ex (_102373 -> Prop))). Qed.
Lemma lem4075272 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : (term162 _102373 _102400 n s P f) = (term201 _102373 _102400 n s P f).
Proof. exact (MK_COMB (@lem4075271 _102373) (@lem4075270 _102373 _102400 n s P f)). Qed.
Lemma lem4075277 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4075278 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : (term163 _102373 _102400 n s P f) = (term202 _102373 _102400 n s P f).
Proof. exact (MK_COMB (@lem4075277) (@lem4075272 _102373 _102400 n s P f)). Qed.
Lemma lem4075279 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : ((term146 _102373 _102400 n f s P) = (term163 _102373 _102400 n s P f)) = ((term202 _102373 _102400 n s P f) = (term202 _102373 _102400 n s P f)).
Proof. exact (MK_COMB (@lem4075244 _102373 _102400 n s P f) (@lem4075278 _102373 _102400 n s P f)). Qed.
Lemma lem4075281 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4075282 (x : Prop) : (x = x) = True.
Proof. exact (@lem4075281 Prop x). Qed.
Lemma lem4075283 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : ((term202 _102373 _102400 n s P f) = (term202 _102373 _102400 n s P f)) = True.
Proof. exact (@lem4075282 (term202 _102373 _102400 n s P f)). Qed.
Lemma lem4075284 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : ((term146 _102373 _102400 n f s P) = (term163 _102373 _102400 n s P f)) = True.
Proof. exact (TRANS (@lem4075279 _102373 _102400 n s P f) (@lem4075283 _102373 _102400 n s P f)). Qed.
Lemma lem4075285 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : True = ((term146 _102373 _102400 n f s P) = (term163 _102373 _102400 n s P f)).
Proof. exact (SYM (@lem4075284 _102373 _102400 n s P f)). Qed.
Lemma lem4075286 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : (term146 _102373 _102400 n f s P) = (term163 _102373 _102400 n s P f).
Proof. exact (EQ_MP (@lem4075285 _102373 _102400 n s P f) (@lem0)). Qed.
Lemma lem4075287 {_102373 _102400 : Type'} (n : nat) (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : (term137 _102373 _102400 n f s P) = (term154 _102373 _102400 n s P f).
Proof. exact (EQ_MP (@lem4075171 _102373 _102400 n s P f) (@lem4075286 _102373 _102400 n s P f)). Qed.
Lemma lem4075292 {_102373 _102400 : Type'} (s : _102373 -> Prop) (P : type686 _102400) (f : _102373 -> _102400) : term210 _102373 _102400 s P f.
Proof. exact (fun n : nat => @lem4075287 _102373 _102400 n s P f). Qed.
Lemma lem4075297 {_102373 _102400 : Type'} (P : type686 _102400) (f : _102373 -> _102400) : term211 _102373 _102400 P f.
Proof. exact (fun s : _102373 -> Prop => @lem4075292 _102373 _102400 s P f). Qed.
Lemma lem4075302 {_102373 _102400 : Type'} (P : type686 _102400) : term212 _102373 _102400 P.
Proof. exact (fun f : _102373 -> _102400 => @lem4075297 _102373 _102400 P f). Qed.
Lemma lem4075307 {_102373 _102400 : Type'} : term213 _102373 _102400.
Proof. exact (fun P : type686 _102400 => @lem4075302 _102373 _102400 P). Qed.
