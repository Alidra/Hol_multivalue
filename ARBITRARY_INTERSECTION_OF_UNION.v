Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARBITRARY_INTERSECTION_OF_UNION_term_abbrevs.
Require Import ARBITRARY_INTERSECTION_OF_INC_spec.
Require Import ARBITRARY_INTERSECTION_OF_UNION_EQ_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem4875558 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4875559 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4875560 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4875559 t1) (@lem4875558 t1)). Qed.
Lemma lem4875561 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4875560 t1 t2). Qed.
Lemma lem4875562 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4875563 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4875562 t1 t2) (@lem4875561 t1 t2)). Qed.
Lemma lem4875564 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4875563 t1 t2 t3). Qed.
Lemma lem4875565 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4875566 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4875565 t1 t2 t3) (@lem4875564 t1 t2 t3)). Qed.
Lemma lem4875567 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4875566 t1 t2 t3)). Qed.
Lemma lem4875568 {A : Type'} (P : type686 A) : term7 A P.
Proof. exact (@lem4875557 A P). Qed.
Lemma lem4875569 {A : Type'} (P : type686 A) : (term7 A P) = ((term8 A P) = (term9 A P)).
Proof. exact (eq_refl (term7 A P)). Qed.
Lemma lem4875590 {A : Type'} (P : type686 A) : (term8 A P) = (term9 A P).
Proof. exact (EQ_MP (@lem4875569 A P) (@lem4875568 A P)). Qed.
Lemma lem4875591 {A : Type'} (P : type686 A) : (term8 A P) = (term9 A P).
Proof. exact (@lem4875590 A P). Qed.
Lemma lem4875604 {A : Type'} (P : type686 A) : (term10 A P) = (term10 A P).
Proof. exact (eq_refl (term10 A P)). Qed.
Lemma lem4875605 {A : Type'} (P : type686 A) : (term11 A P) = (term12 A P).
Proof. exact (MK_COMB (@lem4875604 A P) (@lem4875591 A P)). Qed.
Lemma lem4875608 {A : Type'} : (term13 A) = (term14 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4875605 A P)). Qed.
Lemma lem4875609 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4875610 {A : Type'} : (term15 A) = (term16 A).
Proof. exact (MK_COMB (@lem4875609 A) (@lem4875608 A)). Qed.
Lemma lem4875615 {A : Type'} : (term16 A) = (term15 A).
Proof. exact (SYM (@lem4875610 A)). Qed.
Lemma lem4875617 (p : Prop) : p = (term17 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4875618 {A : Type'} : (term16 A) = (term18 A).
Proof. exact (@lem4875617 (term16 A)). Qed.
Lemma lem4875619 {A : Type'} : (term18 A) = (term16 A).
Proof. exact (SYM (@lem4875618 A)). Qed.
Lemma lem4875620 {A : Type'} (h1 : term19 A) : term19 A.
Proof. exact (h1). Qed.
Lemma lem4875621 {A : Type'} : term20 A.
Proof. exact (@lem4858519 A). Qed.
Lemma lem4875625 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (h1). Qed.
Lemma lem4875626 {A : Type'} : term22 A.
Proof. exact (fun h0 : term21 A => @lem4875625 A h0). Qed.
Lemma lem4875627 {A : Type'} (h1 : term22 A) : term22 A.
Proof. exact (h1). Qed.
Lemma lem4875628 {A : Type'} (h1 : term21 A) : term21 A.
Proof. exact (h1). Qed.
Lemma lem4875629 {A : Type'} (h1 : term21 A) (h2 : term22 A) : term21 A.
Proof. exact (@lem4875627 A h2 (@lem4875628 A h1)). Qed.
Lemma lem4875630 {A : Type'} (h1 : term21 A) : term23 A.
Proof. exact (fun h0 : term22 A => @lem4875629 A h1 h0). Qed.
Lemma lem4875631 {A : Type'} (h1 : term22 A) : term22 A.
Proof. exact (h1). Qed.
Lemma lem4875632 {A : Type'} (h1 : term21 A) (h2 : term22 A) : term21 A.
Proof. exact (@lem4875630 A h1 (@lem4875631 A h2)). Qed.
Lemma lem4875633 {A : Type'} (h1 : term22 A) : term22 A.
Proof. exact (fun h0 : term21 A => @lem4875632 A h0 h1). Qed.
Lemma lem4875634 {A : Type'} : term24 A.
Proof. exact (fun h0 : term22 A => @lem4875633 A h0). Qed.
Lemma lem4875637 {A : Type'} : term22 A.
Proof. exact (@lem4875634 A (@lem4875626 A)). Qed.
Lemma lem4875638 {A : Type'} : term22 A.
Proof. exact (@lem4875637 A). Qed.
Lemma lem4875672 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4875673 {A : Type'} : (term25 A) = (term26 A).
Proof. exact (@lem4875672 (term20 A)). Qed.
Lemma lem4875684 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (eq_refl (term27 A)). Qed.
Lemma lem4875691 {A : Type'} : (term21 A) = (term28 A).
Proof. exact (MK_COMB (@lem4875684 A) (@lem4875673 A)). Qed.
Lemma lem4875696 {A : Type'} (P : type686 A) (s : A -> Prop) : (term29 A P s) = (term29 A P s).
Proof. exact (eq_refl (term29 A P s)). Qed.
Lemma lem4875697 {A : Type'} (P : type686 A) : (term30 A P) = (term30 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4875696 A P s)). Qed.
Lemma lem4875698 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4875699 {A : Type'} (P : type686 A) : (term31 A P) = (term31 A P).
Proof. exact (MK_COMB (@lem4875698 A) (@lem4875697 A P)). Qed.
Lemma lem4875700 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4875699 A P)). Qed.
Lemma lem4875701 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4875702 {A : Type'} : (term20 A) = (term20 A).
Proof. exact (MK_COMB (@lem4875701 A) (@lem4875700 A)). Qed.
Lemma lem4875703 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4875704 {A : Type'} : (term26 A) = (term26 A).
Proof. exact (MK_COMB (@lem4875703) (@lem4875702 A)). Qed.
Lemma lem4875713 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term33 A P s t) = (term33 A P s t).
Proof. exact (eq_refl (term33 A P s t)). Qed.
Lemma lem4875714 {A : Type'} (P : type686 A) (s : A -> Prop) : (term34 A P s) = (term34 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4875713 A P s t)). Qed.
Lemma lem4875715 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4875716 {A : Type'} (P : type686 A) (s : A -> Prop) : (term35 A P s) = (term35 A P s).
Proof. exact (MK_COMB (@lem4875715 A) (@lem4875714 A P s)). Qed.
Lemma lem4875717 {A : Type'} (P : type686 A) : (term36 A P) = (term36 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4875716 A P s)). Qed.
Lemma lem4875718 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4875719 {A : Type'} (P : type686 A) : (term9 A P) = (term9 A P).
Proof. exact (MK_COMB (@lem4875718 A) (@lem4875717 A P)). Qed.
Lemma lem4875728 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term37 A P s t) = (term37 A P s t).
Proof. exact (eq_refl (term37 A P s t)). Qed.
Lemma lem4875729 {A : Type'} (P : type686 A) (s : A -> Prop) : (term38 A P s) = (term38 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4875728 A P s t)). Qed.
Lemma lem4875730 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4875731 {A : Type'} (P : type686 A) (s : A -> Prop) : (term39 A P s) = (term39 A P s).
Proof. exact (MK_COMB (@lem4875730 A) (@lem4875729 A P s)). Qed.
Lemma lem4875732 {A : Type'} (P : type686 A) : (term40 A P) = (term40 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4875731 A P s)). Qed.
Lemma lem4875733 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4875734 {A : Type'} (P : type686 A) : (term41 A P) = (term41 A P).
Proof. exact (MK_COMB (@lem4875733 A) (@lem4875732 A P)). Qed.
Lemma lem4875735 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4875736 {A : Type'} (P : type686 A) : (term10 A P) = (term10 A P).
Proof. exact (MK_COMB (@lem4875735) (@lem4875734 A P)). Qed.
Lemma lem4875737 {A : Type'} (P : type686 A) : (term12 A P) = (term12 A P).
Proof. exact (MK_COMB (@lem4875736 A P) (@lem4875719 A P)). Qed.
Lemma lem4875738 {A : Type'} : (term14 A) = (term14 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4875737 A P)). Qed.
Lemma lem4875739 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4875740 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (MK_COMB (@lem4875739 A) (@lem4875738 A)). Qed.
Lemma lem4875741 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4875742 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem4875741) (@lem4875740 A)). Qed.
Lemma lem4875743 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4875744 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (MK_COMB (@lem4875743) (@lem4875742 A)). Qed.
Lemma lem4875745 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (MK_COMB (@lem4875744 A) (@lem4875704 A)). Qed.
Lemma lem4875804 {A : Type'} : (term21 A) = (term28 A).
Proof. exact (TRANS (@lem4875691 A) (@lem4875745 A)). Qed.
Lemma lem4875805 {A : Type'} : (term28 A) = (term21 A).
Proof. exact (SYM (@lem4875804 A)). Qed.
Lemma lem4875806 {A : Type'} (h1 : term19 A) : term19 A.
Proof. exact (h1). Qed.
Lemma lem4875807 {A : Type'} (h1 : term20 A) : term20 A.
Proof. exact (h1). Qed.
Lemma lem4875814 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term42 A s P t) = (term43 A s P t).
Proof. exact (@lem17045 (P s) (P t)). Qed.
Lemma lem4875815 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term44 A P s t) = (term44 A P s t).
Proof. exact (eq_refl (term44 A P s t)). Qed.
Lemma lem4875816 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4875817 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term45 A s P t) = (term46 A s P t).
Proof. exact (MK_COMB (@lem4875816) (@lem4875814 A s P t)). Qed.
Lemma lem4875818 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term47 A P s t) = (term48 A P s t).
Proof. exact (MK_COMB (@lem4875817 A s P t) (@lem4875815 A P s t)). Qed.
Lemma lem4875819 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term37 A P s t) = (term47 A P s t).
Proof. exact (@lem17265 (term49 A s P t) (term44 A P s t)). Qed.
Lemma lem4875820 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term37 A P s t) = (term48 A P s t).
Proof. exact (TRANS (@lem4875819 A P s t) (@lem4875818 A P s t)). Qed.
Lemma lem4875821 {A : Type'} (P : type686 A) (s : A -> Prop) : (term38 A P s) = (term50 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4875820 A P s t)). Qed.
Lemma lem4875822 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4875823 {A : Type'} (P : type686 A) (s : A -> Prop) : (term39 A P s) = (term51 A P s).
Proof. exact (MK_COMB (@lem4875822 A) (@lem4875821 A P s)). Qed.
Lemma lem4875824 {A : Type'} (P : type686 A) : (term40 A P) = (term52 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4875823 A P s)). Qed.
Lemma lem4875825 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4875826 {A : Type'} (P : type686 A) : (term41 A P) = (term53 A P).
Proof. exact (MK_COMB (@lem4875825 A) (@lem4875824 A P)). Qed.
Lemma lem4875837 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term54 A P s t) = (term55 A P s t).
Proof. exact (@lem17362 (term49 A s P t) (term56 A P s t)). Qed.
Lemma lem4875838 {A : Type'} (P : type686 A) : (term57 A P) = (term58 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4875839 {A : Type'} (P : type686 A) (s : A -> Prop) : (term59 A P s) = (term60 A P s).
Proof. exact (@lem4875838 A (term34 A P s)). Qed.
Lemma lem4875840 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term61 A P s t) = (term33 A P s t).
Proof. exact (eq_refl (term61 A P s t)). Qed.
Lemma lem4875841 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4875842 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term62 A P s t) = (term54 A P s t).
Proof. exact (MK_COMB (@lem4875841) (@lem4875840 A P s t)). Qed.
Lemma lem4875843 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term62 A P s t) = (term55 A P s t).
Proof. exact (TRANS (@lem4875842 A P s t) (@lem4875837 A P s t)). Qed.
Lemma lem4875844 {A : Type'} (P : type686 A) (s : A -> Prop) : (term63 A P s) = (term64 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4875843 A P s t)). Qed.
Lemma lem4875845 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4875846 {A : Type'} (P : type686 A) (s : A -> Prop) : (term60 A P s) = (term65 A P s).
Proof. exact (MK_COMB (@lem4875845 A) (@lem4875844 A P s)). Qed.
Lemma lem4875847 {A : Type'} (P : type686 A) (s : A -> Prop) : (term59 A P s) = (term65 A P s).
Proof. exact (TRANS (@lem4875839 A P s) (@lem4875846 A P s)). Qed.
Lemma lem4875848 {A : Type'} (P : type686 A) : (term57 A P) = (term58 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4875849 {A : Type'} (P : type686 A) : (term66 A P) = (term67 A P).
Proof. exact (@lem4875848 A (term36 A P)). Qed.
Lemma lem4875850 {A : Type'} (P : type686 A) (s : A -> Prop) : (term68 A P s) = (term35 A P s).
Proof. exact (eq_refl (term68 A P s)). Qed.
Lemma lem4875851 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4875852 {A : Type'} (P : type686 A) (s : A -> Prop) : (term69 A P s) = (term59 A P s).
Proof. exact (MK_COMB (@lem4875851) (@lem4875850 A P s)). Qed.
Lemma lem4875853 {A : Type'} (P : type686 A) (s : A -> Prop) : (term69 A P s) = (term65 A P s).
Proof. exact (TRANS (@lem4875852 A P s) (@lem4875847 A P s)). Qed.
Lemma lem4875854 {A : Type'} (P : type686 A) : (term70 A P) = (term71 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4875853 A P s)). Qed.
Lemma lem4875855 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4875856 {A : Type'} (P : type686 A) : (term67 A P) = (term72 A P).
Proof. exact (MK_COMB (@lem4875855 A) (@lem4875854 A P)). Qed.
Lemma lem4875857 {A : Type'} (P : type686 A) : (term66 A P) = (term72 A P).
Proof. exact (TRANS (@lem4875849 A P) (@lem4875856 A P)). Qed.
Lemma lem4875858 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4875859 {A : Type'} (P : type686 A) : (term73 A P) = (term74 A P).
Proof. exact (MK_COMB (@lem4875858) (@lem4875826 A P)). Qed.
Lemma lem4875860 {A : Type'} (P : type686 A) : (term75 A P) = (term76 A P).
Proof. exact (MK_COMB (@lem4875859 A P) (@lem4875857 A P)). Qed.
Lemma lem4875861 {A : Type'} (P : type686 A) : (term77 A P) = (term75 A P).
Proof. exact (@lem17362 (term41 A P) (term9 A P)). Qed.
Lemma lem4875862 {A : Type'} (P : type686 A) : (term77 A P) = (term76 A P).
Proof. exact (TRANS (@lem4875861 A P) (@lem4875860 A P)). Qed.
Lemma lem4875863 {A : Type'} (P : type180 A) : (term78 A P) = (term79 A P).
Proof. exact (@lem18392 (type686 A) P). Qed.
Lemma lem4875864 {A : Type'} : (term19 A) = (term80 A).
Proof. exact (@lem4875863 A (term14 A)). Qed.
Lemma lem4875865 {A : Type'} (P : type686 A) : (term81 A P) = (term12 A P).
Proof. exact (eq_refl (term81 A P)). Qed.
Lemma lem4875866 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4875867 {A : Type'} (P : type686 A) : (term82 A P) = (term77 A P).
Proof. exact (MK_COMB (@lem4875866) (@lem4875865 A P)). Qed.
Lemma lem4875868 {A : Type'} (P : type686 A) : (term82 A P) = (term76 A P).
Proof. exact (TRANS (@lem4875867 A P) (@lem4875862 A P)). Qed.
Lemma lem4875869 {A : Type'} : (term83 A) = (term84 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4875868 A P)). Qed.
Lemma lem4875870 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4875871 {A : Type'} : (term80 A) = (term85 A).
Proof. exact (MK_COMB (@lem4875870 A) (@lem4875869 A)). Qed.
Lemma lem4875872 {A : Type'} : (term19 A) = (term85 A).
Proof. exact (TRANS (@lem4875864 A) (@lem4875871 A)). Qed.
Lemma lem4876027 {A : Type'} (P : Prop) (Q : A -> Prop) : (term86 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4876028 {A : Type'} (P : Prop) (Q : type686 A) : (term88 A P Q) = (term89 A P Q).
Proof. exact (@lem4876027 (A -> Prop) P Q). Qed.
Lemma lem4876029 {A : Type'} (P : type686 A) : (term90 A P) = (term91 A P).
Proof. exact (@lem4876028 A (term53 A P) (term71 A P)). Qed.
Lemma lem4876030 {A : Type'} (P : type686 A) (s : A -> Prop) : (term92 A P s) = (term65 A P s).
Proof. exact (eq_refl (term92 A P s)). Qed.
Lemma lem4876031 {A : Type'} (P : type686 A) : (term93 A P) = (term71 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4876030 A P s)). Qed.
Lemma lem4876032 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4876033 {A : Type'} (P : type686 A) : (term94 A P) = (term72 A P).
Proof. exact (MK_COMB (@lem4876032 A) (@lem4876031 A P)). Qed.
Lemma lem4876034 {A : Type'} (P : type686 A) : (term74 A P) = (term74 A P).
Proof. exact (eq_refl (term74 A P)). Qed.
Lemma lem4876035 {A : Type'} (P : type686 A) : (term90 A P) = (term76 A P).
Proof. exact (MK_COMB (@lem4876034 A P) (@lem4876033 A P)). Qed.
Lemma lem4876036 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4876037 {A : Type'} (P : type686 A) : (term95 A P) = (term96 A P).
Proof. exact (MK_COMB (@lem4876036) (@lem4876035 A P)). Qed.
Lemma lem4876038 {A : Type'} (P : type686 A) (s : A -> Prop) : (term92 A P s) = (term65 A P s).
Proof. exact (eq_refl (term92 A P s)). Qed.
Lemma lem4876039 {A : Type'} (P : type686 A) : (term74 A P) = (term74 A P).
Proof. exact (eq_refl (term74 A P)). Qed.
Lemma lem4876040 {A : Type'} (P : type686 A) (s : A -> Prop) : (term97 A P s) = (term98 A P s).
Proof. exact (MK_COMB (@lem4876039 A P) (@lem4876038 A P s)). Qed.
Lemma lem4876041 {A : Type'} (P : type686 A) : (term99 A P) = (term100 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4876040 A P s)). Qed.
Lemma lem4876042 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4876043 {A : Type'} (P : type686 A) : (term91 A P) = (term101 A P).
Proof. exact (MK_COMB (@lem4876042 A) (@lem4876041 A P)). Qed.
Lemma lem4876044 {A : Type'} (P : type686 A) : ((term90 A P) = (term91 A P)) = ((term76 A P) = (term101 A P)).
Proof. exact (MK_COMB (@lem4876037 A P) (@lem4876043 A P)). Qed.
Lemma lem4876045 {A : Type'} (P : type686 A) : (term76 A P) = (term101 A P).
Proof. exact (EQ_MP (@lem4876044 A P) (@lem4876029 A P)). Qed.
Lemma lem4876047 {A : Type'} (P : Prop) (Q : A -> Prop) : (term86 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4876048 {A : Type'} (P : Prop) (Q : type686 A) : (term88 A P Q) = (term89 A P Q).
Proof. exact (@lem4876047 (A -> Prop) P Q). Qed.
Lemma lem4876049 {A : Type'} (P : type686 A) (s : A -> Prop) : (term102 A P s) = (term103 A P s).
Proof. exact (@lem4876048 A (term53 A P) (term64 A P s)). Qed.
Lemma lem4876050 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term104 A P s t) = (term55 A P s t).
Proof. exact (eq_refl (term104 A P s t)). Qed.
Lemma lem4876051 {A : Type'} (P : type686 A) (s : A -> Prop) : (term105 A P s) = (term64 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4876050 A P s t)). Qed.
Lemma lem4876052 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4876053 {A : Type'} (P : type686 A) (s : A -> Prop) : (term106 A P s) = (term65 A P s).
Proof. exact (MK_COMB (@lem4876052 A) (@lem4876051 A P s)). Qed.
Lemma lem4876054 {A : Type'} (P : type686 A) : (term74 A P) = (term74 A P).
Proof. exact (eq_refl (term74 A P)). Qed.
Lemma lem4876055 {A : Type'} (P : type686 A) (s : A -> Prop) : (term102 A P s) = (term98 A P s).
Proof. exact (MK_COMB (@lem4876054 A P) (@lem4876053 A P s)). Qed.
Lemma lem4876056 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4876057 {A : Type'} (P : type686 A) (s : A -> Prop) : (term107 A P s) = (term108 A P s).
Proof. exact (MK_COMB (@lem4876056) (@lem4876055 A P s)). Qed.
Lemma lem4876058 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term104 A P s t) = (term55 A P s t).
Proof. exact (eq_refl (term104 A P s t)). Qed.
Lemma lem4876059 {A : Type'} (P : type686 A) : (term74 A P) = (term74 A P).
Proof. exact (eq_refl (term74 A P)). Qed.
Lemma lem4876060 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term109 A P s t) = (term110 A P s t).
Proof. exact (MK_COMB (@lem4876059 A P) (@lem4876058 A P s t)). Qed.
Lemma lem4876061 {A : Type'} (P : type686 A) (s : A -> Prop) : (term111 A P s) = (term112 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4876060 A P s t)). Qed.
Lemma lem4876062 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4876063 {A : Type'} (P : type686 A) (s : A -> Prop) : (term103 A P s) = (term113 A P s).
Proof. exact (MK_COMB (@lem4876062 A) (@lem4876061 A P s)). Qed.
Lemma lem4876064 {A : Type'} (P : type686 A) (s : A -> Prop) : ((term102 A P s) = (term103 A P s)) = ((term98 A P s) = (term113 A P s)).
Proof. exact (MK_COMB (@lem4876057 A P s) (@lem4876063 A P s)). Qed.
Lemma lem4876065 {A : Type'} (P : type686 A) (s : A -> Prop) : (term98 A P s) = (term113 A P s).
Proof. exact (EQ_MP (@lem4876064 A P s) (@lem4876049 A P s)). Qed.
Lemma lem4876066 {A : Type'} (P : type686 A) : (term100 A P) = (term114 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4876065 A P s)). Qed.
Lemma lem4876067 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4876068 {A : Type'} (P : type686 A) : (term101 A P) = (term115 A P).
Proof. exact (MK_COMB (@lem4876067 A) (@lem4876066 A P)). Qed.
Lemma lem4876069 {A : Type'} (P : type686 A) : (term76 A P) = (term115 A P).
Proof. exact (TRANS (@lem4876045 A P) (@lem4876068 A P)). Qed.
Lemma lem4876070 {A : Type'} : (term84 A) = (term116 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4876069 A P)). Qed.
Lemma lem4876071 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4876073 {A : Type'} : (term85 A) = (term117 A).
Proof. exact (MK_COMB (@lem4876071 A) (@lem4876070 A)). Qed.
Lemma lem4876074 {A : Type'} : (term19 A) = (term117 A).
Proof. exact (TRANS (@lem4875872 A) (@lem4876073 A)). Qed.
Lemma lem4876075 {A : Type'} (h1 : term19 A) : term117 A.
Proof. exact (EQ_MP (@lem4876074 A) (@lem4875806 A h1)). Qed.
Lemma lem4876082 {A : Type'} (P : type686 A) (s : A -> Prop) : (term29 A P s) = (term118 A P s).
Proof. exact (@lem17265 (P s) (@INTERSECTION_OF A (@ARBITRARY A) P s)). Qed.
Lemma lem4876083 {A : Type'} (P : type686 A) : (term30 A P) = (term119 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4876082 A P s)). Qed.
Lemma lem4876084 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4876085 {A : Type'} (P : type686 A) : (term31 A P) = (term120 A P).
Proof. exact (MK_COMB (@lem4876084 A) (@lem4876083 A P)). Qed.
Lemma lem4876086 {A : Type'} : (term32 A) = (term121 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4876085 A P)). Qed.
Lemma lem4876087 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4876144 {A : Type'} : (term20 A) = (term122 A).
Proof. exact (MK_COMB (@lem4876087 A) (@lem4876086 A)). Qed.
Lemma lem4876145 {A : Type'} (h1 : term20 A) : term122 A.
Proof. exact (EQ_MP (@lem4876144 A) (@lem4875807 A h1)). Qed.
Lemma lem4876146 {A : Type'} (P : type686 A) (h1 : term115 A P) : term115 A P.
Proof. exact (h1). Qed.
Lemma lem4876147 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term113 A P s) : term113 A P s.
Proof. exact (h1). Qed.
Lemma lem4876148 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term110 A P s t.
Proof. exact (h1). Qed.
Lemma lem4876157 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4876158 {A : Type'} (f : type74 A) (x : type180 A) : (f x) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4876157 (type180 A) (type174 A) f x). Qed.
Lemma lem4876159 {A : Type'} : (@INTERSECTION_OF A (@ARBITRARY A)) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@INTERSECTION_OF A) (@ARBITRARY A)).
Proof. exact (@lem4876158 A (@INTERSECTION_OF A) (@ARBITRARY A)). Qed.
Lemma lem4876160 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4876161 {A : Type'} (P : type686 A) : (@INTERSECTION_OF A (@ARBITRARY A) P) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@INTERSECTION_OF A) (@ARBITRARY A) P).
Proof. exact (MK_COMB (@lem4876159 A) (@lem4876160 A P)). Qed.
Lemma lem4876163 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4876164 {A : Type'} (f : type174 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4876163 (type686 A) (type686 A) f x). Qed.
Lemma lem4876165 {A : Type'} (P : type686 A) : (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@INTERSECTION_OF A) (@ARBITRARY A) P) = (term123 A P).
Proof. exact (@lem4876164 A (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@INTERSECTION_OF A) (@ARBITRARY A)) P). Qed.
Lemma lem4876166 {A : Type'} (P : type686 A) : (@INTERSECTION_OF A (@ARBITRARY A) P) = (term123 A P).
Proof. exact (TRANS (@lem4876161 A P) (@lem4876165 A P)). Qed.
Lemma lem4876167 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4876168 {A : Type'} (P : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A (@ARBITRARY A) P s) = (term124 A P s).
Proof. exact (MK_COMB (@lem4876166 A P) (@lem4876167 A s)). Qed.
Lemma lem4876170 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4876171 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4876170 (A -> Prop) Prop f x). Qed.
Lemma lem4876172 {A : Type'} (P : type686 A) (s : A -> Prop) : (term124 A P s) = (term125 A P s).
Proof. exact (@lem4876171 A (term123 A P) s). Qed.
Lemma lem4876174 {A : Type'} (P : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A (@ARBITRARY A) P s) = (term125 A P s).
Proof. exact (TRANS (@lem4876168 A P s) (@lem4876172 A P s)). Qed.
Lemma lem4876175 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4876180 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4876181 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4876180 (A -> Prop) Prop f x). Qed.
Lemma lem4876183 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = (@I ((A -> Prop) -> Prop) P s).
Proof. exact (@lem4876181 A P s). Qed.
Lemma lem4876184 {A : Type'} (P : type686 A) (s : A -> Prop) : (term126 A P s) = (term127 A P s).
Proof. exact (MK_COMB (@lem4876175) (@lem4876183 A P s)). Qed.
Lemma lem4876185 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4876186 {A : Type'} (P : type686 A) (s : A -> Prop) : (term128 A P s) = (term129 A P s).
Proof. exact (MK_COMB (@lem4876185) (@lem4876184 A P s)). Qed.
Lemma lem4876187 {A : Type'} (P : type686 A) (s : A -> Prop) : (term118 A P s) = (term130 A P s).
Proof. exact (MK_COMB (@lem4876186 A P s) (@lem4876174 A P s)). Qed.
Lemma lem4876188 {A : Type'} (P : type686 A) : (term119 A P) = (term131 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4876187 A P s)). Qed.
Lemma lem4876189 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4876190 {A : Type'} (P : type686 A) : (term120 A P) = (term132 A P).
Proof. exact (MK_COMB (@lem4876189 A) (@lem4876188 A P)). Qed.
Lemma lem4876191 {A : Type'} : (term121 A) = (term133 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4876190 A P)). Qed.
Lemma lem4876192 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4876193 {A : Type'} : (term122 A) = (term134 A).
Proof. exact (MK_COMB (@lem4876192 A) (@lem4876191 A)). Qed.
Lemma lem4876194 {A : Type'} (h1 : term20 A) : term134 A.
Proof. exact (EQ_MP (@lem4876193 A) (@lem4876145 A h1)). Qed.
Lemma lem4876195 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4876205 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4876206 {A : Type'} (f : type636 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4876205 (A -> Prop) (type672 A) f x). Qed.
Lemma lem4876207 {A : Type'} (s : A -> Prop) : (@UNION A s) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) s).
Proof. exact (@lem4876206 A (@UNION A) s). Qed.
Lemma lem4876208 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4876209 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@UNION A s t) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) s t).
Proof. exact (MK_COMB (@lem4876207 A s) (@lem4876208 A t)). Qed.
Lemma lem4876211 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4876212 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4876211 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem4876213 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) s t) = (term135 A s t).
Proof. exact (@lem4876212 A (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) s) t). Qed.
Lemma lem4876215 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@UNION A s t) = (term135 A s t).
Proof. exact (TRANS (@lem4876209 A s t) (@lem4876213 A s t)). Qed.
Lemma lem4876217 {A : Type'} (P : type686 A) : (@INTERSECTION_OF A (@ARBITRARY A) P) = (@INTERSECTION_OF A (@ARBITRARY A) P).
Proof. exact (eq_refl (@INTERSECTION_OF A (@ARBITRARY A) P)). Qed.
Lemma lem4876218 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term56 A P s t) = (term136 A P s t).
Proof. exact (MK_COMB (@lem4876217 A P) (@lem4876215 A s t)). Qed.
Lemma lem4876220 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4876221 {A : Type'} (f : type74 A) (x : type180 A) : (f x) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4876220 (type180 A) (type174 A) f x). Qed.
Lemma lem4876222 {A : Type'} : (@INTERSECTION_OF A (@ARBITRARY A)) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@INTERSECTION_OF A) (@ARBITRARY A)).
Proof. exact (@lem4876221 A (@INTERSECTION_OF A) (@ARBITRARY A)). Qed.
Lemma lem4876223 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4876224 {A : Type'} (P : type686 A) : (@INTERSECTION_OF A (@ARBITRARY A) P) = (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@INTERSECTION_OF A) (@ARBITRARY A) P).
Proof. exact (MK_COMB (@lem4876222 A) (@lem4876223 A P)). Qed.
Lemma lem4876226 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4876227 {A : Type'} (f : type174 A) (x : type686 A) : (f x) = (@I (((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem4876226 (type686 A) (type686 A) f x). Qed.
Lemma lem4876228 {A : Type'} (P : type686 A) : (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@INTERSECTION_OF A) (@ARBITRARY A) P) = (term123 A P).
Proof. exact (@lem4876227 A (@I ((((A -> Prop) -> Prop) -> Prop) -> ((A -> Prop) -> Prop) -> (A -> Prop) -> Prop) (@INTERSECTION_OF A) (@ARBITRARY A)) P). Qed.
Lemma lem4876229 {A : Type'} (P : type686 A) : (@INTERSECTION_OF A (@ARBITRARY A) P) = (term123 A P).
Proof. exact (TRANS (@lem4876224 A P) (@lem4876228 A P)). Qed.
Lemma lem4876230 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term135 A s t) = (term135 A s t).
Proof. exact (eq_refl (term135 A s t)). Qed.
Lemma lem4876231 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term136 A P s t) = (term137 A P s t).
Proof. exact (MK_COMB (@lem4876229 A P) (@lem4876230 A s t)). Qed.
Lemma lem4876233 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4876234 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4876233 (A -> Prop) Prop f x). Qed.
Lemma lem4876235 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term137 A P s t) = (term138 A P s t).
Proof. exact (@lem4876234 A (term123 A P) (term135 A s t)). Qed.
Lemma lem4876236 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term136 A P s t) = (term138 A P s t).
Proof. exact (TRANS (@lem4876231 A P s t) (@lem4876235 A P s t)). Qed.
Lemma lem4876237 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term56 A P s t) = (term138 A P s t).
Proof. exact (TRANS (@lem4876218 A P s t) (@lem4876236 A P s t)). Qed.
Lemma lem4876238 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term139 A P s t) = (term140 A P s t).
Proof. exact (MK_COMB (@lem4876195) (@lem4876237 A P s t)). Qed.
Lemma lem4876243 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4876244 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4876243 (A -> Prop) Prop f x). Qed.
Lemma lem4876246 {A : Type'} (P : type686 A) (t : A -> Prop) : (P t) = (@I ((A -> Prop) -> Prop) P t).
Proof. exact (@lem4876244 A P t). Qed.
Lemma lem4876251 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4876252 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4876251 (A -> Prop) Prop f x). Qed.
Lemma lem4876254 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = (@I ((A -> Prop) -> Prop) P s).
Proof. exact (@lem4876252 A P s). Qed.
Lemma lem4876255 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4876256 {A : Type'} (P : type686 A) (s : A -> Prop) : (term141 A P s) = (term142 A P s).
Proof. exact (MK_COMB (@lem4876255) (@lem4876254 A P s)). Qed.
Lemma lem4876257 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term49 A s P t) = (term143 A s P t).
Proof. exact (MK_COMB (@lem4876256 A P s) (@lem4876246 A P t)). Qed.
Lemma lem4876258 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4876259 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term144 A s P t) = (term145 A s P t).
Proof. exact (MK_COMB (@lem4876258) (@lem4876257 A s P t)). Qed.
Lemma lem4876260 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term55 A P s t) = (term146 A P s t).
Proof. exact (MK_COMB (@lem4876259 A s P t) (@lem4876238 A P s t)). Qed.
Lemma lem4876261 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem4876268 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4876269 {A : Type'} (f : type636 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4876268 (A -> Prop) (type672 A) f x). Qed.
Lemma lem4876270 {A : Type'} (s : A -> Prop) : (@UNION A s) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) s).
Proof. exact (@lem4876269 A (@UNION A) s). Qed.
Lemma lem4876271 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4876272 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@UNION A s t) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) s t).
Proof. exact (MK_COMB (@lem4876270 A s) (@lem4876271 A t)). Qed.
Lemma lem4876274 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4876275 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem4876274 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem4876276 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) s t) = (term135 A s t).
Proof. exact (@lem4876275 A (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@UNION A) s) t). Qed.
Lemma lem4876278 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@UNION A s t) = (term135 A s t).
Proof. exact (TRANS (@lem4876272 A s t) (@lem4876276 A s t)). Qed.
Lemma lem4876279 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term44 A P s t) = (term147 A P s t).
Proof. exact (MK_COMB (@lem4876261 A P) (@lem4876278 A s t)). Qed.
Lemma lem4876281 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4876282 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4876281 (A -> Prop) Prop f x). Qed.
Lemma lem4876283 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term147 A P s t) = (term148 A P s t).
Proof. exact (@lem4876282 A P (term135 A s t)). Qed.
Lemma lem4876284 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term44 A P s t) = (term148 A P s t).
Proof. exact (TRANS (@lem4876279 A P s t) (@lem4876283 A P s t)). Qed.
Lemma lem4876285 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4876290 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4876291 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4876290 (A -> Prop) Prop f x). Qed.
Lemma lem4876293 {A : Type'} (P : type686 A) (t : A -> Prop) : (P t) = (@I ((A -> Prop) -> Prop) P t).
Proof. exact (@lem4876291 A P t). Qed.
Lemma lem4876294 {A : Type'} (P : type686 A) (t : A -> Prop) : (term126 A P t) = (term127 A P t).
Proof. exact (MK_COMB (@lem4876285) (@lem4876293 A P t)). Qed.
Lemma lem4876295 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4876300 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4876301 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4876300 (A -> Prop) Prop f x). Qed.
Lemma lem4876303 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = (@I ((A -> Prop) -> Prop) P s).
Proof. exact (@lem4876301 A P s). Qed.
Lemma lem4876304 {A : Type'} (P : type686 A) (s : A -> Prop) : (term126 A P s) = (term127 A P s).
Proof. exact (MK_COMB (@lem4876295) (@lem4876303 A P s)). Qed.
Lemma lem4876305 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4876306 {A : Type'} (P : type686 A) (s : A -> Prop) : (term128 A P s) = (term129 A P s).
Proof. exact (MK_COMB (@lem4876305) (@lem4876304 A P s)). Qed.
Lemma lem4876307 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term43 A s P t) = (term149 A s P t).
Proof. exact (MK_COMB (@lem4876306 A P s) (@lem4876294 A P t)). Qed.
Lemma lem4876308 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4876309 {A : Type'} (s : A -> Prop) (P : type686 A) (t : A -> Prop) : (term46 A s P t) = (term150 A s P t).
Proof. exact (MK_COMB (@lem4876308) (@lem4876307 A s P t)). Qed.
Lemma lem4876310 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term48 A P s t) = (term151 A P s t).
Proof. exact (MK_COMB (@lem4876309 A s P t) (@lem4876284 A P s t)). Qed.
Lemma lem4876311 {A : Type'} (P : type686 A) (s : A -> Prop) : (term50 A P s) = (term152 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4876310 A P s t)). Qed.
Lemma lem4876312 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4876313 {A : Type'} (P : type686 A) (s : A -> Prop) : (term51 A P s) = (term153 A P s).
Proof. exact (MK_COMB (@lem4876312 A) (@lem4876311 A P s)). Qed.
Lemma lem4876314 {A : Type'} (P : type686 A) : (term52 A P) = (term154 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4876313 A P s)). Qed.
Lemma lem4876315 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4876316 {A : Type'} (P : type686 A) : (term53 A P) = (term155 A P).
Proof. exact (MK_COMB (@lem4876315 A) (@lem4876314 A P)). Qed.
Lemma lem4876317 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4876318 {A : Type'} (P : type686 A) : (term74 A P) = (term156 A P).
Proof. exact (MK_COMB (@lem4876317) (@lem4876316 A P)). Qed.
Lemma lem4876319 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term110 A P s t) = (term157 A P s t).
Proof. exact (MK_COMB (@lem4876318 A P) (@lem4876260 A P s t)). Qed.
Lemma lem4876320 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term157 A P s t.
Proof. exact (EQ_MP (@lem4876319 A P s t) (@lem4876148 A P s t h1)). Qed.
Lemma lem4876321 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term146 A P s t.
Proof. exact (proj2 (@lem4876320 A P s t h1)). Qed.
Lemma lem4876322 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term155 A P.
Proof. exact (proj1 (@lem4876320 A P s t h1)). Qed.
Lemma lem4876324 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term143 A s P t.
Proof. exact (proj1 (@lem4876321 A P s t h1)). Qed.
Lemma lem4876334 {A : Type'} (P : type686 A) (s : A -> Prop) : (term130 A P s) = (term130 A P s).
Proof. exact (eq_refl (term130 A P s)). Qed.
Lemma lem4876335 {A : Type'} (P : type686 A) : (term131 A P) = (term131 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4876334 A P s)). Qed.
Lemma lem4876336 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4876337 {A : Type'} (P : type686 A) : (term132 A P) = (term132 A P).
Proof. exact (MK_COMB (@lem4876336 A) (@lem4876335 A P)). Qed.
Lemma lem4876338 {A : Type'} : (term133 A) = (term133 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4876337 A P)). Qed.
Lemma lem4876339 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4876341 {A : Type'} : (term134 A) = (term134 A).
Proof. exact (MK_COMB (@lem4876339 A) (@lem4876338 A)). Qed.
Lemma lem4876342 {A : Type'} (h1 : term20 A) : term134 A.
Proof. exact (EQ_MP (@lem4876341 A) (@lem4876194 A h1)). Qed.
Lemma lem4876356 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term151 A P s t) = (term151 A P s t).
Proof. exact (eq_refl (term151 A P s t)). Qed.
Lemma lem4876357 {A : Type'} (P : type686 A) (s : A -> Prop) : (term152 A P s) = (term152 A P s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4876356 A P s t)). Qed.
Lemma lem4876358 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4876359 {A : Type'} (P : type686 A) (s : A -> Prop) : (term153 A P s) = (term153 A P s).
Proof. exact (MK_COMB (@lem4876358 A) (@lem4876357 A P s)). Qed.
Lemma lem4876360 {A : Type'} (P : type686 A) : (term154 A P) = (term154 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4876359 A P s)). Qed.
Lemma lem4876361 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4876363 {A : Type'} (P : type686 A) : (term155 A P) = (term155 A P).
Proof. exact (MK_COMB (@lem4876361 A) (@lem4876360 A P)). Qed.
Lemma lem4876364 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term155 A P.
Proof. exact (EQ_MP (@lem4876363 A P) (@lem4876322 A P s t h1)). Qed.
Lemma lem4876377 {A : Type'} (_60339 : type686 A) (h1 : term20 A) : term158 A _60339.
Proof. exact (@lem4876342 A h1 _60339). Qed.
Lemma lem4876378 {A : Type'} (_60339 : type686 A) : (term158 A _60339) = (term132 A _60339).
Proof. exact (eq_refl (term158 A _60339)). Qed.
Lemma lem4876379 {A : Type'} (_60339 : type686 A) (h1 : term20 A) : term132 A _60339.
Proof. exact (EQ_MP (@lem4876378 A _60339) (@lem4876377 A _60339 h1)). Qed.
Lemma lem4876380 {A : Type'} (_60339 : type686 A) (_60340 : A -> Prop) (h1 : term20 A) : term159 A _60339 _60340.
Proof. exact (@lem4876379 A _60339 h1 _60340). Qed.
Lemma lem4876381 {A : Type'} (_60339 : type686 A) (_60340 : A -> Prop) : (term159 A _60339 _60340) = (term130 A _60339 _60340).
Proof. exact (eq_refl (term159 A _60339 _60340)). Qed.
Lemma lem4876383 {A : Type'} (_60341 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term160 A P _60341.
Proof. exact (@lem4876364 A P s t h1 _60341). Qed.
Lemma lem4876384 {A : Type'} (P : type686 A) (_60341 : A -> Prop) : (term160 A P _60341) = (term153 A P _60341).
Proof. exact (eq_refl (term160 A P _60341)). Qed.
Lemma lem4876385 {A : Type'} (_60341 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term153 A P _60341.
Proof. exact (EQ_MP (@lem4876384 A P _60341) (@lem4876383 A _60341 P s t h1)). Qed.
Lemma lem4876386 {A : Type'} (_60341 : A -> Prop) (_60342 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term161 A P _60341 _60342.
Proof. exact (@lem4876385 A _60341 P s t h1 _60342). Qed.
Lemma lem4876387 {A : Type'} (P : type686 A) (_60341 : A -> Prop) (_60342 : A -> Prop) : (term161 A P _60341 _60342) = (term151 A P _60341 _60342).
Proof. exact (eq_refl (term161 A P _60341 _60342)). Qed.
Lemma lem4876388 {A : Type'} (_60341 : A -> Prop) (_60342 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term151 A P _60341 _60342.
Proof. exact (EQ_MP (@lem4876387 A P _60341 _60342) (@lem4876386 A _60341 _60342 P s t h1)). Qed.
Lemma lem4876394 {A : Type'} (_60339 : type686 A) (_60340 : A -> Prop) (h1 : term20 A) : term130 A _60339 _60340.
Proof. exact (EQ_MP (@lem4876381 A _60339 _60340) (@lem4876380 A _60339 _60340 h1)). Qed.
Lemma lem4876405 {A : Type'} (P : type686 A) (_60341 : A -> Prop) (_60342 : A -> Prop) : (term151 A P _60341 _60342) = (term162 A P _60341 _60342).
Proof. exact (@lem4875567 (term127 A P _60341) (term127 A P _60342) (term148 A P _60341 _60342)). Qed.
Lemma lem4876406 {A : Type'} (_60341 : A -> Prop) (_60342 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term162 A P _60341 _60342.
Proof. exact (EQ_MP (@lem4876405 A P _60341 _60342) (@lem4876388 A _60341 _60342 P s t h1)). Qed.
Lemma lem4876408 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term140 A P s t.
Proof. exact (proj2 (@lem4876321 A P s t h1)). Qed.
Lemma lem4876414 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : @I ((A -> Prop) -> Prop) P s.
Proof. exact (proj1 (@lem4876324 A P s t h1)). Qed.
Lemma lem4876415 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term163 A P s.
Proof. exact (fun h0 : term127 A P s => @lem4876414 A P s t h1). Qed.
Lemma lem4876417 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4876418 {A : Type'} (P : type686 A) (s : A -> Prop) : (term163 A P s) = (@I ((A -> Prop) -> Prop) P s).
Proof. exact (@lem4876417 (@I ((A -> Prop) -> Prop) P s)). Qed.
Lemma lem4876419 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : @I ((A -> Prop) -> Prop) P s.
Proof. exact (EQ_MP (@lem4876418 A P s) (@lem4876415 A P s t h1)). Qed.
Lemma lem4876421 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : @I ((A -> Prop) -> Prop) P t.
Proof. exact (proj2 (@lem4876324 A P s t h1)). Qed.
Lemma lem4876422 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term163 A P t.
Proof. exact (fun h0 : term127 A P t => @lem4876421 A P s t h1). Qed.
Lemma lem4876424 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4876425 {A : Type'} (P : type686 A) (t : A -> Prop) : (term163 A P t) = (@I ((A -> Prop) -> Prop) P t).
Proof. exact (@lem4876424 (@I ((A -> Prop) -> Prop) P t)). Qed.
Lemma lem4876426 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : @I ((A -> Prop) -> Prop) P t.
Proof. exact (EQ_MP (@lem4876425 A P t) (@lem4876422 A P s t h1)). Qed.
Lemma lem4876442 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4876443 {A : Type'} (_60341 : A -> Prop) (P : type686 A) (_60342 : A -> Prop) : (term165 A P _60341 _60342) = (term166 A _60341 P _60342).
Proof. exact (@lem4876442 (term148 A P _60341 _60342) (term127 A P _60342)). Qed.
Lemma lem4876449 {A : Type'} (P : type686 A) (_60341 : A -> Prop) : (term129 A P _60341) = (term129 A P _60341).
Proof. exact (eq_refl (term129 A P _60341)). Qed.
Lemma lem4876450 {A : Type'} (_60341 : A -> Prop) (P : type686 A) (_60342 : A -> Prop) : (term162 A P _60341 _60342) = (term167 A _60341 P _60342).
Proof. exact (MK_COMB (@lem4876449 A P _60341) (@lem4876443 A _60341 P _60342)). Qed.
Lemma lem4876454 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4876455 {A : Type'} (_60341 : A -> Prop) (P : type686 A) (_60342 : A -> Prop) : (term167 A _60341 P _60342) = (term168 A _60341 P _60342).
Proof. exact (@lem4876454 (term148 A P _60341 _60342) (term127 A P _60341) (term127 A P _60342)). Qed.
Lemma lem4876471 {A : Type'} (_60341 : A -> Prop) (P : type686 A) (_60342 : A -> Prop) : (term162 A P _60341 _60342) = (term168 A _60341 P _60342).
Proof. exact (TRANS (@lem4876450 A _60341 P _60342) (@lem4876455 A _60341 P _60342)). Qed.
Lemma lem4876472 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4876473 {A : Type'} (_60341 : A -> Prop) (P : type686 A) (_60342 : A -> Prop) : (term169 A P _60341 _60342) = (term170 A _60341 P _60342).
Proof. exact (MK_COMB (@lem4876472) (@lem4876471 A _60341 P _60342)). Qed.
Lemma lem4876489 {A : Type'} (_60341 : A -> Prop) (P : type686 A) (_60342 : A -> Prop) : (term168 A _60341 P _60342) = (term168 A _60341 P _60342).
Proof. exact (eq_refl (term168 A _60341 P _60342)). Qed.
Lemma lem4876490 {A : Type'} (_60341 : A -> Prop) (P : type686 A) (_60342 : A -> Prop) : ((term162 A P _60341 _60342) = (term168 A _60341 P _60342)) = ((term168 A _60341 P _60342) = (term168 A _60341 P _60342)).
Proof. exact (MK_COMB (@lem4876473 A _60341 P _60342) (@lem4876489 A _60341 P _60342)). Qed.
Lemma lem4876492 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4876493 (x : Prop) : (x = x) = True.
Proof. exact (@lem4876492 Prop x). Qed.
Lemma lem4876494 {A : Type'} (_60341 : A -> Prop) (P : type686 A) (_60342 : A -> Prop) : ((term168 A _60341 P _60342) = (term168 A _60341 P _60342)) = True.
Proof. exact (@lem4876493 (term168 A _60341 P _60342)). Qed.
Lemma lem4876495 {A : Type'} (_60341 : A -> Prop) (P : type686 A) (_60342 : A -> Prop) : ((term162 A P _60341 _60342) = (term168 A _60341 P _60342)) = True.
Proof. exact (TRANS (@lem4876490 A _60341 P _60342) (@lem4876494 A _60341 P _60342)). Qed.
Lemma lem4876496 {A : Type'} (_60341 : A -> Prop) (P : type686 A) (_60342 : A -> Prop) : True = ((term162 A P _60341 _60342) = (term168 A _60341 P _60342)).
Proof. exact (SYM (@lem4876495 A _60341 P _60342)). Qed.
Lemma lem4876497 {A : Type'} (_60341 : A -> Prop) (P : type686 A) (_60342 : A -> Prop) : (term162 A P _60341 _60342) = (term168 A _60341 P _60342).
Proof. exact (EQ_MP (@lem4876496 A _60341 P _60342) (@lem0)). Qed.
Lemma lem4876498 {A : Type'} (_60341 : A -> Prop) (_60342 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term168 A _60341 P _60342.
Proof. exact (EQ_MP (@lem4876497 A _60341 P _60342) (@lem4876406 A _60341 _60342 P s t h1)). Qed.
Lemma lem4876500 (b : Prop) (a : Prop) : (a \/ b) = (term171 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4876501 {A : Type'} (P : type686 A) (_60341 : A -> Prop) (_60342 : A -> Prop) : (term168 A _60341 P _60342) = (term172 A P _60341 _60342).
Proof. exact (@lem4876500 (term149 A _60341 P _60342) (term148 A P _60341 _60342)). Qed.
Lemma lem4876503 (a : Prop) (b : Prop) : (term173 a b) = (term174 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4876504 {A : Type'} (_60341 : A -> Prop) (P : type686 A) (_60342 : A -> Prop) : (term175 A _60341 P _60342) = (term176 A _60341 P _60342).
Proof. exact (@lem4876503 (term127 A P _60341) (term127 A P _60342)). Qed.
Lemma lem4876506 (a : Prop) : (term177 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4876507 {A : Type'} (P : type686 A) (_60341 : A -> Prop) : (term178 A P _60341) = (@I ((A -> Prop) -> Prop) P _60341).
Proof. exact (@lem4876506 (@I ((A -> Prop) -> Prop) P _60341)). Qed.
Lemma lem4876508 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4876509 {A : Type'} (P : type686 A) (_60341 : A -> Prop) : (term179 A P _60341) = (term142 A P _60341).
Proof. exact (MK_COMB (@lem4876508) (@lem4876507 A P _60341)). Qed.
Lemma lem4876511 (a : Prop) : (term177 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4876512 {A : Type'} (P : type686 A) (_60342 : A -> Prop) : (term178 A P _60342) = (@I ((A -> Prop) -> Prop) P _60342).
Proof. exact (@lem4876511 (@I ((A -> Prop) -> Prop) P _60342)). Qed.
Lemma lem4876513 {A : Type'} (_60341 : A -> Prop) (P : type686 A) (_60342 : A -> Prop) : (term176 A _60341 P _60342) = (term143 A _60341 P _60342).
Proof. exact (MK_COMB (@lem4876509 A P _60341) (@lem4876512 A P _60342)). Qed.
Lemma lem4876514 {A : Type'} (_60341 : A -> Prop) (P : type686 A) (_60342 : A -> Prop) : (term175 A _60341 P _60342) = (term143 A _60341 P _60342).
Proof. exact (TRANS (@lem4876504 A _60341 P _60342) (@lem4876513 A _60341 P _60342)). Qed.
Lemma lem4876515 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4876516 {A : Type'} (_60341 : A -> Prop) (P : type686 A) (_60342 : A -> Prop) : (term180 A _60341 P _60342) = (term181 A _60341 P _60342).
Proof. exact (MK_COMB (@lem4876515) (@lem4876514 A _60341 P _60342)). Qed.
Lemma lem4876517 {A : Type'} (P : type686 A) (_60341 : A -> Prop) (_60342 : A -> Prop) : (term148 A P _60341 _60342) = (term148 A P _60341 _60342).
Proof. exact (eq_refl (term148 A P _60341 _60342)). Qed.
Lemma lem4876518 {A : Type'} (P : type686 A) (_60341 : A -> Prop) (_60342 : A -> Prop) : (term172 A P _60341 _60342) = (term182 A P _60341 _60342).
Proof. exact (MK_COMB (@lem4876516 A _60341 P _60342) (@lem4876517 A P _60341 _60342)). Qed.
Lemma lem4876519 {A : Type'} (P : type686 A) (_60341 : A -> Prop) (_60342 : A -> Prop) : (term168 A _60341 P _60342) = (term182 A P _60341 _60342).
Proof. exact (TRANS (@lem4876501 A P _60341 _60342) (@lem4876518 A P _60341 _60342)). Qed.
Lemma lem4876521 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term143 A s P t.
Proof. exact (conj (@lem4876419 A P s t h1) (@lem4876426 A P s t h1)). Qed.
Lemma lem4876523 {A : Type'} (_60341 : A -> Prop) (_60342 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term182 A P _60341 _60342.
Proof. exact (EQ_MP (@lem4876519 A P _60341 _60342) (@lem4876498 A _60341 _60342 P s t h1)). Qed.
Lemma lem4876524 {A : Type'} (_60341 : A -> Prop) (_60342 : A -> Prop) (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term182 A P _60341 _60342.
Proof. exact (@lem4876523 A _60341 _60342 P s t h1). Qed.
Lemma lem4876525 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term182 A P s t.
Proof. exact (@lem4876524 A s t P s t h1). Qed.
Lemma lem4876528 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term148 A P s t.
Proof. exact (@lem4876525 A P s t h1 (@lem4876521 A P s t h1)). Qed.
Lemma lem4876529 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term183 A P s t.
Proof. exact (fun h0 : term184 A P s t => @lem4876528 A P s t h1). Qed.
Lemma lem4876531 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4876532 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term183 A P s t) = (term148 A P s t).
Proof. exact (@lem4876531 (term148 A P s t)). Qed.
Lemma lem4876533 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term148 A P s t.
Proof. exact (EQ_MP (@lem4876532 A P s t) (@lem4876529 A P s t h1)). Qed.
Lemma lem4876539 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4876540 {A : Type'} (_60339 : type686 A) (_60340 : A -> Prop) : (term130 A _60339 _60340) = (term185 A _60339 _60340).
Proof. exact (@lem4876539 (term125 A _60339 _60340) (term127 A _60339 _60340)). Qed.
Lemma lem4876546 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4876547 {A : Type'} (_60339 : type686 A) (_60340 : A -> Prop) : (term186 A _60339 _60340) = (term187 A _60339 _60340).
Proof. exact (MK_COMB (@lem4876546) (@lem4876540 A _60339 _60340)). Qed.
Lemma lem4876553 {A : Type'} (_60339 : type686 A) (_60340 : A -> Prop) : (term185 A _60339 _60340) = (term185 A _60339 _60340).
Proof. exact (eq_refl (term185 A _60339 _60340)). Qed.
Lemma lem4876554 {A : Type'} (_60339 : type686 A) (_60340 : A -> Prop) : ((term130 A _60339 _60340) = (term185 A _60339 _60340)) = ((term185 A _60339 _60340) = (term185 A _60339 _60340)).
Proof. exact (MK_COMB (@lem4876547 A _60339 _60340) (@lem4876553 A _60339 _60340)). Qed.
Lemma lem4876556 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4876557 (x : Prop) : (x = x) = True.
Proof. exact (@lem4876556 Prop x). Qed.
Lemma lem4876558 {A : Type'} (_60339 : type686 A) (_60340 : A -> Prop) : ((term185 A _60339 _60340) = (term185 A _60339 _60340)) = True.
Proof. exact (@lem4876557 (term185 A _60339 _60340)). Qed.
Lemma lem4876559 {A : Type'} (_60339 : type686 A) (_60340 : A -> Prop) : ((term130 A _60339 _60340) = (term185 A _60339 _60340)) = True.
Proof. exact (TRANS (@lem4876554 A _60339 _60340) (@lem4876558 A _60339 _60340)). Qed.
Lemma lem4876560 {A : Type'} (_60339 : type686 A) (_60340 : A -> Prop) : True = ((term130 A _60339 _60340) = (term185 A _60339 _60340)).
Proof. exact (SYM (@lem4876559 A _60339 _60340)). Qed.
Lemma lem4876561 {A : Type'} (_60339 : type686 A) (_60340 : A -> Prop) : (term130 A _60339 _60340) = (term185 A _60339 _60340).
Proof. exact (EQ_MP (@lem4876560 A _60339 _60340) (@lem0)). Qed.
Lemma lem4876562 {A : Type'} (_60339 : type686 A) (_60340 : A -> Prop) (h1 : term20 A) : term185 A _60339 _60340.
Proof. exact (EQ_MP (@lem4876561 A _60339 _60340) (@lem4876394 A _60339 _60340 h1)). Qed.
Lemma lem4876564 (b : Prop) (a : Prop) : (a \/ b) = (term171 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4876565 {A : Type'} (_60339 : type686 A) (_60340 : A -> Prop) : (term185 A _60339 _60340) = (term188 A _60339 _60340).
Proof. exact (@lem4876564 (term127 A _60339 _60340) (term125 A _60339 _60340)). Qed.
Lemma lem4876567 (a : Prop) : (term177 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4876568 {A : Type'} (_60339 : type686 A) (_60340 : A -> Prop) : (term178 A _60339 _60340) = (@I ((A -> Prop) -> Prop) _60339 _60340).
Proof. exact (@lem4876567 (@I ((A -> Prop) -> Prop) _60339 _60340)). Qed.
Lemma lem4876569 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4876570 {A : Type'} (_60339 : type686 A) (_60340 : A -> Prop) : (term189 A _60339 _60340) = (term190 A _60339 _60340).
Proof. exact (MK_COMB (@lem4876569) (@lem4876568 A _60339 _60340)). Qed.
Lemma lem4876571 {A : Type'} (_60339 : type686 A) (_60340 : A -> Prop) : (term125 A _60339 _60340) = (term125 A _60339 _60340).
Proof. exact (eq_refl (term125 A _60339 _60340)). Qed.
Lemma lem4876572 {A : Type'} (_60339 : type686 A) (_60340 : A -> Prop) : (term188 A _60339 _60340) = (term191 A _60339 _60340).
Proof. exact (MK_COMB (@lem4876570 A _60339 _60340) (@lem4876571 A _60339 _60340)). Qed.
Lemma lem4876573 {A : Type'} (_60339 : type686 A) (_60340 : A -> Prop) : (term185 A _60339 _60340) = (term191 A _60339 _60340).
Proof. exact (TRANS (@lem4876565 A _60339 _60340) (@lem4876572 A _60339 _60340)). Qed.
Lemma lem4876576 {A : Type'} (_60339 : type686 A) (_60340 : A -> Prop) (h1 : term20 A) : term191 A _60339 _60340.
Proof. exact (EQ_MP (@lem4876573 A _60339 _60340) (@lem4876562 A _60339 _60340 h1)). Qed.
Lemma lem4876577 {A : Type'} (_60339 : type686 A) (_60340 : A -> Prop) (h1 : term20 A) : term191 A _60339 _60340.
Proof. exact (@lem4876576 A _60339 _60340 h1). Qed.
Lemma lem4876578 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) : term192 A P s t.
Proof. exact (@lem4876577 A P (term135 A s t) h1). Qed.
Lemma lem4876581 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) (h2 : term110 A P s t) : term138 A P s t.
Proof. exact (@lem4876578 A P s t h1 (@lem4876533 A P s t h2)). Qed.
Lemma lem4876582 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) (h2 : term110 A P s t) : term193 A P s t.
Proof. exact (fun h0 : term140 A P s t => @lem4876581 A P s t h1 h2). Qed.
Lemma lem4876584 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4876585 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term193 A P s t) = (term138 A P s t).
Proof. exact (@lem4876584 (term138 A P s t)). Qed.
Lemma lem4876586 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) (h2 : term110 A P s t) : term138 A P s t.
Proof. exact (EQ_MP (@lem4876585 A P s t) (@lem4876582 A P s t h1 h2)). Qed.
Lemma lem4876589 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4876591 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) : (term140 A P s t) = (term194 A P s t).
Proof. exact (@lem4876589 (term138 A P s t)). Qed.
Lemma lem4876594 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term110 A P s t) : term194 A P s t.
Proof. exact (EQ_MP (@lem4876591 A P s t) (@lem4876408 A P s t h1)). Qed.
Lemma lem4876597 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) (h2 : term110 A P s t) : False.
Proof. exact (@lem4876594 A P s t h2 (@lem4876586 A P s t h1 h2)). Qed.
Lemma lem4876598 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) (h2 : term110 A P s t) : term195.
Proof. exact (fun h0 : ~ False => @lem4876597 A P s t h1 h2). Qed.
Lemma lem4876600 (p : Prop) : (term164 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4876601 : term195 = False.
Proof. exact (@lem4876600 False). Qed.
Lemma lem4876602 {A : Type'} (P : type686 A) (s : A -> Prop) (t : A -> Prop) (h1 : term20 A) (h2 : term110 A P s t) : False.
Proof. exact (EQ_MP (@lem4876601) (@lem4876598 A P s t h1 h2)). Qed.
Lemma lem4876603 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term20 A) (h2 : term113 A P s) : False.
Proof. exact (ex_elim (@lem4876147 A P s h2) (fun t : A -> Prop => fun h0 : term112 A P s t => @lem4876602 A P s t h1 h0)). Qed.
Lemma lem4876604 {A : Type'} (P : type686 A) (h1 : term20 A) (h2 : term115 A P) : False.
Proof. exact (ex_elim (@lem4876146 A P h2) (fun s : A -> Prop => fun h0 : term114 A P s => @lem4876603 A P s h1 h0)). Qed.
Lemma lem4876605 {A : Type'} (h1 : term20 A) (h2 : term19 A) : False.
Proof. exact (ex_elim (@lem4876075 A h2) (fun P : type686 A => fun h0 : term116 A P => @lem4876604 A P h1 h0)). Qed.
Lemma lem4876606 {A : Type'} (h1 : term19 A) : term25 A.
Proof. exact (fun h0 : term20 A => @lem4876605 A h0 h1). Qed.
Lemma lem4876607 {A : Type'} : (term25 A) = (term26 A).
Proof. exact (@lem69 (term20 A)). Qed.
Lemma lem4876608 {A : Type'} (h1 : term19 A) : term26 A.
Proof. exact (EQ_MP (@lem4876607 A) (@lem4876606 A h1)). Qed.
Lemma lem4876609 {A : Type'} : term28 A.
Proof. exact (fun h0 : term19 A => @lem4876608 A h0). Qed.
Lemma lem4876610 {A : Type'} : term21 A.
Proof. exact (EQ_MP (@lem4875805 A) (@lem4876609 A)). Qed.
Lemma lem4876612 {A : Type'} : term21 A.
Proof. exact (@lem4875638 A (@lem4876610 A)). Qed.
Lemma lem4876613 {A : Type'} (h1 : term19 A) : term25 A.
Proof. exact (@lem4876612 A (@lem4875620 A h1)). Qed.
Lemma lem4876614 {A : Type'} (h1 : term19 A) : False.
Proof. exact (@lem4876613 A h1 (@lem4875621 A)). Qed.
Lemma lem4876615 {A : Type'} (h1 : term19 A) : (term19 A) = False.
Proof. exact (prop_ext (fun h2 : term19 A => @lem4876614 A h1) (fun h2 : False => @lem4875620 A h1)). Qed.
Lemma lem4876616 {A : Type'} (h1 : term19 A) : False.
Proof. exact (EQ_MP (@lem4876615 A h1) (@lem4875620 A h1)). Qed.
Lemma lem4876617 {A : Type'} : term18 A.
Proof. exact (fun h0 : term19 A => @lem4876616 A h0). Qed.
Lemma lem4876618 {A : Type'} : term16 A.
Proof. exact (EQ_MP (@lem4875619 A) (@lem4876617 A)). Qed.
Lemma lem4876619 {A : Type'} : term15 A.
Proof. exact (EQ_MP (@lem4875615 A) (@lem4876618 A)). Qed.
