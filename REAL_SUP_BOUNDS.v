Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUP_BOUNDS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import MEMBER_NOT_EMPTY_spec.
Require Import SUP_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm129_spec.
Require Import thm1339577_spec.
Require Import thm137_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem5163729 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5163730 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5163731 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5163730 t1) (@lem5163729 t1)). Qed.
Lemma lem5163732 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5163731 t1 t2). Qed.
Lemma lem5163733 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5163734 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5163733 t1 t2) (@lem5163732 t1 t2)). Qed.
Lemma lem5163735 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5163734 t1 t2 t3). Qed.
Lemma lem5163736 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5163737 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5163736 t1 t2 t3) (@lem5163735 t1 t2 t3)). Qed.
Lemma lem5163738 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5163737 t1 t2 t3)). Qed.
Lemma lem5163740 {A : Type'} (s : A -> Prop) (h1 : (term7 A s) = (term8 A s)) : (term7 A s) = (term8 A s).
Proof. exact (h1). Qed.
Lemma lem5163741 {A : Type'} (s : A -> Prop) (h1 : (term7 A s) = (term8 A s)) : (term8 A s) = (term7 A s).
Proof. exact (SYM (@lem5163740 A s h1)). Qed.
Lemma lem5163742 {A : Type'} (s : A -> Prop) (h1 : (term8 A s) = (term7 A s)) : (term8 A s) = (term7 A s).
Proof. exact (h1). Qed.
Lemma lem5163743 {A : Type'} (s : A -> Prop) (h1 : (term8 A s) = (term7 A s)) : (term7 A s) = (term8 A s).
Proof. exact (SYM (@lem5163742 A s h1)). Qed.
Lemma lem5163744 {A : Type'} (s : A -> Prop) : ((term7 A s) = (term8 A s)) = ((term8 A s) = (term7 A s)).
Proof. exact (prop_ext (fun h1 : (term7 A s) = (term8 A s) => @lem5163741 A s h1) (fun h1 : (term8 A s) = (term7 A s) => @lem5163743 A s h1)). Qed.
Lemma lem5163745 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5163744 A s)). Qed.
Lemma lem5163746 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5163747 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (MK_COMB (@lem5163746 A) (@lem5163745 A)). Qed.
Lemma lem5163748 {A : Type'} : term12 A.
Proof. exact (EQ_MP (@lem5163747 A) (@lem3216368 A)). Qed.
Lemma lem5163749 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (@lem5163748 A s). Qed.
Lemma lem5163750 {A : Type'} (s : A -> Prop) : (term13 A s) = ((term8 A s) = (term7 A s)).
Proof. exact (eq_refl (term13 A s)). Qed.
Lemma lem5163762 (s : real -> Prop) : term14 s.
Proof. exact (@lem5136700 s). Qed.
Lemma lem5163763 (s : real -> Prop) : (term14 s) = (term15 s).
Proof. exact (eq_refl (term14 s)). Qed.
Lemma lem5163764 (s : real -> Prop) : term15 s.
Proof. exact (EQ_MP (@lem5163763 s) (@lem5163762 s)). Qed.
Lemma lem5163765 (s : real -> Prop) (a : real) (b : real) (h1 : term16 s a b) : term16 s a b.
Proof. exact (h1). Qed.
Lemma lem5163766 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term17 s a b.
Proof. exact (h1). Qed.
Lemma lem5163767 (s : real -> Prop) (h1 : term18 s) : term18 s.
Proof. exact (h1). Qed.
Lemma lem5163769 (p : Prop) (q : Prop) (r : Prop) : term19 p q r.
Proof. exact (@lem137 p q r (@lem129 p q r)). Qed.
Lemma lem5163770 (a : real) (s : real -> Prop) (b : real) : term20 a s b.
Proof. exact (@lem5163769 (term21 s) (term22 s) (term23 a s b)). Qed.
Lemma lem5163772 (p : Prop) : p = (term24 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5163773 (s : real -> Prop) : (term21 s) = (term25 s).
Proof. exact (@lem5163772 (term21 s)). Qed.
Lemma lem5163774 (s : real -> Prop) : (term25 s) = (term21 s).
Proof. exact (SYM (@lem5163773 s)). Qed.
Lemma lem5163775 (s : real -> Prop) (h1 : term26 s) : term26 s.
Proof. exact (h1). Qed.
Lemma lem5163778 (a : real) (b : real) (s : real -> Prop) (h1 : term27 a b s) : term27 a b s.
Proof. exact (h1). Qed.
Lemma lem5163779 (a : real) (b : real) (s : real -> Prop) : term28 a b s.
Proof. exact (fun h0 : term27 a b s => @lem5163778 a b s h0). Qed.
Lemma lem5163780 (a : real) (b : real) (s : real -> Prop) (h1 : term28 a b s) : term28 a b s.
Proof. exact (h1). Qed.
Lemma lem5163781 (a : real) (b : real) (s : real -> Prop) (h1 : term27 a b s) : term27 a b s.
Proof. exact (h1). Qed.
Lemma lem5163782 (a : real) (b : real) (s : real -> Prop) (h1 : term27 a b s) (h2 : term28 a b s) : term27 a b s.
Proof. exact (@lem5163780 a b s h2 (@lem5163781 a b s h1)). Qed.
Lemma lem5163783 (a : real) (b : real) (s : real -> Prop) (h1 : term27 a b s) : term29 a b s.
Proof. exact (fun h0 : term28 a b s => @lem5163782 a b s h1 h0). Qed.
Lemma lem5163784 (a : real) (b : real) (s : real -> Prop) (h1 : term28 a b s) : term28 a b s.
Proof. exact (h1). Qed.
Lemma lem5163785 (a : real) (b : real) (s : real -> Prop) (h1 : term27 a b s) (h2 : term28 a b s) : term27 a b s.
Proof. exact (@lem5163783 a b s h1 (@lem5163784 a b s h2)). Qed.
Lemma lem5163786 (a : real) (b : real) (s : real -> Prop) (h1 : term28 a b s) : term28 a b s.
Proof. exact (fun h0 : term27 a b s => @lem5163785 a b s h0 h1). Qed.
Lemma lem5163787 (a : real) (b : real) (s : real -> Prop) : term30 a b s.
Proof. exact (fun h0 : term28 a b s => @lem5163786 a b s h0). Qed.
Lemma lem5163790 (a : real) (b : real) (s : real -> Prop) : term28 a b s.
Proof. exact (@lem5163787 a b s (@lem5163779 a b s)). Qed.
Lemma lem5163816 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5163817 (s : real -> Prop) : (term25 s) = (term31 s).
Proof. exact (@lem5163816 (term26 s)). Qed.
Lemma lem5163819 (t : Prop) : (term32 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5163820 (s : real -> Prop) : (term31 s) = (term21 s).
Proof. exact (@lem5163819 (term21 s)). Qed.
Lemma lem5163823 (s : real -> Prop) : (term25 s) = (term21 s).
Proof. exact (TRANS (@lem5163817 s) (@lem5163820 s)). Qed.
Lemma lem5163834 (s : real -> Prop) (a : real) (b : real) : (term33 s a b) = (term33 s a b).
Proof. exact (eq_refl (term33 s a b)). Qed.
Lemma lem5163835 (a : real) (b : real) (s : real -> Prop) : (term34 a b s) = (term35 a b s).
Proof. exact (MK_COMB (@lem5163834 s a b) (@lem5163823 s)). Qed.
Lemma lem5163838 (s : real -> Prop) : (term36 s) = (term36 s).
Proof. exact (eq_refl (term36 s)). Qed.
Lemma lem5163839 (a : real) (b : real) (s : real -> Prop) : (term27 a b s) = (term37 a b s).
Proof. exact (MK_COMB (@lem5163838 s) (@lem5163835 a b s)). Qed.
Lemma lem5163842 (b : real) (s : real -> Prop) : (term38 b s) = (term39 b s).
Proof. exact (fun_ext (fun a : real => @lem5163839 a b s)). Qed.
Lemma lem5163843 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5163844 (b : real) (s : real -> Prop) : (term40 b s) = (term41 b s).
Proof. exact (MK_COMB (@lem5163843) (@lem5163842 b s)). Qed.
Lemma lem5163849 (s : real -> Prop) : (term42 s) = (term43 s).
Proof. exact (fun_ext (fun b : real => @lem5163844 b s)). Qed.
Lemma lem5163850 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5163851 (s : real -> Prop) : (term44 s) = (term45 s).
Proof. exact (MK_COMB (@lem5163850) (@lem5163849 s)). Qed.
Lemma lem5163856 : term46 = term47.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5163851 s)). Qed.
Lemma lem5163857 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5163866 : term48 = term49.
Proof. exact (MK_COMB (@lem5163857) (@lem5163856)). Qed.
Lemma lem5163871 (s : real -> Prop) (x : real) (b : real) : (term50 s x b) = (term50 s x b).
Proof. exact (eq_refl (term50 s x b)). Qed.
Lemma lem5163872 (s : real -> Prop) (b : real) : (term51 s b) = (term51 s b).
Proof. exact (fun_ext (fun x : real => @lem5163871 s x b)). Qed.
Lemma lem5163873 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5163874 (s : real -> Prop) (b : real) : (term52 s b) = (term52 s b).
Proof. exact (MK_COMB (@lem5163873) (@lem5163872 s b)). Qed.
Lemma lem5163875 (s : real -> Prop) : (term53 s) = (term53 s).
Proof. exact (fun_ext (fun b : real => @lem5163874 s b)). Qed.
Lemma lem5163876 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5163877 (s : real -> Prop) : (term54 s) = (term54 s).
Proof. exact (MK_COMB (@lem5163876) (@lem5163875 s)). Qed.
Lemma lem5163882 (s : real -> Prop) : (term55 s) = (term55 s).
Proof. exact (eq_refl (term55 s)). Qed.
Lemma lem5163883 (s : real -> Prop) : (term21 s) = (term21 s).
Proof. exact (MK_COMB (@lem5163882 s) (@lem5163877 s)). Qed.
Lemma lem5163892 (s : real -> Prop) (a : real) (x : real) (b : real) : (term56 s a x b) = (term56 s a x b).
Proof. exact (eq_refl (term56 s a x b)). Qed.
Lemma lem5163893 (s : real -> Prop) (a : real) (b : real) : (term57 s a b) = (term57 s a b).
Proof. exact (fun_ext (fun x : real => @lem5163892 s a x b)). Qed.
Lemma lem5163894 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5163895 (s : real -> Prop) (a : real) (b : real) : (term17 s a b) = (term17 s a b).
Proof. exact (MK_COMB (@lem5163894) (@lem5163893 s a b)). Qed.
Lemma lem5163896 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5163897 (s : real -> Prop) (a : real) (b : real) : (term33 s a b) = (term33 s a b).
Proof. exact (MK_COMB (@lem5163896) (@lem5163895 s a b)). Qed.
Lemma lem5163898 (a : real) (b : real) (s : real -> Prop) : (term35 a b s) = (term35 a b s).
Proof. exact (MK_COMB (@lem5163897 s a b) (@lem5163883 s)). Qed.
Lemma lem5163903 (s : real -> Prop) : (term36 s) = (term36 s).
Proof. exact (eq_refl (term36 s)). Qed.
Lemma lem5163904 (a : real) (b : real) (s : real -> Prop) : (term37 a b s) = (term37 a b s).
Proof. exact (MK_COMB (@lem5163903 s) (@lem5163898 a b s)). Qed.
Lemma lem5163905 (b : real) (s : real -> Prop) : (term39 b s) = (term39 b s).
Proof. exact (fun_ext (fun a : real => @lem5163904 a b s)). Qed.
Lemma lem5163906 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5163907 (b : real) (s : real -> Prop) : (term41 b s) = (term41 b s).
Proof. exact (MK_COMB (@lem5163906) (@lem5163905 b s)). Qed.
Lemma lem5163908 (s : real -> Prop) : (term43 s) = (term43 s).
Proof. exact (fun_ext (fun b : real => @lem5163907 b s)). Qed.
Lemma lem5163909 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5163910 (s : real -> Prop) : (term45 s) = (term45 s).
Proof. exact (MK_COMB (@lem5163909) (@lem5163908 s)). Qed.
Lemma lem5163911 : term47 = term47.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5163910 s)). Qed.
Lemma lem5163912 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5163913 : term49 = term49.
Proof. exact (MK_COMB (@lem5163912) (@lem5163911)). Qed.
Lemma lem5163964 : term48 = term49.
Proof. exact (TRANS (@lem5163866) (@lem5163913)). Qed.
Lemma lem5163965 : term49 = term48.
Proof. exact (SYM (@lem5163964)). Qed.
Lemma lem5163967 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term17 s a b.
Proof. exact (h1). Qed.
Lemma lem5163969 (p : Prop) : p = (term24 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5163970 (s : real -> Prop) : (term21 s) = (term25 s).
Proof. exact (@lem5163969 (term21 s)). Qed.
Lemma lem5163971 (s : real -> Prop) : (term25 s) = (term21 s).
Proof. exact (SYM (@lem5163970 s)). Qed.
Lemma lem5163972 (s : real -> Prop) (h1 : term26 s) : term26 s.
Proof. exact (h1). Qed.
Lemma lem5163978 (s : real -> Prop) (h1 : term18 s) : term18 s.
Proof. exact (h1). Qed.
Lemma lem5163989 (s : real -> Prop) (a : real) (x : real) (b : real) : (term56 s a x b) = (term58 s a x b).
Proof. exact (@lem17265 (@IN real x s) (term59 a x b)). Qed.
Lemma lem5163990 (s : real -> Prop) (a : real) (b : real) : (term57 s a b) = (term60 s a b).
Proof. exact (fun_ext (fun x : real => @lem5163989 s a x b)). Qed.
Lemma lem5163991 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5164044 (s : real -> Prop) (a : real) (b : real) : (term17 s a b) = (term61 s a b).
Proof. exact (MK_COMB (@lem5163991) (@lem5163990 s a b)). Qed.
Lemma lem5164045 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term61 s a b.
Proof. exact (EQ_MP (@lem5164044 s a b) (@lem5163967 s a b h1)). Qed.
Lemma lem5164048 (s : real -> Prop) : (term62 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5164055 (s : real -> Prop) (x : real) (b : real) : (term63 s x b) = (term64 s x b).
Proof. exact (@lem17362 (@IN real x s) (real_le x b)). Qed.
Lemma lem5164056 (P : real -> Prop) : (term65 P) = (term66 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5164057 (s : real -> Prop) (b : real) : (term67 s b) = (term68 s b).
Proof. exact (@lem5164056 (term51 s b)). Qed.
Lemma lem5164058 (s : real -> Prop) (x : real) (b : real) : (term69 s b x) = (term50 s x b).
Proof. exact (eq_refl (term69 s b x)). Qed.
Lemma lem5164059 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5164060 (s : real -> Prop) (x : real) (b : real) : (term70 s b x) = (term63 s x b).
Proof. exact (MK_COMB (@lem5164059) (@lem5164058 s x b)). Qed.
Lemma lem5164061 (s : real -> Prop) (x : real) (b : real) : (term70 s b x) = (term64 s x b).
Proof. exact (TRANS (@lem5164060 s x b) (@lem5164055 s x b)). Qed.
Lemma lem5164062 (s : real -> Prop) (b : real) : (term71 s b) = (term72 s b).
Proof. exact (fun_ext (fun x : real => @lem5164061 s x b)). Qed.
Lemma lem5164063 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5164064 (s : real -> Prop) (b : real) : (term68 s b) = (term73 s b).
Proof. exact (MK_COMB (@lem5164063) (@lem5164062 s b)). Qed.
Lemma lem5164065 (s : real -> Prop) (b : real) : (term67 s b) = (term73 s b).
Proof. exact (TRANS (@lem5164057 s b) (@lem5164064 s b)). Qed.
Lemma lem5164066 (P : real -> Prop) : (term74 P) = (term75 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5164067 (s : real -> Prop) : (term76 s) = (term77 s).
Proof. exact (@lem5164066 (term53 s)). Qed.
Lemma lem5164068 (s : real -> Prop) (b : real) : (term78 s b) = (term52 s b).
Proof. exact (eq_refl (term78 s b)). Qed.
Lemma lem5164069 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5164070 (s : real -> Prop) (b : real) : (term79 s b) = (term67 s b).
Proof. exact (MK_COMB (@lem5164069) (@lem5164068 s b)). Qed.
Lemma lem5164071 (s : real -> Prop) (b : real) : (term79 s b) = (term73 s b).
Proof. exact (TRANS (@lem5164070 s b) (@lem5164065 s b)). Qed.
Lemma lem5164072 (s : real -> Prop) : (term80 s) = (term81 s).
Proof. exact (fun_ext (fun b : real => @lem5164071 s b)). Qed.
Lemma lem5164073 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5164074 (s : real -> Prop) : (term77 s) = (term82 s).
Proof. exact (MK_COMB (@lem5164073) (@lem5164072 s)). Qed.
Lemma lem5164075 (s : real -> Prop) : (term76 s) = (term82 s).
Proof. exact (TRANS (@lem5164067 s) (@lem5164074 s)). Qed.
Lemma lem5164076 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5164077 (s : real -> Prop) : (term83 s) = (term84 s).
Proof. exact (MK_COMB (@lem5164076) (@lem5164048 s)). Qed.
Lemma lem5164078 (s : real -> Prop) : (term85 s) = (term86 s).
Proof. exact (MK_COMB (@lem5164077 s) (@lem5164075 s)). Qed.
Lemma lem5164079 (s : real -> Prop) : (term26 s) = (term85 s).
Proof. exact (@lem17045 (term18 s) (term54 s)). Qed.
Lemma lem5164080 (s : real -> Prop) : (term26 s) = (term86 s).
Proof. exact (TRANS (@lem5164079 s) (@lem5164078 s)). Qed.
Lemma lem5164135 {A B : Type'} (P : type1413 A B) : (term87 A B P) = (term88 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5164136 (P : type1626) : (term89 P) = (term90 P).
Proof. exact (@lem5164135 real real P). Qed.
Lemma lem5164137 (s : real -> Prop) : (term91 s) = (term92 s).
Proof. exact (@lem5164136 (term93 s)). Qed.
Lemma lem5164138 (s : real -> Prop) (b : real) : (term94 s b) = (term72 s b).
Proof. exact (eq_refl (term94 s b)). Qed.
Lemma lem5164139 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5164140 (s : real -> Prop) (b : real) (x : real) : (term95 s b x) = (term96 s b x).
Proof. exact (MK_COMB (@lem5164138 s b) (@lem5164139 x)). Qed.
Lemma lem5164141 (s : real -> Prop) (x : real) (b : real) : (term96 s b x) = (term64 s x b).
Proof. exact (eq_refl (term96 s b x)). Qed.
Lemma lem5164142 (s : real -> Prop) (x : real) (b : real) : (term95 s b x) = (term64 s x b).
Proof. exact (TRANS (@lem5164140 s b x) (@lem5164141 s x b)). Qed.
Lemma lem5164143 (s : real -> Prop) (b : real) : (term97 s b) = (term72 s b).
Proof. exact (fun_ext (fun x : real => @lem5164142 s x b)). Qed.
Lemma lem5164144 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5164145 (s : real -> Prop) (b : real) : (term98 s b) = (term73 s b).
Proof. exact (MK_COMB (@lem5164144) (@lem5164143 s b)). Qed.
Lemma lem5164146 (s : real -> Prop) : (term99 s) = (term81 s).
Proof. exact (fun_ext (fun b : real => @lem5164145 s b)). Qed.
Lemma lem5164147 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5164148 (s : real -> Prop) : (term91 s) = (term82 s).
Proof. exact (MK_COMB (@lem5164147) (@lem5164146 s)). Qed.
Lemma lem5164149 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5164150 (s : real -> Prop) : (term100 s) = (term101 s).
Proof. exact (MK_COMB (@lem5164149) (@lem5164148 s)). Qed.
Lemma lem5164151 (s : real -> Prop) (b : real) : (term94 s b) = (term72 s b).
Proof. exact (eq_refl (term94 s b)). Qed.
Lemma lem5164152 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5164153 (s : real -> Prop) (x : real -> real) (b : real) : (term102 s x b) = (term103 s x b).
Proof. exact (MK_COMB (@lem5164151 s b) (@lem5164152 x b)). Qed.
Lemma lem5164154 (s : real -> Prop) (x : real -> real) (b : real) : (term103 s x b) = (term104 s x b).
Proof. exact (eq_refl (term103 s x b)). Qed.
Lemma lem5164155 (s : real -> Prop) (x : real -> real) (b : real) : (term102 s x b) = (term104 s x b).
Proof. exact (TRANS (@lem5164153 s x b) (@lem5164154 s x b)). Qed.
Lemma lem5164156 (s : real -> Prop) (x : real -> real) : (term105 s x) = (term106 s x).
Proof. exact (fun_ext (fun b : real => @lem5164155 s x b)). Qed.
Lemma lem5164157 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5164158 (s : real -> Prop) (x : real -> real) : (term107 s x) = (term108 s x).
Proof. exact (MK_COMB (@lem5164157) (@lem5164156 s x)). Qed.
Lemma lem5164159 (s : real -> Prop) : (term109 s) = (term110 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5164158 s x)). Qed.
Lemma lem5164160 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5164161 (s : real -> Prop) : (term92 s) = (term111 s).
Proof. exact (MK_COMB (@lem5164160) (@lem5164159 s)). Qed.
Lemma lem5164162 (s : real -> Prop) : ((term91 s) = (term92 s)) = ((term82 s) = (term111 s)).
Proof. exact (MK_COMB (@lem5164150 s) (@lem5164161 s)). Qed.
Lemma lem5164163 (s : real -> Prop) : (term82 s) = (term111 s).
Proof. exact (EQ_MP (@lem5164162 s) (@lem5164137 s)). Qed.
Lemma lem5164164 (s : real -> Prop) : (term84 s) = (term84 s).
Proof. exact (eq_refl (term84 s)). Qed.
Lemma lem5164165 (s : real -> Prop) : (term86 s) = (term112 s).
Proof. exact (MK_COMB (@lem5164164 s) (@lem5164163 s)). Qed.
Lemma lem5164167 {A : Type'} (P : Prop) (Q : A -> Prop) : (term113 A P Q) = (term114 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5164168 (P : Prop) (Q : type1028) : (term115 P Q) = (term116 P Q).
Proof. exact (@lem5164167 (real -> real) P Q). Qed.
Lemma lem5164169 (s : real -> Prop) : (term117 s) = (term118 s).
Proof. exact (@lem5164168 (s = (@EMPTY real)) (term110 s)). Qed.
Lemma lem5164170 (s : real -> Prop) (x : real -> real) : (term119 s x) = (term108 s x).
Proof. exact (eq_refl (term119 s x)). Qed.
Lemma lem5164171 (s : real -> Prop) : (term120 s) = (term110 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5164170 s x)). Qed.
Lemma lem5164172 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5164173 (s : real -> Prop) : (term121 s) = (term111 s).
Proof. exact (MK_COMB (@lem5164172) (@lem5164171 s)). Qed.
Lemma lem5164174 (s : real -> Prop) : (term84 s) = (term84 s).
Proof. exact (eq_refl (term84 s)). Qed.
Lemma lem5164175 (s : real -> Prop) : (term117 s) = (term112 s).
Proof. exact (MK_COMB (@lem5164174 s) (@lem5164173 s)). Qed.
Lemma lem5164176 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5164177 (s : real -> Prop) : (term122 s) = (term123 s).
Proof. exact (MK_COMB (@lem5164176) (@lem5164175 s)). Qed.
Lemma lem5164178 (s : real -> Prop) (x : real -> real) : (term119 s x) = (term108 s x).
Proof. exact (eq_refl (term119 s x)). Qed.
Lemma lem5164179 (s : real -> Prop) : (term84 s) = (term84 s).
Proof. exact (eq_refl (term84 s)). Qed.
Lemma lem5164180 (s : real -> Prop) (x : real -> real) : (term124 s x) = (term125 s x).
Proof. exact (MK_COMB (@lem5164179 s) (@lem5164178 s x)). Qed.
Lemma lem5164181 (s : real -> Prop) : (term126 s) = (term127 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5164180 s x)). Qed.
Lemma lem5164182 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5164183 (s : real -> Prop) : (term118 s) = (term128 s).
Proof. exact (MK_COMB (@lem5164182) (@lem5164181 s)). Qed.
Lemma lem5164184 (s : real -> Prop) : ((term117 s) = (term118 s)) = ((term112 s) = (term128 s)).
Proof. exact (MK_COMB (@lem5164177 s) (@lem5164183 s)). Qed.
Lemma lem5164185 (s : real -> Prop) : (term112 s) = (term128 s).
Proof. exact (EQ_MP (@lem5164184 s) (@lem5164169 s)). Qed.
Lemma lem5164187 (s : real -> Prop) : (term86 s) = (term128 s).
Proof. exact (TRANS (@lem5164165 s) (@lem5164185 s)). Qed.
Lemma lem5164188 (s : real -> Prop) : (term26 s) = (term128 s).
Proof. exact (TRANS (@lem5164080 s) (@lem5164187 s)). Qed.
Lemma lem5164189 (s : real -> Prop) (h1 : term26 s) : term128 s.
Proof. exact (EQ_MP (@lem5164188 s) (@lem5163972 s h1)). Qed.
Lemma lem5164190 (s : real -> Prop) (x : real -> real) (h1 : term125 s x) : term125 s x.
Proof. exact (h1). Qed.
Lemma lem5164198 (s : real -> Prop) (h1 : term18 s) : term18 s.
Proof. exact (h1). Qed.
Lemma lem5164221 (s : real -> Prop) (a : real) (x : real) (b : real) : (term58 s a x b) = (term58 s a x b).
Proof. exact (eq_refl (term58 s a x b)). Qed.
Lemma lem5164222 (s : real -> Prop) (a : real) (b : real) : (term60 s a b) = (term60 s a b).
Proof. exact (fun_ext (fun x : real => @lem5164221 s a x b)). Qed.
Lemma lem5164223 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5164224 (s : real -> Prop) (a : real) (b : real) : (term61 s a b) = (term61 s a b).
Proof. exact (MK_COMB (@lem5164223) (@lem5164222 s a b)). Qed.
Lemma lem5164225 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term61 s a b.
Proof. exact (EQ_MP (@lem5164224 s a b) (@lem5164045 s a b h1)). Qed.
Lemma lem5164244 (s : real -> Prop) (x : real -> real) (b : real) : (term104 s x b) = (term104 s x b).
Proof. exact (eq_refl (term104 s x b)). Qed.
Lemma lem5164245 (s : real -> Prop) (x : real -> real) : (term106 s x) = (term106 s x).
Proof. exact (fun_ext (fun b : real => @lem5164244 s x b)). Qed.
Lemma lem5164246 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5164247 (s : real -> Prop) (x : real -> real) : (term108 s x) = (term108 s x).
Proof. exact (MK_COMB (@lem5164246) (@lem5164245 s x)). Qed.
Lemma lem5164254 (s : real -> Prop) : (term84 s) = (term84 s).
Proof. exact (eq_refl (term84 s)). Qed.
Lemma lem5164255 (s : real -> Prop) (x : real -> real) : (term125 s x) = (term125 s x).
Proof. exact (MK_COMB (@lem5164254 s) (@lem5164247 s x)). Qed.
Lemma lem5164256 (s : real -> Prop) (x : real -> real) (h1 : term125 s x) : term125 s x.
Proof. exact (EQ_MP (@lem5164255 s x) (@lem5164190 s x h1)). Qed.
Lemma lem5164258 (s : real -> Prop) (x : real -> real) (h1 : term108 s x) : term108 s x.
Proof. exact (h1). Qed.
Lemma lem5164262 (s : real -> Prop) (h1 : term18 s) : term18 s.
Proof. exact (h1). Qed.
Lemma lem5164289 (s : real -> Prop) (h1 : s = (@EMPTY real)) : s = (@EMPTY real).
Proof. exact (h1). Qed.
Lemma lem5164311 (a : real) (s : real -> Prop) (x : real) (b : real) : (term58 s a x b) = (term129 a s x b).
Proof. exact (@lem19490 (real_le a x) (term130 x s) (real_le x b)). Qed.
Lemma lem5164312 (a : real) (s : real -> Prop) (b : real) : (term60 s a b) = (term131 a s b).
Proof. exact (fun_ext (fun x : real => @lem5164311 a s x b)). Qed.
Lemma lem5164313 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5164315 (a : real) (s : real -> Prop) (b : real) : (term61 s a b) = (term132 a s b).
Proof. exact (MK_COMB (@lem5164313) (@lem5164312 a s b)). Qed.
Lemma lem5164316 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term132 a s b.
Proof. exact (EQ_MP (@lem5164315 a s b) (@lem5164225 s a b h1)). Qed.
Lemma lem5164322 (s : real -> Prop) (x : real -> real) (b : real) : (term104 s x b) = (term104 s x b).
Proof. exact (eq_refl (term104 s x b)). Qed.
Lemma lem5164323 (s : real -> Prop) (x : real -> real) : (term106 s x) = (term106 s x).
Proof. exact (fun_ext (fun b : real => @lem5164322 s x b)). Qed.
Lemma lem5164324 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5164326 (s : real -> Prop) (x : real -> real) : (term108 s x) = (term108 s x).
Proof. exact (MK_COMB (@lem5164324) (@lem5164323 s x)). Qed.
Lemma lem5164327 (s : real -> Prop) (x : real -> real) (h1 : term108 s x) : term108 s x.
Proof. exact (EQ_MP (@lem5164326 s x) (@lem5164258 s x h1)). Qed.
Lemma lem5164331 (_67499 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term133 a s b _67499.
Proof. exact (@lem5164316 s a b h1 _67499). Qed.
Lemma lem5164332 (a : real) (s : real -> Prop) (_67499 : real) (b : real) : (term133 a s b _67499) = (term129 a s _67499 b).
Proof. exact (eq_refl (term133 a s b _67499)). Qed.
Lemma lem5164333 (_67499 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term129 a s _67499 b.
Proof. exact (EQ_MP (@lem5164332 a s _67499 b) (@lem5164331 _67499 s a b h1)). Qed.
Lemma lem5164334 (_67500 : real) (s : real -> Prop) (x : real -> real) (h1 : term108 s x) : term134 s x _67500.
Proof. exact (@lem5164327 s x h1 _67500). Qed.
Lemma lem5164335 (s : real -> Prop) (x : real -> real) (_67500 : real) : (term134 s x _67500) = (term104 s x _67500).
Proof. exact (eq_refl (term134 s x _67500)). Qed.
Lemma lem5164336 (_67500 : real) (s : real -> Prop) (x : real -> real) (h1 : term108 s x) : term104 s x _67500.
Proof. exact (EQ_MP (@lem5164335 s x _67500) (@lem5164334 _67500 s x h1)). Qed.
Lemma lem5164344 (s : real -> Prop) (h1 : term18 s) : term18 s.
Proof. exact (h1). Qed.
Lemma lem5164346 (s : real -> Prop) (h1 : s = (@EMPTY real)) : s = (@EMPTY real).
Proof. exact (h1). Qed.
Lemma lem5164364 (_67500 : real) (s : real -> Prop) (x : real -> real) (h1 : term108 s x) : term135 x _67500.
Proof. exact (proj2 (@lem5164336 _67500 s x h1)). Qed.
Lemma lem5164376 (_67499 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term136 s _67499 b.
Proof. exact (proj2 (@lem5164333 _67499 s a b h1)). Qed.
Lemma lem5164391 : term137 = term137.
Proof. exact (eq_refl term137). Qed.
Lemma lem5164392 (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term138 s) = term139.
Proof. exact (MK_COMB (@lem5164391) (@lem5164346 s h1)). Qed.
Lemma lem5164393 : term139 = term140.
Proof. exact (eq_refl term139). Qed.
Lemma lem5164394 (s : real -> Prop) : (term141 s) = (term141 s).
Proof. exact (eq_refl (term141 s)). Qed.
Lemma lem5164395 (s : real -> Prop) : ((term138 s) = term139) = ((term138 s) = term140).
Proof. exact (MK_COMB (@lem5164394 s) (@lem5164393)). Qed.
Lemma lem5164396 (s : real -> Prop) : (term138 s) = (term18 s).
Proof. exact (eq_refl (term138 s)). Qed.
Lemma lem5164397 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5164398 (s : real -> Prop) : (term141 s) = (term142 s).
Proof. exact (MK_COMB (@lem5164397) (@lem5164396 s)). Qed.
Lemma lem5164399 : term140 = term140.
Proof. exact (eq_refl term140). Qed.
Lemma lem5164400 (s : real -> Prop) : ((term138 s) = term140) = ((term18 s) = term140).
Proof. exact (MK_COMB (@lem5164398 s) (@lem5164399)). Qed.
Lemma lem5164401 (s : real -> Prop) : ((term138 s) = term139) = ((term18 s) = term140).
Proof. exact (TRANS (@lem5164395 s) (@lem5164400 s)). Qed.
Lemma lem5164402 (s : real -> Prop) (h1 : s = (@EMPTY real)) : (term18 s) = term140.
Proof. exact (EQ_MP (@lem5164401 s) (@lem5164392 s h1)). Qed.
Lemma lem5164403 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : term140.
Proof. exact (EQ_MP (@lem5164402 s h2) (@lem5164344 s h1)). Qed.
Lemma lem5164473 (x : real -> Prop) : x = x.
Proof. exact (@lem21386 (real -> Prop) x). Qed.
Lemma lem5164474 : (@EMPTY real) = (@EMPTY real).
Proof. exact (@lem5164473 (@EMPTY real)). Qed.
Lemma lem5164475 : term143.
Proof. exact (fun h0 : term140 => @lem5164474). Qed.
Lemma lem5164477 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5164478 : term143 = ((@EMPTY real) = (@EMPTY real)).
Proof. exact (@lem5164477 ((@EMPTY real) = (@EMPTY real))). Qed.
Lemma lem5164479 : (@EMPTY real) = (@EMPTY real).
Proof. exact (EQ_MP (@lem5164478) (@lem5164475)). Qed.
Lemma lem5164482 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5164484 : term140 = term145.
Proof. exact (@lem5164482 ((@EMPTY real) = (@EMPTY real))). Qed.
Lemma lem5164487 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : term145.
Proof. exact (EQ_MP (@lem5164484) (@lem5164403 s h1 h2)). Qed.
Lemma lem5164490 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : False.
Proof. exact (@lem5164487 s h1 h2 (@lem5164479)). Qed.
Lemma lem5164491 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : term146.
Proof. exact (fun h0 : ~ False => @lem5164490 s h1 h2). Qed.
Lemma lem5164493 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5164494 : term146 = False.
Proof. exact (@lem5164493 False). Qed.
Lemma lem5164547 (_67500 : real) (s : real -> Prop) (x : real -> real) (h1 : term108 s x) : term147 x _67500 s.
Proof. exact (proj1 (@lem5164336 _67500 s x h1)). Qed.
Lemma lem5164548 (b : real) (s : real -> Prop) (x : real -> real) (h1 : term108 s x) : term147 x b s.
Proof. exact (@lem5164547 b s x h1). Qed.
Lemma lem5164549 (b : real) (s : real -> Prop) (x : real -> real) (h1 : term108 s x) : term148 x b s.
Proof. exact (fun h0 : term149 x b s => @lem5164548 b s x h1). Qed.
Lemma lem5164551 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5164552 (x : real -> real) (b : real) (s : real -> Prop) : (term148 x b s) = (term147 x b s).
Proof. exact (@lem5164551 (term147 x b s)). Qed.
Lemma lem5164553 (b : real) (s : real -> Prop) (x : real -> real) (h1 : term108 s x) : term147 x b s.
Proof. exact (EQ_MP (@lem5164552 x b s) (@lem5164549 b s x h1)). Qed.
Lemma lem5164559 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5164560 (b : real) (_67499 : real) (s : real -> Prop) : (term136 s _67499 b) = (term150 b _67499 s).
Proof. exact (@lem5164559 (real_le _67499 b) (term130 _67499 s)). Qed.
Lemma lem5164566 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5164567 (b : real) (_67499 : real) (s : real -> Prop) : (term151 s _67499 b) = (term152 b _67499 s).
Proof. exact (MK_COMB (@lem5164566) (@lem5164560 b _67499 s)). Qed.
Lemma lem5164573 (b : real) (_67499 : real) (s : real -> Prop) : (term150 b _67499 s) = (term150 b _67499 s).
Proof. exact (eq_refl (term150 b _67499 s)). Qed.
Lemma lem5164574 (b : real) (_67499 : real) (s : real -> Prop) : ((term136 s _67499 b) = (term150 b _67499 s)) = ((term150 b _67499 s) = (term150 b _67499 s)).
Proof. exact (MK_COMB (@lem5164567 b _67499 s) (@lem5164573 b _67499 s)). Qed.
Lemma lem5164576 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5164577 (x : Prop) : (x = x) = True.
Proof. exact (@lem5164576 Prop x). Qed.
Lemma lem5164578 (b : real) (_67499 : real) (s : real -> Prop) : ((term150 b _67499 s) = (term150 b _67499 s)) = True.
Proof. exact (@lem5164577 (term150 b _67499 s)). Qed.
Lemma lem5164579 (b : real) (_67499 : real) (s : real -> Prop) : ((term136 s _67499 b) = (term150 b _67499 s)) = True.
Proof. exact (TRANS (@lem5164574 b _67499 s) (@lem5164578 b _67499 s)). Qed.
Lemma lem5164580 (b : real) (_67499 : real) (s : real -> Prop) : True = ((term136 s _67499 b) = (term150 b _67499 s)).
Proof. exact (SYM (@lem5164579 b _67499 s)). Qed.
Lemma lem5164581 (b : real) (_67499 : real) (s : real -> Prop) : (term136 s _67499 b) = (term150 b _67499 s).
Proof. exact (EQ_MP (@lem5164580 b _67499 s) (@lem0)). Qed.
Lemma lem5164582 (_67499 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term150 b _67499 s.
Proof. exact (EQ_MP (@lem5164581 b _67499 s) (@lem5164376 _67499 s a b h1)). Qed.
Lemma lem5164584 (b : Prop) (a : Prop) : (a \/ b) = (term153 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5164585 (s : real -> Prop) (_67499 : real) (b : real) : (term150 b _67499 s) = (term154 s _67499 b).
Proof. exact (@lem5164584 (term130 _67499 s) (real_le _67499 b)). Qed.
Lemma lem5164587 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5164588 (_67499 : real) (s : real -> Prop) : (term155 _67499 s) = (@IN real _67499 s).
Proof. exact (@lem5164587 (@IN real _67499 s)). Qed.
Lemma lem5164589 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5164590 (_67499 : real) (s : real -> Prop) : (term156 _67499 s) = (term157 _67499 s).
Proof. exact (MK_COMB (@lem5164589) (@lem5164588 _67499 s)). Qed.
Lemma lem5164591 (_67499 : real) (b : real) : (real_le _67499 b) = (real_le _67499 b).
Proof. exact (eq_refl (real_le _67499 b)). Qed.
Lemma lem5164592 (s : real -> Prop) (_67499 : real) (b : real) : (term154 s _67499 b) = (term50 s _67499 b).
Proof. exact (MK_COMB (@lem5164590 _67499 s) (@lem5164591 _67499 b)). Qed.
Lemma lem5164593 (s : real -> Prop) (_67499 : real) (b : real) : (term150 b _67499 s) = (term50 s _67499 b).
Proof. exact (TRANS (@lem5164585 s _67499 b) (@lem5164592 s _67499 b)). Qed.
Lemma lem5164596 (_67499 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term50 s _67499 b.
Proof. exact (EQ_MP (@lem5164593 s _67499 b) (@lem5164582 _67499 s a b h1)). Qed.
Lemma lem5164597 (x : real -> real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term158 s x b.
Proof. exact (@lem5164596 (x b) s a b h1). Qed.
Lemma lem5164600 (x : real -> real) (s : real -> Prop) (a : real) (b : real) (h1 : term108 s x) (h2 : term17 s a b) : term159 x b.
Proof. exact (@lem5164597 x s a b h2 (@lem5164553 b s x h1)). Qed.
Lemma lem5164601 (x : real -> real) (s : real -> Prop) (a : real) (b : real) (h1 : term108 s x) (h2 : term17 s a b) : term160 x b.
Proof. exact (fun h0 : term135 x b => @lem5164600 x s a b h1 h2). Qed.
Lemma lem5164603 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5164604 (x : real -> real) (b : real) : (term160 x b) = (term159 x b).
Proof. exact (@lem5164603 (term159 x b)). Qed.
Lemma lem5164605 (x : real -> real) (s : real -> Prop) (a : real) (b : real) (h1 : term108 s x) (h2 : term17 s a b) : term159 x b.
Proof. exact (EQ_MP (@lem5164604 x b) (@lem5164601 x s a b h1 h2)). Qed.
Lemma lem5164608 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5164610 (x : real -> real) (_67500 : real) : (term135 x _67500) = (term161 x _67500).
Proof. exact (@lem5164608 (term159 x _67500)). Qed.
Lemma lem5164613 (_67500 : real) (s : real -> Prop) (x : real -> real) (h1 : term108 s x) : term161 x _67500.
Proof. exact (EQ_MP (@lem5164610 x _67500) (@lem5164364 _67500 s x h1)). Qed.
Lemma lem5164614 (b : real) (s : real -> Prop) (x : real -> real) (h1 : term108 s x) : term161 x b.
Proof. exact (@lem5164613 b s x h1). Qed.
Lemma lem5164617 (x : real -> real) (s : real -> Prop) (a : real) (b : real) (h1 : term108 s x) (h2 : term17 s a b) : False.
Proof. exact (@lem5164614 b s x h1 (@lem5164605 x s a b h1 h2)). Qed.
Lemma lem5164618 (x : real -> real) (s : real -> Prop) (a : real) (b : real) (h1 : term108 s x) (h2 : term17 s a b) : term146.
Proof. exact (fun h0 : ~ False => @lem5164617 x s a b h1 h2). Qed.
Lemma lem5164620 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5164621 : term146 = False.
Proof. exact (@lem5164620 False). Qed.
Lemma lem5164622 (x : real -> real) (s : real -> Prop) (a : real) (b : real) (h1 : term108 s x) (h2 : term17 s a b) : False.
Proof. exact (EQ_MP (@lem5164621) (@lem5164618 x s a b h1 h2)). Qed.
Lemma lem5164623 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : False.
Proof. exact (EQ_MP (@lem5164494) (@lem5164491 s h1 h2)). Qed.
Lemma lem5164624 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : (s = (@EMPTY real)) = False.
Proof. exact (prop_ext (fun h3 : s = (@EMPTY real) => @lem5164623 s h1 h2) (fun h3 : False => @lem5164346 s h2)). Qed.
Lemma lem5164625 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : False.
Proof. exact (EQ_MP (@lem5164624 s h1 h2) (@lem5164346 s h2)). Qed.
Lemma lem5164626 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : (term18 s) = False.
Proof. exact (prop_ext (fun h3 : term18 s => @lem5164625 s h1 h2) (fun h3 : False => @lem5164344 s h1)). Qed.
Lemma lem5164627 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : False.
Proof. exact (EQ_MP (@lem5164626 s h1 h2) (@lem5164344 s h1)). Qed.
Lemma lem5164628 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : (s = (@EMPTY real)) = False.
Proof. exact (prop_ext (fun h3 : s = (@EMPTY real) => @lem5164627 s h1 h2) (fun h3 : False => @lem5164289 s h2)). Qed.
Lemma lem5164629 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : False.
Proof. exact (EQ_MP (@lem5164628 s h1 h2) (@lem5164289 s h2)). Qed.
Lemma lem5164630 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : (term18 s) = False.
Proof. exact (prop_ext (fun h3 : term18 s => @lem5164629 s h1 h2) (fun h3 : False => @lem5164262 s h1)). Qed.
Lemma lem5164631 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : False.
Proof. exact (EQ_MP (@lem5164630 s h1 h2) (@lem5164262 s h1)). Qed.
Lemma lem5164632 (x : real -> real) (s : real -> Prop) (a : real) (b : real) (h1 : term108 s x) (h2 : term17 s a b) : (term108 s x) = False.
Proof. exact (prop_ext (fun h3 : term108 s x => @lem5164622 x s a b h1 h2) (fun h3 : False => @lem5164327 s x h1)). Qed.
Lemma lem5164633 (x : real -> real) (s : real -> Prop) (a : real) (b : real) (h1 : term108 s x) (h2 : term17 s a b) : False.
Proof. exact (EQ_MP (@lem5164632 x s a b h1 h2) (@lem5164327 s x h1)). Qed.
Lemma lem5164634 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : (s = (@EMPTY real)) = False.
Proof. exact (prop_ext (fun h3 : s = (@EMPTY real) => @lem5164631 s h1 h2) (fun h3 : False => @lem5164289 s h2)). Qed.
Lemma lem5164635 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : False.
Proof. exact (EQ_MP (@lem5164634 s h1 h2) (@lem5164289 s h2)). Qed.
Lemma lem5164636 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : (term18 s) = False.
Proof. exact (prop_ext (fun h3 : term18 s => @lem5164635 s h1 h2) (fun h3 : False => @lem5164262 s h1)). Qed.
Lemma lem5164637 (s : real -> Prop) (h1 : term18 s) (h2 : s = (@EMPTY real)) : False.
Proof. exact (EQ_MP (@lem5164636 s h1 h2) (@lem5164262 s h1)). Qed.
Lemma lem5164638 (a : real) (b : real) (s : real -> Prop) (x : real -> real) (h1 : term17 s a b) (h2 : term18 s) (h3 : term125 s x) : False.
Proof. exact (or_elim (@lem5164256 s x h3) (fun h0 : s = (@EMPTY real) => @lem5164637 s h2 h0) (fun h0 : term108 s x => @lem5164633 x s a b h0 h1)). Qed.
Lemma lem5164639 (a : real) (b : real) (s : real -> Prop) (x : real -> real) (h1 : term17 s a b) (h2 : term18 s) (h3 : term125 s x) : (term125 s x) = False.
Proof. exact (prop_ext (fun h4 : term125 s x => @lem5164638 a b s x h1 h2 h3) (fun h4 : False => @lem5164256 s x h3)). Qed.
Lemma lem5164640 (a : real) (b : real) (s : real -> Prop) (x : real -> real) (h1 : term17 s a b) (h2 : term18 s) (h3 : term125 s x) : False.
Proof. exact (EQ_MP (@lem5164639 a b s x h1 h2 h3) (@lem5164256 s x h3)). Qed.
Lemma lem5164641 (a : real) (b : real) (s : real -> Prop) (x : real -> real) (h1 : term17 s a b) (h2 : term18 s) (h3 : term125 s x) : (term18 s) = False.
Proof. exact (prop_ext (fun h4 : term18 s => @lem5164640 a b s x h1 h2 h3) (fun h4 : False => @lem5164198 s h2)). Qed.
Lemma lem5164642 (a : real) (b : real) (s : real -> Prop) (x : real -> real) (h1 : term17 s a b) (h2 : term18 s) (h3 : term125 s x) : False.
Proof. exact (EQ_MP (@lem5164641 a b s x h1 h2 h3) (@lem5164198 s h2)). Qed.
Lemma lem5164643 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term26 s) (h3 : term18 s) : False.
Proof. exact (ex_elim (@lem5164189 s h2) (fun x : real -> real => fun h0 : term127 s x => @lem5164642 a b s x h1 h3 h0)). Qed.
Lemma lem5164644 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term26 s) (h3 : term18 s) : (term18 s) = False.
Proof. exact (prop_ext (fun h4 : term18 s => @lem5164643 a b s h1 h2 h3) (fun h4 : False => @lem5163978 s h3)). Qed.
Lemma lem5164645 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term26 s) (h3 : term18 s) : False.
Proof. exact (EQ_MP (@lem5164644 a b s h1 h2 h3) (@lem5163978 s h3)). Qed.
Lemma lem5164646 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term26 s) (h3 : term18 s) : (term26 s) = False.
Proof. exact (prop_ext (fun h4 : term26 s => @lem5164645 a b s h1 h2 h3) (fun h4 : False => @lem5163972 s h2)). Qed.
Lemma lem5164647 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term26 s) (h3 : term18 s) : False.
Proof. exact (EQ_MP (@lem5164646 a b s h1 h2 h3) (@lem5163972 s h2)). Qed.
Lemma lem5164648 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term18 s) : term25 s.
Proof. exact (fun h0 : term26 s => @lem5164647 a b s h1 h0 h2). Qed.
Lemma lem5164649 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term18 s) : term21 s.
Proof. exact (EQ_MP (@lem5163971 s) (@lem5164648 a b s h1 h2)). Qed.
Lemma lem5164650 (a : real) (b : real) (s : real -> Prop) (h1 : term18 s) : term35 a b s.
Proof. exact (fun h0 : term17 s a b => @lem5164649 a b s h0 h1). Qed.
Lemma lem5164651 (a : real) (b : real) (s : real -> Prop) : term37 a b s.
Proof. exact (fun h0 : term18 s => @lem5164650 a b s h0). Qed.
Lemma lem5164656 (b : real) (s : real -> Prop) : term41 b s.
Proof. exact (fun a : real => @lem5164651 a b s). Qed.
Lemma lem5164661 (s : real -> Prop) : term45 s.
Proof. exact (fun b : real => @lem5164656 b s). Qed.
Lemma lem5164666 : term49.
Proof. exact (fun s : real -> Prop => @lem5164661 s). Qed.
Lemma lem5164667 : term48.
Proof. exact (EQ_MP (@lem5163965) (@lem5164666)). Qed.
Lemma lem5164668 (s : real -> Prop) : term162 s.
Proof. exact (@lem5164667 s). Qed.
Lemma lem5164669 (s : real -> Prop) : (term162 s) = (term44 s).
Proof. exact (eq_refl (term162 s)). Qed.
Lemma lem5164670 (s : real -> Prop) : term44 s.
Proof. exact (EQ_MP (@lem5164669 s) (@lem5164668 s)). Qed.
Lemma lem5164671 (s : real -> Prop) (b : real) : term163 s b.
Proof. exact (@lem5164670 s b). Qed.
Lemma lem5164672 (b : real) (s : real -> Prop) : (term163 s b) = (term40 b s).
Proof. exact (eq_refl (term163 s b)). Qed.
Lemma lem5164673 (b : real) (s : real -> Prop) : term40 b s.
Proof. exact (EQ_MP (@lem5164672 b s) (@lem5164671 s b)). Qed.
Lemma lem5164674 (b : real) (s : real -> Prop) (a : real) : term164 b s a.
Proof. exact (@lem5164673 b s a). Qed.
Lemma lem5164675 (a : real) (b : real) (s : real -> Prop) : (term164 b s a) = (term27 a b s).
Proof. exact (eq_refl (term164 b s a)). Qed.
Lemma lem5164676 (a : real) (b : real) (s : real -> Prop) : term27 a b s.
Proof. exact (EQ_MP (@lem5164675 a b s) (@lem5164674 b s a)). Qed.
Lemma lem5164678 (a : real) (b : real) (s : real -> Prop) : term27 a b s.
Proof. exact (@lem5163790 a b s (@lem5164676 a b s)). Qed.
Lemma lem5164679 (a : real) (b : real) (s : real -> Prop) (h1 : term18 s) : term34 a b s.
Proof. exact (@lem5164678 a b s (@lem5163767 s h1)). Qed.
Lemma lem5164680 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term18 s) : term25 s.
Proof. exact (@lem5164679 a b s h2 (@lem5163766 s a b h1)). Qed.
Lemma lem5164681 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term26 s) (h3 : term18 s) : False.
Proof. exact (@lem5164680 a b s h1 h3 (@lem5163775 s h2)). Qed.
Lemma lem5164682 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term26 s) (h3 : term18 s) : (term26 s) = False.
Proof. exact (prop_ext (fun h4 : term26 s => @lem5164681 a b s h1 h2 h3) (fun h4 : False => @lem5163775 s h2)). Qed.
Lemma lem5164683 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term26 s) (h3 : term18 s) : False.
Proof. exact (EQ_MP (@lem5164682 a b s h1 h2 h3) (@lem5163775 s h2)). Qed.
Lemma lem5164684 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term18 s) : term25 s.
Proof. exact (fun h0 : term26 s => @lem5164683 a b s h1 h0 h2). Qed.
Lemma lem5164685 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term18 s) : term21 s.
Proof. exact (EQ_MP (@lem5163774 s) (@lem5164684 a b s h1 h2)). Qed.
Lemma lem5164687 {A : Type'} (s : A -> Prop) : (term8 A s) = (term7 A s).
Proof. exact (EQ_MP (@lem5163750 A s) (@lem5163749 A s)). Qed.
Lemma lem5164688 (s : real -> Prop) : (term18 s) = (term165 s).
Proof. exact (@lem5164687 real s). Qed.
Lemma lem5164689 (s : real -> Prop) (h1 : term18 s) : term165 s.
Proof. exact (EQ_MP (@lem5164688 s) (@lem5163767 s h1)). Qed.
Lemma lem5164691 (p : Prop) : p = (term24 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5164692 (a : real) (s : real -> Prop) (b : real) : (term166 a s b) = (term167 a s b).
Proof. exact (@lem5164691 (term166 a s b)). Qed.
Lemma lem5164693 (a : real) (s : real -> Prop) (b : real) : (term167 a s b) = (term166 a s b).
Proof. exact (SYM (@lem5164692 a s b)). Qed.
Lemma lem5164694 (a : real) (s : real -> Prop) (b : real) (h1 : term168 a s b) : term168 a s b.
Proof. exact (h1). Qed.
Lemma lem5164697 (a : real) (s : real -> Prop) (b : real) (h1 : term169 a s b) : term169 a s b.
Proof. exact (h1). Qed.
Lemma lem5164698 (a : real) (s : real -> Prop) (b : real) : term170 a s b.
Proof. exact (fun h0 : term169 a s b => @lem5164697 a s b h0). Qed.
Lemma lem5164699 (a : real) (s : real -> Prop) (b : real) (h1 : term170 a s b) : term170 a s b.
Proof. exact (h1). Qed.
Lemma lem5164700 (a : real) (s : real -> Prop) (b : real) (h1 : term169 a s b) : term169 a s b.
Proof. exact (h1). Qed.
Lemma lem5164701 (a : real) (s : real -> Prop) (b : real) (h1 : term169 a s b) (h2 : term170 a s b) : term169 a s b.
Proof. exact (@lem5164699 a s b h2 (@lem5164700 a s b h1)). Qed.
Lemma lem5164702 (a : real) (s : real -> Prop) (b : real) (h1 : term169 a s b) : term171 a s b.
Proof. exact (fun h0 : term170 a s b => @lem5164701 a s b h1 h0). Qed.
Lemma lem5164703 (a : real) (s : real -> Prop) (b : real) (h1 : term170 a s b) : term170 a s b.
Proof. exact (h1). Qed.
Lemma lem5164704 (a : real) (s : real -> Prop) (b : real) (h1 : term169 a s b) (h2 : term170 a s b) : term169 a s b.
Proof. exact (@lem5164702 a s b h1 (@lem5164703 a s b h2)). Qed.
Lemma lem5164705 (a : real) (s : real -> Prop) (b : real) (h1 : term170 a s b) : term170 a s b.
Proof. exact (fun h0 : term169 a s b => @lem5164704 a s b h0 h1). Qed.
Lemma lem5164706 (a : real) (s : real -> Prop) (b : real) : term172 a s b.
Proof. exact (fun h0 : term170 a s b => @lem5164705 a s b h0). Qed.
Lemma lem5164709 (a : real) (s : real -> Prop) (b : real) : term170 a s b.
Proof. exact (@lem5164706 a s b (@lem5164698 a s b)). Qed.
Lemma lem5164765 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5164766 : term173 = term174.
Proof. exact (@lem5164765 term175). Qed.
Lemma lem5164783 (a : real) (s : real -> Prop) (b : real) : (term176 a s b) = (term176 a s b).
Proof. exact (eq_refl (term176 a s b)). Qed.
Lemma lem5164784 (a : real) (s : real -> Prop) (b : real) : (term177 a s b) = (term178 a s b).
Proof. exact (MK_COMB (@lem5164783 a s b) (@lem5164766)). Qed.
Lemma lem5164787 (s : real -> Prop) (a : real) (b : real) : (term33 s a b) = (term33 s a b).
Proof. exact (eq_refl (term33 s a b)). Qed.
Lemma lem5164788 (a : real) (s : real -> Prop) (b : real) : (term169 a s b) = (term179 a s b).
Proof. exact (MK_COMB (@lem5164787 s a b) (@lem5164784 a s b)). Qed.
Lemma lem5164791 (s : real -> Prop) (b : real) : (term180 s b) = (term181 s b).
Proof. exact (fun_ext (fun a : real => @lem5164788 a s b)). Qed.
Lemma lem5164792 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5164793 (s : real -> Prop) (b : real) : (term182 s b) = (term183 s b).
Proof. exact (MK_COMB (@lem5164792) (@lem5164791 s b)). Qed.
Lemma lem5164798 (b : real) : (term184 b) = (term185 b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5164793 s b)). Qed.
Lemma lem5164799 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5164800 (b : real) : (term186 b) = (term187 b).
Proof. exact (MK_COMB (@lem5164799) (@lem5164798 b)). Qed.
Lemma lem5164805 : term188 = term189.
Proof. exact (fun_ext (fun b : real => @lem5164800 b)). Qed.
Lemma lem5164806 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5164815 : term190 = term191.
Proof. exact (MK_COMB (@lem5164806) (@lem5164805)). Qed.
Lemma lem5164824 (y : real) (x : real) (z : real) : (term192 y x z) = (term192 y x z).
Proof. exact (eq_refl (term192 y x z)). Qed.
Lemma lem5164825 (y : real) (x : real) : (term193 y x) = (term193 y x).
Proof. exact (fun_ext (fun z : real => @lem5164824 y x z)). Qed.
Lemma lem5164826 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5164827 (y : real) (x : real) : (term194 y x) = (term194 y x).
Proof. exact (MK_COMB (@lem5164826) (@lem5164825 y x)). Qed.
Lemma lem5164828 (x : real) : (term195 x) = (term195 x).
Proof. exact (fun_ext (fun y : real => @lem5164827 y x)). Qed.
Lemma lem5164829 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5164830 (x : real) : (term196 x) = (term196 x).
Proof. exact (MK_COMB (@lem5164829) (@lem5164828 x)). Qed.
Lemma lem5164831 : term197 = term197.
Proof. exact (fun_ext (fun x : real => @lem5164830 x)). Qed.
Lemma lem5164832 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5164833 : term175 = term175.
Proof. exact (MK_COMB (@lem5164832) (@lem5164831)). Qed.
Lemma lem5164834 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5164835 : term174 = term174.
Proof. exact (MK_COMB (@lem5164834) (@lem5164833)). Qed.
Lemma lem5164840 (a : real) (s : real -> Prop) (b : real) : (term23 a s b) = (term23 a s b).
Proof. exact (eq_refl (term23 a s b)). Qed.
Lemma lem5164841 (s : real -> Prop) (b : real) : (term198 s b) = (term198 s b).
Proof. exact (eq_refl (term198 s b)). Qed.
Lemma lem5164846 (s : real -> Prop) (x : real) (b : real) : (term50 s x b) = (term50 s x b).
Proof. exact (eq_refl (term50 s x b)). Qed.
Lemma lem5164847 (s : real -> Prop) (b : real) : (term51 s b) = (term51 s b).
Proof. exact (fun_ext (fun x : real => @lem5164846 s x b)). Qed.
Lemma lem5164848 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5164849 (s : real -> Prop) (b : real) : (term52 s b) = (term52 s b).
Proof. exact (MK_COMB (@lem5164848) (@lem5164847 s b)). Qed.
Lemma lem5164850 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5164851 (s : real -> Prop) (b : real) : (term199 s b) = (term199 s b).
Proof. exact (MK_COMB (@lem5164850) (@lem5164849 s b)). Qed.
Lemma lem5164852 (s : real -> Prop) (b : real) : (term200 s b) = (term200 s b).
Proof. exact (MK_COMB (@lem5164851 s b) (@lem5164841 s b)). Qed.
Lemma lem5164853 (s : real -> Prop) : (term201 s) = (term201 s).
Proof. exact (fun_ext (fun b : real => @lem5164852 s b)). Qed.
Lemma lem5164854 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5164855 (s : real -> Prop) : (term202 s) = (term202 s).
Proof. exact (MK_COMB (@lem5164854) (@lem5164853 s)). Qed.
Lemma lem5164860 (x : real) (s : real -> Prop) : (term203 x s) = (term203 x s).
Proof. exact (eq_refl (term203 x s)). Qed.
Lemma lem5164861 (s : real -> Prop) : (term204 s) = (term204 s).
Proof. exact (fun_ext (fun x : real => @lem5164860 x s)). Qed.
Lemma lem5164862 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5164863 (s : real -> Prop) : (term205 s) = (term205 s).
Proof. exact (MK_COMB (@lem5164862) (@lem5164861 s)). Qed.
Lemma lem5164864 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5164865 (s : real -> Prop) : (term206 s) = (term206 s).
Proof. exact (MK_COMB (@lem5164864) (@lem5164863 s)). Qed.
Lemma lem5164866 (s : real -> Prop) : (term22 s) = (term22 s).
Proof. exact (MK_COMB (@lem5164865 s) (@lem5164855 s)). Qed.
Lemma lem5164867 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5164868 (s : real -> Prop) : (term207 s) = (term207 s).
Proof. exact (MK_COMB (@lem5164867) (@lem5164866 s)). Qed.
Lemma lem5164869 (a : real) (s : real -> Prop) (b : real) : (term208 a s b) = (term208 a s b).
Proof. exact (MK_COMB (@lem5164868 s) (@lem5164840 a s b)). Qed.
Lemma lem5164870 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5164871 (s : real -> Prop) : (term209 s) = (term209 s).
Proof. exact (fun_ext (fun x : real => @lem5164870 x s)). Qed.
Lemma lem5164872 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5164873 (s : real -> Prop) : (term165 s) = (term165 s).
Proof. exact (MK_COMB (@lem5164872) (@lem5164871 s)). Qed.
Lemma lem5164874 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5164875 (s : real -> Prop) : (term210 s) = (term210 s).
Proof. exact (MK_COMB (@lem5164874) (@lem5164873 s)). Qed.
Lemma lem5164876 (a : real) (s : real -> Prop) (b : real) : (term166 a s b) = (term166 a s b).
Proof. exact (MK_COMB (@lem5164875 s) (@lem5164869 a s b)). Qed.
Lemma lem5164877 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5164878 (a : real) (s : real -> Prop) (b : real) : (term168 a s b) = (term168 a s b).
Proof. exact (MK_COMB (@lem5164877) (@lem5164876 a s b)). Qed.
Lemma lem5164879 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5164880 (a : real) (s : real -> Prop) (b : real) : (term176 a s b) = (term176 a s b).
Proof. exact (MK_COMB (@lem5164879) (@lem5164878 a s b)). Qed.
Lemma lem5164881 (a : real) (s : real -> Prop) (b : real) : (term178 a s b) = (term178 a s b).
Proof. exact (MK_COMB (@lem5164880 a s b) (@lem5164835)). Qed.
Lemma lem5164890 (s : real -> Prop) (a : real) (x : real) (b : real) : (term56 s a x b) = (term56 s a x b).
Proof. exact (eq_refl (term56 s a x b)). Qed.
Lemma lem5164891 (s : real -> Prop) (a : real) (b : real) : (term57 s a b) = (term57 s a b).
Proof. exact (fun_ext (fun x : real => @lem5164890 s a x b)). Qed.
Lemma lem5164892 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5164893 (s : real -> Prop) (a : real) (b : real) : (term17 s a b) = (term17 s a b).
Proof. exact (MK_COMB (@lem5164892) (@lem5164891 s a b)). Qed.
Lemma lem5164894 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5164895 (s : real -> Prop) (a : real) (b : real) : (term33 s a b) = (term33 s a b).
Proof. exact (MK_COMB (@lem5164894) (@lem5164893 s a b)). Qed.
Lemma lem5164896 (a : real) (s : real -> Prop) (b : real) : (term179 a s b) = (term179 a s b).
Proof. exact (MK_COMB (@lem5164895 s a b) (@lem5164881 a s b)). Qed.
Lemma lem5164897 (s : real -> Prop) (b : real) : (term181 s b) = (term181 s b).
Proof. exact (fun_ext (fun a : real => @lem5164896 a s b)). Qed.
Lemma lem5164898 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5164899 (s : real -> Prop) (b : real) : (term183 s b) = (term183 s b).
Proof. exact (MK_COMB (@lem5164898) (@lem5164897 s b)). Qed.
Lemma lem5164900 (b : real) : (term185 b) = (term185 b).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5164899 s b)). Qed.
Lemma lem5164901 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5164902 (b : real) : (term187 b) = (term187 b).
Proof. exact (MK_COMB (@lem5164901) (@lem5164900 b)). Qed.
Lemma lem5164903 : term189 = term189.
Proof. exact (fun_ext (fun b : real => @lem5164902 b)). Qed.
Lemma lem5164904 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5164905 : term191 = term191.
Proof. exact (MK_COMB (@lem5164904) (@lem5164903)). Qed.
Lemma lem5165000 : term190 = term191.
Proof. exact (TRANS (@lem5164815) (@lem5164905)). Qed.
Lemma lem5165001 : term191 = term190.
Proof. exact (SYM (@lem5165000)). Qed.
Lemma lem5165002 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term17 s a b.
Proof. exact (h1). Qed.
Lemma lem5165003 (a : real) (s : real -> Prop) (b : real) (h1 : term168 a s b) : term168 a s b.
Proof. exact (h1). Qed.
Lemma lem5165004 (h1 : term175) : term175.
Proof. exact (h1). Qed.
Lemma lem5165015 (s : real -> Prop) (a : real) (x : real) (b : real) : (term56 s a x b) = (term58 s a x b).
Proof. exact (@lem17265 (@IN real x s) (term59 a x b)). Qed.
Lemma lem5165016 (s : real -> Prop) (a : real) (b : real) : (term57 s a b) = (term60 s a b).
Proof. exact (fun_ext (fun x : real => @lem5165015 s a x b)). Qed.
Lemma lem5165017 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5165070 (s : real -> Prop) (a : real) (b : real) : (term17 s a b) = (term61 s a b).
Proof. exact (MK_COMB (@lem5165017) (@lem5165016 s a b)). Qed.
Lemma lem5165071 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term61 s a b.
Proof. exact (EQ_MP (@lem5165070 s a b) (@lem5165002 s a b h1)). Qed.
Lemma lem5165072 (x : real) (s : real -> Prop) : (@IN real x s) = (@IN real x s).
Proof. exact (eq_refl (@IN real x s)). Qed.
Lemma lem5165073 (s : real -> Prop) : (term209 s) = (term209 s).
Proof. exact (fun_ext (fun x : real => @lem5165072 x s)). Qed.
Lemma lem5165074 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5165075 (s : real -> Prop) : (term165 s) = (term165 s).
Proof. exact (MK_COMB (@lem5165074) (@lem5165073 s)). Qed.
Lemma lem5165082 (x : real) (s : real -> Prop) : (term203 x s) = (term211 x s).
Proof. exact (@lem17265 (@IN real x s) (term212 x s)). Qed.
Lemma lem5165083 (s : real -> Prop) : (term204 s) = (term213 s).
Proof. exact (fun_ext (fun x : real => @lem5165082 x s)). Qed.
Lemma lem5165084 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5165085 (s : real -> Prop) : (term205 s) = (term214 s).
Proof. exact (MK_COMB (@lem5165084) (@lem5165083 s)). Qed.
Lemma lem5165092 (s : real -> Prop) (x : real) (b : real) : (term63 s x b) = (term64 s x b).
Proof. exact (@lem17362 (@IN real x s) (real_le x b)). Qed.
Lemma lem5165093 (P : real -> Prop) : (term65 P) = (term66 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5165094 (s : real -> Prop) (b : real) : (term67 s b) = (term68 s b).
Proof. exact (@lem5165093 (term51 s b)). Qed.
Lemma lem5165095 (s : real -> Prop) (x : real) (b : real) : (term69 s b x) = (term50 s x b).
Proof. exact (eq_refl (term69 s b x)). Qed.
Lemma lem5165096 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5165097 (s : real -> Prop) (x : real) (b : real) : (term70 s b x) = (term63 s x b).
Proof. exact (MK_COMB (@lem5165096) (@lem5165095 s x b)). Qed.
Lemma lem5165098 (s : real -> Prop) (x : real) (b : real) : (term70 s b x) = (term64 s x b).
Proof. exact (TRANS (@lem5165097 s x b) (@lem5165092 s x b)). Qed.
Lemma lem5165099 (s : real -> Prop) (b : real) : (term71 s b) = (term72 s b).
Proof. exact (fun_ext (fun x : real => @lem5165098 s x b)). Qed.
Lemma lem5165100 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5165101 (s : real -> Prop) (b : real) : (term68 s b) = (term73 s b).
Proof. exact (MK_COMB (@lem5165100) (@lem5165099 s b)). Qed.
Lemma lem5165102 (s : real -> Prop) (b : real) : (term67 s b) = (term73 s b).
Proof. exact (TRANS (@lem5165094 s b) (@lem5165101 s b)). Qed.
Lemma lem5165103 (s : real -> Prop) (b : real) : (term198 s b) = (term198 s b).
Proof. exact (eq_refl (term198 s b)). Qed.
Lemma lem5165104 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5165105 (s : real -> Prop) (b : real) : (term215 s b) = (term216 s b).
Proof. exact (MK_COMB (@lem5165104) (@lem5165102 s b)). Qed.
Lemma lem5165106 (s : real -> Prop) (b : real) : (term217 s b) = (term218 s b).
Proof. exact (MK_COMB (@lem5165105 s b) (@lem5165103 s b)). Qed.
Lemma lem5165107 (s : real -> Prop) (b : real) : (term200 s b) = (term217 s b).
Proof. exact (@lem17265 (term52 s b) (term198 s b)). Qed.
Lemma lem5165108 (s : real -> Prop) (b : real) : (term200 s b) = (term218 s b).
Proof. exact (TRANS (@lem5165107 s b) (@lem5165106 s b)). Qed.
Lemma lem5165109 (s : real -> Prop) : (term201 s) = (term219 s).
Proof. exact (fun_ext (fun b : real => @lem5165108 s b)). Qed.
Lemma lem5165110 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5165111 (s : real -> Prop) : (term202 s) = (term220 s).
Proof. exact (MK_COMB (@lem5165110) (@lem5165109 s)). Qed.
Lemma lem5165112 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5165113 (s : real -> Prop) : (term206 s) = (term221 s).
Proof. exact (MK_COMB (@lem5165112) (@lem5165085 s)). Qed.
Lemma lem5165114 (s : real -> Prop) : (term22 s) = (term222 s).
Proof. exact (MK_COMB (@lem5165113 s) (@lem5165111 s)). Qed.
Lemma lem5165121 (a : real) (s : real -> Prop) (b : real) : (term223 a s b) = (term224 a s b).
Proof. exact (@lem17045 (term212 a s) (term198 s b)). Qed.
Lemma lem5165122 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5165123 (s : real -> Prop) : (term225 s) = (term226 s).
Proof. exact (MK_COMB (@lem5165122) (@lem5165114 s)). Qed.
Lemma lem5165124 (a : real) (s : real -> Prop) (b : real) : (term227 a s b) = (term228 a s b).
Proof. exact (MK_COMB (@lem5165123 s) (@lem5165121 a s b)). Qed.
Lemma lem5165125 (a : real) (s : real -> Prop) (b : real) : (term229 a s b) = (term227 a s b).
Proof. exact (@lem17362 (term22 s) (term23 a s b)). Qed.
Lemma lem5165126 (a : real) (s : real -> Prop) (b : real) : (term229 a s b) = (term228 a s b).
Proof. exact (TRANS (@lem5165125 a s b) (@lem5165124 a s b)). Qed.
Lemma lem5165127 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5165128 (s : real -> Prop) : (term230 s) = (term230 s).
Proof. exact (MK_COMB (@lem5165127) (@lem5165075 s)). Qed.
Lemma lem5165129 (a : real) (s : real -> Prop) (b : real) : (term231 a s b) = (term232 a s b).
Proof. exact (MK_COMB (@lem5165128 s) (@lem5165126 a s b)). Qed.
Lemma lem5165130 (a : real) (s : real -> Prop) (b : real) : (term168 a s b) = (term231 a s b).
Proof. exact (@lem17362 (term165 s) (term208 a s b)). Qed.
Lemma lem5165131 (a : real) (s : real -> Prop) (b : real) : (term168 a s b) = (term232 a s b).
Proof. exact (TRANS (@lem5165130 a s b) (@lem5165129 a s b)). Qed.
Lemma lem5165282 {A : Type'} (P : A -> Prop) (Q : Prop) : (term233 A P Q) = (term234 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5165283 (P : real -> Prop) (Q : Prop) : (term235 P Q) = (term236 P Q).
Proof. exact (@lem5165282 real P Q). Qed.
Lemma lem5165284 (s : real -> Prop) (b : real) : (term237 s b) = (term238 s b).
Proof. exact (@lem5165283 (term72 s b) (term198 s b)). Qed.
Lemma lem5165285 (s : real -> Prop) (x : real) (b : real) : (term96 s b x) = (term64 s x b).
Proof. exact (eq_refl (term96 s b x)). Qed.
Lemma lem5165286 (s : real -> Prop) (b : real) : (term239 s b) = (term72 s b).
Proof. exact (fun_ext (fun x : real => @lem5165285 s x b)). Qed.
Lemma lem5165287 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5165288 (s : real -> Prop) (b : real) : (term240 s b) = (term73 s b).
Proof. exact (MK_COMB (@lem5165287) (@lem5165286 s b)). Qed.
Lemma lem5165289 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5165290 (s : real -> Prop) (b : real) : (term241 s b) = (term216 s b).
Proof. exact (MK_COMB (@lem5165289) (@lem5165288 s b)). Qed.
Lemma lem5165291 (s : real -> Prop) (b : real) : (term198 s b) = (term198 s b).
Proof. exact (eq_refl (term198 s b)). Qed.
Lemma lem5165292 (s : real -> Prop) (b : real) : (term237 s b) = (term218 s b).
Proof. exact (MK_COMB (@lem5165290 s b) (@lem5165291 s b)). Qed.
Lemma lem5165293 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5165294 (s : real -> Prop) (b : real) : (term242 s b) = (term243 s b).
Proof. exact (MK_COMB (@lem5165293) (@lem5165292 s b)). Qed.
Lemma lem5165295 (s : real -> Prop) (x : real) (b : real) : (term96 s b x) = (term64 s x b).
Proof. exact (eq_refl (term96 s b x)). Qed.
Lemma lem5165296 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5165297 (s : real -> Prop) (x : real) (b : real) : (term244 s b x) = (term245 s x b).
Proof. exact (MK_COMB (@lem5165296) (@lem5165295 s x b)). Qed.
Lemma lem5165298 (s : real -> Prop) (b : real) : (term198 s b) = (term198 s b).
Proof. exact (eq_refl (term198 s b)). Qed.
Lemma lem5165299 (x : real) (s : real -> Prop) (b : real) : (term246 x s b) = (term247 x s b).
Proof. exact (MK_COMB (@lem5165297 s x b) (@lem5165298 s b)). Qed.
Lemma lem5165300 (s : real -> Prop) (b : real) : (term248 s b) = (term249 s b).
Proof. exact (fun_ext (fun x : real => @lem5165299 x s b)). Qed.
Lemma lem5165301 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5165302 (s : real -> Prop) (b : real) : (term238 s b) = (term250 s b).
Proof. exact (MK_COMB (@lem5165301) (@lem5165300 s b)). Qed.
Lemma lem5165303 (s : real -> Prop) (b : real) : ((term237 s b) = (term238 s b)) = ((term218 s b) = (term250 s b)).
Proof. exact (MK_COMB (@lem5165294 s b) (@lem5165302 s b)). Qed.
Lemma lem5165304 (s : real -> Prop) (b : real) : (term218 s b) = (term250 s b).
Proof. exact (EQ_MP (@lem5165303 s b) (@lem5165284 s b)). Qed.
Lemma lem5165305 (s : real -> Prop) : (term219 s) = (term251 s).
Proof. exact (fun_ext (fun b : real => @lem5165304 s b)). Qed.
Lemma lem5165306 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5165307 (s : real -> Prop) : (term220 s) = (term252 s).
Proof. exact (MK_COMB (@lem5165306) (@lem5165305 s)). Qed.
Lemma lem5165309 {A B : Type'} (P : type1413 A B) : (term87 A B P) = (term88 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5165310 (P : type1626) : (term89 P) = (term90 P).
Proof. exact (@lem5165309 real real P). Qed.
Lemma lem5165311 (s : real -> Prop) : (term253 s) = (term254 s).
Proof. exact (@lem5165310 (term255 s)). Qed.
Lemma lem5165312 (s : real -> Prop) (b : real) : (term256 s b) = (term249 s b).
Proof. exact (eq_refl (term256 s b)). Qed.
Lemma lem5165313 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5165314 (s : real -> Prop) (b : real) (x : real) : (term257 s b x) = (term258 s b x).
Proof. exact (MK_COMB (@lem5165312 s b) (@lem5165313 x)). Qed.
Lemma lem5165315 (x : real) (s : real -> Prop) (b : real) : (term258 s b x) = (term247 x s b).
Proof. exact (eq_refl (term258 s b x)). Qed.
Lemma lem5165316 (x : real) (s : real -> Prop) (b : real) : (term257 s b x) = (term247 x s b).
Proof. exact (TRANS (@lem5165314 s b x) (@lem5165315 x s b)). Qed.
Lemma lem5165317 (s : real -> Prop) (b : real) : (term259 s b) = (term249 s b).
Proof. exact (fun_ext (fun x : real => @lem5165316 x s b)). Qed.
Lemma lem5165318 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5165319 (s : real -> Prop) (b : real) : (term260 s b) = (term250 s b).
Proof. exact (MK_COMB (@lem5165318) (@lem5165317 s b)). Qed.
Lemma lem5165320 (s : real -> Prop) : (term261 s) = (term251 s).
Proof. exact (fun_ext (fun b : real => @lem5165319 s b)). Qed.
Lemma lem5165321 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5165322 (s : real -> Prop) : (term253 s) = (term252 s).
Proof. exact (MK_COMB (@lem5165321) (@lem5165320 s)). Qed.
Lemma lem5165323 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5165324 (s : real -> Prop) : (term262 s) = (term263 s).
Proof. exact (MK_COMB (@lem5165323) (@lem5165322 s)). Qed.
Lemma lem5165325 (s : real -> Prop) (b : real) : (term256 s b) = (term249 s b).
Proof. exact (eq_refl (term256 s b)). Qed.
Lemma lem5165326 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5165327 (s : real -> Prop) (x : real -> real) (b : real) : (term264 s x b) = (term265 s x b).
Proof. exact (MK_COMB (@lem5165325 s b) (@lem5165326 x b)). Qed.
Lemma lem5165328 (x : real -> real) (s : real -> Prop) (b : real) : (term265 s x b) = (term266 x s b).
Proof. exact (eq_refl (term265 s x b)). Qed.
Lemma lem5165329 (x : real -> real) (s : real -> Prop) (b : real) : (term264 s x b) = (term266 x s b).
Proof. exact (TRANS (@lem5165327 s x b) (@lem5165328 x s b)). Qed.
Lemma lem5165330 (x : real -> real) (s : real -> Prop) : (term267 s x) = (term268 x s).
Proof. exact (fun_ext (fun b : real => @lem5165329 x s b)). Qed.
Lemma lem5165331 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5165332 (x : real -> real) (s : real -> Prop) : (term269 s x) = (term270 x s).
Proof. exact (MK_COMB (@lem5165331) (@lem5165330 x s)). Qed.
Lemma lem5165333 (s : real -> Prop) : (term271 s) = (term272 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5165332 x s)). Qed.
Lemma lem5165334 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5165335 (s : real -> Prop) : (term254 s) = (term273 s).
Proof. exact (MK_COMB (@lem5165334) (@lem5165333 s)). Qed.
Lemma lem5165336 (s : real -> Prop) : ((term253 s) = (term254 s)) = ((term252 s) = (term273 s)).
Proof. exact (MK_COMB (@lem5165324 s) (@lem5165335 s)). Qed.
Lemma lem5165337 (s : real -> Prop) : (term252 s) = (term273 s).
Proof. exact (EQ_MP (@lem5165336 s) (@lem5165311 s)). Qed.
Lemma lem5165338 (s : real -> Prop) : (term220 s) = (term273 s).
Proof. exact (TRANS (@lem5165307 s) (@lem5165337 s)). Qed.
Lemma lem5165339 (s : real -> Prop) : (term221 s) = (term221 s).
Proof. exact (eq_refl (term221 s)). Qed.
Lemma lem5165340 (s : real -> Prop) : (term222 s) = (term274 s).
Proof. exact (MK_COMB (@lem5165339 s) (@lem5165338 s)). Qed.
Lemma lem5165342 {A : Type'} (P : Prop) (Q : A -> Prop) : (term275 A P Q) = (term276 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5165343 (P : Prop) (Q : type1028) : (term277 P Q) = (term278 P Q).
Proof. exact (@lem5165342 (real -> real) P Q). Qed.
Lemma lem5165344 (s : real -> Prop) : (term279 s) = (term280 s).
Proof. exact (@lem5165343 (term214 s) (term272 s)). Qed.
Lemma lem5165345 (x : real -> real) (s : real -> Prop) : (term281 s x) = (term270 x s).
Proof. exact (eq_refl (term281 s x)). Qed.
Lemma lem5165346 (s : real -> Prop) : (term282 s) = (term272 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5165345 x s)). Qed.
Lemma lem5165347 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5165348 (s : real -> Prop) : (term283 s) = (term273 s).
Proof. exact (MK_COMB (@lem5165347) (@lem5165346 s)). Qed.
Lemma lem5165349 (s : real -> Prop) : (term221 s) = (term221 s).
Proof. exact (eq_refl (term221 s)). Qed.
Lemma lem5165350 (s : real -> Prop) : (term279 s) = (term274 s).
Proof. exact (MK_COMB (@lem5165349 s) (@lem5165348 s)). Qed.
Lemma lem5165351 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5165352 (s : real -> Prop) : (term284 s) = (term285 s).
Proof. exact (MK_COMB (@lem5165351) (@lem5165350 s)). Qed.
Lemma lem5165353 (x : real -> real) (s : real -> Prop) : (term281 s x) = (term270 x s).
Proof. exact (eq_refl (term281 s x)). Qed.
Lemma lem5165354 (s : real -> Prop) : (term221 s) = (term221 s).
Proof. exact (eq_refl (term221 s)). Qed.
Lemma lem5165355 (x : real -> real) (s : real -> Prop) : (term286 s x) = (term287 x s).
Proof. exact (MK_COMB (@lem5165354 s) (@lem5165353 x s)). Qed.
Lemma lem5165356 (s : real -> Prop) : (term288 s) = (term289 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5165355 x s)). Qed.
Lemma lem5165357 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5165358 (s : real -> Prop) : (term280 s) = (term290 s).
Proof. exact (MK_COMB (@lem5165357) (@lem5165356 s)). Qed.
Lemma lem5165359 (s : real -> Prop) : ((term279 s) = (term280 s)) = ((term274 s) = (term290 s)).
Proof. exact (MK_COMB (@lem5165352 s) (@lem5165358 s)). Qed.
Lemma lem5165360 (s : real -> Prop) : (term274 s) = (term290 s).
Proof. exact (EQ_MP (@lem5165359 s) (@lem5165344 s)). Qed.
Lemma lem5165361 (s : real -> Prop) : (term222 s) = (term290 s).
Proof. exact (TRANS (@lem5165340 s) (@lem5165360 s)). Qed.
Lemma lem5165362 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5165363 (s : real -> Prop) : (term226 s) = (term291 s).
Proof. exact (MK_COMB (@lem5165362) (@lem5165361 s)). Qed.
Lemma lem5165364 (a : real) (s : real -> Prop) (b : real) : (term224 a s b) = (term224 a s b).
Proof. exact (eq_refl (term224 a s b)). Qed.
Lemma lem5165365 (a : real) (s : real -> Prop) (b : real) : (term228 a s b) = (term292 a s b).
Proof. exact (MK_COMB (@lem5165363 s) (@lem5165364 a s b)). Qed.
Lemma lem5165367 {A : Type'} (P : A -> Prop) (Q : Prop) : (term293 A P Q) = (term294 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5165368 (P : type1028) (Q : Prop) : (term295 P Q) = (term296 P Q).
Proof. exact (@lem5165367 (real -> real) P Q). Qed.
Lemma lem5165369 (a : real) (s : real -> Prop) (b : real) : (term297 a s b) = (term298 a s b).
Proof. exact (@lem5165368 (term289 s) (term224 a s b)). Qed.
Lemma lem5165370 (x : real -> real) (s : real -> Prop) : (term299 s x) = (term287 x s).
Proof. exact (eq_refl (term299 s x)). Qed.
Lemma lem5165371 (s : real -> Prop) : (term300 s) = (term289 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5165370 x s)). Qed.
Lemma lem5165372 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5165373 (s : real -> Prop) : (term301 s) = (term290 s).
Proof. exact (MK_COMB (@lem5165372) (@lem5165371 s)). Qed.
Lemma lem5165374 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5165375 (s : real -> Prop) : (term302 s) = (term291 s).
Proof. exact (MK_COMB (@lem5165374) (@lem5165373 s)). Qed.
Lemma lem5165376 (a : real) (s : real -> Prop) (b : real) : (term224 a s b) = (term224 a s b).
Proof. exact (eq_refl (term224 a s b)). Qed.
Lemma lem5165377 (a : real) (s : real -> Prop) (b : real) : (term297 a s b) = (term292 a s b).
Proof. exact (MK_COMB (@lem5165375 s) (@lem5165376 a s b)). Qed.
Lemma lem5165378 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5165379 (a : real) (s : real -> Prop) (b : real) : (term303 a s b) = (term304 a s b).
Proof. exact (MK_COMB (@lem5165378) (@lem5165377 a s b)). Qed.
Lemma lem5165380 (x : real -> real) (s : real -> Prop) : (term299 s x) = (term287 x s).
Proof. exact (eq_refl (term299 s x)). Qed.
Lemma lem5165381 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5165382 (x : real -> real) (s : real -> Prop) : (term305 s x) = (term306 x s).
Proof. exact (MK_COMB (@lem5165381) (@lem5165380 x s)). Qed.
Lemma lem5165383 (a : real) (s : real -> Prop) (b : real) : (term224 a s b) = (term224 a s b).
Proof. exact (eq_refl (term224 a s b)). Qed.
Lemma lem5165384 (x : real -> real) (a : real) (s : real -> Prop) (b : real) : (term307 x a s b) = (term308 x a s b).
Proof. exact (MK_COMB (@lem5165382 x s) (@lem5165383 a s b)). Qed.
Lemma lem5165385 (a : real) (s : real -> Prop) (b : real) : (term309 a s b) = (term310 a s b).
Proof. exact (fun_ext (fun x : real -> real => @lem5165384 x a s b)). Qed.
Lemma lem5165386 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5165387 (a : real) (s : real -> Prop) (b : real) : (term298 a s b) = (term311 a s b).
Proof. exact (MK_COMB (@lem5165386) (@lem5165385 a s b)). Qed.
Lemma lem5165388 (a : real) (s : real -> Prop) (b : real) : ((term297 a s b) = (term298 a s b)) = ((term292 a s b) = (term311 a s b)).
Proof. exact (MK_COMB (@lem5165379 a s b) (@lem5165387 a s b)). Qed.
Lemma lem5165389 (a : real) (s : real -> Prop) (b : real) : (term292 a s b) = (term311 a s b).
Proof. exact (EQ_MP (@lem5165388 a s b) (@lem5165369 a s b)). Qed.
Lemma lem5165390 (a : real) (s : real -> Prop) (b : real) : (term228 a s b) = (term311 a s b).
Proof. exact (TRANS (@lem5165365 a s b) (@lem5165389 a s b)). Qed.
Lemma lem5165391 (s : real -> Prop) : (term230 s) = (term230 s).
Proof. exact (eq_refl (term230 s)). Qed.
Lemma lem5165392 (a : real) (s : real -> Prop) (b : real) : (term232 a s b) = (term312 a s b).
Proof. exact (MK_COMB (@lem5165391 s) (@lem5165390 a s b)). Qed.
Lemma lem5165394 {A : Type'} (P : A -> Prop) (Q : Prop) : (term293 A P Q) = (term294 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5165395 (P : real -> Prop) (Q : Prop) : (term313 P Q) = (term314 P Q).
Proof. exact (@lem5165394 real P Q). Qed.
Lemma lem5165396 (a : real) (s : real -> Prop) (b : real) : (term315 a s b) = (term316 a s b).
Proof. exact (@lem5165395 (term209 s) (term311 a s b)). Qed.
Lemma lem5165397 (x : real) (s : real -> Prop) : (term317 s x) = (@IN real x s).
Proof. exact (eq_refl (term317 s x)). Qed.
Lemma lem5165398 (s : real -> Prop) : (term318 s) = (term209 s).
Proof. exact (fun_ext (fun x : real => @lem5165397 x s)). Qed.
Lemma lem5165399 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5165400 (s : real -> Prop) : (term319 s) = (term165 s).
Proof. exact (MK_COMB (@lem5165399) (@lem5165398 s)). Qed.
Lemma lem5165401 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5165402 (s : real -> Prop) : (term320 s) = (term230 s).
Proof. exact (MK_COMB (@lem5165401) (@lem5165400 s)). Qed.
Lemma lem5165403 (a : real) (s : real -> Prop) (b : real) : (term311 a s b) = (term311 a s b).
Proof. exact (eq_refl (term311 a s b)). Qed.
Lemma lem5165404 (a : real) (s : real -> Prop) (b : real) : (term315 a s b) = (term312 a s b).
Proof. exact (MK_COMB (@lem5165402 s) (@lem5165403 a s b)). Qed.
Lemma lem5165405 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5165406 (a : real) (s : real -> Prop) (b : real) : (term321 a s b) = (term322 a s b).
Proof. exact (MK_COMB (@lem5165405) (@lem5165404 a s b)). Qed.
Lemma lem5165407 (x : real) (s : real -> Prop) : (term317 s x) = (@IN real x s).
Proof. exact (eq_refl (term317 s x)). Qed.
Lemma lem5165408 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5165409 (x : real) (s : real -> Prop) : (term323 s x) = (term324 x s).
Proof. exact (MK_COMB (@lem5165408) (@lem5165407 x s)). Qed.
Lemma lem5165410 (a : real) (s : real -> Prop) (b : real) : (term311 a s b) = (term311 a s b).
Proof. exact (eq_refl (term311 a s b)). Qed.
Lemma lem5165411 (x : real) (a : real) (s : real -> Prop) (b : real) : (term325 x a s b) = (term326 x a s b).
Proof. exact (MK_COMB (@lem5165409 x s) (@lem5165410 a s b)). Qed.
Lemma lem5165412 (a : real) (s : real -> Prop) (b : real) : (term327 a s b) = (term328 a s b).
Proof. exact (fun_ext (fun x : real => @lem5165411 x a s b)). Qed.
Lemma lem5165413 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5165414 (a : real) (s : real -> Prop) (b : real) : (term316 a s b) = (term329 a s b).
Proof. exact (MK_COMB (@lem5165413) (@lem5165412 a s b)). Qed.
Lemma lem5165415 (a : real) (s : real -> Prop) (b : real) : ((term315 a s b) = (term316 a s b)) = ((term312 a s b) = (term329 a s b)).
Proof. exact (MK_COMB (@lem5165406 a s b) (@lem5165414 a s b)). Qed.
Lemma lem5165416 (a : real) (s : real -> Prop) (b : real) : (term312 a s b) = (term329 a s b).
Proof. exact (EQ_MP (@lem5165415 a s b) (@lem5165396 a s b)). Qed.
Lemma lem5165418 {A : Type'} (P : Prop) (Q : A -> Prop) : (term275 A P Q) = (term276 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5165419 (P : Prop) (Q : type1028) : (term277 P Q) = (term278 P Q).
Proof. exact (@lem5165418 (real -> real) P Q). Qed.
Lemma lem5165420 (x : real) (a : real) (s : real -> Prop) (b : real) : (term330 x a s b) = (term331 x a s b).
Proof. exact (@lem5165419 (@IN real x s) (term310 a s b)). Qed.
Lemma lem5165421 (x : real -> real) (a : real) (s : real -> Prop) (b : real) : (term332 a s b x) = (term308 x a s b).
Proof. exact (eq_refl (term332 a s b x)). Qed.
Lemma lem5165422 (a : real) (s : real -> Prop) (b : real) : (term333 a s b) = (term310 a s b).
Proof. exact (fun_ext (fun x : real -> real => @lem5165421 x a s b)). Qed.
Lemma lem5165423 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5165424 (a : real) (s : real -> Prop) (b : real) : (term334 a s b) = (term311 a s b).
Proof. exact (MK_COMB (@lem5165423) (@lem5165422 a s b)). Qed.
Lemma lem5165425 (x : real) (s : real -> Prop) : (term324 x s) = (term324 x s).
Proof. exact (eq_refl (term324 x s)). Qed.
Lemma lem5165426 (x : real) (a : real) (s : real -> Prop) (b : real) : (term330 x a s b) = (term326 x a s b).
Proof. exact (MK_COMB (@lem5165425 x s) (@lem5165424 a s b)). Qed.
Lemma lem5165427 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5165428 (x : real) (a : real) (s : real -> Prop) (b : real) : (term335 x a s b) = (term336 x a s b).
Proof. exact (MK_COMB (@lem5165427) (@lem5165426 x a s b)). Qed.
Lemma lem5165429 (x : real -> real) (a : real) (s : real -> Prop) (b : real) : (term332 a s b x) = (term308 x a s b).
Proof. exact (eq_refl (term332 a s b x)). Qed.
Lemma lem5165430 (x : real) (s : real -> Prop) : (term324 x s) = (term324 x s).
Proof. exact (eq_refl (term324 x s)). Qed.
Lemma lem5165431 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) : (term337 x a s b x') = (term338 x x' a s b).
Proof. exact (MK_COMB (@lem5165430 x s) (@lem5165429 x' a s b)). Qed.
Lemma lem5165432 (x : real) (a : real) (s : real -> Prop) (b : real) : (term339 x a s b) = (term340 x a s b).
Proof. exact (fun_ext (fun x' : real -> real => @lem5165431 x x' a s b)). Qed.
Lemma lem5165433 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5165434 (x : real) (a : real) (s : real -> Prop) (b : real) : (term331 x a s b) = (term341 x a s b).
Proof. exact (MK_COMB (@lem5165433) (@lem5165432 x a s b)). Qed.
Lemma lem5165435 (x : real) (a : real) (s : real -> Prop) (b : real) : ((term330 x a s b) = (term331 x a s b)) = ((term326 x a s b) = (term341 x a s b)).
Proof. exact (MK_COMB (@lem5165428 x a s b) (@lem5165434 x a s b)). Qed.
Lemma lem5165436 (x : real) (a : real) (s : real -> Prop) (b : real) : (term326 x a s b) = (term341 x a s b).
Proof. exact (EQ_MP (@lem5165435 x a s b) (@lem5165420 x a s b)). Qed.
Lemma lem5165437 (a : real) (s : real -> Prop) (b : real) : (term328 a s b) = (term342 a s b).
Proof. exact (fun_ext (fun x : real => @lem5165436 x a s b)). Qed.
Lemma lem5165438 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5165439 (a : real) (s : real -> Prop) (b : real) : (term329 a s b) = (term343 a s b).
Proof. exact (MK_COMB (@lem5165438) (@lem5165437 a s b)). Qed.
Lemma lem5165440 (a : real) (s : real -> Prop) (b : real) : (term312 a s b) = (term343 a s b).
Proof. exact (TRANS (@lem5165416 a s b) (@lem5165439 a s b)). Qed.
Lemma lem5165442 (a : real) (s : real -> Prop) (b : real) : (term232 a s b) = (term343 a s b).
Proof. exact (TRANS (@lem5165392 a s b) (@lem5165440 a s b)). Qed.
Lemma lem5165443 (a : real) (s : real -> Prop) (b : real) : (term168 a s b) = (term343 a s b).
Proof. exact (TRANS (@lem5165131 a s b) (@lem5165442 a s b)). Qed.
Lemma lem5165444 (a : real) (s : real -> Prop) (b : real) (h1 : term168 a s b) : term343 a s b.
Proof. exact (EQ_MP (@lem5165443 a s b) (@lem5165003 a s b h1)). Qed.
Lemma lem5165451 (x : real) (y : real) (z : real) : (term344 x y z) = (term345 x y z).
Proof. exact (@lem17045 (real_le x y) (real_le y z)). Qed.
Lemma lem5165452 (x : real) (z : real) : (real_le x z) = (real_le x z).
Proof. exact (eq_refl (real_le x z)). Qed.
Lemma lem5165453 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5165454 (x : real) (y : real) (z : real) : (term346 x y z) = (term347 x y z).
Proof. exact (MK_COMB (@lem5165453) (@lem5165451 x y z)). Qed.
Lemma lem5165455 (y : real) (x : real) (z : real) : (term348 y x z) = (term349 y x z).
Proof. exact (MK_COMB (@lem5165454 x y z) (@lem5165452 x z)). Qed.
Lemma lem5165456 (y : real) (x : real) (z : real) : (term192 y x z) = (term348 y x z).
Proof. exact (@lem17265 (term59 x y z) (real_le x z)). Qed.
Lemma lem5165457 (y : real) (x : real) (z : real) : (term192 y x z) = (term349 y x z).
Proof. exact (TRANS (@lem5165456 y x z) (@lem5165455 y x z)). Qed.
Lemma lem5165458 (y : real) (x : real) : (term193 y x) = (term350 y x).
Proof. exact (fun_ext (fun z : real => @lem5165457 y x z)). Qed.
Lemma lem5165459 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5165460 (y : real) (x : real) : (term194 y x) = (term351 y x).
Proof. exact (MK_COMB (@lem5165459) (@lem5165458 y x)). Qed.
Lemma lem5165461 (x : real) : (term195 x) = (term352 x).
Proof. exact (fun_ext (fun y : real => @lem5165460 y x)). Qed.
Lemma lem5165462 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5165463 (x : real) : (term196 x) = (term353 x).
Proof. exact (MK_COMB (@lem5165462) (@lem5165461 x)). Qed.
Lemma lem5165464 : term197 = term354.
Proof. exact (fun_ext (fun x : real => @lem5165463 x)). Qed.
Lemma lem5165465 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5165526 : term175 = term355.
Proof. exact (MK_COMB (@lem5165465) (@lem5165464)). Qed.
Lemma lem5165527 (h1 : term175) : term355.
Proof. exact (EQ_MP (@lem5165526) (@lem5165004 h1)). Qed.
Lemma lem5165528 (x : real) (a : real) (s : real -> Prop) (b : real) (h1 : term341 x a s b) : term341 x a s b.
Proof. exact (h1). Qed.
Lemma lem5165529 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term338 x x' a s b.
Proof. exact (h1). Qed.
Lemma lem5165552 (s : real -> Prop) (a : real) (x : real) (b : real) : (term58 s a x b) = (term58 s a x b).
Proof. exact (eq_refl (term58 s a x b)). Qed.
Lemma lem5165553 (s : real -> Prop) (a : real) (b : real) : (term60 s a b) = (term60 s a b).
Proof. exact (fun_ext (fun x : real => @lem5165552 s a x b)). Qed.
Lemma lem5165554 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5165555 (s : real -> Prop) (a : real) (b : real) : (term61 s a b) = (term61 s a b).
Proof. exact (MK_COMB (@lem5165554) (@lem5165553 s a b)). Qed.
Lemma lem5165556 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term61 s a b.
Proof. exact (EQ_MP (@lem5165555 s a b) (@lem5165071 s a b h1)). Qed.
Lemma lem5165581 (y : real) (x : real) (z : real) : (term349 y x z) = (term349 y x z).
Proof. exact (eq_refl (term349 y x z)). Qed.
Lemma lem5165582 (y : real) (x : real) : (term350 y x) = (term350 y x).
Proof. exact (fun_ext (fun z : real => @lem5165581 y x z)). Qed.
Lemma lem5165583 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5165584 (y : real) (x : real) : (term351 y x) = (term351 y x).
Proof. exact (MK_COMB (@lem5165583) (@lem5165582 y x)). Qed.
Lemma lem5165585 (x : real) : (term352 x) = (term352 x).
Proof. exact (fun_ext (fun y : real => @lem5165584 y x)). Qed.
Lemma lem5165586 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5165587 (x : real) : (term353 x) = (term353 x).
Proof. exact (MK_COMB (@lem5165586) (@lem5165585 x)). Qed.
Lemma lem5165588 : term354 = term354.
Proof. exact (fun_ext (fun x : real => @lem5165587 x)). Qed.
Lemma lem5165589 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5165590 : term355 = term355.
Proof. exact (MK_COMB (@lem5165589) (@lem5165588)). Qed.
Lemma lem5165591 (h1 : term175) : term355.
Proof. exact (EQ_MP (@lem5165590) (@lem5165527 h1)). Qed.
Lemma lem5165612 (a : real) (s : real -> Prop) (b : real) : (term224 a s b) = (term224 a s b).
Proof. exact (eq_refl (term224 a s b)). Qed.
Lemma lem5165641 (x' : real -> real) (s : real -> Prop) (b : real) : (term266 x' s b) = (term266 x' s b).
Proof. exact (eq_refl (term266 x' s b)). Qed.
Lemma lem5165642 (x' : real -> real) (s : real -> Prop) : (term268 x' s) = (term268 x' s).
Proof. exact (fun_ext (fun b : real => @lem5165641 x' s b)). Qed.
Lemma lem5165643 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5165644 (x' : real -> real) (s : real -> Prop) : (term270 x' s) = (term270 x' s).
Proof. exact (MK_COMB (@lem5165643) (@lem5165642 x' s)). Qed.
Lemma lem5165661 (x : real) (s : real -> Prop) : (term211 x s) = (term211 x s).
Proof. exact (eq_refl (term211 x s)). Qed.
Lemma lem5165662 (s : real -> Prop) : (term213 s) = (term213 s).
Proof. exact (fun_ext (fun x : real => @lem5165661 x s)). Qed.
Lemma lem5165663 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5165664 (s : real -> Prop) : (term214 s) = (term214 s).
Proof. exact (MK_COMB (@lem5165663) (@lem5165662 s)). Qed.
Lemma lem5165665 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5165666 (s : real -> Prop) : (term221 s) = (term221 s).
Proof. exact (MK_COMB (@lem5165665) (@lem5165664 s)). Qed.
Lemma lem5165667 (x' : real -> real) (s : real -> Prop) : (term287 x' s) = (term287 x' s).
Proof. exact (MK_COMB (@lem5165666 s) (@lem5165644 x' s)). Qed.
Lemma lem5165668 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5165669 (x' : real -> real) (s : real -> Prop) : (term306 x' s) = (term306 x' s).
Proof. exact (MK_COMB (@lem5165668) (@lem5165667 x' s)). Qed.
Lemma lem5165670 (x' : real -> real) (a : real) (s : real -> Prop) (b : real) : (term308 x' a s b) = (term308 x' a s b).
Proof. exact (MK_COMB (@lem5165669 x' s) (@lem5165612 a s b)). Qed.
Lemma lem5165677 (x : real) (s : real -> Prop) : (term324 x s) = (term324 x s).
Proof. exact (eq_refl (term324 x s)). Qed.
Lemma lem5165678 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) : (term338 x x' a s b) = (term338 x x' a s b).
Proof. exact (MK_COMB (@lem5165677 x s) (@lem5165670 x' a s b)). Qed.
Lemma lem5165679 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term338 x x' a s b.
Proof. exact (EQ_MP (@lem5165678 x x' a s b) (@lem5165529 x x' a s b h1)). Qed.
Lemma lem5165680 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term308 x' a s b.
Proof. exact (proj2 (@lem5165679 x x' a s b h1)). Qed.
Lemma lem5165682 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term224 a s b.
Proof. exact (proj2 (@lem5165680 x x' a s b h1)). Qed.
Lemma lem5165683 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term287 x' s.
Proof. exact (proj1 (@lem5165680 x x' a s b h1)). Qed.
Lemma lem5165684 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term270 x' s.
Proof. exact (proj2 (@lem5165683 x x' a s b h1)). Qed.
Lemma lem5165685 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term214 s.
Proof. exact (proj1 (@lem5165683 x x' a s b h1)). Qed.
Lemma lem5165705 (a : real) (s : real -> Prop) (x : real) (b : real) : (term58 s a x b) = (term129 a s x b).
Proof. exact (@lem19490 (real_le a x) (term130 x s) (real_le x b)). Qed.
Lemma lem5165706 (a : real) (s : real -> Prop) (b : real) : (term60 s a b) = (term131 a s b).
Proof. exact (fun_ext (fun x : real => @lem5165705 a s x b)). Qed.
Lemma lem5165707 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5165709 (a : real) (s : real -> Prop) (b : real) : (term61 s a b) = (term132 a s b).
Proof. exact (MK_COMB (@lem5165707) (@lem5165706 a s b)). Qed.
Lemma lem5165710 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term132 a s b.
Proof. exact (EQ_MP (@lem5165709 a s b) (@lem5165556 s a b h1)). Qed.
Lemma lem5165724 (y : real) (x : real) (z : real) : (term349 y x z) = (term349 y x z).
Proof. exact (eq_refl (term349 y x z)). Qed.
Lemma lem5165725 (y : real) (x : real) : (term350 y x) = (term350 y x).
Proof. exact (fun_ext (fun z : real => @lem5165724 y x z)). Qed.
Lemma lem5165726 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5165727 (y : real) (x : real) : (term351 y x) = (term351 y x).
Proof. exact (MK_COMB (@lem5165726) (@lem5165725 y x)). Qed.
Lemma lem5165728 (x : real) : (term352 x) = (term352 x).
Proof. exact (fun_ext (fun y : real => @lem5165727 y x)). Qed.
Lemma lem5165729 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5165730 (x : real) : (term353 x) = (term353 x).
Proof. exact (MK_COMB (@lem5165729) (@lem5165728 x)). Qed.
Lemma lem5165731 : term354 = term354.
Proof. exact (fun_ext (fun x : real => @lem5165730 x)). Qed.
Lemma lem5165732 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5165734 : term355 = term355.
Proof. exact (MK_COMB (@lem5165732) (@lem5165731)). Qed.
Lemma lem5165735 (h1 : term175) : term355.
Proof. exact (EQ_MP (@lem5165734) (@lem5165591 h1)). Qed.
Lemma lem5165747 (x : real) (s : real -> Prop) : (term211 x s) = (term211 x s).
Proof. exact (eq_refl (term211 x s)). Qed.
Lemma lem5165748 (s : real -> Prop) : (term213 s) = (term213 s).
Proof. exact (fun_ext (fun x : real => @lem5165747 x s)). Qed.
Lemma lem5165749 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5165751 (s : real -> Prop) : (term214 s) = (term214 s).
Proof. exact (MK_COMB (@lem5165749) (@lem5165748 s)). Qed.
Lemma lem5165752 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term214 s.
Proof. exact (EQ_MP (@lem5165751 s) (@lem5165685 x x' a s b h1)). Qed.
Lemma lem5165779 (a : real) (s : real -> Prop) (h1 : term356 a s) : term356 a s.
Proof. exact (h1). Qed.
Lemma lem5165797 (a : real) (s : real -> Prop) (x : real) (b : real) : (term58 s a x b) = (term129 a s x b).
Proof. exact (@lem19490 (real_le a x) (term130 x s) (real_le x b)). Qed.
Lemma lem5165798 (a : real) (s : real -> Prop) (b : real) : (term60 s a b) = (term131 a s b).
Proof. exact (fun_ext (fun x : real => @lem5165797 a s x b)). Qed.
Lemma lem5165799 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5165801 (a : real) (s : real -> Prop) (b : real) : (term61 s a b) = (term132 a s b).
Proof. exact (MK_COMB (@lem5165799) (@lem5165798 a s b)). Qed.
Lemma lem5165802 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term132 a s b.
Proof. exact (EQ_MP (@lem5165801 a s b) (@lem5165556 s a b h1)). Qed.
Lemma lem5165862 (x' : real -> real) (s : real -> Prop) (b : real) : (term266 x' s b) = (term357 x' s b).
Proof. exact (@lem19699 (term147 x' b s) (term135 x' b) (term198 s b)). Qed.
Lemma lem5165863 (x' : real -> real) (s : real -> Prop) : (term268 x' s) = (term358 x' s).
Proof. exact (fun_ext (fun b : real => @lem5165862 x' s b)). Qed.
Lemma lem5165864 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5165866 (x' : real -> real) (s : real -> Prop) : (term270 x' s) = (term359 x' s).
Proof. exact (MK_COMB (@lem5165864) (@lem5165863 x' s)). Qed.
Lemma lem5165867 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term359 x' s.
Proof. exact (EQ_MP (@lem5165866 x' s) (@lem5165684 x x' a s b h1)). Qed.
Lemma lem5165871 (s : real -> Prop) (b : real) (h1 : term360 s b) : term360 s b.
Proof. exact (h1). Qed.
Lemma lem5165872 (_67527 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term133 a s b _67527.
Proof. exact (@lem5165710 s a b h1 _67527). Qed.
Lemma lem5165873 (a : real) (s : real -> Prop) (_67527 : real) (b : real) : (term133 a s b _67527) = (term129 a s _67527 b).
Proof. exact (eq_refl (term133 a s b _67527)). Qed.
Lemma lem5165874 (_67527 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term129 a s _67527 b.
Proof. exact (EQ_MP (@lem5165873 a s _67527 b) (@lem5165872 _67527 s a b h1)). Qed.
Lemma lem5165875 (_67528 : real) (h1 : term175) : term361 _67528.
Proof. exact (@lem5165735 h1 _67528). Qed.
Lemma lem5165876 (_67528 : real) : (term361 _67528) = (term353 _67528).
Proof. exact (eq_refl (term361 _67528)). Qed.
Lemma lem5165877 (_67528 : real) (h1 : term175) : term353 _67528.
Proof. exact (EQ_MP (@lem5165876 _67528) (@lem5165875 _67528 h1)). Qed.
Lemma lem5165878 (_67528 : real) (_67529 : real) (h1 : term175) : term362 _67528 _67529.
Proof. exact (@lem5165877 _67528 h1 _67529). Qed.
Lemma lem5165879 (_67529 : real) (_67528 : real) : (term362 _67528 _67529) = (term351 _67529 _67528).
Proof. exact (eq_refl (term362 _67528 _67529)). Qed.
Lemma lem5165880 (_67529 : real) (_67528 : real) (h1 : term175) : term351 _67529 _67528.
Proof. exact (EQ_MP (@lem5165879 _67529 _67528) (@lem5165878 _67528 _67529 h1)). Qed.
Lemma lem5165881 (_67529 : real) (_67528 : real) (_67530 : real) (h1 : term175) : term363 _67529 _67528 _67530.
Proof. exact (@lem5165880 _67529 _67528 h1 _67530). Qed.
Lemma lem5165882 (_67529 : real) (_67528 : real) (_67530 : real) : (term363 _67529 _67528 _67530) = (term349 _67529 _67528 _67530).
Proof. exact (eq_refl (term363 _67529 _67528 _67530)). Qed.
Lemma lem5165883 (_67529 : real) (_67528 : real) (_67530 : real) (h1 : term175) : term349 _67529 _67528 _67530.
Proof. exact (EQ_MP (@lem5165882 _67529 _67528 _67530) (@lem5165881 _67529 _67528 _67530 h1)). Qed.
Lemma lem5165884 (_67531 : real) (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term364 s _67531.
Proof. exact (@lem5165752 x x' a s b h1 _67531). Qed.
Lemma lem5165885 (_67531 : real) (s : real -> Prop) : (term364 s _67531) = (term211 _67531 s).
Proof. exact (eq_refl (term364 s _67531)). Qed.
Lemma lem5165890 (_67533 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term133 a s b _67533.
Proof. exact (@lem5165802 s a b h1 _67533). Qed.
Lemma lem5165891 (a : real) (s : real -> Prop) (_67533 : real) (b : real) : (term133 a s b _67533) = (term129 a s _67533 b).
Proof. exact (eq_refl (term133 a s b _67533)). Qed.
Lemma lem5165892 (_67533 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term129 a s _67533 b.
Proof. exact (EQ_MP (@lem5165891 a s _67533 b) (@lem5165890 _67533 s a b h1)). Qed.
Lemma lem5165905 (_67538 : real) (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term365 x' s _67538.
Proof. exact (@lem5165867 x x' a s b h1 _67538). Qed.
Lemma lem5165906 (x' : real -> real) (s : real -> Prop) (_67538 : real) : (term365 x' s _67538) = (term357 x' s _67538).
Proof. exact (eq_refl (term365 x' s _67538)). Qed.
Lemma lem5165907 (_67538 : real) (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term357 x' s _67538.
Proof. exact (EQ_MP (@lem5165906 x' s _67538) (@lem5165905 _67538 x x' a s b h1)). Qed.
Lemma lem5165926 (_67529 : real) (_67528 : real) (_67530 : real) : (term349 _67529 _67528 _67530) = (term366 _67529 _67528 _67530).
Proof. exact (@lem5163738 (term367 _67528 _67529) (term367 _67529 _67530) (real_le _67528 _67530)). Qed.
Lemma lem5165927 (_67529 : real) (_67528 : real) (_67530 : real) (h1 : term175) : term366 _67529 _67528 _67530.
Proof. exact (EQ_MP (@lem5165926 _67529 _67528 _67530) (@lem5165883 _67529 _67528 _67530 h1)). Qed.
Lemma lem5165935 (_67531 : real) (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term211 _67531 s.
Proof. exact (EQ_MP (@lem5165885 _67531 s) (@lem5165884 _67531 x x' a s b h1)). Qed.
Lemma lem5165937 (a : real) (s : real -> Prop) (h1 : term356 a s) : term356 a s.
Proof. exact (h1). Qed.
Lemma lem5165955 (_67527 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term368 s a _67527.
Proof. exact (proj1 (@lem5165874 _67527 s a b h1)). Qed.
Lemma lem5165983 (s : real -> Prop) (b : real) (h1 : term360 s b) : term360 s b.
Proof. exact (h1). Qed.
Lemma lem5165989 (_67538 : real) (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term369 x' s _67538.
Proof. exact (proj1 (@lem5165907 _67538 x x' a s b h1)). Qed.
Lemma lem5165995 (_67538 : real) (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term370 x' s _67538.
Proof. exact (proj2 (@lem5165907 _67538 x x' a s b h1)). Qed.
Lemma lem5166007 (_67533 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term136 s _67533 b.
Proof. exact (proj2 (@lem5165892 _67533 s a b h1)). Qed.
Lemma lem5166009 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : @IN real x s.
Proof. exact (proj1 (@lem5165679 x x' a s b h1)). Qed.
Lemma lem5166010 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term371 x s.
Proof. exact (fun h0 : term130 x s => @lem5166009 x x' a s b h1). Qed.
Lemma lem5166012 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5166013 (x : real) (s : real -> Prop) : (term371 x s) = (@IN real x s).
Proof. exact (@lem5166012 (@IN real x s)). Qed.
Lemma lem5166014 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : @IN real x s.
Proof. exact (EQ_MP (@lem5166013 x s) (@lem5166010 x x' a s b h1)). Qed.
Lemma lem5166020 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5166021 (a : real) (_67527 : real) (s : real -> Prop) : (term368 s a _67527) = (term372 a _67527 s).
Proof. exact (@lem5166020 (real_le a _67527) (term130 _67527 s)). Qed.
Lemma lem5166027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5166028 (a : real) (_67527 : real) (s : real -> Prop) : (term373 s a _67527) = (term374 a _67527 s).
Proof. exact (MK_COMB (@lem5166027) (@lem5166021 a _67527 s)). Qed.
Lemma lem5166034 (a : real) (_67527 : real) (s : real -> Prop) : (term372 a _67527 s) = (term372 a _67527 s).
Proof. exact (eq_refl (term372 a _67527 s)). Qed.
Lemma lem5166035 (a : real) (_67527 : real) (s : real -> Prop) : ((term368 s a _67527) = (term372 a _67527 s)) = ((term372 a _67527 s) = (term372 a _67527 s)).
Proof. exact (MK_COMB (@lem5166028 a _67527 s) (@lem5166034 a _67527 s)). Qed.
Lemma lem5166037 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5166038 (x : Prop) : (x = x) = True.
Proof. exact (@lem5166037 Prop x). Qed.
Lemma lem5166039 (a : real) (_67527 : real) (s : real -> Prop) : ((term372 a _67527 s) = (term372 a _67527 s)) = True.
Proof. exact (@lem5166038 (term372 a _67527 s)). Qed.
Lemma lem5166040 (a : real) (_67527 : real) (s : real -> Prop) : ((term368 s a _67527) = (term372 a _67527 s)) = True.
Proof. exact (TRANS (@lem5166035 a _67527 s) (@lem5166039 a _67527 s)). Qed.
Lemma lem5166041 (a : real) (_67527 : real) (s : real -> Prop) : True = ((term368 s a _67527) = (term372 a _67527 s)).
Proof. exact (SYM (@lem5166040 a _67527 s)). Qed.
Lemma lem5166042 (a : real) (_67527 : real) (s : real -> Prop) : (term368 s a _67527) = (term372 a _67527 s).
Proof. exact (EQ_MP (@lem5166041 a _67527 s) (@lem0)). Qed.
Lemma lem5166043 (_67527 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term372 a _67527 s.
Proof. exact (EQ_MP (@lem5166042 a _67527 s) (@lem5165955 _67527 s a b h1)). Qed.
Lemma lem5166045 (b : Prop) (a : Prop) : (a \/ b) = (term153 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5166046 (s : real -> Prop) (a : real) (_67527 : real) : (term372 a _67527 s) = (term375 s a _67527).
Proof. exact (@lem5166045 (term130 _67527 s) (real_le a _67527)). Qed.
Lemma lem5166048 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5166049 (_67527 : real) (s : real -> Prop) : (term155 _67527 s) = (@IN real _67527 s).
Proof. exact (@lem5166048 (@IN real _67527 s)). Qed.
Lemma lem5166050 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5166051 (_67527 : real) (s : real -> Prop) : (term156 _67527 s) = (term157 _67527 s).
Proof. exact (MK_COMB (@lem5166050) (@lem5166049 _67527 s)). Qed.
Lemma lem5166052 (a : real) (_67527 : real) : (real_le a _67527) = (real_le a _67527).
Proof. exact (eq_refl (real_le a _67527)). Qed.
Lemma lem5166053 (s : real -> Prop) (a : real) (_67527 : real) : (term375 s a _67527) = (term376 s a _67527).
Proof. exact (MK_COMB (@lem5166051 _67527 s) (@lem5166052 a _67527)). Qed.
Lemma lem5166054 (s : real -> Prop) (a : real) (_67527 : real) : (term372 a _67527 s) = (term376 s a _67527).
Proof. exact (TRANS (@lem5166046 s a _67527) (@lem5166053 s a _67527)). Qed.
Lemma lem5166057 (_67527 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term376 s a _67527.
Proof. exact (EQ_MP (@lem5166054 s a _67527) (@lem5166043 _67527 s a b h1)). Qed.
Lemma lem5166058 (x : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term376 s a x.
Proof. exact (@lem5166057 x s a b h1). Qed.
Lemma lem5166061 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term338 x x' a s b) : real_le a x.
Proof. exact (@lem5166058 x s a b h1 (@lem5166014 x x' a s b h2)). Qed.
Lemma lem5166062 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term338 x x' a s b) : term377 a x.
Proof. exact (fun h0 : term367 a x => @lem5166061 x x' a s b h1 h2). Qed.
Lemma lem5166064 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5166065 (a : real) (x : real) : (term377 a x) = (real_le a x).
Proof. exact (@lem5166064 (real_le a x)). Qed.
Lemma lem5166066 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term338 x x' a s b) : real_le a x.
Proof. exact (EQ_MP (@lem5166065 a x) (@lem5166062 x x' a s b h1 h2)). Qed.
Lemma lem5166068 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : @IN real x s.
Proof. exact (proj1 (@lem5165679 x x' a s b h1)). Qed.
Lemma lem5166069 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term371 x s.
Proof. exact (fun h0 : term130 x s => @lem5166068 x x' a s b h1). Qed.
Lemma lem5166071 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5166072 (x : real) (s : real -> Prop) : (term371 x s) = (@IN real x s).
Proof. exact (@lem5166071 (@IN real x s)). Qed.
Lemma lem5166073 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : @IN real x s.
Proof. exact (EQ_MP (@lem5166072 x s) (@lem5166069 x x' a s b h1)). Qed.
Lemma lem5166079 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5166080 (_67531 : real) (s : real -> Prop) : (term211 _67531 s) = (term378 _67531 s).
Proof. exact (@lem5166079 (term212 _67531 s) (term130 _67531 s)). Qed.
Lemma lem5166086 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5166087 (_67531 : real) (s : real -> Prop) : (term379 _67531 s) = (term380 _67531 s).
Proof. exact (MK_COMB (@lem5166086) (@lem5166080 _67531 s)). Qed.
Lemma lem5166093 (_67531 : real) (s : real -> Prop) : (term378 _67531 s) = (term378 _67531 s).
Proof. exact (eq_refl (term378 _67531 s)). Qed.
Lemma lem5166094 (_67531 : real) (s : real -> Prop) : ((term211 _67531 s) = (term378 _67531 s)) = ((term378 _67531 s) = (term378 _67531 s)).
Proof. exact (MK_COMB (@lem5166087 _67531 s) (@lem5166093 _67531 s)). Qed.
Lemma lem5166096 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5166097 (x : Prop) : (x = x) = True.
Proof. exact (@lem5166096 Prop x). Qed.
Lemma lem5166098 (_67531 : real) (s : real -> Prop) : ((term378 _67531 s) = (term378 _67531 s)) = True.
Proof. exact (@lem5166097 (term378 _67531 s)). Qed.
Lemma lem5166099 (_67531 : real) (s : real -> Prop) : ((term211 _67531 s) = (term378 _67531 s)) = True.
Proof. exact (TRANS (@lem5166094 _67531 s) (@lem5166098 _67531 s)). Qed.
Lemma lem5166100 (_67531 : real) (s : real -> Prop) : True = ((term211 _67531 s) = (term378 _67531 s)).
Proof. exact (SYM (@lem5166099 _67531 s)). Qed.
Lemma lem5166101 (_67531 : real) (s : real -> Prop) : (term211 _67531 s) = (term378 _67531 s).
Proof. exact (EQ_MP (@lem5166100 _67531 s) (@lem0)). Qed.
Lemma lem5166102 (_67531 : real) (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term378 _67531 s.
Proof. exact (EQ_MP (@lem5166101 _67531 s) (@lem5165935 _67531 x x' a s b h1)). Qed.
Lemma lem5166104 (b : Prop) (a : Prop) : (a \/ b) = (term153 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5166105 (_67531 : real) (s : real -> Prop) : (term378 _67531 s) = (term381 _67531 s).
Proof. exact (@lem5166104 (term130 _67531 s) (term212 _67531 s)). Qed.
Lemma lem5166107 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5166108 (_67531 : real) (s : real -> Prop) : (term155 _67531 s) = (@IN real _67531 s).
Proof. exact (@lem5166107 (@IN real _67531 s)). Qed.
Lemma lem5166109 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5166110 (_67531 : real) (s : real -> Prop) : (term156 _67531 s) = (term157 _67531 s).
Proof. exact (MK_COMB (@lem5166109) (@lem5166108 _67531 s)). Qed.
Lemma lem5166111 (_67531 : real) (s : real -> Prop) : (term212 _67531 s) = (term212 _67531 s).
Proof. exact (eq_refl (term212 _67531 s)). Qed.
Lemma lem5166112 (_67531 : real) (s : real -> Prop) : (term381 _67531 s) = (term203 _67531 s).
Proof. exact (MK_COMB (@lem5166110 _67531 s) (@lem5166111 _67531 s)). Qed.
Lemma lem5166113 (_67531 : real) (s : real -> Prop) : (term378 _67531 s) = (term203 _67531 s).
Proof. exact (TRANS (@lem5166105 _67531 s) (@lem5166112 _67531 s)). Qed.
Lemma lem5166116 (_67531 : real) (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term203 _67531 s.
Proof. exact (EQ_MP (@lem5166113 _67531 s) (@lem5166102 _67531 x x' a s b h1)). Qed.
Lemma lem5166117 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term203 x s.
Proof. exact (@lem5166116 x x x' a s b h1). Qed.
Lemma lem5166120 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term212 x s.
Proof. exact (@lem5166117 x x' a s b h1 (@lem5166073 x x' a s b h1)). Qed.
Lemma lem5166121 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term382 x s.
Proof. exact (fun h0 : term356 x s => @lem5166120 x x' a s b h1). Qed.
Lemma lem5166123 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5166124 (x : real) (s : real -> Prop) : (term382 x s) = (term212 x s).
Proof. exact (@lem5166123 (term212 x s)). Qed.
Lemma lem5166125 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term212 x s.
Proof. exact (EQ_MP (@lem5166124 x s) (@lem5166121 x x' a s b h1)). Qed.
Lemma lem5166141 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5166142 (_67528 : real) (_67529 : real) (_67530 : real) : (term383 _67529 _67528 _67530) = (term384 _67528 _67529 _67530).
Proof. exact (@lem5166141 (real_le _67528 _67530) (term367 _67529 _67530)). Qed.
Lemma lem5166148 (_67528 : real) (_67529 : real) : (term385 _67528 _67529) = (term385 _67528 _67529).
Proof. exact (eq_refl (term385 _67528 _67529)). Qed.
Lemma lem5166149 (_67528 : real) (_67529 : real) (_67530 : real) : (term366 _67529 _67528 _67530) = (term386 _67528 _67529 _67530).
Proof. exact (MK_COMB (@lem5166148 _67528 _67529) (@lem5166142 _67528 _67529 _67530)). Qed.
Lemma lem5166153 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5166154 (_67528 : real) (_67529 : real) (_67530 : real) : (term386 _67528 _67529 _67530) = (term387 _67528 _67529 _67530).
Proof. exact (@lem5166153 (real_le _67528 _67530) (term367 _67528 _67529) (term367 _67529 _67530)). Qed.
Lemma lem5166170 (_67528 : real) (_67529 : real) (_67530 : real) : (term366 _67529 _67528 _67530) = (term387 _67528 _67529 _67530).
Proof. exact (TRANS (@lem5166149 _67528 _67529 _67530) (@lem5166154 _67528 _67529 _67530)). Qed.
Lemma lem5166171 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5166172 (_67528 : real) (_67529 : real) (_67530 : real) : (term388 _67529 _67528 _67530) = (term389 _67528 _67529 _67530).
Proof. exact (MK_COMB (@lem5166171) (@lem5166170 _67528 _67529 _67530)). Qed.
Lemma lem5166188 (_67528 : real) (_67529 : real) (_67530 : real) : (term387 _67528 _67529 _67530) = (term387 _67528 _67529 _67530).
Proof. exact (eq_refl (term387 _67528 _67529 _67530)). Qed.
Lemma lem5166189 (_67528 : real) (_67529 : real) (_67530 : real) : ((term366 _67529 _67528 _67530) = (term387 _67528 _67529 _67530)) = ((term387 _67528 _67529 _67530) = (term387 _67528 _67529 _67530)).
Proof. exact (MK_COMB (@lem5166172 _67528 _67529 _67530) (@lem5166188 _67528 _67529 _67530)). Qed.
Lemma lem5166191 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5166192 (x : Prop) : (x = x) = True.
Proof. exact (@lem5166191 Prop x). Qed.
Lemma lem5166193 (_67528 : real) (_67529 : real) (_67530 : real) : ((term387 _67528 _67529 _67530) = (term387 _67528 _67529 _67530)) = True.
Proof. exact (@lem5166192 (term387 _67528 _67529 _67530)). Qed.
Lemma lem5166194 (_67528 : real) (_67529 : real) (_67530 : real) : ((term366 _67529 _67528 _67530) = (term387 _67528 _67529 _67530)) = True.
Proof. exact (TRANS (@lem5166189 _67528 _67529 _67530) (@lem5166193 _67528 _67529 _67530)). Qed.
Lemma lem5166195 (_67528 : real) (_67529 : real) (_67530 : real) : True = ((term366 _67529 _67528 _67530) = (term387 _67528 _67529 _67530)).
Proof. exact (SYM (@lem5166194 _67528 _67529 _67530)). Qed.
Lemma lem5166196 (_67528 : real) (_67529 : real) (_67530 : real) : (term366 _67529 _67528 _67530) = (term387 _67528 _67529 _67530).
Proof. exact (EQ_MP (@lem5166195 _67528 _67529 _67530) (@lem0)). Qed.
Lemma lem5166197 (_67528 : real) (_67529 : real) (_67530 : real) (h1 : term175) : term387 _67528 _67529 _67530.
Proof. exact (EQ_MP (@lem5166196 _67528 _67529 _67530) (@lem5165927 _67529 _67528 _67530 h1)). Qed.
Lemma lem5166199 (b : Prop) (a : Prop) : (a \/ b) = (term153 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5166200 (_67529 : real) (_67528 : real) (_67530 : real) : (term387 _67528 _67529 _67530) = (term390 _67529 _67528 _67530).
Proof. exact (@lem5166199 (term345 _67528 _67529 _67530) (real_le _67528 _67530)). Qed.
Lemma lem5166202 (a : Prop) (b : Prop) : (term391 a b) = (term392 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5166203 (_67528 : real) (_67529 : real) (_67530 : real) : (term393 _67528 _67529 _67530) = (term394 _67528 _67529 _67530).
Proof. exact (@lem5166202 (term367 _67528 _67529) (term367 _67529 _67530)). Qed.
Lemma lem5166205 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5166206 (_67528 : real) (_67529 : real) : (term395 _67528 _67529) = (real_le _67528 _67529).
Proof. exact (@lem5166205 (real_le _67528 _67529)). Qed.
Lemma lem5166207 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5166208 (_67528 : real) (_67529 : real) : (term396 _67528 _67529) = (term397 _67528 _67529).
Proof. exact (MK_COMB (@lem5166207) (@lem5166206 _67528 _67529)). Qed.
Lemma lem5166210 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5166211 (_67529 : real) (_67530 : real) : (term395 _67529 _67530) = (real_le _67529 _67530).
Proof. exact (@lem5166210 (real_le _67529 _67530)). Qed.
Lemma lem5166212 (_67528 : real) (_67529 : real) (_67530 : real) : (term394 _67528 _67529 _67530) = (term59 _67528 _67529 _67530).
Proof. exact (MK_COMB (@lem5166208 _67528 _67529) (@lem5166211 _67529 _67530)). Qed.
Lemma lem5166213 (_67528 : real) (_67529 : real) (_67530 : real) : (term393 _67528 _67529 _67530) = (term59 _67528 _67529 _67530).
Proof. exact (TRANS (@lem5166203 _67528 _67529 _67530) (@lem5166212 _67528 _67529 _67530)). Qed.
Lemma lem5166214 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5166215 (_67528 : real) (_67529 : real) (_67530 : real) : (term398 _67528 _67529 _67530) = (term399 _67528 _67529 _67530).
Proof. exact (MK_COMB (@lem5166214) (@lem5166213 _67528 _67529 _67530)). Qed.
Lemma lem5166216 (_67528 : real) (_67530 : real) : (real_le _67528 _67530) = (real_le _67528 _67530).
Proof. exact (eq_refl (real_le _67528 _67530)). Qed.
Lemma lem5166217 (_67529 : real) (_67528 : real) (_67530 : real) : (term390 _67529 _67528 _67530) = (term192 _67529 _67528 _67530).
Proof. exact (MK_COMB (@lem5166215 _67528 _67529 _67530) (@lem5166216 _67528 _67530)). Qed.
Lemma lem5166218 (_67529 : real) (_67528 : real) (_67530 : real) : (term387 _67528 _67529 _67530) = (term192 _67529 _67528 _67530).
Proof. exact (TRANS (@lem5166200 _67529 _67528 _67530) (@lem5166217 _67529 _67528 _67530)). Qed.
Lemma lem5166220 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term338 x x' a s b) : term400 a x s.
Proof. exact (conj (@lem5166066 x x' a s b h1 h2) (@lem5166125 x x' a s b h2)). Qed.
Lemma lem5166222 (_67529 : real) (_67528 : real) (_67530 : real) (h1 : term175) : term192 _67529 _67528 _67530.
Proof. exact (EQ_MP (@lem5166218 _67529 _67528 _67530) (@lem5166197 _67528 _67529 _67530 h1)). Qed.
Lemma lem5166223 (x : real) (a : real) (s : real -> Prop) (h1 : term175) : term401 x a s.
Proof. exact (@lem5166222 x a (sup s) h1). Qed.
Lemma lem5166226 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term338 x x' a s b) : term212 a s.
Proof. exact (@lem5166223 x a s h1 (@lem5166220 x x' a s b h2 h3)). Qed.
Lemma lem5166227 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term338 x x' a s b) : term382 a s.
Proof. exact (fun h0 : term356 a s => @lem5166226 x x' a s b h1 h2 h3). Qed.
Lemma lem5166229 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5166230 (a : real) (s : real -> Prop) : (term382 a s) = (term212 a s).
Proof. exact (@lem5166229 (term212 a s)). Qed.
Lemma lem5166231 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term338 x x' a s b) : term212 a s.
Proof. exact (EQ_MP (@lem5166230 a s) (@lem5166227 x x' a s b h1 h2 h3)). Qed.
Lemma lem5166234 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5166236 (a : real) (s : real -> Prop) : (term356 a s) = (term402 a s).
Proof. exact (@lem5166234 (term212 a s)). Qed.
Lemma lem5166239 (a : real) (s : real -> Prop) (h1 : term356 a s) : term402 a s.
Proof. exact (EQ_MP (@lem5166236 a s) (@lem5165937 a s h1)). Qed.
Lemma lem5166242 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term356 a s) (h4 : term338 x x' a s b) : False.
Proof. exact (@lem5166239 a s h3 (@lem5166231 x x' a s b h1 h2 h4)). Qed.
Lemma lem5166243 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term356 a s) (h4 : term338 x x' a s b) : term146.
Proof. exact (fun h0 : ~ False => @lem5166242 x x' a s b h1 h2 h3 h4). Qed.
Lemma lem5166245 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5166246 : term146 = False.
Proof. exact (@lem5166245 False). Qed.
Lemma lem5166247 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term356 a s) (h4 : term338 x x' a s b) : False.
Proof. exact (EQ_MP (@lem5166246) (@lem5166243 x x' a s b h1 h2 h3 h4)). Qed.
Lemma lem5166250 (s : real -> Prop) (b : real) (h1 : term360 s b) : term360 s b.
Proof. exact (h1). Qed.
Lemma lem5166251 (s : real -> Prop) (b : real) (h1 : term360 s b) : term403 s b.
Proof. exact (fun h0 : term198 s b => @lem5166250 s b h1). Qed.
Lemma lem5166253 (p : Prop) : (term404 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5166254 (s : real -> Prop) (b : real) : (term403 s b) = (term360 s b).
Proof. exact (@lem5166253 (term198 s b)). Qed.
Lemma lem5166255 (s : real -> Prop) (b : real) (h1 : term360 s b) : term360 s b.
Proof. exact (EQ_MP (@lem5166254 s b) (@lem5166251 s b h1)). Qed.
Lemma lem5166257 (b : Prop) (a : Prop) : (a \/ b) = (term153 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5166260 (x' : real -> real) (_67538 : real) (s : real -> Prop) : (term369 x' s _67538) = (term405 x' _67538 s).
Proof. exact (@lem5166257 (term198 s _67538) (term147 x' _67538 s)). Qed.
Lemma lem5166263 (_67538 : real) (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term405 x' _67538 s.
Proof. exact (EQ_MP (@lem5166260 x' _67538 s) (@lem5165989 _67538 x x' a s b h1)). Qed.
Lemma lem5166264 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term405 x' b s.
Proof. exact (@lem5166263 b x x' a s b h1). Qed.
Lemma lem5166267 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term360 s b) (h2 : term338 x x' a s b) : term147 x' b s.
Proof. exact (@lem5166264 x x' a s b h2 (@lem5166255 s b h1)). Qed.
Lemma lem5166268 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term360 s b) (h2 : term338 x x' a s b) : term148 x' b s.
Proof. exact (fun h0 : term149 x' b s => @lem5166267 x x' a s b h1 h2). Qed.
Lemma lem5166270 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5166271 (x' : real -> real) (b : real) (s : real -> Prop) : (term148 x' b s) = (term147 x' b s).
Proof. exact (@lem5166270 (term147 x' b s)). Qed.
Lemma lem5166272 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term360 s b) (h2 : term338 x x' a s b) : term147 x' b s.
Proof. exact (EQ_MP (@lem5166271 x' b s) (@lem5166268 x x' a s b h1 h2)). Qed.
Lemma lem5166278 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5166279 (b : real) (_67533 : real) (s : real -> Prop) : (term136 s _67533 b) = (term150 b _67533 s).
Proof. exact (@lem5166278 (real_le _67533 b) (term130 _67533 s)). Qed.
Lemma lem5166285 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5166286 (b : real) (_67533 : real) (s : real -> Prop) : (term151 s _67533 b) = (term152 b _67533 s).
Proof. exact (MK_COMB (@lem5166285) (@lem5166279 b _67533 s)). Qed.
Lemma lem5166292 (b : real) (_67533 : real) (s : real -> Prop) : (term150 b _67533 s) = (term150 b _67533 s).
Proof. exact (eq_refl (term150 b _67533 s)). Qed.
Lemma lem5166293 (b : real) (_67533 : real) (s : real -> Prop) : ((term136 s _67533 b) = (term150 b _67533 s)) = ((term150 b _67533 s) = (term150 b _67533 s)).
Proof. exact (MK_COMB (@lem5166286 b _67533 s) (@lem5166292 b _67533 s)). Qed.
Lemma lem5166295 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5166296 (x : Prop) : (x = x) = True.
Proof. exact (@lem5166295 Prop x). Qed.
Lemma lem5166297 (b : real) (_67533 : real) (s : real -> Prop) : ((term150 b _67533 s) = (term150 b _67533 s)) = True.
Proof. exact (@lem5166296 (term150 b _67533 s)). Qed.
Lemma lem5166298 (b : real) (_67533 : real) (s : real -> Prop) : ((term136 s _67533 b) = (term150 b _67533 s)) = True.
Proof. exact (TRANS (@lem5166293 b _67533 s) (@lem5166297 b _67533 s)). Qed.
Lemma lem5166299 (b : real) (_67533 : real) (s : real -> Prop) : True = ((term136 s _67533 b) = (term150 b _67533 s)).
Proof. exact (SYM (@lem5166298 b _67533 s)). Qed.
Lemma lem5166300 (b : real) (_67533 : real) (s : real -> Prop) : (term136 s _67533 b) = (term150 b _67533 s).
Proof. exact (EQ_MP (@lem5166299 b _67533 s) (@lem0)). Qed.
Lemma lem5166301 (_67533 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term150 b _67533 s.
Proof. exact (EQ_MP (@lem5166300 b _67533 s) (@lem5166007 _67533 s a b h1)). Qed.
Lemma lem5166303 (b : Prop) (a : Prop) : (a \/ b) = (term153 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5166304 (s : real -> Prop) (_67533 : real) (b : real) : (term150 b _67533 s) = (term154 s _67533 b).
Proof. exact (@lem5166303 (term130 _67533 s) (real_le _67533 b)). Qed.
Lemma lem5166306 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5166307 (_67533 : real) (s : real -> Prop) : (term155 _67533 s) = (@IN real _67533 s).
Proof. exact (@lem5166306 (@IN real _67533 s)). Qed.
Lemma lem5166308 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5166309 (_67533 : real) (s : real -> Prop) : (term156 _67533 s) = (term157 _67533 s).
Proof. exact (MK_COMB (@lem5166308) (@lem5166307 _67533 s)). Qed.
Lemma lem5166310 (_67533 : real) (b : real) : (real_le _67533 b) = (real_le _67533 b).
Proof. exact (eq_refl (real_le _67533 b)). Qed.
Lemma lem5166311 (s : real -> Prop) (_67533 : real) (b : real) : (term154 s _67533 b) = (term50 s _67533 b).
Proof. exact (MK_COMB (@lem5166309 _67533 s) (@lem5166310 _67533 b)). Qed.
Lemma lem5166312 (s : real -> Prop) (_67533 : real) (b : real) : (term150 b _67533 s) = (term50 s _67533 b).
Proof. exact (TRANS (@lem5166304 s _67533 b) (@lem5166311 s _67533 b)). Qed.
Lemma lem5166315 (_67533 : real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term50 s _67533 b.
Proof. exact (EQ_MP (@lem5166312 s _67533 b) (@lem5166301 _67533 s a b h1)). Qed.
Lemma lem5166316 (x' : real -> real) (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term158 s x' b.
Proof. exact (@lem5166315 (x' b) s a b h1). Qed.
Lemma lem5166319 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term360 s b) (h3 : term338 x x' a s b) : term159 x' b.
Proof. exact (@lem5166316 x' s a b h1 (@lem5166272 x x' a s b h2 h3)). Qed.
Lemma lem5166320 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term360 s b) (h3 : term338 x x' a s b) : term160 x' b.
Proof. exact (fun h0 : term135 x' b => @lem5166319 x x' a s b h1 h2 h3). Qed.
Lemma lem5166322 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5166323 (x' : real -> real) (b : real) : (term160 x' b) = (term159 x' b).
Proof. exact (@lem5166322 (term159 x' b)). Qed.
Lemma lem5166324 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term360 s b) (h3 : term338 x x' a s b) : term159 x' b.
Proof. exact (EQ_MP (@lem5166323 x' b) (@lem5166320 x x' a s b h1 h2 h3)). Qed.
Lemma lem5166330 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5166331 (s : real -> Prop) (x' : real -> real) (_67538 : real) : (term370 x' s _67538) = (term406 s x' _67538).
Proof. exact (@lem5166330 (term198 s _67538) (term135 x' _67538)). Qed.
Lemma lem5166337 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5166338 (s : real -> Prop) (x' : real -> real) (_67538 : real) : (term407 x' s _67538) = (term408 s x' _67538).
Proof. exact (MK_COMB (@lem5166337) (@lem5166331 s x' _67538)). Qed.
Lemma lem5166344 (s : real -> Prop) (x' : real -> real) (_67538 : real) : (term406 s x' _67538) = (term406 s x' _67538).
Proof. exact (eq_refl (term406 s x' _67538)). Qed.
Lemma lem5166345 (s : real -> Prop) (x' : real -> real) (_67538 : real) : ((term370 x' s _67538) = (term406 s x' _67538)) = ((term406 s x' _67538) = (term406 s x' _67538)).
Proof. exact (MK_COMB (@lem5166338 s x' _67538) (@lem5166344 s x' _67538)). Qed.
Lemma lem5166347 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5166348 (x : Prop) : (x = x) = True.
Proof. exact (@lem5166347 Prop x). Qed.
Lemma lem5166349 (s : real -> Prop) (x' : real -> real) (_67538 : real) : ((term406 s x' _67538) = (term406 s x' _67538)) = True.
Proof. exact (@lem5166348 (term406 s x' _67538)). Qed.
Lemma lem5166350 (s : real -> Prop) (x' : real -> real) (_67538 : real) : ((term370 x' s _67538) = (term406 s x' _67538)) = True.
Proof. exact (TRANS (@lem5166345 s x' _67538) (@lem5166349 s x' _67538)). Qed.
Lemma lem5166351 (s : real -> Prop) (x' : real -> real) (_67538 : real) : True = ((term370 x' s _67538) = (term406 s x' _67538)).
Proof. exact (SYM (@lem5166350 s x' _67538)). Qed.
Lemma lem5166352 (s : real -> Prop) (x' : real -> real) (_67538 : real) : (term370 x' s _67538) = (term406 s x' _67538).
Proof. exact (EQ_MP (@lem5166351 s x' _67538) (@lem0)). Qed.
Lemma lem5166353 (_67538 : real) (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term406 s x' _67538.
Proof. exact (EQ_MP (@lem5166352 s x' _67538) (@lem5165995 _67538 x x' a s b h1)). Qed.
Lemma lem5166355 (b : Prop) (a : Prop) : (a \/ b) = (term153 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5166356 (x' : real -> real) (s : real -> Prop) (_67538 : real) : (term406 s x' _67538) = (term409 x' s _67538).
Proof. exact (@lem5166355 (term135 x' _67538) (term198 s _67538)). Qed.
Lemma lem5166358 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5166359 (x' : real -> real) (_67538 : real) : (term410 x' _67538) = (term159 x' _67538).
Proof. exact (@lem5166358 (term159 x' _67538)). Qed.
Lemma lem5166360 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5166361 (x' : real -> real) (_67538 : real) : (term411 x' _67538) = (term412 x' _67538).
Proof. exact (MK_COMB (@lem5166360) (@lem5166359 x' _67538)). Qed.
Lemma lem5166362 (s : real -> Prop) (_67538 : real) : (term198 s _67538) = (term198 s _67538).
Proof. exact (eq_refl (term198 s _67538)). Qed.
Lemma lem5166363 (x' : real -> real) (s : real -> Prop) (_67538 : real) : (term409 x' s _67538) = (term413 x' s _67538).
Proof. exact (MK_COMB (@lem5166361 x' _67538) (@lem5166362 s _67538)). Qed.
Lemma lem5166364 (x' : real -> real) (s : real -> Prop) (_67538 : real) : (term406 s x' _67538) = (term413 x' s _67538).
Proof. exact (TRANS (@lem5166356 x' s _67538) (@lem5166363 x' s _67538)). Qed.
Lemma lem5166367 (_67538 : real) (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term413 x' s _67538.
Proof. exact (EQ_MP (@lem5166364 x' s _67538) (@lem5166353 _67538 x x' a s b h1)). Qed.
Lemma lem5166368 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term338 x x' a s b) : term413 x' s b.
Proof. exact (@lem5166367 b x x' a s b h1). Qed.
Lemma lem5166371 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term360 s b) (h3 : term338 x x' a s b) : term198 s b.
Proof. exact (@lem5166368 x x' a s b h3 (@lem5166324 x x' a s b h1 h2 h3)). Qed.
Lemma lem5166372 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term338 x x' a s b) : term414 s b.
Proof. exact (fun h0 : term360 s b => @lem5166371 x x' a s b h1 h0 h2). Qed.
Lemma lem5166374 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5166375 (s : real -> Prop) (b : real) : (term414 s b) = (term198 s b).
Proof. exact (@lem5166374 (term198 s b)). Qed.
Lemma lem5166376 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term338 x x' a s b) : term198 s b.
Proof. exact (EQ_MP (@lem5166375 s b) (@lem5166372 x x' a s b h1 h2)). Qed.
Lemma lem5166379 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5166381 (s : real -> Prop) (b : real) : (term360 s b) = (term415 s b).
Proof. exact (@lem5166379 (term198 s b)). Qed.
Lemma lem5166384 (s : real -> Prop) (b : real) (h1 : term360 s b) : term415 s b.
Proof. exact (EQ_MP (@lem5166381 s b) (@lem5165983 s b h1)). Qed.
Lemma lem5166387 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term360 s b) (h3 : term338 x x' a s b) : False.
Proof. exact (@lem5166384 s b h2 (@lem5166376 x x' a s b h1 h3)). Qed.
Lemma lem5166388 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term360 s b) (h3 : term338 x x' a s b) : term146.
Proof. exact (fun h0 : ~ False => @lem5166387 x x' a s b h1 h2 h3). Qed.
Lemma lem5166390 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5166391 : term146 = False.
Proof. exact (@lem5166390 False). Qed.
Lemma lem5166392 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term360 s b) (h3 : term338 x x' a s b) : False.
Proof. exact (EQ_MP (@lem5166391) (@lem5166388 x x' a s b h1 h2 h3)). Qed.
Lemma lem5166393 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term360 s b) (h3 : term338 x x' a s b) : (term360 s b) = False.
Proof. exact (prop_ext (fun h4 : term360 s b => @lem5166392 x x' a s b h1 h2 h3) (fun h4 : False => @lem5165983 s b h2)). Qed.
Lemma lem5166394 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term360 s b) (h3 : term338 x x' a s b) : False.
Proof. exact (EQ_MP (@lem5166393 x x' a s b h1 h2 h3) (@lem5165983 s b h2)). Qed.
Lemma lem5166395 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term356 a s) (h4 : term338 x x' a s b) : (term356 a s) = False.
Proof. exact (prop_ext (fun h5 : term356 a s => @lem5166247 x x' a s b h1 h2 h3 h4) (fun h5 : False => @lem5165937 a s h3)). Qed.
Lemma lem5166396 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term356 a s) (h4 : term338 x x' a s b) : False.
Proof. exact (EQ_MP (@lem5166395 x x' a s b h1 h2 h3 h4) (@lem5165937 a s h3)). Qed.
Lemma lem5166397 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term360 s b) (h3 : term338 x x' a s b) : (term360 s b) = False.
Proof. exact (prop_ext (fun h4 : term360 s b => @lem5166394 x x' a s b h1 h2 h3) (fun h4 : False => @lem5165871 s b h2)). Qed.
Lemma lem5166398 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term360 s b) (h3 : term338 x x' a s b) : False.
Proof. exact (EQ_MP (@lem5166397 x x' a s b h1 h2 h3) (@lem5165871 s b h2)). Qed.
Lemma lem5166399 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term356 a s) (h4 : term338 x x' a s b) : (term356 a s) = False.
Proof. exact (prop_ext (fun h5 : term356 a s => @lem5166396 x x' a s b h1 h2 h3 h4) (fun h5 : False => @lem5165779 a s h3)). Qed.
Lemma lem5166400 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term356 a s) (h4 : term338 x x' a s b) : False.
Proof. exact (EQ_MP (@lem5166399 x x' a s b h1 h2 h3 h4) (@lem5165779 a s h3)). Qed.
Lemma lem5166401 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term360 s b) (h3 : term338 x x' a s b) : (term360 s b) = False.
Proof. exact (prop_ext (fun h4 : term360 s b => @lem5166398 x x' a s b h1 h2 h3) (fun h4 : False => @lem5165871 s b h2)). Qed.
Lemma lem5166402 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term360 s b) (h3 : term338 x x' a s b) : False.
Proof. exact (EQ_MP (@lem5166401 x x' a s b h1 h2 h3) (@lem5165871 s b h2)). Qed.
Lemma lem5166403 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term356 a s) (h4 : term338 x x' a s b) : (term356 a s) = False.
Proof. exact (prop_ext (fun h5 : term356 a s => @lem5166400 x x' a s b h1 h2 h3 h4) (fun h5 : False => @lem5165779 a s h3)). Qed.
Lemma lem5166404 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term356 a s) (h4 : term338 x x' a s b) : False.
Proof. exact (EQ_MP (@lem5166403 x x' a s b h1 h2 h3 h4) (@lem5165779 a s h3)). Qed.
Lemma lem5166405 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term338 x x' a s b) : False.
Proof. exact (or_elim (@lem5165682 x x' a s b h3) (fun h0 : term356 a s => @lem5166404 x x' a s b h1 h2 h0 h3) (fun h0 : term360 s b => @lem5166402 x x' a s b h2 h0 h3)). Qed.
Lemma lem5166406 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term338 x x' a s b) : (term338 x x' a s b) = False.
Proof. exact (prop_ext (fun h4 : term338 x x' a s b => @lem5166405 x x' a s b h1 h2 h3) (fun h4 : False => @lem5165679 x x' a s b h3)). Qed.
Lemma lem5166407 (x : real) (x' : real -> real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term338 x x' a s b) : False.
Proof. exact (EQ_MP (@lem5166406 x x' a s b h1 h2 h3) (@lem5165679 x x' a s b h3)). Qed.
Lemma lem5166408 (x : real) (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term341 x a s b) : False.
Proof. exact (ex_elim (@lem5165528 x a s b h3) (fun x' : real -> real => fun h0 : term340 x a s b x' => @lem5166407 x x' a s b h1 h2 h0)). Qed.
Lemma lem5166409 (a : real) (s : real -> Prop) (b : real) (h1 : term175) (h2 : term17 s a b) (h3 : term168 a s b) : False.
Proof. exact (ex_elim (@lem5165444 a s b h3) (fun x : real => fun h0 : term342 a s b x => @lem5166408 x a s b h1 h2 h0)). Qed.
Lemma lem5166410 (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term168 a s b) : term173.
Proof. exact (fun h0 : term175 => @lem5166409 a s b h0 h1 h2). Qed.
Lemma lem5166411 : term173 = term174.
Proof. exact (@lem69 term175). Qed.
Lemma lem5166412 (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term168 a s b) : term174.
Proof. exact (EQ_MP (@lem5166411) (@lem5166410 a s b h1 h2)). Qed.
Lemma lem5166413 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term178 a s b.
Proof. exact (fun h0 : term168 a s b => @lem5166412 a s b h1 h0). Qed.
Lemma lem5166414 (a : real) (s : real -> Prop) (b : real) : term179 a s b.
Proof. exact (fun h0 : term17 s a b => @lem5166413 s a b h0). Qed.
Lemma lem5166419 (s : real -> Prop) (b : real) : term183 s b.
Proof. exact (fun a : real => @lem5166414 a s b). Qed.
Lemma lem5166424 (b : real) : term187 b.
Proof. exact (fun s : real -> Prop => @lem5166419 s b). Qed.
Lemma lem5166429 : term191.
Proof. exact (fun b : real => @lem5166424 b). Qed.
Lemma lem5166430 : term190.
Proof. exact (EQ_MP (@lem5165001) (@lem5166429)). Qed.
Lemma lem5166431 (b : real) : term416 b.
Proof. exact (@lem5166430 b). Qed.
Lemma lem5166432 (b : real) : (term416 b) = (term186 b).
Proof. exact (eq_refl (term416 b)). Qed.
Lemma lem5166433 (b : real) : term186 b.
Proof. exact (EQ_MP (@lem5166432 b) (@lem5166431 b)). Qed.
Lemma lem5166434 (b : real) (s : real -> Prop) : term417 b s.
Proof. exact (@lem5166433 b s). Qed.
Lemma lem5166435 (s : real -> Prop) (b : real) : (term417 b s) = (term182 s b).
Proof. exact (eq_refl (term417 b s)). Qed.
Lemma lem5166436 (s : real -> Prop) (b : real) : term182 s b.
Proof. exact (EQ_MP (@lem5166435 s b) (@lem5166434 b s)). Qed.
Lemma lem5166437 (s : real -> Prop) (b : real) (a : real) : term418 s b a.
Proof. exact (@lem5166436 s b a). Qed.
Lemma lem5166438 (a : real) (s : real -> Prop) (b : real) : (term418 s b a) = (term169 a s b).
Proof. exact (eq_refl (term418 s b a)). Qed.
Lemma lem5166439 (a : real) (s : real -> Prop) (b : real) : term169 a s b.
Proof. exact (EQ_MP (@lem5166438 a s b) (@lem5166437 s b a)). Qed.
Lemma lem5166441 (a : real) (s : real -> Prop) (b : real) : term169 a s b.
Proof. exact (@lem5164709 a s b (@lem5166439 a s b)). Qed.
Lemma lem5166442 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term177 a s b.
Proof. exact (@lem5166441 a s b (@lem5163766 s a b h1)). Qed.
Lemma lem5166443 (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term168 a s b) : term173.
Proof. exact (@lem5166442 s a b h1 (@lem5164694 a s b h2)). Qed.
Lemma lem5166444 (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term168 a s b) : False.
Proof. exact (@lem5166443 a s b h1 h2 (@lem1339577)). Qed.
Lemma lem5166445 (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term168 a s b) : (term168 a s b) = False.
Proof. exact (prop_ext (fun h3 : term168 a s b => @lem5166444 a s b h1 h2) (fun h3 : False => @lem5164694 a s b h2)). Qed.
Lemma lem5166446 (a : real) (s : real -> Prop) (b : real) (h1 : term17 s a b) (h2 : term168 a s b) : False.
Proof. exact (EQ_MP (@lem5166445 a s b h1 h2) (@lem5164694 a s b h2)). Qed.
Lemma lem5166447 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term167 a s b.
Proof. exact (fun h0 : term168 a s b => @lem5166446 a s b h1 h0). Qed.
Lemma lem5166448 (s : real -> Prop) (a : real) (b : real) (h1 : term17 s a b) : term166 a s b.
Proof. exact (EQ_MP (@lem5164693 a s b) (@lem5166447 s a b h1)). Qed.
Lemma lem5166449 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term18 s) : term208 a s b.
Proof. exact (@lem5166448 s a b h1 (@lem5164689 s h2)). Qed.
Lemma lem5166450 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term18 s) : term419 a s b.
Proof. exact (conj (@lem5164685 a b s h1 h2) (@lem5166449 a b s h1 h2)). Qed.
Lemma lem5166451 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term18 s) : term420 a s b.
Proof. exact (@lem5163770 a s b (@lem5166450 a b s h1 h2)). Qed.
Lemma lem5166452 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term18 s) : term23 a s b.
Proof. exact (@lem5166451 a b s h1 h2 (@lem5163764 s)). Qed.
Lemma lem5166453 (s : real -> Prop) (a : real) (b : real) (h1 : term16 s a b) : term17 s a b.
Proof. exact (proj2 (@lem5163765 s a b h1)). Qed.
Lemma lem5166454 (s : real -> Prop) (a : real) (b : real) (h1 : term16 s a b) : term18 s.
Proof. exact (proj1 (@lem5163765 s a b h1)). Qed.
Lemma lem5166455 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term18 s) : (term17 s a b) = (term23 a s b).
Proof. exact (prop_ext (fun h3 : term17 s a b => @lem5166452 a b s h1 h2) (fun h3 : term23 a s b => @lem5163766 s a b h1)). Qed.
Lemma lem5166456 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term18 s) : term23 a s b.
Proof. exact (EQ_MP (@lem5166455 a b s h1 h2) (@lem5163766 s a b h1)). Qed.
Lemma lem5166457 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term18 s) : (term18 s) = (term23 a s b).
Proof. exact (prop_ext (fun h3 : term18 s => @lem5166456 a b s h1 h2) (fun h3 : term23 a s b => @lem5163767 s h2)). Qed.
Lemma lem5166458 (a : real) (b : real) (s : real -> Prop) (h1 : term17 s a b) (h2 : term18 s) : term23 a s b.
Proof. exact (EQ_MP (@lem5166457 a b s h1 h2) (@lem5163767 s h2)). Qed.
Lemma lem5166459 (s : real -> Prop) (a : real) (b : real) (h1 : term18 s) (h2 : term16 s a b) : (term17 s a b) = (term23 a s b).
Proof. exact (prop_ext (fun h3 : term17 s a b => @lem5166458 a b s h3 h1) (fun h3 : term23 a s b => @lem5166453 s a b h2)). Qed.
Lemma lem5166460 (s : real -> Prop) (a : real) (b : real) (h1 : term18 s) (h2 : term16 s a b) : term23 a s b.
Proof. exact (EQ_MP (@lem5166459 s a b h1 h2) (@lem5166453 s a b h2)). Qed.
Lemma lem5166461 (s : real -> Prop) (a : real) (b : real) (h1 : term16 s a b) : (term18 s) = (term23 a s b).
Proof. exact (prop_ext (fun h2 : term18 s => @lem5166460 s a b h2 h1) (fun h2 : term23 a s b => @lem5166454 s a b h1)). Qed.
Lemma lem5166462 (s : real -> Prop) (a : real) (b : real) (h1 : term16 s a b) : term23 a s b.
Proof. exact (EQ_MP (@lem5166461 s a b h1) (@lem5166454 s a b h1)). Qed.
Lemma lem5166463 (a : real) (s : real -> Prop) (b : real) : term421 a s b.
Proof. exact (fun h0 : term16 s a b => @lem5166462 s a b h0). Qed.
Lemma lem5166468 (a : real) (s : real -> Prop) : term422 a s.
Proof. exact (fun b : real => @lem5166463 a s b). Qed.
Lemma lem5166473 (s : real -> Prop) : term423 s.
Proof. exact (fun a : real => @lem5166468 a s). Qed.
Lemma lem5166478 : term424.
Proof. exact (fun s : real -> Prop => @lem5166473 s). Qed.
