Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_INF_FINITE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import INF_FINITE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339577_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18958_spec.
Require Import thm18959_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19490_spec.
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
Require Import thm69_spec.
Lemma lem5222546 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5222547 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5222548 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5222547 t1) (@lem5222546 t1)). Qed.
Lemma lem5222549 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5222548 t1 t2). Qed.
Lemma lem5222550 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5222551 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5222550 t1 t2) (@lem5222549 t1 t2)). Qed.
Lemma lem5222552 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5222551 t1 t2 t3). Qed.
Lemma lem5222553 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5222554 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5222553 t1 t2 t3) (@lem5222552 t1 t2 t3)). Qed.
Lemma lem5222555 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5222554 t1 t2 t3)). Qed.
Lemma lem5222557 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5222558 : term8 = term9.
Proof. exact (@lem5222557 term8). Qed.
Lemma lem5222559 : term9 = term8.
Proof. exact (SYM (@lem5222558)). Qed.
Lemma lem5222560 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5222563 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5222564 : term12.
Proof. exact (fun h0 : term11 => @lem5222563 h0). Qed.
Lemma lem5222565 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5222566 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5222567 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem5222565 h2 (@lem5222566 h1)). Qed.
Lemma lem5222568 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem5222567 h1 h0). Qed.
Lemma lem5222569 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5222570 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem5222568 h1 (@lem5222569 h2)). Qed.
Lemma lem5222571 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem5222570 h0 h1). Qed.
Lemma lem5222572 : term14.
Proof. exact (fun h0 : term12 => @lem5222571 h0). Qed.
Lemma lem5222575 : term12.
Proof. exact (@lem5222572 (@lem5222564)). Qed.
Lemma lem5222615 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5222616 : term15 = term16.
Proof. exact (@lem5222615 term17). Qed.
Lemma lem5222633 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem5222634 : term19 = term20.
Proof. exact (MK_COMB (@lem5222633) (@lem5222616)). Qed.
Lemma lem5222637 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem5222644 : term11 = term22.
Proof. exact (MK_COMB (@lem5222637) (@lem5222634)). Qed.
Lemma lem5222649 (s : real -> Prop) (x : real) : (term23 s x) = (term23 s x).
Proof. exact (eq_refl (term23 s x)). Qed.
Lemma lem5222650 (s : real -> Prop) : (term24 s) = (term24 s).
Proof. exact (fun_ext (fun x : real => @lem5222649 s x)). Qed.
Lemma lem5222651 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5222652 (s : real -> Prop) : (term25 s) = (term25 s).
Proof. exact (MK_COMB (@lem5222651) (@lem5222650 s)). Qed.
Lemma lem5222655 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5222656 (s : real -> Prop) : (term27 s) = (term27 s).
Proof. exact (MK_COMB (@lem5222655 s) (@lem5222652 s)). Qed.
Lemma lem5222665 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5222666 (s : real -> Prop) : (term29 s) = (term29 s).
Proof. exact (MK_COMB (@lem5222665 s) (@lem5222656 s)). Qed.
Lemma lem5222667 : term30 = term30.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5222666 s)). Qed.
Lemma lem5222668 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5222669 : term17 = term17.
Proof. exact (MK_COMB (@lem5222668) (@lem5222667)). Qed.
Lemma lem5222670 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5222671 : term16 = term16.
Proof. exact (MK_COMB (@lem5222670) (@lem5222669)). Qed.
Lemma lem5222680 (y : real) (x : real) (z : real) : (term31 y x z) = (term31 y x z).
Proof. exact (eq_refl (term31 y x z)). Qed.
Lemma lem5222681 (y : real) (x : real) : (term32 y x) = (term32 y x).
Proof. exact (fun_ext (fun z : real => @lem5222680 y x z)). Qed.
Lemma lem5222682 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5222683 (y : real) (x : real) : (term33 y x) = (term33 y x).
Proof. exact (MK_COMB (@lem5222682) (@lem5222681 y x)). Qed.
Lemma lem5222684 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem5222683 y x)). Qed.
Lemma lem5222685 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5222686 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem5222685) (@lem5222684 x)). Qed.
Lemma lem5222687 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem5222686 x)). Qed.
Lemma lem5222688 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5222689 : term37 = term37.
Proof. exact (MK_COMB (@lem5222688) (@lem5222687)). Qed.
Lemma lem5222690 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5222691 : term18 = term18.
Proof. exact (MK_COMB (@lem5222690) (@lem5222689)). Qed.
Lemma lem5222692 : term20 = term20.
Proof. exact (MK_COMB (@lem5222691) (@lem5222671)). Qed.
Lemma lem5222697 (s : real -> Prop) (a : real) (x : real) : (term38 s a x) = (term38 s a x).
Proof. exact (eq_refl (term38 s a x)). Qed.
Lemma lem5222698 (s : real -> Prop) (a : real) : (term39 s a) = (term39 s a).
Proof. exact (fun_ext (fun x : real => @lem5222697 s a x)). Qed.
Lemma lem5222699 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5222700 (s : real -> Prop) (a : real) : (term40 s a) = (term40 s a).
Proof. exact (MK_COMB (@lem5222699) (@lem5222698 s a)). Qed.
Lemma lem5222703 (a : real) (s : real -> Prop) : (term41 a s) = (term41 a s).
Proof. exact (eq_refl (term41 a s)). Qed.
Lemma lem5222704 (s : real -> Prop) (a : real) : ((term42 a s) = (term40 s a)) = ((term42 a s) = (term40 s a)).
Proof. exact (MK_COMB (@lem5222703 a s) (@lem5222700 s a)). Qed.
Lemma lem5222713 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5222714 (s : real -> Prop) (a : real) : (term43 s a) = (term43 s a).
Proof. exact (MK_COMB (@lem5222713 s) (@lem5222704 s a)). Qed.
Lemma lem5222715 (s : real -> Prop) : (term44 s) = (term44 s).
Proof. exact (fun_ext (fun a : real => @lem5222714 s a)). Qed.
Lemma lem5222716 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5222717 (s : real -> Prop) : (term45 s) = (term45 s).
Proof. exact (MK_COMB (@lem5222716) (@lem5222715 s)). Qed.
Lemma lem5222718 : term46 = term46.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5222717 s)). Qed.
Lemma lem5222719 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5222720 : term8 = term8.
Proof. exact (MK_COMB (@lem5222719) (@lem5222718)). Qed.
Lemma lem5222721 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5222722 : term10 = term10.
Proof. exact (MK_COMB (@lem5222721) (@lem5222720)). Qed.
Lemma lem5222723 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5222724 : term21 = term21.
Proof. exact (MK_COMB (@lem5222723) (@lem5222722)). Qed.
Lemma lem5222725 : term22 = term22.
Proof. exact (MK_COMB (@lem5222724) (@lem5222692)). Qed.
Lemma lem5222798 : term11 = term22.
Proof. exact (TRANS (@lem5222644) (@lem5222725)). Qed.
Lemma lem5222799 : term22 = term11.
Proof. exact (SYM (@lem5222798)). Qed.
Lemma lem5222800 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5222801 (h1 : term37) : term37.
Proof. exact (h1). Qed.
Lemma lem5222802 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem5222818 (s : real -> Prop) (a : real) (x : real) : (term47 s a x) = (term48 s a x).
Proof. exact (@lem17362 (@IN real x s) (real_le a x)). Qed.
Lemma lem5222823 (s : real -> Prop) (a : real) (x : real) : (term38 s a x) = (term49 s a x).
Proof. exact (@lem17265 (@IN real x s) (real_le a x)). Qed.
Lemma lem5222824 (P : real -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5222825 (s : real -> Prop) (a : real) : (term52 s a) = (term53 s a).
Proof. exact (@lem5222824 (term39 s a)). Qed.
Lemma lem5222826 (s : real -> Prop) (a : real) (x : real) : (term54 s a x) = (term38 s a x).
Proof. exact (eq_refl (term54 s a x)). Qed.
Lemma lem5222827 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5222828 (s : real -> Prop) (a : real) (x : real) : (term55 s a x) = (term47 s a x).
Proof. exact (MK_COMB (@lem5222827) (@lem5222826 s a x)). Qed.
Lemma lem5222829 (s : real -> Prop) (a : real) (x : real) : (term55 s a x) = (term48 s a x).
Proof. exact (TRANS (@lem5222828 s a x) (@lem5222818 s a x)). Qed.
Lemma lem5222830 (s : real -> Prop) (a : real) : (term56 s a) = (term57 s a).
Proof. exact (fun_ext (fun x : real => @lem5222829 s a x)). Qed.
Lemma lem5222831 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5222832 (s : real -> Prop) (a : real) : (term53 s a) = (term58 s a).
Proof. exact (MK_COMB (@lem5222831) (@lem5222830 s a)). Qed.
Lemma lem5222833 (s : real -> Prop) (a : real) : (term52 s a) = (term58 s a).
Proof. exact (TRANS (@lem5222825 s a) (@lem5222832 s a)). Qed.
Lemma lem5222834 (s : real -> Prop) (a : real) : (term39 s a) = (term59 s a).
Proof. exact (fun_ext (fun x : real => @lem5222823 s a x)). Qed.
Lemma lem5222835 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5222836 (s : real -> Prop) (a : real) : (term40 s a) = (term60 s a).
Proof. exact (MK_COMB (@lem5222835) (@lem5222834 s a)). Qed.
Lemma lem5222838 (a : real) (s : real -> Prop) : (term61 a s) = (term61 a s).
Proof. exact (eq_refl (term61 a s)). Qed.
Lemma lem5222839 (s : real -> Prop) (a : real) : (term62 s a) = (term63 s a).
Proof. exact (MK_COMB (@lem5222838 a s) (@lem5222836 s a)). Qed.
Lemma lem5222841 (a : real) (s : real -> Prop) : (term64 a s) = (term64 a s).
Proof. exact (eq_refl (term64 a s)). Qed.
Lemma lem5222842 (s : real -> Prop) (a : real) : (term65 s a) = (term66 s a).
Proof. exact (MK_COMB (@lem5222841 a s) (@lem5222833 s a)). Qed.
Lemma lem5222843 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5222844 (s : real -> Prop) (a : real) : (term67 s a) = (term68 s a).
Proof. exact (MK_COMB (@lem5222843) (@lem5222842 s a)). Qed.
Lemma lem5222845 (s : real -> Prop) (a : real) : (term69 s a) = (term70 s a).
Proof. exact (MK_COMB (@lem5222844 s a) (@lem5222839 s a)). Qed.
Lemma lem5222846 (s : real -> Prop) (a : real) : (term71 s a) = (term69 s a).
Proof. exact (@lem17646 (term42 a s) (term40 s a)). Qed.
Lemma lem5222847 (s : real -> Prop) (a : real) : (term71 s a) = (term70 s a).
Proof. exact (TRANS (@lem5222846 s a) (@lem5222845 s a)). Qed.
Lemma lem5222849 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5222850 (s : real -> Prop) (a : real) : (term73 s a) = (term74 s a).
Proof. exact (MK_COMB (@lem5222849 s) (@lem5222847 s a)). Qed.
Lemma lem5222851 (s : real -> Prop) (a : real) : (term75 s a) = (term73 s a).
Proof. exact (@lem17362 (term76 s) ((term42 a s) = (term40 s a))). Qed.
Lemma lem5222852 (s : real -> Prop) (a : real) : (term75 s a) = (term74 s a).
Proof. exact (TRANS (@lem5222851 s a) (@lem5222850 s a)). Qed.
Lemma lem5222853 (P : real -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5222854 (s : real -> Prop) : (term77 s) = (term78 s).
Proof. exact (@lem5222853 (term44 s)). Qed.
Lemma lem5222855 (s : real -> Prop) (a : real) : (term79 s a) = (term43 s a).
Proof. exact (eq_refl (term79 s a)). Qed.
Lemma lem5222856 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5222857 (s : real -> Prop) (a : real) : (term80 s a) = (term75 s a).
Proof. exact (MK_COMB (@lem5222856) (@lem5222855 s a)). Qed.
Lemma lem5222858 (s : real -> Prop) (a : real) : (term80 s a) = (term74 s a).
Proof. exact (TRANS (@lem5222857 s a) (@lem5222852 s a)). Qed.
Lemma lem5222859 (s : real -> Prop) : (term81 s) = (term82 s).
Proof. exact (fun_ext (fun a : real => @lem5222858 s a)). Qed.
Lemma lem5222860 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5222861 (s : real -> Prop) : (term78 s) = (term83 s).
Proof. exact (MK_COMB (@lem5222860) (@lem5222859 s)). Qed.
Lemma lem5222862 (s : real -> Prop) : (term77 s) = (term83 s).
Proof. exact (TRANS (@lem5222854 s) (@lem5222861 s)). Qed.
Lemma lem5222863 (P : type1022) : (term84 P) = (term85 P).
Proof. exact (@lem18392 (real -> Prop) P). Qed.
Lemma lem5222864 : term10 = term86.
Proof. exact (@lem5222863 term46). Qed.
Lemma lem5222865 (s : real -> Prop) : (term87 s) = (term45 s).
Proof. exact (eq_refl (term87 s)). Qed.
Lemma lem5222866 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5222867 (s : real -> Prop) : (term88 s) = (term77 s).
Proof. exact (MK_COMB (@lem5222866) (@lem5222865 s)). Qed.
Lemma lem5222868 (s : real -> Prop) : (term88 s) = (term83 s).
Proof. exact (TRANS (@lem5222867 s) (@lem5222862 s)). Qed.
Lemma lem5222869 : term89 = term90.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5222868 s)). Qed.
Lemma lem5222870 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5222871 : term86 = term91.
Proof. exact (MK_COMB (@lem5222870) (@lem5222869)). Qed.
Lemma lem5222872 : term10 = term91.
Proof. exact (TRANS (@lem5222864) (@lem5222871)). Qed.
Lemma lem5222878 {A : Type'} (P : Prop) (Q : A -> Prop) : (term92 A P Q) = (term93 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem5222879 (P : Prop) (Q : real -> Prop) : (term94 P Q) = (term95 P Q).
Proof. exact (@lem5222878 real P Q). Qed.
Lemma lem5222880 (s : real -> Prop) : (term96 s) = (term97 s).
Proof. exact (@lem5222879 (term76 s) (term98 s)). Qed.
Lemma lem5222881 (s : real -> Prop) (a : real) : (term99 s a) = (term70 s a).
Proof. exact (eq_refl (term99 s a)). Qed.
Lemma lem5222882 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5222883 (s : real -> Prop) (a : real) : (term100 s a) = (term74 s a).
Proof. exact (MK_COMB (@lem5222882 s) (@lem5222881 s a)). Qed.
Lemma lem5222884 (s : real -> Prop) : (term101 s) = (term82 s).
Proof. exact (fun_ext (fun a : real => @lem5222883 s a)). Qed.
Lemma lem5222885 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5222886 (s : real -> Prop) : (term96 s) = (term83 s).
Proof. exact (MK_COMB (@lem5222885) (@lem5222884 s)). Qed.
Lemma lem5222887 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5222888 (s : real -> Prop) : (term102 s) = (term103 s).
Proof. exact (MK_COMB (@lem5222887) (@lem5222886 s)). Qed.
Lemma lem5222889 (s : real -> Prop) (a : real) : (term99 s a) = (term70 s a).
Proof. exact (eq_refl (term99 s a)). Qed.
Lemma lem5222890 (s : real -> Prop) : (term104 s) = (term98 s).
Proof. exact (fun_ext (fun a : real => @lem5222889 s a)). Qed.
Lemma lem5222891 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5222892 (s : real -> Prop) : (term105 s) = (term106 s).
Proof. exact (MK_COMB (@lem5222891) (@lem5222890 s)). Qed.
Lemma lem5222893 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5222894 (s : real -> Prop) : (term97 s) = (term107 s).
Proof. exact (MK_COMB (@lem5222893 s) (@lem5222892 s)). Qed.
Lemma lem5222895 (s : real -> Prop) : ((term96 s) = (term97 s)) = ((term83 s) = (term107 s)).
Proof. exact (MK_COMB (@lem5222888 s) (@lem5222894 s)). Qed.
Lemma lem5222896 (s : real -> Prop) : (term83 s) = (term107 s).
Proof. exact (EQ_MP (@lem5222895 s) (@lem5222880 s)). Qed.
Lemma lem5222898 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5222899 (P : real -> Prop) (Q : real -> Prop) : (term110 P Q) = (term111 P Q).
Proof. exact (@lem5222898 real P Q). Qed.
Lemma lem5222900 (s : real -> Prop) : (term112 s) = (term113 s).
Proof. exact (@lem5222899 (term114 s) (term115 s)). Qed.
Lemma lem5222901 (s : real -> Prop) (a : real) : (term116 s a) = (term66 s a).
Proof. exact (eq_refl (term116 s a)). Qed.
Lemma lem5222902 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5222903 (s : real -> Prop) (a : real) : (term117 s a) = (term68 s a).
Proof. exact (MK_COMB (@lem5222902) (@lem5222901 s a)). Qed.
Lemma lem5222904 (s : real -> Prop) (a : real) : (term118 s a) = (term63 s a).
Proof. exact (eq_refl (term118 s a)). Qed.
Lemma lem5222905 (s : real -> Prop) (a : real) : (term119 s a) = (term70 s a).
Proof. exact (MK_COMB (@lem5222903 s a) (@lem5222904 s a)). Qed.
Lemma lem5222906 (s : real -> Prop) : (term120 s) = (term98 s).
Proof. exact (fun_ext (fun a : real => @lem5222905 s a)). Qed.
Lemma lem5222907 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5222908 (s : real -> Prop) : (term112 s) = (term106 s).
Proof. exact (MK_COMB (@lem5222907) (@lem5222906 s)). Qed.
Lemma lem5222909 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5222910 (s : real -> Prop) : (term121 s) = (term122 s).
Proof. exact (MK_COMB (@lem5222909) (@lem5222908 s)). Qed.
Lemma lem5222911 (s : real -> Prop) (a : real) : (term116 s a) = (term66 s a).
Proof. exact (eq_refl (term116 s a)). Qed.
Lemma lem5222912 (s : real -> Prop) : (term123 s) = (term114 s).
Proof. exact (fun_ext (fun a : real => @lem5222911 s a)). Qed.
Lemma lem5222913 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5222914 (s : real -> Prop) : (term124 s) = (term125 s).
Proof. exact (MK_COMB (@lem5222913) (@lem5222912 s)). Qed.
Lemma lem5222915 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5222916 (s : real -> Prop) : (term126 s) = (term127 s).
Proof. exact (MK_COMB (@lem5222915) (@lem5222914 s)). Qed.
Lemma lem5222917 (s : real -> Prop) (a : real) : (term118 s a) = (term63 s a).
Proof. exact (eq_refl (term118 s a)). Qed.
Lemma lem5222918 (s : real -> Prop) : (term128 s) = (term115 s).
Proof. exact (fun_ext (fun a : real => @lem5222917 s a)). Qed.
Lemma lem5222919 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5222920 (s : real -> Prop) : (term129 s) = (term130 s).
Proof. exact (MK_COMB (@lem5222919) (@lem5222918 s)). Qed.
Lemma lem5222921 (s : real -> Prop) : (term113 s) = (term131 s).
Proof. exact (MK_COMB (@lem5222916 s) (@lem5222920 s)). Qed.
Lemma lem5222922 (s : real -> Prop) : ((term112 s) = (term113 s)) = ((term106 s) = (term131 s)).
Proof. exact (MK_COMB (@lem5222910 s) (@lem5222921 s)). Qed.
Lemma lem5222923 (s : real -> Prop) : (term106 s) = (term131 s).
Proof. exact (EQ_MP (@lem5222922 s) (@lem5222900 s)). Qed.
Lemma lem5223116 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5223117 (s : real -> Prop) : (term107 s) = (term132 s).
Proof. exact (MK_COMB (@lem5223116 s) (@lem5222923 s)). Qed.
Lemma lem5223118 (s : real -> Prop) : (term83 s) = (term132 s).
Proof. exact (TRANS (@lem5222896 s) (@lem5223117 s)). Qed.
Lemma lem5223119 : term90 = term133.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5223118 s)). Qed.
Lemma lem5223120 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5223121 : term91 = term134.
Proof. exact (MK_COMB (@lem5223120) (@lem5223119)). Qed.
Lemma lem5223171 {A : Type'} (P : Prop) (Q : A -> Prop) : (term93 A P Q) = (term92 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5223172 (P : Prop) (Q : real -> Prop) : (term95 P Q) = (term94 P Q).
Proof. exact (@lem5223171 real P Q). Qed.
Lemma lem5223173 (s : real -> Prop) (a : real) : (term135 s a) = (term136 s a).
Proof. exact (@lem5223172 (term42 a s) (term57 s a)). Qed.
Lemma lem5223174 (s : real -> Prop) (a : real) (x : real) : (term137 s a x) = (term48 s a x).
Proof. exact (eq_refl (term137 s a x)). Qed.
Lemma lem5223175 (s : real -> Prop) (a : real) : (term138 s a) = (term57 s a).
Proof. exact (fun_ext (fun x : real => @lem5223174 s a x)). Qed.
Lemma lem5223176 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5223177 (s : real -> Prop) (a : real) : (term139 s a) = (term58 s a).
Proof. exact (MK_COMB (@lem5223176) (@lem5223175 s a)). Qed.
Lemma lem5223178 (a : real) (s : real -> Prop) : (term64 a s) = (term64 a s).
Proof. exact (eq_refl (term64 a s)). Qed.
Lemma lem5223179 (s : real -> Prop) (a : real) : (term135 s a) = (term66 s a).
Proof. exact (MK_COMB (@lem5223178 a s) (@lem5223177 s a)). Qed.
Lemma lem5223180 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5223181 (s : real -> Prop) (a : real) : (term140 s a) = (term141 s a).
Proof. exact (MK_COMB (@lem5223180) (@lem5223179 s a)). Qed.
Lemma lem5223182 (s : real -> Prop) (a : real) (x : real) : (term137 s a x) = (term48 s a x).
Proof. exact (eq_refl (term137 s a x)). Qed.
Lemma lem5223183 (a : real) (s : real -> Prop) : (term64 a s) = (term64 a s).
Proof. exact (eq_refl (term64 a s)). Qed.
Lemma lem5223184 (s : real -> Prop) (a : real) (x : real) : (term142 s a x) = (term143 s a x).
Proof. exact (MK_COMB (@lem5223183 a s) (@lem5223182 s a x)). Qed.
Lemma lem5223185 (s : real -> Prop) (a : real) : (term144 s a) = (term145 s a).
Proof. exact (fun_ext (fun x : real => @lem5223184 s a x)). Qed.
Lemma lem5223186 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5223187 (s : real -> Prop) (a : real) : (term136 s a) = (term146 s a).
Proof. exact (MK_COMB (@lem5223186) (@lem5223185 s a)). Qed.
Lemma lem5223188 (s : real -> Prop) (a : real) : ((term135 s a) = (term136 s a)) = ((term66 s a) = (term146 s a)).
Proof. exact (MK_COMB (@lem5223181 s a) (@lem5223187 s a)). Qed.
Lemma lem5223189 (s : real -> Prop) (a : real) : (term66 s a) = (term146 s a).
Proof. exact (EQ_MP (@lem5223188 s a) (@lem5223173 s a)). Qed.
Lemma lem5223190 (s : real -> Prop) : (term114 s) = (term147 s).
Proof. exact (fun_ext (fun a : real => @lem5223189 s a)). Qed.
Lemma lem5223191 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5223192 (s : real -> Prop) : (term125 s) = (term148 s).
Proof. exact (MK_COMB (@lem5223191) (@lem5223190 s)). Qed.
Lemma lem5223193 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5223194 (s : real -> Prop) : (term127 s) = (term149 s).
Proof. exact (MK_COMB (@lem5223193) (@lem5223192 s)). Qed.
Lemma lem5223195 (s : real -> Prop) : (term130 s) = (term130 s).
Proof. exact (eq_refl (term130 s)). Qed.
Lemma lem5223196 (s : real -> Prop) : (term131 s) = (term150 s).
Proof. exact (MK_COMB (@lem5223194 s) (@lem5223195 s)). Qed.
Lemma lem5223198 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term109 A P Q) = (term108 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5223199 (P : real -> Prop) (Q : real -> Prop) : (term111 P Q) = (term110 P Q).
Proof. exact (@lem5223198 real P Q). Qed.
Lemma lem5223200 (s : real -> Prop) : (term151 s) = (term152 s).
Proof. exact (@lem5223199 (term147 s) (term115 s)). Qed.
Lemma lem5223201 (s : real -> Prop) (a : real) : (term153 s a) = (term146 s a).
Proof. exact (eq_refl (term153 s a)). Qed.
Lemma lem5223202 (s : real -> Prop) : (term154 s) = (term147 s).
Proof. exact (fun_ext (fun a : real => @lem5223201 s a)). Qed.
Lemma lem5223203 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5223204 (s : real -> Prop) : (term155 s) = (term148 s).
Proof. exact (MK_COMB (@lem5223203) (@lem5223202 s)). Qed.
Lemma lem5223205 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5223206 (s : real -> Prop) : (term156 s) = (term149 s).
Proof. exact (MK_COMB (@lem5223205) (@lem5223204 s)). Qed.
Lemma lem5223207 (s : real -> Prop) (a : real) : (term118 s a) = (term63 s a).
Proof. exact (eq_refl (term118 s a)). Qed.
Lemma lem5223208 (s : real -> Prop) : (term128 s) = (term115 s).
Proof. exact (fun_ext (fun a : real => @lem5223207 s a)). Qed.
Lemma lem5223209 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5223210 (s : real -> Prop) : (term129 s) = (term130 s).
Proof. exact (MK_COMB (@lem5223209) (@lem5223208 s)). Qed.
Lemma lem5223211 (s : real -> Prop) : (term151 s) = (term150 s).
Proof. exact (MK_COMB (@lem5223206 s) (@lem5223210 s)). Qed.
Lemma lem5223212 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5223213 (s : real -> Prop) : (term157 s) = (term158 s).
Proof. exact (MK_COMB (@lem5223212) (@lem5223211 s)). Qed.
Lemma lem5223214 (s : real -> Prop) (a : real) : (term153 s a) = (term146 s a).
Proof. exact (eq_refl (term153 s a)). Qed.
Lemma lem5223215 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5223216 (s : real -> Prop) (a : real) : (term159 s a) = (term160 s a).
Proof. exact (MK_COMB (@lem5223215) (@lem5223214 s a)). Qed.
Lemma lem5223217 (s : real -> Prop) (a : real) : (term118 s a) = (term63 s a).
Proof. exact (eq_refl (term118 s a)). Qed.
Lemma lem5223218 (s : real -> Prop) (a : real) : (term161 s a) = (term162 s a).
Proof. exact (MK_COMB (@lem5223216 s a) (@lem5223217 s a)). Qed.
Lemma lem5223219 (s : real -> Prop) : (term163 s) = (term164 s).
Proof. exact (fun_ext (fun a : real => @lem5223218 s a)). Qed.
Lemma lem5223220 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5223221 (s : real -> Prop) : (term152 s) = (term165 s).
Proof. exact (MK_COMB (@lem5223220) (@lem5223219 s)). Qed.
Lemma lem5223222 (s : real -> Prop) : ((term151 s) = (term152 s)) = ((term150 s) = (term165 s)).
Proof. exact (MK_COMB (@lem5223213 s) (@lem5223221 s)). Qed.
Lemma lem5223223 (s : real -> Prop) : (term150 s) = (term165 s).
Proof. exact (EQ_MP (@lem5223222 s) (@lem5223200 s)). Qed.
Lemma lem5223225 {A : Type'} (P : A -> Prop) (Q : Prop) : (term166 A P Q) = (term167 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5223226 (P : real -> Prop) (Q : Prop) : (term168 P Q) = (term169 P Q).
Proof. exact (@lem5223225 real P Q). Qed.
Lemma lem5223227 (s : real -> Prop) (a : real) : (term170 s a) = (term171 s a).
Proof. exact (@lem5223226 (term145 s a) (term63 s a)). Qed.
Lemma lem5223228 (s : real -> Prop) (a : real) (x : real) : (term172 s a x) = (term143 s a x).
Proof. exact (eq_refl (term172 s a x)). Qed.
Lemma lem5223229 (s : real -> Prop) (a : real) : (term173 s a) = (term145 s a).
Proof. exact (fun_ext (fun x : real => @lem5223228 s a x)). Qed.
Lemma lem5223230 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5223231 (s : real -> Prop) (a : real) : (term174 s a) = (term146 s a).
Proof. exact (MK_COMB (@lem5223230) (@lem5223229 s a)). Qed.
Lemma lem5223232 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5223233 (s : real -> Prop) (a : real) : (term175 s a) = (term160 s a).
Proof. exact (MK_COMB (@lem5223232) (@lem5223231 s a)). Qed.
Lemma lem5223234 (s : real -> Prop) (a : real) : (term63 s a) = (term63 s a).
Proof. exact (eq_refl (term63 s a)). Qed.
Lemma lem5223235 (s : real -> Prop) (a : real) : (term170 s a) = (term162 s a).
Proof. exact (MK_COMB (@lem5223233 s a) (@lem5223234 s a)). Qed.
Lemma lem5223236 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5223237 (s : real -> Prop) (a : real) : (term176 s a) = (term177 s a).
Proof. exact (MK_COMB (@lem5223236) (@lem5223235 s a)). Qed.
Lemma lem5223238 (s : real -> Prop) (a : real) (x : real) : (term172 s a x) = (term143 s a x).
Proof. exact (eq_refl (term172 s a x)). Qed.
Lemma lem5223239 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5223240 (s : real -> Prop) (a : real) (x : real) : (term178 s a x) = (term179 s a x).
Proof. exact (MK_COMB (@lem5223239) (@lem5223238 s a x)). Qed.
Lemma lem5223241 (s : real -> Prop) (a : real) : (term63 s a) = (term63 s a).
Proof. exact (eq_refl (term63 s a)). Qed.
Lemma lem5223242 (x : real) (s : real -> Prop) (a : real) : (term180 x s a) = (term181 x s a).
Proof. exact (MK_COMB (@lem5223240 s a x) (@lem5223241 s a)). Qed.
Lemma lem5223243 (s : real -> Prop) (a : real) : (term182 s a) = (term183 s a).
Proof. exact (fun_ext (fun x : real => @lem5223242 x s a)). Qed.
Lemma lem5223244 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5223245 (s : real -> Prop) (a : real) : (term171 s a) = (term184 s a).
Proof. exact (MK_COMB (@lem5223244) (@lem5223243 s a)). Qed.
Lemma lem5223246 (s : real -> Prop) (a : real) : ((term170 s a) = (term171 s a)) = ((term162 s a) = (term184 s a)).
Proof. exact (MK_COMB (@lem5223237 s a) (@lem5223245 s a)). Qed.
Lemma lem5223247 (s : real -> Prop) (a : real) : (term162 s a) = (term184 s a).
Proof. exact (EQ_MP (@lem5223246 s a) (@lem5223227 s a)). Qed.
Lemma lem5223248 (s : real -> Prop) : (term164 s) = (term185 s).
Proof. exact (fun_ext (fun a : real => @lem5223247 s a)). Qed.
Lemma lem5223249 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5223250 (s : real -> Prop) : (term165 s) = (term186 s).
Proof. exact (MK_COMB (@lem5223249) (@lem5223248 s)). Qed.
Lemma lem5223251 (s : real -> Prop) : (term150 s) = (term186 s).
Proof. exact (TRANS (@lem5223223 s) (@lem5223250 s)). Qed.
Lemma lem5223252 (s : real -> Prop) : (term131 s) = (term186 s).
Proof. exact (TRANS (@lem5223196 s) (@lem5223251 s)). Qed.
Lemma lem5223253 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5223254 (s : real -> Prop) : (term132 s) = (term187 s).
Proof. exact (MK_COMB (@lem5223253 s) (@lem5223252 s)). Qed.
Lemma lem5223256 {A : Type'} (P : Prop) (Q : A -> Prop) : (term93 A P Q) = (term92 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5223257 (P : Prop) (Q : real -> Prop) : (term95 P Q) = (term94 P Q).
Proof. exact (@lem5223256 real P Q). Qed.
Lemma lem5223258 (s : real -> Prop) : (term188 s) = (term189 s).
Proof. exact (@lem5223257 (term76 s) (term185 s)). Qed.
Lemma lem5223259 (s : real -> Prop) (a : real) : (term190 s a) = (term184 s a).
Proof. exact (eq_refl (term190 s a)). Qed.
Lemma lem5223260 (s : real -> Prop) : (term191 s) = (term185 s).
Proof. exact (fun_ext (fun a : real => @lem5223259 s a)). Qed.
Lemma lem5223261 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5223262 (s : real -> Prop) : (term192 s) = (term186 s).
Proof. exact (MK_COMB (@lem5223261) (@lem5223260 s)). Qed.
Lemma lem5223263 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5223264 (s : real -> Prop) : (term188 s) = (term187 s).
Proof. exact (MK_COMB (@lem5223263 s) (@lem5223262 s)). Qed.
Lemma lem5223265 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5223266 (s : real -> Prop) : (term193 s) = (term194 s).
Proof. exact (MK_COMB (@lem5223265) (@lem5223264 s)). Qed.
Lemma lem5223267 (s : real -> Prop) (a : real) : (term190 s a) = (term184 s a).
Proof. exact (eq_refl (term190 s a)). Qed.
Lemma lem5223268 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5223269 (s : real -> Prop) (a : real) : (term195 s a) = (term196 s a).
Proof. exact (MK_COMB (@lem5223268 s) (@lem5223267 s a)). Qed.
Lemma lem5223270 (s : real -> Prop) : (term197 s) = (term198 s).
Proof. exact (fun_ext (fun a : real => @lem5223269 s a)). Qed.
Lemma lem5223271 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5223272 (s : real -> Prop) : (term189 s) = (term199 s).
Proof. exact (MK_COMB (@lem5223271) (@lem5223270 s)). Qed.
Lemma lem5223273 (s : real -> Prop) : ((term188 s) = (term189 s)) = ((term187 s) = (term199 s)).
Proof. exact (MK_COMB (@lem5223266 s) (@lem5223272 s)). Qed.
Lemma lem5223274 (s : real -> Prop) : (term187 s) = (term199 s).
Proof. exact (EQ_MP (@lem5223273 s) (@lem5223258 s)). Qed.
Lemma lem5223276 {A : Type'} (P : Prop) (Q : A -> Prop) : (term93 A P Q) = (term92 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5223277 (P : Prop) (Q : real -> Prop) : (term95 P Q) = (term94 P Q).
Proof. exact (@lem5223276 real P Q). Qed.
Lemma lem5223278 (s : real -> Prop) (a : real) : (term200 s a) = (term201 s a).
Proof. exact (@lem5223277 (term76 s) (term183 s a)). Qed.
Lemma lem5223279 (x : real) (s : real -> Prop) (a : real) : (term202 s a x) = (term181 x s a).
Proof. exact (eq_refl (term202 s a x)). Qed.
Lemma lem5223280 (s : real -> Prop) (a : real) : (term203 s a) = (term183 s a).
Proof. exact (fun_ext (fun x : real => @lem5223279 x s a)). Qed.
Lemma lem5223281 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5223282 (s : real -> Prop) (a : real) : (term204 s a) = (term184 s a).
Proof. exact (MK_COMB (@lem5223281) (@lem5223280 s a)). Qed.
Lemma lem5223283 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5223284 (s : real -> Prop) (a : real) : (term200 s a) = (term196 s a).
Proof. exact (MK_COMB (@lem5223283 s) (@lem5223282 s a)). Qed.
Lemma lem5223285 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5223286 (s : real -> Prop) (a : real) : (term205 s a) = (term206 s a).
Proof. exact (MK_COMB (@lem5223285) (@lem5223284 s a)). Qed.
Lemma lem5223287 (x : real) (s : real -> Prop) (a : real) : (term202 s a x) = (term181 x s a).
Proof. exact (eq_refl (term202 s a x)). Qed.
Lemma lem5223288 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5223289 (x : real) (s : real -> Prop) (a : real) : (term207 s a x) = (term208 x s a).
Proof. exact (MK_COMB (@lem5223288 s) (@lem5223287 x s a)). Qed.
Lemma lem5223290 (s : real -> Prop) (a : real) : (term209 s a) = (term210 s a).
Proof. exact (fun_ext (fun x : real => @lem5223289 x s a)). Qed.
Lemma lem5223291 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5223292 (s : real -> Prop) (a : real) : (term201 s a) = (term211 s a).
Proof. exact (MK_COMB (@lem5223291) (@lem5223290 s a)). Qed.
Lemma lem5223293 (s : real -> Prop) (a : real) : ((term200 s a) = (term201 s a)) = ((term196 s a) = (term211 s a)).
Proof. exact (MK_COMB (@lem5223286 s a) (@lem5223292 s a)). Qed.
Lemma lem5223294 (s : real -> Prop) (a : real) : (term196 s a) = (term211 s a).
Proof. exact (EQ_MP (@lem5223293 s a) (@lem5223278 s a)). Qed.
Lemma lem5223295 (s : real -> Prop) : (term198 s) = (term212 s).
Proof. exact (fun_ext (fun a : real => @lem5223294 s a)). Qed.
Lemma lem5223296 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5223297 (s : real -> Prop) : (term199 s) = (term213 s).
Proof. exact (MK_COMB (@lem5223296) (@lem5223295 s)). Qed.
Lemma lem5223298 (s : real -> Prop) : (term187 s) = (term213 s).
Proof. exact (TRANS (@lem5223274 s) (@lem5223297 s)). Qed.
Lemma lem5223299 (s : real -> Prop) : (term132 s) = (term213 s).
Proof. exact (TRANS (@lem5223254 s) (@lem5223298 s)). Qed.
Lemma lem5223300 : term133 = term214.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5223299 s)). Qed.
Lemma lem5223301 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5223302 : term134 = term215.
Proof. exact (MK_COMB (@lem5223301) (@lem5223300)). Qed.
Lemma lem5223303 : term91 = term215.
Proof. exact (TRANS (@lem5223121) (@lem5223302)). Qed.
Lemma lem5223304 : term10 = term215.
Proof. exact (TRANS (@lem5222872) (@lem5223303)). Qed.
Lemma lem5223305 (h1 : term10) : term215.
Proof. exact (EQ_MP (@lem5223304) (@lem5222800 h1)). Qed.
Lemma lem5223312 (x : real) (y : real) (z : real) : (term216 x y z) = (term217 x y z).
Proof. exact (@lem17045 (real_le x y) (real_le y z)). Qed.
Lemma lem5223313 (x : real) (z : real) : (real_le x z) = (real_le x z).
Proof. exact (eq_refl (real_le x z)). Qed.
Lemma lem5223314 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5223315 (x : real) (y : real) (z : real) : (term218 x y z) = (term219 x y z).
Proof. exact (MK_COMB (@lem5223314) (@lem5223312 x y z)). Qed.
Lemma lem5223316 (y : real) (x : real) (z : real) : (term220 y x z) = (term221 y x z).
Proof. exact (MK_COMB (@lem5223315 x y z) (@lem5223313 x z)). Qed.
Lemma lem5223317 (y : real) (x : real) (z : real) : (term31 y x z) = (term220 y x z).
Proof. exact (@lem17265 (term222 x y z) (real_le x z)). Qed.
Lemma lem5223318 (y : real) (x : real) (z : real) : (term31 y x z) = (term221 y x z).
Proof. exact (TRANS (@lem5223317 y x z) (@lem5223316 y x z)). Qed.
Lemma lem5223319 (y : real) (x : real) : (term32 y x) = (term223 y x).
Proof. exact (fun_ext (fun z : real => @lem5223318 y x z)). Qed.
Lemma lem5223320 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5223321 (y : real) (x : real) : (term33 y x) = (term224 y x).
Proof. exact (MK_COMB (@lem5223320) (@lem5223319 y x)). Qed.
Lemma lem5223322 (x : real) : (term34 x) = (term225 x).
Proof. exact (fun_ext (fun y : real => @lem5223321 y x)). Qed.
Lemma lem5223323 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5223324 (x : real) : (term35 x) = (term226 x).
Proof. exact (MK_COMB (@lem5223323) (@lem5223322 x)). Qed.
Lemma lem5223325 : term36 = term227.
Proof. exact (fun_ext (fun x : real => @lem5223324 x)). Qed.
Lemma lem5223326 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5223387 : term37 = term228.
Proof. exact (MK_COMB (@lem5223326) (@lem5223325)). Qed.
Lemma lem5223388 (h1 : term37) : term228.
Proof. exact (EQ_MP (@lem5223387) (@lem5222801 h1)). Qed.
Lemma lem5223392 (s : real -> Prop) : (term229 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5223394 (s : real -> Prop) : (term230 s) = (term230 s).
Proof. exact (eq_refl (term230 s)). Qed.
Lemma lem5223395 (s : real -> Prop) : (term231 s) = (term232 s).
Proof. exact (MK_COMB (@lem5223394 s) (@lem5223392 s)). Qed.
Lemma lem5223396 (s : real -> Prop) : (term233 s) = (term231 s).
Proof. exact (@lem17045 (@FINITE real s) (term234 s)). Qed.
Lemma lem5223397 (s : real -> Prop) : (term233 s) = (term232 s).
Proof. exact (TRANS (@lem5223396 s) (@lem5223395 s)). Qed.
Lemma lem5223405 (s : real -> Prop) (x : real) : (term23 s x) = (term235 s x).
Proof. exact (@lem17265 (@IN real x s) (term236 s x)). Qed.
Lemma lem5223406 (s : real -> Prop) : (term24 s) = (term237 s).
Proof. exact (fun_ext (fun x : real => @lem5223405 s x)). Qed.
Lemma lem5223407 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5223408 (s : real -> Prop) : (term25 s) = (term238 s).
Proof. exact (MK_COMB (@lem5223407) (@lem5223406 s)). Qed.
Lemma lem5223410 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5223411 (s : real -> Prop) : (term27 s) = (term239 s).
Proof. exact (MK_COMB (@lem5223410 s) (@lem5223408 s)). Qed.
Lemma lem5223412 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5223413 (s : real -> Prop) : (term240 s) = (term241 s).
Proof. exact (MK_COMB (@lem5223412) (@lem5223397 s)). Qed.
Lemma lem5223414 (s : real -> Prop) : (term242 s) = (term243 s).
Proof. exact (MK_COMB (@lem5223413 s) (@lem5223411 s)). Qed.
Lemma lem5223415 (s : real -> Prop) : (term29 s) = (term242 s).
Proof. exact (@lem17265 (term76 s) (term27 s)). Qed.
Lemma lem5223416 (s : real -> Prop) : (term29 s) = (term243 s).
Proof. exact (TRANS (@lem5223415 s) (@lem5223414 s)). Qed.
Lemma lem5223417 : term30 = term244.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5223416 s)). Qed.
Lemma lem5223418 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5223519 : term17 = term245.
Proof. exact (MK_COMB (@lem5223418) (@lem5223417)). Qed.
Lemma lem5223520 (h1 : term17) : term245.
Proof. exact (EQ_MP (@lem5223519) (@lem5222802 h1)). Qed.
Lemma lem5223521 (s : real -> Prop) (h1 : term213 s) : term213 s.
Proof. exact (h1). Qed.
Lemma lem5223522 (s : real -> Prop) (a : real) (h1 : term211 s a) : term211 s a.
Proof. exact (h1). Qed.
Lemma lem5223523 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term208 x s a.
Proof. exact (h1). Qed.
Lemma lem5223548 (y : real) (x : real) (z : real) : (term221 y x z) = (term221 y x z).
Proof. exact (eq_refl (term221 y x z)). Qed.
Lemma lem5223549 (y : real) (x : real) : (term223 y x) = (term223 y x).
Proof. exact (fun_ext (fun z : real => @lem5223548 y x z)). Qed.
Lemma lem5223550 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5223551 (y : real) (x : real) : (term224 y x) = (term224 y x).
Proof. exact (MK_COMB (@lem5223550) (@lem5223549 y x)). Qed.
Lemma lem5223552 (x : real) : (term225 x) = (term225 x).
Proof. exact (fun_ext (fun y : real => @lem5223551 y x)). Qed.
Lemma lem5223553 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5223554 (x : real) : (term226 x) = (term226 x).
Proof. exact (MK_COMB (@lem5223553) (@lem5223552 x)). Qed.
Lemma lem5223555 : term227 = term227.
Proof. exact (fun_ext (fun x : real => @lem5223554 x)). Qed.
Lemma lem5223556 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5223557 : term228 = term228.
Proof. exact (MK_COMB (@lem5223556) (@lem5223555)). Qed.
Lemma lem5223558 (h1 : term37) : term228.
Proof. exact (EQ_MP (@lem5223557) (@lem5223388 h1)). Qed.
Lemma lem5223575 (s : real -> Prop) (x : real) : (term235 s x) = (term235 s x).
Proof. exact (eq_refl (term235 s x)). Qed.
Lemma lem5223576 (s : real -> Prop) : (term237 s) = (term237 s).
Proof. exact (fun_ext (fun x : real => @lem5223575 s x)). Qed.
Lemma lem5223577 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5223578 (s : real -> Prop) : (term238 s) = (term238 s).
Proof. exact (MK_COMB (@lem5223577) (@lem5223576 s)). Qed.
Lemma lem5223587 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5223588 (s : real -> Prop) : (term239 s) = (term239 s).
Proof. exact (MK_COMB (@lem5223587 s) (@lem5223578 s)). Qed.
Lemma lem5223603 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5223604 (s : real -> Prop) : (term243 s) = (term243 s).
Proof. exact (MK_COMB (@lem5223603 s) (@lem5223588 s)). Qed.
Lemma lem5223605 : term244 = term244.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5223604 s)). Qed.
Lemma lem5223606 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5223607 : term245 = term245.
Proof. exact (MK_COMB (@lem5223606) (@lem5223605)). Qed.
Lemma lem5223608 (h1 : term17) : term245.
Proof. exact (EQ_MP (@lem5223607) (@lem5223520 h1)). Qed.
Lemma lem5223623 (s : real -> Prop) (a : real) (x : real) : (term49 s a x) = (term49 s a x).
Proof. exact (eq_refl (term49 s a x)). Qed.
Lemma lem5223624 (s : real -> Prop) (a : real) : (term59 s a) = (term59 s a).
Proof. exact (fun_ext (fun x : real => @lem5223623 s a x)). Qed.
Lemma lem5223625 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5223626 (s : real -> Prop) (a : real) : (term60 s a) = (term60 s a).
Proof. exact (MK_COMB (@lem5223625) (@lem5223624 s a)). Qed.
Lemma lem5223637 (a : real) (s : real -> Prop) : (term61 a s) = (term61 a s).
Proof. exact (eq_refl (term61 a s)). Qed.
Lemma lem5223638 (s : real -> Prop) (a : real) : (term63 s a) = (term63 s a).
Proof. exact (MK_COMB (@lem5223637 a s) (@lem5223626 s a)). Qed.
Lemma lem5223665 (s : real -> Prop) (a : real) (x : real) : (term179 s a x) = (term179 s a x).
Proof. exact (eq_refl (term179 s a x)). Qed.
Lemma lem5223666 (x : real) (s : real -> Prop) (a : real) : (term181 x s a) = (term181 x s a).
Proof. exact (MK_COMB (@lem5223665 s a x) (@lem5223638 s a)). Qed.
Lemma lem5223681 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5223682 (x : real) (s : real -> Prop) (a : real) : (term208 x s a) = (term208 x s a).
Proof. exact (MK_COMB (@lem5223681 s) (@lem5223666 x s a)). Qed.
Lemma lem5223683 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term208 x s a.
Proof. exact (EQ_MP (@lem5223682 x s a) (@lem5223523 x s a h1)). Qed.
Lemma lem5223684 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term181 x s a.
Proof. exact (proj2 (@lem5223683 x s a h1)). Qed.
Lemma lem5223685 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term76 s.
Proof. exact (proj1 (@lem5223683 x s a h1)). Qed.
Lemma lem5223688 (s : real -> Prop) (a : real) (x : real) (h1 : term143 s a x) : term143 s a x.
Proof. exact (h1). Qed.
Lemma lem5223689 (s : real -> Prop) (a : real) (h1 : term63 s a) : term63 s a.
Proof. exact (h1). Qed.
Lemma lem5223690 (s : real -> Prop) (a : real) (x : real) (h1 : term143 s a x) : term48 s a x.
Proof. exact (proj2 (@lem5223688 s a x h1)). Qed.
Lemma lem5223694 (s : real -> Prop) (a : real) (h1 : term63 s a) : term60 s a.
Proof. exact (proj2 (@lem5223689 s a h1)). Qed.
Lemma lem5223709 (y : real) (x : real) (z : real) : (term221 y x z) = (term221 y x z).
Proof. exact (eq_refl (term221 y x z)). Qed.
Lemma lem5223710 (y : real) (x : real) : (term223 y x) = (term223 y x).
Proof. exact (fun_ext (fun z : real => @lem5223709 y x z)). Qed.
Lemma lem5223711 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5223712 (y : real) (x : real) : (term224 y x) = (term224 y x).
Proof. exact (MK_COMB (@lem5223711) (@lem5223710 y x)). Qed.
Lemma lem5223713 (x : real) : (term225 x) = (term225 x).
Proof. exact (fun_ext (fun y : real => @lem5223712 y x)). Qed.
Lemma lem5223714 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5223715 (x : real) : (term226 x) = (term226 x).
Proof. exact (MK_COMB (@lem5223714) (@lem5223713 x)). Qed.
Lemma lem5223716 : term227 = term227.
Proof. exact (fun_ext (fun x : real => @lem5223715 x)). Qed.
Lemma lem5223717 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5223719 : term228 = term228.
Proof. exact (MK_COMB (@lem5223717) (@lem5223716)). Qed.
Lemma lem5223720 (h1 : term37) : term228.
Proof. exact (EQ_MP (@lem5223719) (@lem5223558 h1)). Qed.
Lemma lem5223722 {A : Type'} (P : Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5223723 (P : Prop) (Q : real -> Prop) : (term248 P Q) = (term249 P Q).
Proof. exact (@lem5223722 real P Q). Qed.
Lemma lem5223724 (s : real -> Prop) : (term250 s) = (term251 s).
Proof. exact (@lem5223723 (term252 s) (term237 s)). Qed.
Lemma lem5223725 (s : real -> Prop) (x : real) : (term253 s x) = (term235 s x).
Proof. exact (eq_refl (term253 s x)). Qed.
Lemma lem5223726 (s : real -> Prop) : (term254 s) = (term237 s).
Proof. exact (fun_ext (fun x : real => @lem5223725 s x)). Qed.
Lemma lem5223727 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5223728 (s : real -> Prop) : (term255 s) = (term238 s).
Proof. exact (MK_COMB (@lem5223727) (@lem5223726 s)). Qed.
Lemma lem5223729 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5223730 (s : real -> Prop) : (term250 s) = (term239 s).
Proof. exact (MK_COMB (@lem5223729 s) (@lem5223728 s)). Qed.
Lemma lem5223731 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5223732 (s : real -> Prop) : (term256 s) = (term257 s).
Proof. exact (MK_COMB (@lem5223731) (@lem5223730 s)). Qed.
Lemma lem5223733 (s : real -> Prop) (x : real) : (term253 s x) = (term235 s x).
Proof. exact (eq_refl (term253 s x)). Qed.
Lemma lem5223734 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5223735 (s : real -> Prop) (x : real) : (term258 s x) = (term259 s x).
Proof. exact (MK_COMB (@lem5223734 s) (@lem5223733 s x)). Qed.
Lemma lem5223736 (s : real -> Prop) : (term260 s) = (term261 s).
Proof. exact (fun_ext (fun x : real => @lem5223735 s x)). Qed.
Lemma lem5223737 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5223738 (s : real -> Prop) : (term251 s) = (term262 s).
Proof. exact (MK_COMB (@lem5223737) (@lem5223736 s)). Qed.
Lemma lem5223739 (s : real -> Prop) : ((term250 s) = (term251 s)) = ((term239 s) = (term262 s)).
Proof. exact (MK_COMB (@lem5223732 s) (@lem5223738 s)). Qed.
Lemma lem5223740 (s : real -> Prop) : (term239 s) = (term262 s).
Proof. exact (EQ_MP (@lem5223739 s) (@lem5223724 s)). Qed.
Lemma lem5223741 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5223742 (s : real -> Prop) : (term243 s) = (term263 s).
Proof. exact (MK_COMB (@lem5223741 s) (@lem5223740 s)). Qed.
Lemma lem5223744 {A : Type'} (P : Prop) (Q : A -> Prop) : (term264 A P Q) = (term265 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5223745 (P : Prop) (Q : real -> Prop) : (term266 P Q) = (term267 P Q).
Proof. exact (@lem5223744 real P Q). Qed.
Lemma lem5223746 (s : real -> Prop) : (term268 s) = (term269 s).
Proof. exact (@lem5223745 (term232 s) (term261 s)). Qed.
Lemma lem5223747 (s : real -> Prop) (x : real) : (term270 s x) = (term259 s x).
Proof. exact (eq_refl (term270 s x)). Qed.
Lemma lem5223748 (s : real -> Prop) : (term271 s) = (term261 s).
Proof. exact (fun_ext (fun x : real => @lem5223747 s x)). Qed.
Lemma lem5223749 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5223750 (s : real -> Prop) : (term272 s) = (term262 s).
Proof. exact (MK_COMB (@lem5223749) (@lem5223748 s)). Qed.
Lemma lem5223751 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5223752 (s : real -> Prop) : (term268 s) = (term263 s).
Proof. exact (MK_COMB (@lem5223751 s) (@lem5223750 s)). Qed.
Lemma lem5223753 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5223754 (s : real -> Prop) : (term273 s) = (term274 s).
Proof. exact (MK_COMB (@lem5223753) (@lem5223752 s)). Qed.
Lemma lem5223755 (s : real -> Prop) (x : real) : (term270 s x) = (term259 s x).
Proof. exact (eq_refl (term270 s x)). Qed.
Lemma lem5223756 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5223757 (s : real -> Prop) (x : real) : (term275 s x) = (term276 s x).
Proof. exact (MK_COMB (@lem5223756 s) (@lem5223755 s x)). Qed.
Lemma lem5223758 (s : real -> Prop) : (term277 s) = (term278 s).
Proof. exact (fun_ext (fun x : real => @lem5223757 s x)). Qed.
Lemma lem5223759 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5223760 (s : real -> Prop) : (term269 s) = (term279 s).
Proof. exact (MK_COMB (@lem5223759) (@lem5223758 s)). Qed.
Lemma lem5223761 (s : real -> Prop) : ((term268 s) = (term269 s)) = ((term263 s) = (term279 s)).
Proof. exact (MK_COMB (@lem5223754 s) (@lem5223760 s)). Qed.
Lemma lem5223762 (s : real -> Prop) : (term263 s) = (term279 s).
Proof. exact (EQ_MP (@lem5223761 s) (@lem5223746 s)). Qed.
Lemma lem5223763 (s : real -> Prop) : (term243 s) = (term279 s).
Proof. exact (TRANS (@lem5223742 s) (@lem5223762 s)). Qed.
Lemma lem5223764 : term244 = term280.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5223763 s)). Qed.
Lemma lem5223765 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5223766 : term245 = term281.
Proof. exact (MK_COMB (@lem5223765) (@lem5223764)). Qed.
Lemma lem5223795 (s : real -> Prop) (x : real) : (term276 s x) = (term282 s x).
Proof. exact (@lem19490 (term252 s) (term232 s) (term235 s x)). Qed.
Lemma lem5223796 (s : real -> Prop) : (term278 s) = (term283 s).
Proof. exact (fun_ext (fun x : real => @lem5223795 s x)). Qed.
Lemma lem5223797 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5223798 (s : real -> Prop) : (term279 s) = (term284 s).
Proof. exact (MK_COMB (@lem5223797) (@lem5223796 s)). Qed.
Lemma lem5223799 : term280 = term285.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5223798 s)). Qed.
Lemma lem5223800 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5223801 : term281 = term286.
Proof. exact (MK_COMB (@lem5223800) (@lem5223799)). Qed.
Lemma lem5223802 : term245 = term286.
Proof. exact (TRANS (@lem5223766) (@lem5223801)). Qed.
Lemma lem5223803 (h1 : term17) : term286.
Proof. exact (EQ_MP (@lem5223802) (@lem5223608 h1)). Qed.
Lemma lem5223850 {A : Type'} (P : Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5223851 (P : Prop) (Q : real -> Prop) : (term248 P Q) = (term249 P Q).
Proof. exact (@lem5223850 real P Q). Qed.
Lemma lem5223852 (s : real -> Prop) : (term250 s) = (term251 s).
Proof. exact (@lem5223851 (term252 s) (term237 s)). Qed.
Lemma lem5223853 (s : real -> Prop) (x : real) : (term253 s x) = (term235 s x).
Proof. exact (eq_refl (term253 s x)). Qed.
Lemma lem5223854 (s : real -> Prop) : (term254 s) = (term237 s).
Proof. exact (fun_ext (fun x : real => @lem5223853 s x)). Qed.
Lemma lem5223855 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5223856 (s : real -> Prop) : (term255 s) = (term238 s).
Proof. exact (MK_COMB (@lem5223855) (@lem5223854 s)). Qed.
Lemma lem5223857 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5223858 (s : real -> Prop) : (term250 s) = (term239 s).
Proof. exact (MK_COMB (@lem5223857 s) (@lem5223856 s)). Qed.
Lemma lem5223859 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5223860 (s : real -> Prop) : (term256 s) = (term257 s).
Proof. exact (MK_COMB (@lem5223859) (@lem5223858 s)). Qed.
Lemma lem5223861 (s : real -> Prop) (x : real) : (term253 s x) = (term235 s x).
Proof. exact (eq_refl (term253 s x)). Qed.
Lemma lem5223862 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5223863 (s : real -> Prop) (x : real) : (term258 s x) = (term259 s x).
Proof. exact (MK_COMB (@lem5223862 s) (@lem5223861 s x)). Qed.
Lemma lem5223864 (s : real -> Prop) : (term260 s) = (term261 s).
Proof. exact (fun_ext (fun x : real => @lem5223863 s x)). Qed.
Lemma lem5223865 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5223866 (s : real -> Prop) : (term251 s) = (term262 s).
Proof. exact (MK_COMB (@lem5223865) (@lem5223864 s)). Qed.
Lemma lem5223867 (s : real -> Prop) : ((term250 s) = (term251 s)) = ((term239 s) = (term262 s)).
Proof. exact (MK_COMB (@lem5223860 s) (@lem5223866 s)). Qed.
Lemma lem5223868 (s : real -> Prop) : (term239 s) = (term262 s).
Proof. exact (EQ_MP (@lem5223867 s) (@lem5223852 s)). Qed.
Lemma lem5223869 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5223870 (s : real -> Prop) : (term243 s) = (term263 s).
Proof. exact (MK_COMB (@lem5223869 s) (@lem5223868 s)). Qed.
Lemma lem5223872 {A : Type'} (P : Prop) (Q : A -> Prop) : (term264 A P Q) = (term265 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5223873 (P : Prop) (Q : real -> Prop) : (term266 P Q) = (term267 P Q).
Proof. exact (@lem5223872 real P Q). Qed.
Lemma lem5223874 (s : real -> Prop) : (term268 s) = (term269 s).
Proof. exact (@lem5223873 (term232 s) (term261 s)). Qed.
Lemma lem5223875 (s : real -> Prop) (x : real) : (term270 s x) = (term259 s x).
Proof. exact (eq_refl (term270 s x)). Qed.
Lemma lem5223876 (s : real -> Prop) : (term271 s) = (term261 s).
Proof. exact (fun_ext (fun x : real => @lem5223875 s x)). Qed.
Lemma lem5223877 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5223878 (s : real -> Prop) : (term272 s) = (term262 s).
Proof. exact (MK_COMB (@lem5223877) (@lem5223876 s)). Qed.
Lemma lem5223879 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5223880 (s : real -> Prop) : (term268 s) = (term263 s).
Proof. exact (MK_COMB (@lem5223879 s) (@lem5223878 s)). Qed.
Lemma lem5223881 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5223882 (s : real -> Prop) : (term273 s) = (term274 s).
Proof. exact (MK_COMB (@lem5223881) (@lem5223880 s)). Qed.
Lemma lem5223883 (s : real -> Prop) (x : real) : (term270 s x) = (term259 s x).
Proof. exact (eq_refl (term270 s x)). Qed.
Lemma lem5223884 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5223885 (s : real -> Prop) (x : real) : (term275 s x) = (term276 s x).
Proof. exact (MK_COMB (@lem5223884 s) (@lem5223883 s x)). Qed.
Lemma lem5223886 (s : real -> Prop) : (term277 s) = (term278 s).
Proof. exact (fun_ext (fun x : real => @lem5223885 s x)). Qed.
Lemma lem5223887 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5223888 (s : real -> Prop) : (term269 s) = (term279 s).
Proof. exact (MK_COMB (@lem5223887) (@lem5223886 s)). Qed.
Lemma lem5223889 (s : real -> Prop) : ((term268 s) = (term269 s)) = ((term263 s) = (term279 s)).
Proof. exact (MK_COMB (@lem5223882 s) (@lem5223888 s)). Qed.
Lemma lem5223890 (s : real -> Prop) : (term263 s) = (term279 s).
Proof. exact (EQ_MP (@lem5223889 s) (@lem5223874 s)). Qed.
Lemma lem5223891 (s : real -> Prop) : (term243 s) = (term279 s).
Proof. exact (TRANS (@lem5223870 s) (@lem5223890 s)). Qed.
Lemma lem5223892 : term244 = term280.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5223891 s)). Qed.
Lemma lem5223893 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5223894 : term245 = term281.
Proof. exact (MK_COMB (@lem5223893) (@lem5223892)). Qed.
Lemma lem5223923 (s : real -> Prop) (x : real) : (term276 s x) = (term282 s x).
Proof. exact (@lem19490 (term252 s) (term232 s) (term235 s x)). Qed.
Lemma lem5223924 (s : real -> Prop) : (term278 s) = (term283 s).
Proof. exact (fun_ext (fun x : real => @lem5223923 s x)). Qed.
Lemma lem5223925 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5223926 (s : real -> Prop) : (term279 s) = (term284 s).
Proof. exact (MK_COMB (@lem5223925) (@lem5223924 s)). Qed.
Lemma lem5223927 : term280 = term285.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5223926 s)). Qed.
Lemma lem5223928 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5223929 : term281 = term286.
Proof. exact (MK_COMB (@lem5223928) (@lem5223927)). Qed.
Lemma lem5223930 : term245 = term286.
Proof. exact (TRANS (@lem5223894) (@lem5223929)). Qed.
Lemma lem5223931 (h1 : term17) : term286.
Proof. exact (EQ_MP (@lem5223930) (@lem5223608 h1)). Qed.
Lemma lem5223951 (s : real -> Prop) (a : real) (x : real) : (term49 s a x) = (term49 s a x).
Proof. exact (eq_refl (term49 s a x)). Qed.
Lemma lem5223952 (s : real -> Prop) (a : real) : (term59 s a) = (term59 s a).
Proof. exact (fun_ext (fun x : real => @lem5223951 s a x)). Qed.
Lemma lem5223953 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5223955 (s : real -> Prop) (a : real) : (term60 s a) = (term60 s a).
Proof. exact (MK_COMB (@lem5223953) (@lem5223952 s a)). Qed.
Lemma lem5223956 (s : real -> Prop) (a : real) (h1 : term63 s a) : term60 s a.
Proof. exact (EQ_MP (@lem5223955 s a) (@lem5223694 s a h1)). Qed.
Lemma lem5223957 (_68362 : real) (h1 : term37) : term287 _68362.
Proof. exact (@lem5223720 h1 _68362). Qed.
Lemma lem5223958 (_68362 : real) : (term287 _68362) = (term226 _68362).
Proof. exact (eq_refl (term287 _68362)). Qed.
Lemma lem5223959 (_68362 : real) (h1 : term37) : term226 _68362.
Proof. exact (EQ_MP (@lem5223958 _68362) (@lem5223957 _68362 h1)). Qed.
Lemma lem5223960 (_68362 : real) (_68363 : real) (h1 : term37) : term288 _68362 _68363.
Proof. exact (@lem5223959 _68362 h1 _68363). Qed.
Lemma lem5223961 (_68363 : real) (_68362 : real) : (term288 _68362 _68363) = (term224 _68363 _68362).
Proof. exact (eq_refl (term288 _68362 _68363)). Qed.
Lemma lem5223962 (_68363 : real) (_68362 : real) (h1 : term37) : term224 _68363 _68362.
Proof. exact (EQ_MP (@lem5223961 _68363 _68362) (@lem5223960 _68362 _68363 h1)). Qed.
Lemma lem5223963 (_68363 : real) (_68362 : real) (_68364 : real) (h1 : term37) : term289 _68363 _68362 _68364.
Proof. exact (@lem5223962 _68363 _68362 h1 _68364). Qed.
Lemma lem5223964 (_68363 : real) (_68362 : real) (_68364 : real) : (term289 _68363 _68362 _68364) = (term221 _68363 _68362 _68364).
Proof. exact (eq_refl (term289 _68363 _68362 _68364)). Qed.
Lemma lem5223965 (_68363 : real) (_68362 : real) (_68364 : real) (h1 : term37) : term221 _68363 _68362 _68364.
Proof. exact (EQ_MP (@lem5223964 _68363 _68362 _68364) (@lem5223963 _68363 _68362 _68364 h1)). Qed.
Lemma lem5223966 (_68365 : real -> Prop) (h1 : term17) : term290 _68365.
Proof. exact (@lem5223803 h1 _68365). Qed.
Lemma lem5223967 (_68365 : real -> Prop) : (term290 _68365) = (term284 _68365).
Proof. exact (eq_refl (term290 _68365)). Qed.
Lemma lem5223968 (_68365 : real -> Prop) (h1 : term17) : term284 _68365.
Proof. exact (EQ_MP (@lem5223967 _68365) (@lem5223966 _68365 h1)). Qed.
Lemma lem5223969 (_68365 : real -> Prop) (_68366 : real) (h1 : term17) : term291 _68365 _68366.
Proof. exact (@lem5223968 _68365 h1 _68366). Qed.
Lemma lem5223970 (_68365 : real -> Prop) (_68366 : real) : (term291 _68365 _68366) = (term282 _68365 _68366).
Proof. exact (eq_refl (term291 _68365 _68366)). Qed.
Lemma lem5223971 (_68365 : real -> Prop) (_68366 : real) (h1 : term17) : term282 _68365 _68366.
Proof. exact (EQ_MP (@lem5223970 _68365 _68366) (@lem5223969 _68365 _68366 h1)). Qed.
Lemma lem5223981 (_68370 : real -> Prop) (h1 : term17) : term290 _68370.
Proof. exact (@lem5223931 h1 _68370). Qed.
Lemma lem5223982 (_68370 : real -> Prop) : (term290 _68370) = (term284 _68370).
Proof. exact (eq_refl (term290 _68370)). Qed.
Lemma lem5223983 (_68370 : real -> Prop) (h1 : term17) : term284 _68370.
Proof. exact (EQ_MP (@lem5223982 _68370) (@lem5223981 _68370 h1)). Qed.
Lemma lem5223984 (_68370 : real -> Prop) (_68371 : real) (h1 : term17) : term291 _68370 _68371.
Proof. exact (@lem5223983 _68370 h1 _68371). Qed.
Lemma lem5223985 (_68370 : real -> Prop) (_68371 : real) : (term291 _68370 _68371) = (term282 _68370 _68371).
Proof. exact (eq_refl (term291 _68370 _68371)). Qed.
Lemma lem5223986 (_68370 : real -> Prop) (_68371 : real) (h1 : term17) : term282 _68370 _68371.
Proof. exact (EQ_MP (@lem5223985 _68370 _68371) (@lem5223984 _68370 _68371 h1)). Qed.
Lemma lem5223987 (_68372 : real) (s : real -> Prop) (a : real) (h1 : term63 s a) : term292 s a _68372.
Proof. exact (@lem5223956 s a h1 _68372). Qed.
Lemma lem5223988 (s : real -> Prop) (a : real) (_68372 : real) : (term292 s a _68372) = (term49 s a _68372).
Proof. exact (eq_refl (term292 s a _68372)). Qed.
Lemma lem5223990 (_68365 : real -> Prop) (_68366 : real) (h1 : term17) : term293 _68365 _68366.
Proof. exact (proj2 (@lem5223971 _68365 _68366 h1)). Qed.
Lemma lem5223993 (_68370 : real -> Prop) (h1 : term17) : term294 _68370.
Proof. exact (proj1 (@lem5223986 _68370 (@el real) h1)). Qed.
Lemma lem5224004 (_68363 : real) (_68362 : real) (_68364 : real) : (term221 _68363 _68362 _68364) = (term295 _68363 _68362 _68364).
Proof. exact (@lem5222555 (term296 _68362 _68363) (term296 _68363 _68364) (real_le _68362 _68364)). Qed.
Lemma lem5224005 (_68363 : real) (_68362 : real) (_68364 : real) (h1 : term37) : term295 _68363 _68362 _68364.
Proof. exact (EQ_MP (@lem5224004 _68363 _68362 _68364) (@lem5223965 _68363 _68362 _68364 h1)). Qed.
Lemma lem5224015 (s : real -> Prop) (a : real) (x : real) (h1 : term143 s a x) : term296 a x.
Proof. exact (proj2 (@lem5223690 s a x h1)). Qed.
Lemma lem5224042 (_68365 : real -> Prop) (_68366 : real) : (term293 _68365 _68366) = (term297 _68365 _68366).
Proof. exact (@lem5222555 (term298 _68365) (_68365 = (@EMPTY real)) (term235 _68365 _68366)). Qed.
Lemma lem5224043 (_68365 : real -> Prop) (_68366 : real) (h1 : term17) : term297 _68365 _68366.
Proof. exact (EQ_MP (@lem5224042 _68365 _68366) (@lem5223990 _68365 _68366 h1)). Qed.
Lemma lem5224061 (s : real -> Prop) (a : real) (h1 : term63 s a) : term299 a s.
Proof. exact (proj1 (@lem5223689 s a h1)). Qed.
Lemma lem5224067 (_68372 : real) (s : real -> Prop) (a : real) (h1 : term63 s a) : term49 s a _68372.
Proof. exact (EQ_MP (@lem5223988 s a _68372) (@lem5223987 _68372 s a h1)). Qed.
Lemma lem5224078 (_68370 : real -> Prop) : (term294 _68370) = (term300 _68370).
Proof. exact (@lem5222555 (term298 _68370) (_68370 = (@EMPTY real)) (term252 _68370)). Qed.
Lemma lem5224079 (_68370 : real -> Prop) (h1 : term17) : term300 _68370.
Proof. exact (EQ_MP (@lem5224078 _68370) (@lem5223993 _68370 h1)). Qed.
Lemma lem5224159 (s : real -> Prop) (a : real) (x : real) (h1 : term143 s a x) : term42 a s.
Proof. exact (proj1 (@lem5223688 s a x h1)). Qed.
Lemma lem5224160 (s : real -> Prop) (a : real) (x : real) (h1 : term143 s a x) : term301 a s.
Proof. exact (fun h0 : term299 a s => @lem5224159 s a x h1). Qed.
Lemma lem5224162 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5224163 (a : real) (s : real -> Prop) : (term301 a s) = (term42 a s).
Proof. exact (@lem5224162 (term42 a s)). Qed.
Lemma lem5224164 (s : real -> Prop) (a : real) (x : real) (h1 : term143 s a x) : term42 a s.
Proof. exact (EQ_MP (@lem5224163 a s) (@lem5224160 s a x h1)). Qed.
Lemma lem5224166 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : @FINITE real s.
Proof. exact (proj1 (@lem5223685 x s a h1)). Qed.
Lemma lem5224167 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term303 s.
Proof. exact (fun h0 : term298 s => @lem5224166 x s a h1). Qed.
Lemma lem5224169 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5224170 (s : real -> Prop) : (term303 s) = (@FINITE real s).
Proof. exact (@lem5224169 (@FINITE real s)). Qed.
Lemma lem5224171 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : @FINITE real s.
Proof. exact (EQ_MP (@lem5224170 s) (@lem5224167 x s a h1)). Qed.
Lemma lem5224173 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term234 s.
Proof. exact (proj2 (@lem5223685 x s a h1)). Qed.
Lemma lem5224174 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term304 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5224173 x s a h1). Qed.
Lemma lem5224176 (p : Prop) : (term305 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5224177 (s : real -> Prop) : (term304 s) = (term234 s).
Proof. exact (@lem5224176 (s = (@EMPTY real))). Qed.
Lemma lem5224178 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term234 s.
Proof. exact (EQ_MP (@lem5224177 s) (@lem5224174 x s a h1)). Qed.
Lemma lem5224180 (s : real -> Prop) (a : real) (x : real) (h1 : term143 s a x) : @IN real x s.
Proof. exact (proj1 (@lem5223690 s a x h1)). Qed.
Lemma lem5224181 (s : real -> Prop) (a : real) (x : real) (h1 : term143 s a x) : term306 x s.
Proof. exact (fun h0 : term307 x s => @lem5224180 s a x h1). Qed.
Lemma lem5224183 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5224184 (x : real) (s : real -> Prop) : (term306 x s) = (@IN real x s).
Proof. exact (@lem5224183 (@IN real x s)). Qed.
Lemma lem5224185 (s : real -> Prop) (a : real) (x : real) (h1 : term143 s a x) : @IN real x s.
Proof. exact (EQ_MP (@lem5224184 x s) (@lem5224181 s a x h1)). Qed.
Lemma lem5224191 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5224192 (_68365 : real -> Prop) (_68366 : real) : (term297 _68365 _68366) = (term308 _68365 _68366).
Proof. exact (@lem5224191 (_68365 = (@EMPTY real)) (term298 _68365) (term235 _68365 _68366)). Qed.
Lemma lem5224218 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5224219 (_68366 : real) (_68365 : real -> Prop) : (term235 _68365 _68366) = (term309 _68366 _68365).
Proof. exact (@lem5224218 (term236 _68365 _68366) (term307 _68366 _68365)). Qed.
Lemma lem5224225 (_68365 : real -> Prop) : (term230 _68365) = (term230 _68365).
Proof. exact (eq_refl (term230 _68365)). Qed.
Lemma lem5224226 (_68366 : real) (_68365 : real -> Prop) : (term310 _68365 _68366) = (term311 _68366 _68365).
Proof. exact (MK_COMB (@lem5224225 _68365) (@lem5224219 _68366 _68365)). Qed.
Lemma lem5224230 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5224231 (_68366 : real) (_68365 : real -> Prop) : (term311 _68366 _68365) = (term312 _68366 _68365).
Proof. exact (@lem5224230 (term236 _68365 _68366) (term298 _68365) (term307 _68366 _68365)). Qed.
Lemma lem5224247 (_68366 : real) (_68365 : real -> Prop) : (term310 _68365 _68366) = (term312 _68366 _68365).
Proof. exact (TRANS (@lem5224226 _68366 _68365) (@lem5224231 _68366 _68365)). Qed.
Lemma lem5224248 (_68365 : real -> Prop) : (term313 _68365) = (term313 _68365).
Proof. exact (eq_refl (term313 _68365)). Qed.
Lemma lem5224249 (_68366 : real) (_68365 : real -> Prop) : (term308 _68365 _68366) = (term314 _68366 _68365).
Proof. exact (MK_COMB (@lem5224248 _68365) (@lem5224247 _68366 _68365)). Qed.
Lemma lem5224260 (_68366 : real) (_68365 : real -> Prop) : (term297 _68365 _68366) = (term314 _68366 _68365).
Proof. exact (TRANS (@lem5224192 _68365 _68366) (@lem5224249 _68366 _68365)). Qed.
Lemma lem5224261 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5224262 (_68366 : real) (_68365 : real -> Prop) : (term315 _68365 _68366) = (term316 _68366 _68365).
Proof. exact (MK_COMB (@lem5224261) (@lem5224260 _68366 _68365)). Qed.
Lemma lem5224276 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5224277 (_68366 : real) (_68365 : real -> Prop) : (term317 _68366 _68365) = (term318 _68366 _68365).
Proof. exact (@lem5224276 (_68365 = (@EMPTY real)) (term298 _68365) (term307 _68366 _68365)). Qed.
Lemma lem5224295 (_68365 : real -> Prop) (_68366 : real) : (term319 _68365 _68366) = (term319 _68365 _68366).
Proof. exact (eq_refl (term319 _68365 _68366)). Qed.
Lemma lem5224296 (_68366 : real) (_68365 : real -> Prop) : (term320 _68366 _68365) = (term321 _68366 _68365).
Proof. exact (MK_COMB (@lem5224295 _68365 _68366) (@lem5224277 _68366 _68365)). Qed.
Lemma lem5224300 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5224301 (_68366 : real) (_68365 : real -> Prop) : (term321 _68366 _68365) = (term314 _68366 _68365).
Proof. exact (@lem5224300 (_68365 = (@EMPTY real)) (term236 _68365 _68366) (term322 _68366 _68365)). Qed.
Lemma lem5224329 (_68366 : real) (_68365 : real -> Prop) : (term320 _68366 _68365) = (term314 _68366 _68365).
Proof. exact (TRANS (@lem5224296 _68366 _68365) (@lem5224301 _68366 _68365)). Qed.
Lemma lem5224330 (_68366 : real) (_68365 : real -> Prop) : ((term297 _68365 _68366) = (term320 _68366 _68365)) = ((term314 _68366 _68365) = (term314 _68366 _68365)).
Proof. exact (MK_COMB (@lem5224262 _68366 _68365) (@lem5224329 _68366 _68365)). Qed.
Lemma lem5224332 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5224333 (x : Prop) : (x = x) = True.
Proof. exact (@lem5224332 Prop x). Qed.
Lemma lem5224334 (_68366 : real) (_68365 : real -> Prop) : ((term314 _68366 _68365) = (term314 _68366 _68365)) = True.
Proof. exact (@lem5224333 (term314 _68366 _68365)). Qed.
Lemma lem5224335 (_68366 : real) (_68365 : real -> Prop) : ((term297 _68365 _68366) = (term320 _68366 _68365)) = True.
Proof. exact (TRANS (@lem5224330 _68366 _68365) (@lem5224334 _68366 _68365)). Qed.
Lemma lem5224336 (_68366 : real) (_68365 : real -> Prop) : True = ((term297 _68365 _68366) = (term320 _68366 _68365)).
Proof. exact (SYM (@lem5224335 _68366 _68365)). Qed.
Lemma lem5224337 (_68366 : real) (_68365 : real -> Prop) : (term297 _68365 _68366) = (term320 _68366 _68365).
Proof. exact (EQ_MP (@lem5224336 _68366 _68365) (@lem0)). Qed.
Lemma lem5224338 (_68366 : real) (_68365 : real -> Prop) (h1 : term17) : term320 _68366 _68365.
Proof. exact (EQ_MP (@lem5224337 _68366 _68365) (@lem5224043 _68365 _68366 h1)). Qed.
Lemma lem5224340 (b : Prop) (a : Prop) : (a \/ b) = (term323 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5224341 (_68365 : real -> Prop) (_68366 : real) : (term320 _68366 _68365) = (term324 _68365 _68366).
Proof. exact (@lem5224340 (term317 _68366 _68365) (term236 _68365 _68366)). Qed.
Lemma lem5224343 (a : Prop) (b : Prop) : (term325 a b) = (term326 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5224344 (_68366 : real) (_68365 : real -> Prop) : (term327 _68366 _68365) = (term328 _68366 _68365).
Proof. exact (@lem5224343 (term298 _68365) (term329 _68366 _68365)). Qed.
Lemma lem5224346 (a : Prop) : (term330 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5224347 (_68365 : real -> Prop) : (term331 _68365) = (@FINITE real _68365).
Proof. exact (@lem5224346 (@FINITE real _68365)). Qed.
Lemma lem5224348 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5224349 (_68365 : real -> Prop) : (term332 _68365) = (term333 _68365).
Proof. exact (MK_COMB (@lem5224348) (@lem5224347 _68365)). Qed.
Lemma lem5224351 (a : Prop) (b : Prop) : (term325 a b) = (term326 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5224352 (_68366 : real) (_68365 : real -> Prop) : (term334 _68366 _68365) = (term335 _68366 _68365).
Proof. exact (@lem5224351 (_68365 = (@EMPTY real)) (term307 _68366 _68365)). Qed.
Lemma lem5224354 (a : Prop) : (term330 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5224355 (_68366 : real) (_68365 : real -> Prop) : (term336 _68366 _68365) = (@IN real _68366 _68365).
Proof. exact (@lem5224354 (@IN real _68366 _68365)). Qed.
Lemma lem5224356 (_68365 : real -> Prop) : (term337 _68365) = (term337 _68365).
Proof. exact (eq_refl (term337 _68365)). Qed.
Lemma lem5224357 (_68366 : real) (_68365 : real -> Prop) : (term335 _68366 _68365) = (term338 _68366 _68365).
Proof. exact (MK_COMB (@lem5224356 _68365) (@lem5224355 _68366 _68365)). Qed.
Lemma lem5224358 (_68366 : real) (_68365 : real -> Prop) : (term334 _68366 _68365) = (term338 _68366 _68365).
Proof. exact (TRANS (@lem5224352 _68366 _68365) (@lem5224357 _68366 _68365)). Qed.
Lemma lem5224359 (_68366 : real) (_68365 : real -> Prop) : (term328 _68366 _68365) = (term339 _68366 _68365).
Proof. exact (MK_COMB (@lem5224349 _68365) (@lem5224358 _68366 _68365)). Qed.
Lemma lem5224360 (_68366 : real) (_68365 : real -> Prop) : (term327 _68366 _68365) = (term339 _68366 _68365).
Proof. exact (TRANS (@lem5224344 _68366 _68365) (@lem5224359 _68366 _68365)). Qed.
Lemma lem5224361 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5224362 (_68366 : real) (_68365 : real -> Prop) : (term340 _68366 _68365) = (term341 _68366 _68365).
Proof. exact (MK_COMB (@lem5224361) (@lem5224360 _68366 _68365)). Qed.
Lemma lem5224363 (_68365 : real -> Prop) (_68366 : real) : (term236 _68365 _68366) = (term236 _68365 _68366).
Proof. exact (eq_refl (term236 _68365 _68366)). Qed.
Lemma lem5224364 (_68365 : real -> Prop) (_68366 : real) : (term324 _68365 _68366) = (term342 _68365 _68366).
Proof. exact (MK_COMB (@lem5224362 _68366 _68365) (@lem5224363 _68365 _68366)). Qed.
Lemma lem5224365 (_68365 : real -> Prop) (_68366 : real) : (term320 _68366 _68365) = (term342 _68365 _68366).
Proof. exact (TRANS (@lem5224341 _68365 _68366) (@lem5224364 _68365 _68366)). Qed.
Lemma lem5224367 (s : real -> Prop) (a : real) (x : real) (h1 : term208 x s a) (h2 : term143 s a x) : term338 x s.
Proof. exact (conj (@lem5224178 x s a h1) (@lem5224185 s a x h2)). Qed.
Lemma lem5224368 (s : real -> Prop) (a : real) (x : real) (h1 : term208 x s a) (h2 : term143 s a x) : term339 x s.
Proof. exact (conj (@lem5224171 x s a h1) (@lem5224367 s a x h1 h2)). Qed.
Lemma lem5224370 (_68365 : real -> Prop) (_68366 : real) (h1 : term17) : term342 _68365 _68366.
Proof. exact (EQ_MP (@lem5224365 _68365 _68366) (@lem5224338 _68366 _68365 h1)). Qed.
Lemma lem5224371 (s : real -> Prop) (x : real) (h1 : term17) : term342 s x.
Proof. exact (@lem5224370 s x h1). Qed.
Lemma lem5224374 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term208 x s a) (h3 : term143 s a x) : term236 s x.
Proof. exact (@lem5224371 s x h1 (@lem5224368 s a x h2 h3)). Qed.
Lemma lem5224375 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term208 x s a) (h3 : term143 s a x) : term343 s x.
Proof. exact (fun h0 : term344 s x => @lem5224374 s a x h1 h2 h3). Qed.
Lemma lem5224377 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5224378 (s : real -> Prop) (x : real) : (term343 s x) = (term236 s x).
Proof. exact (@lem5224377 (term236 s x)). Qed.
Lemma lem5224379 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term208 x s a) (h3 : term143 s a x) : term236 s x.
Proof. exact (EQ_MP (@lem5224378 s x) (@lem5224375 s a x h1 h2 h3)). Qed.
Lemma lem5224395 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5224396 (_68362 : real) (_68363 : real) (_68364 : real) : (term345 _68363 _68362 _68364) = (term346 _68362 _68363 _68364).
Proof. exact (@lem5224395 (real_le _68362 _68364) (term296 _68363 _68364)). Qed.
Lemma lem5224402 (_68362 : real) (_68363 : real) : (term347 _68362 _68363) = (term347 _68362 _68363).
Proof. exact (eq_refl (term347 _68362 _68363)). Qed.
Lemma lem5224403 (_68362 : real) (_68363 : real) (_68364 : real) : (term295 _68363 _68362 _68364) = (term348 _68362 _68363 _68364).
Proof. exact (MK_COMB (@lem5224402 _68362 _68363) (@lem5224396 _68362 _68363 _68364)). Qed.
Lemma lem5224407 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5224408 (_68362 : real) (_68363 : real) (_68364 : real) : (term348 _68362 _68363 _68364) = (term349 _68362 _68363 _68364).
Proof. exact (@lem5224407 (real_le _68362 _68364) (term296 _68362 _68363) (term296 _68363 _68364)). Qed.
Lemma lem5224424 (_68362 : real) (_68363 : real) (_68364 : real) : (term295 _68363 _68362 _68364) = (term349 _68362 _68363 _68364).
Proof. exact (TRANS (@lem5224403 _68362 _68363 _68364) (@lem5224408 _68362 _68363 _68364)). Qed.
Lemma lem5224425 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5224426 (_68362 : real) (_68363 : real) (_68364 : real) : (term350 _68363 _68362 _68364) = (term351 _68362 _68363 _68364).
Proof. exact (MK_COMB (@lem5224425) (@lem5224424 _68362 _68363 _68364)). Qed.
Lemma lem5224442 (_68362 : real) (_68363 : real) (_68364 : real) : (term349 _68362 _68363 _68364) = (term349 _68362 _68363 _68364).
Proof. exact (eq_refl (term349 _68362 _68363 _68364)). Qed.
Lemma lem5224443 (_68362 : real) (_68363 : real) (_68364 : real) : ((term295 _68363 _68362 _68364) = (term349 _68362 _68363 _68364)) = ((term349 _68362 _68363 _68364) = (term349 _68362 _68363 _68364)).
Proof. exact (MK_COMB (@lem5224426 _68362 _68363 _68364) (@lem5224442 _68362 _68363 _68364)). Qed.
Lemma lem5224445 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5224446 (x : Prop) : (x = x) = True.
Proof. exact (@lem5224445 Prop x). Qed.
Lemma lem5224447 (_68362 : real) (_68363 : real) (_68364 : real) : ((term349 _68362 _68363 _68364) = (term349 _68362 _68363 _68364)) = True.
Proof. exact (@lem5224446 (term349 _68362 _68363 _68364)). Qed.
Lemma lem5224448 (_68362 : real) (_68363 : real) (_68364 : real) : ((term295 _68363 _68362 _68364) = (term349 _68362 _68363 _68364)) = True.
Proof. exact (TRANS (@lem5224443 _68362 _68363 _68364) (@lem5224447 _68362 _68363 _68364)). Qed.
Lemma lem5224449 (_68362 : real) (_68363 : real) (_68364 : real) : True = ((term295 _68363 _68362 _68364) = (term349 _68362 _68363 _68364)).
Proof. exact (SYM (@lem5224448 _68362 _68363 _68364)). Qed.
Lemma lem5224450 (_68362 : real) (_68363 : real) (_68364 : real) : (term295 _68363 _68362 _68364) = (term349 _68362 _68363 _68364).
Proof. exact (EQ_MP (@lem5224449 _68362 _68363 _68364) (@lem0)). Qed.
Lemma lem5224451 (_68362 : real) (_68363 : real) (_68364 : real) (h1 : term37) : term349 _68362 _68363 _68364.
Proof. exact (EQ_MP (@lem5224450 _68362 _68363 _68364) (@lem5224005 _68363 _68362 _68364 h1)). Qed.
Lemma lem5224453 (b : Prop) (a : Prop) : (a \/ b) = (term323 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5224454 (_68363 : real) (_68362 : real) (_68364 : real) : (term349 _68362 _68363 _68364) = (term352 _68363 _68362 _68364).
Proof. exact (@lem5224453 (term217 _68362 _68363 _68364) (real_le _68362 _68364)). Qed.
Lemma lem5224456 (a : Prop) (b : Prop) : (term325 a b) = (term326 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5224457 (_68362 : real) (_68363 : real) (_68364 : real) : (term353 _68362 _68363 _68364) = (term354 _68362 _68363 _68364).
Proof. exact (@lem5224456 (term296 _68362 _68363) (term296 _68363 _68364)). Qed.
Lemma lem5224459 (a : Prop) : (term330 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5224460 (_68362 : real) (_68363 : real) : (term355 _68362 _68363) = (real_le _68362 _68363).
Proof. exact (@lem5224459 (real_le _68362 _68363)). Qed.
Lemma lem5224461 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5224462 (_68362 : real) (_68363 : real) : (term356 _68362 _68363) = (term357 _68362 _68363).
Proof. exact (MK_COMB (@lem5224461) (@lem5224460 _68362 _68363)). Qed.
Lemma lem5224464 (a : Prop) : (term330 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5224465 (_68363 : real) (_68364 : real) : (term355 _68363 _68364) = (real_le _68363 _68364).
Proof. exact (@lem5224464 (real_le _68363 _68364)). Qed.
Lemma lem5224466 (_68362 : real) (_68363 : real) (_68364 : real) : (term354 _68362 _68363 _68364) = (term222 _68362 _68363 _68364).
Proof. exact (MK_COMB (@lem5224462 _68362 _68363) (@lem5224465 _68363 _68364)). Qed.
Lemma lem5224467 (_68362 : real) (_68363 : real) (_68364 : real) : (term353 _68362 _68363 _68364) = (term222 _68362 _68363 _68364).
Proof. exact (TRANS (@lem5224457 _68362 _68363 _68364) (@lem5224466 _68362 _68363 _68364)). Qed.
Lemma lem5224468 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5224469 (_68362 : real) (_68363 : real) (_68364 : real) : (term358 _68362 _68363 _68364) = (term359 _68362 _68363 _68364).
Proof. exact (MK_COMB (@lem5224468) (@lem5224467 _68362 _68363 _68364)). Qed.
Lemma lem5224470 (_68362 : real) (_68364 : real) : (real_le _68362 _68364) = (real_le _68362 _68364).
Proof. exact (eq_refl (real_le _68362 _68364)). Qed.
Lemma lem5224471 (_68363 : real) (_68362 : real) (_68364 : real) : (term352 _68363 _68362 _68364) = (term31 _68363 _68362 _68364).
Proof. exact (MK_COMB (@lem5224469 _68362 _68363 _68364) (@lem5224470 _68362 _68364)). Qed.
Lemma lem5224472 (_68363 : real) (_68362 : real) (_68364 : real) : (term349 _68362 _68363 _68364) = (term31 _68363 _68362 _68364).
Proof. exact (TRANS (@lem5224454 _68363 _68362 _68364) (@lem5224471 _68363 _68362 _68364)). Qed.
Lemma lem5224474 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term208 x s a) (h3 : term143 s a x) : term360 a s x.
Proof. exact (conj (@lem5224164 s a x h3) (@lem5224379 s a x h1 h2 h3)). Qed.
Lemma lem5224476 (_68363 : real) (_68362 : real) (_68364 : real) (h1 : term37) : term31 _68363 _68362 _68364.
Proof. exact (EQ_MP (@lem5224472 _68363 _68362 _68364) (@lem5224451 _68362 _68363 _68364 h1)). Qed.
Lemma lem5224477 (s : real -> Prop) (a : real) (x : real) (h1 : term37) : term361 s a x.
Proof. exact (@lem5224476 (inf s) a x h1). Qed.
Lemma lem5224480 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) (h4 : term143 s a x) : real_le a x.
Proof. exact (@lem5224477 s a x h2 (@lem5224474 s a x h1 h3 h4)). Qed.
Lemma lem5224481 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) (h4 : term143 s a x) : term362 a x.
Proof. exact (fun h0 : term296 a x => @lem5224480 s a x h1 h2 h3 h4). Qed.
Lemma lem5224483 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5224484 (a : real) (x : real) : (term362 a x) = (real_le a x).
Proof. exact (@lem5224483 (real_le a x)). Qed.
Lemma lem5224485 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) (h4 : term143 s a x) : real_le a x.
Proof. exact (EQ_MP (@lem5224484 a x) (@lem5224481 s a x h1 h2 h3 h4)). Qed.
Lemma lem5224488 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5224490 (a : real) (x : real) : (term296 a x) = (term363 a x).
Proof. exact (@lem5224488 (real_le a x)). Qed.
Lemma lem5224493 (s : real -> Prop) (a : real) (x : real) (h1 : term143 s a x) : term363 a x.
Proof. exact (EQ_MP (@lem5224490 a x) (@lem5224015 s a x h1)). Qed.
Lemma lem5224496 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) (h4 : term143 s a x) : False.
Proof. exact (@lem5224493 s a x h4 (@lem5224485 s a x h1 h2 h3 h4)). Qed.
Lemma lem5224497 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) (h4 : term143 s a x) : term364.
Proof. exact (fun h0 : ~ False => @lem5224496 s a x h1 h2 h3 h4). Qed.
Lemma lem5224499 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5224500 : term364 = False.
Proof. exact (@lem5224499 False). Qed.
Lemma lem5224501 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) (h4 : term143 s a x) : False.
Proof. exact (EQ_MP (@lem5224500) (@lem5224497 s a x h1 h2 h3 h4)). Qed.
Lemma lem5224565 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : @FINITE real s.
Proof. exact (proj1 (@lem5223685 x s a h1)). Qed.
Lemma lem5224566 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term303 s.
Proof. exact (fun h0 : term298 s => @lem5224565 x s a h1). Qed.
Lemma lem5224568 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5224569 (s : real -> Prop) : (term303 s) = (@FINITE real s).
Proof. exact (@lem5224568 (@FINITE real s)). Qed.
Lemma lem5224570 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : @FINITE real s.
Proof. exact (EQ_MP (@lem5224569 s) (@lem5224566 x s a h1)). Qed.
Lemma lem5224572 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term234 s.
Proof. exact (proj2 (@lem5223685 x s a h1)). Qed.
Lemma lem5224573 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term304 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5224572 x s a h1). Qed.
Lemma lem5224575 (p : Prop) : (term305 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5224576 (s : real -> Prop) : (term304 s) = (term234 s).
Proof. exact (@lem5224575 (s = (@EMPTY real))). Qed.
Lemma lem5224577 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term234 s.
Proof. exact (EQ_MP (@lem5224576 s) (@lem5224573 x s a h1)). Qed.
Lemma lem5224583 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5224584 (_68370 : real -> Prop) : (term300 _68370) = (term365 _68370).
Proof. exact (@lem5224583 (_68370 = (@EMPTY real)) (term298 _68370) (term252 _68370)). Qed.
Lemma lem5224600 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5224601 (_68370 : real -> Prop) : (term366 _68370) = (term367 _68370).
Proof. exact (@lem5224600 (term252 _68370) (term298 _68370)). Qed.
Lemma lem5224607 (_68370 : real -> Prop) : (term313 _68370) = (term313 _68370).
Proof. exact (eq_refl (term313 _68370)). Qed.
Lemma lem5224608 (_68370 : real -> Prop) : (term365 _68370) = (term368 _68370).
Proof. exact (MK_COMB (@lem5224607 _68370) (@lem5224601 _68370)). Qed.
Lemma lem5224619 (_68370 : real -> Prop) : (term300 _68370) = (term368 _68370).
Proof. exact (TRANS (@lem5224584 _68370) (@lem5224608 _68370)). Qed.
Lemma lem5224620 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5224621 (_68370 : real -> Prop) : (term369 _68370) = (term370 _68370).
Proof. exact (MK_COMB (@lem5224620) (@lem5224619 _68370)). Qed.
Lemma lem5224635 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5224636 (_68370 : real -> Prop) : (term232 _68370) = (term371 _68370).
Proof. exact (@lem5224635 (_68370 = (@EMPTY real)) (term298 _68370)). Qed.
Lemma lem5224644 (_68370 : real -> Prop) : (term372 _68370) = (term372 _68370).
Proof. exact (eq_refl (term372 _68370)). Qed.
Lemma lem5224645 (_68370 : real -> Prop) : (term373 _68370) = (term374 _68370).
Proof. exact (MK_COMB (@lem5224644 _68370) (@lem5224636 _68370)). Qed.
Lemma lem5224649 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5224650 (_68370 : real -> Prop) : (term374 _68370) = (term368 _68370).
Proof. exact (@lem5224649 (_68370 = (@EMPTY real)) (term252 _68370) (term298 _68370)). Qed.
Lemma lem5224668 (_68370 : real -> Prop) : (term373 _68370) = (term368 _68370).
Proof. exact (TRANS (@lem5224645 _68370) (@lem5224650 _68370)). Qed.
Lemma lem5224669 (_68370 : real -> Prop) : ((term300 _68370) = (term373 _68370)) = ((term368 _68370) = (term368 _68370)).
Proof. exact (MK_COMB (@lem5224621 _68370) (@lem5224668 _68370)). Qed.
Lemma lem5224671 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5224672 (x : Prop) : (x = x) = True.
Proof. exact (@lem5224671 Prop x). Qed.
Lemma lem5224673 (_68370 : real -> Prop) : ((term368 _68370) = (term368 _68370)) = True.
Proof. exact (@lem5224672 (term368 _68370)). Qed.
Lemma lem5224674 (_68370 : real -> Prop) : ((term300 _68370) = (term373 _68370)) = True.
Proof. exact (TRANS (@lem5224669 _68370) (@lem5224673 _68370)). Qed.
Lemma lem5224675 (_68370 : real -> Prop) : True = ((term300 _68370) = (term373 _68370)).
Proof. exact (SYM (@lem5224674 _68370)). Qed.
Lemma lem5224676 (_68370 : real -> Prop) : (term300 _68370) = (term373 _68370).
Proof. exact (EQ_MP (@lem5224675 _68370) (@lem0)). Qed.
Lemma lem5224677 (_68370 : real -> Prop) (h1 : term17) : term373 _68370.
Proof. exact (EQ_MP (@lem5224676 _68370) (@lem5224079 _68370 h1)). Qed.
Lemma lem5224679 (b : Prop) (a : Prop) : (a \/ b) = (term323 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5224680 (_68370 : real -> Prop) : (term373 _68370) = (term375 _68370).
Proof. exact (@lem5224679 (term232 _68370) (term252 _68370)). Qed.
Lemma lem5224682 (a : Prop) (b : Prop) : (term325 a b) = (term326 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5224683 (_68370 : real -> Prop) : (term376 _68370) = (term377 _68370).
Proof. exact (@lem5224682 (term298 _68370) (_68370 = (@EMPTY real))). Qed.
Lemma lem5224685 (a : Prop) : (term330 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5224686 (_68370 : real -> Prop) : (term331 _68370) = (@FINITE real _68370).
Proof. exact (@lem5224685 (@FINITE real _68370)). Qed.
Lemma lem5224687 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5224688 (_68370 : real -> Prop) : (term332 _68370) = (term333 _68370).
Proof. exact (MK_COMB (@lem5224687) (@lem5224686 _68370)). Qed.
Lemma lem5224689 (_68370 : real -> Prop) : (term234 _68370) = (term234 _68370).
Proof. exact (eq_refl (term234 _68370)). Qed.
Lemma lem5224690 (_68370 : real -> Prop) : (term377 _68370) = (term76 _68370).
Proof. exact (MK_COMB (@lem5224688 _68370) (@lem5224689 _68370)). Qed.
Lemma lem5224691 (_68370 : real -> Prop) : (term376 _68370) = (term76 _68370).
Proof. exact (TRANS (@lem5224683 _68370) (@lem5224690 _68370)). Qed.
Lemma lem5224692 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5224693 (_68370 : real -> Prop) : (term378 _68370) = (term28 _68370).
Proof. exact (MK_COMB (@lem5224692) (@lem5224691 _68370)). Qed.
Lemma lem5224694 (_68370 : real -> Prop) : (term252 _68370) = (term252 _68370).
Proof. exact (eq_refl (term252 _68370)). Qed.
Lemma lem5224695 (_68370 : real -> Prop) : (term375 _68370) = (term379 _68370).
Proof. exact (MK_COMB (@lem5224693 _68370) (@lem5224694 _68370)). Qed.
Lemma lem5224696 (_68370 : real -> Prop) : (term373 _68370) = (term379 _68370).
Proof. exact (TRANS (@lem5224680 _68370) (@lem5224695 _68370)). Qed.
Lemma lem5224698 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term76 s.
Proof. exact (conj (@lem5224570 x s a h1) (@lem5224577 x s a h1)). Qed.
Lemma lem5224700 (_68370 : real -> Prop) (h1 : term17) : term379 _68370.
Proof. exact (EQ_MP (@lem5224696 _68370) (@lem5224677 _68370 h1)). Qed.
Lemma lem5224701 (s : real -> Prop) (h1 : term17) : term379 s.
Proof. exact (@lem5224700 s h1). Qed.
Lemma lem5224704 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term208 x s a) : term252 s.
Proof. exact (@lem5224701 s h1 (@lem5224698 x s a h2)). Qed.
Lemma lem5224705 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term208 x s a) : term380 s.
Proof. exact (fun h0 : term381 s => @lem5224704 x s a h1 h2). Qed.
Lemma lem5224707 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5224708 (s : real -> Prop) : (term380 s) = (term252 s).
Proof. exact (@lem5224707 (term252 s)). Qed.
Lemma lem5224709 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term208 x s a) : term252 s.
Proof. exact (EQ_MP (@lem5224708 s) (@lem5224705 x s a h1 h2)). Qed.
Lemma lem5224715 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5224716 (a : real) (_68372 : real) (s : real -> Prop) : (term49 s a _68372) = (term382 a _68372 s).
Proof. exact (@lem5224715 (real_le a _68372) (term307 _68372 s)). Qed.
Lemma lem5224722 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5224723 (a : real) (_68372 : real) (s : real -> Prop) : (term383 s a _68372) = (term384 a _68372 s).
Proof. exact (MK_COMB (@lem5224722) (@lem5224716 a _68372 s)). Qed.
Lemma lem5224729 (a : real) (_68372 : real) (s : real -> Prop) : (term382 a _68372 s) = (term382 a _68372 s).
Proof. exact (eq_refl (term382 a _68372 s)). Qed.
Lemma lem5224730 (a : real) (_68372 : real) (s : real -> Prop) : ((term49 s a _68372) = (term382 a _68372 s)) = ((term382 a _68372 s) = (term382 a _68372 s)).
Proof. exact (MK_COMB (@lem5224723 a _68372 s) (@lem5224729 a _68372 s)). Qed.
Lemma lem5224732 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5224733 (x : Prop) : (x = x) = True.
Proof. exact (@lem5224732 Prop x). Qed.
Lemma lem5224734 (a : real) (_68372 : real) (s : real -> Prop) : ((term382 a _68372 s) = (term382 a _68372 s)) = True.
Proof. exact (@lem5224733 (term382 a _68372 s)). Qed.
Lemma lem5224735 (a : real) (_68372 : real) (s : real -> Prop) : ((term49 s a _68372) = (term382 a _68372 s)) = True.
Proof. exact (TRANS (@lem5224730 a _68372 s) (@lem5224734 a _68372 s)). Qed.
Lemma lem5224736 (a : real) (_68372 : real) (s : real -> Prop) : True = ((term49 s a _68372) = (term382 a _68372 s)).
Proof. exact (SYM (@lem5224735 a _68372 s)). Qed.
Lemma lem5224737 (a : real) (_68372 : real) (s : real -> Prop) : (term49 s a _68372) = (term382 a _68372 s).
Proof. exact (EQ_MP (@lem5224736 a _68372 s) (@lem0)). Qed.
Lemma lem5224738 (_68372 : real) (s : real -> Prop) (a : real) (h1 : term63 s a) : term382 a _68372 s.
Proof. exact (EQ_MP (@lem5224737 a _68372 s) (@lem5224067 _68372 s a h1)). Qed.
Lemma lem5224740 (b : Prop) (a : Prop) : (a \/ b) = (term323 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5224741 (s : real -> Prop) (a : real) (_68372 : real) : (term382 a _68372 s) = (term385 s a _68372).
Proof. exact (@lem5224740 (term307 _68372 s) (real_le a _68372)). Qed.
Lemma lem5224743 (a : Prop) : (term330 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5224744 (_68372 : real) (s : real -> Prop) : (term336 _68372 s) = (@IN real _68372 s).
Proof. exact (@lem5224743 (@IN real _68372 s)). Qed.
Lemma lem5224745 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5224746 (_68372 : real) (s : real -> Prop) : (term386 _68372 s) = (term387 _68372 s).
Proof. exact (MK_COMB (@lem5224745) (@lem5224744 _68372 s)). Qed.
Lemma lem5224747 (a : real) (_68372 : real) : (real_le a _68372) = (real_le a _68372).
Proof. exact (eq_refl (real_le a _68372)). Qed.
Lemma lem5224748 (s : real -> Prop) (a : real) (_68372 : real) : (term385 s a _68372) = (term38 s a _68372).
Proof. exact (MK_COMB (@lem5224746 _68372 s) (@lem5224747 a _68372)). Qed.
Lemma lem5224749 (s : real -> Prop) (a : real) (_68372 : real) : (term382 a _68372 s) = (term38 s a _68372).
Proof. exact (TRANS (@lem5224741 s a _68372) (@lem5224748 s a _68372)). Qed.
Lemma lem5224752 (_68372 : real) (s : real -> Prop) (a : real) (h1 : term63 s a) : term38 s a _68372.
Proof. exact (EQ_MP (@lem5224749 s a _68372) (@lem5224738 _68372 s a h1)). Qed.
Lemma lem5224753 (s : real -> Prop) (a : real) (h1 : term63 s a) : term388 a s.
Proof. exact (@lem5224752 (inf s) s a h1). Qed.
Lemma lem5224756 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term63 s a) (h3 : term208 x s a) : term42 a s.
Proof. exact (@lem5224753 s a h2 (@lem5224709 x s a h1 h3)). Qed.
Lemma lem5224757 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term63 s a) (h3 : term208 x s a) : term301 a s.
Proof. exact (fun h0 : term299 a s => @lem5224756 x s a h1 h2 h3). Qed.
Lemma lem5224759 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5224760 (a : real) (s : real -> Prop) : (term301 a s) = (term42 a s).
Proof. exact (@lem5224759 (term42 a s)). Qed.
Lemma lem5224761 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term63 s a) (h3 : term208 x s a) : term42 a s.
Proof. exact (EQ_MP (@lem5224760 a s) (@lem5224757 x s a h1 h2 h3)). Qed.
Lemma lem5224764 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5224766 (a : real) (s : real -> Prop) : (term299 a s) = (term389 a s).
Proof. exact (@lem5224764 (term42 a s)). Qed.
Lemma lem5224769 (s : real -> Prop) (a : real) (h1 : term63 s a) : term389 a s.
Proof. exact (EQ_MP (@lem5224766 a s) (@lem5224061 s a h1)). Qed.
Lemma lem5224772 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term63 s a) (h3 : term208 x s a) : False.
Proof. exact (@lem5224769 s a h2 (@lem5224761 x s a h1 h2 h3)). Qed.
Lemma lem5224773 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term63 s a) (h3 : term208 x s a) : term364.
Proof. exact (fun h0 : ~ False => @lem5224772 x s a h1 h2 h3). Qed.
Lemma lem5224775 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5224776 : term364 = False.
Proof. exact (@lem5224775 False). Qed.
Lemma lem5224777 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term63 s a) (h3 : term208 x s a) : False.
Proof. exact (EQ_MP (@lem5224776) (@lem5224773 x s a h1 h2 h3)). Qed.
Lemma lem5224778 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) : False.
Proof. exact (or_elim (@lem5223684 x s a h3) (fun h0 : term143 s a x => @lem5224501 s a x h1 h2 h3 h0) (fun h0 : term63 s a => @lem5224777 x s a h1 h0 h3)). Qed.
Lemma lem5224779 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) : (term208 x s a) = False.
Proof. exact (prop_ext (fun h4 : term208 x s a => @lem5224778 x s a h1 h2 h3) (fun h4 : False => @lem5223683 x s a h3)). Qed.
Lemma lem5224780 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) : False.
Proof. exact (EQ_MP (@lem5224779 x s a h1 h2 h3) (@lem5223683 x s a h3)). Qed.
Lemma lem5224781 (s : real -> Prop) (a : real) (h1 : term17) (h2 : term37) (h3 : term211 s a) : False.
Proof. exact (ex_elim (@lem5223522 s a h3) (fun x : real => fun h0 : term210 s a x => @lem5224780 x s a h1 h2 h0)). Qed.
Lemma lem5224782 (s : real -> Prop) (h1 : term17) (h2 : term37) (h3 : term213 s) : False.
Proof. exact (ex_elim (@lem5223521 s h3) (fun a : real => fun h0 : term212 s a => @lem5224781 s a h1 h2 h0)). Qed.
Lemma lem5224783 (h1 : term17) (h2 : term37) (h3 : term10) : False.
Proof. exact (ex_elim (@lem5223305 h3) (fun s : real -> Prop => fun h0 : term214 s => @lem5224782 s h1 h2 h0)). Qed.
Lemma lem5224784 (h1 : term37) (h2 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem5224783 h0 h1 h2). Qed.
Lemma lem5224785 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem5224786 (h1 : term37) (h2 : term10) : term16.
Proof. exact (EQ_MP (@lem5224785) (@lem5224784 h1 h2)). Qed.
Lemma lem5224787 (h1 : term10) : term20.
Proof. exact (fun h0 : term37 => @lem5224786 h0 h1). Qed.
Lemma lem5224788 : term22.
Proof. exact (fun h0 : term10 => @lem5224787 h0). Qed.
Lemma lem5224789 : term11.
Proof. exact (EQ_MP (@lem5222799) (@lem5224788)). Qed.
Lemma lem5224791 : term11.
Proof. exact (@lem5222575 (@lem5224789)). Qed.
Lemma lem5224792 (h1 : term10) : term19.
Proof. exact (@lem5224791 (@lem5222560 h1)). Qed.
Lemma lem5224793 (h1 : term10) : term15.
Proof. exact (@lem5224792 h1 (@lem1339577)). Qed.
Lemma lem5224794 (h1 : term10) : False.
Proof. exact (@lem5224793 h1 (@lem5222545)). Qed.
Lemma lem5224795 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem5224794 h1) (fun h2 : False => @lem5222560 h1)). Qed.
Lemma lem5224796 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem5224795 h1) (@lem5222560 h1)). Qed.
Lemma lem5224797 : term9.
Proof. exact (fun h0 : term10 => @lem5224796 h0). Qed.
Lemma lem5224798 : term8.
Proof. exact (EQ_MP (@lem5222559) (@lem5224797)). Qed.
