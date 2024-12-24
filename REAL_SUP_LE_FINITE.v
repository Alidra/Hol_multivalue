Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUP_LE_FINITE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import SUP_FINITE_spec.
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
Lemma lem5147522 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5147523 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5147524 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5147523 t1) (@lem5147522 t1)). Qed.
Lemma lem5147525 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5147524 t1 t2). Qed.
Lemma lem5147526 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5147527 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5147526 t1 t2) (@lem5147525 t1 t2)). Qed.
Lemma lem5147528 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5147527 t1 t2 t3). Qed.
Lemma lem5147529 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5147530 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5147529 t1 t2 t3) (@lem5147528 t1 t2 t3)). Qed.
Lemma lem5147531 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5147530 t1 t2 t3)). Qed.
Lemma lem5147533 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5147534 : term8 = term9.
Proof. exact (@lem5147533 term8). Qed.
Lemma lem5147535 : term9 = term8.
Proof. exact (SYM (@lem5147534)). Qed.
Lemma lem5147536 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5147539 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5147540 : term12.
Proof. exact (fun h0 : term11 => @lem5147539 h0). Qed.
Lemma lem5147541 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5147542 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5147543 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem5147541 h2 (@lem5147542 h1)). Qed.
Lemma lem5147544 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem5147543 h1 h0). Qed.
Lemma lem5147545 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5147546 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem5147544 h1 (@lem5147545 h2)). Qed.
Lemma lem5147547 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem5147546 h0 h1). Qed.
Lemma lem5147548 : term14.
Proof. exact (fun h0 : term12 => @lem5147547 h0). Qed.
Lemma lem5147551 : term12.
Proof. exact (@lem5147548 (@lem5147540)). Qed.
Lemma lem5147591 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5147592 : term15 = term16.
Proof. exact (@lem5147591 term17). Qed.
Lemma lem5147609 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem5147610 : term19 = term20.
Proof. exact (MK_COMB (@lem5147609) (@lem5147592)). Qed.
Lemma lem5147613 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem5147620 : term11 = term22.
Proof. exact (MK_COMB (@lem5147613) (@lem5147610)). Qed.
Lemma lem5147625 (x : real) (s : real -> Prop) : (term23 x s) = (term23 x s).
Proof. exact (eq_refl (term23 x s)). Qed.
Lemma lem5147626 (s : real -> Prop) : (term24 s) = (term24 s).
Proof. exact (fun_ext (fun x : real => @lem5147625 x s)). Qed.
Lemma lem5147627 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5147628 (s : real -> Prop) : (term25 s) = (term25 s).
Proof. exact (MK_COMB (@lem5147627) (@lem5147626 s)). Qed.
Lemma lem5147631 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5147632 (s : real -> Prop) : (term27 s) = (term27 s).
Proof. exact (MK_COMB (@lem5147631 s) (@lem5147628 s)). Qed.
Lemma lem5147641 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5147642 (s : real -> Prop) : (term29 s) = (term29 s).
Proof. exact (MK_COMB (@lem5147641 s) (@lem5147632 s)). Qed.
Lemma lem5147643 : term30 = term30.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5147642 s)). Qed.
Lemma lem5147644 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5147645 : term17 = term17.
Proof. exact (MK_COMB (@lem5147644) (@lem5147643)). Qed.
Lemma lem5147646 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5147647 : term16 = term16.
Proof. exact (MK_COMB (@lem5147646) (@lem5147645)). Qed.
Lemma lem5147656 (y : real) (x : real) (z : real) : (term31 y x z) = (term31 y x z).
Proof. exact (eq_refl (term31 y x z)). Qed.
Lemma lem5147657 (y : real) (x : real) : (term32 y x) = (term32 y x).
Proof. exact (fun_ext (fun z : real => @lem5147656 y x z)). Qed.
Lemma lem5147658 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5147659 (y : real) (x : real) : (term33 y x) = (term33 y x).
Proof. exact (MK_COMB (@lem5147658) (@lem5147657 y x)). Qed.
Lemma lem5147660 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem5147659 y x)). Qed.
Lemma lem5147661 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5147662 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem5147661) (@lem5147660 x)). Qed.
Lemma lem5147663 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem5147662 x)). Qed.
Lemma lem5147664 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5147665 : term37 = term37.
Proof. exact (MK_COMB (@lem5147664) (@lem5147663)). Qed.
Lemma lem5147666 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5147667 : term18 = term18.
Proof. exact (MK_COMB (@lem5147666) (@lem5147665)). Qed.
Lemma lem5147668 : term20 = term20.
Proof. exact (MK_COMB (@lem5147667) (@lem5147647)). Qed.
Lemma lem5147673 (s : real -> Prop) (x : real) (a : real) : (term38 s x a) = (term38 s x a).
Proof. exact (eq_refl (term38 s x a)). Qed.
Lemma lem5147674 (s : real -> Prop) (a : real) : (term39 s a) = (term39 s a).
Proof. exact (fun_ext (fun x : real => @lem5147673 s x a)). Qed.
Lemma lem5147675 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5147676 (s : real -> Prop) (a : real) : (term40 s a) = (term40 s a).
Proof. exact (MK_COMB (@lem5147675) (@lem5147674 s a)). Qed.
Lemma lem5147679 (s : real -> Prop) (a : real) : (term41 s a) = (term41 s a).
Proof. exact (eq_refl (term41 s a)). Qed.
Lemma lem5147680 (s : real -> Prop) (a : real) : ((term42 s a) = (term40 s a)) = ((term42 s a) = (term40 s a)).
Proof. exact (MK_COMB (@lem5147679 s a) (@lem5147676 s a)). Qed.
Lemma lem5147689 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5147690 (s : real -> Prop) (a : real) : (term43 s a) = (term43 s a).
Proof. exact (MK_COMB (@lem5147689 s) (@lem5147680 s a)). Qed.
Lemma lem5147691 (s : real -> Prop) : (term44 s) = (term44 s).
Proof. exact (fun_ext (fun a : real => @lem5147690 s a)). Qed.
Lemma lem5147692 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5147693 (s : real -> Prop) : (term45 s) = (term45 s).
Proof. exact (MK_COMB (@lem5147692) (@lem5147691 s)). Qed.
Lemma lem5147694 : term46 = term46.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5147693 s)). Qed.
Lemma lem5147695 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5147696 : term8 = term8.
Proof. exact (MK_COMB (@lem5147695) (@lem5147694)). Qed.
Lemma lem5147697 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5147698 : term10 = term10.
Proof. exact (MK_COMB (@lem5147697) (@lem5147696)). Qed.
Lemma lem5147699 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5147700 : term21 = term21.
Proof. exact (MK_COMB (@lem5147699) (@lem5147698)). Qed.
Lemma lem5147701 : term22 = term22.
Proof. exact (MK_COMB (@lem5147700) (@lem5147668)). Qed.
Lemma lem5147774 : term11 = term22.
Proof. exact (TRANS (@lem5147620) (@lem5147701)). Qed.
Lemma lem5147775 : term22 = term11.
Proof. exact (SYM (@lem5147774)). Qed.
Lemma lem5147776 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5147777 (h1 : term37) : term37.
Proof. exact (h1). Qed.
Lemma lem5147778 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem5147794 (s : real -> Prop) (x : real) (a : real) : (term47 s x a) = (term48 s x a).
Proof. exact (@lem17362 (@IN real x s) (real_le x a)). Qed.
Lemma lem5147799 (s : real -> Prop) (x : real) (a : real) : (term38 s x a) = (term49 s x a).
Proof. exact (@lem17265 (@IN real x s) (real_le x a)). Qed.
Lemma lem5147800 (P : real -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5147801 (s : real -> Prop) (a : real) : (term52 s a) = (term53 s a).
Proof. exact (@lem5147800 (term39 s a)). Qed.
Lemma lem5147802 (s : real -> Prop) (x : real) (a : real) : (term54 s a x) = (term38 s x a).
Proof. exact (eq_refl (term54 s a x)). Qed.
Lemma lem5147803 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5147804 (s : real -> Prop) (x : real) (a : real) : (term55 s a x) = (term47 s x a).
Proof. exact (MK_COMB (@lem5147803) (@lem5147802 s x a)). Qed.
Lemma lem5147805 (s : real -> Prop) (x : real) (a : real) : (term55 s a x) = (term48 s x a).
Proof. exact (TRANS (@lem5147804 s x a) (@lem5147794 s x a)). Qed.
Lemma lem5147806 (s : real -> Prop) (a : real) : (term56 s a) = (term57 s a).
Proof. exact (fun_ext (fun x : real => @lem5147805 s x a)). Qed.
Lemma lem5147807 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5147808 (s : real -> Prop) (a : real) : (term53 s a) = (term58 s a).
Proof. exact (MK_COMB (@lem5147807) (@lem5147806 s a)). Qed.
Lemma lem5147809 (s : real -> Prop) (a : real) : (term52 s a) = (term58 s a).
Proof. exact (TRANS (@lem5147801 s a) (@lem5147808 s a)). Qed.
Lemma lem5147810 (s : real -> Prop) (a : real) : (term39 s a) = (term59 s a).
Proof. exact (fun_ext (fun x : real => @lem5147799 s x a)). Qed.
Lemma lem5147811 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5147812 (s : real -> Prop) (a : real) : (term40 s a) = (term60 s a).
Proof. exact (MK_COMB (@lem5147811) (@lem5147810 s a)). Qed.
Lemma lem5147814 (s : real -> Prop) (a : real) : (term61 s a) = (term61 s a).
Proof. exact (eq_refl (term61 s a)). Qed.
Lemma lem5147815 (s : real -> Prop) (a : real) : (term62 s a) = (term63 s a).
Proof. exact (MK_COMB (@lem5147814 s a) (@lem5147812 s a)). Qed.
Lemma lem5147817 (s : real -> Prop) (a : real) : (term64 s a) = (term64 s a).
Proof. exact (eq_refl (term64 s a)). Qed.
Lemma lem5147818 (s : real -> Prop) (a : real) : (term65 s a) = (term66 s a).
Proof. exact (MK_COMB (@lem5147817 s a) (@lem5147809 s a)). Qed.
Lemma lem5147819 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5147820 (s : real -> Prop) (a : real) : (term67 s a) = (term68 s a).
Proof. exact (MK_COMB (@lem5147819) (@lem5147818 s a)). Qed.
Lemma lem5147821 (s : real -> Prop) (a : real) : (term69 s a) = (term70 s a).
Proof. exact (MK_COMB (@lem5147820 s a) (@lem5147815 s a)). Qed.
Lemma lem5147822 (s : real -> Prop) (a : real) : (term71 s a) = (term69 s a).
Proof. exact (@lem17646 (term42 s a) (term40 s a)). Qed.
Lemma lem5147823 (s : real -> Prop) (a : real) : (term71 s a) = (term70 s a).
Proof. exact (TRANS (@lem5147822 s a) (@lem5147821 s a)). Qed.
Lemma lem5147825 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5147826 (s : real -> Prop) (a : real) : (term73 s a) = (term74 s a).
Proof. exact (MK_COMB (@lem5147825 s) (@lem5147823 s a)). Qed.
Lemma lem5147827 (s : real -> Prop) (a : real) : (term75 s a) = (term73 s a).
Proof. exact (@lem17362 (term76 s) ((term42 s a) = (term40 s a))). Qed.
Lemma lem5147828 (s : real -> Prop) (a : real) : (term75 s a) = (term74 s a).
Proof. exact (TRANS (@lem5147827 s a) (@lem5147826 s a)). Qed.
Lemma lem5147829 (P : real -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5147830 (s : real -> Prop) : (term77 s) = (term78 s).
Proof. exact (@lem5147829 (term44 s)). Qed.
Lemma lem5147831 (s : real -> Prop) (a : real) : (term79 s a) = (term43 s a).
Proof. exact (eq_refl (term79 s a)). Qed.
Lemma lem5147832 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5147833 (s : real -> Prop) (a : real) : (term80 s a) = (term75 s a).
Proof. exact (MK_COMB (@lem5147832) (@lem5147831 s a)). Qed.
Lemma lem5147834 (s : real -> Prop) (a : real) : (term80 s a) = (term74 s a).
Proof. exact (TRANS (@lem5147833 s a) (@lem5147828 s a)). Qed.
Lemma lem5147835 (s : real -> Prop) : (term81 s) = (term82 s).
Proof. exact (fun_ext (fun a : real => @lem5147834 s a)). Qed.
Lemma lem5147836 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5147837 (s : real -> Prop) : (term78 s) = (term83 s).
Proof. exact (MK_COMB (@lem5147836) (@lem5147835 s)). Qed.
Lemma lem5147838 (s : real -> Prop) : (term77 s) = (term83 s).
Proof. exact (TRANS (@lem5147830 s) (@lem5147837 s)). Qed.
Lemma lem5147839 (P : type1022) : (term84 P) = (term85 P).
Proof. exact (@lem18392 (real -> Prop) P). Qed.
Lemma lem5147840 : term10 = term86.
Proof. exact (@lem5147839 term46). Qed.
Lemma lem5147841 (s : real -> Prop) : (term87 s) = (term45 s).
Proof. exact (eq_refl (term87 s)). Qed.
Lemma lem5147842 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5147843 (s : real -> Prop) : (term88 s) = (term77 s).
Proof. exact (MK_COMB (@lem5147842) (@lem5147841 s)). Qed.
Lemma lem5147844 (s : real -> Prop) : (term88 s) = (term83 s).
Proof. exact (TRANS (@lem5147843 s) (@lem5147838 s)). Qed.
Lemma lem5147845 : term89 = term90.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5147844 s)). Qed.
Lemma lem5147846 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5147847 : term86 = term91.
Proof. exact (MK_COMB (@lem5147846) (@lem5147845)). Qed.
Lemma lem5147848 : term10 = term91.
Proof. exact (TRANS (@lem5147840) (@lem5147847)). Qed.
Lemma lem5147854 {A : Type'} (P : Prop) (Q : A -> Prop) : (term92 A P Q) = (term93 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem5147855 (P : Prop) (Q : real -> Prop) : (term94 P Q) = (term95 P Q).
Proof. exact (@lem5147854 real P Q). Qed.
Lemma lem5147856 (s : real -> Prop) : (term96 s) = (term97 s).
Proof. exact (@lem5147855 (term76 s) (term98 s)). Qed.
Lemma lem5147857 (s : real -> Prop) (a : real) : (term99 s a) = (term70 s a).
Proof. exact (eq_refl (term99 s a)). Qed.
Lemma lem5147858 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5147859 (s : real -> Prop) (a : real) : (term100 s a) = (term74 s a).
Proof. exact (MK_COMB (@lem5147858 s) (@lem5147857 s a)). Qed.
Lemma lem5147860 (s : real -> Prop) : (term101 s) = (term82 s).
Proof. exact (fun_ext (fun a : real => @lem5147859 s a)). Qed.
Lemma lem5147861 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5147862 (s : real -> Prop) : (term96 s) = (term83 s).
Proof. exact (MK_COMB (@lem5147861) (@lem5147860 s)). Qed.
Lemma lem5147863 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5147864 (s : real -> Prop) : (term102 s) = (term103 s).
Proof. exact (MK_COMB (@lem5147863) (@lem5147862 s)). Qed.
Lemma lem5147865 (s : real -> Prop) (a : real) : (term99 s a) = (term70 s a).
Proof. exact (eq_refl (term99 s a)). Qed.
Lemma lem5147866 (s : real -> Prop) : (term104 s) = (term98 s).
Proof. exact (fun_ext (fun a : real => @lem5147865 s a)). Qed.
Lemma lem5147867 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5147868 (s : real -> Prop) : (term105 s) = (term106 s).
Proof. exact (MK_COMB (@lem5147867) (@lem5147866 s)). Qed.
Lemma lem5147869 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5147870 (s : real -> Prop) : (term97 s) = (term107 s).
Proof. exact (MK_COMB (@lem5147869 s) (@lem5147868 s)). Qed.
Lemma lem5147871 (s : real -> Prop) : ((term96 s) = (term97 s)) = ((term83 s) = (term107 s)).
Proof. exact (MK_COMB (@lem5147864 s) (@lem5147870 s)). Qed.
Lemma lem5147872 (s : real -> Prop) : (term83 s) = (term107 s).
Proof. exact (EQ_MP (@lem5147871 s) (@lem5147856 s)). Qed.
Lemma lem5147874 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5147875 (P : real -> Prop) (Q : real -> Prop) : (term110 P Q) = (term111 P Q).
Proof. exact (@lem5147874 real P Q). Qed.
Lemma lem5147876 (s : real -> Prop) : (term112 s) = (term113 s).
Proof. exact (@lem5147875 (term114 s) (term115 s)). Qed.
Lemma lem5147877 (s : real -> Prop) (a : real) : (term116 s a) = (term66 s a).
Proof. exact (eq_refl (term116 s a)). Qed.
Lemma lem5147878 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5147879 (s : real -> Prop) (a : real) : (term117 s a) = (term68 s a).
Proof. exact (MK_COMB (@lem5147878) (@lem5147877 s a)). Qed.
Lemma lem5147880 (s : real -> Prop) (a : real) : (term118 s a) = (term63 s a).
Proof. exact (eq_refl (term118 s a)). Qed.
Lemma lem5147881 (s : real -> Prop) (a : real) : (term119 s a) = (term70 s a).
Proof. exact (MK_COMB (@lem5147879 s a) (@lem5147880 s a)). Qed.
Lemma lem5147882 (s : real -> Prop) : (term120 s) = (term98 s).
Proof. exact (fun_ext (fun a : real => @lem5147881 s a)). Qed.
Lemma lem5147883 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5147884 (s : real -> Prop) : (term112 s) = (term106 s).
Proof. exact (MK_COMB (@lem5147883) (@lem5147882 s)). Qed.
Lemma lem5147885 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5147886 (s : real -> Prop) : (term121 s) = (term122 s).
Proof. exact (MK_COMB (@lem5147885) (@lem5147884 s)). Qed.
Lemma lem5147887 (s : real -> Prop) (a : real) : (term116 s a) = (term66 s a).
Proof. exact (eq_refl (term116 s a)). Qed.
Lemma lem5147888 (s : real -> Prop) : (term123 s) = (term114 s).
Proof. exact (fun_ext (fun a : real => @lem5147887 s a)). Qed.
Lemma lem5147889 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5147890 (s : real -> Prop) : (term124 s) = (term125 s).
Proof. exact (MK_COMB (@lem5147889) (@lem5147888 s)). Qed.
Lemma lem5147891 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5147892 (s : real -> Prop) : (term126 s) = (term127 s).
Proof. exact (MK_COMB (@lem5147891) (@lem5147890 s)). Qed.
Lemma lem5147893 (s : real -> Prop) (a : real) : (term118 s a) = (term63 s a).
Proof. exact (eq_refl (term118 s a)). Qed.
Lemma lem5147894 (s : real -> Prop) : (term128 s) = (term115 s).
Proof. exact (fun_ext (fun a : real => @lem5147893 s a)). Qed.
Lemma lem5147895 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5147896 (s : real -> Prop) : (term129 s) = (term130 s).
Proof. exact (MK_COMB (@lem5147895) (@lem5147894 s)). Qed.
Lemma lem5147897 (s : real -> Prop) : (term113 s) = (term131 s).
Proof. exact (MK_COMB (@lem5147892 s) (@lem5147896 s)). Qed.
Lemma lem5147898 (s : real -> Prop) : ((term112 s) = (term113 s)) = ((term106 s) = (term131 s)).
Proof. exact (MK_COMB (@lem5147886 s) (@lem5147897 s)). Qed.
Lemma lem5147899 (s : real -> Prop) : (term106 s) = (term131 s).
Proof. exact (EQ_MP (@lem5147898 s) (@lem5147876 s)). Qed.
Lemma lem5148092 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5148093 (s : real -> Prop) : (term107 s) = (term132 s).
Proof. exact (MK_COMB (@lem5148092 s) (@lem5147899 s)). Qed.
Lemma lem5148094 (s : real -> Prop) : (term83 s) = (term132 s).
Proof. exact (TRANS (@lem5147872 s) (@lem5148093 s)). Qed.
Lemma lem5148095 : term90 = term133.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5148094 s)). Qed.
Lemma lem5148096 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5148097 : term91 = term134.
Proof. exact (MK_COMB (@lem5148096) (@lem5148095)). Qed.
Lemma lem5148147 {A : Type'} (P : Prop) (Q : A -> Prop) : (term93 A P Q) = (term92 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5148148 (P : Prop) (Q : real -> Prop) : (term95 P Q) = (term94 P Q).
Proof. exact (@lem5148147 real P Q). Qed.
Lemma lem5148149 (s : real -> Prop) (a : real) : (term135 s a) = (term136 s a).
Proof. exact (@lem5148148 (term42 s a) (term57 s a)). Qed.
Lemma lem5148150 (s : real -> Prop) (x : real) (a : real) : (term137 s a x) = (term48 s x a).
Proof. exact (eq_refl (term137 s a x)). Qed.
Lemma lem5148151 (s : real -> Prop) (a : real) : (term138 s a) = (term57 s a).
Proof. exact (fun_ext (fun x : real => @lem5148150 s x a)). Qed.
Lemma lem5148152 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5148153 (s : real -> Prop) (a : real) : (term139 s a) = (term58 s a).
Proof. exact (MK_COMB (@lem5148152) (@lem5148151 s a)). Qed.
Lemma lem5148154 (s : real -> Prop) (a : real) : (term64 s a) = (term64 s a).
Proof. exact (eq_refl (term64 s a)). Qed.
Lemma lem5148155 (s : real -> Prop) (a : real) : (term135 s a) = (term66 s a).
Proof. exact (MK_COMB (@lem5148154 s a) (@lem5148153 s a)). Qed.
Lemma lem5148156 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5148157 (s : real -> Prop) (a : real) : (term140 s a) = (term141 s a).
Proof. exact (MK_COMB (@lem5148156) (@lem5148155 s a)). Qed.
Lemma lem5148158 (s : real -> Prop) (x : real) (a : real) : (term137 s a x) = (term48 s x a).
Proof. exact (eq_refl (term137 s a x)). Qed.
Lemma lem5148159 (s : real -> Prop) (a : real) : (term64 s a) = (term64 s a).
Proof. exact (eq_refl (term64 s a)). Qed.
Lemma lem5148160 (s : real -> Prop) (x : real) (a : real) : (term142 s a x) = (term143 s x a).
Proof. exact (MK_COMB (@lem5148159 s a) (@lem5148158 s x a)). Qed.
Lemma lem5148161 (s : real -> Prop) (a : real) : (term144 s a) = (term145 s a).
Proof. exact (fun_ext (fun x : real => @lem5148160 s x a)). Qed.
Lemma lem5148162 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5148163 (s : real -> Prop) (a : real) : (term136 s a) = (term146 s a).
Proof. exact (MK_COMB (@lem5148162) (@lem5148161 s a)). Qed.
Lemma lem5148164 (s : real -> Prop) (a : real) : ((term135 s a) = (term136 s a)) = ((term66 s a) = (term146 s a)).
Proof. exact (MK_COMB (@lem5148157 s a) (@lem5148163 s a)). Qed.
Lemma lem5148165 (s : real -> Prop) (a : real) : (term66 s a) = (term146 s a).
Proof. exact (EQ_MP (@lem5148164 s a) (@lem5148149 s a)). Qed.
Lemma lem5148166 (s : real -> Prop) : (term114 s) = (term147 s).
Proof. exact (fun_ext (fun a : real => @lem5148165 s a)). Qed.
Lemma lem5148167 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5148168 (s : real -> Prop) : (term125 s) = (term148 s).
Proof. exact (MK_COMB (@lem5148167) (@lem5148166 s)). Qed.
Lemma lem5148169 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5148170 (s : real -> Prop) : (term127 s) = (term149 s).
Proof. exact (MK_COMB (@lem5148169) (@lem5148168 s)). Qed.
Lemma lem5148171 (s : real -> Prop) : (term130 s) = (term130 s).
Proof. exact (eq_refl (term130 s)). Qed.
Lemma lem5148172 (s : real -> Prop) : (term131 s) = (term150 s).
Proof. exact (MK_COMB (@lem5148170 s) (@lem5148171 s)). Qed.
Lemma lem5148174 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term109 A P Q) = (term108 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5148175 (P : real -> Prop) (Q : real -> Prop) : (term111 P Q) = (term110 P Q).
Proof. exact (@lem5148174 real P Q). Qed.
Lemma lem5148176 (s : real -> Prop) : (term151 s) = (term152 s).
Proof. exact (@lem5148175 (term147 s) (term115 s)). Qed.
Lemma lem5148177 (s : real -> Prop) (a : real) : (term153 s a) = (term146 s a).
Proof. exact (eq_refl (term153 s a)). Qed.
Lemma lem5148178 (s : real -> Prop) : (term154 s) = (term147 s).
Proof. exact (fun_ext (fun a : real => @lem5148177 s a)). Qed.
Lemma lem5148179 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5148180 (s : real -> Prop) : (term155 s) = (term148 s).
Proof. exact (MK_COMB (@lem5148179) (@lem5148178 s)). Qed.
Lemma lem5148181 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5148182 (s : real -> Prop) : (term156 s) = (term149 s).
Proof. exact (MK_COMB (@lem5148181) (@lem5148180 s)). Qed.
Lemma lem5148183 (s : real -> Prop) (a : real) : (term118 s a) = (term63 s a).
Proof. exact (eq_refl (term118 s a)). Qed.
Lemma lem5148184 (s : real -> Prop) : (term128 s) = (term115 s).
Proof. exact (fun_ext (fun a : real => @lem5148183 s a)). Qed.
Lemma lem5148185 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5148186 (s : real -> Prop) : (term129 s) = (term130 s).
Proof. exact (MK_COMB (@lem5148185) (@lem5148184 s)). Qed.
Lemma lem5148187 (s : real -> Prop) : (term151 s) = (term150 s).
Proof. exact (MK_COMB (@lem5148182 s) (@lem5148186 s)). Qed.
Lemma lem5148188 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5148189 (s : real -> Prop) : (term157 s) = (term158 s).
Proof. exact (MK_COMB (@lem5148188) (@lem5148187 s)). Qed.
Lemma lem5148190 (s : real -> Prop) (a : real) : (term153 s a) = (term146 s a).
Proof. exact (eq_refl (term153 s a)). Qed.
Lemma lem5148191 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5148192 (s : real -> Prop) (a : real) : (term159 s a) = (term160 s a).
Proof. exact (MK_COMB (@lem5148191) (@lem5148190 s a)). Qed.
Lemma lem5148193 (s : real -> Prop) (a : real) : (term118 s a) = (term63 s a).
Proof. exact (eq_refl (term118 s a)). Qed.
Lemma lem5148194 (s : real -> Prop) (a : real) : (term161 s a) = (term162 s a).
Proof. exact (MK_COMB (@lem5148192 s a) (@lem5148193 s a)). Qed.
Lemma lem5148195 (s : real -> Prop) : (term163 s) = (term164 s).
Proof. exact (fun_ext (fun a : real => @lem5148194 s a)). Qed.
Lemma lem5148196 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5148197 (s : real -> Prop) : (term152 s) = (term165 s).
Proof. exact (MK_COMB (@lem5148196) (@lem5148195 s)). Qed.
Lemma lem5148198 (s : real -> Prop) : ((term151 s) = (term152 s)) = ((term150 s) = (term165 s)).
Proof. exact (MK_COMB (@lem5148189 s) (@lem5148197 s)). Qed.
Lemma lem5148199 (s : real -> Prop) : (term150 s) = (term165 s).
Proof. exact (EQ_MP (@lem5148198 s) (@lem5148176 s)). Qed.
Lemma lem5148201 {A : Type'} (P : A -> Prop) (Q : Prop) : (term166 A P Q) = (term167 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5148202 (P : real -> Prop) (Q : Prop) : (term168 P Q) = (term169 P Q).
Proof. exact (@lem5148201 real P Q). Qed.
Lemma lem5148203 (s : real -> Prop) (a : real) : (term170 s a) = (term171 s a).
Proof. exact (@lem5148202 (term145 s a) (term63 s a)). Qed.
Lemma lem5148204 (s : real -> Prop) (x : real) (a : real) : (term172 s a x) = (term143 s x a).
Proof. exact (eq_refl (term172 s a x)). Qed.
Lemma lem5148205 (s : real -> Prop) (a : real) : (term173 s a) = (term145 s a).
Proof. exact (fun_ext (fun x : real => @lem5148204 s x a)). Qed.
Lemma lem5148206 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5148207 (s : real -> Prop) (a : real) : (term174 s a) = (term146 s a).
Proof. exact (MK_COMB (@lem5148206) (@lem5148205 s a)). Qed.
Lemma lem5148208 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5148209 (s : real -> Prop) (a : real) : (term175 s a) = (term160 s a).
Proof. exact (MK_COMB (@lem5148208) (@lem5148207 s a)). Qed.
Lemma lem5148210 (s : real -> Prop) (a : real) : (term63 s a) = (term63 s a).
Proof. exact (eq_refl (term63 s a)). Qed.
Lemma lem5148211 (s : real -> Prop) (a : real) : (term170 s a) = (term162 s a).
Proof. exact (MK_COMB (@lem5148209 s a) (@lem5148210 s a)). Qed.
Lemma lem5148212 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5148213 (s : real -> Prop) (a : real) : (term176 s a) = (term177 s a).
Proof. exact (MK_COMB (@lem5148212) (@lem5148211 s a)). Qed.
Lemma lem5148214 (s : real -> Prop) (x : real) (a : real) : (term172 s a x) = (term143 s x a).
Proof. exact (eq_refl (term172 s a x)). Qed.
Lemma lem5148215 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5148216 (s : real -> Prop) (x : real) (a : real) : (term178 s a x) = (term179 s x a).
Proof. exact (MK_COMB (@lem5148215) (@lem5148214 s x a)). Qed.
Lemma lem5148217 (s : real -> Prop) (a : real) : (term63 s a) = (term63 s a).
Proof. exact (eq_refl (term63 s a)). Qed.
Lemma lem5148218 (x : real) (s : real -> Prop) (a : real) : (term180 x s a) = (term181 x s a).
Proof. exact (MK_COMB (@lem5148216 s x a) (@lem5148217 s a)). Qed.
Lemma lem5148219 (s : real -> Prop) (a : real) : (term182 s a) = (term183 s a).
Proof. exact (fun_ext (fun x : real => @lem5148218 x s a)). Qed.
Lemma lem5148220 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5148221 (s : real -> Prop) (a : real) : (term171 s a) = (term184 s a).
Proof. exact (MK_COMB (@lem5148220) (@lem5148219 s a)). Qed.
Lemma lem5148222 (s : real -> Prop) (a : real) : ((term170 s a) = (term171 s a)) = ((term162 s a) = (term184 s a)).
Proof. exact (MK_COMB (@lem5148213 s a) (@lem5148221 s a)). Qed.
Lemma lem5148223 (s : real -> Prop) (a : real) : (term162 s a) = (term184 s a).
Proof. exact (EQ_MP (@lem5148222 s a) (@lem5148203 s a)). Qed.
Lemma lem5148224 (s : real -> Prop) : (term164 s) = (term185 s).
Proof. exact (fun_ext (fun a : real => @lem5148223 s a)). Qed.
Lemma lem5148225 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5148226 (s : real -> Prop) : (term165 s) = (term186 s).
Proof. exact (MK_COMB (@lem5148225) (@lem5148224 s)). Qed.
Lemma lem5148227 (s : real -> Prop) : (term150 s) = (term186 s).
Proof. exact (TRANS (@lem5148199 s) (@lem5148226 s)). Qed.
Lemma lem5148228 (s : real -> Prop) : (term131 s) = (term186 s).
Proof. exact (TRANS (@lem5148172 s) (@lem5148227 s)). Qed.
Lemma lem5148229 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5148230 (s : real -> Prop) : (term132 s) = (term187 s).
Proof. exact (MK_COMB (@lem5148229 s) (@lem5148228 s)). Qed.
Lemma lem5148232 {A : Type'} (P : Prop) (Q : A -> Prop) : (term93 A P Q) = (term92 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5148233 (P : Prop) (Q : real -> Prop) : (term95 P Q) = (term94 P Q).
Proof. exact (@lem5148232 real P Q). Qed.
Lemma lem5148234 (s : real -> Prop) : (term188 s) = (term189 s).
Proof. exact (@lem5148233 (term76 s) (term185 s)). Qed.
Lemma lem5148235 (s : real -> Prop) (a : real) : (term190 s a) = (term184 s a).
Proof. exact (eq_refl (term190 s a)). Qed.
Lemma lem5148236 (s : real -> Prop) : (term191 s) = (term185 s).
Proof. exact (fun_ext (fun a : real => @lem5148235 s a)). Qed.
Lemma lem5148237 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5148238 (s : real -> Prop) : (term192 s) = (term186 s).
Proof. exact (MK_COMB (@lem5148237) (@lem5148236 s)). Qed.
Lemma lem5148239 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5148240 (s : real -> Prop) : (term188 s) = (term187 s).
Proof. exact (MK_COMB (@lem5148239 s) (@lem5148238 s)). Qed.
Lemma lem5148241 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5148242 (s : real -> Prop) : (term193 s) = (term194 s).
Proof. exact (MK_COMB (@lem5148241) (@lem5148240 s)). Qed.
Lemma lem5148243 (s : real -> Prop) (a : real) : (term190 s a) = (term184 s a).
Proof. exact (eq_refl (term190 s a)). Qed.
Lemma lem5148244 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5148245 (s : real -> Prop) (a : real) : (term195 s a) = (term196 s a).
Proof. exact (MK_COMB (@lem5148244 s) (@lem5148243 s a)). Qed.
Lemma lem5148246 (s : real -> Prop) : (term197 s) = (term198 s).
Proof. exact (fun_ext (fun a : real => @lem5148245 s a)). Qed.
Lemma lem5148247 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5148248 (s : real -> Prop) : (term189 s) = (term199 s).
Proof. exact (MK_COMB (@lem5148247) (@lem5148246 s)). Qed.
Lemma lem5148249 (s : real -> Prop) : ((term188 s) = (term189 s)) = ((term187 s) = (term199 s)).
Proof. exact (MK_COMB (@lem5148242 s) (@lem5148248 s)). Qed.
Lemma lem5148250 (s : real -> Prop) : (term187 s) = (term199 s).
Proof. exact (EQ_MP (@lem5148249 s) (@lem5148234 s)). Qed.
Lemma lem5148252 {A : Type'} (P : Prop) (Q : A -> Prop) : (term93 A P Q) = (term92 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5148253 (P : Prop) (Q : real -> Prop) : (term95 P Q) = (term94 P Q).
Proof. exact (@lem5148252 real P Q). Qed.
Lemma lem5148254 (s : real -> Prop) (a : real) : (term200 s a) = (term201 s a).
Proof. exact (@lem5148253 (term76 s) (term183 s a)). Qed.
Lemma lem5148255 (x : real) (s : real -> Prop) (a : real) : (term202 s a x) = (term181 x s a).
Proof. exact (eq_refl (term202 s a x)). Qed.
Lemma lem5148256 (s : real -> Prop) (a : real) : (term203 s a) = (term183 s a).
Proof. exact (fun_ext (fun x : real => @lem5148255 x s a)). Qed.
Lemma lem5148257 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5148258 (s : real -> Prop) (a : real) : (term204 s a) = (term184 s a).
Proof. exact (MK_COMB (@lem5148257) (@lem5148256 s a)). Qed.
Lemma lem5148259 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5148260 (s : real -> Prop) (a : real) : (term200 s a) = (term196 s a).
Proof. exact (MK_COMB (@lem5148259 s) (@lem5148258 s a)). Qed.
Lemma lem5148261 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5148262 (s : real -> Prop) (a : real) : (term205 s a) = (term206 s a).
Proof. exact (MK_COMB (@lem5148261) (@lem5148260 s a)). Qed.
Lemma lem5148263 (x : real) (s : real -> Prop) (a : real) : (term202 s a x) = (term181 x s a).
Proof. exact (eq_refl (term202 s a x)). Qed.
Lemma lem5148264 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5148265 (x : real) (s : real -> Prop) (a : real) : (term207 s a x) = (term208 x s a).
Proof. exact (MK_COMB (@lem5148264 s) (@lem5148263 x s a)). Qed.
Lemma lem5148266 (s : real -> Prop) (a : real) : (term209 s a) = (term210 s a).
Proof. exact (fun_ext (fun x : real => @lem5148265 x s a)). Qed.
Lemma lem5148267 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5148268 (s : real -> Prop) (a : real) : (term201 s a) = (term211 s a).
Proof. exact (MK_COMB (@lem5148267) (@lem5148266 s a)). Qed.
Lemma lem5148269 (s : real -> Prop) (a : real) : ((term200 s a) = (term201 s a)) = ((term196 s a) = (term211 s a)).
Proof. exact (MK_COMB (@lem5148262 s a) (@lem5148268 s a)). Qed.
Lemma lem5148270 (s : real -> Prop) (a : real) : (term196 s a) = (term211 s a).
Proof. exact (EQ_MP (@lem5148269 s a) (@lem5148254 s a)). Qed.
Lemma lem5148271 (s : real -> Prop) : (term198 s) = (term212 s).
Proof. exact (fun_ext (fun a : real => @lem5148270 s a)). Qed.
Lemma lem5148272 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5148273 (s : real -> Prop) : (term199 s) = (term213 s).
Proof. exact (MK_COMB (@lem5148272) (@lem5148271 s)). Qed.
Lemma lem5148274 (s : real -> Prop) : (term187 s) = (term213 s).
Proof. exact (TRANS (@lem5148250 s) (@lem5148273 s)). Qed.
Lemma lem5148275 (s : real -> Prop) : (term132 s) = (term213 s).
Proof. exact (TRANS (@lem5148230 s) (@lem5148274 s)). Qed.
Lemma lem5148276 : term133 = term214.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5148275 s)). Qed.
Lemma lem5148277 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5148278 : term134 = term215.
Proof. exact (MK_COMB (@lem5148277) (@lem5148276)). Qed.
Lemma lem5148279 : term91 = term215.
Proof. exact (TRANS (@lem5148097) (@lem5148278)). Qed.
Lemma lem5148280 : term10 = term215.
Proof. exact (TRANS (@lem5147848) (@lem5148279)). Qed.
Lemma lem5148281 (h1 : term10) : term215.
Proof. exact (EQ_MP (@lem5148280) (@lem5147776 h1)). Qed.
Lemma lem5148288 (x : real) (y : real) (z : real) : (term216 x y z) = (term217 x y z).
Proof. exact (@lem17045 (real_le x y) (real_le y z)). Qed.
Lemma lem5148289 (x : real) (z : real) : (real_le x z) = (real_le x z).
Proof. exact (eq_refl (real_le x z)). Qed.
Lemma lem5148290 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5148291 (x : real) (y : real) (z : real) : (term218 x y z) = (term219 x y z).
Proof. exact (MK_COMB (@lem5148290) (@lem5148288 x y z)). Qed.
Lemma lem5148292 (y : real) (x : real) (z : real) : (term220 y x z) = (term221 y x z).
Proof. exact (MK_COMB (@lem5148291 x y z) (@lem5148289 x z)). Qed.
Lemma lem5148293 (y : real) (x : real) (z : real) : (term31 y x z) = (term220 y x z).
Proof. exact (@lem17265 (term222 x y z) (real_le x z)). Qed.
Lemma lem5148294 (y : real) (x : real) (z : real) : (term31 y x z) = (term221 y x z).
Proof. exact (TRANS (@lem5148293 y x z) (@lem5148292 y x z)). Qed.
Lemma lem5148295 (y : real) (x : real) : (term32 y x) = (term223 y x).
Proof. exact (fun_ext (fun z : real => @lem5148294 y x z)). Qed.
Lemma lem5148296 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5148297 (y : real) (x : real) : (term33 y x) = (term224 y x).
Proof. exact (MK_COMB (@lem5148296) (@lem5148295 y x)). Qed.
Lemma lem5148298 (x : real) : (term34 x) = (term225 x).
Proof. exact (fun_ext (fun y : real => @lem5148297 y x)). Qed.
Lemma lem5148299 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5148300 (x : real) : (term35 x) = (term226 x).
Proof. exact (MK_COMB (@lem5148299) (@lem5148298 x)). Qed.
Lemma lem5148301 : term36 = term227.
Proof. exact (fun_ext (fun x : real => @lem5148300 x)). Qed.
Lemma lem5148302 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5148363 : term37 = term228.
Proof. exact (MK_COMB (@lem5148302) (@lem5148301)). Qed.
Lemma lem5148364 (h1 : term37) : term228.
Proof. exact (EQ_MP (@lem5148363) (@lem5147777 h1)). Qed.
Lemma lem5148368 (s : real -> Prop) : (term229 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5148370 (s : real -> Prop) : (term230 s) = (term230 s).
Proof. exact (eq_refl (term230 s)). Qed.
Lemma lem5148371 (s : real -> Prop) : (term231 s) = (term232 s).
Proof. exact (MK_COMB (@lem5148370 s) (@lem5148368 s)). Qed.
Lemma lem5148372 (s : real -> Prop) : (term233 s) = (term231 s).
Proof. exact (@lem17045 (@FINITE real s) (term234 s)). Qed.
Lemma lem5148373 (s : real -> Prop) : (term233 s) = (term232 s).
Proof. exact (TRANS (@lem5148372 s) (@lem5148371 s)). Qed.
Lemma lem5148381 (x : real) (s : real -> Prop) : (term23 x s) = (term235 x s).
Proof. exact (@lem17265 (@IN real x s) (term236 x s)). Qed.
Lemma lem5148382 (s : real -> Prop) : (term24 s) = (term237 s).
Proof. exact (fun_ext (fun x : real => @lem5148381 x s)). Qed.
Lemma lem5148383 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5148384 (s : real -> Prop) : (term25 s) = (term238 s).
Proof. exact (MK_COMB (@lem5148383) (@lem5148382 s)). Qed.
Lemma lem5148386 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5148387 (s : real -> Prop) : (term27 s) = (term239 s).
Proof. exact (MK_COMB (@lem5148386 s) (@lem5148384 s)). Qed.
Lemma lem5148388 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5148389 (s : real -> Prop) : (term240 s) = (term241 s).
Proof. exact (MK_COMB (@lem5148388) (@lem5148373 s)). Qed.
Lemma lem5148390 (s : real -> Prop) : (term242 s) = (term243 s).
Proof. exact (MK_COMB (@lem5148389 s) (@lem5148387 s)). Qed.
Lemma lem5148391 (s : real -> Prop) : (term29 s) = (term242 s).
Proof. exact (@lem17265 (term76 s) (term27 s)). Qed.
Lemma lem5148392 (s : real -> Prop) : (term29 s) = (term243 s).
Proof. exact (TRANS (@lem5148391 s) (@lem5148390 s)). Qed.
Lemma lem5148393 : term30 = term244.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5148392 s)). Qed.
Lemma lem5148394 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5148495 : term17 = term245.
Proof. exact (MK_COMB (@lem5148394) (@lem5148393)). Qed.
Lemma lem5148496 (h1 : term17) : term245.
Proof. exact (EQ_MP (@lem5148495) (@lem5147778 h1)). Qed.
Lemma lem5148497 (s : real -> Prop) (h1 : term213 s) : term213 s.
Proof. exact (h1). Qed.
Lemma lem5148498 (s : real -> Prop) (a : real) (h1 : term211 s a) : term211 s a.
Proof. exact (h1). Qed.
Lemma lem5148499 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term208 x s a.
Proof. exact (h1). Qed.
Lemma lem5148524 (y : real) (x : real) (z : real) : (term221 y x z) = (term221 y x z).
Proof. exact (eq_refl (term221 y x z)). Qed.
Lemma lem5148525 (y : real) (x : real) : (term223 y x) = (term223 y x).
Proof. exact (fun_ext (fun z : real => @lem5148524 y x z)). Qed.
Lemma lem5148526 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5148527 (y : real) (x : real) : (term224 y x) = (term224 y x).
Proof. exact (MK_COMB (@lem5148526) (@lem5148525 y x)). Qed.
Lemma lem5148528 (x : real) : (term225 x) = (term225 x).
Proof. exact (fun_ext (fun y : real => @lem5148527 y x)). Qed.
Lemma lem5148529 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5148530 (x : real) : (term226 x) = (term226 x).
Proof. exact (MK_COMB (@lem5148529) (@lem5148528 x)). Qed.
Lemma lem5148531 : term227 = term227.
Proof. exact (fun_ext (fun x : real => @lem5148530 x)). Qed.
Lemma lem5148532 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5148533 : term228 = term228.
Proof. exact (MK_COMB (@lem5148532) (@lem5148531)). Qed.
Lemma lem5148534 (h1 : term37) : term228.
Proof. exact (EQ_MP (@lem5148533) (@lem5148364 h1)). Qed.
Lemma lem5148551 (x : real) (s : real -> Prop) : (term235 x s) = (term235 x s).
Proof. exact (eq_refl (term235 x s)). Qed.
Lemma lem5148552 (s : real -> Prop) : (term237 s) = (term237 s).
Proof. exact (fun_ext (fun x : real => @lem5148551 x s)). Qed.
Lemma lem5148553 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5148554 (s : real -> Prop) : (term238 s) = (term238 s).
Proof. exact (MK_COMB (@lem5148553) (@lem5148552 s)). Qed.
Lemma lem5148563 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5148564 (s : real -> Prop) : (term239 s) = (term239 s).
Proof. exact (MK_COMB (@lem5148563 s) (@lem5148554 s)). Qed.
Lemma lem5148579 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5148580 (s : real -> Prop) : (term243 s) = (term243 s).
Proof. exact (MK_COMB (@lem5148579 s) (@lem5148564 s)). Qed.
Lemma lem5148581 : term244 = term244.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5148580 s)). Qed.
Lemma lem5148582 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5148583 : term245 = term245.
Proof. exact (MK_COMB (@lem5148582) (@lem5148581)). Qed.
Lemma lem5148584 (h1 : term17) : term245.
Proof. exact (EQ_MP (@lem5148583) (@lem5148496 h1)). Qed.
Lemma lem5148599 (s : real -> Prop) (x : real) (a : real) : (term49 s x a) = (term49 s x a).
Proof. exact (eq_refl (term49 s x a)). Qed.
Lemma lem5148600 (s : real -> Prop) (a : real) : (term59 s a) = (term59 s a).
Proof. exact (fun_ext (fun x : real => @lem5148599 s x a)). Qed.
Lemma lem5148601 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5148602 (s : real -> Prop) (a : real) : (term60 s a) = (term60 s a).
Proof. exact (MK_COMB (@lem5148601) (@lem5148600 s a)). Qed.
Lemma lem5148613 (s : real -> Prop) (a : real) : (term61 s a) = (term61 s a).
Proof. exact (eq_refl (term61 s a)). Qed.
Lemma lem5148614 (s : real -> Prop) (a : real) : (term63 s a) = (term63 s a).
Proof. exact (MK_COMB (@lem5148613 s a) (@lem5148602 s a)). Qed.
Lemma lem5148641 (s : real -> Prop) (x : real) (a : real) : (term179 s x a) = (term179 s x a).
Proof. exact (eq_refl (term179 s x a)). Qed.
Lemma lem5148642 (x : real) (s : real -> Prop) (a : real) : (term181 x s a) = (term181 x s a).
Proof. exact (MK_COMB (@lem5148641 s x a) (@lem5148614 s a)). Qed.
Lemma lem5148657 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5148658 (x : real) (s : real -> Prop) (a : real) : (term208 x s a) = (term208 x s a).
Proof. exact (MK_COMB (@lem5148657 s) (@lem5148642 x s a)). Qed.
Lemma lem5148659 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term208 x s a.
Proof. exact (EQ_MP (@lem5148658 x s a) (@lem5148499 x s a h1)). Qed.
Lemma lem5148660 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term181 x s a.
Proof. exact (proj2 (@lem5148659 x s a h1)). Qed.
Lemma lem5148661 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term76 s.
Proof. exact (proj1 (@lem5148659 x s a h1)). Qed.
Lemma lem5148664 (s : real -> Prop) (x : real) (a : real) (h1 : term143 s x a) : term143 s x a.
Proof. exact (h1). Qed.
Lemma lem5148665 (s : real -> Prop) (a : real) (h1 : term63 s a) : term63 s a.
Proof. exact (h1). Qed.
Lemma lem5148666 (s : real -> Prop) (x : real) (a : real) (h1 : term143 s x a) : term48 s x a.
Proof. exact (proj2 (@lem5148664 s x a h1)). Qed.
Lemma lem5148670 (s : real -> Prop) (a : real) (h1 : term63 s a) : term60 s a.
Proof. exact (proj2 (@lem5148665 s a h1)). Qed.
Lemma lem5148685 (y : real) (x : real) (z : real) : (term221 y x z) = (term221 y x z).
Proof. exact (eq_refl (term221 y x z)). Qed.
Lemma lem5148686 (y : real) (x : real) : (term223 y x) = (term223 y x).
Proof. exact (fun_ext (fun z : real => @lem5148685 y x z)). Qed.
Lemma lem5148687 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5148688 (y : real) (x : real) : (term224 y x) = (term224 y x).
Proof. exact (MK_COMB (@lem5148687) (@lem5148686 y x)). Qed.
Lemma lem5148689 (x : real) : (term225 x) = (term225 x).
Proof. exact (fun_ext (fun y : real => @lem5148688 y x)). Qed.
Lemma lem5148690 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5148691 (x : real) : (term226 x) = (term226 x).
Proof. exact (MK_COMB (@lem5148690) (@lem5148689 x)). Qed.
Lemma lem5148692 : term227 = term227.
Proof. exact (fun_ext (fun x : real => @lem5148691 x)). Qed.
Lemma lem5148693 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5148695 : term228 = term228.
Proof. exact (MK_COMB (@lem5148693) (@lem5148692)). Qed.
Lemma lem5148696 (h1 : term37) : term228.
Proof. exact (EQ_MP (@lem5148695) (@lem5148534 h1)). Qed.
Lemma lem5148698 {A : Type'} (P : Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5148699 (P : Prop) (Q : real -> Prop) : (term248 P Q) = (term249 P Q).
Proof. exact (@lem5148698 real P Q). Qed.
Lemma lem5148700 (s : real -> Prop) : (term250 s) = (term251 s).
Proof. exact (@lem5148699 (term252 s) (term237 s)). Qed.
Lemma lem5148701 (x : real) (s : real -> Prop) : (term253 s x) = (term235 x s).
Proof. exact (eq_refl (term253 s x)). Qed.
Lemma lem5148702 (s : real -> Prop) : (term254 s) = (term237 s).
Proof. exact (fun_ext (fun x : real => @lem5148701 x s)). Qed.
Lemma lem5148703 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5148704 (s : real -> Prop) : (term255 s) = (term238 s).
Proof. exact (MK_COMB (@lem5148703) (@lem5148702 s)). Qed.
Lemma lem5148705 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5148706 (s : real -> Prop) : (term250 s) = (term239 s).
Proof. exact (MK_COMB (@lem5148705 s) (@lem5148704 s)). Qed.
Lemma lem5148707 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5148708 (s : real -> Prop) : (term256 s) = (term257 s).
Proof. exact (MK_COMB (@lem5148707) (@lem5148706 s)). Qed.
Lemma lem5148709 (x : real) (s : real -> Prop) : (term253 s x) = (term235 x s).
Proof. exact (eq_refl (term253 s x)). Qed.
Lemma lem5148710 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5148711 (x : real) (s : real -> Prop) : (term258 s x) = (term259 x s).
Proof. exact (MK_COMB (@lem5148710 s) (@lem5148709 x s)). Qed.
Lemma lem5148712 (s : real -> Prop) : (term260 s) = (term261 s).
Proof. exact (fun_ext (fun x : real => @lem5148711 x s)). Qed.
Lemma lem5148713 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5148714 (s : real -> Prop) : (term251 s) = (term262 s).
Proof. exact (MK_COMB (@lem5148713) (@lem5148712 s)). Qed.
Lemma lem5148715 (s : real -> Prop) : ((term250 s) = (term251 s)) = ((term239 s) = (term262 s)).
Proof. exact (MK_COMB (@lem5148708 s) (@lem5148714 s)). Qed.
Lemma lem5148716 (s : real -> Prop) : (term239 s) = (term262 s).
Proof. exact (EQ_MP (@lem5148715 s) (@lem5148700 s)). Qed.
Lemma lem5148717 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5148718 (s : real -> Prop) : (term243 s) = (term263 s).
Proof. exact (MK_COMB (@lem5148717 s) (@lem5148716 s)). Qed.
Lemma lem5148720 {A : Type'} (P : Prop) (Q : A -> Prop) : (term264 A P Q) = (term265 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5148721 (P : Prop) (Q : real -> Prop) : (term266 P Q) = (term267 P Q).
Proof. exact (@lem5148720 real P Q). Qed.
Lemma lem5148722 (s : real -> Prop) : (term268 s) = (term269 s).
Proof. exact (@lem5148721 (term232 s) (term261 s)). Qed.
Lemma lem5148723 (x : real) (s : real -> Prop) : (term270 s x) = (term259 x s).
Proof. exact (eq_refl (term270 s x)). Qed.
Lemma lem5148724 (s : real -> Prop) : (term271 s) = (term261 s).
Proof. exact (fun_ext (fun x : real => @lem5148723 x s)). Qed.
Lemma lem5148725 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5148726 (s : real -> Prop) : (term272 s) = (term262 s).
Proof. exact (MK_COMB (@lem5148725) (@lem5148724 s)). Qed.
Lemma lem5148727 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5148728 (s : real -> Prop) : (term268 s) = (term263 s).
Proof. exact (MK_COMB (@lem5148727 s) (@lem5148726 s)). Qed.
Lemma lem5148729 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5148730 (s : real -> Prop) : (term273 s) = (term274 s).
Proof. exact (MK_COMB (@lem5148729) (@lem5148728 s)). Qed.
Lemma lem5148731 (x : real) (s : real -> Prop) : (term270 s x) = (term259 x s).
Proof. exact (eq_refl (term270 s x)). Qed.
Lemma lem5148732 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5148733 (x : real) (s : real -> Prop) : (term275 s x) = (term276 x s).
Proof. exact (MK_COMB (@lem5148732 s) (@lem5148731 x s)). Qed.
Lemma lem5148734 (s : real -> Prop) : (term277 s) = (term278 s).
Proof. exact (fun_ext (fun x : real => @lem5148733 x s)). Qed.
Lemma lem5148735 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5148736 (s : real -> Prop) : (term269 s) = (term279 s).
Proof. exact (MK_COMB (@lem5148735) (@lem5148734 s)). Qed.
Lemma lem5148737 (s : real -> Prop) : ((term268 s) = (term269 s)) = ((term263 s) = (term279 s)).
Proof. exact (MK_COMB (@lem5148730 s) (@lem5148736 s)). Qed.
Lemma lem5148738 (s : real -> Prop) : (term263 s) = (term279 s).
Proof. exact (EQ_MP (@lem5148737 s) (@lem5148722 s)). Qed.
Lemma lem5148739 (s : real -> Prop) : (term243 s) = (term279 s).
Proof. exact (TRANS (@lem5148718 s) (@lem5148738 s)). Qed.
Lemma lem5148740 : term244 = term280.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5148739 s)). Qed.
Lemma lem5148741 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5148742 : term245 = term281.
Proof. exact (MK_COMB (@lem5148741) (@lem5148740)). Qed.
Lemma lem5148771 (x : real) (s : real -> Prop) : (term276 x s) = (term282 x s).
Proof. exact (@lem19490 (term252 s) (term232 s) (term235 x s)). Qed.
Lemma lem5148772 (s : real -> Prop) : (term278 s) = (term283 s).
Proof. exact (fun_ext (fun x : real => @lem5148771 x s)). Qed.
Lemma lem5148773 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5148774 (s : real -> Prop) : (term279 s) = (term284 s).
Proof. exact (MK_COMB (@lem5148773) (@lem5148772 s)). Qed.
Lemma lem5148775 : term280 = term285.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5148774 s)). Qed.
Lemma lem5148776 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5148777 : term281 = term286.
Proof. exact (MK_COMB (@lem5148776) (@lem5148775)). Qed.
Lemma lem5148778 : term245 = term286.
Proof. exact (TRANS (@lem5148742) (@lem5148777)). Qed.
Lemma lem5148779 (h1 : term17) : term286.
Proof. exact (EQ_MP (@lem5148778) (@lem5148584 h1)). Qed.
Lemma lem5148826 {A : Type'} (P : Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5148827 (P : Prop) (Q : real -> Prop) : (term248 P Q) = (term249 P Q).
Proof. exact (@lem5148826 real P Q). Qed.
Lemma lem5148828 (s : real -> Prop) : (term250 s) = (term251 s).
Proof. exact (@lem5148827 (term252 s) (term237 s)). Qed.
Lemma lem5148829 (x : real) (s : real -> Prop) : (term253 s x) = (term235 x s).
Proof. exact (eq_refl (term253 s x)). Qed.
Lemma lem5148830 (s : real -> Prop) : (term254 s) = (term237 s).
Proof. exact (fun_ext (fun x : real => @lem5148829 x s)). Qed.
Lemma lem5148831 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5148832 (s : real -> Prop) : (term255 s) = (term238 s).
Proof. exact (MK_COMB (@lem5148831) (@lem5148830 s)). Qed.
Lemma lem5148833 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5148834 (s : real -> Prop) : (term250 s) = (term239 s).
Proof. exact (MK_COMB (@lem5148833 s) (@lem5148832 s)). Qed.
Lemma lem5148835 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5148836 (s : real -> Prop) : (term256 s) = (term257 s).
Proof. exact (MK_COMB (@lem5148835) (@lem5148834 s)). Qed.
Lemma lem5148837 (x : real) (s : real -> Prop) : (term253 s x) = (term235 x s).
Proof. exact (eq_refl (term253 s x)). Qed.
Lemma lem5148838 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5148839 (x : real) (s : real -> Prop) : (term258 s x) = (term259 x s).
Proof. exact (MK_COMB (@lem5148838 s) (@lem5148837 x s)). Qed.
Lemma lem5148840 (s : real -> Prop) : (term260 s) = (term261 s).
Proof. exact (fun_ext (fun x : real => @lem5148839 x s)). Qed.
Lemma lem5148841 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5148842 (s : real -> Prop) : (term251 s) = (term262 s).
Proof. exact (MK_COMB (@lem5148841) (@lem5148840 s)). Qed.
Lemma lem5148843 (s : real -> Prop) : ((term250 s) = (term251 s)) = ((term239 s) = (term262 s)).
Proof. exact (MK_COMB (@lem5148836 s) (@lem5148842 s)). Qed.
Lemma lem5148844 (s : real -> Prop) : (term239 s) = (term262 s).
Proof. exact (EQ_MP (@lem5148843 s) (@lem5148828 s)). Qed.
Lemma lem5148845 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5148846 (s : real -> Prop) : (term243 s) = (term263 s).
Proof. exact (MK_COMB (@lem5148845 s) (@lem5148844 s)). Qed.
Lemma lem5148848 {A : Type'} (P : Prop) (Q : A -> Prop) : (term264 A P Q) = (term265 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5148849 (P : Prop) (Q : real -> Prop) : (term266 P Q) = (term267 P Q).
Proof. exact (@lem5148848 real P Q). Qed.
Lemma lem5148850 (s : real -> Prop) : (term268 s) = (term269 s).
Proof. exact (@lem5148849 (term232 s) (term261 s)). Qed.
Lemma lem5148851 (x : real) (s : real -> Prop) : (term270 s x) = (term259 x s).
Proof. exact (eq_refl (term270 s x)). Qed.
Lemma lem5148852 (s : real -> Prop) : (term271 s) = (term261 s).
Proof. exact (fun_ext (fun x : real => @lem5148851 x s)). Qed.
Lemma lem5148853 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5148854 (s : real -> Prop) : (term272 s) = (term262 s).
Proof. exact (MK_COMB (@lem5148853) (@lem5148852 s)). Qed.
Lemma lem5148855 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5148856 (s : real -> Prop) : (term268 s) = (term263 s).
Proof. exact (MK_COMB (@lem5148855 s) (@lem5148854 s)). Qed.
Lemma lem5148857 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5148858 (s : real -> Prop) : (term273 s) = (term274 s).
Proof. exact (MK_COMB (@lem5148857) (@lem5148856 s)). Qed.
Lemma lem5148859 (x : real) (s : real -> Prop) : (term270 s x) = (term259 x s).
Proof. exact (eq_refl (term270 s x)). Qed.
Lemma lem5148860 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5148861 (x : real) (s : real -> Prop) : (term275 s x) = (term276 x s).
Proof. exact (MK_COMB (@lem5148860 s) (@lem5148859 x s)). Qed.
Lemma lem5148862 (s : real -> Prop) : (term277 s) = (term278 s).
Proof. exact (fun_ext (fun x : real => @lem5148861 x s)). Qed.
Lemma lem5148863 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5148864 (s : real -> Prop) : (term269 s) = (term279 s).
Proof. exact (MK_COMB (@lem5148863) (@lem5148862 s)). Qed.
Lemma lem5148865 (s : real -> Prop) : ((term268 s) = (term269 s)) = ((term263 s) = (term279 s)).
Proof. exact (MK_COMB (@lem5148858 s) (@lem5148864 s)). Qed.
Lemma lem5148866 (s : real -> Prop) : (term263 s) = (term279 s).
Proof. exact (EQ_MP (@lem5148865 s) (@lem5148850 s)). Qed.
Lemma lem5148867 (s : real -> Prop) : (term243 s) = (term279 s).
Proof. exact (TRANS (@lem5148846 s) (@lem5148866 s)). Qed.
Lemma lem5148868 : term244 = term280.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5148867 s)). Qed.
Lemma lem5148869 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5148870 : term245 = term281.
Proof. exact (MK_COMB (@lem5148869) (@lem5148868)). Qed.
Lemma lem5148899 (x : real) (s : real -> Prop) : (term276 x s) = (term282 x s).
Proof. exact (@lem19490 (term252 s) (term232 s) (term235 x s)). Qed.
Lemma lem5148900 (s : real -> Prop) : (term278 s) = (term283 s).
Proof. exact (fun_ext (fun x : real => @lem5148899 x s)). Qed.
Lemma lem5148901 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5148902 (s : real -> Prop) : (term279 s) = (term284 s).
Proof. exact (MK_COMB (@lem5148901) (@lem5148900 s)). Qed.
Lemma lem5148903 : term280 = term285.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5148902 s)). Qed.
Lemma lem5148904 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5148905 : term281 = term286.
Proof. exact (MK_COMB (@lem5148904) (@lem5148903)). Qed.
Lemma lem5148906 : term245 = term286.
Proof. exact (TRANS (@lem5148870) (@lem5148905)). Qed.
Lemma lem5148907 (h1 : term17) : term286.
Proof. exact (EQ_MP (@lem5148906) (@lem5148584 h1)). Qed.
Lemma lem5148927 (s : real -> Prop) (x : real) (a : real) : (term49 s x a) = (term49 s x a).
Proof. exact (eq_refl (term49 s x a)). Qed.
Lemma lem5148928 (s : real -> Prop) (a : real) : (term59 s a) = (term59 s a).
Proof. exact (fun_ext (fun x : real => @lem5148927 s x a)). Qed.
Lemma lem5148929 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5148931 (s : real -> Prop) (a : real) : (term60 s a) = (term60 s a).
Proof. exact (MK_COMB (@lem5148929) (@lem5148928 s a)). Qed.
Lemma lem5148932 (s : real -> Prop) (a : real) (h1 : term63 s a) : term60 s a.
Proof. exact (EQ_MP (@lem5148931 s a) (@lem5148670 s a h1)). Qed.
Lemma lem5148933 (_67211 : real) (h1 : term37) : term287 _67211.
Proof. exact (@lem5148696 h1 _67211). Qed.
Lemma lem5148934 (_67211 : real) : (term287 _67211) = (term226 _67211).
Proof. exact (eq_refl (term287 _67211)). Qed.
Lemma lem5148935 (_67211 : real) (h1 : term37) : term226 _67211.
Proof. exact (EQ_MP (@lem5148934 _67211) (@lem5148933 _67211 h1)). Qed.
Lemma lem5148936 (_67211 : real) (_67212 : real) (h1 : term37) : term288 _67211 _67212.
Proof. exact (@lem5148935 _67211 h1 _67212). Qed.
Lemma lem5148937 (_67212 : real) (_67211 : real) : (term288 _67211 _67212) = (term224 _67212 _67211).
Proof. exact (eq_refl (term288 _67211 _67212)). Qed.
Lemma lem5148938 (_67212 : real) (_67211 : real) (h1 : term37) : term224 _67212 _67211.
Proof. exact (EQ_MP (@lem5148937 _67212 _67211) (@lem5148936 _67211 _67212 h1)). Qed.
Lemma lem5148939 (_67212 : real) (_67211 : real) (_67213 : real) (h1 : term37) : term289 _67212 _67211 _67213.
Proof. exact (@lem5148938 _67212 _67211 h1 _67213). Qed.
Lemma lem5148940 (_67212 : real) (_67211 : real) (_67213 : real) : (term289 _67212 _67211 _67213) = (term221 _67212 _67211 _67213).
Proof. exact (eq_refl (term289 _67212 _67211 _67213)). Qed.
Lemma lem5148941 (_67212 : real) (_67211 : real) (_67213 : real) (h1 : term37) : term221 _67212 _67211 _67213.
Proof. exact (EQ_MP (@lem5148940 _67212 _67211 _67213) (@lem5148939 _67212 _67211 _67213 h1)). Qed.
Lemma lem5148942 (_67214 : real -> Prop) (h1 : term17) : term290 _67214.
Proof. exact (@lem5148779 h1 _67214). Qed.
Lemma lem5148943 (_67214 : real -> Prop) : (term290 _67214) = (term284 _67214).
Proof. exact (eq_refl (term290 _67214)). Qed.
Lemma lem5148944 (_67214 : real -> Prop) (h1 : term17) : term284 _67214.
Proof. exact (EQ_MP (@lem5148943 _67214) (@lem5148942 _67214 h1)). Qed.
Lemma lem5148945 (_67214 : real -> Prop) (_67215 : real) (h1 : term17) : term291 _67214 _67215.
Proof. exact (@lem5148944 _67214 h1 _67215). Qed.
Lemma lem5148946 (_67215 : real) (_67214 : real -> Prop) : (term291 _67214 _67215) = (term282 _67215 _67214).
Proof. exact (eq_refl (term291 _67214 _67215)). Qed.
Lemma lem5148947 (_67215 : real) (_67214 : real -> Prop) (h1 : term17) : term282 _67215 _67214.
Proof. exact (EQ_MP (@lem5148946 _67215 _67214) (@lem5148945 _67214 _67215 h1)). Qed.
Lemma lem5148957 (_67219 : real -> Prop) (h1 : term17) : term290 _67219.
Proof. exact (@lem5148907 h1 _67219). Qed.
Lemma lem5148958 (_67219 : real -> Prop) : (term290 _67219) = (term284 _67219).
Proof. exact (eq_refl (term290 _67219)). Qed.
Lemma lem5148959 (_67219 : real -> Prop) (h1 : term17) : term284 _67219.
Proof. exact (EQ_MP (@lem5148958 _67219) (@lem5148957 _67219 h1)). Qed.
Lemma lem5148960 (_67219 : real -> Prop) (_67220 : real) (h1 : term17) : term291 _67219 _67220.
Proof. exact (@lem5148959 _67219 h1 _67220). Qed.
Lemma lem5148961 (_67220 : real) (_67219 : real -> Prop) : (term291 _67219 _67220) = (term282 _67220 _67219).
Proof. exact (eq_refl (term291 _67219 _67220)). Qed.
Lemma lem5148962 (_67220 : real) (_67219 : real -> Prop) (h1 : term17) : term282 _67220 _67219.
Proof. exact (EQ_MP (@lem5148961 _67220 _67219) (@lem5148960 _67219 _67220 h1)). Qed.
Lemma lem5148963 (_67221 : real) (s : real -> Prop) (a : real) (h1 : term63 s a) : term292 s a _67221.
Proof. exact (@lem5148932 s a h1 _67221). Qed.
Lemma lem5148964 (s : real -> Prop) (_67221 : real) (a : real) : (term292 s a _67221) = (term49 s _67221 a).
Proof. exact (eq_refl (term292 s a _67221)). Qed.
Lemma lem5148966 (_67215 : real) (_67214 : real -> Prop) (h1 : term17) : term293 _67215 _67214.
Proof. exact (proj2 (@lem5148947 _67215 _67214 h1)). Qed.
Lemma lem5148969 (_67219 : real -> Prop) (h1 : term17) : term294 _67219.
Proof. exact (proj1 (@lem5148962 (@el real) _67219 h1)). Qed.
Lemma lem5148980 (_67212 : real) (_67211 : real) (_67213 : real) : (term221 _67212 _67211 _67213) = (term295 _67212 _67211 _67213).
Proof. exact (@lem5147531 (term296 _67211 _67212) (term296 _67212 _67213) (real_le _67211 _67213)). Qed.
Lemma lem5148981 (_67212 : real) (_67211 : real) (_67213 : real) (h1 : term37) : term295 _67212 _67211 _67213.
Proof. exact (EQ_MP (@lem5148980 _67212 _67211 _67213) (@lem5148941 _67212 _67211 _67213 h1)). Qed.
Lemma lem5148991 (s : real -> Prop) (x : real) (a : real) (h1 : term143 s x a) : term296 x a.
Proof. exact (proj2 (@lem5148666 s x a h1)). Qed.
Lemma lem5149018 (_67215 : real) (_67214 : real -> Prop) : (term293 _67215 _67214) = (term297 _67215 _67214).
Proof. exact (@lem5147531 (term298 _67214) (_67214 = (@EMPTY real)) (term235 _67215 _67214)). Qed.
Lemma lem5149019 (_67215 : real) (_67214 : real -> Prop) (h1 : term17) : term297 _67215 _67214.
Proof. exact (EQ_MP (@lem5149018 _67215 _67214) (@lem5148966 _67215 _67214 h1)). Qed.
Lemma lem5149037 (s : real -> Prop) (a : real) (h1 : term63 s a) : term299 s a.
Proof. exact (proj1 (@lem5148665 s a h1)). Qed.
Lemma lem5149043 (_67221 : real) (s : real -> Prop) (a : real) (h1 : term63 s a) : term49 s _67221 a.
Proof. exact (EQ_MP (@lem5148964 s _67221 a) (@lem5148963 _67221 s a h1)). Qed.
Lemma lem5149054 (_67219 : real -> Prop) : (term294 _67219) = (term300 _67219).
Proof. exact (@lem5147531 (term298 _67219) (_67219 = (@EMPTY real)) (term252 _67219)). Qed.
Lemma lem5149055 (_67219 : real -> Prop) (h1 : term17) : term300 _67219.
Proof. exact (EQ_MP (@lem5149054 _67219) (@lem5148969 _67219 h1)). Qed.
Lemma lem5149135 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : @FINITE real s.
Proof. exact (proj1 (@lem5148661 x s a h1)). Qed.
Lemma lem5149136 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term301 s.
Proof. exact (fun h0 : term298 s => @lem5149135 x s a h1). Qed.
Lemma lem5149138 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5149139 (s : real -> Prop) : (term301 s) = (@FINITE real s).
Proof. exact (@lem5149138 (@FINITE real s)). Qed.
Lemma lem5149140 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : @FINITE real s.
Proof. exact (EQ_MP (@lem5149139 s) (@lem5149136 x s a h1)). Qed.
Lemma lem5149142 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term234 s.
Proof. exact (proj2 (@lem5148661 x s a h1)). Qed.
Lemma lem5149143 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term303 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5149142 x s a h1). Qed.
Lemma lem5149145 (p : Prop) : (term304 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5149146 (s : real -> Prop) : (term303 s) = (term234 s).
Proof. exact (@lem5149145 (s = (@EMPTY real))). Qed.
Lemma lem5149147 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term234 s.
Proof. exact (EQ_MP (@lem5149146 s) (@lem5149143 x s a h1)). Qed.
Lemma lem5149149 (s : real -> Prop) (x : real) (a : real) (h1 : term143 s x a) : @IN real x s.
Proof. exact (proj1 (@lem5148666 s x a h1)). Qed.
Lemma lem5149150 (s : real -> Prop) (x : real) (a : real) (h1 : term143 s x a) : term305 x s.
Proof. exact (fun h0 : term306 x s => @lem5149149 s x a h1). Qed.
Lemma lem5149152 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5149153 (x : real) (s : real -> Prop) : (term305 x s) = (@IN real x s).
Proof. exact (@lem5149152 (@IN real x s)). Qed.
Lemma lem5149154 (s : real -> Prop) (x : real) (a : real) (h1 : term143 s x a) : @IN real x s.
Proof. exact (EQ_MP (@lem5149153 x s) (@lem5149150 s x a h1)). Qed.
Lemma lem5149160 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5149161 (_67215 : real) (_67214 : real -> Prop) : (term297 _67215 _67214) = (term307 _67215 _67214).
Proof. exact (@lem5149160 (_67214 = (@EMPTY real)) (term298 _67214) (term235 _67215 _67214)). Qed.
Lemma lem5149187 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5149188 (_67215 : real) (_67214 : real -> Prop) : (term235 _67215 _67214) = (term308 _67215 _67214).
Proof. exact (@lem5149187 (term236 _67215 _67214) (term306 _67215 _67214)). Qed.
Lemma lem5149194 (_67214 : real -> Prop) : (term230 _67214) = (term230 _67214).
Proof. exact (eq_refl (term230 _67214)). Qed.
Lemma lem5149195 (_67215 : real) (_67214 : real -> Prop) : (term309 _67215 _67214) = (term310 _67215 _67214).
Proof. exact (MK_COMB (@lem5149194 _67214) (@lem5149188 _67215 _67214)). Qed.
Lemma lem5149199 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5149200 (_67215 : real) (_67214 : real -> Prop) : (term310 _67215 _67214) = (term311 _67215 _67214).
Proof. exact (@lem5149199 (term236 _67215 _67214) (term298 _67214) (term306 _67215 _67214)). Qed.
Lemma lem5149216 (_67215 : real) (_67214 : real -> Prop) : (term309 _67215 _67214) = (term311 _67215 _67214).
Proof. exact (TRANS (@lem5149195 _67215 _67214) (@lem5149200 _67215 _67214)). Qed.
Lemma lem5149217 (_67214 : real -> Prop) : (term312 _67214) = (term312 _67214).
Proof. exact (eq_refl (term312 _67214)). Qed.
Lemma lem5149218 (_67215 : real) (_67214 : real -> Prop) : (term307 _67215 _67214) = (term313 _67215 _67214).
Proof. exact (MK_COMB (@lem5149217 _67214) (@lem5149216 _67215 _67214)). Qed.
Lemma lem5149229 (_67215 : real) (_67214 : real -> Prop) : (term297 _67215 _67214) = (term313 _67215 _67214).
Proof. exact (TRANS (@lem5149161 _67215 _67214) (@lem5149218 _67215 _67214)). Qed.
Lemma lem5149230 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5149231 (_67215 : real) (_67214 : real -> Prop) : (term314 _67215 _67214) = (term315 _67215 _67214).
Proof. exact (MK_COMB (@lem5149230) (@lem5149229 _67215 _67214)). Qed.
Lemma lem5149245 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5149246 (_67215 : real) (_67214 : real -> Prop) : (term316 _67215 _67214) = (term317 _67215 _67214).
Proof. exact (@lem5149245 (_67214 = (@EMPTY real)) (term298 _67214) (term306 _67215 _67214)). Qed.
Lemma lem5149264 (_67215 : real) (_67214 : real -> Prop) : (term318 _67215 _67214) = (term318 _67215 _67214).
Proof. exact (eq_refl (term318 _67215 _67214)). Qed.
Lemma lem5149265 (_67215 : real) (_67214 : real -> Prop) : (term319 _67215 _67214) = (term320 _67215 _67214).
Proof. exact (MK_COMB (@lem5149264 _67215 _67214) (@lem5149246 _67215 _67214)). Qed.
Lemma lem5149269 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5149270 (_67215 : real) (_67214 : real -> Prop) : (term320 _67215 _67214) = (term313 _67215 _67214).
Proof. exact (@lem5149269 (_67214 = (@EMPTY real)) (term236 _67215 _67214) (term321 _67215 _67214)). Qed.
Lemma lem5149298 (_67215 : real) (_67214 : real -> Prop) : (term319 _67215 _67214) = (term313 _67215 _67214).
Proof. exact (TRANS (@lem5149265 _67215 _67214) (@lem5149270 _67215 _67214)). Qed.
Lemma lem5149299 (_67215 : real) (_67214 : real -> Prop) : ((term297 _67215 _67214) = (term319 _67215 _67214)) = ((term313 _67215 _67214) = (term313 _67215 _67214)).
Proof. exact (MK_COMB (@lem5149231 _67215 _67214) (@lem5149298 _67215 _67214)). Qed.
Lemma lem5149301 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5149302 (x : Prop) : (x = x) = True.
Proof. exact (@lem5149301 Prop x). Qed.
Lemma lem5149303 (_67215 : real) (_67214 : real -> Prop) : ((term313 _67215 _67214) = (term313 _67215 _67214)) = True.
Proof. exact (@lem5149302 (term313 _67215 _67214)). Qed.
Lemma lem5149304 (_67215 : real) (_67214 : real -> Prop) : ((term297 _67215 _67214) = (term319 _67215 _67214)) = True.
Proof. exact (TRANS (@lem5149299 _67215 _67214) (@lem5149303 _67215 _67214)). Qed.
Lemma lem5149305 (_67215 : real) (_67214 : real -> Prop) : True = ((term297 _67215 _67214) = (term319 _67215 _67214)).
Proof. exact (SYM (@lem5149304 _67215 _67214)). Qed.
Lemma lem5149306 (_67215 : real) (_67214 : real -> Prop) : (term297 _67215 _67214) = (term319 _67215 _67214).
Proof. exact (EQ_MP (@lem5149305 _67215 _67214) (@lem0)). Qed.
Lemma lem5149307 (_67215 : real) (_67214 : real -> Prop) (h1 : term17) : term319 _67215 _67214.
Proof. exact (EQ_MP (@lem5149306 _67215 _67214) (@lem5149019 _67215 _67214 h1)). Qed.
Lemma lem5149309 (b : Prop) (a : Prop) : (a \/ b) = (term322 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5149310 (_67215 : real) (_67214 : real -> Prop) : (term319 _67215 _67214) = (term323 _67215 _67214).
Proof. exact (@lem5149309 (term316 _67215 _67214) (term236 _67215 _67214)). Qed.
Lemma lem5149312 (a : Prop) (b : Prop) : (term324 a b) = (term325 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5149313 (_67215 : real) (_67214 : real -> Prop) : (term326 _67215 _67214) = (term327 _67215 _67214).
Proof. exact (@lem5149312 (term298 _67214) (term328 _67215 _67214)). Qed.
Lemma lem5149315 (a : Prop) : (term329 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5149316 (_67214 : real -> Prop) : (term330 _67214) = (@FINITE real _67214).
Proof. exact (@lem5149315 (@FINITE real _67214)). Qed.
Lemma lem5149317 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5149318 (_67214 : real -> Prop) : (term331 _67214) = (term332 _67214).
Proof. exact (MK_COMB (@lem5149317) (@lem5149316 _67214)). Qed.
Lemma lem5149320 (a : Prop) (b : Prop) : (term324 a b) = (term325 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5149321 (_67215 : real) (_67214 : real -> Prop) : (term333 _67215 _67214) = (term334 _67215 _67214).
Proof. exact (@lem5149320 (_67214 = (@EMPTY real)) (term306 _67215 _67214)). Qed.
Lemma lem5149323 (a : Prop) : (term329 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5149324 (_67215 : real) (_67214 : real -> Prop) : (term335 _67215 _67214) = (@IN real _67215 _67214).
Proof. exact (@lem5149323 (@IN real _67215 _67214)). Qed.
Lemma lem5149325 (_67214 : real -> Prop) : (term336 _67214) = (term336 _67214).
Proof. exact (eq_refl (term336 _67214)). Qed.
Lemma lem5149326 (_67215 : real) (_67214 : real -> Prop) : (term334 _67215 _67214) = (term337 _67215 _67214).
Proof. exact (MK_COMB (@lem5149325 _67214) (@lem5149324 _67215 _67214)). Qed.
Lemma lem5149327 (_67215 : real) (_67214 : real -> Prop) : (term333 _67215 _67214) = (term337 _67215 _67214).
Proof. exact (TRANS (@lem5149321 _67215 _67214) (@lem5149326 _67215 _67214)). Qed.
Lemma lem5149328 (_67215 : real) (_67214 : real -> Prop) : (term327 _67215 _67214) = (term338 _67215 _67214).
Proof. exact (MK_COMB (@lem5149318 _67214) (@lem5149327 _67215 _67214)). Qed.
Lemma lem5149329 (_67215 : real) (_67214 : real -> Prop) : (term326 _67215 _67214) = (term338 _67215 _67214).
Proof. exact (TRANS (@lem5149313 _67215 _67214) (@lem5149328 _67215 _67214)). Qed.
Lemma lem5149330 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5149331 (_67215 : real) (_67214 : real -> Prop) : (term339 _67215 _67214) = (term340 _67215 _67214).
Proof. exact (MK_COMB (@lem5149330) (@lem5149329 _67215 _67214)). Qed.
Lemma lem5149332 (_67215 : real) (_67214 : real -> Prop) : (term236 _67215 _67214) = (term236 _67215 _67214).
Proof. exact (eq_refl (term236 _67215 _67214)). Qed.
Lemma lem5149333 (_67215 : real) (_67214 : real -> Prop) : (term323 _67215 _67214) = (term341 _67215 _67214).
Proof. exact (MK_COMB (@lem5149331 _67215 _67214) (@lem5149332 _67215 _67214)). Qed.
Lemma lem5149334 (_67215 : real) (_67214 : real -> Prop) : (term319 _67215 _67214) = (term341 _67215 _67214).
Proof. exact (TRANS (@lem5149310 _67215 _67214) (@lem5149333 _67215 _67214)). Qed.
Lemma lem5149336 (s : real -> Prop) (x : real) (a : real) (h1 : term208 x s a) (h2 : term143 s x a) : term337 x s.
Proof. exact (conj (@lem5149147 x s a h1) (@lem5149154 s x a h2)). Qed.
Lemma lem5149337 (s : real -> Prop) (x : real) (a : real) (h1 : term208 x s a) (h2 : term143 s x a) : term338 x s.
Proof. exact (conj (@lem5149140 x s a h1) (@lem5149336 s x a h1 h2)). Qed.
Lemma lem5149339 (_67215 : real) (_67214 : real -> Prop) (h1 : term17) : term341 _67215 _67214.
Proof. exact (EQ_MP (@lem5149334 _67215 _67214) (@lem5149307 _67215 _67214 h1)). Qed.
Lemma lem5149340 (x : real) (s : real -> Prop) (h1 : term17) : term341 x s.
Proof. exact (@lem5149339 x s h1). Qed.
Lemma lem5149343 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term208 x s a) (h3 : term143 s x a) : term236 x s.
Proof. exact (@lem5149340 x s h1 (@lem5149337 s x a h2 h3)). Qed.
Lemma lem5149344 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term208 x s a) (h3 : term143 s x a) : term342 x s.
Proof. exact (fun h0 : term343 x s => @lem5149343 s x a h1 h2 h3). Qed.
Lemma lem5149346 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5149347 (x : real) (s : real -> Prop) : (term342 x s) = (term236 x s).
Proof. exact (@lem5149346 (term236 x s)). Qed.
Lemma lem5149348 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term208 x s a) (h3 : term143 s x a) : term236 x s.
Proof. exact (EQ_MP (@lem5149347 x s) (@lem5149344 s x a h1 h2 h3)). Qed.
Lemma lem5149350 (s : real -> Prop) (x : real) (a : real) (h1 : term143 s x a) : term42 s a.
Proof. exact (proj1 (@lem5148664 s x a h1)). Qed.
Lemma lem5149351 (s : real -> Prop) (x : real) (a : real) (h1 : term143 s x a) : term344 s a.
Proof. exact (fun h0 : term299 s a => @lem5149350 s x a h1). Qed.
Lemma lem5149353 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5149354 (s : real -> Prop) (a : real) : (term344 s a) = (term42 s a).
Proof. exact (@lem5149353 (term42 s a)). Qed.
Lemma lem5149355 (s : real -> Prop) (x : real) (a : real) (h1 : term143 s x a) : term42 s a.
Proof. exact (EQ_MP (@lem5149354 s a) (@lem5149351 s x a h1)). Qed.
Lemma lem5149371 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5149372 (_67211 : real) (_67212 : real) (_67213 : real) : (term345 _67212 _67211 _67213) = (term346 _67211 _67212 _67213).
Proof. exact (@lem5149371 (real_le _67211 _67213) (term296 _67212 _67213)). Qed.
Lemma lem5149378 (_67211 : real) (_67212 : real) : (term347 _67211 _67212) = (term347 _67211 _67212).
Proof. exact (eq_refl (term347 _67211 _67212)). Qed.
Lemma lem5149379 (_67211 : real) (_67212 : real) (_67213 : real) : (term295 _67212 _67211 _67213) = (term348 _67211 _67212 _67213).
Proof. exact (MK_COMB (@lem5149378 _67211 _67212) (@lem5149372 _67211 _67212 _67213)). Qed.
Lemma lem5149383 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5149384 (_67211 : real) (_67212 : real) (_67213 : real) : (term348 _67211 _67212 _67213) = (term349 _67211 _67212 _67213).
Proof. exact (@lem5149383 (real_le _67211 _67213) (term296 _67211 _67212) (term296 _67212 _67213)). Qed.
Lemma lem5149400 (_67211 : real) (_67212 : real) (_67213 : real) : (term295 _67212 _67211 _67213) = (term349 _67211 _67212 _67213).
Proof. exact (TRANS (@lem5149379 _67211 _67212 _67213) (@lem5149384 _67211 _67212 _67213)). Qed.
Lemma lem5149401 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5149402 (_67211 : real) (_67212 : real) (_67213 : real) : (term350 _67212 _67211 _67213) = (term351 _67211 _67212 _67213).
Proof. exact (MK_COMB (@lem5149401) (@lem5149400 _67211 _67212 _67213)). Qed.
Lemma lem5149418 (_67211 : real) (_67212 : real) (_67213 : real) : (term349 _67211 _67212 _67213) = (term349 _67211 _67212 _67213).
Proof. exact (eq_refl (term349 _67211 _67212 _67213)). Qed.
Lemma lem5149419 (_67211 : real) (_67212 : real) (_67213 : real) : ((term295 _67212 _67211 _67213) = (term349 _67211 _67212 _67213)) = ((term349 _67211 _67212 _67213) = (term349 _67211 _67212 _67213)).
Proof. exact (MK_COMB (@lem5149402 _67211 _67212 _67213) (@lem5149418 _67211 _67212 _67213)). Qed.
Lemma lem5149421 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5149422 (x : Prop) : (x = x) = True.
Proof. exact (@lem5149421 Prop x). Qed.
Lemma lem5149423 (_67211 : real) (_67212 : real) (_67213 : real) : ((term349 _67211 _67212 _67213) = (term349 _67211 _67212 _67213)) = True.
Proof. exact (@lem5149422 (term349 _67211 _67212 _67213)). Qed.
Lemma lem5149424 (_67211 : real) (_67212 : real) (_67213 : real) : ((term295 _67212 _67211 _67213) = (term349 _67211 _67212 _67213)) = True.
Proof. exact (TRANS (@lem5149419 _67211 _67212 _67213) (@lem5149423 _67211 _67212 _67213)). Qed.
Lemma lem5149425 (_67211 : real) (_67212 : real) (_67213 : real) : True = ((term295 _67212 _67211 _67213) = (term349 _67211 _67212 _67213)).
Proof. exact (SYM (@lem5149424 _67211 _67212 _67213)). Qed.
Lemma lem5149426 (_67211 : real) (_67212 : real) (_67213 : real) : (term295 _67212 _67211 _67213) = (term349 _67211 _67212 _67213).
Proof. exact (EQ_MP (@lem5149425 _67211 _67212 _67213) (@lem0)). Qed.
Lemma lem5149427 (_67211 : real) (_67212 : real) (_67213 : real) (h1 : term37) : term349 _67211 _67212 _67213.
Proof. exact (EQ_MP (@lem5149426 _67211 _67212 _67213) (@lem5148981 _67212 _67211 _67213 h1)). Qed.
Lemma lem5149429 (b : Prop) (a : Prop) : (a \/ b) = (term322 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5149430 (_67212 : real) (_67211 : real) (_67213 : real) : (term349 _67211 _67212 _67213) = (term352 _67212 _67211 _67213).
Proof. exact (@lem5149429 (term217 _67211 _67212 _67213) (real_le _67211 _67213)). Qed.
Lemma lem5149432 (a : Prop) (b : Prop) : (term324 a b) = (term325 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5149433 (_67211 : real) (_67212 : real) (_67213 : real) : (term353 _67211 _67212 _67213) = (term354 _67211 _67212 _67213).
Proof. exact (@lem5149432 (term296 _67211 _67212) (term296 _67212 _67213)). Qed.
Lemma lem5149435 (a : Prop) : (term329 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5149436 (_67211 : real) (_67212 : real) : (term355 _67211 _67212) = (real_le _67211 _67212).
Proof. exact (@lem5149435 (real_le _67211 _67212)). Qed.
Lemma lem5149437 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5149438 (_67211 : real) (_67212 : real) : (term356 _67211 _67212) = (term357 _67211 _67212).
Proof. exact (MK_COMB (@lem5149437) (@lem5149436 _67211 _67212)). Qed.
Lemma lem5149440 (a : Prop) : (term329 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5149441 (_67212 : real) (_67213 : real) : (term355 _67212 _67213) = (real_le _67212 _67213).
Proof. exact (@lem5149440 (real_le _67212 _67213)). Qed.
Lemma lem5149442 (_67211 : real) (_67212 : real) (_67213 : real) : (term354 _67211 _67212 _67213) = (term222 _67211 _67212 _67213).
Proof. exact (MK_COMB (@lem5149438 _67211 _67212) (@lem5149441 _67212 _67213)). Qed.
Lemma lem5149443 (_67211 : real) (_67212 : real) (_67213 : real) : (term353 _67211 _67212 _67213) = (term222 _67211 _67212 _67213).
Proof. exact (TRANS (@lem5149433 _67211 _67212 _67213) (@lem5149442 _67211 _67212 _67213)). Qed.
Lemma lem5149444 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5149445 (_67211 : real) (_67212 : real) (_67213 : real) : (term358 _67211 _67212 _67213) = (term359 _67211 _67212 _67213).
Proof. exact (MK_COMB (@lem5149444) (@lem5149443 _67211 _67212 _67213)). Qed.
Lemma lem5149446 (_67211 : real) (_67213 : real) : (real_le _67211 _67213) = (real_le _67211 _67213).
Proof. exact (eq_refl (real_le _67211 _67213)). Qed.
Lemma lem5149447 (_67212 : real) (_67211 : real) (_67213 : real) : (term352 _67212 _67211 _67213) = (term31 _67212 _67211 _67213).
Proof. exact (MK_COMB (@lem5149445 _67211 _67212 _67213) (@lem5149446 _67211 _67213)). Qed.
Lemma lem5149448 (_67212 : real) (_67211 : real) (_67213 : real) : (term349 _67211 _67212 _67213) = (term31 _67212 _67211 _67213).
Proof. exact (TRANS (@lem5149430 _67212 _67211 _67213) (@lem5149447 _67212 _67211 _67213)). Qed.
Lemma lem5149450 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term208 x s a) (h3 : term143 s x a) : term360 x s a.
Proof. exact (conj (@lem5149348 s x a h1 h2 h3) (@lem5149355 s x a h3)). Qed.
Lemma lem5149452 (_67212 : real) (_67211 : real) (_67213 : real) (h1 : term37) : term31 _67212 _67211 _67213.
Proof. exact (EQ_MP (@lem5149448 _67212 _67211 _67213) (@lem5149427 _67211 _67212 _67213 h1)). Qed.
Lemma lem5149453 (s : real -> Prop) (x : real) (a : real) (h1 : term37) : term361 s x a.
Proof. exact (@lem5149452 (sup s) x a h1). Qed.
Lemma lem5149456 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) (h4 : term143 s x a) : real_le x a.
Proof. exact (@lem5149453 s x a h2 (@lem5149450 s x a h1 h3 h4)). Qed.
Lemma lem5149457 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) (h4 : term143 s x a) : term362 x a.
Proof. exact (fun h0 : term296 x a => @lem5149456 s x a h1 h2 h3 h4). Qed.
Lemma lem5149459 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5149460 (x : real) (a : real) : (term362 x a) = (real_le x a).
Proof. exact (@lem5149459 (real_le x a)). Qed.
Lemma lem5149461 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) (h4 : term143 s x a) : real_le x a.
Proof. exact (EQ_MP (@lem5149460 x a) (@lem5149457 s x a h1 h2 h3 h4)). Qed.
Lemma lem5149464 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5149466 (x : real) (a : real) : (term296 x a) = (term363 x a).
Proof. exact (@lem5149464 (real_le x a)). Qed.
Lemma lem5149469 (s : real -> Prop) (x : real) (a : real) (h1 : term143 s x a) : term363 x a.
Proof. exact (EQ_MP (@lem5149466 x a) (@lem5148991 s x a h1)). Qed.
Lemma lem5149472 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) (h4 : term143 s x a) : False.
Proof. exact (@lem5149469 s x a h4 (@lem5149461 s x a h1 h2 h3 h4)). Qed.
Lemma lem5149473 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) (h4 : term143 s x a) : term364.
Proof. exact (fun h0 : ~ False => @lem5149472 s x a h1 h2 h3 h4). Qed.
Lemma lem5149475 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5149476 : term364 = False.
Proof. exact (@lem5149475 False). Qed.
Lemma lem5149477 (s : real -> Prop) (x : real) (a : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) (h4 : term143 s x a) : False.
Proof. exact (EQ_MP (@lem5149476) (@lem5149473 s x a h1 h2 h3 h4)). Qed.
Lemma lem5149541 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : @FINITE real s.
Proof. exact (proj1 (@lem5148661 x s a h1)). Qed.
Lemma lem5149542 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term301 s.
Proof. exact (fun h0 : term298 s => @lem5149541 x s a h1). Qed.
Lemma lem5149544 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5149545 (s : real -> Prop) : (term301 s) = (@FINITE real s).
Proof. exact (@lem5149544 (@FINITE real s)). Qed.
Lemma lem5149546 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : @FINITE real s.
Proof. exact (EQ_MP (@lem5149545 s) (@lem5149542 x s a h1)). Qed.
Lemma lem5149548 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term234 s.
Proof. exact (proj2 (@lem5148661 x s a h1)). Qed.
Lemma lem5149549 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term303 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5149548 x s a h1). Qed.
Lemma lem5149551 (p : Prop) : (term304 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5149552 (s : real -> Prop) : (term303 s) = (term234 s).
Proof. exact (@lem5149551 (s = (@EMPTY real))). Qed.
Lemma lem5149553 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term234 s.
Proof. exact (EQ_MP (@lem5149552 s) (@lem5149549 x s a h1)). Qed.
Lemma lem5149559 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5149560 (_67219 : real -> Prop) : (term300 _67219) = (term365 _67219).
Proof. exact (@lem5149559 (_67219 = (@EMPTY real)) (term298 _67219) (term252 _67219)). Qed.
Lemma lem5149576 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5149577 (_67219 : real -> Prop) : (term366 _67219) = (term367 _67219).
Proof. exact (@lem5149576 (term252 _67219) (term298 _67219)). Qed.
Lemma lem5149583 (_67219 : real -> Prop) : (term312 _67219) = (term312 _67219).
Proof. exact (eq_refl (term312 _67219)). Qed.
Lemma lem5149584 (_67219 : real -> Prop) : (term365 _67219) = (term368 _67219).
Proof. exact (MK_COMB (@lem5149583 _67219) (@lem5149577 _67219)). Qed.
Lemma lem5149595 (_67219 : real -> Prop) : (term300 _67219) = (term368 _67219).
Proof. exact (TRANS (@lem5149560 _67219) (@lem5149584 _67219)). Qed.
Lemma lem5149596 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5149597 (_67219 : real -> Prop) : (term369 _67219) = (term370 _67219).
Proof. exact (MK_COMB (@lem5149596) (@lem5149595 _67219)). Qed.
Lemma lem5149611 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5149612 (_67219 : real -> Prop) : (term232 _67219) = (term371 _67219).
Proof. exact (@lem5149611 (_67219 = (@EMPTY real)) (term298 _67219)). Qed.
Lemma lem5149620 (_67219 : real -> Prop) : (term372 _67219) = (term372 _67219).
Proof. exact (eq_refl (term372 _67219)). Qed.
Lemma lem5149621 (_67219 : real -> Prop) : (term373 _67219) = (term374 _67219).
Proof. exact (MK_COMB (@lem5149620 _67219) (@lem5149612 _67219)). Qed.
Lemma lem5149625 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5149626 (_67219 : real -> Prop) : (term374 _67219) = (term368 _67219).
Proof. exact (@lem5149625 (_67219 = (@EMPTY real)) (term252 _67219) (term298 _67219)). Qed.
Lemma lem5149644 (_67219 : real -> Prop) : (term373 _67219) = (term368 _67219).
Proof. exact (TRANS (@lem5149621 _67219) (@lem5149626 _67219)). Qed.
Lemma lem5149645 (_67219 : real -> Prop) : ((term300 _67219) = (term373 _67219)) = ((term368 _67219) = (term368 _67219)).
Proof. exact (MK_COMB (@lem5149597 _67219) (@lem5149644 _67219)). Qed.
Lemma lem5149647 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5149648 (x : Prop) : (x = x) = True.
Proof. exact (@lem5149647 Prop x). Qed.
Lemma lem5149649 (_67219 : real -> Prop) : ((term368 _67219) = (term368 _67219)) = True.
Proof. exact (@lem5149648 (term368 _67219)). Qed.
Lemma lem5149650 (_67219 : real -> Prop) : ((term300 _67219) = (term373 _67219)) = True.
Proof. exact (TRANS (@lem5149645 _67219) (@lem5149649 _67219)). Qed.
Lemma lem5149651 (_67219 : real -> Prop) : True = ((term300 _67219) = (term373 _67219)).
Proof. exact (SYM (@lem5149650 _67219)). Qed.
Lemma lem5149652 (_67219 : real -> Prop) : (term300 _67219) = (term373 _67219).
Proof. exact (EQ_MP (@lem5149651 _67219) (@lem0)). Qed.
Lemma lem5149653 (_67219 : real -> Prop) (h1 : term17) : term373 _67219.
Proof. exact (EQ_MP (@lem5149652 _67219) (@lem5149055 _67219 h1)). Qed.
Lemma lem5149655 (b : Prop) (a : Prop) : (a \/ b) = (term322 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5149656 (_67219 : real -> Prop) : (term373 _67219) = (term375 _67219).
Proof. exact (@lem5149655 (term232 _67219) (term252 _67219)). Qed.
Lemma lem5149658 (a : Prop) (b : Prop) : (term324 a b) = (term325 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5149659 (_67219 : real -> Prop) : (term376 _67219) = (term377 _67219).
Proof. exact (@lem5149658 (term298 _67219) (_67219 = (@EMPTY real))). Qed.
Lemma lem5149661 (a : Prop) : (term329 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5149662 (_67219 : real -> Prop) : (term330 _67219) = (@FINITE real _67219).
Proof. exact (@lem5149661 (@FINITE real _67219)). Qed.
Lemma lem5149663 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5149664 (_67219 : real -> Prop) : (term331 _67219) = (term332 _67219).
Proof. exact (MK_COMB (@lem5149663) (@lem5149662 _67219)). Qed.
Lemma lem5149665 (_67219 : real -> Prop) : (term234 _67219) = (term234 _67219).
Proof. exact (eq_refl (term234 _67219)). Qed.
Lemma lem5149666 (_67219 : real -> Prop) : (term377 _67219) = (term76 _67219).
Proof. exact (MK_COMB (@lem5149664 _67219) (@lem5149665 _67219)). Qed.
Lemma lem5149667 (_67219 : real -> Prop) : (term376 _67219) = (term76 _67219).
Proof. exact (TRANS (@lem5149659 _67219) (@lem5149666 _67219)). Qed.
Lemma lem5149668 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5149669 (_67219 : real -> Prop) : (term378 _67219) = (term28 _67219).
Proof. exact (MK_COMB (@lem5149668) (@lem5149667 _67219)). Qed.
Lemma lem5149670 (_67219 : real -> Prop) : (term252 _67219) = (term252 _67219).
Proof. exact (eq_refl (term252 _67219)). Qed.
Lemma lem5149671 (_67219 : real -> Prop) : (term375 _67219) = (term379 _67219).
Proof. exact (MK_COMB (@lem5149669 _67219) (@lem5149670 _67219)). Qed.
Lemma lem5149672 (_67219 : real -> Prop) : (term373 _67219) = (term379 _67219).
Proof. exact (TRANS (@lem5149656 _67219) (@lem5149671 _67219)). Qed.
Lemma lem5149674 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term76 s.
Proof. exact (conj (@lem5149546 x s a h1) (@lem5149553 x s a h1)). Qed.
Lemma lem5149676 (_67219 : real -> Prop) (h1 : term17) : term379 _67219.
Proof. exact (EQ_MP (@lem5149672 _67219) (@lem5149653 _67219 h1)). Qed.
Lemma lem5149677 (s : real -> Prop) (h1 : term17) : term379 s.
Proof. exact (@lem5149676 s h1). Qed.
Lemma lem5149680 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term208 x s a) : term252 s.
Proof. exact (@lem5149677 s h1 (@lem5149674 x s a h2)). Qed.
Lemma lem5149681 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term208 x s a) : term380 s.
Proof. exact (fun h0 : term381 s => @lem5149680 x s a h1 h2). Qed.
Lemma lem5149683 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5149684 (s : real -> Prop) : (term380 s) = (term252 s).
Proof. exact (@lem5149683 (term252 s)). Qed.
Lemma lem5149685 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term208 x s a) : term252 s.
Proof. exact (EQ_MP (@lem5149684 s) (@lem5149681 x s a h1 h2)). Qed.
Lemma lem5149691 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5149692 (a : real) (_67221 : real) (s : real -> Prop) : (term49 s _67221 a) = (term382 a _67221 s).
Proof. exact (@lem5149691 (real_le _67221 a) (term306 _67221 s)). Qed.
Lemma lem5149698 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5149699 (a : real) (_67221 : real) (s : real -> Prop) : (term383 s _67221 a) = (term384 a _67221 s).
Proof. exact (MK_COMB (@lem5149698) (@lem5149692 a _67221 s)). Qed.
Lemma lem5149705 (a : real) (_67221 : real) (s : real -> Prop) : (term382 a _67221 s) = (term382 a _67221 s).
Proof. exact (eq_refl (term382 a _67221 s)). Qed.
Lemma lem5149706 (a : real) (_67221 : real) (s : real -> Prop) : ((term49 s _67221 a) = (term382 a _67221 s)) = ((term382 a _67221 s) = (term382 a _67221 s)).
Proof. exact (MK_COMB (@lem5149699 a _67221 s) (@lem5149705 a _67221 s)). Qed.
Lemma lem5149708 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5149709 (x : Prop) : (x = x) = True.
Proof. exact (@lem5149708 Prop x). Qed.
Lemma lem5149710 (a : real) (_67221 : real) (s : real -> Prop) : ((term382 a _67221 s) = (term382 a _67221 s)) = True.
Proof. exact (@lem5149709 (term382 a _67221 s)). Qed.
Lemma lem5149711 (a : real) (_67221 : real) (s : real -> Prop) : ((term49 s _67221 a) = (term382 a _67221 s)) = True.
Proof. exact (TRANS (@lem5149706 a _67221 s) (@lem5149710 a _67221 s)). Qed.
Lemma lem5149712 (a : real) (_67221 : real) (s : real -> Prop) : True = ((term49 s _67221 a) = (term382 a _67221 s)).
Proof. exact (SYM (@lem5149711 a _67221 s)). Qed.
Lemma lem5149713 (a : real) (_67221 : real) (s : real -> Prop) : (term49 s _67221 a) = (term382 a _67221 s).
Proof. exact (EQ_MP (@lem5149712 a _67221 s) (@lem0)). Qed.
Lemma lem5149714 (_67221 : real) (s : real -> Prop) (a : real) (h1 : term63 s a) : term382 a _67221 s.
Proof. exact (EQ_MP (@lem5149713 a _67221 s) (@lem5149043 _67221 s a h1)). Qed.
Lemma lem5149716 (b : Prop) (a : Prop) : (a \/ b) = (term322 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5149717 (s : real -> Prop) (_67221 : real) (a : real) : (term382 a _67221 s) = (term385 s _67221 a).
Proof. exact (@lem5149716 (term306 _67221 s) (real_le _67221 a)). Qed.
Lemma lem5149719 (a : Prop) : (term329 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5149720 (_67221 : real) (s : real -> Prop) : (term335 _67221 s) = (@IN real _67221 s).
Proof. exact (@lem5149719 (@IN real _67221 s)). Qed.
Lemma lem5149721 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5149722 (_67221 : real) (s : real -> Prop) : (term386 _67221 s) = (term387 _67221 s).
Proof. exact (MK_COMB (@lem5149721) (@lem5149720 _67221 s)). Qed.
Lemma lem5149723 (_67221 : real) (a : real) : (real_le _67221 a) = (real_le _67221 a).
Proof. exact (eq_refl (real_le _67221 a)). Qed.
Lemma lem5149724 (s : real -> Prop) (_67221 : real) (a : real) : (term385 s _67221 a) = (term38 s _67221 a).
Proof. exact (MK_COMB (@lem5149722 _67221 s) (@lem5149723 _67221 a)). Qed.
Lemma lem5149725 (s : real -> Prop) (_67221 : real) (a : real) : (term382 a _67221 s) = (term38 s _67221 a).
Proof. exact (TRANS (@lem5149717 s _67221 a) (@lem5149724 s _67221 a)). Qed.
Lemma lem5149728 (_67221 : real) (s : real -> Prop) (a : real) (h1 : term63 s a) : term38 s _67221 a.
Proof. exact (EQ_MP (@lem5149725 s _67221 a) (@lem5149714 _67221 s a h1)). Qed.
Lemma lem5149729 (s : real -> Prop) (a : real) (h1 : term63 s a) : term388 s a.
Proof. exact (@lem5149728 (sup s) s a h1). Qed.
Lemma lem5149732 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term63 s a) (h3 : term208 x s a) : term42 s a.
Proof. exact (@lem5149729 s a h2 (@lem5149685 x s a h1 h3)). Qed.
Lemma lem5149733 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term63 s a) (h3 : term208 x s a) : term344 s a.
Proof. exact (fun h0 : term299 s a => @lem5149732 x s a h1 h2 h3). Qed.
Lemma lem5149735 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5149736 (s : real -> Prop) (a : real) : (term344 s a) = (term42 s a).
Proof. exact (@lem5149735 (term42 s a)). Qed.
Lemma lem5149737 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term63 s a) (h3 : term208 x s a) : term42 s a.
Proof. exact (EQ_MP (@lem5149736 s a) (@lem5149733 x s a h1 h2 h3)). Qed.
Lemma lem5149740 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5149742 (s : real -> Prop) (a : real) : (term299 s a) = (term389 s a).
Proof. exact (@lem5149740 (term42 s a)). Qed.
Lemma lem5149745 (s : real -> Prop) (a : real) (h1 : term63 s a) : term389 s a.
Proof. exact (EQ_MP (@lem5149742 s a) (@lem5149037 s a h1)). Qed.
Lemma lem5149748 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term63 s a) (h3 : term208 x s a) : False.
Proof. exact (@lem5149745 s a h2 (@lem5149737 x s a h1 h2 h3)). Qed.
Lemma lem5149749 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term63 s a) (h3 : term208 x s a) : term364.
Proof. exact (fun h0 : ~ False => @lem5149748 x s a h1 h2 h3). Qed.
Lemma lem5149751 (p : Prop) : (term302 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5149752 : term364 = False.
Proof. exact (@lem5149751 False). Qed.
Lemma lem5149753 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term63 s a) (h3 : term208 x s a) : False.
Proof. exact (EQ_MP (@lem5149752) (@lem5149749 x s a h1 h2 h3)). Qed.
Lemma lem5149754 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) : False.
Proof. exact (or_elim (@lem5148660 x s a h3) (fun h0 : term143 s x a => @lem5149477 s x a h1 h2 h3 h0) (fun h0 : term63 s a => @lem5149753 x s a h1 h0 h3)). Qed.
Lemma lem5149755 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) : (term208 x s a) = False.
Proof. exact (prop_ext (fun h4 : term208 x s a => @lem5149754 x s a h1 h2 h3) (fun h4 : False => @lem5148659 x s a h3)). Qed.
Lemma lem5149756 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) : False.
Proof. exact (EQ_MP (@lem5149755 x s a h1 h2 h3) (@lem5148659 x s a h3)). Qed.
Lemma lem5149757 (s : real -> Prop) (a : real) (h1 : term17) (h2 : term37) (h3 : term211 s a) : False.
Proof. exact (ex_elim (@lem5148498 s a h3) (fun x : real => fun h0 : term210 s a x => @lem5149756 x s a h1 h2 h0)). Qed.
Lemma lem5149758 (s : real -> Prop) (h1 : term17) (h2 : term37) (h3 : term213 s) : False.
Proof. exact (ex_elim (@lem5148497 s h3) (fun a : real => fun h0 : term212 s a => @lem5149757 s a h1 h2 h0)). Qed.
Lemma lem5149759 (h1 : term17) (h2 : term37) (h3 : term10) : False.
Proof. exact (ex_elim (@lem5148281 h3) (fun s : real -> Prop => fun h0 : term214 s => @lem5149758 s h1 h2 h0)). Qed.
Lemma lem5149760 (h1 : term37) (h2 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem5149759 h0 h1 h2). Qed.
Lemma lem5149761 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem5149762 (h1 : term37) (h2 : term10) : term16.
Proof. exact (EQ_MP (@lem5149761) (@lem5149760 h1 h2)). Qed.
Lemma lem5149763 (h1 : term10) : term20.
Proof. exact (fun h0 : term37 => @lem5149762 h0 h1). Qed.
Lemma lem5149764 : term22.
Proof. exact (fun h0 : term10 => @lem5149763 h0). Qed.
Lemma lem5149765 : term11.
Proof. exact (EQ_MP (@lem5147775) (@lem5149764)). Qed.
Lemma lem5149767 : term11.
Proof. exact (@lem5147551 (@lem5149765)). Qed.
Lemma lem5149768 (h1 : term10) : term19.
Proof. exact (@lem5149767 (@lem5147536 h1)). Qed.
Lemma lem5149769 (h1 : term10) : term15.
Proof. exact (@lem5149768 h1 (@lem1339577)). Qed.
Lemma lem5149770 (h1 : term10) : False.
Proof. exact (@lem5149769 h1 (@lem5145274)). Qed.
Lemma lem5149771 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem5149770 h1) (fun h2 : False => @lem5147536 h1)). Qed.
Lemma lem5149772 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem5149771 h1) (@lem5147536 h1)). Qed.
Lemma lem5149773 : term9.
Proof. exact (fun h0 : term10 => @lem5149772 h0). Qed.
Lemma lem5149774 : term8.
Proof. exact (EQ_MP (@lem5147535) (@lem5149773)). Qed.
