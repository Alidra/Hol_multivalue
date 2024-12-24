Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_WLOG_LE_3_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339697_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
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
Lemma lem1866513 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1866514 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1866515 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1866514 t1) (@lem1866513 t1)). Qed.
Lemma lem1866516 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1866515 t1 t2). Qed.
Lemma lem1866517 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1866518 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1866517 t1 t2) (@lem1866516 t1 t2)). Qed.
Lemma lem1866519 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1866518 t1 t2 t3). Qed.
Lemma lem1866520 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1866521 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1866520 t1 t2 t3) (@lem1866519 t1 t2 t3)). Qed.
Lemma lem1866522 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1866521 t1 t2 t3)). Qed.
Lemma lem1866524 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1866525 : term8 = term9.
Proof. exact (@lem1866524 term8). Qed.
Lemma lem1866526 : term9 = term8.
Proof. exact (SYM (@lem1866525)). Qed.
Lemma lem1866527 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1866530 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1866531 : term12.
Proof. exact (fun h0 : term11 => @lem1866530 h0). Qed.
Lemma lem1866532 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1866533 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1866534 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1866532 h2 (@lem1866533 h1)). Qed.
Lemma lem1866535 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem1866534 h1 h0). Qed.
Lemma lem1866536 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1866537 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1866535 h1 (@lem1866536 h2)). Qed.
Lemma lem1866538 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem1866537 h0 h1). Qed.
Lemma lem1866539 : term14.
Proof. exact (fun h0 : term12 => @lem1866538 h0). Qed.
Lemma lem1866542 : term12.
Proof. exact (@lem1866539 (@lem1866531)). Qed.
Lemma lem1866598 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1866599 : term15 = term16.
Proof. exact (@lem1866598 term17). Qed.
Lemma lem1866654 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1866661 : term11 = term19.
Proof. exact (MK_COMB (@lem1866654) (@lem1866599)). Qed.
Lemma lem1866666 (y : real) (x : real) : (term20 y x) = (term20 y x).
Proof. exact (eq_refl (term20 y x)). Qed.
Lemma lem1866667 (x : real) : (term21 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1866666 y x)). Qed.
Lemma lem1866668 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1866669 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1866668) (@lem1866667 x)). Qed.
Lemma lem1866670 : term23 = term23.
Proof. exact (fun_ext (fun x : real => @lem1866669 x)). Qed.
Lemma lem1866671 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1866672 : term17 = term17.
Proof. exact (MK_COMB (@lem1866671) (@lem1866670)). Qed.
Lemma lem1866673 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1866674 : term16 = term16.
Proof. exact (MK_COMB (@lem1866673) (@lem1866672)). Qed.
Lemma lem1866675 (P : type1624) (x : real) (y : real) (z : real) : (P x y z) = (P x y z).
Proof. exact (eq_refl (P x y z)). Qed.
Lemma lem1866676 (P : type1624) (x : real) (y : real) : (term24 P x y) = (term24 P x y).
Proof. exact (fun_ext (fun z : real => @lem1866675 P x y z)). Qed.
Lemma lem1866677 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1866678 (P : type1624) (x : real) (y : real) : (term25 P x y) = (term25 P x y).
Proof. exact (MK_COMB (@lem1866677) (@lem1866676 P x y)). Qed.
Lemma lem1866679 (P : type1624) (x : real) : (term26 P x) = (term26 P x).
Proof. exact (fun_ext (fun y : real => @lem1866678 P x y)). Qed.
Lemma lem1866680 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1866681 (P : type1624) (x : real) : (term27 P x) = (term27 P x).
Proof. exact (MK_COMB (@lem1866680) (@lem1866679 P x)). Qed.
Lemma lem1866682 (P : type1624) : (term28 P) = (term28 P).
Proof. exact (fun_ext (fun x : real => @lem1866681 P x)). Qed.
Lemma lem1866683 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1866684 (P : type1624) : (term29 P) = (term29 P).
Proof. exact (MK_COMB (@lem1866683) (@lem1866682 P)). Qed.
Lemma lem1866693 (P : type1624) (x : real) (y : real) (z : real) : (term30 P x y z) = (term30 P x y z).
Proof. exact (eq_refl (term30 P x y z)). Qed.
Lemma lem1866694 (P : type1624) (x : real) (y : real) : (term31 P x y) = (term31 P x y).
Proof. exact (fun_ext (fun z : real => @lem1866693 P x y z)). Qed.
Lemma lem1866695 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1866696 (P : type1624) (x : real) (y : real) : (term32 P x y) = (term32 P x y).
Proof. exact (MK_COMB (@lem1866695) (@lem1866694 P x y)). Qed.
Lemma lem1866697 (P : type1624) (x : real) : (term33 P x) = (term33 P x).
Proof. exact (fun_ext (fun y : real => @lem1866696 P x y)). Qed.
Lemma lem1866698 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1866699 (P : type1624) (x : real) : (term34 P x) = (term34 P x).
Proof. exact (MK_COMB (@lem1866698) (@lem1866697 P x)). Qed.
Lemma lem1866700 (P : type1624) : (term35 P) = (term35 P).
Proof. exact (fun_ext (fun x : real => @lem1866699 P x)). Qed.
Lemma lem1866701 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1866702 (P : type1624) : (term36 P) = (term36 P).
Proof. exact (MK_COMB (@lem1866701) (@lem1866700 P)). Qed.
Lemma lem1866711 (P : type1624) (x : real) (z : real) (y : real) : (term37 P x z y) = (term37 P x z y).
Proof. exact (eq_refl (term37 P x z y)). Qed.
Lemma lem1866712 (P : type1624) (x : real) (y : real) : (term38 P x y) = (term38 P x y).
Proof. exact (fun_ext (fun z : real => @lem1866711 P x z y)). Qed.
Lemma lem1866713 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1866714 (P : type1624) (x : real) (y : real) : (term39 P x y) = (term39 P x y).
Proof. exact (MK_COMB (@lem1866713) (@lem1866712 P x y)). Qed.
Lemma lem1866715 (P : type1624) (x : real) : (term40 P x) = (term40 P x).
Proof. exact (fun_ext (fun y : real => @lem1866714 P x y)). Qed.
Lemma lem1866716 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1866717 (P : type1624) (x : real) : (term41 P x) = (term41 P x).
Proof. exact (MK_COMB (@lem1866716) (@lem1866715 P x)). Qed.
Lemma lem1866718 (P : type1624) : (term42 P) = (term42 P).
Proof. exact (fun_ext (fun x : real => @lem1866717 P x)). Qed.
Lemma lem1866719 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1866720 (P : type1624) : (term43 P) = (term43 P).
Proof. exact (MK_COMB (@lem1866719) (@lem1866718 P)). Qed.
Lemma lem1866721 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1866722 (P : type1624) : (term44 P) = (term44 P).
Proof. exact (MK_COMB (@lem1866721) (@lem1866720 P)). Qed.
Lemma lem1866723 (P : type1624) : (term45 P) = (term45 P).
Proof. exact (MK_COMB (@lem1866722 P) (@lem1866702 P)). Qed.
Lemma lem1866724 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1866725 (P : type1624) : (term46 P) = (term46 P).
Proof. exact (MK_COMB (@lem1866724) (@lem1866723 P)). Qed.
Lemma lem1866726 (P : type1624) : (term47 P) = (term47 P).
Proof. exact (MK_COMB (@lem1866725 P) (@lem1866684 P)). Qed.
Lemma lem1866727 : term48 = term48.
Proof. exact (fun_ext (fun P : type1624 => @lem1866726 P)). Qed.
Lemma lem1866728 : (@all (real -> real -> real -> Prop)) = (@all (real -> real -> real -> Prop)).
Proof. exact (eq_refl (@all (real -> real -> real -> Prop))). Qed.
Lemma lem1866729 : term8 = term8.
Proof. exact (MK_COMB (@lem1866728) (@lem1866727)). Qed.
Lemma lem1866730 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1866731 : term10 = term10.
Proof. exact (MK_COMB (@lem1866730) (@lem1866729)). Qed.
Lemma lem1866732 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1866733 : term18 = term18.
Proof. exact (MK_COMB (@lem1866732) (@lem1866731)). Qed.
Lemma lem1866734 : term19 = term19.
Proof. exact (MK_COMB (@lem1866733) (@lem1866674)). Qed.
Lemma lem1866825 : term11 = term19.
Proof. exact (TRANS (@lem1866661) (@lem1866734)). Qed.
Lemma lem1866826 : term19 = term11.
Proof. exact (SYM (@lem1866825)). Qed.
Lemma lem1866827 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1866828 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1866839 (P : type1624) (x : real) (z : real) (y : real) : (term37 P x z y) = (term49 P x z y).
Proof. exact (@lem17265 (P x y z) (term50 P x z y)). Qed.
Lemma lem1866840 (P : type1624) (x : real) (y : real) : (term38 P x y) = (term51 P x y).
Proof. exact (fun_ext (fun z : real => @lem1866839 P x z y)). Qed.
Lemma lem1866841 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1866842 (P : type1624) (x : real) (y : real) : (term39 P x y) = (term52 P x y).
Proof. exact (MK_COMB (@lem1866841) (@lem1866840 P x y)). Qed.
Lemma lem1866843 (P : type1624) (x : real) : (term40 P x) = (term53 P x).
Proof. exact (fun_ext (fun y : real => @lem1866842 P x y)). Qed.
Lemma lem1866844 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1866845 (P : type1624) (x : real) : (term41 P x) = (term54 P x).
Proof. exact (MK_COMB (@lem1866844) (@lem1866843 P x)). Qed.
Lemma lem1866846 (P : type1624) : (term42 P) = (term55 P).
Proof. exact (fun_ext (fun x : real => @lem1866845 P x)). Qed.
Lemma lem1866847 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1866848 (P : type1624) : (term43 P) = (term56 P).
Proof. exact (MK_COMB (@lem1866847) (@lem1866846 P)). Qed.
Lemma lem1866855 (x : real) (y : real) (z : real) : (term57 x y z) = (term58 x y z).
Proof. exact (@lem17045 (real_le x y) (real_le y z)). Qed.
Lemma lem1866856 (P : type1624) (x : real) (y : real) (z : real) : (P x y z) = (P x y z).
Proof. exact (eq_refl (P x y z)). Qed.
Lemma lem1866857 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1866858 (x : real) (y : real) (z : real) : (term59 x y z) = (term60 x y z).
Proof. exact (MK_COMB (@lem1866857) (@lem1866855 x y z)). Qed.
Lemma lem1866859 (P : type1624) (x : real) (y : real) (z : real) : (term61 P x y z) = (term62 P x y z).
Proof. exact (MK_COMB (@lem1866858 x y z) (@lem1866856 P x y z)). Qed.
Lemma lem1866860 (P : type1624) (x : real) (y : real) (z : real) : (term30 P x y z) = (term61 P x y z).
Proof. exact (@lem17265 (term63 x y z) (P x y z)). Qed.
Lemma lem1866861 (P : type1624) (x : real) (y : real) (z : real) : (term30 P x y z) = (term62 P x y z).
Proof. exact (TRANS (@lem1866860 P x y z) (@lem1866859 P x y z)). Qed.
Lemma lem1866862 (P : type1624) (x : real) (y : real) : (term31 P x y) = (term64 P x y).
Proof. exact (fun_ext (fun z : real => @lem1866861 P x y z)). Qed.
Lemma lem1866863 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1866864 (P : type1624) (x : real) (y : real) : (term32 P x y) = (term65 P x y).
Proof. exact (MK_COMB (@lem1866863) (@lem1866862 P x y)). Qed.
Lemma lem1866865 (P : type1624) (x : real) : (term33 P x) = (term66 P x).
Proof. exact (fun_ext (fun y : real => @lem1866864 P x y)). Qed.
Lemma lem1866866 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1866867 (P : type1624) (x : real) : (term34 P x) = (term67 P x).
Proof. exact (MK_COMB (@lem1866866) (@lem1866865 P x)). Qed.
Lemma lem1866868 (P : type1624) : (term35 P) = (term68 P).
Proof. exact (fun_ext (fun x : real => @lem1866867 P x)). Qed.
Lemma lem1866869 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1866870 (P : type1624) : (term36 P) = (term69 P).
Proof. exact (MK_COMB (@lem1866869) (@lem1866868 P)). Qed.
Lemma lem1866871 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1866872 (P : type1624) : (term44 P) = (term70 P).
Proof. exact (MK_COMB (@lem1866871) (@lem1866848 P)). Qed.
Lemma lem1866873 (P : type1624) : (term45 P) = (term71 P).
Proof. exact (MK_COMB (@lem1866872 P) (@lem1866870 P)). Qed.
Lemma lem1866875 (P : real -> Prop) : (term72 P) = (term73 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1866876 (P : type1624) (x : real) (y : real) : (term74 P x y) = (term75 P x y).
Proof. exact (@lem1866875 (term24 P x y)). Qed.
Lemma lem1866877 (P : type1624) (x : real) (y : real) (z : real) : (term76 P x y z) = (P x y z).
Proof. exact (eq_refl (term76 P x y z)). Qed.
Lemma lem1866878 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1866880 (P : type1624) (x : real) (y : real) (z : real) : (term77 P x y z) = (term78 P x y z).
Proof. exact (MK_COMB (@lem1866878) (@lem1866877 P x y z)). Qed.
Lemma lem1866881 (P : type1624) (x : real) (y : real) : (term79 P x y) = (term80 P x y).
Proof. exact (fun_ext (fun z : real => @lem1866880 P x y z)). Qed.
Lemma lem1866882 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1866883 (P : type1624) (x : real) (y : real) : (term75 P x y) = (term81 P x y).
Proof. exact (MK_COMB (@lem1866882) (@lem1866881 P x y)). Qed.
Lemma lem1866884 (P : type1624) (x : real) (y : real) : (term74 P x y) = (term81 P x y).
Proof. exact (TRANS (@lem1866876 P x y) (@lem1866883 P x y)). Qed.
Lemma lem1866885 (P : real -> Prop) : (term72 P) = (term73 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1866886 (P : type1624) (x : real) : (term82 P x) = (term83 P x).
Proof. exact (@lem1866885 (term26 P x)). Qed.
Lemma lem1866887 (P : type1624) (x : real) (y : real) : (term84 P x y) = (term25 P x y).
Proof. exact (eq_refl (term84 P x y)). Qed.
Lemma lem1866888 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1866889 (P : type1624) (x : real) (y : real) : (term85 P x y) = (term74 P x y).
Proof. exact (MK_COMB (@lem1866888) (@lem1866887 P x y)). Qed.
Lemma lem1866890 (P : type1624) (x : real) (y : real) : (term85 P x y) = (term81 P x y).
Proof. exact (TRANS (@lem1866889 P x y) (@lem1866884 P x y)). Qed.
Lemma lem1866891 (P : type1624) (x : real) : (term86 P x) = (term87 P x).
Proof. exact (fun_ext (fun y : real => @lem1866890 P x y)). Qed.
Lemma lem1866892 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1866893 (P : type1624) (x : real) : (term83 P x) = (term88 P x).
Proof. exact (MK_COMB (@lem1866892) (@lem1866891 P x)). Qed.
Lemma lem1866894 (P : type1624) (x : real) : (term82 P x) = (term88 P x).
Proof. exact (TRANS (@lem1866886 P x) (@lem1866893 P x)). Qed.
Lemma lem1866895 (P : real -> Prop) : (term72 P) = (term73 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1866896 (P : type1624) : (term89 P) = (term90 P).
Proof. exact (@lem1866895 (term28 P)). Qed.
Lemma lem1866897 (P : type1624) (x : real) : (term91 P x) = (term27 P x).
Proof. exact (eq_refl (term91 P x)). Qed.
Lemma lem1866898 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1866899 (P : type1624) (x : real) : (term92 P x) = (term82 P x).
Proof. exact (MK_COMB (@lem1866898) (@lem1866897 P x)). Qed.
Lemma lem1866900 (P : type1624) (x : real) : (term92 P x) = (term88 P x).
Proof. exact (TRANS (@lem1866899 P x) (@lem1866894 P x)). Qed.
Lemma lem1866901 (P : type1624) : (term93 P) = (term94 P).
Proof. exact (fun_ext (fun x : real => @lem1866900 P x)). Qed.
Lemma lem1866902 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1866903 (P : type1624) : (term90 P) = (term95 P).
Proof. exact (MK_COMB (@lem1866902) (@lem1866901 P)). Qed.
Lemma lem1866904 (P : type1624) : (term89 P) = (term95 P).
Proof. exact (TRANS (@lem1866896 P) (@lem1866903 P)). Qed.
Lemma lem1866905 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1866906 (P : type1624) : (term96 P) = (term97 P).
Proof. exact (MK_COMB (@lem1866905) (@lem1866873 P)). Qed.
Lemma lem1866907 (P : type1624) : (term98 P) = (term99 P).
Proof. exact (MK_COMB (@lem1866906 P) (@lem1866904 P)). Qed.
Lemma lem1866908 (P : type1624) : (term100 P) = (term98 P).
Proof. exact (@lem17362 (term45 P) (term29 P)). Qed.
Lemma lem1866909 (P : type1624) : (term100 P) = (term99 P).
Proof. exact (TRANS (@lem1866908 P) (@lem1866907 P)). Qed.
Lemma lem1866910 (P : type1013) : (term101 P) = (term102 P).
Proof. exact (@lem18392 type1624 P). Qed.
Lemma lem1866911 : term10 = term103.
Proof. exact (@lem1866910 term48). Qed.
Lemma lem1866912 (P : type1624) : (term104 P) = (term47 P).
Proof. exact (eq_refl (term104 P)). Qed.
Lemma lem1866913 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1866914 (P : type1624) : (term105 P) = (term100 P).
Proof. exact (MK_COMB (@lem1866913) (@lem1866912 P)). Qed.
Lemma lem1866915 (P : type1624) : (term105 P) = (term99 P).
Proof. exact (TRANS (@lem1866914 P) (@lem1866909 P)). Qed.
Lemma lem1866916 : term106 = term107.
Proof. exact (fun_ext (fun P : type1624 => @lem1866915 P)). Qed.
Lemma lem1866917 : (@ex (real -> real -> real -> Prop)) = (@ex (real -> real -> real -> Prop)).
Proof. exact (eq_refl (@ex (real -> real -> real -> Prop))). Qed.
Lemma lem1866918 : term103 = term108.
Proof. exact (MK_COMB (@lem1866917) (@lem1866916)). Qed.
Lemma lem1866919 : term10 = term108.
Proof. exact (TRANS (@lem1866911) (@lem1866918)). Qed.
Lemma lem1867094 {A : Type'} (P : Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1867095 (P : Prop) (Q : real -> Prop) : (term111 P Q) = (term112 P Q).
Proof. exact (@lem1867094 real P Q). Qed.
Lemma lem1867096 (P : type1624) : (term113 P) = (term114 P).
Proof. exact (@lem1867095 (term71 P) (term94 P)). Qed.
Lemma lem1867097 (P : type1624) (x : real) : (term115 P x) = (term88 P x).
Proof. exact (eq_refl (term115 P x)). Qed.
Lemma lem1867098 (P : type1624) : (term116 P) = (term94 P).
Proof. exact (fun_ext (fun x : real => @lem1867097 P x)). Qed.
Lemma lem1867099 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1867100 (P : type1624) : (term117 P) = (term95 P).
Proof. exact (MK_COMB (@lem1867099) (@lem1867098 P)). Qed.
Lemma lem1867101 (P : type1624) : (term97 P) = (term97 P).
Proof. exact (eq_refl (term97 P)). Qed.
Lemma lem1867102 (P : type1624) : (term113 P) = (term99 P).
Proof. exact (MK_COMB (@lem1867101 P) (@lem1867100 P)). Qed.
Lemma lem1867103 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1867104 (P : type1624) : (term118 P) = (term119 P).
Proof. exact (MK_COMB (@lem1867103) (@lem1867102 P)). Qed.
Lemma lem1867105 (P : type1624) (x : real) : (term115 P x) = (term88 P x).
Proof. exact (eq_refl (term115 P x)). Qed.
Lemma lem1867106 (P : type1624) : (term97 P) = (term97 P).
Proof. exact (eq_refl (term97 P)). Qed.
Lemma lem1867107 (P : type1624) (x : real) : (term120 P x) = (term121 P x).
Proof. exact (MK_COMB (@lem1867106 P) (@lem1867105 P x)). Qed.
Lemma lem1867108 (P : type1624) : (term122 P) = (term123 P).
Proof. exact (fun_ext (fun x : real => @lem1867107 P x)). Qed.
Lemma lem1867109 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1867110 (P : type1624) : (term114 P) = (term124 P).
Proof. exact (MK_COMB (@lem1867109) (@lem1867108 P)). Qed.
Lemma lem1867111 (P : type1624) : ((term113 P) = (term114 P)) = ((term99 P) = (term124 P)).
Proof. exact (MK_COMB (@lem1867104 P) (@lem1867110 P)). Qed.
Lemma lem1867112 (P : type1624) : (term99 P) = (term124 P).
Proof. exact (EQ_MP (@lem1867111 P) (@lem1867096 P)). Qed.
Lemma lem1867114 {A : Type'} (P : Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1867115 (P : Prop) (Q : real -> Prop) : (term111 P Q) = (term112 P Q).
Proof. exact (@lem1867114 real P Q). Qed.
Lemma lem1867116 (P : type1624) (x : real) : (term125 P x) = (term126 P x).
Proof. exact (@lem1867115 (term71 P) (term87 P x)). Qed.
Lemma lem1867117 (P : type1624) (x : real) (y : real) : (term127 P x y) = (term81 P x y).
Proof. exact (eq_refl (term127 P x y)). Qed.
Lemma lem1867118 (P : type1624) (x : real) : (term128 P x) = (term87 P x).
Proof. exact (fun_ext (fun y : real => @lem1867117 P x y)). Qed.
Lemma lem1867119 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1867120 (P : type1624) (x : real) : (term129 P x) = (term88 P x).
Proof. exact (MK_COMB (@lem1867119) (@lem1867118 P x)). Qed.
Lemma lem1867121 (P : type1624) : (term97 P) = (term97 P).
Proof. exact (eq_refl (term97 P)). Qed.
Lemma lem1867122 (P : type1624) (x : real) : (term125 P x) = (term121 P x).
Proof. exact (MK_COMB (@lem1867121 P) (@lem1867120 P x)). Qed.
Lemma lem1867123 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1867124 (P : type1624) (x : real) : (term130 P x) = (term131 P x).
Proof. exact (MK_COMB (@lem1867123) (@lem1867122 P x)). Qed.
Lemma lem1867125 (P : type1624) (x : real) (y : real) : (term127 P x y) = (term81 P x y).
Proof. exact (eq_refl (term127 P x y)). Qed.
Lemma lem1867126 (P : type1624) : (term97 P) = (term97 P).
Proof. exact (eq_refl (term97 P)). Qed.
Lemma lem1867127 (P : type1624) (x : real) (y : real) : (term132 P x y) = (term133 P x y).
Proof. exact (MK_COMB (@lem1867126 P) (@lem1867125 P x y)). Qed.
Lemma lem1867128 (P : type1624) (x : real) : (term134 P x) = (term135 P x).
Proof. exact (fun_ext (fun y : real => @lem1867127 P x y)). Qed.
Lemma lem1867129 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1867130 (P : type1624) (x : real) : (term126 P x) = (term136 P x).
Proof. exact (MK_COMB (@lem1867129) (@lem1867128 P x)). Qed.
Lemma lem1867131 (P : type1624) (x : real) : ((term125 P x) = (term126 P x)) = ((term121 P x) = (term136 P x)).
Proof. exact (MK_COMB (@lem1867124 P x) (@lem1867130 P x)). Qed.
Lemma lem1867132 (P : type1624) (x : real) : (term121 P x) = (term136 P x).
Proof. exact (EQ_MP (@lem1867131 P x) (@lem1867116 P x)). Qed.
Lemma lem1867134 {A : Type'} (P : Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1867135 (P : Prop) (Q : real -> Prop) : (term111 P Q) = (term112 P Q).
Proof. exact (@lem1867134 real P Q). Qed.
Lemma lem1867136 (P : type1624) (x : real) (y : real) : (term137 P x y) = (term138 P x y).
Proof. exact (@lem1867135 (term71 P) (term80 P x y)). Qed.
Lemma lem1867137 (P : type1624) (x : real) (y : real) (z : real) : (term139 P x y z) = (term78 P x y z).
Proof. exact (eq_refl (term139 P x y z)). Qed.
Lemma lem1867138 (P : type1624) (x : real) (y : real) : (term140 P x y) = (term80 P x y).
Proof. exact (fun_ext (fun z : real => @lem1867137 P x y z)). Qed.
Lemma lem1867139 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1867140 (P : type1624) (x : real) (y : real) : (term141 P x y) = (term81 P x y).
Proof. exact (MK_COMB (@lem1867139) (@lem1867138 P x y)). Qed.
Lemma lem1867141 (P : type1624) : (term97 P) = (term97 P).
Proof. exact (eq_refl (term97 P)). Qed.
Lemma lem1867142 (P : type1624) (x : real) (y : real) : (term137 P x y) = (term133 P x y).
Proof. exact (MK_COMB (@lem1867141 P) (@lem1867140 P x y)). Qed.
Lemma lem1867143 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1867144 (P : type1624) (x : real) (y : real) : (term142 P x y) = (term143 P x y).
Proof. exact (MK_COMB (@lem1867143) (@lem1867142 P x y)). Qed.
Lemma lem1867145 (P : type1624) (x : real) (y : real) (z : real) : (term139 P x y z) = (term78 P x y z).
Proof. exact (eq_refl (term139 P x y z)). Qed.
Lemma lem1867146 (P : type1624) : (term97 P) = (term97 P).
Proof. exact (eq_refl (term97 P)). Qed.
Lemma lem1867147 (P : type1624) (x : real) (y : real) (z : real) : (term144 P x y z) = (term145 P x y z).
Proof. exact (MK_COMB (@lem1867146 P) (@lem1867145 P x y z)). Qed.
Lemma lem1867148 (P : type1624) (x : real) (y : real) : (term146 P x y) = (term147 P x y).
Proof. exact (fun_ext (fun z : real => @lem1867147 P x y z)). Qed.
Lemma lem1867149 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1867150 (P : type1624) (x : real) (y : real) : (term138 P x y) = (term148 P x y).
Proof. exact (MK_COMB (@lem1867149) (@lem1867148 P x y)). Qed.
Lemma lem1867151 (P : type1624) (x : real) (y : real) : ((term137 P x y) = (term138 P x y)) = ((term133 P x y) = (term148 P x y)).
Proof. exact (MK_COMB (@lem1867144 P x y) (@lem1867150 P x y)). Qed.
Lemma lem1867152 (P : type1624) (x : real) (y : real) : (term133 P x y) = (term148 P x y).
Proof. exact (EQ_MP (@lem1867151 P x y) (@lem1867136 P x y)). Qed.
Lemma lem1867153 (P : type1624) (x : real) : (term135 P x) = (term149 P x).
Proof. exact (fun_ext (fun y : real => @lem1867152 P x y)). Qed.
Lemma lem1867154 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1867155 (P : type1624) (x : real) : (term136 P x) = (term150 P x).
Proof. exact (MK_COMB (@lem1867154) (@lem1867153 P x)). Qed.
Lemma lem1867156 (P : type1624) (x : real) : (term121 P x) = (term150 P x).
Proof. exact (TRANS (@lem1867132 P x) (@lem1867155 P x)). Qed.
Lemma lem1867157 (P : type1624) : (term123 P) = (term151 P).
Proof. exact (fun_ext (fun x : real => @lem1867156 P x)). Qed.
Lemma lem1867158 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1867159 (P : type1624) : (term124 P) = (term152 P).
Proof. exact (MK_COMB (@lem1867158) (@lem1867157 P)). Qed.
Lemma lem1867160 (P : type1624) : (term99 P) = (term152 P).
Proof. exact (TRANS (@lem1867112 P) (@lem1867159 P)). Qed.
Lemma lem1867161 : term107 = term153.
Proof. exact (fun_ext (fun P : type1624 => @lem1867160 P)). Qed.
Lemma lem1867162 : (@ex (real -> real -> real -> Prop)) = (@ex (real -> real -> real -> Prop)).
Proof. exact (eq_refl (@ex (real -> real -> real -> Prop))). Qed.
Lemma lem1867164 : term108 = term154.
Proof. exact (MK_COMB (@lem1867162) (@lem1867161)). Qed.
Lemma lem1867165 : term10 = term154.
Proof. exact (TRANS (@lem1866919) (@lem1867164)). Qed.
Lemma lem1867166 (h1 : term10) : term154.
Proof. exact (EQ_MP (@lem1867165) (@lem1866827 h1)). Qed.
Lemma lem1867171 (y : real) (x : real) : (term20 y x) = (term20 y x).
Proof. exact (eq_refl (term20 y x)). Qed.
Lemma lem1867172 (x : real) : (term21 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1867171 y x)). Qed.
Lemma lem1867173 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1867174 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1867173) (@lem1867172 x)). Qed.
Lemma lem1867175 : term23 = term23.
Proof. exact (fun_ext (fun x : real => @lem1867174 x)). Qed.
Lemma lem1867176 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1867233 : term17 = term17.
Proof. exact (MK_COMB (@lem1867176) (@lem1867175)). Qed.
Lemma lem1867234 (h1 : term17) : term17.
Proof. exact (EQ_MP (@lem1867233) (@lem1866828 h1)). Qed.
Lemma lem1867235 (P : type1624) (h1 : term152 P) : term152 P.
Proof. exact (h1). Qed.
Lemma lem1867236 (P : type1624) (x : real) (h1 : term150 P x) : term150 P x.
Proof. exact (h1). Qed.
Lemma lem1867237 (P : type1624) (x : real) (y : real) (h1 : term148 P x y) : term148 P x y.
Proof. exact (h1). Qed.
Lemma lem1867238 (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term145 P x y z.
Proof. exact (h1). Qed.
Lemma lem1867251 (y : real) (x : real) : (term20 y x) = (term20 y x).
Proof. exact (eq_refl (term20 y x)). Qed.
Lemma lem1867252 (x : real) : (term21 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1867251 y x)). Qed.
Lemma lem1867253 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1867254 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1867253) (@lem1867252 x)). Qed.
Lemma lem1867255 : term23 = term23.
Proof. exact (fun_ext (fun x : real => @lem1867254 x)). Qed.
Lemma lem1867256 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1867257 : term17 = term17.
Proof. exact (MK_COMB (@lem1867256) (@lem1867255)). Qed.
Lemma lem1867258 (h1 : term17) : term17.
Proof. exact (EQ_MP (@lem1867257) (@lem1867234 h1)). Qed.
Lemma lem1867267 (P : type1624) (x : real) (y : real) (z : real) : (term78 P x y z) = (term78 P x y z).
Proof. exact (eq_refl (term78 P x y z)). Qed.
Lemma lem1867294 (P : type1624) (x : real) (y : real) (z : real) : (term62 P x y z) = (term62 P x y z).
Proof. exact (eq_refl (term62 P x y z)). Qed.
Lemma lem1867295 (P : type1624) (x : real) (y : real) : (term64 P x y) = (term64 P x y).
Proof. exact (fun_ext (fun z : real => @lem1867294 P x y z)). Qed.
Lemma lem1867296 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1867297 (P : type1624) (x : real) (y : real) : (term65 P x y) = (term65 P x y).
Proof. exact (MK_COMB (@lem1867296) (@lem1867295 P x y)). Qed.
Lemma lem1867298 (P : type1624) (x : real) : (term66 P x) = (term66 P x).
Proof. exact (fun_ext (fun y : real => @lem1867297 P x y)). Qed.
Lemma lem1867299 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1867300 (P : type1624) (x : real) : (term67 P x) = (term67 P x).
Proof. exact (MK_COMB (@lem1867299) (@lem1867298 P x)). Qed.
Lemma lem1867301 (P : type1624) : (term68 P) = (term68 P).
Proof. exact (fun_ext (fun x : real => @lem1867300 P x)). Qed.
Lemma lem1867302 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1867303 (P : type1624) : (term69 P) = (term69 P).
Proof. exact (MK_COMB (@lem1867302) (@lem1867301 P)). Qed.
Lemma lem1867332 (P : type1624) (x : real) (z : real) (y : real) : (term49 P x z y) = (term49 P x z y).
Proof. exact (eq_refl (term49 P x z y)). Qed.
Lemma lem1867333 (P : type1624) (x : real) (y : real) : (term51 P x y) = (term51 P x y).
Proof. exact (fun_ext (fun z : real => @lem1867332 P x z y)). Qed.
Lemma lem1867334 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1867335 (P : type1624) (x : real) (y : real) : (term52 P x y) = (term52 P x y).
Proof. exact (MK_COMB (@lem1867334) (@lem1867333 P x y)). Qed.
Lemma lem1867336 (P : type1624) (x : real) : (term53 P x) = (term53 P x).
Proof. exact (fun_ext (fun y : real => @lem1867335 P x y)). Qed.
Lemma lem1867337 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1867338 (P : type1624) (x : real) : (term54 P x) = (term54 P x).
Proof. exact (MK_COMB (@lem1867337) (@lem1867336 P x)). Qed.
Lemma lem1867339 (P : type1624) : (term55 P) = (term55 P).
Proof. exact (fun_ext (fun x : real => @lem1867338 P x)). Qed.
Lemma lem1867340 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1867341 (P : type1624) : (term56 P) = (term56 P).
Proof. exact (MK_COMB (@lem1867340) (@lem1867339 P)). Qed.
Lemma lem1867342 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1867343 (P : type1624) : (term70 P) = (term70 P).
Proof. exact (MK_COMB (@lem1867342) (@lem1867341 P)). Qed.
Lemma lem1867344 (P : type1624) : (term71 P) = (term71 P).
Proof. exact (MK_COMB (@lem1867343 P) (@lem1867303 P)). Qed.
Lemma lem1867345 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1867346 (P : type1624) : (term97 P) = (term97 P).
Proof. exact (MK_COMB (@lem1867345) (@lem1867344 P)). Qed.
Lemma lem1867347 (P : type1624) (x : real) (y : real) (z : real) : (term145 P x y z) = (term145 P x y z).
Proof. exact (MK_COMB (@lem1867346 P) (@lem1867267 P x y z)). Qed.
Lemma lem1867348 (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term145 P x y z.
Proof. exact (EQ_MP (@lem1867347 P x y z) (@lem1867238 P x y z h1)). Qed.
Lemma lem1867350 (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term71 P.
Proof. exact (proj1 (@lem1867348 P x y z h1)). Qed.
Lemma lem1867351 (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term69 P.
Proof. exact (proj2 (@lem1867350 P x y z h1)). Qed.
Lemma lem1867352 (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term56 P.
Proof. exact (proj1 (@lem1867350 P x y z h1)). Qed.
Lemma lem1867360 (y : real) (x : real) : (term20 y x) = (term20 y x).
Proof. exact (eq_refl (term20 y x)). Qed.
Lemma lem1867361 (x : real) : (term21 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1867360 y x)). Qed.
Lemma lem1867362 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1867363 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1867362) (@lem1867361 x)). Qed.
Lemma lem1867364 : term23 = term23.
Proof. exact (fun_ext (fun x : real => @lem1867363 x)). Qed.
Lemma lem1867365 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1867367 : term17 = term17.
Proof. exact (MK_COMB (@lem1867365) (@lem1867364)). Qed.
Lemma lem1867368 (h1 : term17) : term17.
Proof. exact (EQ_MP (@lem1867367) (@lem1867258 h1)). Qed.
Lemma lem1867390 (P : type1624) (x : real) (z : real) (y : real) : (term49 P x z y) = (term155 P x z y).
Proof. exact (@lem19490 (P y x z) (term78 P x y z) (P x z y)). Qed.
Lemma lem1867391 (P : type1624) (x : real) (y : real) : (term51 P x y) = (term156 P x y).
Proof. exact (fun_ext (fun z : real => @lem1867390 P x z y)). Qed.
Lemma lem1867392 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1867393 (P : type1624) (x : real) (y : real) : (term52 P x y) = (term157 P x y).
Proof. exact (MK_COMB (@lem1867392) (@lem1867391 P x y)). Qed.
Lemma lem1867394 (P : type1624) (x : real) : (term53 P x) = (term158 P x).
Proof. exact (fun_ext (fun y : real => @lem1867393 P x y)). Qed.
Lemma lem1867395 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1867396 (P : type1624) (x : real) : (term54 P x) = (term159 P x).
Proof. exact (MK_COMB (@lem1867395) (@lem1867394 P x)). Qed.
Lemma lem1867397 (P : type1624) : (term55 P) = (term160 P).
Proof. exact (fun_ext (fun x : real => @lem1867396 P x)). Qed.
Lemma lem1867398 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1867400 (P : type1624) : (term56 P) = (term161 P).
Proof. exact (MK_COMB (@lem1867398) (@lem1867397 P)). Qed.
Lemma lem1867401 (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term161 P.
Proof. exact (EQ_MP (@lem1867400 P) (@lem1867352 P x y z h1)). Qed.
Lemma lem1867415 (P : type1624) (x : real) (y : real) (z : real) : (term62 P x y z) = (term62 P x y z).
Proof. exact (eq_refl (term62 P x y z)). Qed.
Lemma lem1867416 (P : type1624) (x : real) (y : real) : (term64 P x y) = (term64 P x y).
Proof. exact (fun_ext (fun z : real => @lem1867415 P x y z)). Qed.
Lemma lem1867417 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1867418 (P : type1624) (x : real) (y : real) : (term65 P x y) = (term65 P x y).
Proof. exact (MK_COMB (@lem1867417) (@lem1867416 P x y)). Qed.
Lemma lem1867419 (P : type1624) (x : real) : (term66 P x) = (term66 P x).
Proof. exact (fun_ext (fun y : real => @lem1867418 P x y)). Qed.
Lemma lem1867420 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1867421 (P : type1624) (x : real) : (term67 P x) = (term67 P x).
Proof. exact (MK_COMB (@lem1867420) (@lem1867419 P x)). Qed.
Lemma lem1867422 (P : type1624) : (term68 P) = (term68 P).
Proof. exact (fun_ext (fun x : real => @lem1867421 P x)). Qed.
Lemma lem1867423 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1867425 (P : type1624) : (term69 P) = (term69 P).
Proof. exact (MK_COMB (@lem1867423) (@lem1867422 P)). Qed.
Lemma lem1867426 (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term69 P.
Proof. exact (EQ_MP (@lem1867425 P) (@lem1867351 P x y z h1)). Qed.
Lemma lem1867427 (_27014 : real) (h1 : term17) : term162 _27014.
Proof. exact (@lem1867368 h1 _27014). Qed.
Lemma lem1867428 (_27014 : real) : (term162 _27014) = (term22 _27014).
Proof. exact (eq_refl (term162 _27014)). Qed.
Lemma lem1867429 (_27014 : real) (h1 : term17) : term22 _27014.
Proof. exact (EQ_MP (@lem1867428 _27014) (@lem1867427 _27014 h1)). Qed.
Lemma lem1867430 (_27014 : real) (_27015 : real) (h1 : term17) : term163 _27014 _27015.
Proof. exact (@lem1867429 _27014 h1 _27015). Qed.
Lemma lem1867431 (_27015 : real) (_27014 : real) : (term163 _27014 _27015) = (term20 _27015 _27014).
Proof. exact (eq_refl (term163 _27014 _27015)). Qed.
Lemma lem1867433 (_27016 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term164 P _27016.
Proof. exact (@lem1867401 P x y z h1 _27016). Qed.
Lemma lem1867434 (P : type1624) (_27016 : real) : (term164 P _27016) = (term159 P _27016).
Proof. exact (eq_refl (term164 P _27016)). Qed.
Lemma lem1867435 (_27016 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term159 P _27016.
Proof. exact (EQ_MP (@lem1867434 P _27016) (@lem1867433 _27016 P x y z h1)). Qed.
Lemma lem1867436 (_27016 : real) (_27017 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term165 P _27016 _27017.
Proof. exact (@lem1867435 _27016 P x y z h1 _27017). Qed.
Lemma lem1867437 (P : type1624) (_27016 : real) (_27017 : real) : (term165 P _27016 _27017) = (term157 P _27016 _27017).
Proof. exact (eq_refl (term165 P _27016 _27017)). Qed.
Lemma lem1867438 (_27016 : real) (_27017 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term157 P _27016 _27017.
Proof. exact (EQ_MP (@lem1867437 P _27016 _27017) (@lem1867436 _27016 _27017 P x y z h1)). Qed.
Lemma lem1867439 (_27016 : real) (_27017 : real) (_27018 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term166 P _27016 _27017 _27018.
Proof. exact (@lem1867438 _27016 _27017 P x y z h1 _27018). Qed.
Lemma lem1867440 (P : type1624) (_27016 : real) (_27018 : real) (_27017 : real) : (term166 P _27016 _27017 _27018) = (term155 P _27016 _27018 _27017).
Proof. exact (eq_refl (term166 P _27016 _27017 _27018)). Qed.
Lemma lem1867441 (_27016 : real) (_27018 : real) (_27017 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term155 P _27016 _27018 _27017.
Proof. exact (EQ_MP (@lem1867440 P _27016 _27018 _27017) (@lem1867439 _27016 _27017 _27018 P x y z h1)). Qed.
Lemma lem1867442 (_27019 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term167 P _27019.
Proof. exact (@lem1867426 P x y z h1 _27019). Qed.
Lemma lem1867443 (P : type1624) (_27019 : real) : (term167 P _27019) = (term67 P _27019).
Proof. exact (eq_refl (term167 P _27019)). Qed.
Lemma lem1867444 (_27019 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term67 P _27019.
Proof. exact (EQ_MP (@lem1867443 P _27019) (@lem1867442 _27019 P x y z h1)). Qed.
Lemma lem1867445 (_27019 : real) (_27020 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term168 P _27019 _27020.
Proof. exact (@lem1867444 _27019 P x y z h1 _27020). Qed.
Lemma lem1867446 (P : type1624) (_27019 : real) (_27020 : real) : (term168 P _27019 _27020) = (term65 P _27019 _27020).
Proof. exact (eq_refl (term168 P _27019 _27020)). Qed.
Lemma lem1867447 (_27019 : real) (_27020 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term65 P _27019 _27020.
Proof. exact (EQ_MP (@lem1867446 P _27019 _27020) (@lem1867445 _27019 _27020 P x y z h1)). Qed.
Lemma lem1867448 (_27019 : real) (_27020 : real) (_27021 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term169 P _27019 _27020 _27021.
Proof. exact (@lem1867447 _27019 _27020 P x y z h1 _27021). Qed.
Lemma lem1867449 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term169 P _27019 _27020 _27021) = (term62 P _27019 _27020 _27021).
Proof. exact (eq_refl (term169 P _27019 _27020 _27021)). Qed.
Lemma lem1867450 (_27019 : real) (_27020 : real) (_27021 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term62 P _27019 _27020 _27021.
Proof. exact (EQ_MP (@lem1867449 P _27019 _27020 _27021) (@lem1867448 _27019 _27020 _27021 P x y z h1)). Qed.
Lemma lem1867458 (_27015 : real) (_27014 : real) (h1 : term17) : term20 _27015 _27014.
Proof. exact (EQ_MP (@lem1867431 _27015 _27014) (@lem1867430 _27014 _27015 h1)). Qed.
Lemma lem1867460 (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term78 P x y z.
Proof. exact (proj2 (@lem1867348 P x y z h1)). Qed.
Lemma lem1867471 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term62 P _27019 _27020 _27021) = (term170 P _27019 _27020 _27021).
Proof. exact (@lem1866522 (term171 _27019 _27020) (term171 _27020 _27021) (P _27019 _27020 _27021)). Qed.
Lemma lem1867472 (_27019 : real) (_27020 : real) (_27021 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term170 P _27019 _27020 _27021.
Proof. exact (EQ_MP (@lem1867471 P _27019 _27020 _27021) (@lem1867450 _27019 _27020 _27021 P x y z h1)). Qed.
Lemma lem1867478 (_27017 : real) (_27016 : real) (_27018 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term172 P _27017 _27016 _27018.
Proof. exact (proj1 (@lem1867441 _27016 _27018 _27017 P x y z h1)). Qed.
Lemma lem1867484 (_27016 : real) (_27018 : real) (_27017 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term173 P _27016 _27018 _27017.
Proof. exact (proj2 (@lem1867441 _27016 _27018 _27017 P x y z h1)). Qed.
Lemma lem1867487 (z : real) (y : real) (h1 : term171 z y) : term171 z y.
Proof. exact (h1). Qed.
Lemma lem1867488 (z : real) (y : real) (h1 : term171 z y) : term174 z y.
Proof. exact (fun h0 : real_le z y => @lem1867487 z y h1). Qed.
Lemma lem1867490 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1867491 (z : real) (y : real) : (term174 z y) = (term171 z y).
Proof. exact (@lem1867490 (real_le z y)). Qed.
Lemma lem1867492 (z : real) (y : real) (h1 : term171 z y) : term171 z y.
Proof. exact (EQ_MP (@lem1867491 z y) (@lem1867488 z y h1)). Qed.
Lemma lem1867503 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1867504 (_27015 : real) (_27014 : real) : (term20 _27014 _27015) = (term20 _27015 _27014).
Proof. exact (@lem1867503 (real_le _27014 _27015) (real_le _27015 _27014)). Qed.
Lemma lem1867510 (_27015 : real) (_27014 : real) : (term176 _27015 _27014) = (term176 _27015 _27014).
Proof. exact (eq_refl (term176 _27015 _27014)). Qed.
Lemma lem1867511 (_27015 : real) (_27014 : real) : ((term20 _27015 _27014) = (term20 _27014 _27015)) = ((term20 _27015 _27014) = (term20 _27015 _27014)).
Proof. exact (MK_COMB (@lem1867510 _27015 _27014) (@lem1867504 _27015 _27014)). Qed.
Lemma lem1867513 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1867514 (x : Prop) : (x = x) = True.
Proof. exact (@lem1867513 Prop x). Qed.
Lemma lem1867515 (_27015 : real) (_27014 : real) : ((term20 _27015 _27014) = (term20 _27015 _27014)) = True.
Proof. exact (@lem1867514 (term20 _27015 _27014)). Qed.
Lemma lem1867516 (_27014 : real) (_27015 : real) : ((term20 _27015 _27014) = (term20 _27014 _27015)) = True.
Proof. exact (TRANS (@lem1867511 _27015 _27014) (@lem1867515 _27015 _27014)). Qed.
Lemma lem1867517 (_27014 : real) (_27015 : real) : True = ((term20 _27015 _27014) = (term20 _27014 _27015)).
Proof. exact (SYM (@lem1867516 _27014 _27015)). Qed.
Lemma lem1867518 (_27014 : real) (_27015 : real) : (term20 _27015 _27014) = (term20 _27014 _27015).
Proof. exact (EQ_MP (@lem1867517 _27014 _27015) (@lem0)). Qed.
Lemma lem1867519 (_27014 : real) (_27015 : real) (h1 : term17) : term20 _27014 _27015.
Proof. exact (EQ_MP (@lem1867518 _27014 _27015) (@lem1867458 _27015 _27014 h1)). Qed.
Lemma lem1867521 (b : Prop) (a : Prop) : (a \/ b) = (term177 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1867524 (_27015 : real) (_27014 : real) : (term20 _27014 _27015) = (term178 _27015 _27014).
Proof. exact (@lem1867521 (real_le _27014 _27015) (real_le _27015 _27014)). Qed.
Lemma lem1867527 (_27015 : real) (_27014 : real) (h1 : term17) : term178 _27015 _27014.
Proof. exact (EQ_MP (@lem1867524 _27015 _27014) (@lem1867519 _27014 _27015 h1)). Qed.
Lemma lem1867528 (y : real) (z : real) (h1 : term17) : term178 y z.
Proof. exact (@lem1867527 y z h1). Qed.
Lemma lem1867531 (z : real) (y : real) (h1 : term17) (h2 : term171 z y) : real_le y z.
Proof. exact (@lem1867528 y z h1 (@lem1867492 z y h2)). Qed.
Lemma lem1867532 (z : real) (y : real) (h1 : term17) (h2 : term171 z y) : term179 y z.
Proof. exact (fun h0 : term171 y z => @lem1867531 z y h1 h2). Qed.
Lemma lem1867534 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1867535 (y : real) (z : real) : (term179 y z) = (real_le y z).
Proof. exact (@lem1867534 (real_le y z)). Qed.
Lemma lem1867536 (z : real) (y : real) (h1 : term17) (h2 : term171 z y) : real_le y z.
Proof. exact (EQ_MP (@lem1867535 y z) (@lem1867532 z y h1 h2)). Qed.
Lemma lem1867539 (P : type1624) (x : real) (y : real) (z : real) (h1 : term78 P x y z) : term78 P x y z.
Proof. exact (h1). Qed.
Lemma lem1867540 (P : type1624) (x : real) (y : real) (z : real) (h1 : term78 P x y z) : term181 P x y z.
Proof. exact (fun h0 : P x y z => @lem1867539 P x y z h1). Qed.
Lemma lem1867542 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1867543 (P : type1624) (x : real) (y : real) (z : real) : (term181 P x y z) = (term78 P x y z).
Proof. exact (@lem1867542 (P x y z)). Qed.
Lemma lem1867544 (P : type1624) (x : real) (y : real) (z : real) (h1 : term78 P x y z) : term78 P x y z.
Proof. exact (EQ_MP (@lem1867543 P x y z) (@lem1867540 P x y z h1)). Qed.
Lemma lem1867546 (b : Prop) (a : Prop) : (a \/ b) = (term177 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1867549 (P : type1624) (_27016 : real) (_27017 : real) (_27018 : real) : (term172 P _27017 _27016 _27018) = (term182 P _27016 _27017 _27018).
Proof. exact (@lem1867546 (P _27017 _27016 _27018) (term78 P _27016 _27017 _27018)). Qed.
Lemma lem1867552 (_27016 : real) (_27017 : real) (_27018 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term182 P _27016 _27017 _27018.
Proof. exact (EQ_MP (@lem1867549 P _27016 _27017 _27018) (@lem1867478 _27017 _27016 _27018 P x y z h1)). Qed.
Lemma lem1867553 (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term182 P y x z.
Proof. exact (@lem1867552 y x z P x y z h1). Qed.
Lemma lem1867556 (P : type1624) (x : real) (y : real) (z : real) (h1 : term78 P x y z) (h2 : term145 P x y z) : term78 P y x z.
Proof. exact (@lem1867553 P x y z h2 (@lem1867544 P x y z h1)). Qed.
Lemma lem1867557 (P : type1624) (x : real) (y : real) (z : real) (h1 : term78 P x y z) (h2 : term145 P x y z) : term181 P y x z.
Proof. exact (fun h0 : P y x z => @lem1867556 P x y z h1 h2). Qed.
Lemma lem1867559 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1867560 (P : type1624) (y : real) (x : real) (z : real) : (term181 P y x z) = (term78 P y x z).
Proof. exact (@lem1867559 (P y x z)). Qed.
Lemma lem1867561 (P : type1624) (x : real) (y : real) (z : real) (h1 : term78 P x y z) (h2 : term145 P x y z) : term78 P y x z.
Proof. exact (EQ_MP (@lem1867560 P y x z) (@lem1867557 P x y z h1 h2)). Qed.
Lemma lem1867563 (b : Prop) (a : Prop) : (a \/ b) = (term177 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1867566 (P : type1624) (_27016 : real) (_27017 : real) (_27018 : real) : (term173 P _27016 _27018 _27017) = (term183 P _27016 _27017 _27018).
Proof. exact (@lem1867563 (P _27016 _27018 _27017) (term78 P _27016 _27017 _27018)). Qed.
Lemma lem1867569 (_27016 : real) (_27017 : real) (_27018 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term183 P _27016 _27017 _27018.
Proof. exact (EQ_MP (@lem1867566 P _27016 _27017 _27018) (@lem1867484 _27016 _27018 _27017 P x y z h1)). Qed.
Lemma lem1867570 (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term183 P y z x.
Proof. exact (@lem1867569 y z x P x y z h1). Qed.
Lemma lem1867573 (P : type1624) (x : real) (y : real) (z : real) (h1 : term78 P x y z) (h2 : term145 P x y z) : term78 P y z x.
Proof. exact (@lem1867570 P x y z h2 (@lem1867561 P x y z h1 h2)). Qed.
Lemma lem1867574 (P : type1624) (x : real) (y : real) (z : real) (h1 : term78 P x y z) (h2 : term145 P x y z) : term181 P y z x.
Proof. exact (fun h0 : P y z x => @lem1867573 P x y z h1 h2). Qed.
Lemma lem1867576 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1867577 (P : type1624) (y : real) (z : real) (x : real) : (term181 P y z x) = (term78 P y z x).
Proof. exact (@lem1867576 (P y z x)). Qed.
Lemma lem1867578 (P : type1624) (x : real) (y : real) (z : real) (h1 : term78 P x y z) (h2 : term145 P x y z) : term78 P y z x.
Proof. exact (EQ_MP (@lem1867577 P y z x) (@lem1867574 P x y z h1 h2)). Qed.
Lemma lem1867594 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1867595 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term184 P _27019 _27020 _27021) = (term185 P _27019 _27020 _27021).
Proof. exact (@lem1867594 (P _27019 _27020 _27021) (term171 _27020 _27021)). Qed.
Lemma lem1867601 (_27019 : real) (_27020 : real) : (term186 _27019 _27020) = (term186 _27019 _27020).
Proof. exact (eq_refl (term186 _27019 _27020)). Qed.
Lemma lem1867602 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term170 P _27019 _27020 _27021) = (term187 P _27019 _27020 _27021).
Proof. exact (MK_COMB (@lem1867601 _27019 _27020) (@lem1867595 P _27019 _27020 _27021)). Qed.
Lemma lem1867606 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1867607 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term187 P _27019 _27020 _27021) = (term188 P _27019 _27020 _27021).
Proof. exact (@lem1867606 (P _27019 _27020 _27021) (term171 _27019 _27020) (term171 _27020 _27021)). Qed.
Lemma lem1867623 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term170 P _27019 _27020 _27021) = (term188 P _27019 _27020 _27021).
Proof. exact (TRANS (@lem1867602 P _27019 _27020 _27021) (@lem1867607 P _27019 _27020 _27021)). Qed.
Lemma lem1867624 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1867625 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term189 P _27019 _27020 _27021) = (term190 P _27019 _27020 _27021).
Proof. exact (MK_COMB (@lem1867624) (@lem1867623 P _27019 _27020 _27021)). Qed.
Lemma lem1867629 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1867630 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term191 P _27019 _27020 _27021) = (term170 P _27019 _27020 _27021).
Proof. exact (@lem1867629 (term171 _27019 _27020) (term171 _27020 _27021) (P _27019 _27020 _27021)). Qed.
Lemma lem1867644 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1867645 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term184 P _27019 _27020 _27021) = (term185 P _27019 _27020 _27021).
Proof. exact (@lem1867644 (P _27019 _27020 _27021) (term171 _27020 _27021)). Qed.
Lemma lem1867651 (_27019 : real) (_27020 : real) : (term186 _27019 _27020) = (term186 _27019 _27020).
Proof. exact (eq_refl (term186 _27019 _27020)). Qed.
Lemma lem1867652 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term170 P _27019 _27020 _27021) = (term187 P _27019 _27020 _27021).
Proof. exact (MK_COMB (@lem1867651 _27019 _27020) (@lem1867645 P _27019 _27020 _27021)). Qed.
Lemma lem1867656 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1867657 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term187 P _27019 _27020 _27021) = (term188 P _27019 _27020 _27021).
Proof. exact (@lem1867656 (P _27019 _27020 _27021) (term171 _27019 _27020) (term171 _27020 _27021)). Qed.
Lemma lem1867673 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term170 P _27019 _27020 _27021) = (term188 P _27019 _27020 _27021).
Proof. exact (TRANS (@lem1867652 P _27019 _27020 _27021) (@lem1867657 P _27019 _27020 _27021)). Qed.
Lemma lem1867674 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term191 P _27019 _27020 _27021) = (term188 P _27019 _27020 _27021).
Proof. exact (TRANS (@lem1867630 P _27019 _27020 _27021) (@lem1867673 P _27019 _27020 _27021)). Qed.
Lemma lem1867675 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : ((term170 P _27019 _27020 _27021) = (term191 P _27019 _27020 _27021)) = ((term188 P _27019 _27020 _27021) = (term188 P _27019 _27020 _27021)).
Proof. exact (MK_COMB (@lem1867625 P _27019 _27020 _27021) (@lem1867674 P _27019 _27020 _27021)). Qed.
Lemma lem1867677 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1867678 (x : Prop) : (x = x) = True.
Proof. exact (@lem1867677 Prop x). Qed.
Lemma lem1867679 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : ((term188 P _27019 _27020 _27021) = (term188 P _27019 _27020 _27021)) = True.
Proof. exact (@lem1867678 (term188 P _27019 _27020 _27021)). Qed.
Lemma lem1867680 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : ((term170 P _27019 _27020 _27021) = (term191 P _27019 _27020 _27021)) = True.
Proof. exact (TRANS (@lem1867675 P _27019 _27020 _27021) (@lem1867679 P _27019 _27020 _27021)). Qed.
Lemma lem1867681 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : True = ((term170 P _27019 _27020 _27021) = (term191 P _27019 _27020 _27021)).
Proof. exact (SYM (@lem1867680 P _27019 _27020 _27021)). Qed.
Lemma lem1867682 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term170 P _27019 _27020 _27021) = (term191 P _27019 _27020 _27021).
Proof. exact (EQ_MP (@lem1867681 P _27019 _27020 _27021) (@lem0)). Qed.
Lemma lem1867683 (_27019 : real) (_27020 : real) (_27021 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term191 P _27019 _27020 _27021.
Proof. exact (EQ_MP (@lem1867682 P _27019 _27020 _27021) (@lem1867472 _27019 _27020 _27021 P x y z h1)). Qed.
Lemma lem1867685 (b : Prop) (a : Prop) : (a \/ b) = (term177 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1867686 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term191 P _27019 _27020 _27021) = (term192 P _27019 _27020 _27021).
Proof. exact (@lem1867685 (term193 P _27019 _27020 _27021) (term171 _27020 _27021)). Qed.
Lemma lem1867688 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1867689 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term196 P _27019 _27020 _27021) = (term197 P _27019 _27020 _27021).
Proof. exact (@lem1867688 (term171 _27019 _27020) (P _27019 _27020 _27021)). Qed.
Lemma lem1867691 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1867692 (_27019 : real) (_27020 : real) : (term199 _27019 _27020) = (real_le _27019 _27020).
Proof. exact (@lem1867691 (real_le _27019 _27020)). Qed.
Lemma lem1867693 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1867694 (_27019 : real) (_27020 : real) : (term200 _27019 _27020) = (term201 _27019 _27020).
Proof. exact (MK_COMB (@lem1867693) (@lem1867692 _27019 _27020)). Qed.
Lemma lem1867695 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term78 P _27019 _27020 _27021) = (term78 P _27019 _27020 _27021).
Proof. exact (eq_refl (term78 P _27019 _27020 _27021)). Qed.
Lemma lem1867696 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term197 P _27019 _27020 _27021) = (term202 P _27019 _27020 _27021).
Proof. exact (MK_COMB (@lem1867694 _27019 _27020) (@lem1867695 P _27019 _27020 _27021)). Qed.
Lemma lem1867697 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term196 P _27019 _27020 _27021) = (term202 P _27019 _27020 _27021).
Proof. exact (TRANS (@lem1867689 P _27019 _27020 _27021) (@lem1867696 P _27019 _27020 _27021)). Qed.
Lemma lem1867698 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1867699 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term203 P _27019 _27020 _27021) = (term204 P _27019 _27020 _27021).
Proof. exact (MK_COMB (@lem1867698) (@lem1867697 P _27019 _27020 _27021)). Qed.
Lemma lem1867700 (_27020 : real) (_27021 : real) : (term171 _27020 _27021) = (term171 _27020 _27021).
Proof. exact (eq_refl (term171 _27020 _27021)). Qed.
Lemma lem1867701 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term192 P _27019 _27020 _27021) = (term205 P _27019 _27020 _27021).
Proof. exact (MK_COMB (@lem1867699 P _27019 _27020 _27021) (@lem1867700 _27020 _27021)). Qed.
Lemma lem1867702 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term191 P _27019 _27020 _27021) = (term205 P _27019 _27020 _27021).
Proof. exact (TRANS (@lem1867686 P _27019 _27020 _27021) (@lem1867701 P _27019 _27020 _27021)). Qed.
Lemma lem1867704 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term145 P x y z) : term202 P y z x.
Proof. exact (conj (@lem1867536 z y h1 h2) (@lem1867578 P x y z h3 h4)). Qed.
Lemma lem1867706 (_27019 : real) (_27020 : real) (_27021 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term205 P _27019 _27020 _27021.
Proof. exact (EQ_MP (@lem1867702 P _27019 _27020 _27021) (@lem1867683 _27019 _27020 _27021 P x y z h1)). Qed.
Lemma lem1867707 (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term205 P y z x.
Proof. exact (@lem1867706 y z x P x y z h1). Qed.
Lemma lem1867710 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term145 P x y z) : term171 z x.
Proof. exact (@lem1867707 P x y z h4 (@lem1867704 P x y z h1 h2 h3 h4)). Qed.
Lemma lem1867711 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term145 P x y z) : term174 z x.
Proof. exact (fun h0 : real_le z x => @lem1867710 P x y z h1 h2 h3 h4). Qed.
Lemma lem1867713 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1867714 (z : real) (x : real) : (term174 z x) = (term171 z x).
Proof. exact (@lem1867713 (real_le z x)). Qed.
Lemma lem1867715 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term145 P x y z) : term171 z x.
Proof. exact (EQ_MP (@lem1867714 z x) (@lem1867711 P x y z h1 h2 h3 h4)). Qed.
Lemma lem1867717 (_27015 : real) (_27014 : real) (h1 : term17) : term178 _27015 _27014.
Proof. exact (EQ_MP (@lem1867524 _27015 _27014) (@lem1867519 _27014 _27015 h1)). Qed.
Lemma lem1867718 (x : real) (z : real) (h1 : term17) : term178 x z.
Proof. exact (@lem1867717 x z h1). Qed.
Lemma lem1867721 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term145 P x y z) : real_le x z.
Proof. exact (@lem1867718 x z h1 (@lem1867715 P x y z h1 h2 h3 h4)). Qed.
Lemma lem1867722 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term145 P x y z) : term179 x z.
Proof. exact (fun h0 : term171 x z => @lem1867721 P x y z h1 h2 h3 h4). Qed.
Lemma lem1867724 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1867725 (x : real) (z : real) : (term179 x z) = (real_le x z).
Proof. exact (@lem1867724 (real_le x z)). Qed.
Lemma lem1867726 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term145 P x y z) : real_le x z.
Proof. exact (EQ_MP (@lem1867725 x z) (@lem1867722 P x y z h1 h2 h3 h4)). Qed.
Lemma lem1867729 (P : type1624) (z : real) (y : real) (x : real) (h1 : term78 P z y x) : term78 P z y x.
Proof. exact (h1). Qed.
Lemma lem1867730 (P : type1624) (z : real) (y : real) (x : real) (h1 : term78 P z y x) : term181 P z y x.
Proof. exact (fun h0 : P z y x => @lem1867729 P z y x h1). Qed.
Lemma lem1867732 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1867733 (P : type1624) (z : real) (y : real) (x : real) : (term181 P z y x) = (term78 P z y x).
Proof. exact (@lem1867732 (P z y x)). Qed.
Lemma lem1867734 (P : type1624) (z : real) (y : real) (x : real) (h1 : term78 P z y x) : term78 P z y x.
Proof. exact (EQ_MP (@lem1867733 P z y x) (@lem1867730 P z y x h1)). Qed.
Lemma lem1867736 (_27016 : real) (_27017 : real) (_27018 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term182 P _27016 _27017 _27018.
Proof. exact (EQ_MP (@lem1867549 P _27016 _27017 _27018) (@lem1867478 _27017 _27016 _27018 P x y z h1)). Qed.
Lemma lem1867737 (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term182 P y z x.
Proof. exact (@lem1867736 y z x P x y z h1). Qed.
Lemma lem1867740 (P : type1624) (x : real) (y : real) (z : real) (h1 : term78 P z y x) (h2 : term145 P x y z) : term78 P y z x.
Proof. exact (@lem1867737 P x y z h2 (@lem1867734 P z y x h1)). Qed.
Lemma lem1867741 (P : type1624) (x : real) (y : real) (z : real) (h1 : term78 P z y x) (h2 : term145 P x y z) : term181 P y z x.
Proof. exact (fun h0 : P y z x => @lem1867740 P x y z h1 h2). Qed.
Lemma lem1867743 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1867744 (P : type1624) (y : real) (z : real) (x : real) : (term181 P y z x) = (term78 P y z x).
Proof. exact (@lem1867743 (P y z x)). Qed.
Lemma lem1867745 (P : type1624) (x : real) (y : real) (z : real) (h1 : term78 P z y x) (h2 : term145 P x y z) : term78 P y z x.
Proof. exact (EQ_MP (@lem1867744 P y z x) (@lem1867741 P x y z h1 h2)). Qed.
Lemma lem1867747 (_27016 : real) (_27017 : real) (_27018 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term183 P _27016 _27017 _27018.
Proof. exact (EQ_MP (@lem1867566 P _27016 _27017 _27018) (@lem1867484 _27016 _27018 _27017 P x y z h1)). Qed.
Lemma lem1867748 (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term183 P y x z.
Proof. exact (@lem1867747 y x z P x y z h1). Qed.
Lemma lem1867751 (P : type1624) (x : real) (y : real) (z : real) (h1 : term78 P z y x) (h2 : term145 P x y z) : term78 P y x z.
Proof. exact (@lem1867748 P x y z h2 (@lem1867745 P x y z h1 h2)). Qed.
Lemma lem1867752 (P : type1624) (x : real) (y : real) (z : real) (h1 : term78 P z y x) (h2 : term145 P x y z) : term181 P y x z.
Proof. exact (fun h0 : P y x z => @lem1867751 P x y z h1 h2). Qed.
Lemma lem1867754 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1867755 (P : type1624) (y : real) (x : real) (z : real) : (term181 P y x z) = (term78 P y x z).
Proof. exact (@lem1867754 (P y x z)). Qed.
Lemma lem1867756 (P : type1624) (x : real) (y : real) (z : real) (h1 : term78 P z y x) (h2 : term145 P x y z) : term78 P y x z.
Proof. exact (EQ_MP (@lem1867755 P y x z) (@lem1867752 P x y z h1 h2)). Qed.
Lemma lem1867758 (b : Prop) (a : Prop) : (a \/ b) = (term177 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1867759 (P : type1624) (_27021 : real) (_27019 : real) (_27020 : real) : (term170 P _27019 _27020 _27021) = (term206 P _27021 _27019 _27020).
Proof. exact (@lem1867758 (term184 P _27019 _27020 _27021) (term171 _27019 _27020)). Qed.
Lemma lem1867761 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1867762 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term207 P _27019 _27020 _27021) = (term208 P _27019 _27020 _27021).
Proof. exact (@lem1867761 (term171 _27020 _27021) (P _27019 _27020 _27021)). Qed.
Lemma lem1867764 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1867765 (_27020 : real) (_27021 : real) : (term199 _27020 _27021) = (real_le _27020 _27021).
Proof. exact (@lem1867764 (real_le _27020 _27021)). Qed.
Lemma lem1867766 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1867767 (_27020 : real) (_27021 : real) : (term200 _27020 _27021) = (term201 _27020 _27021).
Proof. exact (MK_COMB (@lem1867766) (@lem1867765 _27020 _27021)). Qed.
Lemma lem1867768 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term78 P _27019 _27020 _27021) = (term78 P _27019 _27020 _27021).
Proof. exact (eq_refl (term78 P _27019 _27020 _27021)). Qed.
Lemma lem1867769 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term208 P _27019 _27020 _27021) = (term209 P _27019 _27020 _27021).
Proof. exact (MK_COMB (@lem1867767 _27020 _27021) (@lem1867768 P _27019 _27020 _27021)). Qed.
Lemma lem1867770 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term207 P _27019 _27020 _27021) = (term209 P _27019 _27020 _27021).
Proof. exact (TRANS (@lem1867762 P _27019 _27020 _27021) (@lem1867769 P _27019 _27020 _27021)). Qed.
Lemma lem1867771 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1867772 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term210 P _27019 _27020 _27021) = (term211 P _27019 _27020 _27021).
Proof. exact (MK_COMB (@lem1867771) (@lem1867770 P _27019 _27020 _27021)). Qed.
Lemma lem1867773 (_27019 : real) (_27020 : real) : (term171 _27019 _27020) = (term171 _27019 _27020).
Proof. exact (eq_refl (term171 _27019 _27020)). Qed.
Lemma lem1867774 (P : type1624) (_27021 : real) (_27019 : real) (_27020 : real) : (term206 P _27021 _27019 _27020) = (term212 P _27021 _27019 _27020).
Proof. exact (MK_COMB (@lem1867772 P _27019 _27020 _27021) (@lem1867773 _27019 _27020)). Qed.
Lemma lem1867775 (P : type1624) (_27021 : real) (_27019 : real) (_27020 : real) : (term170 P _27019 _27020 _27021) = (term212 P _27021 _27019 _27020).
Proof. exact (TRANS (@lem1867759 P _27021 _27019 _27020) (@lem1867774 P _27021 _27019 _27020)). Qed.
Lemma lem1867777 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term78 P z y x) (h5 : term145 P x y z) : term209 P y x z.
Proof. exact (conj (@lem1867726 P x y z h1 h2 h3 h5) (@lem1867756 P x y z h4 h5)). Qed.
Lemma lem1867779 (_27021 : real) (_27019 : real) (_27020 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term212 P _27021 _27019 _27020.
Proof. exact (EQ_MP (@lem1867775 P _27021 _27019 _27020) (@lem1867472 _27019 _27020 _27021 P x y z h1)). Qed.
Lemma lem1867780 (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term212 P z y x.
Proof. exact (@lem1867779 z y x P x y z h1). Qed.
Lemma lem1867783 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term78 P z y x) (h5 : term145 P x y z) : term171 y x.
Proof. exact (@lem1867780 P x y z h5 (@lem1867777 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem1867784 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term78 P z y x) (h5 : term145 P x y z) : term174 y x.
Proof. exact (fun h0 : real_le y x => @lem1867783 P x y z h1 h2 h3 h4 h5). Qed.
Lemma lem1867786 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1867787 (y : real) (x : real) : (term174 y x) = (term171 y x).
Proof. exact (@lem1867786 (real_le y x)). Qed.
Lemma lem1867788 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term78 P z y x) (h5 : term145 P x y z) : term171 y x.
Proof. exact (EQ_MP (@lem1867787 y x) (@lem1867784 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem1867790 (_27015 : real) (_27014 : real) (h1 : term17) : term178 _27015 _27014.
Proof. exact (EQ_MP (@lem1867524 _27015 _27014) (@lem1867519 _27014 _27015 h1)). Qed.
Lemma lem1867791 (x : real) (y : real) (h1 : term17) : term178 x y.
Proof. exact (@lem1867790 x y h1). Qed.
Lemma lem1867794 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term78 P z y x) (h5 : term145 P x y z) : real_le x y.
Proof. exact (@lem1867791 x y h1 (@lem1867788 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem1867795 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term78 P z y x) (h5 : term145 P x y z) : term179 x y.
Proof. exact (fun h0 : term171 x y => @lem1867794 P x y z h1 h2 h3 h4 h5). Qed.
Lemma lem1867797 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1867798 (x : real) (y : real) : (term179 x y) = (real_le x y).
Proof. exact (@lem1867797 (real_le x y)). Qed.
Lemma lem1867799 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term78 P z y x) (h5 : term145 P x y z) : real_le x y.
Proof. exact (EQ_MP (@lem1867798 x y) (@lem1867795 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem1867802 (P : type1624) (x : real) (y : real) (z : real) (h1 : term78 P x y z) : term78 P x y z.
Proof. exact (h1). Qed.
Lemma lem1867803 (P : type1624) (x : real) (y : real) (z : real) (h1 : term78 P x y z) : term181 P x y z.
Proof. exact (fun h0 : P x y z => @lem1867802 P x y z h1). Qed.
Lemma lem1867805 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1867806 (P : type1624) (x : real) (y : real) (z : real) : (term181 P x y z) = (term78 P x y z).
Proof. exact (@lem1867805 (P x y z)). Qed.
Lemma lem1867807 (P : type1624) (x : real) (y : real) (z : real) (h1 : term78 P x y z) : term78 P x y z.
Proof. exact (EQ_MP (@lem1867806 P x y z) (@lem1867803 P x y z h1)). Qed.
Lemma lem1867808 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term78 P z y x) (h5 : term145 P x y z) : term202 P x y z.
Proof. exact (conj (@lem1867799 P x y z h1 h2 h3 h4 h5) (@lem1867807 P x y z h3)). Qed.
Lemma lem1867810 (_27019 : real) (_27020 : real) (_27021 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term205 P _27019 _27020 _27021.
Proof. exact (EQ_MP (@lem1867702 P _27019 _27020 _27021) (@lem1867683 _27019 _27020 _27021 P x y z h1)). Qed.
Lemma lem1867811 (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term205 P x y z.
Proof. exact (@lem1867810 x y z P x y z h1). Qed.
Lemma lem1867814 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term78 P z y x) (h5 : term145 P x y z) : term171 y z.
Proof. exact (@lem1867811 P x y z h5 (@lem1867808 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem1867815 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term78 P z y x) (h5 : term145 P x y z) : term174 y z.
Proof. exact (fun h0 : real_le y z => @lem1867814 P x y z h1 h2 h3 h4 h5). Qed.
Lemma lem1867817 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1867818 (y : real) (z : real) : (term174 y z) = (term171 y z).
Proof. exact (@lem1867817 (real_le y z)). Qed.
Lemma lem1867819 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term78 P z y x) (h5 : term145 P x y z) : term171 y z.
Proof. exact (EQ_MP (@lem1867818 y z) (@lem1867815 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem1867821 (_27015 : real) (_27014 : real) (h1 : term17) : term178 _27015 _27014.
Proof. exact (EQ_MP (@lem1867524 _27015 _27014) (@lem1867519 _27014 _27015 h1)). Qed.
Lemma lem1867822 (z : real) (y : real) (h1 : term17) : term178 z y.
Proof. exact (@lem1867821 z y h1). Qed.
Lemma lem1867825 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term78 P z y x) (h5 : term145 P x y z) : real_le z y.
Proof. exact (@lem1867822 z y h1 (@lem1867819 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem1867826 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term78 P x y z) (h3 : term78 P z y x) (h4 : term145 P x y z) : term179 z y.
Proof. exact (fun h0 : term171 z y => @lem1867825 P x y z h1 h0 h2 h3 h4). Qed.
Lemma lem1867828 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1867829 (z : real) (y : real) : (term179 z y) = (real_le z y).
Proof. exact (@lem1867828 (real_le z y)). Qed.
Lemma lem1867830 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term78 P x y z) (h3 : term78 P z y x) (h4 : term145 P x y z) : real_le z y.
Proof. exact (EQ_MP (@lem1867829 z y) (@lem1867826 P x y z h1 h2 h3 h4)). Qed.
Lemma lem1867833 (y : real) (x : real) (h1 : term171 y x) : term171 y x.
Proof. exact (h1). Qed.
Lemma lem1867834 (y : real) (x : real) (h1 : term171 y x) : term174 y x.
Proof. exact (fun h0 : real_le y x => @lem1867833 y x h1). Qed.
Lemma lem1867836 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1867837 (y : real) (x : real) : (term174 y x) = (term171 y x).
Proof. exact (@lem1867836 (real_le y x)). Qed.
Lemma lem1867838 (y : real) (x : real) (h1 : term171 y x) : term171 y x.
Proof. exact (EQ_MP (@lem1867837 y x) (@lem1867834 y x h1)). Qed.
Lemma lem1867840 (_27015 : real) (_27014 : real) (h1 : term17) : term178 _27015 _27014.
Proof. exact (EQ_MP (@lem1867524 _27015 _27014) (@lem1867519 _27014 _27015 h1)). Qed.
Lemma lem1867841 (x : real) (y : real) (h1 : term17) : term178 x y.
Proof. exact (@lem1867840 x y h1). Qed.
Lemma lem1867844 (y : real) (x : real) (h1 : term17) (h2 : term171 y x) : real_le x y.
Proof. exact (@lem1867841 x y h1 (@lem1867838 y x h2)). Qed.
Lemma lem1867845 (y : real) (x : real) (h1 : term17) (h2 : term171 y x) : term179 x y.
Proof. exact (fun h0 : term171 x y => @lem1867844 y x h1 h2). Qed.
Lemma lem1867847 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1867848 (x : real) (y : real) : (term179 x y) = (real_le x y).
Proof. exact (@lem1867847 (real_le x y)). Qed.
Lemma lem1867849 (y : real) (x : real) (h1 : term17) (h2 : term171 y x) : real_le x y.
Proof. exact (EQ_MP (@lem1867848 x y) (@lem1867845 y x h1 h2)). Qed.
Lemma lem1867852 (P : type1624) (x : real) (y : real) (z : real) (h1 : term78 P x y z) : term78 P x y z.
Proof. exact (h1). Qed.
Lemma lem1867853 (P : type1624) (x : real) (y : real) (z : real) (h1 : term78 P x y z) : term181 P x y z.
Proof. exact (fun h0 : P x y z => @lem1867852 P x y z h1). Qed.
Lemma lem1867855 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1867856 (P : type1624) (x : real) (y : real) (z : real) : (term181 P x y z) = (term78 P x y z).
Proof. exact (@lem1867855 (P x y z)). Qed.
Lemma lem1867857 (P : type1624) (x : real) (y : real) (z : real) (h1 : term78 P x y z) : term78 P x y z.
Proof. exact (EQ_MP (@lem1867856 P x y z) (@lem1867853 P x y z h1)). Qed.
Lemma lem1867858 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) : term202 P x y z.
Proof. exact (conj (@lem1867849 y x h1 h2) (@lem1867857 P x y z h3)). Qed.
Lemma lem1867860 (_27019 : real) (_27020 : real) (_27021 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term205 P _27019 _27020 _27021.
Proof. exact (EQ_MP (@lem1867702 P _27019 _27020 _27021) (@lem1867683 _27019 _27020 _27021 P x y z h1)). Qed.
Lemma lem1867861 (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term205 P x y z.
Proof. exact (@lem1867860 x y z P x y z h1). Qed.
Lemma lem1867864 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term145 P x y z) : term171 y z.
Proof. exact (@lem1867861 P x y z h4 (@lem1867858 P x y z h1 h2 h3)). Qed.
Lemma lem1867865 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term145 P x y z) : term174 y z.
Proof. exact (fun h0 : real_le y z => @lem1867864 P x y z h1 h2 h3 h4). Qed.
Lemma lem1867867 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1867868 (y : real) (z : real) : (term174 y z) = (term171 y z).
Proof. exact (@lem1867867 (real_le y z)). Qed.
Lemma lem1867869 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term145 P x y z) : term171 y z.
Proof. exact (EQ_MP (@lem1867868 y z) (@lem1867865 P x y z h1 h2 h3 h4)). Qed.
Lemma lem1867871 (_27015 : real) (_27014 : real) (h1 : term17) : term178 _27015 _27014.
Proof. exact (EQ_MP (@lem1867524 _27015 _27014) (@lem1867519 _27014 _27015 h1)). Qed.
Lemma lem1867872 (z : real) (y : real) (h1 : term17) : term178 z y.
Proof. exact (@lem1867871 z y h1). Qed.
Lemma lem1867875 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term145 P x y z) : real_le z y.
Proof. exact (@lem1867872 z y h1 (@lem1867869 P x y z h1 h2 h3 h4)). Qed.
Lemma lem1867876 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term145 P x y z) : term179 z y.
Proof. exact (fun h0 : term171 z y => @lem1867875 P x y z h1 h2 h3 h4). Qed.
Lemma lem1867878 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1867879 (z : real) (y : real) : (term179 z y) = (real_le z y).
Proof. exact (@lem1867878 (real_le z y)). Qed.
Lemma lem1867880 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term145 P x y z) : real_le z y.
Proof. exact (EQ_MP (@lem1867879 z y) (@lem1867876 P x y z h1 h2 h3 h4)). Qed.
Lemma lem1867883 (P : type1624) (x : real) (z : real) (y : real) (h1 : term78 P x z y) : term78 P x z y.
Proof. exact (h1). Qed.
Lemma lem1867884 (P : type1624) (x : real) (z : real) (y : real) (h1 : term78 P x z y) : term181 P x z y.
Proof. exact (fun h0 : P x z y => @lem1867883 P x z y h1). Qed.
Lemma lem1867886 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1867887 (P : type1624) (x : real) (z : real) (y : real) : (term181 P x z y) = (term78 P x z y).
Proof. exact (@lem1867886 (P x z y)). Qed.
Lemma lem1867888 (P : type1624) (x : real) (z : real) (y : real) (h1 : term78 P x z y) : term78 P x z y.
Proof. exact (EQ_MP (@lem1867887 P x z y) (@lem1867884 P x z y h1)). Qed.
Lemma lem1867889 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term78 P x z y) (h5 : term145 P x y z) : term209 P x z y.
Proof. exact (conj (@lem1867880 P x y z h1 h2 h3 h5) (@lem1867888 P x z y h4)). Qed.
Lemma lem1867891 (_27021 : real) (_27019 : real) (_27020 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term212 P _27021 _27019 _27020.
Proof. exact (EQ_MP (@lem1867775 P _27021 _27019 _27020) (@lem1867472 _27019 _27020 _27021 P x y z h1)). Qed.
Lemma lem1867892 (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term212 P y x z.
Proof. exact (@lem1867891 y x z P x y z h1). Qed.
Lemma lem1867895 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term78 P x z y) (h5 : term145 P x y z) : term171 x z.
Proof. exact (@lem1867892 P x y z h5 (@lem1867889 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem1867896 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term78 P x z y) (h5 : term145 P x y z) : term174 x z.
Proof. exact (fun h0 : real_le x z => @lem1867895 P x y z h1 h2 h3 h4 h5). Qed.
Lemma lem1867898 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1867899 (x : real) (z : real) : (term174 x z) = (term171 x z).
Proof. exact (@lem1867898 (real_le x z)). Qed.
Lemma lem1867900 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term78 P x z y) (h5 : term145 P x y z) : term171 x z.
Proof. exact (EQ_MP (@lem1867899 x z) (@lem1867896 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem1867902 (_27015 : real) (_27014 : real) (h1 : term17) : term178 _27015 _27014.
Proof. exact (EQ_MP (@lem1867524 _27015 _27014) (@lem1867519 _27014 _27015 h1)). Qed.
Lemma lem1867903 (z : real) (x : real) (h1 : term17) : term178 z x.
Proof. exact (@lem1867902 z x h1). Qed.
Lemma lem1867906 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term78 P x z y) (h5 : term145 P x y z) : real_le z x.
Proof. exact (@lem1867903 z x h1 (@lem1867900 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem1867907 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term78 P x z y) (h5 : term145 P x y z) : term179 z x.
Proof. exact (fun h0 : term171 z x => @lem1867906 P x y z h1 h2 h3 h4 h5). Qed.
Lemma lem1867909 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1867910 (z : real) (x : real) : (term179 z x) = (real_le z x).
Proof. exact (@lem1867909 (real_le z x)). Qed.
Lemma lem1867911 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term78 P x z y) (h5 : term145 P x y z) : real_le z x.
Proof. exact (EQ_MP (@lem1867910 z x) (@lem1867907 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem1867914 (P : type1624) (z : real) (x : real) (y : real) (h1 : term78 P z x y) : term78 P z x y.
Proof. exact (h1). Qed.
Lemma lem1867915 (P : type1624) (z : real) (x : real) (y : real) (h1 : term78 P z x y) : term181 P z x y.
Proof. exact (fun h0 : P z x y => @lem1867914 P z x y h1). Qed.
Lemma lem1867917 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1867918 (P : type1624) (z : real) (x : real) (y : real) : (term181 P z x y) = (term78 P z x y).
Proof. exact (@lem1867917 (P z x y)). Qed.
Lemma lem1867919 (P : type1624) (z : real) (x : real) (y : real) (h1 : term78 P z x y) : term78 P z x y.
Proof. exact (EQ_MP (@lem1867918 P z x y) (@lem1867915 P z x y h1)). Qed.
Lemma lem1867920 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term78 P x z y) (h5 : term78 P z x y) (h6 : term145 P x y z) : term202 P z x y.
Proof. exact (conj (@lem1867911 P x y z h1 h2 h3 h4 h6) (@lem1867919 P z x y h5)). Qed.
Lemma lem1867922 (_27019 : real) (_27020 : real) (_27021 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term205 P _27019 _27020 _27021.
Proof. exact (EQ_MP (@lem1867702 P _27019 _27020 _27021) (@lem1867683 _27019 _27020 _27021 P x y z h1)). Qed.
Lemma lem1867923 (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term205 P z x y.
Proof. exact (@lem1867922 z x y P x y z h1). Qed.
Lemma lem1867926 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term78 P x z y) (h5 : term78 P z x y) (h6 : term145 P x y z) : term171 x y.
Proof. exact (@lem1867923 P x y z h6 (@lem1867920 P x y z h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem1867927 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term78 P x z y) (h5 : term78 P z x y) (h6 : term145 P x y z) : term174 x y.
Proof. exact (fun h0 : real_le x y => @lem1867926 P x y z h1 h2 h3 h4 h5 h6). Qed.
Lemma lem1867929 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1867930 (x : real) (y : real) : (term174 x y) = (term171 x y).
Proof. exact (@lem1867929 (real_le x y)). Qed.
Lemma lem1867931 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term78 P x z y) (h5 : term78 P z x y) (h6 : term145 P x y z) : term171 x y.
Proof. exact (EQ_MP (@lem1867930 x y) (@lem1867927 P x y z h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem1867933 (_27015 : real) (_27014 : real) (h1 : term17) : term178 _27015 _27014.
Proof. exact (EQ_MP (@lem1867524 _27015 _27014) (@lem1867519 _27014 _27015 h1)). Qed.
Lemma lem1867934 (y : real) (x : real) (h1 : term17) : term178 y x.
Proof. exact (@lem1867933 y x h1). Qed.
Lemma lem1867937 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term78 P x z y) (h5 : term78 P z x y) (h6 : term145 P x y z) : real_le y x.
Proof. exact (@lem1867934 y x h1 (@lem1867931 P x y z h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem1867938 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term78 P x y z) (h3 : term78 P x z y) (h4 : term78 P z x y) (h5 : term145 P x y z) : term179 y x.
Proof. exact (fun h0 : term171 y x => @lem1867937 P x y z h1 h0 h2 h3 h4 h5). Qed.
Lemma lem1867940 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1867941 (y : real) (x : real) : (term179 y x) = (real_le y x).
Proof. exact (@lem1867940 (real_le y x)). Qed.
Lemma lem1867942 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term78 P x y z) (h3 : term78 P x z y) (h4 : term78 P z x y) (h5 : term145 P x y z) : real_le y x.
Proof. exact (EQ_MP (@lem1867941 y x) (@lem1867938 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem1867958 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1867959 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term184 P _27019 _27020 _27021) = (term185 P _27019 _27020 _27021).
Proof. exact (@lem1867958 (P _27019 _27020 _27021) (term171 _27020 _27021)). Qed.
Lemma lem1867965 (_27019 : real) (_27020 : real) : (term186 _27019 _27020) = (term186 _27019 _27020).
Proof. exact (eq_refl (term186 _27019 _27020)). Qed.
Lemma lem1867966 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term170 P _27019 _27020 _27021) = (term187 P _27019 _27020 _27021).
Proof. exact (MK_COMB (@lem1867965 _27019 _27020) (@lem1867959 P _27019 _27020 _27021)). Qed.
Lemma lem1867970 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1867971 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term187 P _27019 _27020 _27021) = (term188 P _27019 _27020 _27021).
Proof. exact (@lem1867970 (P _27019 _27020 _27021) (term171 _27019 _27020) (term171 _27020 _27021)). Qed.
Lemma lem1867987 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term170 P _27019 _27020 _27021) = (term188 P _27019 _27020 _27021).
Proof. exact (TRANS (@lem1867966 P _27019 _27020 _27021) (@lem1867971 P _27019 _27020 _27021)). Qed.
Lemma lem1867988 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1867989 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term189 P _27019 _27020 _27021) = (term190 P _27019 _27020 _27021).
Proof. exact (MK_COMB (@lem1867988) (@lem1867987 P _27019 _27020 _27021)). Qed.
Lemma lem1868005 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term188 P _27019 _27020 _27021) = (term188 P _27019 _27020 _27021).
Proof. exact (eq_refl (term188 P _27019 _27020 _27021)). Qed.
Lemma lem1868006 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : ((term170 P _27019 _27020 _27021) = (term188 P _27019 _27020 _27021)) = ((term188 P _27019 _27020 _27021) = (term188 P _27019 _27020 _27021)).
Proof. exact (MK_COMB (@lem1867989 P _27019 _27020 _27021) (@lem1868005 P _27019 _27020 _27021)). Qed.
Lemma lem1868008 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1868009 (x : Prop) : (x = x) = True.
Proof. exact (@lem1868008 Prop x). Qed.
Lemma lem1868010 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : ((term188 P _27019 _27020 _27021) = (term188 P _27019 _27020 _27021)) = True.
Proof. exact (@lem1868009 (term188 P _27019 _27020 _27021)). Qed.
Lemma lem1868011 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : ((term170 P _27019 _27020 _27021) = (term188 P _27019 _27020 _27021)) = True.
Proof. exact (TRANS (@lem1868006 P _27019 _27020 _27021) (@lem1868010 P _27019 _27020 _27021)). Qed.
Lemma lem1868012 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : True = ((term170 P _27019 _27020 _27021) = (term188 P _27019 _27020 _27021)).
Proof. exact (SYM (@lem1868011 P _27019 _27020 _27021)). Qed.
Lemma lem1868013 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term170 P _27019 _27020 _27021) = (term188 P _27019 _27020 _27021).
Proof. exact (EQ_MP (@lem1868012 P _27019 _27020 _27021) (@lem0)). Qed.
Lemma lem1868014 (_27019 : real) (_27020 : real) (_27021 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term188 P _27019 _27020 _27021.
Proof. exact (EQ_MP (@lem1868013 P _27019 _27020 _27021) (@lem1867472 _27019 _27020 _27021 P x y z h1)). Qed.
Lemma lem1868016 (b : Prop) (a : Prop) : (a \/ b) = (term177 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1868017 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term188 P _27019 _27020 _27021) = (term213 P _27019 _27020 _27021).
Proof. exact (@lem1868016 (term58 _27019 _27020 _27021) (P _27019 _27020 _27021)). Qed.
Lemma lem1868019 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1868020 (_27019 : real) (_27020 : real) (_27021 : real) : (term214 _27019 _27020 _27021) = (term215 _27019 _27020 _27021).
Proof. exact (@lem1868019 (term171 _27019 _27020) (term171 _27020 _27021)). Qed.
Lemma lem1868022 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1868023 (_27019 : real) (_27020 : real) : (term199 _27019 _27020) = (real_le _27019 _27020).
Proof. exact (@lem1868022 (real_le _27019 _27020)). Qed.
Lemma lem1868024 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1868025 (_27019 : real) (_27020 : real) : (term200 _27019 _27020) = (term201 _27019 _27020).
Proof. exact (MK_COMB (@lem1868024) (@lem1868023 _27019 _27020)). Qed.
Lemma lem1868027 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1868028 (_27020 : real) (_27021 : real) : (term199 _27020 _27021) = (real_le _27020 _27021).
Proof. exact (@lem1868027 (real_le _27020 _27021)). Qed.
Lemma lem1868029 (_27019 : real) (_27020 : real) (_27021 : real) : (term215 _27019 _27020 _27021) = (term63 _27019 _27020 _27021).
Proof. exact (MK_COMB (@lem1868025 _27019 _27020) (@lem1868028 _27020 _27021)). Qed.
Lemma lem1868030 (_27019 : real) (_27020 : real) (_27021 : real) : (term214 _27019 _27020 _27021) = (term63 _27019 _27020 _27021).
Proof. exact (TRANS (@lem1868020 _27019 _27020 _27021) (@lem1868029 _27019 _27020 _27021)). Qed.
Lemma lem1868031 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1868032 (_27019 : real) (_27020 : real) (_27021 : real) : (term216 _27019 _27020 _27021) = (term217 _27019 _27020 _27021).
Proof. exact (MK_COMB (@lem1868031) (@lem1868030 _27019 _27020 _27021)). Qed.
Lemma lem1868033 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (P _27019 _27020 _27021) = (P _27019 _27020 _27021).
Proof. exact (eq_refl (P _27019 _27020 _27021)). Qed.
Lemma lem1868034 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term213 P _27019 _27020 _27021) = (term30 P _27019 _27020 _27021).
Proof. exact (MK_COMB (@lem1868032 _27019 _27020 _27021) (@lem1868033 P _27019 _27020 _27021)). Qed.
Lemma lem1868035 (P : type1624) (_27019 : real) (_27020 : real) (_27021 : real) : (term188 P _27019 _27020 _27021) = (term30 P _27019 _27020 _27021).
Proof. exact (TRANS (@lem1868017 P _27019 _27020 _27021) (@lem1868034 P _27019 _27020 _27021)). Qed.
Lemma lem1868037 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term78 P x y z) (h3 : term78 P x z y) (h4 : term78 P z x y) (h5 : term78 P z y x) (h6 : term145 P x y z) : term63 z y x.
Proof. exact (conj (@lem1867830 P x y z h1 h2 h5 h6) (@lem1867942 P x y z h1 h2 h3 h4 h6)). Qed.
Lemma lem1868039 (_27019 : real) (_27020 : real) (_27021 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term30 P _27019 _27020 _27021.
Proof. exact (EQ_MP (@lem1868035 P _27019 _27020 _27021) (@lem1868014 _27019 _27020 _27021 P x y z h1)). Qed.
Lemma lem1868040 (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term30 P z y x.
Proof. exact (@lem1868039 z y x P x y z h1). Qed.
Lemma lem1868043 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term78 P x y z) (h3 : term78 P x z y) (h4 : term78 P z x y) (h5 : term78 P z y x) (h6 : term145 P x y z) : P z y x.
Proof. exact (@lem1868040 P x y z h6 (@lem1868037 P x y z h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem1868044 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term78 P x y z) (h3 : term78 P x z y) (h4 : term78 P z x y) (h5 : term145 P x y z) : term218 P z y x.
Proof. exact (fun h0 : term78 P z y x => @lem1868043 P x y z h1 h2 h3 h4 h0 h5). Qed.
Lemma lem1868046 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1868047 (P : type1624) (z : real) (y : real) (x : real) : (term218 P z y x) = (P z y x).
Proof. exact (@lem1868046 (P z y x)). Qed.
Lemma lem1868048 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term78 P x y z) (h3 : term78 P x z y) (h4 : term78 P z x y) (h5 : term145 P x y z) : P z y x.
Proof. exact (EQ_MP (@lem1868047 P z y x) (@lem1868044 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem1868054 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1868055 (P : type1624) (_27016 : real) (_27017 : real) (_27018 : real) : (term173 P _27016 _27018 _27017) = (term219 P _27016 _27017 _27018).
Proof. exact (@lem1868054 (P _27016 _27018 _27017) (term78 P _27016 _27017 _27018)). Qed.
Lemma lem1868061 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1868062 (P : type1624) (_27016 : real) (_27017 : real) (_27018 : real) : (term220 P _27016 _27018 _27017) = (term221 P _27016 _27017 _27018).
Proof. exact (MK_COMB (@lem1868061) (@lem1868055 P _27016 _27017 _27018)). Qed.
Lemma lem1868068 (P : type1624) (_27016 : real) (_27017 : real) (_27018 : real) : (term219 P _27016 _27017 _27018) = (term219 P _27016 _27017 _27018).
Proof. exact (eq_refl (term219 P _27016 _27017 _27018)). Qed.
Lemma lem1868069 (P : type1624) (_27016 : real) (_27017 : real) (_27018 : real) : ((term173 P _27016 _27018 _27017) = (term219 P _27016 _27017 _27018)) = ((term219 P _27016 _27017 _27018) = (term219 P _27016 _27017 _27018)).
Proof. exact (MK_COMB (@lem1868062 P _27016 _27017 _27018) (@lem1868068 P _27016 _27017 _27018)). Qed.
Lemma lem1868071 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1868072 (x : Prop) : (x = x) = True.
Proof. exact (@lem1868071 Prop x). Qed.
Lemma lem1868073 (P : type1624) (_27016 : real) (_27017 : real) (_27018 : real) : ((term219 P _27016 _27017 _27018) = (term219 P _27016 _27017 _27018)) = True.
Proof. exact (@lem1868072 (term219 P _27016 _27017 _27018)). Qed.
Lemma lem1868074 (P : type1624) (_27016 : real) (_27017 : real) (_27018 : real) : ((term173 P _27016 _27018 _27017) = (term219 P _27016 _27017 _27018)) = True.
Proof. exact (TRANS (@lem1868069 P _27016 _27017 _27018) (@lem1868073 P _27016 _27017 _27018)). Qed.
Lemma lem1868075 (P : type1624) (_27016 : real) (_27017 : real) (_27018 : real) : True = ((term173 P _27016 _27018 _27017) = (term219 P _27016 _27017 _27018)).
Proof. exact (SYM (@lem1868074 P _27016 _27017 _27018)). Qed.
Lemma lem1868076 (P : type1624) (_27016 : real) (_27017 : real) (_27018 : real) : (term173 P _27016 _27018 _27017) = (term219 P _27016 _27017 _27018).
Proof. exact (EQ_MP (@lem1868075 P _27016 _27017 _27018) (@lem0)). Qed.
Lemma lem1868077 (_27016 : real) (_27017 : real) (_27018 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term219 P _27016 _27017 _27018.
Proof. exact (EQ_MP (@lem1868076 P _27016 _27017 _27018) (@lem1867484 _27016 _27018 _27017 P x y z h1)). Qed.
Lemma lem1868079 (b : Prop) (a : Prop) : (a \/ b) = (term177 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1868080 (P : type1624) (_27016 : real) (_27018 : real) (_27017 : real) : (term219 P _27016 _27017 _27018) = (term222 P _27016 _27018 _27017).
Proof. exact (@lem1868079 (term78 P _27016 _27017 _27018) (P _27016 _27018 _27017)). Qed.
Lemma lem1868082 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1868083 (P : type1624) (_27016 : real) (_27017 : real) (_27018 : real) : (term223 P _27016 _27017 _27018) = (P _27016 _27017 _27018).
Proof. exact (@lem1868082 (P _27016 _27017 _27018)). Qed.
Lemma lem1868084 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1868085 (P : type1624) (_27016 : real) (_27017 : real) (_27018 : real) : (term224 P _27016 _27017 _27018) = (term225 P _27016 _27017 _27018).
Proof. exact (MK_COMB (@lem1868084) (@lem1868083 P _27016 _27017 _27018)). Qed.
Lemma lem1868086 (P : type1624) (_27016 : real) (_27018 : real) (_27017 : real) : (P _27016 _27018 _27017) = (P _27016 _27018 _27017).
Proof. exact (eq_refl (P _27016 _27018 _27017)). Qed.
Lemma lem1868087 (P : type1624) (_27016 : real) (_27018 : real) (_27017 : real) : (term222 P _27016 _27018 _27017) = (term226 P _27016 _27018 _27017).
Proof. exact (MK_COMB (@lem1868085 P _27016 _27017 _27018) (@lem1868086 P _27016 _27018 _27017)). Qed.
Lemma lem1868088 (P : type1624) (_27016 : real) (_27018 : real) (_27017 : real) : (term219 P _27016 _27017 _27018) = (term226 P _27016 _27018 _27017).
Proof. exact (TRANS (@lem1868080 P _27016 _27018 _27017) (@lem1868087 P _27016 _27018 _27017)). Qed.
Lemma lem1868091 (_27016 : real) (_27018 : real) (_27017 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term226 P _27016 _27018 _27017.
Proof. exact (EQ_MP (@lem1868088 P _27016 _27018 _27017) (@lem1868077 _27016 _27017 _27018 P x y z h1)). Qed.
Lemma lem1868092 (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term226 P z x y.
Proof. exact (@lem1868091 z x y P x y z h1). Qed.
Lemma lem1868095 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term78 P x y z) (h3 : term78 P x z y) (h4 : term78 P z x y) (h5 : term145 P x y z) : P z x y.
Proof. exact (@lem1868092 P x y z h5 (@lem1868048 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem1868096 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term78 P x y z) (h3 : term78 P x z y) (h4 : term145 P x y z) : term218 P z x y.
Proof. exact (fun h0 : term78 P z x y => @lem1868095 P x y z h1 h2 h3 h0 h4). Qed.
Lemma lem1868098 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1868099 (P : type1624) (z : real) (x : real) (y : real) : (term218 P z x y) = (P z x y).
Proof. exact (@lem1868098 (P z x y)). Qed.
Lemma lem1868100 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term78 P x y z) (h3 : term78 P x z y) (h4 : term145 P x y z) : P z x y.
Proof. exact (EQ_MP (@lem1868099 P z x y) (@lem1868096 P x y z h1 h2 h3 h4)). Qed.
Lemma lem1868106 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1868107 (P : type1624) (_27016 : real) (_27017 : real) (_27018 : real) : (term172 P _27017 _27016 _27018) = (term227 P _27016 _27017 _27018).
Proof. exact (@lem1868106 (P _27017 _27016 _27018) (term78 P _27016 _27017 _27018)). Qed.
Lemma lem1868113 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1868114 (P : type1624) (_27016 : real) (_27017 : real) (_27018 : real) : (term228 P _27017 _27016 _27018) = (term229 P _27016 _27017 _27018).
Proof. exact (MK_COMB (@lem1868113) (@lem1868107 P _27016 _27017 _27018)). Qed.
Lemma lem1868120 (P : type1624) (_27016 : real) (_27017 : real) (_27018 : real) : (term227 P _27016 _27017 _27018) = (term227 P _27016 _27017 _27018).
Proof. exact (eq_refl (term227 P _27016 _27017 _27018)). Qed.
Lemma lem1868121 (P : type1624) (_27016 : real) (_27017 : real) (_27018 : real) : ((term172 P _27017 _27016 _27018) = (term227 P _27016 _27017 _27018)) = ((term227 P _27016 _27017 _27018) = (term227 P _27016 _27017 _27018)).
Proof. exact (MK_COMB (@lem1868114 P _27016 _27017 _27018) (@lem1868120 P _27016 _27017 _27018)). Qed.
Lemma lem1868123 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1868124 (x : Prop) : (x = x) = True.
Proof. exact (@lem1868123 Prop x). Qed.
Lemma lem1868125 (P : type1624) (_27016 : real) (_27017 : real) (_27018 : real) : ((term227 P _27016 _27017 _27018) = (term227 P _27016 _27017 _27018)) = True.
Proof. exact (@lem1868124 (term227 P _27016 _27017 _27018)). Qed.
Lemma lem1868126 (P : type1624) (_27016 : real) (_27017 : real) (_27018 : real) : ((term172 P _27017 _27016 _27018) = (term227 P _27016 _27017 _27018)) = True.
Proof. exact (TRANS (@lem1868121 P _27016 _27017 _27018) (@lem1868125 P _27016 _27017 _27018)). Qed.
Lemma lem1868127 (P : type1624) (_27016 : real) (_27017 : real) (_27018 : real) : True = ((term172 P _27017 _27016 _27018) = (term227 P _27016 _27017 _27018)).
Proof. exact (SYM (@lem1868126 P _27016 _27017 _27018)). Qed.
Lemma lem1868128 (P : type1624) (_27016 : real) (_27017 : real) (_27018 : real) : (term172 P _27017 _27016 _27018) = (term227 P _27016 _27017 _27018).
Proof. exact (EQ_MP (@lem1868127 P _27016 _27017 _27018) (@lem0)). Qed.
Lemma lem1868129 (_27016 : real) (_27017 : real) (_27018 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term227 P _27016 _27017 _27018.
Proof. exact (EQ_MP (@lem1868128 P _27016 _27017 _27018) (@lem1867478 _27017 _27016 _27018 P x y z h1)). Qed.
Lemma lem1868131 (b : Prop) (a : Prop) : (a \/ b) = (term177 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1868132 (P : type1624) (_27017 : real) (_27016 : real) (_27018 : real) : (term227 P _27016 _27017 _27018) = (term230 P _27017 _27016 _27018).
Proof. exact (@lem1868131 (term78 P _27016 _27017 _27018) (P _27017 _27016 _27018)). Qed.
Lemma lem1868134 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1868135 (P : type1624) (_27016 : real) (_27017 : real) (_27018 : real) : (term223 P _27016 _27017 _27018) = (P _27016 _27017 _27018).
Proof. exact (@lem1868134 (P _27016 _27017 _27018)). Qed.
Lemma lem1868136 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1868137 (P : type1624) (_27016 : real) (_27017 : real) (_27018 : real) : (term224 P _27016 _27017 _27018) = (term225 P _27016 _27017 _27018).
Proof. exact (MK_COMB (@lem1868136) (@lem1868135 P _27016 _27017 _27018)). Qed.
Lemma lem1868138 (P : type1624) (_27017 : real) (_27016 : real) (_27018 : real) : (P _27017 _27016 _27018) = (P _27017 _27016 _27018).
Proof. exact (eq_refl (P _27017 _27016 _27018)). Qed.
Lemma lem1868139 (P : type1624) (_27017 : real) (_27016 : real) (_27018 : real) : (term230 P _27017 _27016 _27018) = (term231 P _27017 _27016 _27018).
Proof. exact (MK_COMB (@lem1868137 P _27016 _27017 _27018) (@lem1868138 P _27017 _27016 _27018)). Qed.
Lemma lem1868140 (P : type1624) (_27017 : real) (_27016 : real) (_27018 : real) : (term227 P _27016 _27017 _27018) = (term231 P _27017 _27016 _27018).
Proof. exact (TRANS (@lem1868132 P _27017 _27016 _27018) (@lem1868139 P _27017 _27016 _27018)). Qed.
Lemma lem1868143 (_27017 : real) (_27016 : real) (_27018 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term231 P _27017 _27016 _27018.
Proof. exact (EQ_MP (@lem1868140 P _27017 _27016 _27018) (@lem1868129 _27016 _27017 _27018 P x y z h1)). Qed.
Lemma lem1868144 (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term231 P x z y.
Proof. exact (@lem1868143 x z y P x y z h1). Qed.
Lemma lem1868147 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term78 P x y z) (h3 : term78 P x z y) (h4 : term145 P x y z) : P x z y.
Proof. exact (@lem1868144 P x y z h4 (@lem1868100 P x y z h1 h2 h3 h4)). Qed.
Lemma lem1868148 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term78 P x y z) (h3 : term145 P x y z) : term218 P x z y.
Proof. exact (fun h0 : term78 P x z y => @lem1868147 P x y z h1 h2 h0 h3). Qed.
Lemma lem1868150 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1868151 (P : type1624) (x : real) (z : real) (y : real) : (term218 P x z y) = (P x z y).
Proof. exact (@lem1868150 (P x z y)). Qed.
Lemma lem1868152 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term78 P x y z) (h3 : term145 P x y z) : P x z y.
Proof. exact (EQ_MP (@lem1868151 P x z y) (@lem1868148 P x y z h1 h2 h3)). Qed.
Lemma lem1868154 (_27016 : real) (_27018 : real) (_27017 : real) (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term226 P _27016 _27018 _27017.
Proof. exact (EQ_MP (@lem1868088 P _27016 _27018 _27017) (@lem1868077 _27016 _27017 _27018 P x y z h1)). Qed.
Lemma lem1868155 (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term226 P x y z.
Proof. exact (@lem1868154 x y z P x y z h1). Qed.
Lemma lem1868158 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term78 P x y z) (h3 : term145 P x y z) : P x y z.
Proof. exact (@lem1868155 P x y z h3 (@lem1868152 P x y z h1 h2 h3)). Qed.
Lemma lem1868159 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term145 P x y z) : term218 P x y z.
Proof. exact (fun h0 : term78 P x y z => @lem1868158 P x y z h1 h0 h2). Qed.
Lemma lem1868161 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1868162 (P : type1624) (x : real) (y : real) (z : real) : (term218 P x y z) = (P x y z).
Proof. exact (@lem1868161 (P x y z)). Qed.
Lemma lem1868163 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term145 P x y z) : P x y z.
Proof. exact (EQ_MP (@lem1868162 P x y z) (@lem1868159 P x y z h1 h2)). Qed.
Lemma lem1868166 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1868168 (P : type1624) (x : real) (y : real) (z : real) : (term78 P x y z) = (term232 P x y z).
Proof. exact (@lem1868166 (P x y z)). Qed.
Lemma lem1868171 (P : type1624) (x : real) (y : real) (z : real) (h1 : term145 P x y z) : term232 P x y z.
Proof. exact (EQ_MP (@lem1868168 P x y z) (@lem1867460 P x y z h1)). Qed.
Lemma lem1868174 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term145 P x y z) : False.
Proof. exact (@lem1868171 P x y z h2 (@lem1868163 P x y z h1 h2)). Qed.
Lemma lem1868175 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term145 P x y z) : term233.
Proof. exact (fun h0 : ~ False => @lem1868174 P x y z h1 h2). Qed.
Lemma lem1868177 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1868178 : term233 = False.
Proof. exact (@lem1868177 False). Qed.
Lemma lem1868179 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term145 P x y z) : False.
Proof. exact (EQ_MP (@lem1868178) (@lem1868175 P x y z h1 h2)). Qed.
Lemma lem1868180 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term145 P x y z) : term17 = False.
Proof. exact (prop_ext (fun h3 : term17 => @lem1868179 P x y z h1 h2) (fun h3 : False => @lem1867368 h1)). Qed.
Lemma lem1868181 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term145 P x y z) : False.
Proof. exact (EQ_MP (@lem1868180 P x y z h1 h2) (@lem1867368 h1)). Qed.
Lemma lem1868182 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term145 P x y z) : (term145 P x y z) = False.
Proof. exact (prop_ext (fun h3 : term145 P x y z => @lem1868181 P x y z h1 h2) (fun h3 : False => @lem1867348 P x y z h2)). Qed.
Lemma lem1868183 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term145 P x y z) : False.
Proof. exact (EQ_MP (@lem1868182 P x y z h1 h2) (@lem1867348 P x y z h2)). Qed.
Lemma lem1868184 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term145 P x y z) : term17 = False.
Proof. exact (prop_ext (fun h3 : term17 => @lem1868183 P x y z h1 h2) (fun h3 : False => @lem1867258 h1)). Qed.
Lemma lem1868185 (P : type1624) (x : real) (y : real) (z : real) (h1 : term17) (h2 : term145 P x y z) : False.
Proof. exact (EQ_MP (@lem1868184 P x y z h1 h2) (@lem1867258 h1)). Qed.
Lemma lem1868186 (P : type1624) (x : real) (y : real) (h1 : term17) (h2 : term148 P x y) : False.
Proof. exact (ex_elim (@lem1867237 P x y h2) (fun z : real => fun h0 : term147 P x y z => @lem1868185 P x y z h1 h0)). Qed.
Lemma lem1868187 (P : type1624) (x : real) (h1 : term17) (h2 : term150 P x) : False.
Proof. exact (ex_elim (@lem1867236 P x h2) (fun y : real => fun h0 : term149 P x y => @lem1868186 P x y h1 h0)). Qed.
Lemma lem1868188 (P : type1624) (h1 : term17) (h2 : term152 P) : False.
Proof. exact (ex_elim (@lem1867235 P h2) (fun x : real => fun h0 : term151 P x => @lem1868187 P x h1 h0)). Qed.
Lemma lem1868189 (h1 : term17) (h2 : term10) : False.
Proof. exact (ex_elim (@lem1867166 h2) (fun P : type1624 => fun h0 : term153 P => @lem1868188 P h1 h0)). Qed.
Lemma lem1868190 (h1 : term17) (h2 : term10) : term17 = False.
Proof. exact (prop_ext (fun h3 : term17 => @lem1868189 h1 h2) (fun h3 : False => @lem1867234 h1)). Qed.
Lemma lem1868191 (h1 : term17) (h2 : term10) : False.
Proof. exact (EQ_MP (@lem1868190 h1 h2) (@lem1867234 h1)). Qed.
Lemma lem1868192 (h1 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem1868191 h0 h1). Qed.
Lemma lem1868193 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem1868194 (h1 : term10) : term16.
Proof. exact (EQ_MP (@lem1868193) (@lem1868192 h1)). Qed.
Lemma lem1868195 : term19.
Proof. exact (fun h0 : term10 => @lem1868194 h0). Qed.
Lemma lem1868196 : term11.
Proof. exact (EQ_MP (@lem1866826) (@lem1868195)). Qed.
Lemma lem1868198 : term11.
Proof. exact (@lem1866542 (@lem1868196)). Qed.
Lemma lem1868199 (h1 : term10) : term15.
Proof. exact (@lem1868198 (@lem1866527 h1)). Qed.
Lemma lem1868200 (h1 : term10) : False.
Proof. exact (@lem1868199 h1 (@lem1339697)). Qed.
Lemma lem1868201 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem1868200 h1) (fun h2 : False => @lem1866527 h1)). Qed.
Lemma lem1868202 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem1868201 h1) (@lem1866527 h1)). Qed.
Lemma lem1868203 : term9.
Proof. exact (fun h0 : term10 => @lem1868202 h0). Qed.
Lemma lem1868204 : term8.
Proof. exact (EQ_MP (@lem1866526) (@lem1868203)). Qed.
