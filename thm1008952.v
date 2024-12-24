Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1008952_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EXP_2_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17646_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Require Import thm75543_spec.
Lemma lem1007675 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1007676 (m : nat) (p : nat) : (((term1 m) = p) = ((term2 m) = (NUMERAL p))) = (term3 m p).
Proof. exact (@lem1007675 (((term1 m) = p) = ((term2 m) = (NUMERAL p)))). Qed.
Lemma lem1007677 (m : nat) (p : nat) : (term3 m p) = (((term1 m) = p) = ((term2 m) = (NUMERAL p))).
Proof. exact (SYM (@lem1007676 m p)). Qed.
Lemma lem1007678 (m : nat) (p : nat) (h1 : term4 m p) : term4 m p.
Proof. exact (h1). Qed.
Lemma lem1007681 (m : nat) (p : nat) (h1 : term5 m p) : term5 m p.
Proof. exact (h1). Qed.
Lemma lem1007682 (m : nat) (p : nat) : term6 m p.
Proof. exact (fun h0 : term5 m p => @lem1007681 m p h0). Qed.
Lemma lem1007683 (m : nat) (p : nat) (h1 : term6 m p) : term6 m p.
Proof. exact (h1). Qed.
Lemma lem1007684 (m : nat) (p : nat) (h1 : term5 m p) : term5 m p.
Proof. exact (h1). Qed.
Lemma lem1007685 (m : nat) (p : nat) (h1 : term5 m p) (h2 : term6 m p) : term5 m p.
Proof. exact (@lem1007683 m p h2 (@lem1007684 m p h1)). Qed.
Lemma lem1007686 (m : nat) (p : nat) (h1 : term5 m p) : term7 m p.
Proof. exact (fun h0 : term6 m p => @lem1007685 m p h1 h0). Qed.
Lemma lem1007687 (m : nat) (p : nat) (h1 : term6 m p) : term6 m p.
Proof. exact (h1). Qed.
Lemma lem1007688 (m : nat) (p : nat) (h1 : term5 m p) (h2 : term6 m p) : term5 m p.
Proof. exact (@lem1007686 m p h1 (@lem1007687 m p h2)). Qed.
Lemma lem1007689 (m : nat) (p : nat) (h1 : term6 m p) : term6 m p.
Proof. exact (fun h0 : term5 m p => @lem1007688 m p h0 h1). Qed.
Lemma lem1007690 (m : nat) (p : nat) : term8 m p.
Proof. exact (fun h0 : term6 m p => @lem1007689 m p h0). Qed.
Lemma lem1007693 (m : nat) (p : nat) : term6 m p.
Proof. exact (@lem1007690 m p (@lem1007682 m p)). Qed.
Lemma lem1007711 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1007712 : term9 = term10.
Proof. exact (@lem1007711 term11). Qed.
Lemma lem1007717 : term12 = term12.
Proof. exact (eq_refl term12). Qed.
Lemma lem1007718 : term13 = term14.
Proof. exact (MK_COMB (@lem1007717) (@lem1007712)). Qed.
Lemma lem1007721 (m : nat) (p : nat) : (term15 m p) = (term15 m p).
Proof. exact (eq_refl (term15 m p)). Qed.
Lemma lem1007722 (m : nat) (p : nat) : (term5 m p) = (term16 m p).
Proof. exact (MK_COMB (@lem1007721 m p) (@lem1007718)). Qed.
Lemma lem1007725 (p : nat) : (term17 p) = (term18 p).
Proof. exact (fun_ext (fun m : nat => @lem1007722 m p)). Qed.
Lemma lem1007726 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1007727 (p : nat) : (term19 p) = (term20 p).
Proof. exact (MK_COMB (@lem1007726) (@lem1007725 p)). Qed.
Lemma lem1007732 : term21 = term22.
Proof. exact (fun_ext (fun p : nat => @lem1007727 p)). Qed.
Lemma lem1007733 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1007742 : term23 = term24.
Proof. exact (MK_COMB (@lem1007733) (@lem1007732)). Qed.
Lemma lem1007743 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem1007744 : term25 = term25.
Proof. exact (fun_ext (fun n : nat => @lem1007743 n)). Qed.
Lemma lem1007745 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1007746 : term11 = term11.
Proof. exact (MK_COMB (@lem1007745) (@lem1007744)). Qed.
Lemma lem1007747 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1007748 : term10 = term10.
Proof. exact (MK_COMB (@lem1007747) (@lem1007746)). Qed.
Lemma lem1007749 (n : nat) : ((term1 n) = (Nat.mul n n)) = ((term1 n) = (Nat.mul n n)).
Proof. exact (eq_refl ((term1 n) = (Nat.mul n n))). Qed.
Lemma lem1007750 : term26 = term26.
Proof. exact (fun_ext (fun n : nat => @lem1007749 n)). Qed.
Lemma lem1007751 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1007752 : term27 = term27.
Proof. exact (MK_COMB (@lem1007751) (@lem1007750)). Qed.
Lemma lem1007753 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1007754 : term12 = term12.
Proof. exact (MK_COMB (@lem1007753) (@lem1007752)). Qed.
Lemma lem1007755 : term14 = term14.
Proof. exact (MK_COMB (@lem1007754) (@lem1007748)). Qed.
Lemma lem1007764 (m : nat) (p : nat) : (term15 m p) = (term15 m p).
Proof. exact (eq_refl (term15 m p)). Qed.
Lemma lem1007765 (m : nat) (p : nat) : (term16 m p) = (term16 m p).
Proof. exact (MK_COMB (@lem1007764 m p) (@lem1007755)). Qed.
Lemma lem1007766 (p : nat) : (term18 p) = (term18 p).
Proof. exact (fun_ext (fun m : nat => @lem1007765 m p)). Qed.
Lemma lem1007767 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1007768 (p : nat) : (term20 p) = (term20 p).
Proof. exact (MK_COMB (@lem1007767) (@lem1007766 p)). Qed.
Lemma lem1007769 : term22 = term22.
Proof. exact (fun_ext (fun p : nat => @lem1007768 p)). Qed.
Lemma lem1007770 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1007771 : term24 = term24.
Proof. exact (MK_COMB (@lem1007770) (@lem1007769)). Qed.
Lemma lem1007802 : term23 = term24.
Proof. exact (TRANS (@lem1007742) (@lem1007771)). Qed.
Lemma lem1007803 : term24 = term23.
Proof. exact (SYM (@lem1007802)). Qed.
Lemma lem1007804 (m : nat) (p : nat) (h1 : term4 m p) : term4 m p.
Proof. exact (h1). Qed.
Lemma lem1007805 (h1 : term27) : term27.
Proof. exact (h1). Qed.
Lemma lem1007806 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1007825 (m : nat) (p : nat) : (term4 m p) = (term28 m p).
Proof. exact (@lem17646 ((term1 m) = p) ((term2 m) = (NUMERAL p))). Qed.
Lemma lem1007827 (n : nat) : ((term1 n) = (Nat.mul n n)) = ((term1 n) = (Nat.mul n n)).
Proof. exact (eq_refl ((term1 n) = (Nat.mul n n))). Qed.
Lemma lem1007828 : term26 = term26.
Proof. exact (fun_ext (fun n : nat => @lem1007827 n)). Qed.
Lemma lem1007829 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1007838 : term27 = term27.
Proof. exact (MK_COMB (@lem1007829) (@lem1007828)). Qed.
Lemma lem1007839 (h1 : term27) : term27.
Proof. exact (EQ_MP (@lem1007838) (@lem1007805 h1)). Qed.
Lemma lem1007840 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem1007841 : term25 = term25.
Proof. exact (fun_ext (fun n : nat => @lem1007840 n)). Qed.
Lemma lem1007842 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1007851 : term11 = term11.
Proof. exact (MK_COMB (@lem1007842) (@lem1007841)). Qed.
Lemma lem1007852 (h1 : term11) : term11.
Proof. exact (EQ_MP (@lem1007851) (@lem1007806 h1)). Qed.
Lemma lem1007926 (m : nat) (p : nat) (h1 : term4 m p) : term28 m p.
Proof. exact (EQ_MP (@lem1007825 m p) (@lem1007804 m p h1)). Qed.
Lemma lem1007945 (n : nat) : ((term1 n) = (Nat.mul n n)) = ((term1 n) = (Nat.mul n n)).
Proof. exact (eq_refl ((term1 n) = (Nat.mul n n))). Qed.
Lemma lem1007946 : term26 = term26.
Proof. exact (fun_ext (fun n : nat => @lem1007945 n)). Qed.
Lemma lem1007947 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1007948 : term27 = term27.
Proof. exact (MK_COMB (@lem1007947) (@lem1007946)). Qed.
Lemma lem1007949 (h1 : term27) : term27.
Proof. exact (EQ_MP (@lem1007948) (@lem1007839 h1)). Qed.
Lemma lem1007956 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem1007957 : term25 = term25.
Proof. exact (fun_ext (fun n : nat => @lem1007956 n)). Qed.
Lemma lem1007958 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1007959 : term11 = term11.
Proof. exact (MK_COMB (@lem1007958) (@lem1007957)). Qed.
Lemma lem1007960 (h1 : term11) : term11.
Proof. exact (EQ_MP (@lem1007959) (@lem1007852 h1)). Qed.
Lemma lem1007961 (m : nat) (p : nat) (h1 : term29 m p) : term29 m p.
Proof. exact (h1). Qed.
Lemma lem1007962 (m : nat) (p : nat) (h1 : term30 m p) : term30 m p.
Proof. exact (h1). Qed.
Lemma lem1007968 (n : nat) : ((term1 n) = (Nat.mul n n)) = ((term1 n) = (Nat.mul n n)).
Proof. exact (eq_refl ((term1 n) = (Nat.mul n n))). Qed.
Lemma lem1007969 : term26 = term26.
Proof. exact (fun_ext (fun n : nat => @lem1007968 n)). Qed.
Lemma lem1007970 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1007972 : term27 = term27.
Proof. exact (MK_COMB (@lem1007970) (@lem1007969)). Qed.
Lemma lem1007973 (h1 : term27) : term27.
Proof. exact (EQ_MP (@lem1007972) (@lem1007949 h1)). Qed.
Lemma lem1007975 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem1007976 : term25 = term25.
Proof. exact (fun_ext (fun n : nat => @lem1007975 n)). Qed.
Lemma lem1007977 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1007979 : term11 = term11.
Proof. exact (MK_COMB (@lem1007977) (@lem1007976)). Qed.
Lemma lem1007980 (h1 : term11) : term11.
Proof. exact (EQ_MP (@lem1007979) (@lem1007960 h1)). Qed.
Lemma lem1007990 (n : nat) : ((term1 n) = (Nat.mul n n)) = ((term1 n) = (Nat.mul n n)).
Proof. exact (eq_refl ((term1 n) = (Nat.mul n n))). Qed.
Lemma lem1007991 : term26 = term26.
Proof. exact (fun_ext (fun n : nat => @lem1007990 n)). Qed.
Lemma lem1007992 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1007994 : term27 = term27.
Proof. exact (MK_COMB (@lem1007992) (@lem1007991)). Qed.
Lemma lem1007995 (h1 : term27) : term27.
Proof. exact (EQ_MP (@lem1007994) (@lem1007949 h1)). Qed.
Lemma lem1007997 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem1007998 : term25 = term25.
Proof. exact (fun_ext (fun n : nat => @lem1007997 n)). Qed.
Lemma lem1007999 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1008001 : term11 = term11.
Proof. exact (MK_COMB (@lem1007999) (@lem1007998)). Qed.
Lemma lem1008002 (h1 : term11) : term11.
Proof. exact (EQ_MP (@lem1008001) (@lem1007960 h1)). Qed.
Lemma lem1008011 (_16342 : nat) (h1 : term27) : term31 _16342.
Proof. exact (@lem1007973 h1 _16342). Qed.
Lemma lem1008012 (_16342 : nat) : (term31 _16342) = ((term1 _16342) = (Nat.mul _16342 _16342)).
Proof. exact (eq_refl (term31 _16342)). Qed.
Lemma lem1008014 (_16343 : nat) (h1 : term11) : term32 _16343.
Proof. exact (@lem1007980 h1 _16343). Qed.
Lemma lem1008015 (_16343 : nat) : (term32 _16343) = ((NUMERAL _16343) = _16343).
Proof. exact (eq_refl (term32 _16343)). Qed.
Lemma lem1008017 (_16344 : nat) (h1 : term27) : term31 _16344.
Proof. exact (@lem1007995 h1 _16344). Qed.
Lemma lem1008018 (_16344 : nat) : (term31 _16344) = ((term1 _16344) = (Nat.mul _16344 _16344)).
Proof. exact (eq_refl (term31 _16344)). Qed.
Lemma lem1008020 (_16345 : nat) (h1 : term11) : term32 _16345.
Proof. exact (@lem1008002 h1 _16345). Qed.
Lemma lem1008021 (_16345 : nat) : (term32 _16345) = ((NUMERAL _16345) = _16345).
Proof. exact (eq_refl (term32 _16345)). Qed.
Lemma lem1008028 (m : nat) (p : nat) (h1 : term29 m p) : (term1 m) = p.
Proof. exact (proj1 (@lem1007961 m p h1)). Qed.
Lemma lem1008030 (m : nat) (p : nat) (h1 : term29 m p) : term33 m p.
Proof. exact (proj2 (@lem1007961 m p h1)). Qed.
Lemma lem1008036 (m : nat) (p : nat) (h1 : term30 m p) : term34 m p.
Proof. exact (proj1 (@lem1007962 m p h1)). Qed.
Lemma lem1008039 (m : nat) (p : nat) (h1 : term29 m p) : p = (term1 m).
Proof. exact (SYM (@lem1008028 m p h1)). Qed.
Lemma lem1008082 (m : nat) : (term35 m) = (term35 m).
Proof. exact (eq_refl (term35 m)). Qed.
Lemma lem1008083 (m : nat) (p : nat) (h1 : term29 m p) : (term36 m p) = (term37 m).
Proof. exact (MK_COMB (@lem1008082 m) (@lem1008039 m p h1)). Qed.
Lemma lem1008084 (m : nat) : (term37 m) = (term38 m).
Proof. exact (eq_refl (term37 m)). Qed.
Lemma lem1008085 (m : nat) (p : nat) : (term39 m p) = (term39 m p).
Proof. exact (eq_refl (term39 m p)). Qed.
Lemma lem1008086 (p : nat) (m : nat) : ((term36 m p) = (term37 m)) = ((term36 m p) = (term38 m)).
Proof. exact (MK_COMB (@lem1008085 m p) (@lem1008084 m)). Qed.
Lemma lem1008087 (m : nat) (p : nat) : (term36 m p) = (term33 m p).
Proof. exact (eq_refl (term36 m p)). Qed.
Lemma lem1008088 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1008089 (m : nat) (p : nat) : (term39 m p) = (term40 m p).
Proof. exact (MK_COMB (@lem1008088) (@lem1008087 m p)). Qed.
Lemma lem1008090 (m : nat) : (term38 m) = (term38 m).
Proof. exact (eq_refl (term38 m)). Qed.
Lemma lem1008091 (p : nat) (m : nat) : ((term36 m p) = (term38 m)) = ((term33 m p) = (term38 m)).
Proof. exact (MK_COMB (@lem1008089 m p) (@lem1008090 m)). Qed.
Lemma lem1008092 (p : nat) (m : nat) : ((term36 m p) = (term37 m)) = ((term33 m p) = (term38 m)).
Proof. exact (TRANS (@lem1008086 p m) (@lem1008091 p m)). Qed.
Lemma lem1008093 (m : nat) (p : nat) (h1 : term29 m p) : (term33 m p) = (term38 m).
Proof. exact (EQ_MP (@lem1008092 p m) (@lem1008083 m p h1)). Qed.
Lemma lem1008094 (m : nat) (p : nat) (h1 : term29 m p) : term38 m.
Proof. exact (EQ_MP (@lem1008093 m p h1) (@lem1008030 m p h1)). Qed.
Lemma lem1008111 : NUMERAL = NUMERAL.
Proof. exact (eq_refl NUMERAL). Qed.
Lemma lem1008112 (_16358 : nat) (_16359 : nat) (h1 : _16358 = _16359) : _16358 = _16359.
Proof. exact (h1). Qed.
Lemma lem1008113 (_16358 : nat) (_16359 : nat) (h1 : _16358 = _16359) : (NUMERAL _16358) = (NUMERAL _16359).
Proof. exact (MK_COMB (@lem1008111) (@lem1008112 _16358 _16359 h1)). Qed.
Lemma lem1008114 (_16358 : nat) (_16359 : nat) : term41 _16358 _16359.
Proof. exact (fun h0 : _16358 = _16359 => @lem1008113 _16358 _16359 h0). Qed.
Lemma lem1008116 (a : Prop) (b : Prop) : (a -> b) = (term42 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1008117 (_16358 : nat) (_16359 : nat) : (term41 _16358 _16359) = (term43 _16358 _16359).
Proof. exact (@lem1008116 (_16358 = _16359) ((NUMERAL _16358) = (NUMERAL _16359))). Qed.
Lemma lem1008118 (_16358 : nat) (_16359 : nat) : term43 _16358 _16359.
Proof. exact (EQ_MP (@lem1008117 _16358 _16359) (@lem1008114 _16358 _16359)). Qed.
Lemma lem1008119 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem1008120 (_16360 : nat) (_16362 : nat) (h1 : _16360 = _16362) : _16360 = _16362.
Proof. exact (h1). Qed.
Lemma lem1008121 (_16361 : nat) (_16363 : nat) (h1 : _16361 = _16363) : _16361 = _16363.
Proof. exact (h1). Qed.
Lemma lem1008122 (_16360 : nat) (_16362 : nat) (h1 : _16360 = _16362) : (Nat.pow _16360) = (Nat.pow _16362).
Proof. exact (MK_COMB (@lem1008119) (@lem1008120 _16360 _16362 h1)). Qed.
Lemma lem1008123 (_16360 : nat) (_16362 : nat) (_16361 : nat) (_16363 : nat) (h1 : _16360 = _16362) (h2 : _16361 = _16363) : (Nat.pow _16360 _16361) = (Nat.pow _16362 _16363).
Proof. exact (MK_COMB (@lem1008122 _16360 _16362 h1) (@lem1008121 _16361 _16363 h2)). Qed.
Lemma lem1008124 (_16361 : nat) (_16363 : nat) (_16360 : nat) (_16362 : nat) (h1 : _16360 = _16362) : term44 _16360 _16361 _16362 _16363.
Proof. exact (fun h0 : _16361 = _16363 => @lem1008123 _16360 _16362 _16361 _16363 h1 h0). Qed.
Lemma lem1008126 (a : Prop) (b : Prop) : (a -> b) = (term42 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1008127 (_16360 : nat) (_16361 : nat) (_16362 : nat) (_16363 : nat) : (term44 _16360 _16361 _16362 _16363) = (term45 _16360 _16361 _16362 _16363).
Proof. exact (@lem1008126 (_16361 = _16363) ((Nat.pow _16360 _16361) = (Nat.pow _16362 _16363))). Qed.
Lemma lem1008128 (_16361 : nat) (_16363 : nat) (_16360 : nat) (_16362 : nat) (h1 : _16360 = _16362) : term45 _16360 _16361 _16362 _16363.
Proof. exact (EQ_MP (@lem1008127 _16360 _16361 _16362 _16363) (@lem1008124 _16361 _16363 _16360 _16362 h1)). Qed.
Lemma lem1008129 (_16360 : nat) (_16361 : nat) (_16362 : nat) (_16363 : nat) : term46 _16360 _16361 _16362 _16363.
Proof. exact (fun h0 : _16360 = _16362 => @lem1008128 _16361 _16363 _16360 _16362 h0). Qed.
Lemma lem1008131 (a : Prop) (b : Prop) : (a -> b) = (term42 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1008132 (_16360 : nat) (_16361 : nat) (_16362 : nat) (_16363 : nat) : (term46 _16360 _16361 _16362 _16363) = (term47 _16360 _16361 _16362 _16363).
Proof. exact (@lem1008131 (_16360 = _16362) (term45 _16360 _16361 _16362 _16363)). Qed.
Lemma lem1008133 (_16360 : nat) (_16361 : nat) (_16362 : nat) (_16363 : nat) : term47 _16360 _16361 _16362 _16363.
Proof. exact (EQ_MP (@lem1008132 _16360 _16361 _16362 _16363) (@lem1008129 _16360 _16361 _16362 _16363)). Qed.
Lemma lem1008150 (x : nat) (y : nat) (z : nat) : term48 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem1008152 (_16343 : nat) (h1 : term11) : (NUMERAL _16343) = _16343.
Proof. exact (EQ_MP (@lem1008015 _16343) (@lem1008014 _16343 h1)). Qed.
Lemma lem1008153 (m : nat) (h1 : term11) : (term49 m) = (term2 m).
Proof. exact (@lem1008152 (term2 m) h1). Qed.
Lemma lem1008154 (m : nat) (h1 : term11) : term50 m.
Proof. exact (fun h0 : term51 m => @lem1008153 m h1). Qed.
Lemma lem1008156 (p : Prop) : (term52 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1008157 (m : nat) : (term50 m) = ((term49 m) = (term2 m)).
Proof. exact (@lem1008156 ((term49 m) = (term2 m))). Qed.
Lemma lem1008158 (m : nat) (h1 : term11) : (term49 m) = (term2 m).
Proof. exact (EQ_MP (@lem1008157 m) (@lem1008154 m h1)). Qed.
Lemma lem1008160 (_16342 : nat) (h1 : term27) : (term1 _16342) = (Nat.mul _16342 _16342).
Proof. exact (EQ_MP (@lem1008012 _16342) (@lem1008011 _16342 h1)). Qed.
Lemma lem1008161 (m : nat) (h1 : term27) : (term53 m) = (term2 m).
Proof. exact (@lem1008160 (NUMERAL m) h1). Qed.
Lemma lem1008162 (m : nat) (h1 : term27) : term54 m.
Proof. exact (fun h0 : term55 m => @lem1008161 m h1). Qed.
Lemma lem1008164 (p : Prop) : (term52 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1008165 (m : nat) : (term54 m) = ((term53 m) = (term2 m)).
Proof. exact (@lem1008164 ((term53 m) = (term2 m))). Qed.
Lemma lem1008166 (m : nat) (h1 : term27) : (term53 m) = (term2 m).
Proof. exact (EQ_MP (@lem1008165 m) (@lem1008162 m h1)). Qed.
Lemma lem1008168 (_16343 : nat) (h1 : term11) : (NUMERAL _16343) = _16343.
Proof. exact (EQ_MP (@lem1008015 _16343) (@lem1008014 _16343 h1)). Qed.
Lemma lem1008169 (m : nat) (h1 : term11) : (NUMERAL m) = m.
Proof. exact (@lem1008168 m h1). Qed.
Lemma lem1008170 (m : nat) (h1 : term11) : term56 m.
Proof. exact (fun h0 : term57 m => @lem1008169 m h1). Qed.
Lemma lem1008172 (p : Prop) : (term52 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1008173 (m : nat) : (term56 m) = ((NUMERAL m) = m).
Proof. exact (@lem1008172 ((NUMERAL m) = m)). Qed.
Lemma lem1008174 (m : nat) (h1 : term11) : (NUMERAL m) = m.
Proof. exact (EQ_MP (@lem1008173 m) (@lem1008170 m h1)). Qed.
Lemma lem1008176 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1008177 : term58 = term58.
Proof. exact (@lem1008176 term58). Qed.
Lemma lem1008178 : term59.
Proof. exact (fun h0 : term60 => @lem1008177). Qed.
Lemma lem1008180 (p : Prop) : (term52 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1008181 : term59 = (term58 = term58).
Proof. exact (@lem1008180 (term58 = term58)). Qed.
Lemma lem1008182 : term58 = term58.
Proof. exact (EQ_MP (@lem1008181) (@lem1008178)). Qed.
Lemma lem1008200 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1008201 (_16360 : nat) (_16362 : nat) (_16361 : nat) (_16363 : nat) : (term45 _16360 _16361 _16362 _16363) = (term61 _16360 _16362 _16361 _16363).
Proof. exact (@lem1008200 ((Nat.pow _16360 _16361) = (Nat.pow _16362 _16363)) (term62 _16361 _16363)). Qed.
Lemma lem1008211 (_16360 : nat) (_16362 : nat) : (term63 _16360 _16362) = (term63 _16360 _16362).
Proof. exact (eq_refl (term63 _16360 _16362)). Qed.
Lemma lem1008212 (_16360 : nat) (_16362 : nat) (_16361 : nat) (_16363 : nat) : (term47 _16360 _16361 _16362 _16363) = (term64 _16360 _16362 _16361 _16363).
Proof. exact (MK_COMB (@lem1008211 _16360 _16362) (@lem1008201 _16360 _16362 _16361 _16363)). Qed.
Lemma lem1008216 (q : Prop) (p : Prop) (r : Prop) : (term65 p q r) = (term65 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1008217 (_16360 : nat) (_16362 : nat) (_16361 : nat) (_16363 : nat) : (term64 _16360 _16362 _16361 _16363) = (term66 _16360 _16362 _16361 _16363).
Proof. exact (@lem1008216 ((Nat.pow _16360 _16361) = (Nat.pow _16362 _16363)) (term62 _16360 _16362) (term62 _16361 _16363)). Qed.
Lemma lem1008239 (_16360 : nat) (_16362 : nat) (_16361 : nat) (_16363 : nat) : (term47 _16360 _16361 _16362 _16363) = (term66 _16360 _16362 _16361 _16363).
Proof. exact (TRANS (@lem1008212 _16360 _16362 _16361 _16363) (@lem1008217 _16360 _16362 _16361 _16363)). Qed.
Lemma lem1008240 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1008241 (_16360 : nat) (_16362 : nat) (_16361 : nat) (_16363 : nat) : (term67 _16360 _16361 _16362 _16363) = (term68 _16360 _16362 _16361 _16363).
Proof. exact (MK_COMB (@lem1008240) (@lem1008239 _16360 _16362 _16361 _16363)). Qed.
Lemma lem1008263 (_16360 : nat) (_16362 : nat) (_16361 : nat) (_16363 : nat) : (term66 _16360 _16362 _16361 _16363) = (term66 _16360 _16362 _16361 _16363).
Proof. exact (eq_refl (term66 _16360 _16362 _16361 _16363)). Qed.
Lemma lem1008264 (_16360 : nat) (_16362 : nat) (_16361 : nat) (_16363 : nat) : ((term47 _16360 _16361 _16362 _16363) = (term66 _16360 _16362 _16361 _16363)) = ((term66 _16360 _16362 _16361 _16363) = (term66 _16360 _16362 _16361 _16363)).
Proof. exact (MK_COMB (@lem1008241 _16360 _16362 _16361 _16363) (@lem1008263 _16360 _16362 _16361 _16363)). Qed.
Lemma lem1008266 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1008267 (x : Prop) : (x = x) = True.
Proof. exact (@lem1008266 Prop x). Qed.
Lemma lem1008268 (_16360 : nat) (_16362 : nat) (_16361 : nat) (_16363 : nat) : ((term66 _16360 _16362 _16361 _16363) = (term66 _16360 _16362 _16361 _16363)) = True.
Proof. exact (@lem1008267 (term66 _16360 _16362 _16361 _16363)). Qed.
Lemma lem1008269 (_16360 : nat) (_16362 : nat) (_16361 : nat) (_16363 : nat) : ((term47 _16360 _16361 _16362 _16363) = (term66 _16360 _16362 _16361 _16363)) = True.
Proof. exact (TRANS (@lem1008264 _16360 _16362 _16361 _16363) (@lem1008268 _16360 _16362 _16361 _16363)). Qed.
Lemma lem1008270 (_16360 : nat) (_16362 : nat) (_16361 : nat) (_16363 : nat) : True = ((term47 _16360 _16361 _16362 _16363) = (term66 _16360 _16362 _16361 _16363)).
Proof. exact (SYM (@lem1008269 _16360 _16362 _16361 _16363)). Qed.
Lemma lem1008271 (_16360 : nat) (_16362 : nat) (_16361 : nat) (_16363 : nat) : (term47 _16360 _16361 _16362 _16363) = (term66 _16360 _16362 _16361 _16363).
Proof. exact (EQ_MP (@lem1008270 _16360 _16362 _16361 _16363) (@lem0)). Qed.
Lemma lem1008272 (_16360 : nat) (_16362 : nat) (_16361 : nat) (_16363 : nat) : term66 _16360 _16362 _16361 _16363.
Proof. exact (EQ_MP (@lem1008271 _16360 _16362 _16361 _16363) (@lem1008133 _16360 _16361 _16362 _16363)). Qed.
Lemma lem1008274 (b : Prop) (a : Prop) : (a \/ b) = (term69 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1008275 (_16360 : nat) (_16361 : nat) (_16362 : nat) (_16363 : nat) : (term66 _16360 _16362 _16361 _16363) = (term70 _16360 _16361 _16362 _16363).
Proof. exact (@lem1008274 (term71 _16360 _16362 _16361 _16363) ((Nat.pow _16360 _16361) = (Nat.pow _16362 _16363))). Qed.
Lemma lem1008277 (a : Prop) (b : Prop) : (term72 a b) = (term73 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1008278 (_16360 : nat) (_16362 : nat) (_16361 : nat) (_16363 : nat) : (term74 _16360 _16362 _16361 _16363) = (term75 _16360 _16362 _16361 _16363).
Proof. exact (@lem1008277 (term62 _16360 _16362) (term62 _16361 _16363)). Qed.
Lemma lem1008280 (a : Prop) : (term76 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1008281 (_16360 : nat) (_16362 : nat) : (term77 _16360 _16362) = (_16360 = _16362).
Proof. exact (@lem1008280 (_16360 = _16362)). Qed.
Lemma lem1008282 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1008283 (_16360 : nat) (_16362 : nat) : (term78 _16360 _16362) = (term79 _16360 _16362).
Proof. exact (MK_COMB (@lem1008282) (@lem1008281 _16360 _16362)). Qed.
Lemma lem1008285 (a : Prop) : (term76 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1008286 (_16361 : nat) (_16363 : nat) : (term77 _16361 _16363) = (_16361 = _16363).
Proof. exact (@lem1008285 (_16361 = _16363)). Qed.
Lemma lem1008287 (_16360 : nat) (_16362 : nat) (_16361 : nat) (_16363 : nat) : (term75 _16360 _16362 _16361 _16363) = (term80 _16360 _16362 _16361 _16363).
Proof. exact (MK_COMB (@lem1008283 _16360 _16362) (@lem1008286 _16361 _16363)). Qed.
Lemma lem1008288 (_16360 : nat) (_16362 : nat) (_16361 : nat) (_16363 : nat) : (term74 _16360 _16362 _16361 _16363) = (term80 _16360 _16362 _16361 _16363).
Proof. exact (TRANS (@lem1008278 _16360 _16362 _16361 _16363) (@lem1008287 _16360 _16362 _16361 _16363)). Qed.
Lemma lem1008289 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1008290 (_16360 : nat) (_16362 : nat) (_16361 : nat) (_16363 : nat) : (term81 _16360 _16362 _16361 _16363) = (term82 _16360 _16362 _16361 _16363).
Proof. exact (MK_COMB (@lem1008289) (@lem1008288 _16360 _16362 _16361 _16363)). Qed.
Lemma lem1008291 (_16360 : nat) (_16361 : nat) (_16362 : nat) (_16363 : nat) : ((Nat.pow _16360 _16361) = (Nat.pow _16362 _16363)) = ((Nat.pow _16360 _16361) = (Nat.pow _16362 _16363)).
Proof. exact (eq_refl ((Nat.pow _16360 _16361) = (Nat.pow _16362 _16363))). Qed.
Lemma lem1008292 (_16360 : nat) (_16361 : nat) (_16362 : nat) (_16363 : nat) : (term70 _16360 _16361 _16362 _16363) = (term83 _16360 _16361 _16362 _16363).
Proof. exact (MK_COMB (@lem1008290 _16360 _16362 _16361 _16363) (@lem1008291 _16360 _16361 _16362 _16363)). Qed.
Lemma lem1008293 (_16360 : nat) (_16361 : nat) (_16362 : nat) (_16363 : nat) : (term66 _16360 _16362 _16361 _16363) = (term83 _16360 _16361 _16362 _16363).
Proof. exact (TRANS (@lem1008275 _16360 _16361 _16362 _16363) (@lem1008292 _16360 _16361 _16362 _16363)). Qed.
Lemma lem1008295 (m : nat) (h1 : term11) : term84 m.
Proof. exact (conj (@lem1008174 m h1) (@lem1008182)). Qed.
Lemma lem1008297 (_16360 : nat) (_16361 : nat) (_16362 : nat) (_16363 : nat) : term83 _16360 _16361 _16362 _16363.
Proof. exact (EQ_MP (@lem1008293 _16360 _16361 _16362 _16363) (@lem1008272 _16360 _16362 _16361 _16363)). Qed.
Lemma lem1008298 (m : nat) : term85 m.
Proof. exact (@lem1008297 (NUMERAL m) term58 m term58). Qed.
Lemma lem1008301 (m : nat) (h1 : term11) : (term53 m) = (term1 m).
Proof. exact (@lem1008298 m (@lem1008295 m h1)). Qed.
Lemma lem1008302 (m : nat) (h1 : term11) : term86 m.
Proof. exact (fun h0 : term87 m => @lem1008301 m h1). Qed.
Lemma lem1008304 (p : Prop) : (term52 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1008305 (m : nat) : (term86 m) = ((term53 m) = (term1 m)).
Proof. exact (@lem1008304 ((term53 m) = (term1 m))). Qed.
Lemma lem1008306 (m : nat) (h1 : term11) : (term53 m) = (term1 m).
Proof. exact (EQ_MP (@lem1008305 m) (@lem1008302 m h1)). Qed.
Lemma lem1008324 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1008325 (y : nat) (x : nat) (z : nat) : (term88 x y z) = (term89 y x z).
Proof. exact (@lem1008324 (y = z) (term62 x z)). Qed.
Lemma lem1008335 (x : nat) (y : nat) : (term63 x y) = (term63 x y).
Proof. exact (eq_refl (term63 x y)). Qed.
Lemma lem1008336 (y : nat) (x : nat) (z : nat) : (term48 x y z) = (term90 y x z).
Proof. exact (MK_COMB (@lem1008335 x y) (@lem1008325 y x z)). Qed.
Lemma lem1008340 (q : Prop) (p : Prop) (r : Prop) : (term65 p q r) = (term65 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1008341 (y : nat) (x : nat) (z : nat) : (term90 y x z) = (term91 y x z).
Proof. exact (@lem1008340 (y = z) (term62 x y) (term62 x z)). Qed.
Lemma lem1008363 (y : nat) (x : nat) (z : nat) : (term48 x y z) = (term91 y x z).
Proof. exact (TRANS (@lem1008336 y x z) (@lem1008341 y x z)). Qed.
Lemma lem1008364 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1008365 (y : nat) (x : nat) (z : nat) : (term92 x y z) = (term93 y x z).
Proof. exact (MK_COMB (@lem1008364) (@lem1008363 y x z)). Qed.
Lemma lem1008387 (y : nat) (x : nat) (z : nat) : (term91 y x z) = (term91 y x z).
Proof. exact (eq_refl (term91 y x z)). Qed.
Lemma lem1008388 (y : nat) (x : nat) (z : nat) : ((term48 x y z) = (term91 y x z)) = ((term91 y x z) = (term91 y x z)).
Proof. exact (MK_COMB (@lem1008365 y x z) (@lem1008387 y x z)). Qed.
Lemma lem1008390 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1008391 (x : Prop) : (x = x) = True.
Proof. exact (@lem1008390 Prop x). Qed.
Lemma lem1008392 (y : nat) (x : nat) (z : nat) : ((term91 y x z) = (term91 y x z)) = True.
Proof. exact (@lem1008391 (term91 y x z)). Qed.
Lemma lem1008393 (y : nat) (x : nat) (z : nat) : ((term48 x y z) = (term91 y x z)) = True.
Proof. exact (TRANS (@lem1008388 y x z) (@lem1008392 y x z)). Qed.
Lemma lem1008394 (y : nat) (x : nat) (z : nat) : True = ((term48 x y z) = (term91 y x z)).
Proof. exact (SYM (@lem1008393 y x z)). Qed.
Lemma lem1008395 (y : nat) (x : nat) (z : nat) : (term48 x y z) = (term91 y x z).
Proof. exact (EQ_MP (@lem1008394 y x z) (@lem0)). Qed.
Lemma lem1008396 (y : nat) (x : nat) (z : nat) : term91 y x z.
Proof. exact (EQ_MP (@lem1008395 y x z) (@lem1008150 x y z)). Qed.
Lemma lem1008398 (b : Prop) (a : Prop) : (a \/ b) = (term69 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1008399 (x : nat) (y : nat) (z : nat) : (term91 y x z) = (term94 x y z).
Proof. exact (@lem1008398 (term95 y x z) (y = z)). Qed.
Lemma lem1008401 (a : Prop) (b : Prop) : (term72 a b) = (term73 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1008402 (y : nat) (x : nat) (z : nat) : (term96 y x z) = (term97 y x z).
Proof. exact (@lem1008401 (term62 x y) (term62 x z)). Qed.
Lemma lem1008404 (a : Prop) : (term76 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1008405 (x : nat) (y : nat) : (term77 x y) = (x = y).
Proof. exact (@lem1008404 (x = y)). Qed.
Lemma lem1008406 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1008407 (x : nat) (y : nat) : (term78 x y) = (term79 x y).
Proof. exact (MK_COMB (@lem1008406) (@lem1008405 x y)). Qed.
Lemma lem1008409 (a : Prop) : (term76 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1008410 (x : nat) (z : nat) : (term77 x z) = (x = z).
Proof. exact (@lem1008409 (x = z)). Qed.
Lemma lem1008411 (y : nat) (x : nat) (z : nat) : (term97 y x z) = (term98 y x z).
Proof. exact (MK_COMB (@lem1008407 x y) (@lem1008410 x z)). Qed.
Lemma lem1008412 (y : nat) (x : nat) (z : nat) : (term96 y x z) = (term98 y x z).
Proof. exact (TRANS (@lem1008402 y x z) (@lem1008411 y x z)). Qed.
Lemma lem1008413 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1008414 (y : nat) (x : nat) (z : nat) : (term99 y x z) = (term100 y x z).
Proof. exact (MK_COMB (@lem1008413) (@lem1008412 y x z)). Qed.
Lemma lem1008415 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1008416 (x : nat) (y : nat) (z : nat) : (term94 x y z) = (term101 x y z).
Proof. exact (MK_COMB (@lem1008414 y x z) (@lem1008415 y z)). Qed.
Lemma lem1008417 (x : nat) (y : nat) (z : nat) : (term91 y x z) = (term101 x y z).
Proof. exact (TRANS (@lem1008399 x y z) (@lem1008416 x y z)). Qed.
Lemma lem1008419 (m : nat) (h1 : term11) (h2 : term27) : term102 m.
Proof. exact (conj (@lem1008166 m h2) (@lem1008306 m h1)). Qed.
Lemma lem1008421 (x : nat) (y : nat) (z : nat) : term101 x y z.
Proof. exact (EQ_MP (@lem1008417 x y z) (@lem1008396 y x z)). Qed.
Lemma lem1008422 (m : nat) : term103 m.
Proof. exact (@lem1008421 (term53 m) (term2 m) (term1 m)). Qed.
Lemma lem1008425 (m : nat) (h1 : term11) (h2 : term27) : (term2 m) = (term1 m).
Proof. exact (@lem1008422 m (@lem1008419 m h1 h2)). Qed.
Lemma lem1008426 (m : nat) (h1 : term11) (h2 : term27) : term104 m.
Proof. exact (fun h0 : term105 m => @lem1008425 m h1 h2). Qed.
Lemma lem1008428 (p : Prop) : (term52 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1008429 (m : nat) : (term104 m) = ((term2 m) = (term1 m)).
Proof. exact (@lem1008428 ((term2 m) = (term1 m))). Qed.
Lemma lem1008430 (m : nat) (h1 : term11) (h2 : term27) : (term2 m) = (term1 m).
Proof. exact (EQ_MP (@lem1008429 m) (@lem1008426 m h1 h2)). Qed.
Lemma lem1008436 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1008437 (_16358 : nat) (_16359 : nat) : (term43 _16358 _16359) = (term106 _16358 _16359).
Proof. exact (@lem1008436 ((NUMERAL _16358) = (NUMERAL _16359)) (term62 _16358 _16359)). Qed.
Lemma lem1008447 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1008448 (_16358 : nat) (_16359 : nat) : (term107 _16358 _16359) = (term108 _16358 _16359).
Proof. exact (MK_COMB (@lem1008447) (@lem1008437 _16358 _16359)). Qed.
Lemma lem1008458 (_16358 : nat) (_16359 : nat) : (term106 _16358 _16359) = (term106 _16358 _16359).
Proof. exact (eq_refl (term106 _16358 _16359)). Qed.
Lemma lem1008459 (_16358 : nat) (_16359 : nat) : ((term43 _16358 _16359) = (term106 _16358 _16359)) = ((term106 _16358 _16359) = (term106 _16358 _16359)).
Proof. exact (MK_COMB (@lem1008448 _16358 _16359) (@lem1008458 _16358 _16359)). Qed.
Lemma lem1008461 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1008462 (x : Prop) : (x = x) = True.
Proof. exact (@lem1008461 Prop x). Qed.
Lemma lem1008463 (_16358 : nat) (_16359 : nat) : ((term106 _16358 _16359) = (term106 _16358 _16359)) = True.
Proof. exact (@lem1008462 (term106 _16358 _16359)). Qed.
Lemma lem1008464 (_16358 : nat) (_16359 : nat) : ((term43 _16358 _16359) = (term106 _16358 _16359)) = True.
Proof. exact (TRANS (@lem1008459 _16358 _16359) (@lem1008463 _16358 _16359)). Qed.
Lemma lem1008465 (_16358 : nat) (_16359 : nat) : True = ((term43 _16358 _16359) = (term106 _16358 _16359)).
Proof. exact (SYM (@lem1008464 _16358 _16359)). Qed.
Lemma lem1008466 (_16358 : nat) (_16359 : nat) : (term43 _16358 _16359) = (term106 _16358 _16359).
Proof. exact (EQ_MP (@lem1008465 _16358 _16359) (@lem0)). Qed.
Lemma lem1008467 (_16358 : nat) (_16359 : nat) : term106 _16358 _16359.
Proof. exact (EQ_MP (@lem1008466 _16358 _16359) (@lem1008118 _16358 _16359)). Qed.
Lemma lem1008469 (b : Prop) (a : Prop) : (a \/ b) = (term69 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1008470 (_16358 : nat) (_16359 : nat) : (term106 _16358 _16359) = (term109 _16358 _16359).
Proof. exact (@lem1008469 (term62 _16358 _16359) ((NUMERAL _16358) = (NUMERAL _16359))). Qed.
Lemma lem1008472 (a : Prop) : (term76 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1008473 (_16358 : nat) (_16359 : nat) : (term77 _16358 _16359) = (_16358 = _16359).
Proof. exact (@lem1008472 (_16358 = _16359)). Qed.
Lemma lem1008474 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1008475 (_16358 : nat) (_16359 : nat) : (term110 _16358 _16359) = (term111 _16358 _16359).
Proof. exact (MK_COMB (@lem1008474) (@lem1008473 _16358 _16359)). Qed.
Lemma lem1008476 (_16358 : nat) (_16359 : nat) : ((NUMERAL _16358) = (NUMERAL _16359)) = ((NUMERAL _16358) = (NUMERAL _16359)).
Proof. exact (eq_refl ((NUMERAL _16358) = (NUMERAL _16359))). Qed.
Lemma lem1008477 (_16358 : nat) (_16359 : nat) : (term109 _16358 _16359) = (term41 _16358 _16359).
Proof. exact (MK_COMB (@lem1008475 _16358 _16359) (@lem1008476 _16358 _16359)). Qed.
Lemma lem1008478 (_16358 : nat) (_16359 : nat) : (term106 _16358 _16359) = (term41 _16358 _16359).
Proof. exact (TRANS (@lem1008470 _16358 _16359) (@lem1008477 _16358 _16359)). Qed.
Lemma lem1008481 (_16358 : nat) (_16359 : nat) : term41 _16358 _16359.
Proof. exact (EQ_MP (@lem1008478 _16358 _16359) (@lem1008467 _16358 _16359)). Qed.
Lemma lem1008482 (m : nat) : term112 m.
Proof. exact (@lem1008481 (term2 m) (term1 m)). Qed.
Lemma lem1008485 (m : nat) (h1 : term11) (h2 : term27) : (term49 m) = (term113 m).
Proof. exact (@lem1008482 m (@lem1008430 m h1 h2)). Qed.
Lemma lem1008486 (m : nat) (h1 : term11) (h2 : term27) : term114 m.
Proof. exact (fun h0 : term115 m => @lem1008485 m h1 h2). Qed.
Lemma lem1008488 (p : Prop) : (term52 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1008489 (m : nat) : (term114 m) = ((term49 m) = (term113 m)).
Proof. exact (@lem1008488 ((term49 m) = (term113 m))). Qed.
Lemma lem1008490 (m : nat) (h1 : term11) (h2 : term27) : (term49 m) = (term113 m).
Proof. exact (EQ_MP (@lem1008489 m) (@lem1008486 m h1 h2)). Qed.
Lemma lem1008491 (m : nat) (h1 : term11) (h2 : term27) : term116 m.
Proof. exact (conj (@lem1008158 m h1) (@lem1008490 m h1 h2)). Qed.
Lemma lem1008493 (x : nat) (y : nat) (z : nat) : term101 x y z.
Proof. exact (EQ_MP (@lem1008417 x y z) (@lem1008396 y x z)). Qed.
Lemma lem1008494 (m : nat) : term117 m.
Proof. exact (@lem1008493 (term49 m) (term2 m) (term113 m)). Qed.
Lemma lem1008497 (m : nat) (h1 : term11) (h2 : term27) : (term2 m) = (term113 m).
Proof. exact (@lem1008494 m (@lem1008491 m h1 h2)). Qed.
Lemma lem1008498 (m : nat) (h1 : term11) (h2 : term27) : term118 m.
Proof. exact (fun h0 : term38 m => @lem1008497 m h1 h2). Qed.
Lemma lem1008500 (p : Prop) : (term52 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1008501 (m : nat) : (term118 m) = ((term2 m) = (term113 m)).
Proof. exact (@lem1008500 ((term2 m) = (term113 m))). Qed.
Lemma lem1008502 (m : nat) (h1 : term11) (h2 : term27) : (term2 m) = (term113 m).
Proof. exact (EQ_MP (@lem1008501 m) (@lem1008498 m h1 h2)). Qed.
Lemma lem1008505 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1008507 (m : nat) : (term38 m) = (term119 m).
Proof. exact (@lem1008505 ((term2 m) = (term113 m))). Qed.
Lemma lem1008510 (m : nat) (p : nat) (h1 : term29 m p) : term119 m.
Proof. exact (EQ_MP (@lem1008507 m) (@lem1008094 m p h1)). Qed.
Lemma lem1008513 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term29 m p) : False.
Proof. exact (@lem1008510 m p h3 (@lem1008502 m h1 h2)). Qed.
Lemma lem1008514 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term29 m p) : term120.
Proof. exact (fun h0 : ~ False => @lem1008513 m p h1 h2 h3). Qed.
Lemma lem1008516 (p : Prop) : (term52 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1008517 : term120 = False.
Proof. exact (@lem1008516 False). Qed.
Lemma lem1008543 : Nat.pow = Nat.pow.
Proof. exact (eq_refl Nat.pow). Qed.
Lemma lem1008544 (_16374 : nat) (_16376 : nat) (h1 : _16374 = _16376) : _16374 = _16376.
Proof. exact (h1). Qed.
Lemma lem1008545 (_16375 : nat) (_16377 : nat) (h1 : _16375 = _16377) : _16375 = _16377.
Proof. exact (h1). Qed.
Lemma lem1008546 (_16374 : nat) (_16376 : nat) (h1 : _16374 = _16376) : (Nat.pow _16374) = (Nat.pow _16376).
Proof. exact (MK_COMB (@lem1008543) (@lem1008544 _16374 _16376 h1)). Qed.
Lemma lem1008547 (_16374 : nat) (_16376 : nat) (_16375 : nat) (_16377 : nat) (h1 : _16374 = _16376) (h2 : _16375 = _16377) : (Nat.pow _16374 _16375) = (Nat.pow _16376 _16377).
Proof. exact (MK_COMB (@lem1008546 _16374 _16376 h1) (@lem1008545 _16375 _16377 h2)). Qed.
Lemma lem1008548 (_16375 : nat) (_16377 : nat) (_16374 : nat) (_16376 : nat) (h1 : _16374 = _16376) : term44 _16374 _16375 _16376 _16377.
Proof. exact (fun h0 : _16375 = _16377 => @lem1008547 _16374 _16376 _16375 _16377 h1 h0). Qed.
Lemma lem1008550 (a : Prop) (b : Prop) : (a -> b) = (term42 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1008551 (_16374 : nat) (_16375 : nat) (_16376 : nat) (_16377 : nat) : (term44 _16374 _16375 _16376 _16377) = (term45 _16374 _16375 _16376 _16377).
Proof. exact (@lem1008550 (_16375 = _16377) ((Nat.pow _16374 _16375) = (Nat.pow _16376 _16377))). Qed.
Lemma lem1008552 (_16375 : nat) (_16377 : nat) (_16374 : nat) (_16376 : nat) (h1 : _16374 = _16376) : term45 _16374 _16375 _16376 _16377.
Proof. exact (EQ_MP (@lem1008551 _16374 _16375 _16376 _16377) (@lem1008548 _16375 _16377 _16374 _16376 h1)). Qed.
Lemma lem1008553 (_16374 : nat) (_16375 : nat) (_16376 : nat) (_16377 : nat) : term46 _16374 _16375 _16376 _16377.
Proof. exact (fun h0 : _16374 = _16376 => @lem1008552 _16375 _16377 _16374 _16376 h0). Qed.
Lemma lem1008555 (a : Prop) (b : Prop) : (a -> b) = (term42 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1008556 (_16374 : nat) (_16375 : nat) (_16376 : nat) (_16377 : nat) : (term46 _16374 _16375 _16376 _16377) = (term47 _16374 _16375 _16376 _16377).
Proof. exact (@lem1008555 (_16374 = _16376) (term45 _16374 _16375 _16376 _16377)). Qed.
Lemma lem1008557 (_16374 : nat) (_16375 : nat) (_16376 : nat) (_16377 : nat) : term47 _16374 _16375 _16376 _16377.
Proof. exact (EQ_MP (@lem1008556 _16374 _16375 _16376 _16377) (@lem1008553 _16374 _16375 _16376 _16377)). Qed.
Lemma lem1008574 (x : nat) (y : nat) (z : nat) : term48 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem1008576 (m : nat) (p : nat) (h1 : term30 m p) : (term2 m) = (NUMERAL p).
Proof. exact (proj2 (@lem1007962 m p h1)). Qed.
Lemma lem1008577 (m : nat) (p : nat) (h1 : term30 m p) : term121 m p.
Proof. exact (fun h0 : term33 m p => @lem1008576 m p h1). Qed.
Lemma lem1008579 (p : Prop) : (term52 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1008580 (m : nat) (p : nat) : (term121 m p) = ((term2 m) = (NUMERAL p)).
Proof. exact (@lem1008579 ((term2 m) = (NUMERAL p))). Qed.
Lemma lem1008581 (m : nat) (p : nat) (h1 : term30 m p) : (term2 m) = (NUMERAL p).
Proof. exact (EQ_MP (@lem1008580 m p) (@lem1008577 m p h1)). Qed.
Lemma lem1008583 (_16344 : nat) (h1 : term27) : (term1 _16344) = (Nat.mul _16344 _16344).
Proof. exact (EQ_MP (@lem1008018 _16344) (@lem1008017 _16344 h1)). Qed.
Lemma lem1008584 (m : nat) (h1 : term27) : (term53 m) = (term2 m).
Proof. exact (@lem1008583 (NUMERAL m) h1). Qed.
Lemma lem1008585 (m : nat) (h1 : term27) : term54 m.
Proof. exact (fun h0 : term55 m => @lem1008584 m h1). Qed.
Lemma lem1008587 (p : Prop) : (term52 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1008588 (m : nat) : (term54 m) = ((term53 m) = (term2 m)).
Proof. exact (@lem1008587 ((term53 m) = (term2 m))). Qed.
Lemma lem1008589 (m : nat) (h1 : term27) : (term53 m) = (term2 m).
Proof. exact (EQ_MP (@lem1008588 m) (@lem1008585 m h1)). Qed.
Lemma lem1008591 (_16345 : nat) (h1 : term11) : (NUMERAL _16345) = _16345.
Proof. exact (EQ_MP (@lem1008021 _16345) (@lem1008020 _16345 h1)). Qed.
Lemma lem1008592 (m : nat) (h1 : term11) : (NUMERAL m) = m.
Proof. exact (@lem1008591 m h1). Qed.
Lemma lem1008593 (m : nat) (h1 : term11) : term56 m.
Proof. exact (fun h0 : term57 m => @lem1008592 m h1). Qed.
Lemma lem1008595 (p : Prop) : (term52 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1008596 (m : nat) : (term56 m) = ((NUMERAL m) = m).
Proof. exact (@lem1008595 ((NUMERAL m) = m)). Qed.
Lemma lem1008597 (m : nat) (h1 : term11) : (NUMERAL m) = m.
Proof. exact (EQ_MP (@lem1008596 m) (@lem1008593 m h1)). Qed.
Lemma lem1008599 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1008600 : term58 = term58.
Proof. exact (@lem1008599 term58). Qed.
Lemma lem1008601 : term59.
Proof. exact (fun h0 : term60 => @lem1008600). Qed.
Lemma lem1008603 (p : Prop) : (term52 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1008604 : term59 = (term58 = term58).
Proof. exact (@lem1008603 (term58 = term58)). Qed.
Lemma lem1008605 : term58 = term58.
Proof. exact (EQ_MP (@lem1008604) (@lem1008601)). Qed.
Lemma lem1008623 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1008624 (_16374 : nat) (_16376 : nat) (_16375 : nat) (_16377 : nat) : (term45 _16374 _16375 _16376 _16377) = (term61 _16374 _16376 _16375 _16377).
Proof. exact (@lem1008623 ((Nat.pow _16374 _16375) = (Nat.pow _16376 _16377)) (term62 _16375 _16377)). Qed.
Lemma lem1008634 (_16374 : nat) (_16376 : nat) : (term63 _16374 _16376) = (term63 _16374 _16376).
Proof. exact (eq_refl (term63 _16374 _16376)). Qed.
Lemma lem1008635 (_16374 : nat) (_16376 : nat) (_16375 : nat) (_16377 : nat) : (term47 _16374 _16375 _16376 _16377) = (term64 _16374 _16376 _16375 _16377).
Proof. exact (MK_COMB (@lem1008634 _16374 _16376) (@lem1008624 _16374 _16376 _16375 _16377)). Qed.
Lemma lem1008639 (q : Prop) (p : Prop) (r : Prop) : (term65 p q r) = (term65 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1008640 (_16374 : nat) (_16376 : nat) (_16375 : nat) (_16377 : nat) : (term64 _16374 _16376 _16375 _16377) = (term66 _16374 _16376 _16375 _16377).
Proof. exact (@lem1008639 ((Nat.pow _16374 _16375) = (Nat.pow _16376 _16377)) (term62 _16374 _16376) (term62 _16375 _16377)). Qed.
Lemma lem1008662 (_16374 : nat) (_16376 : nat) (_16375 : nat) (_16377 : nat) : (term47 _16374 _16375 _16376 _16377) = (term66 _16374 _16376 _16375 _16377).
Proof. exact (TRANS (@lem1008635 _16374 _16376 _16375 _16377) (@lem1008640 _16374 _16376 _16375 _16377)). Qed.
Lemma lem1008663 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1008664 (_16374 : nat) (_16376 : nat) (_16375 : nat) (_16377 : nat) : (term67 _16374 _16375 _16376 _16377) = (term68 _16374 _16376 _16375 _16377).
Proof. exact (MK_COMB (@lem1008663) (@lem1008662 _16374 _16376 _16375 _16377)). Qed.
Lemma lem1008686 (_16374 : nat) (_16376 : nat) (_16375 : nat) (_16377 : nat) : (term66 _16374 _16376 _16375 _16377) = (term66 _16374 _16376 _16375 _16377).
Proof. exact (eq_refl (term66 _16374 _16376 _16375 _16377)). Qed.
Lemma lem1008687 (_16374 : nat) (_16376 : nat) (_16375 : nat) (_16377 : nat) : ((term47 _16374 _16375 _16376 _16377) = (term66 _16374 _16376 _16375 _16377)) = ((term66 _16374 _16376 _16375 _16377) = (term66 _16374 _16376 _16375 _16377)).
Proof. exact (MK_COMB (@lem1008664 _16374 _16376 _16375 _16377) (@lem1008686 _16374 _16376 _16375 _16377)). Qed.
Lemma lem1008689 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1008690 (x : Prop) : (x = x) = True.
Proof. exact (@lem1008689 Prop x). Qed.
Lemma lem1008691 (_16374 : nat) (_16376 : nat) (_16375 : nat) (_16377 : nat) : ((term66 _16374 _16376 _16375 _16377) = (term66 _16374 _16376 _16375 _16377)) = True.
Proof. exact (@lem1008690 (term66 _16374 _16376 _16375 _16377)). Qed.
Lemma lem1008692 (_16374 : nat) (_16376 : nat) (_16375 : nat) (_16377 : nat) : ((term47 _16374 _16375 _16376 _16377) = (term66 _16374 _16376 _16375 _16377)) = True.
Proof. exact (TRANS (@lem1008687 _16374 _16376 _16375 _16377) (@lem1008691 _16374 _16376 _16375 _16377)). Qed.
Lemma lem1008693 (_16374 : nat) (_16376 : nat) (_16375 : nat) (_16377 : nat) : True = ((term47 _16374 _16375 _16376 _16377) = (term66 _16374 _16376 _16375 _16377)).
Proof. exact (SYM (@lem1008692 _16374 _16376 _16375 _16377)). Qed.
Lemma lem1008694 (_16374 : nat) (_16376 : nat) (_16375 : nat) (_16377 : nat) : (term47 _16374 _16375 _16376 _16377) = (term66 _16374 _16376 _16375 _16377).
Proof. exact (EQ_MP (@lem1008693 _16374 _16376 _16375 _16377) (@lem0)). Qed.
Lemma lem1008695 (_16374 : nat) (_16376 : nat) (_16375 : nat) (_16377 : nat) : term66 _16374 _16376 _16375 _16377.
Proof. exact (EQ_MP (@lem1008694 _16374 _16376 _16375 _16377) (@lem1008557 _16374 _16375 _16376 _16377)). Qed.
Lemma lem1008697 (b : Prop) (a : Prop) : (a \/ b) = (term69 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1008698 (_16374 : nat) (_16375 : nat) (_16376 : nat) (_16377 : nat) : (term66 _16374 _16376 _16375 _16377) = (term70 _16374 _16375 _16376 _16377).
Proof. exact (@lem1008697 (term71 _16374 _16376 _16375 _16377) ((Nat.pow _16374 _16375) = (Nat.pow _16376 _16377))). Qed.
Lemma lem1008700 (a : Prop) (b : Prop) : (term72 a b) = (term73 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1008701 (_16374 : nat) (_16376 : nat) (_16375 : nat) (_16377 : nat) : (term74 _16374 _16376 _16375 _16377) = (term75 _16374 _16376 _16375 _16377).
Proof. exact (@lem1008700 (term62 _16374 _16376) (term62 _16375 _16377)). Qed.
Lemma lem1008703 (a : Prop) : (term76 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1008704 (_16374 : nat) (_16376 : nat) : (term77 _16374 _16376) = (_16374 = _16376).
Proof. exact (@lem1008703 (_16374 = _16376)). Qed.
Lemma lem1008705 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1008706 (_16374 : nat) (_16376 : nat) : (term78 _16374 _16376) = (term79 _16374 _16376).
Proof. exact (MK_COMB (@lem1008705) (@lem1008704 _16374 _16376)). Qed.
Lemma lem1008708 (a : Prop) : (term76 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1008709 (_16375 : nat) (_16377 : nat) : (term77 _16375 _16377) = (_16375 = _16377).
Proof. exact (@lem1008708 (_16375 = _16377)). Qed.
Lemma lem1008710 (_16374 : nat) (_16376 : nat) (_16375 : nat) (_16377 : nat) : (term75 _16374 _16376 _16375 _16377) = (term80 _16374 _16376 _16375 _16377).
Proof. exact (MK_COMB (@lem1008706 _16374 _16376) (@lem1008709 _16375 _16377)). Qed.
Lemma lem1008711 (_16374 : nat) (_16376 : nat) (_16375 : nat) (_16377 : nat) : (term74 _16374 _16376 _16375 _16377) = (term80 _16374 _16376 _16375 _16377).
Proof. exact (TRANS (@lem1008701 _16374 _16376 _16375 _16377) (@lem1008710 _16374 _16376 _16375 _16377)). Qed.
Lemma lem1008712 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1008713 (_16374 : nat) (_16376 : nat) (_16375 : nat) (_16377 : nat) : (term81 _16374 _16376 _16375 _16377) = (term82 _16374 _16376 _16375 _16377).
Proof. exact (MK_COMB (@lem1008712) (@lem1008711 _16374 _16376 _16375 _16377)). Qed.
Lemma lem1008714 (_16374 : nat) (_16375 : nat) (_16376 : nat) (_16377 : nat) : ((Nat.pow _16374 _16375) = (Nat.pow _16376 _16377)) = ((Nat.pow _16374 _16375) = (Nat.pow _16376 _16377)).
Proof. exact (eq_refl ((Nat.pow _16374 _16375) = (Nat.pow _16376 _16377))). Qed.
Lemma lem1008715 (_16374 : nat) (_16375 : nat) (_16376 : nat) (_16377 : nat) : (term70 _16374 _16375 _16376 _16377) = (term83 _16374 _16375 _16376 _16377).
Proof. exact (MK_COMB (@lem1008713 _16374 _16376 _16375 _16377) (@lem1008714 _16374 _16375 _16376 _16377)). Qed.
Lemma lem1008716 (_16374 : nat) (_16375 : nat) (_16376 : nat) (_16377 : nat) : (term66 _16374 _16376 _16375 _16377) = (term83 _16374 _16375 _16376 _16377).
Proof. exact (TRANS (@lem1008698 _16374 _16375 _16376 _16377) (@lem1008715 _16374 _16375 _16376 _16377)). Qed.
Lemma lem1008718 (m : nat) (h1 : term11) : term84 m.
Proof. exact (conj (@lem1008597 m h1) (@lem1008605)). Qed.
Lemma lem1008720 (_16374 : nat) (_16375 : nat) (_16376 : nat) (_16377 : nat) : term83 _16374 _16375 _16376 _16377.
Proof. exact (EQ_MP (@lem1008716 _16374 _16375 _16376 _16377) (@lem1008695 _16374 _16376 _16375 _16377)). Qed.
Lemma lem1008721 (m : nat) : term85 m.
Proof. exact (@lem1008720 (NUMERAL m) term58 m term58). Qed.
Lemma lem1008724 (m : nat) (h1 : term11) : (term53 m) = (term1 m).
Proof. exact (@lem1008721 m (@lem1008718 m h1)). Qed.
Lemma lem1008725 (m : nat) (h1 : term11) : term86 m.
Proof. exact (fun h0 : term87 m => @lem1008724 m h1). Qed.
Lemma lem1008727 (p : Prop) : (term52 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1008728 (m : nat) : (term86 m) = ((term53 m) = (term1 m)).
Proof. exact (@lem1008727 ((term53 m) = (term1 m))). Qed.
Lemma lem1008729 (m : nat) (h1 : term11) : (term53 m) = (term1 m).
Proof. exact (EQ_MP (@lem1008728 m) (@lem1008725 m h1)). Qed.
Lemma lem1008747 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1008748 (y : nat) (x : nat) (z : nat) : (term88 x y z) = (term89 y x z).
Proof. exact (@lem1008747 (y = z) (term62 x z)). Qed.
Lemma lem1008758 (x : nat) (y : nat) : (term63 x y) = (term63 x y).
Proof. exact (eq_refl (term63 x y)). Qed.
Lemma lem1008759 (y : nat) (x : nat) (z : nat) : (term48 x y z) = (term90 y x z).
Proof. exact (MK_COMB (@lem1008758 x y) (@lem1008748 y x z)). Qed.
Lemma lem1008763 (q : Prop) (p : Prop) (r : Prop) : (term65 p q r) = (term65 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1008764 (y : nat) (x : nat) (z : nat) : (term90 y x z) = (term91 y x z).
Proof. exact (@lem1008763 (y = z) (term62 x y) (term62 x z)). Qed.
Lemma lem1008786 (y : nat) (x : nat) (z : nat) : (term48 x y z) = (term91 y x z).
Proof. exact (TRANS (@lem1008759 y x z) (@lem1008764 y x z)). Qed.
Lemma lem1008787 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1008788 (y : nat) (x : nat) (z : nat) : (term92 x y z) = (term93 y x z).
Proof. exact (MK_COMB (@lem1008787) (@lem1008786 y x z)). Qed.
Lemma lem1008810 (y : nat) (x : nat) (z : nat) : (term91 y x z) = (term91 y x z).
Proof. exact (eq_refl (term91 y x z)). Qed.
Lemma lem1008811 (y : nat) (x : nat) (z : nat) : ((term48 x y z) = (term91 y x z)) = ((term91 y x z) = (term91 y x z)).
Proof. exact (MK_COMB (@lem1008788 y x z) (@lem1008810 y x z)). Qed.
Lemma lem1008813 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1008814 (x : Prop) : (x = x) = True.
Proof. exact (@lem1008813 Prop x). Qed.
Lemma lem1008815 (y : nat) (x : nat) (z : nat) : ((term91 y x z) = (term91 y x z)) = True.
Proof. exact (@lem1008814 (term91 y x z)). Qed.
Lemma lem1008816 (y : nat) (x : nat) (z : nat) : ((term48 x y z) = (term91 y x z)) = True.
Proof. exact (TRANS (@lem1008811 y x z) (@lem1008815 y x z)). Qed.
Lemma lem1008817 (y : nat) (x : nat) (z : nat) : True = ((term48 x y z) = (term91 y x z)).
Proof. exact (SYM (@lem1008816 y x z)). Qed.
Lemma lem1008818 (y : nat) (x : nat) (z : nat) : (term48 x y z) = (term91 y x z).
Proof. exact (EQ_MP (@lem1008817 y x z) (@lem0)). Qed.
Lemma lem1008819 (y : nat) (x : nat) (z : nat) : term91 y x z.
Proof. exact (EQ_MP (@lem1008818 y x z) (@lem1008574 x y z)). Qed.
Lemma lem1008821 (b : Prop) (a : Prop) : (a \/ b) = (term69 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1008822 (x : nat) (y : nat) (z : nat) : (term91 y x z) = (term94 x y z).
Proof. exact (@lem1008821 (term95 y x z) (y = z)). Qed.
Lemma lem1008824 (a : Prop) (b : Prop) : (term72 a b) = (term73 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1008825 (y : nat) (x : nat) (z : nat) : (term96 y x z) = (term97 y x z).
Proof. exact (@lem1008824 (term62 x y) (term62 x z)). Qed.
Lemma lem1008827 (a : Prop) : (term76 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1008828 (x : nat) (y : nat) : (term77 x y) = (x = y).
Proof. exact (@lem1008827 (x = y)). Qed.
Lemma lem1008829 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1008830 (x : nat) (y : nat) : (term78 x y) = (term79 x y).
Proof. exact (MK_COMB (@lem1008829) (@lem1008828 x y)). Qed.
Lemma lem1008832 (a : Prop) : (term76 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1008833 (x : nat) (z : nat) : (term77 x z) = (x = z).
Proof. exact (@lem1008832 (x = z)). Qed.
Lemma lem1008834 (y : nat) (x : nat) (z : nat) : (term97 y x z) = (term98 y x z).
Proof. exact (MK_COMB (@lem1008830 x y) (@lem1008833 x z)). Qed.
Lemma lem1008835 (y : nat) (x : nat) (z : nat) : (term96 y x z) = (term98 y x z).
Proof. exact (TRANS (@lem1008825 y x z) (@lem1008834 y x z)). Qed.
Lemma lem1008836 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1008837 (y : nat) (x : nat) (z : nat) : (term99 y x z) = (term100 y x z).
Proof. exact (MK_COMB (@lem1008836) (@lem1008835 y x z)). Qed.
Lemma lem1008838 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1008839 (x : nat) (y : nat) (z : nat) : (term94 x y z) = (term101 x y z).
Proof. exact (MK_COMB (@lem1008837 y x z) (@lem1008838 y z)). Qed.
Lemma lem1008840 (x : nat) (y : nat) (z : nat) : (term91 y x z) = (term101 x y z).
Proof. exact (TRANS (@lem1008822 x y z) (@lem1008839 x y z)). Qed.
Lemma lem1008842 (m : nat) (h1 : term11) (h2 : term27) : term102 m.
Proof. exact (conj (@lem1008589 m h2) (@lem1008729 m h1)). Qed.
Lemma lem1008844 (x : nat) (y : nat) (z : nat) : term101 x y z.
Proof. exact (EQ_MP (@lem1008840 x y z) (@lem1008819 y x z)). Qed.
Lemma lem1008845 (m : nat) : term103 m.
Proof. exact (@lem1008844 (term53 m) (term2 m) (term1 m)). Qed.
Lemma lem1008848 (m : nat) (h1 : term11) (h2 : term27) : (term2 m) = (term1 m).
Proof. exact (@lem1008845 m (@lem1008842 m h1 h2)). Qed.
Lemma lem1008849 (m : nat) (h1 : term11) (h2 : term27) : term104 m.
Proof. exact (fun h0 : term105 m => @lem1008848 m h1 h2). Qed.
Lemma lem1008851 (p : Prop) : (term52 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1008852 (m : nat) : (term104 m) = ((term2 m) = (term1 m)).
Proof. exact (@lem1008851 ((term2 m) = (term1 m))). Qed.
Lemma lem1008853 (m : nat) (h1 : term11) (h2 : term27) : (term2 m) = (term1 m).
Proof. exact (EQ_MP (@lem1008852 m) (@lem1008849 m h1 h2)). Qed.
Lemma lem1008854 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term30 m p) : term122 p m.
Proof. exact (conj (@lem1008581 m p h3) (@lem1008853 m h1 h2)). Qed.
Lemma lem1008856 (x : nat) (y : nat) (z : nat) : term101 x y z.
Proof. exact (EQ_MP (@lem1008840 x y z) (@lem1008819 y x z)). Qed.
Lemma lem1008857 (p : nat) (m : nat) : term123 p m.
Proof. exact (@lem1008856 (term2 m) (NUMERAL p) (term1 m)). Qed.
Lemma lem1008860 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term30 m p) : (NUMERAL p) = (term1 m).
Proof. exact (@lem1008857 p m (@lem1008854 m p h1 h2 h3)). Qed.
Lemma lem1008861 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term30 m p) : term124 p m.
Proof. exact (fun h0 : term125 p m => @lem1008860 m p h1 h2 h3). Qed.
Lemma lem1008863 (p : Prop) : (term52 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1008864 (p : nat) (m : nat) : (term124 p m) = ((NUMERAL p) = (term1 m)).
Proof. exact (@lem1008863 ((NUMERAL p) = (term1 m))). Qed.
Lemma lem1008865 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term30 m p) : (NUMERAL p) = (term1 m).
Proof. exact (EQ_MP (@lem1008864 p m) (@lem1008861 m p h1 h2 h3)). Qed.
Lemma lem1008867 (_16345 : nat) (h1 : term11) : (NUMERAL _16345) = _16345.
Proof. exact (EQ_MP (@lem1008021 _16345) (@lem1008020 _16345 h1)). Qed.
Lemma lem1008868 (p : nat) (h1 : term11) : (NUMERAL p) = p.
Proof. exact (@lem1008867 p h1). Qed.
Lemma lem1008869 (p : nat) (h1 : term11) : term56 p.
Proof. exact (fun h0 : term57 p => @lem1008868 p h1). Qed.
Lemma lem1008871 (p : Prop) : (term52 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1008872 (p : nat) : (term56 p) = ((NUMERAL p) = p).
Proof. exact (@lem1008871 ((NUMERAL p) = p)). Qed.
Lemma lem1008873 (p : nat) (h1 : term11) : (NUMERAL p) = p.
Proof. exact (EQ_MP (@lem1008872 p) (@lem1008869 p h1)). Qed.
Lemma lem1008874 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term30 m p) : term126 m p.
Proof. exact (conj (@lem1008865 m p h1 h2 h3) (@lem1008873 p h1)). Qed.
Lemma lem1008876 (x : nat) (y : nat) (z : nat) : term101 x y z.
Proof. exact (EQ_MP (@lem1008840 x y z) (@lem1008819 y x z)). Qed.
Lemma lem1008877 (m : nat) (p : nat) : term127 m p.
Proof. exact (@lem1008876 (NUMERAL p) (term1 m) p). Qed.
Lemma lem1008880 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term30 m p) : (term1 m) = p.
Proof. exact (@lem1008877 m p (@lem1008874 m p h1 h2 h3)). Qed.
Lemma lem1008881 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term30 m p) : term128 m p.
Proof. exact (fun h0 : term34 m p => @lem1008880 m p h1 h2 h3). Qed.
Lemma lem1008883 (p : Prop) : (term52 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1008884 (m : nat) (p : nat) : (term128 m p) = ((term1 m) = p).
Proof. exact (@lem1008883 ((term1 m) = p)). Qed.
Lemma lem1008885 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term30 m p) : (term1 m) = p.
Proof. exact (EQ_MP (@lem1008884 m p) (@lem1008881 m p h1 h2 h3)). Qed.
Lemma lem1008888 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1008890 (m : nat) (p : nat) : (term34 m p) = (term129 m p).
Proof. exact (@lem1008888 ((term1 m) = p)). Qed.
Lemma lem1008893 (m : nat) (p : nat) (h1 : term30 m p) : term129 m p.
Proof. exact (EQ_MP (@lem1008890 m p) (@lem1008036 m p h1)). Qed.
Lemma lem1008896 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term30 m p) : False.
Proof. exact (@lem1008893 m p h3 (@lem1008885 m p h1 h2 h3)). Qed.
Lemma lem1008897 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term30 m p) : term120.
Proof. exact (fun h0 : ~ False => @lem1008896 m p h1 h2 h3). Qed.
Lemma lem1008899 (p : Prop) : (term52 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1008900 : term120 = False.
Proof. exact (@lem1008899 False). Qed.
Lemma lem1008901 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term30 m p) : False.
Proof. exact (EQ_MP (@lem1008900) (@lem1008897 m p h1 h2 h3)). Qed.
Lemma lem1008902 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term29 m p) : False.
Proof. exact (EQ_MP (@lem1008517) (@lem1008514 m p h1 h2 h3)). Qed.
Lemma lem1008903 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term30 m p) : term11 = False.
Proof. exact (prop_ext (fun h4 : term11 => @lem1008901 m p h1 h2 h3) (fun h4 : False => @lem1008002 h1)). Qed.
Lemma lem1008904 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term30 m p) : False.
Proof. exact (EQ_MP (@lem1008903 m p h1 h2 h3) (@lem1008002 h1)). Qed.
Lemma lem1008905 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term30 m p) : term27 = False.
Proof. exact (prop_ext (fun h4 : term27 => @lem1008904 m p h1 h2 h3) (fun h4 : False => @lem1007995 h2)). Qed.
Lemma lem1008906 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term30 m p) : False.
Proof. exact (EQ_MP (@lem1008905 m p h1 h2 h3) (@lem1007995 h2)). Qed.
Lemma lem1008907 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term29 m p) : term11 = False.
Proof. exact (prop_ext (fun h4 : term11 => @lem1008902 m p h1 h2 h3) (fun h4 : False => @lem1007980 h1)). Qed.
Lemma lem1008908 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term29 m p) : False.
Proof. exact (EQ_MP (@lem1008907 m p h1 h2 h3) (@lem1007980 h1)). Qed.
Lemma lem1008909 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term29 m p) : term27 = False.
Proof. exact (prop_ext (fun h4 : term27 => @lem1008908 m p h1 h2 h3) (fun h4 : False => @lem1007973 h2)). Qed.
Lemma lem1008910 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term29 m p) : False.
Proof. exact (EQ_MP (@lem1008909 m p h1 h2 h3) (@lem1007973 h2)). Qed.
Lemma lem1008911 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term4 m p) : False.
Proof. exact (or_elim (@lem1007926 m p h3) (fun h0 : term29 m p => @lem1008910 m p h1 h2 h0) (fun h0 : term30 m p => @lem1008906 m p h1 h2 h0)). Qed.
Lemma lem1008912 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term4 m p) : term11 = False.
Proof. exact (prop_ext (fun h4 : term11 => @lem1008911 m p h1 h2 h3) (fun h4 : False => @lem1007960 h1)). Qed.
Lemma lem1008913 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term4 m p) : False.
Proof. exact (EQ_MP (@lem1008912 m p h1 h2 h3) (@lem1007960 h1)). Qed.
Lemma lem1008914 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term4 m p) : term27 = False.
Proof. exact (prop_ext (fun h4 : term27 => @lem1008913 m p h1 h2 h3) (fun h4 : False => @lem1007949 h2)). Qed.
Lemma lem1008915 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term4 m p) : False.
Proof. exact (EQ_MP (@lem1008914 m p h1 h2 h3) (@lem1007949 h2)). Qed.
Lemma lem1008916 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term4 m p) : term11 = False.
Proof. exact (prop_ext (fun h4 : term11 => @lem1008915 m p h1 h2 h3) (fun h4 : False => @lem1007852 h1)). Qed.
Lemma lem1008917 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term4 m p) : False.
Proof. exact (EQ_MP (@lem1008916 m p h1 h2 h3) (@lem1007852 h1)). Qed.
Lemma lem1008918 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term4 m p) : term27 = False.
Proof. exact (prop_ext (fun h4 : term27 => @lem1008917 m p h1 h2 h3) (fun h4 : False => @lem1007839 h2)). Qed.
Lemma lem1008919 (m : nat) (p : nat) (h1 : term11) (h2 : term27) (h3 : term4 m p) : False.
Proof. exact (EQ_MP (@lem1008918 m p h1 h2 h3) (@lem1007839 h2)). Qed.
Lemma lem1008920 (m : nat) (p : nat) (h1 : term27) (h2 : term4 m p) : term9.
Proof. exact (fun h0 : term11 => @lem1008919 m p h0 h1 h2). Qed.
Lemma lem1008921 : term9 = term10.
Proof. exact (@lem69 term11). Qed.
Lemma lem1008922 (m : nat) (p : nat) (h1 : term27) (h2 : term4 m p) : term10.
Proof. exact (EQ_MP (@lem1008921) (@lem1008920 m p h1 h2)). Qed.
Lemma lem1008923 (m : nat) (p : nat) (h1 : term4 m p) : term14.
Proof. exact (fun h0 : term27 => @lem1008922 m p h0 h1). Qed.
Lemma lem1008924 (m : nat) (p : nat) : term16 m p.
Proof. exact (fun h0 : term4 m p => @lem1008923 m p h0). Qed.
Lemma lem1008929 (p : nat) : term20 p.
Proof. exact (fun m : nat => @lem1008924 m p). Qed.
Lemma lem1008934 : term24.
Proof. exact (fun p : nat => @lem1008929 p). Qed.
Lemma lem1008935 : term23.
Proof. exact (EQ_MP (@lem1007803) (@lem1008934)). Qed.
Lemma lem1008936 (p : nat) : term130 p.
Proof. exact (@lem1008935 p). Qed.
Lemma lem1008937 (p : nat) : (term130 p) = (term19 p).
Proof. exact (eq_refl (term130 p)). Qed.
Lemma lem1008938 (p : nat) : term19 p.
Proof. exact (EQ_MP (@lem1008937 p) (@lem1008936 p)). Qed.
Lemma lem1008939 (p : nat) (m : nat) : term131 p m.
Proof. exact (@lem1008938 p m). Qed.
Lemma lem1008940 (m : nat) (p : nat) : (term131 p m) = (term5 m p).
Proof. exact (eq_refl (term131 p m)). Qed.
Lemma lem1008941 (m : nat) (p : nat) : term5 m p.
Proof. exact (EQ_MP (@lem1008940 m p) (@lem1008939 p m)). Qed.
Lemma lem1008943 (m : nat) (p : nat) : term5 m p.
Proof. exact (@lem1007693 m p (@lem1008941 m p)). Qed.
Lemma lem1008944 (m : nat) (p : nat) (h1 : term4 m p) : term13.
Proof. exact (@lem1008943 m p (@lem1007678 m p h1)). Qed.
Lemma lem1008945 (m : nat) (p : nat) (h1 : term4 m p) : term9.
Proof. exact (@lem1008944 m p h1 (@lem88196)). Qed.
Lemma lem1008946 (m : nat) (p : nat) (h1 : term4 m p) : False.
Proof. exact (@lem1008945 m p h1 (@lem75543)). Qed.
Lemma lem1008947 (m : nat) (p : nat) (h1 : term4 m p) : (term4 m p) = False.
Proof. exact (prop_ext (fun h2 : term4 m p => @lem1008946 m p h1) (fun h2 : False => @lem1007678 m p h1)). Qed.
Lemma lem1008948 (m : nat) (p : nat) (h1 : term4 m p) : False.
Proof. exact (EQ_MP (@lem1008947 m p h1) (@lem1007678 m p h1)). Qed.
Lemma lem1008949 (m : nat) (p : nat) : term3 m p.
Proof. exact (fun h0 : term4 m p => @lem1008948 m p h0). Qed.
Lemma lem1008952 (m : nat) (p : nat) : ((term1 m) = p) = ((term2 m) = (NUMERAL p)).
Proof. exact (EQ_MP (@lem1007677 m p) (@lem1008949 m p)). Qed.
