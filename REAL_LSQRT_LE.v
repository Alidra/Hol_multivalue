Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LSQRT_LE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_POW_LE2_spec.
Require Import SQRT_POS_LE_spec.
Require Import SQRT_POW_2_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339577_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
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
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem1966799 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1966800 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1966801 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1966800 t1) (@lem1966799 t1)). Qed.
Lemma lem1966802 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1966801 t1 t2). Qed.
Lemma lem1966803 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1966804 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1966803 t1 t2) (@lem1966802 t1 t2)). Qed.
Lemma lem1966805 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1966804 t1 t2 t3). Qed.
Lemma lem1966806 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1966807 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1966806 t1 t2 t3) (@lem1966805 t1 t2 t3)). Qed.
Lemma lem1966808 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1966807 t1 t2 t3)). Qed.
Lemma lem1966810 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1966811 : term8 = term9.
Proof. exact (@lem1966810 term8). Qed.
Lemma lem1966812 : term9 = term8.
Proof. exact (SYM (@lem1966811)). Qed.
Lemma lem1966813 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1966816 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1966817 : term12.
Proof. exact (fun h0 : term11 => @lem1966816 h0). Qed.
Lemma lem1966818 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1966819 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1966820 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1966818 h2 (@lem1966819 h1)). Qed.
Lemma lem1966821 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem1966820 h1 h0). Qed.
Lemma lem1966822 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1966823 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1966821 h1 (@lem1966822 h2)). Qed.
Lemma lem1966824 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem1966823 h0 h1). Qed.
Lemma lem1966825 : term14.
Proof. exact (fun h0 : term12 => @lem1966824 h0). Qed.
Lemma lem1966828 : term12.
Proof. exact (@lem1966825 (@lem1966817)). Qed.
Lemma lem1966878 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1966879 : term15 = term16.
Proof. exact (@lem1966878 term17). Qed.
Lemma lem1966896 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1966897 : term19 = term20.
Proof. exact (MK_COMB (@lem1966896) (@lem1966879)). Qed.
Lemma lem1966900 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1966901 : term22 = term23.
Proof. exact (MK_COMB (@lem1966900) (@lem1966897)). Qed.
Lemma lem1966904 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1966905 : term25 = term26.
Proof. exact (MK_COMB (@lem1966904) (@lem1966901)). Qed.
Lemma lem1966908 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem1966915 : term11 = term28.
Proof. exact (MK_COMB (@lem1966908) (@lem1966905)). Qed.
Lemma lem1966924 (x : real) (y : real) (n : nat) : (term29 x y n) = (term29 x y n).
Proof. exact (eq_refl (term29 x y n)). Qed.
Lemma lem1966925 (x : real) (n : nat) : (term30 x n) = (term30 x n).
Proof. exact (fun_ext (fun y : real => @lem1966924 x y n)). Qed.
Lemma lem1966926 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1966927 (x : real) (n : nat) : (term31 x n) = (term31 x n).
Proof. exact (MK_COMB (@lem1966926) (@lem1966925 x n)). Qed.
Lemma lem1966928 (n : nat) : (term32 n) = (term32 n).
Proof. exact (fun_ext (fun x : real => @lem1966927 x n)). Qed.
Lemma lem1966929 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1966930 (n : nat) : (term33 n) = (term33 n).
Proof. exact (MK_COMB (@lem1966929) (@lem1966928 n)). Qed.
Lemma lem1966931 : term34 = term34.
Proof. exact (fun_ext (fun n : nat => @lem1966930 n)). Qed.
Lemma lem1966932 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1966933 : term17 = term17.
Proof. exact (MK_COMB (@lem1966932) (@lem1966931)). Qed.
Lemma lem1966934 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1966935 : term16 = term16.
Proof. exact (MK_COMB (@lem1966934) (@lem1966933)). Qed.
Lemma lem1966940 (x : real) : (term35 x) = (term35 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem1966941 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem1966940 x)). Qed.
Lemma lem1966942 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1966943 : term37 = term37.
Proof. exact (MK_COMB (@lem1966942) (@lem1966941)). Qed.
Lemma lem1966944 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1966945 : term18 = term18.
Proof. exact (MK_COMB (@lem1966944) (@lem1966943)). Qed.
Lemma lem1966946 : term20 = term20.
Proof. exact (MK_COMB (@lem1966945) (@lem1966935)). Qed.
Lemma lem1966955 (y : real) (x : real) (z : real) : (term38 y x z) = (term38 y x z).
Proof. exact (eq_refl (term38 y x z)). Qed.
Lemma lem1966956 (y : real) (x : real) : (term39 y x) = (term39 y x).
Proof. exact (fun_ext (fun z : real => @lem1966955 y x z)). Qed.
Lemma lem1966957 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1966958 (y : real) (x : real) : (term40 y x) = (term40 y x).
Proof. exact (MK_COMB (@lem1966957) (@lem1966956 y x)). Qed.
Lemma lem1966959 (x : real) : (term41 x) = (term41 x).
Proof. exact (fun_ext (fun y : real => @lem1966958 y x)). Qed.
Lemma lem1966960 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1966961 (x : real) : (term42 x) = (term42 x).
Proof. exact (MK_COMB (@lem1966960) (@lem1966959 x)). Qed.
Lemma lem1966962 : term43 = term43.
Proof. exact (fun_ext (fun x : real => @lem1966961 x)). Qed.
Lemma lem1966963 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1966964 : term44 = term44.
Proof. exact (MK_COMB (@lem1966963) (@lem1966962)). Qed.
Lemma lem1966965 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1966966 : term21 = term21.
Proof. exact (MK_COMB (@lem1966965) (@lem1966964)). Qed.
Lemma lem1966967 : term23 = term23.
Proof. exact (MK_COMB (@lem1966966) (@lem1966946)). Qed.
Lemma lem1966972 (x : real) : (term45 x) = (term45 x).
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem1966973 : term46 = term46.
Proof. exact (fun_ext (fun x : real => @lem1966972 x)). Qed.
Lemma lem1966974 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1966975 : term47 = term47.
Proof. exact (MK_COMB (@lem1966974) (@lem1966973)). Qed.
Lemma lem1966976 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1966977 : term24 = term24.
Proof. exact (MK_COMB (@lem1966976) (@lem1966975)). Qed.
Lemma lem1966978 : term26 = term26.
Proof. exact (MK_COMB (@lem1966977) (@lem1966967)). Qed.
Lemma lem1966987 (x : real) (y : real) : (term48 x y) = (term48 x y).
Proof. exact (eq_refl (term48 x y)). Qed.
Lemma lem1966988 (x : real) : (term49 x) = (term49 x).
Proof. exact (fun_ext (fun y : real => @lem1966987 x y)). Qed.
Lemma lem1966989 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1966990 (x : real) : (term50 x) = (term50 x).
Proof. exact (MK_COMB (@lem1966989) (@lem1966988 x)). Qed.
Lemma lem1966991 : term51 = term51.
Proof. exact (fun_ext (fun x : real => @lem1966990 x)). Qed.
Lemma lem1966992 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1966993 : term8 = term8.
Proof. exact (MK_COMB (@lem1966992) (@lem1966991)). Qed.
Lemma lem1966994 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1966995 : term10 = term10.
Proof. exact (MK_COMB (@lem1966994) (@lem1966993)). Qed.
Lemma lem1966996 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1966997 : term27 = term27.
Proof. exact (MK_COMB (@lem1966996) (@lem1966995)). Qed.
Lemma lem1966998 : term28 = term28.
Proof. exact (MK_COMB (@lem1966997) (@lem1966978)). Qed.
Lemma lem1967085 : term11 = term28.
Proof. exact (TRANS (@lem1966915) (@lem1966998)). Qed.
Lemma lem1967086 : term28 = term11.
Proof. exact (SYM (@lem1967085)). Qed.
Lemma lem1967087 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1967088 (h1 : term47) : term47.
Proof. exact (h1). Qed.
Lemma lem1967090 (h1 : term37) : term37.
Proof. exact (h1). Qed.
Lemma lem1967091 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1967102 (x : real) (y : real) : (term52 x y) = (term53 x y).
Proof. exact (@lem17362 (term54 x y) (term55 x y)). Qed.
Lemma lem1967103 (P : real -> Prop) : (term56 P) = (term57 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1967104 (x : real) : (term58 x) = (term59 x).
Proof. exact (@lem1967103 (term49 x)). Qed.
Lemma lem1967105 (x : real) (y : real) : (term60 x y) = (term48 x y).
Proof. exact (eq_refl (term60 x y)). Qed.
Lemma lem1967106 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1967107 (x : real) (y : real) : (term61 x y) = (term52 x y).
Proof. exact (MK_COMB (@lem1967106) (@lem1967105 x y)). Qed.
Lemma lem1967108 (x : real) (y : real) : (term61 x y) = (term53 x y).
Proof. exact (TRANS (@lem1967107 x y) (@lem1967102 x y)). Qed.
Lemma lem1967109 (x : real) : (term62 x) = (term63 x).
Proof. exact (fun_ext (fun y : real => @lem1967108 x y)). Qed.
Lemma lem1967110 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1967111 (x : real) : (term59 x) = (term64 x).
Proof. exact (MK_COMB (@lem1967110) (@lem1967109 x)). Qed.
Lemma lem1967112 (x : real) : (term58 x) = (term64 x).
Proof. exact (TRANS (@lem1967104 x) (@lem1967111 x)). Qed.
Lemma lem1967113 (P : real -> Prop) : (term56 P) = (term57 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1967114 : term10 = term65.
Proof. exact (@lem1967113 term51). Qed.
Lemma lem1967115 (x : real) : (term66 x) = (term50 x).
Proof. exact (eq_refl (term66 x)). Qed.
Lemma lem1967116 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1967117 (x : real) : (term67 x) = (term58 x).
Proof. exact (MK_COMB (@lem1967116) (@lem1967115 x)). Qed.
Lemma lem1967118 (x : real) : (term67 x) = (term64 x).
Proof. exact (TRANS (@lem1967117 x) (@lem1967112 x)). Qed.
Lemma lem1967119 : term68 = term69.
Proof. exact (fun_ext (fun x : real => @lem1967118 x)). Qed.
Lemma lem1967120 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1967121 : term65 = term70.
Proof. exact (MK_COMB (@lem1967120) (@lem1967119)). Qed.
Lemma lem1967178 : term10 = term70.
Proof. exact (TRANS (@lem1967114) (@lem1967121)). Qed.
Lemma lem1967179 (h1 : term10) : term70.
Proof. exact (EQ_MP (@lem1967178) (@lem1967087 h1)). Qed.
Lemma lem1967186 (x : real) : (term45 x) = (term71 x).
Proof. exact (@lem17265 (term72 x) ((term73 x) = x)). Qed.
Lemma lem1967187 : term46 = term74.
Proof. exact (fun_ext (fun x : real => @lem1967186 x)). Qed.
Lemma lem1967188 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1967241 : term47 = term75.
Proof. exact (MK_COMB (@lem1967188) (@lem1967187)). Qed.
Lemma lem1967242 (h1 : term47) : term75.
Proof. exact (EQ_MP (@lem1967241) (@lem1967088 h1)). Qed.
Lemma lem1967332 (x : real) : (term35 x) = (term76 x).
Proof. exact (@lem17265 (term72 x) (term77 x)). Qed.
Lemma lem1967333 : term36 = term78.
Proof. exact (fun_ext (fun x : real => @lem1967332 x)). Qed.
Lemma lem1967334 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1967387 : term37 = term79.
Proof. exact (MK_COMB (@lem1967334) (@lem1967333)). Qed.
Lemma lem1967388 (h1 : term37) : term79.
Proof. exact (EQ_MP (@lem1967387) (@lem1967090 h1)). Qed.
Lemma lem1967395 (x : real) (y : real) : (term80 x y) = (term81 x y).
Proof. exact (@lem17045 (term72 x) (real_le x y)). Qed.
Lemma lem1967396 (x : real) (y : real) (n : nat) : (term82 x y n) = (term82 x y n).
Proof. exact (eq_refl (term82 x y n)). Qed.
Lemma lem1967397 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1967398 (x : real) (y : real) : (term83 x y) = (term84 x y).
Proof. exact (MK_COMB (@lem1967397) (@lem1967395 x y)). Qed.
Lemma lem1967399 (x : real) (y : real) (n : nat) : (term85 x y n) = (term86 x y n).
Proof. exact (MK_COMB (@lem1967398 x y) (@lem1967396 x y n)). Qed.
Lemma lem1967400 (x : real) (y : real) (n : nat) : (term29 x y n) = (term85 x y n).
Proof. exact (@lem17265 (term87 x y) (term82 x y n)). Qed.
Lemma lem1967401 (x : real) (y : real) (n : nat) : (term29 x y n) = (term86 x y n).
Proof. exact (TRANS (@lem1967400 x y n) (@lem1967399 x y n)). Qed.
Lemma lem1967402 (x : real) (n : nat) : (term30 x n) = (term88 x n).
Proof. exact (fun_ext (fun y : real => @lem1967401 x y n)). Qed.
Lemma lem1967403 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1967404 (x : real) (n : nat) : (term31 x n) = (term89 x n).
Proof. exact (MK_COMB (@lem1967403) (@lem1967402 x n)). Qed.
Lemma lem1967405 (n : nat) : (term32 n) = (term90 n).
Proof. exact (fun_ext (fun x : real => @lem1967404 x n)). Qed.
Lemma lem1967406 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1967407 (n : nat) : (term33 n) = (term91 n).
Proof. exact (MK_COMB (@lem1967406) (@lem1967405 n)). Qed.
Lemma lem1967408 : term34 = term92.
Proof. exact (fun_ext (fun n : nat => @lem1967407 n)). Qed.
Lemma lem1967409 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1967470 : term17 = term93.
Proof. exact (MK_COMB (@lem1967409) (@lem1967408)). Qed.
Lemma lem1967471 (h1 : term17) : term93.
Proof. exact (EQ_MP (@lem1967470) (@lem1967091 h1)). Qed.
Lemma lem1967472 (x : real) (h1 : term64 x) : term64 x.
Proof. exact (h1). Qed.
Lemma lem1967504 (x : real) : (term71 x) = (term71 x).
Proof. exact (eq_refl (term71 x)). Qed.
Lemma lem1967505 : term74 = term74.
Proof. exact (fun_ext (fun x : real => @lem1967504 x)). Qed.
Lemma lem1967506 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1967507 : term75 = term75.
Proof. exact (MK_COMB (@lem1967506) (@lem1967505)). Qed.
Lemma lem1967508 (h1 : term47) : term75.
Proof. exact (EQ_MP (@lem1967507) (@lem1967242 h1)). Qed.
Lemma lem1967568 (x : real) : (term76 x) = (term76 x).
Proof. exact (eq_refl (term76 x)). Qed.
Lemma lem1967569 : term78 = term78.
Proof. exact (fun_ext (fun x : real => @lem1967568 x)). Qed.
Lemma lem1967570 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1967571 : term79 = term79.
Proof. exact (MK_COMB (@lem1967570) (@lem1967569)). Qed.
Lemma lem1967572 (h1 : term37) : term79.
Proof. exact (EQ_MP (@lem1967571) (@lem1967388 h1)). Qed.
Lemma lem1967609 (x : real) (y : real) (n : nat) : (term86 x y n) = (term86 x y n).
Proof. exact (eq_refl (term86 x y n)). Qed.
Lemma lem1967610 (x : real) (n : nat) : (term88 x n) = (term88 x n).
Proof. exact (fun_ext (fun y : real => @lem1967609 x y n)). Qed.
Lemma lem1967611 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1967612 (x : real) (n : nat) : (term89 x n) = (term89 x n).
Proof. exact (MK_COMB (@lem1967611) (@lem1967610 x n)). Qed.
Lemma lem1967613 (n : nat) : (term90 n) = (term90 n).
Proof. exact (fun_ext (fun x : real => @lem1967612 x n)). Qed.
Lemma lem1967614 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1967615 (n : nat) : (term91 n) = (term91 n).
Proof. exact (MK_COMB (@lem1967614) (@lem1967613 n)). Qed.
Lemma lem1967616 : term92 = term92.
Proof. exact (fun_ext (fun n : nat => @lem1967615 n)). Qed.
Lemma lem1967617 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1967618 : term93 = term93.
Proof. exact (MK_COMB (@lem1967617) (@lem1967616)). Qed.
Lemma lem1967619 (h1 : term17) : term93.
Proof. exact (EQ_MP (@lem1967618) (@lem1967471 h1)). Qed.
Lemma lem1967659 (x : real) (y : real) (h1 : term53 x y) : term53 x y.
Proof. exact (h1). Qed.
Lemma lem1967661 (x : real) (y : real) (h1 : term53 x y) : term54 x y.
Proof. exact (proj1 (@lem1967659 x y h1)). Qed.
Lemma lem1967671 (x : real) : (term71 x) = (term71 x).
Proof. exact (eq_refl (term71 x)). Qed.
Lemma lem1967672 : term74 = term74.
Proof. exact (fun_ext (fun x : real => @lem1967671 x)). Qed.
Lemma lem1967673 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1967675 : term75 = term75.
Proof. exact (MK_COMB (@lem1967673) (@lem1967672)). Qed.
Lemma lem1967676 (h1 : term47) : term75.
Proof. exact (EQ_MP (@lem1967675) (@lem1967508 h1)). Qed.
Lemma lem1967709 (x : real) : (term76 x) = (term76 x).
Proof. exact (eq_refl (term76 x)). Qed.
Lemma lem1967710 : term78 = term78.
Proof. exact (fun_ext (fun x : real => @lem1967709 x)). Qed.
Lemma lem1967711 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1967713 : term79 = term79.
Proof. exact (MK_COMB (@lem1967711) (@lem1967710)). Qed.
Lemma lem1967714 (h1 : term37) : term79.
Proof. exact (EQ_MP (@lem1967713) (@lem1967572 h1)). Qed.
Lemma lem1967728 (x : real) (y : real) (n : nat) : (term86 x y n) = (term86 x y n).
Proof. exact (eq_refl (term86 x y n)). Qed.
Lemma lem1967729 (x : real) (n : nat) : (term88 x n) = (term88 x n).
Proof. exact (fun_ext (fun y : real => @lem1967728 x y n)). Qed.
Lemma lem1967730 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1967731 (x : real) (n : nat) : (term89 x n) = (term89 x n).
Proof. exact (MK_COMB (@lem1967730) (@lem1967729 x n)). Qed.
Lemma lem1967732 (n : nat) : (term90 n) = (term90 n).
Proof. exact (fun_ext (fun x : real => @lem1967731 x n)). Qed.
Lemma lem1967733 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1967734 (n : nat) : (term91 n) = (term91 n).
Proof. exact (MK_COMB (@lem1967733) (@lem1967732 n)). Qed.
Lemma lem1967735 : term92 = term92.
Proof. exact (fun_ext (fun n : nat => @lem1967734 n)). Qed.
Lemma lem1967736 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1967738 : term93 = term93.
Proof. exact (MK_COMB (@lem1967736) (@lem1967735)). Qed.
Lemma lem1967739 (h1 : term17) : term93.
Proof. exact (EQ_MP (@lem1967738) (@lem1967619 h1)). Qed.
Lemma lem1967752 (_27661 : real) (h1 : term47) : term94 _27661.
Proof. exact (@lem1967676 h1 _27661). Qed.
Lemma lem1967753 (_27661 : real) : (term94 _27661) = (term71 _27661).
Proof. exact (eq_refl (term94 _27661)). Qed.
Lemma lem1967764 (_27665 : real) (h1 : term37) : term95 _27665.
Proof. exact (@lem1967714 h1 _27665). Qed.
Lemma lem1967765 (_27665 : real) : (term95 _27665) = (term76 _27665).
Proof. exact (eq_refl (term95 _27665)). Qed.
Lemma lem1967767 (_27666 : nat) (h1 : term17) : term96 _27666.
Proof. exact (@lem1967739 h1 _27666). Qed.
Lemma lem1967768 (_27666 : nat) : (term96 _27666) = (term91 _27666).
Proof. exact (eq_refl (term96 _27666)). Qed.
Lemma lem1967769 (_27666 : nat) (h1 : term17) : term91 _27666.
Proof. exact (EQ_MP (@lem1967768 _27666) (@lem1967767 _27666 h1)). Qed.
Lemma lem1967770 (_27666 : nat) (_27667 : real) (h1 : term17) : term97 _27666 _27667.
Proof. exact (@lem1967769 _27666 h1 _27667). Qed.
Lemma lem1967771 (_27667 : real) (_27666 : nat) : (term97 _27666 _27667) = (term89 _27667 _27666).
Proof. exact (eq_refl (term97 _27666 _27667)). Qed.
Lemma lem1967772 (_27667 : real) (_27666 : nat) (h1 : term17) : term89 _27667 _27666.
Proof. exact (EQ_MP (@lem1967771 _27667 _27666) (@lem1967770 _27666 _27667 h1)). Qed.
Lemma lem1967773 (_27667 : real) (_27666 : nat) (_27668 : real) (h1 : term17) : term98 _27667 _27666 _27668.
Proof. exact (@lem1967772 _27667 _27666 h1 _27668). Qed.
Lemma lem1967774 (_27667 : real) (_27668 : real) (_27666 : nat) : (term98 _27667 _27666 _27668) = (term86 _27667 _27668 _27666).
Proof. exact (eq_refl (term98 _27667 _27666 _27668)). Qed.
Lemma lem1967775 (_27667 : real) (_27668 : real) (_27666 : nat) (h1 : term17) : term86 _27667 _27668 _27666.
Proof. exact (EQ_MP (@lem1967774 _27667 _27668 _27666) (@lem1967773 _27667 _27666 _27668 h1)). Qed.
Lemma lem1967781 (_27661 : real) (h1 : term47) : term71 _27661.
Proof. exact (EQ_MP (@lem1967753 _27661) (@lem1967752 _27661 h1)). Qed.
Lemma lem1967799 (_27665 : real) (h1 : term37) : term76 _27665.
Proof. exact (EQ_MP (@lem1967765 _27665) (@lem1967764 _27665 h1)). Qed.
Lemma lem1967810 (_27667 : real) (_27668 : real) (_27666 : nat) : (term86 _27667 _27668 _27666) = (term99 _27667 _27668 _27666).
Proof. exact (@lem1966808 (term100 _27667) (term101 _27667 _27668) (term82 _27667 _27668 _27666)). Qed.
Lemma lem1967811 (_27667 : real) (_27668 : real) (_27666 : nat) (h1 : term17) : term99 _27667 _27668 _27666.
Proof. exact (EQ_MP (@lem1967810 _27667 _27668 _27666) (@lem1967775 _27667 _27668 _27666 h1)). Qed.
Lemma lem1967813 (x : real) (y : real) (h1 : term53 x y) : term102 x y.
Proof. exact (proj2 (@lem1967659 x y h1)). Qed.
Lemma lem1967818 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1967819 (_27669 : real) (_27671 : real) (h1 : _27669 = _27671) : _27669 = _27671.
Proof. exact (h1). Qed.
Lemma lem1967820 (_27670 : real) (_27672 : real) (h1 : _27670 = _27672) : _27670 = _27672.
Proof. exact (h1). Qed.
Lemma lem1967821 (_27669 : real) (_27671 : real) (h1 : _27669 = _27671) : (real_le _27669) = (real_le _27671).
Proof. exact (MK_COMB (@lem1967818) (@lem1967819 _27669 _27671 h1)). Qed.
Lemma lem1967822 (_27669 : real) (_27671 : real) (_27670 : real) (_27672 : real) (h1 : _27669 = _27671) (h2 : _27670 = _27672) : (real_le _27669 _27670) = (real_le _27671 _27672).
Proof. exact (MK_COMB (@lem1967821 _27669 _27671 h1) (@lem1967820 _27670 _27672 h2)). Qed.
Lemma lem1967824 (b : Prop) (a : Prop) : term103 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1967825 (_27671 : real) (_27672 : real) (_27669 : real) (_27670 : real) : term104 _27671 _27672 _27669 _27670.
Proof. exact (@lem1967824 (real_le _27671 _27672) (real_le _27669 _27670)). Qed.
Lemma lem1967826 (_27669 : real) (_27671 : real) (_27670 : real) (_27672 : real) (h1 : _27669 = _27671) (h2 : _27670 = _27672) : term105 _27671 _27672 _27669 _27670.
Proof. exact (@lem1967825 _27671 _27672 _27669 _27670 (@lem1967822 _27669 _27671 _27670 _27672 h1 h2)). Qed.
Lemma lem1967827 (_27672 : real) (_27670 : real) (_27669 : real) (_27671 : real) (h1 : _27669 = _27671) : term106 _27671 _27672 _27669 _27670.
Proof. exact (fun h0 : _27670 = _27672 => @lem1967826 _27669 _27671 _27670 _27672 h1 h0). Qed.
Lemma lem1967829 (a : Prop) (b : Prop) : (a -> b) = (term107 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1967830 (_27671 : real) (_27672 : real) (_27669 : real) (_27670 : real) : (term106 _27671 _27672 _27669 _27670) = (term108 _27671 _27672 _27669 _27670).
Proof. exact (@lem1967829 (_27670 = _27672) (term105 _27671 _27672 _27669 _27670)). Qed.
Lemma lem1967831 (_27672 : real) (_27670 : real) (_27669 : real) (_27671 : real) (h1 : _27669 = _27671) : term108 _27671 _27672 _27669 _27670.
Proof. exact (EQ_MP (@lem1967830 _27671 _27672 _27669 _27670) (@lem1967827 _27672 _27670 _27669 _27671 h1)). Qed.
Lemma lem1967832 (_27671 : real) (_27672 : real) (_27669 : real) (_27670 : real) : term109 _27671 _27672 _27669 _27670.
Proof. exact (fun h0 : _27669 = _27671 => @lem1967831 _27672 _27670 _27669 _27671 h0). Qed.
Lemma lem1967834 (a : Prop) (b : Prop) : (a -> b) = (term107 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1967835 (_27671 : real) (_27672 : real) (_27669 : real) (_27670 : real) : (term109 _27671 _27672 _27669 _27670) = (term110 _27671 _27672 _27669 _27670).
Proof. exact (@lem1967834 (_27669 = _27671) (term108 _27671 _27672 _27669 _27670)). Qed.
Lemma lem1967836 (_27671 : real) (_27672 : real) (_27669 : real) (_27670 : real) : term110 _27671 _27672 _27669 _27670.
Proof. exact (EQ_MP (@lem1967835 _27671 _27672 _27669 _27670) (@lem1967832 _27671 _27672 _27669 _27670)). Qed.
Lemma lem1967897 (x : real) (y : real) (h1 : term53 x y) : term72 x.
Proof. exact (proj1 (@lem1967661 x y h1)). Qed.
Lemma lem1967898 (x : real) (y : real) (h1 : term53 x y) : term111 x.
Proof. exact (fun h0 : term100 x => @lem1967897 x y h1). Qed.
Lemma lem1967900 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1967901 (x : real) : (term111 x) = (term72 x).
Proof. exact (@lem1967900 (term72 x)). Qed.
Lemma lem1967902 (x : real) (y : real) (h1 : term53 x y) : term72 x.
Proof. exact (EQ_MP (@lem1967901 x) (@lem1967898 x y h1)). Qed.
Lemma lem1967908 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1967909 (_27661 : real) : (term71 _27661) = (term113 _27661).
Proof. exact (@lem1967908 ((term73 _27661) = _27661) (term100 _27661)). Qed.
Lemma lem1967917 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1967918 (_27661 : real) : (term114 _27661) = (term115 _27661).
Proof. exact (MK_COMB (@lem1967917) (@lem1967909 _27661)). Qed.
Lemma lem1967926 (_27661 : real) : (term113 _27661) = (term113 _27661).
Proof. exact (eq_refl (term113 _27661)). Qed.
Lemma lem1967927 (_27661 : real) : ((term71 _27661) = (term113 _27661)) = ((term113 _27661) = (term113 _27661)).
Proof. exact (MK_COMB (@lem1967918 _27661) (@lem1967926 _27661)). Qed.
Lemma lem1967929 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1967930 (x : Prop) : (x = x) = True.
Proof. exact (@lem1967929 Prop x). Qed.
Lemma lem1967931 (_27661 : real) : ((term113 _27661) = (term113 _27661)) = True.
Proof. exact (@lem1967930 (term113 _27661)). Qed.
Lemma lem1967932 (_27661 : real) : ((term71 _27661) = (term113 _27661)) = True.
Proof. exact (TRANS (@lem1967927 _27661) (@lem1967931 _27661)). Qed.
Lemma lem1967933 (_27661 : real) : True = ((term71 _27661) = (term113 _27661)).
Proof. exact (SYM (@lem1967932 _27661)). Qed.
Lemma lem1967934 (_27661 : real) : (term71 _27661) = (term113 _27661).
Proof. exact (EQ_MP (@lem1967933 _27661) (@lem0)). Qed.
Lemma lem1967935 (_27661 : real) (h1 : term47) : term113 _27661.
Proof. exact (EQ_MP (@lem1967934 _27661) (@lem1967781 _27661 h1)). Qed.
Lemma lem1967937 (b : Prop) (a : Prop) : (a \/ b) = (term116 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1967938 (_27661 : real) : (term113 _27661) = (term117 _27661).
Proof. exact (@lem1967937 (term100 _27661) ((term73 _27661) = _27661)). Qed.
Lemma lem1967940 (a : Prop) : (term118 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1967941 (_27661 : real) : (term119 _27661) = (term72 _27661).
Proof. exact (@lem1967940 (term72 _27661)). Qed.
Lemma lem1967942 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1967943 (_27661 : real) : (term120 _27661) = (term121 _27661).
Proof. exact (MK_COMB (@lem1967942) (@lem1967941 _27661)). Qed.
Lemma lem1967944 (_27661 : real) : ((term73 _27661) = _27661) = ((term73 _27661) = _27661).
Proof. exact (eq_refl ((term73 _27661) = _27661)). Qed.
Lemma lem1967945 (_27661 : real) : (term117 _27661) = (term45 _27661).
Proof. exact (MK_COMB (@lem1967943 _27661) (@lem1967944 _27661)). Qed.
Lemma lem1967946 (_27661 : real) : (term113 _27661) = (term45 _27661).
Proof. exact (TRANS (@lem1967938 _27661) (@lem1967945 _27661)). Qed.
Lemma lem1967949 (_27661 : real) (h1 : term47) : term45 _27661.
Proof. exact (EQ_MP (@lem1967946 _27661) (@lem1967935 _27661 h1)). Qed.
Lemma lem1967950 (x : real) (h1 : term47) : term45 x.
Proof. exact (@lem1967949 x h1). Qed.
Lemma lem1967953 (x : real) (y : real) (h1 : term47) (h2 : term53 x y) : (term73 x) = x.
Proof. exact (@lem1967950 x h1 (@lem1967902 x y h2)). Qed.
Lemma lem1967954 (x : real) (y : real) (h1 : term47) (h2 : term53 x y) : term122 x.
Proof. exact (fun h0 : term123 x => @lem1967953 x y h1 h2). Qed.
Lemma lem1967956 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1967957 (x : real) : (term122 x) = ((term73 x) = x).
Proof. exact (@lem1967956 ((term73 x) = x)). Qed.
Lemma lem1967958 (x : real) (y : real) (h1 : term47) (h2 : term53 x y) : (term73 x) = x.
Proof. exact (EQ_MP (@lem1967957 x) (@lem1967954 x y h1 h2)). Qed.
Lemma lem1967960 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1967961 (y : real) : (term124 y) = (term124 y).
Proof. exact (@lem1967960 (term124 y)). Qed.
Lemma lem1967962 (y : real) : term125 y.
Proof. exact (fun h0 : term126 y => @lem1967961 y). Qed.
Lemma lem1967964 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1967965 (y : real) : (term125 y) = ((term124 y) = (term124 y)).
Proof. exact (@lem1967964 ((term124 y) = (term124 y))). Qed.
Lemma lem1967966 (y : real) : (term124 y) = (term124 y).
Proof. exact (EQ_MP (@lem1967965 y) (@lem1967962 y)). Qed.
Lemma lem1967968 (x : real) (y : real) (h1 : term53 x y) : term72 x.
Proof. exact (proj1 (@lem1967661 x y h1)). Qed.
Lemma lem1967969 (x : real) (y : real) (h1 : term53 x y) : term111 x.
Proof. exact (fun h0 : term100 x => @lem1967968 x y h1). Qed.
Lemma lem1967971 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1967972 (x : real) : (term111 x) = (term72 x).
Proof. exact (@lem1967971 (term72 x)). Qed.
Lemma lem1967973 (x : real) (y : real) (h1 : term53 x y) : term72 x.
Proof. exact (EQ_MP (@lem1967972 x) (@lem1967969 x y h1)). Qed.
Lemma lem1967979 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1967980 (_27665 : real) : (term76 _27665) = (term127 _27665).
Proof. exact (@lem1967979 (term77 _27665) (term100 _27665)). Qed.
Lemma lem1967986 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1967987 (_27665 : real) : (term128 _27665) = (term129 _27665).
Proof. exact (MK_COMB (@lem1967986) (@lem1967980 _27665)). Qed.
Lemma lem1967993 (_27665 : real) : (term127 _27665) = (term127 _27665).
Proof. exact (eq_refl (term127 _27665)). Qed.
Lemma lem1967994 (_27665 : real) : ((term76 _27665) = (term127 _27665)) = ((term127 _27665) = (term127 _27665)).
Proof. exact (MK_COMB (@lem1967987 _27665) (@lem1967993 _27665)). Qed.
Lemma lem1967996 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1967997 (x : Prop) : (x = x) = True.
Proof. exact (@lem1967996 Prop x). Qed.
Lemma lem1967998 (_27665 : real) : ((term127 _27665) = (term127 _27665)) = True.
Proof. exact (@lem1967997 (term127 _27665)). Qed.
Lemma lem1967999 (_27665 : real) : ((term76 _27665) = (term127 _27665)) = True.
Proof. exact (TRANS (@lem1967994 _27665) (@lem1967998 _27665)). Qed.
Lemma lem1968000 (_27665 : real) : True = ((term76 _27665) = (term127 _27665)).
Proof. exact (SYM (@lem1967999 _27665)). Qed.
Lemma lem1968001 (_27665 : real) : (term76 _27665) = (term127 _27665).
Proof. exact (EQ_MP (@lem1968000 _27665) (@lem0)). Qed.
Lemma lem1968002 (_27665 : real) (h1 : term37) : term127 _27665.
Proof. exact (EQ_MP (@lem1968001 _27665) (@lem1967799 _27665 h1)). Qed.
Lemma lem1968004 (b : Prop) (a : Prop) : (a \/ b) = (term116 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1968005 (_27665 : real) : (term127 _27665) = (term130 _27665).
Proof. exact (@lem1968004 (term100 _27665) (term77 _27665)). Qed.
Lemma lem1968007 (a : Prop) : (term118 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1968008 (_27665 : real) : (term119 _27665) = (term72 _27665).
Proof. exact (@lem1968007 (term72 _27665)). Qed.
Lemma lem1968009 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1968010 (_27665 : real) : (term120 _27665) = (term121 _27665).
Proof. exact (MK_COMB (@lem1968009) (@lem1968008 _27665)). Qed.
Lemma lem1968011 (_27665 : real) : (term77 _27665) = (term77 _27665).
Proof. exact (eq_refl (term77 _27665)). Qed.
Lemma lem1968012 (_27665 : real) : (term130 _27665) = (term35 _27665).
Proof. exact (MK_COMB (@lem1968010 _27665) (@lem1968011 _27665)). Qed.
Lemma lem1968013 (_27665 : real) : (term127 _27665) = (term35 _27665).
Proof. exact (TRANS (@lem1968005 _27665) (@lem1968012 _27665)). Qed.
Lemma lem1968016 (_27665 : real) (h1 : term37) : term35 _27665.
Proof. exact (EQ_MP (@lem1968013 _27665) (@lem1968002 _27665 h1)). Qed.
Lemma lem1968017 (x : real) (h1 : term37) : term35 x.
Proof. exact (@lem1968016 x h1). Qed.
Lemma lem1968020 (x : real) (y : real) (h1 : term37) (h2 : term53 x y) : term77 x.
Proof. exact (@lem1968017 x h1 (@lem1967973 x y h2)). Qed.
Lemma lem1968021 (x : real) (y : real) (h1 : term37) (h2 : term53 x y) : term131 x.
Proof. exact (fun h0 : term132 x => @lem1968020 x y h1 h2). Qed.
Lemma lem1968023 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1968024 (x : real) : (term131 x) = (term77 x).
Proof. exact (@lem1968023 (term77 x)). Qed.
Lemma lem1968025 (x : real) (y : real) (h1 : term37) (h2 : term53 x y) : term77 x.
Proof. exact (EQ_MP (@lem1968024 x) (@lem1968021 x y h1 h2)). Qed.
Lemma lem1968027 (x : real) (y : real) (h1 : term53 x y) : term133 x y.
Proof. exact (proj2 (@lem1967661 x y h1)). Qed.
Lemma lem1968028 (x : real) (y : real) (h1 : term53 x y) : term134 x y.
Proof. exact (fun h0 : term135 x y => @lem1968027 x y h1). Qed.
Lemma lem1968030 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1968031 (x : real) (y : real) : (term134 x y) = (term133 x y).
Proof. exact (@lem1968030 (term133 x y)). Qed.
Lemma lem1968032 (x : real) (y : real) (h1 : term53 x y) : term133 x y.
Proof. exact (EQ_MP (@lem1968031 x y) (@lem1968028 x y h1)). Qed.
Lemma lem1968038 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1968039 (_27667 : real) (_27668 : real) (_27666 : nat) : (term99 _27667 _27668 _27666) = (term136 _27667 _27668 _27666).
Proof. exact (@lem1968038 (term101 _27667 _27668) (term100 _27667) (term82 _27667 _27668 _27666)). Qed.
Lemma lem1968053 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1968054 (_27668 : real) (_27666 : nat) (_27667 : real) : (term137 _27667 _27668 _27666) = (term138 _27668 _27666 _27667).
Proof. exact (@lem1968053 (term82 _27667 _27668 _27666) (term100 _27667)). Qed.
Lemma lem1968060 (_27667 : real) (_27668 : real) : (term139 _27667 _27668) = (term139 _27667 _27668).
Proof. exact (eq_refl (term139 _27667 _27668)). Qed.
Lemma lem1968061 (_27668 : real) (_27666 : nat) (_27667 : real) : (term136 _27667 _27668 _27666) = (term140 _27668 _27666 _27667).
Proof. exact (MK_COMB (@lem1968060 _27667 _27668) (@lem1968054 _27668 _27666 _27667)). Qed.
Lemma lem1968065 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1968066 (_27666 : nat) (_27668 : real) (_27667 : real) : (term140 _27668 _27666 _27667) = (term141 _27666 _27668 _27667).
Proof. exact (@lem1968065 (term82 _27667 _27668 _27666) (term101 _27667 _27668) (term100 _27667)). Qed.
Lemma lem1968082 (_27666 : nat) (_27668 : real) (_27667 : real) : (term136 _27667 _27668 _27666) = (term141 _27666 _27668 _27667).
Proof. exact (TRANS (@lem1968061 _27668 _27666 _27667) (@lem1968066 _27666 _27668 _27667)). Qed.
Lemma lem1968083 (_27666 : nat) (_27668 : real) (_27667 : real) : (term99 _27667 _27668 _27666) = (term141 _27666 _27668 _27667).
Proof. exact (TRANS (@lem1968039 _27667 _27668 _27666) (@lem1968082 _27666 _27668 _27667)). Qed.
Lemma lem1968084 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1968085 (_27666 : nat) (_27668 : real) (_27667 : real) : (term142 _27667 _27668 _27666) = (term143 _27666 _27668 _27667).
Proof. exact (MK_COMB (@lem1968084) (@lem1968083 _27666 _27668 _27667)). Qed.
Lemma lem1968099 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1968100 (_27668 : real) (_27667 : real) : (term81 _27667 _27668) = (term144 _27668 _27667).
Proof. exact (@lem1968099 (term101 _27667 _27668) (term100 _27667)). Qed.
Lemma lem1968106 (_27667 : real) (_27668 : real) (_27666 : nat) : (term145 _27667 _27668 _27666) = (term145 _27667 _27668 _27666).
Proof. exact (eq_refl (term145 _27667 _27668 _27666)). Qed.
Lemma lem1968107 (_27666 : nat) (_27668 : real) (_27667 : real) : (term146 _27666 _27667 _27668) = (term141 _27666 _27668 _27667).
Proof. exact (MK_COMB (@lem1968106 _27667 _27668 _27666) (@lem1968100 _27668 _27667)). Qed.
Lemma lem1968118 (_27666 : nat) (_27668 : real) (_27667 : real) : ((term99 _27667 _27668 _27666) = (term146 _27666 _27667 _27668)) = ((term141 _27666 _27668 _27667) = (term141 _27666 _27668 _27667)).
Proof. exact (MK_COMB (@lem1968085 _27666 _27668 _27667) (@lem1968107 _27666 _27668 _27667)). Qed.
Lemma lem1968120 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1968121 (x : Prop) : (x = x) = True.
Proof. exact (@lem1968120 Prop x). Qed.
Lemma lem1968122 (_27666 : nat) (_27668 : real) (_27667 : real) : ((term141 _27666 _27668 _27667) = (term141 _27666 _27668 _27667)) = True.
Proof. exact (@lem1968121 (term141 _27666 _27668 _27667)). Qed.
Lemma lem1968123 (_27666 : nat) (_27667 : real) (_27668 : real) : ((term99 _27667 _27668 _27666) = (term146 _27666 _27667 _27668)) = True.
Proof. exact (TRANS (@lem1968118 _27666 _27668 _27667) (@lem1968122 _27666 _27668 _27667)). Qed.
Lemma lem1968124 (_27666 : nat) (_27667 : real) (_27668 : real) : True = ((term99 _27667 _27668 _27666) = (term146 _27666 _27667 _27668)).
Proof. exact (SYM (@lem1968123 _27666 _27667 _27668)). Qed.
Lemma lem1968125 (_27666 : nat) (_27667 : real) (_27668 : real) : (term99 _27667 _27668 _27666) = (term146 _27666 _27667 _27668).
Proof. exact (EQ_MP (@lem1968124 _27666 _27667 _27668) (@lem0)). Qed.
Lemma lem1968126 (_27666 : nat) (_27667 : real) (_27668 : real) (h1 : term17) : term146 _27666 _27667 _27668.
Proof. exact (EQ_MP (@lem1968125 _27666 _27667 _27668) (@lem1967811 _27667 _27668 _27666 h1)). Qed.
Lemma lem1968128 (b : Prop) (a : Prop) : (a \/ b) = (term116 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1968129 (_27667 : real) (_27668 : real) (_27666 : nat) : (term146 _27666 _27667 _27668) = (term147 _27667 _27668 _27666).
Proof. exact (@lem1968128 (term81 _27667 _27668) (term82 _27667 _27668 _27666)). Qed.
Lemma lem1968131 (a : Prop) (b : Prop) : (term148 a b) = (term149 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1968132 (_27667 : real) (_27668 : real) : (term150 _27667 _27668) = (term151 _27667 _27668).
Proof. exact (@lem1968131 (term100 _27667) (term101 _27667 _27668)). Qed.
Lemma lem1968134 (a : Prop) : (term118 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1968135 (_27667 : real) : (term119 _27667) = (term72 _27667).
Proof. exact (@lem1968134 (term72 _27667)). Qed.
Lemma lem1968136 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1968137 (_27667 : real) : (term152 _27667) = (term153 _27667).
Proof. exact (MK_COMB (@lem1968136) (@lem1968135 _27667)). Qed.
Lemma lem1968139 (a : Prop) : (term118 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1968140 (_27667 : real) (_27668 : real) : (term154 _27667 _27668) = (real_le _27667 _27668).
Proof. exact (@lem1968139 (real_le _27667 _27668)). Qed.
Lemma lem1968141 (_27667 : real) (_27668 : real) : (term151 _27667 _27668) = (term87 _27667 _27668).
Proof. exact (MK_COMB (@lem1968137 _27667) (@lem1968140 _27667 _27668)). Qed.
Lemma lem1968142 (_27667 : real) (_27668 : real) : (term150 _27667 _27668) = (term87 _27667 _27668).
Proof. exact (TRANS (@lem1968132 _27667 _27668) (@lem1968141 _27667 _27668)). Qed.
Lemma lem1968143 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1968144 (_27667 : real) (_27668 : real) : (term155 _27667 _27668) = (term156 _27667 _27668).
Proof. exact (MK_COMB (@lem1968143) (@lem1968142 _27667 _27668)). Qed.
Lemma lem1968145 (_27667 : real) (_27668 : real) (_27666 : nat) : (term82 _27667 _27668 _27666) = (term82 _27667 _27668 _27666).
Proof. exact (eq_refl (term82 _27667 _27668 _27666)). Qed.
Lemma lem1968146 (_27667 : real) (_27668 : real) (_27666 : nat) : (term147 _27667 _27668 _27666) = (term29 _27667 _27668 _27666).
Proof. exact (MK_COMB (@lem1968144 _27667 _27668) (@lem1968145 _27667 _27668 _27666)). Qed.
Lemma lem1968147 (_27667 : real) (_27668 : real) (_27666 : nat) : (term146 _27666 _27667 _27668) = (term29 _27667 _27668 _27666).
Proof. exact (TRANS (@lem1968129 _27667 _27668 _27666) (@lem1968146 _27667 _27668 _27666)). Qed.
Lemma lem1968149 (x : real) (y : real) (h1 : term37) (h2 : term53 x y) : term157 x y.
Proof. exact (conj (@lem1968025 x y h1 h2) (@lem1968032 x y h2)). Qed.
Lemma lem1968151 (_27667 : real) (_27668 : real) (_27666 : nat) (h1 : term17) : term29 _27667 _27668 _27666.
Proof. exact (EQ_MP (@lem1968147 _27667 _27668 _27666) (@lem1968126 _27666 _27667 _27668 h1)). Qed.
Lemma lem1968152 (x : real) (y : real) (_27666 : nat) (h1 : term17) : term158 x y _27666.
Proof. exact (@lem1968151 (sqrt x) y _27666 h1). Qed.
Lemma lem1968155 (_27666 : nat) (x : real) (y : real) (h1 : term17) (h2 : term37) (h3 : term53 x y) : term159 x y _27666.
Proof. exact (@lem1968152 x y _27666 h1 (@lem1968149 x y h2 h3)). Qed.
Lemma lem1968156 (x : real) (y : real) (h1 : term17) (h2 : term37) (h3 : term53 x y) : term160 x y.
Proof. exact (@lem1968155 term161 x y h1 h2 h3). Qed.
Lemma lem1968157 (x : real) (y : real) (h1 : term17) (h2 : term37) (h3 : term53 x y) : term162 x y.
Proof. exact (fun h0 : term163 x y => @lem1968156 x y h1 h2 h3). Qed.
Lemma lem1968159 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1968160 (x : real) (y : real) : (term162 x y) = (term160 x y).
Proof. exact (@lem1968159 (term160 x y)). Qed.
Lemma lem1968161 (x : real) (y : real) (h1 : term17) (h2 : term37) (h3 : term53 x y) : term160 x y.
Proof. exact (EQ_MP (@lem1968160 x y) (@lem1968157 x y h1 h2 h3)). Qed.
Lemma lem1968179 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1968180 (_27671 : real) (_27672 : real) (_27669 : real) (_27670 : real) : (term108 _27671 _27672 _27669 _27670) = (term164 _27671 _27672 _27669 _27670).
Proof. exact (@lem1968179 (real_le _27671 _27672) (term165 _27670 _27672) (term101 _27669 _27670)). Qed.
Lemma lem1968198 (_27669 : real) (_27671 : real) : (term166 _27669 _27671) = (term166 _27669 _27671).
Proof. exact (eq_refl (term166 _27669 _27671)). Qed.
Lemma lem1968199 (_27671 : real) (_27672 : real) (_27669 : real) (_27670 : real) : (term110 _27671 _27672 _27669 _27670) = (term167 _27671 _27672 _27669 _27670).
Proof. exact (MK_COMB (@lem1968198 _27669 _27671) (@lem1968180 _27671 _27672 _27669 _27670)). Qed.
Lemma lem1968203 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1968204 (_27671 : real) (_27672 : real) (_27669 : real) (_27670 : real) : (term167 _27671 _27672 _27669 _27670) = (term168 _27671 _27672 _27669 _27670).
Proof. exact (@lem1968203 (real_le _27671 _27672) (term165 _27669 _27671) (term169 _27672 _27669 _27670)). Qed.
Lemma lem1968234 (_27671 : real) (_27672 : real) (_27669 : real) (_27670 : real) : (term110 _27671 _27672 _27669 _27670) = (term168 _27671 _27672 _27669 _27670).
Proof. exact (TRANS (@lem1968199 _27671 _27672 _27669 _27670) (@lem1968204 _27671 _27672 _27669 _27670)). Qed.
Lemma lem1968235 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1968236 (_27671 : real) (_27672 : real) (_27669 : real) (_27670 : real) : (term170 _27671 _27672 _27669 _27670) = (term171 _27671 _27672 _27669 _27670).
Proof. exact (MK_COMB (@lem1968235) (@lem1968234 _27671 _27672 _27669 _27670)). Qed.
Lemma lem1968266 (_27671 : real) (_27672 : real) (_27669 : real) (_27670 : real) : (term168 _27671 _27672 _27669 _27670) = (term168 _27671 _27672 _27669 _27670).
Proof. exact (eq_refl (term168 _27671 _27672 _27669 _27670)). Qed.
Lemma lem1968267 (_27671 : real) (_27672 : real) (_27669 : real) (_27670 : real) : ((term110 _27671 _27672 _27669 _27670) = (term168 _27671 _27672 _27669 _27670)) = ((term168 _27671 _27672 _27669 _27670) = (term168 _27671 _27672 _27669 _27670)).
Proof. exact (MK_COMB (@lem1968236 _27671 _27672 _27669 _27670) (@lem1968266 _27671 _27672 _27669 _27670)). Qed.
Lemma lem1968269 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1968270 (x : Prop) : (x = x) = True.
Proof. exact (@lem1968269 Prop x). Qed.
Lemma lem1968271 (_27671 : real) (_27672 : real) (_27669 : real) (_27670 : real) : ((term168 _27671 _27672 _27669 _27670) = (term168 _27671 _27672 _27669 _27670)) = True.
Proof. exact (@lem1968270 (term168 _27671 _27672 _27669 _27670)). Qed.
Lemma lem1968272 (_27671 : real) (_27672 : real) (_27669 : real) (_27670 : real) : ((term110 _27671 _27672 _27669 _27670) = (term168 _27671 _27672 _27669 _27670)) = True.
Proof. exact (TRANS (@lem1968267 _27671 _27672 _27669 _27670) (@lem1968271 _27671 _27672 _27669 _27670)). Qed.
Lemma lem1968273 (_27671 : real) (_27672 : real) (_27669 : real) (_27670 : real) : True = ((term110 _27671 _27672 _27669 _27670) = (term168 _27671 _27672 _27669 _27670)).
Proof. exact (SYM (@lem1968272 _27671 _27672 _27669 _27670)). Qed.
Lemma lem1968274 (_27671 : real) (_27672 : real) (_27669 : real) (_27670 : real) : (term110 _27671 _27672 _27669 _27670) = (term168 _27671 _27672 _27669 _27670).
Proof. exact (EQ_MP (@lem1968273 _27671 _27672 _27669 _27670) (@lem0)). Qed.
Lemma lem1968275 (_27671 : real) (_27672 : real) (_27669 : real) (_27670 : real) : term168 _27671 _27672 _27669 _27670.
Proof. exact (EQ_MP (@lem1968274 _27671 _27672 _27669 _27670) (@lem1967836 _27671 _27672 _27669 _27670)). Qed.
Lemma lem1968277 (b : Prop) (a : Prop) : (a \/ b) = (term116 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1968278 (_27669 : real) (_27670 : real) (_27671 : real) (_27672 : real) : (term168 _27671 _27672 _27669 _27670) = (term172 _27669 _27670 _27671 _27672).
Proof. exact (@lem1968277 (term173 _27671 _27672 _27669 _27670) (real_le _27671 _27672)). Qed.
Lemma lem1968280 (a : Prop) (b : Prop) : (term148 a b) = (term149 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1968281 (_27671 : real) (_27672 : real) (_27669 : real) (_27670 : real) : (term174 _27671 _27672 _27669 _27670) = (term175 _27671 _27672 _27669 _27670).
Proof. exact (@lem1968280 (term165 _27669 _27671) (term169 _27672 _27669 _27670)). Qed.
Lemma lem1968283 (a : Prop) : (term118 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1968284 (_27669 : real) (_27671 : real) : (term176 _27669 _27671) = (_27669 = _27671).
Proof. exact (@lem1968283 (_27669 = _27671)). Qed.
Lemma lem1968285 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1968286 (_27669 : real) (_27671 : real) : (term177 _27669 _27671) = (term178 _27669 _27671).
Proof. exact (MK_COMB (@lem1968285) (@lem1968284 _27669 _27671)). Qed.
Lemma lem1968288 (a : Prop) (b : Prop) : (term148 a b) = (term149 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1968289 (_27672 : real) (_27669 : real) (_27670 : real) : (term179 _27672 _27669 _27670) = (term180 _27672 _27669 _27670).
Proof. exact (@lem1968288 (term165 _27670 _27672) (term101 _27669 _27670)). Qed.
Lemma lem1968291 (a : Prop) : (term118 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1968292 (_27670 : real) (_27672 : real) : (term176 _27670 _27672) = (_27670 = _27672).
Proof. exact (@lem1968291 (_27670 = _27672)). Qed.
Lemma lem1968293 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1968294 (_27670 : real) (_27672 : real) : (term177 _27670 _27672) = (term178 _27670 _27672).
Proof. exact (MK_COMB (@lem1968293) (@lem1968292 _27670 _27672)). Qed.
Lemma lem1968296 (a : Prop) : (term118 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1968297 (_27669 : real) (_27670 : real) : (term154 _27669 _27670) = (real_le _27669 _27670).
Proof. exact (@lem1968296 (real_le _27669 _27670)). Qed.
Lemma lem1968298 (_27672 : real) (_27669 : real) (_27670 : real) : (term180 _27672 _27669 _27670) = (term181 _27672 _27669 _27670).
Proof. exact (MK_COMB (@lem1968294 _27670 _27672) (@lem1968297 _27669 _27670)). Qed.
Lemma lem1968299 (_27672 : real) (_27669 : real) (_27670 : real) : (term179 _27672 _27669 _27670) = (term181 _27672 _27669 _27670).
Proof. exact (TRANS (@lem1968289 _27672 _27669 _27670) (@lem1968298 _27672 _27669 _27670)). Qed.
Lemma lem1968300 (_27671 : real) (_27672 : real) (_27669 : real) (_27670 : real) : (term175 _27671 _27672 _27669 _27670) = (term182 _27671 _27672 _27669 _27670).
Proof. exact (MK_COMB (@lem1968286 _27669 _27671) (@lem1968299 _27672 _27669 _27670)). Qed.
Lemma lem1968301 (_27671 : real) (_27672 : real) (_27669 : real) (_27670 : real) : (term174 _27671 _27672 _27669 _27670) = (term182 _27671 _27672 _27669 _27670).
Proof. exact (TRANS (@lem1968281 _27671 _27672 _27669 _27670) (@lem1968300 _27671 _27672 _27669 _27670)). Qed.
Lemma lem1968302 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1968303 (_27671 : real) (_27672 : real) (_27669 : real) (_27670 : real) : (term183 _27671 _27672 _27669 _27670) = (term184 _27671 _27672 _27669 _27670).
Proof. exact (MK_COMB (@lem1968302) (@lem1968301 _27671 _27672 _27669 _27670)). Qed.
Lemma lem1968304 (_27671 : real) (_27672 : real) : (real_le _27671 _27672) = (real_le _27671 _27672).
Proof. exact (eq_refl (real_le _27671 _27672)). Qed.
Lemma lem1968305 (_27669 : real) (_27670 : real) (_27671 : real) (_27672 : real) : (term172 _27669 _27670 _27671 _27672) = (term185 _27669 _27670 _27671 _27672).
Proof. exact (MK_COMB (@lem1968303 _27671 _27672 _27669 _27670) (@lem1968304 _27671 _27672)). Qed.
Lemma lem1968306 (_27669 : real) (_27670 : real) (_27671 : real) (_27672 : real) : (term168 _27671 _27672 _27669 _27670) = (term185 _27669 _27670 _27671 _27672).
Proof. exact (TRANS (@lem1968278 _27669 _27670 _27671 _27672) (@lem1968305 _27669 _27670 _27671 _27672)). Qed.
Lemma lem1968308 (x : real) (y : real) (h1 : term17) (h2 : term37) (h3 : term53 x y) : term186 x y.
Proof. exact (conj (@lem1967966 y) (@lem1968161 x y h1 h2 h3)). Qed.
Lemma lem1968309 (x : real) (y : real) (h1 : term17) (h2 : term47) (h3 : term37) (h4 : term53 x y) : term187 x y.
Proof. exact (conj (@lem1967958 x y h2 h4) (@lem1968308 x y h1 h3 h4)). Qed.
Lemma lem1968311 (_27669 : real) (_27670 : real) (_27671 : real) (_27672 : real) : term185 _27669 _27670 _27671 _27672.
Proof. exact (EQ_MP (@lem1968306 _27669 _27670 _27671 _27672) (@lem1968275 _27671 _27672 _27669 _27670)). Qed.
Lemma lem1968312 (x : real) (y : real) : term188 x y.
Proof. exact (@lem1968311 (term73 x) (term124 y) x (term124 y)). Qed.
Lemma lem1968315 (x : real) (y : real) (h1 : term17) (h2 : term47) (h3 : term37) (h4 : term53 x y) : term55 x y.
Proof. exact (@lem1968312 x y (@lem1968309 x y h1 h2 h3 h4)). Qed.
Lemma lem1968316 (x : real) (y : real) (h1 : term17) (h2 : term47) (h3 : term37) (h4 : term53 x y) : term189 x y.
Proof. exact (fun h0 : term102 x y => @lem1968315 x y h1 h2 h3 h4). Qed.
Lemma lem1968318 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1968319 (x : real) (y : real) : (term189 x y) = (term55 x y).
Proof. exact (@lem1968318 (term55 x y)). Qed.
Lemma lem1968320 (x : real) (y : real) (h1 : term17) (h2 : term47) (h3 : term37) (h4 : term53 x y) : term55 x y.
Proof. exact (EQ_MP (@lem1968319 x y) (@lem1968316 x y h1 h2 h3 h4)). Qed.
Lemma lem1968323 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1968325 (x : real) (y : real) : (term102 x y) = (term190 x y).
Proof. exact (@lem1968323 (term55 x y)). Qed.
Lemma lem1968328 (x : real) (y : real) (h1 : term53 x y) : term190 x y.
Proof. exact (EQ_MP (@lem1968325 x y) (@lem1967813 x y h1)). Qed.
Lemma lem1968331 (x : real) (y : real) (h1 : term17) (h2 : term47) (h3 : term37) (h4 : term53 x y) : False.
Proof. exact (@lem1968328 x y h4 (@lem1968320 x y h1 h2 h3 h4)). Qed.
Lemma lem1968332 (x : real) (y : real) (h1 : term17) (h2 : term47) (h3 : term37) (h4 : term53 x y) : term191.
Proof. exact (fun h0 : ~ False => @lem1968331 x y h1 h2 h3 h4). Qed.
Lemma lem1968334 (p : Prop) : (term112 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1968335 : term191 = False.
Proof. exact (@lem1968334 False). Qed.
Lemma lem1968336 (x : real) (y : real) (h1 : term17) (h2 : term47) (h3 : term37) (h4 : term53 x y) : False.
Proof. exact (EQ_MP (@lem1968335) (@lem1968332 x y h1 h2 h3 h4)). Qed.
Lemma lem1968337 (x : real) (y : real) (h1 : term17) (h2 : term47) (h3 : term37) (h4 : term53 x y) : (term53 x y) = False.
Proof. exact (prop_ext (fun h5 : term53 x y => @lem1968336 x y h1 h2 h3 h4) (fun h5 : False => @lem1967659 x y h4)). Qed.
Lemma lem1968338 (x : real) (y : real) (h1 : term17) (h2 : term47) (h3 : term37) (h4 : term53 x y) : False.
Proof. exact (EQ_MP (@lem1968337 x y h1 h2 h3 h4) (@lem1967659 x y h4)). Qed.
Lemma lem1968339 (x : real) (h1 : term17) (h2 : term47) (h3 : term37) (h4 : term64 x) : False.
Proof. exact (ex_elim (@lem1967472 x h4) (fun y : real => fun h0 : term63 x y => @lem1968338 x y h1 h2 h3 h0)). Qed.
Lemma lem1968340 (h1 : term17) (h2 : term47) (h3 : term37) (h4 : term10) : False.
Proof. exact (ex_elim (@lem1967179 h4) (fun x : real => fun h0 : term69 x => @lem1968339 x h1 h2 h3 h0)). Qed.
Lemma lem1968341 (h1 : term47) (h2 : term37) (h3 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem1968340 h0 h1 h2 h3). Qed.
Lemma lem1968342 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem1968343 (h1 : term47) (h2 : term37) (h3 : term10) : term16.
Proof. exact (EQ_MP (@lem1968342) (@lem1968341 h1 h2 h3)). Qed.
Lemma lem1968344 (h1 : term47) (h2 : term10) : term20.
Proof. exact (fun h0 : term37 => @lem1968343 h1 h0 h2). Qed.
Lemma lem1968345 (h1 : term47) (h2 : term10) : term23.
Proof. exact (fun h0 : term44 => @lem1968344 h1 h2). Qed.
Lemma lem1968346 (h1 : term10) : term26.
Proof. exact (fun h0 : term47 => @lem1968345 h0 h1). Qed.
Lemma lem1968347 : term28.
Proof. exact (fun h0 : term10 => @lem1968346 h0). Qed.
Lemma lem1968348 : term11.
Proof. exact (EQ_MP (@lem1967086) (@lem1968347)). Qed.
Lemma lem1968350 : term11.
Proof. exact (@lem1966828 (@lem1968348)). Qed.
Lemma lem1968351 (h1 : term10) : term25.
Proof. exact (@lem1968350 (@lem1966813 h1)). Qed.
Lemma lem1968352 (h1 : term10) : term22.
Proof. exact (@lem1968351 h1 (@lem1945848)). Qed.
Lemma lem1968353 (h1 : term10) : term19.
Proof. exact (@lem1968352 h1 (@lem1339577)). Qed.
Lemma lem1968354 (h1 : term10) : term15.
Proof. exact (@lem1968353 h1 (@lem1945292)). Qed.
Lemma lem1968355 (h1 : term10) : False.
Proof. exact (@lem1968354 h1 (@lem1636714)). Qed.
Lemma lem1968356 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem1968355 h1) (fun h2 : False => @lem1966813 h1)). Qed.
Lemma lem1968357 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem1968356 h1) (@lem1966813 h1)). Qed.
Lemma lem1968358 : term9.
Proof. exact (fun h0 : term10 => @lem1968357 h0). Qed.
Lemma lem1968359 : term8.
Proof. exact (EQ_MP (@lem1966812) (@lem1968358)). Qed.
