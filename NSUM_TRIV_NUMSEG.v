Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_TRIV_NUMSEG_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import LE_TRANS_spec.
Require Import NOT_LT_spec.
Require Import NSUM_EQ_0_NUMSEG_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19699_spec.
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
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem7044963 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem7044964 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem7044965 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem7044964 t1) (@lem7044963 t1)). Qed.
Lemma lem7044966 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem7044965 t1 t2). Qed.
Lemma lem7044967 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem7044968 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem7044967 t1 t2) (@lem7044966 t1 t2)). Qed.
Lemma lem7044969 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem7044968 t1 t2 t3). Qed.
Lemma lem7044970 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem7044971 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem7044970 t1 t2 t3) (@lem7044969 t1 t2 t3)). Qed.
Lemma lem7044972 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem7044971 t1 t2 t3)). Qed.
Lemma lem7044974 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7044975 : term8 = term9.
Proof. exact (@lem7044974 term8). Qed.
Lemma lem7044976 : term9 = term8.
Proof. exact (SYM (@lem7044975)). Qed.
Lemma lem7044977 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem7044980 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem7044981 : term12.
Proof. exact (fun h0 : term11 => @lem7044980 h0). Qed.
Lemma lem7044982 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem7044983 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem7044984 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem7044982 h2 (@lem7044983 h1)). Qed.
Lemma lem7044985 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem7044984 h1 h0). Qed.
Lemma lem7044986 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem7044987 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem7044985 h1 (@lem7044986 h2)). Qed.
Lemma lem7044988 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem7044987 h0 h1). Qed.
Lemma lem7044989 : term14.
Proof. exact (fun h0 : term12 => @lem7044988 h0). Qed.
Lemma lem7044992 : term12.
Proof. exact (@lem7044989 (@lem7044981)). Qed.
Lemma lem7045038 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7045039 : term15 = term16.
Proof. exact (@lem7045038 term17). Qed.
Lemma lem7045062 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem7045063 : term19 = term20.
Proof. exact (MK_COMB (@lem7045062) (@lem7045039)). Qed.
Lemma lem7045066 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem7045067 : term22 = term23.
Proof. exact (MK_COMB (@lem7045066) (@lem7045063)). Qed.
Lemma lem7045070 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem7045077 : term11 = term25.
Proof. exact (MK_COMB (@lem7045070) (@lem7045067)). Qed.
Lemma lem7045078 (m : nat) (n : nat) (f : nat -> nat) : ((term26 m n f) = (NUMERAL 0)) = ((term26 m n f) = (NUMERAL 0)).
Proof. exact (eq_refl ((term26 m n f) = (NUMERAL 0))). Qed.
Lemma lem7045087 (m : nat) (n : nat) (f : nat -> nat) (i : nat) : (term27 m n f i) = (term27 m n f i).
Proof. exact (eq_refl (term27 m n f i)). Qed.
Lemma lem7045088 (m : nat) (n : nat) (f : nat -> nat) : (term28 m n f) = (term28 m n f).
Proof. exact (fun_ext (fun i : nat => @lem7045087 m n f i)). Qed.
Lemma lem7045089 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045090 (m : nat) (n : nat) (f : nat -> nat) : (term29 m n f) = (term29 m n f).
Proof. exact (MK_COMB (@lem7045089) (@lem7045088 m n f)). Qed.
Lemma lem7045091 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7045092 (m : nat) (n : nat) (f : nat -> nat) : (term30 m n f) = (term30 m n f).
Proof. exact (MK_COMB (@lem7045091) (@lem7045090 m n f)). Qed.
Lemma lem7045093 (m : nat) (n : nat) (f : nat -> nat) : (term31 m n f) = (term31 m n f).
Proof. exact (MK_COMB (@lem7045092 m n f) (@lem7045078 m n f)). Qed.
Lemma lem7045094 (m : nat) (f : nat -> nat) : (term32 m f) = (term32 m f).
Proof. exact (fun_ext (fun n : nat => @lem7045093 m n f)). Qed.
Lemma lem7045095 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045096 (m : nat) (f : nat -> nat) : (term33 m f) = (term33 m f).
Proof. exact (MK_COMB (@lem7045095) (@lem7045094 m f)). Qed.
Lemma lem7045097 (f : nat -> nat) : (term34 f) = (term34 f).
Proof. exact (fun_ext (fun m : nat => @lem7045096 m f)). Qed.
Lemma lem7045098 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045099 (f : nat -> nat) : (term35 f) = (term35 f).
Proof. exact (MK_COMB (@lem7045098) (@lem7045097 f)). Qed.
Lemma lem7045100 : term36 = term36.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7045099 f)). Qed.
Lemma lem7045101 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7045102 : term17 = term17.
Proof. exact (MK_COMB (@lem7045101) (@lem7045100)). Qed.
Lemma lem7045103 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7045104 : term16 = term16.
Proof. exact (MK_COMB (@lem7045103) (@lem7045102)). Qed.
Lemma lem7045113 (n : nat) (m : nat) (p : nat) : (term37 n m p) = (term37 n m p).
Proof. exact (eq_refl (term37 n m p)). Qed.
Lemma lem7045114 (n : nat) (m : nat) : (term38 n m) = (term38 n m).
Proof. exact (fun_ext (fun p : nat => @lem7045113 n m p)). Qed.
Lemma lem7045115 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045116 (n : nat) (m : nat) : (term39 n m) = (term39 n m).
Proof. exact (MK_COMB (@lem7045115) (@lem7045114 n m)). Qed.
Lemma lem7045117 (m : nat) : (term40 m) = (term40 m).
Proof. exact (fun_ext (fun n : nat => @lem7045116 n m)). Qed.
Lemma lem7045118 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045119 (m : nat) : (term41 m) = (term41 m).
Proof. exact (MK_COMB (@lem7045118) (@lem7045117 m)). Qed.
Lemma lem7045120 : term42 = term42.
Proof. exact (fun_ext (fun m : nat => @lem7045119 m)). Qed.
Lemma lem7045121 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045122 : term43 = term43.
Proof. exact (MK_COMB (@lem7045121) (@lem7045120)). Qed.
Lemma lem7045123 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7045124 : term18 = term18.
Proof. exact (MK_COMB (@lem7045123) (@lem7045122)). Qed.
Lemma lem7045125 : term20 = term20.
Proof. exact (MK_COMB (@lem7045124) (@lem7045104)). Qed.
Lemma lem7045132 (n : nat) (m : nat) : ((term44 m n) = (Peano.le n m)) = ((term44 m n) = (Peano.le n m)).
Proof. exact (eq_refl ((term44 m n) = (Peano.le n m))). Qed.
Lemma lem7045133 (m : nat) : (term45 m) = (term45 m).
Proof. exact (fun_ext (fun n : nat => @lem7045132 n m)). Qed.
Lemma lem7045134 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045135 (m : nat) : (term46 m) = (term46 m).
Proof. exact (MK_COMB (@lem7045134) (@lem7045133 m)). Qed.
Lemma lem7045136 : term47 = term47.
Proof. exact (fun_ext (fun m : nat => @lem7045135 m)). Qed.
Lemma lem7045137 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045138 : term48 = term48.
Proof. exact (MK_COMB (@lem7045137) (@lem7045136)). Qed.
Lemma lem7045139 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7045140 : term21 = term21.
Proof. exact (MK_COMB (@lem7045139) (@lem7045138)). Qed.
Lemma lem7045141 : term23 = term23.
Proof. exact (MK_COMB (@lem7045140) (@lem7045125)). Qed.
Lemma lem7045146 (m : nat) (n : nat) (f : nat -> nat) : (term49 m n f) = (term49 m n f).
Proof. exact (eq_refl (term49 m n f)). Qed.
Lemma lem7045147 (m : nat) (f : nat -> nat) : (term50 m f) = (term50 m f).
Proof. exact (fun_ext (fun n : nat => @lem7045146 m n f)). Qed.
Lemma lem7045148 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045149 (m : nat) (f : nat -> nat) : (term51 m f) = (term51 m f).
Proof. exact (MK_COMB (@lem7045148) (@lem7045147 m f)). Qed.
Lemma lem7045150 (f : nat -> nat) : (term52 f) = (term52 f).
Proof. exact (fun_ext (fun m : nat => @lem7045149 m f)). Qed.
Lemma lem7045151 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045152 (f : nat -> nat) : (term53 f) = (term53 f).
Proof. exact (MK_COMB (@lem7045151) (@lem7045150 f)). Qed.
Lemma lem7045153 : term54 = term54.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7045152 f)). Qed.
Lemma lem7045154 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7045155 : term8 = term8.
Proof. exact (MK_COMB (@lem7045154) (@lem7045153)). Qed.
Lemma lem7045156 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7045157 : term10 = term10.
Proof. exact (MK_COMB (@lem7045156) (@lem7045155)). Qed.
Lemma lem7045158 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7045159 : term24 = term24.
Proof. exact (MK_COMB (@lem7045158) (@lem7045157)). Qed.
Lemma lem7045160 : term25 = term25.
Proof. exact (MK_COMB (@lem7045159) (@lem7045141)). Qed.
Lemma lem7045253 : term11 = term25.
Proof. exact (TRANS (@lem7045077) (@lem7045160)). Qed.
Lemma lem7045254 : term25 = term11.
Proof. exact (SYM (@lem7045253)). Qed.
Lemma lem7045255 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem7045256 (h1 : term48) : term48.
Proof. exact (h1). Qed.
Lemma lem7045257 (h1 : term43) : term43.
Proof. exact (h1). Qed.
Lemma lem7045258 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem7045265 (m : nat) (n : nat) (f : nat -> nat) : (term55 m n f) = (term56 m n f).
Proof. exact (@lem17362 (Peano.lt n m) ((term26 m n f) = (NUMERAL 0))). Qed.
Lemma lem7045266 (P : nat -> Prop) : (term57 P) = (term58 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7045267 (m : nat) (f : nat -> nat) : (term59 m f) = (term60 m f).
Proof. exact (@lem7045266 (term50 m f)). Qed.
Lemma lem7045268 (m : nat) (n : nat) (f : nat -> nat) : (term61 m f n) = (term49 m n f).
Proof. exact (eq_refl (term61 m f n)). Qed.
Lemma lem7045269 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7045270 (m : nat) (n : nat) (f : nat -> nat) : (term62 m f n) = (term55 m n f).
Proof. exact (MK_COMB (@lem7045269) (@lem7045268 m n f)). Qed.
Lemma lem7045271 (m : nat) (n : nat) (f : nat -> nat) : (term62 m f n) = (term56 m n f).
Proof. exact (TRANS (@lem7045270 m n f) (@lem7045265 m n f)). Qed.
Lemma lem7045272 (m : nat) (f : nat -> nat) : (term63 m f) = (term64 m f).
Proof. exact (fun_ext (fun n : nat => @lem7045271 m n f)). Qed.
Lemma lem7045273 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7045274 (m : nat) (f : nat -> nat) : (term60 m f) = (term65 m f).
Proof. exact (MK_COMB (@lem7045273) (@lem7045272 m f)). Qed.
Lemma lem7045275 (m : nat) (f : nat -> nat) : (term59 m f) = (term65 m f).
Proof. exact (TRANS (@lem7045267 m f) (@lem7045274 m f)). Qed.
Lemma lem7045276 (P : nat -> Prop) : (term57 P) = (term58 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7045277 (f : nat -> nat) : (term66 f) = (term67 f).
Proof. exact (@lem7045276 (term52 f)). Qed.
Lemma lem7045278 (m : nat) (f : nat -> nat) : (term68 f m) = (term51 m f).
Proof. exact (eq_refl (term68 f m)). Qed.
Lemma lem7045279 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7045280 (m : nat) (f : nat -> nat) : (term69 f m) = (term59 m f).
Proof. exact (MK_COMB (@lem7045279) (@lem7045278 m f)). Qed.
Lemma lem7045281 (m : nat) (f : nat -> nat) : (term69 f m) = (term65 m f).
Proof. exact (TRANS (@lem7045280 m f) (@lem7045275 m f)). Qed.
Lemma lem7045282 (f : nat -> nat) : (term70 f) = (term71 f).
Proof. exact (fun_ext (fun m : nat => @lem7045281 m f)). Qed.
Lemma lem7045283 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7045284 (f : nat -> nat) : (term67 f) = (term72 f).
Proof. exact (MK_COMB (@lem7045283) (@lem7045282 f)). Qed.
Lemma lem7045285 (f : nat -> nat) : (term66 f) = (term72 f).
Proof. exact (TRANS (@lem7045277 f) (@lem7045284 f)). Qed.
Lemma lem7045286 (P : type1002) : (term73 P) = (term74 P).
Proof. exact (@lem18392 (nat -> nat) P). Qed.
Lemma lem7045287 : term10 = term75.
Proof. exact (@lem7045286 term54). Qed.
Lemma lem7045288 (f : nat -> nat) : (term76 f) = (term53 f).
Proof. exact (eq_refl (term76 f)). Qed.
Lemma lem7045289 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7045290 (f : nat -> nat) : (term77 f) = (term66 f).
Proof. exact (MK_COMB (@lem7045289) (@lem7045288 f)). Qed.
Lemma lem7045291 (f : nat -> nat) : (term77 f) = (term72 f).
Proof. exact (TRANS (@lem7045290 f) (@lem7045285 f)). Qed.
Lemma lem7045292 : term78 = term79.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7045291 f)). Qed.
Lemma lem7045293 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem7045294 : term75 = term80.
Proof. exact (MK_COMB (@lem7045293) (@lem7045292)). Qed.
Lemma lem7045355 : term10 = term80.
Proof. exact (TRANS (@lem7045287) (@lem7045294)). Qed.
Lemma lem7045356 (h1 : term10) : term80.
Proof. exact (EQ_MP (@lem7045355) (@lem7045255 h1)). Qed.
Lemma lem7045360 (m : nat) (n : nat) : (term81 m n) = (Peano.lt m n).
Proof. exact (@lem16933 (Peano.lt m n)). Qed.
Lemma lem7045362 (n : nat) (m : nat) : (Peano.le n m) = (Peano.le n m).
Proof. exact (eq_refl (Peano.le n m)). Qed.
Lemma lem7045363 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7045364 (m : nat) (n : nat) : (term82 m n) = (term83 m n).
Proof. exact (MK_COMB (@lem7045363) (@lem7045360 m n)). Qed.
Lemma lem7045365 (n : nat) (m : nat) : (term84 n m) = (term85 n m).
Proof. exact (MK_COMB (@lem7045364 m n) (@lem7045362 n m)). Qed.
Lemma lem7045370 (n : nat) (m : nat) : (term86 n m) = (term86 n m).
Proof. exact (eq_refl (term86 n m)). Qed.
Lemma lem7045371 (n : nat) (m : nat) : (term87 n m) = (term88 n m).
Proof. exact (MK_COMB (@lem7045370 n m) (@lem7045365 n m)). Qed.
Lemma lem7045372 (n : nat) (m : nat) : ((term44 m n) = (Peano.le n m)) = (term87 n m).
Proof. exact (@lem17784 (term44 m n) (Peano.le n m)). Qed.
Lemma lem7045373 (n : nat) (m : nat) : ((term44 m n) = (Peano.le n m)) = (term88 n m).
Proof. exact (TRANS (@lem7045372 n m) (@lem7045371 n m)). Qed.
Lemma lem7045374 (m : nat) : (term45 m) = (term89 m).
Proof. exact (fun_ext (fun n : nat => @lem7045373 n m)). Qed.
Lemma lem7045375 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045376 (m : nat) : (term46 m) = (term90 m).
Proof. exact (MK_COMB (@lem7045375) (@lem7045374 m)). Qed.
Lemma lem7045377 : term47 = term91.
Proof. exact (fun_ext (fun m : nat => @lem7045376 m)). Qed.
Lemma lem7045378 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045379 : term48 = term92.
Proof. exact (MK_COMB (@lem7045378) (@lem7045377)). Qed.
Lemma lem7045385 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term93 A P Q) = (term94 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7045386 (P : nat -> Prop) (Q : nat -> Prop) : (term95 P Q) = (term96 P Q).
Proof. exact (@lem7045385 nat P Q). Qed.
Lemma lem7045387 (m : nat) : (term97 m) = (term98 m).
Proof. exact (@lem7045386 (term99 m) (term100 m)). Qed.
Lemma lem7045388 (n : nat) (m : nat) : (term101 m n) = (term102 n m).
Proof. exact (eq_refl (term101 m n)). Qed.
Lemma lem7045389 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7045390 (n : nat) (m : nat) : (term103 m n) = (term86 n m).
Proof. exact (MK_COMB (@lem7045389) (@lem7045388 n m)). Qed.
Lemma lem7045391 (n : nat) (m : nat) : (term104 m n) = (term85 n m).
Proof. exact (eq_refl (term104 m n)). Qed.
Lemma lem7045392 (n : nat) (m : nat) : (term105 m n) = (term88 n m).
Proof. exact (MK_COMB (@lem7045390 n m) (@lem7045391 n m)). Qed.
Lemma lem7045393 (m : nat) : (term106 m) = (term89 m).
Proof. exact (fun_ext (fun n : nat => @lem7045392 n m)). Qed.
Lemma lem7045394 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045395 (m : nat) : (term97 m) = (term90 m).
Proof. exact (MK_COMB (@lem7045394) (@lem7045393 m)). Qed.
Lemma lem7045396 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7045397 (m : nat) : (term107 m) = (term108 m).
Proof. exact (MK_COMB (@lem7045396) (@lem7045395 m)). Qed.
Lemma lem7045398 (n : nat) (m : nat) : (term101 m n) = (term102 n m).
Proof. exact (eq_refl (term101 m n)). Qed.
Lemma lem7045399 (m : nat) : (term109 m) = (term99 m).
Proof. exact (fun_ext (fun n : nat => @lem7045398 n m)). Qed.
Lemma lem7045400 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045401 (m : nat) : (term110 m) = (term111 m).
Proof. exact (MK_COMB (@lem7045400) (@lem7045399 m)). Qed.
Lemma lem7045402 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7045403 (m : nat) : (term112 m) = (term113 m).
Proof. exact (MK_COMB (@lem7045402) (@lem7045401 m)). Qed.
Lemma lem7045404 (n : nat) (m : nat) : (term104 m n) = (term85 n m).
Proof. exact (eq_refl (term104 m n)). Qed.
Lemma lem7045405 (m : nat) : (term114 m) = (term100 m).
Proof. exact (fun_ext (fun n : nat => @lem7045404 n m)). Qed.
Lemma lem7045406 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045407 (m : nat) : (term115 m) = (term116 m).
Proof. exact (MK_COMB (@lem7045406) (@lem7045405 m)). Qed.
Lemma lem7045408 (m : nat) : (term98 m) = (term117 m).
Proof. exact (MK_COMB (@lem7045403 m) (@lem7045407 m)). Qed.
Lemma lem7045409 (m : nat) : ((term97 m) = (term98 m)) = ((term90 m) = (term117 m)).
Proof. exact (MK_COMB (@lem7045397 m) (@lem7045408 m)). Qed.
Lemma lem7045410 (m : nat) : (term90 m) = (term117 m).
Proof. exact (EQ_MP (@lem7045409 m) (@lem7045387 m)). Qed.
Lemma lem7045507 : term91 = term118.
Proof. exact (fun_ext (fun m : nat => @lem7045410 m)). Qed.
Lemma lem7045508 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045509 : term92 = term119.
Proof. exact (MK_COMB (@lem7045508) (@lem7045507)). Qed.
Lemma lem7045511 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term93 A P Q) = (term94 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7045512 (P : nat -> Prop) (Q : nat -> Prop) : (term95 P Q) = (term96 P Q).
Proof. exact (@lem7045511 nat P Q). Qed.
Lemma lem7045513 : term120 = term121.
Proof. exact (@lem7045512 term122 term123). Qed.
Lemma lem7045514 (m : nat) : (term124 m) = (term111 m).
Proof. exact (eq_refl (term124 m)). Qed.
Lemma lem7045515 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7045516 (m : nat) : (term125 m) = (term113 m).
Proof. exact (MK_COMB (@lem7045515) (@lem7045514 m)). Qed.
Lemma lem7045517 (m : nat) : (term126 m) = (term116 m).
Proof. exact (eq_refl (term126 m)). Qed.
Lemma lem7045518 (m : nat) : (term127 m) = (term117 m).
Proof. exact (MK_COMB (@lem7045516 m) (@lem7045517 m)). Qed.
Lemma lem7045519 : term128 = term118.
Proof. exact (fun_ext (fun m : nat => @lem7045518 m)). Qed.
Lemma lem7045520 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045521 : term120 = term119.
Proof. exact (MK_COMB (@lem7045520) (@lem7045519)). Qed.
Lemma lem7045522 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7045523 : term129 = term130.
Proof. exact (MK_COMB (@lem7045522) (@lem7045521)). Qed.
Lemma lem7045524 (m : nat) : (term124 m) = (term111 m).
Proof. exact (eq_refl (term124 m)). Qed.
Lemma lem7045525 : term131 = term122.
Proof. exact (fun_ext (fun m : nat => @lem7045524 m)). Qed.
Lemma lem7045526 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045527 : term132 = term133.
Proof. exact (MK_COMB (@lem7045526) (@lem7045525)). Qed.
Lemma lem7045528 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7045529 : term134 = term135.
Proof. exact (MK_COMB (@lem7045528) (@lem7045527)). Qed.
Lemma lem7045530 (m : nat) : (term126 m) = (term116 m).
Proof. exact (eq_refl (term126 m)). Qed.
Lemma lem7045531 : term136 = term123.
Proof. exact (fun_ext (fun m : nat => @lem7045530 m)). Qed.
Lemma lem7045532 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045533 : term137 = term138.
Proof. exact (MK_COMB (@lem7045532) (@lem7045531)). Qed.
Lemma lem7045534 : term121 = term139.
Proof. exact (MK_COMB (@lem7045529) (@lem7045533)). Qed.
Lemma lem7045535 : (term120 = term121) = (term119 = term139).
Proof. exact (MK_COMB (@lem7045523) (@lem7045534)). Qed.
Lemma lem7045536 : term119 = term139.
Proof. exact (EQ_MP (@lem7045535) (@lem7045513)). Qed.
Lemma lem7045643 : term92 = term139.
Proof. exact (TRANS (@lem7045509) (@lem7045536)). Qed.
Lemma lem7045644 : term48 = term139.
Proof. exact (TRANS (@lem7045379) (@lem7045643)). Qed.
Lemma lem7045645 (h1 : term48) : term139.
Proof. exact (EQ_MP (@lem7045644) (@lem7045256 h1)). Qed.
Lemma lem7045652 (m : nat) (n : nat) (p : nat) : (term140 m n p) = (term141 m n p).
Proof. exact (@lem17045 (Peano.le m n) (Peano.le n p)). Qed.
Lemma lem7045653 (m : nat) (p : nat) : (Peano.le m p) = (Peano.le m p).
Proof. exact (eq_refl (Peano.le m p)). Qed.
Lemma lem7045654 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7045655 (m : nat) (n : nat) (p : nat) : (term142 m n p) = (term143 m n p).
Proof. exact (MK_COMB (@lem7045654) (@lem7045652 m n p)). Qed.
Lemma lem7045656 (n : nat) (m : nat) (p : nat) : (term144 n m p) = (term145 n m p).
Proof. exact (MK_COMB (@lem7045655 m n p) (@lem7045653 m p)). Qed.
Lemma lem7045657 (n : nat) (m : nat) (p : nat) : (term37 n m p) = (term144 n m p).
Proof. exact (@lem17265 (term146 m n p) (Peano.le m p)). Qed.
Lemma lem7045658 (n : nat) (m : nat) (p : nat) : (term37 n m p) = (term145 n m p).
Proof. exact (TRANS (@lem7045657 n m p) (@lem7045656 n m p)). Qed.
Lemma lem7045659 (n : nat) (m : nat) : (term38 n m) = (term147 n m).
Proof. exact (fun_ext (fun p : nat => @lem7045658 n m p)). Qed.
Lemma lem7045660 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045661 (n : nat) (m : nat) : (term39 n m) = (term148 n m).
Proof. exact (MK_COMB (@lem7045660) (@lem7045659 n m)). Qed.
Lemma lem7045662 (m : nat) : (term40 m) = (term149 m).
Proof. exact (fun_ext (fun n : nat => @lem7045661 n m)). Qed.
Lemma lem7045663 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045664 (m : nat) : (term41 m) = (term150 m).
Proof. exact (MK_COMB (@lem7045663) (@lem7045662 m)). Qed.
Lemma lem7045665 : term42 = term151.
Proof. exact (fun_ext (fun m : nat => @lem7045664 m)). Qed.
Lemma lem7045666 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045727 : term43 = term152.
Proof. exact (MK_COMB (@lem7045666) (@lem7045665)). Qed.
Lemma lem7045728 (h1 : term43) : term152.
Proof. exact (EQ_MP (@lem7045727) (@lem7045257 h1)). Qed.
Lemma lem7045739 (m : nat) (n : nat) (f : nat -> nat) (i : nat) : (term153 m n f i) = (term154 m n f i).
Proof. exact (@lem17362 (term146 m i n) ((f i) = (NUMERAL 0))). Qed.
Lemma lem7045740 (P : nat -> Prop) : (term57 P) = (term58 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem7045741 (m : nat) (n : nat) (f : nat -> nat) : (term155 m n f) = (term156 m n f).
Proof. exact (@lem7045740 (term28 m n f)). Qed.
Lemma lem7045742 (m : nat) (n : nat) (f : nat -> nat) (i : nat) : (term157 m n f i) = (term27 m n f i).
Proof. exact (eq_refl (term157 m n f i)). Qed.
Lemma lem7045743 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7045744 (m : nat) (n : nat) (f : nat -> nat) (i : nat) : (term158 m n f i) = (term153 m n f i).
Proof. exact (MK_COMB (@lem7045743) (@lem7045742 m n f i)). Qed.
Lemma lem7045745 (m : nat) (n : nat) (f : nat -> nat) (i : nat) : (term158 m n f i) = (term154 m n f i).
Proof. exact (TRANS (@lem7045744 m n f i) (@lem7045739 m n f i)). Qed.
Lemma lem7045746 (m : nat) (n : nat) (f : nat -> nat) : (term159 m n f) = (term160 m n f).
Proof. exact (fun_ext (fun i : nat => @lem7045745 m n f i)). Qed.
Lemma lem7045747 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7045748 (m : nat) (n : nat) (f : nat -> nat) : (term156 m n f) = (term161 m n f).
Proof. exact (MK_COMB (@lem7045747) (@lem7045746 m n f)). Qed.
Lemma lem7045749 (m : nat) (n : nat) (f : nat -> nat) : (term155 m n f) = (term161 m n f).
Proof. exact (TRANS (@lem7045741 m n f) (@lem7045748 m n f)). Qed.
Lemma lem7045750 (m : nat) (n : nat) (f : nat -> nat) : ((term26 m n f) = (NUMERAL 0)) = ((term26 m n f) = (NUMERAL 0)).
Proof. exact (eq_refl ((term26 m n f) = (NUMERAL 0))). Qed.
Lemma lem7045751 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7045752 (m : nat) (n : nat) (f : nat -> nat) : (term162 m n f) = (term163 m n f).
Proof. exact (MK_COMB (@lem7045751) (@lem7045749 m n f)). Qed.
Lemma lem7045753 (m : nat) (n : nat) (f : nat -> nat) : (term164 m n f) = (term165 m n f).
Proof. exact (MK_COMB (@lem7045752 m n f) (@lem7045750 m n f)). Qed.
Lemma lem7045754 (m : nat) (n : nat) (f : nat -> nat) : (term31 m n f) = (term164 m n f).
Proof. exact (@lem17265 (term29 m n f) ((term26 m n f) = (NUMERAL 0))). Qed.
Lemma lem7045755 (m : nat) (n : nat) (f : nat -> nat) : (term31 m n f) = (term165 m n f).
Proof. exact (TRANS (@lem7045754 m n f) (@lem7045753 m n f)). Qed.
Lemma lem7045756 (m : nat) (f : nat -> nat) : (term32 m f) = (term166 m f).
Proof. exact (fun_ext (fun n : nat => @lem7045755 m n f)). Qed.
Lemma lem7045757 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045758 (m : nat) (f : nat -> nat) : (term33 m f) = (term167 m f).
Proof. exact (MK_COMB (@lem7045757) (@lem7045756 m f)). Qed.
Lemma lem7045759 (f : nat -> nat) : (term34 f) = (term168 f).
Proof. exact (fun_ext (fun m : nat => @lem7045758 m f)). Qed.
Lemma lem7045760 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045761 (f : nat -> nat) : (term35 f) = (term169 f).
Proof. exact (MK_COMB (@lem7045760) (@lem7045759 f)). Qed.
Lemma lem7045762 : term36 = term170.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7045761 f)). Qed.
Lemma lem7045763 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7045764 : term17 = term171.
Proof. exact (MK_COMB (@lem7045763) (@lem7045762)). Qed.
Lemma lem7045871 {A : Type'} (P : A -> Prop) (Q : Prop) : (term172 A P Q) = (term173 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7045872 (P : nat -> Prop) (Q : Prop) : (term174 P Q) = (term175 P Q).
Proof. exact (@lem7045871 nat P Q). Qed.
Lemma lem7045873 (m : nat) (n : nat) (f : nat -> nat) : (term176 m n f) = (term177 m n f).
Proof. exact (@lem7045872 (term160 m n f) ((term26 m n f) = (NUMERAL 0))). Qed.
Lemma lem7045874 (m : nat) (n : nat) (f : nat -> nat) (i : nat) : (term178 m n f i) = (term154 m n f i).
Proof. exact (eq_refl (term178 m n f i)). Qed.
Lemma lem7045875 (m : nat) (n : nat) (f : nat -> nat) : (term179 m n f) = (term160 m n f).
Proof. exact (fun_ext (fun i : nat => @lem7045874 m n f i)). Qed.
Lemma lem7045876 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7045877 (m : nat) (n : nat) (f : nat -> nat) : (term180 m n f) = (term161 m n f).
Proof. exact (MK_COMB (@lem7045876) (@lem7045875 m n f)). Qed.
Lemma lem7045878 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7045879 (m : nat) (n : nat) (f : nat -> nat) : (term181 m n f) = (term163 m n f).
Proof. exact (MK_COMB (@lem7045878) (@lem7045877 m n f)). Qed.
Lemma lem7045880 (m : nat) (n : nat) (f : nat -> nat) : ((term26 m n f) = (NUMERAL 0)) = ((term26 m n f) = (NUMERAL 0)).
Proof. exact (eq_refl ((term26 m n f) = (NUMERAL 0))). Qed.
Lemma lem7045881 (m : nat) (n : nat) (f : nat -> nat) : (term176 m n f) = (term165 m n f).
Proof. exact (MK_COMB (@lem7045879 m n f) (@lem7045880 m n f)). Qed.
Lemma lem7045882 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7045883 (m : nat) (n : nat) (f : nat -> nat) : (term182 m n f) = (term183 m n f).
Proof. exact (MK_COMB (@lem7045882) (@lem7045881 m n f)). Qed.
Lemma lem7045884 (m : nat) (n : nat) (f : nat -> nat) (i : nat) : (term178 m n f i) = (term154 m n f i).
Proof. exact (eq_refl (term178 m n f i)). Qed.
Lemma lem7045885 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7045886 (m : nat) (n : nat) (f : nat -> nat) (i : nat) : (term184 m n f i) = (term185 m n f i).
Proof. exact (MK_COMB (@lem7045885) (@lem7045884 m n f i)). Qed.
Lemma lem7045887 (m : nat) (n : nat) (f : nat -> nat) : ((term26 m n f) = (NUMERAL 0)) = ((term26 m n f) = (NUMERAL 0)).
Proof. exact (eq_refl ((term26 m n f) = (NUMERAL 0))). Qed.
Lemma lem7045888 (i : nat) (m : nat) (n : nat) (f : nat -> nat) : (term186 i m n f) = (term187 i m n f).
Proof. exact (MK_COMB (@lem7045886 m n f i) (@lem7045887 m n f)). Qed.
Lemma lem7045889 (m : nat) (n : nat) (f : nat -> nat) : (term188 m n f) = (term189 m n f).
Proof. exact (fun_ext (fun i : nat => @lem7045888 i m n f)). Qed.
Lemma lem7045890 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7045891 (m : nat) (n : nat) (f : nat -> nat) : (term177 m n f) = (term190 m n f).
Proof. exact (MK_COMB (@lem7045890) (@lem7045889 m n f)). Qed.
Lemma lem7045892 (m : nat) (n : nat) (f : nat -> nat) : ((term176 m n f) = (term177 m n f)) = ((term165 m n f) = (term190 m n f)).
Proof. exact (MK_COMB (@lem7045883 m n f) (@lem7045891 m n f)). Qed.
Lemma lem7045893 (m : nat) (n : nat) (f : nat -> nat) : (term165 m n f) = (term190 m n f).
Proof. exact (EQ_MP (@lem7045892 m n f) (@lem7045873 m n f)). Qed.
Lemma lem7045894 (m : nat) (f : nat -> nat) : (term166 m f) = (term191 m f).
Proof. exact (fun_ext (fun n : nat => @lem7045893 m n f)). Qed.
Lemma lem7045895 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045896 (m : nat) (f : nat -> nat) : (term167 m f) = (term192 m f).
Proof. exact (MK_COMB (@lem7045895) (@lem7045894 m f)). Qed.
Lemma lem7045898 {A B : Type'} (P : type1413 A B) : (term193 A B P) = (term194 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7045899 (P : type1605) : (term195 P) = (term196 P).
Proof. exact (@lem7045898 nat nat P). Qed.
Lemma lem7045900 (m : nat) (f : nat -> nat) : (term197 m f) = (term198 m f).
Proof. exact (@lem7045899 (term199 m f)). Qed.
Lemma lem7045901 (m : nat) (n : nat) (f : nat -> nat) : (term200 m f n) = (term189 m n f).
Proof. exact (eq_refl (term200 m f n)). Qed.
Lemma lem7045902 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7045903 (m : nat) (n : nat) (f : nat -> nat) (i : nat) : (term201 m f n i) = (term202 m n f i).
Proof. exact (MK_COMB (@lem7045901 m n f) (@lem7045902 i)). Qed.
Lemma lem7045904 (i : nat) (m : nat) (n : nat) (f : nat -> nat) : (term202 m n f i) = (term187 i m n f).
Proof. exact (eq_refl (term202 m n f i)). Qed.
Lemma lem7045905 (i : nat) (m : nat) (n : nat) (f : nat -> nat) : (term201 m f n i) = (term187 i m n f).
Proof. exact (TRANS (@lem7045903 m n f i) (@lem7045904 i m n f)). Qed.
Lemma lem7045906 (m : nat) (n : nat) (f : nat -> nat) : (term203 m f n) = (term189 m n f).
Proof. exact (fun_ext (fun i : nat => @lem7045905 i m n f)). Qed.
Lemma lem7045907 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7045908 (m : nat) (n : nat) (f : nat -> nat) : (term204 m f n) = (term190 m n f).
Proof. exact (MK_COMB (@lem7045907) (@lem7045906 m n f)). Qed.
Lemma lem7045909 (m : nat) (f : nat -> nat) : (term205 m f) = (term191 m f).
Proof. exact (fun_ext (fun n : nat => @lem7045908 m n f)). Qed.
Lemma lem7045910 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045911 (m : nat) (f : nat -> nat) : (term197 m f) = (term192 m f).
Proof. exact (MK_COMB (@lem7045910) (@lem7045909 m f)). Qed.
Lemma lem7045912 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7045913 (m : nat) (f : nat -> nat) : (term206 m f) = (term207 m f).
Proof. exact (MK_COMB (@lem7045912) (@lem7045911 m f)). Qed.
Lemma lem7045914 (m : nat) (n : nat) (f : nat -> nat) : (term200 m f n) = (term189 m n f).
Proof. exact (eq_refl (term200 m f n)). Qed.
Lemma lem7045915 (i : nat -> nat) (n : nat) : (i n) = (i n).
Proof. exact (eq_refl (i n)). Qed.
Lemma lem7045916 (m : nat) (f : nat -> nat) (i : nat -> nat) (n : nat) : (term208 m f i n) = (term209 m f i n).
Proof. exact (MK_COMB (@lem7045914 m n f) (@lem7045915 i n)). Qed.
Lemma lem7045917 (i : nat -> nat) (m : nat) (n : nat) (f : nat -> nat) : (term209 m f i n) = (term210 i m n f).
Proof. exact (eq_refl (term209 m f i n)). Qed.
Lemma lem7045918 (i : nat -> nat) (m : nat) (n : nat) (f : nat -> nat) : (term208 m f i n) = (term210 i m n f).
Proof. exact (TRANS (@lem7045916 m f i n) (@lem7045917 i m n f)). Qed.
Lemma lem7045919 (i : nat -> nat) (m : nat) (f : nat -> nat) : (term211 m f i) = (term212 i m f).
Proof. exact (fun_ext (fun n : nat => @lem7045918 i m n f)). Qed.
Lemma lem7045920 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045921 (i : nat -> nat) (m : nat) (f : nat -> nat) : (term213 m f i) = (term214 i m f).
Proof. exact (MK_COMB (@lem7045920) (@lem7045919 i m f)). Qed.
Lemma lem7045922 (m : nat) (f : nat -> nat) : (term215 m f) = (term216 m f).
Proof. exact (fun_ext (fun i : nat -> nat => @lem7045921 i m f)). Qed.
Lemma lem7045923 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem7045924 (m : nat) (f : nat -> nat) : (term198 m f) = (term217 m f).
Proof. exact (MK_COMB (@lem7045923) (@lem7045922 m f)). Qed.
Lemma lem7045925 (m : nat) (f : nat -> nat) : ((term197 m f) = (term198 m f)) = ((term192 m f) = (term217 m f)).
Proof. exact (MK_COMB (@lem7045913 m f) (@lem7045924 m f)). Qed.
Lemma lem7045926 (m : nat) (f : nat -> nat) : (term192 m f) = (term217 m f).
Proof. exact (EQ_MP (@lem7045925 m f) (@lem7045900 m f)). Qed.
Lemma lem7045927 (m : nat) (f : nat -> nat) : (term167 m f) = (term217 m f).
Proof. exact (TRANS (@lem7045896 m f) (@lem7045926 m f)). Qed.
Lemma lem7045928 (f : nat -> nat) : (term168 f) = (term218 f).
Proof. exact (fun_ext (fun m : nat => @lem7045927 m f)). Qed.
Lemma lem7045929 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045930 (f : nat -> nat) : (term169 f) = (term219 f).
Proof. exact (MK_COMB (@lem7045929) (@lem7045928 f)). Qed.
Lemma lem7045932 {A B : Type'} (P : type1413 A B) : (term193 A B P) = (term194 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7045933 (P : type1586) : (term220 P) = (term221 P).
Proof. exact (@lem7045932 nat (nat -> nat) P). Qed.
Lemma lem7045934 (f : nat -> nat) : (term222 f) = (term223 f).
Proof. exact (@lem7045933 (term224 f)). Qed.
Lemma lem7045935 (m : nat) (f : nat -> nat) : (term225 f m) = (term216 m f).
Proof. exact (eq_refl (term225 f m)). Qed.
Lemma lem7045936 (i : nat -> nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7045937 (m : nat) (f : nat -> nat) (i : nat -> nat) : (term226 f m i) = (term227 m f i).
Proof. exact (MK_COMB (@lem7045935 m f) (@lem7045936 i)). Qed.
Lemma lem7045938 (i : nat -> nat) (m : nat) (f : nat -> nat) : (term227 m f i) = (term214 i m f).
Proof. exact (eq_refl (term227 m f i)). Qed.
Lemma lem7045939 (i : nat -> nat) (m : nat) (f : nat -> nat) : (term226 f m i) = (term214 i m f).
Proof. exact (TRANS (@lem7045937 m f i) (@lem7045938 i m f)). Qed.
Lemma lem7045940 (m : nat) (f : nat -> nat) : (term228 f m) = (term216 m f).
Proof. exact (fun_ext (fun i : nat -> nat => @lem7045939 i m f)). Qed.
Lemma lem7045941 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem7045942 (m : nat) (f : nat -> nat) : (term229 f m) = (term217 m f).
Proof. exact (MK_COMB (@lem7045941) (@lem7045940 m f)). Qed.
Lemma lem7045943 (f : nat -> nat) : (term230 f) = (term218 f).
Proof. exact (fun_ext (fun m : nat => @lem7045942 m f)). Qed.
Lemma lem7045944 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045945 (f : nat -> nat) : (term222 f) = (term219 f).
Proof. exact (MK_COMB (@lem7045944) (@lem7045943 f)). Qed.
Lemma lem7045946 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7045947 (f : nat -> nat) : (term231 f) = (term232 f).
Proof. exact (MK_COMB (@lem7045946) (@lem7045945 f)). Qed.
Lemma lem7045948 (m : nat) (f : nat -> nat) : (term225 f m) = (term216 m f).
Proof. exact (eq_refl (term225 f m)). Qed.
Lemma lem7045949 (i : type1606) (m : nat) : (i m) = (i m).
Proof. exact (eq_refl (i m)). Qed.
Lemma lem7045950 (f : nat -> nat) (i : type1606) (m : nat) : (term233 f i m) = (term234 f i m).
Proof. exact (MK_COMB (@lem7045948 m f) (@lem7045949 i m)). Qed.
Lemma lem7045951 (i : type1606) (m : nat) (f : nat -> nat) : (term234 f i m) = (term235 i m f).
Proof. exact (eq_refl (term234 f i m)). Qed.
Lemma lem7045952 (i : type1606) (m : nat) (f : nat -> nat) : (term233 f i m) = (term235 i m f).
Proof. exact (TRANS (@lem7045950 f i m) (@lem7045951 i m f)). Qed.
Lemma lem7045953 (i : type1606) (f : nat -> nat) : (term236 f i) = (term237 i f).
Proof. exact (fun_ext (fun m : nat => @lem7045952 i m f)). Qed.
Lemma lem7045954 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7045955 (i : type1606) (f : nat -> nat) : (term238 f i) = (term239 i f).
Proof. exact (MK_COMB (@lem7045954) (@lem7045953 i f)). Qed.
Lemma lem7045956 (f : nat -> nat) : (term240 f) = (term241 f).
Proof. exact (fun_ext (fun i : type1606 => @lem7045955 i f)). Qed.
Lemma lem7045957 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem7045958 (f : nat -> nat) : (term223 f) = (term242 f).
Proof. exact (MK_COMB (@lem7045957) (@lem7045956 f)). Qed.
Lemma lem7045959 (f : nat -> nat) : ((term222 f) = (term223 f)) = ((term219 f) = (term242 f)).
Proof. exact (MK_COMB (@lem7045947 f) (@lem7045958 f)). Qed.
Lemma lem7045960 (f : nat -> nat) : (term219 f) = (term242 f).
Proof. exact (EQ_MP (@lem7045959 f) (@lem7045934 f)). Qed.
Lemma lem7045961 (f : nat -> nat) : (term169 f) = (term242 f).
Proof. exact (TRANS (@lem7045930 f) (@lem7045960 f)). Qed.
Lemma lem7045962 : term170 = term243.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7045961 f)). Qed.
Lemma lem7045963 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7045964 : term171 = term244.
Proof. exact (MK_COMB (@lem7045963) (@lem7045962)). Qed.
Lemma lem7045966 {A B : Type'} (P : type1413 A B) : (term193 A B P) = (term194 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7045967 (P : type997) : (term245 P) = (term246 P).
Proof. exact (@lem7045966 (nat -> nat) type1606 P). Qed.
Lemma lem7045968 : term247 = term248.
Proof. exact (@lem7045967 term249). Qed.
Lemma lem7045969 (f : nat -> nat) : (term250 f) = (term241 f).
Proof. exact (eq_refl (term250 f)). Qed.
Lemma lem7045970 (i : type1606) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7045971 (f : nat -> nat) (i : type1606) : (term251 f i) = (term252 f i).
Proof. exact (MK_COMB (@lem7045969 f) (@lem7045970 i)). Qed.
Lemma lem7045972 (i : type1606) (f : nat -> nat) : (term252 f i) = (term239 i f).
Proof. exact (eq_refl (term252 f i)). Qed.
Lemma lem7045973 (i : type1606) (f : nat -> nat) : (term251 f i) = (term239 i f).
Proof. exact (TRANS (@lem7045971 f i) (@lem7045972 i f)). Qed.
Lemma lem7045974 (f : nat -> nat) : (term253 f) = (term241 f).
Proof. exact (fun_ext (fun i : type1606 => @lem7045973 i f)). Qed.
Lemma lem7045975 : (@ex (nat -> nat -> nat)) = (@ex (nat -> nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat))). Qed.
Lemma lem7045976 (f : nat -> nat) : (term254 f) = (term242 f).
Proof. exact (MK_COMB (@lem7045975) (@lem7045974 f)). Qed.
Lemma lem7045977 : term255 = term243.
Proof. exact (fun_ext (fun f : nat -> nat => @lem7045976 f)). Qed.
Lemma lem7045978 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7045979 : term247 = term244.
Proof. exact (MK_COMB (@lem7045978) (@lem7045977)). Qed.
Lemma lem7045980 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7045981 : term256 = term257.
Proof. exact (MK_COMB (@lem7045980) (@lem7045979)). Qed.
Lemma lem7045982 (f : nat -> nat) : (term250 f) = (term241 f).
Proof. exact (eq_refl (term250 f)). Qed.
Lemma lem7045983 (i : type1000) (f : nat -> nat) : (i f) = (i f).
Proof. exact (eq_refl (i f)). Qed.
Lemma lem7045984 (i : type1000) (f : nat -> nat) : (term258 i f) = (term259 i f).
Proof. exact (MK_COMB (@lem7045982 f) (@lem7045983 i f)). Qed.
Lemma lem7045985 (i : type1000) (f : nat -> nat) : (term259 i f) = (term260 i f).
Proof. exact (eq_refl (term259 i f)). Qed.
Lemma lem7045986 (i : type1000) (f : nat -> nat) : (term258 i f) = (term260 i f).
Proof. exact (TRANS (@lem7045984 i f) (@lem7045985 i f)). Qed.
Lemma lem7045987 (i : type1000) : (term261 i) = (term262 i).
Proof. exact (fun_ext (fun f : nat -> nat => @lem7045986 i f)). Qed.
Lemma lem7045988 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7045989 (i : type1000) : (term263 i) = (term264 i).
Proof. exact (MK_COMB (@lem7045988) (@lem7045987 i)). Qed.
Lemma lem7045990 : term265 = term266.
Proof. exact (fun_ext (fun i : type1000 => @lem7045989 i)). Qed.
Lemma lem7045991 : (@ex ((nat -> nat) -> nat -> nat -> nat)) = (@ex ((nat -> nat) -> nat -> nat -> nat)).
Proof. exact (eq_refl (@ex ((nat -> nat) -> nat -> nat -> nat))). Qed.
Lemma lem7045992 : term248 = term267.
Proof. exact (MK_COMB (@lem7045991) (@lem7045990)). Qed.
Lemma lem7045993 : (term247 = term248) = (term244 = term267).
Proof. exact (MK_COMB (@lem7045981) (@lem7045992)). Qed.
Lemma lem7045994 : term244 = term267.
Proof. exact (EQ_MP (@lem7045993) (@lem7045968)). Qed.
Lemma lem7045996 : term171 = term267.
Proof. exact (TRANS (@lem7045964) (@lem7045994)). Qed.
Lemma lem7045997 : term17 = term267.
Proof. exact (TRANS (@lem7045764) (@lem7045996)). Qed.
Lemma lem7045998 (h1 : term17) : term267.
Proof. exact (EQ_MP (@lem7045997) (@lem7045258 h1)). Qed.
Lemma lem7045999 (i : type1000) (h1 : term264 i) : term264 i.
Proof. exact (h1). Qed.
Lemma lem7046000 (f : nat -> nat) (h1 : term72 f) : term72 f.
Proof. exact (h1). Qed.
Lemma lem7046001 (m : nat) (f : nat -> nat) (h1 : term65 m f) : term65 m f.
Proof. exact (h1). Qed.
Lemma lem7046002 (m : nat) (n : nat) (f : nat -> nat) (h1 : term56 m n f) : term56 m n f.
Proof. exact (h1). Qed.
Lemma lem7046009 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046010 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7046009 nat (nat -> Prop) f x). Qed.
Lemma lem7046011 (n : nat) : (Peano.le n) = (@I (nat -> nat -> Prop) Peano.le n).
Proof. exact (@lem7046010 Peano.le n). Qed.
Lemma lem7046012 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem7046013 (n : nat) (m : nat) : (Peano.le n m) = (@I (nat -> nat -> Prop) Peano.le n m).
Proof. exact (MK_COMB (@lem7046011 n) (@lem7046012 m)). Qed.
Lemma lem7046015 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046016 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7046015 nat Prop f x). Qed.
Lemma lem7046017 (n : nat) (m : nat) : (@I (nat -> nat -> Prop) Peano.le n m) = (term268 n m).
Proof. exact (@lem7046016 (@I (nat -> nat -> Prop) Peano.le n) m). Qed.
Lemma lem7046019 (n : nat) (m : nat) : (Peano.le n m) = (term268 n m).
Proof. exact (TRANS (@lem7046013 n m) (@lem7046017 n m)). Qed.
Lemma lem7046026 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046027 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7046026 nat (nat -> Prop) f x). Qed.
Lemma lem7046028 (m : nat) : (Peano.lt m) = (@I (nat -> nat -> Prop) Peano.lt m).
Proof. exact (@lem7046027 Peano.lt m). Qed.
Lemma lem7046029 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7046030 (m : nat) (n : nat) : (Peano.lt m n) = (@I (nat -> nat -> Prop) Peano.lt m n).
Proof. exact (MK_COMB (@lem7046028 m) (@lem7046029 n)). Qed.
Lemma lem7046032 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046033 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7046032 nat Prop f x). Qed.
Lemma lem7046034 (m : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.lt m n) = (term269 m n).
Proof. exact (@lem7046033 (@I (nat -> nat -> Prop) Peano.lt m) n). Qed.
Lemma lem7046036 (m : nat) (n : nat) : (Peano.lt m n) = (term269 m n).
Proof. exact (TRANS (@lem7046030 m n) (@lem7046034 m n)). Qed.
Lemma lem7046037 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7046038 (m : nat) (n : nat) : (term83 m n) = (term270 m n).
Proof. exact (MK_COMB (@lem7046037) (@lem7046036 m n)). Qed.
Lemma lem7046039 (n : nat) (m : nat) : (term85 n m) = (term271 n m).
Proof. exact (MK_COMB (@lem7046038 m n) (@lem7046019 n m)). Qed.
Lemma lem7046040 (m : nat) : (term100 m) = (term272 m).
Proof. exact (fun_ext (fun n : nat => @lem7046039 n m)). Qed.
Lemma lem7046041 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7046042 (m : nat) : (term116 m) = (term273 m).
Proof. exact (MK_COMB (@lem7046041) (@lem7046040 m)). Qed.
Lemma lem7046043 : term123 = term274.
Proof. exact (fun_ext (fun m : nat => @lem7046042 m)). Qed.
Lemma lem7046044 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7046045 : term138 = term275.
Proof. exact (MK_COMB (@lem7046044) (@lem7046043)). Qed.
Lemma lem7046046 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7046053 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046054 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7046053 nat (nat -> Prop) f x). Qed.
Lemma lem7046055 (n : nat) : (Peano.le n) = (@I (nat -> nat -> Prop) Peano.le n).
Proof. exact (@lem7046054 Peano.le n). Qed.
Lemma lem7046056 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem7046057 (n : nat) (m : nat) : (Peano.le n m) = (@I (nat -> nat -> Prop) Peano.le n m).
Proof. exact (MK_COMB (@lem7046055 n) (@lem7046056 m)). Qed.
Lemma lem7046059 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046060 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7046059 nat Prop f x). Qed.
Lemma lem7046061 (n : nat) (m : nat) : (@I (nat -> nat -> Prop) Peano.le n m) = (term268 n m).
Proof. exact (@lem7046060 (@I (nat -> nat -> Prop) Peano.le n) m). Qed.
Lemma lem7046063 (n : nat) (m : nat) : (Peano.le n m) = (term268 n m).
Proof. exact (TRANS (@lem7046057 n m) (@lem7046061 n m)). Qed.
Lemma lem7046064 (n : nat) (m : nat) : (term276 n m) = (term277 n m).
Proof. exact (MK_COMB (@lem7046046) (@lem7046063 n m)). Qed.
Lemma lem7046065 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7046072 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046073 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7046072 nat (nat -> Prop) f x). Qed.
Lemma lem7046074 (m : nat) : (Peano.lt m) = (@I (nat -> nat -> Prop) Peano.lt m).
Proof. exact (@lem7046073 Peano.lt m). Qed.
Lemma lem7046075 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7046076 (m : nat) (n : nat) : (Peano.lt m n) = (@I (nat -> nat -> Prop) Peano.lt m n).
Proof. exact (MK_COMB (@lem7046074 m) (@lem7046075 n)). Qed.
Lemma lem7046078 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046079 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7046078 nat Prop f x). Qed.
Lemma lem7046080 (m : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.lt m n) = (term269 m n).
Proof. exact (@lem7046079 (@I (nat -> nat -> Prop) Peano.lt m) n). Qed.
Lemma lem7046082 (m : nat) (n : nat) : (Peano.lt m n) = (term269 m n).
Proof. exact (TRANS (@lem7046076 m n) (@lem7046080 m n)). Qed.
Lemma lem7046083 (m : nat) (n : nat) : (term44 m n) = (term278 m n).
Proof. exact (MK_COMB (@lem7046065) (@lem7046082 m n)). Qed.
Lemma lem7046084 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7046085 (m : nat) (n : nat) : (term279 m n) = (term280 m n).
Proof. exact (MK_COMB (@lem7046084) (@lem7046083 m n)). Qed.
Lemma lem7046086 (n : nat) (m : nat) : (term102 n m) = (term281 n m).
Proof. exact (MK_COMB (@lem7046085 m n) (@lem7046064 n m)). Qed.
Lemma lem7046087 (m : nat) : (term99 m) = (term282 m).
Proof. exact (fun_ext (fun n : nat => @lem7046086 n m)). Qed.
Lemma lem7046088 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7046089 (m : nat) : (term111 m) = (term283 m).
Proof. exact (MK_COMB (@lem7046088) (@lem7046087 m)). Qed.
Lemma lem7046090 : term122 = term284.
Proof. exact (fun_ext (fun m : nat => @lem7046089 m)). Qed.
Lemma lem7046091 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7046092 : term133 = term285.
Proof. exact (MK_COMB (@lem7046091) (@lem7046090)). Qed.
Lemma lem7046093 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7046094 : term135 = term286.
Proof. exact (MK_COMB (@lem7046093) (@lem7046092)). Qed.
Lemma lem7046095 : term139 = term287.
Proof. exact (MK_COMB (@lem7046094) (@lem7046045)). Qed.
Lemma lem7046096 (h1 : term48) : term287.
Proof. exact (EQ_MP (@lem7046095) (@lem7045645 h1)). Qed.
Lemma lem7046103 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046104 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7046103 nat (nat -> Prop) f x). Qed.
Lemma lem7046105 (m : nat) : (Peano.le m) = (@I (nat -> nat -> Prop) Peano.le m).
Proof. exact (@lem7046104 Peano.le m). Qed.
Lemma lem7046106 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem7046107 (m : nat) (p : nat) : (Peano.le m p) = (@I (nat -> nat -> Prop) Peano.le m p).
Proof. exact (MK_COMB (@lem7046105 m) (@lem7046106 p)). Qed.
Lemma lem7046109 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046110 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7046109 nat Prop f x). Qed.
Lemma lem7046111 (m : nat) (p : nat) : (@I (nat -> nat -> Prop) Peano.le m p) = (term268 m p).
Proof. exact (@lem7046110 (@I (nat -> nat -> Prop) Peano.le m) p). Qed.
Lemma lem7046113 (m : nat) (p : nat) : (Peano.le m p) = (term268 m p).
Proof. exact (TRANS (@lem7046107 m p) (@lem7046111 m p)). Qed.
Lemma lem7046114 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7046121 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046122 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7046121 nat (nat -> Prop) f x). Qed.
Lemma lem7046123 (n : nat) : (Peano.le n) = (@I (nat -> nat -> Prop) Peano.le n).
Proof. exact (@lem7046122 Peano.le n). Qed.
Lemma lem7046124 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem7046125 (n : nat) (p : nat) : (Peano.le n p) = (@I (nat -> nat -> Prop) Peano.le n p).
Proof. exact (MK_COMB (@lem7046123 n) (@lem7046124 p)). Qed.
Lemma lem7046127 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046128 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7046127 nat Prop f x). Qed.
Lemma lem7046129 (n : nat) (p : nat) : (@I (nat -> nat -> Prop) Peano.le n p) = (term268 n p).
Proof. exact (@lem7046128 (@I (nat -> nat -> Prop) Peano.le n) p). Qed.
Lemma lem7046131 (n : nat) (p : nat) : (Peano.le n p) = (term268 n p).
Proof. exact (TRANS (@lem7046125 n p) (@lem7046129 n p)). Qed.
Lemma lem7046132 (n : nat) (p : nat) : (term276 n p) = (term277 n p).
Proof. exact (MK_COMB (@lem7046114) (@lem7046131 n p)). Qed.
Lemma lem7046133 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7046140 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046141 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7046140 nat (nat -> Prop) f x). Qed.
Lemma lem7046142 (m : nat) : (Peano.le m) = (@I (nat -> nat -> Prop) Peano.le m).
Proof. exact (@lem7046141 Peano.le m). Qed.
Lemma lem7046143 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7046144 (m : nat) (n : nat) : (Peano.le m n) = (@I (nat -> nat -> Prop) Peano.le m n).
Proof. exact (MK_COMB (@lem7046142 m) (@lem7046143 n)). Qed.
Lemma lem7046146 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046147 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7046146 nat Prop f x). Qed.
Lemma lem7046148 (m : nat) (n : nat) : (@I (nat -> nat -> Prop) Peano.le m n) = (term268 m n).
Proof. exact (@lem7046147 (@I (nat -> nat -> Prop) Peano.le m) n). Qed.
Lemma lem7046150 (m : nat) (n : nat) : (Peano.le m n) = (term268 m n).
Proof. exact (TRANS (@lem7046144 m n) (@lem7046148 m n)). Qed.
Lemma lem7046151 (m : nat) (n : nat) : (term276 m n) = (term277 m n).
Proof. exact (MK_COMB (@lem7046133) (@lem7046150 m n)). Qed.
Lemma lem7046152 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7046153 (m : nat) (n : nat) : (term288 m n) = (term289 m n).
Proof. exact (MK_COMB (@lem7046152) (@lem7046151 m n)). Qed.
Lemma lem7046154 (m : nat) (n : nat) (p : nat) : (term141 m n p) = (term290 m n p).
Proof. exact (MK_COMB (@lem7046153 m n) (@lem7046132 n p)). Qed.
Lemma lem7046155 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7046156 (m : nat) (n : nat) (p : nat) : (term143 m n p) = (term291 m n p).
Proof. exact (MK_COMB (@lem7046155) (@lem7046154 m n p)). Qed.
Lemma lem7046157 (n : nat) (m : nat) (p : nat) : (term145 n m p) = (term292 n m p).
Proof. exact (MK_COMB (@lem7046156 m n p) (@lem7046113 m p)). Qed.
Lemma lem7046158 (n : nat) (m : nat) : (term147 n m) = (term293 n m).
Proof. exact (fun_ext (fun p : nat => @lem7046157 n m p)). Qed.
Lemma lem7046159 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7046160 (n : nat) (m : nat) : (term148 n m) = (term294 n m).
Proof. exact (MK_COMB (@lem7046159) (@lem7046158 n m)). Qed.
Lemma lem7046161 (m : nat) : (term149 m) = (term295 m).
Proof. exact (fun_ext (fun n : nat => @lem7046160 n m)). Qed.
Lemma lem7046162 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7046163 (m : nat) : (term150 m) = (term296 m).
Proof. exact (MK_COMB (@lem7046162) (@lem7046161 m)). Qed.
Lemma lem7046164 : term151 = term297.
Proof. exact (fun_ext (fun m : nat => @lem7046163 m)). Qed.
Lemma lem7046165 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7046166 : term152 = term298.
Proof. exact (MK_COMB (@lem7046165) (@lem7046164)). Qed.
Lemma lem7046167 (h1 : term43) : term298.
Proof. exact (EQ_MP (@lem7046166) (@lem7045728 h1)). Qed.
Lemma lem7046168 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7046169 : (@nsum nat) = (@nsum nat).
Proof. exact (eq_refl (@nsum nat)). Qed.
Lemma lem7046176 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046177 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem7046176 nat type1605 f x). Qed.
Lemma lem7046178 (m : nat) : (dotdot m) = (@I (nat -> nat -> nat -> Prop) dotdot m).
Proof. exact (@lem7046177 dotdot m). Qed.
Lemma lem7046179 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7046180 (m : nat) (n : nat) : (dotdot m n) = (@I (nat -> nat -> nat -> Prop) dotdot m n).
Proof. exact (MK_COMB (@lem7046178 m) (@lem7046179 n)). Qed.
Lemma lem7046182 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046183 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7046182 nat (nat -> Prop) f x). Qed.
Lemma lem7046184 (m : nat) (n : nat) : (@I (nat -> nat -> nat -> Prop) dotdot m n) = (term299 m n).
Proof. exact (@lem7046183 (@I (nat -> nat -> nat -> Prop) dotdot m) n). Qed.
Lemma lem7046186 (m : nat) (n : nat) : (dotdot m n) = (term299 m n).
Proof. exact (TRANS (@lem7046180 m n) (@lem7046184 m n)). Qed.
Lemma lem7046187 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7046188 (m : nat) (n : nat) : (term300 m n) = (term301 m n).
Proof. exact (MK_COMB (@lem7046169) (@lem7046186 m n)). Qed.
Lemma lem7046189 (m : nat) (n : nat) (f : nat -> nat) : (term26 m n f) = (term302 m n f).
Proof. exact (MK_COMB (@lem7046188 m n) (@lem7046187 f)). Qed.
Lemma lem7046191 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046192 (f : type987) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> (nat -> nat) -> nat) f x).
Proof. exact (@lem7046191 (nat -> Prop) type1003 f x). Qed.
Lemma lem7046193 (m : nat) (n : nat) : (term301 m n) = (term303 m n).
Proof. exact (@lem7046192 (@nsum nat) (term299 m n)). Qed.
Lemma lem7046194 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7046195 (m : nat) (n : nat) (f : nat -> nat) : (term302 m n f) = (term304 m n f).
Proof. exact (MK_COMB (@lem7046193 m n) (@lem7046194 f)). Qed.
Lemma lem7046197 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046198 (f : type1003) (x : nat -> nat) : (f x) = (@I ((nat -> nat) -> nat) f x).
Proof. exact (@lem7046197 (nat -> nat) nat f x). Qed.
Lemma lem7046199 (m : nat) (n : nat) (f : nat -> nat) : (term304 m n f) = (term305 m n f).
Proof. exact (@lem7046198 (term303 m n) f). Qed.
Lemma lem7046200 (m : nat) (n : nat) (f : nat -> nat) : (term302 m n f) = (term305 m n f).
Proof. exact (TRANS (@lem7046195 m n f) (@lem7046199 m n f)). Qed.
Lemma lem7046201 (m : nat) (n : nat) (f : nat -> nat) : (term26 m n f) = (term305 m n f).
Proof. exact (TRANS (@lem7046189 m n f) (@lem7046200 m n f)). Qed.
Lemma lem7046206 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046207 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7046206 nat nat f x). Qed.
Lemma lem7046209 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7046207 NUMERAL 0). Qed.
Lemma lem7046210 (m : nat) (n : nat) (f : nat -> nat) : (term306 m n f) = (term307 m n f).
Proof. exact (MK_COMB (@lem7046168) (@lem7046201 m n f)). Qed.
Lemma lem7046211 (m : nat) (n : nat) (f : nat -> nat) : ((term26 m n f) = (NUMERAL 0)) = ((term305 m n f) = (@I (nat -> nat) NUMERAL 0)).
Proof. exact (MK_COMB (@lem7046210 m n f) (@lem7046209)). Qed.
Lemma lem7046212 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7046213 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7046214 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7046223 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046224 (f : type1000) (x : nat -> nat) : (f x) = (@I ((nat -> nat) -> nat -> nat -> nat) f x).
Proof. exact (@lem7046223 (nat -> nat) type1606 f x). Qed.
Lemma lem7046225 (i : type1000) (f : nat -> nat) : (i f) = (@I ((nat -> nat) -> nat -> nat -> nat) i f).
Proof. exact (@lem7046224 i f). Qed.
Lemma lem7046226 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem7046227 (i : type1000) (f : nat -> nat) (m : nat) : (i f m) = (@I ((nat -> nat) -> nat -> nat -> nat) i f m).
Proof. exact (MK_COMB (@lem7046225 i f) (@lem7046226 m)). Qed.
Lemma lem7046229 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046230 (f : type1606) (x : nat) : (f x) = (@I (nat -> nat -> nat) f x).
Proof. exact (@lem7046229 nat (nat -> nat) f x). Qed.
Lemma lem7046231 (i : type1000) (f : nat -> nat) (m : nat) : (@I ((nat -> nat) -> nat -> nat -> nat) i f m) = (term308 i f m).
Proof. exact (@lem7046230 (@I ((nat -> nat) -> nat -> nat -> nat) i f) m). Qed.
Lemma lem7046232 (i : type1000) (f : nat -> nat) (m : nat) : (i f m) = (term308 i f m).
Proof. exact (TRANS (@lem7046227 i f m) (@lem7046231 i f m)). Qed.
Lemma lem7046233 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7046234 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (i f m n) = (term309 i f m n).
Proof. exact (MK_COMB (@lem7046232 i f m) (@lem7046233 n)). Qed.
Lemma lem7046236 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046237 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7046236 nat nat f x). Qed.
Lemma lem7046238 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term309 i f m n) = (term310 i f m n).
Proof. exact (@lem7046237 (term308 i f m) n). Qed.
Lemma lem7046240 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (i f m n) = (term310 i f m n).
Proof. exact (TRANS (@lem7046234 i f m n) (@lem7046238 i f m n)). Qed.
Lemma lem7046241 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term311 i f m n) = (term312 i f m n).
Proof. exact (MK_COMB (@lem7046214 f) (@lem7046240 i f m n)). Qed.
Lemma lem7046243 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046244 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7046243 nat nat f x). Qed.
Lemma lem7046245 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term312 i f m n) = (term313 i f m n).
Proof. exact (@lem7046244 f (term310 i f m n)). Qed.
Lemma lem7046246 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term311 i f m n) = (term313 i f m n).
Proof. exact (TRANS (@lem7046241 i f m n) (@lem7046245 i f m n)). Qed.
Lemma lem7046251 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046252 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7046251 nat nat f x). Qed.
Lemma lem7046254 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7046252 NUMERAL 0). Qed.
Lemma lem7046255 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term314 i f m n) = (term315 i f m n).
Proof. exact (MK_COMB (@lem7046213) (@lem7046246 i f m n)). Qed.
Lemma lem7046256 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : ((term311 i f m n) = (NUMERAL 0)) = ((term313 i f m n) = (@I (nat -> nat) NUMERAL 0)).
Proof. exact (MK_COMB (@lem7046255 i f m n) (@lem7046254)). Qed.
Lemma lem7046257 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term316 i f m n) = (term317 i f m n).
Proof. exact (MK_COMB (@lem7046212) (@lem7046256 i f m n)). Qed.
Lemma lem7046258 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem7046267 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046268 (f : type1000) (x : nat -> nat) : (f x) = (@I ((nat -> nat) -> nat -> nat -> nat) f x).
Proof. exact (@lem7046267 (nat -> nat) type1606 f x). Qed.
Lemma lem7046269 (i : type1000) (f : nat -> nat) : (i f) = (@I ((nat -> nat) -> nat -> nat -> nat) i f).
Proof. exact (@lem7046268 i f). Qed.
Lemma lem7046270 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem7046271 (i : type1000) (f : nat -> nat) (m : nat) : (i f m) = (@I ((nat -> nat) -> nat -> nat -> nat) i f m).
Proof. exact (MK_COMB (@lem7046269 i f) (@lem7046270 m)). Qed.
Lemma lem7046273 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046274 (f : type1606) (x : nat) : (f x) = (@I (nat -> nat -> nat) f x).
Proof. exact (@lem7046273 nat (nat -> nat) f x). Qed.
Lemma lem7046275 (i : type1000) (f : nat -> nat) (m : nat) : (@I ((nat -> nat) -> nat -> nat -> nat) i f m) = (term308 i f m).
Proof. exact (@lem7046274 (@I ((nat -> nat) -> nat -> nat -> nat) i f) m). Qed.
Lemma lem7046276 (i : type1000) (f : nat -> nat) (m : nat) : (i f m) = (term308 i f m).
Proof. exact (TRANS (@lem7046271 i f m) (@lem7046275 i f m)). Qed.
Lemma lem7046277 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7046278 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (i f m n) = (term309 i f m n).
Proof. exact (MK_COMB (@lem7046276 i f m) (@lem7046277 n)). Qed.
Lemma lem7046280 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046281 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7046280 nat nat f x). Qed.
Lemma lem7046282 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term309 i f m n) = (term310 i f m n).
Proof. exact (@lem7046281 (term308 i f m) n). Qed.
Lemma lem7046284 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (i f m n) = (term310 i f m n).
Proof. exact (TRANS (@lem7046278 i f m n) (@lem7046282 i f m n)). Qed.
Lemma lem7046285 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7046286 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term318 i f m n) = (term319 i f m n).
Proof. exact (MK_COMB (@lem7046258) (@lem7046284 i f m n)). Qed.
Lemma lem7046287 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term320 i f m n) = (term321 i f m n).
Proof. exact (MK_COMB (@lem7046286 i f m n) (@lem7046285 n)). Qed.
Lemma lem7046289 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046290 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7046289 nat (nat -> Prop) f x). Qed.
Lemma lem7046291 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term319 i f m n) = (term322 i f m n).
Proof. exact (@lem7046290 Peano.le (term310 i f m n)). Qed.
Lemma lem7046292 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7046293 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term321 i f m n) = (term323 i f m n).
Proof. exact (MK_COMB (@lem7046291 i f m n) (@lem7046292 n)). Qed.
Lemma lem7046295 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046296 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7046295 nat Prop f x). Qed.
Lemma lem7046297 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term323 i f m n) = (term324 i f m n).
Proof. exact (@lem7046296 (term322 i f m n) n). Qed.
Lemma lem7046298 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term321 i f m n) = (term324 i f m n).
Proof. exact (TRANS (@lem7046293 i f m n) (@lem7046297 i f m n)). Qed.
Lemma lem7046299 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term320 i f m n) = (term324 i f m n).
Proof. exact (TRANS (@lem7046287 i f m n) (@lem7046298 i f m n)). Qed.
Lemma lem7046310 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046311 (f : type1000) (x : nat -> nat) : (f x) = (@I ((nat -> nat) -> nat -> nat -> nat) f x).
Proof. exact (@lem7046310 (nat -> nat) type1606 f x). Qed.
Lemma lem7046312 (i : type1000) (f : nat -> nat) : (i f) = (@I ((nat -> nat) -> nat -> nat -> nat) i f).
Proof. exact (@lem7046311 i f). Qed.
Lemma lem7046313 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem7046314 (i : type1000) (f : nat -> nat) (m : nat) : (i f m) = (@I ((nat -> nat) -> nat -> nat -> nat) i f m).
Proof. exact (MK_COMB (@lem7046312 i f) (@lem7046313 m)). Qed.
Lemma lem7046316 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046317 (f : type1606) (x : nat) : (f x) = (@I (nat -> nat -> nat) f x).
Proof. exact (@lem7046316 nat (nat -> nat) f x). Qed.
Lemma lem7046318 (i : type1000) (f : nat -> nat) (m : nat) : (@I ((nat -> nat) -> nat -> nat -> nat) i f m) = (term308 i f m).
Proof. exact (@lem7046317 (@I ((nat -> nat) -> nat -> nat -> nat) i f) m). Qed.
Lemma lem7046319 (i : type1000) (f : nat -> nat) (m : nat) : (i f m) = (term308 i f m).
Proof. exact (TRANS (@lem7046314 i f m) (@lem7046318 i f m)). Qed.
Lemma lem7046320 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7046321 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (i f m n) = (term309 i f m n).
Proof. exact (MK_COMB (@lem7046319 i f m) (@lem7046320 n)). Qed.
Lemma lem7046323 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046324 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7046323 nat nat f x). Qed.
Lemma lem7046325 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term309 i f m n) = (term310 i f m n).
Proof. exact (@lem7046324 (term308 i f m) n). Qed.
Lemma lem7046327 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (i f m n) = (term310 i f m n).
Proof. exact (TRANS (@lem7046321 i f m n) (@lem7046325 i f m n)). Qed.
Lemma lem7046328 (m : nat) : (Peano.le m) = (Peano.le m).
Proof. exact (eq_refl (Peano.le m)). Qed.
Lemma lem7046329 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term325 i f m n) = (term326 i f m n).
Proof. exact (MK_COMB (@lem7046328 m) (@lem7046327 i f m n)). Qed.
Lemma lem7046331 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046332 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7046331 nat (nat -> Prop) f x). Qed.
Lemma lem7046333 (m : nat) : (Peano.le m) = (@I (nat -> nat -> Prop) Peano.le m).
Proof. exact (@lem7046332 Peano.le m). Qed.
Lemma lem7046334 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term310 i f m n) = (term310 i f m n).
Proof. exact (eq_refl (term310 i f m n)). Qed.
Lemma lem7046335 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term326 i f m n) = (term327 i f m n).
Proof. exact (MK_COMB (@lem7046333 m) (@lem7046334 i f m n)). Qed.
Lemma lem7046337 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046338 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7046337 nat Prop f x). Qed.
Lemma lem7046339 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term327 i f m n) = (term328 i f m n).
Proof. exact (@lem7046338 (@I (nat -> nat -> Prop) Peano.le m) (term310 i f m n)). Qed.
Lemma lem7046340 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term326 i f m n) = (term328 i f m n).
Proof. exact (TRANS (@lem7046335 i f m n) (@lem7046339 i f m n)). Qed.
Lemma lem7046341 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term325 i f m n) = (term328 i f m n).
Proof. exact (TRANS (@lem7046329 i f m n) (@lem7046340 i f m n)). Qed.
Lemma lem7046342 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7046343 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term329 i f m n) = (term330 i f m n).
Proof. exact (MK_COMB (@lem7046342) (@lem7046341 i f m n)). Qed.
Lemma lem7046344 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term331 i f m n) = (term332 i f m n).
Proof. exact (MK_COMB (@lem7046343 i f m n) (@lem7046299 i f m n)). Qed.
Lemma lem7046345 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7046346 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term333 i f m n) = (term334 i f m n).
Proof. exact (MK_COMB (@lem7046345) (@lem7046344 i f m n)). Qed.
Lemma lem7046347 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term335 i f m n) = (term336 i f m n).
Proof. exact (MK_COMB (@lem7046346 i f m n) (@lem7046257 i f m n)). Qed.
Lemma lem7046348 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7046349 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term337 i f m n) = (term338 i f m n).
Proof. exact (MK_COMB (@lem7046348) (@lem7046347 i f m n)). Qed.
Lemma lem7046350 (i : type1000) (m : nat) (n : nat) (f : nat -> nat) : (term339 i m n f) = (term340 i m n f).
Proof. exact (MK_COMB (@lem7046349 i f m n) (@lem7046211 m n f)). Qed.
Lemma lem7046351 (i : type1000) (m : nat) (f : nat -> nat) : (term341 i m f) = (term342 i m f).
Proof. exact (fun_ext (fun n : nat => @lem7046350 i m n f)). Qed.
Lemma lem7046352 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7046353 (i : type1000) (m : nat) (f : nat -> nat) : (term343 i m f) = (term344 i m f).
Proof. exact (MK_COMB (@lem7046352) (@lem7046351 i m f)). Qed.
Lemma lem7046354 (i : type1000) (f : nat -> nat) : (term345 i f) = (term346 i f).
Proof. exact (fun_ext (fun m : nat => @lem7046353 i m f)). Qed.
Lemma lem7046355 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7046356 (i : type1000) (f : nat -> nat) : (term260 i f) = (term347 i f).
Proof. exact (MK_COMB (@lem7046355) (@lem7046354 i f)). Qed.
Lemma lem7046357 (i : type1000) : (term262 i) = (term348 i).
Proof. exact (fun_ext (fun f : nat -> nat => @lem7046356 i f)). Qed.
Lemma lem7046358 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7046359 (i : type1000) : (term264 i) = (term349 i).
Proof. exact (MK_COMB (@lem7046358) (@lem7046357 i)). Qed.
Lemma lem7046360 (i : type1000) (h1 : term264 i) : term349 i.
Proof. exact (EQ_MP (@lem7046359 i) (@lem7045999 i h1)). Qed.
Lemma lem7046361 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7046362 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7046363 : (@nsum nat) = (@nsum nat).
Proof. exact (eq_refl (@nsum nat)). Qed.
Lemma lem7046370 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046371 (f : type1601) (x : nat) : (f x) = (@I (nat -> nat -> nat -> Prop) f x).
Proof. exact (@lem7046370 nat type1605 f x). Qed.
Lemma lem7046372 (m : nat) : (dotdot m) = (@I (nat -> nat -> nat -> Prop) dotdot m).
Proof. exact (@lem7046371 dotdot m). Qed.
Lemma lem7046373 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem7046374 (m : nat) (n : nat) : (dotdot m n) = (@I (nat -> nat -> nat -> Prop) dotdot m n).
Proof. exact (MK_COMB (@lem7046372 m) (@lem7046373 n)). Qed.
Lemma lem7046376 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046377 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7046376 nat (nat -> Prop) f x). Qed.
Lemma lem7046378 (m : nat) (n : nat) : (@I (nat -> nat -> nat -> Prop) dotdot m n) = (term299 m n).
Proof. exact (@lem7046377 (@I (nat -> nat -> nat -> Prop) dotdot m) n). Qed.
Lemma lem7046380 (m : nat) (n : nat) : (dotdot m n) = (term299 m n).
Proof. exact (TRANS (@lem7046374 m n) (@lem7046378 m n)). Qed.
Lemma lem7046381 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7046382 (m : nat) (n : nat) : (term300 m n) = (term301 m n).
Proof. exact (MK_COMB (@lem7046363) (@lem7046380 m n)). Qed.
Lemma lem7046383 (m : nat) (n : nat) (f : nat -> nat) : (term26 m n f) = (term302 m n f).
Proof. exact (MK_COMB (@lem7046382 m n) (@lem7046381 f)). Qed.
Lemma lem7046385 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046386 (f : type987) (x : nat -> Prop) : (f x) = (@I ((nat -> Prop) -> (nat -> nat) -> nat) f x).
Proof. exact (@lem7046385 (nat -> Prop) type1003 f x). Qed.
Lemma lem7046387 (m : nat) (n : nat) : (term301 m n) = (term303 m n).
Proof. exact (@lem7046386 (@nsum nat) (term299 m n)). Qed.
Lemma lem7046388 (f : nat -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7046389 (m : nat) (n : nat) (f : nat -> nat) : (term302 m n f) = (term304 m n f).
Proof. exact (MK_COMB (@lem7046387 m n) (@lem7046388 f)). Qed.
Lemma lem7046391 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046392 (f : type1003) (x : nat -> nat) : (f x) = (@I ((nat -> nat) -> nat) f x).
Proof. exact (@lem7046391 (nat -> nat) nat f x). Qed.
Lemma lem7046393 (m : nat) (n : nat) (f : nat -> nat) : (term304 m n f) = (term305 m n f).
Proof. exact (@lem7046392 (term303 m n) f). Qed.
Lemma lem7046394 (m : nat) (n : nat) (f : nat -> nat) : (term302 m n f) = (term305 m n f).
Proof. exact (TRANS (@lem7046389 m n f) (@lem7046393 m n f)). Qed.
Lemma lem7046395 (m : nat) (n : nat) (f : nat -> nat) : (term26 m n f) = (term305 m n f).
Proof. exact (TRANS (@lem7046383 m n f) (@lem7046394 m n f)). Qed.
Lemma lem7046400 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046401 (f : nat -> nat) (x : nat) : (f x) = (@I (nat -> nat) f x).
Proof. exact (@lem7046400 nat nat f x). Qed.
Lemma lem7046403 : (NUMERAL 0) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7046401 NUMERAL 0). Qed.
Lemma lem7046404 (m : nat) (n : nat) (f : nat -> nat) : (term306 m n f) = (term307 m n f).
Proof. exact (MK_COMB (@lem7046362) (@lem7046395 m n f)). Qed.
Lemma lem7046405 (m : nat) (n : nat) (f : nat -> nat) : ((term26 m n f) = (NUMERAL 0)) = ((term305 m n f) = (@I (nat -> nat) NUMERAL 0)).
Proof. exact (MK_COMB (@lem7046404 m n f) (@lem7046403)). Qed.
Lemma lem7046406 (m : nat) (n : nat) (f : nat -> nat) : (term350 m n f) = (term351 m n f).
Proof. exact (MK_COMB (@lem7046361) (@lem7046405 m n f)). Qed.
Lemma lem7046413 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046414 (f : type1605) (x : nat) : (f x) = (@I (nat -> nat -> Prop) f x).
Proof. exact (@lem7046413 nat (nat -> Prop) f x). Qed.
Lemma lem7046415 (n : nat) : (Peano.lt n) = (@I (nat -> nat -> Prop) Peano.lt n).
Proof. exact (@lem7046414 Peano.lt n). Qed.
Lemma lem7046416 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem7046417 (n : nat) (m : nat) : (Peano.lt n m) = (@I (nat -> nat -> Prop) Peano.lt n m).
Proof. exact (MK_COMB (@lem7046415 n) (@lem7046416 m)). Qed.
Lemma lem7046419 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem7046420 (f : nat -> Prop) (x : nat) : (f x) = (@I (nat -> Prop) f x).
Proof. exact (@lem7046419 nat Prop f x). Qed.
Lemma lem7046421 (n : nat) (m : nat) : (@I (nat -> nat -> Prop) Peano.lt n m) = (term269 n m).
Proof. exact (@lem7046420 (@I (nat -> nat -> Prop) Peano.lt n) m). Qed.
Lemma lem7046423 (n : nat) (m : nat) : (Peano.lt n m) = (term269 n m).
Proof. exact (TRANS (@lem7046417 n m) (@lem7046421 n m)). Qed.
Lemma lem7046424 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7046425 (n : nat) (m : nat) : (term352 n m) = (term353 n m).
Proof. exact (MK_COMB (@lem7046424) (@lem7046423 n m)). Qed.
Lemma lem7046426 (m : nat) (n : nat) (f : nat -> nat) : (term56 m n f) = (term354 m n f).
Proof. exact (MK_COMB (@lem7046425 n m) (@lem7046406 m n f)). Qed.
Lemma lem7046427 (m : nat) (n : nat) (f : nat -> nat) (h1 : term56 m n f) : term354 m n f.
Proof. exact (EQ_MP (@lem7046426 m n f) (@lem7046002 m n f h1)). Qed.
Lemma lem7046431 (h1 : term48) : term285.
Proof. exact (proj1 (@lem7046096 h1)). Qed.
Lemma lem7046445 (n : nat) (m : nat) (p : nat) : (term292 n m p) = (term292 n m p).
Proof. exact (eq_refl (term292 n m p)). Qed.
Lemma lem7046446 (n : nat) (m : nat) : (term293 n m) = (term293 n m).
Proof. exact (fun_ext (fun p : nat => @lem7046445 n m p)). Qed.
Lemma lem7046447 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7046448 (n : nat) (m : nat) : (term294 n m) = (term294 n m).
Proof. exact (MK_COMB (@lem7046447) (@lem7046446 n m)). Qed.
Lemma lem7046449 (m : nat) : (term295 m) = (term295 m).
Proof. exact (fun_ext (fun n : nat => @lem7046448 n m)). Qed.
Lemma lem7046450 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7046451 (m : nat) : (term296 m) = (term296 m).
Proof. exact (MK_COMB (@lem7046450) (@lem7046449 m)). Qed.
Lemma lem7046452 : term297 = term297.
Proof. exact (fun_ext (fun m : nat => @lem7046451 m)). Qed.
Lemma lem7046453 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7046455 : term298 = term298.
Proof. exact (MK_COMB (@lem7046453) (@lem7046452)). Qed.
Lemma lem7046456 (h1 : term43) : term298.
Proof. exact (EQ_MP (@lem7046455) (@lem7046167 h1)). Qed.
Lemma lem7046471 (i : type1000) (m : nat) (n : nat) (f : nat -> nat) : (term340 i m n f) = (term355 i m n f).
Proof. exact (@lem19699 (term332 i f m n) (term317 i f m n) ((term305 m n f) = (@I (nat -> nat) NUMERAL 0))). Qed.
Lemma lem7046472 (i : type1000) (m : nat) (n : nat) (f : nat -> nat) : (term356 i m n f) = (term356 i m n f).
Proof. exact (eq_refl (term356 i m n f)). Qed.
Lemma lem7046479 (i : type1000) (m : nat) (n : nat) (f : nat -> nat) : (term357 i m n f) = (term358 i m n f).
Proof. exact (@lem19699 (term328 i f m n) (term324 i f m n) ((term305 m n f) = (@I (nat -> nat) NUMERAL 0))). Qed.
Lemma lem7046480 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7046481 (i : type1000) (m : nat) (n : nat) (f : nat -> nat) : (term359 i m n f) = (term360 i m n f).
Proof. exact (MK_COMB (@lem7046480) (@lem7046479 i m n f)). Qed.
Lemma lem7046482 (i : type1000) (m : nat) (n : nat) (f : nat -> nat) : (term355 i m n f) = (term361 i m n f).
Proof. exact (MK_COMB (@lem7046481 i m n f) (@lem7046472 i m n f)). Qed.
Lemma lem7046484 (i : type1000) (m : nat) (n : nat) (f : nat -> nat) : (term340 i m n f) = (term361 i m n f).
Proof. exact (TRANS (@lem7046471 i m n f) (@lem7046482 i m n f)). Qed.
Lemma lem7046485 (i : type1000) (m : nat) (f : nat -> nat) : (term342 i m f) = (term362 i m f).
Proof. exact (fun_ext (fun n : nat => @lem7046484 i m n f)). Qed.
Lemma lem7046486 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7046487 (i : type1000) (m : nat) (f : nat -> nat) : (term344 i m f) = (term363 i m f).
Proof. exact (MK_COMB (@lem7046486) (@lem7046485 i m f)). Qed.
Lemma lem7046488 (i : type1000) (f : nat -> nat) : (term346 i f) = (term364 i f).
Proof. exact (fun_ext (fun m : nat => @lem7046487 i m f)). Qed.
Lemma lem7046489 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7046490 (i : type1000) (f : nat -> nat) : (term347 i f) = (term365 i f).
Proof. exact (MK_COMB (@lem7046489) (@lem7046488 i f)). Qed.
Lemma lem7046491 (i : type1000) : (term348 i) = (term366 i).
Proof. exact (fun_ext (fun f : nat -> nat => @lem7046490 i f)). Qed.
Lemma lem7046492 : (@all (nat -> nat)) = (@all (nat -> nat)).
Proof. exact (eq_refl (@all (nat -> nat))). Qed.
Lemma lem7046494 (i : type1000) : (term349 i) = (term367 i).
Proof. exact (MK_COMB (@lem7046492) (@lem7046491 i)). Qed.
Lemma lem7046495 (i : type1000) (h1 : term264 i) : term367 i.
Proof. exact (EQ_MP (@lem7046494 i) (@lem7046360 i h1)). Qed.
Lemma lem7046511 (n : nat) (m : nat) : (term281 n m) = (term281 n m).
Proof. exact (eq_refl (term281 n m)). Qed.
Lemma lem7046512 (m : nat) : (term282 m) = (term282 m).
Proof. exact (fun_ext (fun n : nat => @lem7046511 n m)). Qed.
Lemma lem7046513 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7046514 (m : nat) : (term283 m) = (term283 m).
Proof. exact (MK_COMB (@lem7046513) (@lem7046512 m)). Qed.
Lemma lem7046515 : term284 = term284.
Proof. exact (fun_ext (fun m : nat => @lem7046514 m)). Qed.
Lemma lem7046516 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7046518 : term285 = term285.
Proof. exact (MK_COMB (@lem7046516) (@lem7046515)). Qed.
Lemma lem7046519 (h1 : term48) : term285.
Proof. exact (EQ_MP (@lem7046518) (@lem7046431 h1)). Qed.
Lemma lem7046536 (_94098 : nat) (h1 : term43) : term368 _94098.
Proof. exact (@lem7046456 h1 _94098). Qed.
Lemma lem7046537 (_94098 : nat) : (term368 _94098) = (term296 _94098).
Proof. exact (eq_refl (term368 _94098)). Qed.
Lemma lem7046538 (_94098 : nat) (h1 : term43) : term296 _94098.
Proof. exact (EQ_MP (@lem7046537 _94098) (@lem7046536 _94098 h1)). Qed.
Lemma lem7046539 (_94098 : nat) (_94099 : nat) (h1 : term43) : term369 _94098 _94099.
Proof. exact (@lem7046538 _94098 h1 _94099). Qed.
Lemma lem7046540 (_94099 : nat) (_94098 : nat) : (term369 _94098 _94099) = (term294 _94099 _94098).
Proof. exact (eq_refl (term369 _94098 _94099)). Qed.
Lemma lem7046541 (_94099 : nat) (_94098 : nat) (h1 : term43) : term294 _94099 _94098.
Proof. exact (EQ_MP (@lem7046540 _94099 _94098) (@lem7046539 _94098 _94099 h1)). Qed.
Lemma lem7046542 (_94099 : nat) (_94098 : nat) (_94100 : nat) (h1 : term43) : term370 _94099 _94098 _94100.
Proof. exact (@lem7046541 _94099 _94098 h1 _94100). Qed.
Lemma lem7046543 (_94099 : nat) (_94098 : nat) (_94100 : nat) : (term370 _94099 _94098 _94100) = (term292 _94099 _94098 _94100).
Proof. exact (eq_refl (term370 _94099 _94098 _94100)). Qed.
Lemma lem7046544 (_94099 : nat) (_94098 : nat) (_94100 : nat) (h1 : term43) : term292 _94099 _94098 _94100.
Proof. exact (EQ_MP (@lem7046543 _94099 _94098 _94100) (@lem7046542 _94099 _94098 _94100 h1)). Qed.
Lemma lem7046545 (_94101 : nat -> nat) (i : type1000) (h1 : term264 i) : term371 i _94101.
Proof. exact (@lem7046495 i h1 _94101). Qed.
Lemma lem7046546 (i : type1000) (_94101 : nat -> nat) : (term371 i _94101) = (term365 i _94101).
Proof. exact (eq_refl (term371 i _94101)). Qed.
Lemma lem7046547 (_94101 : nat -> nat) (i : type1000) (h1 : term264 i) : term365 i _94101.
Proof. exact (EQ_MP (@lem7046546 i _94101) (@lem7046545 _94101 i h1)). Qed.
Lemma lem7046548 (_94101 : nat -> nat) (_94102 : nat) (i : type1000) (h1 : term264 i) : term372 i _94101 _94102.
Proof. exact (@lem7046547 _94101 i h1 _94102). Qed.
Lemma lem7046549 (i : type1000) (_94102 : nat) (_94101 : nat -> nat) : (term372 i _94101 _94102) = (term363 i _94102 _94101).
Proof. exact (eq_refl (term372 i _94101 _94102)). Qed.
Lemma lem7046550 (_94102 : nat) (_94101 : nat -> nat) (i : type1000) (h1 : term264 i) : term363 i _94102 _94101.
Proof. exact (EQ_MP (@lem7046549 i _94102 _94101) (@lem7046548 _94101 _94102 i h1)). Qed.
Lemma lem7046551 (_94102 : nat) (_94101 : nat -> nat) (_94103 : nat) (i : type1000) (h1 : term264 i) : term373 i _94102 _94101 _94103.
Proof. exact (@lem7046550 _94102 _94101 i h1 _94103). Qed.
Lemma lem7046552 (i : type1000) (_94102 : nat) (_94103 : nat) (_94101 : nat -> nat) : (term373 i _94102 _94101 _94103) = (term361 i _94102 _94103 _94101).
Proof. exact (eq_refl (term373 i _94102 _94101 _94103)). Qed.
Lemma lem7046553 (_94102 : nat) (_94103 : nat) (_94101 : nat -> nat) (i : type1000) (h1 : term264 i) : term361 i _94102 _94103 _94101.
Proof. exact (EQ_MP (@lem7046552 i _94102 _94103 _94101) (@lem7046551 _94102 _94101 _94103 i h1)). Qed.
Lemma lem7046554 (_94104 : nat) (h1 : term48) : term374 _94104.
Proof. exact (@lem7046519 h1 _94104). Qed.
Lemma lem7046555 (_94104 : nat) : (term374 _94104) = (term283 _94104).
Proof. exact (eq_refl (term374 _94104)). Qed.
Lemma lem7046556 (_94104 : nat) (h1 : term48) : term283 _94104.
Proof. exact (EQ_MP (@lem7046555 _94104) (@lem7046554 _94104 h1)). Qed.
Lemma lem7046557 (_94104 : nat) (_94105 : nat) (h1 : term48) : term375 _94104 _94105.
Proof. exact (@lem7046556 _94104 h1 _94105). Qed.
Lemma lem7046558 (_94105 : nat) (_94104 : nat) : (term375 _94104 _94105) = (term281 _94105 _94104).
Proof. exact (eq_refl (term375 _94104 _94105)). Qed.
Lemma lem7046567 (_94102 : nat) (_94103 : nat) (_94101 : nat -> nat) (i : type1000) (h1 : term264 i) : term358 i _94102 _94103 _94101.
Proof. exact (proj1 (@lem7046553 _94102 _94103 _94101 i h1)). Qed.
Lemma lem7046580 (_94099 : nat) (_94098 : nat) (_94100 : nat) : (term292 _94099 _94098 _94100) = (term376 _94099 _94098 _94100).
Proof. exact (@lem7044972 (term277 _94098 _94099) (term277 _94099 _94100) (term268 _94098 _94100)). Qed.
Lemma lem7046581 (_94099 : nat) (_94098 : nat) (_94100 : nat) (h1 : term43) : term376 _94099 _94098 _94100.
Proof. exact (EQ_MP (@lem7046580 _94099 _94098 _94100) (@lem7046544 _94099 _94098 _94100 h1)). Qed.
Lemma lem7046585 (m : nat) (n : nat) (f : nat -> nat) (h1 : term56 m n f) : term351 m n f.
Proof. exact (proj2 (@lem7046427 m n f h1)). Qed.
Lemma lem7046591 (_94105 : nat) (_94104 : nat) (h1 : term48) : term281 _94105 _94104.
Proof. exact (EQ_MP (@lem7046558 _94105 _94104) (@lem7046557 _94104 _94105 h1)). Qed.
Lemma lem7046609 (_94102 : nat) (_94103 : nat) (_94101 : nat -> nat) (i : type1000) (h1 : term264 i) : term377 i _94102 _94103 _94101.
Proof. exact (proj1 (@lem7046567 _94102 _94103 _94101 i h1)). Qed.
Lemma lem7046615 (_94102 : nat) (_94103 : nat) (_94101 : nat -> nat) (i : type1000) (h1 : term264 i) : term378 i _94102 _94103 _94101.
Proof. exact (proj2 (@lem7046567 _94102 _94103 _94101 i h1)). Qed.
Lemma lem7046760 (m : nat) (n : nat) (f : nat -> nat) (h1 : term351 m n f) : term351 m n f.
Proof. exact (h1). Qed.
Lemma lem7046761 (m : nat) (n : nat) (f : nat -> nat) (h1 : term351 m n f) : term379 m n f.
Proof. exact (fun h0 : (term305 m n f) = (@I (nat -> nat) NUMERAL 0) => @lem7046760 m n f h1). Qed.
Lemma lem7046763 (p : Prop) : (term380 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7046764 (m : nat) (n : nat) (f : nat -> nat) : (term379 m n f) = (term351 m n f).
Proof. exact (@lem7046763 ((term305 m n f) = (@I (nat -> nat) NUMERAL 0))). Qed.
Lemma lem7046765 (m : nat) (n : nat) (f : nat -> nat) (h1 : term351 m n f) : term351 m n f.
Proof. exact (EQ_MP (@lem7046764 m n f) (@lem7046761 m n f h1)). Qed.
Lemma lem7046767 (b : Prop) (a : Prop) : (a \/ b) = (term381 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7046770 (i : type1000) (_94101 : nat -> nat) (_94102 : nat) (_94103 : nat) : (term377 i _94102 _94103 _94101) = (term382 i _94101 _94102 _94103).
Proof. exact (@lem7046767 ((term305 _94102 _94103 _94101) = (@I (nat -> nat) NUMERAL 0)) (term328 i _94101 _94102 _94103)). Qed.
Lemma lem7046773 (_94101 : nat -> nat) (_94102 : nat) (_94103 : nat) (i : type1000) (h1 : term264 i) : term382 i _94101 _94102 _94103.
Proof. exact (EQ_MP (@lem7046770 i _94101 _94102 _94103) (@lem7046609 _94102 _94103 _94101 i h1)). Qed.
Lemma lem7046774 (f : nat -> nat) (m : nat) (n : nat) (i : type1000) (h1 : term264 i) : term382 i f m n.
Proof. exact (@lem7046773 f m n i h1). Qed.
Lemma lem7046777 (i : type1000) (m : nat) (n : nat) (f : nat -> nat) (h1 : term264 i) (h2 : term351 m n f) : term328 i f m n.
Proof. exact (@lem7046774 f m n i h1 (@lem7046765 m n f h2)). Qed.
Lemma lem7046778 (i : type1000) (m : nat) (n : nat) (f : nat -> nat) (h1 : term264 i) (h2 : term351 m n f) : term383 i f m n.
Proof. exact (fun h0 : term384 i f m n => @lem7046777 i m n f h1 h2). Qed.
Lemma lem7046780 (p : Prop) : (term385 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7046781 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term383 i f m n) = (term328 i f m n).
Proof. exact (@lem7046780 (term328 i f m n)). Qed.
Lemma lem7046782 (i : type1000) (m : nat) (n : nat) (f : nat -> nat) (h1 : term264 i) (h2 : term351 m n f) : term328 i f m n.
Proof. exact (EQ_MP (@lem7046781 i f m n) (@lem7046778 i m n f h1 h2)). Qed.
Lemma lem7046784 (m : nat) (n : nat) (f : nat -> nat) (h1 : term56 m n f) : term269 n m.
Proof. exact (proj1 (@lem7046427 m n f h1)). Qed.
Lemma lem7046785 (m : nat) (n : nat) (f : nat -> nat) (h1 : term56 m n f) : term386 n m.
Proof. exact (fun h0 : term278 n m => @lem7046784 m n f h1). Qed.
Lemma lem7046787 (p : Prop) : (term385 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7046788 (n : nat) (m : nat) : (term386 n m) = (term269 n m).
Proof. exact (@lem7046787 (term269 n m)). Qed.
Lemma lem7046789 (m : nat) (n : nat) (f : nat -> nat) (h1 : term56 m n f) : term269 n m.
Proof. exact (EQ_MP (@lem7046788 n m) (@lem7046785 m n f h1)). Qed.
Lemma lem7046800 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7046801 (_94105 : nat) (_94104 : nat) : (term387 _94104 _94105) = (term281 _94105 _94104).
Proof. exact (@lem7046800 (term278 _94104 _94105) (term277 _94105 _94104)). Qed.
Lemma lem7046807 (_94105 : nat) (_94104 : nat) : (term388 _94105 _94104) = (term388 _94105 _94104).
Proof. exact (eq_refl (term388 _94105 _94104)). Qed.
Lemma lem7046808 (_94105 : nat) (_94104 : nat) : ((term281 _94105 _94104) = (term387 _94104 _94105)) = ((term281 _94105 _94104) = (term281 _94105 _94104)).
Proof. exact (MK_COMB (@lem7046807 _94105 _94104) (@lem7046801 _94105 _94104)). Qed.
Lemma lem7046810 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7046811 (x : Prop) : (x = x) = True.
Proof. exact (@lem7046810 Prop x). Qed.
Lemma lem7046812 (_94105 : nat) (_94104 : nat) : ((term281 _94105 _94104) = (term281 _94105 _94104)) = True.
Proof. exact (@lem7046811 (term281 _94105 _94104)). Qed.
Lemma lem7046813 (_94104 : nat) (_94105 : nat) : ((term281 _94105 _94104) = (term387 _94104 _94105)) = True.
Proof. exact (TRANS (@lem7046808 _94105 _94104) (@lem7046812 _94105 _94104)). Qed.
Lemma lem7046814 (_94104 : nat) (_94105 : nat) : True = ((term281 _94105 _94104) = (term387 _94104 _94105)).
Proof. exact (SYM (@lem7046813 _94104 _94105)). Qed.
Lemma lem7046815 (_94104 : nat) (_94105 : nat) : (term281 _94105 _94104) = (term387 _94104 _94105).
Proof. exact (EQ_MP (@lem7046814 _94104 _94105) (@lem0)). Qed.
Lemma lem7046816 (_94104 : nat) (_94105 : nat) (h1 : term48) : term387 _94104 _94105.
Proof. exact (EQ_MP (@lem7046815 _94104 _94105) (@lem7046591 _94105 _94104 h1)). Qed.
Lemma lem7046818 (b : Prop) (a : Prop) : (a \/ b) = (term381 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7046819 (_94105 : nat) (_94104 : nat) : (term387 _94104 _94105) = (term389 _94105 _94104).
Proof. exact (@lem7046818 (term278 _94104 _94105) (term277 _94105 _94104)). Qed.
Lemma lem7046821 (a : Prop) : (term390 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7046822 (_94104 : nat) (_94105 : nat) : (term391 _94104 _94105) = (term269 _94104 _94105).
Proof. exact (@lem7046821 (term269 _94104 _94105)). Qed.
Lemma lem7046823 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7046824 (_94104 : nat) (_94105 : nat) : (term392 _94104 _94105) = (term393 _94104 _94105).
Proof. exact (MK_COMB (@lem7046823) (@lem7046822 _94104 _94105)). Qed.
Lemma lem7046825 (_94105 : nat) (_94104 : nat) : (term277 _94105 _94104) = (term277 _94105 _94104).
Proof. exact (eq_refl (term277 _94105 _94104)). Qed.
Lemma lem7046826 (_94105 : nat) (_94104 : nat) : (term389 _94105 _94104) = (term394 _94105 _94104).
Proof. exact (MK_COMB (@lem7046824 _94104 _94105) (@lem7046825 _94105 _94104)). Qed.
Lemma lem7046827 (_94105 : nat) (_94104 : nat) : (term387 _94104 _94105) = (term394 _94105 _94104).
Proof. exact (TRANS (@lem7046819 _94105 _94104) (@lem7046826 _94105 _94104)). Qed.
Lemma lem7046830 (_94105 : nat) (_94104 : nat) (h1 : term48) : term394 _94105 _94104.
Proof. exact (EQ_MP (@lem7046827 _94105 _94104) (@lem7046816 _94104 _94105 h1)). Qed.
Lemma lem7046831 (m : nat) (n : nat) (h1 : term48) : term394 m n.
Proof. exact (@lem7046830 m n h1). Qed.
Lemma lem7046834 (m : nat) (n : nat) (f : nat -> nat) (h1 : term48) (h2 : term56 m n f) : term277 m n.
Proof. exact (@lem7046831 m n h1 (@lem7046789 m n f h2)). Qed.
Lemma lem7046835 (m : nat) (n : nat) (f : nat -> nat) (h1 : term48) (h2 : term56 m n f) : term395 m n.
Proof. exact (fun h0 : term268 m n => @lem7046834 m n f h1 h2). Qed.
Lemma lem7046837 (p : Prop) : (term380 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7046838 (m : nat) (n : nat) : (term395 m n) = (term277 m n).
Proof. exact (@lem7046837 (term268 m n)). Qed.
Lemma lem7046839 (m : nat) (n : nat) (f : nat -> nat) (h1 : term48) (h2 : term56 m n f) : term277 m n.
Proof. exact (EQ_MP (@lem7046838 m n) (@lem7046835 m n f h1 h2)). Qed.
Lemma lem7046855 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7046856 (_94098 : nat) (_94099 : nat) (_94100 : nat) : (term396 _94099 _94098 _94100) = (term397 _94098 _94099 _94100).
Proof. exact (@lem7046855 (term268 _94098 _94100) (term277 _94099 _94100)). Qed.
Lemma lem7046862 (_94098 : nat) (_94099 : nat) : (term289 _94098 _94099) = (term289 _94098 _94099).
Proof. exact (eq_refl (term289 _94098 _94099)). Qed.
Lemma lem7046863 (_94098 : nat) (_94099 : nat) (_94100 : nat) : (term376 _94099 _94098 _94100) = (term398 _94098 _94099 _94100).
Proof. exact (MK_COMB (@lem7046862 _94098 _94099) (@lem7046856 _94098 _94099 _94100)). Qed.
Lemma lem7046867 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7046868 (_94098 : nat) (_94099 : nat) (_94100 : nat) : (term398 _94098 _94099 _94100) = (term399 _94098 _94099 _94100).
Proof. exact (@lem7046867 (term268 _94098 _94100) (term277 _94098 _94099) (term277 _94099 _94100)). Qed.
Lemma lem7046884 (_94098 : nat) (_94099 : nat) (_94100 : nat) : (term376 _94099 _94098 _94100) = (term399 _94098 _94099 _94100).
Proof. exact (TRANS (@lem7046863 _94098 _94099 _94100) (@lem7046868 _94098 _94099 _94100)). Qed.
Lemma lem7046885 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7046886 (_94098 : nat) (_94099 : nat) (_94100 : nat) : (term400 _94099 _94098 _94100) = (term401 _94098 _94099 _94100).
Proof. exact (MK_COMB (@lem7046885) (@lem7046884 _94098 _94099 _94100)). Qed.
Lemma lem7046890 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7046891 (_94099 : nat) (_94098 : nat) (_94100 : nat) : (term402 _94099 _94098 _94100) = (term376 _94099 _94098 _94100).
Proof. exact (@lem7046890 (term277 _94098 _94099) (term277 _94099 _94100) (term268 _94098 _94100)). Qed.
Lemma lem7046905 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7046906 (_94098 : nat) (_94099 : nat) (_94100 : nat) : (term396 _94099 _94098 _94100) = (term397 _94098 _94099 _94100).
Proof. exact (@lem7046905 (term268 _94098 _94100) (term277 _94099 _94100)). Qed.
Lemma lem7046912 (_94098 : nat) (_94099 : nat) : (term289 _94098 _94099) = (term289 _94098 _94099).
Proof. exact (eq_refl (term289 _94098 _94099)). Qed.
Lemma lem7046913 (_94098 : nat) (_94099 : nat) (_94100 : nat) : (term376 _94099 _94098 _94100) = (term398 _94098 _94099 _94100).
Proof. exact (MK_COMB (@lem7046912 _94098 _94099) (@lem7046906 _94098 _94099 _94100)). Qed.
Lemma lem7046917 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7046918 (_94098 : nat) (_94099 : nat) (_94100 : nat) : (term398 _94098 _94099 _94100) = (term399 _94098 _94099 _94100).
Proof. exact (@lem7046917 (term268 _94098 _94100) (term277 _94098 _94099) (term277 _94099 _94100)). Qed.
Lemma lem7046934 (_94098 : nat) (_94099 : nat) (_94100 : nat) : (term376 _94099 _94098 _94100) = (term399 _94098 _94099 _94100).
Proof. exact (TRANS (@lem7046913 _94098 _94099 _94100) (@lem7046918 _94098 _94099 _94100)). Qed.
Lemma lem7046935 (_94098 : nat) (_94099 : nat) (_94100 : nat) : (term402 _94099 _94098 _94100) = (term399 _94098 _94099 _94100).
Proof. exact (TRANS (@lem7046891 _94099 _94098 _94100) (@lem7046934 _94098 _94099 _94100)). Qed.
Lemma lem7046936 (_94098 : nat) (_94099 : nat) (_94100 : nat) : ((term376 _94099 _94098 _94100) = (term402 _94099 _94098 _94100)) = ((term399 _94098 _94099 _94100) = (term399 _94098 _94099 _94100)).
Proof. exact (MK_COMB (@lem7046886 _94098 _94099 _94100) (@lem7046935 _94098 _94099 _94100)). Qed.
Lemma lem7046938 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7046939 (x : Prop) : (x = x) = True.
Proof. exact (@lem7046938 Prop x). Qed.
Lemma lem7046940 (_94098 : nat) (_94099 : nat) (_94100 : nat) : ((term399 _94098 _94099 _94100) = (term399 _94098 _94099 _94100)) = True.
Proof. exact (@lem7046939 (term399 _94098 _94099 _94100)). Qed.
Lemma lem7046941 (_94099 : nat) (_94098 : nat) (_94100 : nat) : ((term376 _94099 _94098 _94100) = (term402 _94099 _94098 _94100)) = True.
Proof. exact (TRANS (@lem7046936 _94098 _94099 _94100) (@lem7046940 _94098 _94099 _94100)). Qed.
Lemma lem7046942 (_94099 : nat) (_94098 : nat) (_94100 : nat) : True = ((term376 _94099 _94098 _94100) = (term402 _94099 _94098 _94100)).
Proof. exact (SYM (@lem7046941 _94099 _94098 _94100)). Qed.
Lemma lem7046943 (_94099 : nat) (_94098 : nat) (_94100 : nat) : (term376 _94099 _94098 _94100) = (term402 _94099 _94098 _94100).
Proof. exact (EQ_MP (@lem7046942 _94099 _94098 _94100) (@lem0)). Qed.
Lemma lem7046944 (_94099 : nat) (_94098 : nat) (_94100 : nat) (h1 : term43) : term402 _94099 _94098 _94100.
Proof. exact (EQ_MP (@lem7046943 _94099 _94098 _94100) (@lem7046581 _94099 _94098 _94100 h1)). Qed.
Lemma lem7046946 (b : Prop) (a : Prop) : (a \/ b) = (term381 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7046947 (_94098 : nat) (_94099 : nat) (_94100 : nat) : (term402 _94099 _94098 _94100) = (term403 _94098 _94099 _94100).
Proof. exact (@lem7046946 (term404 _94099 _94098 _94100) (term277 _94099 _94100)). Qed.
Lemma lem7046949 (a : Prop) (b : Prop) : (term405 a b) = (term406 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7046950 (_94099 : nat) (_94098 : nat) (_94100 : nat) : (term407 _94099 _94098 _94100) = (term408 _94099 _94098 _94100).
Proof. exact (@lem7046949 (term277 _94098 _94099) (term268 _94098 _94100)). Qed.
Lemma lem7046952 (a : Prop) : (term390 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7046953 (_94098 : nat) (_94099 : nat) : (term409 _94098 _94099) = (term268 _94098 _94099).
Proof. exact (@lem7046952 (term268 _94098 _94099)). Qed.
Lemma lem7046954 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7046955 (_94098 : nat) (_94099 : nat) : (term410 _94098 _94099) = (term411 _94098 _94099).
Proof. exact (MK_COMB (@lem7046954) (@lem7046953 _94098 _94099)). Qed.
Lemma lem7046956 (_94098 : nat) (_94100 : nat) : (term277 _94098 _94100) = (term277 _94098 _94100).
Proof. exact (eq_refl (term277 _94098 _94100)). Qed.
Lemma lem7046957 (_94099 : nat) (_94098 : nat) (_94100 : nat) : (term408 _94099 _94098 _94100) = (term412 _94099 _94098 _94100).
Proof. exact (MK_COMB (@lem7046955 _94098 _94099) (@lem7046956 _94098 _94100)). Qed.
Lemma lem7046958 (_94099 : nat) (_94098 : nat) (_94100 : nat) : (term407 _94099 _94098 _94100) = (term412 _94099 _94098 _94100).
Proof. exact (TRANS (@lem7046950 _94099 _94098 _94100) (@lem7046957 _94099 _94098 _94100)). Qed.
Lemma lem7046959 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7046960 (_94099 : nat) (_94098 : nat) (_94100 : nat) : (term413 _94099 _94098 _94100) = (term414 _94099 _94098 _94100).
Proof. exact (MK_COMB (@lem7046959) (@lem7046958 _94099 _94098 _94100)). Qed.
Lemma lem7046961 (_94099 : nat) (_94100 : nat) : (term277 _94099 _94100) = (term277 _94099 _94100).
Proof. exact (eq_refl (term277 _94099 _94100)). Qed.
Lemma lem7046962 (_94098 : nat) (_94099 : nat) (_94100 : nat) : (term403 _94098 _94099 _94100) = (term415 _94098 _94099 _94100).
Proof. exact (MK_COMB (@lem7046960 _94099 _94098 _94100) (@lem7046961 _94099 _94100)). Qed.
Lemma lem7046963 (_94098 : nat) (_94099 : nat) (_94100 : nat) : (term402 _94099 _94098 _94100) = (term415 _94098 _94099 _94100).
Proof. exact (TRANS (@lem7046947 _94098 _94099 _94100) (@lem7046962 _94098 _94099 _94100)). Qed.
Lemma lem7046965 (i : type1000) (m : nat) (n : nat) (f : nat -> nat) (h1 : term264 i) (h2 : term48) (h3 : term351 m n f) (h4 : term56 m n f) : term416 i f m n.
Proof. exact (conj (@lem7046782 i m n f h1 h3) (@lem7046839 m n f h2 h4)). Qed.
Lemma lem7046967 (_94098 : nat) (_94099 : nat) (_94100 : nat) (h1 : term43) : term415 _94098 _94099 _94100.
Proof. exact (EQ_MP (@lem7046963 _94098 _94099 _94100) (@lem7046944 _94099 _94098 _94100 h1)). Qed.
Lemma lem7046968 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) (h1 : term43) : term417 i f m n.
Proof. exact (@lem7046967 m (term310 i f m n) n h1). Qed.
Lemma lem7046971 (i : type1000) (m : nat) (n : nat) (f : nat -> nat) (h1 : term264 i) (h2 : term43) (h3 : term48) (h4 : term351 m n f) (h5 : term56 m n f) : term418 i f m n.
Proof. exact (@lem7046968 i f m n h2 (@lem7046965 i m n f h1 h3 h4 h5)). Qed.
Lemma lem7046972 (i : type1000) (m : nat) (n : nat) (f : nat -> nat) (h1 : term264 i) (h2 : term43) (h3 : term48) (h4 : term351 m n f) (h5 : term56 m n f) : term419 i f m n.
Proof. exact (fun h0 : term324 i f m n => @lem7046971 i m n f h1 h2 h3 h4 h5). Qed.
Lemma lem7046974 (p : Prop) : (term380 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7046975 (i : type1000) (f : nat -> nat) (m : nat) (n : nat) : (term419 i f m n) = (term418 i f m n).
Proof. exact (@lem7046974 (term324 i f m n)). Qed.
Lemma lem7046976 (i : type1000) (m : nat) (n : nat) (f : nat -> nat) (h1 : term264 i) (h2 : term43) (h3 : term48) (h4 : term351 m n f) (h5 : term56 m n f) : term418 i f m n.
Proof. exact (EQ_MP (@lem7046975 i f m n) (@lem7046972 i m n f h1 h2 h3 h4 h5)). Qed.
Lemma lem7046982 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7046983 (i : type1000) (_94101 : nat -> nat) (_94102 : nat) (_94103 : nat) : (term378 i _94102 _94103 _94101) = (term420 i _94101 _94102 _94103).
Proof. exact (@lem7046982 ((term305 _94102 _94103 _94101) = (@I (nat -> nat) NUMERAL 0)) (term324 i _94101 _94102 _94103)). Qed.
Lemma lem7046991 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7046992 (i : type1000) (_94101 : nat -> nat) (_94102 : nat) (_94103 : nat) : (term421 i _94102 _94103 _94101) = (term422 i _94101 _94102 _94103).
Proof. exact (MK_COMB (@lem7046991) (@lem7046983 i _94101 _94102 _94103)). Qed.
Lemma lem7047000 (i : type1000) (_94101 : nat -> nat) (_94102 : nat) (_94103 : nat) : (term420 i _94101 _94102 _94103) = (term420 i _94101 _94102 _94103).
Proof. exact (eq_refl (term420 i _94101 _94102 _94103)). Qed.
Lemma lem7047001 (i : type1000) (_94101 : nat -> nat) (_94102 : nat) (_94103 : nat) : ((term378 i _94102 _94103 _94101) = (term420 i _94101 _94102 _94103)) = ((term420 i _94101 _94102 _94103) = (term420 i _94101 _94102 _94103)).
Proof. exact (MK_COMB (@lem7046992 i _94101 _94102 _94103) (@lem7047000 i _94101 _94102 _94103)). Qed.
Lemma lem7047003 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7047004 (x : Prop) : (x = x) = True.
Proof. exact (@lem7047003 Prop x). Qed.
Lemma lem7047005 (i : type1000) (_94101 : nat -> nat) (_94102 : nat) (_94103 : nat) : ((term420 i _94101 _94102 _94103) = (term420 i _94101 _94102 _94103)) = True.
Proof. exact (@lem7047004 (term420 i _94101 _94102 _94103)). Qed.
Lemma lem7047006 (i : type1000) (_94101 : nat -> nat) (_94102 : nat) (_94103 : nat) : ((term378 i _94102 _94103 _94101) = (term420 i _94101 _94102 _94103)) = True.
Proof. exact (TRANS (@lem7047001 i _94101 _94102 _94103) (@lem7047005 i _94101 _94102 _94103)). Qed.
Lemma lem7047007 (i : type1000) (_94101 : nat -> nat) (_94102 : nat) (_94103 : nat) : True = ((term378 i _94102 _94103 _94101) = (term420 i _94101 _94102 _94103)).
Proof. exact (SYM (@lem7047006 i _94101 _94102 _94103)). Qed.
Lemma lem7047008 (i : type1000) (_94101 : nat -> nat) (_94102 : nat) (_94103 : nat) : (term378 i _94102 _94103 _94101) = (term420 i _94101 _94102 _94103).
Proof. exact (EQ_MP (@lem7047007 i _94101 _94102 _94103) (@lem0)). Qed.
Lemma lem7047009 (_94101 : nat -> nat) (_94102 : nat) (_94103 : nat) (i : type1000) (h1 : term264 i) : term420 i _94101 _94102 _94103.
Proof. exact (EQ_MP (@lem7047008 i _94101 _94102 _94103) (@lem7046615 _94102 _94103 _94101 i h1)). Qed.
Lemma lem7047011 (b : Prop) (a : Prop) : (a \/ b) = (term381 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7047014 (i : type1000) (_94102 : nat) (_94103 : nat) (_94101 : nat -> nat) : (term420 i _94101 _94102 _94103) = (term423 i _94102 _94103 _94101).
Proof. exact (@lem7047011 (term324 i _94101 _94102 _94103) ((term305 _94102 _94103 _94101) = (@I (nat -> nat) NUMERAL 0))). Qed.
Lemma lem7047017 (_94102 : nat) (_94103 : nat) (_94101 : nat -> nat) (i : type1000) (h1 : term264 i) : term423 i _94102 _94103 _94101.
Proof. exact (EQ_MP (@lem7047014 i _94102 _94103 _94101) (@lem7047009 _94101 _94102 _94103 i h1)). Qed.
Lemma lem7047018 (m : nat) (n : nat) (f : nat -> nat) (i : type1000) (h1 : term264 i) : term423 i m n f.
Proof. exact (@lem7047017 m n f i h1). Qed.
Lemma lem7047021 (i : type1000) (m : nat) (n : nat) (f : nat -> nat) (h1 : term264 i) (h2 : term43) (h3 : term48) (h4 : term351 m n f) (h5 : term56 m n f) : (term305 m n f) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (@lem7047018 m n f i h1 (@lem7046976 i m n f h1 h2 h3 h4 h5)). Qed.
Lemma lem7047022 (i : type1000) (m : nat) (n : nat) (f : nat -> nat) (h1 : term264 i) (h2 : term43) (h3 : term48) (h4 : term56 m n f) : term424 m n f.
Proof. exact (fun h0 : term351 m n f => @lem7047021 i m n f h1 h2 h3 h0 h4). Qed.
Lemma lem7047024 (p : Prop) : (term385 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7047025 (m : nat) (n : nat) (f : nat -> nat) : (term424 m n f) = ((term305 m n f) = (@I (nat -> nat) NUMERAL 0)).
Proof. exact (@lem7047024 ((term305 m n f) = (@I (nat -> nat) NUMERAL 0))). Qed.
Lemma lem7047026 (i : type1000) (m : nat) (n : nat) (f : nat -> nat) (h1 : term264 i) (h2 : term43) (h3 : term48) (h4 : term56 m n f) : (term305 m n f) = (@I (nat -> nat) NUMERAL 0).
Proof. exact (EQ_MP (@lem7047025 m n f) (@lem7047022 i m n f h1 h2 h3 h4)). Qed.
Lemma lem7047029 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7047031 (m : nat) (n : nat) (f : nat -> nat) : (term351 m n f) = (term425 m n f).
Proof. exact (@lem7047029 ((term305 m n f) = (@I (nat -> nat) NUMERAL 0))). Qed.
Lemma lem7047034 (m : nat) (n : nat) (f : nat -> nat) (h1 : term56 m n f) : term425 m n f.
Proof. exact (EQ_MP (@lem7047031 m n f) (@lem7046585 m n f h1)). Qed.
Lemma lem7047037 (i : type1000) (m : nat) (n : nat) (f : nat -> nat) (h1 : term264 i) (h2 : term43) (h3 : term48) (h4 : term56 m n f) : False.
Proof. exact (@lem7047034 m n f h4 (@lem7047026 i m n f h1 h2 h3 h4)). Qed.
Lemma lem7047038 (i : type1000) (m : nat) (n : nat) (f : nat -> nat) (h1 : term264 i) (h2 : term43) (h3 : term48) (h4 : term56 m n f) : term426.
Proof. exact (fun h0 : ~ False => @lem7047037 i m n f h1 h2 h3 h4). Qed.
Lemma lem7047040 (p : Prop) : (term385 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7047041 : term426 = False.
Proof. exact (@lem7047040 False). Qed.
Lemma lem7047042 (i : type1000) (m : nat) (n : nat) (f : nat -> nat) (h1 : term264 i) (h2 : term43) (h3 : term48) (h4 : term56 m n f) : False.
Proof. exact (EQ_MP (@lem7047041) (@lem7047038 i m n f h1 h2 h3 h4)). Qed.
Lemma lem7047043 (i : type1000) (m : nat) (f : nat -> nat) (h1 : term264 i) (h2 : term43) (h3 : term48) (h4 : term65 m f) : False.
Proof. exact (ex_elim (@lem7046001 m f h4) (fun n : nat => fun h0 : term64 m f n => @lem7047042 i m n f h1 h2 h3 h0)). Qed.
Lemma lem7047044 (i : type1000) (f : nat -> nat) (h1 : term264 i) (h2 : term43) (h3 : term48) (h4 : term72 f) : False.
Proof. exact (ex_elim (@lem7046000 f h4) (fun m : nat => fun h0 : term71 f m => @lem7047043 i m f h1 h2 h3 h0)). Qed.
Lemma lem7047045 (i : type1000) (h1 : term264 i) (h2 : term43) (h3 : term48) (h4 : term10) : False.
Proof. exact (ex_elim (@lem7045356 h4) (fun f : nat -> nat => fun h0 : term79 f => @lem7047044 i f h1 h2 h3 h0)). Qed.
Lemma lem7047046 (h1 : term17) (h2 : term43) (h3 : term48) (h4 : term10) : False.
Proof. exact (ex_elim (@lem7045998 h1) (fun i : type1000 => fun h0 : term266 i => @lem7047045 i h0 h2 h3 h4)). Qed.
Lemma lem7047047 (h1 : term43) (h2 : term48) (h3 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem7047046 h0 h1 h2 h3). Qed.
Lemma lem7047048 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem7047049 (h1 : term43) (h2 : term48) (h3 : term10) : term16.
Proof. exact (EQ_MP (@lem7047048) (@lem7047047 h1 h2 h3)). Qed.
Lemma lem7047050 (h1 : term48) (h2 : term10) : term20.
Proof. exact (fun h0 : term43 => @lem7047049 h0 h1 h2). Qed.
Lemma lem7047051 (h1 : term10) : term23.
Proof. exact (fun h0 : term48 => @lem7047050 h0 h1). Qed.
Lemma lem7047052 : term25.
Proof. exact (fun h0 : term10 => @lem7047051 h0). Qed.
Lemma lem7047053 : term11.
Proof. exact (EQ_MP (@lem7045254) (@lem7047052)). Qed.
Lemma lem7047055 : term11.
Proof. exact (@lem7044992 (@lem7047053)). Qed.
Lemma lem7047056 (h1 : term10) : term22.
Proof. exact (@lem7047055 (@lem7044977 h1)). Qed.
Lemma lem7047057 (h1 : term10) : term19.
Proof. exact (@lem7047056 h1 (@lem98377)). Qed.
Lemma lem7047058 (h1 : term10) : term15.
Proof. exact (@lem7047057 h1 (@lem93743)). Qed.
Lemma lem7047059 (h1 : term10) : False.
Proof. exact (@lem7047058 h1 (@lem7044635)). Qed.
Lemma lem7047060 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem7047059 h1) (fun h2 : False => @lem7044977 h1)). Qed.
Lemma lem7047061 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem7047060 h1) (@lem7044977 h1)). Qed.
Lemma lem7047062 : term9.
Proof. exact (fun h0 : term10 => @lem7047061 h0). Qed.
Lemma lem7047063 : term8.
Proof. exact (EQ_MP (@lem7044976) (@lem7047062)). Qed.
