Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import REAL_POW_LE2_REV_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339379_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
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
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem1651997 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1651998 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1651999 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1651998 t1) (@lem1651997 t1)). Qed.
Lemma lem1652000 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1651999 t1 t2). Qed.
Lemma lem1652001 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1652002 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1652001 t1 t2) (@lem1652000 t1 t2)). Qed.
Lemma lem1652003 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1652002 t1 t2 t3). Qed.
Lemma lem1652004 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1652005 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1652004 t1 t2 t3) (@lem1652003 t1 t2 t3)). Qed.
Lemma lem1652006 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1652005 t1 t2 t3)). Qed.
Lemma lem1652009 (x : real) (y : real) (h1 : (term7 y x) = (x = y)) : (term7 y x) = (x = y).
Proof. exact (h1). Qed.
Lemma lem1652010 (x : real) (y : real) (h1 : (term7 y x) = (x = y)) : (x = y) = (term7 y x).
Proof. exact (SYM (@lem1652009 x y h1)). Qed.
Lemma lem1652011 (y : real) (x : real) (h1 : (x = y) = (term7 y x)) : (x = y) = (term7 y x).
Proof. exact (h1). Qed.
Lemma lem1652012 (y : real) (x : real) (h1 : (x = y) = (term7 y x)) : (term7 y x) = (x = y).
Proof. exact (SYM (@lem1652011 y x h1)). Qed.
Lemma lem1652013 (y : real) (x : real) : ((term7 y x) = (x = y)) = ((x = y) = (term7 y x)).
Proof. exact (prop_ext (fun h1 : (term7 y x) = (x = y) => @lem1652010 x y h1) (fun h1 : (x = y) = (term7 y x) => @lem1652012 y x h1)). Qed.
Lemma lem1652014 (x : real) : (term8 x) = (term9 x).
Proof. exact (fun_ext (fun y : real => @lem1652013 y x)). Qed.
Lemma lem1652015 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1652016 (x : real) : (term10 x) = (term11 x).
Proof. exact (MK_COMB (@lem1652015) (@lem1652014 x)). Qed.
Lemma lem1652017 : term12 = term13.
Proof. exact (fun_ext (fun x : real => @lem1652016 x)). Qed.
Lemma lem1652018 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1652019 : term14 = term15.
Proof. exact (MK_COMB (@lem1652018) (@lem1652017)). Qed.
Lemma lem1652020 : term15.
Proof. exact (EQ_MP (@lem1652019) (@lem1339379)). Qed.
Lemma lem1652021 (x : real) : term16 x.
Proof. exact (@lem1652020 x). Qed.
Lemma lem1652022 (x : real) : (term16 x) = (term11 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1652023 (x : real) : term11 x.
Proof. exact (EQ_MP (@lem1652022 x) (@lem1652021 x)). Qed.
Lemma lem1652024 (x : real) (y : real) : term17 x y.
Proof. exact (@lem1652023 x y). Qed.
Lemma lem1652025 (y : real) (x : real) : (term17 x y) = ((x = y) = (term7 y x)).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem1652054 (y : real) (x : real) : (x = y) = (term7 y x).
Proof. exact (EQ_MP (@lem1652025 y x) (@lem1652024 x y)). Qed.
Lemma lem1652055 (y : real) (x : real) (n : nat) : ((real_pow x n) = (real_pow y n)) = (term18 y x n).
Proof. exact (@lem1652054 (real_pow y n) (real_pow x n)). Qed.
Lemma lem1652058 (y : real) : (term19 y) = (term19 y).
Proof. exact (eq_refl (term19 y)). Qed.
Lemma lem1652059 (y : real) (x : real) (n : nat) : (term20 x y n) = (term21 y x n).
Proof. exact (MK_COMB (@lem1652058 y) (@lem1652055 y x n)). Qed.
Lemma lem1652062 (x : real) : (term19 x) = (term19 x).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem1652063 (y : real) (x : real) (n : nat) : (term22 x y n) = (term23 y x n).
Proof. exact (MK_COMB (@lem1652062 x) (@lem1652059 y x n)). Qed.
Lemma lem1652066 (n : nat) : (term24 n) = (term24 n).
Proof. exact (eq_refl (term24 n)). Qed.
Lemma lem1652067 (y : real) (x : real) (n : nat) : (term25 x y n) = (term26 y x n).
Proof. exact (MK_COMB (@lem1652066 n) (@lem1652063 y x n)). Qed.
Lemma lem1652070 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1652071 (y : real) (x : real) (n : nat) : (term27 x y n) = (term28 y x n).
Proof. exact (MK_COMB (@lem1652070) (@lem1652067 y x n)). Qed.
Lemma lem1652075 (y : real) (x : real) : (x = y) = (term7 y x).
Proof. exact (EQ_MP (@lem1652025 y x) (@lem1652024 x y)). Qed.
Lemma lem1652078 (n : nat) (y : real) (x : real) : (term29 n x y) = (term30 n y x).
Proof. exact (MK_COMB (@lem1652071 y x n) (@lem1652075 y x)). Qed.
Lemma lem1652081 (n : nat) (x : real) : (term31 n x) = (term32 n x).
Proof. exact (fun_ext (fun y : real => @lem1652078 n y x)). Qed.
Lemma lem1652082 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1652083 (n : nat) (x : real) : (term33 n x) = (term34 n x).
Proof. exact (MK_COMB (@lem1652082) (@lem1652081 n x)). Qed.
Lemma lem1652088 (n : nat) : (term35 n) = (term36 n).
Proof. exact (fun_ext (fun x : real => @lem1652083 n x)). Qed.
Lemma lem1652089 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1652090 (n : nat) : (term37 n) = (term38 n).
Proof. exact (MK_COMB (@lem1652089) (@lem1652088 n)). Qed.
Lemma lem1652095 : term39 = term40.
Proof. exact (fun_ext (fun n : nat => @lem1652090 n)). Qed.
Lemma lem1652096 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1652097 : term41 = term42.
Proof. exact (MK_COMB (@lem1652096) (@lem1652095)). Qed.
Lemma lem1652102 : term42 = term41.
Proof. exact (SYM (@lem1652097)). Qed.
Lemma lem1652104 (p : Prop) : p = (term43 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1652105 : term42 = term44.
Proof. exact (@lem1652104 term42). Qed.
Lemma lem1652106 : term44 = term42.
Proof. exact (SYM (@lem1652105)). Qed.
Lemma lem1652107 (h1 : term45) : term45.
Proof. exact (h1). Qed.
Lemma lem1652110 (h1 : term46) : term46.
Proof. exact (h1). Qed.
Lemma lem1652111 : term47.
Proof. exact (fun h0 : term46 => @lem1652110 h0). Qed.
Lemma lem1652112 (h1 : term47) : term47.
Proof. exact (h1). Qed.
Lemma lem1652113 (h1 : term46) : term46.
Proof. exact (h1). Qed.
Lemma lem1652114 (h1 : term46) (h2 : term47) : term46.
Proof. exact (@lem1652112 h2 (@lem1652113 h1)). Qed.
Lemma lem1652115 (h1 : term46) : term48.
Proof. exact (fun h0 : term47 => @lem1652114 h1 h0). Qed.
Lemma lem1652116 (h1 : term47) : term47.
Proof. exact (h1). Qed.
Lemma lem1652117 (h1 : term46) (h2 : term47) : term46.
Proof. exact (@lem1652115 h1 (@lem1652116 h2)). Qed.
Lemma lem1652118 (h1 : term47) : term47.
Proof. exact (fun h0 : term46 => @lem1652117 h0 h1). Qed.
Lemma lem1652119 : term49.
Proof. exact (fun h0 : term47 => @lem1652118 h0). Qed.
Lemma lem1652122 : term47.
Proof. exact (@lem1652119 (@lem1652111)). Qed.
Lemma lem1652150 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1652151 : term50 = term51.
Proof. exact (@lem1652150 term52). Qed.
Lemma lem1652170 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem1652177 : term46 = term54.
Proof. exact (MK_COMB (@lem1652170) (@lem1652151)). Qed.
Lemma lem1652192 (n : nat) (x : real) (y : real) : (term55 n x y) = (term55 n x y).
Proof. exact (eq_refl (term55 n x y)). Qed.
Lemma lem1652193 (n : nat) (x : real) : (term56 n x) = (term56 n x).
Proof. exact (fun_ext (fun y : real => @lem1652192 n x y)). Qed.
Lemma lem1652194 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1652195 (n : nat) (x : real) : (term57 n x) = (term57 n x).
Proof. exact (MK_COMB (@lem1652194) (@lem1652193 n x)). Qed.
Lemma lem1652196 (n : nat) : (term58 n) = (term58 n).
Proof. exact (fun_ext (fun x : real => @lem1652195 n x)). Qed.
Lemma lem1652197 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1652198 (n : nat) : (term59 n) = (term59 n).
Proof. exact (MK_COMB (@lem1652197) (@lem1652196 n)). Qed.
Lemma lem1652199 : term60 = term60.
Proof. exact (fun_ext (fun n : nat => @lem1652198 n)). Qed.
Lemma lem1652200 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1652201 : term52 = term52.
Proof. exact (MK_COMB (@lem1652200) (@lem1652199)). Qed.
Lemma lem1652202 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1652203 : term51 = term51.
Proof. exact (MK_COMB (@lem1652202) (@lem1652201)). Qed.
Lemma lem1652230 (n : nat) (y : real) (x : real) : (term30 n y x) = (term30 n y x).
Proof. exact (eq_refl (term30 n y x)). Qed.
Lemma lem1652231 (n : nat) (x : real) : (term32 n x) = (term32 n x).
Proof. exact (fun_ext (fun y : real => @lem1652230 n y x)). Qed.
Lemma lem1652232 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1652233 (n : nat) (x : real) : (term34 n x) = (term34 n x).
Proof. exact (MK_COMB (@lem1652232) (@lem1652231 n x)). Qed.
Lemma lem1652234 (n : nat) : (term36 n) = (term36 n).
Proof. exact (fun_ext (fun x : real => @lem1652233 n x)). Qed.
Lemma lem1652235 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1652236 (n : nat) : (term38 n) = (term38 n).
Proof. exact (MK_COMB (@lem1652235) (@lem1652234 n)). Qed.
Lemma lem1652237 : term40 = term40.
Proof. exact (fun_ext (fun n : nat => @lem1652236 n)). Qed.
Lemma lem1652238 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1652239 : term42 = term42.
Proof. exact (MK_COMB (@lem1652238) (@lem1652237)). Qed.
Lemma lem1652240 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1652241 : term45 = term45.
Proof. exact (MK_COMB (@lem1652240) (@lem1652239)). Qed.
Lemma lem1652242 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1652243 : term53 = term53.
Proof. exact (MK_COMB (@lem1652242) (@lem1652241)). Qed.
Lemma lem1652244 : term54 = term54.
Proof. exact (MK_COMB (@lem1652243) (@lem1652203)). Qed.
Lemma lem1652303 : term46 = term54.
Proof. exact (TRANS (@lem1652177) (@lem1652244)). Qed.
Lemma lem1652304 : term54 = term46.
Proof. exact (SYM (@lem1652303)). Qed.
Lemma lem1652305 (h1 : term45) : term45.
Proof. exact (h1). Qed.
Lemma lem1652306 (h1 : term52) : term52.
Proof. exact (h1). Qed.
Lemma lem1652330 (y : real) (x : real) : (term61 y x) = (term62 y x).
Proof. exact (@lem17045 (real_le x y) (real_le y x)). Qed.
Lemma lem1652332 (y : real) (x : real) (n : nat) : (term63 y x n) = (term63 y x n).
Proof. exact (eq_refl (term63 y x n)). Qed.
Lemma lem1652333 (n : nat) (y : real) (x : real) : (term64 n y x) = (term65 n y x).
Proof. exact (MK_COMB (@lem1652332 y x n) (@lem1652330 y x)). Qed.
Lemma lem1652334 (n : nat) (y : real) (x : real) : (term66 n y x) = (term64 n y x).
Proof. exact (@lem17362 (term26 y x n) (term7 y x)). Qed.
Lemma lem1652335 (n : nat) (y : real) (x : real) : (term66 n y x) = (term65 n y x).
Proof. exact (TRANS (@lem1652334 n y x) (@lem1652333 n y x)). Qed.
Lemma lem1652336 (P : real -> Prop) : (term67 P) = (term68 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1652337 (n : nat) (x : real) : (term69 n x) = (term70 n x).
Proof. exact (@lem1652336 (term32 n x)). Qed.
Lemma lem1652338 (n : nat) (y : real) (x : real) : (term71 n x y) = (term30 n y x).
Proof. exact (eq_refl (term71 n x y)). Qed.
Lemma lem1652339 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1652340 (n : nat) (y : real) (x : real) : (term72 n x y) = (term66 n y x).
Proof. exact (MK_COMB (@lem1652339) (@lem1652338 n y x)). Qed.
Lemma lem1652341 (n : nat) (y : real) (x : real) : (term72 n x y) = (term65 n y x).
Proof. exact (TRANS (@lem1652340 n y x) (@lem1652335 n y x)). Qed.
Lemma lem1652342 (n : nat) (x : real) : (term73 n x) = (term74 n x).
Proof. exact (fun_ext (fun y : real => @lem1652341 n y x)). Qed.
Lemma lem1652343 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1652344 (n : nat) (x : real) : (term70 n x) = (term75 n x).
Proof. exact (MK_COMB (@lem1652343) (@lem1652342 n x)). Qed.
Lemma lem1652345 (n : nat) (x : real) : (term69 n x) = (term75 n x).
Proof. exact (TRANS (@lem1652337 n x) (@lem1652344 n x)). Qed.
Lemma lem1652346 (P : real -> Prop) : (term67 P) = (term68 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1652347 (n : nat) : (term76 n) = (term77 n).
Proof. exact (@lem1652346 (term36 n)). Qed.
Lemma lem1652348 (n : nat) (x : real) : (term78 n x) = (term34 n x).
Proof. exact (eq_refl (term78 n x)). Qed.
Lemma lem1652349 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1652350 (n : nat) (x : real) : (term79 n x) = (term69 n x).
Proof. exact (MK_COMB (@lem1652349) (@lem1652348 n x)). Qed.
Lemma lem1652351 (n : nat) (x : real) : (term79 n x) = (term75 n x).
Proof. exact (TRANS (@lem1652350 n x) (@lem1652345 n x)). Qed.
Lemma lem1652352 (n : nat) : (term80 n) = (term81 n).
Proof. exact (fun_ext (fun x : real => @lem1652351 n x)). Qed.
Lemma lem1652353 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1652354 (n : nat) : (term77 n) = (term82 n).
Proof. exact (MK_COMB (@lem1652353) (@lem1652352 n)). Qed.
Lemma lem1652355 (n : nat) : (term76 n) = (term82 n).
Proof. exact (TRANS (@lem1652347 n) (@lem1652354 n)). Qed.
Lemma lem1652356 (P : nat -> Prop) : (term83 P) = (term84 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem1652357 : term45 = term85.
Proof. exact (@lem1652356 term40). Qed.
Lemma lem1652358 (n : nat) : (term86 n) = (term38 n).
Proof. exact (eq_refl (term86 n)). Qed.
Lemma lem1652359 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1652360 (n : nat) : (term87 n) = (term76 n).
Proof. exact (MK_COMB (@lem1652359) (@lem1652358 n)). Qed.
Lemma lem1652361 (n : nat) : (term87 n) = (term82 n).
Proof. exact (TRANS (@lem1652360 n) (@lem1652355 n)). Qed.
Lemma lem1652362 : term88 = term89.
Proof. exact (fun_ext (fun n : nat => @lem1652361 n)). Qed.
Lemma lem1652363 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1652364 : term85 = term90.
Proof. exact (MK_COMB (@lem1652363) (@lem1652362)). Qed.
Lemma lem1652425 : term45 = term90.
Proof. exact (TRANS (@lem1652357) (@lem1652364)). Qed.
Lemma lem1652426 (h1 : term45) : term90.
Proof. exact (EQ_MP (@lem1652425) (@lem1652305 h1)). Qed.
Lemma lem1652429 (n : nat) : (term91 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem1652436 (x : real) (y : real) (n : nat) : (term92 x y n) = (term93 x y n).
Proof. exact (@lem17045 (term94 y) (term95 x y n)). Qed.
Lemma lem1652437 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1652438 (n : nat) : (term96 n) = (term97 n).
Proof. exact (MK_COMB (@lem1652437) (@lem1652429 n)). Qed.
Lemma lem1652439 (x : real) (y : real) (n : nat) : (term98 x y n) = (term99 x y n).
Proof. exact (MK_COMB (@lem1652438 n) (@lem1652436 x y n)). Qed.
Lemma lem1652440 (x : real) (y : real) (n : nat) : (term100 x y n) = (term98 x y n).
Proof. exact (@lem17045 (term101 n) (term102 x y n)). Qed.
Lemma lem1652441 (x : real) (y : real) (n : nat) : (term100 x y n) = (term99 x y n).
Proof. exact (TRANS (@lem1652440 x y n) (@lem1652439 x y n)). Qed.
Lemma lem1652442 (x : real) (y : real) : (real_le x y) = (real_le x y).
Proof. exact (eq_refl (real_le x y)). Qed.
Lemma lem1652443 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1652444 (x : real) (y : real) (n : nat) : (term103 x y n) = (term104 x y n).
Proof. exact (MK_COMB (@lem1652443) (@lem1652441 x y n)). Qed.
Lemma lem1652445 (n : nat) (x : real) (y : real) : (term105 n x y) = (term106 n x y).
Proof. exact (MK_COMB (@lem1652444 x y n) (@lem1652442 x y)). Qed.
Lemma lem1652446 (n : nat) (x : real) (y : real) : (term55 n x y) = (term105 n x y).
Proof. exact (@lem17265 (term107 x y n) (real_le x y)). Qed.
Lemma lem1652447 (n : nat) (x : real) (y : real) : (term55 n x y) = (term106 n x y).
Proof. exact (TRANS (@lem1652446 n x y) (@lem1652445 n x y)). Qed.
Lemma lem1652448 (n : nat) (x : real) : (term56 n x) = (term108 n x).
Proof. exact (fun_ext (fun y : real => @lem1652447 n x y)). Qed.
Lemma lem1652449 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1652450 (n : nat) (x : real) : (term57 n x) = (term109 n x).
Proof. exact (MK_COMB (@lem1652449) (@lem1652448 n x)). Qed.
Lemma lem1652451 (n : nat) : (term58 n) = (term110 n).
Proof. exact (fun_ext (fun x : real => @lem1652450 n x)). Qed.
Lemma lem1652452 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1652453 (n : nat) : (term59 n) = (term111 n).
Proof. exact (MK_COMB (@lem1652452) (@lem1652451 n)). Qed.
Lemma lem1652454 : term60 = term112.
Proof. exact (fun_ext (fun n : nat => @lem1652453 n)). Qed.
Lemma lem1652455 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1652516 : term52 = term113.
Proof. exact (MK_COMB (@lem1652455) (@lem1652454)). Qed.
Lemma lem1652517 (h1 : term52) : term113.
Proof. exact (EQ_MP (@lem1652516) (@lem1652306 h1)). Qed.
Lemma lem1652518 (n : nat) (h1 : term82 n) : term82 n.
Proof. exact (h1). Qed.
Lemma lem1652519 (n : nat) (x : real) (h1 : term75 n x) : term75 n x.
Proof. exact (h1). Qed.
Lemma lem1652567 (n : nat) (x : real) (y : real) : (term106 n x y) = (term106 n x y).
Proof. exact (eq_refl (term106 n x y)). Qed.
Lemma lem1652568 (n : nat) (x : real) : (term108 n x) = (term108 n x).
Proof. exact (fun_ext (fun y : real => @lem1652567 n x y)). Qed.
Lemma lem1652569 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1652570 (n : nat) (x : real) : (term109 n x) = (term109 n x).
Proof. exact (MK_COMB (@lem1652569) (@lem1652568 n x)). Qed.
Lemma lem1652571 (n : nat) : (term110 n) = (term110 n).
Proof. exact (fun_ext (fun x : real => @lem1652570 n x)). Qed.
Lemma lem1652572 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1652573 (n : nat) : (term111 n) = (term111 n).
Proof. exact (MK_COMB (@lem1652572) (@lem1652571 n)). Qed.
Lemma lem1652574 : term112 = term112.
Proof. exact (fun_ext (fun n : nat => @lem1652573 n)). Qed.
Lemma lem1652575 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1652576 : term113 = term113.
Proof. exact (MK_COMB (@lem1652575) (@lem1652574)). Qed.
Lemma lem1652577 (h1 : term52) : term113.
Proof. exact (EQ_MP (@lem1652576) (@lem1652517 h1)). Qed.
Lemma lem1652663 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term65 n y x.
Proof. exact (h1). Qed.
Lemma lem1652664 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term62 y x.
Proof. exact (proj2 (@lem1652663 n y x h1)). Qed.
Lemma lem1652665 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term26 y x n.
Proof. exact (proj1 (@lem1652663 n y x h1)). Qed.
Lemma lem1652666 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term23 y x n.
Proof. exact (proj2 (@lem1652665 n y x h1)). Qed.
Lemma lem1652668 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term21 y x n.
Proof. exact (proj2 (@lem1652666 n y x h1)). Qed.
Lemma lem1652670 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term18 y x n.
Proof. exact (proj2 (@lem1652668 n y x h1)). Qed.
Lemma lem1652695 (n : nat) (x : real) (y : real) : (term106 n x y) = (term106 n x y).
Proof. exact (eq_refl (term106 n x y)). Qed.
Lemma lem1652696 (n : nat) (x : real) : (term108 n x) = (term108 n x).
Proof. exact (fun_ext (fun y : real => @lem1652695 n x y)). Qed.
Lemma lem1652697 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1652698 (n : nat) (x : real) : (term109 n x) = (term109 n x).
Proof. exact (MK_COMB (@lem1652697) (@lem1652696 n x)). Qed.
Lemma lem1652699 (n : nat) : (term110 n) = (term110 n).
Proof. exact (fun_ext (fun x : real => @lem1652698 n x)). Qed.
Lemma lem1652700 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1652701 (n : nat) : (term111 n) = (term111 n).
Proof. exact (MK_COMB (@lem1652700) (@lem1652699 n)). Qed.
Lemma lem1652702 : term112 = term112.
Proof. exact (fun_ext (fun n : nat => @lem1652701 n)). Qed.
Lemma lem1652703 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1652705 : term113 = term113.
Proof. exact (MK_COMB (@lem1652703) (@lem1652702)). Qed.
Lemma lem1652706 (h1 : term52) : term113.
Proof. exact (EQ_MP (@lem1652705) (@lem1652577 h1)). Qed.
Lemma lem1652730 (x : real) (y : real) (h1 : term114 x y) : term114 x y.
Proof. exact (h1). Qed.
Lemma lem1652750 (n : nat) (x : real) (y : real) : (term106 n x y) = (term106 n x y).
Proof. exact (eq_refl (term106 n x y)). Qed.
Lemma lem1652751 (n : nat) (x : real) : (term108 n x) = (term108 n x).
Proof. exact (fun_ext (fun y : real => @lem1652750 n x y)). Qed.
Lemma lem1652752 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1652753 (n : nat) (x : real) : (term109 n x) = (term109 n x).
Proof. exact (MK_COMB (@lem1652752) (@lem1652751 n x)). Qed.
Lemma lem1652754 (n : nat) : (term110 n) = (term110 n).
Proof. exact (fun_ext (fun x : real => @lem1652753 n x)). Qed.
Lemma lem1652755 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1652756 (n : nat) : (term111 n) = (term111 n).
Proof. exact (MK_COMB (@lem1652755) (@lem1652754 n)). Qed.
Lemma lem1652757 : term112 = term112.
Proof. exact (fun_ext (fun n : nat => @lem1652756 n)). Qed.
Lemma lem1652758 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1652760 : term113 = term113.
Proof. exact (MK_COMB (@lem1652758) (@lem1652757)). Qed.
Lemma lem1652761 (h1 : term52) : term113.
Proof. exact (EQ_MP (@lem1652760) (@lem1652577 h1)). Qed.
Lemma lem1652785 (y : real) (x : real) (h1 : term114 y x) : term114 y x.
Proof. exact (h1). Qed.
Lemma lem1652786 (_25609 : nat) (h1 : term52) : term115 _25609.
Proof. exact (@lem1652706 h1 _25609). Qed.
Lemma lem1652787 (_25609 : nat) : (term115 _25609) = (term111 _25609).
Proof. exact (eq_refl (term115 _25609)). Qed.
Lemma lem1652788 (_25609 : nat) (h1 : term52) : term111 _25609.
Proof. exact (EQ_MP (@lem1652787 _25609) (@lem1652786 _25609 h1)). Qed.
Lemma lem1652789 (_25609 : nat) (_25610 : real) (h1 : term52) : term116 _25609 _25610.
Proof. exact (@lem1652788 _25609 h1 _25610). Qed.
Lemma lem1652790 (_25609 : nat) (_25610 : real) : (term116 _25609 _25610) = (term109 _25609 _25610).
Proof. exact (eq_refl (term116 _25609 _25610)). Qed.
Lemma lem1652791 (_25609 : nat) (_25610 : real) (h1 : term52) : term109 _25609 _25610.
Proof. exact (EQ_MP (@lem1652790 _25609 _25610) (@lem1652789 _25609 _25610 h1)). Qed.
Lemma lem1652792 (_25609 : nat) (_25610 : real) (_25611 : real) (h1 : term52) : term117 _25609 _25610 _25611.
Proof. exact (@lem1652791 _25609 _25610 h1 _25611). Qed.
Lemma lem1652793 (_25609 : nat) (_25610 : real) (_25611 : real) : (term117 _25609 _25610 _25611) = (term106 _25609 _25610 _25611).
Proof. exact (eq_refl (term117 _25609 _25610 _25611)). Qed.
Lemma lem1652794 (_25609 : nat) (_25610 : real) (_25611 : real) (h1 : term52) : term106 _25609 _25610 _25611.
Proof. exact (EQ_MP (@lem1652793 _25609 _25610 _25611) (@lem1652792 _25609 _25610 _25611 h1)). Qed.
Lemma lem1652795 (_25612 : nat) (h1 : term52) : term115 _25612.
Proof. exact (@lem1652761 h1 _25612). Qed.
Lemma lem1652796 (_25612 : nat) : (term115 _25612) = (term111 _25612).
Proof. exact (eq_refl (term115 _25612)). Qed.
Lemma lem1652797 (_25612 : nat) (h1 : term52) : term111 _25612.
Proof. exact (EQ_MP (@lem1652796 _25612) (@lem1652795 _25612 h1)). Qed.
Lemma lem1652798 (_25612 : nat) (_25613 : real) (h1 : term52) : term116 _25612 _25613.
Proof. exact (@lem1652797 _25612 h1 _25613). Qed.
Lemma lem1652799 (_25612 : nat) (_25613 : real) : (term116 _25612 _25613) = (term109 _25612 _25613).
Proof. exact (eq_refl (term116 _25612 _25613)). Qed.
Lemma lem1652800 (_25612 : nat) (_25613 : real) (h1 : term52) : term109 _25612 _25613.
Proof. exact (EQ_MP (@lem1652799 _25612 _25613) (@lem1652798 _25612 _25613 h1)). Qed.
Lemma lem1652801 (_25612 : nat) (_25613 : real) (_25614 : real) (h1 : term52) : term117 _25612 _25613 _25614.
Proof. exact (@lem1652800 _25612 _25613 h1 _25614). Qed.
Lemma lem1652802 (_25612 : nat) (_25613 : real) (_25614 : real) : (term117 _25612 _25613 _25614) = (term106 _25612 _25613 _25614).
Proof. exact (eq_refl (term117 _25612 _25613 _25614)). Qed.
Lemma lem1652803 (_25612 : nat) (_25613 : real) (_25614 : real) (h1 : term52) : term106 _25612 _25613 _25614.
Proof. exact (EQ_MP (@lem1652802 _25612 _25613 _25614) (@lem1652801 _25612 _25613 _25614 h1)). Qed.
Lemma lem1652807 (_25609 : nat) (_25610 : real) (_25611 : real) : (term106 _25609 _25610 _25611) = (term118 _25609 _25610 _25611).
Proof. exact (@lem1652006 (_25609 = (NUMERAL 0)) (term93 _25610 _25611 _25609) (real_le _25610 _25611)). Qed.
Lemma lem1652814 (_25609 : nat) (_25610 : real) (_25611 : real) : (term119 _25609 _25610 _25611) = (term120 _25609 _25610 _25611).
Proof. exact (@lem1652006 (term121 _25611) (term122 _25610 _25611 _25609) (real_le _25610 _25611)). Qed.
Lemma lem1652815 (_25609 : nat) : (term97 _25609) = (term97 _25609).
Proof. exact (eq_refl (term97 _25609)). Qed.
Lemma lem1652818 (_25609 : nat) (_25610 : real) (_25611 : real) : (term118 _25609 _25610 _25611) = (term123 _25609 _25610 _25611).
Proof. exact (MK_COMB (@lem1652815 _25609) (@lem1652814 _25609 _25610 _25611)). Qed.
Lemma lem1652820 (_25609 : nat) (_25610 : real) (_25611 : real) : (term106 _25609 _25610 _25611) = (term123 _25609 _25610 _25611).
Proof. exact (TRANS (@lem1652807 _25609 _25610 _25611) (@lem1652818 _25609 _25610 _25611)). Qed.
Lemma lem1652821 (_25609 : nat) (_25610 : real) (_25611 : real) (h1 : term52) : term123 _25609 _25610 _25611.
Proof. exact (EQ_MP (@lem1652820 _25609 _25610 _25611) (@lem1652794 _25609 _25610 _25611 h1)). Qed.
Lemma lem1652833 (x : real) (y : real) (h1 : term114 x y) : term114 x y.
Proof. exact (h1). Qed.
Lemma lem1652837 (_25612 : nat) (_25613 : real) (_25614 : real) : (term106 _25612 _25613 _25614) = (term118 _25612 _25613 _25614).
Proof. exact (@lem1652006 (_25612 = (NUMERAL 0)) (term93 _25613 _25614 _25612) (real_le _25613 _25614)). Qed.
Lemma lem1652844 (_25612 : nat) (_25613 : real) (_25614 : real) : (term119 _25612 _25613 _25614) = (term120 _25612 _25613 _25614).
Proof. exact (@lem1652006 (term121 _25614) (term122 _25613 _25614 _25612) (real_le _25613 _25614)). Qed.
Lemma lem1652845 (_25612 : nat) : (term97 _25612) = (term97 _25612).
Proof. exact (eq_refl (term97 _25612)). Qed.
Lemma lem1652848 (_25612 : nat) (_25613 : real) (_25614 : real) : (term118 _25612 _25613 _25614) = (term123 _25612 _25613 _25614).
Proof. exact (MK_COMB (@lem1652845 _25612) (@lem1652844 _25612 _25613 _25614)). Qed.
Lemma lem1652850 (_25612 : nat) (_25613 : real) (_25614 : real) : (term106 _25612 _25613 _25614) = (term123 _25612 _25613 _25614).
Proof. exact (TRANS (@lem1652837 _25612 _25613 _25614) (@lem1652848 _25612 _25613 _25614)). Qed.
Lemma lem1652851 (_25612 : nat) (_25613 : real) (_25614 : real) (h1 : term52) : term123 _25612 _25613 _25614.
Proof. exact (EQ_MP (@lem1652850 _25612 _25613 _25614) (@lem1652803 _25612 _25613 _25614 h1)). Qed.
Lemma lem1652863 (y : real) (x : real) (h1 : term114 y x) : term114 y x.
Proof. exact (h1). Qed.
Lemma lem1652919 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term101 n.
Proof. exact (proj1 (@lem1652665 n y x h1)). Qed.
Lemma lem1652920 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term124 n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem1652919 n y x h1). Qed.
Lemma lem1652922 (p : Prop) : (term125 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1652923 (n : nat) : (term124 n) = (term101 n).
Proof. exact (@lem1652922 (n = (NUMERAL 0))). Qed.
Lemma lem1652924 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term101 n.
Proof. exact (EQ_MP (@lem1652923 n) (@lem1652920 n y x h1)). Qed.
Lemma lem1652926 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term94 y.
Proof. exact (proj1 (@lem1652668 n y x h1)). Qed.
Lemma lem1652927 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term126 y.
Proof. exact (fun h0 : term121 y => @lem1652926 n y x h1). Qed.
Lemma lem1652929 (p : Prop) : (term127 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1652930 (y : real) : (term126 y) = (term94 y).
Proof. exact (@lem1652929 (term94 y)). Qed.
Lemma lem1652931 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term94 y.
Proof. exact (EQ_MP (@lem1652930 y) (@lem1652927 n y x h1)). Qed.
Lemma lem1652933 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term95 x y n.
Proof. exact (proj1 (@lem1652670 n y x h1)). Qed.
Lemma lem1652934 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term128 x y n.
Proof. exact (fun h0 : term122 x y n => @lem1652933 n y x h1). Qed.
Lemma lem1652936 (p : Prop) : (term127 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1652937 (x : real) (y : real) (n : nat) : (term128 x y n) = (term95 x y n).
Proof. exact (@lem1652936 (term95 x y n)). Qed.
Lemma lem1652938 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term95 x y n.
Proof. exact (EQ_MP (@lem1652937 x y n) (@lem1652934 n y x h1)). Qed.
Lemma lem1652966 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1652967 (_25610 : real) (_25611 : real) (_25609 : nat) : (term129 _25609 _25610 _25611) = (term130 _25610 _25611 _25609).
Proof. exact (@lem1652966 (real_le _25610 _25611) (term122 _25610 _25611 _25609)). Qed.
Lemma lem1652973 (_25611 : real) : (term131 _25611) = (term131 _25611).
Proof. exact (eq_refl (term131 _25611)). Qed.
Lemma lem1652974 (_25610 : real) (_25611 : real) (_25609 : nat) : (term120 _25609 _25610 _25611) = (term132 _25610 _25611 _25609).
Proof. exact (MK_COMB (@lem1652973 _25611) (@lem1652967 _25610 _25611 _25609)). Qed.
Lemma lem1652978 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1652979 (_25610 : real) (_25611 : real) (_25609 : nat) : (term132 _25610 _25611 _25609) = (term133 _25610 _25611 _25609).
Proof. exact (@lem1652978 (real_le _25610 _25611) (term121 _25611) (term122 _25610 _25611 _25609)). Qed.
Lemma lem1652995 (_25610 : real) (_25611 : real) (_25609 : nat) : (term120 _25609 _25610 _25611) = (term133 _25610 _25611 _25609).
Proof. exact (TRANS (@lem1652974 _25610 _25611 _25609) (@lem1652979 _25610 _25611 _25609)). Qed.
Lemma lem1652996 (_25609 : nat) : (term97 _25609) = (term97 _25609).
Proof. exact (eq_refl (term97 _25609)). Qed.
Lemma lem1652997 (_25610 : real) (_25611 : real) (_25609 : nat) : (term123 _25609 _25610 _25611) = (term134 _25610 _25611 _25609).
Proof. exact (MK_COMB (@lem1652996 _25609) (@lem1652995 _25610 _25611 _25609)). Qed.
Lemma lem1653008 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1653009 (_25610 : real) (_25611 : real) (_25609 : nat) : (term135 _25609 _25610 _25611) = (term136 _25610 _25611 _25609).
Proof. exact (MK_COMB (@lem1653008) (@lem1652997 _25610 _25611 _25609)). Qed.
Lemma lem1653013 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1653014 (_25610 : real) (_25611 : real) (_25609 : nat) : (term137 _25610 _25611 _25609) = (term134 _25610 _25611 _25609).
Proof. exact (@lem1653013 (_25609 = (NUMERAL 0)) (real_le _25610 _25611) (term93 _25610 _25611 _25609)). Qed.
Lemma lem1653042 (_25610 : real) (_25611 : real) (_25609 : nat) : ((term123 _25609 _25610 _25611) = (term137 _25610 _25611 _25609)) = ((term134 _25610 _25611 _25609) = (term134 _25610 _25611 _25609)).
Proof. exact (MK_COMB (@lem1653009 _25610 _25611 _25609) (@lem1653014 _25610 _25611 _25609)). Qed.
Lemma lem1653044 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1653045 (x : Prop) : (x = x) = True.
Proof. exact (@lem1653044 Prop x). Qed.
Lemma lem1653046 (_25610 : real) (_25611 : real) (_25609 : nat) : ((term134 _25610 _25611 _25609) = (term134 _25610 _25611 _25609)) = True.
Proof. exact (@lem1653045 (term134 _25610 _25611 _25609)). Qed.
Lemma lem1653047 (_25610 : real) (_25611 : real) (_25609 : nat) : ((term123 _25609 _25610 _25611) = (term137 _25610 _25611 _25609)) = True.
Proof. exact (TRANS (@lem1653042 _25610 _25611 _25609) (@lem1653046 _25610 _25611 _25609)). Qed.
Lemma lem1653048 (_25610 : real) (_25611 : real) (_25609 : nat) : True = ((term123 _25609 _25610 _25611) = (term137 _25610 _25611 _25609)).
Proof. exact (SYM (@lem1653047 _25610 _25611 _25609)). Qed.
Lemma lem1653049 (_25610 : real) (_25611 : real) (_25609 : nat) : (term123 _25609 _25610 _25611) = (term137 _25610 _25611 _25609).
Proof. exact (EQ_MP (@lem1653048 _25610 _25611 _25609) (@lem0)). Qed.
Lemma lem1653050 (_25610 : real) (_25611 : real) (_25609 : nat) (h1 : term52) : term137 _25610 _25611 _25609.
Proof. exact (EQ_MP (@lem1653049 _25610 _25611 _25609) (@lem1652821 _25609 _25610 _25611 h1)). Qed.
Lemma lem1653052 (b : Prop) (a : Prop) : (a \/ b) = (term138 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1653053 (_25609 : nat) (_25610 : real) (_25611 : real) : (term137 _25610 _25611 _25609) = (term139 _25609 _25610 _25611).
Proof. exact (@lem1653052 (term99 _25610 _25611 _25609) (real_le _25610 _25611)). Qed.
Lemma lem1653055 (a : Prop) (b : Prop) : (term140 a b) = (term141 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1653056 (_25610 : real) (_25611 : real) (_25609 : nat) : (term142 _25610 _25611 _25609) = (term143 _25610 _25611 _25609).
Proof. exact (@lem1653055 (_25609 = (NUMERAL 0)) (term93 _25610 _25611 _25609)). Qed.
Lemma lem1653058 (a : Prop) (b : Prop) : (term140 a b) = (term141 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1653059 (_25610 : real) (_25611 : real) (_25609 : nat) : (term144 _25610 _25611 _25609) = (term145 _25610 _25611 _25609).
Proof. exact (@lem1653058 (term121 _25611) (term122 _25610 _25611 _25609)). Qed.
Lemma lem1653061 (a : Prop) : (term146 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1653062 (_25611 : real) : (term147 _25611) = (term94 _25611).
Proof. exact (@lem1653061 (term94 _25611)). Qed.
Lemma lem1653063 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1653064 (_25611 : real) : (term148 _25611) = (term19 _25611).
Proof. exact (MK_COMB (@lem1653063) (@lem1653062 _25611)). Qed.
Lemma lem1653066 (a : Prop) : (term146 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1653067 (_25610 : real) (_25611 : real) (_25609 : nat) : (term149 _25610 _25611 _25609) = (term95 _25610 _25611 _25609).
Proof. exact (@lem1653066 (term95 _25610 _25611 _25609)). Qed.
Lemma lem1653068 (_25610 : real) (_25611 : real) (_25609 : nat) : (term145 _25610 _25611 _25609) = (term102 _25610 _25611 _25609).
Proof. exact (MK_COMB (@lem1653064 _25611) (@lem1653067 _25610 _25611 _25609)). Qed.
Lemma lem1653069 (_25610 : real) (_25611 : real) (_25609 : nat) : (term144 _25610 _25611 _25609) = (term102 _25610 _25611 _25609).
Proof. exact (TRANS (@lem1653059 _25610 _25611 _25609) (@lem1653068 _25610 _25611 _25609)). Qed.
Lemma lem1653070 (_25609 : nat) : (term24 _25609) = (term24 _25609).
Proof. exact (eq_refl (term24 _25609)). Qed.
Lemma lem1653071 (_25610 : real) (_25611 : real) (_25609 : nat) : (term143 _25610 _25611 _25609) = (term107 _25610 _25611 _25609).
Proof. exact (MK_COMB (@lem1653070 _25609) (@lem1653069 _25610 _25611 _25609)). Qed.
Lemma lem1653072 (_25610 : real) (_25611 : real) (_25609 : nat) : (term142 _25610 _25611 _25609) = (term107 _25610 _25611 _25609).
Proof. exact (TRANS (@lem1653056 _25610 _25611 _25609) (@lem1653071 _25610 _25611 _25609)). Qed.
Lemma lem1653073 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1653074 (_25610 : real) (_25611 : real) (_25609 : nat) : (term150 _25610 _25611 _25609) = (term151 _25610 _25611 _25609).
Proof. exact (MK_COMB (@lem1653073) (@lem1653072 _25610 _25611 _25609)). Qed.
Lemma lem1653075 (_25610 : real) (_25611 : real) : (real_le _25610 _25611) = (real_le _25610 _25611).
Proof. exact (eq_refl (real_le _25610 _25611)). Qed.
Lemma lem1653076 (_25609 : nat) (_25610 : real) (_25611 : real) : (term139 _25609 _25610 _25611) = (term55 _25609 _25610 _25611).
Proof. exact (MK_COMB (@lem1653074 _25610 _25611 _25609) (@lem1653075 _25610 _25611)). Qed.
Lemma lem1653077 (_25609 : nat) (_25610 : real) (_25611 : real) : (term137 _25610 _25611 _25609) = (term55 _25609 _25610 _25611).
Proof. exact (TRANS (@lem1653053 _25609 _25610 _25611) (@lem1653076 _25609 _25610 _25611)). Qed.
Lemma lem1653079 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term102 x y n.
Proof. exact (conj (@lem1652931 n y x h1) (@lem1652938 n y x h1)). Qed.
Lemma lem1653080 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term107 x y n.
Proof. exact (conj (@lem1652924 n y x h1) (@lem1653079 n y x h1)). Qed.
Lemma lem1653082 (_25609 : nat) (_25610 : real) (_25611 : real) (h1 : term52) : term55 _25609 _25610 _25611.
Proof. exact (EQ_MP (@lem1653077 _25609 _25610 _25611) (@lem1653050 _25610 _25611 _25609 h1)). Qed.
Lemma lem1653083 (n : nat) (x : real) (y : real) (h1 : term52) : term55 n x y.
Proof. exact (@lem1653082 n x y h1). Qed.
Lemma lem1653086 (n : nat) (y : real) (x : real) (h1 : term52) (h2 : term65 n y x) : real_le x y.
Proof. exact (@lem1653083 n x y h1 (@lem1653080 n y x h2)). Qed.
Lemma lem1653087 (n : nat) (y : real) (x : real) (h1 : term52) (h2 : term65 n y x) : term152 x y.
Proof. exact (fun h0 : term114 x y => @lem1653086 n y x h1 h2). Qed.
Lemma lem1653089 (p : Prop) : (term127 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1653090 (x : real) (y : real) : (term152 x y) = (real_le x y).
Proof. exact (@lem1653089 (real_le x y)). Qed.
Lemma lem1653091 (n : nat) (y : real) (x : real) (h1 : term52) (h2 : term65 n y x) : real_le x y.
Proof. exact (EQ_MP (@lem1653090 x y) (@lem1653087 n y x h1 h2)). Qed.
Lemma lem1653094 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1653096 (x : real) (y : real) : (term114 x y) = (term153 x y).
Proof. exact (@lem1653094 (real_le x y)). Qed.
Lemma lem1653099 (x : real) (y : real) (h1 : term114 x y) : term153 x y.
Proof. exact (EQ_MP (@lem1653096 x y) (@lem1652833 x y h1)). Qed.
Lemma lem1653102 (n : nat) (y : real) (x : real) (h1 : term52) (h2 : term114 x y) (h3 : term65 n y x) : False.
Proof. exact (@lem1653099 x y h2 (@lem1653091 n y x h1 h3)). Qed.
Lemma lem1653103 (n : nat) (y : real) (x : real) (h1 : term52) (h2 : term114 x y) (h3 : term65 n y x) : term154.
Proof. exact (fun h0 : ~ False => @lem1653102 n y x h1 h2 h3). Qed.
Lemma lem1653105 (p : Prop) : (term127 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1653106 : term154 = False.
Proof. exact (@lem1653105 False). Qed.
Lemma lem1653107 (n : nat) (y : real) (x : real) (h1 : term52) (h2 : term114 x y) (h3 : term65 n y x) : False.
Proof. exact (EQ_MP (@lem1653106) (@lem1653103 n y x h1 h2 h3)). Qed.
Lemma lem1653163 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term101 n.
Proof. exact (proj1 (@lem1652665 n y x h1)). Qed.
Lemma lem1653164 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term124 n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem1653163 n y x h1). Qed.
Lemma lem1653166 (p : Prop) : (term125 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1653167 (n : nat) : (term124 n) = (term101 n).
Proof. exact (@lem1653166 (n = (NUMERAL 0))). Qed.
Lemma lem1653168 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term101 n.
Proof. exact (EQ_MP (@lem1653167 n) (@lem1653164 n y x h1)). Qed.
Lemma lem1653170 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term94 x.
Proof. exact (proj1 (@lem1652666 n y x h1)). Qed.
Lemma lem1653171 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term126 x.
Proof. exact (fun h0 : term121 x => @lem1653170 n y x h1). Qed.
Lemma lem1653173 (p : Prop) : (term127 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1653174 (x : real) : (term126 x) = (term94 x).
Proof. exact (@lem1653173 (term94 x)). Qed.
Lemma lem1653175 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term94 x.
Proof. exact (EQ_MP (@lem1653174 x) (@lem1653171 n y x h1)). Qed.
Lemma lem1653177 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term95 y x n.
Proof. exact (proj2 (@lem1652670 n y x h1)). Qed.
Lemma lem1653178 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term128 y x n.
Proof. exact (fun h0 : term122 y x n => @lem1653177 n y x h1). Qed.
Lemma lem1653180 (p : Prop) : (term127 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1653181 (y : real) (x : real) (n : nat) : (term128 y x n) = (term95 y x n).
Proof. exact (@lem1653180 (term95 y x n)). Qed.
Lemma lem1653182 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term95 y x n.
Proof. exact (EQ_MP (@lem1653181 y x n) (@lem1653178 n y x h1)). Qed.
Lemma lem1653210 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1653211 (_25613 : real) (_25614 : real) (_25612 : nat) : (term129 _25612 _25613 _25614) = (term130 _25613 _25614 _25612).
Proof. exact (@lem1653210 (real_le _25613 _25614) (term122 _25613 _25614 _25612)). Qed.
Lemma lem1653217 (_25614 : real) : (term131 _25614) = (term131 _25614).
Proof. exact (eq_refl (term131 _25614)). Qed.
Lemma lem1653218 (_25613 : real) (_25614 : real) (_25612 : nat) : (term120 _25612 _25613 _25614) = (term132 _25613 _25614 _25612).
Proof. exact (MK_COMB (@lem1653217 _25614) (@lem1653211 _25613 _25614 _25612)). Qed.
Lemma lem1653222 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1653223 (_25613 : real) (_25614 : real) (_25612 : nat) : (term132 _25613 _25614 _25612) = (term133 _25613 _25614 _25612).
Proof. exact (@lem1653222 (real_le _25613 _25614) (term121 _25614) (term122 _25613 _25614 _25612)). Qed.
Lemma lem1653239 (_25613 : real) (_25614 : real) (_25612 : nat) : (term120 _25612 _25613 _25614) = (term133 _25613 _25614 _25612).
Proof. exact (TRANS (@lem1653218 _25613 _25614 _25612) (@lem1653223 _25613 _25614 _25612)). Qed.
Lemma lem1653240 (_25612 : nat) : (term97 _25612) = (term97 _25612).
Proof. exact (eq_refl (term97 _25612)). Qed.
Lemma lem1653241 (_25613 : real) (_25614 : real) (_25612 : nat) : (term123 _25612 _25613 _25614) = (term134 _25613 _25614 _25612).
Proof. exact (MK_COMB (@lem1653240 _25612) (@lem1653239 _25613 _25614 _25612)). Qed.
Lemma lem1653252 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1653253 (_25613 : real) (_25614 : real) (_25612 : nat) : (term135 _25612 _25613 _25614) = (term136 _25613 _25614 _25612).
Proof. exact (MK_COMB (@lem1653252) (@lem1653241 _25613 _25614 _25612)). Qed.
Lemma lem1653257 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1653258 (_25613 : real) (_25614 : real) (_25612 : nat) : (term137 _25613 _25614 _25612) = (term134 _25613 _25614 _25612).
Proof. exact (@lem1653257 (_25612 = (NUMERAL 0)) (real_le _25613 _25614) (term93 _25613 _25614 _25612)). Qed.
Lemma lem1653286 (_25613 : real) (_25614 : real) (_25612 : nat) : ((term123 _25612 _25613 _25614) = (term137 _25613 _25614 _25612)) = ((term134 _25613 _25614 _25612) = (term134 _25613 _25614 _25612)).
Proof. exact (MK_COMB (@lem1653253 _25613 _25614 _25612) (@lem1653258 _25613 _25614 _25612)). Qed.
Lemma lem1653288 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1653289 (x : Prop) : (x = x) = True.
Proof. exact (@lem1653288 Prop x). Qed.
Lemma lem1653290 (_25613 : real) (_25614 : real) (_25612 : nat) : ((term134 _25613 _25614 _25612) = (term134 _25613 _25614 _25612)) = True.
Proof. exact (@lem1653289 (term134 _25613 _25614 _25612)). Qed.
Lemma lem1653291 (_25613 : real) (_25614 : real) (_25612 : nat) : ((term123 _25612 _25613 _25614) = (term137 _25613 _25614 _25612)) = True.
Proof. exact (TRANS (@lem1653286 _25613 _25614 _25612) (@lem1653290 _25613 _25614 _25612)). Qed.
Lemma lem1653292 (_25613 : real) (_25614 : real) (_25612 : nat) : True = ((term123 _25612 _25613 _25614) = (term137 _25613 _25614 _25612)).
Proof. exact (SYM (@lem1653291 _25613 _25614 _25612)). Qed.
Lemma lem1653293 (_25613 : real) (_25614 : real) (_25612 : nat) : (term123 _25612 _25613 _25614) = (term137 _25613 _25614 _25612).
Proof. exact (EQ_MP (@lem1653292 _25613 _25614 _25612) (@lem0)). Qed.
Lemma lem1653294 (_25613 : real) (_25614 : real) (_25612 : nat) (h1 : term52) : term137 _25613 _25614 _25612.
Proof. exact (EQ_MP (@lem1653293 _25613 _25614 _25612) (@lem1652851 _25612 _25613 _25614 h1)). Qed.
Lemma lem1653296 (b : Prop) (a : Prop) : (a \/ b) = (term138 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1653297 (_25612 : nat) (_25613 : real) (_25614 : real) : (term137 _25613 _25614 _25612) = (term139 _25612 _25613 _25614).
Proof. exact (@lem1653296 (term99 _25613 _25614 _25612) (real_le _25613 _25614)). Qed.
Lemma lem1653299 (a : Prop) (b : Prop) : (term140 a b) = (term141 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1653300 (_25613 : real) (_25614 : real) (_25612 : nat) : (term142 _25613 _25614 _25612) = (term143 _25613 _25614 _25612).
Proof. exact (@lem1653299 (_25612 = (NUMERAL 0)) (term93 _25613 _25614 _25612)). Qed.
Lemma lem1653302 (a : Prop) (b : Prop) : (term140 a b) = (term141 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1653303 (_25613 : real) (_25614 : real) (_25612 : nat) : (term144 _25613 _25614 _25612) = (term145 _25613 _25614 _25612).
Proof. exact (@lem1653302 (term121 _25614) (term122 _25613 _25614 _25612)). Qed.
Lemma lem1653305 (a : Prop) : (term146 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1653306 (_25614 : real) : (term147 _25614) = (term94 _25614).
Proof. exact (@lem1653305 (term94 _25614)). Qed.
Lemma lem1653307 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1653308 (_25614 : real) : (term148 _25614) = (term19 _25614).
Proof. exact (MK_COMB (@lem1653307) (@lem1653306 _25614)). Qed.
Lemma lem1653310 (a : Prop) : (term146 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1653311 (_25613 : real) (_25614 : real) (_25612 : nat) : (term149 _25613 _25614 _25612) = (term95 _25613 _25614 _25612).
Proof. exact (@lem1653310 (term95 _25613 _25614 _25612)). Qed.
Lemma lem1653312 (_25613 : real) (_25614 : real) (_25612 : nat) : (term145 _25613 _25614 _25612) = (term102 _25613 _25614 _25612).
Proof. exact (MK_COMB (@lem1653308 _25614) (@lem1653311 _25613 _25614 _25612)). Qed.
Lemma lem1653313 (_25613 : real) (_25614 : real) (_25612 : nat) : (term144 _25613 _25614 _25612) = (term102 _25613 _25614 _25612).
Proof. exact (TRANS (@lem1653303 _25613 _25614 _25612) (@lem1653312 _25613 _25614 _25612)). Qed.
Lemma lem1653314 (_25612 : nat) : (term24 _25612) = (term24 _25612).
Proof. exact (eq_refl (term24 _25612)). Qed.
Lemma lem1653315 (_25613 : real) (_25614 : real) (_25612 : nat) : (term143 _25613 _25614 _25612) = (term107 _25613 _25614 _25612).
Proof. exact (MK_COMB (@lem1653314 _25612) (@lem1653313 _25613 _25614 _25612)). Qed.
Lemma lem1653316 (_25613 : real) (_25614 : real) (_25612 : nat) : (term142 _25613 _25614 _25612) = (term107 _25613 _25614 _25612).
Proof. exact (TRANS (@lem1653300 _25613 _25614 _25612) (@lem1653315 _25613 _25614 _25612)). Qed.
Lemma lem1653317 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1653318 (_25613 : real) (_25614 : real) (_25612 : nat) : (term150 _25613 _25614 _25612) = (term151 _25613 _25614 _25612).
Proof. exact (MK_COMB (@lem1653317) (@lem1653316 _25613 _25614 _25612)). Qed.
Lemma lem1653319 (_25613 : real) (_25614 : real) : (real_le _25613 _25614) = (real_le _25613 _25614).
Proof. exact (eq_refl (real_le _25613 _25614)). Qed.
Lemma lem1653320 (_25612 : nat) (_25613 : real) (_25614 : real) : (term139 _25612 _25613 _25614) = (term55 _25612 _25613 _25614).
Proof. exact (MK_COMB (@lem1653318 _25613 _25614 _25612) (@lem1653319 _25613 _25614)). Qed.
Lemma lem1653321 (_25612 : nat) (_25613 : real) (_25614 : real) : (term137 _25613 _25614 _25612) = (term55 _25612 _25613 _25614).
Proof. exact (TRANS (@lem1653297 _25612 _25613 _25614) (@lem1653320 _25612 _25613 _25614)). Qed.
Lemma lem1653323 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term102 y x n.
Proof. exact (conj (@lem1653175 n y x h1) (@lem1653182 n y x h1)). Qed.
Lemma lem1653324 (n : nat) (y : real) (x : real) (h1 : term65 n y x) : term107 y x n.
Proof. exact (conj (@lem1653168 n y x h1) (@lem1653323 n y x h1)). Qed.
Lemma lem1653326 (_25612 : nat) (_25613 : real) (_25614 : real) (h1 : term52) : term55 _25612 _25613 _25614.
Proof. exact (EQ_MP (@lem1653321 _25612 _25613 _25614) (@lem1653294 _25613 _25614 _25612 h1)). Qed.
Lemma lem1653327 (n : nat) (y : real) (x : real) (h1 : term52) : term55 n y x.
Proof. exact (@lem1653326 n y x h1). Qed.
Lemma lem1653330 (n : nat) (y : real) (x : real) (h1 : term52) (h2 : term65 n y x) : real_le y x.
Proof. exact (@lem1653327 n y x h1 (@lem1653324 n y x h2)). Qed.
Lemma lem1653331 (n : nat) (y : real) (x : real) (h1 : term52) (h2 : term65 n y x) : term152 y x.
Proof. exact (fun h0 : term114 y x => @lem1653330 n y x h1 h2). Qed.
Lemma lem1653333 (p : Prop) : (term127 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1653334 (y : real) (x : real) : (term152 y x) = (real_le y x).
Proof. exact (@lem1653333 (real_le y x)). Qed.
Lemma lem1653335 (n : nat) (y : real) (x : real) (h1 : term52) (h2 : term65 n y x) : real_le y x.
Proof. exact (EQ_MP (@lem1653334 y x) (@lem1653331 n y x h1 h2)). Qed.
Lemma lem1653338 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1653340 (y : real) (x : real) : (term114 y x) = (term153 y x).
Proof. exact (@lem1653338 (real_le y x)). Qed.
Lemma lem1653343 (y : real) (x : real) (h1 : term114 y x) : term153 y x.
Proof. exact (EQ_MP (@lem1653340 y x) (@lem1652863 y x h1)). Qed.
Lemma lem1653346 (n : nat) (y : real) (x : real) (h1 : term52) (h2 : term114 y x) (h3 : term65 n y x) : False.
Proof. exact (@lem1653343 y x h2 (@lem1653335 n y x h1 h3)). Qed.
Lemma lem1653347 (n : nat) (y : real) (x : real) (h1 : term52) (h2 : term114 y x) (h3 : term65 n y x) : term154.
Proof. exact (fun h0 : ~ False => @lem1653346 n y x h1 h2 h3). Qed.
Lemma lem1653349 (p : Prop) : (term127 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1653350 : term154 = False.
Proof. exact (@lem1653349 False). Qed.
Lemma lem1653351 (n : nat) (y : real) (x : real) (h1 : term52) (h2 : term114 y x) (h3 : term65 n y x) : False.
Proof. exact (EQ_MP (@lem1653350) (@lem1653347 n y x h1 h2 h3)). Qed.
Lemma lem1653352 (n : nat) (y : real) (x : real) (h1 : term52) (h2 : term114 y x) (h3 : term65 n y x) : (term114 y x) = False.
Proof. exact (prop_ext (fun h4 : term114 y x => @lem1653351 n y x h1 h2 h3) (fun h4 : False => @lem1652863 y x h2)). Qed.
Lemma lem1653353 (n : nat) (y : real) (x : real) (h1 : term52) (h2 : term114 y x) (h3 : term65 n y x) : False.
Proof. exact (EQ_MP (@lem1653352 n y x h1 h2 h3) (@lem1652863 y x h2)). Qed.
Lemma lem1653354 (n : nat) (y : real) (x : real) (h1 : term52) (h2 : term114 x y) (h3 : term65 n y x) : (term114 x y) = False.
Proof. exact (prop_ext (fun h4 : term114 x y => @lem1653107 n y x h1 h2 h3) (fun h4 : False => @lem1652833 x y h2)). Qed.
Lemma lem1653355 (n : nat) (y : real) (x : real) (h1 : term52) (h2 : term114 x y) (h3 : term65 n y x) : False.
Proof. exact (EQ_MP (@lem1653354 n y x h1 h2 h3) (@lem1652833 x y h2)). Qed.
Lemma lem1653356 (n : nat) (y : real) (x : real) (h1 : term52) (h2 : term114 y x) (h3 : term65 n y x) : (term114 y x) = False.
Proof. exact (prop_ext (fun h4 : term114 y x => @lem1653353 n y x h1 h2 h3) (fun h4 : False => @lem1652785 y x h2)). Qed.
Lemma lem1653357 (n : nat) (y : real) (x : real) (h1 : term52) (h2 : term114 y x) (h3 : term65 n y x) : False.
Proof. exact (EQ_MP (@lem1653356 n y x h1 h2 h3) (@lem1652785 y x h2)). Qed.
Lemma lem1653358 (n : nat) (y : real) (x : real) (h1 : term52) (h2 : term114 x y) (h3 : term65 n y x) : (term114 x y) = False.
Proof. exact (prop_ext (fun h4 : term114 x y => @lem1653355 n y x h1 h2 h3) (fun h4 : False => @lem1652730 x y h2)). Qed.
Lemma lem1653359 (n : nat) (y : real) (x : real) (h1 : term52) (h2 : term114 x y) (h3 : term65 n y x) : False.
Proof. exact (EQ_MP (@lem1653358 n y x h1 h2 h3) (@lem1652730 x y h2)). Qed.
Lemma lem1653360 (n : nat) (y : real) (x : real) (h1 : term52) (h2 : term114 y x) (h3 : term65 n y x) : (term114 y x) = False.
Proof. exact (prop_ext (fun h4 : term114 y x => @lem1653357 n y x h1 h2 h3) (fun h4 : False => @lem1652785 y x h2)). Qed.
Lemma lem1653361 (n : nat) (y : real) (x : real) (h1 : term52) (h2 : term114 y x) (h3 : term65 n y x) : False.
Proof. exact (EQ_MP (@lem1653360 n y x h1 h2 h3) (@lem1652785 y x h2)). Qed.
Lemma lem1653362 (n : nat) (y : real) (x : real) (h1 : term52) (h2 : term114 x y) (h3 : term65 n y x) : (term114 x y) = False.
Proof. exact (prop_ext (fun h4 : term114 x y => @lem1653359 n y x h1 h2 h3) (fun h4 : False => @lem1652730 x y h2)). Qed.
Lemma lem1653363 (n : nat) (y : real) (x : real) (h1 : term52) (h2 : term114 x y) (h3 : term65 n y x) : False.
Proof. exact (EQ_MP (@lem1653362 n y x h1 h2 h3) (@lem1652730 x y h2)). Qed.
Lemma lem1653364 (n : nat) (y : real) (x : real) (h1 : term52) (h2 : term65 n y x) : False.
Proof. exact (or_elim (@lem1652664 n y x h2) (fun h0 : term114 x y => @lem1653363 n y x h1 h0 h2) (fun h0 : term114 y x => @lem1653361 n y x h1 h0 h2)). Qed.
Lemma lem1653365 (n : nat) (y : real) (x : real) (h1 : term52) (h2 : term65 n y x) : (term65 n y x) = False.
Proof. exact (prop_ext (fun h3 : term65 n y x => @lem1653364 n y x h1 h2) (fun h3 : False => @lem1652663 n y x h2)). Qed.
Lemma lem1653366 (n : nat) (y : real) (x : real) (h1 : term52) (h2 : term65 n y x) : False.
Proof. exact (EQ_MP (@lem1653365 n y x h1 h2) (@lem1652663 n y x h2)). Qed.
Lemma lem1653367 (n : nat) (x : real) (h1 : term52) (h2 : term75 n x) : False.
Proof. exact (ex_elim (@lem1652519 n x h2) (fun y : real => fun h0 : term74 n x y => @lem1653366 n y x h1 h0)). Qed.
Lemma lem1653368 (n : nat) (h1 : term52) (h2 : term82 n) : False.
Proof. exact (ex_elim (@lem1652518 n h2) (fun x : real => fun h0 : term81 n x => @lem1653367 n x h1 h0)). Qed.
Lemma lem1653369 (h1 : term52) (h2 : term45) : False.
Proof. exact (ex_elim (@lem1652426 h2) (fun n : nat => fun h0 : term89 n => @lem1653368 n h1 h0)). Qed.
Lemma lem1653370 (h1 : term45) : term50.
Proof. exact (fun h0 : term52 => @lem1653369 h0 h1). Qed.
Lemma lem1653371 : term50 = term51.
Proof. exact (@lem69 term52). Qed.
Lemma lem1653372 (h1 : term45) : term51.
Proof. exact (EQ_MP (@lem1653371) (@lem1653370 h1)). Qed.
Lemma lem1653373 : term54.
Proof. exact (fun h0 : term45 => @lem1653372 h0). Qed.
Lemma lem1653374 : term46.
Proof. exact (EQ_MP (@lem1652304) (@lem1653373)). Qed.
Lemma lem1653376 : term46.
Proof. exact (@lem1652122 (@lem1653374)). Qed.
Lemma lem1653377 (h1 : term45) : term50.
Proof. exact (@lem1653376 (@lem1652107 h1)). Qed.
Lemma lem1653378 (h1 : term45) : False.
Proof. exact (@lem1653377 h1 (@lem1650795)). Qed.
Lemma lem1653379 (h1 : term45) : term45 = False.
Proof. exact (prop_ext (fun h2 : term45 => @lem1653378 h1) (fun h2 : False => @lem1652107 h1)). Qed.
Lemma lem1653380 (h1 : term45) : False.
Proof. exact (EQ_MP (@lem1653379 h1) (@lem1652107 h1)). Qed.
Lemma lem1653381 : term44.
Proof. exact (fun h0 : term45 => @lem1653380 h0). Qed.
Lemma lem1653382 : term42.
Proof. exact (EQ_MP (@lem1652106) (@lem1653381)). Qed.
Lemma lem1653383 : term41.
Proof. exact (EQ_MP (@lem1652102) (@lem1653382)). Qed.
