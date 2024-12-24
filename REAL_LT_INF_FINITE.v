Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_INF_FINITE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import INF_FINITE_spec.
Require Import REAL_LTE_TRANS_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
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
Lemma lem5227046 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5227047 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5227048 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5227047 t1) (@lem5227046 t1)). Qed.
Lemma lem5227049 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5227048 t1 t2). Qed.
Lemma lem5227050 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5227051 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5227050 t1 t2) (@lem5227049 t1 t2)). Qed.
Lemma lem5227052 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5227051 t1 t2 t3). Qed.
Lemma lem5227053 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5227054 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5227053 t1 t2 t3) (@lem5227052 t1 t2 t3)). Qed.
Lemma lem5227055 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5227054 t1 t2 t3)). Qed.
Lemma lem5227057 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5227058 : term8 = term9.
Proof. exact (@lem5227057 term8). Qed.
Lemma lem5227059 : term9 = term8.
Proof. exact (SYM (@lem5227058)). Qed.
Lemma lem5227060 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5227063 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5227064 : term12.
Proof. exact (fun h0 : term11 => @lem5227063 h0). Qed.
Lemma lem5227065 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5227066 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem5227067 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem5227065 h2 (@lem5227066 h1)). Qed.
Lemma lem5227068 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem5227067 h1 h0). Qed.
Lemma lem5227069 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem5227070 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem5227068 h1 (@lem5227069 h2)). Qed.
Lemma lem5227071 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem5227070 h0 h1). Qed.
Lemma lem5227072 : term14.
Proof. exact (fun h0 : term12 => @lem5227071 h0). Qed.
Lemma lem5227075 : term12.
Proof. exact (@lem5227072 (@lem5227064)). Qed.
Lemma lem5227115 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5227116 : term15 = term16.
Proof. exact (@lem5227115 term17). Qed.
Lemma lem5227133 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem5227134 : term19 = term20.
Proof. exact (MK_COMB (@lem5227133) (@lem5227116)). Qed.
Lemma lem5227137 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem5227144 : term11 = term22.
Proof. exact (MK_COMB (@lem5227137) (@lem5227134)). Qed.
Lemma lem5227149 (s : real -> Prop) (x : real) : (term23 s x) = (term23 s x).
Proof. exact (eq_refl (term23 s x)). Qed.
Lemma lem5227150 (s : real -> Prop) : (term24 s) = (term24 s).
Proof. exact (fun_ext (fun x : real => @lem5227149 s x)). Qed.
Lemma lem5227151 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5227152 (s : real -> Prop) : (term25 s) = (term25 s).
Proof. exact (MK_COMB (@lem5227151) (@lem5227150 s)). Qed.
Lemma lem5227155 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5227156 (s : real -> Prop) : (term27 s) = (term27 s).
Proof. exact (MK_COMB (@lem5227155 s) (@lem5227152 s)). Qed.
Lemma lem5227165 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5227166 (s : real -> Prop) : (term29 s) = (term29 s).
Proof. exact (MK_COMB (@lem5227165 s) (@lem5227156 s)). Qed.
Lemma lem5227167 : term30 = term30.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5227166 s)). Qed.
Lemma lem5227168 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5227169 : term17 = term17.
Proof. exact (MK_COMB (@lem5227168) (@lem5227167)). Qed.
Lemma lem5227170 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5227171 : term16 = term16.
Proof. exact (MK_COMB (@lem5227170) (@lem5227169)). Qed.
Lemma lem5227180 (y : real) (x : real) (z : real) : (term31 y x z) = (term31 y x z).
Proof. exact (eq_refl (term31 y x z)). Qed.
Lemma lem5227181 (y : real) (x : real) : (term32 y x) = (term32 y x).
Proof. exact (fun_ext (fun z : real => @lem5227180 y x z)). Qed.
Lemma lem5227182 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5227183 (y : real) (x : real) : (term33 y x) = (term33 y x).
Proof. exact (MK_COMB (@lem5227182) (@lem5227181 y x)). Qed.
Lemma lem5227184 (x : real) : (term34 x) = (term34 x).
Proof. exact (fun_ext (fun y : real => @lem5227183 y x)). Qed.
Lemma lem5227185 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5227186 (x : real) : (term35 x) = (term35 x).
Proof. exact (MK_COMB (@lem5227185) (@lem5227184 x)). Qed.
Lemma lem5227187 : term36 = term36.
Proof. exact (fun_ext (fun x : real => @lem5227186 x)). Qed.
Lemma lem5227188 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5227189 : term37 = term37.
Proof. exact (MK_COMB (@lem5227188) (@lem5227187)). Qed.
Lemma lem5227190 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5227191 : term18 = term18.
Proof. exact (MK_COMB (@lem5227190) (@lem5227189)). Qed.
Lemma lem5227192 : term20 = term20.
Proof. exact (MK_COMB (@lem5227191) (@lem5227171)). Qed.
Lemma lem5227197 (s : real -> Prop) (a : real) (x : real) : (term38 s a x) = (term38 s a x).
Proof. exact (eq_refl (term38 s a x)). Qed.
Lemma lem5227198 (s : real -> Prop) (a : real) : (term39 s a) = (term39 s a).
Proof. exact (fun_ext (fun x : real => @lem5227197 s a x)). Qed.
Lemma lem5227199 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5227200 (s : real -> Prop) (a : real) : (term40 s a) = (term40 s a).
Proof. exact (MK_COMB (@lem5227199) (@lem5227198 s a)). Qed.
Lemma lem5227203 (a : real) (s : real -> Prop) : (term41 a s) = (term41 a s).
Proof. exact (eq_refl (term41 a s)). Qed.
Lemma lem5227204 (s : real -> Prop) (a : real) : ((term42 a s) = (term40 s a)) = ((term42 a s) = (term40 s a)).
Proof. exact (MK_COMB (@lem5227203 a s) (@lem5227200 s a)). Qed.
Lemma lem5227213 (s : real -> Prop) : (term28 s) = (term28 s).
Proof. exact (eq_refl (term28 s)). Qed.
Lemma lem5227214 (s : real -> Prop) (a : real) : (term43 s a) = (term43 s a).
Proof. exact (MK_COMB (@lem5227213 s) (@lem5227204 s a)). Qed.
Lemma lem5227215 (s : real -> Prop) : (term44 s) = (term44 s).
Proof. exact (fun_ext (fun a : real => @lem5227214 s a)). Qed.
Lemma lem5227216 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5227217 (s : real -> Prop) : (term45 s) = (term45 s).
Proof. exact (MK_COMB (@lem5227216) (@lem5227215 s)). Qed.
Lemma lem5227218 : term46 = term46.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5227217 s)). Qed.
Lemma lem5227219 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5227220 : term8 = term8.
Proof. exact (MK_COMB (@lem5227219) (@lem5227218)). Qed.
Lemma lem5227221 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5227222 : term10 = term10.
Proof. exact (MK_COMB (@lem5227221) (@lem5227220)). Qed.
Lemma lem5227223 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5227224 : term21 = term21.
Proof. exact (MK_COMB (@lem5227223) (@lem5227222)). Qed.
Lemma lem5227225 : term22 = term22.
Proof. exact (MK_COMB (@lem5227224) (@lem5227192)). Qed.
Lemma lem5227298 : term11 = term22.
Proof. exact (TRANS (@lem5227144) (@lem5227225)). Qed.
Lemma lem5227299 : term22 = term11.
Proof. exact (SYM (@lem5227298)). Qed.
Lemma lem5227300 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem5227301 (h1 : term37) : term37.
Proof. exact (h1). Qed.
Lemma lem5227302 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem5227318 (s : real -> Prop) (a : real) (x : real) : (term47 s a x) = (term48 s a x).
Proof. exact (@lem17362 (@IN real x s) (real_lt a x)). Qed.
Lemma lem5227323 (s : real -> Prop) (a : real) (x : real) : (term38 s a x) = (term49 s a x).
Proof. exact (@lem17265 (@IN real x s) (real_lt a x)). Qed.
Lemma lem5227324 (P : real -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5227325 (s : real -> Prop) (a : real) : (term52 s a) = (term53 s a).
Proof. exact (@lem5227324 (term39 s a)). Qed.
Lemma lem5227326 (s : real -> Prop) (a : real) (x : real) : (term54 s a x) = (term38 s a x).
Proof. exact (eq_refl (term54 s a x)). Qed.
Lemma lem5227327 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5227328 (s : real -> Prop) (a : real) (x : real) : (term55 s a x) = (term47 s a x).
Proof. exact (MK_COMB (@lem5227327) (@lem5227326 s a x)). Qed.
Lemma lem5227329 (s : real -> Prop) (a : real) (x : real) : (term55 s a x) = (term48 s a x).
Proof. exact (TRANS (@lem5227328 s a x) (@lem5227318 s a x)). Qed.
Lemma lem5227330 (s : real -> Prop) (a : real) : (term56 s a) = (term57 s a).
Proof. exact (fun_ext (fun x : real => @lem5227329 s a x)). Qed.
Lemma lem5227331 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5227332 (s : real -> Prop) (a : real) : (term53 s a) = (term58 s a).
Proof. exact (MK_COMB (@lem5227331) (@lem5227330 s a)). Qed.
Lemma lem5227333 (s : real -> Prop) (a : real) : (term52 s a) = (term58 s a).
Proof. exact (TRANS (@lem5227325 s a) (@lem5227332 s a)). Qed.
Lemma lem5227334 (s : real -> Prop) (a : real) : (term39 s a) = (term59 s a).
Proof. exact (fun_ext (fun x : real => @lem5227323 s a x)). Qed.
Lemma lem5227335 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5227336 (s : real -> Prop) (a : real) : (term40 s a) = (term60 s a).
Proof. exact (MK_COMB (@lem5227335) (@lem5227334 s a)). Qed.
Lemma lem5227338 (a : real) (s : real -> Prop) : (term61 a s) = (term61 a s).
Proof. exact (eq_refl (term61 a s)). Qed.
Lemma lem5227339 (s : real -> Prop) (a : real) : (term62 s a) = (term63 s a).
Proof. exact (MK_COMB (@lem5227338 a s) (@lem5227336 s a)). Qed.
Lemma lem5227341 (a : real) (s : real -> Prop) : (term64 a s) = (term64 a s).
Proof. exact (eq_refl (term64 a s)). Qed.
Lemma lem5227342 (s : real -> Prop) (a : real) : (term65 s a) = (term66 s a).
Proof. exact (MK_COMB (@lem5227341 a s) (@lem5227333 s a)). Qed.
Lemma lem5227343 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5227344 (s : real -> Prop) (a : real) : (term67 s a) = (term68 s a).
Proof. exact (MK_COMB (@lem5227343) (@lem5227342 s a)). Qed.
Lemma lem5227345 (s : real -> Prop) (a : real) : (term69 s a) = (term70 s a).
Proof. exact (MK_COMB (@lem5227344 s a) (@lem5227339 s a)). Qed.
Lemma lem5227346 (s : real -> Prop) (a : real) : (term71 s a) = (term69 s a).
Proof. exact (@lem17646 (term42 a s) (term40 s a)). Qed.
Lemma lem5227347 (s : real -> Prop) (a : real) : (term71 s a) = (term70 s a).
Proof. exact (TRANS (@lem5227346 s a) (@lem5227345 s a)). Qed.
Lemma lem5227349 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5227350 (s : real -> Prop) (a : real) : (term73 s a) = (term74 s a).
Proof. exact (MK_COMB (@lem5227349 s) (@lem5227347 s a)). Qed.
Lemma lem5227351 (s : real -> Prop) (a : real) : (term75 s a) = (term73 s a).
Proof. exact (@lem17362 (term76 s) ((term42 a s) = (term40 s a))). Qed.
Lemma lem5227352 (s : real -> Prop) (a : real) : (term75 s a) = (term74 s a).
Proof. exact (TRANS (@lem5227351 s a) (@lem5227350 s a)). Qed.
Lemma lem5227353 (P : real -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5227354 (s : real -> Prop) : (term77 s) = (term78 s).
Proof. exact (@lem5227353 (term44 s)). Qed.
Lemma lem5227355 (s : real -> Prop) (a : real) : (term79 s a) = (term43 s a).
Proof. exact (eq_refl (term79 s a)). Qed.
Lemma lem5227356 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5227357 (s : real -> Prop) (a : real) : (term80 s a) = (term75 s a).
Proof. exact (MK_COMB (@lem5227356) (@lem5227355 s a)). Qed.
Lemma lem5227358 (s : real -> Prop) (a : real) : (term80 s a) = (term74 s a).
Proof. exact (TRANS (@lem5227357 s a) (@lem5227352 s a)). Qed.
Lemma lem5227359 (s : real -> Prop) : (term81 s) = (term82 s).
Proof. exact (fun_ext (fun a : real => @lem5227358 s a)). Qed.
Lemma lem5227360 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5227361 (s : real -> Prop) : (term78 s) = (term83 s).
Proof. exact (MK_COMB (@lem5227360) (@lem5227359 s)). Qed.
Lemma lem5227362 (s : real -> Prop) : (term77 s) = (term83 s).
Proof. exact (TRANS (@lem5227354 s) (@lem5227361 s)). Qed.
Lemma lem5227363 (P : type1022) : (term84 P) = (term85 P).
Proof. exact (@lem18392 (real -> Prop) P). Qed.
Lemma lem5227364 : term10 = term86.
Proof. exact (@lem5227363 term46). Qed.
Lemma lem5227365 (s : real -> Prop) : (term87 s) = (term45 s).
Proof. exact (eq_refl (term87 s)). Qed.
Lemma lem5227366 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5227367 (s : real -> Prop) : (term88 s) = (term77 s).
Proof. exact (MK_COMB (@lem5227366) (@lem5227365 s)). Qed.
Lemma lem5227368 (s : real -> Prop) : (term88 s) = (term83 s).
Proof. exact (TRANS (@lem5227367 s) (@lem5227362 s)). Qed.
Lemma lem5227369 : term89 = term90.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5227368 s)). Qed.
Lemma lem5227370 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5227371 : term86 = term91.
Proof. exact (MK_COMB (@lem5227370) (@lem5227369)). Qed.
Lemma lem5227372 : term10 = term91.
Proof. exact (TRANS (@lem5227364) (@lem5227371)). Qed.
Lemma lem5227378 {A : Type'} (P : Prop) (Q : A -> Prop) : (term92 A P Q) = (term93 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem5227379 (P : Prop) (Q : real -> Prop) : (term94 P Q) = (term95 P Q).
Proof. exact (@lem5227378 real P Q). Qed.
Lemma lem5227380 (s : real -> Prop) : (term96 s) = (term97 s).
Proof. exact (@lem5227379 (term76 s) (term98 s)). Qed.
Lemma lem5227381 (s : real -> Prop) (a : real) : (term99 s a) = (term70 s a).
Proof. exact (eq_refl (term99 s a)). Qed.
Lemma lem5227382 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5227383 (s : real -> Prop) (a : real) : (term100 s a) = (term74 s a).
Proof. exact (MK_COMB (@lem5227382 s) (@lem5227381 s a)). Qed.
Lemma lem5227384 (s : real -> Prop) : (term101 s) = (term82 s).
Proof. exact (fun_ext (fun a : real => @lem5227383 s a)). Qed.
Lemma lem5227385 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5227386 (s : real -> Prop) : (term96 s) = (term83 s).
Proof. exact (MK_COMB (@lem5227385) (@lem5227384 s)). Qed.
Lemma lem5227387 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5227388 (s : real -> Prop) : (term102 s) = (term103 s).
Proof. exact (MK_COMB (@lem5227387) (@lem5227386 s)). Qed.
Lemma lem5227389 (s : real -> Prop) (a : real) : (term99 s a) = (term70 s a).
Proof. exact (eq_refl (term99 s a)). Qed.
Lemma lem5227390 (s : real -> Prop) : (term104 s) = (term98 s).
Proof. exact (fun_ext (fun a : real => @lem5227389 s a)). Qed.
Lemma lem5227391 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5227392 (s : real -> Prop) : (term105 s) = (term106 s).
Proof. exact (MK_COMB (@lem5227391) (@lem5227390 s)). Qed.
Lemma lem5227393 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5227394 (s : real -> Prop) : (term97 s) = (term107 s).
Proof. exact (MK_COMB (@lem5227393 s) (@lem5227392 s)). Qed.
Lemma lem5227395 (s : real -> Prop) : ((term96 s) = (term97 s)) = ((term83 s) = (term107 s)).
Proof. exact (MK_COMB (@lem5227388 s) (@lem5227394 s)). Qed.
Lemma lem5227396 (s : real -> Prop) : (term83 s) = (term107 s).
Proof. exact (EQ_MP (@lem5227395 s) (@lem5227380 s)). Qed.
Lemma lem5227398 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem5227399 (P : real -> Prop) (Q : real -> Prop) : (term110 P Q) = (term111 P Q).
Proof. exact (@lem5227398 real P Q). Qed.
Lemma lem5227400 (s : real -> Prop) : (term112 s) = (term113 s).
Proof. exact (@lem5227399 (term114 s) (term115 s)). Qed.
Lemma lem5227401 (s : real -> Prop) (a : real) : (term116 s a) = (term66 s a).
Proof. exact (eq_refl (term116 s a)). Qed.
Lemma lem5227402 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5227403 (s : real -> Prop) (a : real) : (term117 s a) = (term68 s a).
Proof. exact (MK_COMB (@lem5227402) (@lem5227401 s a)). Qed.
Lemma lem5227404 (s : real -> Prop) (a : real) : (term118 s a) = (term63 s a).
Proof. exact (eq_refl (term118 s a)). Qed.
Lemma lem5227405 (s : real -> Prop) (a : real) : (term119 s a) = (term70 s a).
Proof. exact (MK_COMB (@lem5227403 s a) (@lem5227404 s a)). Qed.
Lemma lem5227406 (s : real -> Prop) : (term120 s) = (term98 s).
Proof. exact (fun_ext (fun a : real => @lem5227405 s a)). Qed.
Lemma lem5227407 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5227408 (s : real -> Prop) : (term112 s) = (term106 s).
Proof. exact (MK_COMB (@lem5227407) (@lem5227406 s)). Qed.
Lemma lem5227409 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5227410 (s : real -> Prop) : (term121 s) = (term122 s).
Proof. exact (MK_COMB (@lem5227409) (@lem5227408 s)). Qed.
Lemma lem5227411 (s : real -> Prop) (a : real) : (term116 s a) = (term66 s a).
Proof. exact (eq_refl (term116 s a)). Qed.
Lemma lem5227412 (s : real -> Prop) : (term123 s) = (term114 s).
Proof. exact (fun_ext (fun a : real => @lem5227411 s a)). Qed.
Lemma lem5227413 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5227414 (s : real -> Prop) : (term124 s) = (term125 s).
Proof. exact (MK_COMB (@lem5227413) (@lem5227412 s)). Qed.
Lemma lem5227415 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5227416 (s : real -> Prop) : (term126 s) = (term127 s).
Proof. exact (MK_COMB (@lem5227415) (@lem5227414 s)). Qed.
Lemma lem5227417 (s : real -> Prop) (a : real) : (term118 s a) = (term63 s a).
Proof. exact (eq_refl (term118 s a)). Qed.
Lemma lem5227418 (s : real -> Prop) : (term128 s) = (term115 s).
Proof. exact (fun_ext (fun a : real => @lem5227417 s a)). Qed.
Lemma lem5227419 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5227420 (s : real -> Prop) : (term129 s) = (term130 s).
Proof. exact (MK_COMB (@lem5227419) (@lem5227418 s)). Qed.
Lemma lem5227421 (s : real -> Prop) : (term113 s) = (term131 s).
Proof. exact (MK_COMB (@lem5227416 s) (@lem5227420 s)). Qed.
Lemma lem5227422 (s : real -> Prop) : ((term112 s) = (term113 s)) = ((term106 s) = (term131 s)).
Proof. exact (MK_COMB (@lem5227410 s) (@lem5227421 s)). Qed.
Lemma lem5227423 (s : real -> Prop) : (term106 s) = (term131 s).
Proof. exact (EQ_MP (@lem5227422 s) (@lem5227400 s)). Qed.
Lemma lem5227616 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5227617 (s : real -> Prop) : (term107 s) = (term132 s).
Proof. exact (MK_COMB (@lem5227616 s) (@lem5227423 s)). Qed.
Lemma lem5227618 (s : real -> Prop) : (term83 s) = (term132 s).
Proof. exact (TRANS (@lem5227396 s) (@lem5227617 s)). Qed.
Lemma lem5227619 : term90 = term133.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5227618 s)). Qed.
Lemma lem5227620 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5227621 : term91 = term134.
Proof. exact (MK_COMB (@lem5227620) (@lem5227619)). Qed.
Lemma lem5227671 {A : Type'} (P : Prop) (Q : A -> Prop) : (term93 A P Q) = (term92 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5227672 (P : Prop) (Q : real -> Prop) : (term95 P Q) = (term94 P Q).
Proof. exact (@lem5227671 real P Q). Qed.
Lemma lem5227673 (s : real -> Prop) (a : real) : (term135 s a) = (term136 s a).
Proof. exact (@lem5227672 (term42 a s) (term57 s a)). Qed.
Lemma lem5227674 (s : real -> Prop) (a : real) (x : real) : (term137 s a x) = (term48 s a x).
Proof. exact (eq_refl (term137 s a x)). Qed.
Lemma lem5227675 (s : real -> Prop) (a : real) : (term138 s a) = (term57 s a).
Proof. exact (fun_ext (fun x : real => @lem5227674 s a x)). Qed.
Lemma lem5227676 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5227677 (s : real -> Prop) (a : real) : (term139 s a) = (term58 s a).
Proof. exact (MK_COMB (@lem5227676) (@lem5227675 s a)). Qed.
Lemma lem5227678 (a : real) (s : real -> Prop) : (term64 a s) = (term64 a s).
Proof. exact (eq_refl (term64 a s)). Qed.
Lemma lem5227679 (s : real -> Prop) (a : real) : (term135 s a) = (term66 s a).
Proof. exact (MK_COMB (@lem5227678 a s) (@lem5227677 s a)). Qed.
Lemma lem5227680 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5227681 (s : real -> Prop) (a : real) : (term140 s a) = (term141 s a).
Proof. exact (MK_COMB (@lem5227680) (@lem5227679 s a)). Qed.
Lemma lem5227682 (s : real -> Prop) (a : real) (x : real) : (term137 s a x) = (term48 s a x).
Proof. exact (eq_refl (term137 s a x)). Qed.
Lemma lem5227683 (a : real) (s : real -> Prop) : (term64 a s) = (term64 a s).
Proof. exact (eq_refl (term64 a s)). Qed.
Lemma lem5227684 (s : real -> Prop) (a : real) (x : real) : (term142 s a x) = (term143 s a x).
Proof. exact (MK_COMB (@lem5227683 a s) (@lem5227682 s a x)). Qed.
Lemma lem5227685 (s : real -> Prop) (a : real) : (term144 s a) = (term145 s a).
Proof. exact (fun_ext (fun x : real => @lem5227684 s a x)). Qed.
Lemma lem5227686 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5227687 (s : real -> Prop) (a : real) : (term136 s a) = (term146 s a).
Proof. exact (MK_COMB (@lem5227686) (@lem5227685 s a)). Qed.
Lemma lem5227688 (s : real -> Prop) (a : real) : ((term135 s a) = (term136 s a)) = ((term66 s a) = (term146 s a)).
Proof. exact (MK_COMB (@lem5227681 s a) (@lem5227687 s a)). Qed.
Lemma lem5227689 (s : real -> Prop) (a : real) : (term66 s a) = (term146 s a).
Proof. exact (EQ_MP (@lem5227688 s a) (@lem5227673 s a)). Qed.
Lemma lem5227690 (s : real -> Prop) : (term114 s) = (term147 s).
Proof. exact (fun_ext (fun a : real => @lem5227689 s a)). Qed.
Lemma lem5227691 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5227692 (s : real -> Prop) : (term125 s) = (term148 s).
Proof. exact (MK_COMB (@lem5227691) (@lem5227690 s)). Qed.
Lemma lem5227693 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5227694 (s : real -> Prop) : (term127 s) = (term149 s).
Proof. exact (MK_COMB (@lem5227693) (@lem5227692 s)). Qed.
Lemma lem5227695 (s : real -> Prop) : (term130 s) = (term130 s).
Proof. exact (eq_refl (term130 s)). Qed.
Lemma lem5227696 (s : real -> Prop) : (term131 s) = (term150 s).
Proof. exact (MK_COMB (@lem5227694 s) (@lem5227695 s)). Qed.
Lemma lem5227698 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term109 A P Q) = (term108 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem5227699 (P : real -> Prop) (Q : real -> Prop) : (term111 P Q) = (term110 P Q).
Proof. exact (@lem5227698 real P Q). Qed.
Lemma lem5227700 (s : real -> Prop) : (term151 s) = (term152 s).
Proof. exact (@lem5227699 (term147 s) (term115 s)). Qed.
Lemma lem5227701 (s : real -> Prop) (a : real) : (term153 s a) = (term146 s a).
Proof. exact (eq_refl (term153 s a)). Qed.
Lemma lem5227702 (s : real -> Prop) : (term154 s) = (term147 s).
Proof. exact (fun_ext (fun a : real => @lem5227701 s a)). Qed.
Lemma lem5227703 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5227704 (s : real -> Prop) : (term155 s) = (term148 s).
Proof. exact (MK_COMB (@lem5227703) (@lem5227702 s)). Qed.
Lemma lem5227705 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5227706 (s : real -> Prop) : (term156 s) = (term149 s).
Proof. exact (MK_COMB (@lem5227705) (@lem5227704 s)). Qed.
Lemma lem5227707 (s : real -> Prop) (a : real) : (term118 s a) = (term63 s a).
Proof. exact (eq_refl (term118 s a)). Qed.
Lemma lem5227708 (s : real -> Prop) : (term128 s) = (term115 s).
Proof. exact (fun_ext (fun a : real => @lem5227707 s a)). Qed.
Lemma lem5227709 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5227710 (s : real -> Prop) : (term129 s) = (term130 s).
Proof. exact (MK_COMB (@lem5227709) (@lem5227708 s)). Qed.
Lemma lem5227711 (s : real -> Prop) : (term151 s) = (term150 s).
Proof. exact (MK_COMB (@lem5227706 s) (@lem5227710 s)). Qed.
Lemma lem5227712 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5227713 (s : real -> Prop) : (term157 s) = (term158 s).
Proof. exact (MK_COMB (@lem5227712) (@lem5227711 s)). Qed.
Lemma lem5227714 (s : real -> Prop) (a : real) : (term153 s a) = (term146 s a).
Proof. exact (eq_refl (term153 s a)). Qed.
Lemma lem5227715 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5227716 (s : real -> Prop) (a : real) : (term159 s a) = (term160 s a).
Proof. exact (MK_COMB (@lem5227715) (@lem5227714 s a)). Qed.
Lemma lem5227717 (s : real -> Prop) (a : real) : (term118 s a) = (term63 s a).
Proof. exact (eq_refl (term118 s a)). Qed.
Lemma lem5227718 (s : real -> Prop) (a : real) : (term161 s a) = (term162 s a).
Proof. exact (MK_COMB (@lem5227716 s a) (@lem5227717 s a)). Qed.
Lemma lem5227719 (s : real -> Prop) : (term163 s) = (term164 s).
Proof. exact (fun_ext (fun a : real => @lem5227718 s a)). Qed.
Lemma lem5227720 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5227721 (s : real -> Prop) : (term152 s) = (term165 s).
Proof. exact (MK_COMB (@lem5227720) (@lem5227719 s)). Qed.
Lemma lem5227722 (s : real -> Prop) : ((term151 s) = (term152 s)) = ((term150 s) = (term165 s)).
Proof. exact (MK_COMB (@lem5227713 s) (@lem5227721 s)). Qed.
Lemma lem5227723 (s : real -> Prop) : (term150 s) = (term165 s).
Proof. exact (EQ_MP (@lem5227722 s) (@lem5227700 s)). Qed.
Lemma lem5227725 {A : Type'} (P : A -> Prop) (Q : Prop) : (term166 A P Q) = (term167 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5227726 (P : real -> Prop) (Q : Prop) : (term168 P Q) = (term169 P Q).
Proof. exact (@lem5227725 real P Q). Qed.
Lemma lem5227727 (s : real -> Prop) (a : real) : (term170 s a) = (term171 s a).
Proof. exact (@lem5227726 (term145 s a) (term63 s a)). Qed.
Lemma lem5227728 (s : real -> Prop) (a : real) (x : real) : (term172 s a x) = (term143 s a x).
Proof. exact (eq_refl (term172 s a x)). Qed.
Lemma lem5227729 (s : real -> Prop) (a : real) : (term173 s a) = (term145 s a).
Proof. exact (fun_ext (fun x : real => @lem5227728 s a x)). Qed.
Lemma lem5227730 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5227731 (s : real -> Prop) (a : real) : (term174 s a) = (term146 s a).
Proof. exact (MK_COMB (@lem5227730) (@lem5227729 s a)). Qed.
Lemma lem5227732 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5227733 (s : real -> Prop) (a : real) : (term175 s a) = (term160 s a).
Proof. exact (MK_COMB (@lem5227732) (@lem5227731 s a)). Qed.
Lemma lem5227734 (s : real -> Prop) (a : real) : (term63 s a) = (term63 s a).
Proof. exact (eq_refl (term63 s a)). Qed.
Lemma lem5227735 (s : real -> Prop) (a : real) : (term170 s a) = (term162 s a).
Proof. exact (MK_COMB (@lem5227733 s a) (@lem5227734 s a)). Qed.
Lemma lem5227736 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5227737 (s : real -> Prop) (a : real) : (term176 s a) = (term177 s a).
Proof. exact (MK_COMB (@lem5227736) (@lem5227735 s a)). Qed.
Lemma lem5227738 (s : real -> Prop) (a : real) (x : real) : (term172 s a x) = (term143 s a x).
Proof. exact (eq_refl (term172 s a x)). Qed.
Lemma lem5227739 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5227740 (s : real -> Prop) (a : real) (x : real) : (term178 s a x) = (term179 s a x).
Proof. exact (MK_COMB (@lem5227739) (@lem5227738 s a x)). Qed.
Lemma lem5227741 (s : real -> Prop) (a : real) : (term63 s a) = (term63 s a).
Proof. exact (eq_refl (term63 s a)). Qed.
Lemma lem5227742 (x : real) (s : real -> Prop) (a : real) : (term180 x s a) = (term181 x s a).
Proof. exact (MK_COMB (@lem5227740 s a x) (@lem5227741 s a)). Qed.
Lemma lem5227743 (s : real -> Prop) (a : real) : (term182 s a) = (term183 s a).
Proof. exact (fun_ext (fun x : real => @lem5227742 x s a)). Qed.
Lemma lem5227744 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5227745 (s : real -> Prop) (a : real) : (term171 s a) = (term184 s a).
Proof. exact (MK_COMB (@lem5227744) (@lem5227743 s a)). Qed.
Lemma lem5227746 (s : real -> Prop) (a : real) : ((term170 s a) = (term171 s a)) = ((term162 s a) = (term184 s a)).
Proof. exact (MK_COMB (@lem5227737 s a) (@lem5227745 s a)). Qed.
Lemma lem5227747 (s : real -> Prop) (a : real) : (term162 s a) = (term184 s a).
Proof. exact (EQ_MP (@lem5227746 s a) (@lem5227727 s a)). Qed.
Lemma lem5227748 (s : real -> Prop) : (term164 s) = (term185 s).
Proof. exact (fun_ext (fun a : real => @lem5227747 s a)). Qed.
Lemma lem5227749 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5227750 (s : real -> Prop) : (term165 s) = (term186 s).
Proof. exact (MK_COMB (@lem5227749) (@lem5227748 s)). Qed.
Lemma lem5227751 (s : real -> Prop) : (term150 s) = (term186 s).
Proof. exact (TRANS (@lem5227723 s) (@lem5227750 s)). Qed.
Lemma lem5227752 (s : real -> Prop) : (term131 s) = (term186 s).
Proof. exact (TRANS (@lem5227696 s) (@lem5227751 s)). Qed.
Lemma lem5227753 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5227754 (s : real -> Prop) : (term132 s) = (term187 s).
Proof. exact (MK_COMB (@lem5227753 s) (@lem5227752 s)). Qed.
Lemma lem5227756 {A : Type'} (P : Prop) (Q : A -> Prop) : (term93 A P Q) = (term92 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5227757 (P : Prop) (Q : real -> Prop) : (term95 P Q) = (term94 P Q).
Proof. exact (@lem5227756 real P Q). Qed.
Lemma lem5227758 (s : real -> Prop) : (term188 s) = (term189 s).
Proof. exact (@lem5227757 (term76 s) (term185 s)). Qed.
Lemma lem5227759 (s : real -> Prop) (a : real) : (term190 s a) = (term184 s a).
Proof. exact (eq_refl (term190 s a)). Qed.
Lemma lem5227760 (s : real -> Prop) : (term191 s) = (term185 s).
Proof. exact (fun_ext (fun a : real => @lem5227759 s a)). Qed.
Lemma lem5227761 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5227762 (s : real -> Prop) : (term192 s) = (term186 s).
Proof. exact (MK_COMB (@lem5227761) (@lem5227760 s)). Qed.
Lemma lem5227763 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5227764 (s : real -> Prop) : (term188 s) = (term187 s).
Proof. exact (MK_COMB (@lem5227763 s) (@lem5227762 s)). Qed.
Lemma lem5227765 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5227766 (s : real -> Prop) : (term193 s) = (term194 s).
Proof. exact (MK_COMB (@lem5227765) (@lem5227764 s)). Qed.
Lemma lem5227767 (s : real -> Prop) (a : real) : (term190 s a) = (term184 s a).
Proof. exact (eq_refl (term190 s a)). Qed.
Lemma lem5227768 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5227769 (s : real -> Prop) (a : real) : (term195 s a) = (term196 s a).
Proof. exact (MK_COMB (@lem5227768 s) (@lem5227767 s a)). Qed.
Lemma lem5227770 (s : real -> Prop) : (term197 s) = (term198 s).
Proof. exact (fun_ext (fun a : real => @lem5227769 s a)). Qed.
Lemma lem5227771 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5227772 (s : real -> Prop) : (term189 s) = (term199 s).
Proof. exact (MK_COMB (@lem5227771) (@lem5227770 s)). Qed.
Lemma lem5227773 (s : real -> Prop) : ((term188 s) = (term189 s)) = ((term187 s) = (term199 s)).
Proof. exact (MK_COMB (@lem5227766 s) (@lem5227772 s)). Qed.
Lemma lem5227774 (s : real -> Prop) : (term187 s) = (term199 s).
Proof. exact (EQ_MP (@lem5227773 s) (@lem5227758 s)). Qed.
Lemma lem5227776 {A : Type'} (P : Prop) (Q : A -> Prop) : (term93 A P Q) = (term92 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5227777 (P : Prop) (Q : real -> Prop) : (term95 P Q) = (term94 P Q).
Proof. exact (@lem5227776 real P Q). Qed.
Lemma lem5227778 (s : real -> Prop) (a : real) : (term200 s a) = (term201 s a).
Proof. exact (@lem5227777 (term76 s) (term183 s a)). Qed.
Lemma lem5227779 (x : real) (s : real -> Prop) (a : real) : (term202 s a x) = (term181 x s a).
Proof. exact (eq_refl (term202 s a x)). Qed.
Lemma lem5227780 (s : real -> Prop) (a : real) : (term203 s a) = (term183 s a).
Proof. exact (fun_ext (fun x : real => @lem5227779 x s a)). Qed.
Lemma lem5227781 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5227782 (s : real -> Prop) (a : real) : (term204 s a) = (term184 s a).
Proof. exact (MK_COMB (@lem5227781) (@lem5227780 s a)). Qed.
Lemma lem5227783 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5227784 (s : real -> Prop) (a : real) : (term200 s a) = (term196 s a).
Proof. exact (MK_COMB (@lem5227783 s) (@lem5227782 s a)). Qed.
Lemma lem5227785 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5227786 (s : real -> Prop) (a : real) : (term205 s a) = (term206 s a).
Proof. exact (MK_COMB (@lem5227785) (@lem5227784 s a)). Qed.
Lemma lem5227787 (x : real) (s : real -> Prop) (a : real) : (term202 s a x) = (term181 x s a).
Proof. exact (eq_refl (term202 s a x)). Qed.
Lemma lem5227788 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5227789 (x : real) (s : real -> Prop) (a : real) : (term207 s a x) = (term208 x s a).
Proof. exact (MK_COMB (@lem5227788 s) (@lem5227787 x s a)). Qed.
Lemma lem5227790 (s : real -> Prop) (a : real) : (term209 s a) = (term210 s a).
Proof. exact (fun_ext (fun x : real => @lem5227789 x s a)). Qed.
Lemma lem5227791 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5227792 (s : real -> Prop) (a : real) : (term201 s a) = (term211 s a).
Proof. exact (MK_COMB (@lem5227791) (@lem5227790 s a)). Qed.
Lemma lem5227793 (s : real -> Prop) (a : real) : ((term200 s a) = (term201 s a)) = ((term196 s a) = (term211 s a)).
Proof. exact (MK_COMB (@lem5227786 s a) (@lem5227792 s a)). Qed.
Lemma lem5227794 (s : real -> Prop) (a : real) : (term196 s a) = (term211 s a).
Proof. exact (EQ_MP (@lem5227793 s a) (@lem5227778 s a)). Qed.
Lemma lem5227795 (s : real -> Prop) : (term198 s) = (term212 s).
Proof. exact (fun_ext (fun a : real => @lem5227794 s a)). Qed.
Lemma lem5227796 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5227797 (s : real -> Prop) : (term199 s) = (term213 s).
Proof. exact (MK_COMB (@lem5227796) (@lem5227795 s)). Qed.
Lemma lem5227798 (s : real -> Prop) : (term187 s) = (term213 s).
Proof. exact (TRANS (@lem5227774 s) (@lem5227797 s)). Qed.
Lemma lem5227799 (s : real -> Prop) : (term132 s) = (term213 s).
Proof. exact (TRANS (@lem5227754 s) (@lem5227798 s)). Qed.
Lemma lem5227800 : term133 = term214.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5227799 s)). Qed.
Lemma lem5227801 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5227802 : term134 = term215.
Proof. exact (MK_COMB (@lem5227801) (@lem5227800)). Qed.
Lemma lem5227803 : term91 = term215.
Proof. exact (TRANS (@lem5227621) (@lem5227802)). Qed.
Lemma lem5227804 : term10 = term215.
Proof. exact (TRANS (@lem5227372) (@lem5227803)). Qed.
Lemma lem5227805 (h1 : term10) : term215.
Proof. exact (EQ_MP (@lem5227804) (@lem5227300 h1)). Qed.
Lemma lem5227812 (x : real) (y : real) (z : real) : (term216 x y z) = (term217 x y z).
Proof. exact (@lem17045 (real_lt x y) (real_le y z)). Qed.
Lemma lem5227813 (x : real) (z : real) : (real_lt x z) = (real_lt x z).
Proof. exact (eq_refl (real_lt x z)). Qed.
Lemma lem5227814 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5227815 (x : real) (y : real) (z : real) : (term218 x y z) = (term219 x y z).
Proof. exact (MK_COMB (@lem5227814) (@lem5227812 x y z)). Qed.
Lemma lem5227816 (y : real) (x : real) (z : real) : (term220 y x z) = (term221 y x z).
Proof. exact (MK_COMB (@lem5227815 x y z) (@lem5227813 x z)). Qed.
Lemma lem5227817 (y : real) (x : real) (z : real) : (term31 y x z) = (term220 y x z).
Proof. exact (@lem17265 (term222 x y z) (real_lt x z)). Qed.
Lemma lem5227818 (y : real) (x : real) (z : real) : (term31 y x z) = (term221 y x z).
Proof. exact (TRANS (@lem5227817 y x z) (@lem5227816 y x z)). Qed.
Lemma lem5227819 (y : real) (x : real) : (term32 y x) = (term223 y x).
Proof. exact (fun_ext (fun z : real => @lem5227818 y x z)). Qed.
Lemma lem5227820 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5227821 (y : real) (x : real) : (term33 y x) = (term224 y x).
Proof. exact (MK_COMB (@lem5227820) (@lem5227819 y x)). Qed.
Lemma lem5227822 (x : real) : (term34 x) = (term225 x).
Proof. exact (fun_ext (fun y : real => @lem5227821 y x)). Qed.
Lemma lem5227823 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5227824 (x : real) : (term35 x) = (term226 x).
Proof. exact (MK_COMB (@lem5227823) (@lem5227822 x)). Qed.
Lemma lem5227825 : term36 = term227.
Proof. exact (fun_ext (fun x : real => @lem5227824 x)). Qed.
Lemma lem5227826 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5227887 : term37 = term228.
Proof. exact (MK_COMB (@lem5227826) (@lem5227825)). Qed.
Lemma lem5227888 (h1 : term37) : term228.
Proof. exact (EQ_MP (@lem5227887) (@lem5227301 h1)). Qed.
Lemma lem5227892 (s : real -> Prop) : (term229 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5227894 (s : real -> Prop) : (term230 s) = (term230 s).
Proof. exact (eq_refl (term230 s)). Qed.
Lemma lem5227895 (s : real -> Prop) : (term231 s) = (term232 s).
Proof. exact (MK_COMB (@lem5227894 s) (@lem5227892 s)). Qed.
Lemma lem5227896 (s : real -> Prop) : (term233 s) = (term231 s).
Proof. exact (@lem17045 (@FINITE real s) (term234 s)). Qed.
Lemma lem5227897 (s : real -> Prop) : (term233 s) = (term232 s).
Proof. exact (TRANS (@lem5227896 s) (@lem5227895 s)). Qed.
Lemma lem5227905 (s : real -> Prop) (x : real) : (term23 s x) = (term235 s x).
Proof. exact (@lem17265 (@IN real x s) (term236 s x)). Qed.
Lemma lem5227906 (s : real -> Prop) : (term24 s) = (term237 s).
Proof. exact (fun_ext (fun x : real => @lem5227905 s x)). Qed.
Lemma lem5227907 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5227908 (s : real -> Prop) : (term25 s) = (term238 s).
Proof. exact (MK_COMB (@lem5227907) (@lem5227906 s)). Qed.
Lemma lem5227910 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5227911 (s : real -> Prop) : (term27 s) = (term239 s).
Proof. exact (MK_COMB (@lem5227910 s) (@lem5227908 s)). Qed.
Lemma lem5227912 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5227913 (s : real -> Prop) : (term240 s) = (term241 s).
Proof. exact (MK_COMB (@lem5227912) (@lem5227897 s)). Qed.
Lemma lem5227914 (s : real -> Prop) : (term242 s) = (term243 s).
Proof. exact (MK_COMB (@lem5227913 s) (@lem5227911 s)). Qed.
Lemma lem5227915 (s : real -> Prop) : (term29 s) = (term242 s).
Proof. exact (@lem17265 (term76 s) (term27 s)). Qed.
Lemma lem5227916 (s : real -> Prop) : (term29 s) = (term243 s).
Proof. exact (TRANS (@lem5227915 s) (@lem5227914 s)). Qed.
Lemma lem5227917 : term30 = term244.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5227916 s)). Qed.
Lemma lem5227918 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5228019 : term17 = term245.
Proof. exact (MK_COMB (@lem5227918) (@lem5227917)). Qed.
Lemma lem5228020 (h1 : term17) : term245.
Proof. exact (EQ_MP (@lem5228019) (@lem5227302 h1)). Qed.
Lemma lem5228021 (s : real -> Prop) (h1 : term213 s) : term213 s.
Proof. exact (h1). Qed.
Lemma lem5228022 (s : real -> Prop) (a : real) (h1 : term211 s a) : term211 s a.
Proof. exact (h1). Qed.
Lemma lem5228023 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term208 x s a.
Proof. exact (h1). Qed.
Lemma lem5228048 (y : real) (x : real) (z : real) : (term221 y x z) = (term221 y x z).
Proof. exact (eq_refl (term221 y x z)). Qed.
Lemma lem5228049 (y : real) (x : real) : (term223 y x) = (term223 y x).
Proof. exact (fun_ext (fun z : real => @lem5228048 y x z)). Qed.
Lemma lem5228050 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5228051 (y : real) (x : real) : (term224 y x) = (term224 y x).
Proof. exact (MK_COMB (@lem5228050) (@lem5228049 y x)). Qed.
Lemma lem5228052 (x : real) : (term225 x) = (term225 x).
Proof. exact (fun_ext (fun y : real => @lem5228051 y x)). Qed.
Lemma lem5228053 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5228054 (x : real) : (term226 x) = (term226 x).
Proof. exact (MK_COMB (@lem5228053) (@lem5228052 x)). Qed.
Lemma lem5228055 : term227 = term227.
Proof. exact (fun_ext (fun x : real => @lem5228054 x)). Qed.
Lemma lem5228056 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5228057 : term228 = term228.
Proof. exact (MK_COMB (@lem5228056) (@lem5228055)). Qed.
Lemma lem5228058 (h1 : term37) : term228.
Proof. exact (EQ_MP (@lem5228057) (@lem5227888 h1)). Qed.
Lemma lem5228075 (s : real -> Prop) (x : real) : (term235 s x) = (term235 s x).
Proof. exact (eq_refl (term235 s x)). Qed.
Lemma lem5228076 (s : real -> Prop) : (term237 s) = (term237 s).
Proof. exact (fun_ext (fun x : real => @lem5228075 s x)). Qed.
Lemma lem5228077 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5228078 (s : real -> Prop) : (term238 s) = (term238 s).
Proof. exact (MK_COMB (@lem5228077) (@lem5228076 s)). Qed.
Lemma lem5228087 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5228088 (s : real -> Prop) : (term239 s) = (term239 s).
Proof. exact (MK_COMB (@lem5228087 s) (@lem5228078 s)). Qed.
Lemma lem5228103 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5228104 (s : real -> Prop) : (term243 s) = (term243 s).
Proof. exact (MK_COMB (@lem5228103 s) (@lem5228088 s)). Qed.
Lemma lem5228105 : term244 = term244.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5228104 s)). Qed.
Lemma lem5228106 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5228107 : term245 = term245.
Proof. exact (MK_COMB (@lem5228106) (@lem5228105)). Qed.
Lemma lem5228108 (h1 : term17) : term245.
Proof. exact (EQ_MP (@lem5228107) (@lem5228020 h1)). Qed.
Lemma lem5228123 (s : real -> Prop) (a : real) (x : real) : (term49 s a x) = (term49 s a x).
Proof. exact (eq_refl (term49 s a x)). Qed.
Lemma lem5228124 (s : real -> Prop) (a : real) : (term59 s a) = (term59 s a).
Proof. exact (fun_ext (fun x : real => @lem5228123 s a x)). Qed.
Lemma lem5228125 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5228126 (s : real -> Prop) (a : real) : (term60 s a) = (term60 s a).
Proof. exact (MK_COMB (@lem5228125) (@lem5228124 s a)). Qed.
Lemma lem5228137 (a : real) (s : real -> Prop) : (term61 a s) = (term61 a s).
Proof. exact (eq_refl (term61 a s)). Qed.
Lemma lem5228138 (s : real -> Prop) (a : real) : (term63 s a) = (term63 s a).
Proof. exact (MK_COMB (@lem5228137 a s) (@lem5228126 s a)). Qed.
Lemma lem5228165 (s : real -> Prop) (a : real) (x : real) : (term179 s a x) = (term179 s a x).
Proof. exact (eq_refl (term179 s a x)). Qed.
Lemma lem5228166 (x : real) (s : real -> Prop) (a : real) : (term181 x s a) = (term181 x s a).
Proof. exact (MK_COMB (@lem5228165 s a x) (@lem5228138 s a)). Qed.
Lemma lem5228181 (s : real -> Prop) : (term72 s) = (term72 s).
Proof. exact (eq_refl (term72 s)). Qed.
Lemma lem5228182 (x : real) (s : real -> Prop) (a : real) : (term208 x s a) = (term208 x s a).
Proof. exact (MK_COMB (@lem5228181 s) (@lem5228166 x s a)). Qed.
Lemma lem5228183 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term208 x s a.
Proof. exact (EQ_MP (@lem5228182 x s a) (@lem5228023 x s a h1)). Qed.
Lemma lem5228184 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term181 x s a.
Proof. exact (proj2 (@lem5228183 x s a h1)). Qed.
Lemma lem5228185 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term76 s.
Proof. exact (proj1 (@lem5228183 x s a h1)). Qed.
Lemma lem5228188 (s : real -> Prop) (a : real) (x : real) (h1 : term143 s a x) : term143 s a x.
Proof. exact (h1). Qed.
Lemma lem5228189 (s : real -> Prop) (a : real) (h1 : term63 s a) : term63 s a.
Proof. exact (h1). Qed.
Lemma lem5228190 (s : real -> Prop) (a : real) (x : real) (h1 : term143 s a x) : term48 s a x.
Proof. exact (proj2 (@lem5228188 s a x h1)). Qed.
Lemma lem5228194 (s : real -> Prop) (a : real) (h1 : term63 s a) : term60 s a.
Proof. exact (proj2 (@lem5228189 s a h1)). Qed.
Lemma lem5228209 (y : real) (x : real) (z : real) : (term221 y x z) = (term221 y x z).
Proof. exact (eq_refl (term221 y x z)). Qed.
Lemma lem5228210 (y : real) (x : real) : (term223 y x) = (term223 y x).
Proof. exact (fun_ext (fun z : real => @lem5228209 y x z)). Qed.
Lemma lem5228211 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5228212 (y : real) (x : real) : (term224 y x) = (term224 y x).
Proof. exact (MK_COMB (@lem5228211) (@lem5228210 y x)). Qed.
Lemma lem5228213 (x : real) : (term225 x) = (term225 x).
Proof. exact (fun_ext (fun y : real => @lem5228212 y x)). Qed.
Lemma lem5228214 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5228215 (x : real) : (term226 x) = (term226 x).
Proof. exact (MK_COMB (@lem5228214) (@lem5228213 x)). Qed.
Lemma lem5228216 : term227 = term227.
Proof. exact (fun_ext (fun x : real => @lem5228215 x)). Qed.
Lemma lem5228217 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5228219 : term228 = term228.
Proof. exact (MK_COMB (@lem5228217) (@lem5228216)). Qed.
Lemma lem5228220 (h1 : term37) : term228.
Proof. exact (EQ_MP (@lem5228219) (@lem5228058 h1)). Qed.
Lemma lem5228222 {A : Type'} (P : Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5228223 (P : Prop) (Q : real -> Prop) : (term248 P Q) = (term249 P Q).
Proof. exact (@lem5228222 real P Q). Qed.
Lemma lem5228224 (s : real -> Prop) : (term250 s) = (term251 s).
Proof. exact (@lem5228223 (term252 s) (term237 s)). Qed.
Lemma lem5228225 (s : real -> Prop) (x : real) : (term253 s x) = (term235 s x).
Proof. exact (eq_refl (term253 s x)). Qed.
Lemma lem5228226 (s : real -> Prop) : (term254 s) = (term237 s).
Proof. exact (fun_ext (fun x : real => @lem5228225 s x)). Qed.
Lemma lem5228227 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5228228 (s : real -> Prop) : (term255 s) = (term238 s).
Proof. exact (MK_COMB (@lem5228227) (@lem5228226 s)). Qed.
Lemma lem5228229 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5228230 (s : real -> Prop) : (term250 s) = (term239 s).
Proof. exact (MK_COMB (@lem5228229 s) (@lem5228228 s)). Qed.
Lemma lem5228231 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5228232 (s : real -> Prop) : (term256 s) = (term257 s).
Proof. exact (MK_COMB (@lem5228231) (@lem5228230 s)). Qed.
Lemma lem5228233 (s : real -> Prop) (x : real) : (term253 s x) = (term235 s x).
Proof. exact (eq_refl (term253 s x)). Qed.
Lemma lem5228234 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5228235 (s : real -> Prop) (x : real) : (term258 s x) = (term259 s x).
Proof. exact (MK_COMB (@lem5228234 s) (@lem5228233 s x)). Qed.
Lemma lem5228236 (s : real -> Prop) : (term260 s) = (term261 s).
Proof. exact (fun_ext (fun x : real => @lem5228235 s x)). Qed.
Lemma lem5228237 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5228238 (s : real -> Prop) : (term251 s) = (term262 s).
Proof. exact (MK_COMB (@lem5228237) (@lem5228236 s)). Qed.
Lemma lem5228239 (s : real -> Prop) : ((term250 s) = (term251 s)) = ((term239 s) = (term262 s)).
Proof. exact (MK_COMB (@lem5228232 s) (@lem5228238 s)). Qed.
Lemma lem5228240 (s : real -> Prop) : (term239 s) = (term262 s).
Proof. exact (EQ_MP (@lem5228239 s) (@lem5228224 s)). Qed.
Lemma lem5228241 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5228242 (s : real -> Prop) : (term243 s) = (term263 s).
Proof. exact (MK_COMB (@lem5228241 s) (@lem5228240 s)). Qed.
Lemma lem5228244 {A : Type'} (P : Prop) (Q : A -> Prop) : (term264 A P Q) = (term265 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5228245 (P : Prop) (Q : real -> Prop) : (term266 P Q) = (term267 P Q).
Proof. exact (@lem5228244 real P Q). Qed.
Lemma lem5228246 (s : real -> Prop) : (term268 s) = (term269 s).
Proof. exact (@lem5228245 (term232 s) (term261 s)). Qed.
Lemma lem5228247 (s : real -> Prop) (x : real) : (term270 s x) = (term259 s x).
Proof. exact (eq_refl (term270 s x)). Qed.
Lemma lem5228248 (s : real -> Prop) : (term271 s) = (term261 s).
Proof. exact (fun_ext (fun x : real => @lem5228247 s x)). Qed.
Lemma lem5228249 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5228250 (s : real -> Prop) : (term272 s) = (term262 s).
Proof. exact (MK_COMB (@lem5228249) (@lem5228248 s)). Qed.
Lemma lem5228251 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5228252 (s : real -> Prop) : (term268 s) = (term263 s).
Proof. exact (MK_COMB (@lem5228251 s) (@lem5228250 s)). Qed.
Lemma lem5228253 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5228254 (s : real -> Prop) : (term273 s) = (term274 s).
Proof. exact (MK_COMB (@lem5228253) (@lem5228252 s)). Qed.
Lemma lem5228255 (s : real -> Prop) (x : real) : (term270 s x) = (term259 s x).
Proof. exact (eq_refl (term270 s x)). Qed.
Lemma lem5228256 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5228257 (s : real -> Prop) (x : real) : (term275 s x) = (term276 s x).
Proof. exact (MK_COMB (@lem5228256 s) (@lem5228255 s x)). Qed.
Lemma lem5228258 (s : real -> Prop) : (term277 s) = (term278 s).
Proof. exact (fun_ext (fun x : real => @lem5228257 s x)). Qed.
Lemma lem5228259 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5228260 (s : real -> Prop) : (term269 s) = (term279 s).
Proof. exact (MK_COMB (@lem5228259) (@lem5228258 s)). Qed.
Lemma lem5228261 (s : real -> Prop) : ((term268 s) = (term269 s)) = ((term263 s) = (term279 s)).
Proof. exact (MK_COMB (@lem5228254 s) (@lem5228260 s)). Qed.
Lemma lem5228262 (s : real -> Prop) : (term263 s) = (term279 s).
Proof. exact (EQ_MP (@lem5228261 s) (@lem5228246 s)). Qed.
Lemma lem5228263 (s : real -> Prop) : (term243 s) = (term279 s).
Proof. exact (TRANS (@lem5228242 s) (@lem5228262 s)). Qed.
Lemma lem5228264 : term244 = term280.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5228263 s)). Qed.
Lemma lem5228265 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5228266 : term245 = term281.
Proof. exact (MK_COMB (@lem5228265) (@lem5228264)). Qed.
Lemma lem5228295 (s : real -> Prop) (x : real) : (term276 s x) = (term282 s x).
Proof. exact (@lem19490 (term252 s) (term232 s) (term235 s x)). Qed.
Lemma lem5228296 (s : real -> Prop) : (term278 s) = (term283 s).
Proof. exact (fun_ext (fun x : real => @lem5228295 s x)). Qed.
Lemma lem5228297 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5228298 (s : real -> Prop) : (term279 s) = (term284 s).
Proof. exact (MK_COMB (@lem5228297) (@lem5228296 s)). Qed.
Lemma lem5228299 : term280 = term285.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5228298 s)). Qed.
Lemma lem5228300 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5228301 : term281 = term286.
Proof. exact (MK_COMB (@lem5228300) (@lem5228299)). Qed.
Lemma lem5228302 : term245 = term286.
Proof. exact (TRANS (@lem5228266) (@lem5228301)). Qed.
Lemma lem5228303 (h1 : term17) : term286.
Proof. exact (EQ_MP (@lem5228302) (@lem5228108 h1)). Qed.
Lemma lem5228350 {A : Type'} (P : Prop) (Q : A -> Prop) : (term246 A P Q) = (term247 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem5228351 (P : Prop) (Q : real -> Prop) : (term248 P Q) = (term249 P Q).
Proof. exact (@lem5228350 real P Q). Qed.
Lemma lem5228352 (s : real -> Prop) : (term250 s) = (term251 s).
Proof. exact (@lem5228351 (term252 s) (term237 s)). Qed.
Lemma lem5228353 (s : real -> Prop) (x : real) : (term253 s x) = (term235 s x).
Proof. exact (eq_refl (term253 s x)). Qed.
Lemma lem5228354 (s : real -> Prop) : (term254 s) = (term237 s).
Proof. exact (fun_ext (fun x : real => @lem5228353 s x)). Qed.
Lemma lem5228355 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5228356 (s : real -> Prop) : (term255 s) = (term238 s).
Proof. exact (MK_COMB (@lem5228355) (@lem5228354 s)). Qed.
Lemma lem5228357 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5228358 (s : real -> Prop) : (term250 s) = (term239 s).
Proof. exact (MK_COMB (@lem5228357 s) (@lem5228356 s)). Qed.
Lemma lem5228359 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5228360 (s : real -> Prop) : (term256 s) = (term257 s).
Proof. exact (MK_COMB (@lem5228359) (@lem5228358 s)). Qed.
Lemma lem5228361 (s : real -> Prop) (x : real) : (term253 s x) = (term235 s x).
Proof. exact (eq_refl (term253 s x)). Qed.
Lemma lem5228362 (s : real -> Prop) : (term26 s) = (term26 s).
Proof. exact (eq_refl (term26 s)). Qed.
Lemma lem5228363 (s : real -> Prop) (x : real) : (term258 s x) = (term259 s x).
Proof. exact (MK_COMB (@lem5228362 s) (@lem5228361 s x)). Qed.
Lemma lem5228364 (s : real -> Prop) : (term260 s) = (term261 s).
Proof. exact (fun_ext (fun x : real => @lem5228363 s x)). Qed.
Lemma lem5228365 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5228366 (s : real -> Prop) : (term251 s) = (term262 s).
Proof. exact (MK_COMB (@lem5228365) (@lem5228364 s)). Qed.
Lemma lem5228367 (s : real -> Prop) : ((term250 s) = (term251 s)) = ((term239 s) = (term262 s)).
Proof. exact (MK_COMB (@lem5228360 s) (@lem5228366 s)). Qed.
Lemma lem5228368 (s : real -> Prop) : (term239 s) = (term262 s).
Proof. exact (EQ_MP (@lem5228367 s) (@lem5228352 s)). Qed.
Lemma lem5228369 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5228370 (s : real -> Prop) : (term243 s) = (term263 s).
Proof. exact (MK_COMB (@lem5228369 s) (@lem5228368 s)). Qed.
Lemma lem5228372 {A : Type'} (P : Prop) (Q : A -> Prop) : (term264 A P Q) = (term265 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5228373 (P : Prop) (Q : real -> Prop) : (term266 P Q) = (term267 P Q).
Proof. exact (@lem5228372 real P Q). Qed.
Lemma lem5228374 (s : real -> Prop) : (term268 s) = (term269 s).
Proof. exact (@lem5228373 (term232 s) (term261 s)). Qed.
Lemma lem5228375 (s : real -> Prop) (x : real) : (term270 s x) = (term259 s x).
Proof. exact (eq_refl (term270 s x)). Qed.
Lemma lem5228376 (s : real -> Prop) : (term271 s) = (term261 s).
Proof. exact (fun_ext (fun x : real => @lem5228375 s x)). Qed.
Lemma lem5228377 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5228378 (s : real -> Prop) : (term272 s) = (term262 s).
Proof. exact (MK_COMB (@lem5228377) (@lem5228376 s)). Qed.
Lemma lem5228379 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5228380 (s : real -> Prop) : (term268 s) = (term263 s).
Proof. exact (MK_COMB (@lem5228379 s) (@lem5228378 s)). Qed.
Lemma lem5228381 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5228382 (s : real -> Prop) : (term273 s) = (term274 s).
Proof. exact (MK_COMB (@lem5228381) (@lem5228380 s)). Qed.
Lemma lem5228383 (s : real -> Prop) (x : real) : (term270 s x) = (term259 s x).
Proof. exact (eq_refl (term270 s x)). Qed.
Lemma lem5228384 (s : real -> Prop) : (term241 s) = (term241 s).
Proof. exact (eq_refl (term241 s)). Qed.
Lemma lem5228385 (s : real -> Prop) (x : real) : (term275 s x) = (term276 s x).
Proof. exact (MK_COMB (@lem5228384 s) (@lem5228383 s x)). Qed.
Lemma lem5228386 (s : real -> Prop) : (term277 s) = (term278 s).
Proof. exact (fun_ext (fun x : real => @lem5228385 s x)). Qed.
Lemma lem5228387 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5228388 (s : real -> Prop) : (term269 s) = (term279 s).
Proof. exact (MK_COMB (@lem5228387) (@lem5228386 s)). Qed.
Lemma lem5228389 (s : real -> Prop) : ((term268 s) = (term269 s)) = ((term263 s) = (term279 s)).
Proof. exact (MK_COMB (@lem5228382 s) (@lem5228388 s)). Qed.
Lemma lem5228390 (s : real -> Prop) : (term263 s) = (term279 s).
Proof. exact (EQ_MP (@lem5228389 s) (@lem5228374 s)). Qed.
Lemma lem5228391 (s : real -> Prop) : (term243 s) = (term279 s).
Proof. exact (TRANS (@lem5228370 s) (@lem5228390 s)). Qed.
Lemma lem5228392 : term244 = term280.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5228391 s)). Qed.
Lemma lem5228393 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5228394 : term245 = term281.
Proof. exact (MK_COMB (@lem5228393) (@lem5228392)). Qed.
Lemma lem5228423 (s : real -> Prop) (x : real) : (term276 s x) = (term282 s x).
Proof. exact (@lem19490 (term252 s) (term232 s) (term235 s x)). Qed.
Lemma lem5228424 (s : real -> Prop) : (term278 s) = (term283 s).
Proof. exact (fun_ext (fun x : real => @lem5228423 s x)). Qed.
Lemma lem5228425 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5228426 (s : real -> Prop) : (term279 s) = (term284 s).
Proof. exact (MK_COMB (@lem5228425) (@lem5228424 s)). Qed.
Lemma lem5228427 : term280 = term285.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5228426 s)). Qed.
Lemma lem5228428 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5228429 : term281 = term286.
Proof. exact (MK_COMB (@lem5228428) (@lem5228427)). Qed.
Lemma lem5228430 : term245 = term286.
Proof. exact (TRANS (@lem5228394) (@lem5228429)). Qed.
Lemma lem5228431 (h1 : term17) : term286.
Proof. exact (EQ_MP (@lem5228430) (@lem5228108 h1)). Qed.
Lemma lem5228451 (s : real -> Prop) (a : real) (x : real) : (term49 s a x) = (term49 s a x).
Proof. exact (eq_refl (term49 s a x)). Qed.
Lemma lem5228452 (s : real -> Prop) (a : real) : (term59 s a) = (term59 s a).
Proof. exact (fun_ext (fun x : real => @lem5228451 s a x)). Qed.
Lemma lem5228453 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5228455 (s : real -> Prop) (a : real) : (term60 s a) = (term60 s a).
Proof. exact (MK_COMB (@lem5228453) (@lem5228452 s a)). Qed.
Lemma lem5228456 (s : real -> Prop) (a : real) (h1 : term63 s a) : term60 s a.
Proof. exact (EQ_MP (@lem5228455 s a) (@lem5228194 s a h1)). Qed.
Lemma lem5228457 (_68432 : real) (h1 : term37) : term287 _68432.
Proof. exact (@lem5228220 h1 _68432). Qed.
Lemma lem5228458 (_68432 : real) : (term287 _68432) = (term226 _68432).
Proof. exact (eq_refl (term287 _68432)). Qed.
Lemma lem5228459 (_68432 : real) (h1 : term37) : term226 _68432.
Proof. exact (EQ_MP (@lem5228458 _68432) (@lem5228457 _68432 h1)). Qed.
Lemma lem5228460 (_68432 : real) (_68433 : real) (h1 : term37) : term288 _68432 _68433.
Proof. exact (@lem5228459 _68432 h1 _68433). Qed.
Lemma lem5228461 (_68433 : real) (_68432 : real) : (term288 _68432 _68433) = (term224 _68433 _68432).
Proof. exact (eq_refl (term288 _68432 _68433)). Qed.
Lemma lem5228462 (_68433 : real) (_68432 : real) (h1 : term37) : term224 _68433 _68432.
Proof. exact (EQ_MP (@lem5228461 _68433 _68432) (@lem5228460 _68432 _68433 h1)). Qed.
Lemma lem5228463 (_68433 : real) (_68432 : real) (_68434 : real) (h1 : term37) : term289 _68433 _68432 _68434.
Proof. exact (@lem5228462 _68433 _68432 h1 _68434). Qed.
Lemma lem5228464 (_68433 : real) (_68432 : real) (_68434 : real) : (term289 _68433 _68432 _68434) = (term221 _68433 _68432 _68434).
Proof. exact (eq_refl (term289 _68433 _68432 _68434)). Qed.
Lemma lem5228465 (_68433 : real) (_68432 : real) (_68434 : real) (h1 : term37) : term221 _68433 _68432 _68434.
Proof. exact (EQ_MP (@lem5228464 _68433 _68432 _68434) (@lem5228463 _68433 _68432 _68434 h1)). Qed.
Lemma lem5228466 (_68435 : real -> Prop) (h1 : term17) : term290 _68435.
Proof. exact (@lem5228303 h1 _68435). Qed.
Lemma lem5228467 (_68435 : real -> Prop) : (term290 _68435) = (term284 _68435).
Proof. exact (eq_refl (term290 _68435)). Qed.
Lemma lem5228468 (_68435 : real -> Prop) (h1 : term17) : term284 _68435.
Proof. exact (EQ_MP (@lem5228467 _68435) (@lem5228466 _68435 h1)). Qed.
Lemma lem5228469 (_68435 : real -> Prop) (_68436 : real) (h1 : term17) : term291 _68435 _68436.
Proof. exact (@lem5228468 _68435 h1 _68436). Qed.
Lemma lem5228470 (_68435 : real -> Prop) (_68436 : real) : (term291 _68435 _68436) = (term282 _68435 _68436).
Proof. exact (eq_refl (term291 _68435 _68436)). Qed.
Lemma lem5228471 (_68435 : real -> Prop) (_68436 : real) (h1 : term17) : term282 _68435 _68436.
Proof. exact (EQ_MP (@lem5228470 _68435 _68436) (@lem5228469 _68435 _68436 h1)). Qed.
Lemma lem5228481 (_68440 : real -> Prop) (h1 : term17) : term290 _68440.
Proof. exact (@lem5228431 h1 _68440). Qed.
Lemma lem5228482 (_68440 : real -> Prop) : (term290 _68440) = (term284 _68440).
Proof. exact (eq_refl (term290 _68440)). Qed.
Lemma lem5228483 (_68440 : real -> Prop) (h1 : term17) : term284 _68440.
Proof. exact (EQ_MP (@lem5228482 _68440) (@lem5228481 _68440 h1)). Qed.
Lemma lem5228484 (_68440 : real -> Prop) (_68441 : real) (h1 : term17) : term291 _68440 _68441.
Proof. exact (@lem5228483 _68440 h1 _68441). Qed.
Lemma lem5228485 (_68440 : real -> Prop) (_68441 : real) : (term291 _68440 _68441) = (term282 _68440 _68441).
Proof. exact (eq_refl (term291 _68440 _68441)). Qed.
Lemma lem5228486 (_68440 : real -> Prop) (_68441 : real) (h1 : term17) : term282 _68440 _68441.
Proof. exact (EQ_MP (@lem5228485 _68440 _68441) (@lem5228484 _68440 _68441 h1)). Qed.
Lemma lem5228487 (_68442 : real) (s : real -> Prop) (a : real) (h1 : term63 s a) : term292 s a _68442.
Proof. exact (@lem5228456 s a h1 _68442). Qed.
Lemma lem5228488 (s : real -> Prop) (a : real) (_68442 : real) : (term292 s a _68442) = (term49 s a _68442).
Proof. exact (eq_refl (term292 s a _68442)). Qed.
Lemma lem5228490 (_68435 : real -> Prop) (_68436 : real) (h1 : term17) : term293 _68435 _68436.
Proof. exact (proj2 (@lem5228471 _68435 _68436 h1)). Qed.
Lemma lem5228493 (_68440 : real -> Prop) (h1 : term17) : term294 _68440.
Proof. exact (proj1 (@lem5228486 _68440 (@el real) h1)). Qed.
Lemma lem5228504 (_68433 : real) (_68432 : real) (_68434 : real) : (term221 _68433 _68432 _68434) = (term295 _68433 _68432 _68434).
Proof. exact (@lem5227055 (term296 _68432 _68433) (term297 _68433 _68434) (real_lt _68432 _68434)). Qed.
Lemma lem5228505 (_68433 : real) (_68432 : real) (_68434 : real) (h1 : term37) : term295 _68433 _68432 _68434.
Proof. exact (EQ_MP (@lem5228504 _68433 _68432 _68434) (@lem5228465 _68433 _68432 _68434 h1)). Qed.
Lemma lem5228515 (s : real -> Prop) (a : real) (x : real) (h1 : term143 s a x) : term296 a x.
Proof. exact (proj2 (@lem5228190 s a x h1)). Qed.
Lemma lem5228542 (_68435 : real -> Prop) (_68436 : real) : (term293 _68435 _68436) = (term298 _68435 _68436).
Proof. exact (@lem5227055 (term299 _68435) (_68435 = (@EMPTY real)) (term235 _68435 _68436)). Qed.
Lemma lem5228543 (_68435 : real -> Prop) (_68436 : real) (h1 : term17) : term298 _68435 _68436.
Proof. exact (EQ_MP (@lem5228542 _68435 _68436) (@lem5228490 _68435 _68436 h1)). Qed.
Lemma lem5228561 (s : real -> Prop) (a : real) (h1 : term63 s a) : term300 a s.
Proof. exact (proj1 (@lem5228189 s a h1)). Qed.
Lemma lem5228567 (_68442 : real) (s : real -> Prop) (a : real) (h1 : term63 s a) : term49 s a _68442.
Proof. exact (EQ_MP (@lem5228488 s a _68442) (@lem5228487 _68442 s a h1)). Qed.
Lemma lem5228578 (_68440 : real -> Prop) : (term294 _68440) = (term301 _68440).
Proof. exact (@lem5227055 (term299 _68440) (_68440 = (@EMPTY real)) (term252 _68440)). Qed.
Lemma lem5228579 (_68440 : real -> Prop) (h1 : term17) : term301 _68440.
Proof. exact (EQ_MP (@lem5228578 _68440) (@lem5228493 _68440 h1)). Qed.
Lemma lem5228678 (s : real -> Prop) (a : real) (x : real) (h1 : term143 s a x) : term42 a s.
Proof. exact (proj1 (@lem5228188 s a x h1)). Qed.
Lemma lem5228679 (s : real -> Prop) (a : real) (x : real) (h1 : term143 s a x) : term302 a s.
Proof. exact (fun h0 : term300 a s => @lem5228678 s a x h1). Qed.
Lemma lem5228681 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5228682 (a : real) (s : real -> Prop) : (term302 a s) = (term42 a s).
Proof. exact (@lem5228681 (term42 a s)). Qed.
Lemma lem5228683 (s : real -> Prop) (a : real) (x : real) (h1 : term143 s a x) : term42 a s.
Proof. exact (EQ_MP (@lem5228682 a s) (@lem5228679 s a x h1)). Qed.
Lemma lem5228685 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : @FINITE real s.
Proof. exact (proj1 (@lem5228185 x s a h1)). Qed.
Lemma lem5228686 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term304 s.
Proof. exact (fun h0 : term299 s => @lem5228685 x s a h1). Qed.
Lemma lem5228688 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5228689 (s : real -> Prop) : (term304 s) = (@FINITE real s).
Proof. exact (@lem5228688 (@FINITE real s)). Qed.
Lemma lem5228690 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : @FINITE real s.
Proof. exact (EQ_MP (@lem5228689 s) (@lem5228686 x s a h1)). Qed.
Lemma lem5228692 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term234 s.
Proof. exact (proj2 (@lem5228185 x s a h1)). Qed.
Lemma lem5228693 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term305 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5228692 x s a h1). Qed.
Lemma lem5228695 (p : Prop) : (term306 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5228696 (s : real -> Prop) : (term305 s) = (term234 s).
Proof. exact (@lem5228695 (s = (@EMPTY real))). Qed.
Lemma lem5228697 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term234 s.
Proof. exact (EQ_MP (@lem5228696 s) (@lem5228693 x s a h1)). Qed.
Lemma lem5228699 (s : real -> Prop) (a : real) (x : real) (h1 : term143 s a x) : @IN real x s.
Proof. exact (proj1 (@lem5228190 s a x h1)). Qed.
Lemma lem5228700 (s : real -> Prop) (a : real) (x : real) (h1 : term143 s a x) : term307 x s.
Proof. exact (fun h0 : term308 x s => @lem5228699 s a x h1). Qed.
Lemma lem5228702 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5228703 (x : real) (s : real -> Prop) : (term307 x s) = (@IN real x s).
Proof. exact (@lem5228702 (@IN real x s)). Qed.
Lemma lem5228704 (s : real -> Prop) (a : real) (x : real) (h1 : term143 s a x) : @IN real x s.
Proof. exact (EQ_MP (@lem5228703 x s) (@lem5228700 s a x h1)). Qed.
Lemma lem5228710 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5228711 (_68435 : real -> Prop) (_68436 : real) : (term298 _68435 _68436) = (term309 _68435 _68436).
Proof. exact (@lem5228710 (_68435 = (@EMPTY real)) (term299 _68435) (term235 _68435 _68436)). Qed.
Lemma lem5228737 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5228738 (_68436 : real) (_68435 : real -> Prop) : (term235 _68435 _68436) = (term310 _68436 _68435).
Proof. exact (@lem5228737 (term236 _68435 _68436) (term308 _68436 _68435)). Qed.
Lemma lem5228744 (_68435 : real -> Prop) : (term230 _68435) = (term230 _68435).
Proof. exact (eq_refl (term230 _68435)). Qed.
Lemma lem5228745 (_68436 : real) (_68435 : real -> Prop) : (term311 _68435 _68436) = (term312 _68436 _68435).
Proof. exact (MK_COMB (@lem5228744 _68435) (@lem5228738 _68436 _68435)). Qed.
Lemma lem5228749 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5228750 (_68436 : real) (_68435 : real -> Prop) : (term312 _68436 _68435) = (term313 _68436 _68435).
Proof. exact (@lem5228749 (term236 _68435 _68436) (term299 _68435) (term308 _68436 _68435)). Qed.
Lemma lem5228766 (_68436 : real) (_68435 : real -> Prop) : (term311 _68435 _68436) = (term313 _68436 _68435).
Proof. exact (TRANS (@lem5228745 _68436 _68435) (@lem5228750 _68436 _68435)). Qed.
Lemma lem5228767 (_68435 : real -> Prop) : (term314 _68435) = (term314 _68435).
Proof. exact (eq_refl (term314 _68435)). Qed.
Lemma lem5228768 (_68436 : real) (_68435 : real -> Prop) : (term309 _68435 _68436) = (term315 _68436 _68435).
Proof. exact (MK_COMB (@lem5228767 _68435) (@lem5228766 _68436 _68435)). Qed.
Lemma lem5228779 (_68436 : real) (_68435 : real -> Prop) : (term298 _68435 _68436) = (term315 _68436 _68435).
Proof. exact (TRANS (@lem5228711 _68435 _68436) (@lem5228768 _68436 _68435)). Qed.
Lemma lem5228780 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5228781 (_68436 : real) (_68435 : real -> Prop) : (term316 _68435 _68436) = (term317 _68436 _68435).
Proof. exact (MK_COMB (@lem5228780) (@lem5228779 _68436 _68435)). Qed.
Lemma lem5228795 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5228796 (_68436 : real) (_68435 : real -> Prop) : (term318 _68436 _68435) = (term319 _68436 _68435).
Proof. exact (@lem5228795 (_68435 = (@EMPTY real)) (term299 _68435) (term308 _68436 _68435)). Qed.
Lemma lem5228814 (_68435 : real -> Prop) (_68436 : real) : (term320 _68435 _68436) = (term320 _68435 _68436).
Proof. exact (eq_refl (term320 _68435 _68436)). Qed.
Lemma lem5228815 (_68436 : real) (_68435 : real -> Prop) : (term321 _68436 _68435) = (term322 _68436 _68435).
Proof. exact (MK_COMB (@lem5228814 _68435 _68436) (@lem5228796 _68436 _68435)). Qed.
Lemma lem5228819 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5228820 (_68436 : real) (_68435 : real -> Prop) : (term322 _68436 _68435) = (term315 _68436 _68435).
Proof. exact (@lem5228819 (_68435 = (@EMPTY real)) (term236 _68435 _68436) (term323 _68436 _68435)). Qed.
Lemma lem5228848 (_68436 : real) (_68435 : real -> Prop) : (term321 _68436 _68435) = (term315 _68436 _68435).
Proof. exact (TRANS (@lem5228815 _68436 _68435) (@lem5228820 _68436 _68435)). Qed.
Lemma lem5228849 (_68436 : real) (_68435 : real -> Prop) : ((term298 _68435 _68436) = (term321 _68436 _68435)) = ((term315 _68436 _68435) = (term315 _68436 _68435)).
Proof. exact (MK_COMB (@lem5228781 _68436 _68435) (@lem5228848 _68436 _68435)). Qed.
Lemma lem5228851 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5228852 (x : Prop) : (x = x) = True.
Proof. exact (@lem5228851 Prop x). Qed.
Lemma lem5228853 (_68436 : real) (_68435 : real -> Prop) : ((term315 _68436 _68435) = (term315 _68436 _68435)) = True.
Proof. exact (@lem5228852 (term315 _68436 _68435)). Qed.
Lemma lem5228854 (_68436 : real) (_68435 : real -> Prop) : ((term298 _68435 _68436) = (term321 _68436 _68435)) = True.
Proof. exact (TRANS (@lem5228849 _68436 _68435) (@lem5228853 _68436 _68435)). Qed.
Lemma lem5228855 (_68436 : real) (_68435 : real -> Prop) : True = ((term298 _68435 _68436) = (term321 _68436 _68435)).
Proof. exact (SYM (@lem5228854 _68436 _68435)). Qed.
Lemma lem5228856 (_68436 : real) (_68435 : real -> Prop) : (term298 _68435 _68436) = (term321 _68436 _68435).
Proof. exact (EQ_MP (@lem5228855 _68436 _68435) (@lem0)). Qed.
Lemma lem5228857 (_68436 : real) (_68435 : real -> Prop) (h1 : term17) : term321 _68436 _68435.
Proof. exact (EQ_MP (@lem5228856 _68436 _68435) (@lem5228543 _68435 _68436 h1)). Qed.
Lemma lem5228859 (b : Prop) (a : Prop) : (a \/ b) = (term324 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5228860 (_68435 : real -> Prop) (_68436 : real) : (term321 _68436 _68435) = (term325 _68435 _68436).
Proof. exact (@lem5228859 (term318 _68436 _68435) (term236 _68435 _68436)). Qed.
Lemma lem5228862 (a : Prop) (b : Prop) : (term326 a b) = (term327 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5228863 (_68436 : real) (_68435 : real -> Prop) : (term328 _68436 _68435) = (term329 _68436 _68435).
Proof. exact (@lem5228862 (term299 _68435) (term330 _68436 _68435)). Qed.
Lemma lem5228865 (a : Prop) : (term331 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5228866 (_68435 : real -> Prop) : (term332 _68435) = (@FINITE real _68435).
Proof. exact (@lem5228865 (@FINITE real _68435)). Qed.
Lemma lem5228867 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5228868 (_68435 : real -> Prop) : (term333 _68435) = (term334 _68435).
Proof. exact (MK_COMB (@lem5228867) (@lem5228866 _68435)). Qed.
Lemma lem5228870 (a : Prop) (b : Prop) : (term326 a b) = (term327 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5228871 (_68436 : real) (_68435 : real -> Prop) : (term335 _68436 _68435) = (term336 _68436 _68435).
Proof. exact (@lem5228870 (_68435 = (@EMPTY real)) (term308 _68436 _68435)). Qed.
Lemma lem5228873 (a : Prop) : (term331 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5228874 (_68436 : real) (_68435 : real -> Prop) : (term337 _68436 _68435) = (@IN real _68436 _68435).
Proof. exact (@lem5228873 (@IN real _68436 _68435)). Qed.
Lemma lem5228875 (_68435 : real -> Prop) : (term338 _68435) = (term338 _68435).
Proof. exact (eq_refl (term338 _68435)). Qed.
Lemma lem5228876 (_68436 : real) (_68435 : real -> Prop) : (term336 _68436 _68435) = (term339 _68436 _68435).
Proof. exact (MK_COMB (@lem5228875 _68435) (@lem5228874 _68436 _68435)). Qed.
Lemma lem5228877 (_68436 : real) (_68435 : real -> Prop) : (term335 _68436 _68435) = (term339 _68436 _68435).
Proof. exact (TRANS (@lem5228871 _68436 _68435) (@lem5228876 _68436 _68435)). Qed.
Lemma lem5228878 (_68436 : real) (_68435 : real -> Prop) : (term329 _68436 _68435) = (term340 _68436 _68435).
Proof. exact (MK_COMB (@lem5228868 _68435) (@lem5228877 _68436 _68435)). Qed.
Lemma lem5228879 (_68436 : real) (_68435 : real -> Prop) : (term328 _68436 _68435) = (term340 _68436 _68435).
Proof. exact (TRANS (@lem5228863 _68436 _68435) (@lem5228878 _68436 _68435)). Qed.
Lemma lem5228880 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5228881 (_68436 : real) (_68435 : real -> Prop) : (term341 _68436 _68435) = (term342 _68436 _68435).
Proof. exact (MK_COMB (@lem5228880) (@lem5228879 _68436 _68435)). Qed.
Lemma lem5228882 (_68435 : real -> Prop) (_68436 : real) : (term236 _68435 _68436) = (term236 _68435 _68436).
Proof. exact (eq_refl (term236 _68435 _68436)). Qed.
Lemma lem5228883 (_68435 : real -> Prop) (_68436 : real) : (term325 _68435 _68436) = (term343 _68435 _68436).
Proof. exact (MK_COMB (@lem5228881 _68436 _68435) (@lem5228882 _68435 _68436)). Qed.
Lemma lem5228884 (_68435 : real -> Prop) (_68436 : real) : (term321 _68436 _68435) = (term343 _68435 _68436).
Proof. exact (TRANS (@lem5228860 _68435 _68436) (@lem5228883 _68435 _68436)). Qed.
Lemma lem5228886 (s : real -> Prop) (a : real) (x : real) (h1 : term208 x s a) (h2 : term143 s a x) : term339 x s.
Proof. exact (conj (@lem5228697 x s a h1) (@lem5228704 s a x h2)). Qed.
Lemma lem5228887 (s : real -> Prop) (a : real) (x : real) (h1 : term208 x s a) (h2 : term143 s a x) : term340 x s.
Proof. exact (conj (@lem5228690 x s a h1) (@lem5228886 s a x h1 h2)). Qed.
Lemma lem5228889 (_68435 : real -> Prop) (_68436 : real) (h1 : term17) : term343 _68435 _68436.
Proof. exact (EQ_MP (@lem5228884 _68435 _68436) (@lem5228857 _68436 _68435 h1)). Qed.
Lemma lem5228890 (s : real -> Prop) (x : real) (h1 : term17) : term343 s x.
Proof. exact (@lem5228889 s x h1). Qed.
Lemma lem5228893 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term208 x s a) (h3 : term143 s a x) : term236 s x.
Proof. exact (@lem5228890 s x h1 (@lem5228887 s a x h2 h3)). Qed.
Lemma lem5228894 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term208 x s a) (h3 : term143 s a x) : term344 s x.
Proof. exact (fun h0 : term345 s x => @lem5228893 s a x h1 h2 h3). Qed.
Lemma lem5228896 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5228897 (s : real -> Prop) (x : real) : (term344 s x) = (term236 s x).
Proof. exact (@lem5228896 (term236 s x)). Qed.
Lemma lem5228898 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term208 x s a) (h3 : term143 s a x) : term236 s x.
Proof. exact (EQ_MP (@lem5228897 s x) (@lem5228894 s a x h1 h2 h3)). Qed.
Lemma lem5228904 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5228905 (_68433 : real) (_68432 : real) (_68434 : real) : (term295 _68433 _68432 _68434) = (term346 _68433 _68432 _68434).
Proof. exact (@lem5228904 (term297 _68433 _68434) (term296 _68432 _68433) (real_lt _68432 _68434)). Qed.
Lemma lem5228919 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5228920 (_68434 : real) (_68432 : real) (_68433 : real) : (term347 _68433 _68432 _68434) = (term348 _68434 _68432 _68433).
Proof. exact (@lem5228919 (real_lt _68432 _68434) (term296 _68432 _68433)). Qed.
Lemma lem5228926 (_68433 : real) (_68434 : real) : (term349 _68433 _68434) = (term349 _68433 _68434).
Proof. exact (eq_refl (term349 _68433 _68434)). Qed.
Lemma lem5228927 (_68434 : real) (_68432 : real) (_68433 : real) : (term346 _68433 _68432 _68434) = (term350 _68434 _68432 _68433).
Proof. exact (MK_COMB (@lem5228926 _68433 _68434) (@lem5228920 _68434 _68432 _68433)). Qed.
Lemma lem5228931 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5228932 (_68434 : real) (_68432 : real) (_68433 : real) : (term350 _68434 _68432 _68433) = (term351 _68434 _68432 _68433).
Proof. exact (@lem5228931 (real_lt _68432 _68434) (term297 _68433 _68434) (term296 _68432 _68433)). Qed.
Lemma lem5228948 (_68434 : real) (_68432 : real) (_68433 : real) : (term346 _68433 _68432 _68434) = (term351 _68434 _68432 _68433).
Proof. exact (TRANS (@lem5228927 _68434 _68432 _68433) (@lem5228932 _68434 _68432 _68433)). Qed.
Lemma lem5228949 (_68434 : real) (_68432 : real) (_68433 : real) : (term295 _68433 _68432 _68434) = (term351 _68434 _68432 _68433).
Proof. exact (TRANS (@lem5228905 _68433 _68432 _68434) (@lem5228948 _68434 _68432 _68433)). Qed.
Lemma lem5228950 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5228951 (_68434 : real) (_68432 : real) (_68433 : real) : (term352 _68433 _68432 _68434) = (term353 _68434 _68432 _68433).
Proof. exact (MK_COMB (@lem5228950) (@lem5228949 _68434 _68432 _68433)). Qed.
Lemma lem5228965 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5228966 (_68434 : real) (_68432 : real) (_68433 : real) : (term217 _68432 _68433 _68434) = (term354 _68434 _68432 _68433).
Proof. exact (@lem5228965 (term297 _68433 _68434) (term296 _68432 _68433)). Qed.
Lemma lem5228972 (_68432 : real) (_68434 : real) : (term355 _68432 _68434) = (term355 _68432 _68434).
Proof. exact (eq_refl (term355 _68432 _68434)). Qed.
Lemma lem5228973 (_68434 : real) (_68432 : real) (_68433 : real) : (term356 _68432 _68433 _68434) = (term351 _68434 _68432 _68433).
Proof. exact (MK_COMB (@lem5228972 _68432 _68434) (@lem5228966 _68434 _68432 _68433)). Qed.
Lemma lem5228984 (_68434 : real) (_68432 : real) (_68433 : real) : ((term295 _68433 _68432 _68434) = (term356 _68432 _68433 _68434)) = ((term351 _68434 _68432 _68433) = (term351 _68434 _68432 _68433)).
Proof. exact (MK_COMB (@lem5228951 _68434 _68432 _68433) (@lem5228973 _68434 _68432 _68433)). Qed.
Lemma lem5228986 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5228987 (x : Prop) : (x = x) = True.
Proof. exact (@lem5228986 Prop x). Qed.
Lemma lem5228988 (_68434 : real) (_68432 : real) (_68433 : real) : ((term351 _68434 _68432 _68433) = (term351 _68434 _68432 _68433)) = True.
Proof. exact (@lem5228987 (term351 _68434 _68432 _68433)). Qed.
Lemma lem5228989 (_68432 : real) (_68433 : real) (_68434 : real) : ((term295 _68433 _68432 _68434) = (term356 _68432 _68433 _68434)) = True.
Proof. exact (TRANS (@lem5228984 _68434 _68432 _68433) (@lem5228988 _68434 _68432 _68433)). Qed.
Lemma lem5228990 (_68432 : real) (_68433 : real) (_68434 : real) : True = ((term295 _68433 _68432 _68434) = (term356 _68432 _68433 _68434)).
Proof. exact (SYM (@lem5228989 _68432 _68433 _68434)). Qed.
Lemma lem5228991 (_68432 : real) (_68433 : real) (_68434 : real) : (term295 _68433 _68432 _68434) = (term356 _68432 _68433 _68434).
Proof. exact (EQ_MP (@lem5228990 _68432 _68433 _68434) (@lem0)). Qed.
Lemma lem5228992 (_68432 : real) (_68433 : real) (_68434 : real) (h1 : term37) : term356 _68432 _68433 _68434.
Proof. exact (EQ_MP (@lem5228991 _68432 _68433 _68434) (@lem5228505 _68433 _68432 _68434 h1)). Qed.
Lemma lem5228994 (b : Prop) (a : Prop) : (a \/ b) = (term324 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5228995 (_68433 : real) (_68432 : real) (_68434 : real) : (term356 _68432 _68433 _68434) = (term357 _68433 _68432 _68434).
Proof. exact (@lem5228994 (term217 _68432 _68433 _68434) (real_lt _68432 _68434)). Qed.
Lemma lem5228997 (a : Prop) (b : Prop) : (term326 a b) = (term327 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5228998 (_68432 : real) (_68433 : real) (_68434 : real) : (term358 _68432 _68433 _68434) = (term359 _68432 _68433 _68434).
Proof. exact (@lem5228997 (term296 _68432 _68433) (term297 _68433 _68434)). Qed.
Lemma lem5229000 (a : Prop) : (term331 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5229001 (_68432 : real) (_68433 : real) : (term360 _68432 _68433) = (real_lt _68432 _68433).
Proof. exact (@lem5229000 (real_lt _68432 _68433)). Qed.
Lemma lem5229002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5229003 (_68432 : real) (_68433 : real) : (term361 _68432 _68433) = (term362 _68432 _68433).
Proof. exact (MK_COMB (@lem5229002) (@lem5229001 _68432 _68433)). Qed.
Lemma lem5229005 (a : Prop) : (term331 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5229006 (_68433 : real) (_68434 : real) : (term363 _68433 _68434) = (real_le _68433 _68434).
Proof. exact (@lem5229005 (real_le _68433 _68434)). Qed.
Lemma lem5229007 (_68432 : real) (_68433 : real) (_68434 : real) : (term359 _68432 _68433 _68434) = (term222 _68432 _68433 _68434).
Proof. exact (MK_COMB (@lem5229003 _68432 _68433) (@lem5229006 _68433 _68434)). Qed.
Lemma lem5229008 (_68432 : real) (_68433 : real) (_68434 : real) : (term358 _68432 _68433 _68434) = (term222 _68432 _68433 _68434).
Proof. exact (TRANS (@lem5228998 _68432 _68433 _68434) (@lem5229007 _68432 _68433 _68434)). Qed.
Lemma lem5229009 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5229010 (_68432 : real) (_68433 : real) (_68434 : real) : (term364 _68432 _68433 _68434) = (term365 _68432 _68433 _68434).
Proof. exact (MK_COMB (@lem5229009) (@lem5229008 _68432 _68433 _68434)). Qed.
Lemma lem5229011 (_68432 : real) (_68434 : real) : (real_lt _68432 _68434) = (real_lt _68432 _68434).
Proof. exact (eq_refl (real_lt _68432 _68434)). Qed.
Lemma lem5229012 (_68433 : real) (_68432 : real) (_68434 : real) : (term357 _68433 _68432 _68434) = (term31 _68433 _68432 _68434).
Proof. exact (MK_COMB (@lem5229010 _68432 _68433 _68434) (@lem5229011 _68432 _68434)). Qed.
Lemma lem5229013 (_68433 : real) (_68432 : real) (_68434 : real) : (term356 _68432 _68433 _68434) = (term31 _68433 _68432 _68434).
Proof. exact (TRANS (@lem5228995 _68433 _68432 _68434) (@lem5229012 _68433 _68432 _68434)). Qed.
Lemma lem5229015 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term208 x s a) (h3 : term143 s a x) : term366 a s x.
Proof. exact (conj (@lem5228683 s a x h3) (@lem5228898 s a x h1 h2 h3)). Qed.
Lemma lem5229017 (_68433 : real) (_68432 : real) (_68434 : real) (h1 : term37) : term31 _68433 _68432 _68434.
Proof. exact (EQ_MP (@lem5229013 _68433 _68432 _68434) (@lem5228992 _68432 _68433 _68434 h1)). Qed.
Lemma lem5229018 (s : real -> Prop) (a : real) (x : real) (h1 : term37) : term367 s a x.
Proof. exact (@lem5229017 (inf s) a x h1). Qed.
Lemma lem5229021 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) (h4 : term143 s a x) : real_lt a x.
Proof. exact (@lem5229018 s a x h2 (@lem5229015 s a x h1 h3 h4)). Qed.
Lemma lem5229022 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) (h4 : term143 s a x) : term368 a x.
Proof. exact (fun h0 : term296 a x => @lem5229021 s a x h1 h2 h3 h4). Qed.
Lemma lem5229024 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5229025 (a : real) (x : real) : (term368 a x) = (real_lt a x).
Proof. exact (@lem5229024 (real_lt a x)). Qed.
Lemma lem5229026 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) (h4 : term143 s a x) : real_lt a x.
Proof. exact (EQ_MP (@lem5229025 a x) (@lem5229022 s a x h1 h2 h3 h4)). Qed.
Lemma lem5229029 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5229031 (a : real) (x : real) : (term296 a x) = (term369 a x).
Proof. exact (@lem5229029 (real_lt a x)). Qed.
Lemma lem5229034 (s : real -> Prop) (a : real) (x : real) (h1 : term143 s a x) : term369 a x.
Proof. exact (EQ_MP (@lem5229031 a x) (@lem5228515 s a x h1)). Qed.
Lemma lem5229037 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) (h4 : term143 s a x) : False.
Proof. exact (@lem5229034 s a x h4 (@lem5229026 s a x h1 h2 h3 h4)). Qed.
Lemma lem5229038 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) (h4 : term143 s a x) : term370.
Proof. exact (fun h0 : ~ False => @lem5229037 s a x h1 h2 h3 h4). Qed.
Lemma lem5229040 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5229041 : term370 = False.
Proof. exact (@lem5229040 False). Qed.
Lemma lem5229042 (s : real -> Prop) (a : real) (x : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) (h4 : term143 s a x) : False.
Proof. exact (EQ_MP (@lem5229041) (@lem5229038 s a x h1 h2 h3 h4)). Qed.
Lemma lem5229125 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : @FINITE real s.
Proof. exact (proj1 (@lem5228185 x s a h1)). Qed.
Lemma lem5229126 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term304 s.
Proof. exact (fun h0 : term299 s => @lem5229125 x s a h1). Qed.
Lemma lem5229128 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5229129 (s : real -> Prop) : (term304 s) = (@FINITE real s).
Proof. exact (@lem5229128 (@FINITE real s)). Qed.
Lemma lem5229130 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : @FINITE real s.
Proof. exact (EQ_MP (@lem5229129 s) (@lem5229126 x s a h1)). Qed.
Lemma lem5229132 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term234 s.
Proof. exact (proj2 (@lem5228185 x s a h1)). Qed.
Lemma lem5229133 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term305 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5229132 x s a h1). Qed.
Lemma lem5229135 (p : Prop) : (term306 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5229136 (s : real -> Prop) : (term305 s) = (term234 s).
Proof. exact (@lem5229135 (s = (@EMPTY real))). Qed.
Lemma lem5229137 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term234 s.
Proof. exact (EQ_MP (@lem5229136 s) (@lem5229133 x s a h1)). Qed.
Lemma lem5229143 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5229144 (_68440 : real -> Prop) : (term301 _68440) = (term371 _68440).
Proof. exact (@lem5229143 (_68440 = (@EMPTY real)) (term299 _68440) (term252 _68440)). Qed.
Lemma lem5229160 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5229161 (_68440 : real -> Prop) : (term372 _68440) = (term373 _68440).
Proof. exact (@lem5229160 (term252 _68440) (term299 _68440)). Qed.
Lemma lem5229167 (_68440 : real -> Prop) : (term314 _68440) = (term314 _68440).
Proof. exact (eq_refl (term314 _68440)). Qed.
Lemma lem5229168 (_68440 : real -> Prop) : (term371 _68440) = (term374 _68440).
Proof. exact (MK_COMB (@lem5229167 _68440) (@lem5229161 _68440)). Qed.
Lemma lem5229179 (_68440 : real -> Prop) : (term301 _68440) = (term374 _68440).
Proof. exact (TRANS (@lem5229144 _68440) (@lem5229168 _68440)). Qed.
Lemma lem5229180 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5229181 (_68440 : real -> Prop) : (term375 _68440) = (term376 _68440).
Proof. exact (MK_COMB (@lem5229180) (@lem5229179 _68440)). Qed.
Lemma lem5229195 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5229196 (_68440 : real -> Prop) : (term232 _68440) = (term377 _68440).
Proof. exact (@lem5229195 (_68440 = (@EMPTY real)) (term299 _68440)). Qed.
Lemma lem5229204 (_68440 : real -> Prop) : (term378 _68440) = (term378 _68440).
Proof. exact (eq_refl (term378 _68440)). Qed.
Lemma lem5229205 (_68440 : real -> Prop) : (term379 _68440) = (term380 _68440).
Proof. exact (MK_COMB (@lem5229204 _68440) (@lem5229196 _68440)). Qed.
Lemma lem5229209 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5229210 (_68440 : real -> Prop) : (term380 _68440) = (term374 _68440).
Proof. exact (@lem5229209 (_68440 = (@EMPTY real)) (term252 _68440) (term299 _68440)). Qed.
Lemma lem5229228 (_68440 : real -> Prop) : (term379 _68440) = (term374 _68440).
Proof. exact (TRANS (@lem5229205 _68440) (@lem5229210 _68440)). Qed.
Lemma lem5229229 (_68440 : real -> Prop) : ((term301 _68440) = (term379 _68440)) = ((term374 _68440) = (term374 _68440)).
Proof. exact (MK_COMB (@lem5229181 _68440) (@lem5229228 _68440)). Qed.
Lemma lem5229231 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5229232 (x : Prop) : (x = x) = True.
Proof. exact (@lem5229231 Prop x). Qed.
Lemma lem5229233 (_68440 : real -> Prop) : ((term374 _68440) = (term374 _68440)) = True.
Proof. exact (@lem5229232 (term374 _68440)). Qed.
Lemma lem5229234 (_68440 : real -> Prop) : ((term301 _68440) = (term379 _68440)) = True.
Proof. exact (TRANS (@lem5229229 _68440) (@lem5229233 _68440)). Qed.
Lemma lem5229235 (_68440 : real -> Prop) : True = ((term301 _68440) = (term379 _68440)).
Proof. exact (SYM (@lem5229234 _68440)). Qed.
Lemma lem5229236 (_68440 : real -> Prop) : (term301 _68440) = (term379 _68440).
Proof. exact (EQ_MP (@lem5229235 _68440) (@lem0)). Qed.
Lemma lem5229237 (_68440 : real -> Prop) (h1 : term17) : term379 _68440.
Proof. exact (EQ_MP (@lem5229236 _68440) (@lem5228579 _68440 h1)). Qed.
Lemma lem5229239 (b : Prop) (a : Prop) : (a \/ b) = (term324 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5229240 (_68440 : real -> Prop) : (term379 _68440) = (term381 _68440).
Proof. exact (@lem5229239 (term232 _68440) (term252 _68440)). Qed.
Lemma lem5229242 (a : Prop) (b : Prop) : (term326 a b) = (term327 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5229243 (_68440 : real -> Prop) : (term382 _68440) = (term383 _68440).
Proof. exact (@lem5229242 (term299 _68440) (_68440 = (@EMPTY real))). Qed.
Lemma lem5229245 (a : Prop) : (term331 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5229246 (_68440 : real -> Prop) : (term332 _68440) = (@FINITE real _68440).
Proof. exact (@lem5229245 (@FINITE real _68440)). Qed.
Lemma lem5229247 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5229248 (_68440 : real -> Prop) : (term333 _68440) = (term334 _68440).
Proof. exact (MK_COMB (@lem5229247) (@lem5229246 _68440)). Qed.
Lemma lem5229249 (_68440 : real -> Prop) : (term234 _68440) = (term234 _68440).
Proof. exact (eq_refl (term234 _68440)). Qed.
Lemma lem5229250 (_68440 : real -> Prop) : (term383 _68440) = (term76 _68440).
Proof. exact (MK_COMB (@lem5229248 _68440) (@lem5229249 _68440)). Qed.
Lemma lem5229251 (_68440 : real -> Prop) : (term382 _68440) = (term76 _68440).
Proof. exact (TRANS (@lem5229243 _68440) (@lem5229250 _68440)). Qed.
Lemma lem5229252 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5229253 (_68440 : real -> Prop) : (term384 _68440) = (term28 _68440).
Proof. exact (MK_COMB (@lem5229252) (@lem5229251 _68440)). Qed.
Lemma lem5229254 (_68440 : real -> Prop) : (term252 _68440) = (term252 _68440).
Proof. exact (eq_refl (term252 _68440)). Qed.
Lemma lem5229255 (_68440 : real -> Prop) : (term381 _68440) = (term385 _68440).
Proof. exact (MK_COMB (@lem5229253 _68440) (@lem5229254 _68440)). Qed.
Lemma lem5229256 (_68440 : real -> Prop) : (term379 _68440) = (term385 _68440).
Proof. exact (TRANS (@lem5229240 _68440) (@lem5229255 _68440)). Qed.
Lemma lem5229258 (x : real) (s : real -> Prop) (a : real) (h1 : term208 x s a) : term76 s.
Proof. exact (conj (@lem5229130 x s a h1) (@lem5229137 x s a h1)). Qed.
Lemma lem5229260 (_68440 : real -> Prop) (h1 : term17) : term385 _68440.
Proof. exact (EQ_MP (@lem5229256 _68440) (@lem5229237 _68440 h1)). Qed.
Lemma lem5229261 (s : real -> Prop) (h1 : term17) : term385 s.
Proof. exact (@lem5229260 s h1). Qed.
Lemma lem5229264 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term208 x s a) : term252 s.
Proof. exact (@lem5229261 s h1 (@lem5229258 x s a h2)). Qed.
Lemma lem5229265 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term208 x s a) : term386 s.
Proof. exact (fun h0 : term387 s => @lem5229264 x s a h1 h2). Qed.
Lemma lem5229267 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5229268 (s : real -> Prop) : (term386 s) = (term252 s).
Proof. exact (@lem5229267 (term252 s)). Qed.
Lemma lem5229269 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term208 x s a) : term252 s.
Proof. exact (EQ_MP (@lem5229268 s) (@lem5229265 x s a h1 h2)). Qed.
Lemma lem5229275 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5229276 (a : real) (_68442 : real) (s : real -> Prop) : (term49 s a _68442) = (term388 a _68442 s).
Proof. exact (@lem5229275 (real_lt a _68442) (term308 _68442 s)). Qed.
Lemma lem5229282 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5229283 (a : real) (_68442 : real) (s : real -> Prop) : (term389 s a _68442) = (term390 a _68442 s).
Proof. exact (MK_COMB (@lem5229282) (@lem5229276 a _68442 s)). Qed.
Lemma lem5229289 (a : real) (_68442 : real) (s : real -> Prop) : (term388 a _68442 s) = (term388 a _68442 s).
Proof. exact (eq_refl (term388 a _68442 s)). Qed.
Lemma lem5229290 (a : real) (_68442 : real) (s : real -> Prop) : ((term49 s a _68442) = (term388 a _68442 s)) = ((term388 a _68442 s) = (term388 a _68442 s)).
Proof. exact (MK_COMB (@lem5229283 a _68442 s) (@lem5229289 a _68442 s)). Qed.
Lemma lem5229292 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5229293 (x : Prop) : (x = x) = True.
Proof. exact (@lem5229292 Prop x). Qed.
Lemma lem5229294 (a : real) (_68442 : real) (s : real -> Prop) : ((term388 a _68442 s) = (term388 a _68442 s)) = True.
Proof. exact (@lem5229293 (term388 a _68442 s)). Qed.
Lemma lem5229295 (a : real) (_68442 : real) (s : real -> Prop) : ((term49 s a _68442) = (term388 a _68442 s)) = True.
Proof. exact (TRANS (@lem5229290 a _68442 s) (@lem5229294 a _68442 s)). Qed.
Lemma lem5229296 (a : real) (_68442 : real) (s : real -> Prop) : True = ((term49 s a _68442) = (term388 a _68442 s)).
Proof. exact (SYM (@lem5229295 a _68442 s)). Qed.
Lemma lem5229297 (a : real) (_68442 : real) (s : real -> Prop) : (term49 s a _68442) = (term388 a _68442 s).
Proof. exact (EQ_MP (@lem5229296 a _68442 s) (@lem0)). Qed.
Lemma lem5229298 (_68442 : real) (s : real -> Prop) (a : real) (h1 : term63 s a) : term388 a _68442 s.
Proof. exact (EQ_MP (@lem5229297 a _68442 s) (@lem5228567 _68442 s a h1)). Qed.
Lemma lem5229300 (b : Prop) (a : Prop) : (a \/ b) = (term324 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5229301 (s : real -> Prop) (a : real) (_68442 : real) : (term388 a _68442 s) = (term391 s a _68442).
Proof. exact (@lem5229300 (term308 _68442 s) (real_lt a _68442)). Qed.
Lemma lem5229303 (a : Prop) : (term331 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5229304 (_68442 : real) (s : real -> Prop) : (term337 _68442 s) = (@IN real _68442 s).
Proof. exact (@lem5229303 (@IN real _68442 s)). Qed.
Lemma lem5229305 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5229306 (_68442 : real) (s : real -> Prop) : (term392 _68442 s) = (term393 _68442 s).
Proof. exact (MK_COMB (@lem5229305) (@lem5229304 _68442 s)). Qed.
Lemma lem5229307 (a : real) (_68442 : real) : (real_lt a _68442) = (real_lt a _68442).
Proof. exact (eq_refl (real_lt a _68442)). Qed.
Lemma lem5229308 (s : real -> Prop) (a : real) (_68442 : real) : (term391 s a _68442) = (term38 s a _68442).
Proof. exact (MK_COMB (@lem5229306 _68442 s) (@lem5229307 a _68442)). Qed.
Lemma lem5229309 (s : real -> Prop) (a : real) (_68442 : real) : (term388 a _68442 s) = (term38 s a _68442).
Proof. exact (TRANS (@lem5229301 s a _68442) (@lem5229308 s a _68442)). Qed.
Lemma lem5229312 (_68442 : real) (s : real -> Prop) (a : real) (h1 : term63 s a) : term38 s a _68442.
Proof. exact (EQ_MP (@lem5229309 s a _68442) (@lem5229298 _68442 s a h1)). Qed.
Lemma lem5229313 (s : real -> Prop) (a : real) (h1 : term63 s a) : term394 a s.
Proof. exact (@lem5229312 (inf s) s a h1). Qed.
Lemma lem5229316 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term63 s a) (h3 : term208 x s a) : term42 a s.
Proof. exact (@lem5229313 s a h2 (@lem5229269 x s a h1 h3)). Qed.
Lemma lem5229317 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term63 s a) (h3 : term208 x s a) : term302 a s.
Proof. exact (fun h0 : term300 a s => @lem5229316 x s a h1 h2 h3). Qed.
Lemma lem5229319 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5229320 (a : real) (s : real -> Prop) : (term302 a s) = (term42 a s).
Proof. exact (@lem5229319 (term42 a s)). Qed.
Lemma lem5229321 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term63 s a) (h3 : term208 x s a) : term42 a s.
Proof. exact (EQ_MP (@lem5229320 a s) (@lem5229317 x s a h1 h2 h3)). Qed.
Lemma lem5229324 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5229326 (a : real) (s : real -> Prop) : (term300 a s) = (term395 a s).
Proof. exact (@lem5229324 (term42 a s)). Qed.
Lemma lem5229329 (s : real -> Prop) (a : real) (h1 : term63 s a) : term395 a s.
Proof. exact (EQ_MP (@lem5229326 a s) (@lem5228561 s a h1)). Qed.
Lemma lem5229332 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term63 s a) (h3 : term208 x s a) : False.
Proof. exact (@lem5229329 s a h2 (@lem5229321 x s a h1 h2 h3)). Qed.
Lemma lem5229333 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term63 s a) (h3 : term208 x s a) : term370.
Proof. exact (fun h0 : ~ False => @lem5229332 x s a h1 h2 h3). Qed.
Lemma lem5229335 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5229336 : term370 = False.
Proof. exact (@lem5229335 False). Qed.
Lemma lem5229337 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term63 s a) (h3 : term208 x s a) : False.
Proof. exact (EQ_MP (@lem5229336) (@lem5229333 x s a h1 h2 h3)). Qed.
Lemma lem5229338 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) : False.
Proof. exact (or_elim (@lem5228184 x s a h3) (fun h0 : term143 s a x => @lem5229042 s a x h1 h2 h3 h0) (fun h0 : term63 s a => @lem5229337 x s a h1 h0 h3)). Qed.
Lemma lem5229339 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) : (term208 x s a) = False.
Proof. exact (prop_ext (fun h4 : term208 x s a => @lem5229338 x s a h1 h2 h3) (fun h4 : False => @lem5228183 x s a h3)). Qed.
Lemma lem5229340 (x : real) (s : real -> Prop) (a : real) (h1 : term17) (h2 : term37) (h3 : term208 x s a) : False.
Proof. exact (EQ_MP (@lem5229339 x s a h1 h2 h3) (@lem5228183 x s a h3)). Qed.
Lemma lem5229341 (s : real -> Prop) (a : real) (h1 : term17) (h2 : term37) (h3 : term211 s a) : False.
Proof. exact (ex_elim (@lem5228022 s a h3) (fun x : real => fun h0 : term210 s a x => @lem5229340 x s a h1 h2 h0)). Qed.
Lemma lem5229342 (s : real -> Prop) (h1 : term17) (h2 : term37) (h3 : term213 s) : False.
Proof. exact (ex_elim (@lem5228021 s h3) (fun a : real => fun h0 : term212 s a => @lem5229341 s a h1 h2 h0)). Qed.
Lemma lem5229343 (h1 : term17) (h2 : term37) (h3 : term10) : False.
Proof. exact (ex_elim (@lem5227805 h3) (fun s : real -> Prop => fun h0 : term214 s => @lem5229342 s h1 h2 h0)). Qed.
Lemma lem5229344 (h1 : term37) (h2 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem5229343 h0 h1 h2). Qed.
Lemma lem5229345 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem5229346 (h1 : term37) (h2 : term10) : term16.
Proof. exact (EQ_MP (@lem5229345) (@lem5229344 h1 h2)). Qed.
Lemma lem5229347 (h1 : term10) : term20.
Proof. exact (fun h0 : term37 => @lem5229346 h0 h1). Qed.
Lemma lem5229348 : term22.
Proof. exact (fun h0 : term10 => @lem5229347 h0). Qed.
Lemma lem5229349 : term11.
Proof. exact (EQ_MP (@lem5227299) (@lem5229348)). Qed.
Lemma lem5229351 : term11.
Proof. exact (@lem5227075 (@lem5229349)). Qed.
Lemma lem5229352 (h1 : term10) : term19.
Proof. exact (@lem5229351 (@lem5227060 h1)). Qed.
Lemma lem5229353 (h1 : term10) : term15.
Proof. exact (@lem5229352 h1 (@lem1370312)). Qed.
Lemma lem5229354 (h1 : term10) : False.
Proof. exact (@lem5229353 h1 (@lem5222545)). Qed.
Lemma lem5229355 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem5229354 h1) (fun h2 : False => @lem5227060 h1)). Qed.
Lemma lem5229356 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem5229355 h1) (@lem5227060 h1)). Qed.
Lemma lem5229357 : term9.
Proof. exact (fun h0 : term10 => @lem5229356 h0). Qed.
Lemma lem5229358 : term8.
Proof. exact (EQ_MP (@lem5227059) (@lem5229357)). Qed.
