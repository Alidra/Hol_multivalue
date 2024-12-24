Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_RDISTRIB_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import NADD_ADD_WELLDEF_spec.
Require Import NADD_EQ_REFL_spec.
Require Import NADD_EQ_SYM_spec.
Require Import NADD_EQ_TRANS_spec.
Require Import NADD_LDISTRIB_spec.
Require Import NADD_MUL_SYM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
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
Require Import thm69_spec.
Lemma lem1284108 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1284109 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1284110 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1284109 t1) (@lem1284108 t1)). Qed.
Lemma lem1284111 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1284110 t1 t2). Qed.
Lemma lem1284112 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1284113 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1284112 t1 t2) (@lem1284111 t1 t2)). Qed.
Lemma lem1284114 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1284113 t1 t2 t3). Qed.
Lemma lem1284115 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1284116 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1284115 t1 t2 t3) (@lem1284114 t1 t2 t3)). Qed.
Lemma lem1284117 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1284116 t1 t2 t3)). Qed.
Lemma lem1284119 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1284120 : term8 = term9.
Proof. exact (@lem1284119 term8). Qed.
Lemma lem1284121 : term9 = term8.
Proof. exact (SYM (@lem1284120)). Qed.
Lemma lem1284122 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1284125 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1284126 : term12.
Proof. exact (fun h0 : term11 => @lem1284125 h0). Qed.
Lemma lem1284127 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1284128 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1284129 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1284127 h2 (@lem1284128 h1)). Qed.
Lemma lem1284130 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem1284129 h1 h0). Qed.
Lemma lem1284131 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1284132 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1284130 h1 (@lem1284131 h2)). Qed.
Lemma lem1284133 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem1284132 h0 h1). Qed.
Lemma lem1284134 : term14.
Proof. exact (fun h0 : term12 => @lem1284133 h0). Qed.
Lemma lem1284137 : term12.
Proof. exact (@lem1284134 (@lem1284126)). Qed.
Lemma lem1284219 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1284220 : term15 = term16.
Proof. exact (@lem1284219 term17). Qed.
Lemma lem1284233 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1284234 : term19 = term20.
Proof. exact (MK_COMB (@lem1284233) (@lem1284220)). Qed.
Lemma lem1284237 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1284238 : term22 = term23.
Proof. exact (MK_COMB (@lem1284237) (@lem1284234)). Qed.
Lemma lem1284241 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1284242 : term25 = term26.
Proof. exact (MK_COMB (@lem1284241) (@lem1284238)). Qed.
Lemma lem1284245 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem1284246 : term28 = term29.
Proof. exact (MK_COMB (@lem1284245) (@lem1284242)). Qed.
Lemma lem1284249 : term30 = term30.
Proof. exact (eq_refl term30). Qed.
Lemma lem1284250 : term31 = term32.
Proof. exact (MK_COMB (@lem1284249) (@lem1284246)). Qed.
Lemma lem1284253 : term33 = term33.
Proof. exact (eq_refl term33). Qed.
Lemma lem1284260 : term11 = term34.
Proof. exact (MK_COMB (@lem1284253) (@lem1284250)). Qed.
Lemma lem1284261 (y : nadd) (x : nadd) (z : nadd) : (term35 y x z) = (term35 y x z).
Proof. exact (eq_refl (term35 y x z)). Qed.
Lemma lem1284262 (y : nadd) (x : nadd) : (term36 y x) = (term36 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1284261 y x z)). Qed.
Lemma lem1284263 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1284264 (y : nadd) (x : nadd) : (term37 y x) = (term37 y x).
Proof. exact (MK_COMB (@lem1284263) (@lem1284262 y x)). Qed.
Lemma lem1284265 (x : nadd) : (term38 x) = (term38 x).
Proof. exact (fun_ext (fun y : nadd => @lem1284264 y x)). Qed.
Lemma lem1284266 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1284267 (x : nadd) : (term39 x) = (term39 x).
Proof. exact (MK_COMB (@lem1284266) (@lem1284265 x)). Qed.
Lemma lem1284268 : term40 = term40.
Proof. exact (fun_ext (fun x : nadd => @lem1284267 x)). Qed.
Lemma lem1284269 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1284270 : term17 = term17.
Proof. exact (MK_COMB (@lem1284269) (@lem1284268)). Qed.
Lemma lem1284271 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1284272 : term16 = term16.
Proof. exact (MK_COMB (@lem1284271) (@lem1284270)). Qed.
Lemma lem1284273 (y : nadd) (x : nadd) : (term41 y x) = (term41 y x).
Proof. exact (eq_refl (term41 y x)). Qed.
Lemma lem1284274 (x : nadd) : (term42 x) = (term42 x).
Proof. exact (fun_ext (fun y : nadd => @lem1284273 y x)). Qed.
Lemma lem1284275 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1284276 (x : nadd) : (term43 x) = (term43 x).
Proof. exact (MK_COMB (@lem1284275) (@lem1284274 x)). Qed.
Lemma lem1284277 : term44 = term44.
Proof. exact (fun_ext (fun x : nadd => @lem1284276 x)). Qed.
Lemma lem1284278 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1284279 : term45 = term45.
Proof. exact (MK_COMB (@lem1284278) (@lem1284277)). Qed.
Lemma lem1284280 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1284281 : term18 = term18.
Proof. exact (MK_COMB (@lem1284280) (@lem1284279)). Qed.
Lemma lem1284282 : term20 = term20.
Proof. exact (MK_COMB (@lem1284281) (@lem1284272)). Qed.
Lemma lem1284291 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term46 x y x' y') = (term46 x y x' y').
Proof. exact (eq_refl (term46 x y x' y')). Qed.
Lemma lem1284292 (x : nadd) (y : nadd) (x' : nadd) : (term47 x y x') = (term47 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1284291 x y x' y')). Qed.
Lemma lem1284293 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1284294 (x : nadd) (y : nadd) (x' : nadd) : (term48 x y x') = (term48 x y x').
Proof. exact (MK_COMB (@lem1284293) (@lem1284292 x y x')). Qed.
Lemma lem1284295 (x : nadd) (x' : nadd) : (term49 x x') = (term49 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1284294 x y x')). Qed.
Lemma lem1284296 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1284297 (x : nadd) (x' : nadd) : (term50 x x') = (term50 x x').
Proof. exact (MK_COMB (@lem1284296) (@lem1284295 x x')). Qed.
Lemma lem1284298 (x : nadd) : (term51 x) = (term51 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1284297 x x')). Qed.
Lemma lem1284299 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1284300 (x : nadd) : (term52 x) = (term52 x).
Proof. exact (MK_COMB (@lem1284299) (@lem1284298 x)). Qed.
Lemma lem1284301 : term53 = term53.
Proof. exact (fun_ext (fun x : nadd => @lem1284300 x)). Qed.
Lemma lem1284302 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1284303 : term54 = term54.
Proof. exact (MK_COMB (@lem1284302) (@lem1284301)). Qed.
Lemma lem1284304 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1284305 : term21 = term21.
Proof. exact (MK_COMB (@lem1284304) (@lem1284303)). Qed.
Lemma lem1284306 : term23 = term23.
Proof. exact (MK_COMB (@lem1284305) (@lem1284282)). Qed.
Lemma lem1284315 (y : nadd) (x : nadd) (z : nadd) : (term55 y x z) = (term55 y x z).
Proof. exact (eq_refl (term55 y x z)). Qed.
Lemma lem1284316 (y : nadd) (x : nadd) : (term56 y x) = (term56 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1284315 y x z)). Qed.
Lemma lem1284317 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1284318 (y : nadd) (x : nadd) : (term57 y x) = (term57 y x).
Proof. exact (MK_COMB (@lem1284317) (@lem1284316 y x)). Qed.
Lemma lem1284319 (x : nadd) : (term58 x) = (term58 x).
Proof. exact (fun_ext (fun y : nadd => @lem1284318 y x)). Qed.
Lemma lem1284320 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1284321 (x : nadd) : (term59 x) = (term59 x).
Proof. exact (MK_COMB (@lem1284320) (@lem1284319 x)). Qed.
Lemma lem1284322 : term60 = term60.
Proof. exact (fun_ext (fun x : nadd => @lem1284321 x)). Qed.
Lemma lem1284323 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1284324 : term61 = term61.
Proof. exact (MK_COMB (@lem1284323) (@lem1284322)). Qed.
Lemma lem1284325 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1284326 : term24 = term24.
Proof. exact (MK_COMB (@lem1284325) (@lem1284324)). Qed.
Lemma lem1284327 : term26 = term26.
Proof. exact (MK_COMB (@lem1284326) (@lem1284306)). Qed.
Lemma lem1284328 (x : nadd) : (nadd_eq x x) = (nadd_eq x x).
Proof. exact (eq_refl (nadd_eq x x)). Qed.
Lemma lem1284329 : term62 = term62.
Proof. exact (fun_ext (fun x : nadd => @lem1284328 x)). Qed.
Lemma lem1284330 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1284331 : term63 = term63.
Proof. exact (MK_COMB (@lem1284330) (@lem1284329)). Qed.
Lemma lem1284332 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1284333 : term27 = term27.
Proof. exact (MK_COMB (@lem1284332) (@lem1284331)). Qed.
Lemma lem1284334 : term29 = term29.
Proof. exact (MK_COMB (@lem1284333) (@lem1284327)). Qed.
Lemma lem1284339 (y : nadd) (x : nadd) : ((nadd_eq x y) = (nadd_eq y x)) = ((nadd_eq x y) = (nadd_eq y x)).
Proof. exact (eq_refl ((nadd_eq x y) = (nadd_eq y x))). Qed.
Lemma lem1284340 (x : nadd) : (term64 x) = (term64 x).
Proof. exact (fun_ext (fun y : nadd => @lem1284339 y x)). Qed.
Lemma lem1284341 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1284342 (x : nadd) : (term65 x) = (term65 x).
Proof. exact (MK_COMB (@lem1284341) (@lem1284340 x)). Qed.
Lemma lem1284343 : term66 = term66.
Proof. exact (fun_ext (fun x : nadd => @lem1284342 x)). Qed.
Lemma lem1284344 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1284345 : term67 = term67.
Proof. exact (MK_COMB (@lem1284344) (@lem1284343)). Qed.
Lemma lem1284346 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1284347 : term30 = term30.
Proof. exact (MK_COMB (@lem1284346) (@lem1284345)). Qed.
Lemma lem1284348 : term32 = term32.
Proof. exact (MK_COMB (@lem1284347) (@lem1284334)). Qed.
Lemma lem1284349 (x : nadd) (y : nadd) (z : nadd) : (term68 x y z) = (term68 x y z).
Proof. exact (eq_refl (term68 x y z)). Qed.
Lemma lem1284350 (x : nadd) (y : nadd) : (term69 x y) = (term69 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1284349 x y z)). Qed.
Lemma lem1284351 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1284352 (x : nadd) (y : nadd) : (term70 x y) = (term70 x y).
Proof. exact (MK_COMB (@lem1284351) (@lem1284350 x y)). Qed.
Lemma lem1284353 (x : nadd) : (term71 x) = (term71 x).
Proof. exact (fun_ext (fun y : nadd => @lem1284352 x y)). Qed.
Lemma lem1284354 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1284355 (x : nadd) : (term72 x) = (term72 x).
Proof. exact (MK_COMB (@lem1284354) (@lem1284353 x)). Qed.
Lemma lem1284356 : term73 = term73.
Proof. exact (fun_ext (fun x : nadd => @lem1284355 x)). Qed.
Lemma lem1284357 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1284358 : term8 = term8.
Proof. exact (MK_COMB (@lem1284357) (@lem1284356)). Qed.
Lemma lem1284359 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1284360 : term10 = term10.
Proof. exact (MK_COMB (@lem1284359) (@lem1284358)). Qed.
Lemma lem1284361 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1284362 : term33 = term33.
Proof. exact (MK_COMB (@lem1284361) (@lem1284360)). Qed.
Lemma lem1284363 : term34 = term34.
Proof. exact (MK_COMB (@lem1284362) (@lem1284348)). Qed.
Lemma lem1284494 : term11 = term34.
Proof. exact (TRANS (@lem1284260) (@lem1284363)). Qed.
Lemma lem1284495 : term34 = term11.
Proof. exact (SYM (@lem1284494)). Qed.
Lemma lem1284496 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1284499 (h1 : term61) : term61.
Proof. exact (h1). Qed.
Lemma lem1284500 (h1 : term54) : term54.
Proof. exact (h1). Qed.
Lemma lem1284501 (h1 : term45) : term45.
Proof. exact (h1). Qed.
Lemma lem1284502 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1284504 (P : nadd -> Prop) : (term74 P) = (term75 P).
Proof. exact (@lem18392 nadd P). Qed.
Lemma lem1284505 (x : nadd) (y : nadd) : (term76 x y) = (term77 x y).
Proof. exact (@lem1284504 (term69 x y)). Qed.
Lemma lem1284506 (x : nadd) (y : nadd) (z : nadd) : (term78 x y z) = (term68 x y z).
Proof. exact (eq_refl (term78 x y z)). Qed.
Lemma lem1284507 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1284509 (x : nadd) (y : nadd) (z : nadd) : (term79 x y z) = (term80 x y z).
Proof. exact (MK_COMB (@lem1284507) (@lem1284506 x y z)). Qed.
Lemma lem1284510 (x : nadd) (y : nadd) : (term81 x y) = (term82 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1284509 x y z)). Qed.
Lemma lem1284511 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1284512 (x : nadd) (y : nadd) : (term77 x y) = (term83 x y).
Proof. exact (MK_COMB (@lem1284511) (@lem1284510 x y)). Qed.
Lemma lem1284513 (x : nadd) (y : nadd) : (term76 x y) = (term83 x y).
Proof. exact (TRANS (@lem1284505 x y) (@lem1284512 x y)). Qed.
Lemma lem1284514 (P : nadd -> Prop) : (term74 P) = (term75 P).
Proof. exact (@lem18392 nadd P). Qed.
Lemma lem1284515 (x : nadd) : (term84 x) = (term85 x).
Proof. exact (@lem1284514 (term71 x)). Qed.
Lemma lem1284516 (x : nadd) (y : nadd) : (term86 x y) = (term70 x y).
Proof. exact (eq_refl (term86 x y)). Qed.
Lemma lem1284517 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1284518 (x : nadd) (y : nadd) : (term87 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem1284517) (@lem1284516 x y)). Qed.
Lemma lem1284519 (x : nadd) (y : nadd) : (term87 x y) = (term83 x y).
Proof. exact (TRANS (@lem1284518 x y) (@lem1284513 x y)). Qed.
Lemma lem1284520 (x : nadd) : (term88 x) = (term89 x).
Proof. exact (fun_ext (fun y : nadd => @lem1284519 x y)). Qed.
Lemma lem1284521 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1284522 (x : nadd) : (term85 x) = (term90 x).
Proof. exact (MK_COMB (@lem1284521) (@lem1284520 x)). Qed.
Lemma lem1284523 (x : nadd) : (term84 x) = (term90 x).
Proof. exact (TRANS (@lem1284515 x) (@lem1284522 x)). Qed.
Lemma lem1284524 (P : nadd -> Prop) : (term74 P) = (term75 P).
Proof. exact (@lem18392 nadd P). Qed.
Lemma lem1284525 : term10 = term91.
Proof. exact (@lem1284524 term73). Qed.
Lemma lem1284526 (x : nadd) : (term92 x) = (term72 x).
Proof. exact (eq_refl (term92 x)). Qed.
Lemma lem1284527 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1284528 (x : nadd) : (term93 x) = (term84 x).
Proof. exact (MK_COMB (@lem1284527) (@lem1284526 x)). Qed.
Lemma lem1284529 (x : nadd) : (term93 x) = (term90 x).
Proof. exact (TRANS (@lem1284528 x) (@lem1284523 x)). Qed.
Lemma lem1284530 : term94 = term95.
Proof. exact (fun_ext (fun x : nadd => @lem1284529 x)). Qed.
Lemma lem1284531 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1284532 : term91 = term96.
Proof. exact (MK_COMB (@lem1284531) (@lem1284530)). Qed.
Lemma lem1284549 : term10 = term96.
Proof. exact (TRANS (@lem1284525) (@lem1284532)). Qed.
Lemma lem1284550 (h1 : term10) : term96.
Proof. exact (EQ_MP (@lem1284549) (@lem1284496 h1)). Qed.
Lemma lem1284857 (x : nadd) (y : nadd) (z : nadd) : (term97 x y z) = (term98 x y z).
Proof. exact (@lem17045 (nadd_eq x y) (nadd_eq y z)). Qed.
Lemma lem1284858 (x : nadd) (z : nadd) : (nadd_eq x z) = (nadd_eq x z).
Proof. exact (eq_refl (nadd_eq x z)). Qed.
Lemma lem1284859 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1284860 (x : nadd) (y : nadd) (z : nadd) : (term99 x y z) = (term100 x y z).
Proof. exact (MK_COMB (@lem1284859) (@lem1284857 x y z)). Qed.
Lemma lem1284861 (y : nadd) (x : nadd) (z : nadd) : (term101 y x z) = (term102 y x z).
Proof. exact (MK_COMB (@lem1284860 x y z) (@lem1284858 x z)). Qed.
Lemma lem1284862 (y : nadd) (x : nadd) (z : nadd) : (term55 y x z) = (term101 y x z).
Proof. exact (@lem17265 (term103 x y z) (nadd_eq x z)). Qed.
Lemma lem1284863 (y : nadd) (x : nadd) (z : nadd) : (term55 y x z) = (term102 y x z).
Proof. exact (TRANS (@lem1284862 y x z) (@lem1284861 y x z)). Qed.
Lemma lem1284864 (y : nadd) (x : nadd) : (term56 y x) = (term104 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1284863 y x z)). Qed.
Lemma lem1284865 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1284866 (y : nadd) (x : nadd) : (term57 y x) = (term105 y x).
Proof. exact (MK_COMB (@lem1284865) (@lem1284864 y x)). Qed.
Lemma lem1284867 (x : nadd) : (term58 x) = (term106 x).
Proof. exact (fun_ext (fun y : nadd => @lem1284866 y x)). Qed.
Lemma lem1284868 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1284869 (x : nadd) : (term59 x) = (term107 x).
Proof. exact (MK_COMB (@lem1284868) (@lem1284867 x)). Qed.
Lemma lem1284870 : term60 = term108.
Proof. exact (fun_ext (fun x : nadd => @lem1284869 x)). Qed.
Lemma lem1284871 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1284932 : term61 = term109.
Proof. exact (MK_COMB (@lem1284871) (@lem1284870)). Qed.
Lemma lem1284933 (h1 : term61) : term109.
Proof. exact (EQ_MP (@lem1284932) (@lem1284499 h1)). Qed.
Lemma lem1284940 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term110 x x' y y') = (term111 x x' y y').
Proof. exact (@lem17045 (nadd_eq x x') (nadd_eq y y')). Qed.
Lemma lem1284941 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term112 x y x' y') = (term112 x y x' y').
Proof. exact (eq_refl (term112 x y x' y')). Qed.
Lemma lem1284942 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1284943 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term113 x x' y y') = (term114 x x' y y').
Proof. exact (MK_COMB (@lem1284942) (@lem1284940 x x' y y')). Qed.
Lemma lem1284944 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term115 x y x' y') = (term116 x y x' y').
Proof. exact (MK_COMB (@lem1284943 x x' y y') (@lem1284941 x y x' y')). Qed.
Lemma lem1284945 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term46 x y x' y') = (term115 x y x' y').
Proof. exact (@lem17265 (term117 x x' y y') (term112 x y x' y')). Qed.
Lemma lem1284946 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term46 x y x' y') = (term116 x y x' y').
Proof. exact (TRANS (@lem1284945 x y x' y') (@lem1284944 x y x' y')). Qed.
Lemma lem1284947 (x : nadd) (y : nadd) (x' : nadd) : (term47 x y x') = (term118 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1284946 x y x' y')). Qed.
Lemma lem1284948 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1284949 (x : nadd) (y : nadd) (x' : nadd) : (term48 x y x') = (term119 x y x').
Proof. exact (MK_COMB (@lem1284948) (@lem1284947 x y x')). Qed.
Lemma lem1284950 (x : nadd) (x' : nadd) : (term49 x x') = (term120 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1284949 x y x')). Qed.
Lemma lem1284951 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1284952 (x : nadd) (x' : nadd) : (term50 x x') = (term121 x x').
Proof. exact (MK_COMB (@lem1284951) (@lem1284950 x x')). Qed.
Lemma lem1284953 (x : nadd) : (term51 x) = (term122 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1284952 x x')). Qed.
Lemma lem1284954 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1284955 (x : nadd) : (term52 x) = (term123 x).
Proof. exact (MK_COMB (@lem1284954) (@lem1284953 x)). Qed.
Lemma lem1284956 : term53 = term124.
Proof. exact (fun_ext (fun x : nadd => @lem1284955 x)). Qed.
Lemma lem1284957 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285022 : term54 = term125.
Proof. exact (MK_COMB (@lem1284957) (@lem1284956)). Qed.
Lemma lem1285023 (h1 : term54) : term125.
Proof. exact (EQ_MP (@lem1285022) (@lem1284500 h1)). Qed.
Lemma lem1285024 (y : nadd) (x : nadd) : (term41 y x) = (term41 y x).
Proof. exact (eq_refl (term41 y x)). Qed.
Lemma lem1285025 (x : nadd) : (term42 x) = (term42 x).
Proof. exact (fun_ext (fun y : nadd => @lem1285024 y x)). Qed.
Lemma lem1285026 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285027 (x : nadd) : (term43 x) = (term43 x).
Proof. exact (MK_COMB (@lem1285026) (@lem1285025 x)). Qed.
Lemma lem1285028 : term44 = term44.
Proof. exact (fun_ext (fun x : nadd => @lem1285027 x)). Qed.
Lemma lem1285029 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285042 : term45 = term45.
Proof. exact (MK_COMB (@lem1285029) (@lem1285028)). Qed.
Lemma lem1285043 (h1 : term45) : term45.
Proof. exact (EQ_MP (@lem1285042) (@lem1284501 h1)). Qed.
Lemma lem1285044 (y : nadd) (x : nadd) (z : nadd) : (term35 y x z) = (term35 y x z).
Proof. exact (eq_refl (term35 y x z)). Qed.
Lemma lem1285045 (y : nadd) (x : nadd) : (term36 y x) = (term36 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1285044 y x z)). Qed.
Lemma lem1285046 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285047 (y : nadd) (x : nadd) : (term37 y x) = (term37 y x).
Proof. exact (MK_COMB (@lem1285046) (@lem1285045 y x)). Qed.
Lemma lem1285048 (x : nadd) : (term38 x) = (term38 x).
Proof. exact (fun_ext (fun y : nadd => @lem1285047 y x)). Qed.
Lemma lem1285049 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285050 (x : nadd) : (term39 x) = (term39 x).
Proof. exact (MK_COMB (@lem1285049) (@lem1285048 x)). Qed.
Lemma lem1285051 : term40 = term40.
Proof. exact (fun_ext (fun x : nadd => @lem1285050 x)). Qed.
Lemma lem1285052 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285069 : term17 = term17.
Proof. exact (MK_COMB (@lem1285052) (@lem1285051)). Qed.
Lemma lem1285070 (h1 : term17) : term17.
Proof. exact (EQ_MP (@lem1285069) (@lem1284502 h1)). Qed.
Lemma lem1285071 (x : nadd) (h1 : term90 x) : term90 x.
Proof. exact (h1). Qed.
Lemma lem1285072 (x : nadd) (y : nadd) (h1 : term83 x y) : term83 x y.
Proof. exact (h1). Qed.
Lemma lem1285153 (y : nadd) (x : nadd) (z : nadd) : (term102 y x z) = (term102 y x z).
Proof. exact (eq_refl (term102 y x z)). Qed.
Lemma lem1285154 (y : nadd) (x : nadd) : (term104 y x) = (term104 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1285153 y x z)). Qed.
Lemma lem1285155 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285156 (y : nadd) (x : nadd) : (term105 y x) = (term105 y x).
Proof. exact (MK_COMB (@lem1285155) (@lem1285154 y x)). Qed.
Lemma lem1285157 (x : nadd) : (term106 x) = (term106 x).
Proof. exact (fun_ext (fun y : nadd => @lem1285156 y x)). Qed.
Lemma lem1285158 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285159 (x : nadd) : (term107 x) = (term107 x).
Proof. exact (MK_COMB (@lem1285158) (@lem1285157 x)). Qed.
Lemma lem1285160 : term108 = term108.
Proof. exact (fun_ext (fun x : nadd => @lem1285159 x)). Qed.
Lemma lem1285161 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285162 : term109 = term109.
Proof. exact (MK_COMB (@lem1285161) (@lem1285160)). Qed.
Lemma lem1285163 (h1 : term61) : term109.
Proof. exact (EQ_MP (@lem1285162) (@lem1284933 h1)). Qed.
Lemma lem1285196 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term116 x y x' y') = (term116 x y x' y').
Proof. exact (eq_refl (term116 x y x' y')). Qed.
Lemma lem1285197 (x : nadd) (y : nadd) (x' : nadd) : (term118 x y x') = (term118 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1285196 x y x' y')). Qed.
Lemma lem1285198 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285199 (x : nadd) (y : nadd) (x' : nadd) : (term119 x y x') = (term119 x y x').
Proof. exact (MK_COMB (@lem1285198) (@lem1285197 x y x')). Qed.
Lemma lem1285200 (x : nadd) (x' : nadd) : (term120 x x') = (term120 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1285199 x y x')). Qed.
Lemma lem1285201 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285202 (x : nadd) (x' : nadd) : (term121 x x') = (term121 x x').
Proof. exact (MK_COMB (@lem1285201) (@lem1285200 x x')). Qed.
Lemma lem1285203 (x : nadd) : (term122 x) = (term122 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1285202 x x')). Qed.
Lemma lem1285204 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285205 (x : nadd) : (term123 x) = (term123 x).
Proof. exact (MK_COMB (@lem1285204) (@lem1285203 x)). Qed.
Lemma lem1285206 : term124 = term124.
Proof. exact (fun_ext (fun x : nadd => @lem1285205 x)). Qed.
Lemma lem1285207 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285208 : term125 = term125.
Proof. exact (MK_COMB (@lem1285207) (@lem1285206)). Qed.
Lemma lem1285209 (h1 : term54) : term125.
Proof. exact (EQ_MP (@lem1285208) (@lem1285023 h1)). Qed.
Lemma lem1285222 (y : nadd) (x : nadd) : (term41 y x) = (term41 y x).
Proof. exact (eq_refl (term41 y x)). Qed.
Lemma lem1285223 (x : nadd) : (term42 x) = (term42 x).
Proof. exact (fun_ext (fun y : nadd => @lem1285222 y x)). Qed.
Lemma lem1285224 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285225 (x : nadd) : (term43 x) = (term43 x).
Proof. exact (MK_COMB (@lem1285224) (@lem1285223 x)). Qed.
Lemma lem1285226 : term44 = term44.
Proof. exact (fun_ext (fun x : nadd => @lem1285225 x)). Qed.
Lemma lem1285227 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285228 : term45 = term45.
Proof. exact (MK_COMB (@lem1285227) (@lem1285226)). Qed.
Lemma lem1285229 (h1 : term45) : term45.
Proof. exact (EQ_MP (@lem1285228) (@lem1285043 h1)). Qed.
Lemma lem1285254 (y : nadd) (x : nadd) (z : nadd) : (term35 y x z) = (term35 y x z).
Proof. exact (eq_refl (term35 y x z)). Qed.
Lemma lem1285255 (y : nadd) (x : nadd) : (term36 y x) = (term36 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1285254 y x z)). Qed.
Lemma lem1285256 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285257 (y : nadd) (x : nadd) : (term37 y x) = (term37 y x).
Proof. exact (MK_COMB (@lem1285256) (@lem1285255 y x)). Qed.
Lemma lem1285258 (x : nadd) : (term38 x) = (term38 x).
Proof. exact (fun_ext (fun y : nadd => @lem1285257 y x)). Qed.
Lemma lem1285259 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285260 (x : nadd) : (term39 x) = (term39 x).
Proof. exact (MK_COMB (@lem1285259) (@lem1285258 x)). Qed.
Lemma lem1285261 : term40 = term40.
Proof. exact (fun_ext (fun x : nadd => @lem1285260 x)). Qed.
Lemma lem1285262 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285263 : term17 = term17.
Proof. exact (MK_COMB (@lem1285262) (@lem1285261)). Qed.
Lemma lem1285264 (h1 : term17) : term17.
Proof. exact (EQ_MP (@lem1285263) (@lem1285070 h1)). Qed.
Lemma lem1285292 (x : nadd) (y : nadd) (z : nadd) (h1 : term80 x y z) : term80 x y z.
Proof. exact (h1). Qed.
Lemma lem1285315 (y : nadd) (x : nadd) (z : nadd) : (term102 y x z) = (term102 y x z).
Proof. exact (eq_refl (term102 y x z)). Qed.
Lemma lem1285316 (y : nadd) (x : nadd) : (term104 y x) = (term104 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1285315 y x z)). Qed.
Lemma lem1285317 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285318 (y : nadd) (x : nadd) : (term105 y x) = (term105 y x).
Proof. exact (MK_COMB (@lem1285317) (@lem1285316 y x)). Qed.
Lemma lem1285319 (x : nadd) : (term106 x) = (term106 x).
Proof. exact (fun_ext (fun y : nadd => @lem1285318 y x)). Qed.
Lemma lem1285320 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285321 (x : nadd) : (term107 x) = (term107 x).
Proof. exact (MK_COMB (@lem1285320) (@lem1285319 x)). Qed.
Lemma lem1285322 : term108 = term108.
Proof. exact (fun_ext (fun x : nadd => @lem1285321 x)). Qed.
Lemma lem1285323 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285325 : term109 = term109.
Proof. exact (MK_COMB (@lem1285323) (@lem1285322)). Qed.
Lemma lem1285326 (h1 : term61) : term109.
Proof. exact (EQ_MP (@lem1285325) (@lem1285163 h1)). Qed.
Lemma lem1285340 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term116 x y x' y') = (term116 x y x' y').
Proof. exact (eq_refl (term116 x y x' y')). Qed.
Lemma lem1285341 (x : nadd) (y : nadd) (x' : nadd) : (term118 x y x') = (term118 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1285340 x y x' y')). Qed.
Lemma lem1285342 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285343 (x : nadd) (y : nadd) (x' : nadd) : (term119 x y x') = (term119 x y x').
Proof. exact (MK_COMB (@lem1285342) (@lem1285341 x y x')). Qed.
Lemma lem1285344 (x : nadd) (x' : nadd) : (term120 x x') = (term120 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1285343 x y x')). Qed.
Lemma lem1285345 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285346 (x : nadd) (x' : nadd) : (term121 x x') = (term121 x x').
Proof. exact (MK_COMB (@lem1285345) (@lem1285344 x x')). Qed.
Lemma lem1285347 (x : nadd) : (term122 x) = (term122 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1285346 x x')). Qed.
Lemma lem1285348 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285349 (x : nadd) : (term123 x) = (term123 x).
Proof. exact (MK_COMB (@lem1285348) (@lem1285347 x)). Qed.
Lemma lem1285350 : term124 = term124.
Proof. exact (fun_ext (fun x : nadd => @lem1285349 x)). Qed.
Lemma lem1285351 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285353 : term125 = term125.
Proof. exact (MK_COMB (@lem1285351) (@lem1285350)). Qed.
Lemma lem1285354 (h1 : term54) : term125.
Proof. exact (EQ_MP (@lem1285353) (@lem1285209 h1)). Qed.
Lemma lem1285356 (y : nadd) (x : nadd) : (term41 y x) = (term41 y x).
Proof. exact (eq_refl (term41 y x)). Qed.
Lemma lem1285357 (x : nadd) : (term42 x) = (term42 x).
Proof. exact (fun_ext (fun y : nadd => @lem1285356 y x)). Qed.
Lemma lem1285358 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285359 (x : nadd) : (term43 x) = (term43 x).
Proof. exact (MK_COMB (@lem1285358) (@lem1285357 x)). Qed.
Lemma lem1285360 : term44 = term44.
Proof. exact (fun_ext (fun x : nadd => @lem1285359 x)). Qed.
Lemma lem1285361 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285363 : term45 = term45.
Proof. exact (MK_COMB (@lem1285361) (@lem1285360)). Qed.
Lemma lem1285364 (h1 : term45) : term45.
Proof. exact (EQ_MP (@lem1285363) (@lem1285229 h1)). Qed.
Lemma lem1285366 (y : nadd) (x : nadd) (z : nadd) : (term35 y x z) = (term35 y x z).
Proof. exact (eq_refl (term35 y x z)). Qed.
Lemma lem1285367 (y : nadd) (x : nadd) : (term36 y x) = (term36 y x).
Proof. exact (fun_ext (fun z : nadd => @lem1285366 y x z)). Qed.
Lemma lem1285368 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285369 (y : nadd) (x : nadd) : (term37 y x) = (term37 y x).
Proof. exact (MK_COMB (@lem1285368) (@lem1285367 y x)). Qed.
Lemma lem1285370 (x : nadd) : (term38 x) = (term38 x).
Proof. exact (fun_ext (fun y : nadd => @lem1285369 y x)). Qed.
Lemma lem1285371 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285372 (x : nadd) : (term39 x) = (term39 x).
Proof. exact (MK_COMB (@lem1285371) (@lem1285370 x)). Qed.
Lemma lem1285373 : term40 = term40.
Proof. exact (fun_ext (fun x : nadd => @lem1285372 x)). Qed.
Lemma lem1285374 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1285376 : term17 = term17.
Proof. exact (MK_COMB (@lem1285374) (@lem1285373)). Qed.
Lemma lem1285377 (h1 : term17) : term17.
Proof. exact (EQ_MP (@lem1285376) (@lem1285264 h1)). Qed.
Lemma lem1285381 (x : nadd) (y : nadd) (z : nadd) (h1 : term80 x y z) : term80 x y z.
Proof. exact (h1). Qed.
Lemma lem1285417 (_23244 : nadd) (h1 : term61) : term126 _23244.
Proof. exact (@lem1285326 h1 _23244). Qed.
Lemma lem1285418 (_23244 : nadd) : (term126 _23244) = (term107 _23244).
Proof. exact (eq_refl (term126 _23244)). Qed.
Lemma lem1285419 (_23244 : nadd) (h1 : term61) : term107 _23244.
Proof. exact (EQ_MP (@lem1285418 _23244) (@lem1285417 _23244 h1)). Qed.
Lemma lem1285420 (_23244 : nadd) (_23245 : nadd) (h1 : term61) : term127 _23244 _23245.
Proof. exact (@lem1285419 _23244 h1 _23245). Qed.
Lemma lem1285421 (_23245 : nadd) (_23244 : nadd) : (term127 _23244 _23245) = (term105 _23245 _23244).
Proof. exact (eq_refl (term127 _23244 _23245)). Qed.
Lemma lem1285422 (_23245 : nadd) (_23244 : nadd) (h1 : term61) : term105 _23245 _23244.
Proof. exact (EQ_MP (@lem1285421 _23245 _23244) (@lem1285420 _23244 _23245 h1)). Qed.
Lemma lem1285423 (_23245 : nadd) (_23244 : nadd) (_23246 : nadd) (h1 : term61) : term128 _23245 _23244 _23246.
Proof. exact (@lem1285422 _23245 _23244 h1 _23246). Qed.
Lemma lem1285424 (_23245 : nadd) (_23244 : nadd) (_23246 : nadd) : (term128 _23245 _23244 _23246) = (term102 _23245 _23244 _23246).
Proof. exact (eq_refl (term128 _23245 _23244 _23246)). Qed.
Lemma lem1285425 (_23245 : nadd) (_23244 : nadd) (_23246 : nadd) (h1 : term61) : term102 _23245 _23244 _23246.
Proof. exact (EQ_MP (@lem1285424 _23245 _23244 _23246) (@lem1285423 _23245 _23244 _23246 h1)). Qed.
Lemma lem1285426 (_23247 : nadd) (h1 : term54) : term129 _23247.
Proof. exact (@lem1285354 h1 _23247). Qed.
Lemma lem1285427 (_23247 : nadd) : (term129 _23247) = (term123 _23247).
Proof. exact (eq_refl (term129 _23247)). Qed.
Lemma lem1285428 (_23247 : nadd) (h1 : term54) : term123 _23247.
Proof. exact (EQ_MP (@lem1285427 _23247) (@lem1285426 _23247 h1)). Qed.
Lemma lem1285429 (_23247 : nadd) (_23248 : nadd) (h1 : term54) : term130 _23247 _23248.
Proof. exact (@lem1285428 _23247 h1 _23248). Qed.
Lemma lem1285430 (_23247 : nadd) (_23248 : nadd) : (term130 _23247 _23248) = (term121 _23247 _23248).
Proof. exact (eq_refl (term130 _23247 _23248)). Qed.
Lemma lem1285431 (_23247 : nadd) (_23248 : nadd) (h1 : term54) : term121 _23247 _23248.
Proof. exact (EQ_MP (@lem1285430 _23247 _23248) (@lem1285429 _23247 _23248 h1)). Qed.
Lemma lem1285432 (_23247 : nadd) (_23248 : nadd) (_23249 : nadd) (h1 : term54) : term131 _23247 _23248 _23249.
Proof. exact (@lem1285431 _23247 _23248 h1 _23249). Qed.
Lemma lem1285433 (_23247 : nadd) (_23249 : nadd) (_23248 : nadd) : (term131 _23247 _23248 _23249) = (term119 _23247 _23249 _23248).
Proof. exact (eq_refl (term131 _23247 _23248 _23249)). Qed.
Lemma lem1285434 (_23247 : nadd) (_23249 : nadd) (_23248 : nadd) (h1 : term54) : term119 _23247 _23249 _23248.
Proof. exact (EQ_MP (@lem1285433 _23247 _23249 _23248) (@lem1285432 _23247 _23248 _23249 h1)). Qed.
Lemma lem1285435 (_23247 : nadd) (_23249 : nadd) (_23248 : nadd) (_23250 : nadd) (h1 : term54) : term132 _23247 _23249 _23248 _23250.
Proof. exact (@lem1285434 _23247 _23249 _23248 h1 _23250). Qed.
Lemma lem1285436 (_23247 : nadd) (_23249 : nadd) (_23248 : nadd) (_23250 : nadd) : (term132 _23247 _23249 _23248 _23250) = (term116 _23247 _23249 _23248 _23250).
Proof. exact (eq_refl (term132 _23247 _23249 _23248 _23250)). Qed.
Lemma lem1285437 (_23247 : nadd) (_23249 : nadd) (_23248 : nadd) (_23250 : nadd) (h1 : term54) : term116 _23247 _23249 _23248 _23250.
Proof. exact (EQ_MP (@lem1285436 _23247 _23249 _23248 _23250) (@lem1285435 _23247 _23249 _23248 _23250 h1)). Qed.
Lemma lem1285438 (_23251 : nadd) (h1 : term45) : term133 _23251.
Proof. exact (@lem1285364 h1 _23251). Qed.
Lemma lem1285439 (_23251 : nadd) : (term133 _23251) = (term43 _23251).
Proof. exact (eq_refl (term133 _23251)). Qed.
Lemma lem1285440 (_23251 : nadd) (h1 : term45) : term43 _23251.
Proof. exact (EQ_MP (@lem1285439 _23251) (@lem1285438 _23251 h1)). Qed.
Lemma lem1285441 (_23251 : nadd) (_23252 : nadd) (h1 : term45) : term134 _23251 _23252.
Proof. exact (@lem1285440 _23251 h1 _23252). Qed.
Lemma lem1285442 (_23252 : nadd) (_23251 : nadd) : (term134 _23251 _23252) = (term41 _23252 _23251).
Proof. exact (eq_refl (term134 _23251 _23252)). Qed.
Lemma lem1285444 (_23253 : nadd) (h1 : term17) : term135 _23253.
Proof. exact (@lem1285377 h1 _23253). Qed.
Lemma lem1285445 (_23253 : nadd) : (term135 _23253) = (term39 _23253).
Proof. exact (eq_refl (term135 _23253)). Qed.
Lemma lem1285446 (_23253 : nadd) (h1 : term17) : term39 _23253.
Proof. exact (EQ_MP (@lem1285445 _23253) (@lem1285444 _23253 h1)). Qed.
Lemma lem1285447 (_23253 : nadd) (_23254 : nadd) (h1 : term17) : term136 _23253 _23254.
Proof. exact (@lem1285446 _23253 h1 _23254). Qed.
Lemma lem1285448 (_23254 : nadd) (_23253 : nadd) : (term136 _23253 _23254) = (term37 _23254 _23253).
Proof. exact (eq_refl (term136 _23253 _23254)). Qed.
Lemma lem1285449 (_23254 : nadd) (_23253 : nadd) (h1 : term17) : term37 _23254 _23253.
Proof. exact (EQ_MP (@lem1285448 _23254 _23253) (@lem1285447 _23253 _23254 h1)). Qed.
Lemma lem1285450 (_23254 : nadd) (_23253 : nadd) (_23255 : nadd) (h1 : term17) : term137 _23254 _23253 _23255.
Proof. exact (@lem1285449 _23254 _23253 h1 _23255). Qed.
Lemma lem1285451 (_23254 : nadd) (_23253 : nadd) (_23255 : nadd) : (term137 _23254 _23253 _23255) = (term35 _23254 _23253 _23255).
Proof. exact (eq_refl (term137 _23254 _23253 _23255)). Qed.
Lemma lem1285477 (_23245 : nadd) (_23244 : nadd) (_23246 : nadd) : (term102 _23245 _23244 _23246) = (term138 _23245 _23244 _23246).
Proof. exact (@lem1284117 (term139 _23244 _23245) (term139 _23245 _23246) (nadd_eq _23244 _23246)). Qed.
Lemma lem1285478 (_23245 : nadd) (_23244 : nadd) (_23246 : nadd) (h1 : term61) : term138 _23245 _23244 _23246.
Proof. exact (EQ_MP (@lem1285477 _23245 _23244 _23246) (@lem1285425 _23245 _23244 _23246 h1)). Qed.
Lemma lem1285489 (_23247 : nadd) (_23249 : nadd) (_23248 : nadd) (_23250 : nadd) : (term116 _23247 _23249 _23248 _23250) = (term140 _23247 _23249 _23248 _23250).
Proof. exact (@lem1284117 (term139 _23247 _23248) (term139 _23249 _23250) (term112 _23247 _23249 _23248 _23250)). Qed.
Lemma lem1285490 (_23247 : nadd) (_23249 : nadd) (_23248 : nadd) (_23250 : nadd) (h1 : term54) : term140 _23247 _23249 _23248 _23250.
Proof. exact (EQ_MP (@lem1285489 _23247 _23249 _23248 _23250) (@lem1285437 _23247 _23249 _23248 _23250 h1)). Qed.
Lemma lem1285496 (x : nadd) (y : nadd) (z : nadd) (h1 : term80 x y z) : term80 x y z.
Proof. exact (h1). Qed.
Lemma lem1285510 (_23252 : nadd) (_23251 : nadd) (h1 : term45) : term41 _23252 _23251.
Proof. exact (EQ_MP (@lem1285442 _23252 _23251) (@lem1285441 _23251 _23252 h1)). Qed.
Lemma lem1285511 (z : nadd) (x : nadd) (y : nadd) (h1 : term45) : term141 z x y.
Proof. exact (@lem1285510 z (nadd_add x y) h1). Qed.
Lemma lem1285512 (z : nadd) (x : nadd) (y : nadd) (h1 : term45) : term142 z x y.
Proof. exact (fun h0 : term143 z x y => @lem1285511 z x y h1). Qed.
Lemma lem1285514 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1285515 (z : nadd) (x : nadd) (y : nadd) : (term142 z x y) = (term141 z x y).
Proof. exact (@lem1285514 (term141 z x y)). Qed.
Lemma lem1285516 (z : nadd) (x : nadd) (y : nadd) (h1 : term45) : term141 z x y.
Proof. exact (EQ_MP (@lem1285515 z x y) (@lem1285512 z x y h1)). Qed.
Lemma lem1285518 (_23254 : nadd) (_23253 : nadd) (_23255 : nadd) (h1 : term17) : term35 _23254 _23253 _23255.
Proof. exact (EQ_MP (@lem1285451 _23254 _23253 _23255) (@lem1285450 _23254 _23253 _23255 h1)). Qed.
Lemma lem1285519 (x : nadd) (z : nadd) (y : nadd) (h1 : term17) : term35 x z y.
Proof. exact (@lem1285518 x z y h1). Qed.
Lemma lem1285520 (x : nadd) (z : nadd) (y : nadd) (h1 : term17) : term145 x z y.
Proof. exact (fun h0 : term146 x z y => @lem1285519 x z y h1). Qed.
Lemma lem1285522 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1285523 (x : nadd) (z : nadd) (y : nadd) : (term145 x z y) = (term35 x z y).
Proof. exact (@lem1285522 (term35 x z y)). Qed.
Lemma lem1285524 (x : nadd) (z : nadd) (y : nadd) (h1 : term17) : term35 x z y.
Proof. exact (EQ_MP (@lem1285523 x z y) (@lem1285520 x z y h1)). Qed.
Lemma lem1285526 (_23252 : nadd) (_23251 : nadd) (h1 : term45) : term41 _23252 _23251.
Proof. exact (EQ_MP (@lem1285442 _23252 _23251) (@lem1285441 _23251 _23252 h1)). Qed.
Lemma lem1285527 (x : nadd) (z : nadd) (h1 : term45) : term41 x z.
Proof. exact (@lem1285526 x z h1). Qed.
Lemma lem1285528 (x : nadd) (z : nadd) (h1 : term45) : term147 x z.
Proof. exact (fun h0 : term148 x z => @lem1285527 x z h1). Qed.
Lemma lem1285530 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1285531 (x : nadd) (z : nadd) : (term147 x z) = (term41 x z).
Proof. exact (@lem1285530 (term41 x z)). Qed.
Lemma lem1285532 (x : nadd) (z : nadd) (h1 : term45) : term41 x z.
Proof. exact (EQ_MP (@lem1285531 x z) (@lem1285528 x z h1)). Qed.
Lemma lem1285534 (_23252 : nadd) (_23251 : nadd) (h1 : term45) : term41 _23252 _23251.
Proof. exact (EQ_MP (@lem1285442 _23252 _23251) (@lem1285441 _23251 _23252 h1)). Qed.
Lemma lem1285535 (y : nadd) (z : nadd) (h1 : term45) : term41 y z.
Proof. exact (@lem1285534 y z h1). Qed.
Lemma lem1285536 (y : nadd) (z : nadd) (h1 : term45) : term147 y z.
Proof. exact (fun h0 : term148 y z => @lem1285535 y z h1). Qed.
Lemma lem1285538 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1285539 (y : nadd) (z : nadd) : (term147 y z) = (term41 y z).
Proof. exact (@lem1285538 (term41 y z)). Qed.
Lemma lem1285540 (y : nadd) (z : nadd) (h1 : term45) : term41 y z.
Proof. exact (EQ_MP (@lem1285539 y z) (@lem1285536 y z h1)). Qed.
Lemma lem1285556 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1285557 (_23247 : nadd) (_23248 : nadd) (_23249 : nadd) (_23250 : nadd) : (term149 _23247 _23249 _23248 _23250) = (term150 _23247 _23248 _23249 _23250).
Proof. exact (@lem1285556 (term112 _23247 _23249 _23248 _23250) (term139 _23249 _23250)). Qed.
Lemma lem1285563 (_23247 : nadd) (_23248 : nadd) : (term151 _23247 _23248) = (term151 _23247 _23248).
Proof. exact (eq_refl (term151 _23247 _23248)). Qed.
Lemma lem1285564 (_23247 : nadd) (_23248 : nadd) (_23249 : nadd) (_23250 : nadd) : (term140 _23247 _23249 _23248 _23250) = (term152 _23247 _23248 _23249 _23250).
Proof. exact (MK_COMB (@lem1285563 _23247 _23248) (@lem1285557 _23247 _23248 _23249 _23250)). Qed.
Lemma lem1285568 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1285569 (_23247 : nadd) (_23248 : nadd) (_23249 : nadd) (_23250 : nadd) : (term152 _23247 _23248 _23249 _23250) = (term153 _23247 _23248 _23249 _23250).
Proof. exact (@lem1285568 (term112 _23247 _23249 _23248 _23250) (term139 _23247 _23248) (term139 _23249 _23250)). Qed.
Lemma lem1285585 (_23247 : nadd) (_23248 : nadd) (_23249 : nadd) (_23250 : nadd) : (term140 _23247 _23249 _23248 _23250) = (term153 _23247 _23248 _23249 _23250).
Proof. exact (TRANS (@lem1285564 _23247 _23248 _23249 _23250) (@lem1285569 _23247 _23248 _23249 _23250)). Qed.
Lemma lem1285586 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1285587 (_23247 : nadd) (_23248 : nadd) (_23249 : nadd) (_23250 : nadd) : (term154 _23247 _23249 _23248 _23250) = (term155 _23247 _23248 _23249 _23250).
Proof. exact (MK_COMB (@lem1285586) (@lem1285585 _23247 _23248 _23249 _23250)). Qed.
Lemma lem1285603 (_23247 : nadd) (_23248 : nadd) (_23249 : nadd) (_23250 : nadd) : (term153 _23247 _23248 _23249 _23250) = (term153 _23247 _23248 _23249 _23250).
Proof. exact (eq_refl (term153 _23247 _23248 _23249 _23250)). Qed.
Lemma lem1285604 (_23247 : nadd) (_23248 : nadd) (_23249 : nadd) (_23250 : nadd) : ((term140 _23247 _23249 _23248 _23250) = (term153 _23247 _23248 _23249 _23250)) = ((term153 _23247 _23248 _23249 _23250) = (term153 _23247 _23248 _23249 _23250)).
Proof. exact (MK_COMB (@lem1285587 _23247 _23248 _23249 _23250) (@lem1285603 _23247 _23248 _23249 _23250)). Qed.
Lemma lem1285606 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1285607 (x : Prop) : (x = x) = True.
Proof. exact (@lem1285606 Prop x). Qed.
Lemma lem1285608 (_23247 : nadd) (_23248 : nadd) (_23249 : nadd) (_23250 : nadd) : ((term153 _23247 _23248 _23249 _23250) = (term153 _23247 _23248 _23249 _23250)) = True.
Proof. exact (@lem1285607 (term153 _23247 _23248 _23249 _23250)). Qed.
Lemma lem1285609 (_23247 : nadd) (_23248 : nadd) (_23249 : nadd) (_23250 : nadd) : ((term140 _23247 _23249 _23248 _23250) = (term153 _23247 _23248 _23249 _23250)) = True.
Proof. exact (TRANS (@lem1285604 _23247 _23248 _23249 _23250) (@lem1285608 _23247 _23248 _23249 _23250)). Qed.
Lemma lem1285610 (_23247 : nadd) (_23248 : nadd) (_23249 : nadd) (_23250 : nadd) : True = ((term140 _23247 _23249 _23248 _23250) = (term153 _23247 _23248 _23249 _23250)).
Proof. exact (SYM (@lem1285609 _23247 _23248 _23249 _23250)). Qed.
Lemma lem1285611 (_23247 : nadd) (_23248 : nadd) (_23249 : nadd) (_23250 : nadd) : (term140 _23247 _23249 _23248 _23250) = (term153 _23247 _23248 _23249 _23250).
Proof. exact (EQ_MP (@lem1285610 _23247 _23248 _23249 _23250) (@lem0)). Qed.
Lemma lem1285612 (_23247 : nadd) (_23248 : nadd) (_23249 : nadd) (_23250 : nadd) (h1 : term54) : term153 _23247 _23248 _23249 _23250.
Proof. exact (EQ_MP (@lem1285611 _23247 _23248 _23249 _23250) (@lem1285490 _23247 _23249 _23248 _23250 h1)). Qed.
Lemma lem1285614 (b : Prop) (a : Prop) : (a \/ b) = (term156 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1285615 (_23247 : nadd) (_23249 : nadd) (_23248 : nadd) (_23250 : nadd) : (term153 _23247 _23248 _23249 _23250) = (term157 _23247 _23249 _23248 _23250).
Proof. exact (@lem1285614 (term111 _23247 _23248 _23249 _23250) (term112 _23247 _23249 _23248 _23250)). Qed.
Lemma lem1285617 (a : Prop) (b : Prop) : (term158 a b) = (term159 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1285618 (_23247 : nadd) (_23248 : nadd) (_23249 : nadd) (_23250 : nadd) : (term160 _23247 _23248 _23249 _23250) = (term161 _23247 _23248 _23249 _23250).
Proof. exact (@lem1285617 (term139 _23247 _23248) (term139 _23249 _23250)). Qed.
Lemma lem1285620 (a : Prop) : (term162 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1285621 (_23247 : nadd) (_23248 : nadd) : (term163 _23247 _23248) = (nadd_eq _23247 _23248).
Proof. exact (@lem1285620 (nadd_eq _23247 _23248)). Qed.
Lemma lem1285622 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1285623 (_23247 : nadd) (_23248 : nadd) : (term164 _23247 _23248) = (term165 _23247 _23248).
Proof. exact (MK_COMB (@lem1285622) (@lem1285621 _23247 _23248)). Qed.
Lemma lem1285625 (a : Prop) : (term162 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1285626 (_23249 : nadd) (_23250 : nadd) : (term163 _23249 _23250) = (nadd_eq _23249 _23250).
Proof. exact (@lem1285625 (nadd_eq _23249 _23250)). Qed.
Lemma lem1285627 (_23247 : nadd) (_23248 : nadd) (_23249 : nadd) (_23250 : nadd) : (term161 _23247 _23248 _23249 _23250) = (term117 _23247 _23248 _23249 _23250).
Proof. exact (MK_COMB (@lem1285623 _23247 _23248) (@lem1285626 _23249 _23250)). Qed.
Lemma lem1285628 (_23247 : nadd) (_23248 : nadd) (_23249 : nadd) (_23250 : nadd) : (term160 _23247 _23248 _23249 _23250) = (term117 _23247 _23248 _23249 _23250).
Proof. exact (TRANS (@lem1285618 _23247 _23248 _23249 _23250) (@lem1285627 _23247 _23248 _23249 _23250)). Qed.
Lemma lem1285629 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1285630 (_23247 : nadd) (_23248 : nadd) (_23249 : nadd) (_23250 : nadd) : (term166 _23247 _23248 _23249 _23250) = (term167 _23247 _23248 _23249 _23250).
Proof. exact (MK_COMB (@lem1285629) (@lem1285628 _23247 _23248 _23249 _23250)). Qed.
Lemma lem1285631 (_23247 : nadd) (_23249 : nadd) (_23248 : nadd) (_23250 : nadd) : (term112 _23247 _23249 _23248 _23250) = (term112 _23247 _23249 _23248 _23250).
Proof. exact (eq_refl (term112 _23247 _23249 _23248 _23250)). Qed.
Lemma lem1285632 (_23247 : nadd) (_23249 : nadd) (_23248 : nadd) (_23250 : nadd) : (term157 _23247 _23249 _23248 _23250) = (term46 _23247 _23249 _23248 _23250).
Proof. exact (MK_COMB (@lem1285630 _23247 _23248 _23249 _23250) (@lem1285631 _23247 _23249 _23248 _23250)). Qed.
Lemma lem1285633 (_23247 : nadd) (_23249 : nadd) (_23248 : nadd) (_23250 : nadd) : (term153 _23247 _23248 _23249 _23250) = (term46 _23247 _23249 _23248 _23250).
Proof. exact (TRANS (@lem1285615 _23247 _23249 _23248 _23250) (@lem1285632 _23247 _23249 _23248 _23250)). Qed.
Lemma lem1285635 (x : nadd) (y : nadd) (z : nadd) (h1 : term45) : term168 x y z.
Proof. exact (conj (@lem1285532 x z h1) (@lem1285540 y z h1)). Qed.
Lemma lem1285637 (_23247 : nadd) (_23249 : nadd) (_23248 : nadd) (_23250 : nadd) (h1 : term54) : term46 _23247 _23249 _23248 _23250.
Proof. exact (EQ_MP (@lem1285633 _23247 _23249 _23248 _23250) (@lem1285612 _23247 _23248 _23249 _23250 h1)). Qed.
Lemma lem1285638 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) : term169 x y z.
Proof. exact (@lem1285637 (nadd_mul z x) (nadd_mul z y) (nadd_mul x z) (nadd_mul y z) h1). Qed.
Lemma lem1285641 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term45) : term170 x y z.
Proof. exact (@lem1285638 x y z h1 (@lem1285635 x y z h2)). Qed.
Lemma lem1285642 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term45) : term171 x y z.
Proof. exact (fun h0 : term172 x y z => @lem1285641 x y z h1 h2). Qed.
Lemma lem1285644 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1285645 (x : nadd) (y : nadd) (z : nadd) : (term171 x y z) = (term170 x y z).
Proof. exact (@lem1285644 (term170 x y z)). Qed.
Lemma lem1285646 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term45) : term170 x y z.
Proof. exact (EQ_MP (@lem1285645 x y z) (@lem1285642 x y z h1 h2)). Qed.
Lemma lem1285662 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1285663 (_23244 : nadd) (_23245 : nadd) (_23246 : nadd) : (term173 _23245 _23244 _23246) = (term174 _23244 _23245 _23246).
Proof. exact (@lem1285662 (nadd_eq _23244 _23246) (term139 _23245 _23246)). Qed.
Lemma lem1285669 (_23244 : nadd) (_23245 : nadd) : (term151 _23244 _23245) = (term151 _23244 _23245).
Proof. exact (eq_refl (term151 _23244 _23245)). Qed.
Lemma lem1285670 (_23244 : nadd) (_23245 : nadd) (_23246 : nadd) : (term138 _23245 _23244 _23246) = (term175 _23244 _23245 _23246).
Proof. exact (MK_COMB (@lem1285669 _23244 _23245) (@lem1285663 _23244 _23245 _23246)). Qed.
Lemma lem1285674 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1285675 (_23244 : nadd) (_23245 : nadd) (_23246 : nadd) : (term175 _23244 _23245 _23246) = (term176 _23244 _23245 _23246).
Proof. exact (@lem1285674 (nadd_eq _23244 _23246) (term139 _23244 _23245) (term139 _23245 _23246)). Qed.
Lemma lem1285691 (_23244 : nadd) (_23245 : nadd) (_23246 : nadd) : (term138 _23245 _23244 _23246) = (term176 _23244 _23245 _23246).
Proof. exact (TRANS (@lem1285670 _23244 _23245 _23246) (@lem1285675 _23244 _23245 _23246)). Qed.
Lemma lem1285692 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1285693 (_23244 : nadd) (_23245 : nadd) (_23246 : nadd) : (term177 _23245 _23244 _23246) = (term178 _23244 _23245 _23246).
Proof. exact (MK_COMB (@lem1285692) (@lem1285691 _23244 _23245 _23246)). Qed.
Lemma lem1285709 (_23244 : nadd) (_23245 : nadd) (_23246 : nadd) : (term176 _23244 _23245 _23246) = (term176 _23244 _23245 _23246).
Proof. exact (eq_refl (term176 _23244 _23245 _23246)). Qed.
Lemma lem1285710 (_23244 : nadd) (_23245 : nadd) (_23246 : nadd) : ((term138 _23245 _23244 _23246) = (term176 _23244 _23245 _23246)) = ((term176 _23244 _23245 _23246) = (term176 _23244 _23245 _23246)).
Proof. exact (MK_COMB (@lem1285693 _23244 _23245 _23246) (@lem1285709 _23244 _23245 _23246)). Qed.
Lemma lem1285712 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1285713 (x : Prop) : (x = x) = True.
Proof. exact (@lem1285712 Prop x). Qed.
Lemma lem1285714 (_23244 : nadd) (_23245 : nadd) (_23246 : nadd) : ((term176 _23244 _23245 _23246) = (term176 _23244 _23245 _23246)) = True.
Proof. exact (@lem1285713 (term176 _23244 _23245 _23246)). Qed.
Lemma lem1285715 (_23244 : nadd) (_23245 : nadd) (_23246 : nadd) : ((term138 _23245 _23244 _23246) = (term176 _23244 _23245 _23246)) = True.
Proof. exact (TRANS (@lem1285710 _23244 _23245 _23246) (@lem1285714 _23244 _23245 _23246)). Qed.
Lemma lem1285716 (_23244 : nadd) (_23245 : nadd) (_23246 : nadd) : True = ((term138 _23245 _23244 _23246) = (term176 _23244 _23245 _23246)).
Proof. exact (SYM (@lem1285715 _23244 _23245 _23246)). Qed.
Lemma lem1285717 (_23244 : nadd) (_23245 : nadd) (_23246 : nadd) : (term138 _23245 _23244 _23246) = (term176 _23244 _23245 _23246).
Proof. exact (EQ_MP (@lem1285716 _23244 _23245 _23246) (@lem0)). Qed.
Lemma lem1285718 (_23244 : nadd) (_23245 : nadd) (_23246 : nadd) (h1 : term61) : term176 _23244 _23245 _23246.
Proof. exact (EQ_MP (@lem1285717 _23244 _23245 _23246) (@lem1285478 _23245 _23244 _23246 h1)). Qed.
Lemma lem1285720 (b : Prop) (a : Prop) : (a \/ b) = (term156 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1285721 (_23245 : nadd) (_23244 : nadd) (_23246 : nadd) : (term176 _23244 _23245 _23246) = (term179 _23245 _23244 _23246).
Proof. exact (@lem1285720 (term98 _23244 _23245 _23246) (nadd_eq _23244 _23246)). Qed.
Lemma lem1285723 (a : Prop) (b : Prop) : (term158 a b) = (term159 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1285724 (_23244 : nadd) (_23245 : nadd) (_23246 : nadd) : (term180 _23244 _23245 _23246) = (term181 _23244 _23245 _23246).
Proof. exact (@lem1285723 (term139 _23244 _23245) (term139 _23245 _23246)). Qed.
Lemma lem1285726 (a : Prop) : (term162 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1285727 (_23244 : nadd) (_23245 : nadd) : (term163 _23244 _23245) = (nadd_eq _23244 _23245).
Proof. exact (@lem1285726 (nadd_eq _23244 _23245)). Qed.
Lemma lem1285728 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1285729 (_23244 : nadd) (_23245 : nadd) : (term164 _23244 _23245) = (term165 _23244 _23245).
Proof. exact (MK_COMB (@lem1285728) (@lem1285727 _23244 _23245)). Qed.
Lemma lem1285731 (a : Prop) : (term162 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1285732 (_23245 : nadd) (_23246 : nadd) : (term163 _23245 _23246) = (nadd_eq _23245 _23246).
Proof. exact (@lem1285731 (nadd_eq _23245 _23246)). Qed.
Lemma lem1285733 (_23244 : nadd) (_23245 : nadd) (_23246 : nadd) : (term181 _23244 _23245 _23246) = (term103 _23244 _23245 _23246).
Proof. exact (MK_COMB (@lem1285729 _23244 _23245) (@lem1285732 _23245 _23246)). Qed.
Lemma lem1285734 (_23244 : nadd) (_23245 : nadd) (_23246 : nadd) : (term180 _23244 _23245 _23246) = (term103 _23244 _23245 _23246).
Proof. exact (TRANS (@lem1285724 _23244 _23245 _23246) (@lem1285733 _23244 _23245 _23246)). Qed.
Lemma lem1285735 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1285736 (_23244 : nadd) (_23245 : nadd) (_23246 : nadd) : (term182 _23244 _23245 _23246) = (term183 _23244 _23245 _23246).
Proof. exact (MK_COMB (@lem1285735) (@lem1285734 _23244 _23245 _23246)). Qed.
Lemma lem1285737 (_23244 : nadd) (_23246 : nadd) : (nadd_eq _23244 _23246) = (nadd_eq _23244 _23246).
Proof. exact (eq_refl (nadd_eq _23244 _23246)). Qed.
Lemma lem1285738 (_23245 : nadd) (_23244 : nadd) (_23246 : nadd) : (term179 _23245 _23244 _23246) = (term55 _23245 _23244 _23246).
Proof. exact (MK_COMB (@lem1285736 _23244 _23245 _23246) (@lem1285737 _23244 _23246)). Qed.
Lemma lem1285739 (_23245 : nadd) (_23244 : nadd) (_23246 : nadd) : (term176 _23244 _23245 _23246) = (term55 _23245 _23244 _23246).
Proof. exact (TRANS (@lem1285721 _23245 _23244 _23246) (@lem1285738 _23245 _23244 _23246)). Qed.
Lemma lem1285741 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term17) (h3 : term45) : term184 x y z.
Proof. exact (conj (@lem1285524 x z y h2) (@lem1285646 x y z h1 h3)). Qed.
Lemma lem1285743 (_23245 : nadd) (_23244 : nadd) (_23246 : nadd) (h1 : term61) : term55 _23245 _23244 _23246.
Proof. exact (EQ_MP (@lem1285739 _23245 _23244 _23246) (@lem1285718 _23244 _23245 _23246 h1)). Qed.
Lemma lem1285744 (x : nadd) (y : nadd) (z : nadd) (h1 : term61) : term185 x y z.
Proof. exact (@lem1285743 (term186 x z y) (term187 z x y) (term188 x y z) h1). Qed.
Lemma lem1285747 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) : term189 x y z.
Proof. exact (@lem1285744 x y z h2 (@lem1285741 x y z h1 h3 h4)). Qed.
Lemma lem1285748 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) : term190 x y z.
Proof. exact (fun h0 : term191 x y z => @lem1285747 x y z h1 h2 h3 h4). Qed.
Lemma lem1285750 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1285751 (x : nadd) (y : nadd) (z : nadd) : (term190 x y z) = (term189 x y z).
Proof. exact (@lem1285750 (term189 x y z)). Qed.
Lemma lem1285752 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) : term189 x y z.
Proof. exact (EQ_MP (@lem1285751 x y z) (@lem1285748 x y z h1 h2 h3 h4)). Qed.
Lemma lem1285753 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) : term192 x y z.
Proof. exact (conj (@lem1285516 z x y h4) (@lem1285752 x y z h1 h2 h3 h4)). Qed.
Lemma lem1285755 (_23245 : nadd) (_23244 : nadd) (_23246 : nadd) (h1 : term61) : term55 _23245 _23244 _23246.
Proof. exact (EQ_MP (@lem1285739 _23245 _23244 _23246) (@lem1285718 _23244 _23245 _23246 h1)). Qed.
Lemma lem1285756 (x : nadd) (y : nadd) (z : nadd) (h1 : term61) : term193 x y z.
Proof. exact (@lem1285755 (term187 z x y) (term194 x y z) (term188 x y z) h1). Qed.
Lemma lem1285759 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) : term68 x y z.
Proof. exact (@lem1285756 x y z h2 (@lem1285753 x y z h1 h2 h3 h4)). Qed.
Lemma lem1285760 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) : term195 x y z.
Proof. exact (fun h0 : term80 x y z => @lem1285759 x y z h1 h2 h3 h4). Qed.
Lemma lem1285762 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1285763 (x : nadd) (y : nadd) (z : nadd) : (term195 x y z) = (term68 x y z).
Proof. exact (@lem1285762 (term68 x y z)). Qed.
Lemma lem1285764 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) : term68 x y z.
Proof. exact (EQ_MP (@lem1285763 x y z) (@lem1285760 x y z h1 h2 h3 h4)). Qed.
Lemma lem1285767 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1285769 (x : nadd) (y : nadd) (z : nadd) : (term80 x y z) = (term196 x y z).
Proof. exact (@lem1285767 (term68 x y z)). Qed.
Lemma lem1285772 (x : nadd) (y : nadd) (z : nadd) (h1 : term80 x y z) : term196 x y z.
Proof. exact (EQ_MP (@lem1285769 x y z) (@lem1285496 x y z h1)). Qed.
Lemma lem1285775 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) (h5 : term80 x y z) : False.
Proof. exact (@lem1285772 x y z h5 (@lem1285764 x y z h1 h2 h3 h4)). Qed.
Lemma lem1285776 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) (h5 : term80 x y z) : term197.
Proof. exact (fun h0 : ~ False => @lem1285775 x y z h1 h2 h3 h4 h5). Qed.
Lemma lem1285778 (p : Prop) : (term144 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1285779 : term197 = False.
Proof. exact (@lem1285778 False). Qed.
Lemma lem1285780 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) (h5 : term80 x y z) : False.
Proof. exact (EQ_MP (@lem1285779) (@lem1285776 x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem1285781 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) (h5 : term80 x y z) : (term80 x y z) = False.
Proof. exact (prop_ext (fun h6 : term80 x y z => @lem1285780 x y z h1 h2 h3 h4 h5) (fun h6 : False => @lem1285496 x y z h5)). Qed.
Lemma lem1285782 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) (h5 : term80 x y z) : False.
Proof. exact (EQ_MP (@lem1285781 x y z h1 h2 h3 h4 h5) (@lem1285496 x y z h5)). Qed.
Lemma lem1285783 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) (h5 : term80 x y z) : (term80 x y z) = False.
Proof. exact (prop_ext (fun h6 : term80 x y z => @lem1285782 x y z h1 h2 h3 h4 h5) (fun h6 : False => @lem1285381 x y z h5)). Qed.
Lemma lem1285784 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) (h5 : term80 x y z) : False.
Proof. exact (EQ_MP (@lem1285783 x y z h1 h2 h3 h4 h5) (@lem1285381 x y z h5)). Qed.
Lemma lem1285785 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) (h5 : term80 x y z) : (term80 x y z) = False.
Proof. exact (prop_ext (fun h6 : term80 x y z => @lem1285784 x y z h1 h2 h3 h4 h5) (fun h6 : False => @lem1285381 x y z h5)). Qed.
Lemma lem1285786 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) (h5 : term80 x y z) : False.
Proof. exact (EQ_MP (@lem1285785 x y z h1 h2 h3 h4 h5) (@lem1285381 x y z h5)). Qed.
Lemma lem1285787 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) (h5 : term80 x y z) : term17 = False.
Proof. exact (prop_ext (fun h6 : term17 => @lem1285786 x y z h1 h2 h3 h4 h5) (fun h6 : False => @lem1285377 h3)). Qed.
Lemma lem1285788 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) (h5 : term80 x y z) : False.
Proof. exact (EQ_MP (@lem1285787 x y z h1 h2 h3 h4 h5) (@lem1285377 h3)). Qed.
Lemma lem1285789 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) (h5 : term80 x y z) : term45 = False.
Proof. exact (prop_ext (fun h6 : term45 => @lem1285788 x y z h1 h2 h3 h4 h5) (fun h6 : False => @lem1285364 h4)). Qed.
Lemma lem1285790 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) (h5 : term80 x y z) : False.
Proof. exact (EQ_MP (@lem1285789 x y z h1 h2 h3 h4 h5) (@lem1285364 h4)). Qed.
Lemma lem1285791 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) (h5 : term80 x y z) : (term80 x y z) = False.
Proof. exact (prop_ext (fun h6 : term80 x y z => @lem1285790 x y z h1 h2 h3 h4 h5) (fun h6 : False => @lem1285292 x y z h5)). Qed.
Lemma lem1285792 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) (h5 : term80 x y z) : False.
Proof. exact (EQ_MP (@lem1285791 x y z h1 h2 h3 h4 h5) (@lem1285292 x y z h5)). Qed.
Lemma lem1285793 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) (h5 : term80 x y z) : term17 = False.
Proof. exact (prop_ext (fun h6 : term17 => @lem1285792 x y z h1 h2 h3 h4 h5) (fun h6 : False => @lem1285264 h3)). Qed.
Lemma lem1285794 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) (h5 : term80 x y z) : False.
Proof. exact (EQ_MP (@lem1285793 x y z h1 h2 h3 h4 h5) (@lem1285264 h3)). Qed.
Lemma lem1285795 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) (h5 : term80 x y z) : term45 = False.
Proof. exact (prop_ext (fun h6 : term45 => @lem1285794 x y z h1 h2 h3 h4 h5) (fun h6 : False => @lem1285229 h4)). Qed.
Lemma lem1285796 (x : nadd) (y : nadd) (z : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) (h5 : term80 x y z) : False.
Proof. exact (EQ_MP (@lem1285795 x y z h1 h2 h3 h4 h5) (@lem1285229 h4)). Qed.
Lemma lem1285797 (x : nadd) (y : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) (h5 : term83 x y) : False.
Proof. exact (ex_elim (@lem1285072 x y h5) (fun z : nadd => fun h0 : term82 x y z => @lem1285796 x y z h1 h2 h3 h4 h0)). Qed.
Lemma lem1285798 (x : nadd) (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) (h5 : term90 x) : False.
Proof. exact (ex_elim (@lem1285071 x h5) (fun y : nadd => fun h0 : term89 x y => @lem1285797 x y h1 h2 h3 h4 h0)). Qed.
Lemma lem1285799 (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) (h5 : term10) : False.
Proof. exact (ex_elim (@lem1284550 h5) (fun x : nadd => fun h0 : term95 x => @lem1285798 x h1 h2 h3 h4 h0)). Qed.
Lemma lem1285800 (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) (h5 : term10) : term17 = False.
Proof. exact (prop_ext (fun h6 : term17 => @lem1285799 h1 h2 h3 h4 h5) (fun h6 : False => @lem1285070 h3)). Qed.
Lemma lem1285801 (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) (h5 : term10) : False.
Proof. exact (EQ_MP (@lem1285800 h1 h2 h3 h4 h5) (@lem1285070 h3)). Qed.
Lemma lem1285802 (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) (h5 : term10) : term45 = False.
Proof. exact (prop_ext (fun h6 : term45 => @lem1285801 h1 h2 h3 h4 h5) (fun h6 : False => @lem1285043 h4)). Qed.
Lemma lem1285803 (h1 : term54) (h2 : term61) (h3 : term17) (h4 : term45) (h5 : term10) : False.
Proof. exact (EQ_MP (@lem1285802 h1 h2 h3 h4 h5) (@lem1285043 h4)). Qed.
Lemma lem1285804 (h1 : term54) (h2 : term61) (h3 : term45) (h4 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem1285803 h1 h2 h0 h3 h4). Qed.
Lemma lem1285805 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem1285806 (h1 : term54) (h2 : term61) (h3 : term45) (h4 : term10) : term16.
Proof. exact (EQ_MP (@lem1285805) (@lem1285804 h1 h2 h3 h4)). Qed.
Lemma lem1285807 (h1 : term54) (h2 : term61) (h3 : term10) : term20.
Proof. exact (fun h0 : term45 => @lem1285806 h1 h2 h0 h3). Qed.
Lemma lem1285808 (h1 : term61) (h2 : term10) : term23.
Proof. exact (fun h0 : term54 => @lem1285807 h0 h1 h2). Qed.
Lemma lem1285809 (h1 : term10) : term26.
Proof. exact (fun h0 : term61 => @lem1285808 h0 h1). Qed.
Lemma lem1285810 (h1 : term10) : term29.
Proof. exact (fun h0 : term63 => @lem1285809 h1). Qed.
Lemma lem1285811 (h1 : term10) : term32.
Proof. exact (fun h0 : term67 => @lem1285810 h1). Qed.
Lemma lem1285812 : term34.
Proof. exact (fun h0 : term10 => @lem1285811 h0). Qed.
Lemma lem1285813 : term11.
Proof. exact (EQ_MP (@lem1284495) (@lem1285812)). Qed.
Lemma lem1285815 : term11.
Proof. exact (@lem1284137 (@lem1285813)). Qed.
Lemma lem1285816 (h1 : term10) : term31.
Proof. exact (@lem1285815 (@lem1284122 h1)). Qed.
Lemma lem1285817 (h1 : term10) : term28.
Proof. exact (@lem1285816 h1 (@lem1268060)). Qed.
Lemma lem1285818 (h1 : term10) : term25.
Proof. exact (@lem1285817 h1 (@lem1267990)). Qed.
Lemma lem1285819 (h1 : term10) : term22.
Proof. exact (@lem1285818 h1 (@lem1268295)). Qed.
Lemma lem1285820 (h1 : term10) : term19.
Proof. exact (@lem1285819 h1 (@lem1274424)). Qed.
Lemma lem1285821 (h1 : term10) : term15.
Proof. exact (@lem1285820 h1 (@lem1278399)). Qed.
Lemma lem1285822 (h1 : term10) : False.
Proof. exact (@lem1285821 h1 (@lem1278840)). Qed.
Lemma lem1285823 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem1285822 h1) (fun h2 : False => @lem1284122 h1)). Qed.
Lemma lem1285824 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem1285823 h1) (@lem1284122 h1)). Qed.
Lemma lem1285825 : term9.
Proof. exact (fun h0 : term10 => @lem1285824 h0). Qed.
Lemma lem1285826 : term8.
Proof. exact (EQ_MP (@lem1284121) (@lem1285825)). Qed.
