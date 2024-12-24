Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_MUL_RZERO_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_EQ_ADD_RCANCEL_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1338512_spec.
Require Import thm1339188_spec.
Require Import thm16474_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
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
Lemma lem1355159 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1355160 : term1 = term2.
Proof. exact (@lem1355159 term1). Qed.
Lemma lem1355161 : term2 = term1.
Proof. exact (SYM (@lem1355160)). Qed.
Lemma lem1355162 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1355165 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1355166 : term5.
Proof. exact (fun h0 : term4 => @lem1355165 h0). Qed.
Lemma lem1355167 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1355168 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1355169 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1355167 h2 (@lem1355168 h1)). Qed.
Lemma lem1355170 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1355169 h1 h0). Qed.
Lemma lem1355171 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1355172 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1355170 h1 (@lem1355171 h2)). Qed.
Lemma lem1355173 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1355172 h0 h1). Qed.
Lemma lem1355174 : term7.
Proof. exact (fun h0 : term5 => @lem1355173 h0). Qed.
Lemma lem1355177 : term5.
Proof. exact (@lem1355174 (@lem1355166)). Qed.
Lemma lem1355205 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1355206 : term8 = term9.
Proof. exact (@lem1355205 term10). Qed.
Lemma lem1355219 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1355220 : term12 = term13.
Proof. exact (MK_COMB (@lem1355219) (@lem1355206)). Qed.
Lemma lem1355223 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1355224 : term15 = term16.
Proof. exact (MK_COMB (@lem1355223) (@lem1355220)). Qed.
Lemma lem1355227 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1355234 : term4 = term18.
Proof. exact (MK_COMB (@lem1355227) (@lem1355224)). Qed.
Lemma lem1355239 (z : real) (x : real) (y : real) : (((real_add x z) = (real_add y z)) = (x = y)) = (((real_add x z) = (real_add y z)) = (x = y)).
Proof. exact (eq_refl (((real_add x z) = (real_add y z)) = (x = y))). Qed.
Lemma lem1355240 (x : real) (y : real) : (term19 x y) = (term19 x y).
Proof. exact (fun_ext (fun z : real => @lem1355239 z x y)). Qed.
Lemma lem1355241 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355242 (x : real) (y : real) : (term20 x y) = (term20 x y).
Proof. exact (MK_COMB (@lem1355241) (@lem1355240 x y)). Qed.
Lemma lem1355243 (x : real) : (term21 x) = (term21 x).
Proof. exact (fun_ext (fun y : real => @lem1355242 x y)). Qed.
Lemma lem1355244 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355245 (x : real) : (term22 x) = (term22 x).
Proof. exact (MK_COMB (@lem1355244) (@lem1355243 x)). Qed.
Lemma lem1355246 : term23 = term23.
Proof. exact (fun_ext (fun x : real => @lem1355245 x)). Qed.
Lemma lem1355247 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355248 : term10 = term10.
Proof. exact (MK_COMB (@lem1355247) (@lem1355246)). Qed.
Lemma lem1355249 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1355250 : term9 = term9.
Proof. exact (MK_COMB (@lem1355249) (@lem1355248)). Qed.
Lemma lem1355251 (y : real) (x : real) (z : real) : ((term24 x y z) = (term25 y x z)) = ((term24 x y z) = (term25 y x z)).
Proof. exact (eq_refl ((term24 x y z) = (term25 y x z))). Qed.
Lemma lem1355252 (y : real) (x : real) : (term26 y x) = (term26 y x).
Proof. exact (fun_ext (fun z : real => @lem1355251 y x z)). Qed.
Lemma lem1355253 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355254 (y : real) (x : real) : (term27 y x) = (term27 y x).
Proof. exact (MK_COMB (@lem1355253) (@lem1355252 y x)). Qed.
Lemma lem1355255 (x : real) : (term28 x) = (term28 x).
Proof. exact (fun_ext (fun y : real => @lem1355254 y x)). Qed.
Lemma lem1355256 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355257 (x : real) : (term29 x) = (term29 x).
Proof. exact (MK_COMB (@lem1355256) (@lem1355255 x)). Qed.
Lemma lem1355258 : term30 = term30.
Proof. exact (fun_ext (fun x : real => @lem1355257 x)). Qed.
Lemma lem1355259 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355260 : term31 = term31.
Proof. exact (MK_COMB (@lem1355259) (@lem1355258)). Qed.
Lemma lem1355261 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1355262 : term11 = term11.
Proof. exact (MK_COMB (@lem1355261) (@lem1355260)). Qed.
Lemma lem1355263 : term13 = term13.
Proof. exact (MK_COMB (@lem1355262) (@lem1355250)). Qed.
Lemma lem1355264 (x : real) : ((term32 x) = x) = ((term32 x) = x).
Proof. exact (eq_refl ((term32 x) = x)). Qed.
Lemma lem1355265 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem1355264 x)). Qed.
Lemma lem1355266 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355267 : term34 = term34.
Proof. exact (MK_COMB (@lem1355266) (@lem1355265)). Qed.
Lemma lem1355268 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1355269 : term14 = term14.
Proof. exact (MK_COMB (@lem1355268) (@lem1355267)). Qed.
Lemma lem1355270 : term16 = term16.
Proof. exact (MK_COMB (@lem1355269) (@lem1355263)). Qed.
Lemma lem1355271 (x : real) : ((term35 x) = term36) = ((term35 x) = term36).
Proof. exact (eq_refl ((term35 x) = term36)). Qed.
Lemma lem1355272 : term37 = term37.
Proof. exact (fun_ext (fun x : real => @lem1355271 x)). Qed.
Lemma lem1355273 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355274 : term1 = term1.
Proof. exact (MK_COMB (@lem1355273) (@lem1355272)). Qed.
Lemma lem1355275 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1355276 : term3 = term3.
Proof. exact (MK_COMB (@lem1355275) (@lem1355274)). Qed.
Lemma lem1355277 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1355278 : term17 = term17.
Proof. exact (MK_COMB (@lem1355277) (@lem1355276)). Qed.
Lemma lem1355279 : term18 = term18.
Proof. exact (MK_COMB (@lem1355278) (@lem1355270)). Qed.
Lemma lem1355336 : term4 = term18.
Proof. exact (TRANS (@lem1355234) (@lem1355279)). Qed.
Lemma lem1355337 : term18 = term4.
Proof. exact (SYM (@lem1355336)). Qed.
Lemma lem1355338 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1355339 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem1355340 (h1 : term31) : term31.
Proof. exact (h1). Qed.
Lemma lem1355341 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1355343 (P : real -> Prop) : (term38 P) = (term39 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1355344 : term3 = term40.
Proof. exact (@lem1355343 term37). Qed.
Lemma lem1355345 (x : real) : (term41 x) = ((term35 x) = term36).
Proof. exact (eq_refl (term41 x)). Qed.
Lemma lem1355346 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1355348 (x : real) : (term42 x) = (term43 x).
Proof. exact (MK_COMB (@lem1355346) (@lem1355345 x)). Qed.
Lemma lem1355349 : term44 = term45.
Proof. exact (fun_ext (fun x : real => @lem1355348 x)). Qed.
Lemma lem1355350 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1355351 : term40 = term46.
Proof. exact (MK_COMB (@lem1355350) (@lem1355349)). Qed.
Lemma lem1355360 : term3 = term46.
Proof. exact (TRANS (@lem1355344) (@lem1355351)). Qed.
Lemma lem1355361 (h1 : term3) : term46.
Proof. exact (EQ_MP (@lem1355360) (@lem1355338 h1)). Qed.
Lemma lem1355362 (x : real) : ((term32 x) = x) = ((term32 x) = x).
Proof. exact (eq_refl ((term32 x) = x)). Qed.
Lemma lem1355363 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem1355362 x)). Qed.
Lemma lem1355364 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355373 : term34 = term34.
Proof. exact (MK_COMB (@lem1355364) (@lem1355363)). Qed.
Lemma lem1355374 (h1 : term34) : term34.
Proof. exact (EQ_MP (@lem1355373) (@lem1355339 h1)). Qed.
Lemma lem1355375 (y : real) (x : real) (z : real) : ((term24 x y z) = (term25 y x z)) = ((term24 x y z) = (term25 y x z)).
Proof. exact (eq_refl ((term24 x y z) = (term25 y x z))). Qed.
Lemma lem1355376 (y : real) (x : real) : (term26 y x) = (term26 y x).
Proof. exact (fun_ext (fun z : real => @lem1355375 y x z)). Qed.
Lemma lem1355377 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355378 (y : real) (x : real) : (term27 y x) = (term27 y x).
Proof. exact (MK_COMB (@lem1355377) (@lem1355376 y x)). Qed.
Lemma lem1355379 (x : real) : (term28 x) = (term28 x).
Proof. exact (fun_ext (fun y : real => @lem1355378 y x)). Qed.
Lemma lem1355380 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355381 (x : real) : (term29 x) = (term29 x).
Proof. exact (MK_COMB (@lem1355380) (@lem1355379 x)). Qed.
Lemma lem1355382 : term30 = term30.
Proof. exact (fun_ext (fun x : real => @lem1355381 x)). Qed.
Lemma lem1355383 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355400 : term31 = term31.
Proof. exact (MK_COMB (@lem1355383) (@lem1355382)). Qed.
Lemma lem1355401 (h1 : term31) : term31.
Proof. exact (EQ_MP (@lem1355400) (@lem1355340 h1)). Qed.
Lemma lem1355416 (z : real) (x : real) (y : real) : (((real_add x z) = (real_add y z)) = (x = y)) = (term47 z x y).
Proof. exact (@lem17784 ((real_add x z) = (real_add y z)) (x = y)). Qed.
Lemma lem1355417 (x : real) (y : real) : (term19 x y) = (term48 x y).
Proof. exact (fun_ext (fun z : real => @lem1355416 z x y)). Qed.
Lemma lem1355418 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355419 (x : real) (y : real) : (term20 x y) = (term49 x y).
Proof. exact (MK_COMB (@lem1355418) (@lem1355417 x y)). Qed.
Lemma lem1355420 (x : real) : (term21 x) = (term50 x).
Proof. exact (fun_ext (fun y : real => @lem1355419 x y)). Qed.
Lemma lem1355421 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355422 (x : real) : (term22 x) = (term51 x).
Proof. exact (MK_COMB (@lem1355421) (@lem1355420 x)). Qed.
Lemma lem1355423 : term23 = term52.
Proof. exact (fun_ext (fun x : real => @lem1355422 x)). Qed.
Lemma lem1355424 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355425 : term10 = term53.
Proof. exact (MK_COMB (@lem1355424) (@lem1355423)). Qed.
Lemma lem1355435 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term54 A P Q) = (term55 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1355436 (P : real -> Prop) (Q : real -> Prop) : (term56 P Q) = (term57 P Q).
Proof. exact (@lem1355435 real P Q). Qed.
Lemma lem1355437 (x : real) (y : real) : (term58 x y) = (term59 x y).
Proof. exact (@lem1355436 (term60 x y) (term61 x y)). Qed.
Lemma lem1355438 (z : real) (x : real) (y : real) : (term62 x y z) = (term63 z x y).
Proof. exact (eq_refl (term62 x y z)). Qed.
Lemma lem1355439 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1355440 (z : real) (x : real) (y : real) : (term64 x y z) = (term65 z x y).
Proof. exact (MK_COMB (@lem1355439) (@lem1355438 z x y)). Qed.
Lemma lem1355441 (z : real) (x : real) (y : real) : (term66 x y z) = (term67 z x y).
Proof. exact (eq_refl (term66 x y z)). Qed.
Lemma lem1355442 (z : real) (x : real) (y : real) : (term68 x y z) = (term47 z x y).
Proof. exact (MK_COMB (@lem1355440 z x y) (@lem1355441 z x y)). Qed.
Lemma lem1355443 (x : real) (y : real) : (term69 x y) = (term48 x y).
Proof. exact (fun_ext (fun z : real => @lem1355442 z x y)). Qed.
Lemma lem1355444 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355445 (x : real) (y : real) : (term58 x y) = (term49 x y).
Proof. exact (MK_COMB (@lem1355444) (@lem1355443 x y)). Qed.
Lemma lem1355446 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1355447 (x : real) (y : real) : (term70 x y) = (term71 x y).
Proof. exact (MK_COMB (@lem1355446) (@lem1355445 x y)). Qed.
Lemma lem1355448 (z : real) (x : real) (y : real) : (term62 x y z) = (term63 z x y).
Proof. exact (eq_refl (term62 x y z)). Qed.
Lemma lem1355449 (x : real) (y : real) : (term72 x y) = (term60 x y).
Proof. exact (fun_ext (fun z : real => @lem1355448 z x y)). Qed.
Lemma lem1355450 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355451 (x : real) (y : real) : (term73 x y) = (term74 x y).
Proof. exact (MK_COMB (@lem1355450) (@lem1355449 x y)). Qed.
Lemma lem1355452 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1355453 (x : real) (y : real) : (term75 x y) = (term76 x y).
Proof. exact (MK_COMB (@lem1355452) (@lem1355451 x y)). Qed.
Lemma lem1355454 (z : real) (x : real) (y : real) : (term66 x y z) = (term67 z x y).
Proof. exact (eq_refl (term66 x y z)). Qed.
Lemma lem1355455 (x : real) (y : real) : (term77 x y) = (term61 x y).
Proof. exact (fun_ext (fun z : real => @lem1355454 z x y)). Qed.
Lemma lem1355456 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355457 (x : real) (y : real) : (term78 x y) = (term79 x y).
Proof. exact (MK_COMB (@lem1355456) (@lem1355455 x y)). Qed.
Lemma lem1355458 (x : real) (y : real) : (term59 x y) = (term80 x y).
Proof. exact (MK_COMB (@lem1355453 x y) (@lem1355457 x y)). Qed.
Lemma lem1355459 (x : real) (y : real) : ((term58 x y) = (term59 x y)) = ((term49 x y) = (term80 x y)).
Proof. exact (MK_COMB (@lem1355447 x y) (@lem1355458 x y)). Qed.
Lemma lem1355460 (x : real) (y : real) : (term49 x y) = (term80 x y).
Proof. exact (EQ_MP (@lem1355459 x y) (@lem1355437 x y)). Qed.
Lemma lem1355482 {A : Type'} (P : A -> Prop) (Q : Prop) : (term81 A P Q) = (term82 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem1355483 (P : real -> Prop) (Q : Prop) : (term83 P Q) = (term84 P Q).
Proof. exact (@lem1355482 real P Q). Qed.
Lemma lem1355484 (x : real) (y : real) : (term85 x y) = (term86 x y).
Proof. exact (@lem1355483 (term87 x y) (term88 x y)). Qed.
Lemma lem1355485 (x : real) (y : real) (z : real) : (term89 x y z) = ((real_add x z) = (real_add y z)).
Proof. exact (eq_refl (term89 x y z)). Qed.
Lemma lem1355486 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1355487 (x : real) (y : real) (z : real) : (term90 x y z) = (term91 x y z).
Proof. exact (MK_COMB (@lem1355486) (@lem1355485 x y z)). Qed.
Lemma lem1355488 (x : real) (y : real) : (term88 x y) = (term88 x y).
Proof. exact (eq_refl (term88 x y)). Qed.
Lemma lem1355489 (z : real) (x : real) (y : real) : (term92 z x y) = (term63 z x y).
Proof. exact (MK_COMB (@lem1355487 x y z) (@lem1355488 x y)). Qed.
Lemma lem1355490 (x : real) (y : real) : (term93 x y) = (term60 x y).
Proof. exact (fun_ext (fun z : real => @lem1355489 z x y)). Qed.
Lemma lem1355491 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355492 (x : real) (y : real) : (term85 x y) = (term74 x y).
Proof. exact (MK_COMB (@lem1355491) (@lem1355490 x y)). Qed.
Lemma lem1355493 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1355494 (x : real) (y : real) : (term94 x y) = (term95 x y).
Proof. exact (MK_COMB (@lem1355493) (@lem1355492 x y)). Qed.
Lemma lem1355495 (x : real) (y : real) (z : real) : (term89 x y z) = ((real_add x z) = (real_add y z)).
Proof. exact (eq_refl (term89 x y z)). Qed.
Lemma lem1355496 (x : real) (y : real) : (term96 x y) = (term87 x y).
Proof. exact (fun_ext (fun z : real => @lem1355495 x y z)). Qed.
Lemma lem1355497 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355498 (x : real) (y : real) : (term97 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem1355497) (@lem1355496 x y)). Qed.
Lemma lem1355499 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1355500 (x : real) (y : real) : (term99 x y) = (term100 x y).
Proof. exact (MK_COMB (@lem1355499) (@lem1355498 x y)). Qed.
Lemma lem1355501 (x : real) (y : real) : (term88 x y) = (term88 x y).
Proof. exact (eq_refl (term88 x y)). Qed.
Lemma lem1355502 (x : real) (y : real) : (term86 x y) = (term101 x y).
Proof. exact (MK_COMB (@lem1355500 x y) (@lem1355501 x y)). Qed.
Lemma lem1355503 (x : real) (y : real) : ((term85 x y) = (term86 x y)) = ((term74 x y) = (term101 x y)).
Proof. exact (MK_COMB (@lem1355494 x y) (@lem1355502 x y)). Qed.
Lemma lem1355504 (x : real) (y : real) : (term74 x y) = (term101 x y).
Proof. exact (EQ_MP (@lem1355503 x y) (@lem1355484 x y)). Qed.
Lemma lem1355509 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1355510 (x : real) (y : real) : (term76 x y) = (term102 x y).
Proof. exact (MK_COMB (@lem1355509) (@lem1355504 x y)). Qed.
Lemma lem1355532 {A : Type'} (P : A -> Prop) (Q : Prop) : (term81 A P Q) = (term82 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem1355533 (P : real -> Prop) (Q : Prop) : (term83 P Q) = (term84 P Q).
Proof. exact (@lem1355532 real P Q). Qed.
Lemma lem1355534 (x : real) (y : real) : (term103 x y) = (term104 x y).
Proof. exact (@lem1355533 (term105 x y) (x = y)). Qed.
Lemma lem1355535 (x : real) (y : real) (z : real) : (term106 x y z) = (term107 x y z).
Proof. exact (eq_refl (term106 x y z)). Qed.
Lemma lem1355536 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1355537 (x : real) (y : real) (z : real) : (term108 x y z) = (term109 x y z).
Proof. exact (MK_COMB (@lem1355536) (@lem1355535 x y z)). Qed.
Lemma lem1355538 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1355539 (z : real) (x : real) (y : real) : (term110 z x y) = (term67 z x y).
Proof. exact (MK_COMB (@lem1355537 x y z) (@lem1355538 x y)). Qed.
Lemma lem1355540 (x : real) (y : real) : (term111 x y) = (term61 x y).
Proof. exact (fun_ext (fun z : real => @lem1355539 z x y)). Qed.
Lemma lem1355541 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355542 (x : real) (y : real) : (term103 x y) = (term79 x y).
Proof. exact (MK_COMB (@lem1355541) (@lem1355540 x y)). Qed.
Lemma lem1355543 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1355544 (x : real) (y : real) : (term112 x y) = (term113 x y).
Proof. exact (MK_COMB (@lem1355543) (@lem1355542 x y)). Qed.
Lemma lem1355545 (x : real) (y : real) (z : real) : (term106 x y z) = (term107 x y z).
Proof. exact (eq_refl (term106 x y z)). Qed.
Lemma lem1355546 (x : real) (y : real) : (term114 x y) = (term105 x y).
Proof. exact (fun_ext (fun z : real => @lem1355545 x y z)). Qed.
Lemma lem1355547 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355548 (x : real) (y : real) : (term115 x y) = (term116 x y).
Proof. exact (MK_COMB (@lem1355547) (@lem1355546 x y)). Qed.
Lemma lem1355549 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1355550 (x : real) (y : real) : (term117 x y) = (term118 x y).
Proof. exact (MK_COMB (@lem1355549) (@lem1355548 x y)). Qed.
Lemma lem1355551 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1355552 (x : real) (y : real) : (term104 x y) = (term119 x y).
Proof. exact (MK_COMB (@lem1355550 x y) (@lem1355551 x y)). Qed.
Lemma lem1355553 (x : real) (y : real) : ((term103 x y) = (term104 x y)) = ((term79 x y) = (term119 x y)).
Proof. exact (MK_COMB (@lem1355544 x y) (@lem1355552 x y)). Qed.
Lemma lem1355554 (x : real) (y : real) : (term79 x y) = (term119 x y).
Proof. exact (EQ_MP (@lem1355553 x y) (@lem1355534 x y)). Qed.
Lemma lem1355559 (x : real) (y : real) : (term80 x y) = (term120 x y).
Proof. exact (MK_COMB (@lem1355510 x y) (@lem1355554 x y)). Qed.
Lemma lem1355560 (x : real) (y : real) : (term49 x y) = (term120 x y).
Proof. exact (TRANS (@lem1355460 x y) (@lem1355559 x y)). Qed.
Lemma lem1355561 (x : real) : (term50 x) = (term121 x).
Proof. exact (fun_ext (fun y : real => @lem1355560 x y)). Qed.
Lemma lem1355562 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355563 (x : real) : (term51 x) = (term122 x).
Proof. exact (MK_COMB (@lem1355562) (@lem1355561 x)). Qed.
Lemma lem1355565 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term54 A P Q) = (term55 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1355566 (P : real -> Prop) (Q : real -> Prop) : (term56 P Q) = (term57 P Q).
Proof. exact (@lem1355565 real P Q). Qed.
Lemma lem1355567 (x : real) : (term123 x) = (term124 x).
Proof. exact (@lem1355566 (term125 x) (term126 x)). Qed.
Lemma lem1355568 (x : real) (y : real) : (term127 x y) = (term101 x y).
Proof. exact (eq_refl (term127 x y)). Qed.
Lemma lem1355569 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1355570 (x : real) (y : real) : (term128 x y) = (term102 x y).
Proof. exact (MK_COMB (@lem1355569) (@lem1355568 x y)). Qed.
Lemma lem1355571 (x : real) (y : real) : (term129 x y) = (term119 x y).
Proof. exact (eq_refl (term129 x y)). Qed.
Lemma lem1355572 (x : real) (y : real) : (term130 x y) = (term120 x y).
Proof. exact (MK_COMB (@lem1355570 x y) (@lem1355571 x y)). Qed.
Lemma lem1355573 (x : real) : (term131 x) = (term121 x).
Proof. exact (fun_ext (fun y : real => @lem1355572 x y)). Qed.
Lemma lem1355574 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355575 (x : real) : (term123 x) = (term122 x).
Proof. exact (MK_COMB (@lem1355574) (@lem1355573 x)). Qed.
Lemma lem1355576 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1355577 (x : real) : (term132 x) = (term133 x).
Proof. exact (MK_COMB (@lem1355576) (@lem1355575 x)). Qed.
Lemma lem1355578 (x : real) (y : real) : (term127 x y) = (term101 x y).
Proof. exact (eq_refl (term127 x y)). Qed.
Lemma lem1355579 (x : real) : (term134 x) = (term125 x).
Proof. exact (fun_ext (fun y : real => @lem1355578 x y)). Qed.
Lemma lem1355580 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355581 (x : real) : (term135 x) = (term136 x).
Proof. exact (MK_COMB (@lem1355580) (@lem1355579 x)). Qed.
Lemma lem1355582 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1355583 (x : real) : (term137 x) = (term138 x).
Proof. exact (MK_COMB (@lem1355582) (@lem1355581 x)). Qed.
Lemma lem1355584 (x : real) (y : real) : (term129 x y) = (term119 x y).
Proof. exact (eq_refl (term129 x y)). Qed.
Lemma lem1355585 (x : real) : (term139 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem1355584 x y)). Qed.
Lemma lem1355586 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355587 (x : real) : (term140 x) = (term141 x).
Proof. exact (MK_COMB (@lem1355586) (@lem1355585 x)). Qed.
Lemma lem1355588 (x : real) : (term124 x) = (term142 x).
Proof. exact (MK_COMB (@lem1355583 x) (@lem1355587 x)). Qed.
Lemma lem1355589 (x : real) : ((term123 x) = (term124 x)) = ((term122 x) = (term142 x)).
Proof. exact (MK_COMB (@lem1355577 x) (@lem1355588 x)). Qed.
Lemma lem1355590 (x : real) : (term122 x) = (term142 x).
Proof. exact (EQ_MP (@lem1355589 x) (@lem1355567 x)). Qed.
Lemma lem1355695 (x : real) : (term51 x) = (term142 x).
Proof. exact (TRANS (@lem1355563 x) (@lem1355590 x)). Qed.
Lemma lem1355696 : term52 = term143.
Proof. exact (fun_ext (fun x : real => @lem1355695 x)). Qed.
Lemma lem1355697 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355698 : term53 = term144.
Proof. exact (MK_COMB (@lem1355697) (@lem1355696)). Qed.
Lemma lem1355700 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term54 A P Q) = (term55 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1355701 (P : real -> Prop) (Q : real -> Prop) : (term56 P Q) = (term57 P Q).
Proof. exact (@lem1355700 real P Q). Qed.
Lemma lem1355702 : term145 = term146.
Proof. exact (@lem1355701 term147 term148). Qed.
Lemma lem1355703 (x : real) : (term149 x) = (term136 x).
Proof. exact (eq_refl (term149 x)). Qed.
Lemma lem1355704 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1355705 (x : real) : (term150 x) = (term138 x).
Proof. exact (MK_COMB (@lem1355704) (@lem1355703 x)). Qed.
Lemma lem1355706 (x : real) : (term151 x) = (term141 x).
Proof. exact (eq_refl (term151 x)). Qed.
Lemma lem1355707 (x : real) : (term152 x) = (term142 x).
Proof. exact (MK_COMB (@lem1355705 x) (@lem1355706 x)). Qed.
Lemma lem1355708 : term153 = term143.
Proof. exact (fun_ext (fun x : real => @lem1355707 x)). Qed.
Lemma lem1355709 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355710 : term145 = term144.
Proof. exact (MK_COMB (@lem1355709) (@lem1355708)). Qed.
Lemma lem1355711 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1355712 : term154 = term155.
Proof. exact (MK_COMB (@lem1355711) (@lem1355710)). Qed.
Lemma lem1355713 (x : real) : (term149 x) = (term136 x).
Proof. exact (eq_refl (term149 x)). Qed.
Lemma lem1355714 : term156 = term147.
Proof. exact (fun_ext (fun x : real => @lem1355713 x)). Qed.
Lemma lem1355715 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355716 : term157 = term158.
Proof. exact (MK_COMB (@lem1355715) (@lem1355714)). Qed.
Lemma lem1355717 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1355718 : term159 = term160.
Proof. exact (MK_COMB (@lem1355717) (@lem1355716)). Qed.
Lemma lem1355719 (x : real) : (term151 x) = (term141 x).
Proof. exact (eq_refl (term151 x)). Qed.
Lemma lem1355720 : term161 = term148.
Proof. exact (fun_ext (fun x : real => @lem1355719 x)). Qed.
Lemma lem1355721 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355722 : term162 = term163.
Proof. exact (MK_COMB (@lem1355721) (@lem1355720)). Qed.
Lemma lem1355723 : term146 = term164.
Proof. exact (MK_COMB (@lem1355718) (@lem1355722)). Qed.
Lemma lem1355724 : (term145 = term146) = (term144 = term164).
Proof. exact (MK_COMB (@lem1355712) (@lem1355723)). Qed.
Lemma lem1355725 : term144 = term164.
Proof. exact (EQ_MP (@lem1355724) (@lem1355702)). Qed.
Lemma lem1355840 : term53 = term164.
Proof. exact (TRANS (@lem1355698) (@lem1355725)). Qed.
Lemma lem1355841 : term10 = term164.
Proof. exact (TRANS (@lem1355425) (@lem1355840)). Qed.
Lemma lem1355842 (h1 : term10) : term164.
Proof. exact (EQ_MP (@lem1355841) (@lem1355341 h1)). Qed.
Lemma lem1355856 (x : real) : ((term32 x) = x) = ((term32 x) = x).
Proof. exact (eq_refl ((term32 x) = x)). Qed.
Lemma lem1355857 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem1355856 x)). Qed.
Lemma lem1355858 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355859 : term34 = term34.
Proof. exact (MK_COMB (@lem1355858) (@lem1355857)). Qed.
Lemma lem1355860 (h1 : term34) : term34.
Proof. exact (EQ_MP (@lem1355859) (@lem1355374 h1)). Qed.
Lemma lem1355885 (y : real) (x : real) (z : real) : ((term24 x y z) = (term25 y x z)) = ((term24 x y z) = (term25 y x z)).
Proof. exact (eq_refl ((term24 x y z) = (term25 y x z))). Qed.
Lemma lem1355886 (y : real) (x : real) : (term26 y x) = (term26 y x).
Proof. exact (fun_ext (fun z : real => @lem1355885 y x z)). Qed.
Lemma lem1355887 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355888 (y : real) (x : real) : (term27 y x) = (term27 y x).
Proof. exact (MK_COMB (@lem1355887) (@lem1355886 y x)). Qed.
Lemma lem1355889 (x : real) : (term28 x) = (term28 x).
Proof. exact (fun_ext (fun y : real => @lem1355888 y x)). Qed.
Lemma lem1355890 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355891 (x : real) : (term29 x) = (term29 x).
Proof. exact (MK_COMB (@lem1355890) (@lem1355889 x)). Qed.
Lemma lem1355892 : term30 = term30.
Proof. exact (fun_ext (fun x : real => @lem1355891 x)). Qed.
Lemma lem1355893 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355894 : term31 = term31.
Proof. exact (MK_COMB (@lem1355893) (@lem1355892)). Qed.
Lemma lem1355895 (h1 : term31) : term31.
Proof. exact (EQ_MP (@lem1355894) (@lem1355401 h1)). Qed.
Lemma lem1355900 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1355915 (x : real) (y : real) (z : real) : (term107 x y z) = (term107 x y z).
Proof. exact (eq_refl (term107 x y z)). Qed.
Lemma lem1355916 (x : real) (y : real) : (term105 x y) = (term105 x y).
Proof. exact (fun_ext (fun z : real => @lem1355915 x y z)). Qed.
Lemma lem1355917 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355918 (x : real) (y : real) : (term116 x y) = (term116 x y).
Proof. exact (MK_COMB (@lem1355917) (@lem1355916 x y)). Qed.
Lemma lem1355919 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1355920 (x : real) (y : real) : (term118 x y) = (term118 x y).
Proof. exact (MK_COMB (@lem1355919) (@lem1355918 x y)). Qed.
Lemma lem1355921 (x : real) (y : real) : (term119 x y) = (term119 x y).
Proof. exact (MK_COMB (@lem1355920 x y) (@lem1355900 x y)). Qed.
Lemma lem1355922 (x : real) : (term126 x) = (term126 x).
Proof. exact (fun_ext (fun y : real => @lem1355921 x y)). Qed.
Lemma lem1355923 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355924 (x : real) : (term141 x) = (term141 x).
Proof. exact (MK_COMB (@lem1355923) (@lem1355922 x)). Qed.
Lemma lem1355925 : term148 = term148.
Proof. exact (fun_ext (fun x : real => @lem1355924 x)). Qed.
Lemma lem1355926 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355927 : term163 = term163.
Proof. exact (MK_COMB (@lem1355926) (@lem1355925)). Qed.
Lemma lem1355934 (x : real) (y : real) : (term88 x y) = (term88 x y).
Proof. exact (eq_refl (term88 x y)). Qed.
Lemma lem1355947 (x : real) (y : real) (z : real) : ((real_add x z) = (real_add y z)) = ((real_add x z) = (real_add y z)).
Proof. exact (eq_refl ((real_add x z) = (real_add y z))). Qed.
Lemma lem1355948 (x : real) (y : real) : (term87 x y) = (term87 x y).
Proof. exact (fun_ext (fun z : real => @lem1355947 x y z)). Qed.
Lemma lem1355949 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355950 (x : real) (y : real) : (term98 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem1355949) (@lem1355948 x y)). Qed.
Lemma lem1355951 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1355952 (x : real) (y : real) : (term100 x y) = (term100 x y).
Proof. exact (MK_COMB (@lem1355951) (@lem1355950 x y)). Qed.
Lemma lem1355953 (x : real) (y : real) : (term101 x y) = (term101 x y).
Proof. exact (MK_COMB (@lem1355952 x y) (@lem1355934 x y)). Qed.
Lemma lem1355954 (x : real) : (term125 x) = (term125 x).
Proof. exact (fun_ext (fun y : real => @lem1355953 x y)). Qed.
Lemma lem1355955 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355956 (x : real) : (term136 x) = (term136 x).
Proof. exact (MK_COMB (@lem1355955) (@lem1355954 x)). Qed.
Lemma lem1355957 : term147 = term147.
Proof. exact (fun_ext (fun x : real => @lem1355956 x)). Qed.
Lemma lem1355958 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355959 : term158 = term158.
Proof. exact (MK_COMB (@lem1355958) (@lem1355957)). Qed.
Lemma lem1355960 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1355961 : term160 = term160.
Proof. exact (MK_COMB (@lem1355960) (@lem1355959)). Qed.
Lemma lem1355962 : term164 = term164.
Proof. exact (MK_COMB (@lem1355961) (@lem1355927)). Qed.
Lemma lem1355963 (h1 : term10) : term164.
Proof. exact (EQ_MP (@lem1355962) (@lem1355842 h1)). Qed.
Lemma lem1355983 (x : real) (h1 : term43 x) : term43 x.
Proof. exact (h1). Qed.
Lemma lem1355984 (h1 : term10) : term163.
Proof. exact (proj2 (@lem1355963 h1)). Qed.
Lemma lem1355987 (x : real) : ((term32 x) = x) = ((term32 x) = x).
Proof. exact (eq_refl ((term32 x) = x)). Qed.
Lemma lem1355988 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem1355987 x)). Qed.
Lemma lem1355989 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355991 : term34 = term34.
Proof. exact (MK_COMB (@lem1355989) (@lem1355988)). Qed.
Lemma lem1355992 (h1 : term34) : term34.
Proof. exact (EQ_MP (@lem1355991) (@lem1355860 h1)). Qed.
Lemma lem1355994 (y : real) (x : real) (z : real) : ((term24 x y z) = (term25 y x z)) = ((term24 x y z) = (term25 y x z)).
Proof. exact (eq_refl ((term24 x y z) = (term25 y x z))). Qed.
Lemma lem1355995 (y : real) (x : real) : (term26 y x) = (term26 y x).
Proof. exact (fun_ext (fun z : real => @lem1355994 y x z)). Qed.
Lemma lem1355996 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1355997 (y : real) (x : real) : (term27 y x) = (term27 y x).
Proof. exact (MK_COMB (@lem1355996) (@lem1355995 y x)). Qed.
Lemma lem1355998 (x : real) : (term28 x) = (term28 x).
Proof. exact (fun_ext (fun y : real => @lem1355997 y x)). Qed.
Lemma lem1355999 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1356000 (x : real) : (term29 x) = (term29 x).
Proof. exact (MK_COMB (@lem1355999) (@lem1355998 x)). Qed.
Lemma lem1356001 : term30 = term30.
Proof. exact (fun_ext (fun x : real => @lem1356000 x)). Qed.
Lemma lem1356002 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1356004 : term31 = term31.
Proof. exact (MK_COMB (@lem1356002) (@lem1356001)). Qed.
Lemma lem1356005 (h1 : term31) : term31.
Proof. exact (EQ_MP (@lem1356004) (@lem1355895 h1)). Qed.
Lemma lem1356009 (x : real) (h1 : term43 x) : term43 x.
Proof. exact (h1). Qed.
Lemma lem1356059 {A : Type'} (P : A -> Prop) (Q : Prop) : (term82 A P Q) = (term81 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem1356060 (P : real -> Prop) (Q : Prop) : (term84 P Q) = (term83 P Q).
Proof. exact (@lem1356059 real P Q). Qed.
Lemma lem1356061 (x : real) (y : real) : (term104 x y) = (term103 x y).
Proof. exact (@lem1356060 (term105 x y) (x = y)). Qed.
Lemma lem1356062 (x : real) (y : real) (z : real) : (term106 x y z) = (term107 x y z).
Proof. exact (eq_refl (term106 x y z)). Qed.
Lemma lem1356063 (x : real) (y : real) : (term114 x y) = (term105 x y).
Proof. exact (fun_ext (fun z : real => @lem1356062 x y z)). Qed.
Lemma lem1356064 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1356065 (x : real) (y : real) : (term115 x y) = (term116 x y).
Proof. exact (MK_COMB (@lem1356064) (@lem1356063 x y)). Qed.
Lemma lem1356066 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1356067 (x : real) (y : real) : (term117 x y) = (term118 x y).
Proof. exact (MK_COMB (@lem1356066) (@lem1356065 x y)). Qed.
Lemma lem1356068 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1356069 (x : real) (y : real) : (term104 x y) = (term119 x y).
Proof. exact (MK_COMB (@lem1356067 x y) (@lem1356068 x y)). Qed.
Lemma lem1356070 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1356071 (x : real) (y : real) : (term165 x y) = (term166 x y).
Proof. exact (MK_COMB (@lem1356070) (@lem1356069 x y)). Qed.
Lemma lem1356072 (x : real) (y : real) (z : real) : (term106 x y z) = (term107 x y z).
Proof. exact (eq_refl (term106 x y z)). Qed.
Lemma lem1356073 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1356074 (x : real) (y : real) (z : real) : (term108 x y z) = (term109 x y z).
Proof. exact (MK_COMB (@lem1356073) (@lem1356072 x y z)). Qed.
Lemma lem1356075 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1356076 (z : real) (x : real) (y : real) : (term110 z x y) = (term67 z x y).
Proof. exact (MK_COMB (@lem1356074 x y z) (@lem1356075 x y)). Qed.
Lemma lem1356077 (x : real) (y : real) : (term111 x y) = (term61 x y).
Proof. exact (fun_ext (fun z : real => @lem1356076 z x y)). Qed.
Lemma lem1356078 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1356079 (x : real) (y : real) : (term103 x y) = (term79 x y).
Proof. exact (MK_COMB (@lem1356078) (@lem1356077 x y)). Qed.
Lemma lem1356080 (x : real) (y : real) : ((term104 x y) = (term103 x y)) = ((term119 x y) = (term79 x y)).
Proof. exact (MK_COMB (@lem1356071 x y) (@lem1356079 x y)). Qed.
Lemma lem1356081 (x : real) (y : real) : (term119 x y) = (term79 x y).
Proof. exact (EQ_MP (@lem1356080 x y) (@lem1356061 x y)). Qed.
Lemma lem1356082 (x : real) : (term126 x) = (term167 x).
Proof. exact (fun_ext (fun y : real => @lem1356081 x y)). Qed.
Lemma lem1356083 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1356084 (x : real) : (term141 x) = (term168 x).
Proof. exact (MK_COMB (@lem1356083) (@lem1356082 x)). Qed.
Lemma lem1356085 : term148 = term169.
Proof. exact (fun_ext (fun x : real => @lem1356084 x)). Qed.
Lemma lem1356086 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1356087 : term163 = term170.
Proof. exact (MK_COMB (@lem1356086) (@lem1356085)). Qed.
Lemma lem1356094 (z : real) (x : real) (y : real) : (term67 z x y) = (term67 z x y).
Proof. exact (eq_refl (term67 z x y)). Qed.
Lemma lem1356095 (x : real) (y : real) : (term61 x y) = (term61 x y).
Proof. exact (fun_ext (fun z : real => @lem1356094 z x y)). Qed.
Lemma lem1356096 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1356097 (x : real) (y : real) : (term79 x y) = (term79 x y).
Proof. exact (MK_COMB (@lem1356096) (@lem1356095 x y)). Qed.
Lemma lem1356098 (x : real) : (term167 x) = (term167 x).
Proof. exact (fun_ext (fun y : real => @lem1356097 x y)). Qed.
Lemma lem1356099 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1356100 (x : real) : (term168 x) = (term168 x).
Proof. exact (MK_COMB (@lem1356099) (@lem1356098 x)). Qed.
Lemma lem1356101 : term169 = term169.
Proof. exact (fun_ext (fun x : real => @lem1356100 x)). Qed.
Lemma lem1356102 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1356103 : term170 = term170.
Proof. exact (MK_COMB (@lem1356102) (@lem1356101)). Qed.
Lemma lem1356104 : term163 = term170.
Proof. exact (TRANS (@lem1356087) (@lem1356103)). Qed.
Lemma lem1356105 (h1 : term10) : term170.
Proof. exact (EQ_MP (@lem1356104) (@lem1355984 h1)). Qed.
Lemma lem1356106 (_24117 : real) (h1 : term34) : term171 _24117.
Proof. exact (@lem1355992 h1 _24117). Qed.
Lemma lem1356107 (_24117 : real) : (term171 _24117) = ((term32 _24117) = _24117).
Proof. exact (eq_refl (term171 _24117)). Qed.
Lemma lem1356109 (_24118 : real) (h1 : term31) : term172 _24118.
Proof. exact (@lem1356005 h1 _24118). Qed.
Lemma lem1356110 (_24118 : real) : (term172 _24118) = (term29 _24118).
Proof. exact (eq_refl (term172 _24118)). Qed.
Lemma lem1356111 (_24118 : real) (h1 : term31) : term29 _24118.
Proof. exact (EQ_MP (@lem1356110 _24118) (@lem1356109 _24118 h1)). Qed.
Lemma lem1356112 (_24118 : real) (_24119 : real) (h1 : term31) : term173 _24118 _24119.
Proof. exact (@lem1356111 _24118 h1 _24119). Qed.
Lemma lem1356113 (_24119 : real) (_24118 : real) : (term173 _24118 _24119) = (term27 _24119 _24118).
Proof. exact (eq_refl (term173 _24118 _24119)). Qed.
Lemma lem1356114 (_24119 : real) (_24118 : real) (h1 : term31) : term27 _24119 _24118.
Proof. exact (EQ_MP (@lem1356113 _24119 _24118) (@lem1356112 _24118 _24119 h1)). Qed.
Lemma lem1356115 (_24119 : real) (_24118 : real) (_24120 : real) (h1 : term31) : term174 _24119 _24118 _24120.
Proof. exact (@lem1356114 _24119 _24118 h1 _24120). Qed.
Lemma lem1356116 (_24119 : real) (_24118 : real) (_24120 : real) : (term174 _24119 _24118 _24120) = ((term24 _24118 _24119 _24120) = (term25 _24119 _24118 _24120)).
Proof. exact (eq_refl (term174 _24119 _24118 _24120)). Qed.
Lemma lem1356127 (_24124 : real) (h1 : term10) : term175 _24124.
Proof. exact (@lem1356105 h1 _24124). Qed.
Lemma lem1356128 (_24124 : real) : (term175 _24124) = (term168 _24124).
Proof. exact (eq_refl (term175 _24124)). Qed.
Lemma lem1356129 (_24124 : real) (h1 : term10) : term168 _24124.
Proof. exact (EQ_MP (@lem1356128 _24124) (@lem1356127 _24124 h1)). Qed.
Lemma lem1356130 (_24124 : real) (_24125 : real) (h1 : term10) : term176 _24124 _24125.
Proof. exact (@lem1356129 _24124 h1 _24125). Qed.
Lemma lem1356131 (_24124 : real) (_24125 : real) : (term176 _24124 _24125) = (term79 _24124 _24125).
Proof. exact (eq_refl (term176 _24124 _24125)). Qed.
Lemma lem1356132 (_24124 : real) (_24125 : real) (h1 : term10) : term79 _24124 _24125.
Proof. exact (EQ_MP (@lem1356131 _24124 _24125) (@lem1356130 _24124 _24125 h1)). Qed.
Lemma lem1356133 (_24124 : real) (_24125 : real) (_24126 : real) (h1 : term10) : term66 _24124 _24125 _24126.
Proof. exact (@lem1356132 _24124 _24125 h1 _24126). Qed.
Lemma lem1356134 (_24126 : real) (_24124 : real) (_24125 : real) : (term66 _24124 _24125 _24126) = (term67 _24126 _24124 _24125).
Proof. exact (eq_refl (term66 _24124 _24125 _24126)). Qed.
Lemma lem1356141 (x : real) (h1 : term43 x) : term43 x.
Proof. exact (h1). Qed.
Lemma lem1356153 (_24126 : real) (_24124 : real) (_24125 : real) (h1 : term10) : term67 _24126 _24124 _24125.
Proof. exact (EQ_MP (@lem1356134 _24126 _24124 _24125) (@lem1356133 _24124 _24125 _24126 h1)). Qed.
Lemma lem1356154 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1356155 (_24127 : real) (_24129 : real) (h1 : _24127 = _24129) : _24127 = _24129.
Proof. exact (h1). Qed.
Lemma lem1356156 (_24128 : real) (_24130 : real) (h1 : _24128 = _24130) : _24128 = _24130.
Proof. exact (h1). Qed.
Lemma lem1356157 (_24127 : real) (_24129 : real) (h1 : _24127 = _24129) : (real_mul _24127) = (real_mul _24129).
Proof. exact (MK_COMB (@lem1356154) (@lem1356155 _24127 _24129 h1)). Qed.
Lemma lem1356158 (_24127 : real) (_24129 : real) (_24128 : real) (_24130 : real) (h1 : _24127 = _24129) (h2 : _24128 = _24130) : (real_mul _24127 _24128) = (real_mul _24129 _24130).
Proof. exact (MK_COMB (@lem1356157 _24127 _24129 h1) (@lem1356156 _24128 _24130 h2)). Qed.
Lemma lem1356159 (_24128 : real) (_24130 : real) (_24127 : real) (_24129 : real) (h1 : _24127 = _24129) : term177 _24127 _24128 _24129 _24130.
Proof. exact (fun h0 : _24128 = _24130 => @lem1356158 _24127 _24129 _24128 _24130 h1 h0). Qed.
Lemma lem1356161 (a : Prop) (b : Prop) : (a -> b) = (term178 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1356162 (_24127 : real) (_24128 : real) (_24129 : real) (_24130 : real) : (term177 _24127 _24128 _24129 _24130) = (term179 _24127 _24128 _24129 _24130).
Proof. exact (@lem1356161 (_24128 = _24130) ((real_mul _24127 _24128) = (real_mul _24129 _24130))). Qed.
Lemma lem1356163 (_24128 : real) (_24130 : real) (_24127 : real) (_24129 : real) (h1 : _24127 = _24129) : term179 _24127 _24128 _24129 _24130.
Proof. exact (EQ_MP (@lem1356162 _24127 _24128 _24129 _24130) (@lem1356159 _24128 _24130 _24127 _24129 h1)). Qed.
Lemma lem1356164 (_24127 : real) (_24128 : real) (_24129 : real) (_24130 : real) : term180 _24127 _24128 _24129 _24130.
Proof. exact (fun h0 : _24127 = _24129 => @lem1356163 _24128 _24130 _24127 _24129 h0). Qed.
Lemma lem1356166 (a : Prop) (b : Prop) : (a -> b) = (term178 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1356167 (_24127 : real) (_24128 : real) (_24129 : real) (_24130 : real) : (term180 _24127 _24128 _24129 _24130) = (term181 _24127 _24128 _24129 _24130).
Proof. exact (@lem1356166 (_24127 = _24129) (term179 _24127 _24128 _24129 _24130)). Qed.
Lemma lem1356168 (_24127 : real) (_24128 : real) (_24129 : real) (_24130 : real) : term181 _24127 _24128 _24129 _24130.
Proof. exact (EQ_MP (@lem1356167 _24127 _24128 _24129 _24130) (@lem1356164 _24127 _24128 _24129 _24130)). Qed.
Lemma lem1356185 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1356186 (_24135 : real) (_24137 : real) (h1 : _24135 = _24137) : _24135 = _24137.
Proof. exact (h1). Qed.
Lemma lem1356187 (_24136 : real) (_24138 : real) (h1 : _24136 = _24138) : _24136 = _24138.
Proof. exact (h1). Qed.
Lemma lem1356188 (_24135 : real) (_24137 : real) (h1 : _24135 = _24137) : (real_add _24135) = (real_add _24137).
Proof. exact (MK_COMB (@lem1356185) (@lem1356186 _24135 _24137 h1)). Qed.
Lemma lem1356189 (_24135 : real) (_24137 : real) (_24136 : real) (_24138 : real) (h1 : _24135 = _24137) (h2 : _24136 = _24138) : (real_add _24135 _24136) = (real_add _24137 _24138).
Proof. exact (MK_COMB (@lem1356188 _24135 _24137 h1) (@lem1356187 _24136 _24138 h2)). Qed.
Lemma lem1356190 (_24136 : real) (_24138 : real) (_24135 : real) (_24137 : real) (h1 : _24135 = _24137) : term182 _24135 _24136 _24137 _24138.
Proof. exact (fun h0 : _24136 = _24138 => @lem1356189 _24135 _24137 _24136 _24138 h1 h0). Qed.
Lemma lem1356192 (a : Prop) (b : Prop) : (a -> b) = (term178 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1356193 (_24135 : real) (_24136 : real) (_24137 : real) (_24138 : real) : (term182 _24135 _24136 _24137 _24138) = (term183 _24135 _24136 _24137 _24138).
Proof. exact (@lem1356192 (_24136 = _24138) ((real_add _24135 _24136) = (real_add _24137 _24138))). Qed.
Lemma lem1356194 (_24136 : real) (_24138 : real) (_24135 : real) (_24137 : real) (h1 : _24135 = _24137) : term183 _24135 _24136 _24137 _24138.
Proof. exact (EQ_MP (@lem1356193 _24135 _24136 _24137 _24138) (@lem1356190 _24136 _24138 _24135 _24137 h1)). Qed.
Lemma lem1356195 (_24135 : real) (_24136 : real) (_24137 : real) (_24138 : real) : term184 _24135 _24136 _24137 _24138.
Proof. exact (fun h0 : _24135 = _24137 => @lem1356194 _24136 _24138 _24135 _24137 h0). Qed.
Lemma lem1356197 (a : Prop) (b : Prop) : (a -> b) = (term178 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1356198 (_24135 : real) (_24136 : real) (_24137 : real) (_24138 : real) : (term184 _24135 _24136 _24137 _24138) = (term185 _24135 _24136 _24137 _24138).
Proof. exact (@lem1356197 (_24135 = _24137) (term183 _24135 _24136 _24137 _24138)). Qed.
Lemma lem1356199 (_24135 : real) (_24136 : real) (_24137 : real) (_24138 : real) : term185 _24135 _24136 _24137 _24138.
Proof. exact (EQ_MP (@lem1356198 _24135 _24136 _24137 _24138) (@lem1356195 _24135 _24136 _24137 _24138)). Qed.
Lemma lem1356201 (x : real) (y : real) (z : real) : term186 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1356205 (_24119 : real) (_24118 : real) (_24120 : real) (h1 : term31) : (term24 _24118 _24119 _24120) = (term25 _24119 _24118 _24120).
Proof. exact (EQ_MP (@lem1356116 _24119 _24118 _24120) (@lem1356115 _24119 _24118 _24120 h1)). Qed.
Lemma lem1356206 (x : real) (_24139 : real) (h1 : term31) : (term187 x _24139) = (term188 x _24139).
Proof. exact (@lem1356205 term36 x _24139 h1). Qed.
Lemma lem1356207 (x : real) (_24139 : real) (h1 : term31) : term189 x _24139.
Proof. exact (fun h0 : term190 x _24139 => @lem1356206 x _24139 h1). Qed.
Lemma lem1356209 (p : Prop) : (term191 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1356210 (x : real) (_24139 : real) : (term189 x _24139) = ((term187 x _24139) = (term188 x _24139)).
Proof. exact (@lem1356209 ((term187 x _24139) = (term188 x _24139))). Qed.
Lemma lem1356211 (x : real) (_24139 : real) (h1 : term31) : (term187 x _24139) = (term188 x _24139).
Proof. exact (EQ_MP (@lem1356210 x _24139) (@lem1356207 x _24139 h1)). Qed.
Lemma lem1356213 (_24117 : real) (h1 : term34) : (term32 _24117) = _24117.
Proof. exact (EQ_MP (@lem1356107 _24117) (@lem1356106 _24117 h1)). Qed.
Lemma lem1356214 (x : real) (_24139 : real) (h1 : term34) : (term192 x _24139) = (term187 x _24139).
Proof. exact (@lem1356213 (term187 x _24139) h1). Qed.
Lemma lem1356215 (x : real) (_24139 : real) (h1 : term34) : term193 x _24139.
Proof. exact (fun h0 : term194 x _24139 => @lem1356214 x _24139 h1). Qed.
Lemma lem1356217 (p : Prop) : (term191 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1356218 (x : real) (_24139 : real) : (term193 x _24139) = ((term192 x _24139) = (term187 x _24139)).
Proof. exact (@lem1356217 ((term192 x _24139) = (term187 x _24139))). Qed.
Lemma lem1356219 (x : real) (_24139 : real) (h1 : term34) : (term192 x _24139) = (term187 x _24139).
Proof. exact (EQ_MP (@lem1356218 x _24139) (@lem1356215 x _24139 h1)). Qed.
Lemma lem1356221 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1356222 : term36 = term36.
Proof. exact (@lem1356221 term36). Qed.
Lemma lem1356223 : term195.
Proof. exact (fun h0 : term196 => @lem1356222). Qed.
Lemma lem1356225 (p : Prop) : (term191 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1356226 : term195 = (term36 = term36).
Proof. exact (@lem1356225 (term36 = term36)). Qed.
Lemma lem1356227 : term36 = term36.
Proof. exact (EQ_MP (@lem1356226) (@lem1356223)). Qed.
Lemma lem1356229 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1356230 (x : real) : term197 x.
Proof. exact (fun h0 : term198 x => @lem1356229 x). Qed.
Lemma lem1356232 (p : Prop) : (term191 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1356233 (x : real) : (term197 x) = (x = x).
Proof. exact (@lem1356232 (x = x)). Qed.
Lemma lem1356234 (x : real) : x = x.
Proof. exact (EQ_MP (@lem1356233 x) (@lem1356230 x)). Qed.
Lemma lem1356236 (_24117 : real) (h1 : term34) : (term32 _24117) = _24117.
Proof. exact (EQ_MP (@lem1356107 _24117) (@lem1356106 _24117 h1)). Qed.
Lemma lem1356237 (_24139 : real) (h1 : term34) : (term32 _24139) = _24139.
Proof. exact (@lem1356236 _24139 h1). Qed.
Lemma lem1356238 (_24139 : real) (h1 : term34) : term199 _24139.
Proof. exact (fun h0 : term200 _24139 => @lem1356237 _24139 h1). Qed.
Lemma lem1356240 (p : Prop) : (term191 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1356241 (_24139 : real) : (term199 _24139) = ((term32 _24139) = _24139).
Proof. exact (@lem1356240 ((term32 _24139) = _24139)). Qed.
Lemma lem1356242 (_24139 : real) (h1 : term34) : (term32 _24139) = _24139.
Proof. exact (EQ_MP (@lem1356241 _24139) (@lem1356238 _24139 h1)). Qed.
Lemma lem1356260 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1356261 (_24127 : real) (_24129 : real) (_24128 : real) (_24130 : real) : (term179 _24127 _24128 _24129 _24130) = (term201 _24127 _24129 _24128 _24130).
Proof. exact (@lem1356260 ((real_mul _24127 _24128) = (real_mul _24129 _24130)) (term88 _24128 _24130)). Qed.
Lemma lem1356271 (_24127 : real) (_24129 : real) : (term202 _24127 _24129) = (term202 _24127 _24129).
Proof. exact (eq_refl (term202 _24127 _24129)). Qed.
Lemma lem1356272 (_24127 : real) (_24129 : real) (_24128 : real) (_24130 : real) : (term181 _24127 _24128 _24129 _24130) = (term203 _24127 _24129 _24128 _24130).
Proof. exact (MK_COMB (@lem1356271 _24127 _24129) (@lem1356261 _24127 _24129 _24128 _24130)). Qed.
Lemma lem1356276 (q : Prop) (p : Prop) (r : Prop) : (term204 p q r) = (term204 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1356277 (_24127 : real) (_24129 : real) (_24128 : real) (_24130 : real) : (term203 _24127 _24129 _24128 _24130) = (term205 _24127 _24129 _24128 _24130).
Proof. exact (@lem1356276 ((real_mul _24127 _24128) = (real_mul _24129 _24130)) (term88 _24127 _24129) (term88 _24128 _24130)). Qed.
Lemma lem1356299 (_24127 : real) (_24129 : real) (_24128 : real) (_24130 : real) : (term181 _24127 _24128 _24129 _24130) = (term205 _24127 _24129 _24128 _24130).
Proof. exact (TRANS (@lem1356272 _24127 _24129 _24128 _24130) (@lem1356277 _24127 _24129 _24128 _24130)). Qed.
Lemma lem1356300 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1356301 (_24127 : real) (_24129 : real) (_24128 : real) (_24130 : real) : (term206 _24127 _24128 _24129 _24130) = (term207 _24127 _24129 _24128 _24130).
Proof. exact (MK_COMB (@lem1356300) (@lem1356299 _24127 _24129 _24128 _24130)). Qed.
Lemma lem1356323 (_24127 : real) (_24129 : real) (_24128 : real) (_24130 : real) : (term205 _24127 _24129 _24128 _24130) = (term205 _24127 _24129 _24128 _24130).
Proof. exact (eq_refl (term205 _24127 _24129 _24128 _24130)). Qed.
Lemma lem1356324 (_24127 : real) (_24129 : real) (_24128 : real) (_24130 : real) : ((term181 _24127 _24128 _24129 _24130) = (term205 _24127 _24129 _24128 _24130)) = ((term205 _24127 _24129 _24128 _24130) = (term205 _24127 _24129 _24128 _24130)).
Proof. exact (MK_COMB (@lem1356301 _24127 _24129 _24128 _24130) (@lem1356323 _24127 _24129 _24128 _24130)). Qed.
Lemma lem1356326 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1356327 (x : Prop) : (x = x) = True.
Proof. exact (@lem1356326 Prop x). Qed.
Lemma lem1356328 (_24127 : real) (_24129 : real) (_24128 : real) (_24130 : real) : ((term205 _24127 _24129 _24128 _24130) = (term205 _24127 _24129 _24128 _24130)) = True.
Proof. exact (@lem1356327 (term205 _24127 _24129 _24128 _24130)). Qed.
Lemma lem1356329 (_24127 : real) (_24129 : real) (_24128 : real) (_24130 : real) : ((term181 _24127 _24128 _24129 _24130) = (term205 _24127 _24129 _24128 _24130)) = True.
Proof. exact (TRANS (@lem1356324 _24127 _24129 _24128 _24130) (@lem1356328 _24127 _24129 _24128 _24130)). Qed.
Lemma lem1356330 (_24127 : real) (_24129 : real) (_24128 : real) (_24130 : real) : True = ((term181 _24127 _24128 _24129 _24130) = (term205 _24127 _24129 _24128 _24130)).
Proof. exact (SYM (@lem1356329 _24127 _24129 _24128 _24130)). Qed.
Lemma lem1356331 (_24127 : real) (_24129 : real) (_24128 : real) (_24130 : real) : (term181 _24127 _24128 _24129 _24130) = (term205 _24127 _24129 _24128 _24130).
Proof. exact (EQ_MP (@lem1356330 _24127 _24129 _24128 _24130) (@lem0)). Qed.
Lemma lem1356332 (_24127 : real) (_24129 : real) (_24128 : real) (_24130 : real) : term205 _24127 _24129 _24128 _24130.
Proof. exact (EQ_MP (@lem1356331 _24127 _24129 _24128 _24130) (@lem1356168 _24127 _24128 _24129 _24130)). Qed.
Lemma lem1356334 (b : Prop) (a : Prop) : (a \/ b) = (term208 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1356335 (_24127 : real) (_24128 : real) (_24129 : real) (_24130 : real) : (term205 _24127 _24129 _24128 _24130) = (term209 _24127 _24128 _24129 _24130).
Proof. exact (@lem1356334 (term210 _24127 _24129 _24128 _24130) ((real_mul _24127 _24128) = (real_mul _24129 _24130))). Qed.
Lemma lem1356337 (a : Prop) (b : Prop) : (term211 a b) = (term212 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1356338 (_24127 : real) (_24129 : real) (_24128 : real) (_24130 : real) : (term213 _24127 _24129 _24128 _24130) = (term214 _24127 _24129 _24128 _24130).
Proof. exact (@lem1356337 (term88 _24127 _24129) (term88 _24128 _24130)). Qed.
Lemma lem1356340 (a : Prop) : (term215 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1356341 (_24127 : real) (_24129 : real) : (term216 _24127 _24129) = (_24127 = _24129).
Proof. exact (@lem1356340 (_24127 = _24129)). Qed.
Lemma lem1356342 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1356343 (_24127 : real) (_24129 : real) : (term217 _24127 _24129) = (term218 _24127 _24129).
Proof. exact (MK_COMB (@lem1356342) (@lem1356341 _24127 _24129)). Qed.
Lemma lem1356345 (a : Prop) : (term215 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1356346 (_24128 : real) (_24130 : real) : (term216 _24128 _24130) = (_24128 = _24130).
Proof. exact (@lem1356345 (_24128 = _24130)). Qed.
Lemma lem1356347 (_24127 : real) (_24129 : real) (_24128 : real) (_24130 : real) : (term214 _24127 _24129 _24128 _24130) = (term219 _24127 _24129 _24128 _24130).
Proof. exact (MK_COMB (@lem1356343 _24127 _24129) (@lem1356346 _24128 _24130)). Qed.
Lemma lem1356348 (_24127 : real) (_24129 : real) (_24128 : real) (_24130 : real) : (term213 _24127 _24129 _24128 _24130) = (term219 _24127 _24129 _24128 _24130).
Proof. exact (TRANS (@lem1356338 _24127 _24129 _24128 _24130) (@lem1356347 _24127 _24129 _24128 _24130)). Qed.
Lemma lem1356349 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1356350 (_24127 : real) (_24129 : real) (_24128 : real) (_24130 : real) : (term220 _24127 _24129 _24128 _24130) = (term221 _24127 _24129 _24128 _24130).
Proof. exact (MK_COMB (@lem1356349) (@lem1356348 _24127 _24129 _24128 _24130)). Qed.
Lemma lem1356351 (_24127 : real) (_24128 : real) (_24129 : real) (_24130 : real) : ((real_mul _24127 _24128) = (real_mul _24129 _24130)) = ((real_mul _24127 _24128) = (real_mul _24129 _24130)).
Proof. exact (eq_refl ((real_mul _24127 _24128) = (real_mul _24129 _24130))). Qed.
Lemma lem1356352 (_24127 : real) (_24128 : real) (_24129 : real) (_24130 : real) : (term209 _24127 _24128 _24129 _24130) = (term222 _24127 _24128 _24129 _24130).
Proof. exact (MK_COMB (@lem1356350 _24127 _24129 _24128 _24130) (@lem1356351 _24127 _24128 _24129 _24130)). Qed.
Lemma lem1356353 (_24127 : real) (_24128 : real) (_24129 : real) (_24130 : real) : (term205 _24127 _24129 _24128 _24130) = (term222 _24127 _24128 _24129 _24130).
Proof. exact (TRANS (@lem1356335 _24127 _24128 _24129 _24130) (@lem1356352 _24127 _24128 _24129 _24130)). Qed.
Lemma lem1356355 (x : real) (_24139 : real) (h1 : term34) : term223 x _24139.
Proof. exact (conj (@lem1356234 x) (@lem1356242 _24139 h1)). Qed.
Lemma lem1356357 (_24127 : real) (_24128 : real) (_24129 : real) (_24130 : real) : term222 _24127 _24128 _24129 _24130.
Proof. exact (EQ_MP (@lem1356353 _24127 _24128 _24129 _24130) (@lem1356332 _24127 _24129 _24128 _24130)). Qed.
Lemma lem1356358 (x : real) (_24139 : real) : term224 x _24139.
Proof. exact (@lem1356357 x (term32 _24139) x _24139). Qed.
Lemma lem1356361 (x : real) (_24139 : real) (h1 : term34) : (term187 x _24139) = (real_mul x _24139).
Proof. exact (@lem1356358 x _24139 (@lem1356355 x _24139 h1)). Qed.
Lemma lem1356362 (x : real) (_24139 : real) (h1 : term34) : term225 x _24139.
Proof. exact (fun h0 : term226 x _24139 => @lem1356361 x _24139 h1). Qed.
Lemma lem1356364 (p : Prop) : (term191 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1356365 (x : real) (_24139 : real) : (term225 x _24139) = ((term187 x _24139) = (real_mul x _24139)).
Proof. exact (@lem1356364 ((term187 x _24139) = (real_mul x _24139))). Qed.
Lemma lem1356366 (x : real) (_24139 : real) (h1 : term34) : (term187 x _24139) = (real_mul x _24139).
Proof. exact (EQ_MP (@lem1356365 x _24139) (@lem1356362 x _24139 h1)). Qed.
Lemma lem1356384 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1356385 (_24135 : real) (_24137 : real) (_24136 : real) (_24138 : real) : (term183 _24135 _24136 _24137 _24138) = (term227 _24135 _24137 _24136 _24138).
Proof. exact (@lem1356384 ((real_add _24135 _24136) = (real_add _24137 _24138)) (term88 _24136 _24138)). Qed.
Lemma lem1356395 (_24135 : real) (_24137 : real) : (term202 _24135 _24137) = (term202 _24135 _24137).
Proof. exact (eq_refl (term202 _24135 _24137)). Qed.
Lemma lem1356396 (_24135 : real) (_24137 : real) (_24136 : real) (_24138 : real) : (term185 _24135 _24136 _24137 _24138) = (term228 _24135 _24137 _24136 _24138).
Proof. exact (MK_COMB (@lem1356395 _24135 _24137) (@lem1356385 _24135 _24137 _24136 _24138)). Qed.
Lemma lem1356400 (q : Prop) (p : Prop) (r : Prop) : (term204 p q r) = (term204 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1356401 (_24135 : real) (_24137 : real) (_24136 : real) (_24138 : real) : (term228 _24135 _24137 _24136 _24138) = (term229 _24135 _24137 _24136 _24138).
Proof. exact (@lem1356400 ((real_add _24135 _24136) = (real_add _24137 _24138)) (term88 _24135 _24137) (term88 _24136 _24138)). Qed.
Lemma lem1356423 (_24135 : real) (_24137 : real) (_24136 : real) (_24138 : real) : (term185 _24135 _24136 _24137 _24138) = (term229 _24135 _24137 _24136 _24138).
Proof. exact (TRANS (@lem1356396 _24135 _24137 _24136 _24138) (@lem1356401 _24135 _24137 _24136 _24138)). Qed.
Lemma lem1356424 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1356425 (_24135 : real) (_24137 : real) (_24136 : real) (_24138 : real) : (term230 _24135 _24136 _24137 _24138) = (term231 _24135 _24137 _24136 _24138).
Proof. exact (MK_COMB (@lem1356424) (@lem1356423 _24135 _24137 _24136 _24138)). Qed.
Lemma lem1356447 (_24135 : real) (_24137 : real) (_24136 : real) (_24138 : real) : (term229 _24135 _24137 _24136 _24138) = (term229 _24135 _24137 _24136 _24138).
Proof. exact (eq_refl (term229 _24135 _24137 _24136 _24138)). Qed.
Lemma lem1356448 (_24135 : real) (_24137 : real) (_24136 : real) (_24138 : real) : ((term185 _24135 _24136 _24137 _24138) = (term229 _24135 _24137 _24136 _24138)) = ((term229 _24135 _24137 _24136 _24138) = (term229 _24135 _24137 _24136 _24138)).
Proof. exact (MK_COMB (@lem1356425 _24135 _24137 _24136 _24138) (@lem1356447 _24135 _24137 _24136 _24138)). Qed.
Lemma lem1356450 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1356451 (x : Prop) : (x = x) = True.
Proof. exact (@lem1356450 Prop x). Qed.
Lemma lem1356452 (_24135 : real) (_24137 : real) (_24136 : real) (_24138 : real) : ((term229 _24135 _24137 _24136 _24138) = (term229 _24135 _24137 _24136 _24138)) = True.
Proof. exact (@lem1356451 (term229 _24135 _24137 _24136 _24138)). Qed.
Lemma lem1356453 (_24135 : real) (_24137 : real) (_24136 : real) (_24138 : real) : ((term185 _24135 _24136 _24137 _24138) = (term229 _24135 _24137 _24136 _24138)) = True.
Proof. exact (TRANS (@lem1356448 _24135 _24137 _24136 _24138) (@lem1356452 _24135 _24137 _24136 _24138)). Qed.
Lemma lem1356454 (_24135 : real) (_24137 : real) (_24136 : real) (_24138 : real) : True = ((term185 _24135 _24136 _24137 _24138) = (term229 _24135 _24137 _24136 _24138)).
Proof. exact (SYM (@lem1356453 _24135 _24137 _24136 _24138)). Qed.
Lemma lem1356455 (_24135 : real) (_24137 : real) (_24136 : real) (_24138 : real) : (term185 _24135 _24136 _24137 _24138) = (term229 _24135 _24137 _24136 _24138).
Proof. exact (EQ_MP (@lem1356454 _24135 _24137 _24136 _24138) (@lem0)). Qed.
Lemma lem1356456 (_24135 : real) (_24137 : real) (_24136 : real) (_24138 : real) : term229 _24135 _24137 _24136 _24138.
Proof. exact (EQ_MP (@lem1356455 _24135 _24137 _24136 _24138) (@lem1356199 _24135 _24136 _24137 _24138)). Qed.
Lemma lem1356458 (b : Prop) (a : Prop) : (a \/ b) = (term208 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1356459 (_24135 : real) (_24136 : real) (_24137 : real) (_24138 : real) : (term229 _24135 _24137 _24136 _24138) = (term232 _24135 _24136 _24137 _24138).
Proof. exact (@lem1356458 (term210 _24135 _24137 _24136 _24138) ((real_add _24135 _24136) = (real_add _24137 _24138))). Qed.
Lemma lem1356461 (a : Prop) (b : Prop) : (term211 a b) = (term212 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1356462 (_24135 : real) (_24137 : real) (_24136 : real) (_24138 : real) : (term213 _24135 _24137 _24136 _24138) = (term214 _24135 _24137 _24136 _24138).
Proof. exact (@lem1356461 (term88 _24135 _24137) (term88 _24136 _24138)). Qed.
Lemma lem1356464 (a : Prop) : (term215 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1356465 (_24135 : real) (_24137 : real) : (term216 _24135 _24137) = (_24135 = _24137).
Proof. exact (@lem1356464 (_24135 = _24137)). Qed.
Lemma lem1356466 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1356467 (_24135 : real) (_24137 : real) : (term217 _24135 _24137) = (term218 _24135 _24137).
Proof. exact (MK_COMB (@lem1356466) (@lem1356465 _24135 _24137)). Qed.
Lemma lem1356469 (a : Prop) : (term215 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1356470 (_24136 : real) (_24138 : real) : (term216 _24136 _24138) = (_24136 = _24138).
Proof. exact (@lem1356469 (_24136 = _24138)). Qed.
Lemma lem1356471 (_24135 : real) (_24137 : real) (_24136 : real) (_24138 : real) : (term214 _24135 _24137 _24136 _24138) = (term219 _24135 _24137 _24136 _24138).
Proof. exact (MK_COMB (@lem1356467 _24135 _24137) (@lem1356470 _24136 _24138)). Qed.
Lemma lem1356472 (_24135 : real) (_24137 : real) (_24136 : real) (_24138 : real) : (term213 _24135 _24137 _24136 _24138) = (term219 _24135 _24137 _24136 _24138).
Proof. exact (TRANS (@lem1356462 _24135 _24137 _24136 _24138) (@lem1356471 _24135 _24137 _24136 _24138)). Qed.
Lemma lem1356473 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1356474 (_24135 : real) (_24137 : real) (_24136 : real) (_24138 : real) : (term220 _24135 _24137 _24136 _24138) = (term221 _24135 _24137 _24136 _24138).
Proof. exact (MK_COMB (@lem1356473) (@lem1356472 _24135 _24137 _24136 _24138)). Qed.
Lemma lem1356475 (_24135 : real) (_24136 : real) (_24137 : real) (_24138 : real) : ((real_add _24135 _24136) = (real_add _24137 _24138)) = ((real_add _24135 _24136) = (real_add _24137 _24138)).
Proof. exact (eq_refl ((real_add _24135 _24136) = (real_add _24137 _24138))). Qed.
Lemma lem1356476 (_24135 : real) (_24136 : real) (_24137 : real) (_24138 : real) : (term232 _24135 _24136 _24137 _24138) = (term233 _24135 _24136 _24137 _24138).
Proof. exact (MK_COMB (@lem1356474 _24135 _24137 _24136 _24138) (@lem1356475 _24135 _24136 _24137 _24138)). Qed.
Lemma lem1356477 (_24135 : real) (_24136 : real) (_24137 : real) (_24138 : real) : (term229 _24135 _24137 _24136 _24138) = (term233 _24135 _24136 _24137 _24138).
Proof. exact (TRANS (@lem1356459 _24135 _24136 _24137 _24138) (@lem1356476 _24135 _24136 _24137 _24138)). Qed.
Lemma lem1356479 (x : real) (_24139 : real) (h1 : term34) : term234 x _24139.
Proof. exact (conj (@lem1356227) (@lem1356366 x _24139 h1)). Qed.
Lemma lem1356481 (_24135 : real) (_24136 : real) (_24137 : real) (_24138 : real) : term233 _24135 _24136 _24137 _24138.
Proof. exact (EQ_MP (@lem1356477 _24135 _24136 _24137 _24138) (@lem1356456 _24135 _24137 _24136 _24138)). Qed.
Lemma lem1356482 (x : real) (_24139 : real) : term235 x _24139.
Proof. exact (@lem1356481 term36 (term187 x _24139) term36 (real_mul x _24139)). Qed.
Lemma lem1356485 (x : real) (_24139 : real) (h1 : term34) : (term192 x _24139) = (term236 x _24139).
Proof. exact (@lem1356482 x _24139 (@lem1356479 x _24139 h1)). Qed.
Lemma lem1356486 (x : real) (_24139 : real) (h1 : term34) : term237 x _24139.
Proof. exact (fun h0 : term238 x _24139 => @lem1356485 x _24139 h1). Qed.
Lemma lem1356488 (p : Prop) : (term191 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1356489 (x : real) (_24139 : real) : (term237 x _24139) = ((term192 x _24139) = (term236 x _24139)).
Proof. exact (@lem1356488 ((term192 x _24139) = (term236 x _24139))). Qed.
Lemma lem1356490 (x : real) (_24139 : real) (h1 : term34) : (term192 x _24139) = (term236 x _24139).
Proof. exact (EQ_MP (@lem1356489 x _24139) (@lem1356486 x _24139 h1)). Qed.
Lemma lem1356508 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1356509 (y : real) (x : real) (z : real) : (term239 x y z) = (term240 y x z).
Proof. exact (@lem1356508 (y = z) (term88 x z)). Qed.
Lemma lem1356519 (x : real) (y : real) : (term202 x y) = (term202 x y).
Proof. exact (eq_refl (term202 x y)). Qed.
Lemma lem1356520 (y : real) (x : real) (z : real) : (term186 x y z) = (term241 y x z).
Proof. exact (MK_COMB (@lem1356519 x y) (@lem1356509 y x z)). Qed.
Lemma lem1356524 (q : Prop) (p : Prop) (r : Prop) : (term204 p q r) = (term204 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1356525 (y : real) (x : real) (z : real) : (term241 y x z) = (term242 y x z).
Proof. exact (@lem1356524 (y = z) (term88 x y) (term88 x z)). Qed.
Lemma lem1356547 (y : real) (x : real) (z : real) : (term186 x y z) = (term242 y x z).
Proof. exact (TRANS (@lem1356520 y x z) (@lem1356525 y x z)). Qed.
Lemma lem1356548 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1356549 (y : real) (x : real) (z : real) : (term243 x y z) = (term244 y x z).
Proof. exact (MK_COMB (@lem1356548) (@lem1356547 y x z)). Qed.
Lemma lem1356571 (y : real) (x : real) (z : real) : (term242 y x z) = (term242 y x z).
Proof. exact (eq_refl (term242 y x z)). Qed.
Lemma lem1356572 (y : real) (x : real) (z : real) : ((term186 x y z) = (term242 y x z)) = ((term242 y x z) = (term242 y x z)).
Proof. exact (MK_COMB (@lem1356549 y x z) (@lem1356571 y x z)). Qed.
Lemma lem1356574 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1356575 (x : Prop) : (x = x) = True.
Proof. exact (@lem1356574 Prop x). Qed.
Lemma lem1356576 (y : real) (x : real) (z : real) : ((term242 y x z) = (term242 y x z)) = True.
Proof. exact (@lem1356575 (term242 y x z)). Qed.
Lemma lem1356577 (y : real) (x : real) (z : real) : ((term186 x y z) = (term242 y x z)) = True.
Proof. exact (TRANS (@lem1356572 y x z) (@lem1356576 y x z)). Qed.
Lemma lem1356578 (y : real) (x : real) (z : real) : True = ((term186 x y z) = (term242 y x z)).
Proof. exact (SYM (@lem1356577 y x z)). Qed.
Lemma lem1356579 (y : real) (x : real) (z : real) : (term186 x y z) = (term242 y x z).
Proof. exact (EQ_MP (@lem1356578 y x z) (@lem0)). Qed.
Lemma lem1356580 (y : real) (x : real) (z : real) : term242 y x z.
Proof. exact (EQ_MP (@lem1356579 y x z) (@lem1356201 x y z)). Qed.
Lemma lem1356582 (b : Prop) (a : Prop) : (a \/ b) = (term208 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1356583 (x : real) (y : real) (z : real) : (term242 y x z) = (term245 x y z).
Proof. exact (@lem1356582 (term246 y x z) (y = z)). Qed.
Lemma lem1356585 (a : Prop) (b : Prop) : (term211 a b) = (term212 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1356586 (y : real) (x : real) (z : real) : (term247 y x z) = (term248 y x z).
Proof. exact (@lem1356585 (term88 x y) (term88 x z)). Qed.
Lemma lem1356588 (a : Prop) : (term215 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1356589 (x : real) (y : real) : (term216 x y) = (x = y).
Proof. exact (@lem1356588 (x = y)). Qed.
Lemma lem1356590 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1356591 (x : real) (y : real) : (term217 x y) = (term218 x y).
Proof. exact (MK_COMB (@lem1356590) (@lem1356589 x y)). Qed.
Lemma lem1356593 (a : Prop) : (term215 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1356594 (x : real) (z : real) : (term216 x z) = (x = z).
Proof. exact (@lem1356593 (x = z)). Qed.
Lemma lem1356595 (y : real) (x : real) (z : real) : (term248 y x z) = (term249 y x z).
Proof. exact (MK_COMB (@lem1356591 x y) (@lem1356594 x z)). Qed.
Lemma lem1356596 (y : real) (x : real) (z : real) : (term247 y x z) = (term249 y x z).
Proof. exact (TRANS (@lem1356586 y x z) (@lem1356595 y x z)). Qed.
Lemma lem1356597 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1356598 (y : real) (x : real) (z : real) : (term250 y x z) = (term251 y x z).
Proof. exact (MK_COMB (@lem1356597) (@lem1356596 y x z)). Qed.
Lemma lem1356599 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1356600 (x : real) (y : real) (z : real) : (term245 x y z) = (term252 x y z).
Proof. exact (MK_COMB (@lem1356598 y x z) (@lem1356599 y z)). Qed.
Lemma lem1356601 (x : real) (y : real) (z : real) : (term242 y x z) = (term252 x y z).
Proof. exact (TRANS (@lem1356583 x y z) (@lem1356600 x y z)). Qed.
Lemma lem1356603 (x : real) (_24139 : real) (h1 : term34) : term253 x _24139.
Proof. exact (conj (@lem1356219 x _24139 h1) (@lem1356490 x _24139 h1)). Qed.
Lemma lem1356605 (x : real) (y : real) (z : real) : term252 x y z.
Proof. exact (EQ_MP (@lem1356601 x y z) (@lem1356580 y x z)). Qed.
Lemma lem1356606 (x : real) (_24139 : real) : term254 x _24139.
Proof. exact (@lem1356605 (term192 x _24139) (term187 x _24139) (term236 x _24139)). Qed.
Lemma lem1356609 (x : real) (_24139 : real) (h1 : term34) : (term187 x _24139) = (term236 x _24139).
Proof. exact (@lem1356606 x _24139 (@lem1356603 x _24139 h1)). Qed.
Lemma lem1356610 (x : real) (_24139 : real) (h1 : term34) : term255 x _24139.
Proof. exact (fun h0 : term256 x _24139 => @lem1356609 x _24139 h1). Qed.
Lemma lem1356612 (p : Prop) : (term191 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1356613 (x : real) (_24139 : real) : (term255 x _24139) = ((term187 x _24139) = (term236 x _24139)).
Proof. exact (@lem1356612 ((term187 x _24139) = (term236 x _24139))). Qed.
Lemma lem1356614 (x : real) (_24139 : real) (h1 : term34) : (term187 x _24139) = (term236 x _24139).
Proof. exact (EQ_MP (@lem1356613 x _24139) (@lem1356610 x _24139 h1)). Qed.
Lemma lem1356615 (x : real) (_24139 : real) (h1 : term31) (h2 : term34) : term257 x _24139.
Proof. exact (conj (@lem1356211 x _24139 h1) (@lem1356614 x _24139 h2)). Qed.
Lemma lem1356617 (x : real) (y : real) (z : real) : term252 x y z.
Proof. exact (EQ_MP (@lem1356601 x y z) (@lem1356580 y x z)). Qed.
Lemma lem1356618 (x : real) (_24139 : real) : term258 x _24139.
Proof. exact (@lem1356617 (term187 x _24139) (term188 x _24139) (term236 x _24139)). Qed.
Lemma lem1356621 (x : real) (_24139 : real) (h1 : term31) (h2 : term34) : (term188 x _24139) = (term236 x _24139).
Proof. exact (@lem1356618 x _24139 (@lem1356615 x _24139 h1 h2)). Qed.
Lemma lem1356622 (x : real) (_24139 : real) (h1 : term31) (h2 : term34) : term259 x _24139.
Proof. exact (fun h0 : term260 x _24139 => @lem1356621 x _24139 h1 h2). Qed.
Lemma lem1356624 (p : Prop) : (term191 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1356625 (x : real) (_24139 : real) : (term259 x _24139) = ((term188 x _24139) = (term236 x _24139)).
Proof. exact (@lem1356624 ((term188 x _24139) = (term236 x _24139))). Qed.
Lemma lem1356626 (x : real) (_24139 : real) (h1 : term31) (h2 : term34) : (term188 x _24139) = (term236 x _24139).
Proof. exact (EQ_MP (@lem1356625 x _24139) (@lem1356622 x _24139 h1 h2)). Qed.
Lemma lem1356632 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1356633 (_24124 : real) (_24125 : real) (_24126 : real) : (term67 _24126 _24124 _24125) = (term261 _24124 _24125 _24126).
Proof. exact (@lem1356632 (_24124 = _24125) (term107 _24124 _24125 _24126)). Qed.
Lemma lem1356643 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1356644 (_24124 : real) (_24125 : real) (_24126 : real) : (term262 _24126 _24124 _24125) = (term263 _24124 _24125 _24126).
Proof. exact (MK_COMB (@lem1356643) (@lem1356633 _24124 _24125 _24126)). Qed.
Lemma lem1356654 (_24124 : real) (_24125 : real) (_24126 : real) : (term261 _24124 _24125 _24126) = (term261 _24124 _24125 _24126).
Proof. exact (eq_refl (term261 _24124 _24125 _24126)). Qed.
Lemma lem1356655 (_24124 : real) (_24125 : real) (_24126 : real) : ((term67 _24126 _24124 _24125) = (term261 _24124 _24125 _24126)) = ((term261 _24124 _24125 _24126) = (term261 _24124 _24125 _24126)).
Proof. exact (MK_COMB (@lem1356644 _24124 _24125 _24126) (@lem1356654 _24124 _24125 _24126)). Qed.
Lemma lem1356657 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1356658 (x : Prop) : (x = x) = True.
Proof. exact (@lem1356657 Prop x). Qed.
Lemma lem1356659 (_24124 : real) (_24125 : real) (_24126 : real) : ((term261 _24124 _24125 _24126) = (term261 _24124 _24125 _24126)) = True.
Proof. exact (@lem1356658 (term261 _24124 _24125 _24126)). Qed.
Lemma lem1356660 (_24124 : real) (_24125 : real) (_24126 : real) : ((term67 _24126 _24124 _24125) = (term261 _24124 _24125 _24126)) = True.
Proof. exact (TRANS (@lem1356655 _24124 _24125 _24126) (@lem1356659 _24124 _24125 _24126)). Qed.
Lemma lem1356661 (_24124 : real) (_24125 : real) (_24126 : real) : True = ((term67 _24126 _24124 _24125) = (term261 _24124 _24125 _24126)).
Proof. exact (SYM (@lem1356660 _24124 _24125 _24126)). Qed.
Lemma lem1356662 (_24124 : real) (_24125 : real) (_24126 : real) : (term67 _24126 _24124 _24125) = (term261 _24124 _24125 _24126).
Proof. exact (EQ_MP (@lem1356661 _24124 _24125 _24126) (@lem0)). Qed.
Lemma lem1356663 (_24124 : real) (_24125 : real) (_24126 : real) (h1 : term10) : term261 _24124 _24125 _24126.
Proof. exact (EQ_MP (@lem1356662 _24124 _24125 _24126) (@lem1356153 _24126 _24124 _24125 h1)). Qed.
Lemma lem1356665 (b : Prop) (a : Prop) : (a \/ b) = (term208 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1356666 (_24126 : real) (_24124 : real) (_24125 : real) : (term261 _24124 _24125 _24126) = (term264 _24126 _24124 _24125).
Proof. exact (@lem1356665 (term107 _24124 _24125 _24126) (_24124 = _24125)). Qed.
Lemma lem1356668 (a : Prop) : (term215 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1356669 (_24124 : real) (_24125 : real) (_24126 : real) : (term265 _24124 _24125 _24126) = ((real_add _24124 _24126) = (real_add _24125 _24126)).
Proof. exact (@lem1356668 ((real_add _24124 _24126) = (real_add _24125 _24126))). Qed.
Lemma lem1356670 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1356671 (_24124 : real) (_24125 : real) (_24126 : real) : (term266 _24124 _24125 _24126) = (term267 _24124 _24125 _24126).
Proof. exact (MK_COMB (@lem1356670) (@lem1356669 _24124 _24125 _24126)). Qed.
Lemma lem1356672 (_24124 : real) (_24125 : real) : (_24124 = _24125) = (_24124 = _24125).
Proof. exact (eq_refl (_24124 = _24125)). Qed.
Lemma lem1356673 (_24126 : real) (_24124 : real) (_24125 : real) : (term264 _24126 _24124 _24125) = (term268 _24126 _24124 _24125).
Proof. exact (MK_COMB (@lem1356671 _24124 _24125 _24126) (@lem1356672 _24124 _24125)). Qed.
Lemma lem1356674 (_24126 : real) (_24124 : real) (_24125 : real) : (term261 _24124 _24125 _24126) = (term268 _24126 _24124 _24125).
Proof. exact (TRANS (@lem1356666 _24126 _24124 _24125) (@lem1356673 _24126 _24124 _24125)). Qed.
Lemma lem1356677 (_24126 : real) (_24124 : real) (_24125 : real) (h1 : term10) : term268 _24126 _24124 _24125.
Proof. exact (EQ_MP (@lem1356674 _24126 _24124 _24125) (@lem1356663 _24124 _24125 _24126 h1)). Qed.
Lemma lem1356678 (_24139 : real) (x : real) (h1 : term10) : term269 _24139 x.
Proof. exact (@lem1356677 (real_mul x _24139) (term35 x) term36 h1). Qed.
Lemma lem1356681 (x : real) (h1 : term10) (h2 : term31) (h3 : term34) : (term35 x) = term36.
Proof. exact (@lem1356678 (@el real) x h1 (@lem1356626 x (@el real) h2 h3)). Qed.
Lemma lem1356682 (x : real) (h1 : term10) (h2 : term31) (h3 : term34) : term270 x.
Proof. exact (fun h0 : term43 x => @lem1356681 x h1 h2 h3). Qed.
Lemma lem1356684 (p : Prop) : (term191 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1356685 (x : real) : (term270 x) = ((term35 x) = term36).
Proof. exact (@lem1356684 ((term35 x) = term36)). Qed.
Lemma lem1356686 (x : real) (h1 : term10) (h2 : term31) (h3 : term34) : (term35 x) = term36.
Proof. exact (EQ_MP (@lem1356685 x) (@lem1356682 x h1 h2 h3)). Qed.
Lemma lem1356689 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1356691 (x : real) : (term43 x) = (term271 x).
Proof. exact (@lem1356689 ((term35 x) = term36)). Qed.
Lemma lem1356694 (x : real) (h1 : term43 x) : term271 x.
Proof. exact (EQ_MP (@lem1356691 x) (@lem1356141 x h1)). Qed.
Lemma lem1356697 (x : real) (h1 : term10) (h2 : term31) (h3 : term34) (h4 : term43 x) : False.
Proof. exact (@lem1356694 x h4 (@lem1356686 x h1 h2 h3)). Qed.
Lemma lem1356698 (x : real) (h1 : term10) (h2 : term31) (h3 : term34) (h4 : term43 x) : term272.
Proof. exact (fun h0 : ~ False => @lem1356697 x h1 h2 h3 h4). Qed.
Lemma lem1356700 (p : Prop) : (term191 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1356701 : term272 = False.
Proof. exact (@lem1356700 False). Qed.
Lemma lem1356702 (x : real) (h1 : term10) (h2 : term31) (h3 : term34) (h4 : term43 x) : False.
Proof. exact (EQ_MP (@lem1356701) (@lem1356698 x h1 h2 h3 h4)). Qed.
Lemma lem1356703 (x : real) (h1 : term10) (h2 : term31) (h3 : term34) (h4 : term43 x) : (term43 x) = False.
Proof. exact (prop_ext (fun h5 : term43 x => @lem1356702 x h1 h2 h3 h4) (fun h5 : False => @lem1356141 x h4)). Qed.
Lemma lem1356704 (x : real) (h1 : term10) (h2 : term31) (h3 : term34) (h4 : term43 x) : False.
Proof. exact (EQ_MP (@lem1356703 x h1 h2 h3 h4) (@lem1356141 x h4)). Qed.
Lemma lem1356705 (x : real) (h1 : term10) (h2 : term31) (h3 : term34) (h4 : term43 x) : (term43 x) = False.
Proof. exact (prop_ext (fun h5 : term43 x => @lem1356704 x h1 h2 h3 h4) (fun h5 : False => @lem1356009 x h4)). Qed.
Lemma lem1356706 (x : real) (h1 : term10) (h2 : term31) (h3 : term34) (h4 : term43 x) : False.
Proof. exact (EQ_MP (@lem1356705 x h1 h2 h3 h4) (@lem1356009 x h4)). Qed.
Lemma lem1356707 (x : real) (h1 : term10) (h2 : term31) (h3 : term34) (h4 : term43 x) : (term43 x) = False.
Proof. exact (prop_ext (fun h5 : term43 x => @lem1356706 x h1 h2 h3 h4) (fun h5 : False => @lem1356009 x h4)). Qed.
Lemma lem1356708 (x : real) (h1 : term10) (h2 : term31) (h3 : term34) (h4 : term43 x) : False.
Proof. exact (EQ_MP (@lem1356707 x h1 h2 h3 h4) (@lem1356009 x h4)). Qed.
Lemma lem1356709 (x : real) (h1 : term10) (h2 : term31) (h3 : term34) (h4 : term43 x) : term31 = False.
Proof. exact (prop_ext (fun h5 : term31 => @lem1356708 x h1 h2 h3 h4) (fun h5 : False => @lem1356005 h2)). Qed.
Lemma lem1356710 (x : real) (h1 : term10) (h2 : term31) (h3 : term34) (h4 : term43 x) : False.
Proof. exact (EQ_MP (@lem1356709 x h1 h2 h3 h4) (@lem1356005 h2)). Qed.
Lemma lem1356711 (x : real) (h1 : term10) (h2 : term31) (h3 : term34) (h4 : term43 x) : term34 = False.
Proof. exact (prop_ext (fun h5 : term34 => @lem1356710 x h1 h2 h3 h4) (fun h5 : False => @lem1355992 h3)). Qed.
Lemma lem1356712 (x : real) (h1 : term10) (h2 : term31) (h3 : term34) (h4 : term43 x) : False.
Proof. exact (EQ_MP (@lem1356711 x h1 h2 h3 h4) (@lem1355992 h3)). Qed.
Lemma lem1356713 (x : real) (h1 : term10) (h2 : term31) (h3 : term34) (h4 : term43 x) : (term43 x) = False.
Proof. exact (prop_ext (fun h5 : term43 x => @lem1356712 x h1 h2 h3 h4) (fun h5 : False => @lem1355983 x h4)). Qed.
Lemma lem1356714 (x : real) (h1 : term10) (h2 : term31) (h3 : term34) (h4 : term43 x) : False.
Proof. exact (EQ_MP (@lem1356713 x h1 h2 h3 h4) (@lem1355983 x h4)). Qed.
Lemma lem1356715 (x : real) (h1 : term10) (h2 : term31) (h3 : term34) (h4 : term43 x) : term31 = False.
Proof. exact (prop_ext (fun h5 : term31 => @lem1356714 x h1 h2 h3 h4) (fun h5 : False => @lem1355895 h2)). Qed.
Lemma lem1356716 (x : real) (h1 : term10) (h2 : term31) (h3 : term34) (h4 : term43 x) : False.
Proof. exact (EQ_MP (@lem1356715 x h1 h2 h3 h4) (@lem1355895 h2)). Qed.
Lemma lem1356717 (x : real) (h1 : term10) (h2 : term31) (h3 : term34) (h4 : term43 x) : term34 = False.
Proof. exact (prop_ext (fun h5 : term34 => @lem1356716 x h1 h2 h3 h4) (fun h5 : False => @lem1355860 h3)). Qed.
Lemma lem1356718 (x : real) (h1 : term10) (h2 : term31) (h3 : term34) (h4 : term43 x) : False.
Proof. exact (EQ_MP (@lem1356717 x h1 h2 h3 h4) (@lem1355860 h3)). Qed.
Lemma lem1356719 (h1 : term10) (h2 : term31) (h3 : term34) (h4 : term3) : False.
Proof. exact (ex_elim (@lem1355361 h4) (fun x : real => fun h0 : term45 x => @lem1356718 x h1 h2 h3 h0)). Qed.
Lemma lem1356720 (h1 : term10) (h2 : term31) (h3 : term34) (h4 : term3) : term31 = False.
Proof. exact (prop_ext (fun h5 : term31 => @lem1356719 h1 h2 h3 h4) (fun h5 : False => @lem1355401 h2)). Qed.
Lemma lem1356721 (h1 : term10) (h2 : term31) (h3 : term34) (h4 : term3) : False.
Proof. exact (EQ_MP (@lem1356720 h1 h2 h3 h4) (@lem1355401 h2)). Qed.
Lemma lem1356722 (h1 : term10) (h2 : term31) (h3 : term34) (h4 : term3) : term34 = False.
Proof. exact (prop_ext (fun h5 : term34 => @lem1356721 h1 h2 h3 h4) (fun h5 : False => @lem1355374 h3)). Qed.
Lemma lem1356723 (h1 : term10) (h2 : term31) (h3 : term34) (h4 : term3) : False.
Proof. exact (EQ_MP (@lem1356722 h1 h2 h3 h4) (@lem1355374 h3)). Qed.
Lemma lem1356724 (h1 : term31) (h2 : term34) (h3 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1356723 h0 h1 h2 h3). Qed.
Lemma lem1356725 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1356726 (h1 : term31) (h2 : term34) (h3 : term3) : term9.
Proof. exact (EQ_MP (@lem1356725) (@lem1356724 h1 h2 h3)). Qed.
Lemma lem1356727 (h1 : term34) (h2 : term3) : term13.
Proof. exact (fun h0 : term31 => @lem1356726 h0 h1 h2). Qed.
Lemma lem1356728 (h1 : term3) : term16.
Proof. exact (fun h0 : term34 => @lem1356727 h0 h1). Qed.
Lemma lem1356729 : term18.
Proof. exact (fun h0 : term3 => @lem1356728 h0). Qed.
Lemma lem1356730 : term4.
Proof. exact (EQ_MP (@lem1355337) (@lem1356729)). Qed.
Lemma lem1356732 : term4.
Proof. exact (@lem1355177 (@lem1356730)). Qed.
Lemma lem1356733 (h1 : term3) : term15.
Proof. exact (@lem1356732 (@lem1355162 h1)). Qed.
Lemma lem1356734 (h1 : term3) : term12.
Proof. exact (@lem1356733 h1 (@lem1338512)). Qed.
Lemma lem1356735 (h1 : term3) : term8.
Proof. exact (@lem1356734 h1 (@lem1339188)). Qed.
Lemma lem1356736 (h1 : term3) : False.
Proof. exact (@lem1356735 h1 (@lem1355147)). Qed.
Lemma lem1356737 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1356736 h1) (fun h2 : False => @lem1355162 h1)). Qed.
Lemma lem1356738 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1356737 h1) (@lem1355162 h1)). Qed.
Lemma lem1356739 : term2.
Proof. exact (fun h0 : term3 => @lem1356738 h0). Qed.
Lemma lem1356740 : term1.
Proof. exact (EQ_MP (@lem1355161) (@lem1356739)). Qed.
