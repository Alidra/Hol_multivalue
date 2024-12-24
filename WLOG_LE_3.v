Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WLOG_LE_3_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import LE_CASES_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
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
Lemma lem111143 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem111144 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem111145 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem111144 t1) (@lem111143 t1)). Qed.
Lemma lem111146 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem111145 t1 t2). Qed.
Lemma lem111147 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem111148 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem111147 t1 t2) (@lem111146 t1 t2)). Qed.
Lemma lem111149 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem111148 t1 t2 t3). Qed.
Lemma lem111150 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem111151 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem111150 t1 t2 t3) (@lem111149 t1 t2 t3)). Qed.
Lemma lem111152 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem111151 t1 t2 t3)). Qed.
Lemma lem111154 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem111155 : term8 = term9.
Proof. exact (@lem111154 term8). Qed.
Lemma lem111156 : term9 = term8.
Proof. exact (SYM (@lem111155)). Qed.
Lemma lem111157 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem111160 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem111161 : term12.
Proof. exact (fun h0 : term11 => @lem111160 h0). Qed.
Lemma lem111162 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem111163 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem111164 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem111162 h2 (@lem111163 h1)). Qed.
Lemma lem111165 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem111164 h1 h0). Qed.
Lemma lem111166 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem111167 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem111165 h1 (@lem111166 h2)). Qed.
Lemma lem111168 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem111167 h0 h1). Qed.
Lemma lem111169 : term14.
Proof. exact (fun h0 : term12 => @lem111168 h0). Qed.
Lemma lem111172 : term12.
Proof. exact (@lem111169 (@lem111161)). Qed.
Lemma lem111228 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem111229 : term15 = term16.
Proof. exact (@lem111228 term17). Qed.
Lemma lem111284 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem111291 : term11 = term19.
Proof. exact (MK_COMB (@lem111284) (@lem111229)). Qed.
Lemma lem111296 (n : nat) (m : nat) : (term20 n m) = (term20 n m).
Proof. exact (eq_refl (term20 n m)). Qed.
Lemma lem111297 (m : nat) : (term21 m) = (term21 m).
Proof. exact (fun_ext (fun n : nat => @lem111296 n m)). Qed.
Lemma lem111298 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111299 (m : nat) : (term22 m) = (term22 m).
Proof. exact (MK_COMB (@lem111298) (@lem111297 m)). Qed.
Lemma lem111300 : term23 = term23.
Proof. exact (fun_ext (fun m : nat => @lem111299 m)). Qed.
Lemma lem111301 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111302 : term17 = term17.
Proof. exact (MK_COMB (@lem111301) (@lem111300)). Qed.
Lemma lem111303 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem111304 : term16 = term16.
Proof. exact (MK_COMB (@lem111303) (@lem111302)). Qed.
Lemma lem111305 (P : type1601) (x : nat) (y : nat) (z : nat) : (P x y z) = (P x y z).
Proof. exact (eq_refl (P x y z)). Qed.
Lemma lem111306 (P : type1601) (x : nat) (y : nat) : (term24 P x y) = (term24 P x y).
Proof. exact (fun_ext (fun z : nat => @lem111305 P x y z)). Qed.
Lemma lem111307 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111308 (P : type1601) (x : nat) (y : nat) : (term25 P x y) = (term25 P x y).
Proof. exact (MK_COMB (@lem111307) (@lem111306 P x y)). Qed.
Lemma lem111309 (P : type1601) (x : nat) : (term26 P x) = (term26 P x).
Proof. exact (fun_ext (fun y : nat => @lem111308 P x y)). Qed.
Lemma lem111310 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111311 (P : type1601) (x : nat) : (term27 P x) = (term27 P x).
Proof. exact (MK_COMB (@lem111310) (@lem111309 P x)). Qed.
Lemma lem111312 (P : type1601) : (term28 P) = (term28 P).
Proof. exact (fun_ext (fun x : nat => @lem111311 P x)). Qed.
Lemma lem111313 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111314 (P : type1601) : (term29 P) = (term29 P).
Proof. exact (MK_COMB (@lem111313) (@lem111312 P)). Qed.
Lemma lem111323 (P : type1601) (x : nat) (y : nat) (z : nat) : (term30 P x y z) = (term30 P x y z).
Proof. exact (eq_refl (term30 P x y z)). Qed.
Lemma lem111324 (P : type1601) (x : nat) (y : nat) : (term31 P x y) = (term31 P x y).
Proof. exact (fun_ext (fun z : nat => @lem111323 P x y z)). Qed.
Lemma lem111325 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111326 (P : type1601) (x : nat) (y : nat) : (term32 P x y) = (term32 P x y).
Proof. exact (MK_COMB (@lem111325) (@lem111324 P x y)). Qed.
Lemma lem111327 (P : type1601) (x : nat) : (term33 P x) = (term33 P x).
Proof. exact (fun_ext (fun y : nat => @lem111326 P x y)). Qed.
Lemma lem111328 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111329 (P : type1601) (x : nat) : (term34 P x) = (term34 P x).
Proof. exact (MK_COMB (@lem111328) (@lem111327 P x)). Qed.
Lemma lem111330 (P : type1601) : (term35 P) = (term35 P).
Proof. exact (fun_ext (fun x : nat => @lem111329 P x)). Qed.
Lemma lem111331 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111332 (P : type1601) : (term36 P) = (term36 P).
Proof. exact (MK_COMB (@lem111331) (@lem111330 P)). Qed.
Lemma lem111341 (P : type1601) (x : nat) (z : nat) (y : nat) : (term37 P x z y) = (term37 P x z y).
Proof. exact (eq_refl (term37 P x z y)). Qed.
Lemma lem111342 (P : type1601) (x : nat) (y : nat) : (term38 P x y) = (term38 P x y).
Proof. exact (fun_ext (fun z : nat => @lem111341 P x z y)). Qed.
Lemma lem111343 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111344 (P : type1601) (x : nat) (y : nat) : (term39 P x y) = (term39 P x y).
Proof. exact (MK_COMB (@lem111343) (@lem111342 P x y)). Qed.
Lemma lem111345 (P : type1601) (x : nat) : (term40 P x) = (term40 P x).
Proof. exact (fun_ext (fun y : nat => @lem111344 P x y)). Qed.
Lemma lem111346 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111347 (P : type1601) (x : nat) : (term41 P x) = (term41 P x).
Proof. exact (MK_COMB (@lem111346) (@lem111345 P x)). Qed.
Lemma lem111348 (P : type1601) : (term42 P) = (term42 P).
Proof. exact (fun_ext (fun x : nat => @lem111347 P x)). Qed.
Lemma lem111349 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111350 (P : type1601) : (term43 P) = (term43 P).
Proof. exact (MK_COMB (@lem111349) (@lem111348 P)). Qed.
Lemma lem111351 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem111352 (P : type1601) : (term44 P) = (term44 P).
Proof. exact (MK_COMB (@lem111351) (@lem111350 P)). Qed.
Lemma lem111353 (P : type1601) : (term45 P) = (term45 P).
Proof. exact (MK_COMB (@lem111352 P) (@lem111332 P)). Qed.
Lemma lem111354 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem111355 (P : type1601) : (term46 P) = (term46 P).
Proof. exact (MK_COMB (@lem111354) (@lem111353 P)). Qed.
Lemma lem111356 (P : type1601) : (term47 P) = (term47 P).
Proof. exact (MK_COMB (@lem111355 P) (@lem111314 P)). Qed.
Lemma lem111357 : term48 = term48.
Proof. exact (fun_ext (fun P : type1601 => @lem111356 P)). Qed.
Lemma lem111358 : (@all (nat -> nat -> nat -> Prop)) = (@all (nat -> nat -> nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> nat -> nat -> Prop))). Qed.
Lemma lem111359 : term8 = term8.
Proof. exact (MK_COMB (@lem111358) (@lem111357)). Qed.
Lemma lem111360 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem111361 : term10 = term10.
Proof. exact (MK_COMB (@lem111360) (@lem111359)). Qed.
Lemma lem111362 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem111363 : term18 = term18.
Proof. exact (MK_COMB (@lem111362) (@lem111361)). Qed.
Lemma lem111364 : term19 = term19.
Proof. exact (MK_COMB (@lem111363) (@lem111304)). Qed.
Lemma lem111455 : term11 = term19.
Proof. exact (TRANS (@lem111291) (@lem111364)). Qed.
Lemma lem111456 : term19 = term11.
Proof. exact (SYM (@lem111455)). Qed.
Lemma lem111457 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem111458 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem111469 (P : type1601) (x : nat) (z : nat) (y : nat) : (term37 P x z y) = (term49 P x z y).
Proof. exact (@lem17265 (P x y z) (term50 P x z y)). Qed.
Lemma lem111470 (P : type1601) (x : nat) (y : nat) : (term38 P x y) = (term51 P x y).
Proof. exact (fun_ext (fun z : nat => @lem111469 P x z y)). Qed.
Lemma lem111471 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111472 (P : type1601) (x : nat) (y : nat) : (term39 P x y) = (term52 P x y).
Proof. exact (MK_COMB (@lem111471) (@lem111470 P x y)). Qed.
Lemma lem111473 (P : type1601) (x : nat) : (term40 P x) = (term53 P x).
Proof. exact (fun_ext (fun y : nat => @lem111472 P x y)). Qed.
Lemma lem111474 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111475 (P : type1601) (x : nat) : (term41 P x) = (term54 P x).
Proof. exact (MK_COMB (@lem111474) (@lem111473 P x)). Qed.
Lemma lem111476 (P : type1601) : (term42 P) = (term55 P).
Proof. exact (fun_ext (fun x : nat => @lem111475 P x)). Qed.
Lemma lem111477 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111478 (P : type1601) : (term43 P) = (term56 P).
Proof. exact (MK_COMB (@lem111477) (@lem111476 P)). Qed.
Lemma lem111485 (x : nat) (y : nat) (z : nat) : (term57 x y z) = (term58 x y z).
Proof. exact (@lem17045 (Peano.le x y) (Peano.le y z)). Qed.
Lemma lem111486 (P : type1601) (x : nat) (y : nat) (z : nat) : (P x y z) = (P x y z).
Proof. exact (eq_refl (P x y z)). Qed.
Lemma lem111487 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem111488 (x : nat) (y : nat) (z : nat) : (term59 x y z) = (term60 x y z).
Proof. exact (MK_COMB (@lem111487) (@lem111485 x y z)). Qed.
Lemma lem111489 (P : type1601) (x : nat) (y : nat) (z : nat) : (term61 P x y z) = (term62 P x y z).
Proof. exact (MK_COMB (@lem111488 x y z) (@lem111486 P x y z)). Qed.
Lemma lem111490 (P : type1601) (x : nat) (y : nat) (z : nat) : (term30 P x y z) = (term61 P x y z).
Proof. exact (@lem17265 (term63 x y z) (P x y z)). Qed.
Lemma lem111491 (P : type1601) (x : nat) (y : nat) (z : nat) : (term30 P x y z) = (term62 P x y z).
Proof. exact (TRANS (@lem111490 P x y z) (@lem111489 P x y z)). Qed.
Lemma lem111492 (P : type1601) (x : nat) (y : nat) : (term31 P x y) = (term64 P x y).
Proof. exact (fun_ext (fun z : nat => @lem111491 P x y z)). Qed.
Lemma lem111493 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111494 (P : type1601) (x : nat) (y : nat) : (term32 P x y) = (term65 P x y).
Proof. exact (MK_COMB (@lem111493) (@lem111492 P x y)). Qed.
Lemma lem111495 (P : type1601) (x : nat) : (term33 P x) = (term66 P x).
Proof. exact (fun_ext (fun y : nat => @lem111494 P x y)). Qed.
Lemma lem111496 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111497 (P : type1601) (x : nat) : (term34 P x) = (term67 P x).
Proof. exact (MK_COMB (@lem111496) (@lem111495 P x)). Qed.
Lemma lem111498 (P : type1601) : (term35 P) = (term68 P).
Proof. exact (fun_ext (fun x : nat => @lem111497 P x)). Qed.
Lemma lem111499 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111500 (P : type1601) : (term36 P) = (term69 P).
Proof. exact (MK_COMB (@lem111499) (@lem111498 P)). Qed.
Lemma lem111501 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem111502 (P : type1601) : (term44 P) = (term70 P).
Proof. exact (MK_COMB (@lem111501) (@lem111478 P)). Qed.
Lemma lem111503 (P : type1601) : (term45 P) = (term71 P).
Proof. exact (MK_COMB (@lem111502 P) (@lem111500 P)). Qed.
Lemma lem111505 (P : nat -> Prop) : (term72 P) = (term73 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem111506 (P : type1601) (x : nat) (y : nat) : (term74 P x y) = (term75 P x y).
Proof. exact (@lem111505 (term24 P x y)). Qed.
Lemma lem111507 (P : type1601) (x : nat) (y : nat) (z : nat) : (term76 P x y z) = (P x y z).
Proof. exact (eq_refl (term76 P x y z)). Qed.
Lemma lem111508 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem111510 (P : type1601) (x : nat) (y : nat) (z : nat) : (term77 P x y z) = (term78 P x y z).
Proof. exact (MK_COMB (@lem111508) (@lem111507 P x y z)). Qed.
Lemma lem111511 (P : type1601) (x : nat) (y : nat) : (term79 P x y) = (term80 P x y).
Proof. exact (fun_ext (fun z : nat => @lem111510 P x y z)). Qed.
Lemma lem111512 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem111513 (P : type1601) (x : nat) (y : nat) : (term75 P x y) = (term81 P x y).
Proof. exact (MK_COMB (@lem111512) (@lem111511 P x y)). Qed.
Lemma lem111514 (P : type1601) (x : nat) (y : nat) : (term74 P x y) = (term81 P x y).
Proof. exact (TRANS (@lem111506 P x y) (@lem111513 P x y)). Qed.
Lemma lem111515 (P : nat -> Prop) : (term72 P) = (term73 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem111516 (P : type1601) (x : nat) : (term82 P x) = (term83 P x).
Proof. exact (@lem111515 (term26 P x)). Qed.
Lemma lem111517 (P : type1601) (x : nat) (y : nat) : (term84 P x y) = (term25 P x y).
Proof. exact (eq_refl (term84 P x y)). Qed.
Lemma lem111518 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem111519 (P : type1601) (x : nat) (y : nat) : (term85 P x y) = (term74 P x y).
Proof. exact (MK_COMB (@lem111518) (@lem111517 P x y)). Qed.
Lemma lem111520 (P : type1601) (x : nat) (y : nat) : (term85 P x y) = (term81 P x y).
Proof. exact (TRANS (@lem111519 P x y) (@lem111514 P x y)). Qed.
Lemma lem111521 (P : type1601) (x : nat) : (term86 P x) = (term87 P x).
Proof. exact (fun_ext (fun y : nat => @lem111520 P x y)). Qed.
Lemma lem111522 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem111523 (P : type1601) (x : nat) : (term83 P x) = (term88 P x).
Proof. exact (MK_COMB (@lem111522) (@lem111521 P x)). Qed.
Lemma lem111524 (P : type1601) (x : nat) : (term82 P x) = (term88 P x).
Proof. exact (TRANS (@lem111516 P x) (@lem111523 P x)). Qed.
Lemma lem111525 (P : nat -> Prop) : (term72 P) = (term73 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem111526 (P : type1601) : (term89 P) = (term90 P).
Proof. exact (@lem111525 (term28 P)). Qed.
Lemma lem111527 (P : type1601) (x : nat) : (term91 P x) = (term27 P x).
Proof. exact (eq_refl (term91 P x)). Qed.
Lemma lem111528 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem111529 (P : type1601) (x : nat) : (term92 P x) = (term82 P x).
Proof. exact (MK_COMB (@lem111528) (@lem111527 P x)). Qed.
Lemma lem111530 (P : type1601) (x : nat) : (term92 P x) = (term88 P x).
Proof. exact (TRANS (@lem111529 P x) (@lem111524 P x)). Qed.
Lemma lem111531 (P : type1601) : (term93 P) = (term94 P).
Proof. exact (fun_ext (fun x : nat => @lem111530 P x)). Qed.
Lemma lem111532 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem111533 (P : type1601) : (term90 P) = (term95 P).
Proof. exact (MK_COMB (@lem111532) (@lem111531 P)). Qed.
Lemma lem111534 (P : type1601) : (term89 P) = (term95 P).
Proof. exact (TRANS (@lem111526 P) (@lem111533 P)). Qed.
Lemma lem111535 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem111536 (P : type1601) : (term96 P) = (term97 P).
Proof. exact (MK_COMB (@lem111535) (@lem111503 P)). Qed.
Lemma lem111537 (P : type1601) : (term98 P) = (term99 P).
Proof. exact (MK_COMB (@lem111536 P) (@lem111534 P)). Qed.
Lemma lem111538 (P : type1601) : (term100 P) = (term98 P).
Proof. exact (@lem17362 (term45 P) (term29 P)). Qed.
Lemma lem111539 (P : type1601) : (term100 P) = (term99 P).
Proof. exact (TRANS (@lem111538 P) (@lem111537 P)). Qed.
Lemma lem111540 (P : type956) : (term101 P) = (term102 P).
Proof. exact (@lem18392 type1601 P). Qed.
Lemma lem111541 : term10 = term103.
Proof. exact (@lem111540 term48). Qed.
Lemma lem111542 (P : type1601) : (term104 P) = (term47 P).
Proof. exact (eq_refl (term104 P)). Qed.
Lemma lem111543 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem111544 (P : type1601) : (term105 P) = (term100 P).
Proof. exact (MK_COMB (@lem111543) (@lem111542 P)). Qed.
Lemma lem111545 (P : type1601) : (term105 P) = (term99 P).
Proof. exact (TRANS (@lem111544 P) (@lem111539 P)). Qed.
Lemma lem111546 : term106 = term107.
Proof. exact (fun_ext (fun P : type1601 => @lem111545 P)). Qed.
Lemma lem111547 : (@ex (nat -> nat -> nat -> Prop)) = (@ex (nat -> nat -> nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat -> Prop))). Qed.
Lemma lem111548 : term103 = term108.
Proof. exact (MK_COMB (@lem111547) (@lem111546)). Qed.
Lemma lem111549 : term10 = term108.
Proof. exact (TRANS (@lem111541) (@lem111548)). Qed.
Lemma lem111724 {A : Type'} (P : Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem111725 (P : Prop) (Q : nat -> Prop) : (term111 P Q) = (term112 P Q).
Proof. exact (@lem111724 nat P Q). Qed.
Lemma lem111726 (P : type1601) : (term113 P) = (term114 P).
Proof. exact (@lem111725 (term71 P) (term94 P)). Qed.
Lemma lem111727 (P : type1601) (x : nat) : (term115 P x) = (term88 P x).
Proof. exact (eq_refl (term115 P x)). Qed.
Lemma lem111728 (P : type1601) : (term116 P) = (term94 P).
Proof. exact (fun_ext (fun x : nat => @lem111727 P x)). Qed.
Lemma lem111729 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem111730 (P : type1601) : (term117 P) = (term95 P).
Proof. exact (MK_COMB (@lem111729) (@lem111728 P)). Qed.
Lemma lem111731 (P : type1601) : (term97 P) = (term97 P).
Proof. exact (eq_refl (term97 P)). Qed.
Lemma lem111732 (P : type1601) : (term113 P) = (term99 P).
Proof. exact (MK_COMB (@lem111731 P) (@lem111730 P)). Qed.
Lemma lem111733 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem111734 (P : type1601) : (term118 P) = (term119 P).
Proof. exact (MK_COMB (@lem111733) (@lem111732 P)). Qed.
Lemma lem111735 (P : type1601) (x : nat) : (term115 P x) = (term88 P x).
Proof. exact (eq_refl (term115 P x)). Qed.
Lemma lem111736 (P : type1601) : (term97 P) = (term97 P).
Proof. exact (eq_refl (term97 P)). Qed.
Lemma lem111737 (P : type1601) (x : nat) : (term120 P x) = (term121 P x).
Proof. exact (MK_COMB (@lem111736 P) (@lem111735 P x)). Qed.
Lemma lem111738 (P : type1601) : (term122 P) = (term123 P).
Proof. exact (fun_ext (fun x : nat => @lem111737 P x)). Qed.
Lemma lem111739 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem111740 (P : type1601) : (term114 P) = (term124 P).
Proof. exact (MK_COMB (@lem111739) (@lem111738 P)). Qed.
Lemma lem111741 (P : type1601) : ((term113 P) = (term114 P)) = ((term99 P) = (term124 P)).
Proof. exact (MK_COMB (@lem111734 P) (@lem111740 P)). Qed.
Lemma lem111742 (P : type1601) : (term99 P) = (term124 P).
Proof. exact (EQ_MP (@lem111741 P) (@lem111726 P)). Qed.
Lemma lem111744 {A : Type'} (P : Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem111745 (P : Prop) (Q : nat -> Prop) : (term111 P Q) = (term112 P Q).
Proof. exact (@lem111744 nat P Q). Qed.
Lemma lem111746 (P : type1601) (x : nat) : (term125 P x) = (term126 P x).
Proof. exact (@lem111745 (term71 P) (term87 P x)). Qed.
Lemma lem111747 (P : type1601) (x : nat) (y : nat) : (term127 P x y) = (term81 P x y).
Proof. exact (eq_refl (term127 P x y)). Qed.
Lemma lem111748 (P : type1601) (x : nat) : (term128 P x) = (term87 P x).
Proof. exact (fun_ext (fun y : nat => @lem111747 P x y)). Qed.
Lemma lem111749 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem111750 (P : type1601) (x : nat) : (term129 P x) = (term88 P x).
Proof. exact (MK_COMB (@lem111749) (@lem111748 P x)). Qed.
Lemma lem111751 (P : type1601) : (term97 P) = (term97 P).
Proof. exact (eq_refl (term97 P)). Qed.
Lemma lem111752 (P : type1601) (x : nat) : (term125 P x) = (term121 P x).
Proof. exact (MK_COMB (@lem111751 P) (@lem111750 P x)). Qed.
Lemma lem111753 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem111754 (P : type1601) (x : nat) : (term130 P x) = (term131 P x).
Proof. exact (MK_COMB (@lem111753) (@lem111752 P x)). Qed.
Lemma lem111755 (P : type1601) (x : nat) (y : nat) : (term127 P x y) = (term81 P x y).
Proof. exact (eq_refl (term127 P x y)). Qed.
Lemma lem111756 (P : type1601) : (term97 P) = (term97 P).
Proof. exact (eq_refl (term97 P)). Qed.
Lemma lem111757 (P : type1601) (x : nat) (y : nat) : (term132 P x y) = (term133 P x y).
Proof. exact (MK_COMB (@lem111756 P) (@lem111755 P x y)). Qed.
Lemma lem111758 (P : type1601) (x : nat) : (term134 P x) = (term135 P x).
Proof. exact (fun_ext (fun y : nat => @lem111757 P x y)). Qed.
Lemma lem111759 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem111760 (P : type1601) (x : nat) : (term126 P x) = (term136 P x).
Proof. exact (MK_COMB (@lem111759) (@lem111758 P x)). Qed.
Lemma lem111761 (P : type1601) (x : nat) : ((term125 P x) = (term126 P x)) = ((term121 P x) = (term136 P x)).
Proof. exact (MK_COMB (@lem111754 P x) (@lem111760 P x)). Qed.
Lemma lem111762 (P : type1601) (x : nat) : (term121 P x) = (term136 P x).
Proof. exact (EQ_MP (@lem111761 P x) (@lem111746 P x)). Qed.
Lemma lem111764 {A : Type'} (P : Prop) (Q : A -> Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem111765 (P : Prop) (Q : nat -> Prop) : (term111 P Q) = (term112 P Q).
Proof. exact (@lem111764 nat P Q). Qed.
Lemma lem111766 (P : type1601) (x : nat) (y : nat) : (term137 P x y) = (term138 P x y).
Proof. exact (@lem111765 (term71 P) (term80 P x y)). Qed.
Lemma lem111767 (P : type1601) (x : nat) (y : nat) (z : nat) : (term139 P x y z) = (term78 P x y z).
Proof. exact (eq_refl (term139 P x y z)). Qed.
Lemma lem111768 (P : type1601) (x : nat) (y : nat) : (term140 P x y) = (term80 P x y).
Proof. exact (fun_ext (fun z : nat => @lem111767 P x y z)). Qed.
Lemma lem111769 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem111770 (P : type1601) (x : nat) (y : nat) : (term141 P x y) = (term81 P x y).
Proof. exact (MK_COMB (@lem111769) (@lem111768 P x y)). Qed.
Lemma lem111771 (P : type1601) : (term97 P) = (term97 P).
Proof. exact (eq_refl (term97 P)). Qed.
Lemma lem111772 (P : type1601) (x : nat) (y : nat) : (term137 P x y) = (term133 P x y).
Proof. exact (MK_COMB (@lem111771 P) (@lem111770 P x y)). Qed.
Lemma lem111773 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem111774 (P : type1601) (x : nat) (y : nat) : (term142 P x y) = (term143 P x y).
Proof. exact (MK_COMB (@lem111773) (@lem111772 P x y)). Qed.
Lemma lem111775 (P : type1601) (x : nat) (y : nat) (z : nat) : (term139 P x y z) = (term78 P x y z).
Proof. exact (eq_refl (term139 P x y z)). Qed.
Lemma lem111776 (P : type1601) : (term97 P) = (term97 P).
Proof. exact (eq_refl (term97 P)). Qed.
Lemma lem111777 (P : type1601) (x : nat) (y : nat) (z : nat) : (term144 P x y z) = (term145 P x y z).
Proof. exact (MK_COMB (@lem111776 P) (@lem111775 P x y z)). Qed.
Lemma lem111778 (P : type1601) (x : nat) (y : nat) : (term146 P x y) = (term147 P x y).
Proof. exact (fun_ext (fun z : nat => @lem111777 P x y z)). Qed.
Lemma lem111779 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem111780 (P : type1601) (x : nat) (y : nat) : (term138 P x y) = (term148 P x y).
Proof. exact (MK_COMB (@lem111779) (@lem111778 P x y)). Qed.
Lemma lem111781 (P : type1601) (x : nat) (y : nat) : ((term137 P x y) = (term138 P x y)) = ((term133 P x y) = (term148 P x y)).
Proof. exact (MK_COMB (@lem111774 P x y) (@lem111780 P x y)). Qed.
Lemma lem111782 (P : type1601) (x : nat) (y : nat) : (term133 P x y) = (term148 P x y).
Proof. exact (EQ_MP (@lem111781 P x y) (@lem111766 P x y)). Qed.
Lemma lem111783 (P : type1601) (x : nat) : (term135 P x) = (term149 P x).
Proof. exact (fun_ext (fun y : nat => @lem111782 P x y)). Qed.
Lemma lem111784 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem111785 (P : type1601) (x : nat) : (term136 P x) = (term150 P x).
Proof. exact (MK_COMB (@lem111784) (@lem111783 P x)). Qed.
Lemma lem111786 (P : type1601) (x : nat) : (term121 P x) = (term150 P x).
Proof. exact (TRANS (@lem111762 P x) (@lem111785 P x)). Qed.
Lemma lem111787 (P : type1601) : (term123 P) = (term151 P).
Proof. exact (fun_ext (fun x : nat => @lem111786 P x)). Qed.
Lemma lem111788 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem111789 (P : type1601) : (term124 P) = (term152 P).
Proof. exact (MK_COMB (@lem111788) (@lem111787 P)). Qed.
Lemma lem111790 (P : type1601) : (term99 P) = (term152 P).
Proof. exact (TRANS (@lem111742 P) (@lem111789 P)). Qed.
Lemma lem111791 : term107 = term153.
Proof. exact (fun_ext (fun P : type1601 => @lem111790 P)). Qed.
Lemma lem111792 : (@ex (nat -> nat -> nat -> Prop)) = (@ex (nat -> nat -> nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> nat -> nat -> Prop))). Qed.
Lemma lem111794 : term108 = term154.
Proof. exact (MK_COMB (@lem111792) (@lem111791)). Qed.
Lemma lem111795 : term10 = term154.
Proof. exact (TRANS (@lem111549) (@lem111794)). Qed.
Lemma lem111796 (h1 : term10) : term154.
Proof. exact (EQ_MP (@lem111795) (@lem111457 h1)). Qed.
Lemma lem111801 (n : nat) (m : nat) : (term20 n m) = (term20 n m).
Proof. exact (eq_refl (term20 n m)). Qed.
Lemma lem111802 (m : nat) : (term21 m) = (term21 m).
Proof. exact (fun_ext (fun n : nat => @lem111801 n m)). Qed.
Lemma lem111803 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111804 (m : nat) : (term22 m) = (term22 m).
Proof. exact (MK_COMB (@lem111803) (@lem111802 m)). Qed.
Lemma lem111805 : term23 = term23.
Proof. exact (fun_ext (fun m : nat => @lem111804 m)). Qed.
Lemma lem111806 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111863 : term17 = term17.
Proof. exact (MK_COMB (@lem111806) (@lem111805)). Qed.
Lemma lem111864 (h1 : term17) : term17.
Proof. exact (EQ_MP (@lem111863) (@lem111458 h1)). Qed.
Lemma lem111865 (P : type1601) (h1 : term152 P) : term152 P.
Proof. exact (h1). Qed.
Lemma lem111866 (P : type1601) (x : nat) (h1 : term150 P x) : term150 P x.
Proof. exact (h1). Qed.
Lemma lem111867 (P : type1601) (x : nat) (y : nat) (h1 : term148 P x y) : term148 P x y.
Proof. exact (h1). Qed.
Lemma lem111868 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term145 P x y z.
Proof. exact (h1). Qed.
Lemma lem111881 (n : nat) (m : nat) : (term20 n m) = (term20 n m).
Proof. exact (eq_refl (term20 n m)). Qed.
Lemma lem111882 (m : nat) : (term21 m) = (term21 m).
Proof. exact (fun_ext (fun n : nat => @lem111881 n m)). Qed.
Lemma lem111883 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111884 (m : nat) : (term22 m) = (term22 m).
Proof. exact (MK_COMB (@lem111883) (@lem111882 m)). Qed.
Lemma lem111885 : term23 = term23.
Proof. exact (fun_ext (fun m : nat => @lem111884 m)). Qed.
Lemma lem111886 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111887 : term17 = term17.
Proof. exact (MK_COMB (@lem111886) (@lem111885)). Qed.
Lemma lem111888 (h1 : term17) : term17.
Proof. exact (EQ_MP (@lem111887) (@lem111864 h1)). Qed.
Lemma lem111897 (P : type1601) (x : nat) (y : nat) (z : nat) : (term78 P x y z) = (term78 P x y z).
Proof. exact (eq_refl (term78 P x y z)). Qed.
Lemma lem111924 (P : type1601) (x : nat) (y : nat) (z : nat) : (term62 P x y z) = (term62 P x y z).
Proof. exact (eq_refl (term62 P x y z)). Qed.
Lemma lem111925 (P : type1601) (x : nat) (y : nat) : (term64 P x y) = (term64 P x y).
Proof. exact (fun_ext (fun z : nat => @lem111924 P x y z)). Qed.
Lemma lem111926 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111927 (P : type1601) (x : nat) (y : nat) : (term65 P x y) = (term65 P x y).
Proof. exact (MK_COMB (@lem111926) (@lem111925 P x y)). Qed.
Lemma lem111928 (P : type1601) (x : nat) : (term66 P x) = (term66 P x).
Proof. exact (fun_ext (fun y : nat => @lem111927 P x y)). Qed.
Lemma lem111929 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111930 (P : type1601) (x : nat) : (term67 P x) = (term67 P x).
Proof. exact (MK_COMB (@lem111929) (@lem111928 P x)). Qed.
Lemma lem111931 (P : type1601) : (term68 P) = (term68 P).
Proof. exact (fun_ext (fun x : nat => @lem111930 P x)). Qed.
Lemma lem111932 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111933 (P : type1601) : (term69 P) = (term69 P).
Proof. exact (MK_COMB (@lem111932) (@lem111931 P)). Qed.
Lemma lem111962 (P : type1601) (x : nat) (z : nat) (y : nat) : (term49 P x z y) = (term49 P x z y).
Proof. exact (eq_refl (term49 P x z y)). Qed.
Lemma lem111963 (P : type1601) (x : nat) (y : nat) : (term51 P x y) = (term51 P x y).
Proof. exact (fun_ext (fun z : nat => @lem111962 P x z y)). Qed.
Lemma lem111964 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111965 (P : type1601) (x : nat) (y : nat) : (term52 P x y) = (term52 P x y).
Proof. exact (MK_COMB (@lem111964) (@lem111963 P x y)). Qed.
Lemma lem111966 (P : type1601) (x : nat) : (term53 P x) = (term53 P x).
Proof. exact (fun_ext (fun y : nat => @lem111965 P x y)). Qed.
Lemma lem111967 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111968 (P : type1601) (x : nat) : (term54 P x) = (term54 P x).
Proof. exact (MK_COMB (@lem111967) (@lem111966 P x)). Qed.
Lemma lem111969 (P : type1601) : (term55 P) = (term55 P).
Proof. exact (fun_ext (fun x : nat => @lem111968 P x)). Qed.
Lemma lem111970 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111971 (P : type1601) : (term56 P) = (term56 P).
Proof. exact (MK_COMB (@lem111970) (@lem111969 P)). Qed.
Lemma lem111972 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem111973 (P : type1601) : (term70 P) = (term70 P).
Proof. exact (MK_COMB (@lem111972) (@lem111971 P)). Qed.
Lemma lem111974 (P : type1601) : (term71 P) = (term71 P).
Proof. exact (MK_COMB (@lem111973 P) (@lem111933 P)). Qed.
Lemma lem111975 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem111976 (P : type1601) : (term97 P) = (term97 P).
Proof. exact (MK_COMB (@lem111975) (@lem111974 P)). Qed.
Lemma lem111977 (P : type1601) (x : nat) (y : nat) (z : nat) : (term145 P x y z) = (term145 P x y z).
Proof. exact (MK_COMB (@lem111976 P) (@lem111897 P x y z)). Qed.
Lemma lem111978 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term145 P x y z.
Proof. exact (EQ_MP (@lem111977 P x y z) (@lem111868 P x y z h1)). Qed.
Lemma lem111980 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term71 P.
Proof. exact (proj1 (@lem111978 P x y z h1)). Qed.
Lemma lem111981 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term69 P.
Proof. exact (proj2 (@lem111980 P x y z h1)). Qed.
Lemma lem111982 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term56 P.
Proof. exact (proj1 (@lem111980 P x y z h1)). Qed.
Lemma lem111990 (n : nat) (m : nat) : (term20 n m) = (term20 n m).
Proof. exact (eq_refl (term20 n m)). Qed.
Lemma lem111991 (m : nat) : (term21 m) = (term21 m).
Proof. exact (fun_ext (fun n : nat => @lem111990 n m)). Qed.
Lemma lem111992 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111993 (m : nat) : (term22 m) = (term22 m).
Proof. exact (MK_COMB (@lem111992) (@lem111991 m)). Qed.
Lemma lem111994 : term23 = term23.
Proof. exact (fun_ext (fun m : nat => @lem111993 m)). Qed.
Lemma lem111995 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem111997 : term17 = term17.
Proof. exact (MK_COMB (@lem111995) (@lem111994)). Qed.
Lemma lem111998 (h1 : term17) : term17.
Proof. exact (EQ_MP (@lem111997) (@lem111888 h1)). Qed.
Lemma lem112020 (P : type1601) (x : nat) (z : nat) (y : nat) : (term49 P x z y) = (term155 P x z y).
Proof. exact (@lem19490 (P y x z) (term78 P x y z) (P x z y)). Qed.
Lemma lem112021 (P : type1601) (x : nat) (y : nat) : (term51 P x y) = (term156 P x y).
Proof. exact (fun_ext (fun z : nat => @lem112020 P x z y)). Qed.
Lemma lem112022 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem112023 (P : type1601) (x : nat) (y : nat) : (term52 P x y) = (term157 P x y).
Proof. exact (MK_COMB (@lem112022) (@lem112021 P x y)). Qed.
Lemma lem112024 (P : type1601) (x : nat) : (term53 P x) = (term158 P x).
Proof. exact (fun_ext (fun y : nat => @lem112023 P x y)). Qed.
Lemma lem112025 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem112026 (P : type1601) (x : nat) : (term54 P x) = (term159 P x).
Proof. exact (MK_COMB (@lem112025) (@lem112024 P x)). Qed.
Lemma lem112027 (P : type1601) : (term55 P) = (term160 P).
Proof. exact (fun_ext (fun x : nat => @lem112026 P x)). Qed.
Lemma lem112028 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem112030 (P : type1601) : (term56 P) = (term161 P).
Proof. exact (MK_COMB (@lem112028) (@lem112027 P)). Qed.
Lemma lem112031 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term161 P.
Proof. exact (EQ_MP (@lem112030 P) (@lem111982 P x y z h1)). Qed.
Lemma lem112045 (P : type1601) (x : nat) (y : nat) (z : nat) : (term62 P x y z) = (term62 P x y z).
Proof. exact (eq_refl (term62 P x y z)). Qed.
Lemma lem112046 (P : type1601) (x : nat) (y : nat) : (term64 P x y) = (term64 P x y).
Proof. exact (fun_ext (fun z : nat => @lem112045 P x y z)). Qed.
Lemma lem112047 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem112048 (P : type1601) (x : nat) (y : nat) : (term65 P x y) = (term65 P x y).
Proof. exact (MK_COMB (@lem112047) (@lem112046 P x y)). Qed.
Lemma lem112049 (P : type1601) (x : nat) : (term66 P x) = (term66 P x).
Proof. exact (fun_ext (fun y : nat => @lem112048 P x y)). Qed.
Lemma lem112050 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem112051 (P : type1601) (x : nat) : (term67 P x) = (term67 P x).
Proof. exact (MK_COMB (@lem112050) (@lem112049 P x)). Qed.
Lemma lem112052 (P : type1601) : (term68 P) = (term68 P).
Proof. exact (fun_ext (fun x : nat => @lem112051 P x)). Qed.
Lemma lem112053 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem112055 (P : type1601) : (term69 P) = (term69 P).
Proof. exact (MK_COMB (@lem112053) (@lem112052 P)). Qed.
Lemma lem112056 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term69 P.
Proof. exact (EQ_MP (@lem112055 P) (@lem111981 P x y z h1)). Qed.
Lemma lem112057 (_2382 : nat) (h1 : term17) : term162 _2382.
Proof. exact (@lem111998 h1 _2382). Qed.
Lemma lem112058 (_2382 : nat) : (term162 _2382) = (term22 _2382).
Proof. exact (eq_refl (term162 _2382)). Qed.
Lemma lem112059 (_2382 : nat) (h1 : term17) : term22 _2382.
Proof. exact (EQ_MP (@lem112058 _2382) (@lem112057 _2382 h1)). Qed.
Lemma lem112060 (_2382 : nat) (_2383 : nat) (h1 : term17) : term163 _2382 _2383.
Proof. exact (@lem112059 _2382 h1 _2383). Qed.
Lemma lem112061 (_2383 : nat) (_2382 : nat) : (term163 _2382 _2383) = (term20 _2383 _2382).
Proof. exact (eq_refl (term163 _2382 _2383)). Qed.
Lemma lem112063 (_2384 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term164 P _2384.
Proof. exact (@lem112031 P x y z h1 _2384). Qed.
Lemma lem112064 (P : type1601) (_2384 : nat) : (term164 P _2384) = (term159 P _2384).
Proof. exact (eq_refl (term164 P _2384)). Qed.
Lemma lem112065 (_2384 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term159 P _2384.
Proof. exact (EQ_MP (@lem112064 P _2384) (@lem112063 _2384 P x y z h1)). Qed.
Lemma lem112066 (_2384 : nat) (_2385 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term165 P _2384 _2385.
Proof. exact (@lem112065 _2384 P x y z h1 _2385). Qed.
Lemma lem112067 (P : type1601) (_2384 : nat) (_2385 : nat) : (term165 P _2384 _2385) = (term157 P _2384 _2385).
Proof. exact (eq_refl (term165 P _2384 _2385)). Qed.
Lemma lem112068 (_2384 : nat) (_2385 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term157 P _2384 _2385.
Proof. exact (EQ_MP (@lem112067 P _2384 _2385) (@lem112066 _2384 _2385 P x y z h1)). Qed.
Lemma lem112069 (_2384 : nat) (_2385 : nat) (_2386 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term166 P _2384 _2385 _2386.
Proof. exact (@lem112068 _2384 _2385 P x y z h1 _2386). Qed.
Lemma lem112070 (P : type1601) (_2384 : nat) (_2386 : nat) (_2385 : nat) : (term166 P _2384 _2385 _2386) = (term155 P _2384 _2386 _2385).
Proof. exact (eq_refl (term166 P _2384 _2385 _2386)). Qed.
Lemma lem112071 (_2384 : nat) (_2386 : nat) (_2385 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term155 P _2384 _2386 _2385.
Proof. exact (EQ_MP (@lem112070 P _2384 _2386 _2385) (@lem112069 _2384 _2385 _2386 P x y z h1)). Qed.
Lemma lem112072 (_2387 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term167 P _2387.
Proof. exact (@lem112056 P x y z h1 _2387). Qed.
Lemma lem112073 (P : type1601) (_2387 : nat) : (term167 P _2387) = (term67 P _2387).
Proof. exact (eq_refl (term167 P _2387)). Qed.
Lemma lem112074 (_2387 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term67 P _2387.
Proof. exact (EQ_MP (@lem112073 P _2387) (@lem112072 _2387 P x y z h1)). Qed.
Lemma lem112075 (_2387 : nat) (_2388 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term168 P _2387 _2388.
Proof. exact (@lem112074 _2387 P x y z h1 _2388). Qed.
Lemma lem112076 (P : type1601) (_2387 : nat) (_2388 : nat) : (term168 P _2387 _2388) = (term65 P _2387 _2388).
Proof. exact (eq_refl (term168 P _2387 _2388)). Qed.
Lemma lem112077 (_2387 : nat) (_2388 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term65 P _2387 _2388.
Proof. exact (EQ_MP (@lem112076 P _2387 _2388) (@lem112075 _2387 _2388 P x y z h1)). Qed.
Lemma lem112078 (_2387 : nat) (_2388 : nat) (_2389 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term169 P _2387 _2388 _2389.
Proof. exact (@lem112077 _2387 _2388 P x y z h1 _2389). Qed.
Lemma lem112079 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term169 P _2387 _2388 _2389) = (term62 P _2387 _2388 _2389).
Proof. exact (eq_refl (term169 P _2387 _2388 _2389)). Qed.
Lemma lem112080 (_2387 : nat) (_2388 : nat) (_2389 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term62 P _2387 _2388 _2389.
Proof. exact (EQ_MP (@lem112079 P _2387 _2388 _2389) (@lem112078 _2387 _2388 _2389 P x y z h1)). Qed.
Lemma lem112088 (_2383 : nat) (_2382 : nat) (h1 : term17) : term20 _2383 _2382.
Proof. exact (EQ_MP (@lem112061 _2383 _2382) (@lem112060 _2382 _2383 h1)). Qed.
Lemma lem112090 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term78 P x y z.
Proof. exact (proj2 (@lem111978 P x y z h1)). Qed.
Lemma lem112101 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term62 P _2387 _2388 _2389) = (term170 P _2387 _2388 _2389).
Proof. exact (@lem111152 (term171 _2387 _2388) (term171 _2388 _2389) (P _2387 _2388 _2389)). Qed.
Lemma lem112102 (_2387 : nat) (_2388 : nat) (_2389 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term170 P _2387 _2388 _2389.
Proof. exact (EQ_MP (@lem112101 P _2387 _2388 _2389) (@lem112080 _2387 _2388 _2389 P x y z h1)). Qed.
Lemma lem112108 (_2385 : nat) (_2384 : nat) (_2386 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term172 P _2385 _2384 _2386.
Proof. exact (proj1 (@lem112071 _2384 _2386 _2385 P x y z h1)). Qed.
Lemma lem112114 (_2384 : nat) (_2386 : nat) (_2385 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term173 P _2384 _2386 _2385.
Proof. exact (proj2 (@lem112071 _2384 _2386 _2385 P x y z h1)). Qed.
Lemma lem112117 (z : nat) (y : nat) (h1 : term171 z y) : term171 z y.
Proof. exact (h1). Qed.
Lemma lem112118 (z : nat) (y : nat) (h1 : term171 z y) : term174 z y.
Proof. exact (fun h0 : Peano.le z y => @lem112117 z y h1). Qed.
Lemma lem112120 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem112121 (z : nat) (y : nat) : (term174 z y) = (term171 z y).
Proof. exact (@lem112120 (Peano.le z y)). Qed.
Lemma lem112122 (z : nat) (y : nat) (h1 : term171 z y) : term171 z y.
Proof. exact (EQ_MP (@lem112121 z y) (@lem112118 z y h1)). Qed.
Lemma lem112133 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem112134 (_2383 : nat) (_2382 : nat) : (term20 _2382 _2383) = (term20 _2383 _2382).
Proof. exact (@lem112133 (Peano.le _2382 _2383) (Peano.le _2383 _2382)). Qed.
Lemma lem112140 (_2383 : nat) (_2382 : nat) : (term176 _2383 _2382) = (term176 _2383 _2382).
Proof. exact (eq_refl (term176 _2383 _2382)). Qed.
Lemma lem112141 (_2383 : nat) (_2382 : nat) : ((term20 _2383 _2382) = (term20 _2382 _2383)) = ((term20 _2383 _2382) = (term20 _2383 _2382)).
Proof. exact (MK_COMB (@lem112140 _2383 _2382) (@lem112134 _2383 _2382)). Qed.
Lemma lem112143 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem112144 (x : Prop) : (x = x) = True.
Proof. exact (@lem112143 Prop x). Qed.
Lemma lem112145 (_2383 : nat) (_2382 : nat) : ((term20 _2383 _2382) = (term20 _2383 _2382)) = True.
Proof. exact (@lem112144 (term20 _2383 _2382)). Qed.
Lemma lem112146 (_2382 : nat) (_2383 : nat) : ((term20 _2383 _2382) = (term20 _2382 _2383)) = True.
Proof. exact (TRANS (@lem112141 _2383 _2382) (@lem112145 _2383 _2382)). Qed.
Lemma lem112147 (_2382 : nat) (_2383 : nat) : True = ((term20 _2383 _2382) = (term20 _2382 _2383)).
Proof. exact (SYM (@lem112146 _2382 _2383)). Qed.
Lemma lem112148 (_2382 : nat) (_2383 : nat) : (term20 _2383 _2382) = (term20 _2382 _2383).
Proof. exact (EQ_MP (@lem112147 _2382 _2383) (@lem0)). Qed.
Lemma lem112149 (_2382 : nat) (_2383 : nat) (h1 : term17) : term20 _2382 _2383.
Proof. exact (EQ_MP (@lem112148 _2382 _2383) (@lem112088 _2383 _2382 h1)). Qed.
Lemma lem112151 (b : Prop) (a : Prop) : (a \/ b) = (term177 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem112154 (_2383 : nat) (_2382 : nat) : (term20 _2382 _2383) = (term178 _2383 _2382).
Proof. exact (@lem112151 (Peano.le _2382 _2383) (Peano.le _2383 _2382)). Qed.
Lemma lem112157 (_2383 : nat) (_2382 : nat) (h1 : term17) : term178 _2383 _2382.
Proof. exact (EQ_MP (@lem112154 _2383 _2382) (@lem112149 _2382 _2383 h1)). Qed.
Lemma lem112158 (y : nat) (z : nat) (h1 : term17) : term178 y z.
Proof. exact (@lem112157 y z h1). Qed.
Lemma lem112161 (z : nat) (y : nat) (h1 : term17) (h2 : term171 z y) : Peano.le y z.
Proof. exact (@lem112158 y z h1 (@lem112122 z y h2)). Qed.
Lemma lem112162 (z : nat) (y : nat) (h1 : term17) (h2 : term171 z y) : term179 y z.
Proof. exact (fun h0 : term171 y z => @lem112161 z y h1 h2). Qed.
Lemma lem112164 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem112165 (y : nat) (z : nat) : (term179 y z) = (Peano.le y z).
Proof. exact (@lem112164 (Peano.le y z)). Qed.
Lemma lem112166 (z : nat) (y : nat) (h1 : term17) (h2 : term171 z y) : Peano.le y z.
Proof. exact (EQ_MP (@lem112165 y z) (@lem112162 z y h1 h2)). Qed.
Lemma lem112169 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term78 P x y z) : term78 P x y z.
Proof. exact (h1). Qed.
Lemma lem112170 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term78 P x y z) : term181 P x y z.
Proof. exact (fun h0 : P x y z => @lem112169 P x y z h1). Qed.
Lemma lem112172 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem112173 (P : type1601) (x : nat) (y : nat) (z : nat) : (term181 P x y z) = (term78 P x y z).
Proof. exact (@lem112172 (P x y z)). Qed.
Lemma lem112174 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term78 P x y z) : term78 P x y z.
Proof. exact (EQ_MP (@lem112173 P x y z) (@lem112170 P x y z h1)). Qed.
Lemma lem112176 (b : Prop) (a : Prop) : (a \/ b) = (term177 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem112179 (P : type1601) (_2384 : nat) (_2385 : nat) (_2386 : nat) : (term172 P _2385 _2384 _2386) = (term182 P _2384 _2385 _2386).
Proof. exact (@lem112176 (P _2385 _2384 _2386) (term78 P _2384 _2385 _2386)). Qed.
Lemma lem112182 (_2384 : nat) (_2385 : nat) (_2386 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term182 P _2384 _2385 _2386.
Proof. exact (EQ_MP (@lem112179 P _2384 _2385 _2386) (@lem112108 _2385 _2384 _2386 P x y z h1)). Qed.
Lemma lem112183 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term182 P y x z.
Proof. exact (@lem112182 y x z P x y z h1). Qed.
Lemma lem112186 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term78 P x y z) (h2 : term145 P x y z) : term78 P y x z.
Proof. exact (@lem112183 P x y z h2 (@lem112174 P x y z h1)). Qed.
Lemma lem112187 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term78 P x y z) (h2 : term145 P x y z) : term181 P y x z.
Proof. exact (fun h0 : P y x z => @lem112186 P x y z h1 h2). Qed.
Lemma lem112189 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem112190 (P : type1601) (y : nat) (x : nat) (z : nat) : (term181 P y x z) = (term78 P y x z).
Proof. exact (@lem112189 (P y x z)). Qed.
Lemma lem112191 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term78 P x y z) (h2 : term145 P x y z) : term78 P y x z.
Proof. exact (EQ_MP (@lem112190 P y x z) (@lem112187 P x y z h1 h2)). Qed.
Lemma lem112193 (b : Prop) (a : Prop) : (a \/ b) = (term177 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem112196 (P : type1601) (_2384 : nat) (_2385 : nat) (_2386 : nat) : (term173 P _2384 _2386 _2385) = (term183 P _2384 _2385 _2386).
Proof. exact (@lem112193 (P _2384 _2386 _2385) (term78 P _2384 _2385 _2386)). Qed.
Lemma lem112199 (_2384 : nat) (_2385 : nat) (_2386 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term183 P _2384 _2385 _2386.
Proof. exact (EQ_MP (@lem112196 P _2384 _2385 _2386) (@lem112114 _2384 _2386 _2385 P x y z h1)). Qed.
Lemma lem112200 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term183 P y z x.
Proof. exact (@lem112199 y z x P x y z h1). Qed.
Lemma lem112203 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term78 P x y z) (h2 : term145 P x y z) : term78 P y z x.
Proof. exact (@lem112200 P x y z h2 (@lem112191 P x y z h1 h2)). Qed.
Lemma lem112204 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term78 P x y z) (h2 : term145 P x y z) : term181 P y z x.
Proof. exact (fun h0 : P y z x => @lem112203 P x y z h1 h2). Qed.
Lemma lem112206 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem112207 (P : type1601) (y : nat) (z : nat) (x : nat) : (term181 P y z x) = (term78 P y z x).
Proof. exact (@lem112206 (P y z x)). Qed.
Lemma lem112208 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term78 P x y z) (h2 : term145 P x y z) : term78 P y z x.
Proof. exact (EQ_MP (@lem112207 P y z x) (@lem112204 P x y z h1 h2)). Qed.
Lemma lem112224 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem112225 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term184 P _2387 _2388 _2389) = (term185 P _2387 _2388 _2389).
Proof. exact (@lem112224 (P _2387 _2388 _2389) (term171 _2388 _2389)). Qed.
Lemma lem112231 (_2387 : nat) (_2388 : nat) : (term186 _2387 _2388) = (term186 _2387 _2388).
Proof. exact (eq_refl (term186 _2387 _2388)). Qed.
Lemma lem112232 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term170 P _2387 _2388 _2389) = (term187 P _2387 _2388 _2389).
Proof. exact (MK_COMB (@lem112231 _2387 _2388) (@lem112225 P _2387 _2388 _2389)). Qed.
Lemma lem112236 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem112237 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term187 P _2387 _2388 _2389) = (term188 P _2387 _2388 _2389).
Proof. exact (@lem112236 (P _2387 _2388 _2389) (term171 _2387 _2388) (term171 _2388 _2389)). Qed.
Lemma lem112253 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term170 P _2387 _2388 _2389) = (term188 P _2387 _2388 _2389).
Proof. exact (TRANS (@lem112232 P _2387 _2388 _2389) (@lem112237 P _2387 _2388 _2389)). Qed.
Lemma lem112254 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem112255 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term189 P _2387 _2388 _2389) = (term190 P _2387 _2388 _2389).
Proof. exact (MK_COMB (@lem112254) (@lem112253 P _2387 _2388 _2389)). Qed.
Lemma lem112259 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem112260 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term191 P _2387 _2388 _2389) = (term170 P _2387 _2388 _2389).
Proof. exact (@lem112259 (term171 _2387 _2388) (term171 _2388 _2389) (P _2387 _2388 _2389)). Qed.
Lemma lem112274 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem112275 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term184 P _2387 _2388 _2389) = (term185 P _2387 _2388 _2389).
Proof. exact (@lem112274 (P _2387 _2388 _2389) (term171 _2388 _2389)). Qed.
Lemma lem112281 (_2387 : nat) (_2388 : nat) : (term186 _2387 _2388) = (term186 _2387 _2388).
Proof. exact (eq_refl (term186 _2387 _2388)). Qed.
Lemma lem112282 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term170 P _2387 _2388 _2389) = (term187 P _2387 _2388 _2389).
Proof. exact (MK_COMB (@lem112281 _2387 _2388) (@lem112275 P _2387 _2388 _2389)). Qed.
Lemma lem112286 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem112287 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term187 P _2387 _2388 _2389) = (term188 P _2387 _2388 _2389).
Proof. exact (@lem112286 (P _2387 _2388 _2389) (term171 _2387 _2388) (term171 _2388 _2389)). Qed.
Lemma lem112303 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term170 P _2387 _2388 _2389) = (term188 P _2387 _2388 _2389).
Proof. exact (TRANS (@lem112282 P _2387 _2388 _2389) (@lem112287 P _2387 _2388 _2389)). Qed.
Lemma lem112304 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term191 P _2387 _2388 _2389) = (term188 P _2387 _2388 _2389).
Proof. exact (TRANS (@lem112260 P _2387 _2388 _2389) (@lem112303 P _2387 _2388 _2389)). Qed.
Lemma lem112305 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : ((term170 P _2387 _2388 _2389) = (term191 P _2387 _2388 _2389)) = ((term188 P _2387 _2388 _2389) = (term188 P _2387 _2388 _2389)).
Proof. exact (MK_COMB (@lem112255 P _2387 _2388 _2389) (@lem112304 P _2387 _2388 _2389)). Qed.
Lemma lem112307 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem112308 (x : Prop) : (x = x) = True.
Proof. exact (@lem112307 Prop x). Qed.
Lemma lem112309 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : ((term188 P _2387 _2388 _2389) = (term188 P _2387 _2388 _2389)) = True.
Proof. exact (@lem112308 (term188 P _2387 _2388 _2389)). Qed.
Lemma lem112310 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : ((term170 P _2387 _2388 _2389) = (term191 P _2387 _2388 _2389)) = True.
Proof. exact (TRANS (@lem112305 P _2387 _2388 _2389) (@lem112309 P _2387 _2388 _2389)). Qed.
Lemma lem112311 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : True = ((term170 P _2387 _2388 _2389) = (term191 P _2387 _2388 _2389)).
Proof. exact (SYM (@lem112310 P _2387 _2388 _2389)). Qed.
Lemma lem112312 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term170 P _2387 _2388 _2389) = (term191 P _2387 _2388 _2389).
Proof. exact (EQ_MP (@lem112311 P _2387 _2388 _2389) (@lem0)). Qed.
Lemma lem112313 (_2387 : nat) (_2388 : nat) (_2389 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term191 P _2387 _2388 _2389.
Proof. exact (EQ_MP (@lem112312 P _2387 _2388 _2389) (@lem112102 _2387 _2388 _2389 P x y z h1)). Qed.
Lemma lem112315 (b : Prop) (a : Prop) : (a \/ b) = (term177 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem112316 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term191 P _2387 _2388 _2389) = (term192 P _2387 _2388 _2389).
Proof. exact (@lem112315 (term193 P _2387 _2388 _2389) (term171 _2388 _2389)). Qed.
Lemma lem112318 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem112319 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term196 P _2387 _2388 _2389) = (term197 P _2387 _2388 _2389).
Proof. exact (@lem112318 (term171 _2387 _2388) (P _2387 _2388 _2389)). Qed.
Lemma lem112321 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem112322 (_2387 : nat) (_2388 : nat) : (term199 _2387 _2388) = (Peano.le _2387 _2388).
Proof. exact (@lem112321 (Peano.le _2387 _2388)). Qed.
Lemma lem112323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem112324 (_2387 : nat) (_2388 : nat) : (term200 _2387 _2388) = (term201 _2387 _2388).
Proof. exact (MK_COMB (@lem112323) (@lem112322 _2387 _2388)). Qed.
Lemma lem112325 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term78 P _2387 _2388 _2389) = (term78 P _2387 _2388 _2389).
Proof. exact (eq_refl (term78 P _2387 _2388 _2389)). Qed.
Lemma lem112326 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term197 P _2387 _2388 _2389) = (term202 P _2387 _2388 _2389).
Proof. exact (MK_COMB (@lem112324 _2387 _2388) (@lem112325 P _2387 _2388 _2389)). Qed.
Lemma lem112327 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term196 P _2387 _2388 _2389) = (term202 P _2387 _2388 _2389).
Proof. exact (TRANS (@lem112319 P _2387 _2388 _2389) (@lem112326 P _2387 _2388 _2389)). Qed.
Lemma lem112328 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem112329 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term203 P _2387 _2388 _2389) = (term204 P _2387 _2388 _2389).
Proof. exact (MK_COMB (@lem112328) (@lem112327 P _2387 _2388 _2389)). Qed.
Lemma lem112330 (_2388 : nat) (_2389 : nat) : (term171 _2388 _2389) = (term171 _2388 _2389).
Proof. exact (eq_refl (term171 _2388 _2389)). Qed.
Lemma lem112331 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term192 P _2387 _2388 _2389) = (term205 P _2387 _2388 _2389).
Proof. exact (MK_COMB (@lem112329 P _2387 _2388 _2389) (@lem112330 _2388 _2389)). Qed.
Lemma lem112332 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term191 P _2387 _2388 _2389) = (term205 P _2387 _2388 _2389).
Proof. exact (TRANS (@lem112316 P _2387 _2388 _2389) (@lem112331 P _2387 _2388 _2389)). Qed.
Lemma lem112334 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term145 P x y z) : term202 P y z x.
Proof. exact (conj (@lem112166 z y h1 h2) (@lem112208 P x y z h3 h4)). Qed.
Lemma lem112336 (_2387 : nat) (_2388 : nat) (_2389 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term205 P _2387 _2388 _2389.
Proof. exact (EQ_MP (@lem112332 P _2387 _2388 _2389) (@lem112313 _2387 _2388 _2389 P x y z h1)). Qed.
Lemma lem112337 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term205 P y z x.
Proof. exact (@lem112336 y z x P x y z h1). Qed.
Lemma lem112340 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term145 P x y z) : term171 z x.
Proof. exact (@lem112337 P x y z h4 (@lem112334 P x y z h1 h2 h3 h4)). Qed.
Lemma lem112341 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term145 P x y z) : term174 z x.
Proof. exact (fun h0 : Peano.le z x => @lem112340 P x y z h1 h2 h3 h4). Qed.
Lemma lem112343 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem112344 (z : nat) (x : nat) : (term174 z x) = (term171 z x).
Proof. exact (@lem112343 (Peano.le z x)). Qed.
Lemma lem112345 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term145 P x y z) : term171 z x.
Proof. exact (EQ_MP (@lem112344 z x) (@lem112341 P x y z h1 h2 h3 h4)). Qed.
Lemma lem112347 (_2383 : nat) (_2382 : nat) (h1 : term17) : term178 _2383 _2382.
Proof. exact (EQ_MP (@lem112154 _2383 _2382) (@lem112149 _2382 _2383 h1)). Qed.
Lemma lem112348 (x : nat) (z : nat) (h1 : term17) : term178 x z.
Proof. exact (@lem112347 x z h1). Qed.
Lemma lem112351 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term145 P x y z) : Peano.le x z.
Proof. exact (@lem112348 x z h1 (@lem112345 P x y z h1 h2 h3 h4)). Qed.
Lemma lem112352 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term145 P x y z) : term179 x z.
Proof. exact (fun h0 : term171 x z => @lem112351 P x y z h1 h2 h3 h4). Qed.
Lemma lem112354 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem112355 (x : nat) (z : nat) : (term179 x z) = (Peano.le x z).
Proof. exact (@lem112354 (Peano.le x z)). Qed.
Lemma lem112356 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term145 P x y z) : Peano.le x z.
Proof. exact (EQ_MP (@lem112355 x z) (@lem112352 P x y z h1 h2 h3 h4)). Qed.
Lemma lem112359 (P : type1601) (z : nat) (y : nat) (x : nat) (h1 : term78 P z y x) : term78 P z y x.
Proof. exact (h1). Qed.
Lemma lem112360 (P : type1601) (z : nat) (y : nat) (x : nat) (h1 : term78 P z y x) : term181 P z y x.
Proof. exact (fun h0 : P z y x => @lem112359 P z y x h1). Qed.
Lemma lem112362 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem112363 (P : type1601) (z : nat) (y : nat) (x : nat) : (term181 P z y x) = (term78 P z y x).
Proof. exact (@lem112362 (P z y x)). Qed.
Lemma lem112364 (P : type1601) (z : nat) (y : nat) (x : nat) (h1 : term78 P z y x) : term78 P z y x.
Proof. exact (EQ_MP (@lem112363 P z y x) (@lem112360 P z y x h1)). Qed.
Lemma lem112366 (_2384 : nat) (_2385 : nat) (_2386 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term182 P _2384 _2385 _2386.
Proof. exact (EQ_MP (@lem112179 P _2384 _2385 _2386) (@lem112108 _2385 _2384 _2386 P x y z h1)). Qed.
Lemma lem112367 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term182 P y z x.
Proof. exact (@lem112366 y z x P x y z h1). Qed.
Lemma lem112370 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term78 P z y x) (h2 : term145 P x y z) : term78 P y z x.
Proof. exact (@lem112367 P x y z h2 (@lem112364 P z y x h1)). Qed.
Lemma lem112371 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term78 P z y x) (h2 : term145 P x y z) : term181 P y z x.
Proof. exact (fun h0 : P y z x => @lem112370 P x y z h1 h2). Qed.
Lemma lem112373 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem112374 (P : type1601) (y : nat) (z : nat) (x : nat) : (term181 P y z x) = (term78 P y z x).
Proof. exact (@lem112373 (P y z x)). Qed.
Lemma lem112375 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term78 P z y x) (h2 : term145 P x y z) : term78 P y z x.
Proof. exact (EQ_MP (@lem112374 P y z x) (@lem112371 P x y z h1 h2)). Qed.
Lemma lem112377 (_2384 : nat) (_2385 : nat) (_2386 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term183 P _2384 _2385 _2386.
Proof. exact (EQ_MP (@lem112196 P _2384 _2385 _2386) (@lem112114 _2384 _2386 _2385 P x y z h1)). Qed.
Lemma lem112378 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term183 P y x z.
Proof. exact (@lem112377 y x z P x y z h1). Qed.
Lemma lem112381 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term78 P z y x) (h2 : term145 P x y z) : term78 P y x z.
Proof. exact (@lem112378 P x y z h2 (@lem112375 P x y z h1 h2)). Qed.
Lemma lem112382 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term78 P z y x) (h2 : term145 P x y z) : term181 P y x z.
Proof. exact (fun h0 : P y x z => @lem112381 P x y z h1 h2). Qed.
Lemma lem112384 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem112385 (P : type1601) (y : nat) (x : nat) (z : nat) : (term181 P y x z) = (term78 P y x z).
Proof. exact (@lem112384 (P y x z)). Qed.
Lemma lem112386 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term78 P z y x) (h2 : term145 P x y z) : term78 P y x z.
Proof. exact (EQ_MP (@lem112385 P y x z) (@lem112382 P x y z h1 h2)). Qed.
Lemma lem112388 (b : Prop) (a : Prop) : (a \/ b) = (term177 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem112389 (P : type1601) (_2389 : nat) (_2387 : nat) (_2388 : nat) : (term170 P _2387 _2388 _2389) = (term206 P _2389 _2387 _2388).
Proof. exact (@lem112388 (term184 P _2387 _2388 _2389) (term171 _2387 _2388)). Qed.
Lemma lem112391 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem112392 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term207 P _2387 _2388 _2389) = (term208 P _2387 _2388 _2389).
Proof. exact (@lem112391 (term171 _2388 _2389) (P _2387 _2388 _2389)). Qed.
Lemma lem112394 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem112395 (_2388 : nat) (_2389 : nat) : (term199 _2388 _2389) = (Peano.le _2388 _2389).
Proof. exact (@lem112394 (Peano.le _2388 _2389)). Qed.
Lemma lem112396 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem112397 (_2388 : nat) (_2389 : nat) : (term200 _2388 _2389) = (term201 _2388 _2389).
Proof. exact (MK_COMB (@lem112396) (@lem112395 _2388 _2389)). Qed.
Lemma lem112398 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term78 P _2387 _2388 _2389) = (term78 P _2387 _2388 _2389).
Proof. exact (eq_refl (term78 P _2387 _2388 _2389)). Qed.
Lemma lem112399 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term208 P _2387 _2388 _2389) = (term209 P _2387 _2388 _2389).
Proof. exact (MK_COMB (@lem112397 _2388 _2389) (@lem112398 P _2387 _2388 _2389)). Qed.
Lemma lem112400 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term207 P _2387 _2388 _2389) = (term209 P _2387 _2388 _2389).
Proof. exact (TRANS (@lem112392 P _2387 _2388 _2389) (@lem112399 P _2387 _2388 _2389)). Qed.
Lemma lem112401 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem112402 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term210 P _2387 _2388 _2389) = (term211 P _2387 _2388 _2389).
Proof. exact (MK_COMB (@lem112401) (@lem112400 P _2387 _2388 _2389)). Qed.
Lemma lem112403 (_2387 : nat) (_2388 : nat) : (term171 _2387 _2388) = (term171 _2387 _2388).
Proof. exact (eq_refl (term171 _2387 _2388)). Qed.
Lemma lem112404 (P : type1601) (_2389 : nat) (_2387 : nat) (_2388 : nat) : (term206 P _2389 _2387 _2388) = (term212 P _2389 _2387 _2388).
Proof. exact (MK_COMB (@lem112402 P _2387 _2388 _2389) (@lem112403 _2387 _2388)). Qed.
Lemma lem112405 (P : type1601) (_2389 : nat) (_2387 : nat) (_2388 : nat) : (term170 P _2387 _2388 _2389) = (term212 P _2389 _2387 _2388).
Proof. exact (TRANS (@lem112389 P _2389 _2387 _2388) (@lem112404 P _2389 _2387 _2388)). Qed.
Lemma lem112407 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term78 P z y x) (h5 : term145 P x y z) : term209 P y x z.
Proof. exact (conj (@lem112356 P x y z h1 h2 h3 h5) (@lem112386 P x y z h4 h5)). Qed.
Lemma lem112409 (_2389 : nat) (_2387 : nat) (_2388 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term212 P _2389 _2387 _2388.
Proof. exact (EQ_MP (@lem112405 P _2389 _2387 _2388) (@lem112102 _2387 _2388 _2389 P x y z h1)). Qed.
Lemma lem112410 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term212 P z y x.
Proof. exact (@lem112409 z y x P x y z h1). Qed.
Lemma lem112413 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term78 P z y x) (h5 : term145 P x y z) : term171 y x.
Proof. exact (@lem112410 P x y z h5 (@lem112407 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem112414 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term78 P z y x) (h5 : term145 P x y z) : term174 y x.
Proof. exact (fun h0 : Peano.le y x => @lem112413 P x y z h1 h2 h3 h4 h5). Qed.
Lemma lem112416 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem112417 (y : nat) (x : nat) : (term174 y x) = (term171 y x).
Proof. exact (@lem112416 (Peano.le y x)). Qed.
Lemma lem112418 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term78 P z y x) (h5 : term145 P x y z) : term171 y x.
Proof. exact (EQ_MP (@lem112417 y x) (@lem112414 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem112420 (_2383 : nat) (_2382 : nat) (h1 : term17) : term178 _2383 _2382.
Proof. exact (EQ_MP (@lem112154 _2383 _2382) (@lem112149 _2382 _2383 h1)). Qed.
Lemma lem112421 (x : nat) (y : nat) (h1 : term17) : term178 x y.
Proof. exact (@lem112420 x y h1). Qed.
Lemma lem112424 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term78 P z y x) (h5 : term145 P x y z) : Peano.le x y.
Proof. exact (@lem112421 x y h1 (@lem112418 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem112425 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term78 P z y x) (h5 : term145 P x y z) : term179 x y.
Proof. exact (fun h0 : term171 x y => @lem112424 P x y z h1 h2 h3 h4 h5). Qed.
Lemma lem112427 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem112428 (x : nat) (y : nat) : (term179 x y) = (Peano.le x y).
Proof. exact (@lem112427 (Peano.le x y)). Qed.
Lemma lem112429 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term78 P z y x) (h5 : term145 P x y z) : Peano.le x y.
Proof. exact (EQ_MP (@lem112428 x y) (@lem112425 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem112432 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term78 P x y z) : term78 P x y z.
Proof. exact (h1). Qed.
Lemma lem112433 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term78 P x y z) : term181 P x y z.
Proof. exact (fun h0 : P x y z => @lem112432 P x y z h1). Qed.
Lemma lem112435 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem112436 (P : type1601) (x : nat) (y : nat) (z : nat) : (term181 P x y z) = (term78 P x y z).
Proof. exact (@lem112435 (P x y z)). Qed.
Lemma lem112437 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term78 P x y z) : term78 P x y z.
Proof. exact (EQ_MP (@lem112436 P x y z) (@lem112433 P x y z h1)). Qed.
Lemma lem112438 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term78 P z y x) (h5 : term145 P x y z) : term202 P x y z.
Proof. exact (conj (@lem112429 P x y z h1 h2 h3 h4 h5) (@lem112437 P x y z h3)). Qed.
Lemma lem112440 (_2387 : nat) (_2388 : nat) (_2389 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term205 P _2387 _2388 _2389.
Proof. exact (EQ_MP (@lem112332 P _2387 _2388 _2389) (@lem112313 _2387 _2388 _2389 P x y z h1)). Qed.
Lemma lem112441 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term205 P x y z.
Proof. exact (@lem112440 x y z P x y z h1). Qed.
Lemma lem112444 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term78 P z y x) (h5 : term145 P x y z) : term171 y z.
Proof. exact (@lem112441 P x y z h5 (@lem112438 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem112445 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term78 P z y x) (h5 : term145 P x y z) : term174 y z.
Proof. exact (fun h0 : Peano.le y z => @lem112444 P x y z h1 h2 h3 h4 h5). Qed.
Lemma lem112447 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem112448 (y : nat) (z : nat) : (term174 y z) = (term171 y z).
Proof. exact (@lem112447 (Peano.le y z)). Qed.
Lemma lem112449 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term78 P z y x) (h5 : term145 P x y z) : term171 y z.
Proof. exact (EQ_MP (@lem112448 y z) (@lem112445 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem112451 (_2383 : nat) (_2382 : nat) (h1 : term17) : term178 _2383 _2382.
Proof. exact (EQ_MP (@lem112154 _2383 _2382) (@lem112149 _2382 _2383 h1)). Qed.
Lemma lem112452 (z : nat) (y : nat) (h1 : term17) : term178 z y.
Proof. exact (@lem112451 z y h1). Qed.
Lemma lem112455 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 z y) (h3 : term78 P x y z) (h4 : term78 P z y x) (h5 : term145 P x y z) : Peano.le z y.
Proof. exact (@lem112452 z y h1 (@lem112449 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem112456 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term78 P x y z) (h3 : term78 P z y x) (h4 : term145 P x y z) : term179 z y.
Proof. exact (fun h0 : term171 z y => @lem112455 P x y z h1 h0 h2 h3 h4). Qed.
Lemma lem112458 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem112459 (z : nat) (y : nat) : (term179 z y) = (Peano.le z y).
Proof. exact (@lem112458 (Peano.le z y)). Qed.
Lemma lem112460 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term78 P x y z) (h3 : term78 P z y x) (h4 : term145 P x y z) : Peano.le z y.
Proof. exact (EQ_MP (@lem112459 z y) (@lem112456 P x y z h1 h2 h3 h4)). Qed.
Lemma lem112463 (y : nat) (x : nat) (h1 : term171 y x) : term171 y x.
Proof. exact (h1). Qed.
Lemma lem112464 (y : nat) (x : nat) (h1 : term171 y x) : term174 y x.
Proof. exact (fun h0 : Peano.le y x => @lem112463 y x h1). Qed.
Lemma lem112466 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem112467 (y : nat) (x : nat) : (term174 y x) = (term171 y x).
Proof. exact (@lem112466 (Peano.le y x)). Qed.
Lemma lem112468 (y : nat) (x : nat) (h1 : term171 y x) : term171 y x.
Proof. exact (EQ_MP (@lem112467 y x) (@lem112464 y x h1)). Qed.
Lemma lem112470 (_2383 : nat) (_2382 : nat) (h1 : term17) : term178 _2383 _2382.
Proof. exact (EQ_MP (@lem112154 _2383 _2382) (@lem112149 _2382 _2383 h1)). Qed.
Lemma lem112471 (x : nat) (y : nat) (h1 : term17) : term178 x y.
Proof. exact (@lem112470 x y h1). Qed.
Lemma lem112474 (y : nat) (x : nat) (h1 : term17) (h2 : term171 y x) : Peano.le x y.
Proof. exact (@lem112471 x y h1 (@lem112468 y x h2)). Qed.
Lemma lem112475 (y : nat) (x : nat) (h1 : term17) (h2 : term171 y x) : term179 x y.
Proof. exact (fun h0 : term171 x y => @lem112474 y x h1 h2). Qed.
Lemma lem112477 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem112478 (x : nat) (y : nat) : (term179 x y) = (Peano.le x y).
Proof. exact (@lem112477 (Peano.le x y)). Qed.
Lemma lem112479 (y : nat) (x : nat) (h1 : term17) (h2 : term171 y x) : Peano.le x y.
Proof. exact (EQ_MP (@lem112478 x y) (@lem112475 y x h1 h2)). Qed.
Lemma lem112482 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term78 P x y z) : term78 P x y z.
Proof. exact (h1). Qed.
Lemma lem112483 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term78 P x y z) : term181 P x y z.
Proof. exact (fun h0 : P x y z => @lem112482 P x y z h1). Qed.
Lemma lem112485 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem112486 (P : type1601) (x : nat) (y : nat) (z : nat) : (term181 P x y z) = (term78 P x y z).
Proof. exact (@lem112485 (P x y z)). Qed.
Lemma lem112487 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term78 P x y z) : term78 P x y z.
Proof. exact (EQ_MP (@lem112486 P x y z) (@lem112483 P x y z h1)). Qed.
Lemma lem112488 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) : term202 P x y z.
Proof. exact (conj (@lem112479 y x h1 h2) (@lem112487 P x y z h3)). Qed.
Lemma lem112490 (_2387 : nat) (_2388 : nat) (_2389 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term205 P _2387 _2388 _2389.
Proof. exact (EQ_MP (@lem112332 P _2387 _2388 _2389) (@lem112313 _2387 _2388 _2389 P x y z h1)). Qed.
Lemma lem112491 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term205 P x y z.
Proof. exact (@lem112490 x y z P x y z h1). Qed.
Lemma lem112494 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term145 P x y z) : term171 y z.
Proof. exact (@lem112491 P x y z h4 (@lem112488 P x y z h1 h2 h3)). Qed.
Lemma lem112495 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term145 P x y z) : term174 y z.
Proof. exact (fun h0 : Peano.le y z => @lem112494 P x y z h1 h2 h3 h4). Qed.
Lemma lem112497 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem112498 (y : nat) (z : nat) : (term174 y z) = (term171 y z).
Proof. exact (@lem112497 (Peano.le y z)). Qed.
Lemma lem112499 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term145 P x y z) : term171 y z.
Proof. exact (EQ_MP (@lem112498 y z) (@lem112495 P x y z h1 h2 h3 h4)). Qed.
Lemma lem112501 (_2383 : nat) (_2382 : nat) (h1 : term17) : term178 _2383 _2382.
Proof. exact (EQ_MP (@lem112154 _2383 _2382) (@lem112149 _2382 _2383 h1)). Qed.
Lemma lem112502 (z : nat) (y : nat) (h1 : term17) : term178 z y.
Proof. exact (@lem112501 z y h1). Qed.
Lemma lem112505 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term145 P x y z) : Peano.le z y.
Proof. exact (@lem112502 z y h1 (@lem112499 P x y z h1 h2 h3 h4)). Qed.
Lemma lem112506 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term145 P x y z) : term179 z y.
Proof. exact (fun h0 : term171 z y => @lem112505 P x y z h1 h2 h3 h4). Qed.
Lemma lem112508 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem112509 (z : nat) (y : nat) : (term179 z y) = (Peano.le z y).
Proof. exact (@lem112508 (Peano.le z y)). Qed.
Lemma lem112510 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term145 P x y z) : Peano.le z y.
Proof. exact (EQ_MP (@lem112509 z y) (@lem112506 P x y z h1 h2 h3 h4)). Qed.
Lemma lem112513 (P : type1601) (x : nat) (z : nat) (y : nat) (h1 : term78 P x z y) : term78 P x z y.
Proof. exact (h1). Qed.
Lemma lem112514 (P : type1601) (x : nat) (z : nat) (y : nat) (h1 : term78 P x z y) : term181 P x z y.
Proof. exact (fun h0 : P x z y => @lem112513 P x z y h1). Qed.
Lemma lem112516 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem112517 (P : type1601) (x : nat) (z : nat) (y : nat) : (term181 P x z y) = (term78 P x z y).
Proof. exact (@lem112516 (P x z y)). Qed.
Lemma lem112518 (P : type1601) (x : nat) (z : nat) (y : nat) (h1 : term78 P x z y) : term78 P x z y.
Proof. exact (EQ_MP (@lem112517 P x z y) (@lem112514 P x z y h1)). Qed.
Lemma lem112519 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term78 P x z y) (h5 : term145 P x y z) : term209 P x z y.
Proof. exact (conj (@lem112510 P x y z h1 h2 h3 h5) (@lem112518 P x z y h4)). Qed.
Lemma lem112521 (_2389 : nat) (_2387 : nat) (_2388 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term212 P _2389 _2387 _2388.
Proof. exact (EQ_MP (@lem112405 P _2389 _2387 _2388) (@lem112102 _2387 _2388 _2389 P x y z h1)). Qed.
Lemma lem112522 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term212 P y x z.
Proof. exact (@lem112521 y x z P x y z h1). Qed.
Lemma lem112525 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term78 P x z y) (h5 : term145 P x y z) : term171 x z.
Proof. exact (@lem112522 P x y z h5 (@lem112519 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem112526 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term78 P x z y) (h5 : term145 P x y z) : term174 x z.
Proof. exact (fun h0 : Peano.le x z => @lem112525 P x y z h1 h2 h3 h4 h5). Qed.
Lemma lem112528 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem112529 (x : nat) (z : nat) : (term174 x z) = (term171 x z).
Proof. exact (@lem112528 (Peano.le x z)). Qed.
Lemma lem112530 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term78 P x z y) (h5 : term145 P x y z) : term171 x z.
Proof. exact (EQ_MP (@lem112529 x z) (@lem112526 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem112532 (_2383 : nat) (_2382 : nat) (h1 : term17) : term178 _2383 _2382.
Proof. exact (EQ_MP (@lem112154 _2383 _2382) (@lem112149 _2382 _2383 h1)). Qed.
Lemma lem112533 (z : nat) (x : nat) (h1 : term17) : term178 z x.
Proof. exact (@lem112532 z x h1). Qed.
Lemma lem112536 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term78 P x z y) (h5 : term145 P x y z) : Peano.le z x.
Proof. exact (@lem112533 z x h1 (@lem112530 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem112537 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term78 P x z y) (h5 : term145 P x y z) : term179 z x.
Proof. exact (fun h0 : term171 z x => @lem112536 P x y z h1 h2 h3 h4 h5). Qed.
Lemma lem112539 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem112540 (z : nat) (x : nat) : (term179 z x) = (Peano.le z x).
Proof. exact (@lem112539 (Peano.le z x)). Qed.
Lemma lem112541 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term78 P x z y) (h5 : term145 P x y z) : Peano.le z x.
Proof. exact (EQ_MP (@lem112540 z x) (@lem112537 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem112544 (P : type1601) (z : nat) (x : nat) (y : nat) (h1 : term78 P z x y) : term78 P z x y.
Proof. exact (h1). Qed.
Lemma lem112545 (P : type1601) (z : nat) (x : nat) (y : nat) (h1 : term78 P z x y) : term181 P z x y.
Proof. exact (fun h0 : P z x y => @lem112544 P z x y h1). Qed.
Lemma lem112547 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem112548 (P : type1601) (z : nat) (x : nat) (y : nat) : (term181 P z x y) = (term78 P z x y).
Proof. exact (@lem112547 (P z x y)). Qed.
Lemma lem112549 (P : type1601) (z : nat) (x : nat) (y : nat) (h1 : term78 P z x y) : term78 P z x y.
Proof. exact (EQ_MP (@lem112548 P z x y) (@lem112545 P z x y h1)). Qed.
Lemma lem112550 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term78 P x z y) (h5 : term78 P z x y) (h6 : term145 P x y z) : term202 P z x y.
Proof. exact (conj (@lem112541 P x y z h1 h2 h3 h4 h6) (@lem112549 P z x y h5)). Qed.
Lemma lem112552 (_2387 : nat) (_2388 : nat) (_2389 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term205 P _2387 _2388 _2389.
Proof. exact (EQ_MP (@lem112332 P _2387 _2388 _2389) (@lem112313 _2387 _2388 _2389 P x y z h1)). Qed.
Lemma lem112553 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term205 P z x y.
Proof. exact (@lem112552 z x y P x y z h1). Qed.
Lemma lem112556 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term78 P x z y) (h5 : term78 P z x y) (h6 : term145 P x y z) : term171 x y.
Proof. exact (@lem112553 P x y z h6 (@lem112550 P x y z h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem112557 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term78 P x z y) (h5 : term78 P z x y) (h6 : term145 P x y z) : term174 x y.
Proof. exact (fun h0 : Peano.le x y => @lem112556 P x y z h1 h2 h3 h4 h5 h6). Qed.
Lemma lem112559 (p : Prop) : (term175 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem112560 (x : nat) (y : nat) : (term174 x y) = (term171 x y).
Proof. exact (@lem112559 (Peano.le x y)). Qed.
Lemma lem112561 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term78 P x z y) (h5 : term78 P z x y) (h6 : term145 P x y z) : term171 x y.
Proof. exact (EQ_MP (@lem112560 x y) (@lem112557 P x y z h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem112563 (_2383 : nat) (_2382 : nat) (h1 : term17) : term178 _2383 _2382.
Proof. exact (EQ_MP (@lem112154 _2383 _2382) (@lem112149 _2382 _2383 h1)). Qed.
Lemma lem112564 (y : nat) (x : nat) (h1 : term17) : term178 y x.
Proof. exact (@lem112563 y x h1). Qed.
Lemma lem112567 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term171 y x) (h3 : term78 P x y z) (h4 : term78 P x z y) (h5 : term78 P z x y) (h6 : term145 P x y z) : Peano.le y x.
Proof. exact (@lem112564 y x h1 (@lem112561 P x y z h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem112568 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term78 P x y z) (h3 : term78 P x z y) (h4 : term78 P z x y) (h5 : term145 P x y z) : term179 y x.
Proof. exact (fun h0 : term171 y x => @lem112567 P x y z h1 h0 h2 h3 h4 h5). Qed.
Lemma lem112570 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem112571 (y : nat) (x : nat) : (term179 y x) = (Peano.le y x).
Proof. exact (@lem112570 (Peano.le y x)). Qed.
Lemma lem112572 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term78 P x y z) (h3 : term78 P x z y) (h4 : term78 P z x y) (h5 : term145 P x y z) : Peano.le y x.
Proof. exact (EQ_MP (@lem112571 y x) (@lem112568 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem112588 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem112589 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term184 P _2387 _2388 _2389) = (term185 P _2387 _2388 _2389).
Proof. exact (@lem112588 (P _2387 _2388 _2389) (term171 _2388 _2389)). Qed.
Lemma lem112595 (_2387 : nat) (_2388 : nat) : (term186 _2387 _2388) = (term186 _2387 _2388).
Proof. exact (eq_refl (term186 _2387 _2388)). Qed.
Lemma lem112596 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term170 P _2387 _2388 _2389) = (term187 P _2387 _2388 _2389).
Proof. exact (MK_COMB (@lem112595 _2387 _2388) (@lem112589 P _2387 _2388 _2389)). Qed.
Lemma lem112600 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem112601 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term187 P _2387 _2388 _2389) = (term188 P _2387 _2388 _2389).
Proof. exact (@lem112600 (P _2387 _2388 _2389) (term171 _2387 _2388) (term171 _2388 _2389)). Qed.
Lemma lem112617 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term170 P _2387 _2388 _2389) = (term188 P _2387 _2388 _2389).
Proof. exact (TRANS (@lem112596 P _2387 _2388 _2389) (@lem112601 P _2387 _2388 _2389)). Qed.
Lemma lem112618 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem112619 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term189 P _2387 _2388 _2389) = (term190 P _2387 _2388 _2389).
Proof. exact (MK_COMB (@lem112618) (@lem112617 P _2387 _2388 _2389)). Qed.
Lemma lem112635 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term188 P _2387 _2388 _2389) = (term188 P _2387 _2388 _2389).
Proof. exact (eq_refl (term188 P _2387 _2388 _2389)). Qed.
Lemma lem112636 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : ((term170 P _2387 _2388 _2389) = (term188 P _2387 _2388 _2389)) = ((term188 P _2387 _2388 _2389) = (term188 P _2387 _2388 _2389)).
Proof. exact (MK_COMB (@lem112619 P _2387 _2388 _2389) (@lem112635 P _2387 _2388 _2389)). Qed.
Lemma lem112638 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem112639 (x : Prop) : (x = x) = True.
Proof. exact (@lem112638 Prop x). Qed.
Lemma lem112640 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : ((term188 P _2387 _2388 _2389) = (term188 P _2387 _2388 _2389)) = True.
Proof. exact (@lem112639 (term188 P _2387 _2388 _2389)). Qed.
Lemma lem112641 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : ((term170 P _2387 _2388 _2389) = (term188 P _2387 _2388 _2389)) = True.
Proof. exact (TRANS (@lem112636 P _2387 _2388 _2389) (@lem112640 P _2387 _2388 _2389)). Qed.
Lemma lem112642 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : True = ((term170 P _2387 _2388 _2389) = (term188 P _2387 _2388 _2389)).
Proof. exact (SYM (@lem112641 P _2387 _2388 _2389)). Qed.
Lemma lem112643 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term170 P _2387 _2388 _2389) = (term188 P _2387 _2388 _2389).
Proof. exact (EQ_MP (@lem112642 P _2387 _2388 _2389) (@lem0)). Qed.
Lemma lem112644 (_2387 : nat) (_2388 : nat) (_2389 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term188 P _2387 _2388 _2389.
Proof. exact (EQ_MP (@lem112643 P _2387 _2388 _2389) (@lem112102 _2387 _2388 _2389 P x y z h1)). Qed.
Lemma lem112646 (b : Prop) (a : Prop) : (a \/ b) = (term177 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem112647 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term188 P _2387 _2388 _2389) = (term213 P _2387 _2388 _2389).
Proof. exact (@lem112646 (term58 _2387 _2388 _2389) (P _2387 _2388 _2389)). Qed.
Lemma lem112649 (a : Prop) (b : Prop) : (term194 a b) = (term195 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem112650 (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term214 _2387 _2388 _2389) = (term215 _2387 _2388 _2389).
Proof. exact (@lem112649 (term171 _2387 _2388) (term171 _2388 _2389)). Qed.
Lemma lem112652 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem112653 (_2387 : nat) (_2388 : nat) : (term199 _2387 _2388) = (Peano.le _2387 _2388).
Proof. exact (@lem112652 (Peano.le _2387 _2388)). Qed.
Lemma lem112654 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem112655 (_2387 : nat) (_2388 : nat) : (term200 _2387 _2388) = (term201 _2387 _2388).
Proof. exact (MK_COMB (@lem112654) (@lem112653 _2387 _2388)). Qed.
Lemma lem112657 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem112658 (_2388 : nat) (_2389 : nat) : (term199 _2388 _2389) = (Peano.le _2388 _2389).
Proof. exact (@lem112657 (Peano.le _2388 _2389)). Qed.
Lemma lem112659 (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term215 _2387 _2388 _2389) = (term63 _2387 _2388 _2389).
Proof. exact (MK_COMB (@lem112655 _2387 _2388) (@lem112658 _2388 _2389)). Qed.
Lemma lem112660 (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term214 _2387 _2388 _2389) = (term63 _2387 _2388 _2389).
Proof. exact (TRANS (@lem112650 _2387 _2388 _2389) (@lem112659 _2387 _2388 _2389)). Qed.
Lemma lem112661 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem112662 (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term216 _2387 _2388 _2389) = (term217 _2387 _2388 _2389).
Proof. exact (MK_COMB (@lem112661) (@lem112660 _2387 _2388 _2389)). Qed.
Lemma lem112663 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (P _2387 _2388 _2389) = (P _2387 _2388 _2389).
Proof. exact (eq_refl (P _2387 _2388 _2389)). Qed.
Lemma lem112664 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term213 P _2387 _2388 _2389) = (term30 P _2387 _2388 _2389).
Proof. exact (MK_COMB (@lem112662 _2387 _2388 _2389) (@lem112663 P _2387 _2388 _2389)). Qed.
Lemma lem112665 (P : type1601) (_2387 : nat) (_2388 : nat) (_2389 : nat) : (term188 P _2387 _2388 _2389) = (term30 P _2387 _2388 _2389).
Proof. exact (TRANS (@lem112647 P _2387 _2388 _2389) (@lem112664 P _2387 _2388 _2389)). Qed.
Lemma lem112667 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term78 P x y z) (h3 : term78 P x z y) (h4 : term78 P z x y) (h5 : term78 P z y x) (h6 : term145 P x y z) : term63 z y x.
Proof. exact (conj (@lem112460 P x y z h1 h2 h5 h6) (@lem112572 P x y z h1 h2 h3 h4 h6)). Qed.
Lemma lem112669 (_2387 : nat) (_2388 : nat) (_2389 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term30 P _2387 _2388 _2389.
Proof. exact (EQ_MP (@lem112665 P _2387 _2388 _2389) (@lem112644 _2387 _2388 _2389 P x y z h1)). Qed.
Lemma lem112670 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term30 P z y x.
Proof. exact (@lem112669 z y x P x y z h1). Qed.
Lemma lem112673 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term78 P x y z) (h3 : term78 P x z y) (h4 : term78 P z x y) (h5 : term78 P z y x) (h6 : term145 P x y z) : P z y x.
Proof. exact (@lem112670 P x y z h6 (@lem112667 P x y z h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem112674 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term78 P x y z) (h3 : term78 P x z y) (h4 : term78 P z x y) (h5 : term145 P x y z) : term218 P z y x.
Proof. exact (fun h0 : term78 P z y x => @lem112673 P x y z h1 h2 h3 h4 h0 h5). Qed.
Lemma lem112676 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem112677 (P : type1601) (z : nat) (y : nat) (x : nat) : (term218 P z y x) = (P z y x).
Proof. exact (@lem112676 (P z y x)). Qed.
Lemma lem112678 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term78 P x y z) (h3 : term78 P x z y) (h4 : term78 P z x y) (h5 : term145 P x y z) : P z y x.
Proof. exact (EQ_MP (@lem112677 P z y x) (@lem112674 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem112684 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem112685 (P : type1601) (_2384 : nat) (_2385 : nat) (_2386 : nat) : (term173 P _2384 _2386 _2385) = (term219 P _2384 _2385 _2386).
Proof. exact (@lem112684 (P _2384 _2386 _2385) (term78 P _2384 _2385 _2386)). Qed.
Lemma lem112691 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem112692 (P : type1601) (_2384 : nat) (_2385 : nat) (_2386 : nat) : (term220 P _2384 _2386 _2385) = (term221 P _2384 _2385 _2386).
Proof. exact (MK_COMB (@lem112691) (@lem112685 P _2384 _2385 _2386)). Qed.
Lemma lem112698 (P : type1601) (_2384 : nat) (_2385 : nat) (_2386 : nat) : (term219 P _2384 _2385 _2386) = (term219 P _2384 _2385 _2386).
Proof. exact (eq_refl (term219 P _2384 _2385 _2386)). Qed.
Lemma lem112699 (P : type1601) (_2384 : nat) (_2385 : nat) (_2386 : nat) : ((term173 P _2384 _2386 _2385) = (term219 P _2384 _2385 _2386)) = ((term219 P _2384 _2385 _2386) = (term219 P _2384 _2385 _2386)).
Proof. exact (MK_COMB (@lem112692 P _2384 _2385 _2386) (@lem112698 P _2384 _2385 _2386)). Qed.
Lemma lem112701 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem112702 (x : Prop) : (x = x) = True.
Proof. exact (@lem112701 Prop x). Qed.
Lemma lem112703 (P : type1601) (_2384 : nat) (_2385 : nat) (_2386 : nat) : ((term219 P _2384 _2385 _2386) = (term219 P _2384 _2385 _2386)) = True.
Proof. exact (@lem112702 (term219 P _2384 _2385 _2386)). Qed.
Lemma lem112704 (P : type1601) (_2384 : nat) (_2385 : nat) (_2386 : nat) : ((term173 P _2384 _2386 _2385) = (term219 P _2384 _2385 _2386)) = True.
Proof. exact (TRANS (@lem112699 P _2384 _2385 _2386) (@lem112703 P _2384 _2385 _2386)). Qed.
Lemma lem112705 (P : type1601) (_2384 : nat) (_2385 : nat) (_2386 : nat) : True = ((term173 P _2384 _2386 _2385) = (term219 P _2384 _2385 _2386)).
Proof. exact (SYM (@lem112704 P _2384 _2385 _2386)). Qed.
Lemma lem112706 (P : type1601) (_2384 : nat) (_2385 : nat) (_2386 : nat) : (term173 P _2384 _2386 _2385) = (term219 P _2384 _2385 _2386).
Proof. exact (EQ_MP (@lem112705 P _2384 _2385 _2386) (@lem0)). Qed.
Lemma lem112707 (_2384 : nat) (_2385 : nat) (_2386 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term219 P _2384 _2385 _2386.
Proof. exact (EQ_MP (@lem112706 P _2384 _2385 _2386) (@lem112114 _2384 _2386 _2385 P x y z h1)). Qed.
Lemma lem112709 (b : Prop) (a : Prop) : (a \/ b) = (term177 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem112710 (P : type1601) (_2384 : nat) (_2386 : nat) (_2385 : nat) : (term219 P _2384 _2385 _2386) = (term222 P _2384 _2386 _2385).
Proof. exact (@lem112709 (term78 P _2384 _2385 _2386) (P _2384 _2386 _2385)). Qed.
Lemma lem112712 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem112713 (P : type1601) (_2384 : nat) (_2385 : nat) (_2386 : nat) : (term223 P _2384 _2385 _2386) = (P _2384 _2385 _2386).
Proof. exact (@lem112712 (P _2384 _2385 _2386)). Qed.
Lemma lem112714 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem112715 (P : type1601) (_2384 : nat) (_2385 : nat) (_2386 : nat) : (term224 P _2384 _2385 _2386) = (term225 P _2384 _2385 _2386).
Proof. exact (MK_COMB (@lem112714) (@lem112713 P _2384 _2385 _2386)). Qed.
Lemma lem112716 (P : type1601) (_2384 : nat) (_2386 : nat) (_2385 : nat) : (P _2384 _2386 _2385) = (P _2384 _2386 _2385).
Proof. exact (eq_refl (P _2384 _2386 _2385)). Qed.
Lemma lem112717 (P : type1601) (_2384 : nat) (_2386 : nat) (_2385 : nat) : (term222 P _2384 _2386 _2385) = (term226 P _2384 _2386 _2385).
Proof. exact (MK_COMB (@lem112715 P _2384 _2385 _2386) (@lem112716 P _2384 _2386 _2385)). Qed.
Lemma lem112718 (P : type1601) (_2384 : nat) (_2386 : nat) (_2385 : nat) : (term219 P _2384 _2385 _2386) = (term226 P _2384 _2386 _2385).
Proof. exact (TRANS (@lem112710 P _2384 _2386 _2385) (@lem112717 P _2384 _2386 _2385)). Qed.
Lemma lem112721 (_2384 : nat) (_2386 : nat) (_2385 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term226 P _2384 _2386 _2385.
Proof. exact (EQ_MP (@lem112718 P _2384 _2386 _2385) (@lem112707 _2384 _2385 _2386 P x y z h1)). Qed.
Lemma lem112722 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term226 P z x y.
Proof. exact (@lem112721 z x y P x y z h1). Qed.
Lemma lem112725 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term78 P x y z) (h3 : term78 P x z y) (h4 : term78 P z x y) (h5 : term145 P x y z) : P z x y.
Proof. exact (@lem112722 P x y z h5 (@lem112678 P x y z h1 h2 h3 h4 h5)). Qed.
Lemma lem112726 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term78 P x y z) (h3 : term78 P x z y) (h4 : term145 P x y z) : term218 P z x y.
Proof. exact (fun h0 : term78 P z x y => @lem112725 P x y z h1 h2 h3 h0 h4). Qed.
Lemma lem112728 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem112729 (P : type1601) (z : nat) (x : nat) (y : nat) : (term218 P z x y) = (P z x y).
Proof. exact (@lem112728 (P z x y)). Qed.
Lemma lem112730 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term78 P x y z) (h3 : term78 P x z y) (h4 : term145 P x y z) : P z x y.
Proof. exact (EQ_MP (@lem112729 P z x y) (@lem112726 P x y z h1 h2 h3 h4)). Qed.
Lemma lem112736 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem112737 (P : type1601) (_2384 : nat) (_2385 : nat) (_2386 : nat) : (term172 P _2385 _2384 _2386) = (term227 P _2384 _2385 _2386).
Proof. exact (@lem112736 (P _2385 _2384 _2386) (term78 P _2384 _2385 _2386)). Qed.
Lemma lem112743 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem112744 (P : type1601) (_2384 : nat) (_2385 : nat) (_2386 : nat) : (term228 P _2385 _2384 _2386) = (term229 P _2384 _2385 _2386).
Proof. exact (MK_COMB (@lem112743) (@lem112737 P _2384 _2385 _2386)). Qed.
Lemma lem112750 (P : type1601) (_2384 : nat) (_2385 : nat) (_2386 : nat) : (term227 P _2384 _2385 _2386) = (term227 P _2384 _2385 _2386).
Proof. exact (eq_refl (term227 P _2384 _2385 _2386)). Qed.
Lemma lem112751 (P : type1601) (_2384 : nat) (_2385 : nat) (_2386 : nat) : ((term172 P _2385 _2384 _2386) = (term227 P _2384 _2385 _2386)) = ((term227 P _2384 _2385 _2386) = (term227 P _2384 _2385 _2386)).
Proof. exact (MK_COMB (@lem112744 P _2384 _2385 _2386) (@lem112750 P _2384 _2385 _2386)). Qed.
Lemma lem112753 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem112754 (x : Prop) : (x = x) = True.
Proof. exact (@lem112753 Prop x). Qed.
Lemma lem112755 (P : type1601) (_2384 : nat) (_2385 : nat) (_2386 : nat) : ((term227 P _2384 _2385 _2386) = (term227 P _2384 _2385 _2386)) = True.
Proof. exact (@lem112754 (term227 P _2384 _2385 _2386)). Qed.
Lemma lem112756 (P : type1601) (_2384 : nat) (_2385 : nat) (_2386 : nat) : ((term172 P _2385 _2384 _2386) = (term227 P _2384 _2385 _2386)) = True.
Proof. exact (TRANS (@lem112751 P _2384 _2385 _2386) (@lem112755 P _2384 _2385 _2386)). Qed.
Lemma lem112757 (P : type1601) (_2384 : nat) (_2385 : nat) (_2386 : nat) : True = ((term172 P _2385 _2384 _2386) = (term227 P _2384 _2385 _2386)).
Proof. exact (SYM (@lem112756 P _2384 _2385 _2386)). Qed.
Lemma lem112758 (P : type1601) (_2384 : nat) (_2385 : nat) (_2386 : nat) : (term172 P _2385 _2384 _2386) = (term227 P _2384 _2385 _2386).
Proof. exact (EQ_MP (@lem112757 P _2384 _2385 _2386) (@lem0)). Qed.
Lemma lem112759 (_2384 : nat) (_2385 : nat) (_2386 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term227 P _2384 _2385 _2386.
Proof. exact (EQ_MP (@lem112758 P _2384 _2385 _2386) (@lem112108 _2385 _2384 _2386 P x y z h1)). Qed.
Lemma lem112761 (b : Prop) (a : Prop) : (a \/ b) = (term177 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem112762 (P : type1601) (_2385 : nat) (_2384 : nat) (_2386 : nat) : (term227 P _2384 _2385 _2386) = (term230 P _2385 _2384 _2386).
Proof. exact (@lem112761 (term78 P _2384 _2385 _2386) (P _2385 _2384 _2386)). Qed.
Lemma lem112764 (a : Prop) : (term198 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem112765 (P : type1601) (_2384 : nat) (_2385 : nat) (_2386 : nat) : (term223 P _2384 _2385 _2386) = (P _2384 _2385 _2386).
Proof. exact (@lem112764 (P _2384 _2385 _2386)). Qed.
Lemma lem112766 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem112767 (P : type1601) (_2384 : nat) (_2385 : nat) (_2386 : nat) : (term224 P _2384 _2385 _2386) = (term225 P _2384 _2385 _2386).
Proof. exact (MK_COMB (@lem112766) (@lem112765 P _2384 _2385 _2386)). Qed.
Lemma lem112768 (P : type1601) (_2385 : nat) (_2384 : nat) (_2386 : nat) : (P _2385 _2384 _2386) = (P _2385 _2384 _2386).
Proof. exact (eq_refl (P _2385 _2384 _2386)). Qed.
Lemma lem112769 (P : type1601) (_2385 : nat) (_2384 : nat) (_2386 : nat) : (term230 P _2385 _2384 _2386) = (term231 P _2385 _2384 _2386).
Proof. exact (MK_COMB (@lem112767 P _2384 _2385 _2386) (@lem112768 P _2385 _2384 _2386)). Qed.
Lemma lem112770 (P : type1601) (_2385 : nat) (_2384 : nat) (_2386 : nat) : (term227 P _2384 _2385 _2386) = (term231 P _2385 _2384 _2386).
Proof. exact (TRANS (@lem112762 P _2385 _2384 _2386) (@lem112769 P _2385 _2384 _2386)). Qed.
Lemma lem112773 (_2385 : nat) (_2384 : nat) (_2386 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term231 P _2385 _2384 _2386.
Proof. exact (EQ_MP (@lem112770 P _2385 _2384 _2386) (@lem112759 _2384 _2385 _2386 P x y z h1)). Qed.
Lemma lem112774 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term231 P x z y.
Proof. exact (@lem112773 x z y P x y z h1). Qed.
Lemma lem112777 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term78 P x y z) (h3 : term78 P x z y) (h4 : term145 P x y z) : P x z y.
Proof. exact (@lem112774 P x y z h4 (@lem112730 P x y z h1 h2 h3 h4)). Qed.
Lemma lem112778 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term78 P x y z) (h3 : term145 P x y z) : term218 P x z y.
Proof. exact (fun h0 : term78 P x z y => @lem112777 P x y z h1 h2 h0 h3). Qed.
Lemma lem112780 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem112781 (P : type1601) (x : nat) (z : nat) (y : nat) : (term218 P x z y) = (P x z y).
Proof. exact (@lem112780 (P x z y)). Qed.
Lemma lem112782 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term78 P x y z) (h3 : term145 P x y z) : P x z y.
Proof. exact (EQ_MP (@lem112781 P x z y) (@lem112778 P x y z h1 h2 h3)). Qed.
Lemma lem112784 (_2384 : nat) (_2386 : nat) (_2385 : nat) (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term226 P _2384 _2386 _2385.
Proof. exact (EQ_MP (@lem112718 P _2384 _2386 _2385) (@lem112707 _2384 _2385 _2386 P x y z h1)). Qed.
Lemma lem112785 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term226 P x y z.
Proof. exact (@lem112784 x y z P x y z h1). Qed.
Lemma lem112788 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term78 P x y z) (h3 : term145 P x y z) : P x y z.
Proof. exact (@lem112785 P x y z h3 (@lem112782 P x y z h1 h2 h3)). Qed.
Lemma lem112789 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term145 P x y z) : term218 P x y z.
Proof. exact (fun h0 : term78 P x y z => @lem112788 P x y z h1 h0 h2). Qed.
Lemma lem112791 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem112792 (P : type1601) (x : nat) (y : nat) (z : nat) : (term218 P x y z) = (P x y z).
Proof. exact (@lem112791 (P x y z)). Qed.
Lemma lem112793 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term145 P x y z) : P x y z.
Proof. exact (EQ_MP (@lem112792 P x y z) (@lem112789 P x y z h1 h2)). Qed.
Lemma lem112796 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem112798 (P : type1601) (x : nat) (y : nat) (z : nat) : (term78 P x y z) = (term232 P x y z).
Proof. exact (@lem112796 (P x y z)). Qed.
Lemma lem112801 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term145 P x y z) : term232 P x y z.
Proof. exact (EQ_MP (@lem112798 P x y z) (@lem112090 P x y z h1)). Qed.
Lemma lem112804 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term145 P x y z) : False.
Proof. exact (@lem112801 P x y z h2 (@lem112793 P x y z h1 h2)). Qed.
Lemma lem112805 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term145 P x y z) : term233.
Proof. exact (fun h0 : ~ False => @lem112804 P x y z h1 h2). Qed.
Lemma lem112807 (p : Prop) : (term180 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem112808 : term233 = False.
Proof. exact (@lem112807 False). Qed.
Lemma lem112809 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term145 P x y z) : False.
Proof. exact (EQ_MP (@lem112808) (@lem112805 P x y z h1 h2)). Qed.
Lemma lem112810 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term145 P x y z) : term17 = False.
Proof. exact (prop_ext (fun h3 : term17 => @lem112809 P x y z h1 h2) (fun h3 : False => @lem111998 h1)). Qed.
Lemma lem112811 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term145 P x y z) : False.
Proof. exact (EQ_MP (@lem112810 P x y z h1 h2) (@lem111998 h1)). Qed.
Lemma lem112812 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term145 P x y z) : (term145 P x y z) = False.
Proof. exact (prop_ext (fun h3 : term145 P x y z => @lem112811 P x y z h1 h2) (fun h3 : False => @lem111978 P x y z h2)). Qed.
Lemma lem112813 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term145 P x y z) : False.
Proof. exact (EQ_MP (@lem112812 P x y z h1 h2) (@lem111978 P x y z h2)). Qed.
Lemma lem112814 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term145 P x y z) : term17 = False.
Proof. exact (prop_ext (fun h3 : term17 => @lem112813 P x y z h1 h2) (fun h3 : False => @lem111888 h1)). Qed.
Lemma lem112815 (P : type1601) (x : nat) (y : nat) (z : nat) (h1 : term17) (h2 : term145 P x y z) : False.
Proof. exact (EQ_MP (@lem112814 P x y z h1 h2) (@lem111888 h1)). Qed.
Lemma lem112816 (P : type1601) (x : nat) (y : nat) (h1 : term17) (h2 : term148 P x y) : False.
Proof. exact (ex_elim (@lem111867 P x y h2) (fun z : nat => fun h0 : term147 P x y z => @lem112815 P x y z h1 h0)). Qed.
Lemma lem112817 (P : type1601) (x : nat) (h1 : term17) (h2 : term150 P x) : False.
Proof. exact (ex_elim (@lem111866 P x h2) (fun y : nat => fun h0 : term149 P x y => @lem112816 P x y h1 h0)). Qed.
Lemma lem112818 (P : type1601) (h1 : term17) (h2 : term152 P) : False.
Proof. exact (ex_elim (@lem111865 P h2) (fun x : nat => fun h0 : term151 P x => @lem112817 P x h1 h0)). Qed.
Lemma lem112819 (h1 : term17) (h2 : term10) : False.
Proof. exact (ex_elim (@lem111796 h2) (fun P : type1601 => fun h0 : term153 P => @lem112818 P h1 h0)). Qed.
Lemma lem112820 (h1 : term17) (h2 : term10) : term17 = False.
Proof. exact (prop_ext (fun h3 : term17 => @lem112819 h1 h2) (fun h3 : False => @lem111864 h1)). Qed.
Lemma lem112821 (h1 : term17) (h2 : term10) : False.
Proof. exact (EQ_MP (@lem112820 h1 h2) (@lem111864 h1)). Qed.
Lemma lem112822 (h1 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem112821 h0 h1). Qed.
Lemma lem112823 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem112824 (h1 : term10) : term16.
Proof. exact (EQ_MP (@lem112823) (@lem112822 h1)). Qed.
Lemma lem112825 : term19.
Proof. exact (fun h0 : term10 => @lem112824 h0). Qed.
Lemma lem112826 : term11.
Proof. exact (EQ_MP (@lem111456) (@lem112825)). Qed.
Lemma lem112828 : term11.
Proof. exact (@lem111172 (@lem112826)). Qed.
Lemma lem112829 (h1 : term10) : term15.
Proof. exact (@lem112828 (@lem111157 h1)). Qed.
Lemma lem112830 (h1 : term10) : False.
Proof. exact (@lem112829 h1 (@lem96155)). Qed.
Lemma lem112831 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem112830 h1) (fun h2 : False => @lem111157 h1)). Qed.
Lemma lem112832 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem112831 h1) (@lem111157 h1)). Qed.
Lemma lem112833 : term9.
Proof. exact (fun h0 : term10 => @lem112832 h0). Qed.
Lemma lem112834 : term8.
Proof. exact (EQ_MP (@lem111156) (@lem112833)). Qed.
