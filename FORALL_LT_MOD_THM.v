Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_LT_MOD_THM_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import LT_spec.
Require Import MOD_EQ_SELF_spec.
Require Import MOD_LT_EQ_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16464_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
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
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem238185 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem238186 : term1 = term2.
Proof. exact (@lem238185 term1). Qed.
Lemma lem238187 : term2 = term1.
Proof. exact (SYM (@lem238186)). Qed.
Lemma lem238188 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem238191 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem238192 : term5.
Proof. exact (fun h0 : term4 => @lem238191 h0). Qed.
Lemma lem238193 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem238194 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem238195 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem238193 h2 (@lem238194 h1)). Qed.
Lemma lem238196 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem238195 h1 h0). Qed.
Lemma lem238197 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem238198 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem238196 h1 (@lem238197 h2)). Qed.
Lemma lem238199 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem238198 h0 h1). Qed.
Lemma lem238200 : term7.
Proof. exact (fun h0 : term5 => @lem238199 h0). Qed.
Lemma lem238203 : term5.
Proof. exact (@lem238200 (@lem238192)). Qed.
Lemma lem238249 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem238250 : term8 = term9.
Proof. exact (@lem238249 term10). Qed.
Lemma lem238258 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem16464 t)). Qed.
Lemma lem238259 (m : nat) : ((term11 m) = False) = (term12 m).
Proof. exact (@lem238258 (term11 m)). Qed.
Lemma lem238260 : term13 = term14.
Proof. exact (fun_ext (fun m : nat => @lem238259 m)). Qed.
Lemma lem238261 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem238262 : term15 = term16.
Proof. exact (MK_COMB (@lem238261) (@lem238260)). Qed.
Lemma lem238267 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem238268 : term17 = term18.
Proof. exact (MK_COMB (@lem238267) (@lem238262)). Qed.
Lemma lem238279 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem238280 : term10 = term20.
Proof. exact (MK_COMB (@lem238268) (@lem238279)). Qed.
Lemma lem238283 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem238284 : term9 = term21.
Proof. exact (MK_COMB (@lem238283) (@lem238280)). Qed.
Lemma lem238285 : term8 = term21.
Proof. exact (TRANS (@lem238250) (@lem238284)). Qed.
Lemma lem238286 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem238287 : term23 = term24.
Proof. exact (MK_COMB (@lem238286) (@lem238285)). Qed.
Lemma lem238290 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem238291 : term26 = term27.
Proof. exact (MK_COMB (@lem238290) (@lem238287)). Qed.
Lemma lem238294 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem238301 : term4 = term29.
Proof. exact (MK_COMB (@lem238294) (@lem238291)). Qed.
Lemma lem238310 (m : nat) (n : nat) : ((term30 m n) = (term31 m n)) = ((term30 m n) = (term31 m n)).
Proof. exact (eq_refl ((term30 m n) = (term31 m n))). Qed.
Lemma lem238311 (m : nat) : (term32 m) = (term32 m).
Proof. exact (fun_ext (fun n : nat => @lem238310 m n)). Qed.
Lemma lem238312 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem238313 (m : nat) : (term33 m) = (term33 m).
Proof. exact (MK_COMB (@lem238312) (@lem238311 m)). Qed.
Lemma lem238314 : term34 = term34.
Proof. exact (fun_ext (fun m : nat => @lem238313 m)). Qed.
Lemma lem238315 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem238316 : term19 = term19.
Proof. exact (MK_COMB (@lem238315) (@lem238314)). Qed.
Lemma lem238319 (m : nat) : (term12 m) = (term12 m).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem238320 : term14 = term14.
Proof. exact (fun_ext (fun m : nat => @lem238319 m)). Qed.
Lemma lem238321 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem238322 : term16 = term16.
Proof. exact (MK_COMB (@lem238321) (@lem238320)). Qed.
Lemma lem238323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem238324 : term18 = term18.
Proof. exact (MK_COMB (@lem238323) (@lem238322)). Qed.
Lemma lem238325 : term20 = term20.
Proof. exact (MK_COMB (@lem238324) (@lem238316)). Qed.
Lemma lem238326 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem238327 : term21 = term21.
Proof. exact (MK_COMB (@lem238326) (@lem238325)). Qed.
Lemma lem238336 (m : nat) (n : nat) : (((Nat.modulo m n) = m) = (term35 m n)) = (((Nat.modulo m n) = m) = (term35 m n)).
Proof. exact (eq_refl (((Nat.modulo m n) = m) = (term35 m n))). Qed.
Lemma lem238337 (m : nat) : (term36 m) = (term36 m).
Proof. exact (fun_ext (fun n : nat => @lem238336 m n)). Qed.
Lemma lem238338 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem238339 (m : nat) : (term37 m) = (term37 m).
Proof. exact (MK_COMB (@lem238338) (@lem238337 m)). Qed.
Lemma lem238340 : term38 = term38.
Proof. exact (fun_ext (fun m : nat => @lem238339 m)). Qed.
Lemma lem238341 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem238342 : term39 = term39.
Proof. exact (MK_COMB (@lem238341) (@lem238340)). Qed.
Lemma lem238343 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem238344 : term22 = term22.
Proof. exact (MK_COMB (@lem238343) (@lem238342)). Qed.
Lemma lem238345 : term24 = term24.
Proof. exact (MK_COMB (@lem238344) (@lem238327)). Qed.
Lemma lem238352 (m : nat) (n : nat) : ((term40 m n) = (term41 n)) = ((term40 m n) = (term41 n)).
Proof. exact (eq_refl ((term40 m n) = (term41 n))). Qed.
Lemma lem238353 (m : nat) : (term42 m) = (term42 m).
Proof. exact (fun_ext (fun n : nat => @lem238352 m n)). Qed.
Lemma lem238354 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem238355 (m : nat) : (term43 m) = (term43 m).
Proof. exact (MK_COMB (@lem238354) (@lem238353 m)). Qed.
Lemma lem238356 : term44 = term44.
Proof. exact (fun_ext (fun m : nat => @lem238355 m)). Qed.
Lemma lem238357 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem238358 : term45 = term45.
Proof. exact (MK_COMB (@lem238357) (@lem238356)). Qed.
Lemma lem238359 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem238360 : term25 = term25.
Proof. exact (MK_COMB (@lem238359) (@lem238358)). Qed.
Lemma lem238361 : term27 = term27.
Proof. exact (MK_COMB (@lem238360) (@lem238345)). Qed.
Lemma lem238362 (P : nat -> Prop) (a : nat) (n : nat) : (term46 P a n) = (term46 P a n).
Proof. exact (eq_refl (term46 P a n)). Qed.
Lemma lem238363 (P : nat -> Prop) (n : nat) : (term47 P n) = (term47 P n).
Proof. exact (fun_ext (fun a : nat => @lem238362 P a n)). Qed.
Lemma lem238364 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem238365 (P : nat -> Prop) (n : nat) : (term48 P n) = (term48 P n).
Proof. exact (MK_COMB (@lem238364) (@lem238363 P n)). Qed.
Lemma lem238368 (n : nat) : (term49 n) = (term49 n).
Proof. exact (eq_refl (term49 n)). Qed.
Lemma lem238369 (P : nat -> Prop) (n : nat) : (term50 P n) = (term50 P n).
Proof. exact (MK_COMB (@lem238368 n) (@lem238365 P n)). Qed.
Lemma lem238374 (n : nat) (P : nat -> Prop) (a : nat) : (term51 n P a) = (term51 n P a).
Proof. exact (eq_refl (term51 n P a)). Qed.
Lemma lem238375 (n : nat) (P : nat -> Prop) : (term52 n P) = (term52 n P).
Proof. exact (fun_ext (fun a : nat => @lem238374 n P a)). Qed.
Lemma lem238376 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem238377 (n : nat) (P : nat -> Prop) : (term53 n P) = (term53 n P).
Proof. exact (MK_COMB (@lem238376) (@lem238375 n P)). Qed.
Lemma lem238378 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem238379 (n : nat) (P : nat -> Prop) : (term54 n P) = (term54 n P).
Proof. exact (MK_COMB (@lem238378) (@lem238377 n P)). Qed.
Lemma lem238380 (P : nat -> Prop) (n : nat) : ((term53 n P) = (term50 P n)) = ((term53 n P) = (term50 P n)).
Proof. exact (MK_COMB (@lem238379 n P) (@lem238369 P n)). Qed.
Lemma lem238381 (P : nat -> Prop) : (term55 P) = (term55 P).
Proof. exact (fun_ext (fun n : nat => @lem238380 P n)). Qed.
Lemma lem238382 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem238383 (P : nat -> Prop) : (term56 P) = (term56 P).
Proof. exact (MK_COMB (@lem238382) (@lem238381 P)). Qed.
Lemma lem238384 : term57 = term57.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem238383 P)). Qed.
Lemma lem238385 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem238386 : term1 = term1.
Proof. exact (MK_COMB (@lem238385) (@lem238384)). Qed.
Lemma lem238387 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem238388 : term3 = term3.
Proof. exact (MK_COMB (@lem238387) (@lem238386)). Qed.
Lemma lem238389 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem238390 : term28 = term28.
Proof. exact (MK_COMB (@lem238389) (@lem238388)). Qed.
Lemma lem238391 : term29 = term29.
Proof. exact (MK_COMB (@lem238390) (@lem238361)). Qed.
Lemma lem238476 : term4 = term29.
Proof. exact (TRANS (@lem238301) (@lem238391)). Qed.
Lemma lem238477 : term29 = term4.
Proof. exact (SYM (@lem238476)). Qed.
Lemma lem238478 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem238479 (h1 : term45) : term45.
Proof. exact (h1). Qed.
Lemma lem238480 (h1 : term39) : term39.
Proof. exact (h1). Qed.
Lemma lem238481 (h1 : term20) : term20.
Proof. exact (h1). Qed.
Lemma lem238490 (n : nat) (P : nat -> Prop) (a : nat) : (term58 n P a) = (term59 n P a).
Proof. exact (@lem17362 (Peano.lt a n) (P a)). Qed.
Lemma lem238495 (n : nat) (P : nat -> Prop) (a : nat) : (term51 n P a) = (term60 n P a).
Proof. exact (@lem17265 (Peano.lt a n) (P a)). Qed.
Lemma lem238496 (P : nat -> Prop) : (term61 P) = (term62 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem238497 (n : nat) (P : nat -> Prop) : (term63 n P) = (term64 n P).
Proof. exact (@lem238496 (term52 n P)). Qed.
Lemma lem238498 (n : nat) (P : nat -> Prop) (a : nat) : (term65 n P a) = (term51 n P a).
Proof. exact (eq_refl (term65 n P a)). Qed.
Lemma lem238499 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem238500 (n : nat) (P : nat -> Prop) (a : nat) : (term66 n P a) = (term58 n P a).
Proof. exact (MK_COMB (@lem238499) (@lem238498 n P a)). Qed.
Lemma lem238501 (n : nat) (P : nat -> Prop) (a : nat) : (term66 n P a) = (term59 n P a).
Proof. exact (TRANS (@lem238500 n P a) (@lem238490 n P a)). Qed.
Lemma lem238502 (n : nat) (P : nat -> Prop) : (term67 n P) = (term68 n P).
Proof. exact (fun_ext (fun a : nat => @lem238501 n P a)). Qed.
Lemma lem238503 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem238504 (n : nat) (P : nat -> Prop) : (term64 n P) = (term69 n P).
Proof. exact (MK_COMB (@lem238503) (@lem238502 n P)). Qed.
Lemma lem238505 (n : nat) (P : nat -> Prop) : (term63 n P) = (term69 n P).
Proof. exact (TRANS (@lem238497 n P) (@lem238504 n P)). Qed.
Lemma lem238506 (n : nat) (P : nat -> Prop) : (term52 n P) = (term70 n P).
Proof. exact (fun_ext (fun a : nat => @lem238495 n P a)). Qed.
Lemma lem238507 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem238508 (n : nat) (P : nat -> Prop) : (term53 n P) = (term71 n P).
Proof. exact (MK_COMB (@lem238507) (@lem238506 n P)). Qed.
Lemma lem238512 (P : nat -> Prop) (a : nat) (n : nat) : (term46 P a n) = (term46 P a n).
Proof. exact (eq_refl (term46 P a n)). Qed.
Lemma lem238513 (P : nat -> Prop) : (term61 P) = (term62 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem238514 (P : nat -> Prop) (n : nat) : (term72 P n) = (term73 P n).
Proof. exact (@lem238513 (term47 P n)). Qed.
Lemma lem238515 (P : nat -> Prop) (a : nat) (n : nat) : (term74 P n a) = (term46 P a n).
Proof. exact (eq_refl (term74 P n a)). Qed.
Lemma lem238516 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem238518 (P : nat -> Prop) (a : nat) (n : nat) : (term75 P n a) = (term76 P a n).
Proof. exact (MK_COMB (@lem238516) (@lem238515 P a n)). Qed.
Lemma lem238519 (P : nat -> Prop) (n : nat) : (term77 P n) = (term78 P n).
Proof. exact (fun_ext (fun a : nat => @lem238518 P a n)). Qed.
Lemma lem238520 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem238521 (P : nat -> Prop) (n : nat) : (term73 P n) = (term79 P n).
Proof. exact (MK_COMB (@lem238520) (@lem238519 P n)). Qed.
Lemma lem238522 (P : nat -> Prop) (n : nat) : (term72 P n) = (term79 P n).
Proof. exact (TRANS (@lem238514 P n) (@lem238521 P n)). Qed.
Lemma lem238523 (P : nat -> Prop) (n : nat) : (term47 P n) = (term47 P n).
Proof. exact (fun_ext (fun a : nat => @lem238512 P a n)). Qed.
Lemma lem238524 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem238525 (P : nat -> Prop) (n : nat) : (term48 P n) = (term48 P n).
Proof. exact (MK_COMB (@lem238524) (@lem238523 P n)). Qed.
Lemma lem238527 (n : nat) : (term80 n) = (term80 n).
Proof. exact (eq_refl (term80 n)). Qed.
Lemma lem238528 (P : nat -> Prop) (n : nat) : (term81 P n) = (term82 P n).
Proof. exact (MK_COMB (@lem238527 n) (@lem238522 P n)). Qed.
Lemma lem238529 (P : nat -> Prop) (n : nat) : (term83 P n) = (term81 P n).
Proof. exact (@lem17160 (n = (NUMERAL 0)) (term48 P n)). Qed.
Lemma lem238530 (P : nat -> Prop) (n : nat) : (term83 P n) = (term82 P n).
Proof. exact (TRANS (@lem238529 P n) (@lem238528 P n)). Qed.
Lemma lem238532 (n : nat) : (term49 n) = (term49 n).
Proof. exact (eq_refl (term49 n)). Qed.
Lemma lem238533 (P : nat -> Prop) (n : nat) : (term50 P n) = (term50 P n).
Proof. exact (MK_COMB (@lem238532 n) (@lem238525 P n)). Qed.
Lemma lem238534 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem238535 (n : nat) (P : nat -> Prop) : (term84 n P) = (term85 n P).
Proof. exact (MK_COMB (@lem238534) (@lem238505 n P)). Qed.
Lemma lem238536 (P : nat -> Prop) (n : nat) : (term86 P n) = (term87 P n).
Proof. exact (MK_COMB (@lem238535 n P) (@lem238533 P n)). Qed.
Lemma lem238537 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem238538 (n : nat) (P : nat -> Prop) : (term88 n P) = (term89 n P).
Proof. exact (MK_COMB (@lem238537) (@lem238508 n P)). Qed.
Lemma lem238539 (P : nat -> Prop) (n : nat) : (term90 P n) = (term91 P n).
Proof. exact (MK_COMB (@lem238538 n P) (@lem238530 P n)). Qed.
Lemma lem238540 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem238541 (P : nat -> Prop) (n : nat) : (term92 P n) = (term93 P n).
Proof. exact (MK_COMB (@lem238540) (@lem238539 P n)). Qed.
Lemma lem238542 (P : nat -> Prop) (n : nat) : (term94 P n) = (term95 P n).
Proof. exact (MK_COMB (@lem238541 P n) (@lem238536 P n)). Qed.
Lemma lem238543 (P : nat -> Prop) (n : nat) : (term96 P n) = (term94 P n).
Proof. exact (@lem17646 (term53 n P) (term50 P n)). Qed.
Lemma lem238544 (P : nat -> Prop) (n : nat) : (term96 P n) = (term95 P n).
Proof. exact (TRANS (@lem238543 P n) (@lem238542 P n)). Qed.
Lemma lem238545 (P : nat -> Prop) : (term61 P) = (term62 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem238546 (P : nat -> Prop) : (term97 P) = (term98 P).
Proof. exact (@lem238545 (term55 P)). Qed.
Lemma lem238547 (P : nat -> Prop) (n : nat) : (term99 P n) = ((term53 n P) = (term50 P n)).
Proof. exact (eq_refl (term99 P n)). Qed.
Lemma lem238548 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem238549 (P : nat -> Prop) (n : nat) : (term100 P n) = (term96 P n).
Proof. exact (MK_COMB (@lem238548) (@lem238547 P n)). Qed.
Lemma lem238550 (P : nat -> Prop) (n : nat) : (term100 P n) = (term95 P n).
Proof. exact (TRANS (@lem238549 P n) (@lem238544 P n)). Qed.
Lemma lem238551 (P : nat -> Prop) : (term101 P) = (term102 P).
Proof. exact (fun_ext (fun n : nat => @lem238550 P n)). Qed.
Lemma lem238552 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem238553 (P : nat -> Prop) : (term98 P) = (term103 P).
Proof. exact (MK_COMB (@lem238552) (@lem238551 P)). Qed.
Lemma lem238554 (P : nat -> Prop) : (term97 P) = (term103 P).
Proof. exact (TRANS (@lem238546 P) (@lem238553 P)). Qed.
Lemma lem238555 (P : type993) : (term104 P) = (term105 P).
Proof. exact (@lem18392 (nat -> Prop) P). Qed.
Lemma lem238556 : term3 = term106.
Proof. exact (@lem238555 term57). Qed.
Lemma lem238557 (P : nat -> Prop) : (term107 P) = (term56 P).
Proof. exact (eq_refl (term107 P)). Qed.
Lemma lem238558 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem238559 (P : nat -> Prop) : (term108 P) = (term97 P).
Proof. exact (MK_COMB (@lem238558) (@lem238557 P)). Qed.
Lemma lem238560 (P : nat -> Prop) : (term108 P) = (term103 P).
Proof. exact (TRANS (@lem238559 P) (@lem238554 P)). Qed.
Lemma lem238561 : term109 = term110.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem238560 P)). Qed.
Lemma lem238562 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem238563 : term106 = term111.
Proof. exact (MK_COMB (@lem238562) (@lem238561)). Qed.
Lemma lem238564 : term3 = term111.
Proof. exact (TRANS (@lem238556) (@lem238563)). Qed.
Lemma lem238570 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term112 A P Q) = (term113 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem238571 (P : nat -> Prop) (Q : nat -> Prop) : (term114 P Q) = (term115 P Q).
Proof. exact (@lem238570 nat P Q). Qed.
Lemma lem238572 (P : nat -> Prop) : (term116 P) = (term117 P).
Proof. exact (@lem238571 (term118 P) (term119 P)). Qed.
Lemma lem238573 (P : nat -> Prop) (n : nat) : (term120 P n) = (term91 P n).
Proof. exact (eq_refl (term120 P n)). Qed.
Lemma lem238574 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem238575 (P : nat -> Prop) (n : nat) : (term121 P n) = (term93 P n).
Proof. exact (MK_COMB (@lem238574) (@lem238573 P n)). Qed.
Lemma lem238576 (P : nat -> Prop) (n : nat) : (term122 P n) = (term87 P n).
Proof. exact (eq_refl (term122 P n)). Qed.
Lemma lem238577 (P : nat -> Prop) (n : nat) : (term123 P n) = (term95 P n).
Proof. exact (MK_COMB (@lem238575 P n) (@lem238576 P n)). Qed.
Lemma lem238578 (P : nat -> Prop) : (term124 P) = (term102 P).
Proof. exact (fun_ext (fun n : nat => @lem238577 P n)). Qed.
Lemma lem238579 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem238580 (P : nat -> Prop) : (term116 P) = (term103 P).
Proof. exact (MK_COMB (@lem238579) (@lem238578 P)). Qed.
Lemma lem238581 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem238582 (P : nat -> Prop) : (term125 P) = (term126 P).
Proof. exact (MK_COMB (@lem238581) (@lem238580 P)). Qed.
Lemma lem238583 (P : nat -> Prop) (n : nat) : (term120 P n) = (term91 P n).
Proof. exact (eq_refl (term120 P n)). Qed.
Lemma lem238584 (P : nat -> Prop) : (term127 P) = (term118 P).
Proof. exact (fun_ext (fun n : nat => @lem238583 P n)). Qed.
Lemma lem238585 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem238586 (P : nat -> Prop) : (term128 P) = (term129 P).
Proof. exact (MK_COMB (@lem238585) (@lem238584 P)). Qed.
Lemma lem238587 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem238588 (P : nat -> Prop) : (term130 P) = (term131 P).
Proof. exact (MK_COMB (@lem238587) (@lem238586 P)). Qed.
Lemma lem238589 (P : nat -> Prop) (n : nat) : (term122 P n) = (term87 P n).
Proof. exact (eq_refl (term122 P n)). Qed.
Lemma lem238590 (P : nat -> Prop) : (term132 P) = (term119 P).
Proof. exact (fun_ext (fun n : nat => @lem238589 P n)). Qed.
Lemma lem238591 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem238592 (P : nat -> Prop) : (term133 P) = (term134 P).
Proof. exact (MK_COMB (@lem238591) (@lem238590 P)). Qed.
Lemma lem238593 (P : nat -> Prop) : (term117 P) = (term135 P).
Proof. exact (MK_COMB (@lem238588 P) (@lem238592 P)). Qed.
Lemma lem238594 (P : nat -> Prop) : ((term116 P) = (term117 P)) = ((term103 P) = (term135 P)).
Proof. exact (MK_COMB (@lem238582 P) (@lem238593 P)). Qed.
Lemma lem238595 (P : nat -> Prop) : (term103 P) = (term135 P).
Proof. exact (EQ_MP (@lem238594 P) (@lem238572 P)). Qed.
Lemma lem238780 : term110 = term136.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem238595 P)). Qed.
Lemma lem238781 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem238782 : term111 = term137.
Proof. exact (MK_COMB (@lem238781) (@lem238780)). Qed.
Lemma lem238784 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term112 A P Q) = (term113 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem238785 (P : type993) (Q : type993) : (term138 P Q) = (term139 P Q).
Proof. exact (@lem238784 (nat -> Prop) P Q). Qed.
Lemma lem238786 : term140 = term141.
Proof. exact (@lem238785 term142 term143). Qed.
Lemma lem238787 (P : nat -> Prop) : (term144 P) = (term129 P).
Proof. exact (eq_refl (term144 P)). Qed.
Lemma lem238788 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem238789 (P : nat -> Prop) : (term145 P) = (term131 P).
Proof. exact (MK_COMB (@lem238788) (@lem238787 P)). Qed.
Lemma lem238790 (P : nat -> Prop) : (term146 P) = (term134 P).
Proof. exact (eq_refl (term146 P)). Qed.
Lemma lem238791 (P : nat -> Prop) : (term147 P) = (term135 P).
Proof. exact (MK_COMB (@lem238789 P) (@lem238790 P)). Qed.
Lemma lem238792 : term148 = term136.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem238791 P)). Qed.
Lemma lem238793 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem238794 : term140 = term137.
Proof. exact (MK_COMB (@lem238793) (@lem238792)). Qed.
Lemma lem238795 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem238796 : term149 = term150.
Proof. exact (MK_COMB (@lem238795) (@lem238794)). Qed.
Lemma lem238797 (P : nat -> Prop) : (term144 P) = (term129 P).
Proof. exact (eq_refl (term144 P)). Qed.
Lemma lem238798 : term151 = term142.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem238797 P)). Qed.
Lemma lem238799 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem238800 : term152 = term153.
Proof. exact (MK_COMB (@lem238799) (@lem238798)). Qed.
Lemma lem238801 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem238802 : term154 = term155.
Proof. exact (MK_COMB (@lem238801) (@lem238800)). Qed.
Lemma lem238803 (P : nat -> Prop) : (term146 P) = (term134 P).
Proof. exact (eq_refl (term146 P)). Qed.
Lemma lem238804 : term156 = term143.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem238803 P)). Qed.
Lemma lem238805 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem238806 : term157 = term158.
Proof. exact (MK_COMB (@lem238805) (@lem238804)). Qed.
Lemma lem238807 : term141 = term159.
Proof. exact (MK_COMB (@lem238802) (@lem238806)). Qed.
Lemma lem238808 : (term140 = term141) = (term137 = term159).
Proof. exact (MK_COMB (@lem238796) (@lem238807)). Qed.
Lemma lem238809 : term137 = term159.
Proof. exact (EQ_MP (@lem238808) (@lem238786)). Qed.
Lemma lem239002 : term111 = term159.
Proof. exact (TRANS (@lem238782) (@lem238809)). Qed.
Lemma lem239004 {A : Type'} (P : Prop) (Q : A -> Prop) : (term160 A P Q) = (term161 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem239005 (P : Prop) (Q : nat -> Prop) : (term162 P Q) = (term163 P Q).
Proof. exact (@lem239004 nat P Q). Qed.
Lemma lem239006 (P : nat -> Prop) (n : nat) : (term164 P n) = (term165 P n).
Proof. exact (@lem239005 (term41 n) (term78 P n)). Qed.
Lemma lem239007 (P : nat -> Prop) (a : nat) (n : nat) : (term166 P n a) = (term76 P a n).
Proof. exact (eq_refl (term166 P n a)). Qed.
Lemma lem239008 (P : nat -> Prop) (n : nat) : (term167 P n) = (term78 P n).
Proof. exact (fun_ext (fun a : nat => @lem239007 P a n)). Qed.
Lemma lem239009 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem239010 (P : nat -> Prop) (n : nat) : (term168 P n) = (term79 P n).
Proof. exact (MK_COMB (@lem239009) (@lem239008 P n)). Qed.
Lemma lem239011 (n : nat) : (term80 n) = (term80 n).
Proof. exact (eq_refl (term80 n)). Qed.
Lemma lem239012 (P : nat -> Prop) (n : nat) : (term164 P n) = (term82 P n).
Proof. exact (MK_COMB (@lem239011 n) (@lem239010 P n)). Qed.
Lemma lem239013 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem239014 (P : nat -> Prop) (n : nat) : (term169 P n) = (term170 P n).
Proof. exact (MK_COMB (@lem239013) (@lem239012 P n)). Qed.
Lemma lem239015 (P : nat -> Prop) (a : nat) (n : nat) : (term166 P n a) = (term76 P a n).
Proof. exact (eq_refl (term166 P n a)). Qed.
Lemma lem239016 (n : nat) : (term80 n) = (term80 n).
Proof. exact (eq_refl (term80 n)). Qed.
Lemma lem239017 (P : nat -> Prop) (a : nat) (n : nat) : (term171 P n a) = (term172 P a n).
Proof. exact (MK_COMB (@lem239016 n) (@lem239015 P a n)). Qed.
Lemma lem239018 (P : nat -> Prop) (n : nat) : (term173 P n) = (term174 P n).
Proof. exact (fun_ext (fun a : nat => @lem239017 P a n)). Qed.
Lemma lem239019 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem239020 (P : nat -> Prop) (n : nat) : (term165 P n) = (term175 P n).
Proof. exact (MK_COMB (@lem239019) (@lem239018 P n)). Qed.
Lemma lem239021 (P : nat -> Prop) (n : nat) : ((term164 P n) = (term165 P n)) = ((term82 P n) = (term175 P n)).
Proof. exact (MK_COMB (@lem239014 P n) (@lem239020 P n)). Qed.
Lemma lem239022 (P : nat -> Prop) (n : nat) : (term82 P n) = (term175 P n).
Proof. exact (EQ_MP (@lem239021 P n) (@lem239006 P n)). Qed.
Lemma lem239023 (n : nat) (P : nat -> Prop) : (term89 n P) = (term89 n P).
Proof. exact (eq_refl (term89 n P)). Qed.
Lemma lem239024 (P : nat -> Prop) (n : nat) : (term91 P n) = (term176 P n).
Proof. exact (MK_COMB (@lem239023 n P) (@lem239022 P n)). Qed.
Lemma lem239026 {A : Type'} (P : Prop) (Q : A -> Prop) : (term160 A P Q) = (term161 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem239027 (P : Prop) (Q : nat -> Prop) : (term162 P Q) = (term163 P Q).
Proof. exact (@lem239026 nat P Q). Qed.
Lemma lem239028 (P : nat -> Prop) (n : nat) : (term177 P n) = (term178 P n).
Proof. exact (@lem239027 (term71 n P) (term174 P n)). Qed.
Lemma lem239029 (P : nat -> Prop) (a : nat) (n : nat) : (term179 P n a) = (term172 P a n).
Proof. exact (eq_refl (term179 P n a)). Qed.
Lemma lem239030 (P : nat -> Prop) (n : nat) : (term180 P n) = (term174 P n).
Proof. exact (fun_ext (fun a : nat => @lem239029 P a n)). Qed.
Lemma lem239031 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem239032 (P : nat -> Prop) (n : nat) : (term181 P n) = (term175 P n).
Proof. exact (MK_COMB (@lem239031) (@lem239030 P n)). Qed.
Lemma lem239033 (n : nat) (P : nat -> Prop) : (term89 n P) = (term89 n P).
Proof. exact (eq_refl (term89 n P)). Qed.
Lemma lem239034 (P : nat -> Prop) (n : nat) : (term177 P n) = (term176 P n).
Proof. exact (MK_COMB (@lem239033 n P) (@lem239032 P n)). Qed.
Lemma lem239035 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem239036 (P : nat -> Prop) (n : nat) : (term182 P n) = (term183 P n).
Proof. exact (MK_COMB (@lem239035) (@lem239034 P n)). Qed.
Lemma lem239037 (P : nat -> Prop) (a : nat) (n : nat) : (term179 P n a) = (term172 P a n).
Proof. exact (eq_refl (term179 P n a)). Qed.
Lemma lem239038 (n : nat) (P : nat -> Prop) : (term89 n P) = (term89 n P).
Proof. exact (eq_refl (term89 n P)). Qed.
Lemma lem239039 (P : nat -> Prop) (a : nat) (n : nat) : (term184 P n a) = (term185 P a n).
Proof. exact (MK_COMB (@lem239038 n P) (@lem239037 P a n)). Qed.
Lemma lem239040 (P : nat -> Prop) (n : nat) : (term186 P n) = (term187 P n).
Proof. exact (fun_ext (fun a : nat => @lem239039 P a n)). Qed.
Lemma lem239041 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem239042 (P : nat -> Prop) (n : nat) : (term178 P n) = (term188 P n).
Proof. exact (MK_COMB (@lem239041) (@lem239040 P n)). Qed.
Lemma lem239043 (P : nat -> Prop) (n : nat) : ((term177 P n) = (term178 P n)) = ((term176 P n) = (term188 P n)).
Proof. exact (MK_COMB (@lem239036 P n) (@lem239042 P n)). Qed.
Lemma lem239044 (P : nat -> Prop) (n : nat) : (term176 P n) = (term188 P n).
Proof. exact (EQ_MP (@lem239043 P n) (@lem239028 P n)). Qed.
Lemma lem239045 (P : nat -> Prop) (n : nat) : (term91 P n) = (term188 P n).
Proof. exact (TRANS (@lem239024 P n) (@lem239044 P n)). Qed.
Lemma lem239046 (P : nat -> Prop) : (term118 P) = (term189 P).
Proof. exact (fun_ext (fun n : nat => @lem239045 P n)). Qed.
Lemma lem239047 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem239048 (P : nat -> Prop) : (term129 P) = (term190 P).
Proof. exact (MK_COMB (@lem239047) (@lem239046 P)). Qed.
Lemma lem239049 : term142 = term191.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem239048 P)). Qed.
Lemma lem239050 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem239051 : term153 = term192.
Proof. exact (MK_COMB (@lem239050) (@lem239049)). Qed.
Lemma lem239052 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem239053 : term155 = term193.
Proof. exact (MK_COMB (@lem239052) (@lem239051)). Qed.
Lemma lem239055 {A : Type'} (P : A -> Prop) (Q : Prop) : (term194 A P Q) = (term195 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem239056 (P : nat -> Prop) (Q : Prop) : (term196 P Q) = (term197 P Q).
Proof. exact (@lem239055 nat P Q). Qed.
Lemma lem239057 (P : nat -> Prop) (n : nat) : (term198 P n) = (term199 P n).
Proof. exact (@lem239056 (term68 n P) (term50 P n)). Qed.
Lemma lem239058 (n : nat) (P : nat -> Prop) (a : nat) : (term200 n P a) = (term59 n P a).
Proof. exact (eq_refl (term200 n P a)). Qed.
Lemma lem239059 (n : nat) (P : nat -> Prop) : (term201 n P) = (term68 n P).
Proof. exact (fun_ext (fun a : nat => @lem239058 n P a)). Qed.
Lemma lem239060 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem239061 (n : nat) (P : nat -> Prop) : (term202 n P) = (term69 n P).
Proof. exact (MK_COMB (@lem239060) (@lem239059 n P)). Qed.
Lemma lem239062 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem239063 (n : nat) (P : nat -> Prop) : (term203 n P) = (term85 n P).
Proof. exact (MK_COMB (@lem239062) (@lem239061 n P)). Qed.
Lemma lem239064 (P : nat -> Prop) (n : nat) : (term50 P n) = (term50 P n).
Proof. exact (eq_refl (term50 P n)). Qed.
Lemma lem239065 (P : nat -> Prop) (n : nat) : (term198 P n) = (term87 P n).
Proof. exact (MK_COMB (@lem239063 n P) (@lem239064 P n)). Qed.
Lemma lem239066 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem239067 (P : nat -> Prop) (n : nat) : (term204 P n) = (term205 P n).
Proof. exact (MK_COMB (@lem239066) (@lem239065 P n)). Qed.
Lemma lem239068 (n : nat) (P : nat -> Prop) (a : nat) : (term200 n P a) = (term59 n P a).
Proof. exact (eq_refl (term200 n P a)). Qed.
Lemma lem239069 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem239070 (n : nat) (P : nat -> Prop) (a : nat) : (term206 n P a) = (term207 n P a).
Proof. exact (MK_COMB (@lem239069) (@lem239068 n P a)). Qed.
Lemma lem239071 (P : nat -> Prop) (n : nat) : (term50 P n) = (term50 P n).
Proof. exact (eq_refl (term50 P n)). Qed.
Lemma lem239072 (a : nat) (P : nat -> Prop) (n : nat) : (term208 a P n) = (term209 a P n).
Proof. exact (MK_COMB (@lem239070 n P a) (@lem239071 P n)). Qed.
Lemma lem239073 (P : nat -> Prop) (n : nat) : (term210 P n) = (term211 P n).
Proof. exact (fun_ext (fun a : nat => @lem239072 a P n)). Qed.
Lemma lem239074 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem239075 (P : nat -> Prop) (n : nat) : (term199 P n) = (term212 P n).
Proof. exact (MK_COMB (@lem239074) (@lem239073 P n)). Qed.
Lemma lem239076 (P : nat -> Prop) (n : nat) : ((term198 P n) = (term199 P n)) = ((term87 P n) = (term212 P n)).
Proof. exact (MK_COMB (@lem239067 P n) (@lem239075 P n)). Qed.
Lemma lem239077 (P : nat -> Prop) (n : nat) : (term87 P n) = (term212 P n).
Proof. exact (EQ_MP (@lem239076 P n) (@lem239057 P n)). Qed.
Lemma lem239078 (P : nat -> Prop) : (term119 P) = (term213 P).
Proof. exact (fun_ext (fun n : nat => @lem239077 P n)). Qed.
Lemma lem239079 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem239080 (P : nat -> Prop) : (term134 P) = (term214 P).
Proof. exact (MK_COMB (@lem239079) (@lem239078 P)). Qed.
Lemma lem239081 : term143 = term215.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem239080 P)). Qed.
Lemma lem239082 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem239083 : term158 = term216.
Proof. exact (MK_COMB (@lem239082) (@lem239081)). Qed.
Lemma lem239084 : term159 = term217.
Proof. exact (MK_COMB (@lem239053) (@lem239083)). Qed.
Lemma lem239086 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term113 A P Q) = (term112 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem239087 (P : type993) (Q : type993) : (term139 P Q) = (term138 P Q).
Proof. exact (@lem239086 (nat -> Prop) P Q). Qed.
Lemma lem239088 : term218 = term219.
Proof. exact (@lem239087 term191 term215). Qed.
Lemma lem239089 (P : nat -> Prop) : (term220 P) = (term190 P).
Proof. exact (eq_refl (term220 P)). Qed.
Lemma lem239090 : term221 = term191.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem239089 P)). Qed.
Lemma lem239091 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem239092 : term222 = term192.
Proof. exact (MK_COMB (@lem239091) (@lem239090)). Qed.
Lemma lem239093 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem239094 : term223 = term193.
Proof. exact (MK_COMB (@lem239093) (@lem239092)). Qed.
Lemma lem239095 (P : nat -> Prop) : (term224 P) = (term214 P).
Proof. exact (eq_refl (term224 P)). Qed.
Lemma lem239096 : term225 = term215.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem239095 P)). Qed.
Lemma lem239097 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem239098 : term226 = term216.
Proof. exact (MK_COMB (@lem239097) (@lem239096)). Qed.
Lemma lem239099 : term218 = term217.
Proof. exact (MK_COMB (@lem239094) (@lem239098)). Qed.
Lemma lem239100 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem239101 : term227 = term228.
Proof. exact (MK_COMB (@lem239100) (@lem239099)). Qed.
Lemma lem239102 (P : nat -> Prop) : (term220 P) = (term190 P).
Proof. exact (eq_refl (term220 P)). Qed.
Lemma lem239103 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem239104 (P : nat -> Prop) : (term229 P) = (term230 P).
Proof. exact (MK_COMB (@lem239103) (@lem239102 P)). Qed.
Lemma lem239105 (P : nat -> Prop) : (term224 P) = (term214 P).
Proof. exact (eq_refl (term224 P)). Qed.
Lemma lem239106 (P : nat -> Prop) : (term231 P) = (term232 P).
Proof. exact (MK_COMB (@lem239104 P) (@lem239105 P)). Qed.
Lemma lem239107 : term233 = term234.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem239106 P)). Qed.
Lemma lem239108 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem239109 : term219 = term235.
Proof. exact (MK_COMB (@lem239108) (@lem239107)). Qed.
Lemma lem239110 : (term218 = term219) = (term217 = term235).
Proof. exact (MK_COMB (@lem239101) (@lem239109)). Qed.
Lemma lem239111 : term217 = term235.
Proof. exact (EQ_MP (@lem239110) (@lem239088)). Qed.
Lemma lem239113 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term113 A P Q) = (term112 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem239114 (P : nat -> Prop) (Q : nat -> Prop) : (term115 P Q) = (term114 P Q).
Proof. exact (@lem239113 nat P Q). Qed.
Lemma lem239115 (P : nat -> Prop) : (term236 P) = (term237 P).
Proof. exact (@lem239114 (term189 P) (term213 P)). Qed.
Lemma lem239116 (P : nat -> Prop) (n : nat) : (term238 P n) = (term188 P n).
Proof. exact (eq_refl (term238 P n)). Qed.
Lemma lem239117 (P : nat -> Prop) : (term239 P) = (term189 P).
Proof. exact (fun_ext (fun n : nat => @lem239116 P n)). Qed.
Lemma lem239118 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem239119 (P : nat -> Prop) : (term240 P) = (term190 P).
Proof. exact (MK_COMB (@lem239118) (@lem239117 P)). Qed.
Lemma lem239120 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem239121 (P : nat -> Prop) : (term241 P) = (term230 P).
Proof. exact (MK_COMB (@lem239120) (@lem239119 P)). Qed.
Lemma lem239122 (P : nat -> Prop) (n : nat) : (term242 P n) = (term212 P n).
Proof. exact (eq_refl (term242 P n)). Qed.
Lemma lem239123 (P : nat -> Prop) : (term243 P) = (term213 P).
Proof. exact (fun_ext (fun n : nat => @lem239122 P n)). Qed.
Lemma lem239124 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem239125 (P : nat -> Prop) : (term244 P) = (term214 P).
Proof. exact (MK_COMB (@lem239124) (@lem239123 P)). Qed.
Lemma lem239126 (P : nat -> Prop) : (term236 P) = (term232 P).
Proof. exact (MK_COMB (@lem239121 P) (@lem239125 P)). Qed.
Lemma lem239127 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem239128 (P : nat -> Prop) : (term245 P) = (term246 P).
Proof. exact (MK_COMB (@lem239127) (@lem239126 P)). Qed.
Lemma lem239129 (P : nat -> Prop) (n : nat) : (term238 P n) = (term188 P n).
Proof. exact (eq_refl (term238 P n)). Qed.
Lemma lem239130 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem239131 (P : nat -> Prop) (n : nat) : (term247 P n) = (term248 P n).
Proof. exact (MK_COMB (@lem239130) (@lem239129 P n)). Qed.
Lemma lem239132 (P : nat -> Prop) (n : nat) : (term242 P n) = (term212 P n).
Proof. exact (eq_refl (term242 P n)). Qed.
Lemma lem239133 (P : nat -> Prop) (n : nat) : (term249 P n) = (term250 P n).
Proof. exact (MK_COMB (@lem239131 P n) (@lem239132 P n)). Qed.
Lemma lem239134 (P : nat -> Prop) : (term251 P) = (term252 P).
Proof. exact (fun_ext (fun n : nat => @lem239133 P n)). Qed.
Lemma lem239135 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem239136 (P : nat -> Prop) : (term237 P) = (term253 P).
Proof. exact (MK_COMB (@lem239135) (@lem239134 P)). Qed.
Lemma lem239137 (P : nat -> Prop) : ((term236 P) = (term237 P)) = ((term232 P) = (term253 P)).
Proof. exact (MK_COMB (@lem239128 P) (@lem239136 P)). Qed.
Lemma lem239138 (P : nat -> Prop) : (term232 P) = (term253 P).
Proof. exact (EQ_MP (@lem239137 P) (@lem239115 P)). Qed.
Lemma lem239140 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term113 A P Q) = (term112 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem239141 (P : nat -> Prop) (Q : nat -> Prop) : (term115 P Q) = (term114 P Q).
Proof. exact (@lem239140 nat P Q). Qed.
Lemma lem239142 (P : nat -> Prop) (n : nat) : (term254 P n) = (term255 P n).
Proof. exact (@lem239141 (term187 P n) (term211 P n)). Qed.
Lemma lem239143 (P : nat -> Prop) (a : nat) (n : nat) : (term256 P n a) = (term185 P a n).
Proof. exact (eq_refl (term256 P n a)). Qed.
Lemma lem239144 (P : nat -> Prop) (n : nat) : (term257 P n) = (term187 P n).
Proof. exact (fun_ext (fun a : nat => @lem239143 P a n)). Qed.
Lemma lem239145 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem239146 (P : nat -> Prop) (n : nat) : (term258 P n) = (term188 P n).
Proof. exact (MK_COMB (@lem239145) (@lem239144 P n)). Qed.
Lemma lem239147 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem239148 (P : nat -> Prop) (n : nat) : (term259 P n) = (term248 P n).
Proof. exact (MK_COMB (@lem239147) (@lem239146 P n)). Qed.
Lemma lem239149 (a : nat) (P : nat -> Prop) (n : nat) : (term260 P n a) = (term209 a P n).
Proof. exact (eq_refl (term260 P n a)). Qed.
Lemma lem239150 (P : nat -> Prop) (n : nat) : (term261 P n) = (term211 P n).
Proof. exact (fun_ext (fun a : nat => @lem239149 a P n)). Qed.
Lemma lem239151 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem239152 (P : nat -> Prop) (n : nat) : (term262 P n) = (term212 P n).
Proof. exact (MK_COMB (@lem239151) (@lem239150 P n)). Qed.
Lemma lem239153 (P : nat -> Prop) (n : nat) : (term254 P n) = (term250 P n).
Proof. exact (MK_COMB (@lem239148 P n) (@lem239152 P n)). Qed.
Lemma lem239154 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem239155 (P : nat -> Prop) (n : nat) : (term263 P n) = (term264 P n).
Proof. exact (MK_COMB (@lem239154) (@lem239153 P n)). Qed.
Lemma lem239156 (P : nat -> Prop) (a : nat) (n : nat) : (term256 P n a) = (term185 P a n).
Proof. exact (eq_refl (term256 P n a)). Qed.
Lemma lem239157 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem239158 (P : nat -> Prop) (a : nat) (n : nat) : (term265 P n a) = (term266 P a n).
Proof. exact (MK_COMB (@lem239157) (@lem239156 P a n)). Qed.
Lemma lem239159 (a : nat) (P : nat -> Prop) (n : nat) : (term260 P n a) = (term209 a P n).
Proof. exact (eq_refl (term260 P n a)). Qed.
Lemma lem239160 (a : nat) (P : nat -> Prop) (n : nat) : (term267 P n a) = (term268 a P n).
Proof. exact (MK_COMB (@lem239158 P a n) (@lem239159 a P n)). Qed.
Lemma lem239161 (P : nat -> Prop) (n : nat) : (term269 P n) = (term270 P n).
Proof. exact (fun_ext (fun a : nat => @lem239160 a P n)). Qed.
Lemma lem239162 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem239163 (P : nat -> Prop) (n : nat) : (term255 P n) = (term271 P n).
Proof. exact (MK_COMB (@lem239162) (@lem239161 P n)). Qed.
Lemma lem239164 (P : nat -> Prop) (n : nat) : ((term254 P n) = (term255 P n)) = ((term250 P n) = (term271 P n)).
Proof. exact (MK_COMB (@lem239155 P n) (@lem239163 P n)). Qed.
Lemma lem239165 (P : nat -> Prop) (n : nat) : (term250 P n) = (term271 P n).
Proof. exact (EQ_MP (@lem239164 P n) (@lem239142 P n)). Qed.
Lemma lem239166 (P : nat -> Prop) : (term252 P) = (term272 P).
Proof. exact (fun_ext (fun n : nat => @lem239165 P n)). Qed.
Lemma lem239167 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem239168 (P : nat -> Prop) : (term253 P) = (term273 P).
Proof. exact (MK_COMB (@lem239167) (@lem239166 P)). Qed.
Lemma lem239169 (P : nat -> Prop) : (term232 P) = (term273 P).
Proof. exact (TRANS (@lem239138 P) (@lem239168 P)). Qed.
Lemma lem239170 : term234 = term274.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem239169 P)). Qed.
Lemma lem239171 : (@ex (nat -> Prop)) = (@ex (nat -> Prop)).
Proof. exact (eq_refl (@ex (nat -> Prop))). Qed.
Lemma lem239172 : term235 = term275.
Proof. exact (MK_COMB (@lem239171) (@lem239170)). Qed.
Lemma lem239173 : term217 = term275.
Proof. exact (TRANS (@lem239111) (@lem239172)). Qed.
Lemma lem239174 : term159 = term275.
Proof. exact (TRANS (@lem239084) (@lem239173)). Qed.
Lemma lem239175 : term111 = term275.
Proof. exact (TRANS (@lem239002) (@lem239174)). Qed.
Lemma lem239176 : term3 = term275.
Proof. exact (TRANS (@lem238564) (@lem239175)). Qed.
Lemma lem239177 (h1 : term3) : term275.
Proof. exact (EQ_MP (@lem239176) (@lem238478 h1)). Qed.
Lemma lem239183 (n : nat) : (term276 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem239186 (m : nat) (n : nat) : (term277 m n) = (term277 m n).
Proof. exact (eq_refl (term277 m n)). Qed.
Lemma lem239188 (m : nat) (n : nat) : (term278 m n) = (term278 m n).
Proof. exact (eq_refl (term278 m n)). Qed.
Lemma lem239189 (m : nat) (n : nat) : (term279 m n) = (term280 m n).
Proof. exact (MK_COMB (@lem239188 m n) (@lem239183 n)). Qed.
Lemma lem239190 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem239191 (m : nat) (n : nat) : (term281 m n) = (term282 m n).
Proof. exact (MK_COMB (@lem239190) (@lem239189 m n)). Qed.
Lemma lem239192 (m : nat) (n : nat) : (term283 m n) = (term284 m n).
Proof. exact (MK_COMB (@lem239191 m n) (@lem239186 m n)). Qed.
Lemma lem239193 (m : nat) (n : nat) : ((term40 m n) = (term41 n)) = (term283 m n).
Proof. exact (@lem17784 (term40 m n) (term41 n)). Qed.
Lemma lem239194 (m : nat) (n : nat) : ((term40 m n) = (term41 n)) = (term284 m n).
Proof. exact (TRANS (@lem239193 m n) (@lem239192 m n)). Qed.
Lemma lem239195 (m : nat) : (term42 m) = (term285 m).
Proof. exact (fun_ext (fun n : nat => @lem239194 m n)). Qed.
Lemma lem239196 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239197 (m : nat) : (term43 m) = (term286 m).
Proof. exact (MK_COMB (@lem239196) (@lem239195 m)). Qed.
Lemma lem239198 : term44 = term287.
Proof. exact (fun_ext (fun m : nat => @lem239197 m)). Qed.
Lemma lem239199 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239200 : term45 = term288.
Proof. exact (MK_COMB (@lem239199) (@lem239198)). Qed.
Lemma lem239206 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term289 A P Q) = (term290 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem239207 (P : nat -> Prop) (Q : nat -> Prop) : (term291 P Q) = (term292 P Q).
Proof. exact (@lem239206 nat P Q). Qed.
Lemma lem239208 (m : nat) : (term293 m) = (term294 m).
Proof. exact (@lem239207 (term295 m) (term296 m)). Qed.
Lemma lem239209 (m : nat) (n : nat) : (term297 m n) = (term280 m n).
Proof. exact (eq_refl (term297 m n)). Qed.
Lemma lem239210 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem239211 (m : nat) (n : nat) : (term298 m n) = (term282 m n).
Proof. exact (MK_COMB (@lem239210) (@lem239209 m n)). Qed.
Lemma lem239212 (m : nat) (n : nat) : (term299 m n) = (term277 m n).
Proof. exact (eq_refl (term299 m n)). Qed.
Lemma lem239213 (m : nat) (n : nat) : (term300 m n) = (term284 m n).
Proof. exact (MK_COMB (@lem239211 m n) (@lem239212 m n)). Qed.
Lemma lem239214 (m : nat) : (term301 m) = (term285 m).
Proof. exact (fun_ext (fun n : nat => @lem239213 m n)). Qed.
Lemma lem239215 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239216 (m : nat) : (term293 m) = (term286 m).
Proof. exact (MK_COMB (@lem239215) (@lem239214 m)). Qed.
Lemma lem239217 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem239218 (m : nat) : (term302 m) = (term303 m).
Proof. exact (MK_COMB (@lem239217) (@lem239216 m)). Qed.
Lemma lem239219 (m : nat) (n : nat) : (term297 m n) = (term280 m n).
Proof. exact (eq_refl (term297 m n)). Qed.
Lemma lem239220 (m : nat) : (term304 m) = (term295 m).
Proof. exact (fun_ext (fun n : nat => @lem239219 m n)). Qed.
Lemma lem239221 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239222 (m : nat) : (term305 m) = (term306 m).
Proof. exact (MK_COMB (@lem239221) (@lem239220 m)). Qed.
Lemma lem239223 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem239224 (m : nat) : (term307 m) = (term308 m).
Proof. exact (MK_COMB (@lem239223) (@lem239222 m)). Qed.
Lemma lem239225 (m : nat) (n : nat) : (term299 m n) = (term277 m n).
Proof. exact (eq_refl (term299 m n)). Qed.
Lemma lem239226 (m : nat) : (term309 m) = (term296 m).
Proof. exact (fun_ext (fun n : nat => @lem239225 m n)). Qed.
Lemma lem239227 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239228 (m : nat) : (term310 m) = (term311 m).
Proof. exact (MK_COMB (@lem239227) (@lem239226 m)). Qed.
Lemma lem239229 (m : nat) : (term294 m) = (term312 m).
Proof. exact (MK_COMB (@lem239224 m) (@lem239228 m)). Qed.
Lemma lem239230 (m : nat) : ((term293 m) = (term294 m)) = ((term286 m) = (term312 m)).
Proof. exact (MK_COMB (@lem239218 m) (@lem239229 m)). Qed.
Lemma lem239231 (m : nat) : (term286 m) = (term312 m).
Proof. exact (EQ_MP (@lem239230 m) (@lem239208 m)). Qed.
Lemma lem239328 : term287 = term313.
Proof. exact (fun_ext (fun m : nat => @lem239231 m)). Qed.
Lemma lem239329 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239330 : term288 = term314.
Proof. exact (MK_COMB (@lem239329) (@lem239328)). Qed.
Lemma lem239332 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term289 A P Q) = (term290 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem239333 (P : nat -> Prop) (Q : nat -> Prop) : (term291 P Q) = (term292 P Q).
Proof. exact (@lem239332 nat P Q). Qed.
Lemma lem239334 : term315 = term316.
Proof. exact (@lem239333 term317 term318). Qed.
Lemma lem239335 (m : nat) : (term319 m) = (term306 m).
Proof. exact (eq_refl (term319 m)). Qed.
Lemma lem239336 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem239337 (m : nat) : (term320 m) = (term308 m).
Proof. exact (MK_COMB (@lem239336) (@lem239335 m)). Qed.
Lemma lem239338 (m : nat) : (term321 m) = (term311 m).
Proof. exact (eq_refl (term321 m)). Qed.
Lemma lem239339 (m : nat) : (term322 m) = (term312 m).
Proof. exact (MK_COMB (@lem239337 m) (@lem239338 m)). Qed.
Lemma lem239340 : term323 = term313.
Proof. exact (fun_ext (fun m : nat => @lem239339 m)). Qed.
Lemma lem239341 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239342 : term315 = term314.
Proof. exact (MK_COMB (@lem239341) (@lem239340)). Qed.
Lemma lem239343 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem239344 : term324 = term325.
Proof. exact (MK_COMB (@lem239343) (@lem239342)). Qed.
Lemma lem239345 (m : nat) : (term319 m) = (term306 m).
Proof. exact (eq_refl (term319 m)). Qed.
Lemma lem239346 : term326 = term317.
Proof. exact (fun_ext (fun m : nat => @lem239345 m)). Qed.
Lemma lem239347 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239348 : term327 = term328.
Proof. exact (MK_COMB (@lem239347) (@lem239346)). Qed.
Lemma lem239349 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem239350 : term329 = term330.
Proof. exact (MK_COMB (@lem239349) (@lem239348)). Qed.
Lemma lem239351 (m : nat) : (term321 m) = (term311 m).
Proof. exact (eq_refl (term321 m)). Qed.
Lemma lem239352 : term331 = term318.
Proof. exact (fun_ext (fun m : nat => @lem239351 m)). Qed.
Lemma lem239353 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239354 : term332 = term333.
Proof. exact (MK_COMB (@lem239353) (@lem239352)). Qed.
Lemma lem239355 : term316 = term334.
Proof. exact (MK_COMB (@lem239350) (@lem239354)). Qed.
Lemma lem239356 : (term315 = term316) = (term314 = term334).
Proof. exact (MK_COMB (@lem239344) (@lem239355)). Qed.
Lemma lem239357 : term314 = term334.
Proof. exact (EQ_MP (@lem239356) (@lem239334)). Qed.
Lemma lem239464 : term288 = term334.
Proof. exact (TRANS (@lem239330) (@lem239357)). Qed.
Lemma lem239465 : term45 = term334.
Proof. exact (TRANS (@lem239200) (@lem239464)). Qed.
Lemma lem239466 (h1 : term45) : term334.
Proof. exact (EQ_MP (@lem239465) (@lem238479 h1)). Qed.
Lemma lem239477 (m : nat) (n : nat) : (term335 m n) = (term336 m n).
Proof. exact (@lem17160 (n = (NUMERAL 0)) (Peano.lt m n)). Qed.
Lemma lem239483 (m : nat) (n : nat) : (term337 m n) = (term337 m n).
Proof. exact (eq_refl (term337 m n)). Qed.
Lemma lem239485 (n : nat) (m : nat) : (term338 n m) = (term338 n m).
Proof. exact (eq_refl (term338 n m)). Qed.
Lemma lem239486 (m : nat) (n : nat) : (term339 m n) = (term340 m n).
Proof. exact (MK_COMB (@lem239485 n m) (@lem239477 m n)). Qed.
Lemma lem239487 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem239488 (m : nat) (n : nat) : (term341 m n) = (term342 m n).
Proof. exact (MK_COMB (@lem239487) (@lem239486 m n)). Qed.
Lemma lem239489 (m : nat) (n : nat) : (term343 m n) = (term344 m n).
Proof. exact (MK_COMB (@lem239488 m n) (@lem239483 m n)). Qed.
Lemma lem239490 (m : nat) (n : nat) : (((Nat.modulo m n) = m) = (term35 m n)) = (term343 m n).
Proof. exact (@lem17784 ((Nat.modulo m n) = m) (term35 m n)). Qed.
Lemma lem239491 (m : nat) (n : nat) : (((Nat.modulo m n) = m) = (term35 m n)) = (term344 m n).
Proof. exact (TRANS (@lem239490 m n) (@lem239489 m n)). Qed.
Lemma lem239492 (m : nat) : (term36 m) = (term345 m).
Proof. exact (fun_ext (fun n : nat => @lem239491 m n)). Qed.
Lemma lem239493 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239494 (m : nat) : (term37 m) = (term346 m).
Proof. exact (MK_COMB (@lem239493) (@lem239492 m)). Qed.
Lemma lem239495 : term38 = term347.
Proof. exact (fun_ext (fun m : nat => @lem239494 m)). Qed.
Lemma lem239496 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239497 : term39 = term348.
Proof. exact (MK_COMB (@lem239496) (@lem239495)). Qed.
Lemma lem239503 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term289 A P Q) = (term290 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem239504 (P : nat -> Prop) (Q : nat -> Prop) : (term291 P Q) = (term292 P Q).
Proof. exact (@lem239503 nat P Q). Qed.
Lemma lem239505 (m : nat) : (term349 m) = (term350 m).
Proof. exact (@lem239504 (term351 m) (term352 m)). Qed.
Lemma lem239506 (m : nat) (n : nat) : (term353 m n) = (term340 m n).
Proof. exact (eq_refl (term353 m n)). Qed.
Lemma lem239507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem239508 (m : nat) (n : nat) : (term354 m n) = (term342 m n).
Proof. exact (MK_COMB (@lem239507) (@lem239506 m n)). Qed.
Lemma lem239509 (m : nat) (n : nat) : (term355 m n) = (term337 m n).
Proof. exact (eq_refl (term355 m n)). Qed.
Lemma lem239510 (m : nat) (n : nat) : (term356 m n) = (term344 m n).
Proof. exact (MK_COMB (@lem239508 m n) (@lem239509 m n)). Qed.
Lemma lem239511 (m : nat) : (term357 m) = (term345 m).
Proof. exact (fun_ext (fun n : nat => @lem239510 m n)). Qed.
Lemma lem239512 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239513 (m : nat) : (term349 m) = (term346 m).
Proof. exact (MK_COMB (@lem239512) (@lem239511 m)). Qed.
Lemma lem239514 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem239515 (m : nat) : (term358 m) = (term359 m).
Proof. exact (MK_COMB (@lem239514) (@lem239513 m)). Qed.
Lemma lem239516 (m : nat) (n : nat) : (term353 m n) = (term340 m n).
Proof. exact (eq_refl (term353 m n)). Qed.
Lemma lem239517 (m : nat) : (term360 m) = (term351 m).
Proof. exact (fun_ext (fun n : nat => @lem239516 m n)). Qed.
Lemma lem239518 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239519 (m : nat) : (term361 m) = (term362 m).
Proof. exact (MK_COMB (@lem239518) (@lem239517 m)). Qed.
Lemma lem239520 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem239521 (m : nat) : (term363 m) = (term364 m).
Proof. exact (MK_COMB (@lem239520) (@lem239519 m)). Qed.
Lemma lem239522 (m : nat) (n : nat) : (term355 m n) = (term337 m n).
Proof. exact (eq_refl (term355 m n)). Qed.
Lemma lem239523 (m : nat) : (term365 m) = (term352 m).
Proof. exact (fun_ext (fun n : nat => @lem239522 m n)). Qed.
Lemma lem239524 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239525 (m : nat) : (term366 m) = (term367 m).
Proof. exact (MK_COMB (@lem239524) (@lem239523 m)). Qed.
Lemma lem239526 (m : nat) : (term350 m) = (term368 m).
Proof. exact (MK_COMB (@lem239521 m) (@lem239525 m)). Qed.
Lemma lem239527 (m : nat) : ((term349 m) = (term350 m)) = ((term346 m) = (term368 m)).
Proof. exact (MK_COMB (@lem239515 m) (@lem239526 m)). Qed.
Lemma lem239528 (m : nat) : (term346 m) = (term368 m).
Proof. exact (EQ_MP (@lem239527 m) (@lem239505 m)). Qed.
Lemma lem239625 : term347 = term369.
Proof. exact (fun_ext (fun m : nat => @lem239528 m)). Qed.
Lemma lem239626 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239627 : term348 = term370.
Proof. exact (MK_COMB (@lem239626) (@lem239625)). Qed.
Lemma lem239629 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term289 A P Q) = (term290 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem239630 (P : nat -> Prop) (Q : nat -> Prop) : (term291 P Q) = (term292 P Q).
Proof. exact (@lem239629 nat P Q). Qed.
Lemma lem239631 : term371 = term372.
Proof. exact (@lem239630 term373 term374). Qed.
Lemma lem239632 (m : nat) : (term375 m) = (term362 m).
Proof. exact (eq_refl (term375 m)). Qed.
Lemma lem239633 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem239634 (m : nat) : (term376 m) = (term364 m).
Proof. exact (MK_COMB (@lem239633) (@lem239632 m)). Qed.
Lemma lem239635 (m : nat) : (term377 m) = (term367 m).
Proof. exact (eq_refl (term377 m)). Qed.
Lemma lem239636 (m : nat) : (term378 m) = (term368 m).
Proof. exact (MK_COMB (@lem239634 m) (@lem239635 m)). Qed.
Lemma lem239637 : term379 = term369.
Proof. exact (fun_ext (fun m : nat => @lem239636 m)). Qed.
Lemma lem239638 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239639 : term371 = term370.
Proof. exact (MK_COMB (@lem239638) (@lem239637)). Qed.
Lemma lem239640 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem239641 : term380 = term381.
Proof. exact (MK_COMB (@lem239640) (@lem239639)). Qed.
Lemma lem239642 (m : nat) : (term375 m) = (term362 m).
Proof. exact (eq_refl (term375 m)). Qed.
Lemma lem239643 : term382 = term373.
Proof. exact (fun_ext (fun m : nat => @lem239642 m)). Qed.
Lemma lem239644 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239645 : term383 = term384.
Proof. exact (MK_COMB (@lem239644) (@lem239643)). Qed.
Lemma lem239646 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem239647 : term385 = term386.
Proof. exact (MK_COMB (@lem239646) (@lem239645)). Qed.
Lemma lem239648 (m : nat) : (term377 m) = (term367 m).
Proof. exact (eq_refl (term377 m)). Qed.
Lemma lem239649 : term387 = term374.
Proof. exact (fun_ext (fun m : nat => @lem239648 m)). Qed.
Lemma lem239650 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239651 : term388 = term389.
Proof. exact (MK_COMB (@lem239650) (@lem239649)). Qed.
Lemma lem239652 : term372 = term390.
Proof. exact (MK_COMB (@lem239647) (@lem239651)). Qed.
Lemma lem239653 : (term371 = term372) = (term370 = term390).
Proof. exact (MK_COMB (@lem239641) (@lem239652)). Qed.
Lemma lem239654 : term370 = term390.
Proof. exact (EQ_MP (@lem239653) (@lem239631)). Qed.
Lemma lem239761 : term348 = term390.
Proof. exact (TRANS (@lem239627) (@lem239654)). Qed.
Lemma lem239762 : term39 = term390.
Proof. exact (TRANS (@lem239497) (@lem239761)). Qed.
Lemma lem239763 (h1 : term39) : term390.
Proof. exact (EQ_MP (@lem239762) (@lem238480 h1)). Qed.
Lemma lem239764 (m : nat) : (term12 m) = (term12 m).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem239765 : term14 = term14.
Proof. exact (fun_ext (fun m : nat => @lem239764 m)). Qed.
Lemma lem239766 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239767 : term16 = term16.
Proof. exact (MK_COMB (@lem239766) (@lem239765)). Qed.
Lemma lem239778 (m : nat) (n : nat) : (term391 m n) = (term392 m n).
Proof. exact (@lem17160 (m = n) (Peano.lt m n)). Qed.
Lemma lem239784 (m : nat) (n : nat) : (term393 m n) = (term393 m n).
Proof. exact (eq_refl (term393 m n)). Qed.
Lemma lem239786 (m : nat) (n : nat) : (term394 m n) = (term394 m n).
Proof. exact (eq_refl (term394 m n)). Qed.
Lemma lem239787 (m : nat) (n : nat) : (term395 m n) = (term396 m n).
Proof. exact (MK_COMB (@lem239786 m n) (@lem239778 m n)). Qed.
Lemma lem239788 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem239789 (m : nat) (n : nat) : (term397 m n) = (term398 m n).
Proof. exact (MK_COMB (@lem239788) (@lem239787 m n)). Qed.
Lemma lem239790 (m : nat) (n : nat) : (term399 m n) = (term400 m n).
Proof. exact (MK_COMB (@lem239789 m n) (@lem239784 m n)). Qed.
Lemma lem239791 (m : nat) (n : nat) : ((term30 m n) = (term31 m n)) = (term399 m n).
Proof. exact (@lem17784 (term30 m n) (term31 m n)). Qed.
Lemma lem239792 (m : nat) (n : nat) : ((term30 m n) = (term31 m n)) = (term400 m n).
Proof. exact (TRANS (@lem239791 m n) (@lem239790 m n)). Qed.
Lemma lem239793 (m : nat) : (term32 m) = (term401 m).
Proof. exact (fun_ext (fun n : nat => @lem239792 m n)). Qed.
Lemma lem239794 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239795 (m : nat) : (term33 m) = (term402 m).
Proof. exact (MK_COMB (@lem239794) (@lem239793 m)). Qed.
Lemma lem239796 : term34 = term403.
Proof. exact (fun_ext (fun m : nat => @lem239795 m)). Qed.
Lemma lem239797 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239798 : term19 = term404.
Proof. exact (MK_COMB (@lem239797) (@lem239796)). Qed.
Lemma lem239799 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem239800 : term18 = term18.
Proof. exact (MK_COMB (@lem239799) (@lem239767)). Qed.
Lemma lem239801 : term20 = term405.
Proof. exact (MK_COMB (@lem239800) (@lem239798)). Qed.
Lemma lem239811 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term289 A P Q) = (term290 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem239812 (P : nat -> Prop) (Q : nat -> Prop) : (term291 P Q) = (term292 P Q).
Proof. exact (@lem239811 nat P Q). Qed.
Lemma lem239813 (m : nat) : (term406 m) = (term407 m).
Proof. exact (@lem239812 (term408 m) (term409 m)). Qed.
Lemma lem239814 (m : nat) (n : nat) : (term410 m n) = (term396 m n).
Proof. exact (eq_refl (term410 m n)). Qed.
Lemma lem239815 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem239816 (m : nat) (n : nat) : (term411 m n) = (term398 m n).
Proof. exact (MK_COMB (@lem239815) (@lem239814 m n)). Qed.
Lemma lem239817 (m : nat) (n : nat) : (term412 m n) = (term393 m n).
Proof. exact (eq_refl (term412 m n)). Qed.
Lemma lem239818 (m : nat) (n : nat) : (term413 m n) = (term400 m n).
Proof. exact (MK_COMB (@lem239816 m n) (@lem239817 m n)). Qed.
Lemma lem239819 (m : nat) : (term414 m) = (term401 m).
Proof. exact (fun_ext (fun n : nat => @lem239818 m n)). Qed.
Lemma lem239820 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239821 (m : nat) : (term406 m) = (term402 m).
Proof. exact (MK_COMB (@lem239820) (@lem239819 m)). Qed.
Lemma lem239822 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem239823 (m : nat) : (term415 m) = (term416 m).
Proof. exact (MK_COMB (@lem239822) (@lem239821 m)). Qed.
Lemma lem239824 (m : nat) (n : nat) : (term410 m n) = (term396 m n).
Proof. exact (eq_refl (term410 m n)). Qed.
Lemma lem239825 (m : nat) : (term417 m) = (term408 m).
Proof. exact (fun_ext (fun n : nat => @lem239824 m n)). Qed.
Lemma lem239826 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239827 (m : nat) : (term418 m) = (term419 m).
Proof. exact (MK_COMB (@lem239826) (@lem239825 m)). Qed.
Lemma lem239828 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem239829 (m : nat) : (term420 m) = (term421 m).
Proof. exact (MK_COMB (@lem239828) (@lem239827 m)). Qed.
Lemma lem239830 (m : nat) (n : nat) : (term412 m n) = (term393 m n).
Proof. exact (eq_refl (term412 m n)). Qed.
Lemma lem239831 (m : nat) : (term422 m) = (term409 m).
Proof. exact (fun_ext (fun n : nat => @lem239830 m n)). Qed.
Lemma lem239832 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239833 (m : nat) : (term423 m) = (term424 m).
Proof. exact (MK_COMB (@lem239832) (@lem239831 m)). Qed.
Lemma lem239834 (m : nat) : (term407 m) = (term425 m).
Proof. exact (MK_COMB (@lem239829 m) (@lem239833 m)). Qed.
Lemma lem239835 (m : nat) : ((term406 m) = (term407 m)) = ((term402 m) = (term425 m)).
Proof. exact (MK_COMB (@lem239823 m) (@lem239834 m)). Qed.
Lemma lem239836 (m : nat) : (term402 m) = (term425 m).
Proof. exact (EQ_MP (@lem239835 m) (@lem239813 m)). Qed.
Lemma lem239933 : term403 = term426.
Proof. exact (fun_ext (fun m : nat => @lem239836 m)). Qed.
Lemma lem239934 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239935 : term404 = term427.
Proof. exact (MK_COMB (@lem239934) (@lem239933)). Qed.
Lemma lem239937 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term289 A P Q) = (term290 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem239938 (P : nat -> Prop) (Q : nat -> Prop) : (term291 P Q) = (term292 P Q).
Proof. exact (@lem239937 nat P Q). Qed.
Lemma lem239939 : term428 = term429.
Proof. exact (@lem239938 term430 term431). Qed.
Lemma lem239940 (m : nat) : (term432 m) = (term419 m).
Proof. exact (eq_refl (term432 m)). Qed.
Lemma lem239941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem239942 (m : nat) : (term433 m) = (term421 m).
Proof. exact (MK_COMB (@lem239941) (@lem239940 m)). Qed.
Lemma lem239943 (m : nat) : (term434 m) = (term424 m).
Proof. exact (eq_refl (term434 m)). Qed.
Lemma lem239944 (m : nat) : (term435 m) = (term425 m).
Proof. exact (MK_COMB (@lem239942 m) (@lem239943 m)). Qed.
Lemma lem239945 : term436 = term426.
Proof. exact (fun_ext (fun m : nat => @lem239944 m)). Qed.
Lemma lem239946 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239947 : term428 = term427.
Proof. exact (MK_COMB (@lem239946) (@lem239945)). Qed.
Lemma lem239948 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem239949 : term437 = term438.
Proof. exact (MK_COMB (@lem239948) (@lem239947)). Qed.
Lemma lem239950 (m : nat) : (term432 m) = (term419 m).
Proof. exact (eq_refl (term432 m)). Qed.
Lemma lem239951 : term439 = term430.
Proof. exact (fun_ext (fun m : nat => @lem239950 m)). Qed.
Lemma lem239952 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239953 : term440 = term441.
Proof. exact (MK_COMB (@lem239952) (@lem239951)). Qed.
Lemma lem239954 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem239955 : term442 = term443.
Proof. exact (MK_COMB (@lem239954) (@lem239953)). Qed.
Lemma lem239956 (m : nat) : (term434 m) = (term424 m).
Proof. exact (eq_refl (term434 m)). Qed.
Lemma lem239957 : term444 = term431.
Proof. exact (fun_ext (fun m : nat => @lem239956 m)). Qed.
Lemma lem239958 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem239959 : term445 = term446.
Proof. exact (MK_COMB (@lem239958) (@lem239957)). Qed.
Lemma lem239960 : term429 = term447.
Proof. exact (MK_COMB (@lem239955) (@lem239959)). Qed.
Lemma lem239961 : (term428 = term429) = (term427 = term447).
Proof. exact (MK_COMB (@lem239949) (@lem239960)). Qed.
Lemma lem239962 : term427 = term447.
Proof. exact (EQ_MP (@lem239961) (@lem239939)). Qed.
Lemma lem240067 : term404 = term447.
Proof. exact (TRANS (@lem239935) (@lem239962)). Qed.
Lemma lem240068 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem240071 : term405 = term448.
Proof. exact (MK_COMB (@lem240068) (@lem240067)). Qed.
Lemma lem240072 : term20 = term448.
Proof. exact (TRANS (@lem239801) (@lem240071)). Qed.
Lemma lem240073 (h1 : term20) : term448.
Proof. exact (EQ_MP (@lem240072) (@lem238481 h1)). Qed.
Lemma lem240074 (P : nat -> Prop) (h1 : term273 P) : term273 P.
Proof. exact (h1). Qed.
Lemma lem240075 (P : nat -> Prop) (n : nat) (h1 : term271 P n) : term271 P n.
Proof. exact (h1). Qed.
Lemma lem240076 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term268 a P n) : term268 a P n.
Proof. exact (h1). Qed.
Lemma lem240099 (m : nat) (n : nat) : (term277 m n) = (term277 m n).
Proof. exact (eq_refl (term277 m n)). Qed.
Lemma lem240100 (m : nat) : (term296 m) = (term296 m).
Proof. exact (fun_ext (fun n : nat => @lem240099 m n)). Qed.
Lemma lem240101 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem240102 (m : nat) : (term311 m) = (term311 m).
Proof. exact (MK_COMB (@lem240101) (@lem240100 m)). Qed.
Lemma lem240103 : term318 = term318.
Proof. exact (fun_ext (fun m : nat => @lem240102 m)). Qed.
Lemma lem240104 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem240105 : term333 = term333.
Proof. exact (MK_COMB (@lem240104) (@lem240103)). Qed.
Lemma lem240124 (m : nat) (n : nat) : (term280 m n) = (term280 m n).
Proof. exact (eq_refl (term280 m n)). Qed.
Lemma lem240125 (m : nat) : (term295 m) = (term295 m).
Proof. exact (fun_ext (fun n : nat => @lem240124 m n)). Qed.
Lemma lem240126 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem240127 (m : nat) : (term306 m) = (term306 m).
Proof. exact (MK_COMB (@lem240126) (@lem240125 m)). Qed.
Lemma lem240128 : term317 = term317.
Proof. exact (fun_ext (fun m : nat => @lem240127 m)). Qed.
Lemma lem240129 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem240130 : term328 = term328.
Proof. exact (MK_COMB (@lem240129) (@lem240128)). Qed.
Lemma lem240131 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem240132 : term330 = term330.
Proof. exact (MK_COMB (@lem240131) (@lem240130)). Qed.
Lemma lem240133 : term334 = term334.
Proof. exact (MK_COMB (@lem240132) (@lem240105)). Qed.
Lemma lem240134 (h1 : term45) : term334.
Proof. exact (EQ_MP (@lem240133) (@lem239466 h1)). Qed.
Lemma lem240163 (m : nat) (n : nat) : (term337 m n) = (term337 m n).
Proof. exact (eq_refl (term337 m n)). Qed.
Lemma lem240164 (m : nat) : (term352 m) = (term352 m).
Proof. exact (fun_ext (fun n : nat => @lem240163 m n)). Qed.
Lemma lem240165 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem240166 (m : nat) : (term367 m) = (term367 m).
Proof. exact (MK_COMB (@lem240165) (@lem240164 m)). Qed.
Lemma lem240167 : term374 = term374.
Proof. exact (fun_ext (fun m : nat => @lem240166 m)). Qed.
Lemma lem240168 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem240169 : term389 = term389.
Proof. exact (MK_COMB (@lem240168) (@lem240167)). Qed.
Lemma lem240200 (m : nat) (n : nat) : (term340 m n) = (term340 m n).
Proof. exact (eq_refl (term340 m n)). Qed.
Lemma lem240201 (m : nat) : (term351 m) = (term351 m).
Proof. exact (fun_ext (fun n : nat => @lem240200 m n)). Qed.
Lemma lem240202 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem240203 (m : nat) : (term362 m) = (term362 m).
Proof. exact (MK_COMB (@lem240202) (@lem240201 m)). Qed.
Lemma lem240204 : term373 = term373.
Proof. exact (fun_ext (fun m : nat => @lem240203 m)). Qed.
Lemma lem240205 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem240206 : term384 = term384.
Proof. exact (MK_COMB (@lem240205) (@lem240204)). Qed.
Lemma lem240207 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem240208 : term386 = term386.
Proof. exact (MK_COMB (@lem240207) (@lem240206)). Qed.
Lemma lem240209 : term390 = term390.
Proof. exact (MK_COMB (@lem240208) (@lem240169)). Qed.
Lemma lem240210 (h1 : term39) : term390.
Proof. exact (EQ_MP (@lem240209) (@lem239763 h1)). Qed.
Lemma lem240235 (m : nat) (n : nat) : (term393 m n) = (term393 m n).
Proof. exact (eq_refl (term393 m n)). Qed.
Lemma lem240236 (m : nat) : (term409 m) = (term409 m).
Proof. exact (fun_ext (fun n : nat => @lem240235 m n)). Qed.
Lemma lem240237 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem240238 (m : nat) : (term424 m) = (term424 m).
Proof. exact (MK_COMB (@lem240237) (@lem240236 m)). Qed.
Lemma lem240239 : term431 = term431.
Proof. exact (fun_ext (fun m : nat => @lem240238 m)). Qed.
Lemma lem240240 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem240241 : term446 = term446.
Proof. exact (MK_COMB (@lem240240) (@lem240239)). Qed.
Lemma lem240268 (m : nat) (n : nat) : (term396 m n) = (term396 m n).
Proof. exact (eq_refl (term396 m n)). Qed.
Lemma lem240269 (m : nat) : (term408 m) = (term408 m).
Proof. exact (fun_ext (fun n : nat => @lem240268 m n)). Qed.
Lemma lem240270 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem240271 (m : nat) : (term419 m) = (term419 m).
Proof. exact (MK_COMB (@lem240270) (@lem240269 m)). Qed.
Lemma lem240272 : term430 = term430.
Proof. exact (fun_ext (fun m : nat => @lem240271 m)). Qed.
Lemma lem240273 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem240274 : term441 = term441.
Proof. exact (MK_COMB (@lem240273) (@lem240272)). Qed.
Lemma lem240275 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem240276 : term443 = term443.
Proof. exact (MK_COMB (@lem240275) (@lem240274)). Qed.
Lemma lem240277 : term447 = term447.
Proof. exact (MK_COMB (@lem240276) (@lem240241)). Qed.
Lemma lem240286 (m : nat) : (term12 m) = (term12 m).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem240287 : term14 = term14.
Proof. exact (fun_ext (fun m : nat => @lem240286 m)). Qed.
Lemma lem240288 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem240289 : term16 = term16.
Proof. exact (MK_COMB (@lem240288) (@lem240287)). Qed.
Lemma lem240290 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem240291 : term18 = term18.
Proof. exact (MK_COMB (@lem240290) (@lem240289)). Qed.
Lemma lem240292 : term448 = term448.
Proof. exact (MK_COMB (@lem240291) (@lem240277)). Qed.
Lemma lem240293 (h1 : term20) : term448.
Proof. exact (EQ_MP (@lem240292) (@lem240073 h1)). Qed.
Lemma lem240300 (P : nat -> Prop) (a : nat) (n : nat) : (term46 P a n) = (term46 P a n).
Proof. exact (eq_refl (term46 P a n)). Qed.
Lemma lem240301 (P : nat -> Prop) (n : nat) : (term47 P n) = (term47 P n).
Proof. exact (fun_ext (fun a : nat => @lem240300 P a n)). Qed.
Lemma lem240302 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem240303 (P : nat -> Prop) (n : nat) : (term48 P n) = (term48 P n).
Proof. exact (MK_COMB (@lem240302) (@lem240301 P n)). Qed.
Lemma lem240312 (n : nat) : (term49 n) = (term49 n).
Proof. exact (eq_refl (term49 n)). Qed.
Lemma lem240313 (P : nat -> Prop) (n : nat) : (term50 P n) = (term50 P n).
Proof. exact (MK_COMB (@lem240312 n) (@lem240303 P n)). Qed.
Lemma lem240328 (n : nat) (P : nat -> Prop) (a : nat) : (term207 n P a) = (term207 n P a).
Proof. exact (eq_refl (term207 n P a)). Qed.
Lemma lem240329 (a : nat) (P : nat -> Prop) (n : nat) : (term209 a P n) = (term209 a P n).
Proof. exact (MK_COMB (@lem240328 n P a) (@lem240313 P n)). Qed.
Lemma lem240350 (P : nat -> Prop) (a : nat) (n : nat) : (term172 P a n) = (term172 P a n).
Proof. exact (eq_refl (term172 P a n)). Qed.
Lemma lem240363 (n : nat) (P : nat -> Prop) (a : nat) : (term60 n P a) = (term60 n P a).
Proof. exact (eq_refl (term60 n P a)). Qed.
Lemma lem240364 (n : nat) (P : nat -> Prop) : (term70 n P) = (term70 n P).
Proof. exact (fun_ext (fun a : nat => @lem240363 n P a)). Qed.
Lemma lem240365 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem240366 (n : nat) (P : nat -> Prop) : (term71 n P) = (term71 n P).
Proof. exact (MK_COMB (@lem240365) (@lem240364 n P)). Qed.
Lemma lem240367 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem240368 (n : nat) (P : nat -> Prop) : (term89 n P) = (term89 n P).
Proof. exact (MK_COMB (@lem240367) (@lem240366 n P)). Qed.
Lemma lem240369 (P : nat -> Prop) (a : nat) (n : nat) : (term185 P a n) = (term185 P a n).
Proof. exact (MK_COMB (@lem240368 n P) (@lem240350 P a n)). Qed.
Lemma lem240370 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem240371 (P : nat -> Prop) (a : nat) (n : nat) : (term266 P a n) = (term266 P a n).
Proof. exact (MK_COMB (@lem240370) (@lem240369 P a n)). Qed.
Lemma lem240372 (a : nat) (P : nat -> Prop) (n : nat) : (term268 a P n) = (term268 a P n).
Proof. exact (MK_COMB (@lem240371 P a n) (@lem240329 a P n)). Qed.
Lemma lem240373 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term268 a P n) : term268 a P n.
Proof. exact (EQ_MP (@lem240372 a P n) (@lem240076 a P n h1)). Qed.
Lemma lem240375 (h1 : term20) : term16.
Proof. exact (proj1 (@lem240293 h1)). Qed.
Lemma lem240379 (h1 : term39) : term384.
Proof. exact (proj1 (@lem240210 h1)). Qed.
Lemma lem240381 (h1 : term45) : term328.
Proof. exact (proj1 (@lem240134 h1)). Qed.
Lemma lem240382 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term185 P a n) : term185 P a n.
Proof. exact (h1). Qed.
Lemma lem240383 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term209 a P n) : term209 a P n.
Proof. exact (h1). Qed.
Lemma lem240384 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term185 P a n) : term172 P a n.
Proof. exact (proj2 (@lem240382 P a n h1)). Qed.
Lemma lem240385 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term185 P a n) : term71 n P.
Proof. exact (proj1 (@lem240382 P a n h1)). Qed.
Lemma lem240388 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term209 a P n) : term50 P n.
Proof. exact (proj2 (@lem240383 a P n h1)). Qed.
Lemma lem240389 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term209 a P n) : term59 n P a.
Proof. exact (proj1 (@lem240383 a P n h1)). Qed.
Lemma lem240393 (P : nat -> Prop) (n : nat) (h1 : term48 P n) : term48 P n.
Proof. exact (h1). Qed.
Lemma lem240504 (m : nat) (n : nat) : (term280 m n) = (term280 m n).
Proof. exact (eq_refl (term280 m n)). Qed.
Lemma lem240505 (m : nat) : (term295 m) = (term295 m).
Proof. exact (fun_ext (fun n : nat => @lem240504 m n)). Qed.
Lemma lem240506 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem240507 (m : nat) : (term306 m) = (term306 m).
Proof. exact (MK_COMB (@lem240506) (@lem240505 m)). Qed.
Lemma lem240508 : term317 = term317.
Proof. exact (fun_ext (fun m : nat => @lem240507 m)). Qed.
Lemma lem240509 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem240511 : term328 = term328.
Proof. exact (MK_COMB (@lem240509) (@lem240508)). Qed.
Lemma lem240512 (h1 : term45) : term328.
Proof. exact (EQ_MP (@lem240511) (@lem240381 h1)). Qed.
Lemma lem240536 (n : nat) (P : nat -> Prop) (a : nat) : (term60 n P a) = (term60 n P a).
Proof. exact (eq_refl (term60 n P a)). Qed.
Lemma lem240537 (n : nat) (P : nat -> Prop) : (term70 n P) = (term70 n P).
Proof. exact (fun_ext (fun a : nat => @lem240536 n P a)). Qed.
Lemma lem240538 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem240540 (n : nat) (P : nat -> Prop) : (term71 n P) = (term71 n P).
Proof. exact (MK_COMB (@lem240538) (@lem240537 n P)). Qed.
Lemma lem240541 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term185 P a n) : term71 n P.
Proof. exact (EQ_MP (@lem240540 n P) (@lem240385 P a n h1)). Qed.
Lemma lem240551 (m : nat) : (term12 m) = (term12 m).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem240552 : term14 = term14.
Proof. exact (fun_ext (fun m : nat => @lem240551 m)). Qed.
Lemma lem240553 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem240555 : term16 = term16.
Proof. exact (MK_COMB (@lem240553) (@lem240552)). Qed.
Lemma lem240556 (h1 : term20) : term16.
Proof. exact (EQ_MP (@lem240555) (@lem240375 h1)). Qed.
Lemma lem240696 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem240769 (m : nat) (n : nat) : (term340 m n) = (term449 m n).
Proof. exact (@lem19490 (term41 n) ((Nat.modulo m n) = m) (term450 m n)). Qed.
Lemma lem240770 (m : nat) : (term351 m) = (term451 m).
Proof. exact (fun_ext (fun n : nat => @lem240769 m n)). Qed.
Lemma lem240771 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem240772 (m : nat) : (term362 m) = (term452 m).
Proof. exact (MK_COMB (@lem240771) (@lem240770 m)). Qed.
Lemma lem240773 : term373 = term453.
Proof. exact (fun_ext (fun m : nat => @lem240772 m)). Qed.
Lemma lem240774 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem240776 : term384 = term454.
Proof. exact (MK_COMB (@lem240774) (@lem240773)). Qed.
Lemma lem240777 (h1 : term39) : term454.
Proof. exact (EQ_MP (@lem240776) (@lem240379 h1)). Qed.
Lemma lem240841 (P : nat -> Prop) (a : nat) (n : nat) : (term46 P a n) = (term46 P a n).
Proof. exact (eq_refl (term46 P a n)). Qed.
Lemma lem240842 (P : nat -> Prop) (n : nat) : (term47 P n) = (term47 P n).
Proof. exact (fun_ext (fun a : nat => @lem240841 P a n)). Qed.
Lemma lem240843 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem240845 (P : nat -> Prop) (n : nat) : (term48 P n) = (term48 P n).
Proof. exact (MK_COMB (@lem240843) (@lem240842 P n)). Qed.
Lemma lem240846 (P : nat -> Prop) (n : nat) (h1 : term48 P n) : term48 P n.
Proof. exact (EQ_MP (@lem240845 P n) (@lem240393 P n h1)). Qed.
Lemma lem240874 (_4667 : nat) (h1 : term45) : term319 _4667.
Proof. exact (@lem240512 h1 _4667). Qed.
Lemma lem240875 (_4667 : nat) : (term319 _4667) = (term306 _4667).
Proof. exact (eq_refl (term319 _4667)). Qed.
Lemma lem240876 (_4667 : nat) (h1 : term45) : term306 _4667.
Proof. exact (EQ_MP (@lem240875 _4667) (@lem240874 _4667 h1)). Qed.
Lemma lem240877 (_4667 : nat) (_4668 : nat) (h1 : term45) : term297 _4667 _4668.
Proof. exact (@lem240876 _4667 h1 _4668). Qed.
Lemma lem240878 (_4667 : nat) (_4668 : nat) : (term297 _4667 _4668) = (term280 _4667 _4668).
Proof. exact (eq_refl (term297 _4667 _4668)). Qed.
Lemma lem240886 (_4671 : nat) (P : nat -> Prop) (a : nat) (n : nat) (h1 : term185 P a n) : term455 n P _4671.
Proof. exact (@lem240541 P a n h1 _4671). Qed.
Lemma lem240887 (n : nat) (P : nat -> Prop) (_4671 : nat) : (term455 n P _4671) = (term60 n P _4671).
Proof. exact (eq_refl (term455 n P _4671)). Qed.
Lemma lem240889 (_4672 : nat) (h1 : term20) : term456 _4672.
Proof. exact (@lem240556 h1 _4672). Qed.
Lemma lem240890 (_4672 : nat) : (term456 _4672) = (term12 _4672).
Proof. exact (eq_refl (term456 _4672)). Qed.
Lemma lem240943 (_4690 : nat) (h1 : term39) : term457 _4690.
Proof. exact (@lem240777 h1 _4690). Qed.
Lemma lem240944 (_4690 : nat) : (term457 _4690) = (term452 _4690).
Proof. exact (eq_refl (term457 _4690)). Qed.
Lemma lem240945 (_4690 : nat) (h1 : term39) : term452 _4690.
Proof. exact (EQ_MP (@lem240944 _4690) (@lem240943 _4690 h1)). Qed.
Lemma lem240946 (_4690 : nat) (_4691 : nat) (h1 : term39) : term458 _4690 _4691.
Proof. exact (@lem240945 _4690 h1 _4691). Qed.
Lemma lem240947 (_4690 : nat) (_4691 : nat) : (term458 _4690 _4691) = (term449 _4690 _4691).
Proof. exact (eq_refl (term458 _4690 _4691)). Qed.
Lemma lem240948 (_4690 : nat) (_4691 : nat) (h1 : term39) : term449 _4690 _4691.
Proof. exact (EQ_MP (@lem240947 _4690 _4691) (@lem240946 _4690 _4691 h1)). Qed.
Lemma lem240967 (_4698 : nat) (P : nat -> Prop) (n : nat) (h1 : term48 P n) : term74 P n _4698.
Proof. exact (@lem240846 P n h1 _4698). Qed.
Lemma lem240968 (P : nat -> Prop) (_4698 : nat) (n : nat) : (term74 P n _4698) = (term46 P _4698 n).
Proof. exact (eq_refl (term74 P n _4698)). Qed.
Lemma lem241009 (_4667 : nat) (_4668 : nat) (h1 : term45) : term280 _4667 _4668.
Proof. exact (EQ_MP (@lem240878 _4667 _4668) (@lem240877 _4667 _4668 h1)). Qed.
Lemma lem241021 (_4671 : nat) (P : nat -> Prop) (a : nat) (n : nat) (h1 : term185 P a n) : term60 n P _4671.
Proof. exact (EQ_MP (@lem240887 n P _4671) (@lem240886 _4671 P a n h1)). Qed.
Lemma lem241025 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term185 P a n) : term76 P a n.
Proof. exact (proj2 (@lem240384 P a n h1)). Qed.
Lemma lem241085 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term209 a P n) : Peano.lt a n.
Proof. exact (proj1 (@lem240389 a P n h1)). Qed.
Lemma lem241089 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem241151 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term209 a P n) : term459 P a.
Proof. exact (proj2 (@lem240389 a P n h1)). Qed.
Lemma lem241165 (_4690 : nat) (_4691 : nat) (h1 : term39) : term460 _4690 _4691.
Proof. exact (proj2 (@lem240948 _4690 _4691 h1)). Qed.
Lemma lem241205 (_4672 : nat) (h1 : term20) : term12 _4672.
Proof. exact (EQ_MP (@lem240890 _4672) (@lem240889 _4672 h1)). Qed.
Lemma lem241262 (a : nat) : (term461 a) = (term461 a).
Proof. exact (eq_refl (term461 a)). Qed.
Lemma lem241263 (a : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term462 a n) = (term463 a).
Proof. exact (MK_COMB (@lem241262 a) (@lem241089 n h1)). Qed.
Lemma lem241264 (a : nat) : (term463 a) = (term11 a).
Proof. exact (eq_refl (term463 a)). Qed.
Lemma lem241265 (a : nat) (n : nat) : (term464 a n) = (term464 a n).
Proof. exact (eq_refl (term464 a n)). Qed.
Lemma lem241266 (n : nat) (a : nat) : ((term462 a n) = (term463 a)) = ((term462 a n) = (term11 a)).
Proof. exact (MK_COMB (@lem241265 a n) (@lem241264 a)). Qed.
Lemma lem241267 (a : nat) (n : nat) : (term462 a n) = (Peano.lt a n).
Proof. exact (eq_refl (term462 a n)). Qed.
Lemma lem241268 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem241269 (a : nat) (n : nat) : (term464 a n) = (term465 a n).
Proof. exact (MK_COMB (@lem241268) (@lem241267 a n)). Qed.
Lemma lem241270 (a : nat) : (term11 a) = (term11 a).
Proof. exact (eq_refl (term11 a)). Qed.
Lemma lem241271 (n : nat) (a : nat) : ((term462 a n) = (term11 a)) = ((Peano.lt a n) = (term11 a)).
Proof. exact (MK_COMB (@lem241269 a n) (@lem241270 a)). Qed.
Lemma lem241272 (n : nat) (a : nat) : ((term462 a n) = (term463 a)) = ((Peano.lt a n) = (term11 a)).
Proof. exact (TRANS (@lem241266 n a) (@lem241271 n a)). Qed.
Lemma lem241273 (a : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Peano.lt a n) = (term11 a).
Proof. exact (EQ_MP (@lem241272 n a) (@lem241263 a n h1)). Qed.
Lemma lem241410 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term185 P a n) : term41 n.
Proof. exact (proj1 (@lem240384 P a n h1)). Qed.
Lemma lem241411 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term185 P a n) : term466 n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem241410 P a n h1). Qed.
Lemma lem241413 (p : Prop) : (term467 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem241414 (n : nat) : (term466 n) = (term41 n).
Proof. exact (@lem241413 (n = (NUMERAL 0))). Qed.
Lemma lem241415 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term185 P a n) : term41 n.
Proof. exact (EQ_MP (@lem241414 n) (@lem241411 P a n h1)). Qed.
Lemma lem241417 (b : Prop) (a : Prop) : (a \/ b) = (term468 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem241420 (_4667 : nat) (_4668 : nat) : (term280 _4667 _4668) = (term469 _4667 _4668).
Proof. exact (@lem241417 (_4668 = (NUMERAL 0)) (term40 _4667 _4668)). Qed.
Lemma lem241423 (_4667 : nat) (_4668 : nat) (h1 : term45) : term469 _4667 _4668.
Proof. exact (EQ_MP (@lem241420 _4667 _4668) (@lem241009 _4667 _4668 h1)). Qed.
Lemma lem241424 (_4667 : nat) (n : nat) (h1 : term45) : term469 _4667 n.
Proof. exact (@lem241423 _4667 n h1). Qed.
Lemma lem241427 (_4667 : nat) (P : nat -> Prop) (a : nat) (n : nat) (h1 : term45) (h2 : term185 P a n) : term40 _4667 n.
Proof. exact (@lem241424 _4667 n h1 (@lem241415 P a n h2)). Qed.
Lemma lem241428 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term45) (h2 : term185 P a n) : term40 a n.
Proof. exact (@lem241427 a P a n h1 h2). Qed.
Lemma lem241429 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term45) (h2 : term185 P a n) : term470 a n.
Proof. exact (fun h0 : term471 a n => @lem241428 P a n h1 h2). Qed.
Lemma lem241431 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem241432 (a : nat) (n : nat) : (term470 a n) = (term40 a n).
Proof. exact (@lem241431 (term40 a n)). Qed.
Lemma lem241433 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term45) (h2 : term185 P a n) : term40 a n.
Proof. exact (EQ_MP (@lem241432 a n) (@lem241429 P a n h1 h2)). Qed.
Lemma lem241439 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem241440 (P : nat -> Prop) (_4671 : nat) (n : nat) : (term60 n P _4671) = (term473 P _4671 n).
Proof. exact (@lem241439 (P _4671) (term450 _4671 n)). Qed.
Lemma lem241446 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem241447 (P : nat -> Prop) (_4671 : nat) (n : nat) : (term474 n P _4671) = (term475 P _4671 n).
Proof. exact (MK_COMB (@lem241446) (@lem241440 P _4671 n)). Qed.
Lemma lem241453 (P : nat -> Prop) (_4671 : nat) (n : nat) : (term473 P _4671 n) = (term473 P _4671 n).
Proof. exact (eq_refl (term473 P _4671 n)). Qed.
Lemma lem241454 (P : nat -> Prop) (_4671 : nat) (n : nat) : ((term60 n P _4671) = (term473 P _4671 n)) = ((term473 P _4671 n) = (term473 P _4671 n)).
Proof. exact (MK_COMB (@lem241447 P _4671 n) (@lem241453 P _4671 n)). Qed.
Lemma lem241456 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem241457 (x : Prop) : (x = x) = True.
Proof. exact (@lem241456 Prop x). Qed.
Lemma lem241458 (P : nat -> Prop) (_4671 : nat) (n : nat) : ((term473 P _4671 n) = (term473 P _4671 n)) = True.
Proof. exact (@lem241457 (term473 P _4671 n)). Qed.
Lemma lem241459 (P : nat -> Prop) (_4671 : nat) (n : nat) : ((term60 n P _4671) = (term473 P _4671 n)) = True.
Proof. exact (TRANS (@lem241454 P _4671 n) (@lem241458 P _4671 n)). Qed.
Lemma lem241460 (P : nat -> Prop) (_4671 : nat) (n : nat) : True = ((term60 n P _4671) = (term473 P _4671 n)).
Proof. exact (SYM (@lem241459 P _4671 n)). Qed.
Lemma lem241461 (P : nat -> Prop) (_4671 : nat) (n : nat) : (term60 n P _4671) = (term473 P _4671 n).
Proof. exact (EQ_MP (@lem241460 P _4671 n) (@lem0)). Qed.
Lemma lem241462 (_4671 : nat) (P : nat -> Prop) (a : nat) (n : nat) (h1 : term185 P a n) : term473 P _4671 n.
Proof. exact (EQ_MP (@lem241461 P _4671 n) (@lem241021 _4671 P a n h1)). Qed.
Lemma lem241464 (b : Prop) (a : Prop) : (a \/ b) = (term468 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem241465 (n : nat) (P : nat -> Prop) (_4671 : nat) : (term473 P _4671 n) = (term476 n P _4671).
Proof. exact (@lem241464 (term450 _4671 n) (P _4671)). Qed.
Lemma lem241467 (a : Prop) : (term477 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem241468 (_4671 : nat) (n : nat) : (term478 _4671 n) = (Peano.lt _4671 n).
Proof. exact (@lem241467 (Peano.lt _4671 n)). Qed.
Lemma lem241469 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem241470 (_4671 : nat) (n : nat) : (term479 _4671 n) = (term480 _4671 n).
Proof. exact (MK_COMB (@lem241469) (@lem241468 _4671 n)). Qed.
Lemma lem241471 (P : nat -> Prop) (_4671 : nat) : (P _4671) = (P _4671).
Proof. exact (eq_refl (P _4671)). Qed.
Lemma lem241472 (n : nat) (P : nat -> Prop) (_4671 : nat) : (term476 n P _4671) = (term51 n P _4671).
Proof. exact (MK_COMB (@lem241470 _4671 n) (@lem241471 P _4671)). Qed.
Lemma lem241473 (n : nat) (P : nat -> Prop) (_4671 : nat) : (term473 P _4671 n) = (term51 n P _4671).
Proof. exact (TRANS (@lem241465 n P _4671) (@lem241472 n P _4671)). Qed.
Lemma lem241476 (_4671 : nat) (P : nat -> Prop) (a : nat) (n : nat) (h1 : term185 P a n) : term51 n P _4671.
Proof. exact (EQ_MP (@lem241473 n P _4671) (@lem241462 _4671 P a n h1)). Qed.
Lemma lem241477 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term185 P a n) : term481 P a n.
Proof. exact (@lem241476 (Nat.modulo a n) P a n h1). Qed.
Lemma lem241480 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term45) (h2 : term185 P a n) : term46 P a n.
Proof. exact (@lem241477 P a n h2 (@lem241433 P a n h1 h2)). Qed.
Lemma lem241481 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term45) (h2 : term185 P a n) : term482 P a n.
Proof. exact (fun h0 : term76 P a n => @lem241480 P a n h1 h2). Qed.
Lemma lem241483 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem241484 (P : nat -> Prop) (a : nat) (n : nat) : (term482 P a n) = (term46 P a n).
Proof. exact (@lem241483 (term46 P a n)). Qed.
Lemma lem241485 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term45) (h2 : term185 P a n) : term46 P a n.
Proof. exact (EQ_MP (@lem241484 P a n) (@lem241481 P a n h1 h2)). Qed.
Lemma lem241488 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem241490 (P : nat -> Prop) (a : nat) (n : nat) : (term76 P a n) = (term483 P a n).
Proof. exact (@lem241488 (term46 P a n)). Qed.
Lemma lem241493 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term185 P a n) : term483 P a n.
Proof. exact (EQ_MP (@lem241490 P a n) (@lem241025 P a n h1)). Qed.
Lemma lem241496 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term45) (h2 : term185 P a n) : False.
Proof. exact (@lem241493 P a n h2 (@lem241485 P a n h1 h2)). Qed.
Lemma lem241497 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term45) (h2 : term185 P a n) : term484.
Proof. exact (fun h0 : ~ False => @lem241496 P a n h1 h2). Qed.
Lemma lem241499 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem241500 : term484 = False.
Proof. exact (@lem241499 False). Qed.
Lemma lem241501 (P : nat -> Prop) (a : nat) (n : nat) (h1 : term45) (h2 : term185 P a n) : False.
Proof. exact (EQ_MP (@lem241500) (@lem241497 P a n h1 h2)). Qed.
Lemma lem241567 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term209 a P n) (h2 : n = (NUMERAL 0)) : term11 a.
Proof. exact (EQ_MP (@lem241273 a n h2) (@lem241085 a P n h1)). Qed.
Lemma lem241568 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term209 a P n) (h2 : n = (NUMERAL 0)) : term485 a.
Proof. exact (fun h0 : term12 a => @lem241567 a P n h1 h2). Qed.
Lemma lem241570 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem241571 (a : nat) : (term485 a) = (term11 a).
Proof. exact (@lem241570 (term11 a)). Qed.
Lemma lem241572 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term209 a P n) (h2 : n = (NUMERAL 0)) : term11 a.
Proof. exact (EQ_MP (@lem241571 a) (@lem241568 a P n h1 h2)). Qed.
Lemma lem241575 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem241577 (_4672 : nat) : (term12 _4672) = (term486 _4672).
Proof. exact (@lem241575 (term11 _4672)). Qed.
Lemma lem241580 (_4672 : nat) (h1 : term20) : term486 _4672.
Proof. exact (EQ_MP (@lem241577 _4672) (@lem241205 _4672 h1)). Qed.
Lemma lem241581 (a : nat) (h1 : term20) : term486 a.
Proof. exact (@lem241580 a h1). Qed.
Lemma lem241584 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term20) (h2 : term209 a P n) (h3 : n = (NUMERAL 0)) : False.
Proof. exact (@lem241581 a h1 (@lem241572 a P n h2 h3)). Qed.
Lemma lem241585 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term20) (h2 : term209 a P n) (h3 : n = (NUMERAL 0)) : term484.
Proof. exact (fun h0 : ~ False => @lem241584 a P n h1 h2 h3). Qed.
Lemma lem241587 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem241588 : term484 = False.
Proof. exact (@lem241587 False). Qed.
Lemma lem241590 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem241591 (_4751 : nat) (_4752 : nat) (h1 : _4751 = _4752) : _4751 = _4752.
Proof. exact (h1). Qed.
Lemma lem241592 (P : nat -> Prop) (_4751 : nat) (_4752 : nat) (h1 : _4751 = _4752) : (P _4751) = (P _4752).
Proof. exact (MK_COMB (@lem241590 P) (@lem241591 _4751 _4752 h1)). Qed.
Lemma lem241594 (b : Prop) (a : Prop) : term487 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem241595 (_4752 : nat) (P : nat -> Prop) (_4751 : nat) : term488 _4752 P _4751.
Proof. exact (@lem241594 (P _4752) (P _4751)). Qed.
Lemma lem241596 (P : nat -> Prop) (_4751 : nat) (_4752 : nat) (h1 : _4751 = _4752) : term489 _4752 P _4751.
Proof. exact (@lem241595 _4752 P _4751 (@lem241592 P _4751 _4752 h1)). Qed.
Lemma lem241597 (_4752 : nat) (P : nat -> Prop) (_4751 : nat) : term490 _4752 P _4751.
Proof. exact (fun h0 : _4751 = _4752 => @lem241596 P _4751 _4752 h0). Qed.
Lemma lem241599 (a : Prop) (b : Prop) : (a -> b) = (term491 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem241600 (_4752 : nat) (P : nat -> Prop) (_4751 : nat) : (term490 _4752 P _4751) = (term492 _4752 P _4751).
Proof. exact (@lem241599 (_4751 = _4752) (term489 _4752 P _4751)). Qed.
Lemma lem241601 (_4752 : nat) (P : nat -> Prop) (_4751 : nat) : term492 _4752 P _4751.
Proof. exact (EQ_MP (@lem241600 _4752 P _4751) (@lem241597 _4752 P _4751)). Qed.
Lemma lem241655 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term209 a P n) : Peano.lt a n.
Proof. exact (proj1 (@lem240389 a P n h1)). Qed.
Lemma lem241656 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term209 a P n) : term493 a n.
Proof. exact (fun h0 : term450 a n => @lem241655 a P n h1). Qed.
Lemma lem241658 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem241659 (a : nat) (n : nat) : (term493 a n) = (Peano.lt a n).
Proof. exact (@lem241658 (Peano.lt a n)). Qed.
Lemma lem241660 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term209 a P n) : Peano.lt a n.
Proof. exact (EQ_MP (@lem241659 a n) (@lem241656 a P n h1)). Qed.
Lemma lem241662 (b : Prop) (a : Prop) : (a \/ b) = (term468 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem241663 (_4691 : nat) (_4690 : nat) : (term460 _4690 _4691) = (term494 _4691 _4690).
Proof. exact (@lem241662 (term450 _4690 _4691) ((Nat.modulo _4690 _4691) = _4690)). Qed.
Lemma lem241665 (a : Prop) : (term477 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem241666 (_4690 : nat) (_4691 : nat) : (term478 _4690 _4691) = (Peano.lt _4690 _4691).
Proof. exact (@lem241665 (Peano.lt _4690 _4691)). Qed.
Lemma lem241667 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem241668 (_4690 : nat) (_4691 : nat) : (term479 _4690 _4691) = (term480 _4690 _4691).
Proof. exact (MK_COMB (@lem241667) (@lem241666 _4690 _4691)). Qed.
Lemma lem241669 (_4691 : nat) (_4690 : nat) : ((Nat.modulo _4690 _4691) = _4690) = ((Nat.modulo _4690 _4691) = _4690).
Proof. exact (eq_refl ((Nat.modulo _4690 _4691) = _4690)). Qed.
Lemma lem241670 (_4691 : nat) (_4690 : nat) : (term494 _4691 _4690) = (term495 _4691 _4690).
Proof. exact (MK_COMB (@lem241668 _4690 _4691) (@lem241669 _4691 _4690)). Qed.
Lemma lem241671 (_4691 : nat) (_4690 : nat) : (term460 _4690 _4691) = (term495 _4691 _4690).
Proof. exact (TRANS (@lem241663 _4691 _4690) (@lem241670 _4691 _4690)). Qed.
Lemma lem241674 (_4691 : nat) (_4690 : nat) (h1 : term39) : term495 _4691 _4690.
Proof. exact (EQ_MP (@lem241671 _4691 _4690) (@lem241165 _4690 _4691 h1)). Qed.
Lemma lem241675 (n : nat) (a : nat) (h1 : term39) : term495 n a.
Proof. exact (@lem241674 n a h1). Qed.
Lemma lem241678 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term209 a P n) : (Nat.modulo a n) = a.
Proof. exact (@lem241675 n a h1 (@lem241660 a P n h2)). Qed.
Lemma lem241679 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term209 a P n) : term496 n a.
Proof. exact (fun h0 : term497 n a => @lem241678 a P n h1 h2). Qed.
Lemma lem241681 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem241682 (n : nat) (a : nat) : (term496 n a) = ((Nat.modulo a n) = a).
Proof. exact (@lem241681 ((Nat.modulo a n) = a)). Qed.
Lemma lem241683 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term209 a P n) : (Nat.modulo a n) = a.
Proof. exact (EQ_MP (@lem241682 n a) (@lem241679 a P n h1 h2)). Qed.
Lemma lem241685 (_4698 : nat) (P : nat -> Prop) (n : nat) (h1 : term48 P n) : term46 P _4698 n.
Proof. exact (EQ_MP (@lem240968 P _4698 n) (@lem240967 _4698 P n h1)). Qed.
Lemma lem241686 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term48 P n) : term46 P a n.
Proof. exact (@lem241685 a P n h1). Qed.
Lemma lem241687 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term48 P n) : term482 P a n.
Proof. exact (fun h0 : term76 P a n => @lem241686 a P n h1). Qed.
Lemma lem241689 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem241690 (P : nat -> Prop) (a : nat) (n : nat) : (term482 P a n) = (term46 P a n).
Proof. exact (@lem241689 (term46 P a n)). Qed.
Lemma lem241691 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term48 P n) : term46 P a n.
Proof. exact (EQ_MP (@lem241690 P a n) (@lem241687 a P n h1)). Qed.
Lemma lem241697 (q : Prop) (p : Prop) (r : Prop) : (term498 p q r) = (term498 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem241698 (_4752 : nat) (P : nat -> Prop) (_4751 : nat) : (term492 _4752 P _4751) = (term499 _4752 P _4751).
Proof. exact (@lem241697 (P _4752) (term500 _4751 _4752) (term459 P _4751)). Qed.
Lemma lem241712 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem241713 (P : nat -> Prop) (_4751 : nat) (_4752 : nat) : (term501 _4752 P _4751) = (term502 P _4751 _4752).
Proof. exact (@lem241712 (term459 P _4751) (term500 _4751 _4752)). Qed.
Lemma lem241721 (P : nat -> Prop) (_4752 : nat) : (term503 P _4752) = (term503 P _4752).
Proof. exact (eq_refl (term503 P _4752)). Qed.
Lemma lem241722 (P : nat -> Prop) (_4751 : nat) (_4752 : nat) : (term499 _4752 P _4751) = (term504 P _4751 _4752).
Proof. exact (MK_COMB (@lem241721 P _4752) (@lem241713 P _4751 _4752)). Qed.
Lemma lem241733 (P : nat -> Prop) (_4751 : nat) (_4752 : nat) : (term492 _4752 P _4751) = (term504 P _4751 _4752).
Proof. exact (TRANS (@lem241698 _4752 P _4751) (@lem241722 P _4751 _4752)). Qed.
Lemma lem241734 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem241735 (P : nat -> Prop) (_4751 : nat) (_4752 : nat) : (term505 _4752 P _4751) = (term506 P _4751 _4752).
Proof. exact (MK_COMB (@lem241734) (@lem241733 P _4751 _4752)). Qed.
Lemma lem241749 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem241750 (P : nat -> Prop) (_4751 : nat) (_4752 : nat) : (term501 _4752 P _4751) = (term502 P _4751 _4752).
Proof. exact (@lem241749 (term459 P _4751) (term500 _4751 _4752)). Qed.
Lemma lem241758 (P : nat -> Prop) (_4752 : nat) : (term503 P _4752) = (term503 P _4752).
Proof. exact (eq_refl (term503 P _4752)). Qed.
Lemma lem241759 (P : nat -> Prop) (_4751 : nat) (_4752 : nat) : (term499 _4752 P _4751) = (term504 P _4751 _4752).
Proof. exact (MK_COMB (@lem241758 P _4752) (@lem241750 P _4751 _4752)). Qed.
Lemma lem241770 (P : nat -> Prop) (_4751 : nat) (_4752 : nat) : ((term492 _4752 P _4751) = (term499 _4752 P _4751)) = ((term504 P _4751 _4752) = (term504 P _4751 _4752)).
Proof. exact (MK_COMB (@lem241735 P _4751 _4752) (@lem241759 P _4751 _4752)). Qed.
Lemma lem241772 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem241773 (x : Prop) : (x = x) = True.
Proof. exact (@lem241772 Prop x). Qed.
Lemma lem241774 (P : nat -> Prop) (_4751 : nat) (_4752 : nat) : ((term504 P _4751 _4752) = (term504 P _4751 _4752)) = True.
Proof. exact (@lem241773 (term504 P _4751 _4752)). Qed.
Lemma lem241775 (_4752 : nat) (P : nat -> Prop) (_4751 : nat) : ((term492 _4752 P _4751) = (term499 _4752 P _4751)) = True.
Proof. exact (TRANS (@lem241770 P _4751 _4752) (@lem241774 P _4751 _4752)). Qed.
Lemma lem241776 (_4752 : nat) (P : nat -> Prop) (_4751 : nat) : True = ((term492 _4752 P _4751) = (term499 _4752 P _4751)).
Proof. exact (SYM (@lem241775 _4752 P _4751)). Qed.
Lemma lem241777 (_4752 : nat) (P : nat -> Prop) (_4751 : nat) : (term492 _4752 P _4751) = (term499 _4752 P _4751).
Proof. exact (EQ_MP (@lem241776 _4752 P _4751) (@lem0)). Qed.
Lemma lem241778 (_4752 : nat) (P : nat -> Prop) (_4751 : nat) : term499 _4752 P _4751.
Proof. exact (EQ_MP (@lem241777 _4752 P _4751) (@lem241601 _4752 P _4751)). Qed.
Lemma lem241780 (b : Prop) (a : Prop) : (a \/ b) = (term468 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem241781 (_4751 : nat) (P : nat -> Prop) (_4752 : nat) : (term499 _4752 P _4751) = (term507 _4751 P _4752).
Proof. exact (@lem241780 (term501 _4752 P _4751) (P _4752)). Qed.
Lemma lem241783 (a : Prop) (b : Prop) : (term508 a b) = (term509 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem241784 (_4752 : nat) (P : nat -> Prop) (_4751 : nat) : (term510 _4752 P _4751) = (term511 _4752 P _4751).
Proof. exact (@lem241783 (term500 _4751 _4752) (term459 P _4751)). Qed.
Lemma lem241786 (a : Prop) : (term477 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem241787 (_4751 : nat) (_4752 : nat) : (term512 _4751 _4752) = (_4751 = _4752).
Proof. exact (@lem241786 (_4751 = _4752)). Qed.
Lemma lem241788 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem241789 (_4751 : nat) (_4752 : nat) : (term513 _4751 _4752) = (term514 _4751 _4752).
Proof. exact (MK_COMB (@lem241788) (@lem241787 _4751 _4752)). Qed.
Lemma lem241791 (a : Prop) : (term477 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem241792 (P : nat -> Prop) (_4751 : nat) : (term515 P _4751) = (P _4751).
Proof. exact (@lem241791 (P _4751)). Qed.
Lemma lem241793 (_4752 : nat) (P : nat -> Prop) (_4751 : nat) : (term511 _4752 P _4751) = (term516 _4752 P _4751).
Proof. exact (MK_COMB (@lem241789 _4751 _4752) (@lem241792 P _4751)). Qed.
Lemma lem241794 (_4752 : nat) (P : nat -> Prop) (_4751 : nat) : (term510 _4752 P _4751) = (term516 _4752 P _4751).
Proof. exact (TRANS (@lem241784 _4752 P _4751) (@lem241793 _4752 P _4751)). Qed.
Lemma lem241795 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem241796 (_4752 : nat) (P : nat -> Prop) (_4751 : nat) : (term517 _4752 P _4751) = (term518 _4752 P _4751).
Proof. exact (MK_COMB (@lem241795) (@lem241794 _4752 P _4751)). Qed.
Lemma lem241797 (P : nat -> Prop) (_4752 : nat) : (P _4752) = (P _4752).
Proof. exact (eq_refl (P _4752)). Qed.
Lemma lem241798 (_4751 : nat) (P : nat -> Prop) (_4752 : nat) : (term507 _4751 P _4752) = (term519 _4751 P _4752).
Proof. exact (MK_COMB (@lem241796 _4752 P _4751) (@lem241797 P _4752)). Qed.
Lemma lem241799 (_4751 : nat) (P : nat -> Prop) (_4752 : nat) : (term499 _4752 P _4751) = (term519 _4751 P _4752).
Proof. exact (TRANS (@lem241781 _4751 P _4752) (@lem241798 _4751 P _4752)). Qed.
Lemma lem241801 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term48 P n) (h3 : term209 a P n) : term520 P a n.
Proof. exact (conj (@lem241683 a P n h1 h3) (@lem241691 a P n h2)). Qed.
Lemma lem241803 (_4751 : nat) (P : nat -> Prop) (_4752 : nat) : term519 _4751 P _4752.
Proof. exact (EQ_MP (@lem241799 _4751 P _4752) (@lem241778 _4752 P _4751)). Qed.
Lemma lem241804 (n : nat) (P : nat -> Prop) (a : nat) : term521 n P a.
Proof. exact (@lem241803 (Nat.modulo a n) P a). Qed.
Lemma lem241807 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term48 P n) (h3 : term209 a P n) : P a.
Proof. exact (@lem241804 n P a (@lem241801 a P n h1 h2 h3)). Qed.
Lemma lem241808 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term48 P n) (h3 : term209 a P n) : term522 P a.
Proof. exact (fun h0 : term459 P a => @lem241807 a P n h1 h2 h3). Qed.
Lemma lem241810 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem241811 (P : nat -> Prop) (a : nat) : (term522 P a) = (P a).
Proof. exact (@lem241810 (P a)). Qed.
Lemma lem241812 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term48 P n) (h3 : term209 a P n) : P a.
Proof. exact (EQ_MP (@lem241811 P a) (@lem241808 a P n h1 h2 h3)). Qed.
Lemma lem241815 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem241817 (P : nat -> Prop) (a : nat) : (term459 P a) = (term523 P a).
Proof. exact (@lem241815 (P a)). Qed.
Lemma lem241820 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term209 a P n) : term523 P a.
Proof. exact (EQ_MP (@lem241817 P a) (@lem241151 a P n h1)). Qed.
Lemma lem241823 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term48 P n) (h3 : term209 a P n) : False.
Proof. exact (@lem241820 a P n h3 (@lem241812 a P n h1 h2 h3)). Qed.
Lemma lem241824 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term48 P n) (h3 : term209 a P n) : term484.
Proof. exact (fun h0 : ~ False => @lem241823 a P n h1 h2 h3). Qed.
Lemma lem241826 (p : Prop) : (term472 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem241827 : term484 = False.
Proof. exact (@lem241826 False). Qed.
Lemma lem241828 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term48 P n) (h3 : term209 a P n) : False.
Proof. exact (EQ_MP (@lem241827) (@lem241824 a P n h1 h2 h3)). Qed.
Lemma lem241829 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term20) (h2 : term209 a P n) (h3 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem241588) (@lem241585 a P n h1 h2 h3)). Qed.
Lemma lem241830 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term20) (h2 : term209 a P n) (h3 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h4 : n = (NUMERAL 0) => @lem241829 a P n h1 h2 h3) (fun h4 : False => @lem241089 n h3)). Qed.
Lemma lem241831 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term20) (h2 : term209 a P n) (h3 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem241830 a P n h1 h2 h3) (@lem241089 n h3)). Qed.
Lemma lem241832 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term20) (h2 : term209 a P n) (h3 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h4 : n = (NUMERAL 0) => @lem241831 a P n h1 h2 h3) (fun h4 : False => @lem240696 n h3)). Qed.
Lemma lem241833 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term20) (h2 : term209 a P n) (h3 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem241832 a P n h1 h2 h3) (@lem240696 n h3)). Qed.
Lemma lem241834 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term48 P n) (h3 : term209 a P n) : (term48 P n) = False.
Proof. exact (prop_ext (fun h4 : term48 P n => @lem241828 a P n h1 h2 h3) (fun h4 : False => @lem240846 P n h2)). Qed.
Lemma lem241835 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term48 P n) (h3 : term209 a P n) : False.
Proof. exact (EQ_MP (@lem241834 a P n h1 h2 h3) (@lem240846 P n h2)). Qed.
Lemma lem241836 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term20) (h2 : term209 a P n) (h3 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h4 : n = (NUMERAL 0) => @lem241833 a P n h1 h2 h3) (fun h4 : False => @lem240696 n h3)). Qed.
Lemma lem241837 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term20) (h2 : term209 a P n) (h3 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem241836 a P n h1 h2 h3) (@lem240696 n h3)). Qed.
Lemma lem241838 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term39) (h2 : term20) (h3 : term209 a P n) : False.
Proof. exact (or_elim (@lem240388 a P n h3) (fun h0 : n = (NUMERAL 0) => @lem241837 a P n h2 h3 h0) (fun h0 : term48 P n => @lem241835 a P n h1 h0 h3)). Qed.
Lemma lem241839 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term45) (h2 : term39) (h3 : term20) (h4 : term268 a P n) : False.
Proof. exact (or_elim (@lem240373 a P n h4) (fun h0 : term185 P a n => @lem241501 P a n h1 h0) (fun h0 : term209 a P n => @lem241838 a P n h2 h3 h0)). Qed.
Lemma lem241840 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term45) (h2 : term39) (h3 : term20) (h4 : term268 a P n) : (term268 a P n) = False.
Proof. exact (prop_ext (fun h5 : term268 a P n => @lem241839 a P n h1 h2 h3 h4) (fun h5 : False => @lem240373 a P n h4)). Qed.
Lemma lem241841 (a : nat) (P : nat -> Prop) (n : nat) (h1 : term45) (h2 : term39) (h3 : term20) (h4 : term268 a P n) : False.
Proof. exact (EQ_MP (@lem241840 a P n h1 h2 h3 h4) (@lem240373 a P n h4)). Qed.
Lemma lem241842 (P : nat -> Prop) (n : nat) (h1 : term45) (h2 : term39) (h3 : term271 P n) (h4 : term20) : False.
Proof. exact (ex_elim (@lem240075 P n h3) (fun a : nat => fun h0 : term270 P n a => @lem241841 a P n h1 h2 h4 h0)). Qed.
Lemma lem241843 (P : nat -> Prop) (h1 : term45) (h2 : term39) (h3 : term273 P) (h4 : term20) : False.
Proof. exact (ex_elim (@lem240074 P h3) (fun n : nat => fun h0 : term272 P n => @lem241842 P n h1 h2 h0 h4)). Qed.
Lemma lem241844 (h1 : term45) (h2 : term39) (h3 : term3) (h4 : term20) : False.
Proof. exact (ex_elim (@lem239177 h3) (fun P : nat -> Prop => fun h0 : term274 P => @lem241843 P h1 h2 h0 h4)). Qed.
Lemma lem241845 (h1 : term45) (h2 : term39) (h3 : term3) : term524.
Proof. exact (fun h0 : term20 => @lem241844 h1 h2 h3 h0). Qed.
Lemma lem241846 : term524 = term21.
Proof. exact (@lem69 term20). Qed.
Lemma lem241847 (h1 : term45) (h2 : term39) (h3 : term3) : term21.
Proof. exact (EQ_MP (@lem241846) (@lem241845 h1 h2 h3)). Qed.
Lemma lem241848 (h1 : term45) (h2 : term3) : term24.
Proof. exact (fun h0 : term39 => @lem241847 h1 h0 h2). Qed.
Lemma lem241849 (h1 : term3) : term27.
Proof. exact (fun h0 : term45 => @lem241848 h0 h1). Qed.
Lemma lem241850 : term29.
Proof. exact (fun h0 : term3 => @lem241849 h0). Qed.
Lemma lem241851 : term4.
Proof. exact (EQ_MP (@lem238477) (@lem241850)). Qed.
Lemma lem241853 : term4.
Proof. exact (@lem238203 (@lem241851)). Qed.
Lemma lem241854 (h1 : term3) : term26.
Proof. exact (@lem241853 (@lem238188 h1)). Qed.
Lemma lem241855 (h1 : term3) : term23.
Proof. exact (@lem241854 h1 (@lem165615)). Qed.
Lemma lem241856 (h1 : term3) : term8.
Proof. exact (@lem241855 h1 (@lem173992)). Qed.
Lemma lem241857 (h1 : term3) : False.
Proof. exact (@lem241856 h1 (@lem89997)). Qed.
Lemma lem241858 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem241857 h1) (fun h2 : False => @lem238188 h1)). Qed.
Lemma lem241859 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem241858 h1) (@lem238188 h1)). Qed.
Lemma lem241860 : term2.
Proof. exact (fun h0 : term3 => @lem241859 h0). Qed.
Lemma lem241861 : term1.
Proof. exact (EQ_MP (@lem238187) (@lem241860)). Qed.
