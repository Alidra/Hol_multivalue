Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LIST_EQ_term_abbrevs.
Require Import CONS_11_spec.
Require Import DISJ_ACI_spec.
Require Import LT_0_spec.
Require Import LT_SUC_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_CONS_NIL_spec.
Require Import NOT_SUC_spec.
Require Import SUC_INJ_spec.
Require Import num_CASES_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1094865_spec.
Require Import thm1094866_spec.
Require Import thm1095388_spec.
Require Import thm1095389_spec.
Require Import thm1097080_spec.
Require Import thm1105741_spec.
Require Import thm1105742_spec.
Require Import thm1105747_spec.
Require Import thm1105748_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm554_spec.
Require Import thm555_spec.
Require Import thm616_spec.
Require Import thm617_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm89994_spec.
Lemma lem1114178 (m : nat) : term0 m.
Proof. exact (@lem91415 m). Qed.
Lemma lem1114179 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1114180 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1114179 m) (@lem1114178 m)). Qed.
Lemma lem1114181 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1114180 m n). Qed.
Lemma lem1114182 (m : nat) (n : nat) : (term2 m n) = ((term3 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1114184 (n : nat) : term4 n.
Proof. exact (@lem91530 n). Qed.
Lemma lem1114185 (n : nat) : (term4 n) = (term5 n).
Proof. exact (eq_refl (term4 n)). Qed.
Lemma lem1114186 (n : nat) : term5 n.
Proof. exact (EQ_MP (@lem1114185 n) (@lem1114184 n)). Qed.
Lemma lem1114187 (n : nat) : (term5 n) = ((term5 n) = True).
Proof. exact (@lem7 (term5 n)). Qed.
Lemma lem1114202 (p : Prop) : p = (term6 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1114203 (P : nat -> Prop) : ((term7 P) = (term8 P)) = (term9 P).
Proof. exact (@lem1114202 ((term7 P) = (term8 P))). Qed.
Lemma lem1114204 (P : nat -> Prop) : (term9 P) = ((term7 P) = (term8 P)).
Proof. exact (SYM (@lem1114203 P)). Qed.
Lemma lem1114205 (P : nat -> Prop) (h1 : term10 P) : term10 P.
Proof. exact (h1). Qed.
Lemma lem1114208 (P : nat -> Prop) (h1 : term11 P) : term11 P.
Proof. exact (h1). Qed.
Lemma lem1114209 (P : nat -> Prop) : term12 P.
Proof. exact (fun h0 : term11 P => @lem1114208 P h0). Qed.
Lemma lem1114210 (P : nat -> Prop) (h1 : term12 P) : term12 P.
Proof. exact (h1). Qed.
Lemma lem1114211 (P : nat -> Prop) (h1 : term11 P) : term11 P.
Proof. exact (h1). Qed.
Lemma lem1114212 (P : nat -> Prop) (h1 : term11 P) (h2 : term12 P) : term11 P.
Proof. exact (@lem1114210 P h2 (@lem1114211 P h1)). Qed.
Lemma lem1114213 (P : nat -> Prop) (h1 : term11 P) : term13 P.
Proof. exact (fun h0 : term12 P => @lem1114212 P h1 h0). Qed.
Lemma lem1114214 (P : nat -> Prop) (h1 : term12 P) : term12 P.
Proof. exact (h1). Qed.
Lemma lem1114215 (P : nat -> Prop) (h1 : term11 P) (h2 : term12 P) : term11 P.
Proof. exact (@lem1114213 P h1 (@lem1114214 P h2)). Qed.
Lemma lem1114216 (P : nat -> Prop) (h1 : term12 P) : term12 P.
Proof. exact (fun h0 : term11 P => @lem1114215 P h0 h1). Qed.
Lemma lem1114217 (P : nat -> Prop) : term14 P.
Proof. exact (fun h0 : term12 P => @lem1114216 P h0). Qed.
Lemma lem1114220 (P : nat -> Prop) : term12 P.
Proof. exact (@lem1114217 P (@lem1114209 P)). Qed.
Lemma lem1114238 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1114239 : term15 = term16.
Proof. exact (@lem1114238 term17). Qed.
Lemma lem1114294 (P : nat -> Prop) : (term18 P) = (term18 P).
Proof. exact (eq_refl (term18 P)). Qed.
Lemma lem1114295 (P : nat -> Prop) : (term11 P) = (term19 P).
Proof. exact (MK_COMB (@lem1114294 P) (@lem1114239)). Qed.
Lemma lem1114298 : term20 = term21.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem1114295 P)). Qed.
Lemma lem1114299 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem1114308 : term22 = term23.
Proof. exact (MK_COMB (@lem1114299) (@lem1114298)). Qed.
Lemma lem1114309 (m : nat) (n : nat) : (m = (S n)) = (m = (S n)).
Proof. exact (eq_refl (m = (S n))). Qed.
Lemma lem1114310 (m : nat) : (term24 m) = (term24 m).
Proof. exact (fun_ext (fun n : nat => @lem1114309 m n)). Qed.
Lemma lem1114311 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1114312 (m : nat) : (term25 m) = (term25 m).
Proof. exact (MK_COMB (@lem1114311) (@lem1114310 m)). Qed.
Lemma lem1114315 (m : nat) : (term26 m) = (term26 m).
Proof. exact (eq_refl (term26 m)). Qed.
Lemma lem1114316 (m : nat) : (term27 m) = (term27 m).
Proof. exact (MK_COMB (@lem1114315 m) (@lem1114312 m)). Qed.
Lemma lem1114317 : term28 = term28.
Proof. exact (fun_ext (fun m : nat => @lem1114316 m)). Qed.
Lemma lem1114318 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1114319 : term17 = term17.
Proof. exact (MK_COMB (@lem1114318) (@lem1114317)). Qed.
Lemma lem1114320 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1114321 : term16 = term16.
Proof. exact (MK_COMB (@lem1114320) (@lem1114319)). Qed.
Lemma lem1114322 (P : nat -> Prop) (n : nat) : (term29 P n) = (term29 P n).
Proof. exact (eq_refl (term29 P n)). Qed.
Lemma lem1114323 (P : nat -> Prop) : (term30 P) = (term30 P).
Proof. exact (fun_ext (fun n : nat => @lem1114322 P n)). Qed.
Lemma lem1114324 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1114325 (P : nat -> Prop) : (term31 P) = (term31 P).
Proof. exact (MK_COMB (@lem1114324) (@lem1114323 P)). Qed.
Lemma lem1114328 (P : nat -> Prop) : (term32 P) = (term32 P).
Proof. exact (eq_refl (term32 P)). Qed.
Lemma lem1114329 (P : nat -> Prop) : (term8 P) = (term8 P).
Proof. exact (MK_COMB (@lem1114328 P) (@lem1114325 P)). Qed.
Lemma lem1114330 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem1114331 (P : nat -> Prop) : (term33 P) = (term33 P).
Proof. exact (fun_ext (fun n : nat => @lem1114330 P n)). Qed.
Lemma lem1114332 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1114333 (P : nat -> Prop) : (term7 P) = (term7 P).
Proof. exact (MK_COMB (@lem1114332) (@lem1114331 P)). Qed.
Lemma lem1114334 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1114335 (P : nat -> Prop) : (term34 P) = (term34 P).
Proof. exact (MK_COMB (@lem1114334) (@lem1114333 P)). Qed.
Lemma lem1114336 (P : nat -> Prop) : ((term7 P) = (term8 P)) = ((term7 P) = (term8 P)).
Proof. exact (MK_COMB (@lem1114335 P) (@lem1114329 P)). Qed.
Lemma lem1114337 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1114338 (P : nat -> Prop) : (term10 P) = (term10 P).
Proof. exact (MK_COMB (@lem1114337) (@lem1114336 P)). Qed.
Lemma lem1114339 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1114340 (P : nat -> Prop) : (term18 P) = (term18 P).
Proof. exact (MK_COMB (@lem1114339) (@lem1114338 P)). Qed.
Lemma lem1114341 (P : nat -> Prop) : (term19 P) = (term19 P).
Proof. exact (MK_COMB (@lem1114340 P) (@lem1114321)). Qed.
Lemma lem1114342 : term21 = term21.
Proof. exact (fun_ext (fun P : nat -> Prop => @lem1114341 P)). Qed.
Lemma lem1114343 : (@all (nat -> Prop)) = (@all (nat -> Prop)).
Proof. exact (eq_refl (@all (nat -> Prop))). Qed.
Lemma lem1114344 : term23 = term23.
Proof. exact (MK_COMB (@lem1114343) (@lem1114342)). Qed.
Lemma lem1114383 : term22 = term23.
Proof. exact (TRANS (@lem1114308) (@lem1114344)). Qed.
Lemma lem1114384 : term23 = term22.
Proof. exact (SYM (@lem1114383)). Qed.
Lemma lem1114385 (P : nat -> Prop) (h1 : term10 P) : term10 P.
Proof. exact (h1). Qed.
Lemma lem1114386 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1114388 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem1114389 (P : nat -> Prop) : (term35 P) = (term36 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem1114390 (P : nat -> Prop) : (term37 P) = (term38 P).
Proof. exact (@lem1114389 (term33 P)). Qed.
Lemma lem1114391 (P : nat -> Prop) (n : nat) : (term39 P n) = (P n).
Proof. exact (eq_refl (term39 P n)). Qed.
Lemma lem1114392 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1114394 (P : nat -> Prop) (n : nat) : (term40 P n) = (term41 P n).
Proof. exact (MK_COMB (@lem1114392) (@lem1114391 P n)). Qed.
Lemma lem1114395 (P : nat -> Prop) : (term42 P) = (term43 P).
Proof. exact (fun_ext (fun n : nat => @lem1114394 P n)). Qed.
Lemma lem1114396 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1114397 (P : nat -> Prop) : (term38 P) = (term36 P).
Proof. exact (MK_COMB (@lem1114396) (@lem1114395 P)). Qed.
Lemma lem1114398 (P : nat -> Prop) : (term37 P) = (term36 P).
Proof. exact (TRANS (@lem1114390 P) (@lem1114397 P)). Qed.
Lemma lem1114399 (P : nat -> Prop) : (term33 P) = (term33 P).
Proof. exact (fun_ext (fun n : nat => @lem1114388 P n)). Qed.
Lemma lem1114400 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1114401 (P : nat -> Prop) : (term7 P) = (term7 P).
Proof. exact (MK_COMB (@lem1114400) (@lem1114399 P)). Qed.
Lemma lem1114405 (P : nat -> Prop) (n : nat) : (term29 P n) = (term29 P n).
Proof. exact (eq_refl (term29 P n)). Qed.
Lemma lem1114406 (P : nat -> Prop) : (term35 P) = (term36 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem1114407 (P : nat -> Prop) : (term44 P) = (term45 P).
Proof. exact (@lem1114406 (term30 P)). Qed.
Lemma lem1114408 (P : nat -> Prop) (n : nat) : (term46 P n) = (term29 P n).
Proof. exact (eq_refl (term46 P n)). Qed.
Lemma lem1114409 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1114411 (P : nat -> Prop) (n : nat) : (term47 P n) = (term48 P n).
Proof. exact (MK_COMB (@lem1114409) (@lem1114408 P n)). Qed.
Lemma lem1114412 (P : nat -> Prop) : (term49 P) = (term50 P).
Proof. exact (fun_ext (fun n : nat => @lem1114411 P n)). Qed.
Lemma lem1114413 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1114414 (P : nat -> Prop) : (term45 P) = (term51 P).
Proof. exact (MK_COMB (@lem1114413) (@lem1114412 P)). Qed.
Lemma lem1114415 (P : nat -> Prop) : (term44 P) = (term51 P).
Proof. exact (TRANS (@lem1114407 P) (@lem1114414 P)). Qed.
Lemma lem1114416 (P : nat -> Prop) : (term30 P) = (term30 P).
Proof. exact (fun_ext (fun n : nat => @lem1114405 P n)). Qed.
Lemma lem1114417 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1114418 (P : nat -> Prop) : (term31 P) = (term31 P).
Proof. exact (MK_COMB (@lem1114417) (@lem1114416 P)). Qed.
Lemma lem1114420 (P : nat -> Prop) : (term52 P) = (term52 P).
Proof. exact (eq_refl (term52 P)). Qed.
Lemma lem1114421 (P : nat -> Prop) : (term53 P) = (term54 P).
Proof. exact (MK_COMB (@lem1114420 P) (@lem1114415 P)). Qed.
Lemma lem1114422 (P : nat -> Prop) : (term55 P) = (term53 P).
Proof. exact (@lem17045 (term56 P) (term31 P)). Qed.
Lemma lem1114423 (P : nat -> Prop) : (term55 P) = (term54 P).
Proof. exact (TRANS (@lem1114422 P) (@lem1114421 P)). Qed.
Lemma lem1114425 (P : nat -> Prop) : (term32 P) = (term32 P).
Proof. exact (eq_refl (term32 P)). Qed.
Lemma lem1114426 (P : nat -> Prop) : (term8 P) = (term8 P).
Proof. exact (MK_COMB (@lem1114425 P) (@lem1114418 P)). Qed.
Lemma lem1114427 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1114428 (P : nat -> Prop) : (term57 P) = (term58 P).
Proof. exact (MK_COMB (@lem1114427) (@lem1114398 P)). Qed.
Lemma lem1114429 (P : nat -> Prop) : (term59 P) = (term60 P).
Proof. exact (MK_COMB (@lem1114428 P) (@lem1114426 P)). Qed.
Lemma lem1114430 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1114431 (P : nat -> Prop) : (term61 P) = (term61 P).
Proof. exact (MK_COMB (@lem1114430) (@lem1114401 P)). Qed.
Lemma lem1114432 (P : nat -> Prop) : (term62 P) = (term63 P).
Proof. exact (MK_COMB (@lem1114431 P) (@lem1114423 P)). Qed.
Lemma lem1114433 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1114434 (P : nat -> Prop) : (term64 P) = (term65 P).
Proof. exact (MK_COMB (@lem1114433) (@lem1114432 P)). Qed.
Lemma lem1114435 (P : nat -> Prop) : (term66 P) = (term67 P).
Proof. exact (MK_COMB (@lem1114434 P) (@lem1114429 P)). Qed.
Lemma lem1114436 (P : nat -> Prop) : (term10 P) = (term66 P).
Proof. exact (@lem17646 (term7 P) (term8 P)). Qed.
Lemma lem1114437 (P : nat -> Prop) : (term10 P) = (term67 P).
Proof. exact (TRANS (@lem1114436 P) (@lem1114435 P)). Qed.
Lemma lem1114456 {A : Type'} (P : Prop) (Q : A -> Prop) : (term68 A P Q) = (term69 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1114457 (P : Prop) (Q : nat -> Prop) : (term70 P Q) = (term71 P Q).
Proof. exact (@lem1114456 nat P Q). Qed.
Lemma lem1114458 (P : nat -> Prop) : (term72 P) = (term73 P).
Proof. exact (@lem1114457 (term74 P) (term50 P)). Qed.
Lemma lem1114459 (P : nat -> Prop) (n : nat) : (term75 P n) = (term48 P n).
Proof. exact (eq_refl (term75 P n)). Qed.
Lemma lem1114460 (P : nat -> Prop) : (term76 P) = (term50 P).
Proof. exact (fun_ext (fun n : nat => @lem1114459 P n)). Qed.
Lemma lem1114461 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1114462 (P : nat -> Prop) : (term77 P) = (term51 P).
Proof. exact (MK_COMB (@lem1114461) (@lem1114460 P)). Qed.
Lemma lem1114463 (P : nat -> Prop) : (term52 P) = (term52 P).
Proof. exact (eq_refl (term52 P)). Qed.
Lemma lem1114464 (P : nat -> Prop) : (term72 P) = (term54 P).
Proof. exact (MK_COMB (@lem1114463 P) (@lem1114462 P)). Qed.
Lemma lem1114465 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1114466 (P : nat -> Prop) : (term78 P) = (term79 P).
Proof. exact (MK_COMB (@lem1114465) (@lem1114464 P)). Qed.
Lemma lem1114467 (P : nat -> Prop) (n : nat) : (term75 P n) = (term48 P n).
Proof. exact (eq_refl (term75 P n)). Qed.
Lemma lem1114468 (P : nat -> Prop) : (term52 P) = (term52 P).
Proof. exact (eq_refl (term52 P)). Qed.
Lemma lem1114469 (P : nat -> Prop) (n : nat) : (term80 P n) = (term81 P n).
Proof. exact (MK_COMB (@lem1114468 P) (@lem1114467 P n)). Qed.
Lemma lem1114470 (P : nat -> Prop) : (term82 P) = (term83 P).
Proof. exact (fun_ext (fun n : nat => @lem1114469 P n)). Qed.
Lemma lem1114471 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1114472 (P : nat -> Prop) : (term73 P) = (term84 P).
Proof. exact (MK_COMB (@lem1114471) (@lem1114470 P)). Qed.
Lemma lem1114473 (P : nat -> Prop) : ((term72 P) = (term73 P)) = ((term54 P) = (term84 P)).
Proof. exact (MK_COMB (@lem1114466 P) (@lem1114472 P)). Qed.
Lemma lem1114474 (P : nat -> Prop) : (term54 P) = (term84 P).
Proof. exact (EQ_MP (@lem1114473 P) (@lem1114458 P)). Qed.
Lemma lem1114475 (P : nat -> Prop) : (term61 P) = (term61 P).
Proof. exact (eq_refl (term61 P)). Qed.
Lemma lem1114476 (P : nat -> Prop) : (term63 P) = (term85 P).
Proof. exact (MK_COMB (@lem1114475 P) (@lem1114474 P)). Qed.
Lemma lem1114478 {A : Type'} (P : Prop) (Q : A -> Prop) : (term86 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1114479 (P : Prop) (Q : nat -> Prop) : (term88 P Q) = (term89 P Q).
Proof. exact (@lem1114478 nat P Q). Qed.
Lemma lem1114480 (P : nat -> Prop) : (term90 P) = (term91 P).
Proof. exact (@lem1114479 (term7 P) (term83 P)). Qed.
Lemma lem1114481 (P : nat -> Prop) (n : nat) : (term92 P n) = (term81 P n).
Proof. exact (eq_refl (term92 P n)). Qed.
Lemma lem1114482 (P : nat -> Prop) : (term93 P) = (term83 P).
Proof. exact (fun_ext (fun n : nat => @lem1114481 P n)). Qed.
Lemma lem1114483 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1114484 (P : nat -> Prop) : (term94 P) = (term84 P).
Proof. exact (MK_COMB (@lem1114483) (@lem1114482 P)). Qed.
Lemma lem1114485 (P : nat -> Prop) : (term61 P) = (term61 P).
Proof. exact (eq_refl (term61 P)). Qed.
Lemma lem1114486 (P : nat -> Prop) : (term90 P) = (term85 P).
Proof. exact (MK_COMB (@lem1114485 P) (@lem1114484 P)). Qed.
Lemma lem1114487 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1114488 (P : nat -> Prop) : (term95 P) = (term96 P).
Proof. exact (MK_COMB (@lem1114487) (@lem1114486 P)). Qed.
Lemma lem1114489 (P : nat -> Prop) (n : nat) : (term92 P n) = (term81 P n).
Proof. exact (eq_refl (term92 P n)). Qed.
Lemma lem1114490 (P : nat -> Prop) : (term61 P) = (term61 P).
Proof. exact (eq_refl (term61 P)). Qed.
Lemma lem1114491 (P : nat -> Prop) (n : nat) : (term97 P n) = (term98 P n).
Proof. exact (MK_COMB (@lem1114490 P) (@lem1114489 P n)). Qed.
Lemma lem1114492 (P : nat -> Prop) : (term99 P) = (term100 P).
Proof. exact (fun_ext (fun n : nat => @lem1114491 P n)). Qed.
Lemma lem1114493 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1114494 (P : nat -> Prop) : (term91 P) = (term101 P).
Proof. exact (MK_COMB (@lem1114493) (@lem1114492 P)). Qed.
Lemma lem1114495 (P : nat -> Prop) : ((term90 P) = (term91 P)) = ((term85 P) = (term101 P)).
Proof. exact (MK_COMB (@lem1114488 P) (@lem1114494 P)). Qed.
Lemma lem1114496 (P : nat -> Prop) : (term85 P) = (term101 P).
Proof. exact (EQ_MP (@lem1114495 P) (@lem1114480 P)). Qed.
Lemma lem1114497 (P : nat -> Prop) : (term63 P) = (term101 P).
Proof. exact (TRANS (@lem1114476 P) (@lem1114496 P)). Qed.
Lemma lem1114498 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1114499 (P : nat -> Prop) : (term65 P) = (term102 P).
Proof. exact (MK_COMB (@lem1114498) (@lem1114497 P)). Qed.
Lemma lem1114501 {A : Type'} (P : A -> Prop) (Q : Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1114502 (P : nat -> Prop) (Q : Prop) : (term105 P Q) = (term106 P Q).
Proof. exact (@lem1114501 nat P Q). Qed.
Lemma lem1114503 (P : nat -> Prop) : (term107 P) = (term108 P).
Proof. exact (@lem1114502 (term43 P) (term8 P)). Qed.
Lemma lem1114504 (P : nat -> Prop) (n : nat) : (term109 P n) = (term41 P n).
Proof. exact (eq_refl (term109 P n)). Qed.
Lemma lem1114505 (P : nat -> Prop) : (term110 P) = (term43 P).
Proof. exact (fun_ext (fun n : nat => @lem1114504 P n)). Qed.
Lemma lem1114506 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1114507 (P : nat -> Prop) : (term111 P) = (term36 P).
Proof. exact (MK_COMB (@lem1114506) (@lem1114505 P)). Qed.
Lemma lem1114508 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1114509 (P : nat -> Prop) : (term112 P) = (term58 P).
Proof. exact (MK_COMB (@lem1114508) (@lem1114507 P)). Qed.
Lemma lem1114510 (P : nat -> Prop) : (term8 P) = (term8 P).
Proof. exact (eq_refl (term8 P)). Qed.
Lemma lem1114511 (P : nat -> Prop) : (term107 P) = (term60 P).
Proof. exact (MK_COMB (@lem1114509 P) (@lem1114510 P)). Qed.
Lemma lem1114512 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1114513 (P : nat -> Prop) : (term113 P) = (term114 P).
Proof. exact (MK_COMB (@lem1114512) (@lem1114511 P)). Qed.
Lemma lem1114514 (P : nat -> Prop) (n : nat) : (term109 P n) = (term41 P n).
Proof. exact (eq_refl (term109 P n)). Qed.
Lemma lem1114515 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1114516 (P : nat -> Prop) (n : nat) : (term115 P n) = (term116 P n).
Proof. exact (MK_COMB (@lem1114515) (@lem1114514 P n)). Qed.
Lemma lem1114517 (P : nat -> Prop) : (term8 P) = (term8 P).
Proof. exact (eq_refl (term8 P)). Qed.
Lemma lem1114518 (n : nat) (P : nat -> Prop) : (term117 n P) = (term118 n P).
Proof. exact (MK_COMB (@lem1114516 P n) (@lem1114517 P)). Qed.
Lemma lem1114519 (P : nat -> Prop) : (term119 P) = (term120 P).
Proof. exact (fun_ext (fun n : nat => @lem1114518 n P)). Qed.
Lemma lem1114520 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1114521 (P : nat -> Prop) : (term108 P) = (term121 P).
Proof. exact (MK_COMB (@lem1114520) (@lem1114519 P)). Qed.
Lemma lem1114522 (P : nat -> Prop) : ((term107 P) = (term108 P)) = ((term60 P) = (term121 P)).
Proof. exact (MK_COMB (@lem1114513 P) (@lem1114521 P)). Qed.
Lemma lem1114523 (P : nat -> Prop) : (term60 P) = (term121 P).
Proof. exact (EQ_MP (@lem1114522 P) (@lem1114503 P)). Qed.
Lemma lem1114524 (P : nat -> Prop) : (term67 P) = (term122 P).
Proof. exact (MK_COMB (@lem1114499 P) (@lem1114523 P)). Qed.
Lemma lem1114526 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term123 A P Q) = (term124 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1114527 (P : nat -> Prop) (Q : nat -> Prop) : (term125 P Q) = (term126 P Q).
Proof. exact (@lem1114526 nat P Q). Qed.
Lemma lem1114528 (P : nat -> Prop) : (term127 P) = (term128 P).
Proof. exact (@lem1114527 (term100 P) (term120 P)). Qed.
Lemma lem1114529 (P : nat -> Prop) (n : nat) : (term129 P n) = (term98 P n).
Proof. exact (eq_refl (term129 P n)). Qed.
Lemma lem1114530 (P : nat -> Prop) : (term130 P) = (term100 P).
Proof. exact (fun_ext (fun n : nat => @lem1114529 P n)). Qed.
Lemma lem1114531 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1114532 (P : nat -> Prop) : (term131 P) = (term101 P).
Proof. exact (MK_COMB (@lem1114531) (@lem1114530 P)). Qed.
Lemma lem1114533 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1114534 (P : nat -> Prop) : (term132 P) = (term102 P).
Proof. exact (MK_COMB (@lem1114533) (@lem1114532 P)). Qed.
Lemma lem1114535 (n : nat) (P : nat -> Prop) : (term133 P n) = (term118 n P).
Proof. exact (eq_refl (term133 P n)). Qed.
Lemma lem1114536 (P : nat -> Prop) : (term134 P) = (term120 P).
Proof. exact (fun_ext (fun n : nat => @lem1114535 n P)). Qed.
Lemma lem1114537 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1114538 (P : nat -> Prop) : (term135 P) = (term121 P).
Proof. exact (MK_COMB (@lem1114537) (@lem1114536 P)). Qed.
Lemma lem1114539 (P : nat -> Prop) : (term127 P) = (term122 P).
Proof. exact (MK_COMB (@lem1114534 P) (@lem1114538 P)). Qed.
Lemma lem1114540 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1114541 (P : nat -> Prop) : (term136 P) = (term137 P).
Proof. exact (MK_COMB (@lem1114540) (@lem1114539 P)). Qed.
Lemma lem1114542 (P : nat -> Prop) (n : nat) : (term129 P n) = (term98 P n).
Proof. exact (eq_refl (term129 P n)). Qed.
Lemma lem1114543 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1114544 (P : nat -> Prop) (n : nat) : (term138 P n) = (term139 P n).
Proof. exact (MK_COMB (@lem1114543) (@lem1114542 P n)). Qed.
Lemma lem1114545 (n : nat) (P : nat -> Prop) : (term133 P n) = (term118 n P).
Proof. exact (eq_refl (term133 P n)). Qed.
Lemma lem1114546 (n : nat) (P : nat -> Prop) : (term140 P n) = (term141 n P).
Proof. exact (MK_COMB (@lem1114544 P n) (@lem1114545 n P)). Qed.
Lemma lem1114547 (P : nat -> Prop) : (term142 P) = (term143 P).
Proof. exact (fun_ext (fun n : nat => @lem1114546 n P)). Qed.
Lemma lem1114548 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1114549 (P : nat -> Prop) : (term128 P) = (term144 P).
Proof. exact (MK_COMB (@lem1114548) (@lem1114547 P)). Qed.
Lemma lem1114550 (P : nat -> Prop) : ((term127 P) = (term128 P)) = ((term122 P) = (term144 P)).
Proof. exact (MK_COMB (@lem1114541 P) (@lem1114549 P)). Qed.
Lemma lem1114551 (P : nat -> Prop) : (term122 P) = (term144 P).
Proof. exact (EQ_MP (@lem1114550 P) (@lem1114528 P)). Qed.
Lemma lem1114553 (P : nat -> Prop) : (term67 P) = (term144 P).
Proof. exact (TRANS (@lem1114524 P) (@lem1114551 P)). Qed.
Lemma lem1114554 (P : nat -> Prop) : (term10 P) = (term144 P).
Proof. exact (TRANS (@lem1114437 P) (@lem1114553 P)). Qed.
Lemma lem1114555 (P : nat -> Prop) (h1 : term10 P) : term144 P.
Proof. exact (EQ_MP (@lem1114554 P) (@lem1114385 P h1)). Qed.
Lemma lem1114557 (m : nat) (n : nat) : (m = (S n)) = (m = (S n)).
Proof. exact (eq_refl (m = (S n))). Qed.
Lemma lem1114558 (m : nat) : (term24 m) = (term24 m).
Proof. exact (fun_ext (fun n : nat => @lem1114557 m n)). Qed.
Lemma lem1114559 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1114560 (m : nat) : (term25 m) = (term25 m).
Proof. exact (MK_COMB (@lem1114559) (@lem1114558 m)). Qed.
Lemma lem1114562 (m : nat) : (term26 m) = (term26 m).
Proof. exact (eq_refl (term26 m)). Qed.
Lemma lem1114563 (m : nat) : (term27 m) = (term27 m).
Proof. exact (MK_COMB (@lem1114562 m) (@lem1114560 m)). Qed.
Lemma lem1114564 : term28 = term28.
Proof. exact (fun_ext (fun m : nat => @lem1114563 m)). Qed.
Lemma lem1114565 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1114566 : term17 = term17.
Proof. exact (MK_COMB (@lem1114565) (@lem1114564)). Qed.
Lemma lem1114621 {A : Type'} (P : Prop) (Q : A -> Prop) : (term68 A P Q) = (term69 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1114622 (P : Prop) (Q : nat -> Prop) : (term70 P Q) = (term71 P Q).
Proof. exact (@lem1114621 nat P Q). Qed.
Lemma lem1114623 (m : nat) : (term145 m) = (term146 m).
Proof. exact (@lem1114622 (m = (NUMERAL 0)) (term24 m)). Qed.
Lemma lem1114624 (m : nat) (n : nat) : (term147 m n) = (m = (S n)).
Proof. exact (eq_refl (term147 m n)). Qed.
Lemma lem1114625 (m : nat) : (term148 m) = (term24 m).
Proof. exact (fun_ext (fun n : nat => @lem1114624 m n)). Qed.
Lemma lem1114626 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1114627 (m : nat) : (term149 m) = (term25 m).
Proof. exact (MK_COMB (@lem1114626) (@lem1114625 m)). Qed.
Lemma lem1114628 (m : nat) : (term26 m) = (term26 m).
Proof. exact (eq_refl (term26 m)). Qed.
Lemma lem1114629 (m : nat) : (term145 m) = (term27 m).
Proof. exact (MK_COMB (@lem1114628 m) (@lem1114627 m)). Qed.
Lemma lem1114630 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1114631 (m : nat) : (term150 m) = (term151 m).
Proof. exact (MK_COMB (@lem1114630) (@lem1114629 m)). Qed.
Lemma lem1114632 (m : nat) (n : nat) : (term147 m n) = (m = (S n)).
Proof. exact (eq_refl (term147 m n)). Qed.
Lemma lem1114633 (m : nat) : (term26 m) = (term26 m).
Proof. exact (eq_refl (term26 m)). Qed.
Lemma lem1114634 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (MK_COMB (@lem1114633 m) (@lem1114632 m n)). Qed.
Lemma lem1114635 (m : nat) : (term154 m) = (term155 m).
Proof. exact (fun_ext (fun n : nat => @lem1114634 m n)). Qed.
Lemma lem1114636 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1114637 (m : nat) : (term146 m) = (term156 m).
Proof. exact (MK_COMB (@lem1114636) (@lem1114635 m)). Qed.
Lemma lem1114638 (m : nat) : ((term145 m) = (term146 m)) = ((term27 m) = (term156 m)).
Proof. exact (MK_COMB (@lem1114631 m) (@lem1114637 m)). Qed.
Lemma lem1114639 (m : nat) : (term27 m) = (term156 m).
Proof. exact (EQ_MP (@lem1114638 m) (@lem1114623 m)). Qed.
Lemma lem1114640 : term28 = term157.
Proof. exact (fun_ext (fun m : nat => @lem1114639 m)). Qed.
Lemma lem1114641 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1114642 : term17 = term158.
Proof. exact (MK_COMB (@lem1114641) (@lem1114640)). Qed.
Lemma lem1114644 {A B : Type'} (P : type1413 A B) : (term159 A B P) = (term160 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem1114645 (P : type1605) : (term161 P) = (term162 P).
Proof. exact (@lem1114644 nat nat P). Qed.
Lemma lem1114646 : term163 = term164.
Proof. exact (@lem1114645 term165). Qed.
Lemma lem1114647 (m : nat) : (term166 m) = (term155 m).
Proof. exact (eq_refl (term166 m)). Qed.
Lemma lem1114648 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1114649 (m : nat) (n : nat) : (term167 m n) = (term168 m n).
Proof. exact (MK_COMB (@lem1114647 m) (@lem1114648 n)). Qed.
Lemma lem1114650 (m : nat) (n : nat) : (term168 m n) = (term153 m n).
Proof. exact (eq_refl (term168 m n)). Qed.
Lemma lem1114651 (m : nat) (n : nat) : (term167 m n) = (term153 m n).
Proof. exact (TRANS (@lem1114649 m n) (@lem1114650 m n)). Qed.
Lemma lem1114652 (m : nat) : (term169 m) = (term155 m).
Proof. exact (fun_ext (fun n : nat => @lem1114651 m n)). Qed.
Lemma lem1114653 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1114654 (m : nat) : (term170 m) = (term156 m).
Proof. exact (MK_COMB (@lem1114653) (@lem1114652 m)). Qed.
Lemma lem1114655 : term171 = term157.
Proof. exact (fun_ext (fun m : nat => @lem1114654 m)). Qed.
Lemma lem1114656 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1114657 : term163 = term158.
Proof. exact (MK_COMB (@lem1114656) (@lem1114655)). Qed.
Lemma lem1114658 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1114659 : term172 = term173.
Proof. exact (MK_COMB (@lem1114658) (@lem1114657)). Qed.
Lemma lem1114660 (m : nat) : (term166 m) = (term155 m).
Proof. exact (eq_refl (term166 m)). Qed.
Lemma lem1114661 (n : nat -> nat) (m : nat) : (n m) = (n m).
Proof. exact (eq_refl (n m)). Qed.
Lemma lem1114662 (n : nat -> nat) (m : nat) : (term174 n m) = (term175 n m).
Proof. exact (MK_COMB (@lem1114660 m) (@lem1114661 n m)). Qed.
Lemma lem1114663 (n : nat -> nat) (m : nat) : (term175 n m) = (term176 n m).
Proof. exact (eq_refl (term175 n m)). Qed.
Lemma lem1114664 (n : nat -> nat) (m : nat) : (term174 n m) = (term176 n m).
Proof. exact (TRANS (@lem1114662 n m) (@lem1114663 n m)). Qed.
Lemma lem1114665 (n : nat -> nat) : (term177 n) = (term178 n).
Proof. exact (fun_ext (fun m : nat => @lem1114664 n m)). Qed.
Lemma lem1114666 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1114667 (n : nat -> nat) : (term179 n) = (term180 n).
Proof. exact (MK_COMB (@lem1114666) (@lem1114665 n)). Qed.
Lemma lem1114668 : term181 = term182.
Proof. exact (fun_ext (fun n : nat -> nat => @lem1114667 n)). Qed.
Lemma lem1114669 : (@ex (nat -> nat)) = (@ex (nat -> nat)).
Proof. exact (eq_refl (@ex (nat -> nat))). Qed.
Lemma lem1114670 : term164 = term183.
Proof. exact (MK_COMB (@lem1114669) (@lem1114668)). Qed.
Lemma lem1114671 : (term163 = term164) = (term158 = term183).
Proof. exact (MK_COMB (@lem1114659) (@lem1114670)). Qed.
Lemma lem1114672 : term158 = term183.
Proof. exact (EQ_MP (@lem1114671) (@lem1114646)). Qed.
Lemma lem1114674 : term17 = term183.
Proof. exact (TRANS (@lem1114642) (@lem1114672)). Qed.
Lemma lem1114675 : term17 = term183.
Proof. exact (TRANS (@lem1114566) (@lem1114674)). Qed.
Lemma lem1114676 (h1 : term17) : term183.
Proof. exact (EQ_MP (@lem1114675) (@lem1114386 h1)). Qed.
Lemma lem1114677 (n : nat -> nat) (h1 : term180 n) : term180 n.
Proof. exact (h1). Qed.
Lemma lem1114678 (n' : nat) (P : nat -> Prop) (h1 : term141 n' P) : term141 n' P.
Proof. exact (h1). Qed.
Lemma lem1114697 (n : nat -> nat) (m : nat) : (term176 n m) = (term176 n m).
Proof. exact (eq_refl (term176 n m)). Qed.
Lemma lem1114698 (n : nat -> nat) : (term178 n) = (term178 n).
Proof. exact (fun_ext (fun m : nat => @lem1114697 n m)). Qed.
Lemma lem1114699 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1114700 (n : nat -> nat) : (term180 n) = (term180 n).
Proof. exact (MK_COMB (@lem1114699) (@lem1114698 n)). Qed.
Lemma lem1114701 (n : nat -> nat) (h1 : term180 n) : term180 n.
Proof. exact (EQ_MP (@lem1114700 n) (@lem1114677 n h1)). Qed.
Lemma lem1114706 (P : nat -> Prop) (n : nat) : (term29 P n) = (term29 P n).
Proof. exact (eq_refl (term29 P n)). Qed.
Lemma lem1114707 (P : nat -> Prop) : (term30 P) = (term30 P).
Proof. exact (fun_ext (fun n : nat => @lem1114706 P n)). Qed.
Lemma lem1114708 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1114709 (P : nat -> Prop) : (term31 P) = (term31 P).
Proof. exact (MK_COMB (@lem1114708) (@lem1114707 P)). Qed.
Lemma lem1114716 (P : nat -> Prop) : (term32 P) = (term32 P).
Proof. exact (eq_refl (term32 P)). Qed.
Lemma lem1114717 (P : nat -> Prop) : (term8 P) = (term8 P).
Proof. exact (MK_COMB (@lem1114716 P) (@lem1114709 P)). Qed.
Lemma lem1114724 (P : nat -> Prop) (n' : nat) : (term116 P n') = (term116 P n').
Proof. exact (eq_refl (term116 P n')). Qed.
Lemma lem1114725 (n' : nat) (P : nat -> Prop) : (term118 n' P) = (term118 n' P).
Proof. exact (MK_COMB (@lem1114724 P n') (@lem1114717 P)). Qed.
Lemma lem1114742 (P : nat -> Prop) (n' : nat) : (term81 P n') = (term81 P n').
Proof. exact (eq_refl (term81 P n')). Qed.
Lemma lem1114745 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem1114746 (P : nat -> Prop) : (term33 P) = (term33 P).
Proof. exact (fun_ext (fun n : nat => @lem1114745 P n)). Qed.
Lemma lem1114747 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1114748 (P : nat -> Prop) : (term7 P) = (term7 P).
Proof. exact (MK_COMB (@lem1114747) (@lem1114746 P)). Qed.
Lemma lem1114749 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1114750 (P : nat -> Prop) : (term61 P) = (term61 P).
Proof. exact (MK_COMB (@lem1114749) (@lem1114748 P)). Qed.
Lemma lem1114751 (P : nat -> Prop) (n' : nat) : (term98 P n') = (term98 P n').
Proof. exact (MK_COMB (@lem1114750 P) (@lem1114742 P n')). Qed.
Lemma lem1114752 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1114753 (P : nat -> Prop) (n' : nat) : (term139 P n') = (term139 P n').
Proof. exact (MK_COMB (@lem1114752) (@lem1114751 P n')). Qed.
Lemma lem1114754 (n' : nat) (P : nat -> Prop) : (term141 n' P) = (term141 n' P).
Proof. exact (MK_COMB (@lem1114753 P n') (@lem1114725 n' P)). Qed.
Lemma lem1114755 (n' : nat) (P : nat -> Prop) (h1 : term141 n' P) : term141 n' P.
Proof. exact (EQ_MP (@lem1114754 n' P) (@lem1114678 n' P h1)). Qed.
Lemma lem1114756 (P : nat -> Prop) (n' : nat) (h1 : term98 P n') : term98 P n'.
Proof. exact (h1). Qed.
Lemma lem1114757 (n' : nat) (P : nat -> Prop) (h1 : term118 n' P) : term118 n' P.
Proof. exact (h1). Qed.
Lemma lem1114758 (P : nat -> Prop) (n' : nat) (h1 : term98 P n') : term81 P n'.
Proof. exact (proj2 (@lem1114756 P n' h1)). Qed.
Lemma lem1114759 (P : nat -> Prop) (n' : nat) (h1 : term98 P n') : term7 P.
Proof. exact (proj1 (@lem1114756 P n' h1)). Qed.
Lemma lem1114762 (n' : nat) (P : nat -> Prop) (h1 : term118 n' P) : term8 P.
Proof. exact (proj2 (@lem1114757 n' P h1)). Qed.
Lemma lem1114764 (n' : nat) (P : nat -> Prop) (h1 : term118 n' P) : term31 P.
Proof. exact (proj2 (@lem1114762 n' P h1)). Qed.
Lemma lem1114780 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem1114781 (P : nat -> Prop) : (term33 P) = (term33 P).
Proof. exact (fun_ext (fun n : nat => @lem1114780 P n)). Qed.
Lemma lem1114782 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1114784 (P : nat -> Prop) : (term7 P) = (term7 P).
Proof. exact (MK_COMB (@lem1114782) (@lem1114781 P)). Qed.
Lemma lem1114785 (P : nat -> Prop) (n' : nat) (h1 : term98 P n') : term7 P.
Proof. exact (EQ_MP (@lem1114784 P) (@lem1114759 P n' h1)). Qed.
Lemma lem1114789 (P : nat -> Prop) (h1 : term74 P) : term74 P.
Proof. exact (h1). Qed.
Lemma lem1114804 (P : nat -> Prop) (n : nat) : (P n) = (P n).
Proof. exact (eq_refl (P n)). Qed.
Lemma lem1114805 (P : nat -> Prop) : (term33 P) = (term33 P).
Proof. exact (fun_ext (fun n : nat => @lem1114804 P n)). Qed.
Lemma lem1114806 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1114808 (P : nat -> Prop) : (term7 P) = (term7 P).
Proof. exact (MK_COMB (@lem1114806) (@lem1114805 P)). Qed.
Lemma lem1114809 (P : nat -> Prop) (n' : nat) (h1 : term98 P n') : term7 P.
Proof. exact (EQ_MP (@lem1114808 P) (@lem1114759 P n' h1)). Qed.
Lemma lem1114813 (P : nat -> Prop) (n' : nat) (h1 : term48 P n') : term48 P n'.
Proof. exact (h1). Qed.
Lemma lem1114821 (n : nat -> nat) (m : nat) : (term176 n m) = (term176 n m).
Proof. exact (eq_refl (term176 n m)). Qed.
Lemma lem1114822 (n : nat -> nat) : (term178 n) = (term178 n).
Proof. exact (fun_ext (fun m : nat => @lem1114821 n m)). Qed.
Lemma lem1114823 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1114825 (n : nat -> nat) : (term180 n) = (term180 n).
Proof. exact (MK_COMB (@lem1114823) (@lem1114822 n)). Qed.
Lemma lem1114826 (n : nat -> nat) (h1 : term180 n) : term180 n.
Proof. exact (EQ_MP (@lem1114825 n) (@lem1114701 n h1)). Qed.
Lemma lem1114836 (P : nat -> Prop) (n : nat) : (term29 P n) = (term29 P n).
Proof. exact (eq_refl (term29 P n)). Qed.
Lemma lem1114837 (P : nat -> Prop) : (term30 P) = (term30 P).
Proof. exact (fun_ext (fun n : nat => @lem1114836 P n)). Qed.
Lemma lem1114838 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1114840 (P : nat -> Prop) : (term31 P) = (term31 P).
Proof. exact (MK_COMB (@lem1114838) (@lem1114837 P)). Qed.
Lemma lem1114841 (n' : nat) (P : nat -> Prop) (h1 : term118 n' P) : term31 P.
Proof. exact (EQ_MP (@lem1114840 P) (@lem1114764 n' P h1)). Qed.
Lemma lem1114845 (_18114 : nat) (P : nat -> Prop) (n' : nat) (h1 : term98 P n') : term39 P _18114.
Proof. exact (@lem1114785 P n' h1 _18114). Qed.
Lemma lem1114846 (P : nat -> Prop) (_18114 : nat) : (term39 P _18114) = (P _18114).
Proof. exact (eq_refl (term39 P _18114)). Qed.
Lemma lem1114851 (_18116 : nat) (P : nat -> Prop) (n' : nat) (h1 : term98 P n') : term39 P _18116.
Proof. exact (@lem1114809 P n' h1 _18116). Qed.
Lemma lem1114852 (P : nat -> Prop) (_18116 : nat) : (term39 P _18116) = (P _18116).
Proof. exact (eq_refl (term39 P _18116)). Qed.
Lemma lem1114854 (_18117 : nat) (n : nat -> nat) (h1 : term180 n) : term184 n _18117.
Proof. exact (@lem1114826 n h1 _18117). Qed.
Lemma lem1114855 (n : nat -> nat) (_18117 : nat) : (term184 n _18117) = (term176 n _18117).
Proof. exact (eq_refl (term184 n _18117)). Qed.
Lemma lem1114857 (_18118 : nat) (n' : nat) (P : nat -> Prop) (h1 : term118 n' P) : term46 P _18118.
Proof. exact (@lem1114841 n' P h1 _18118). Qed.
Lemma lem1114858 (P : nat -> Prop) (_18118 : nat) : (term46 P _18118) = (term29 P _18118).
Proof. exact (eq_refl (term46 P _18118)). Qed.
Lemma lem1114869 (P : nat -> Prop) (h1 : term74 P) : term74 P.
Proof. exact (h1). Qed.
Lemma lem1114879 (P : nat -> Prop) (n' : nat) (h1 : term48 P n') : term48 P n'.
Proof. exact (h1). Qed.
Lemma lem1114885 (_18117 : nat) (n : nat -> nat) (h1 : term180 n) : term176 n _18117.
Proof. exact (EQ_MP (@lem1114855 n _18117) (@lem1114854 _18117 n h1)). Qed.
Lemma lem1114887 (n' : nat) (P : nat -> Prop) (h1 : term118 n' P) : term41 P n'.
Proof. exact (proj1 (@lem1114757 n' P h1)). Qed.
Lemma lem1114931 (_18114 : nat) (P : nat -> Prop) (n' : nat) (h1 : term98 P n') : P _18114.
Proof. exact (EQ_MP (@lem1114846 P _18114) (@lem1114845 _18114 P n' h1)). Qed.
Lemma lem1114932 (P : nat -> Prop) (n' : nat) (h1 : term98 P n') : term56 P.
Proof. exact (@lem1114931 (NUMERAL 0) P n' h1). Qed.
Lemma lem1114933 (P : nat -> Prop) (n' : nat) (h1 : term98 P n') : term185 P.
Proof. exact (fun h0 : term74 P => @lem1114932 P n' h1). Qed.
Lemma lem1114935 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1114936 (P : nat -> Prop) : (term185 P) = (term56 P).
Proof. exact (@lem1114935 (term56 P)). Qed.
Lemma lem1114937 (P : nat -> Prop) (n' : nat) (h1 : term98 P n') : term56 P.
Proof. exact (EQ_MP (@lem1114936 P) (@lem1114933 P n' h1)). Qed.
Lemma lem1114940 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1114942 (P : nat -> Prop) : (term74 P) = (term187 P).
Proof. exact (@lem1114940 (term56 P)). Qed.
Lemma lem1114945 (P : nat -> Prop) (h1 : term74 P) : term187 P.
Proof. exact (EQ_MP (@lem1114942 P) (@lem1114869 P h1)). Qed.
Lemma lem1114948 (P : nat -> Prop) (n' : nat) (h1 : term74 P) (h2 : term98 P n') : False.
Proof. exact (@lem1114945 P h1 (@lem1114937 P n' h2)). Qed.
Lemma lem1114949 (P : nat -> Prop) (n' : nat) (h1 : term74 P) (h2 : term98 P n') : term188.
Proof. exact (fun h0 : ~ False => @lem1114948 P n' h1 h2). Qed.
Lemma lem1114951 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1114952 : term188 = False.
Proof. exact (@lem1114951 False). Qed.
Lemma lem1114953 (P : nat -> Prop) (n' : nat) (h1 : term74 P) (h2 : term98 P n') : False.
Proof. exact (EQ_MP (@lem1114952) (@lem1114949 P n' h1 h2)). Qed.
Lemma lem1114993 (_18116 : nat) (P : nat -> Prop) (n' : nat) (h1 : term98 P n') : P _18116.
Proof. exact (EQ_MP (@lem1114852 P _18116) (@lem1114851 _18116 P n' h1)). Qed.
Lemma lem1114994 (P : nat -> Prop) (n' : nat) (h1 : term98 P n') : term29 P n'.
Proof. exact (@lem1114993 (S n') P n' h1). Qed.
Lemma lem1114995 (P : nat -> Prop) (n' : nat) (h1 : term98 P n') : term189 P n'.
Proof. exact (fun h0 : term48 P n' => @lem1114994 P n' h1). Qed.
Lemma lem1114997 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1114998 (P : nat -> Prop) (n' : nat) : (term189 P n') = (term29 P n').
Proof. exact (@lem1114997 (term29 P n')). Qed.
Lemma lem1114999 (P : nat -> Prop) (n' : nat) (h1 : term98 P n') : term29 P n'.
Proof. exact (EQ_MP (@lem1114998 P n') (@lem1114995 P n' h1)). Qed.
Lemma lem1115002 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1115004 (P : nat -> Prop) (n' : nat) : (term48 P n') = (term190 P n').
Proof. exact (@lem1115002 (term29 P n')). Qed.
Lemma lem1115007 (P : nat -> Prop) (n' : nat) (h1 : term48 P n') : term190 P n'.
Proof. exact (EQ_MP (@lem1115004 P n') (@lem1114879 P n' h1)). Qed.
Lemma lem1115010 (P : nat -> Prop) (n' : nat) (h1 : term48 P n') (h2 : term98 P n') : False.
Proof. exact (@lem1115007 P n' h1 (@lem1114999 P n' h2)). Qed.
Lemma lem1115011 (P : nat -> Prop) (n' : nat) (h1 : term48 P n') (h2 : term98 P n') : term188.
Proof. exact (fun h0 : ~ False => @lem1115010 P n' h1 h2). Qed.
Lemma lem1115013 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1115014 : term188 = False.
Proof. exact (@lem1115013 False). Qed.
Lemma lem1115015 (P : nat -> Prop) (n' : nat) (h1 : term48 P n') (h2 : term98 P n') : False.
Proof. exact (EQ_MP (@lem1115014) (@lem1115011 P n' h1 h2)). Qed.
Lemma lem1115016 (P : nat -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem1115017 (_18135 : nat) (_18136 : nat) (h1 : _18135 = _18136) : _18135 = _18136.
Proof. exact (h1). Qed.
Lemma lem1115018 (P : nat -> Prop) (_18135 : nat) (_18136 : nat) (h1 : _18135 = _18136) : (P _18135) = (P _18136).
Proof. exact (MK_COMB (@lem1115016 P) (@lem1115017 _18135 _18136 h1)). Qed.
Lemma lem1115020 (b : Prop) (a : Prop) : term191 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1115021 (_18136 : nat) (P : nat -> Prop) (_18135 : nat) : term192 _18136 P _18135.
Proof. exact (@lem1115020 (P _18136) (P _18135)). Qed.
Lemma lem1115022 (P : nat -> Prop) (_18135 : nat) (_18136 : nat) (h1 : _18135 = _18136) : term193 _18136 P _18135.
Proof. exact (@lem1115021 _18136 P _18135 (@lem1115018 P _18135 _18136 h1)). Qed.
Lemma lem1115023 (_18136 : nat) (P : nat -> Prop) (_18135 : nat) : term194 _18136 P _18135.
Proof. exact (fun h0 : _18135 = _18136 => @lem1115022 P _18135 _18136 h0). Qed.
Lemma lem1115025 (a : Prop) (b : Prop) : (a -> b) = (term195 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1115026 (_18136 : nat) (P : nat -> Prop) (_18135 : nat) : (term194 _18136 P _18135) = (term196 _18136 P _18135).
Proof. exact (@lem1115025 (_18135 = _18136) (term193 _18136 P _18135)). Qed.
Lemma lem1115027 (_18136 : nat) (P : nat -> Prop) (_18135 : nat) : term196 _18136 P _18135.
Proof. exact (EQ_MP (@lem1115026 _18136 P _18135) (@lem1115023 _18136 P _18135)). Qed.
Lemma lem1115053 (x : nat) (y : nat) (z : nat) : term197 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem1115055 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1115056 (n' : nat) : n' = n'.
Proof. exact (@lem1115055 n'). Qed.
Lemma lem1115057 (n' : nat) : term198 n'.
Proof. exact (fun h0 : term199 n' => @lem1115056 n'). Qed.
Lemma lem1115059 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1115060 (n' : nat) : (term198 n') = (n' = n').
Proof. exact (@lem1115059 (n' = n')). Qed.
Lemma lem1115061 (n' : nat) : n' = n'.
Proof. exact (EQ_MP (@lem1115060 n') (@lem1115057 n')). Qed.
Lemma lem1115064 (P : nat -> Prop) (n' : nat) (h1 : term41 P n') : term41 P n'.
Proof. exact (h1). Qed.
Lemma lem1115065 (P : nat -> Prop) (n' : nat) (h1 : term41 P n') : term200 P n'.
Proof. exact (fun h0 : P n' => @lem1115064 P n' h1). Qed.
Lemma lem1115067 (p : Prop) : (term201 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1115068 (P : nat -> Prop) (n' : nat) : (term200 P n') = (term41 P n').
Proof. exact (@lem1115067 (P n')). Qed.
Lemma lem1115069 (P : nat -> Prop) (n' : nat) (h1 : term41 P n') : term41 P n'.
Proof. exact (EQ_MP (@lem1115068 P n') (@lem1115065 P n' h1)). Qed.
Lemma lem1115071 (n' : nat) (P : nat -> Prop) (h1 : term118 n' P) : term56 P.
Proof. exact (proj1 (@lem1114762 n' P h1)). Qed.
Lemma lem1115072 (n' : nat) (P : nat -> Prop) (h1 : term118 n' P) : term185 P.
Proof. exact (fun h0 : term74 P => @lem1115071 n' P h1). Qed.
Lemma lem1115074 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1115075 (P : nat -> Prop) : (term185 P) = (term56 P).
Proof. exact (@lem1115074 (term56 P)). Qed.
Lemma lem1115076 (n' : nat) (P : nat -> Prop) (h1 : term118 n' P) : term56 P.
Proof. exact (EQ_MP (@lem1115075 P) (@lem1115072 n' P h1)). Qed.
Lemma lem1115078 (b : Prop) (a : Prop) : (a \/ b) = (term202 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1115079 (P : nat -> Prop) (_18135 : nat) (_18136 : nat) : (term196 _18136 P _18135) = (term203 P _18135 _18136).
Proof. exact (@lem1115078 (term193 _18136 P _18135) (term204 _18135 _18136)). Qed.
Lemma lem1115081 (a : Prop) (b : Prop) : (term205 a b) = (term206 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1115082 (_18136 : nat) (P : nat -> Prop) (_18135 : nat) : (term207 _18136 P _18135) = (term208 _18136 P _18135).
Proof. exact (@lem1115081 (P _18136) (term41 P _18135)). Qed.
Lemma lem1115084 (a : Prop) : (term209 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1115085 (P : nat -> Prop) (_18135 : nat) : (term210 P _18135) = (P _18135).
Proof. exact (@lem1115084 (P _18135)). Qed.
Lemma lem1115086 (P : nat -> Prop) (_18136 : nat) : (term116 P _18136) = (term116 P _18136).
Proof. exact (eq_refl (term116 P _18136)). Qed.
Lemma lem1115087 (_18136 : nat) (P : nat -> Prop) (_18135 : nat) : (term208 _18136 P _18135) = (term211 _18136 P _18135).
Proof. exact (MK_COMB (@lem1115086 P _18136) (@lem1115085 P _18135)). Qed.
Lemma lem1115088 (_18136 : nat) (P : nat -> Prop) (_18135 : nat) : (term207 _18136 P _18135) = (term211 _18136 P _18135).
Proof. exact (TRANS (@lem1115082 _18136 P _18135) (@lem1115087 _18136 P _18135)). Qed.
Lemma lem1115089 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1115090 (_18136 : nat) (P : nat -> Prop) (_18135 : nat) : (term212 _18136 P _18135) = (term213 _18136 P _18135).
Proof. exact (MK_COMB (@lem1115089) (@lem1115088 _18136 P _18135)). Qed.
Lemma lem1115091 (_18135 : nat) (_18136 : nat) : (term204 _18135 _18136) = (term204 _18135 _18136).
Proof. exact (eq_refl (term204 _18135 _18136)). Qed.
Lemma lem1115092 (P : nat -> Prop) (_18135 : nat) (_18136 : nat) : (term203 P _18135 _18136) = (term214 P _18135 _18136).
Proof. exact (MK_COMB (@lem1115090 _18136 P _18135) (@lem1115091 _18135 _18136)). Qed.
Lemma lem1115093 (P : nat -> Prop) (_18135 : nat) (_18136 : nat) : (term196 _18136 P _18135) = (term214 P _18135 _18136).
Proof. exact (TRANS (@lem1115079 P _18135 _18136) (@lem1115092 P _18135 _18136)). Qed.
Lemma lem1115095 (n' : nat) (P : nat -> Prop) (h1 : term41 P n') (h2 : term118 n' P) : term215 n' P.
Proof. exact (conj (@lem1115069 P n' h1) (@lem1115076 n' P h2)). Qed.
Lemma lem1115097 (P : nat -> Prop) (_18135 : nat) (_18136 : nat) : term214 P _18135 _18136.
Proof. exact (EQ_MP (@lem1115093 P _18135 _18136) (@lem1115027 _18136 P _18135)). Qed.
Lemma lem1115098 (P : nat -> Prop) (n' : nat) : term216 P n'.
Proof. exact (@lem1115097 P (NUMERAL 0) n'). Qed.
Lemma lem1115101 (n' : nat) (P : nat -> Prop) (h1 : term41 P n') (h2 : term118 n' P) : term217 n'.
Proof. exact (@lem1115098 P n' (@lem1115095 n' P h1 h2)). Qed.
Lemma lem1115102 (n' : nat) (P : nat -> Prop) (h1 : term41 P n') (h2 : term118 n' P) : term218 n'.
Proof. exact (fun h0 : (NUMERAL 0) = n' => @lem1115101 n' P h1 h2). Qed.
Lemma lem1115104 (p : Prop) : (term201 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1115105 (n' : nat) : (term218 n') = (term217 n').
Proof. exact (@lem1115104 ((NUMERAL 0) = n')). Qed.
Lemma lem1115106 (n' : nat) (P : nat -> Prop) (h1 : term41 P n') (h2 : term118 n' P) : term217 n'.
Proof. exact (EQ_MP (@lem1115105 n') (@lem1115102 n' P h1 h2)). Qed.
Lemma lem1115108 (b : Prop) (a : Prop) : (a \/ b) = (term202 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1115109 (z : nat) (x : nat) (y : nat) : (term197 x y z) = (term219 z x y).
Proof. exact (@lem1115108 (term220 x y z) (term204 x y)). Qed.
Lemma lem1115111 (a : Prop) (b : Prop) : (term205 a b) = (term206 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1115112 (x : nat) (y : nat) (z : nat) : (term221 x y z) = (term222 x y z).
Proof. exact (@lem1115111 (term204 x z) (y = z)). Qed.
Lemma lem1115114 (a : Prop) : (term209 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1115115 (x : nat) (z : nat) : (term223 x z) = (x = z).
Proof. exact (@lem1115114 (x = z)). Qed.
Lemma lem1115116 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1115117 (x : nat) (z : nat) : (term224 x z) = (term225 x z).
Proof. exact (MK_COMB (@lem1115116) (@lem1115115 x z)). Qed.
Lemma lem1115118 (y : nat) (z : nat) : (term204 y z) = (term204 y z).
Proof. exact (eq_refl (term204 y z)). Qed.
Lemma lem1115119 (x : nat) (y : nat) (z : nat) : (term222 x y z) = (term226 x y z).
Proof. exact (MK_COMB (@lem1115117 x z) (@lem1115118 y z)). Qed.
Lemma lem1115120 (x : nat) (y : nat) (z : nat) : (term221 x y z) = (term226 x y z).
Proof. exact (TRANS (@lem1115112 x y z) (@lem1115119 x y z)). Qed.
Lemma lem1115121 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1115122 (x : nat) (y : nat) (z : nat) : (term227 x y z) = (term228 x y z).
Proof. exact (MK_COMB (@lem1115121) (@lem1115120 x y z)). Qed.
Lemma lem1115123 (x : nat) (y : nat) : (term204 x y) = (term204 x y).
Proof. exact (eq_refl (term204 x y)). Qed.
Lemma lem1115124 (z : nat) (x : nat) (y : nat) : (term219 z x y) = (term229 z x y).
Proof. exact (MK_COMB (@lem1115122 x y z) (@lem1115123 x y)). Qed.
Lemma lem1115125 (z : nat) (x : nat) (y : nat) : (term197 x y z) = (term229 z x y).
Proof. exact (TRANS (@lem1115109 z x y) (@lem1115124 z x y)). Qed.
Lemma lem1115127 (n' : nat) (P : nat -> Prop) (h1 : term41 P n') (h2 : term118 n' P) : term230 n'.
Proof. exact (conj (@lem1115061 n') (@lem1115106 n' P h1 h2)). Qed.
Lemma lem1115129 (z : nat) (x : nat) (y : nat) : term229 z x y.
Proof. exact (EQ_MP (@lem1115125 z x y) (@lem1115053 x y z)). Qed.
Lemma lem1115130 (n' : nat) : term231 n'.
Proof. exact (@lem1115129 n' n' (NUMERAL 0)). Qed.
Lemma lem1115133 (n' : nat) (P : nat -> Prop) (h1 : term41 P n') (h2 : term118 n' P) : term232 n'.
Proof. exact (@lem1115130 n' (@lem1115127 n' P h1 h2)). Qed.
Lemma lem1115134 (n' : nat) (P : nat -> Prop) (h1 : term41 P n') (h2 : term118 n' P) : term233 n'.
Proof. exact (fun h0 : n' = (NUMERAL 0) => @lem1115133 n' P h1 h2). Qed.
Lemma lem1115136 (p : Prop) : (term201 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1115137 (n' : nat) : (term233 n') = (term232 n').
Proof. exact (@lem1115136 (n' = (NUMERAL 0))). Qed.
Lemma lem1115138 (n' : nat) (P : nat -> Prop) (h1 : term41 P n') (h2 : term118 n' P) : term232 n'.
Proof. exact (EQ_MP (@lem1115137 n') (@lem1115134 n' P h1 h2)). Qed.
Lemma lem1115153 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1115154 (n : nat -> nat) (_18117 : nat) : (term234 n _18117) = (term176 n _18117).
Proof. exact (@lem1115153 (_18117 = (NUMERAL 0)) (_18117 = (term235 n _18117))). Qed.
Lemma lem1115164 (n : nat -> nat) (_18117 : nat) : (term236 n _18117) = (term236 n _18117).
Proof. exact (eq_refl (term236 n _18117)). Qed.
Lemma lem1115165 (n : nat -> nat) (_18117 : nat) : ((term176 n _18117) = (term234 n _18117)) = ((term176 n _18117) = (term176 n _18117)).
Proof. exact (MK_COMB (@lem1115164 n _18117) (@lem1115154 n _18117)). Qed.
Lemma lem1115167 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1115168 (x : Prop) : (x = x) = True.
Proof. exact (@lem1115167 Prop x). Qed.
Lemma lem1115169 (n : nat -> nat) (_18117 : nat) : ((term176 n _18117) = (term176 n _18117)) = True.
Proof. exact (@lem1115168 (term176 n _18117)). Qed.
Lemma lem1115170 (n : nat -> nat) (_18117 : nat) : ((term176 n _18117) = (term234 n _18117)) = True.
Proof. exact (TRANS (@lem1115165 n _18117) (@lem1115169 n _18117)). Qed.
Lemma lem1115171 (n : nat -> nat) (_18117 : nat) : True = ((term176 n _18117) = (term234 n _18117)).
Proof. exact (SYM (@lem1115170 n _18117)). Qed.
Lemma lem1115172 (n : nat -> nat) (_18117 : nat) : (term176 n _18117) = (term234 n _18117).
Proof. exact (EQ_MP (@lem1115171 n _18117) (@lem0)). Qed.
Lemma lem1115173 (_18117 : nat) (n : nat -> nat) (h1 : term180 n) : term234 n _18117.
Proof. exact (EQ_MP (@lem1115172 n _18117) (@lem1114885 _18117 n h1)). Qed.
Lemma lem1115175 (b : Prop) (a : Prop) : (a \/ b) = (term202 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1115178 (n : nat -> nat) (_18117 : nat) : (term234 n _18117) = (term237 n _18117).
Proof. exact (@lem1115175 (_18117 = (NUMERAL 0)) (_18117 = (term235 n _18117))). Qed.
Lemma lem1115181 (_18117 : nat) (n : nat -> nat) (h1 : term180 n) : term237 n _18117.
Proof. exact (EQ_MP (@lem1115178 n _18117) (@lem1115173 _18117 n h1)). Qed.
Lemma lem1115182 (n' : nat) (n : nat -> nat) (h1 : term180 n) : term237 n n'.
Proof. exact (@lem1115181 n' n h1). Qed.
Lemma lem1115185 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term180 n) (h2 : term41 P n') (h3 : term118 n' P) : n' = (term235 n n').
Proof. exact (@lem1115182 n' n h1 (@lem1115138 n' P h2 h3)). Qed.
Lemma lem1115186 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term180 n) (h2 : term41 P n') (h3 : term118 n' P) : term238 n n'.
Proof. exact (fun h0 : term239 n n' => @lem1115185 n n' P h1 h2 h3). Qed.
Lemma lem1115188 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1115189 (n : nat -> nat) (n' : nat) : (term238 n n') = (n' = (term235 n n')).
Proof. exact (@lem1115188 (n' = (term235 n n'))). Qed.
Lemma lem1115190 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term180 n) (h2 : term41 P n') (h3 : term118 n' P) : n' = (term235 n n').
Proof. exact (EQ_MP (@lem1115189 n n') (@lem1115186 n n' P h1 h2 h3)). Qed.
Lemma lem1115192 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem1115193 (n' : nat) : n' = n'.
Proof. exact (@lem1115192 n'). Qed.
Lemma lem1115194 (n' : nat) : term198 n'.
Proof. exact (fun h0 : term199 n' => @lem1115193 n'). Qed.
Lemma lem1115196 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1115197 (n' : nat) : (term198 n') = (n' = n').
Proof. exact (@lem1115196 (n' = n')). Qed.
Lemma lem1115198 (n' : nat) : n' = n'.
Proof. exact (EQ_MP (@lem1115197 n') (@lem1115194 n')). Qed.
Lemma lem1115216 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1115217 (y : nat) (x : nat) (z : nat) : (term220 x y z) = (term240 y x z).
Proof. exact (@lem1115216 (y = z) (term204 x z)). Qed.
Lemma lem1115227 (x : nat) (y : nat) : (term241 x y) = (term241 x y).
Proof. exact (eq_refl (term241 x y)). Qed.
Lemma lem1115228 (y : nat) (x : nat) (z : nat) : (term197 x y z) = (term242 y x z).
Proof. exact (MK_COMB (@lem1115227 x y) (@lem1115217 y x z)). Qed.
Lemma lem1115232 (q : Prop) (p : Prop) (r : Prop) : (term243 p q r) = (term243 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1115233 (y : nat) (x : nat) (z : nat) : (term242 y x z) = (term244 y x z).
Proof. exact (@lem1115232 (y = z) (term204 x y) (term204 x z)). Qed.
Lemma lem1115255 (y : nat) (x : nat) (z : nat) : (term197 x y z) = (term244 y x z).
Proof. exact (TRANS (@lem1115228 y x z) (@lem1115233 y x z)). Qed.
Lemma lem1115256 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1115257 (y : nat) (x : nat) (z : nat) : (term245 x y z) = (term246 y x z).
Proof. exact (MK_COMB (@lem1115256) (@lem1115255 y x z)). Qed.
Lemma lem1115279 (y : nat) (x : nat) (z : nat) : (term244 y x z) = (term244 y x z).
Proof. exact (eq_refl (term244 y x z)). Qed.
Lemma lem1115280 (y : nat) (x : nat) (z : nat) : ((term197 x y z) = (term244 y x z)) = ((term244 y x z) = (term244 y x z)).
Proof. exact (MK_COMB (@lem1115257 y x z) (@lem1115279 y x z)). Qed.
Lemma lem1115282 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1115283 (x : Prop) : (x = x) = True.
Proof. exact (@lem1115282 Prop x). Qed.
Lemma lem1115284 (y : nat) (x : nat) (z : nat) : ((term244 y x z) = (term244 y x z)) = True.
Proof. exact (@lem1115283 (term244 y x z)). Qed.
Lemma lem1115285 (y : nat) (x : nat) (z : nat) : ((term197 x y z) = (term244 y x z)) = True.
Proof. exact (TRANS (@lem1115280 y x z) (@lem1115284 y x z)). Qed.
Lemma lem1115286 (y : nat) (x : nat) (z : nat) : True = ((term197 x y z) = (term244 y x z)).
Proof. exact (SYM (@lem1115285 y x z)). Qed.
Lemma lem1115287 (y : nat) (x : nat) (z : nat) : (term197 x y z) = (term244 y x z).
Proof. exact (EQ_MP (@lem1115286 y x z) (@lem0)). Qed.
Lemma lem1115288 (y : nat) (x : nat) (z : nat) : term244 y x z.
Proof. exact (EQ_MP (@lem1115287 y x z) (@lem1115053 x y z)). Qed.
Lemma lem1115290 (b : Prop) (a : Prop) : (a \/ b) = (term202 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1115291 (x : nat) (y : nat) (z : nat) : (term244 y x z) = (term247 x y z).
Proof. exact (@lem1115290 (term248 y x z) (y = z)). Qed.
Lemma lem1115293 (a : Prop) (b : Prop) : (term205 a b) = (term206 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1115294 (y : nat) (x : nat) (z : nat) : (term249 y x z) = (term250 y x z).
Proof. exact (@lem1115293 (term204 x y) (term204 x z)). Qed.
Lemma lem1115296 (a : Prop) : (term209 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1115297 (x : nat) (y : nat) : (term223 x y) = (x = y).
Proof. exact (@lem1115296 (x = y)). Qed.
Lemma lem1115298 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1115299 (x : nat) (y : nat) : (term224 x y) = (term225 x y).
Proof. exact (MK_COMB (@lem1115298) (@lem1115297 x y)). Qed.
Lemma lem1115301 (a : Prop) : (term209 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1115302 (x : nat) (z : nat) : (term223 x z) = (x = z).
Proof. exact (@lem1115301 (x = z)). Qed.
Lemma lem1115303 (y : nat) (x : nat) (z : nat) : (term250 y x z) = (term251 y x z).
Proof. exact (MK_COMB (@lem1115299 x y) (@lem1115302 x z)). Qed.
Lemma lem1115304 (y : nat) (x : nat) (z : nat) : (term249 y x z) = (term251 y x z).
Proof. exact (TRANS (@lem1115294 y x z) (@lem1115303 y x z)). Qed.
Lemma lem1115305 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1115306 (y : nat) (x : nat) (z : nat) : (term252 y x z) = (term253 y x z).
Proof. exact (MK_COMB (@lem1115305) (@lem1115304 y x z)). Qed.
Lemma lem1115307 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1115308 (x : nat) (y : nat) (z : nat) : (term247 x y z) = (term254 x y z).
Proof. exact (MK_COMB (@lem1115306 y x z) (@lem1115307 y z)). Qed.
Lemma lem1115309 (x : nat) (y : nat) (z : nat) : (term244 y x z) = (term254 x y z).
Proof. exact (TRANS (@lem1115291 x y z) (@lem1115308 x y z)). Qed.
Lemma lem1115311 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term180 n) (h2 : term41 P n') (h3 : term118 n' P) : term255 n n'.
Proof. exact (conj (@lem1115190 n n' P h1 h2 h3) (@lem1115198 n')). Qed.
Lemma lem1115313 (x : nat) (y : nat) (z : nat) : term254 x y z.
Proof. exact (EQ_MP (@lem1115309 x y z) (@lem1115288 y x z)). Qed.
Lemma lem1115314 (n : nat -> nat) (n' : nat) : term256 n n'.
Proof. exact (@lem1115313 n' (term235 n n') n'). Qed.
Lemma lem1115317 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term180 n) (h2 : term41 P n') (h3 : term118 n' P) : (term235 n n') = n'.
Proof. exact (@lem1115314 n n' (@lem1115311 n n' P h1 h2 h3)). Qed.
Lemma lem1115318 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term180 n) (h2 : term41 P n') (h3 : term118 n' P) : term257 n n'.
Proof. exact (fun h0 : term258 n n' => @lem1115317 n n' P h1 h2 h3). Qed.
Lemma lem1115320 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1115321 (n : nat -> nat) (n' : nat) : (term257 n n') = ((term235 n n') = n').
Proof. exact (@lem1115320 ((term235 n n') = n')). Qed.
Lemma lem1115322 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term180 n) (h2 : term41 P n') (h3 : term118 n' P) : (term235 n n') = n'.
Proof. exact (EQ_MP (@lem1115321 n n') (@lem1115318 n n' P h1 h2 h3)). Qed.
Lemma lem1115324 (_18118 : nat) (n' : nat) (P : nat -> Prop) (h1 : term118 n' P) : term29 P _18118.
Proof. exact (EQ_MP (@lem1114858 P _18118) (@lem1114857 _18118 n' P h1)). Qed.
Lemma lem1115325 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term118 n' P) : term259 P n n'.
Proof. exact (@lem1115324 (n n') n' P h1). Qed.
Lemma lem1115326 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term118 n' P) : term260 P n n'.
Proof. exact (fun h0 : term261 P n n' => @lem1115325 n n' P h1). Qed.
Lemma lem1115328 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1115329 (P : nat -> Prop) (n : nat -> nat) (n' : nat) : (term260 P n n') = (term259 P n n').
Proof. exact (@lem1115328 (term259 P n n')). Qed.
Lemma lem1115330 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term118 n' P) : term259 P n n'.
Proof. exact (EQ_MP (@lem1115329 P n n') (@lem1115326 n n' P h1)). Qed.
Lemma lem1115336 (q : Prop) (p : Prop) (r : Prop) : (term243 p q r) = (term243 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1115337 (_18136 : nat) (P : nat -> Prop) (_18135 : nat) : (term196 _18136 P _18135) = (term262 _18136 P _18135).
Proof. exact (@lem1115336 (P _18136) (term204 _18135 _18136) (term41 P _18135)). Qed.
Lemma lem1115351 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1115352 (P : nat -> Prop) (_18135 : nat) (_18136 : nat) : (term263 _18136 P _18135) = (term264 P _18135 _18136).
Proof. exact (@lem1115351 (term41 P _18135) (term204 _18135 _18136)). Qed.
Lemma lem1115360 (P : nat -> Prop) (_18136 : nat) : (term265 P _18136) = (term265 P _18136).
Proof. exact (eq_refl (term265 P _18136)). Qed.
Lemma lem1115361 (P : nat -> Prop) (_18135 : nat) (_18136 : nat) : (term262 _18136 P _18135) = (term266 P _18135 _18136).
Proof. exact (MK_COMB (@lem1115360 P _18136) (@lem1115352 P _18135 _18136)). Qed.
Lemma lem1115372 (P : nat -> Prop) (_18135 : nat) (_18136 : nat) : (term196 _18136 P _18135) = (term266 P _18135 _18136).
Proof. exact (TRANS (@lem1115337 _18136 P _18135) (@lem1115361 P _18135 _18136)). Qed.
Lemma lem1115373 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1115374 (P : nat -> Prop) (_18135 : nat) (_18136 : nat) : (term267 _18136 P _18135) = (term268 P _18135 _18136).
Proof. exact (MK_COMB (@lem1115373) (@lem1115372 P _18135 _18136)). Qed.
Lemma lem1115388 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1115389 (P : nat -> Prop) (_18135 : nat) (_18136 : nat) : (term263 _18136 P _18135) = (term264 P _18135 _18136).
Proof. exact (@lem1115388 (term41 P _18135) (term204 _18135 _18136)). Qed.
Lemma lem1115397 (P : nat -> Prop) (_18136 : nat) : (term265 P _18136) = (term265 P _18136).
Proof. exact (eq_refl (term265 P _18136)). Qed.
Lemma lem1115398 (P : nat -> Prop) (_18135 : nat) (_18136 : nat) : (term262 _18136 P _18135) = (term266 P _18135 _18136).
Proof. exact (MK_COMB (@lem1115397 P _18136) (@lem1115389 P _18135 _18136)). Qed.
Lemma lem1115409 (P : nat -> Prop) (_18135 : nat) (_18136 : nat) : ((term196 _18136 P _18135) = (term262 _18136 P _18135)) = ((term266 P _18135 _18136) = (term266 P _18135 _18136)).
Proof. exact (MK_COMB (@lem1115374 P _18135 _18136) (@lem1115398 P _18135 _18136)). Qed.
Lemma lem1115411 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1115412 (x : Prop) : (x = x) = True.
Proof. exact (@lem1115411 Prop x). Qed.
Lemma lem1115413 (P : nat -> Prop) (_18135 : nat) (_18136 : nat) : ((term266 P _18135 _18136) = (term266 P _18135 _18136)) = True.
Proof. exact (@lem1115412 (term266 P _18135 _18136)). Qed.
Lemma lem1115414 (_18136 : nat) (P : nat -> Prop) (_18135 : nat) : ((term196 _18136 P _18135) = (term262 _18136 P _18135)) = True.
Proof. exact (TRANS (@lem1115409 P _18135 _18136) (@lem1115413 P _18135 _18136)). Qed.
Lemma lem1115415 (_18136 : nat) (P : nat -> Prop) (_18135 : nat) : True = ((term196 _18136 P _18135) = (term262 _18136 P _18135)).
Proof. exact (SYM (@lem1115414 _18136 P _18135)). Qed.
Lemma lem1115416 (_18136 : nat) (P : nat -> Prop) (_18135 : nat) : (term196 _18136 P _18135) = (term262 _18136 P _18135).
Proof. exact (EQ_MP (@lem1115415 _18136 P _18135) (@lem0)). Qed.
Lemma lem1115417 (_18136 : nat) (P : nat -> Prop) (_18135 : nat) : term262 _18136 P _18135.
Proof. exact (EQ_MP (@lem1115416 _18136 P _18135) (@lem1115027 _18136 P _18135)). Qed.
Lemma lem1115419 (b : Prop) (a : Prop) : (a \/ b) = (term202 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1115420 (_18135 : nat) (P : nat -> Prop) (_18136 : nat) : (term262 _18136 P _18135) = (term269 _18135 P _18136).
Proof. exact (@lem1115419 (term263 _18136 P _18135) (P _18136)). Qed.
Lemma lem1115422 (a : Prop) (b : Prop) : (term205 a b) = (term206 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1115423 (_18136 : nat) (P : nat -> Prop) (_18135 : nat) : (term270 _18136 P _18135) = (term271 _18136 P _18135).
Proof. exact (@lem1115422 (term204 _18135 _18136) (term41 P _18135)). Qed.
Lemma lem1115425 (a : Prop) : (term209 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1115426 (_18135 : nat) (_18136 : nat) : (term223 _18135 _18136) = (_18135 = _18136).
Proof. exact (@lem1115425 (_18135 = _18136)). Qed.
Lemma lem1115427 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1115428 (_18135 : nat) (_18136 : nat) : (term224 _18135 _18136) = (term225 _18135 _18136).
Proof. exact (MK_COMB (@lem1115427) (@lem1115426 _18135 _18136)). Qed.
Lemma lem1115430 (a : Prop) : (term209 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1115431 (P : nat -> Prop) (_18135 : nat) : (term210 P _18135) = (P _18135).
Proof. exact (@lem1115430 (P _18135)). Qed.
Lemma lem1115432 (_18136 : nat) (P : nat -> Prop) (_18135 : nat) : (term271 _18136 P _18135) = (term272 _18136 P _18135).
Proof. exact (MK_COMB (@lem1115428 _18135 _18136) (@lem1115431 P _18135)). Qed.
Lemma lem1115433 (_18136 : nat) (P : nat -> Prop) (_18135 : nat) : (term270 _18136 P _18135) = (term272 _18136 P _18135).
Proof. exact (TRANS (@lem1115423 _18136 P _18135) (@lem1115432 _18136 P _18135)). Qed.
Lemma lem1115434 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1115435 (_18136 : nat) (P : nat -> Prop) (_18135 : nat) : (term273 _18136 P _18135) = (term274 _18136 P _18135).
Proof. exact (MK_COMB (@lem1115434) (@lem1115433 _18136 P _18135)). Qed.
Lemma lem1115436 (P : nat -> Prop) (_18136 : nat) : (P _18136) = (P _18136).
Proof. exact (eq_refl (P _18136)). Qed.
Lemma lem1115437 (_18135 : nat) (P : nat -> Prop) (_18136 : nat) : (term269 _18135 P _18136) = (term275 _18135 P _18136).
Proof. exact (MK_COMB (@lem1115435 _18136 P _18135) (@lem1115436 P _18136)). Qed.
Lemma lem1115438 (_18135 : nat) (P : nat -> Prop) (_18136 : nat) : (term262 _18136 P _18135) = (term275 _18135 P _18136).
Proof. exact (TRANS (@lem1115420 _18135 P _18136) (@lem1115437 _18135 P _18136)). Qed.
Lemma lem1115440 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term180 n) (h2 : term41 P n') (h3 : term118 n' P) : term276 P n n'.
Proof. exact (conj (@lem1115322 n n' P h1 h2 h3) (@lem1115330 n n' P h3)). Qed.
Lemma lem1115442 (_18135 : nat) (P : nat -> Prop) (_18136 : nat) : term275 _18135 P _18136.
Proof. exact (EQ_MP (@lem1115438 _18135 P _18136) (@lem1115417 _18136 P _18135)). Qed.
Lemma lem1115443 (n : nat -> nat) (P : nat -> Prop) (n' : nat) : term277 n P n'.
Proof. exact (@lem1115442 (term235 n n') P n'). Qed.
Lemma lem1115446 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term180 n) (h2 : term41 P n') (h3 : term118 n' P) : P n'.
Proof. exact (@lem1115443 n P n' (@lem1115440 n n' P h1 h2 h3)). Qed.
Lemma lem1115447 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term180 n) (h2 : term118 n' P) : term278 P n'.
Proof. exact (fun h0 : term41 P n' => @lem1115446 n n' P h1 h0 h2). Qed.
Lemma lem1115449 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1115450 (P : nat -> Prop) (n' : nat) : (term278 P n') = (P n').
Proof. exact (@lem1115449 (P n')). Qed.
Lemma lem1115451 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term180 n) (h2 : term118 n' P) : P n'.
Proof. exact (EQ_MP (@lem1115450 P n') (@lem1115447 n n' P h1 h2)). Qed.
Lemma lem1115454 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1115456 (P : nat -> Prop) (n' : nat) : (term41 P n') = (term279 P n').
Proof. exact (@lem1115454 (P n')). Qed.
Lemma lem1115459 (n' : nat) (P : nat -> Prop) (h1 : term118 n' P) : term279 P n'.
Proof. exact (EQ_MP (@lem1115456 P n') (@lem1114887 n' P h1)). Qed.
Lemma lem1115462 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term180 n) (h2 : term118 n' P) : False.
Proof. exact (@lem1115459 n' P h2 (@lem1115451 n n' P h1 h2)). Qed.
Lemma lem1115463 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term180 n) (h2 : term118 n' P) : term188.
Proof. exact (fun h0 : ~ False => @lem1115462 n n' P h1 h2). Qed.
Lemma lem1115465 (p : Prop) : (term186 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1115466 : term188 = False.
Proof. exact (@lem1115465 False). Qed.
Lemma lem1115467 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term180 n) (h2 : term118 n' P) : False.
Proof. exact (EQ_MP (@lem1115466) (@lem1115463 n n' P h1 h2)). Qed.
Lemma lem1115468 (P : nat -> Prop) (n' : nat) (h1 : term48 P n') (h2 : term98 P n') : (term48 P n') = False.
Proof. exact (prop_ext (fun h3 : term48 P n' => @lem1115015 P n' h1 h2) (fun h3 : False => @lem1114879 P n' h1)). Qed.
Lemma lem1115469 (P : nat -> Prop) (n' : nat) (h1 : term48 P n') (h2 : term98 P n') : False.
Proof. exact (EQ_MP (@lem1115468 P n' h1 h2) (@lem1114879 P n' h1)). Qed.
Lemma lem1115470 (P : nat -> Prop) (n' : nat) (h1 : term74 P) (h2 : term98 P n') : (term74 P) = False.
Proof. exact (prop_ext (fun h3 : term74 P => @lem1114953 P n' h1 h2) (fun h3 : False => @lem1114869 P h1)). Qed.
Lemma lem1115471 (P : nat -> Prop) (n' : nat) (h1 : term74 P) (h2 : term98 P n') : False.
Proof. exact (EQ_MP (@lem1115470 P n' h1 h2) (@lem1114869 P h1)). Qed.
Lemma lem1115472 (P : nat -> Prop) (n' : nat) (h1 : term48 P n') (h2 : term98 P n') : (term48 P n') = False.
Proof. exact (prop_ext (fun h3 : term48 P n' => @lem1115469 P n' h1 h2) (fun h3 : False => @lem1114813 P n' h1)). Qed.
Lemma lem1115473 (P : nat -> Prop) (n' : nat) (h1 : term48 P n') (h2 : term98 P n') : False.
Proof. exact (EQ_MP (@lem1115472 P n' h1 h2) (@lem1114813 P n' h1)). Qed.
Lemma lem1115474 (P : nat -> Prop) (n' : nat) (h1 : term74 P) (h2 : term98 P n') : (term74 P) = False.
Proof. exact (prop_ext (fun h3 : term74 P => @lem1115471 P n' h1 h2) (fun h3 : False => @lem1114789 P h1)). Qed.
Lemma lem1115475 (P : nat -> Prop) (n' : nat) (h1 : term74 P) (h2 : term98 P n') : False.
Proof. exact (EQ_MP (@lem1115474 P n' h1 h2) (@lem1114789 P h1)). Qed.
Lemma lem1115476 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term180 n) (h2 : term118 n' P) : (term180 n) = False.
Proof. exact (prop_ext (fun h3 : term180 n => @lem1115467 n n' P h1 h2) (fun h3 : False => @lem1114826 n h1)). Qed.
Lemma lem1115477 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term180 n) (h2 : term118 n' P) : False.
Proof. exact (EQ_MP (@lem1115476 n n' P h1 h2) (@lem1114826 n h1)). Qed.
Lemma lem1115478 (P : nat -> Prop) (n' : nat) (h1 : term48 P n') (h2 : term98 P n') : (term48 P n') = False.
Proof. exact (prop_ext (fun h3 : term48 P n' => @lem1115473 P n' h1 h2) (fun h3 : False => @lem1114813 P n' h1)). Qed.
Lemma lem1115479 (P : nat -> Prop) (n' : nat) (h1 : term48 P n') (h2 : term98 P n') : False.
Proof. exact (EQ_MP (@lem1115478 P n' h1 h2) (@lem1114813 P n' h1)). Qed.
Lemma lem1115480 (P : nat -> Prop) (n' : nat) (h1 : term74 P) (h2 : term98 P n') : (term74 P) = False.
Proof. exact (prop_ext (fun h3 : term74 P => @lem1115475 P n' h1 h2) (fun h3 : False => @lem1114789 P h1)). Qed.
Lemma lem1115481 (P : nat -> Prop) (n' : nat) (h1 : term74 P) (h2 : term98 P n') : False.
Proof. exact (EQ_MP (@lem1115480 P n' h1 h2) (@lem1114789 P h1)). Qed.
Lemma lem1115482 (P : nat -> Prop) (n' : nat) (h1 : term98 P n') : False.
Proof. exact (or_elim (@lem1114758 P n' h1) (fun h0 : term74 P => @lem1115481 P n' h0 h1) (fun h0 : term48 P n' => @lem1115479 P n' h0 h1)). Qed.
Lemma lem1115483 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term180 n) (h2 : term141 n' P) : False.
Proof. exact (or_elim (@lem1114755 n' P h2) (fun h0 : term98 P n' => @lem1115482 P n' h0) (fun h0 : term118 n' P => @lem1115477 n n' P h1 h0)). Qed.
Lemma lem1115484 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term180 n) (h2 : term141 n' P) : (term141 n' P) = False.
Proof. exact (prop_ext (fun h3 : term141 n' P => @lem1115483 n n' P h1 h2) (fun h3 : False => @lem1114755 n' P h2)). Qed.
Lemma lem1115485 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term180 n) (h2 : term141 n' P) : False.
Proof. exact (EQ_MP (@lem1115484 n n' P h1 h2) (@lem1114755 n' P h2)). Qed.
Lemma lem1115486 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term180 n) (h2 : term141 n' P) : (term180 n) = False.
Proof. exact (prop_ext (fun h3 : term180 n => @lem1115485 n n' P h1 h2) (fun h3 : False => @lem1114701 n h1)). Qed.
Lemma lem1115487 (n : nat -> nat) (n' : nat) (P : nat -> Prop) (h1 : term180 n) (h2 : term141 n' P) : False.
Proof. exact (EQ_MP (@lem1115486 n n' P h1 h2) (@lem1114701 n h1)). Qed.
Lemma lem1115488 (n : nat -> nat) (P : nat -> Prop) (h1 : term180 n) (h2 : term10 P) : False.
Proof. exact (ex_elim (@lem1114555 P h2) (fun n' : nat => fun h0 : term143 P n' => @lem1115487 n n' P h1 h0)). Qed.
Lemma lem1115489 (P : nat -> Prop) (h1 : term17) (h2 : term10 P) : False.
Proof. exact (ex_elim (@lem1114676 h1) (fun n : nat -> nat => fun h0 : term182 n => @lem1115488 n P h0 h2)). Qed.
Lemma lem1115490 (P : nat -> Prop) (h1 : term10 P) : term15.
Proof. exact (fun h0 : term17 => @lem1115489 P h0 h1). Qed.
Lemma lem1115491 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem1115492 (P : nat -> Prop) (h1 : term10 P) : term16.
Proof. exact (EQ_MP (@lem1115491) (@lem1115490 P h1)). Qed.
Lemma lem1115493 (P : nat -> Prop) : term19 P.
Proof. exact (fun h0 : term10 P => @lem1115492 P h0). Qed.
Lemma lem1115498 : term23.
Proof. exact (fun P : nat -> Prop => @lem1115493 P). Qed.
Lemma lem1115499 : term22.
Proof. exact (EQ_MP (@lem1114384) (@lem1115498)). Qed.
Lemma lem1115500 (P : nat -> Prop) : term280 P.
Proof. exact (@lem1115499 P). Qed.
Lemma lem1115501 (P : nat -> Prop) : (term280 P) = (term11 P).
Proof. exact (eq_refl (term280 P)). Qed.
Lemma lem1115502 (P : nat -> Prop) : term11 P.
Proof. exact (EQ_MP (@lem1115501 P) (@lem1115500 P)). Qed.
Lemma lem1115504 (P : nat -> Prop) : term11 P.
Proof. exact (@lem1114220 P (@lem1115502 P)). Qed.
Lemma lem1115505 (P : nat -> Prop) (h1 : term10 P) : term15.
Proof. exact (@lem1115504 P (@lem1114205 P h1)). Qed.
Lemma lem1115506 (P : nat -> Prop) (h1 : term10 P) : False.
Proof. exact (@lem1115505 P h1 (@lem76132)). Qed.
Lemma lem1115507 (P : nat -> Prop) (h1 : term10 P) : (term10 P) = False.
Proof. exact (prop_ext (fun h2 : term10 P => @lem1115506 P h1) (fun h2 : False => @lem1114205 P h1)). Qed.
Lemma lem1115508 (P : nat -> Prop) (h1 : term10 P) : False.
Proof. exact (EQ_MP (@lem1115507 P h1) (@lem1114205 P h1)). Qed.
Lemma lem1115509 (P : nat -> Prop) : term9 P.
Proof. exact (fun h0 : term10 P => @lem1115508 P h0). Qed.
Lemma lem1115511 : term281.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem1115512 (n : nat) : term282 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem1115513 (n : nat) : (term282 n) = (term283 n).
Proof. exact (eq_refl (term282 n)). Qed.
Lemma lem1115514 (n : nat) : term283 n.
Proof. exact (EQ_MP (@lem1115513 n) (@lem1115512 n)). Qed.
Lemma lem1115515 (n : nat) : term284 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem1115518 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (S n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem1115519 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (NUMERAL 0) = (S n).
Proof. exact (SYM (@lem1115518 n h1)). Qed.
Lemma lem1115520 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (NUMERAL 0) = (S n).
Proof. exact (h1). Qed.
Lemma lem1115521 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (S n) = (NUMERAL 0).
Proof. exact (SYM (@lem1115520 n h1)). Qed.
Lemma lem1115522 (n : nat) : ((S n) = (NUMERAL 0)) = ((NUMERAL 0) = (S n)).
Proof. exact (prop_ext (fun h1 : (S n) = (NUMERAL 0) => @lem1115519 n h1) (fun h1 : (NUMERAL 0) = (S n) => @lem1115521 n h1)). Qed.
Lemma lem1115523 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1115524 (n : nat) : (term283 n) = (term285 n).
Proof. exact (MK_COMB (@lem1115523) (@lem1115522 n)). Qed.
Lemma lem1115525 (n : nat) : term285 n.
Proof. exact (EQ_MP (@lem1115524 n) (@lem1115514 n)). Qed.
Lemma lem1115526 (n : nat) : term286 n.
Proof. exact (@lem82 ((NUMERAL 0) = (S n))). Qed.
Lemma lem1115528 (m : nat) : term287 m.
Proof. exact (@lem1115511 m). Qed.
Lemma lem1115529 (m : nat) : (term287 m) = ((term288 m) = False).
Proof. exact (eq_refl (term287 m)). Qed.
Lemma lem1115531 {A : Type'} : term289 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem1115532 {A : Type'} (h : A) : term290 A h.
Proof. exact (@lem1115531 A h). Qed.
Lemma lem1115533 {A : Type'} (h : A) : (term290 A h) = (term291 A h).
Proof. exact (eq_refl (term290 A h)). Qed.
Lemma lem1115534 {A : Type'} (h : A) : term291 A h.
Proof. exact (EQ_MP (@lem1115533 A h) (@lem1115532 A h)). Qed.
Lemma lem1115535 {A : Type'} (h : A) (t : list A) : term292 A h t.
Proof. exact (@lem1115534 A h t). Qed.
Lemma lem1115536 {A : Type'} (h : A) (t : list A) : (term292 A h t) = ((term293 A h t) = (term294 A t)).
Proof. exact (eq_refl (term292 A h t)). Qed.
Lemma lem1115539 {A : Type'} (h1' : A) : term295 A h1'.
Proof. exact (@lem1113436 A h1'). Qed.
Lemma lem1115540 {A : Type'} (h1' : A) : (term295 A h1') = (term296 A h1').
Proof. exact (eq_refl (term295 A h1')). Qed.
Lemma lem1115541 {A : Type'} (h1' : A) : term296 A h1'.
Proof. exact (EQ_MP (@lem1115540 A h1') (@lem1115539 A h1')). Qed.
Lemma lem1115542 {A : Type'} (h1' : A) (h2' : A) : term297 A h1' h2'.
Proof. exact (@lem1115541 A h1' h2'). Qed.
Lemma lem1115543 {A : Type'} (h1' : A) (h2' : A) : (term297 A h1' h2') = (term298 A h1' h2').
Proof. exact (eq_refl (term297 A h1' h2')). Qed.
Lemma lem1115544 {A : Type'} (h1' : A) (h2' : A) : term298 A h1' h2'.
Proof. exact (EQ_MP (@lem1115543 A h1' h2') (@lem1115542 A h1' h2')). Qed.
Lemma lem1115545 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : term299 A h1' h2' t1.
Proof. exact (@lem1115544 A h1' h2' t1). Qed.
Lemma lem1115546 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : (term299 A h1' h2' t1) = (term300 A h1' h2' t1).
Proof. exact (eq_refl (term299 A h1' h2' t1)). Qed.
Lemma lem1115547 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) : term300 A h1' h2' t1.
Proof. exact (EQ_MP (@lem1115546 A h1' h2' t1) (@lem1115545 A h1' h2' t1)). Qed.
Lemma lem1115548 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : term301 A h1' h2' t1 t2.
Proof. exact (@lem1115547 A h1' h2' t1 t2). Qed.
Lemma lem1115549 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : (term301 A h1' h2' t1 t2) = (((@cons A h1' t1) = (@cons A h2' t2)) = (term302 A h1' h2' t1 t2)).
Proof. exact (eq_refl (term301 A h1' h2' t1 t2)). Qed.
Lemma lem1115551 {A : Type'} (h : A) : term303 A h.
Proof. exact (@lem1111523 A h). Qed.
Lemma lem1115552 {A : Type'} (h : A) : (term303 A h) = (term304 A h).
Proof. exact (eq_refl (term303 A h)). Qed.
Lemma lem1115553 {A : Type'} (h : A) : term304 A h.
Proof. exact (EQ_MP (@lem1115552 A h) (@lem1115551 A h)). Qed.
Lemma lem1115554 {A : Type'} (h : A) (t : list A) : term305 A h t.
Proof. exact (@lem1115553 A h t). Qed.
Lemma lem1115555 {A : Type'} (h : A) (t : list A) : (term305 A h t) = (term306 A h t).
Proof. exact (eq_refl (term305 A h t)). Qed.
Lemma lem1115556 {A : Type'} (h : A) (t : list A) : term306 A h t.
Proof. exact (EQ_MP (@lem1115555 A h t) (@lem1115554 A h t)). Qed.
Lemma lem1115557 {A : Type'} (h : A) (t : list A) : term307 A h t.
Proof. exact (@lem82 ((@cons A h t) = (@nil A))). Qed.
Lemma lem1115560 {A : Type'} (h : A) (t : list A) (h1 : (@cons A h t) = (@nil A)) : (@cons A h t) = (@nil A).
Proof. exact (h1). Qed.
Lemma lem1115561 {A : Type'} (h : A) (t : list A) (h1 : (@cons A h t) = (@nil A)) : (@nil A) = (@cons A h t).
Proof. exact (SYM (@lem1115560 A h t h1)). Qed.
Lemma lem1115562 {A : Type'} (h : A) (t : list A) (h1 : (@nil A) = (@cons A h t)) : (@nil A) = (@cons A h t).
Proof. exact (h1). Qed.
Lemma lem1115563 {A : Type'} (h : A) (t : list A) (h1 : (@nil A) = (@cons A h t)) : (@cons A h t) = (@nil A).
Proof. exact (SYM (@lem1115562 A h t h1)). Qed.
Lemma lem1115564 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = ((@nil A) = (@cons A h t)).
Proof. exact (prop_ext (fun h1 : (@cons A h t) = (@nil A) => @lem1115561 A h t h1) (fun h1 : (@nil A) = (@cons A h t) => @lem1115563 A h t h1)). Qed.
Lemma lem1115565 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1115566 {A : Type'} (h : A) (t : list A) : (term306 A h t) = (term308 A h t).
Proof. exact (MK_COMB (@lem1115565) (@lem1115564 A h t)). Qed.
Lemma lem1115567 {A : Type'} (h : A) (t : list A) : term308 A h t.
Proof. exact (EQ_MP (@lem1115566 A h t) (@lem1115556 A h t)). Qed.
Lemma lem1115568 {A : Type'} (h : A) (t : list A) : term309 A h t.
Proof. exact (@lem82 ((@nil A) = (@cons A h t))). Qed.
Lemma lem1115571 {A : Type'} (P : type1143 A) : term310 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1115572 {A : Type'} (P : type1143 A) : term310 A P.
Proof. exact (@lem1115571 A P). Qed.
Lemma lem1115573 {A : Type'} : term311 A.
Proof. exact (@lem1115572 A (term312 A)). Qed.
Lemma lem1115574 {A : Type'} : (term313 A) = (term314 A).
Proof. exact (eq_refl (term313 A)). Qed.
Lemma lem1115575 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1115576 {A : Type'} : (term315 A) = (term316 A).
Proof. exact (MK_COMB (@lem1115575) (@lem1115574 A)). Qed.
Lemma lem1115577 {A : Type'} (t : list A) : (term317 A t) = (term318 A t).
Proof. exact (eq_refl (term317 A t)). Qed.
Lemma lem1115578 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1115579 {A : Type'} (t : list A) : (term319 A t) = (term320 A t).
Proof. exact (MK_COMB (@lem1115578) (@lem1115577 A t)). Qed.
Lemma lem1115580 {A : Type'} (h : A) (t : list A) : (term321 A h t) = (term322 A h t).
Proof. exact (eq_refl (term321 A h t)). Qed.
Lemma lem1115581 {A : Type'} (h : A) (t : list A) : (term323 A h t) = (term324 A h t).
Proof. exact (MK_COMB (@lem1115579 A t) (@lem1115580 A h t)). Qed.
Lemma lem1115582 {A : Type'} (h : A) : (term325 A h) = (term326 A h).
Proof. exact (fun_ext (fun t : list A => @lem1115581 A h t)). Qed.
Lemma lem1115583 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1115584 {A : Type'} (h : A) : (term327 A h) = (term328 A h).
Proof. exact (MK_COMB (@lem1115583 A) (@lem1115582 A h)). Qed.
Lemma lem1115585 {A : Type'} : (term329 A) = (term330 A).
Proof. exact (fun_ext (fun h : A => @lem1115584 A h)). Qed.
Lemma lem1115586 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1115587 {A : Type'} : (term331 A) = (term332 A).
Proof. exact (MK_COMB (@lem1115586 A) (@lem1115585 A)). Qed.
Lemma lem1115588 {A : Type'} : (term333 A) = (term334 A).
Proof. exact (MK_COMB (@lem1115576 A) (@lem1115587 A)). Qed.
Lemma lem1115589 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1115590 {A : Type'} : (term335 A) = (term336 A).
Proof. exact (MK_COMB (@lem1115589) (@lem1115588 A)). Qed.
Lemma lem1115591 {A : Type'} (l1 : list A) : (term317 A l1) = (term318 A l1).
Proof. exact (eq_refl (term317 A l1)). Qed.
Lemma lem1115592 {A : Type'} : (term337 A) = (term312 A).
Proof. exact (fun_ext (fun l1 : list A => @lem1115591 A l1)). Qed.
Lemma lem1115593 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1115594 {A : Type'} : (term338 A) = (term339 A).
Proof. exact (MK_COMB (@lem1115593 A) (@lem1115592 A)). Qed.
Lemma lem1115595 {A : Type'} : (term311 A) = (term340 A).
Proof. exact (MK_COMB (@lem1115590 A) (@lem1115594 A)). Qed.
Lemma lem1115596 {A : Type'} : term340 A.
Proof. exact (EQ_MP (@lem1115595 A) (@lem1115573 A)). Qed.
Lemma lem1115597 {A : Type'} (t : list A) (h1 : term318 A t) : term318 A t.
Proof. exact (h1). Qed.
Lemma lem1115599 {A : Type'} (P : type1143 A) : term310 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1115600 {A : Type'} (P : type1143 A) : term310 A P.
Proof. exact (@lem1115599 A P). Qed.
Lemma lem1115601 {A : Type'} : term341 A.
Proof. exact (@lem1115600 A (term342 A)). Qed.
Lemma lem1115602 {A : Type'} : (term343 A) = (((@nil A) = (@nil A)) = (term344 A)).
Proof. exact (eq_refl (term343 A)). Qed.
Lemma lem1115603 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1115604 {A : Type'} : (term345 A) = (term346 A).
Proof. exact (MK_COMB (@lem1115603) (@lem1115602 A)). Qed.
Lemma lem1115605 {A : Type'} (t : list A) : (term347 A t) = (((@nil A) = t) = (term348 A t)).
Proof. exact (eq_refl (term347 A t)). Qed.
Lemma lem1115606 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1115607 {A : Type'} (t : list A) : (term349 A t) = (term350 A t).
Proof. exact (MK_COMB (@lem1115606) (@lem1115605 A t)). Qed.
Lemma lem1115608 {A : Type'} (h : A) (t : list A) : (term351 A h t) = (((@nil A) = (@cons A h t)) = (term352 A h t)).
Proof. exact (eq_refl (term351 A h t)). Qed.
Lemma lem1115609 {A : Type'} (h : A) (t : list A) : (term353 A h t) = (term354 A h t).
Proof. exact (MK_COMB (@lem1115607 A t) (@lem1115608 A h t)). Qed.
Lemma lem1115610 {A : Type'} (h : A) : (term355 A h) = (term356 A h).
Proof. exact (fun_ext (fun t : list A => @lem1115609 A h t)). Qed.
Lemma lem1115611 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1115612 {A : Type'} (h : A) : (term357 A h) = (term358 A h).
Proof. exact (MK_COMB (@lem1115611 A) (@lem1115610 A h)). Qed.
Lemma lem1115613 {A : Type'} : (term359 A) = (term360 A).
Proof. exact (fun_ext (fun h : A => @lem1115612 A h)). Qed.
Lemma lem1115614 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1115615 {A : Type'} : (term361 A) = (term362 A).
Proof. exact (MK_COMB (@lem1115614 A) (@lem1115613 A)). Qed.
Lemma lem1115616 {A : Type'} : (term363 A) = (term364 A).
Proof. exact (MK_COMB (@lem1115604 A) (@lem1115615 A)). Qed.
Lemma lem1115617 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1115618 {A : Type'} : (term365 A) = (term366 A).
Proof. exact (MK_COMB (@lem1115617) (@lem1115616 A)). Qed.
Lemma lem1115619 {A : Type'} (l2 : list A) : (term347 A l2) = (((@nil A) = l2) = (term348 A l2)).
Proof. exact (eq_refl (term347 A l2)). Qed.
Lemma lem1115620 {A : Type'} : (term367 A) = (term342 A).
Proof. exact (fun_ext (fun l2 : list A => @lem1115619 A l2)). Qed.
Lemma lem1115621 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1115622 {A : Type'} : (term368 A) = (term314 A).
Proof. exact (MK_COMB (@lem1115621 A) (@lem1115620 A)). Qed.
Lemma lem1115623 {A : Type'} : (term341 A) = (term369 A).
Proof. exact (MK_COMB (@lem1115618 A) (@lem1115622 A)). Qed.
Lemma lem1115624 {A : Type'} : term369 A.
Proof. exact (EQ_MP (@lem1115623 A) (@lem1115601 A)). Qed.
Lemma lem1115631 {A : Type'} (P : type1143 A) : term310 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1115632 {A : Type'} (P : type1143 A) : term310 A P.
Proof. exact (@lem1115631 A P). Qed.
Lemma lem1115633 {A : Type'} (h : A) (t : list A) : term370 A h t.
Proof. exact (@lem1115632 A (term371 A h t)). Qed.
Lemma lem1115634 {A : Type'} (h : A) (t : list A) : (term372 A h t) = (((@cons A h t) = (@nil A)) = (term373 A h t)).
Proof. exact (eq_refl (term372 A h t)). Qed.
Lemma lem1115635 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1115636 {A : Type'} (h : A) (t : list A) : (term374 A h t) = (term375 A h t).
Proof. exact (MK_COMB (@lem1115635) (@lem1115634 A h t)). Qed.
Lemma lem1115637 {A : Type'} (h : A) (t : list A) (t' : list A) : (term376 A h t t') = (((@cons A h t) = t') = (term377 A h t t')).
Proof. exact (eq_refl (term376 A h t t')). Qed.
Lemma lem1115638 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1115639 {A : Type'} (h : A) (t : list A) (t' : list A) : (term378 A h t t') = (term379 A h t t').
Proof. exact (MK_COMB (@lem1115638) (@lem1115637 A h t t')). Qed.
Lemma lem1115640 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : (term380 A h t h' t') = (((@cons A h t) = (@cons A h' t')) = (term381 A h t h' t')).
Proof. exact (eq_refl (term380 A h t h' t')). Qed.
Lemma lem1115641 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : (term382 A h t h' t') = (term383 A h t h' t').
Proof. exact (MK_COMB (@lem1115639 A h t t') (@lem1115640 A h t h' t')). Qed.
Lemma lem1115642 {A : Type'} (h : A) (t : list A) (h' : A) : (term384 A h t h') = (term385 A h t h').
Proof. exact (fun_ext (fun t' : list A => @lem1115641 A h t h' t')). Qed.
Lemma lem1115643 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1115644 {A : Type'} (h : A) (t : list A) (h' : A) : (term386 A h t h') = (term387 A h t h').
Proof. exact (MK_COMB (@lem1115643 A) (@lem1115642 A h t h')). Qed.
Lemma lem1115645 {A : Type'} (h : A) (t : list A) : (term388 A h t) = (term389 A h t).
Proof. exact (fun_ext (fun h' : A => @lem1115644 A h t h')). Qed.
Lemma lem1115646 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1115647 {A : Type'} (h : A) (t : list A) : (term390 A h t) = (term391 A h t).
Proof. exact (MK_COMB (@lem1115646 A) (@lem1115645 A h t)). Qed.
Lemma lem1115648 {A : Type'} (h : A) (t : list A) : (term392 A h t) = (term393 A h t).
Proof. exact (MK_COMB (@lem1115636 A h t) (@lem1115647 A h t)). Qed.
Lemma lem1115649 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1115650 {A : Type'} (h : A) (t : list A) : (term394 A h t) = (term395 A h t).
Proof. exact (MK_COMB (@lem1115649) (@lem1115648 A h t)). Qed.
Lemma lem1115651 {A : Type'} (h : A) (t : list A) (l2 : list A) : (term376 A h t l2) = (((@cons A h t) = l2) = (term377 A h t l2)).
Proof. exact (eq_refl (term376 A h t l2)). Qed.
Lemma lem1115652 {A : Type'} (h : A) (t : list A) : (term396 A h t) = (term371 A h t).
Proof. exact (fun_ext (fun l2 : list A => @lem1115651 A h t l2)). Qed.
Lemma lem1115653 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1115654 {A : Type'} (h : A) (t : list A) : (term397 A h t) = (term322 A h t).
Proof. exact (MK_COMB (@lem1115653 A) (@lem1115652 A h t)). Qed.
Lemma lem1115655 {A : Type'} (h : A) (t : list A) : (term370 A h t) = (term398 A h t).
Proof. exact (MK_COMB (@lem1115650 A h t) (@lem1115654 A h t)). Qed.
Lemma lem1115656 {A : Type'} (h : A) (t : list A) : term398 A h t.
Proof. exact (EQ_MP (@lem1115655 A h t) (@lem1115633 A h t)). Qed.
Lemma lem1115665 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1115666 {A : Type'} (x : list A) : (x = x) = True.
Proof. exact (@lem1115665 (list A) x). Qed.
Lemma lem1115667 {A : Type'} : ((@nil A) = (@nil A)) = True.
Proof. exact (@lem1115666 A (@nil A)). Qed.
Lemma lem1115668 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1115669 {A : Type'} : (term399 A) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1115668) (@lem1115667 A)). Qed.
Lemma lem1115673 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1115674 (x : nat) : (x = x) = True.
Proof. exact (@lem1115673 nat x). Qed.
Lemma lem1115675 {A : Type'} : ((@List.length A (@nil A)) = (@List.length A (@nil A))) = True.
Proof. exact (@lem1115674 (@List.length A (@nil A))). Qed.
Lemma lem1115676 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1115677 {A : Type'} : (term400 A) = (and True).
Proof. exact (MK_COMB (@lem1115676) (@lem1115675 A)). Qed.
Lemma lem1115685 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1115686 (n : nat) : (Peano.lt n) = (Peano.lt n).
Proof. exact (eq_refl (Peano.lt n)). Qed.
Lemma lem1115687 {A : Type'} (n : nat) : (term401 A n) = (term288 n).
Proof. exact (MK_COMB (@lem1115686 n) (@lem1115685 A)). Qed.
Lemma lem1115689 (m : nat) : (term288 m) = False.
Proof. exact (EQ_MP (@lem1115529 m) (@lem1115528 m)). Qed.
Lemma lem1115690 (n : nat) : (term288 n) = False.
Proof. exact (@lem1115689 n). Qed.
Lemma lem1115691 {A : Type'} (n : nat) : (term401 A n) = False.
Proof. exact (TRANS (@lem1115687 A n) (@lem1115690 n)). Qed.
Lemma lem1115692 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1115693 {A : Type'} (n : nat) : (term402 A n) = (imp False).
Proof. exact (MK_COMB (@lem1115692) (@lem1115691 A n)). Qed.
Lemma lem1115695 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1115696 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1115695 A x). Qed.
Lemma lem1115697 {A : Type'} (n : nat) : ((@EL A n (@nil A)) = (@EL A n (@nil A))) = True.
Proof. exact (@lem1115696 A (@EL A n (@nil A))). Qed.
Lemma lem1115698 {A : Type'} (n : nat) : (term403 A n) = (False -> True).
Proof. exact (MK_COMB (@lem1115693 A n) (@lem1115697 A n)). Qed.
Lemma lem1115700 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1115701 : (False -> True) = True.
Proof. exact (@lem1115700 True). Qed.
Lemma lem1115702 {A : Type'} (n : nat) : (term403 A n) = True.
Proof. exact (TRANS (@lem1115698 A n) (@lem1115701)). Qed.
Lemma lem1115703 {A : Type'} : (term404 A) = term405.
Proof. exact (fun_ext (fun n : nat => @lem1115702 A n)). Qed.
Lemma lem1115704 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1115705 {A : Type'} : (term406 A) = term407.
Proof. exact (MK_COMB (@lem1115704) (@lem1115703 A)). Qed.
Lemma lem1115707 {A : Type'} (t : Prop) : (term408 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1115708 (t : Prop) : (term409 t) = t.
Proof. exact (@lem1115707 nat t). Qed.
Lemma lem1115709 : term407 = True.
Proof. exact (@lem1115708 True). Qed.
Lemma lem1115710 {A : Type'} : (term406 A) = True.
Proof. exact (TRANS (@lem1115705 A) (@lem1115709)). Qed.
Lemma lem1115711 {A : Type'} : (term344 A) = (True /\ True).
Proof. exact (MK_COMB (@lem1115677 A) (@lem1115710 A)). Qed.
Lemma lem1115713 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1115714 : (True /\ True) = True.
Proof. exact (@lem1115713 True). Qed.
Lemma lem1115715 {A : Type'} : (term344 A) = True.
Proof. exact (TRANS (@lem1115711 A) (@lem1115714)). Qed.
Lemma lem1115716 {A : Type'} : (((@nil A) = (@nil A)) = (term344 A)) = (True = True).
Proof. exact (MK_COMB (@lem1115669 A) (@lem1115715 A)). Qed.
Lemma lem1115718 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1115719 : (True = True) = True.
Proof. exact (@lem1115718 True). Qed.
Lemma lem1115720 {A : Type'} : (((@nil A) = (@nil A)) = (term344 A)) = True.
Proof. exact (TRANS (@lem1115716 A) (@lem1115719)). Qed.
Lemma lem1115721 {A : Type'} : True = (((@nil A) = (@nil A)) = (term344 A)).
Proof. exact (SYM (@lem1115720 A)). Qed.
Lemma lem1115722 {A : Type'} : ((@nil A) = (@nil A)) = (term344 A).
Proof. exact (EQ_MP (@lem1115721 A) (@lem0)). Qed.
Lemma lem1115726 {A : Type'} (h : A) (t : list A) : ((@nil A) = (@cons A h t)) = False.
Proof. exact (@lem1115568 A h t (@lem1115567 A h t)). Qed.
Lemma lem1115727 {A : Type'} (h : A) (t : list A) : ((@nil A) = (@cons A h t)) = False.
Proof. exact (@lem1115726 A h t). Qed.
Lemma lem1115728 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1115729 {A : Type'} (h : A) (t : list A) : (term410 A h t) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1115728) (@lem1115727 A h t)). Qed.
Lemma lem1115735 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1115736 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1115737 {A : Type'} : (term411 A) = term412.
Proof. exact (MK_COMB (@lem1115736) (@lem1115735 A)). Qed.
Lemma lem1115739 {A : Type'} (h : A) (t : list A) : (term293 A h t) = (term294 A t).
Proof. exact (EQ_MP (@lem1115536 A h t) (@lem1115535 A h t)). Qed.
Lemma lem1115740 {A : Type'} (h : A) (t : list A) : (term293 A h t) = (term294 A t).
Proof. exact (@lem1115739 A h t). Qed.
Lemma lem1115741 {A : Type'} (h : A) (t : list A) : ((@List.length A (@nil A)) = (term293 A h t)) = ((NUMERAL 0) = (term294 A t)).
Proof. exact (MK_COMB (@lem1115737 A) (@lem1115740 A h t)). Qed.
Lemma lem1115743 (n : nat) : ((NUMERAL 0) = (S n)) = False.
Proof. exact (@lem1115526 n (@lem1115525 n)). Qed.
Lemma lem1115744 {A : Type'} (t : list A) : ((NUMERAL 0) = (term294 A t)) = False.
Proof. exact (@lem1115743 (@List.length A t)). Qed.
Lemma lem1115745 {A : Type'} (h : A) (t : list A) : ((@List.length A (@nil A)) = (term293 A h t)) = False.
Proof. exact (TRANS (@lem1115741 A h t) (@lem1115744 A t)). Qed.
Lemma lem1115746 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1115747 {A : Type'} (h : A) (t : list A) : (term413 A h t) = (and False).
Proof. exact (MK_COMB (@lem1115746) (@lem1115745 A h t)). Qed.
Lemma lem1115755 {A : Type'} (h : A) (t : list A) : (term293 A h t) = (term294 A t).
Proof. exact (EQ_MP (@lem1115536 A h t) (@lem1115535 A h t)). Qed.
Lemma lem1115756 {A : Type'} (h : A) (t : list A) : (term293 A h t) = (term294 A t).
Proof. exact (@lem1115755 A h t). Qed.
Lemma lem1115757 (n : nat) : (Peano.lt n) = (Peano.lt n).
Proof. exact (eq_refl (Peano.lt n)). Qed.
Lemma lem1115758 {A : Type'} (h : A) (n : nat) (t : list A) : (term414 A n h t) = (term415 A n t).
Proof. exact (MK_COMB (@lem1115757 n) (@lem1115756 A h t)). Qed.
Lemma lem1115759 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1115760 {A : Type'} (h : A) (n : nat) (t : list A) : (term416 A n h t) = (term417 A n t).
Proof. exact (MK_COMB (@lem1115759) (@lem1115758 A h n t)). Qed.
Lemma lem1115763 {A : Type'} (n : nat) (h : A) (t : list A) : ((@EL A n (@nil A)) = (term418 A n h t)) = ((@EL A n (@nil A)) = (term418 A n h t)).
Proof. exact (eq_refl ((@EL A n (@nil A)) = (term418 A n h t))). Qed.
Lemma lem1115764 {A : Type'} (n : nat) (h : A) (t : list A) : (term419 A n h t) = (term420 A n h t).
Proof. exact (MK_COMB (@lem1115760 A h n t) (@lem1115763 A n h t)). Qed.
Lemma lem1115767 {A : Type'} (h : A) (t : list A) : (term421 A h t) = (term422 A h t).
Proof. exact (fun_ext (fun n : nat => @lem1115764 A n h t)). Qed.
Lemma lem1115768 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1115769 {A : Type'} (h : A) (t : list A) : (term423 A h t) = (term424 A h t).
Proof. exact (MK_COMB (@lem1115768) (@lem1115767 A h t)). Qed.
Lemma lem1115774 {A : Type'} (h : A) (t : list A) : (term352 A h t) = (term425 A h t).
Proof. exact (MK_COMB (@lem1115747 A h t) (@lem1115769 A h t)). Qed.
Lemma lem1115776 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1115777 {A : Type'} (h : A) (t : list A) : (term425 A h t) = False.
Proof. exact (@lem1115776 (term424 A h t)). Qed.
Lemma lem1115778 {A : Type'} (h : A) (t : list A) : (term352 A h t) = False.
Proof. exact (TRANS (@lem1115774 A h t) (@lem1115777 A h t)). Qed.
Lemma lem1115779 {A : Type'} (h : A) (t : list A) : (((@nil A) = (@cons A h t)) = (term352 A h t)) = (False = False).
Proof. exact (MK_COMB (@lem1115729 A h t) (@lem1115778 A h t)). Qed.
Lemma lem1115781 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1115782 : (False = False) = (~ False).
Proof. exact (@lem1115781 False). Qed.
Lemma lem1115784 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1115785 : (False = False) = True.
Proof. exact (TRANS (@lem1115782) (@lem1115784)). Qed.
Lemma lem1115786 {A : Type'} (h : A) (t : list A) : (((@nil A) = (@cons A h t)) = (term352 A h t)) = True.
Proof. exact (TRANS (@lem1115779 A h t) (@lem1115785)). Qed.
Lemma lem1115787 {A : Type'} (h : A) (t : list A) : True = (((@nil A) = (@cons A h t)) = (term352 A h t)).
Proof. exact (SYM (@lem1115786 A h t)). Qed.
Lemma lem1115788 {A : Type'} (h : A) (t : list A) : ((@nil A) = (@cons A h t)) = (term352 A h t).
Proof. exact (EQ_MP (@lem1115787 A h t) (@lem0)). Qed.
Lemma lem1115792 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = False.
Proof. exact (@lem1115557 A h t (@lem1115556 A h t)). Qed.
Lemma lem1115793 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = False.
Proof. exact (@lem1115792 A h t). Qed.
Lemma lem1115794 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1115795 {A : Type'} (h : A) (t : list A) : (term426 A h t) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1115794) (@lem1115793 A h t)). Qed.
Lemma lem1115801 {A : Type'} (h : A) (t : list A) : (term293 A h t) = (term294 A t).
Proof. exact (EQ_MP (@lem1115536 A h t) (@lem1115535 A h t)). Qed.
Lemma lem1115802 {A : Type'} (h : A) (t : list A) : (term293 A h t) = (term294 A t).
Proof. exact (@lem1115801 A h t). Qed.
Lemma lem1115803 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1115804 {A : Type'} (h : A) (t : list A) : (term427 A h t) = (term428 A t).
Proof. exact (MK_COMB (@lem1115803) (@lem1115802 A h t)). Qed.
Lemma lem1115806 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1115807 {A : Type'} (h : A) (t : list A) : ((term293 A h t) = (@List.length A (@nil A))) = ((term294 A t) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1115804 A h t) (@lem1115806 A)). Qed.
Lemma lem1115809 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem1115515 n (@lem1115514 n)). Qed.
Lemma lem1115810 {A : Type'} (t : list A) : ((term294 A t) = (NUMERAL 0)) = False.
Proof. exact (@lem1115809 (@List.length A t)). Qed.
Lemma lem1115811 {A : Type'} (h : A) (t : list A) : ((term293 A h t) = (@List.length A (@nil A))) = False.
Proof. exact (TRANS (@lem1115807 A h t) (@lem1115810 A t)). Qed.
Lemma lem1115812 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1115813 {A : Type'} (h : A) (t : list A) : (term429 A h t) = (and False).
Proof. exact (MK_COMB (@lem1115812) (@lem1115811 A h t)). Qed.
Lemma lem1115821 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem1115822 (n : nat) : (Peano.lt n) = (Peano.lt n).
Proof. exact (eq_refl (Peano.lt n)). Qed.
Lemma lem1115823 {A : Type'} (n : nat) : (term401 A n) = (term288 n).
Proof. exact (MK_COMB (@lem1115822 n) (@lem1115821 A)). Qed.
Lemma lem1115825 (m : nat) : (term288 m) = False.
Proof. exact (EQ_MP (@lem1115529 m) (@lem1115528 m)). Qed.
Lemma lem1115826 (n : nat) : (term288 n) = False.
Proof. exact (@lem1115825 n). Qed.
Lemma lem1115827 {A : Type'} (n : nat) : (term401 A n) = False.
Proof. exact (TRANS (@lem1115823 A n) (@lem1115826 n)). Qed.
Lemma lem1115828 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1115829 {A : Type'} (n : nat) : (term402 A n) = (imp False).
Proof. exact (MK_COMB (@lem1115828) (@lem1115827 A n)). Qed.
Lemma lem1115832 {A : Type'} (h : A) (t : list A) (n : nat) : ((term418 A n h t) = (@EL A n (@nil A))) = ((term418 A n h t) = (@EL A n (@nil A))).
Proof. exact (eq_refl ((term418 A n h t) = (@EL A n (@nil A)))). Qed.
Lemma lem1115833 {A : Type'} (h : A) (t : list A) (n : nat) : (term430 A h t n) = (term431 A h t n).
Proof. exact (MK_COMB (@lem1115829 A n) (@lem1115832 A h t n)). Qed.
Lemma lem1115835 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1115836 {A : Type'} (h : A) (t : list A) (n : nat) : (term431 A h t n) = True.
Proof. exact (@lem1115835 ((term418 A n h t) = (@EL A n (@nil A)))). Qed.
Lemma lem1115837 {A : Type'} (h : A) (t : list A) (n : nat) : (term430 A h t n) = True.
Proof. exact (TRANS (@lem1115833 A h t n) (@lem1115836 A h t n)). Qed.
Lemma lem1115838 {A : Type'} (h : A) (t : list A) : (term432 A h t) = term405.
Proof. exact (fun_ext (fun n : nat => @lem1115837 A h t n)). Qed.
Lemma lem1115839 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1115840 {A : Type'} (h : A) (t : list A) : (term433 A h t) = term407.
Proof. exact (MK_COMB (@lem1115839) (@lem1115838 A h t)). Qed.
Lemma lem1115842 {A : Type'} (t : Prop) : (term408 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1115843 (t : Prop) : (term409 t) = t.
Proof. exact (@lem1115842 nat t). Qed.
Lemma lem1115844 : term407 = True.
Proof. exact (@lem1115843 True). Qed.
Lemma lem1115845 {A : Type'} (h : A) (t : list A) : (term433 A h t) = True.
Proof. exact (TRANS (@lem1115840 A h t) (@lem1115844)). Qed.
Lemma lem1115846 {A : Type'} (h : A) (t : list A) : (term373 A h t) = (False /\ True).
Proof. exact (MK_COMB (@lem1115813 A h t) (@lem1115845 A h t)). Qed.
Lemma lem1115848 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1115849 : (False /\ True) = False.
Proof. exact (@lem1115848 True). Qed.
Lemma lem1115850 {A : Type'} (h : A) (t : list A) : (term373 A h t) = False.
Proof. exact (TRANS (@lem1115846 A h t) (@lem1115849)). Qed.
Lemma lem1115851 {A : Type'} (h : A) (t : list A) : (((@cons A h t) = (@nil A)) = (term373 A h t)) = (False = False).
Proof. exact (MK_COMB (@lem1115795 A h t) (@lem1115850 A h t)). Qed.
Lemma lem1115853 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1115854 : (False = False) = (~ False).
Proof. exact (@lem1115853 False). Qed.
Lemma lem1115856 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1115857 : (False = False) = True.
Proof. exact (TRANS (@lem1115854) (@lem1115856)). Qed.
Lemma lem1115858 {A : Type'} (h : A) (t : list A) : (((@cons A h t) = (@nil A)) = (term373 A h t)) = True.
Proof. exact (TRANS (@lem1115851 A h t) (@lem1115857)). Qed.
Lemma lem1115859 {A : Type'} (h : A) (t : list A) : True = (((@cons A h t) = (@nil A)) = (term373 A h t)).
Proof. exact (SYM (@lem1115858 A h t)). Qed.
Lemma lem1115860 {A : Type'} (h : A) (t : list A) : ((@cons A h t) = (@nil A)) = (term373 A h t).
Proof. exact (EQ_MP (@lem1115859 A h t) (@lem0)). Qed.
Lemma lem1115864 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : ((@cons A h1' t1) = (@cons A h2' t2)) = (term302 A h1' h2' t1 t2).
Proof. exact (EQ_MP (@lem1115549 A h1' h2' t1 t2) (@lem1115548 A h1' h2' t1 t2)). Qed.
Lemma lem1115865 {A : Type'} (h1' : A) (h2' : A) (t1 : list A) (t2 : list A) : ((@cons A h1' t1) = (@cons A h2' t2)) = (term302 A h1' h2' t1 t2).
Proof. exact (@lem1115864 A h1' h2' t1 t2). Qed.
Lemma lem1115866 {A : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : ((@cons A h t) = (@cons A h' t')) = (term302 A h h' t t').
Proof. exact (@lem1115865 A h h' t t'). Qed.
Lemma lem1115873 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1115874 {A : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : (term434 A h t h' t') = (term435 A h h' t t').
Proof. exact (MK_COMB (@lem1115873) (@lem1115866 A h h' t t')). Qed.
Lemma lem1115880 {A : Type'} (h : A) (t : list A) : (term293 A h t) = (term294 A t).
Proof. exact (EQ_MP (@lem1115536 A h t) (@lem1115535 A h t)). Qed.
Lemma lem1115881 {A : Type'} (h : A) (t : list A) : (term293 A h t) = (term294 A t).
Proof. exact (@lem1115880 A h t). Qed.
Lemma lem1115882 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1115883 {A : Type'} (h : A) (t : list A) : (term427 A h t) = (term428 A t).
Proof. exact (MK_COMB (@lem1115882) (@lem1115881 A h t)). Qed.
Lemma lem1115885 {A : Type'} (h : A) (t : list A) : (term293 A h t) = (term294 A t).
Proof. exact (EQ_MP (@lem1115536 A h t) (@lem1115535 A h t)). Qed.
Lemma lem1115886 {A : Type'} (h : A) (t : list A) : (term293 A h t) = (term294 A t).
Proof. exact (@lem1115885 A h t). Qed.
Lemma lem1115887 {A : Type'} (h' : A) (t' : list A) : (term293 A h' t') = (term294 A t').
Proof. exact (@lem1115886 A h' t'). Qed.
Lemma lem1115888 {A : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : ((term293 A h t) = (term293 A h' t')) = ((term294 A t) = (term294 A t')).
Proof. exact (MK_COMB (@lem1115883 A h t) (@lem1115887 A h' t')). Qed.
Lemma lem1115891 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1115892 {A : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : (term436 A h t h' t') = (term437 A t t').
Proof. exact (MK_COMB (@lem1115891) (@lem1115888 A h h' t t')). Qed.
Lemma lem1115900 {A : Type'} (h : A) (t : list A) : (term293 A h t) = (term294 A t).
Proof. exact (EQ_MP (@lem1115536 A h t) (@lem1115535 A h t)). Qed.
Lemma lem1115901 {A : Type'} (h : A) (t : list A) : (term293 A h t) = (term294 A t).
Proof. exact (@lem1115900 A h t). Qed.
Lemma lem1115902 {A : Type'} (h' : A) (t' : list A) : (term293 A h' t') = (term294 A t').
Proof. exact (@lem1115901 A h' t'). Qed.
Lemma lem1115903 (n : nat) : (Peano.lt n) = (Peano.lt n).
Proof. exact (eq_refl (Peano.lt n)). Qed.
Lemma lem1115904 {A : Type'} (h' : A) (n : nat) (t' : list A) : (term414 A n h' t') = (term415 A n t').
Proof. exact (MK_COMB (@lem1115903 n) (@lem1115902 A h' t')). Qed.
Lemma lem1115905 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1115906 {A : Type'} (h' : A) (n : nat) (t' : list A) : (term416 A n h' t') = (term417 A n t').
Proof. exact (MK_COMB (@lem1115905) (@lem1115904 A h' n t')). Qed.
Lemma lem1115909 {A : Type'} (h : A) (t : list A) (n : nat) (h' : A) (t' : list A) : ((term418 A n h t) = (term418 A n h' t')) = ((term418 A n h t) = (term418 A n h' t')).
Proof. exact (eq_refl ((term418 A n h t) = (term418 A n h' t'))). Qed.
Lemma lem1115910 {A : Type'} (h : A) (t : list A) (n : nat) (h' : A) (t' : list A) : (term438 A h t n h' t') = (term439 A h t n h' t').
Proof. exact (MK_COMB (@lem1115906 A h' n t') (@lem1115909 A h t n h' t')). Qed.
Lemma lem1115913 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : (term440 A h t h' t') = (term441 A h t h' t').
Proof. exact (fun_ext (fun n : nat => @lem1115910 A h t n h' t')). Qed.
Lemma lem1115914 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1115915 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : (term442 A h t h' t') = (term443 A h t h' t').
Proof. exact (MK_COMB (@lem1115914) (@lem1115913 A h t h' t')). Qed.
Lemma lem1115920 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : (term381 A h t h' t') = (term444 A h t h' t').
Proof. exact (MK_COMB (@lem1115892 A h h' t t') (@lem1115915 A h t h' t')). Qed.
Lemma lem1115923 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : (((@cons A h t) = (@cons A h' t')) = (term381 A h t h' t')) = ((term302 A h h' t t') = (term444 A h t h' t')).
Proof. exact (MK_COMB (@lem1115874 A h h' t t') (@lem1115920 A h t h' t')). Qed.
Lemma lem1115926 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : ((term302 A h h' t t') = (term444 A h t h' t')) = (((@cons A h t) = (@cons A h' t')) = (term381 A h t h' t')).
Proof. exact (SYM (@lem1115923 A h t h' t')). Qed.
Lemma lem1115927 (m : nat) : term445 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem1115928 (m : nat) : (term445 m) = (term446 m).
Proof. exact (eq_refl (term445 m)). Qed.
Lemma lem1115929 (m : nat) : term446 m.
Proof. exact (EQ_MP (@lem1115928 m) (@lem1115927 m)). Qed.
Lemma lem1115930 (m : nat) (n : nat) : term447 m n.
Proof. exact (@lem1115929 m n). Qed.
Lemma lem1115931 (m : nat) (n : nat) : (term447 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term447 m n)). Qed.
Lemma lem1115933 {A : Type'} (l2 : list A) (t : list A) (h1 : term318 A t) : term448 A t l2.
Proof. exact (@lem1115597 A t h1 l2). Qed.
Lemma lem1115934 {A : Type'} (t : list A) (l2 : list A) : (term448 A t l2) = ((t = l2) = (term449 A t l2)).
Proof. exact (eq_refl (term448 A t l2)). Qed.
Lemma lem1115943 {A : Type'} (l2 : list A) (t : list A) (h1 : term318 A t) : (t = l2) = (term449 A t l2).
Proof. exact (EQ_MP (@lem1115934 A t l2) (@lem1115933 A l2 t h1)). Qed.
Lemma lem1115944 {A : Type'} (l2 : list A) (t : list A) (h1 : term318 A t) : (t = l2) = (term449 A t l2).
Proof. exact (@lem1115943 A l2 t h1). Qed.
Lemma lem1115945 {A : Type'} (t' : list A) (t : list A) (h1 : term318 A t) : (t = t') = (term449 A t t').
Proof. exact (@lem1115944 A t' t h1). Qed.
Lemma lem1115958 {A : Type'} (h : A) (h' : A) : (term450 A h h') = (term450 A h h').
Proof. exact (eq_refl (term450 A h h')). Qed.
Lemma lem1115959 {A : Type'} (h : A) (h' : A) (t' : list A) (t : list A) (h1 : term318 A t) : (term302 A h h' t t') = (term451 A h h' t t').
Proof. exact (MK_COMB (@lem1115958 A h h') (@lem1115945 A t' t h1)). Qed.
Lemma lem1115962 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1115963 {A : Type'} (h : A) (h' : A) (t' : list A) (t : list A) (h1 : term318 A t) : (term435 A h h' t t') = (term452 A h h' t t').
Proof. exact (MK_COMB (@lem1115962) (@lem1115959 A h h' t' t h1)). Qed.
Lemma lem1115967 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem1115931 m n) (@lem1115930 m n)). Qed.
Lemma lem1115968 {A : Type'} (t : list A) (t' : list A) : ((term294 A t) = (term294 A t')) = ((@List.length A t) = (@List.length A t')).
Proof. exact (@lem1115967 (@List.length A t) (@List.length A t')). Qed.
Lemma lem1115971 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1115972 {A : Type'} (t : list A) (t' : list A) : (term437 A t t') = (term453 A t t').
Proof. exact (MK_COMB (@lem1115971) (@lem1115968 A t t')). Qed.
Lemma lem1115981 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : (term443 A h t h' t') = (term443 A h t h' t').
Proof. exact (eq_refl (term443 A h t h' t')). Qed.
Lemma lem1115982 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : (term444 A h t h' t') = (term454 A h t h' t').
Proof. exact (MK_COMB (@lem1115972 A t t') (@lem1115981 A h t h' t')). Qed.
Lemma lem1115985 {A : Type'} (h : A) (h' : A) (t' : list A) (t : list A) (h1 : term318 A t) : ((term302 A h h' t t') = (term444 A h t h' t')) = ((term451 A h h' t t') = (term454 A h t h' t')).
Proof. exact (MK_COMB (@lem1115963 A h h' t' t h1) (@lem1115982 A h t h' t')). Qed.
Lemma lem1115988 {A : Type'} (h : A) (h' : A) (t' : list A) (t : list A) (h1 : term318 A t) : ((term451 A h h' t t') = (term454 A h t h' t')) = ((term302 A h h' t t') = (term444 A h t h' t')).
Proof. exact (SYM (@lem1115985 A h h' t' t h1)). Qed.
Lemma lem1115990 (P : nat -> Prop) : (term7 P) = (term8 P).
Proof. exact (EQ_MP (@lem1114204 P) (@lem1115509 P)). Qed.
Lemma lem1115991 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : (term455 A h t h' t') = (term456 A h t h' t').
Proof. exact (@lem1115990 (term441 A h t h' t')). Qed.
Lemma lem1115992 {A : Type'} (h : A) (t : list A) (n : nat) (h' : A) (t' : list A) : (term457 A h t h' t' n) = (term439 A h t n h' t').
Proof. exact (eq_refl (term457 A h t h' t' n)). Qed.
Lemma lem1115993 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : (term458 A h t h' t') = (term441 A h t h' t').
Proof. exact (fun_ext (fun n : nat => @lem1115992 A h t n h' t')). Qed.
Lemma lem1115994 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1115995 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : (term455 A h t h' t') = (term443 A h t h' t').
Proof. exact (MK_COMB (@lem1115994) (@lem1115993 A h t h' t')). Qed.
Lemma lem1115996 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1115997 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : (term459 A h t h' t') = (term460 A h t h' t').
Proof. exact (MK_COMB (@lem1115996) (@lem1115995 A h t h' t')). Qed.
Lemma lem1115998 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : (term461 A h t h' t') = (term462 A h t h' t').
Proof. exact (eq_refl (term461 A h t h' t')). Qed.
Lemma lem1115999 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1116000 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : (term463 A h t h' t') = (term464 A h t h' t').
Proof. exact (MK_COMB (@lem1115999) (@lem1115998 A h t h' t')). Qed.
Lemma lem1116001 {A : Type'} (h : A) (t : list A) (n : nat) (h' : A) (t' : list A) : (term465 A h t h' t' n) = (term466 A h t n h' t').
Proof. exact (eq_refl (term465 A h t h' t' n)). Qed.
Lemma lem1116002 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : (term467 A h t h' t') = (term468 A h t h' t').
Proof. exact (fun_ext (fun n : nat => @lem1116001 A h t n h' t')). Qed.
Lemma lem1116003 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1116004 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : (term469 A h t h' t') = (term470 A h t h' t').
Proof. exact (MK_COMB (@lem1116003) (@lem1116002 A h t h' t')). Qed.
Lemma lem1116005 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : (term456 A h t h' t') = (term471 A h t h' t').
Proof. exact (MK_COMB (@lem1116000 A h t h' t') (@lem1116004 A h t h' t')). Qed.
Lemma lem1116006 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : ((term455 A h t h' t') = (term456 A h t h' t')) = ((term443 A h t h' t') = (term471 A h t h' t')).
Proof. exact (MK_COMB (@lem1115997 A h t h' t') (@lem1116005 A h t h' t')). Qed.
Lemma lem1116007 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : (term443 A h t h' t') = (term471 A h t h' t').
Proof. exact (EQ_MP (@lem1116006 A h t h' t') (@lem1115991 A h t h' t')). Qed.
Lemma lem1116008 {A : Type'} (t : list A) (t' : list A) : (term453 A t t') = (term453 A t t').
Proof. exact (eq_refl (term453 A t t')). Qed.
Lemma lem1116009 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : (term454 A h t h' t') = (term472 A h t h' t').
Proof. exact (MK_COMB (@lem1116008 A t t') (@lem1116007 A h t h' t')). Qed.
Lemma lem1116010 {A : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : (term452 A h h' t t') = (term452 A h h' t t').
Proof. exact (eq_refl (term452 A h h' t t')). Qed.
Lemma lem1116011 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : ((term451 A h h' t t') = (term454 A h t h' t')) = ((term451 A h h' t t') = (term472 A h t h' t')).
Proof. exact (MK_COMB (@lem1116010 A h h' t t') (@lem1116009 A h t h' t')). Qed.
Lemma lem1116012 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : ((term451 A h h' t t') = (term472 A h t h' t')) = ((term451 A h h' t t') = (term454 A h t h' t')).
Proof. exact (SYM (@lem1116011 A h t h' t')). Qed.
Lemma lem1116034 (q : Prop) (p : Prop) : (p /\ q) = (q /\ p).
Proof. exact (EQ_MP (@lem555 q p) (@lem554 p q)). Qed.
Lemma lem1116035 {A : Type'} (t : list A) (t' : list A) : (term449 A t t') = (term473 A t t').
Proof. exact (@lem1116034 (term474 A t t') ((@List.length A t) = (@List.length A t'))). Qed.
Lemma lem1116053 {A : Type'} (h : A) (h' : A) : (term450 A h h') = (term450 A h h').
Proof. exact (eq_refl (term450 A h h')). Qed.
Lemma lem1116054 {A : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : (term451 A h h' t t') = (term475 A h h' t t').
Proof. exact (MK_COMB (@lem1116053 A h h') (@lem1116035 A t t')). Qed.
Lemma lem1116058 (q : Prop) (p : Prop) (r : Prop) : (term476 p q r) = (term476 q p r).
Proof. exact (EQ_MP (@lem617 q p r) (@lem616 p q r)). Qed.
Lemma lem1116059 {A : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : (term475 A h h' t t') = (term477 A h h' t t').
Proof. exact (@lem1116058 (term474 A t t') (h = h') ((@List.length A t) = (@List.length A t'))). Qed.
Lemma lem1116091 {A : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : (term451 A h h' t t') = (term477 A h h' t t').
Proof. exact (TRANS (@lem1116054 A h h' t t') (@lem1116059 A h h' t t')). Qed.
Lemma lem1116092 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1116093 {A : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : (term452 A h h' t t') = (term478 A h h' t t').
Proof. exact (MK_COMB (@lem1116092) (@lem1116091 A h h' t t')). Qed.
Lemma lem1116113 (q : Prop) (p : Prop) : (p /\ q) = (q /\ p).
Proof. exact (EQ_MP (@lem555 q p) (@lem554 p q)). Qed.
Lemma lem1116114 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : (term471 A h t h' t') = (term479 A h t h' t').
Proof. exact (@lem1116113 (term470 A h t h' t') (term462 A h t h' t')). Qed.
Lemma lem1116129 (m : nat) (n : nat) : (term3 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem1114182 m n) (@lem1114181 m n)). Qed.
Lemma lem1116130 {A : Type'} (n : nat) (t' : list A) : (term480 A n t') = (term481 A n t').
Proof. exact (@lem1116129 n (@List.length A t')). Qed.
Lemma lem1116131 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1116132 {A : Type'} (n : nat) (t' : list A) : (term482 A n t') = (term483 A n t').
Proof. exact (MK_COMB (@lem1116131) (@lem1116130 A n t')). Qed.
Lemma lem1116136 {_25569 : Type'} (n : nat) (l : list _25569) : (term484 _25569 n l) = (term485 _25569 n l).
Proof. exact (EQ_MP (@lem1105748 _25569 n l) (@lem1105747 _25569 n l)). Qed.
Lemma lem1116137 {A : Type'} (n : nat) (l : list A) : (term484 A n l) = (term485 A n l).
Proof. exact (@lem1116136 A n l). Qed.
Lemma lem1116138 {A : Type'} (n : nat) (h : A) (t : list A) : (term486 A n h t) = (term487 A n h t).
Proof. exact (@lem1116137 A n (@cons A h t)). Qed.
Lemma lem1116140 {A : Type'} (h : A) (t : list A) : (term488 A h t) = t.
Proof. exact (EQ_MP (@lem1095389 A h t) (@lem1095388 A h t)). Qed.
Lemma lem1116141 {A : Type'} (h : A) (t : list A) : (term488 A h t) = t.
Proof. exact (@lem1116140 A h t). Qed.
Lemma lem1116142 {A : Type'} (n : nat) : (@EL A n) = (@EL A n).
Proof. exact (eq_refl (@EL A n)). Qed.
Lemma lem1116143 {A : Type'} (h : A) (n : nat) (t : list A) : (term487 A n h t) = (@EL A n t).
Proof. exact (MK_COMB (@lem1116142 A n) (@lem1116141 A h t)). Qed.
Lemma lem1116144 {A : Type'} (h : A) (n : nat) (t : list A) : (term486 A n h t) = (@EL A n t).
Proof. exact (TRANS (@lem1116138 A n h t) (@lem1116143 A h n t)). Qed.
Lemma lem1116145 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1116146 {A : Type'} (h : A) (n : nat) (t : list A) : (term489 A n h t) = (term490 A n t).
Proof. exact (MK_COMB (@lem1116145 A) (@lem1116144 A h n t)). Qed.
Lemma lem1116148 {_25569 : Type'} (n : nat) (l : list _25569) : (term484 _25569 n l) = (term485 _25569 n l).
Proof. exact (EQ_MP (@lem1105748 _25569 n l) (@lem1105747 _25569 n l)). Qed.
Lemma lem1116149 {A : Type'} (n : nat) (l : list A) : (term484 A n l) = (term485 A n l).
Proof. exact (@lem1116148 A n l). Qed.
Lemma lem1116150 {A : Type'} (n : nat) (h' : A) (t' : list A) : (term486 A n h' t') = (term487 A n h' t').
Proof. exact (@lem1116149 A n (@cons A h' t')). Qed.
Lemma lem1116152 {A : Type'} (h : A) (t : list A) : (term488 A h t) = t.
Proof. exact (EQ_MP (@lem1095389 A h t) (@lem1095388 A h t)). Qed.
Lemma lem1116153 {A : Type'} (h : A) (t : list A) : (term488 A h t) = t.
Proof. exact (@lem1116152 A h t). Qed.
Lemma lem1116154 {A : Type'} (h' : A) (t' : list A) : (term488 A h' t') = t'.
Proof. exact (@lem1116153 A h' t'). Qed.
Lemma lem1116155 {A : Type'} (n : nat) : (@EL A n) = (@EL A n).
Proof. exact (eq_refl (@EL A n)). Qed.
Lemma lem1116156 {A : Type'} (h' : A) (n : nat) (t' : list A) : (term487 A n h' t') = (@EL A n t').
Proof. exact (MK_COMB (@lem1116155 A n) (@lem1116154 A h' t')). Qed.
Lemma lem1116157 {A : Type'} (h' : A) (n : nat) (t' : list A) : (term486 A n h' t') = (@EL A n t').
Proof. exact (TRANS (@lem1116150 A n h' t') (@lem1116156 A h' n t')). Qed.
Lemma lem1116158 {A : Type'} (h : A) (h' : A) (t : list A) (n : nat) (t' : list A) : ((term486 A n h t) = (term486 A n h' t')) = ((@EL A n t) = (@EL A n t')).
Proof. exact (MK_COMB (@lem1116146 A h n t) (@lem1116157 A h' n t')). Qed.
Lemma lem1116161 {A : Type'} (h : A) (h' : A) (t : list A) (n : nat) (t' : list A) : (term466 A h t n h' t') = (term491 A t n t').
Proof. exact (MK_COMB (@lem1116132 A n t') (@lem1116158 A h h' t n t')). Qed.
Lemma lem1116164 {A : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : (term468 A h t h' t') = (term492 A t t').
Proof. exact (fun_ext (fun n : nat => @lem1116161 A h h' t n t')). Qed.
Lemma lem1116165 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1116166 {A : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : (term470 A h t h' t') = (term474 A t t').
Proof. exact (MK_COMB (@lem1116165) (@lem1116164 A h h' t t')). Qed.
Lemma lem1116171 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1116172 {A : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : (term493 A h t h' t') = (term494 A t t').
Proof. exact (MK_COMB (@lem1116171) (@lem1116166 A h h' t t')). Qed.
Lemma lem1116176 (n : nat) : (term5 n) = True.
Proof. exact (EQ_MP (@lem1114187 n) (@lem1114186 n)). Qed.
Lemma lem1116177 {A : Type'} (t' : list A) : (term495 A t') = True.
Proof. exact (@lem1116176 (@List.length A t')). Qed.
Lemma lem1116178 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1116179 {A : Type'} (t' : list A) : (term496 A t') = (imp True).
Proof. exact (MK_COMB (@lem1116178) (@lem1116177 A t')). Qed.
Lemma lem1116183 {_25569 : Type'} (l : list _25569) : (term497 _25569 l) = (@hd _25569 l).
Proof. exact (EQ_MP (@lem1105742 _25569 l) (@lem1105741 _25569 l)). Qed.
Lemma lem1116184 {A : Type'} (l : list A) : (term497 A l) = (@hd A l).
Proof. exact (@lem1116183 A l). Qed.
Lemma lem1116185 {A : Type'} (h : A) (t : list A) : (term498 A h t) = (term499 A h t).
Proof. exact (@lem1116184 A (@cons A h t)). Qed.
Lemma lem1116187 {A : Type'} (t : list A) (h : A) : (term499 A h t) = h.
Proof. exact (EQ_MP (@lem1094866 A t h) (@lem1094865 A t h)). Qed.
Lemma lem1116188 {A : Type'} (t : list A) (h : A) : (term499 A h t) = h.
Proof. exact (@lem1116187 A t h). Qed.
Lemma lem1116189 {A : Type'} (t : list A) (h : A) : (term498 A h t) = h.
Proof. exact (TRANS (@lem1116185 A h t) (@lem1116188 A t h)). Qed.
Lemma lem1116190 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1116191 {A : Type'} (t : list A) (h : A) : (term500 A h t) = (@eq A h).
Proof. exact (MK_COMB (@lem1116190 A) (@lem1116189 A t h)). Qed.
Lemma lem1116193 {_25569 : Type'} (l : list _25569) : (term497 _25569 l) = (@hd _25569 l).
Proof. exact (EQ_MP (@lem1105742 _25569 l) (@lem1105741 _25569 l)). Qed.
Lemma lem1116194 {A : Type'} (l : list A) : (term497 A l) = (@hd A l).
Proof. exact (@lem1116193 A l). Qed.
Lemma lem1116195 {A : Type'} (h' : A) (t' : list A) : (term498 A h' t') = (term499 A h' t').
Proof. exact (@lem1116194 A (@cons A h' t')). Qed.
Lemma lem1116197 {A : Type'} (t : list A) (h : A) : (term499 A h t) = h.
Proof. exact (EQ_MP (@lem1094866 A t h) (@lem1094865 A t h)). Qed.
Lemma lem1116198 {A : Type'} (t : list A) (h : A) : (term499 A h t) = h.
Proof. exact (@lem1116197 A t h). Qed.
Lemma lem1116199 {A : Type'} (t' : list A) (h' : A) : (term499 A h' t') = h'.
Proof. exact (@lem1116198 A t' h'). Qed.
Lemma lem1116200 {A : Type'} (t' : list A) (h' : A) : (term498 A h' t') = h'.
Proof. exact (TRANS (@lem1116195 A h' t') (@lem1116199 A t' h')). Qed.
Lemma lem1116201 {A : Type'} (t : list A) (t' : list A) (h : A) (h' : A) : ((term498 A h t) = (term498 A h' t')) = (h = h').
Proof. exact (MK_COMB (@lem1116191 A t h) (@lem1116200 A t' h')). Qed.
Lemma lem1116204 {A : Type'} (t : list A) (t' : list A) (h : A) (h' : A) : (term462 A h t h' t') = (term501 A h h').
Proof. exact (MK_COMB (@lem1116179 A t') (@lem1116201 A t t' h h')). Qed.
Lemma lem1116206 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1116207 {A : Type'} (h : A) (h' : A) : (term501 A h h') = (h = h').
Proof. exact (@lem1116206 (h = h')). Qed.
Lemma lem1116210 {A : Type'} (t : list A) (t' : list A) (h : A) (h' : A) : (term462 A h t h' t') = (h = h').
Proof. exact (TRANS (@lem1116204 A t t' h h') (@lem1116207 A h h')). Qed.
Lemma lem1116211 {A : Type'} (t : list A) (t' : list A) (h : A) (h' : A) : (term479 A h t h' t') = (term502 A t t' h h').
Proof. exact (MK_COMB (@lem1116172 A h h' t t') (@lem1116210 A t t' h h')). Qed.
Lemma lem1116219 {A : Type'} (t : list A) (t' : list A) (h : A) (h' : A) : (term471 A h t h' t') = (term502 A t t' h h').
Proof. exact (TRANS (@lem1116114 A h t h' t') (@lem1116211 A t t' h h')). Qed.
Lemma lem1116220 {A : Type'} (t : list A) (t' : list A) : (term453 A t t') = (term453 A t t').
Proof. exact (eq_refl (term453 A t t')). Qed.
Lemma lem1116221 {A : Type'} (t : list A) (t' : list A) (h : A) (h' : A) : (term472 A h t h' t') = (term503 A t t' h h').
Proof. exact (MK_COMB (@lem1116220 A t t') (@lem1116219 A t t' h h')). Qed.
Lemma lem1116225 (q : Prop) (p : Prop) (r : Prop) : (term476 p q r) = (term476 q p r).
Proof. exact (EQ_MP (@lem617 q p r) (@lem616 p q r)). Qed.
Lemma lem1116226 {A : Type'} (t : list A) (t' : list A) (h : A) (h' : A) : (term503 A t t' h h') = (term504 A t t' h h').
Proof. exact (@lem1116225 (term474 A t t') ((@List.length A t) = (@List.length A t')) (h = h')). Qed.
Lemma lem1116252 (q : Prop) (p : Prop) : (p /\ q) = (q /\ p).
Proof. exact (EQ_MP (@lem555 q p) (@lem554 p q)). Qed.
Lemma lem1116253 {A : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : (term505 A t t' h h') = (term506 A h h' t t').
Proof. exact (@lem1116252 (h = h') ((@List.length A t) = (@List.length A t'))). Qed.
Lemma lem1116265 {A : Type'} (t : list A) (t' : list A) : (term494 A t t') = (term494 A t t').
Proof. exact (eq_refl (term494 A t t')). Qed.
Lemma lem1116266 {A : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : (term504 A t t' h h') = (term477 A h h' t t').
Proof. exact (MK_COMB (@lem1116265 A t t') (@lem1116253 A h h' t t')). Qed.
Lemma lem1116279 {A : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : (term503 A t t' h h') = (term477 A h h' t t').
Proof. exact (TRANS (@lem1116226 A t t' h h') (@lem1116266 A h h' t t')). Qed.
Lemma lem1116280 {A : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : (term472 A h t h' t') = (term477 A h h' t t').
Proof. exact (TRANS (@lem1116221 A t t' h h') (@lem1116279 A h h' t t')). Qed.
Lemma lem1116281 {A : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : ((term451 A h h' t t') = (term472 A h t h' t')) = ((term477 A h h' t t') = (term477 A h h' t t')).
Proof. exact (MK_COMB (@lem1116093 A h h' t t') (@lem1116280 A h h' t t')). Qed.
Lemma lem1116283 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1116284 (x : Prop) : (x = x) = True.
Proof. exact (@lem1116283 Prop x). Qed.
Lemma lem1116285 {A : Type'} (h : A) (h' : A) (t : list A) (t' : list A) : ((term477 A h h' t t') = (term477 A h h' t t')) = True.
Proof. exact (@lem1116284 (term477 A h h' t t')). Qed.
Lemma lem1116286 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : ((term451 A h h' t t') = (term472 A h t h' t')) = True.
Proof. exact (TRANS (@lem1116281 A h h' t t') (@lem1116285 A h h' t t')). Qed.
Lemma lem1116287 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : True = ((term451 A h h' t t') = (term472 A h t h' t')).
Proof. exact (SYM (@lem1116286 A h t h' t')). Qed.
Lemma lem1116288 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : (term451 A h h' t t') = (term472 A h t h' t').
Proof. exact (EQ_MP (@lem1116287 A h t h' t') (@lem0)). Qed.
Lemma lem1116289 {A : Type'} (h : A) (t : list A) (h' : A) (t' : list A) : (term451 A h h' t t') = (term454 A h t h' t').
Proof. exact (EQ_MP (@lem1116012 A h t h' t') (@lem1116288 A h t h' t')). Qed.
Lemma lem1116290 {A : Type'} (h : A) (h' : A) (t' : list A) (t : list A) (h1 : term318 A t) : (term302 A h h' t t') = (term444 A h t h' t').
Proof. exact (EQ_MP (@lem1115988 A h h' t' t h1) (@lem1116289 A h t h' t')). Qed.
Lemma lem1116291 {A : Type'} (h : A) (h' : A) (t' : list A) (t : list A) (h1 : term318 A t) : ((@cons A h t) = (@cons A h' t')) = (term381 A h t h' t').
Proof. exact (EQ_MP (@lem1115926 A h t h' t') (@lem1116290 A h h' t' t h1)). Qed.
Lemma lem1116292 {A : Type'} (h : A) (h' : A) (t' : list A) (t : list A) (h1 : term318 A t) : term383 A h t h' t'.
Proof. exact (fun h0 : ((@cons A h t) = t') = (term377 A h t t') => @lem1116291 A h h' t' t h1). Qed.
Lemma lem1116297 {A : Type'} (h : A) (h' : A) (t : list A) (h1 : term318 A t) : term387 A h t h'.
Proof. exact (fun t' : list A => @lem1116292 A h h' t' t h1). Qed.
Lemma lem1116302 {A : Type'} (h : A) (t : list A) (h1 : term318 A t) : term391 A h t.
Proof. exact (fun h' : A => @lem1116297 A h h' t h1). Qed.
Lemma lem1116303 {A : Type'} (h : A) (t : list A) (h1 : term318 A t) : term393 A h t.
Proof. exact (conj (@lem1115860 A h t) (@lem1116302 A h t h1)). Qed.
Lemma lem1116304 {A : Type'} (h : A) (t : list A) (h1 : term318 A t) : term322 A h t.
Proof. exact (@lem1115656 A h t (@lem1116303 A h t h1)). Qed.
Lemma lem1116305 {A : Type'} (h : A) (t : list A) : term354 A h t.
Proof. exact (fun h0 : ((@nil A) = t) = (term348 A t) => @lem1115788 A h t). Qed.
Lemma lem1116310 {A : Type'} (h : A) : term358 A h.
Proof. exact (fun t : list A => @lem1116305 A h t). Qed.
Lemma lem1116315 {A : Type'} : term362 A.
Proof. exact (fun h : A => @lem1116310 A h). Qed.
Lemma lem1116316 {A : Type'} : term364 A.
Proof. exact (conj (@lem1115722 A) (@lem1116315 A)). Qed.
Lemma lem1116317 {A : Type'} : term314 A.
Proof. exact (@lem1115624 A (@lem1116316 A)). Qed.
Lemma lem1116318 {A : Type'} (h : A) (t : list A) : term324 A h t.
Proof. exact (fun h0 : term318 A t => @lem1116304 A h t h0). Qed.
Lemma lem1116323 {A : Type'} (h : A) : term328 A h.
Proof. exact (fun t : list A => @lem1116318 A h t). Qed.
Lemma lem1116328 {A : Type'} : term332 A.
Proof. exact (fun h : A => @lem1116323 A h). Qed.
Lemma lem1116329 {A : Type'} : term334 A.
Proof. exact (conj (@lem1116317 A) (@lem1116328 A)). Qed.
Lemma lem1116330 {A : Type'} : term339 A.
Proof. exact (@lem1115596 A (@lem1116329 A)). Qed.
