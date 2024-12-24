Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EVEN_SUB_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EVEN_spec.
Require Import EVEN_ADD_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LE_CASES_spec.
Require Import SUB_ADD_spec.
Require Import SUB_EQ_0_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16463_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm17500_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm17930_spec.
Require Import thm1833_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Require Import thm82_spec.
Lemma lem137167 (m : nat) : term0 m.
Proof. exact (@lem136494 m). Qed.
Lemma lem137168 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem137169 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem137168 m) (@lem137167 m)). Qed.
Lemma lem137170 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem137169 m n). Qed.
Lemma lem137171 (n : nat) (m : nat) : (term2 m n) = (term3 n m).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem137173 : Coq.Arith.PeanoNat.Nat.Even = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Even). Qed.
Lemma lem137174 (m : nat) : term4 m.
Proof. exact (@lem96155 m). Qed.
Lemma lem137175 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem137176 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem137175 m) (@lem137174 m)). Qed.
Lemma lem137177 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem137176 m n). Qed.
Lemma lem137178 (n : nat) (m : nat) : (term6 m n) = (term7 n m).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem137179 (n : nat) (m : nat) : term7 n m.
Proof. exact (EQ_MP (@lem137178 n m) (@lem137177 m n)). Qed.
Lemma lem137180 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem137181 (n : nat) (m : nat) (h1 : Peano.le n m) : Peano.le n m.
Proof. exact (h1). Qed.
Lemma lem137192 (m : nat) (n : nat) : term8 m n.
Proof. exact (@lem9784 (Peano.le m n)). Qed.
Lemma lem137193 (m : nat) (n : nat) : (term8 m n) = (term9 m n).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem137194 (m : nat) (n : nat) : term9 m n.
Proof. exact (EQ_MP (@lem137193 m n) (@lem137192 m n)). Qed.
Lemma lem137195 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem137196 (m : nat) (n : nat) (h1 : term10 m n) : term10 m n.
Proof. exact (h1). Qed.
Lemma lem137198 (p : Prop) : p = (term11 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem137199 (m : nat) (n : nat) : ((term12 m n) = (term13 m n)) = (term14 m n).
Proof. exact (@lem137198 ((term12 m n) = (term13 m n))). Qed.
Lemma lem137200 (m : nat) (n : nat) : (term14 m n) = ((term12 m n) = (term13 m n)).
Proof. exact (SYM (@lem137199 m n)). Qed.
Lemma lem137201 (m : nat) (n : nat) (h1 : term15 m n) : term15 m n.
Proof. exact (h1). Qed.
Lemma lem137204 (m : nat) (n : nat) (h1 : term16 m n) : term16 m n.
Proof. exact (h1). Qed.
Lemma lem137205 (m : nat) (n : nat) : term17 m n.
Proof. exact (fun h0 : term16 m n => @lem137204 m n h0). Qed.
Lemma lem137206 (m : nat) (n : nat) (h1 : term17 m n) : term17 m n.
Proof. exact (h1). Qed.
Lemma lem137207 (m : nat) (n : nat) (h1 : term16 m n) : term16 m n.
Proof. exact (h1). Qed.
Lemma lem137208 (m : nat) (n : nat) (h1 : term16 m n) (h2 : term17 m n) : term16 m n.
Proof. exact (@lem137206 m n h2 (@lem137207 m n h1)). Qed.
Lemma lem137209 (m : nat) (n : nat) (h1 : term16 m n) : term18 m n.
Proof. exact (fun h0 : term17 m n => @lem137208 m n h1 h0). Qed.
Lemma lem137210 (m : nat) (n : nat) (h1 : term17 m n) : term17 m n.
Proof. exact (h1). Qed.
Lemma lem137211 (m : nat) (n : nat) (h1 : term16 m n) (h2 : term17 m n) : term16 m n.
Proof. exact (@lem137209 m n h1 (@lem137210 m n h2)). Qed.
Lemma lem137212 (m : nat) (n : nat) (h1 : term17 m n) : term17 m n.
Proof. exact (fun h0 : term16 m n => @lem137211 m n h0 h1). Qed.
Lemma lem137213 (m : nat) (n : nat) : term19 m n.
Proof. exact (fun h0 : term17 m n => @lem137212 m n h0). Qed.
Lemma lem137216 (m : nat) (n : nat) : term17 m n.
Proof. exact (@lem137213 m n (@lem137205 m n)). Qed.
Lemma lem137236 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem16463 t)). Qed.
Lemma lem137237 : (term20 = True) = term20.
Proof. exact (@lem137236 term20). Qed.
Lemma lem137238 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem137239 : term21 = term22.
Proof. exact (MK_COMB (@lem137238) (@lem137237)). Qed.
Lemma lem137244 : term23 = term23.
Proof. exact (eq_refl term23). Qed.
Lemma lem137245 : term24 = term25.
Proof. exact (MK_COMB (@lem137239) (@lem137244)). Qed.
Lemma lem137248 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem137249 : term26 = term27.
Proof. exact (MK_COMB (@lem137248) (@lem137245)). Qed.
Lemma lem137251 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem137252 : term28 = term29.
Proof. exact (@lem137251 term30). Qed.
Lemma lem137261 : term31 = term32.
Proof. exact (MK_COMB (@lem137249) (@lem137252)). Qed.
Lemma lem137264 (m : nat) (n : nat) : (term33 m n) = (term33 m n).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem137265 (m : nat) (n : nat) : (term34 m n) = (term35 m n).
Proof. exact (MK_COMB (@lem137264 m n) (@lem137261)). Qed.
Lemma lem137268 (m : nat) (n : nat) : (term36 m n) = (term36 m n).
Proof. exact (eq_refl (term36 m n)). Qed.
Lemma lem137269 (m : nat) (n : nat) : (term16 m n) = (term37 m n).
Proof. exact (MK_COMB (@lem137268 m n) (@lem137265 m n)). Qed.
Lemma lem137272 (n : nat) : (term38 n) = (term39 n).
Proof. exact (fun_ext (fun m : nat => @lem137269 m n)). Qed.
Lemma lem137273 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem137274 (n : nat) : (term40 n) = (term41 n).
Proof. exact (MK_COMB (@lem137273) (@lem137272 n)). Qed.
Lemma lem137279 : term42 = term43.
Proof. exact (fun_ext (fun n : nat => @lem137274 n)). Qed.
Lemma lem137280 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem137289 : term44 = term45.
Proof. exact (MK_COMB (@lem137280) (@lem137279)). Qed.
Lemma lem137294 (m : nat) (n : nat) : (((Nat.sub m n) = (NUMERAL 0)) = (Peano.le m n)) = (((Nat.sub m n) = (NUMERAL 0)) = (Peano.le m n)).
Proof. exact (eq_refl (((Nat.sub m n) = (NUMERAL 0)) = (Peano.le m n))). Qed.
Lemma lem137295 (m : nat) : (term46 m) = (term46 m).
Proof. exact (fun_ext (fun n : nat => @lem137294 m n)). Qed.
Lemma lem137296 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem137297 (m : nat) : (term47 m) = (term47 m).
Proof. exact (MK_COMB (@lem137296) (@lem137295 m)). Qed.
Lemma lem137298 : term48 = term48.
Proof. exact (fun_ext (fun m : nat => @lem137297 m)). Qed.
Lemma lem137299 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem137300 : term30 = term30.
Proof. exact (MK_COMB (@lem137299) (@lem137298)). Qed.
Lemma lem137301 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem137302 : term29 = term29.
Proof. exact (MK_COMB (@lem137301) (@lem137300)). Qed.
Lemma lem137309 (n : nat) : ((term49 n) = (term50 n)) = ((term49 n) = (term50 n)).
Proof. exact (eq_refl ((term49 n) = (term50 n))). Qed.
Lemma lem137310 : term51 = term51.
Proof. exact (fun_ext (fun n : nat => @lem137309 n)). Qed.
Lemma lem137311 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem137312 : term23 = term23.
Proof. exact (MK_COMB (@lem137311) (@lem137310)). Qed.
Lemma lem137315 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem137316 : term25 = term25.
Proof. exact (MK_COMB (@lem137315) (@lem137312)). Qed.
Lemma lem137317 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem137318 : term27 = term27.
Proof. exact (MK_COMB (@lem137317) (@lem137316)). Qed.
Lemma lem137319 : term32 = term32.
Proof. exact (MK_COMB (@lem137318) (@lem137302)). Qed.
Lemma lem137336 (m : nat) (n : nat) : (term33 m n) = (term33 m n).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem137337 (m : nat) (n : nat) : (term35 m n) = (term35 m n).
Proof. exact (MK_COMB (@lem137336 m n) (@lem137319)). Qed.
Lemma lem137340 (m : nat) (n : nat) : (term36 m n) = (term36 m n).
Proof. exact (eq_refl (term36 m n)). Qed.
Lemma lem137341 (m : nat) (n : nat) : (term37 m n) = (term37 m n).
Proof. exact (MK_COMB (@lem137340 m n) (@lem137337 m n)). Qed.
Lemma lem137342 (n : nat) : (term39 n) = (term39 n).
Proof. exact (fun_ext (fun m : nat => @lem137341 m n)). Qed.
Lemma lem137343 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem137344 (n : nat) : (term41 n) = (term41 n).
Proof. exact (MK_COMB (@lem137343) (@lem137342 n)). Qed.
Lemma lem137345 : term43 = term43.
Proof. exact (fun_ext (fun n : nat => @lem137344 n)). Qed.
Lemma lem137346 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem137347 : term45 = term45.
Proof. exact (MK_COMB (@lem137346) (@lem137345)). Qed.
Lemma lem137390 : term44 = term45.
Proof. exact (TRANS (@lem137289) (@lem137347)). Qed.
Lemma lem137391 : term45 = term44.
Proof. exact (SYM (@lem137390)). Qed.
Lemma lem137393 (m : nat) (n : nat) (h1 : term15 m n) : term15 m n.
Proof. exact (h1). Qed.
Lemma lem137394 (h1 : term25) : term25.
Proof. exact (h1). Qed.
Lemma lem137395 (h1 : term30) : term30.
Proof. exact (h1). Qed.
Lemma lem137401 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem137420 (m : nat) (n : nat) : (term52 m n) = (term53 m n).
Proof. exact (@lem17646 (Coq.Arith.PeanoNat.Nat.Even m) (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem137431 (m : nat) (n : nat) : ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)) = (term54 m n).
Proof. exact (@lem17500 (Coq.Arith.PeanoNat.Nat.Even m) (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem137433 (m : nat) (n : nat) : (term55 m n) = (term55 m n).
Proof. exact (eq_refl (term55 m n)). Qed.
Lemma lem137434 (m : nat) (n : nat) : (term56 m n) = (term57 m n).
Proof. exact (MK_COMB (@lem137433 m n) (@lem137420 m n)). Qed.
Lemma lem137435 (m : nat) (n : nat) : (term58 m n) = (term56 m n).
Proof. exact (@lem17160 (Peano.le m n) ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))). Qed.
Lemma lem137436 (m : nat) (n : nat) : (term58 m n) = (term57 m n).
Proof. exact (TRANS (@lem137435 m n) (@lem137434 m n)). Qed.
Lemma lem137438 (m : nat) (n : nat) : (term59 m n) = (term59 m n).
Proof. exact (eq_refl (term59 m n)). Qed.
Lemma lem137439 (m : nat) (n : nat) : (term13 m n) = (term60 m n).
Proof. exact (MK_COMB (@lem137438 m n) (@lem137431 m n)). Qed.
Lemma lem137441 (m : nat) (n : nat) : (term61 m n) = (term61 m n).
Proof. exact (eq_refl (term61 m n)). Qed.
Lemma lem137442 (m : nat) (n : nat) : (term62 m n) = (term63 m n).
Proof. exact (MK_COMB (@lem137441 m n) (@lem137439 m n)). Qed.
Lemma lem137444 (m : nat) (n : nat) : (term64 m n) = (term64 m n).
Proof. exact (eq_refl (term64 m n)). Qed.
Lemma lem137445 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (MK_COMB (@lem137444 m n) (@lem137436 m n)). Qed.
Lemma lem137446 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem137447 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (MK_COMB (@lem137446) (@lem137445 m n)). Qed.
Lemma lem137448 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (MK_COMB (@lem137447 m n) (@lem137442 m n)). Qed.
Lemma lem137449 (m : nat) (n : nat) : (term15 m n) = (term69 m n).
Proof. exact (@lem17646 (term12 m n) (term13 m n)). Qed.
Lemma lem137454 (m : nat) (n : nat) : (term15 m n) = (term70 m n).
Proof. exact (TRANS (@lem137449 m n) (@lem137448 m n)). Qed.
Lemma lem137462 (n : nat) : (term71 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (@lem16933 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem137465 (n : nat) : (term72 n) = (term72 n).
Proof. exact (eq_refl (term72 n)). Qed.
Lemma lem137467 (n : nat) : (term73 n) = (term73 n).
Proof. exact (eq_refl (term73 n)). Qed.
Lemma lem137468 (n : nat) : (term74 n) = (term75 n).
Proof. exact (MK_COMB (@lem137467 n) (@lem137462 n)). Qed.
Lemma lem137469 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem137470 (n : nat) : (term76 n) = (term77 n).
Proof. exact (MK_COMB (@lem137469) (@lem137468 n)). Qed.
Lemma lem137471 (n : nat) : (term78 n) = (term79 n).
Proof. exact (MK_COMB (@lem137470 n) (@lem137465 n)). Qed.
Lemma lem137472 (n : nat) : ((term49 n) = (term50 n)) = (term78 n).
Proof. exact (@lem17784 (term49 n) (term50 n)). Qed.
Lemma lem137473 (n : nat) : ((term49 n) = (term50 n)) = (term79 n).
Proof. exact (TRANS (@lem137472 n) (@lem137471 n)). Qed.
Lemma lem137474 : term51 = term80.
Proof. exact (fun_ext (fun n : nat => @lem137473 n)). Qed.
Lemma lem137475 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem137476 : term23 = term81.
Proof. exact (MK_COMB (@lem137475) (@lem137474)). Qed.
Lemma lem137478 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem137479 : term25 = term82.
Proof. exact (MK_COMB (@lem137478) (@lem137476)). Qed.
Lemma lem137481 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term83 A P Q) = (term84 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem137482 (P : nat -> Prop) (Q : nat -> Prop) : (term85 P Q) = (term86 P Q).
Proof. exact (@lem137481 nat P Q). Qed.
Lemma lem137483 : term87 = term88.
Proof. exact (@lem137482 term89 term90). Qed.
Lemma lem137484 (n : nat) : (term91 n) = (term75 n).
Proof. exact (eq_refl (term91 n)). Qed.
Lemma lem137485 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem137486 (n : nat) : (term92 n) = (term77 n).
Proof. exact (MK_COMB (@lem137485) (@lem137484 n)). Qed.
Lemma lem137487 (n : nat) : (term93 n) = (term72 n).
Proof. exact (eq_refl (term93 n)). Qed.
Lemma lem137488 (n : nat) : (term94 n) = (term79 n).
Proof. exact (MK_COMB (@lem137486 n) (@lem137487 n)). Qed.
Lemma lem137489 : term95 = term80.
Proof. exact (fun_ext (fun n : nat => @lem137488 n)). Qed.
Lemma lem137490 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem137491 : term87 = term81.
Proof. exact (MK_COMB (@lem137490) (@lem137489)). Qed.
Lemma lem137492 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem137493 : term96 = term97.
Proof. exact (MK_COMB (@lem137492) (@lem137491)). Qed.
Lemma lem137494 (n : nat) : (term91 n) = (term75 n).
Proof. exact (eq_refl (term91 n)). Qed.
Lemma lem137495 : term98 = term89.
Proof. exact (fun_ext (fun n : nat => @lem137494 n)). Qed.
Lemma lem137496 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem137497 : term99 = term100.
Proof. exact (MK_COMB (@lem137496) (@lem137495)). Qed.
Lemma lem137498 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem137499 : term101 = term102.
Proof. exact (MK_COMB (@lem137498) (@lem137497)). Qed.
Lemma lem137500 (n : nat) : (term93 n) = (term72 n).
Proof. exact (eq_refl (term93 n)). Qed.
Lemma lem137501 : term103 = term90.
Proof. exact (fun_ext (fun n : nat => @lem137500 n)). Qed.
Lemma lem137502 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem137503 : term104 = term105.
Proof. exact (MK_COMB (@lem137502) (@lem137501)). Qed.
Lemma lem137504 : term88 = term106.
Proof. exact (MK_COMB (@lem137499) (@lem137503)). Qed.
Lemma lem137505 : (term87 = term88) = (term81 = term106).
Proof. exact (MK_COMB (@lem137493) (@lem137504)). Qed.
Lemma lem137506 : term81 = term106.
Proof. exact (EQ_MP (@lem137505) (@lem137483)). Qed.
Lemma lem137587 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem137590 : term82 = term107.
Proof. exact (MK_COMB (@lem137587) (@lem137506)). Qed.
Lemma lem137591 : term25 = term107.
Proof. exact (TRANS (@lem137479) (@lem137590)). Qed.
Lemma lem137592 (h1 : term25) : term107.
Proof. exact (EQ_MP (@lem137591) (@lem137394 h1)). Qed.
Lemma lem137607 (m : nat) (n : nat) : (((Nat.sub m n) = (NUMERAL 0)) = (Peano.le m n)) = (term108 m n).
Proof. exact (@lem17784 ((Nat.sub m n) = (NUMERAL 0)) (Peano.le m n)). Qed.
Lemma lem137608 (m : nat) : (term46 m) = (term109 m).
Proof. exact (fun_ext (fun n : nat => @lem137607 m n)). Qed.
Lemma lem137609 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem137610 (m : nat) : (term47 m) = (term110 m).
Proof. exact (MK_COMB (@lem137609) (@lem137608 m)). Qed.
Lemma lem137611 : term48 = term111.
Proof. exact (fun_ext (fun m : nat => @lem137610 m)). Qed.
Lemma lem137612 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem137613 : term30 = term112.
Proof. exact (MK_COMB (@lem137612) (@lem137611)). Qed.
Lemma lem137619 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term83 A P Q) = (term84 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem137620 (P : nat -> Prop) (Q : nat -> Prop) : (term85 P Q) = (term86 P Q).
Proof. exact (@lem137619 nat P Q). Qed.
Lemma lem137621 (m : nat) : (term113 m) = (term114 m).
Proof. exact (@lem137620 (term115 m) (term116 m)). Qed.
Lemma lem137622 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (eq_refl (term117 m n)). Qed.
Lemma lem137623 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem137624 (m : nat) (n : nat) : (term119 m n) = (term120 m n).
Proof. exact (MK_COMB (@lem137623) (@lem137622 m n)). Qed.
Lemma lem137625 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (eq_refl (term121 m n)). Qed.
Lemma lem137626 (m : nat) (n : nat) : (term123 m n) = (term108 m n).
Proof. exact (MK_COMB (@lem137624 m n) (@lem137625 m n)). Qed.
Lemma lem137627 (m : nat) : (term124 m) = (term109 m).
Proof. exact (fun_ext (fun n : nat => @lem137626 m n)). Qed.
Lemma lem137628 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem137629 (m : nat) : (term113 m) = (term110 m).
Proof. exact (MK_COMB (@lem137628) (@lem137627 m)). Qed.
Lemma lem137630 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem137631 (m : nat) : (term125 m) = (term126 m).
Proof. exact (MK_COMB (@lem137630) (@lem137629 m)). Qed.
Lemma lem137632 (m : nat) (n : nat) : (term117 m n) = (term118 m n).
Proof. exact (eq_refl (term117 m n)). Qed.
Lemma lem137633 (m : nat) : (term127 m) = (term115 m).
Proof. exact (fun_ext (fun n : nat => @lem137632 m n)). Qed.
Lemma lem137634 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem137635 (m : nat) : (term128 m) = (term129 m).
Proof. exact (MK_COMB (@lem137634) (@lem137633 m)). Qed.
Lemma lem137636 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem137637 (m : nat) : (term130 m) = (term131 m).
Proof. exact (MK_COMB (@lem137636) (@lem137635 m)). Qed.
Lemma lem137638 (m : nat) (n : nat) : (term121 m n) = (term122 m n).
Proof. exact (eq_refl (term121 m n)). Qed.
Lemma lem137639 (m : nat) : (term132 m) = (term116 m).
Proof. exact (fun_ext (fun n : nat => @lem137638 m n)). Qed.
Lemma lem137640 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem137641 (m : nat) : (term133 m) = (term134 m).
Proof. exact (MK_COMB (@lem137640) (@lem137639 m)). Qed.
Lemma lem137642 (m : nat) : (term114 m) = (term135 m).
Proof. exact (MK_COMB (@lem137637 m) (@lem137641 m)). Qed.
Lemma lem137643 (m : nat) : ((term113 m) = (term114 m)) = ((term110 m) = (term135 m)).
Proof. exact (MK_COMB (@lem137631 m) (@lem137642 m)). Qed.
Lemma lem137644 (m : nat) : (term110 m) = (term135 m).
Proof. exact (EQ_MP (@lem137643 m) (@lem137621 m)). Qed.
Lemma lem137741 : term111 = term136.
Proof. exact (fun_ext (fun m : nat => @lem137644 m)). Qed.
Lemma lem137742 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem137743 : term112 = term137.
Proof. exact (MK_COMB (@lem137742) (@lem137741)). Qed.
Lemma lem137745 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term83 A P Q) = (term84 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem137746 (P : nat -> Prop) (Q : nat -> Prop) : (term85 P Q) = (term86 P Q).
Proof. exact (@lem137745 nat P Q). Qed.
Lemma lem137747 : term138 = term139.
Proof. exact (@lem137746 term140 term141). Qed.
Lemma lem137748 (m : nat) : (term142 m) = (term129 m).
Proof. exact (eq_refl (term142 m)). Qed.
Lemma lem137749 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem137750 (m : nat) : (term143 m) = (term131 m).
Proof. exact (MK_COMB (@lem137749) (@lem137748 m)). Qed.
Lemma lem137751 (m : nat) : (term144 m) = (term134 m).
Proof. exact (eq_refl (term144 m)). Qed.
Lemma lem137752 (m : nat) : (term145 m) = (term135 m).
Proof. exact (MK_COMB (@lem137750 m) (@lem137751 m)). Qed.
Lemma lem137753 : term146 = term136.
Proof. exact (fun_ext (fun m : nat => @lem137752 m)). Qed.
Lemma lem137754 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem137755 : term138 = term137.
Proof. exact (MK_COMB (@lem137754) (@lem137753)). Qed.
Lemma lem137756 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem137757 : term147 = term148.
Proof. exact (MK_COMB (@lem137756) (@lem137755)). Qed.
Lemma lem137758 (m : nat) : (term142 m) = (term129 m).
Proof. exact (eq_refl (term142 m)). Qed.
Lemma lem137759 : term149 = term140.
Proof. exact (fun_ext (fun m : nat => @lem137758 m)). Qed.
Lemma lem137760 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem137761 : term150 = term151.
Proof. exact (MK_COMB (@lem137760) (@lem137759)). Qed.
Lemma lem137762 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem137763 : term152 = term153.
Proof. exact (MK_COMB (@lem137762) (@lem137761)). Qed.
Lemma lem137764 (m : nat) : (term144 m) = (term134 m).
Proof. exact (eq_refl (term144 m)). Qed.
Lemma lem137765 : term154 = term141.
Proof. exact (fun_ext (fun m : nat => @lem137764 m)). Qed.
Lemma lem137766 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem137767 : term155 = term156.
Proof. exact (MK_COMB (@lem137766) (@lem137765)). Qed.
Lemma lem137768 : term139 = term157.
Proof. exact (MK_COMB (@lem137763) (@lem137767)). Qed.
Lemma lem137769 : (term138 = term139) = (term137 = term157).
Proof. exact (MK_COMB (@lem137757) (@lem137768)). Qed.
Lemma lem137770 : term137 = term157.
Proof. exact (EQ_MP (@lem137769) (@lem137747)). Qed.
Lemma lem137877 : term112 = term157.
Proof. exact (TRANS (@lem137743) (@lem137770)). Qed.
Lemma lem137878 : term30 = term157.
Proof. exact (TRANS (@lem137613) (@lem137877)). Qed.
Lemma lem137879 (h1 : term30) : term157.
Proof. exact (EQ_MP (@lem137878) (@lem137395 h1)). Qed.
Lemma lem137885 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem137979 (m : nat) (n : nat) (h1 : term15 m n) : term70 m n.
Proof. exact (EQ_MP (@lem137454 m n) (@lem137393 m n h1)). Qed.
Lemma lem137994 (n : nat) : (term72 n) = (term72 n).
Proof. exact (eq_refl (term72 n)). Qed.
Lemma lem137995 : term90 = term90.
Proof. exact (fun_ext (fun n : nat => @lem137994 n)). Qed.
Lemma lem137996 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem137997 : term105 = term105.
Proof. exact (MK_COMB (@lem137996) (@lem137995)). Qed.
Lemma lem138008 (n : nat) : (term75 n) = (term75 n).
Proof. exact (eq_refl (term75 n)). Qed.
Lemma lem138009 : term89 = term89.
Proof. exact (fun_ext (fun n : nat => @lem138008 n)). Qed.
Lemma lem138010 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem138011 : term100 = term100.
Proof. exact (MK_COMB (@lem138010) (@lem138009)). Qed.
Lemma lem138012 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem138013 : term102 = term102.
Proof. exact (MK_COMB (@lem138012) (@lem138011)). Qed.
Lemma lem138014 : term106 = term106.
Proof. exact (MK_COMB (@lem138013) (@lem137997)). Qed.
Lemma lem138021 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem138022 : term107 = term107.
Proof. exact (MK_COMB (@lem138021) (@lem138014)). Qed.
Lemma lem138023 (h1 : term25) : term107.
Proof. exact (EQ_MP (@lem138022) (@lem137592 h1)). Qed.
Lemma lem138044 (m : nat) (n : nat) : (term122 m n) = (term122 m n).
Proof. exact (eq_refl (term122 m n)). Qed.
Lemma lem138045 (m : nat) : (term116 m) = (term116 m).
Proof. exact (fun_ext (fun n : nat => @lem138044 m n)). Qed.
Lemma lem138046 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem138047 (m : nat) : (term134 m) = (term134 m).
Proof. exact (MK_COMB (@lem138046) (@lem138045 m)). Qed.
Lemma lem138048 : term141 = term141.
Proof. exact (fun_ext (fun m : nat => @lem138047 m)). Qed.
Lemma lem138049 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem138050 : term156 = term156.
Proof. exact (MK_COMB (@lem138049) (@lem138048)). Qed.
Lemma lem138071 (m : nat) (n : nat) : (term118 m n) = (term118 m n).
Proof. exact (eq_refl (term118 m n)). Qed.
Lemma lem138072 (m : nat) : (term115 m) = (term115 m).
Proof. exact (fun_ext (fun n : nat => @lem138071 m n)). Qed.
Lemma lem138073 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem138074 (m : nat) : (term129 m) = (term129 m).
Proof. exact (MK_COMB (@lem138073) (@lem138072 m)). Qed.
Lemma lem138075 : term140 = term140.
Proof. exact (fun_ext (fun m : nat => @lem138074 m)). Qed.
Lemma lem138076 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem138077 : term151 = term151.
Proof. exact (MK_COMB (@lem138076) (@lem138075)). Qed.
Lemma lem138078 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem138079 : term153 = term153.
Proof. exact (MK_COMB (@lem138078) (@lem138077)). Qed.
Lemma lem138080 : term157 = term157.
Proof. exact (MK_COMB (@lem138079) (@lem138050)). Qed.
Lemma lem138081 (h1 : term30) : term157.
Proof. exact (EQ_MP (@lem138080) (@lem137879 h1)). Qed.
Lemma lem138083 (h1 : term30) : term151.
Proof. exact (proj1 (@lem138081 h1)). Qed.
Lemma lem138088 (m : nat) (n : nat) (h1 : term66 m n) : term66 m n.
Proof. exact (h1). Qed.
Lemma lem138089 (m : nat) (n : nat) (h1 : term63 m n) : term63 m n.
Proof. exact (h1). Qed.
Lemma lem138090 (m : nat) (n : nat) (h1 : term66 m n) : term57 m n.
Proof. exact (proj2 (@lem138088 m n h1)). Qed.
Lemma lem138092 (m : nat) (n : nat) (h1 : term66 m n) : term53 m n.
Proof. exact (proj2 (@lem138090 m n h1)). Qed.
Lemma lem138100 (m : nat) (n : nat) (h1 : term63 m n) : term60 m n.
Proof. exact (proj2 (@lem138089 m n h1)). Qed.
Lemma lem138103 (m : nat) (n : nat) (h1 : term54 m n) : term54 m n.
Proof. exact (h1). Qed.
Lemma lem138113 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem138195 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem138277 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem138285 (m : nat) (n : nat) : (term118 m n) = (term118 m n).
Proof. exact (eq_refl (term118 m n)). Qed.
Lemma lem138286 (m : nat) : (term115 m) = (term115 m).
Proof. exact (fun_ext (fun n : nat => @lem138285 m n)). Qed.
Lemma lem138287 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem138288 (m : nat) : (term129 m) = (term129 m).
Proof. exact (MK_COMB (@lem138287) (@lem138286 m)). Qed.
Lemma lem138289 : term140 = term140.
Proof. exact (fun_ext (fun m : nat => @lem138288 m)). Qed.
Lemma lem138290 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem138292 : term151 = term151.
Proof. exact (MK_COMB (@lem138290) (@lem138289)). Qed.
Lemma lem138293 (h1 : term30) : term151.
Proof. exact (EQ_MP (@lem138292) (@lem138083 h1)). Qed.
Lemma lem138347 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem138351 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem138359 (m : nat) (n : nat) : (term118 m n) = (term118 m n).
Proof. exact (eq_refl (term118 m n)). Qed.
Lemma lem138360 (m : nat) : (term115 m) = (term115 m).
Proof. exact (fun_ext (fun n : nat => @lem138359 m n)). Qed.
Lemma lem138361 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem138362 (m : nat) : (term129 m) = (term129 m).
Proof. exact (MK_COMB (@lem138361) (@lem138360 m)). Qed.
Lemma lem138363 : term140 = term140.
Proof. exact (fun_ext (fun m : nat => @lem138362 m)). Qed.
Lemma lem138364 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem138366 : term151 = term151.
Proof. exact (MK_COMB (@lem138364) (@lem138363)). Qed.
Lemma lem138367 (h1 : term30) : term151.
Proof. exact (EQ_MP (@lem138366) (@lem138083 h1)). Qed.
Lemma lem138429 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem138437 (m : nat) (n : nat) : (term118 m n) = (term118 m n).
Proof. exact (eq_refl (term118 m n)). Qed.
Lemma lem138438 (m : nat) : (term115 m) = (term115 m).
Proof. exact (fun_ext (fun n : nat => @lem138437 m n)). Qed.
Lemma lem138439 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem138440 (m : nat) : (term129 m) = (term129 m).
Proof. exact (MK_COMB (@lem138439) (@lem138438 m)). Qed.
Lemma lem138441 : term140 = term140.
Proof. exact (fun_ext (fun m : nat => @lem138440 m)). Qed.
Lemma lem138442 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem138444 : term151 = term151.
Proof. exact (MK_COMB (@lem138442) (@lem138441)). Qed.
Lemma lem138445 (h1 : term30) : term151.
Proof. exact (EQ_MP (@lem138444) (@lem138083 h1)). Qed.
Lemma lem138540 (_2781 : nat) (h1 : term30) : term142 _2781.
Proof. exact (@lem138293 h1 _2781). Qed.
Lemma lem138541 (_2781 : nat) : (term142 _2781) = (term129 _2781).
Proof. exact (eq_refl (term142 _2781)). Qed.
Lemma lem138542 (_2781 : nat) (h1 : term30) : term129 _2781.
Proof. exact (EQ_MP (@lem138541 _2781) (@lem138540 _2781 h1)). Qed.
Lemma lem138543 (_2781 : nat) (_2782 : nat) (h1 : term30) : term117 _2781 _2782.
Proof. exact (@lem138542 _2781 h1 _2782). Qed.
Lemma lem138544 (_2781 : nat) (_2782 : nat) : (term117 _2781 _2782) = (term118 _2781 _2782).
Proof. exact (eq_refl (term117 _2781 _2782)). Qed.
Lemma lem138558 (_2787 : nat) (h1 : term30) : term142 _2787.
Proof. exact (@lem138367 h1 _2787). Qed.
Lemma lem138559 (_2787 : nat) : (term142 _2787) = (term129 _2787).
Proof. exact (eq_refl (term142 _2787)). Qed.
Lemma lem138560 (_2787 : nat) (h1 : term30) : term129 _2787.
Proof. exact (EQ_MP (@lem138559 _2787) (@lem138558 _2787 h1)). Qed.
Lemma lem138561 (_2787 : nat) (_2788 : nat) (h1 : term30) : term117 _2787 _2788.
Proof. exact (@lem138560 _2787 h1 _2788). Qed.
Lemma lem138562 (_2787 : nat) (_2788 : nat) : (term117 _2787 _2788) = (term118 _2787 _2788).
Proof. exact (eq_refl (term117 _2787 _2788)). Qed.
Lemma lem138576 (_2793 : nat) (h1 : term30) : term142 _2793.
Proof. exact (@lem138445 h1 _2793). Qed.
Lemma lem138577 (_2793 : nat) : (term142 _2793) = (term129 _2793).
Proof. exact (eq_refl (term142 _2793)). Qed.
Lemma lem138578 (_2793 : nat) (h1 : term30) : term129 _2793.
Proof. exact (EQ_MP (@lem138577 _2793) (@lem138576 _2793 h1)). Qed.
Lemma lem138579 (_2793 : nat) (_2794 : nat) (h1 : term30) : term117 _2793 _2794.
Proof. exact (@lem138578 _2793 h1 _2794). Qed.
Lemma lem138580 (_2793 : nat) (_2794 : nat) : (term117 _2793 _2794) = (term118 _2793 _2794).
Proof. exact (eq_refl (term117 _2793 _2794)). Qed.
Lemma lem138595 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem138625 (m : nat) (n : nat) (h1 : term66 m n) : term10 m n.
Proof. exact (proj1 (@lem138090 m n h1)). Qed.
Lemma lem138631 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem138661 (m : nat) (n : nat) (h1 : term66 m n) : term10 m n.
Proof. exact (proj1 (@lem138090 m n h1)). Qed.
Lemma lem138667 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem138673 (_2781 : nat) (_2782 : nat) (h1 : term30) : term118 _2781 _2782.
Proof. exact (EQ_MP (@lem138544 _2781 _2782) (@lem138543 _2781 _2782 h1)). Qed.
Lemma lem138695 (m : nat) (n : nat) (h1 : term63 m n) : term158 m n.
Proof. exact (proj1 (@lem138089 m n h1)). Qed.
Lemma lem138697 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem138699 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem138705 (_2787 : nat) (_2788 : nat) (h1 : term30) : term118 _2787 _2788.
Proof. exact (EQ_MP (@lem138562 _2787 _2788) (@lem138561 _2787 _2788 h1)). Qed.
Lemma lem138727 (m : nat) (n : nat) (h1 : term63 m n) : term158 m n.
Proof. exact (proj1 (@lem138089 m n h1)). Qed.
Lemma lem138733 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem138739 (_2793 : nat) (_2794 : nat) (h1 : term30) : term118 _2793 _2794.
Proof. exact (EQ_MP (@lem138580 _2793 _2794) (@lem138579 _2793 _2794 h1)). Qed.
Lemma lem138761 (m : nat) (n : nat) (h1 : term63 m n) : term158 m n.
Proof. exact (proj1 (@lem138089 m n h1)). Qed.
Lemma lem138831 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem138832 (m : nat) (n : nat) (h1 : Peano.le m n) : term159 m n.
Proof. exact (fun h0 : term10 m n => @lem138831 m n h1). Qed.
Lemma lem138834 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem138835 (m : nat) (n : nat) : (term159 m n) = (Peano.le m n).
Proof. exact (@lem138834 (Peano.le m n)). Qed.
Lemma lem138836 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (EQ_MP (@lem138835 m n) (@lem138832 m n h1)). Qed.
Lemma lem138839 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem138841 (m : nat) (n : nat) : (term10 m n) = (term161 m n).
Proof. exact (@lem138839 (Peano.le m n)). Qed.
Lemma lem138844 (m : nat) (n : nat) (h1 : term66 m n) : term161 m n.
Proof. exact (EQ_MP (@lem138841 m n) (@lem138625 m n h1)). Qed.
Lemma lem138847 (m : nat) (n : nat) (h1 : term66 m n) (h2 : Peano.le m n) : False.
Proof. exact (@lem138844 m n h1 (@lem138836 m n h2)). Qed.
Lemma lem138848 (m : nat) (n : nat) (h1 : term66 m n) (h2 : Peano.le m n) : term162.
Proof. exact (fun h0 : ~ False => @lem138847 m n h1 h2). Qed.
Lemma lem138850 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem138851 : term162 = False.
Proof. exact (@lem138850 False). Qed.
Lemma lem138852 (m : nat) (n : nat) (h1 : term66 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem138851) (@lem138848 m n h1 h2)). Qed.
Lemma lem138918 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem138919 (m : nat) (n : nat) (h1 : Peano.le m n) : term159 m n.
Proof. exact (fun h0 : term10 m n => @lem138918 m n h1). Qed.
Lemma lem138921 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem138922 (m : nat) (n : nat) : (term159 m n) = (Peano.le m n).
Proof. exact (@lem138921 (Peano.le m n)). Qed.
Lemma lem138923 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (EQ_MP (@lem138922 m n) (@lem138919 m n h1)). Qed.
Lemma lem138926 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem138928 (m : nat) (n : nat) : (term10 m n) = (term161 m n).
Proof. exact (@lem138926 (Peano.le m n)). Qed.
Lemma lem138931 (m : nat) (n : nat) (h1 : term66 m n) : term161 m n.
Proof. exact (EQ_MP (@lem138928 m n) (@lem138661 m n h1)). Qed.
Lemma lem138934 (m : nat) (n : nat) (h1 : term66 m n) (h2 : Peano.le m n) : False.
Proof. exact (@lem138931 m n h1 (@lem138923 m n h2)). Qed.
Lemma lem138935 (m : nat) (n : nat) (h1 : term66 m n) (h2 : Peano.le m n) : term162.
Proof. exact (fun h0 : ~ False => @lem138934 m n h1 h2). Qed.
Lemma lem138937 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem138938 : term162 = False.
Proof. exact (@lem138937 False). Qed.
Lemma lem138939 (m : nat) (n : nat) (h1 : term66 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem138938) (@lem138935 m n h1 h2)). Qed.
Lemma lem138940 : Coq.Arith.PeanoNat.Nat.Even = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Even). Qed.
Lemma lem138941 (_2827 : nat) (_2828 : nat) (h1 : _2827 = _2828) : _2827 = _2828.
Proof. exact (h1). Qed.
Lemma lem138942 (_2827 : nat) (_2828 : nat) (h1 : _2827 = _2828) : (Coq.Arith.PeanoNat.Nat.Even _2827) = (Coq.Arith.PeanoNat.Nat.Even _2828).
Proof. exact (MK_COMB (@lem138940) (@lem138941 _2827 _2828 h1)). Qed.
Lemma lem138944 (b : Prop) (a : Prop) : term163 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem138945 (_2828 : nat) (_2827 : nat) : term164 _2828 _2827.
Proof. exact (@lem138944 (Coq.Arith.PeanoNat.Nat.Even _2828) (Coq.Arith.PeanoNat.Nat.Even _2827)). Qed.
Lemma lem138946 (_2827 : nat) (_2828 : nat) (h1 : _2827 = _2828) : term165 _2828 _2827.
Proof. exact (@lem138945 _2828 _2827 (@lem138942 _2827 _2828 h1)). Qed.
Lemma lem138947 (_2828 : nat) (_2827 : nat) : term166 _2828 _2827.
Proof. exact (fun h0 : _2827 = _2828 => @lem138946 _2827 _2828 h0). Qed.
Lemma lem138949 (a : Prop) (b : Prop) : (a -> b) = (term167 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem138950 (_2828 : nat) (_2827 : nat) : (term166 _2828 _2827) = (term168 _2828 _2827).
Proof. exact (@lem138949 (_2827 = _2828) (term165 _2828 _2827)). Qed.
Lemma lem138951 (_2828 : nat) (_2827 : nat) : term168 _2828 _2827.
Proof. exact (EQ_MP (@lem138950 _2828 _2827) (@lem138947 _2828 _2827)). Qed.
Lemma lem139003 (x : nat) (y : nat) (z : nat) : term169 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem139005 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem139006 (m : nat) (n : nat) (h1 : Peano.le m n) : term159 m n.
Proof. exact (fun h0 : term10 m n => @lem139005 m n h1). Qed.
Lemma lem139008 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem139009 (m : nat) (n : nat) : (term159 m n) = (Peano.le m n).
Proof. exact (@lem139008 (Peano.le m n)). Qed.
Lemma lem139010 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (EQ_MP (@lem139009 m n) (@lem139006 m n h1)). Qed.
Lemma lem139012 (b : Prop) (a : Prop) : (a \/ b) = (term170 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem139013 (_2781 : nat) (_2782 : nat) : (term118 _2781 _2782) = (term171 _2781 _2782).
Proof. exact (@lem139012 (term10 _2781 _2782) ((Nat.sub _2781 _2782) = (NUMERAL 0))). Qed.
Lemma lem139015 (a : Prop) : (term172 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem139016 (_2781 : nat) (_2782 : nat) : (term173 _2781 _2782) = (Peano.le _2781 _2782).
Proof. exact (@lem139015 (Peano.le _2781 _2782)). Qed.
Lemma lem139017 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem139018 (_2781 : nat) (_2782 : nat) : (term174 _2781 _2782) = (term36 _2781 _2782).
Proof. exact (MK_COMB (@lem139017) (@lem139016 _2781 _2782)). Qed.
Lemma lem139019 (_2781 : nat) (_2782 : nat) : ((Nat.sub _2781 _2782) = (NUMERAL 0)) = ((Nat.sub _2781 _2782) = (NUMERAL 0)).
Proof. exact (eq_refl ((Nat.sub _2781 _2782) = (NUMERAL 0))). Qed.
Lemma lem139020 (_2781 : nat) (_2782 : nat) : (term171 _2781 _2782) = (term175 _2781 _2782).
Proof. exact (MK_COMB (@lem139018 _2781 _2782) (@lem139019 _2781 _2782)). Qed.
Lemma lem139021 (_2781 : nat) (_2782 : nat) : (term118 _2781 _2782) = (term175 _2781 _2782).
Proof. exact (TRANS (@lem139013 _2781 _2782) (@lem139020 _2781 _2782)). Qed.
Lemma lem139024 (_2781 : nat) (_2782 : nat) (h1 : term30) : term175 _2781 _2782.
Proof. exact (EQ_MP (@lem139021 _2781 _2782) (@lem138673 _2781 _2782 h1)). Qed.
Lemma lem139025 (m : nat) (n : nat) (h1 : term30) : term175 m n.
Proof. exact (@lem139024 m n h1). Qed.
Lemma lem139028 (m : nat) (n : nat) (h1 : term30) (h2 : Peano.le m n) : (Nat.sub m n) = (NUMERAL 0).
Proof. exact (@lem139025 m n h1 (@lem139010 m n h2)). Qed.
Lemma lem139029 (m : nat) (n : nat) (h1 : term30) (h2 : Peano.le m n) : term176 m n.
Proof. exact (fun h0 : term177 m n => @lem139028 m n h1 h2). Qed.
Lemma lem139031 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem139032 (m : nat) (n : nat) : (term176 m n) = ((Nat.sub m n) = (NUMERAL 0)).
Proof. exact (@lem139031 ((Nat.sub m n) = (NUMERAL 0))). Qed.
Lemma lem139033 (m : nat) (n : nat) (h1 : term30) (h2 : Peano.le m n) : (Nat.sub m n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem139032 m n) (@lem139029 m n h1 h2)). Qed.
Lemma lem139035 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem139036 (m : nat) (n : nat) : (Nat.sub m n) = (Nat.sub m n).
Proof. exact (@lem139035 (Nat.sub m n)). Qed.
Lemma lem139037 (m : nat) (n : nat) : term178 m n.
Proof. exact (fun h0 : term179 m n => @lem139036 m n). Qed.
Lemma lem139039 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem139040 (m : nat) (n : nat) : (term178 m n) = ((Nat.sub m n) = (Nat.sub m n)).
Proof. exact (@lem139039 ((Nat.sub m n) = (Nat.sub m n))). Qed.
Lemma lem139041 (m : nat) (n : nat) : (Nat.sub m n) = (Nat.sub m n).
Proof. exact (EQ_MP (@lem139040 m n) (@lem139037 m n)). Qed.
Lemma lem139059 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem139060 (y : nat) (x : nat) (z : nat) : (term180 x y z) = (term181 y x z).
Proof. exact (@lem139059 (y = z) (term182 x z)). Qed.
Lemma lem139070 (x : nat) (y : nat) : (term183 x y) = (term183 x y).
Proof. exact (eq_refl (term183 x y)). Qed.
Lemma lem139071 (y : nat) (x : nat) (z : nat) : (term169 x y z) = (term184 y x z).
Proof. exact (MK_COMB (@lem139070 x y) (@lem139060 y x z)). Qed.
Lemma lem139075 (q : Prop) (p : Prop) (r : Prop) : (term185 p q r) = (term185 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem139076 (y : nat) (x : nat) (z : nat) : (term184 y x z) = (term186 y x z).
Proof. exact (@lem139075 (y = z) (term182 x y) (term182 x z)). Qed.
Lemma lem139098 (y : nat) (x : nat) (z : nat) : (term169 x y z) = (term186 y x z).
Proof. exact (TRANS (@lem139071 y x z) (@lem139076 y x z)). Qed.
Lemma lem139099 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem139100 (y : nat) (x : nat) (z : nat) : (term187 x y z) = (term188 y x z).
Proof. exact (MK_COMB (@lem139099) (@lem139098 y x z)). Qed.
Lemma lem139122 (y : nat) (x : nat) (z : nat) : (term186 y x z) = (term186 y x z).
Proof. exact (eq_refl (term186 y x z)). Qed.
Lemma lem139123 (y : nat) (x : nat) (z : nat) : ((term169 x y z) = (term186 y x z)) = ((term186 y x z) = (term186 y x z)).
Proof. exact (MK_COMB (@lem139100 y x z) (@lem139122 y x z)). Qed.
Lemma lem139125 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem139126 (x : Prop) : (x = x) = True.
Proof. exact (@lem139125 Prop x). Qed.
Lemma lem139127 (y : nat) (x : nat) (z : nat) : ((term186 y x z) = (term186 y x z)) = True.
Proof. exact (@lem139126 (term186 y x z)). Qed.
Lemma lem139128 (y : nat) (x : nat) (z : nat) : ((term169 x y z) = (term186 y x z)) = True.
Proof. exact (TRANS (@lem139123 y x z) (@lem139127 y x z)). Qed.
Lemma lem139129 (y : nat) (x : nat) (z : nat) : True = ((term169 x y z) = (term186 y x z)).
Proof. exact (SYM (@lem139128 y x z)). Qed.
Lemma lem139130 (y : nat) (x : nat) (z : nat) : (term169 x y z) = (term186 y x z).
Proof. exact (EQ_MP (@lem139129 y x z) (@lem0)). Qed.
Lemma lem139131 (y : nat) (x : nat) (z : nat) : term186 y x z.
Proof. exact (EQ_MP (@lem139130 y x z) (@lem139003 x y z)). Qed.
Lemma lem139133 (b : Prop) (a : Prop) : (a \/ b) = (term170 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem139134 (x : nat) (y : nat) (z : nat) : (term186 y x z) = (term189 x y z).
Proof. exact (@lem139133 (term190 y x z) (y = z)). Qed.
Lemma lem139136 (a : Prop) (b : Prop) : (term191 a b) = (term192 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem139137 (y : nat) (x : nat) (z : nat) : (term193 y x z) = (term194 y x z).
Proof. exact (@lem139136 (term182 x y) (term182 x z)). Qed.
Lemma lem139139 (a : Prop) : (term172 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem139140 (x : nat) (y : nat) : (term195 x y) = (x = y).
Proof. exact (@lem139139 (x = y)). Qed.
Lemma lem139141 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem139142 (x : nat) (y : nat) : (term196 x y) = (term197 x y).
Proof. exact (MK_COMB (@lem139141) (@lem139140 x y)). Qed.
Lemma lem139144 (a : Prop) : (term172 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem139145 (x : nat) (z : nat) : (term195 x z) = (x = z).
Proof. exact (@lem139144 (x = z)). Qed.
Lemma lem139146 (y : nat) (x : nat) (z : nat) : (term194 y x z) = (term198 y x z).
Proof. exact (MK_COMB (@lem139142 x y) (@lem139145 x z)). Qed.
Lemma lem139147 (y : nat) (x : nat) (z : nat) : (term193 y x z) = (term198 y x z).
Proof. exact (TRANS (@lem139137 y x z) (@lem139146 y x z)). Qed.
Lemma lem139148 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem139149 (y : nat) (x : nat) (z : nat) : (term199 y x z) = (term200 y x z).
Proof. exact (MK_COMB (@lem139148) (@lem139147 y x z)). Qed.
Lemma lem139150 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem139151 (x : nat) (y : nat) (z : nat) : (term189 x y z) = (term201 x y z).
Proof. exact (MK_COMB (@lem139149 y x z) (@lem139150 y z)). Qed.
Lemma lem139152 (x : nat) (y : nat) (z : nat) : (term186 y x z) = (term201 x y z).
Proof. exact (TRANS (@lem139134 x y z) (@lem139151 x y z)). Qed.
Lemma lem139154 (m : nat) (n : nat) (h1 : term30) (h2 : Peano.le m n) : term202 m n.
Proof. exact (conj (@lem139033 m n h1 h2) (@lem139041 m n)). Qed.
Lemma lem139156 (x : nat) (y : nat) (z : nat) : term201 x y z.
Proof. exact (EQ_MP (@lem139152 x y z) (@lem139131 y x z)). Qed.
Lemma lem139157 (m : nat) (n : nat) : term203 m n.
Proof. exact (@lem139156 (Nat.sub m n) (NUMERAL 0) (Nat.sub m n)). Qed.
Lemma lem139160 (m : nat) (n : nat) (h1 : term30) (h2 : Peano.le m n) : (NUMERAL 0) = (Nat.sub m n).
Proof. exact (@lem139157 m n (@lem139154 m n h1 h2)). Qed.
Lemma lem139161 (m : nat) (n : nat) (h1 : term30) (h2 : Peano.le m n) : term204 m n.
Proof. exact (fun h0 : term205 m n => @lem139160 m n h1 h2). Qed.
Lemma lem139163 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem139164 (m : nat) (n : nat) : (term204 m n) = ((NUMERAL 0) = (Nat.sub m n)).
Proof. exact (@lem139163 ((NUMERAL 0) = (Nat.sub m n))). Qed.
Lemma lem139165 (m : nat) (n : nat) (h1 : term30) (h2 : Peano.le m n) : (NUMERAL 0) = (Nat.sub m n).
Proof. exact (EQ_MP (@lem139164 m n) (@lem139161 m n h1 h2)). Qed.
Lemma lem139167 (h1 : term25) : term20.
Proof. exact (proj1 (@lem138023 h1)). Qed.
Lemma lem139168 (h1 : term25) : term206.
Proof. exact (fun h0 : term207 => @lem139167 h1). Qed.
Lemma lem139170 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem139171 : term206 = term20.
Proof. exact (@lem139170 term20). Qed.
Lemma lem139172 (h1 : term25) : term20.
Proof. exact (EQ_MP (@lem139171) (@lem139168 h1)). Qed.
Lemma lem139178 (q : Prop) (p : Prop) (r : Prop) : (term185 p q r) = (term185 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem139179 (_2828 : nat) (_2827 : nat) : (term168 _2828 _2827) = (term208 _2828 _2827).
Proof. exact (@lem139178 (Coq.Arith.PeanoNat.Nat.Even _2828) (term182 _2827 _2828) (term50 _2827)). Qed.
Lemma lem139197 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem139198 (_2828 : nat) (_2827 : nat) : (term209 _2828 _2827) = (term210 _2828 _2827).
Proof. exact (MK_COMB (@lem139197) (@lem139179 _2828 _2827)). Qed.
Lemma lem139216 (_2828 : nat) (_2827 : nat) : (term208 _2828 _2827) = (term208 _2828 _2827).
Proof. exact (eq_refl (term208 _2828 _2827)). Qed.
Lemma lem139217 (_2828 : nat) (_2827 : nat) : ((term168 _2828 _2827) = (term208 _2828 _2827)) = ((term208 _2828 _2827) = (term208 _2828 _2827)).
Proof. exact (MK_COMB (@lem139198 _2828 _2827) (@lem139216 _2828 _2827)). Qed.
Lemma lem139219 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem139220 (x : Prop) : (x = x) = True.
Proof. exact (@lem139219 Prop x). Qed.
Lemma lem139221 (_2828 : nat) (_2827 : nat) : ((term208 _2828 _2827) = (term208 _2828 _2827)) = True.
Proof. exact (@lem139220 (term208 _2828 _2827)). Qed.
Lemma lem139222 (_2828 : nat) (_2827 : nat) : ((term168 _2828 _2827) = (term208 _2828 _2827)) = True.
Proof. exact (TRANS (@lem139217 _2828 _2827) (@lem139221 _2828 _2827)). Qed.
Lemma lem139223 (_2828 : nat) (_2827 : nat) : True = ((term168 _2828 _2827) = (term208 _2828 _2827)).
Proof. exact (SYM (@lem139222 _2828 _2827)). Qed.
Lemma lem139224 (_2828 : nat) (_2827 : nat) : (term168 _2828 _2827) = (term208 _2828 _2827).
Proof. exact (EQ_MP (@lem139223 _2828 _2827) (@lem0)). Qed.
Lemma lem139225 (_2828 : nat) (_2827 : nat) : term208 _2828 _2827.
Proof. exact (EQ_MP (@lem139224 _2828 _2827) (@lem138951 _2828 _2827)). Qed.
Lemma lem139227 (b : Prop) (a : Prop) : (a \/ b) = (term170 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem139228 (_2827 : nat) (_2828 : nat) : (term208 _2828 _2827) = (term211 _2827 _2828).
Proof. exact (@lem139227 (term212 _2828 _2827) (Coq.Arith.PeanoNat.Nat.Even _2828)). Qed.
Lemma lem139230 (a : Prop) (b : Prop) : (term191 a b) = (term192 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem139231 (_2828 : nat) (_2827 : nat) : (term213 _2828 _2827) = (term214 _2828 _2827).
Proof. exact (@lem139230 (term182 _2827 _2828) (term50 _2827)). Qed.
Lemma lem139233 (a : Prop) : (term172 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem139234 (_2827 : nat) (_2828 : nat) : (term195 _2827 _2828) = (_2827 = _2828).
Proof. exact (@lem139233 (_2827 = _2828)). Qed.
Lemma lem139235 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem139236 (_2827 : nat) (_2828 : nat) : (term196 _2827 _2828) = (term197 _2827 _2828).
Proof. exact (MK_COMB (@lem139235) (@lem139234 _2827 _2828)). Qed.
Lemma lem139238 (a : Prop) : (term172 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem139239 (_2827 : nat) : (term71 _2827) = (Coq.Arith.PeanoNat.Nat.Even _2827).
Proof. exact (@lem139238 (Coq.Arith.PeanoNat.Nat.Even _2827)). Qed.
Lemma lem139240 (_2828 : nat) (_2827 : nat) : (term214 _2828 _2827) = (term215 _2828 _2827).
Proof. exact (MK_COMB (@lem139236 _2827 _2828) (@lem139239 _2827)). Qed.
Lemma lem139241 (_2828 : nat) (_2827 : nat) : (term213 _2828 _2827) = (term215 _2828 _2827).
Proof. exact (TRANS (@lem139231 _2828 _2827) (@lem139240 _2828 _2827)). Qed.
Lemma lem139242 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem139243 (_2828 : nat) (_2827 : nat) : (term216 _2828 _2827) = (term217 _2828 _2827).
Proof. exact (MK_COMB (@lem139242) (@lem139241 _2828 _2827)). Qed.
Lemma lem139244 (_2828 : nat) : (Coq.Arith.PeanoNat.Nat.Even _2828) = (Coq.Arith.PeanoNat.Nat.Even _2828).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Even _2828)). Qed.
Lemma lem139245 (_2827 : nat) (_2828 : nat) : (term211 _2827 _2828) = (term218 _2827 _2828).
Proof. exact (MK_COMB (@lem139243 _2828 _2827) (@lem139244 _2828)). Qed.
Lemma lem139246 (_2827 : nat) (_2828 : nat) : (term208 _2828 _2827) = (term218 _2827 _2828).
Proof. exact (TRANS (@lem139228 _2827 _2828) (@lem139245 _2827 _2828)). Qed.
Lemma lem139248 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : Peano.le m n) : term219 m n.
Proof. exact (conj (@lem139165 m n h1 h3) (@lem139172 h2)). Qed.
Lemma lem139250 (_2827 : nat) (_2828 : nat) : term218 _2827 _2828.
Proof. exact (EQ_MP (@lem139246 _2827 _2828) (@lem139225 _2828 _2827)). Qed.
Lemma lem139251 (m : nat) (n : nat) : term220 m n.
Proof. exact (@lem139250 (NUMERAL 0) (Nat.sub m n)). Qed.
Lemma lem139254 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : Peano.le m n) : term12 m n.
Proof. exact (@lem139251 m n (@lem139248 m n h1 h2 h3)). Qed.
Lemma lem139255 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : Peano.le m n) : term221 m n.
Proof. exact (fun h0 : term158 m n => @lem139254 m n h1 h2 h3). Qed.
Lemma lem139257 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem139258 (m : nat) (n : nat) : (term221 m n) = (term12 m n).
Proof. exact (@lem139257 (term12 m n)). Qed.
Lemma lem139259 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : Peano.le m n) : term12 m n.
Proof. exact (EQ_MP (@lem139258 m n) (@lem139255 m n h1 h2 h3)). Qed.
Lemma lem139262 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem139264 (m : nat) (n : nat) : (term158 m n) = (term222 m n).
Proof. exact (@lem139262 (term12 m n)). Qed.
Lemma lem139267 (m : nat) (n : nat) (h1 : term63 m n) : term222 m n.
Proof. exact (EQ_MP (@lem139264 m n) (@lem138695 m n h1)). Qed.
Lemma lem139270 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : False.
Proof. exact (@lem139267 m n h3 (@lem139259 m n h1 h2 h4)). Qed.
Lemma lem139271 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : term162.
Proof. exact (fun h0 : ~ False => @lem139270 m n h1 h2 h3 h4). Qed.
Lemma lem139273 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem139274 : term162 = False.
Proof. exact (@lem139273 False). Qed.
Lemma lem139275 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem139274) (@lem139271 m n h1 h2 h3 h4)). Qed.
Lemma lem139276 : Coq.Arith.PeanoNat.Nat.Even = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Even). Qed.
Lemma lem139277 (_2841 : nat) (_2842 : nat) (h1 : _2841 = _2842) : _2841 = _2842.
Proof. exact (h1). Qed.
Lemma lem139278 (_2841 : nat) (_2842 : nat) (h1 : _2841 = _2842) : (Coq.Arith.PeanoNat.Nat.Even _2841) = (Coq.Arith.PeanoNat.Nat.Even _2842).
Proof. exact (MK_COMB (@lem139276) (@lem139277 _2841 _2842 h1)). Qed.
Lemma lem139280 (b : Prop) (a : Prop) : term163 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem139281 (_2842 : nat) (_2841 : nat) : term164 _2842 _2841.
Proof. exact (@lem139280 (Coq.Arith.PeanoNat.Nat.Even _2842) (Coq.Arith.PeanoNat.Nat.Even _2841)). Qed.
Lemma lem139282 (_2841 : nat) (_2842 : nat) (h1 : _2841 = _2842) : term165 _2842 _2841.
Proof. exact (@lem139281 _2842 _2841 (@lem139278 _2841 _2842 h1)). Qed.
Lemma lem139283 (_2842 : nat) (_2841 : nat) : term166 _2842 _2841.
Proof. exact (fun h0 : _2841 = _2842 => @lem139282 _2841 _2842 h0). Qed.
Lemma lem139285 (a : Prop) (b : Prop) : (a -> b) = (term167 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem139286 (_2842 : nat) (_2841 : nat) : (term166 _2842 _2841) = (term168 _2842 _2841).
Proof. exact (@lem139285 (_2841 = _2842) (term165 _2842 _2841)). Qed.
Lemma lem139287 (_2842 : nat) (_2841 : nat) : term168 _2842 _2841.
Proof. exact (EQ_MP (@lem139286 _2842 _2841) (@lem139283 _2842 _2841)). Qed.
Lemma lem139339 (x : nat) (y : nat) (z : nat) : term169 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem139341 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem139342 (m : nat) (n : nat) (h1 : Peano.le m n) : term159 m n.
Proof. exact (fun h0 : term10 m n => @lem139341 m n h1). Qed.
Lemma lem139344 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem139345 (m : nat) (n : nat) : (term159 m n) = (Peano.le m n).
Proof. exact (@lem139344 (Peano.le m n)). Qed.
Lemma lem139346 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (EQ_MP (@lem139345 m n) (@lem139342 m n h1)). Qed.
Lemma lem139348 (b : Prop) (a : Prop) : (a \/ b) = (term170 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem139349 (_2787 : nat) (_2788 : nat) : (term118 _2787 _2788) = (term171 _2787 _2788).
Proof. exact (@lem139348 (term10 _2787 _2788) ((Nat.sub _2787 _2788) = (NUMERAL 0))). Qed.
Lemma lem139351 (a : Prop) : (term172 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem139352 (_2787 : nat) (_2788 : nat) : (term173 _2787 _2788) = (Peano.le _2787 _2788).
Proof. exact (@lem139351 (Peano.le _2787 _2788)). Qed.
Lemma lem139353 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem139354 (_2787 : nat) (_2788 : nat) : (term174 _2787 _2788) = (term36 _2787 _2788).
Proof. exact (MK_COMB (@lem139353) (@lem139352 _2787 _2788)). Qed.
Lemma lem139355 (_2787 : nat) (_2788 : nat) : ((Nat.sub _2787 _2788) = (NUMERAL 0)) = ((Nat.sub _2787 _2788) = (NUMERAL 0)).
Proof. exact (eq_refl ((Nat.sub _2787 _2788) = (NUMERAL 0))). Qed.
Lemma lem139356 (_2787 : nat) (_2788 : nat) : (term171 _2787 _2788) = (term175 _2787 _2788).
Proof. exact (MK_COMB (@lem139354 _2787 _2788) (@lem139355 _2787 _2788)). Qed.
Lemma lem139357 (_2787 : nat) (_2788 : nat) : (term118 _2787 _2788) = (term175 _2787 _2788).
Proof. exact (TRANS (@lem139349 _2787 _2788) (@lem139356 _2787 _2788)). Qed.
Lemma lem139360 (_2787 : nat) (_2788 : nat) (h1 : term30) : term175 _2787 _2788.
Proof. exact (EQ_MP (@lem139357 _2787 _2788) (@lem138705 _2787 _2788 h1)). Qed.
Lemma lem139361 (m : nat) (n : nat) (h1 : term30) : term175 m n.
Proof. exact (@lem139360 m n h1). Qed.
Lemma lem139364 (m : nat) (n : nat) (h1 : term30) (h2 : Peano.le m n) : (Nat.sub m n) = (NUMERAL 0).
Proof. exact (@lem139361 m n h1 (@lem139346 m n h2)). Qed.
Lemma lem139365 (m : nat) (n : nat) (h1 : term30) (h2 : Peano.le m n) : term176 m n.
Proof. exact (fun h0 : term177 m n => @lem139364 m n h1 h2). Qed.
Lemma lem139367 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem139368 (m : nat) (n : nat) : (term176 m n) = ((Nat.sub m n) = (NUMERAL 0)).
Proof. exact (@lem139367 ((Nat.sub m n) = (NUMERAL 0))). Qed.
Lemma lem139369 (m : nat) (n : nat) (h1 : term30) (h2 : Peano.le m n) : (Nat.sub m n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem139368 m n) (@lem139365 m n h1 h2)). Qed.
Lemma lem139371 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem139372 (m : nat) (n : nat) : (Nat.sub m n) = (Nat.sub m n).
Proof. exact (@lem139371 (Nat.sub m n)). Qed.
Lemma lem139373 (m : nat) (n : nat) : term178 m n.
Proof. exact (fun h0 : term179 m n => @lem139372 m n). Qed.
Lemma lem139375 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem139376 (m : nat) (n : nat) : (term178 m n) = ((Nat.sub m n) = (Nat.sub m n)).
Proof. exact (@lem139375 ((Nat.sub m n) = (Nat.sub m n))). Qed.
Lemma lem139377 (m : nat) (n : nat) : (Nat.sub m n) = (Nat.sub m n).
Proof. exact (EQ_MP (@lem139376 m n) (@lem139373 m n)). Qed.
Lemma lem139395 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem139396 (y : nat) (x : nat) (z : nat) : (term180 x y z) = (term181 y x z).
Proof. exact (@lem139395 (y = z) (term182 x z)). Qed.
Lemma lem139406 (x : nat) (y : nat) : (term183 x y) = (term183 x y).
Proof. exact (eq_refl (term183 x y)). Qed.
Lemma lem139407 (y : nat) (x : nat) (z : nat) : (term169 x y z) = (term184 y x z).
Proof. exact (MK_COMB (@lem139406 x y) (@lem139396 y x z)). Qed.
Lemma lem139411 (q : Prop) (p : Prop) (r : Prop) : (term185 p q r) = (term185 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem139412 (y : nat) (x : nat) (z : nat) : (term184 y x z) = (term186 y x z).
Proof. exact (@lem139411 (y = z) (term182 x y) (term182 x z)). Qed.
Lemma lem139434 (y : nat) (x : nat) (z : nat) : (term169 x y z) = (term186 y x z).
Proof. exact (TRANS (@lem139407 y x z) (@lem139412 y x z)). Qed.
Lemma lem139435 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem139436 (y : nat) (x : nat) (z : nat) : (term187 x y z) = (term188 y x z).
Proof. exact (MK_COMB (@lem139435) (@lem139434 y x z)). Qed.
Lemma lem139458 (y : nat) (x : nat) (z : nat) : (term186 y x z) = (term186 y x z).
Proof. exact (eq_refl (term186 y x z)). Qed.
Lemma lem139459 (y : nat) (x : nat) (z : nat) : ((term169 x y z) = (term186 y x z)) = ((term186 y x z) = (term186 y x z)).
Proof. exact (MK_COMB (@lem139436 y x z) (@lem139458 y x z)). Qed.
Lemma lem139461 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem139462 (x : Prop) : (x = x) = True.
Proof. exact (@lem139461 Prop x). Qed.
Lemma lem139463 (y : nat) (x : nat) (z : nat) : ((term186 y x z) = (term186 y x z)) = True.
Proof. exact (@lem139462 (term186 y x z)). Qed.
Lemma lem139464 (y : nat) (x : nat) (z : nat) : ((term169 x y z) = (term186 y x z)) = True.
Proof. exact (TRANS (@lem139459 y x z) (@lem139463 y x z)). Qed.
Lemma lem139465 (y : nat) (x : nat) (z : nat) : True = ((term169 x y z) = (term186 y x z)).
Proof. exact (SYM (@lem139464 y x z)). Qed.
Lemma lem139466 (y : nat) (x : nat) (z : nat) : (term169 x y z) = (term186 y x z).
Proof. exact (EQ_MP (@lem139465 y x z) (@lem0)). Qed.
Lemma lem139467 (y : nat) (x : nat) (z : nat) : term186 y x z.
Proof. exact (EQ_MP (@lem139466 y x z) (@lem139339 x y z)). Qed.
Lemma lem139469 (b : Prop) (a : Prop) : (a \/ b) = (term170 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem139470 (x : nat) (y : nat) (z : nat) : (term186 y x z) = (term189 x y z).
Proof. exact (@lem139469 (term190 y x z) (y = z)). Qed.
Lemma lem139472 (a : Prop) (b : Prop) : (term191 a b) = (term192 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem139473 (y : nat) (x : nat) (z : nat) : (term193 y x z) = (term194 y x z).
Proof. exact (@lem139472 (term182 x y) (term182 x z)). Qed.
Lemma lem139475 (a : Prop) : (term172 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem139476 (x : nat) (y : nat) : (term195 x y) = (x = y).
Proof. exact (@lem139475 (x = y)). Qed.
Lemma lem139477 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem139478 (x : nat) (y : nat) : (term196 x y) = (term197 x y).
Proof. exact (MK_COMB (@lem139477) (@lem139476 x y)). Qed.
Lemma lem139480 (a : Prop) : (term172 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem139481 (x : nat) (z : nat) : (term195 x z) = (x = z).
Proof. exact (@lem139480 (x = z)). Qed.
Lemma lem139482 (y : nat) (x : nat) (z : nat) : (term194 y x z) = (term198 y x z).
Proof. exact (MK_COMB (@lem139478 x y) (@lem139481 x z)). Qed.
Lemma lem139483 (y : nat) (x : nat) (z : nat) : (term193 y x z) = (term198 y x z).
Proof. exact (TRANS (@lem139473 y x z) (@lem139482 y x z)). Qed.
Lemma lem139484 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem139485 (y : nat) (x : nat) (z : nat) : (term199 y x z) = (term200 y x z).
Proof. exact (MK_COMB (@lem139484) (@lem139483 y x z)). Qed.
Lemma lem139486 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem139487 (x : nat) (y : nat) (z : nat) : (term189 x y z) = (term201 x y z).
Proof. exact (MK_COMB (@lem139485 y x z) (@lem139486 y z)). Qed.
Lemma lem139488 (x : nat) (y : nat) (z : nat) : (term186 y x z) = (term201 x y z).
Proof. exact (TRANS (@lem139470 x y z) (@lem139487 x y z)). Qed.
Lemma lem139490 (m : nat) (n : nat) (h1 : term30) (h2 : Peano.le m n) : term202 m n.
Proof. exact (conj (@lem139369 m n h1 h2) (@lem139377 m n)). Qed.
Lemma lem139492 (x : nat) (y : nat) (z : nat) : term201 x y z.
Proof. exact (EQ_MP (@lem139488 x y z) (@lem139467 y x z)). Qed.
Lemma lem139493 (m : nat) (n : nat) : term203 m n.
Proof. exact (@lem139492 (Nat.sub m n) (NUMERAL 0) (Nat.sub m n)). Qed.
Lemma lem139496 (m : nat) (n : nat) (h1 : term30) (h2 : Peano.le m n) : (NUMERAL 0) = (Nat.sub m n).
Proof. exact (@lem139493 m n (@lem139490 m n h1 h2)). Qed.
Lemma lem139497 (m : nat) (n : nat) (h1 : term30) (h2 : Peano.le m n) : term204 m n.
Proof. exact (fun h0 : term205 m n => @lem139496 m n h1 h2). Qed.
Lemma lem139499 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem139500 (m : nat) (n : nat) : (term204 m n) = ((NUMERAL 0) = (Nat.sub m n)).
Proof. exact (@lem139499 ((NUMERAL 0) = (Nat.sub m n))). Qed.
Lemma lem139501 (m : nat) (n : nat) (h1 : term30) (h2 : Peano.le m n) : (NUMERAL 0) = (Nat.sub m n).
Proof. exact (EQ_MP (@lem139500 m n) (@lem139497 m n h1 h2)). Qed.
Lemma lem139503 (h1 : term25) : term20.
Proof. exact (proj1 (@lem138023 h1)). Qed.
Lemma lem139504 (h1 : term25) : term206.
Proof. exact (fun h0 : term207 => @lem139503 h1). Qed.
Lemma lem139506 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem139507 : term206 = term20.
Proof. exact (@lem139506 term20). Qed.
Lemma lem139508 (h1 : term25) : term20.
Proof. exact (EQ_MP (@lem139507) (@lem139504 h1)). Qed.
Lemma lem139514 (q : Prop) (p : Prop) (r : Prop) : (term185 p q r) = (term185 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem139515 (_2842 : nat) (_2841 : nat) : (term168 _2842 _2841) = (term208 _2842 _2841).
Proof. exact (@lem139514 (Coq.Arith.PeanoNat.Nat.Even _2842) (term182 _2841 _2842) (term50 _2841)). Qed.
Lemma lem139533 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem139534 (_2842 : nat) (_2841 : nat) : (term209 _2842 _2841) = (term210 _2842 _2841).
Proof. exact (MK_COMB (@lem139533) (@lem139515 _2842 _2841)). Qed.
Lemma lem139552 (_2842 : nat) (_2841 : nat) : (term208 _2842 _2841) = (term208 _2842 _2841).
Proof. exact (eq_refl (term208 _2842 _2841)). Qed.
Lemma lem139553 (_2842 : nat) (_2841 : nat) : ((term168 _2842 _2841) = (term208 _2842 _2841)) = ((term208 _2842 _2841) = (term208 _2842 _2841)).
Proof. exact (MK_COMB (@lem139534 _2842 _2841) (@lem139552 _2842 _2841)). Qed.
Lemma lem139555 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem139556 (x : Prop) : (x = x) = True.
Proof. exact (@lem139555 Prop x). Qed.
Lemma lem139557 (_2842 : nat) (_2841 : nat) : ((term208 _2842 _2841) = (term208 _2842 _2841)) = True.
Proof. exact (@lem139556 (term208 _2842 _2841)). Qed.
Lemma lem139558 (_2842 : nat) (_2841 : nat) : ((term168 _2842 _2841) = (term208 _2842 _2841)) = True.
Proof. exact (TRANS (@lem139553 _2842 _2841) (@lem139557 _2842 _2841)). Qed.
Lemma lem139559 (_2842 : nat) (_2841 : nat) : True = ((term168 _2842 _2841) = (term208 _2842 _2841)).
Proof. exact (SYM (@lem139558 _2842 _2841)). Qed.
Lemma lem139560 (_2842 : nat) (_2841 : nat) : (term168 _2842 _2841) = (term208 _2842 _2841).
Proof. exact (EQ_MP (@lem139559 _2842 _2841) (@lem0)). Qed.
Lemma lem139561 (_2842 : nat) (_2841 : nat) : term208 _2842 _2841.
Proof. exact (EQ_MP (@lem139560 _2842 _2841) (@lem139287 _2842 _2841)). Qed.
Lemma lem139563 (b : Prop) (a : Prop) : (a \/ b) = (term170 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem139564 (_2841 : nat) (_2842 : nat) : (term208 _2842 _2841) = (term211 _2841 _2842).
Proof. exact (@lem139563 (term212 _2842 _2841) (Coq.Arith.PeanoNat.Nat.Even _2842)). Qed.
Lemma lem139566 (a : Prop) (b : Prop) : (term191 a b) = (term192 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem139567 (_2842 : nat) (_2841 : nat) : (term213 _2842 _2841) = (term214 _2842 _2841).
Proof. exact (@lem139566 (term182 _2841 _2842) (term50 _2841)). Qed.
Lemma lem139569 (a : Prop) : (term172 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem139570 (_2841 : nat) (_2842 : nat) : (term195 _2841 _2842) = (_2841 = _2842).
Proof. exact (@lem139569 (_2841 = _2842)). Qed.
Lemma lem139571 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem139572 (_2841 : nat) (_2842 : nat) : (term196 _2841 _2842) = (term197 _2841 _2842).
Proof. exact (MK_COMB (@lem139571) (@lem139570 _2841 _2842)). Qed.
Lemma lem139574 (a : Prop) : (term172 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem139575 (_2841 : nat) : (term71 _2841) = (Coq.Arith.PeanoNat.Nat.Even _2841).
Proof. exact (@lem139574 (Coq.Arith.PeanoNat.Nat.Even _2841)). Qed.
Lemma lem139576 (_2842 : nat) (_2841 : nat) : (term214 _2842 _2841) = (term215 _2842 _2841).
Proof. exact (MK_COMB (@lem139572 _2841 _2842) (@lem139575 _2841)). Qed.
Lemma lem139577 (_2842 : nat) (_2841 : nat) : (term213 _2842 _2841) = (term215 _2842 _2841).
Proof. exact (TRANS (@lem139567 _2842 _2841) (@lem139576 _2842 _2841)). Qed.
Lemma lem139578 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem139579 (_2842 : nat) (_2841 : nat) : (term216 _2842 _2841) = (term217 _2842 _2841).
Proof. exact (MK_COMB (@lem139578) (@lem139577 _2842 _2841)). Qed.
Lemma lem139580 (_2842 : nat) : (Coq.Arith.PeanoNat.Nat.Even _2842) = (Coq.Arith.PeanoNat.Nat.Even _2842).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Even _2842)). Qed.
Lemma lem139581 (_2841 : nat) (_2842 : nat) : (term211 _2841 _2842) = (term218 _2841 _2842).
Proof. exact (MK_COMB (@lem139579 _2842 _2841) (@lem139580 _2842)). Qed.
Lemma lem139582 (_2841 : nat) (_2842 : nat) : (term208 _2842 _2841) = (term218 _2841 _2842).
Proof. exact (TRANS (@lem139564 _2841 _2842) (@lem139581 _2841 _2842)). Qed.
Lemma lem139584 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : Peano.le m n) : term219 m n.
Proof. exact (conj (@lem139501 m n h1 h3) (@lem139508 h2)). Qed.
Lemma lem139586 (_2841 : nat) (_2842 : nat) : term218 _2841 _2842.
Proof. exact (EQ_MP (@lem139582 _2841 _2842) (@lem139561 _2842 _2841)). Qed.
Lemma lem139587 (m : nat) (n : nat) : term220 m n.
Proof. exact (@lem139586 (NUMERAL 0) (Nat.sub m n)). Qed.
Lemma lem139590 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : Peano.le m n) : term12 m n.
Proof. exact (@lem139587 m n (@lem139584 m n h1 h2 h3)). Qed.
Lemma lem139591 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : Peano.le m n) : term221 m n.
Proof. exact (fun h0 : term158 m n => @lem139590 m n h1 h2 h3). Qed.
Lemma lem139593 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem139594 (m : nat) (n : nat) : (term221 m n) = (term12 m n).
Proof. exact (@lem139593 (term12 m n)). Qed.
Lemma lem139595 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : Peano.le m n) : term12 m n.
Proof. exact (EQ_MP (@lem139594 m n) (@lem139591 m n h1 h2 h3)). Qed.
Lemma lem139598 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem139600 (m : nat) (n : nat) : (term158 m n) = (term222 m n).
Proof. exact (@lem139598 (term12 m n)). Qed.
Lemma lem139603 (m : nat) (n : nat) (h1 : term63 m n) : term222 m n.
Proof. exact (EQ_MP (@lem139600 m n) (@lem138727 m n h1)). Qed.
Lemma lem139606 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : False.
Proof. exact (@lem139603 m n h3 (@lem139595 m n h1 h2 h4)). Qed.
Lemma lem139607 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : term162.
Proof. exact (fun h0 : ~ False => @lem139606 m n h1 h2 h3 h4). Qed.
Lemma lem139609 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem139610 : term162 = False.
Proof. exact (@lem139609 False). Qed.
Lemma lem139611 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem139610) (@lem139607 m n h1 h2 h3 h4)). Qed.
Lemma lem139612 : Coq.Arith.PeanoNat.Nat.Even = Coq.Arith.PeanoNat.Nat.Even.
Proof. exact (eq_refl Coq.Arith.PeanoNat.Nat.Even). Qed.
Lemma lem139613 (_2855 : nat) (_2856 : nat) (h1 : _2855 = _2856) : _2855 = _2856.
Proof. exact (h1). Qed.
Lemma lem139614 (_2855 : nat) (_2856 : nat) (h1 : _2855 = _2856) : (Coq.Arith.PeanoNat.Nat.Even _2855) = (Coq.Arith.PeanoNat.Nat.Even _2856).
Proof. exact (MK_COMB (@lem139612) (@lem139613 _2855 _2856 h1)). Qed.
Lemma lem139616 (b : Prop) (a : Prop) : term163 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem139617 (_2856 : nat) (_2855 : nat) : term164 _2856 _2855.
Proof. exact (@lem139616 (Coq.Arith.PeanoNat.Nat.Even _2856) (Coq.Arith.PeanoNat.Nat.Even _2855)). Qed.
Lemma lem139618 (_2855 : nat) (_2856 : nat) (h1 : _2855 = _2856) : term165 _2856 _2855.
Proof. exact (@lem139617 _2856 _2855 (@lem139614 _2855 _2856 h1)). Qed.
Lemma lem139619 (_2856 : nat) (_2855 : nat) : term166 _2856 _2855.
Proof. exact (fun h0 : _2855 = _2856 => @lem139618 _2855 _2856 h0). Qed.
Lemma lem139621 (a : Prop) (b : Prop) : (a -> b) = (term167 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem139622 (_2856 : nat) (_2855 : nat) : (term166 _2856 _2855) = (term168 _2856 _2855).
Proof. exact (@lem139621 (_2855 = _2856) (term165 _2856 _2855)). Qed.
Lemma lem139623 (_2856 : nat) (_2855 : nat) : term168 _2856 _2855.
Proof. exact (EQ_MP (@lem139622 _2856 _2855) (@lem139619 _2856 _2855)). Qed.
Lemma lem139675 (x : nat) (y : nat) (z : nat) : term169 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem139677 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem139678 (m : nat) (n : nat) (h1 : Peano.le m n) : term159 m n.
Proof. exact (fun h0 : term10 m n => @lem139677 m n h1). Qed.
Lemma lem139680 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem139681 (m : nat) (n : nat) : (term159 m n) = (Peano.le m n).
Proof. exact (@lem139680 (Peano.le m n)). Qed.
Lemma lem139682 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (EQ_MP (@lem139681 m n) (@lem139678 m n h1)). Qed.
Lemma lem139684 (b : Prop) (a : Prop) : (a \/ b) = (term170 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem139685 (_2793 : nat) (_2794 : nat) : (term118 _2793 _2794) = (term171 _2793 _2794).
Proof. exact (@lem139684 (term10 _2793 _2794) ((Nat.sub _2793 _2794) = (NUMERAL 0))). Qed.
Lemma lem139687 (a : Prop) : (term172 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem139688 (_2793 : nat) (_2794 : nat) : (term173 _2793 _2794) = (Peano.le _2793 _2794).
Proof. exact (@lem139687 (Peano.le _2793 _2794)). Qed.
Lemma lem139689 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem139690 (_2793 : nat) (_2794 : nat) : (term174 _2793 _2794) = (term36 _2793 _2794).
Proof. exact (MK_COMB (@lem139689) (@lem139688 _2793 _2794)). Qed.
Lemma lem139691 (_2793 : nat) (_2794 : nat) : ((Nat.sub _2793 _2794) = (NUMERAL 0)) = ((Nat.sub _2793 _2794) = (NUMERAL 0)).
Proof. exact (eq_refl ((Nat.sub _2793 _2794) = (NUMERAL 0))). Qed.
Lemma lem139692 (_2793 : nat) (_2794 : nat) : (term171 _2793 _2794) = (term175 _2793 _2794).
Proof. exact (MK_COMB (@lem139690 _2793 _2794) (@lem139691 _2793 _2794)). Qed.
Lemma lem139693 (_2793 : nat) (_2794 : nat) : (term118 _2793 _2794) = (term175 _2793 _2794).
Proof. exact (TRANS (@lem139685 _2793 _2794) (@lem139692 _2793 _2794)). Qed.
Lemma lem139696 (_2793 : nat) (_2794 : nat) (h1 : term30) : term175 _2793 _2794.
Proof. exact (EQ_MP (@lem139693 _2793 _2794) (@lem138739 _2793 _2794 h1)). Qed.
Lemma lem139697 (m : nat) (n : nat) (h1 : term30) : term175 m n.
Proof. exact (@lem139696 m n h1). Qed.
Lemma lem139700 (m : nat) (n : nat) (h1 : term30) (h2 : Peano.le m n) : (Nat.sub m n) = (NUMERAL 0).
Proof. exact (@lem139697 m n h1 (@lem139682 m n h2)). Qed.
Lemma lem139701 (m : nat) (n : nat) (h1 : term30) (h2 : Peano.le m n) : term176 m n.
Proof. exact (fun h0 : term177 m n => @lem139700 m n h1 h2). Qed.
Lemma lem139703 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem139704 (m : nat) (n : nat) : (term176 m n) = ((Nat.sub m n) = (NUMERAL 0)).
Proof. exact (@lem139703 ((Nat.sub m n) = (NUMERAL 0))). Qed.
Lemma lem139705 (m : nat) (n : nat) (h1 : term30) (h2 : Peano.le m n) : (Nat.sub m n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem139704 m n) (@lem139701 m n h1 h2)). Qed.
Lemma lem139707 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem139708 (m : nat) (n : nat) : (Nat.sub m n) = (Nat.sub m n).
Proof. exact (@lem139707 (Nat.sub m n)). Qed.
Lemma lem139709 (m : nat) (n : nat) : term178 m n.
Proof. exact (fun h0 : term179 m n => @lem139708 m n). Qed.
Lemma lem139711 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem139712 (m : nat) (n : nat) : (term178 m n) = ((Nat.sub m n) = (Nat.sub m n)).
Proof. exact (@lem139711 ((Nat.sub m n) = (Nat.sub m n))). Qed.
Lemma lem139713 (m : nat) (n : nat) : (Nat.sub m n) = (Nat.sub m n).
Proof. exact (EQ_MP (@lem139712 m n) (@lem139709 m n)). Qed.
Lemma lem139731 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem139732 (y : nat) (x : nat) (z : nat) : (term180 x y z) = (term181 y x z).
Proof. exact (@lem139731 (y = z) (term182 x z)). Qed.
Lemma lem139742 (x : nat) (y : nat) : (term183 x y) = (term183 x y).
Proof. exact (eq_refl (term183 x y)). Qed.
Lemma lem139743 (y : nat) (x : nat) (z : nat) : (term169 x y z) = (term184 y x z).
Proof. exact (MK_COMB (@lem139742 x y) (@lem139732 y x z)). Qed.
Lemma lem139747 (q : Prop) (p : Prop) (r : Prop) : (term185 p q r) = (term185 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem139748 (y : nat) (x : nat) (z : nat) : (term184 y x z) = (term186 y x z).
Proof. exact (@lem139747 (y = z) (term182 x y) (term182 x z)). Qed.
Lemma lem139770 (y : nat) (x : nat) (z : nat) : (term169 x y z) = (term186 y x z).
Proof. exact (TRANS (@lem139743 y x z) (@lem139748 y x z)). Qed.
Lemma lem139771 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem139772 (y : nat) (x : nat) (z : nat) : (term187 x y z) = (term188 y x z).
Proof. exact (MK_COMB (@lem139771) (@lem139770 y x z)). Qed.
Lemma lem139794 (y : nat) (x : nat) (z : nat) : (term186 y x z) = (term186 y x z).
Proof. exact (eq_refl (term186 y x z)). Qed.
Lemma lem139795 (y : nat) (x : nat) (z : nat) : ((term169 x y z) = (term186 y x z)) = ((term186 y x z) = (term186 y x z)).
Proof. exact (MK_COMB (@lem139772 y x z) (@lem139794 y x z)). Qed.
Lemma lem139797 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem139798 (x : Prop) : (x = x) = True.
Proof. exact (@lem139797 Prop x). Qed.
Lemma lem139799 (y : nat) (x : nat) (z : nat) : ((term186 y x z) = (term186 y x z)) = True.
Proof. exact (@lem139798 (term186 y x z)). Qed.
Lemma lem139800 (y : nat) (x : nat) (z : nat) : ((term169 x y z) = (term186 y x z)) = True.
Proof. exact (TRANS (@lem139795 y x z) (@lem139799 y x z)). Qed.
Lemma lem139801 (y : nat) (x : nat) (z : nat) : True = ((term169 x y z) = (term186 y x z)).
Proof. exact (SYM (@lem139800 y x z)). Qed.
Lemma lem139802 (y : nat) (x : nat) (z : nat) : (term169 x y z) = (term186 y x z).
Proof. exact (EQ_MP (@lem139801 y x z) (@lem0)). Qed.
Lemma lem139803 (y : nat) (x : nat) (z : nat) : term186 y x z.
Proof. exact (EQ_MP (@lem139802 y x z) (@lem139675 x y z)). Qed.
Lemma lem139805 (b : Prop) (a : Prop) : (a \/ b) = (term170 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem139806 (x : nat) (y : nat) (z : nat) : (term186 y x z) = (term189 x y z).
Proof. exact (@lem139805 (term190 y x z) (y = z)). Qed.
Lemma lem139808 (a : Prop) (b : Prop) : (term191 a b) = (term192 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem139809 (y : nat) (x : nat) (z : nat) : (term193 y x z) = (term194 y x z).
Proof. exact (@lem139808 (term182 x y) (term182 x z)). Qed.
Lemma lem139811 (a : Prop) : (term172 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem139812 (x : nat) (y : nat) : (term195 x y) = (x = y).
Proof. exact (@lem139811 (x = y)). Qed.
Lemma lem139813 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem139814 (x : nat) (y : nat) : (term196 x y) = (term197 x y).
Proof. exact (MK_COMB (@lem139813) (@lem139812 x y)). Qed.
Lemma lem139816 (a : Prop) : (term172 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem139817 (x : nat) (z : nat) : (term195 x z) = (x = z).
Proof. exact (@lem139816 (x = z)). Qed.
Lemma lem139818 (y : nat) (x : nat) (z : nat) : (term194 y x z) = (term198 y x z).
Proof. exact (MK_COMB (@lem139814 x y) (@lem139817 x z)). Qed.
Lemma lem139819 (y : nat) (x : nat) (z : nat) : (term193 y x z) = (term198 y x z).
Proof. exact (TRANS (@lem139809 y x z) (@lem139818 y x z)). Qed.
Lemma lem139820 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem139821 (y : nat) (x : nat) (z : nat) : (term199 y x z) = (term200 y x z).
Proof. exact (MK_COMB (@lem139820) (@lem139819 y x z)). Qed.
Lemma lem139822 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem139823 (x : nat) (y : nat) (z : nat) : (term189 x y z) = (term201 x y z).
Proof. exact (MK_COMB (@lem139821 y x z) (@lem139822 y z)). Qed.
Lemma lem139824 (x : nat) (y : nat) (z : nat) : (term186 y x z) = (term201 x y z).
Proof. exact (TRANS (@lem139806 x y z) (@lem139823 x y z)). Qed.
Lemma lem139826 (m : nat) (n : nat) (h1 : term30) (h2 : Peano.le m n) : term202 m n.
Proof. exact (conj (@lem139705 m n h1 h2) (@lem139713 m n)). Qed.
Lemma lem139828 (x : nat) (y : nat) (z : nat) : term201 x y z.
Proof. exact (EQ_MP (@lem139824 x y z) (@lem139803 y x z)). Qed.
Lemma lem139829 (m : nat) (n : nat) : term203 m n.
Proof. exact (@lem139828 (Nat.sub m n) (NUMERAL 0) (Nat.sub m n)). Qed.
Lemma lem139832 (m : nat) (n : nat) (h1 : term30) (h2 : Peano.le m n) : (NUMERAL 0) = (Nat.sub m n).
Proof. exact (@lem139829 m n (@lem139826 m n h1 h2)). Qed.
Lemma lem139833 (m : nat) (n : nat) (h1 : term30) (h2 : Peano.le m n) : term204 m n.
Proof. exact (fun h0 : term205 m n => @lem139832 m n h1 h2). Qed.
Lemma lem139835 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem139836 (m : nat) (n : nat) : (term204 m n) = ((NUMERAL 0) = (Nat.sub m n)).
Proof. exact (@lem139835 ((NUMERAL 0) = (Nat.sub m n))). Qed.
Lemma lem139837 (m : nat) (n : nat) (h1 : term30) (h2 : Peano.le m n) : (NUMERAL 0) = (Nat.sub m n).
Proof. exact (EQ_MP (@lem139836 m n) (@lem139833 m n h1 h2)). Qed.
Lemma lem139839 (h1 : term25) : term20.
Proof. exact (proj1 (@lem138023 h1)). Qed.
Lemma lem139840 (h1 : term25) : term206.
Proof. exact (fun h0 : term207 => @lem139839 h1). Qed.
Lemma lem139842 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem139843 : term206 = term20.
Proof. exact (@lem139842 term20). Qed.
Lemma lem139844 (h1 : term25) : term20.
Proof. exact (EQ_MP (@lem139843) (@lem139840 h1)). Qed.
Lemma lem139850 (q : Prop) (p : Prop) (r : Prop) : (term185 p q r) = (term185 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem139851 (_2856 : nat) (_2855 : nat) : (term168 _2856 _2855) = (term208 _2856 _2855).
Proof. exact (@lem139850 (Coq.Arith.PeanoNat.Nat.Even _2856) (term182 _2855 _2856) (term50 _2855)). Qed.
Lemma lem139869 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem139870 (_2856 : nat) (_2855 : nat) : (term209 _2856 _2855) = (term210 _2856 _2855).
Proof. exact (MK_COMB (@lem139869) (@lem139851 _2856 _2855)). Qed.
Lemma lem139888 (_2856 : nat) (_2855 : nat) : (term208 _2856 _2855) = (term208 _2856 _2855).
Proof. exact (eq_refl (term208 _2856 _2855)). Qed.
Lemma lem139889 (_2856 : nat) (_2855 : nat) : ((term168 _2856 _2855) = (term208 _2856 _2855)) = ((term208 _2856 _2855) = (term208 _2856 _2855)).
Proof. exact (MK_COMB (@lem139870 _2856 _2855) (@lem139888 _2856 _2855)). Qed.
Lemma lem139891 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem139892 (x : Prop) : (x = x) = True.
Proof. exact (@lem139891 Prop x). Qed.
Lemma lem139893 (_2856 : nat) (_2855 : nat) : ((term208 _2856 _2855) = (term208 _2856 _2855)) = True.
Proof. exact (@lem139892 (term208 _2856 _2855)). Qed.
Lemma lem139894 (_2856 : nat) (_2855 : nat) : ((term168 _2856 _2855) = (term208 _2856 _2855)) = True.
Proof. exact (TRANS (@lem139889 _2856 _2855) (@lem139893 _2856 _2855)). Qed.
Lemma lem139895 (_2856 : nat) (_2855 : nat) : True = ((term168 _2856 _2855) = (term208 _2856 _2855)).
Proof. exact (SYM (@lem139894 _2856 _2855)). Qed.
Lemma lem139896 (_2856 : nat) (_2855 : nat) : (term168 _2856 _2855) = (term208 _2856 _2855).
Proof. exact (EQ_MP (@lem139895 _2856 _2855) (@lem0)). Qed.
Lemma lem139897 (_2856 : nat) (_2855 : nat) : term208 _2856 _2855.
Proof. exact (EQ_MP (@lem139896 _2856 _2855) (@lem139623 _2856 _2855)). Qed.
Lemma lem139899 (b : Prop) (a : Prop) : (a \/ b) = (term170 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem139900 (_2855 : nat) (_2856 : nat) : (term208 _2856 _2855) = (term211 _2855 _2856).
Proof. exact (@lem139899 (term212 _2856 _2855) (Coq.Arith.PeanoNat.Nat.Even _2856)). Qed.
Lemma lem139902 (a : Prop) (b : Prop) : (term191 a b) = (term192 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem139903 (_2856 : nat) (_2855 : nat) : (term213 _2856 _2855) = (term214 _2856 _2855).
Proof. exact (@lem139902 (term182 _2855 _2856) (term50 _2855)). Qed.
Lemma lem139905 (a : Prop) : (term172 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem139906 (_2855 : nat) (_2856 : nat) : (term195 _2855 _2856) = (_2855 = _2856).
Proof. exact (@lem139905 (_2855 = _2856)). Qed.
Lemma lem139907 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem139908 (_2855 : nat) (_2856 : nat) : (term196 _2855 _2856) = (term197 _2855 _2856).
Proof. exact (MK_COMB (@lem139907) (@lem139906 _2855 _2856)). Qed.
Lemma lem139910 (a : Prop) : (term172 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem139911 (_2855 : nat) : (term71 _2855) = (Coq.Arith.PeanoNat.Nat.Even _2855).
Proof. exact (@lem139910 (Coq.Arith.PeanoNat.Nat.Even _2855)). Qed.
Lemma lem139912 (_2856 : nat) (_2855 : nat) : (term214 _2856 _2855) = (term215 _2856 _2855).
Proof. exact (MK_COMB (@lem139908 _2855 _2856) (@lem139911 _2855)). Qed.
Lemma lem139913 (_2856 : nat) (_2855 : nat) : (term213 _2856 _2855) = (term215 _2856 _2855).
Proof. exact (TRANS (@lem139903 _2856 _2855) (@lem139912 _2856 _2855)). Qed.
Lemma lem139914 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem139915 (_2856 : nat) (_2855 : nat) : (term216 _2856 _2855) = (term217 _2856 _2855).
Proof. exact (MK_COMB (@lem139914) (@lem139913 _2856 _2855)). Qed.
Lemma lem139916 (_2856 : nat) : (Coq.Arith.PeanoNat.Nat.Even _2856) = (Coq.Arith.PeanoNat.Nat.Even _2856).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Even _2856)). Qed.
Lemma lem139917 (_2855 : nat) (_2856 : nat) : (term211 _2855 _2856) = (term218 _2855 _2856).
Proof. exact (MK_COMB (@lem139915 _2856 _2855) (@lem139916 _2856)). Qed.
Lemma lem139918 (_2855 : nat) (_2856 : nat) : (term208 _2856 _2855) = (term218 _2855 _2856).
Proof. exact (TRANS (@lem139900 _2855 _2856) (@lem139917 _2855 _2856)). Qed.
Lemma lem139920 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : Peano.le m n) : term219 m n.
Proof. exact (conj (@lem139837 m n h1 h3) (@lem139844 h2)). Qed.
Lemma lem139922 (_2855 : nat) (_2856 : nat) : term218 _2855 _2856.
Proof. exact (EQ_MP (@lem139918 _2855 _2856) (@lem139897 _2856 _2855)). Qed.
Lemma lem139923 (m : nat) (n : nat) : term220 m n.
Proof. exact (@lem139922 (NUMERAL 0) (Nat.sub m n)). Qed.
Lemma lem139926 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : Peano.le m n) : term12 m n.
Proof. exact (@lem139923 m n (@lem139920 m n h1 h2 h3)). Qed.
Lemma lem139927 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : Peano.le m n) : term221 m n.
Proof. exact (fun h0 : term158 m n => @lem139926 m n h1 h2 h3). Qed.
Lemma lem139929 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem139930 (m : nat) (n : nat) : (term221 m n) = (term12 m n).
Proof. exact (@lem139929 (term12 m n)). Qed.
Lemma lem139931 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : Peano.le m n) : term12 m n.
Proof. exact (EQ_MP (@lem139930 m n) (@lem139927 m n h1 h2 h3)). Qed.
Lemma lem139934 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem139936 (m : nat) (n : nat) : (term158 m n) = (term222 m n).
Proof. exact (@lem139934 (term12 m n)). Qed.
Lemma lem139939 (m : nat) (n : nat) (h1 : term63 m n) : term222 m n.
Proof. exact (EQ_MP (@lem139936 m n) (@lem138761 m n h1)). Qed.
Lemma lem139942 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : False.
Proof. exact (@lem139939 m n h3 (@lem139931 m n h1 h2 h4)). Qed.
Lemma lem139943 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : term162.
Proof. exact (fun h0 : ~ False => @lem139942 m n h1 h2 h3 h4). Qed.
Lemma lem139945 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem139946 : term162 = False.
Proof. exact (@lem139945 False). Qed.
Lemma lem139947 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem139946) (@lem139943 m n h1 h2 h3 h4)). Qed.
Lemma lem139948 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h5 : Peano.le m n => @lem139947 m n h1 h2 h3 h4) (fun h5 : False => @lem138733 m n h4)). Qed.
Lemma lem139949 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem139948 m n h1 h2 h3 h4) (@lem138733 m n h4)). Qed.
Lemma lem139950 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h5 : Peano.le m n => @lem139611 m n h1 h2 h3 h4) (fun h5 : False => @lem138699 m n h4)). Qed.
Lemma lem139951 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem139950 m n h1 h2 h3 h4) (@lem138699 m n h4)). Qed.
Lemma lem139952 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h5 : Peano.le m n => @lem139275 m n h1 h2 h3 h4) (fun h5 : False => @lem138697 m n h4)). Qed.
Lemma lem139953 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem139952 m n h1 h2 h3 h4) (@lem138697 m n h4)). Qed.
Lemma lem139954 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h5 : Peano.le m n => @lem139953 m n h1 h2 h3 h4) (fun h5 : False => @lem138667 m n h4)). Qed.
Lemma lem139955 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem139954 m n h1 h2 h3 h4) (@lem138667 m n h4)). Qed.
Lemma lem139956 (m : nat) (n : nat) (h1 : term66 m n) (h2 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.le m n => @lem138939 m n h1 h2) (fun h3 : False => @lem138631 m n h2)). Qed.
Lemma lem139957 (m : nat) (n : nat) (h1 : term66 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem139956 m n h1 h2) (@lem138631 m n h2)). Qed.
Lemma lem139958 (m : nat) (n : nat) (h1 : term66 m n) (h2 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.le m n => @lem138852 m n h1 h2) (fun h3 : False => @lem138595 m n h2)). Qed.
Lemma lem139959 (m : nat) (n : nat) (h1 : term66 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem139958 m n h1 h2) (@lem138595 m n h2)). Qed.
Lemma lem139960 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h5 : Peano.le m n => @lem139949 m n h1 h2 h3 h4) (fun h5 : False => @lem138429 m n h4)). Qed.
Lemma lem139961 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem139960 m n h1 h2 h3 h4) (@lem138429 m n h4)). Qed.
Lemma lem139962 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h5 : Peano.le m n => @lem139951 m n h1 h2 h3 h4) (fun h5 : False => @lem138351 m n h4)). Qed.
Lemma lem139963 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem139962 m n h1 h2 h3 h4) (@lem138351 m n h4)). Qed.
Lemma lem139964 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h5 : Peano.le m n => @lem139955 m n h1 h2 h3 h4) (fun h5 : False => @lem138347 m n h4)). Qed.
Lemma lem139965 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem139964 m n h1 h2 h3 h4) (@lem138347 m n h4)). Qed.
Lemma lem139966 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h5 : Peano.le m n => @lem139965 m n h1 h2 h3 h4) (fun h5 : False => @lem138277 m n h4)). Qed.
Lemma lem139967 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem139966 m n h1 h2 h3 h4) (@lem138277 m n h4)). Qed.
Lemma lem139968 (m : nat) (n : nat) (h1 : term66 m n) (h2 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.le m n => @lem139957 m n h1 h2) (fun h3 : False => @lem138195 m n h2)). Qed.
Lemma lem139969 (m : nat) (n : nat) (h1 : term66 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem139968 m n h1 h2) (@lem138195 m n h2)). Qed.
Lemma lem139970 (m : nat) (n : nat) (h1 : term66 m n) (h2 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.le m n => @lem139959 m n h1 h2) (fun h3 : False => @lem138113 m n h2)). Qed.
Lemma lem139971 (m : nat) (n : nat) (h1 : term66 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem139970 m n h1 h2) (@lem138113 m n h2)). Qed.
Lemma lem139972 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h5 : Peano.le m n => @lem139961 m n h1 h2 h3 h4) (fun h5 : False => @lem138429 m n h4)). Qed.
Lemma lem139973 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem139972 m n h1 h2 h3 h4) (@lem138429 m n h4)). Qed.
Lemma lem139974 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h5 : Peano.le m n => @lem139963 m n h1 h2 h3 h4) (fun h5 : False => @lem138351 m n h4)). Qed.
Lemma lem139975 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem139974 m n h1 h2 h3 h4) (@lem138351 m n h4)). Qed.
Lemma lem139976 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h5 : Peano.le m n => @lem139967 m n h1 h2 h3 h4) (fun h5 : False => @lem138347 m n h4)). Qed.
Lemma lem139977 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem139976 m n h1 h2 h3 h4) (@lem138347 m n h4)). Qed.
Lemma lem139978 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h5 : Peano.le m n => @lem139977 m n h1 h2 h3 h4) (fun h5 : False => @lem138277 m n h4)). Qed.
Lemma lem139979 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem139978 m n h1 h2 h3 h4) (@lem138277 m n h4)). Qed.
Lemma lem139980 (m : nat) (n : nat) (h1 : term66 m n) (h2 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.le m n => @lem139969 m n h1 h2) (fun h3 : False => @lem138195 m n h2)). Qed.
Lemma lem139981 (m : nat) (n : nat) (h1 : term66 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem139980 m n h1 h2) (@lem138195 m n h2)). Qed.
Lemma lem139982 (m : nat) (n : nat) (h1 : term66 m n) (h2 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.le m n => @lem139971 m n h1 h2) (fun h3 : False => @lem138113 m n h2)). Qed.
Lemma lem139983 (m : nat) (n : nat) (h1 : term66 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem139982 m n h1 h2) (@lem138113 m n h2)). Qed.
Lemma lem139984 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) (h5 : term54 m n) : False.
Proof. exact (or_elim (@lem138103 m n h5) (fun h0 : term223 m n => @lem139975 m n h1 h2 h3 h4) (fun h0 : term224 m n => @lem139973 m n h1 h2 h3 h4)). Qed.
Lemma lem139985 (m : nat) (n : nat) (h1 : term30) (h2 : term25) (h3 : term63 m n) (h4 : Peano.le m n) : False.
Proof. exact (or_elim (@lem138100 m n h3) (fun h0 : Peano.le m n => @lem139979 m n h1 h2 h3 h4) (fun h0 : term54 m n => @lem139984 m n h1 h2 h3 h4 h0)). Qed.
Lemma lem139986 (m : nat) (n : nat) (h1 : term66 m n) (h2 : Peano.le m n) : False.
Proof. exact (or_elim (@lem138092 m n h1) (fun h0 : term225 m n => @lem139983 m n h1 h2) (fun h0 : term226 m n => @lem139981 m n h1 h2)). Qed.
Lemma lem139987 (m : nat) (n : nat) (h1 : term30) (h2 : term15 m n) (h3 : term25) (h4 : Peano.le m n) : False.
Proof. exact (or_elim (@lem137979 m n h2) (fun h0 : term66 m n => @lem139986 m n h0 h4) (fun h0 : term63 m n => @lem139985 m n h1 h3 h0 h4)). Qed.
Lemma lem139988 (m : nat) (n : nat) (h1 : term30) (h2 : term15 m n) (h3 : term25) (h4 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h5 : Peano.le m n => @lem139987 m n h1 h2 h3 h4) (fun h5 : False => @lem137885 m n h4)). Qed.
Lemma lem139989 (m : nat) (n : nat) (h1 : term30) (h2 : term15 m n) (h3 : term25) (h4 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem139988 m n h1 h2 h3 h4) (@lem137885 m n h4)). Qed.
Lemma lem139990 (m : nat) (n : nat) (h1 : term30) (h2 : term15 m n) (h3 : term25) (h4 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h5 : Peano.le m n => @lem139989 m n h1 h2 h3 h4) (fun h5 : False => @lem137401 m n h4)). Qed.
Lemma lem139991 (m : nat) (n : nat) (h1 : term30) (h2 : term15 m n) (h3 : term25) (h4 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem139990 m n h1 h2 h3 h4) (@lem137401 m n h4)). Qed.
Lemma lem139992 (m : nat) (n : nat) (h1 : term15 m n) (h2 : term25) (h3 : Peano.le m n) : term28.
Proof. exact (fun h0 : term30 => @lem139991 m n h0 h1 h2 h3). Qed.
Lemma lem139993 : term28 = term29.
Proof. exact (@lem69 term30). Qed.
Lemma lem139994 (m : nat) (n : nat) (h1 : term15 m n) (h2 : term25) (h3 : Peano.le m n) : term29.
Proof. exact (EQ_MP (@lem139993) (@lem139992 m n h1 h2 h3)). Qed.
Lemma lem139995 (m : nat) (n : nat) (h1 : term15 m n) (h2 : Peano.le m n) : term32.
Proof. exact (fun h0 : term25 => @lem139994 m n h1 h0 h2). Qed.
Lemma lem139996 (m : nat) (n : nat) (h1 : Peano.le m n) : term35 m n.
Proof. exact (fun h0 : term15 m n => @lem139995 m n h0 h1). Qed.
Lemma lem139997 (m : nat) (n : nat) : term37 m n.
Proof. exact (fun h0 : Peano.le m n => @lem139996 m n h0). Qed.
Lemma lem140002 (n : nat) : term41 n.
Proof. exact (fun m : nat => @lem139997 m n). Qed.
Lemma lem140007 : term45.
Proof. exact (fun n : nat => @lem140002 n). Qed.
Lemma lem140008 : term44.
Proof. exact (EQ_MP (@lem137391) (@lem140007)). Qed.
Lemma lem140009 (n : nat) : term227 n.
Proof. exact (@lem140008 n). Qed.
Lemma lem140010 (n : nat) : (term227 n) = (term40 n).
Proof. exact (eq_refl (term227 n)). Qed.
Lemma lem140011 (n : nat) : term40 n.
Proof. exact (EQ_MP (@lem140010 n) (@lem140009 n)). Qed.
Lemma lem140012 (n : nat) (m : nat) : term228 n m.
Proof. exact (@lem140011 n m). Qed.
Lemma lem140013 (m : nat) (n : nat) : (term228 n m) = (term16 m n).
Proof. exact (eq_refl (term228 n m)). Qed.
Lemma lem140014 (m : nat) (n : nat) : term16 m n.
Proof. exact (EQ_MP (@lem140013 m n) (@lem140012 n m)). Qed.
Lemma lem140016 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem137216 m n (@lem140014 m n)). Qed.
Lemma lem140017 (m : nat) (n : nat) (h1 : Peano.le m n) : term34 m n.
Proof. exact (@lem140016 m n (@lem137195 m n h1)). Qed.
Lemma lem140018 (m : nat) (n : nat) (h1 : term15 m n) (h2 : Peano.le m n) : term31.
Proof. exact (@lem140017 m n h2 (@lem137201 m n h1)). Qed.
Lemma lem140019 (m : nat) (n : nat) (h1 : term15 m n) (h2 : Peano.le m n) : term28.
Proof. exact (@lem140018 m n h1 h2 (@lem124236)). Qed.
Lemma lem140020 (m : nat) (n : nat) (h1 : term15 m n) (h2 : Peano.le m n) : False.
Proof. exact (@lem140019 m n h1 h2 (@lem136259)). Qed.
Lemma lem140021 (m : nat) (n : nat) (h1 : term15 m n) (h2 : Peano.le m n) : (term15 m n) = False.
Proof. exact (prop_ext (fun h3 : term15 m n => @lem140020 m n h1 h2) (fun h3 : False => @lem137201 m n h1)). Qed.
Lemma lem140022 (m : nat) (n : nat) (h1 : term15 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem140021 m n h1 h2) (@lem137201 m n h1)). Qed.
Lemma lem140023 (m : nat) (n : nat) (h1 : Peano.le m n) : term14 m n.
Proof. exact (fun h0 : term15 m n => @lem140022 m n h0 h1). Qed.
Lemma lem140024 (m : nat) (n : nat) (h1 : Peano.le m n) : (term12 m n) = (term13 m n).
Proof. exact (EQ_MP (@lem137200 m n) (@lem140023 m n h1)). Qed.
Lemma lem140025 (m : nat) (n : nat) : term229 m n.
Proof. exact (@lem82 (Peano.le m n)). Qed.
Lemma lem140034 (m : nat) (n : nat) (h1 : term10 m n) : (Peano.le m n) = False.
Proof. exact (@lem140025 m n (@lem137196 m n h1)). Qed.
Lemma lem140035 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem140036 (m : nat) (n : nat) (h1 : term10 m n) : (term59 m n) = (or False).
Proof. exact (MK_COMB (@lem140035) (@lem140034 m n h1)). Qed.
Lemma lem140039 (m : nat) (n : nat) : ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (eq_refl ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))). Qed.
Lemma lem140040 (m : nat) (n : nat) (h1 : term10 m n) : (term13 m n) = (term230 m n).
Proof. exact (MK_COMB (@lem140036 m n h1) (@lem140039 m n)). Qed.
Lemma lem140042 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem140043 (m : nat) (n : nat) : (term230 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (@lem140042 ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))). Qed.
Lemma lem140046 (m : nat) (n : nat) (h1 : term10 m n) : (term13 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (TRANS (@lem140040 m n h1) (@lem140043 m n)). Qed.
Lemma lem140047 (m : nat) (n : nat) : (term231 m n) = (term231 m n).
Proof. exact (eq_refl (term231 m n)). Qed.
Lemma lem140048 (m : nat) (n : nat) (h1 : term10 m n) : ((term12 m n) = (term13 m n)) = ((term12 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))).
Proof. exact (MK_COMB (@lem140047 m n) (@lem140046 m n h1)). Qed.
Lemma lem140053 (m : nat) (n : nat) (h1 : term10 m n) : ((term12 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))) = ((term12 m n) = (term13 m n)).
Proof. exact (SYM (@lem140048 m n h1)). Qed.
Lemma lem140054 (m : nat) (n : nat) : term229 m n.
Proof. exact (@lem82 (Peano.le m n)). Qed.
Lemma lem140063 (m : nat) (n : nat) (h1 : term10 m n) : (Peano.le m n) = False.
Proof. exact (@lem140054 m n (@lem137196 m n h1)). Qed.
Lemma lem140064 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem140065 (m : nat) (n : nat) (h1 : term10 m n) : (term59 m n) = (or False).
Proof. exact (MK_COMB (@lem140064) (@lem140063 m n h1)). Qed.
Lemma lem140068 (m : nat) (n : nat) : ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (eq_refl ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))). Qed.
Lemma lem140069 (m : nat) (n : nat) (h1 : term10 m n) : (term13 m n) = (term230 m n).
Proof. exact (MK_COMB (@lem140065 m n h1) (@lem140068 m n)). Qed.
Lemma lem140071 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem140072 (m : nat) (n : nat) : (term230 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (@lem140071 ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))). Qed.
Lemma lem140075 (m : nat) (n : nat) (h1 : term10 m n) : (term13 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (TRANS (@lem140069 m n h1) (@lem140072 m n)). Qed.
Lemma lem140076 (m : nat) (n : nat) : (term231 m n) = (term231 m n).
Proof. exact (eq_refl (term231 m n)). Qed.
Lemma lem140077 (m : nat) (n : nat) (h1 : term10 m n) : ((term12 m n) = (term13 m n)) = ((term12 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))).
Proof. exact (MK_COMB (@lem140076 m n) (@lem140075 m n h1)). Qed.
Lemma lem140082 (m : nat) (n : nat) (h1 : term10 m n) : ((term12 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))) = ((term12 m n) = (term13 m n)).
Proof. exact (SYM (@lem140077 m n h1)). Qed.
Lemma lem140084 (n : nat) (m : nat) : term3 n m.
Proof. exact (EQ_MP (@lem137171 n m) (@lem137170 m n)). Qed.
Lemma lem140085 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem140084 m n). Qed.
Lemma lem140086 (m : nat) (n : nat) (h1 : Peano.le m n) : (term232 n m) = n.
Proof. exact (@lem140085 m n (@lem137180 m n h1)). Qed.
Lemma lem140087 (m : nat) (n : nat) (h1 : Peano.le m n) : (term233 n m) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (MK_COMB (@lem137173) (@lem140086 m n h1)). Qed.
Lemma lem140089 (n : nat) (m : nat) : term3 n m.
Proof. exact (EQ_MP (@lem137171 n m) (@lem137170 m n)). Qed.
Lemma lem140090 (n : nat) (m : nat) (h1 : Peano.le n m) : (term232 m n) = m.
Proof. exact (@lem140089 n m (@lem137181 n m h1)). Qed.
Lemma lem140091 (n : nat) (m : nat) (h1 : Peano.le n m) : (term233 m n) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (MK_COMB (@lem137173) (@lem140090 n m h1)). Qed.
Lemma lem140093 (p : Prop) : p = (term11 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem140094 (m : nat) (n : nat) : (term234 m n) = (term235 m n).
Proof. exact (@lem140093 (term234 m n)). Qed.
Lemma lem140095 (m : nat) (n : nat) : (term235 m n) = (term234 m n).
Proof. exact (SYM (@lem140094 m n)). Qed.
Lemma lem140096 (m : nat) (n : nat) (h1 : term236 m n) : term236 m n.
Proof. exact (h1). Qed.
Lemma lem140099 (m : nat) (n : nat) (h1 : term237 m n) : term237 m n.
Proof. exact (h1). Qed.
Lemma lem140100 (m : nat) (n : nat) : term238 m n.
Proof. exact (fun h0 : term237 m n => @lem140099 m n h0). Qed.
Lemma lem140101 (m : nat) (n : nat) (h1 : term238 m n) : term238 m n.
Proof. exact (h1). Qed.
Lemma lem140102 (m : nat) (n : nat) (h1 : term237 m n) : term237 m n.
Proof. exact (h1). Qed.
Lemma lem140103 (m : nat) (n : nat) (h1 : term237 m n) (h2 : term238 m n) : term237 m n.
Proof. exact (@lem140101 m n h2 (@lem140102 m n h1)). Qed.
Lemma lem140104 (m : nat) (n : nat) (h1 : term237 m n) : term239 m n.
Proof. exact (fun h0 : term238 m n => @lem140103 m n h1 h0). Qed.
Lemma lem140105 (m : nat) (n : nat) (h1 : term238 m n) : term238 m n.
Proof. exact (h1). Qed.
Lemma lem140106 (m : nat) (n : nat) (h1 : term237 m n) (h2 : term238 m n) : term237 m n.
Proof. exact (@lem140104 m n h1 (@lem140105 m n h2)). Qed.
Lemma lem140107 (m : nat) (n : nat) (h1 : term238 m n) : term238 m n.
Proof. exact (fun h0 : term237 m n => @lem140106 m n h0 h1). Qed.
Lemma lem140108 (m : nat) (n : nat) : term240 m n.
Proof. exact (fun h0 : term238 m n => @lem140107 m n h0). Qed.
Lemma lem140111 (m : nat) (n : nat) : term238 m n.
Proof. exact (@lem140108 m n (@lem140100 m n)). Qed.
Lemma lem140129 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem140130 : term241 = term242.
Proof. exact (@lem140129 term243). Qed.
Lemma lem140139 (m : nat) (n : nat) : (term244 m n) = (term244 m n).
Proof. exact (eq_refl (term244 m n)). Qed.
Lemma lem140140 (m : nat) (n : nat) : (term245 m n) = (term246 m n).
Proof. exact (MK_COMB (@lem140139 m n) (@lem140130)). Qed.
Lemma lem140143 (m : nat) (n : nat) : (term36 m n) = (term36 m n).
Proof. exact (eq_refl (term36 m n)). Qed.
Lemma lem140144 (m : nat) (n : nat) : (term247 m n) = (term248 m n).
Proof. exact (MK_COMB (@lem140143 m n) (@lem140140 m n)). Qed.
Lemma lem140147 (m : nat) (n : nat) : (term249 m n) = (term249 m n).
Proof. exact (eq_refl (term249 m n)). Qed.
Lemma lem140148 (m : nat) (n : nat) : (term237 m n) = (term250 m n).
Proof. exact (MK_COMB (@lem140147 m n) (@lem140144 m n)). Qed.
Lemma lem140151 (n : nat) : (term251 n) = (term252 n).
Proof. exact (fun_ext (fun m : nat => @lem140148 m n)). Qed.
Lemma lem140152 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem140153 (n : nat) : (term253 n) = (term254 n).
Proof. exact (MK_COMB (@lem140152) (@lem140151 n)). Qed.
Lemma lem140158 : term255 = term256.
Proof. exact (fun_ext (fun n : nat => @lem140153 n)). Qed.
Lemma lem140159 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem140168 : term257 = term258.
Proof. exact (MK_COMB (@lem140159) (@lem140158)). Qed.
Lemma lem140177 (m : nat) (n : nat) : ((term259 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))) = ((term259 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))).
Proof. exact (eq_refl ((term259 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)))). Qed.
Lemma lem140178 (m : nat) : (term260 m) = (term260 m).
Proof. exact (fun_ext (fun n : nat => @lem140177 m n)). Qed.
Lemma lem140179 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem140180 (m : nat) : (term261 m) = (term261 m).
Proof. exact (MK_COMB (@lem140179) (@lem140178 m)). Qed.
Lemma lem140181 : term262 = term262.
Proof. exact (fun_ext (fun m : nat => @lem140180 m)). Qed.
Lemma lem140182 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem140183 : term243 = term243.
Proof. exact (MK_COMB (@lem140182) (@lem140181)). Qed.
Lemma lem140184 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem140185 : term242 = term242.
Proof. exact (MK_COMB (@lem140184) (@lem140183)). Qed.
Lemma lem140206 (m : nat) (n : nat) : (term244 m n) = (term244 m n).
Proof. exact (eq_refl (term244 m n)). Qed.
Lemma lem140207 (m : nat) (n : nat) : (term246 m n) = (term246 m n).
Proof. exact (MK_COMB (@lem140206 m n) (@lem140185)). Qed.
Lemma lem140210 (m : nat) (n : nat) : (term36 m n) = (term36 m n).
Proof. exact (eq_refl (term36 m n)). Qed.
Lemma lem140211 (m : nat) (n : nat) : (term248 m n) = (term248 m n).
Proof. exact (MK_COMB (@lem140210 m n) (@lem140207 m n)). Qed.
Lemma lem140216 (m : nat) (n : nat) : (term249 m n) = (term249 m n).
Proof. exact (eq_refl (term249 m n)). Qed.
Lemma lem140217 (m : nat) (n : nat) : (term250 m n) = (term250 m n).
Proof. exact (MK_COMB (@lem140216 m n) (@lem140211 m n)). Qed.
Lemma lem140218 (n : nat) : (term252 n) = (term252 n).
Proof. exact (fun_ext (fun m : nat => @lem140217 m n)). Qed.
Lemma lem140219 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem140220 (n : nat) : (term254 n) = (term254 n).
Proof. exact (MK_COMB (@lem140219) (@lem140218 n)). Qed.
Lemma lem140221 : term256 = term256.
Proof. exact (fun_ext (fun n : nat => @lem140220 n)). Qed.
Lemma lem140222 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem140223 : term258 = term258.
Proof. exact (MK_COMB (@lem140222) (@lem140221)). Qed.
Lemma lem140258 : term257 = term258.
Proof. exact (TRANS (@lem140168) (@lem140223)). Qed.
Lemma lem140259 : term258 = term257.
Proof. exact (SYM (@lem140258)). Qed.
Lemma lem140262 (m : nat) (n : nat) (h1 : term236 m n) : term236 m n.
Proof. exact (h1). Qed.
Lemma lem140269 (m : nat) (n : nat) (h1 : term10 m n) : term10 m n.
Proof. exact (h1). Qed.
Lemma lem140275 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem140290 (m : nat) (n : nat) : ((term233 n m) = (Coq.Arith.PeanoNat.Nat.Even n)) = (term263 m n).
Proof. exact (@lem17500 (term233 n m) (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem140307 (m : nat) (n : nat) : (term52 m n) = (term53 m n).
Proof. exact (@lem17646 (Coq.Arith.PeanoNat.Nat.Even m) (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem140318 (m : nat) (n : nat) : ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)) = (term54 m n).
Proof. exact (@lem17500 (Coq.Arith.PeanoNat.Nat.Even m) (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem140320 (m : nat) (n : nat) : (term61 m n) = (term61 m n).
Proof. exact (eq_refl (term61 m n)). Qed.
Lemma lem140321 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (MK_COMB (@lem140320 m n) (@lem140318 m n)). Qed.
Lemma lem140323 (m : nat) (n : nat) : (term64 m n) = (term64 m n).
Proof. exact (eq_refl (term64 m n)). Qed.
Lemma lem140324 (m : nat) (n : nat) : (term266 m n) = (term267 m n).
Proof. exact (MK_COMB (@lem140323 m n) (@lem140307 m n)). Qed.
Lemma lem140325 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem140326 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (MK_COMB (@lem140325) (@lem140324 m n)). Qed.
Lemma lem140327 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (MK_COMB (@lem140326 m n) (@lem140321 m n)). Qed.
Lemma lem140328 (m : nat) (n : nat) : (term272 m n) = (term270 m n).
Proof. exact (@lem17646 (term12 m n) ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))). Qed.
Lemma lem140329 (m : nat) (n : nat) : (term272 m n) = (term271 m n).
Proof. exact (TRANS (@lem140328 m n) (@lem140327 m n)). Qed.
Lemma lem140330 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem140331 (m : nat) (n : nat) : (term273 m n) = (term274 m n).
Proof. exact (MK_COMB (@lem140330) (@lem140290 m n)). Qed.
Lemma lem140332 (m : nat) (n : nat) : (term275 m n) = (term276 m n).
Proof. exact (MK_COMB (@lem140331 m n) (@lem140329 m n)). Qed.
Lemma lem140333 (m : nat) (n : nat) : (term236 m n) = (term275 m n).
Proof. exact (@lem17362 ((term233 n m) = (Coq.Arith.PeanoNat.Nat.Even n)) ((term12 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)))). Qed.
Lemma lem140338 (m : nat) (n : nat) : (term236 m n) = (term276 m n).
Proof. exact (TRANS (@lem140333 m n) (@lem140332 m n)). Qed.
Lemma lem140658 (m : nat) (n : nat) (h1 : term10 m n) : term10 m n.
Proof. exact (h1). Qed.
Lemma lem140664 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem140784 (m : nat) (n : nat) (h1 : term236 m n) : term276 m n.
Proof. exact (EQ_MP (@lem140338 m n) (@lem140262 m n h1)). Qed.
Lemma lem140875 (m : nat) (n : nat) (h1 : term236 m n) : term271 m n.
Proof. exact (proj2 (@lem140784 m n h1)). Qed.
Lemma lem140876 (m : nat) (n : nat) (h1 : term236 m n) : term263 m n.
Proof. exact (proj1 (@lem140784 m n h1)). Qed.
Lemma lem140877 (m : nat) (n : nat) (h1 : term267 m n) : term267 m n.
Proof. exact (h1). Qed.
Lemma lem140878 (m : nat) (n : nat) (h1 : term265 m n) : term265 m n.
Proof. exact (h1). Qed.
Lemma lem140879 (m : nat) (n : nat) (h1 : term267 m n) : term53 m n.
Proof. exact (proj2 (@lem140877 m n h1)). Qed.
Lemma lem140881 (m : nat) (n : nat) (h1 : term225 m n) : term225 m n.
Proof. exact (h1). Qed.
Lemma lem140882 (m : nat) (n : nat) (h1 : term226 m n) : term226 m n.
Proof. exact (h1). Qed.
Lemma lem140885 (m : nat) (n : nat) (h1 : term277 m n) : term277 m n.
Proof. exact (h1). Qed.
Lemma lem140894 (m : nat) (n : nat) (h1 : term278 m n) : term278 m n.
Proof. exact (h1). Qed.
Lemma lem140899 (m : nat) (n : nat) (h1 : term265 m n) : term54 m n.
Proof. exact (proj2 (@lem140878 m n h1)). Qed.
Lemma lem140901 (m : nat) (n : nat) (h1 : term223 m n) : term223 m n.
Proof. exact (h1). Qed.
Lemma lem140902 (m : nat) (n : nat) (h1 : term224 m n) : term224 m n.
Proof. exact (h1). Qed.
Lemma lem140906 (m : nat) (n : nat) (h1 : term278 m n) : term278 m n.
Proof. exact (h1). Qed.
Lemma lem140913 (m : nat) (n : nat) (h1 : term277 m n) : term277 m n.
Proof. exact (h1). Qed.
Lemma lem141026 (m : nat) (n : nat) (h1 : term10 m n) : term10 m n.
Proof. exact (h1). Qed.
Lemma lem141030 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem141130 (m : nat) (n : nat) (h1 : term10 m n) : term10 m n.
Proof. exact (h1). Qed.
Lemma lem141134 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem141338 (m : nat) (n : nat) (h1 : term10 m n) : term10 m n.
Proof. exact (h1). Qed.
Lemma lem141342 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem141650 (m : nat) (n : nat) (h1 : term10 m n) : term10 m n.
Proof. exact (h1). Qed.
Lemma lem141654 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem141888 (m : nat) (n : nat) (h1 : term225 m n) : term50 n.
Proof. exact (proj2 (@lem140881 m n h1)). Qed.
Lemma lem141934 (m : nat) (n : nat) (h1 : term10 m n) : term10 m n.
Proof. exact (h1). Qed.
Lemma lem141936 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem141988 (m : nat) (n : nat) (h1 : term10 m n) : term10 m n.
Proof. exact (h1). Qed.
Lemma lem141990 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem142054 (m : nat) (n : nat) (h1 : term278 m n) : term50 n.
Proof. exact (proj2 (@lem140894 m n h1)). Qed.
Lemma lem142096 (m : nat) (n : nat) (h1 : term10 m n) : term10 m n.
Proof. exact (h1). Qed.
Lemma lem142098 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem142162 (m : nat) (n : nat) (h1 : term278 m n) : term50 n.
Proof. exact (proj2 (@lem140906 m n h1)). Qed.
Lemma lem142212 (m : nat) (n : nat) (h1 : term224 m n) : term50 n.
Proof. exact (proj2 (@lem140902 m n h1)). Qed.
Lemma lem142258 (m : nat) (n : nat) (h1 : term10 m n) : term10 m n.
Proof. exact (h1). Qed.
Lemma lem142260 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem142312 (m : nat) (n : nat) (h1 : term277 m n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (proj2 (@lem140885 m n h1)). Qed.
Lemma lem142313 (m : nat) (n : nat) (h1 : term277 m n) : term279 n.
Proof. exact (fun h0 : term50 n => @lem142312 m n h1). Qed.
Lemma lem142315 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem142316 (n : nat) : (term279 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (@lem142315 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem142317 (m : nat) (n : nat) (h1 : term277 m n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (EQ_MP (@lem142316 n) (@lem142313 m n h1)). Qed.
Lemma lem142320 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem142322 (n : nat) : (term50 n) = (term280 n).
Proof. exact (@lem142320 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem142325 (m : nat) (n : nat) (h1 : term225 m n) : term280 n.
Proof. exact (EQ_MP (@lem142322 n) (@lem141888 m n h1)). Qed.
Lemma lem142328 (m : nat) (n : nat) (h1 : term225 m n) (h2 : term277 m n) : False.
Proof. exact (@lem142325 m n h1 (@lem142317 m n h2)). Qed.
Lemma lem142329 (m : nat) (n : nat) (h1 : term225 m n) (h2 : term277 m n) : term162.
Proof. exact (fun h0 : ~ False => @lem142328 m n h1 h2). Qed.
Lemma lem142331 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem142332 : term162 = False.
Proof. exact (@lem142331 False). Qed.
Lemma lem142333 (m : nat) (n : nat) (h1 : term225 m n) (h2 : term277 m n) : False.
Proof. exact (EQ_MP (@lem142332) (@lem142329 m n h1 h2)). Qed.
Lemma lem142335 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem142336 (m : nat) (n : nat) (h1 : Peano.le m n) : term159 m n.
Proof. exact (fun h0 : term10 m n => @lem142335 m n h1). Qed.
Lemma lem142338 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem142339 (m : nat) (n : nat) : (term159 m n) = (Peano.le m n).
Proof. exact (@lem142338 (Peano.le m n)). Qed.
Lemma lem142340 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (EQ_MP (@lem142339 m n) (@lem142336 m n h1)). Qed.
Lemma lem142343 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem142345 (m : nat) (n : nat) : (term10 m n) = (term161 m n).
Proof. exact (@lem142343 (Peano.le m n)). Qed.
Lemma lem142348 (m : nat) (n : nat) (h1 : term10 m n) : term161 m n.
Proof. exact (EQ_MP (@lem142345 m n) (@lem141934 m n h1)). Qed.
Lemma lem142351 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (@lem142348 m n h1 (@lem142340 m n h2)). Qed.
Lemma lem142352 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : term162.
Proof. exact (fun h0 : ~ False => @lem142351 m n h1 h2). Qed.
Lemma lem142354 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem142355 : term162 = False.
Proof. exact (@lem142354 False). Qed.
Lemma lem142356 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142355) (@lem142352 m n h1 h2)). Qed.
Lemma lem142358 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem142359 (m : nat) (n : nat) (h1 : Peano.le m n) : term159 m n.
Proof. exact (fun h0 : term10 m n => @lem142358 m n h1). Qed.
Lemma lem142361 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem142362 (m : nat) (n : nat) : (term159 m n) = (Peano.le m n).
Proof. exact (@lem142361 (Peano.le m n)). Qed.
Lemma lem142363 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (EQ_MP (@lem142362 m n) (@lem142359 m n h1)). Qed.
Lemma lem142366 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem142368 (m : nat) (n : nat) : (term10 m n) = (term161 m n).
Proof. exact (@lem142366 (Peano.le m n)). Qed.
Lemma lem142371 (m : nat) (n : nat) (h1 : term10 m n) : term161 m n.
Proof. exact (EQ_MP (@lem142368 m n) (@lem141988 m n h1)). Qed.
Lemma lem142374 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (@lem142371 m n h1 (@lem142363 m n h2)). Qed.
Lemma lem142375 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : term162.
Proof. exact (fun h0 : ~ False => @lem142374 m n h1 h2). Qed.
Lemma lem142377 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem142378 : term162 = False.
Proof. exact (@lem142377 False). Qed.
Lemma lem142379 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142378) (@lem142375 m n h1 h2)). Qed.
Lemma lem142381 (m : nat) (n : nat) (h1 : term226 m n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (proj2 (@lem140882 m n h1)). Qed.
Lemma lem142382 (m : nat) (n : nat) (h1 : term226 m n) : term279 n.
Proof. exact (fun h0 : term50 n => @lem142381 m n h1). Qed.
Lemma lem142384 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem142385 (n : nat) : (term279 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (@lem142384 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem142386 (m : nat) (n : nat) (h1 : term226 m n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (EQ_MP (@lem142385 n) (@lem142382 m n h1)). Qed.
Lemma lem142389 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem142391 (n : nat) : (term50 n) = (term280 n).
Proof. exact (@lem142389 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem142394 (m : nat) (n : nat) (h1 : term278 m n) : term280 n.
Proof. exact (EQ_MP (@lem142391 n) (@lem142054 m n h1)). Qed.
Lemma lem142397 (m : nat) (n : nat) (h1 : term226 m n) (h2 : term278 m n) : False.
Proof. exact (@lem142394 m n h2 (@lem142386 m n h1)). Qed.
Lemma lem142398 (m : nat) (n : nat) (h1 : term226 m n) (h2 : term278 m n) : term162.
Proof. exact (fun h0 : ~ False => @lem142397 m n h1 h2). Qed.
Lemma lem142400 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem142401 : term162 = False.
Proof. exact (@lem142400 False). Qed.
Lemma lem142402 (m : nat) (n : nat) (h1 : term226 m n) (h2 : term278 m n) : False.
Proof. exact (EQ_MP (@lem142401) (@lem142398 m n h1 h2)). Qed.
Lemma lem142404 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem142405 (m : nat) (n : nat) (h1 : Peano.le m n) : term159 m n.
Proof. exact (fun h0 : term10 m n => @lem142404 m n h1). Qed.
Lemma lem142407 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem142408 (m : nat) (n : nat) : (term159 m n) = (Peano.le m n).
Proof. exact (@lem142407 (Peano.le m n)). Qed.
Lemma lem142409 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (EQ_MP (@lem142408 m n) (@lem142405 m n h1)). Qed.
Lemma lem142412 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem142414 (m : nat) (n : nat) : (term10 m n) = (term161 m n).
Proof. exact (@lem142412 (Peano.le m n)). Qed.
Lemma lem142417 (m : nat) (n : nat) (h1 : term10 m n) : term161 m n.
Proof. exact (EQ_MP (@lem142414 m n) (@lem142096 m n h1)). Qed.
Lemma lem142420 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (@lem142417 m n h1 (@lem142409 m n h2)). Qed.
Lemma lem142421 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : term162.
Proof. exact (fun h0 : ~ False => @lem142420 m n h1 h2). Qed.
Lemma lem142423 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem142424 : term162 = False.
Proof. exact (@lem142423 False). Qed.
Lemma lem142425 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142424) (@lem142421 m n h1 h2)). Qed.
Lemma lem142427 (m : nat) (n : nat) (h1 : term223 m n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (proj2 (@lem140901 m n h1)). Qed.
Lemma lem142428 (m : nat) (n : nat) (h1 : term223 m n) : term279 n.
Proof. exact (fun h0 : term50 n => @lem142427 m n h1). Qed.
Lemma lem142430 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem142431 (n : nat) : (term279 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (@lem142430 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem142432 (m : nat) (n : nat) (h1 : term223 m n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (EQ_MP (@lem142431 n) (@lem142428 m n h1)). Qed.
Lemma lem142435 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem142437 (n : nat) : (term50 n) = (term280 n).
Proof. exact (@lem142435 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem142440 (m : nat) (n : nat) (h1 : term278 m n) : term280 n.
Proof. exact (EQ_MP (@lem142437 n) (@lem142162 m n h1)). Qed.
Lemma lem142443 (m : nat) (n : nat) (h1 : term223 m n) (h2 : term278 m n) : False.
Proof. exact (@lem142440 m n h2 (@lem142432 m n h1)). Qed.
Lemma lem142444 (m : nat) (n : nat) (h1 : term223 m n) (h2 : term278 m n) : term162.
Proof. exact (fun h0 : ~ False => @lem142443 m n h1 h2). Qed.
Lemma lem142446 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem142447 : term162 = False.
Proof. exact (@lem142446 False). Qed.
Lemma lem142448 (m : nat) (n : nat) (h1 : term223 m n) (h2 : term278 m n) : False.
Proof. exact (EQ_MP (@lem142447) (@lem142444 m n h1 h2)). Qed.
Lemma lem142450 (m : nat) (n : nat) (h1 : term277 m n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (proj2 (@lem140913 m n h1)). Qed.
Lemma lem142451 (m : nat) (n : nat) (h1 : term277 m n) : term279 n.
Proof. exact (fun h0 : term50 n => @lem142450 m n h1). Qed.
Lemma lem142453 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem142454 (n : nat) : (term279 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (@lem142453 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem142455 (m : nat) (n : nat) (h1 : term277 m n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (EQ_MP (@lem142454 n) (@lem142451 m n h1)). Qed.
Lemma lem142458 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem142460 (n : nat) : (term50 n) = (term280 n).
Proof. exact (@lem142458 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem142463 (m : nat) (n : nat) (h1 : term224 m n) : term280 n.
Proof. exact (EQ_MP (@lem142460 n) (@lem142212 m n h1)). Qed.
Lemma lem142466 (m : nat) (n : nat) (h1 : term277 m n) (h2 : term224 m n) : False.
Proof. exact (@lem142463 m n h2 (@lem142455 m n h1)). Qed.
Lemma lem142467 (m : nat) (n : nat) (h1 : term277 m n) (h2 : term224 m n) : term162.
Proof. exact (fun h0 : ~ False => @lem142466 m n h1 h2). Qed.
Lemma lem142469 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem142470 : term162 = False.
Proof. exact (@lem142469 False). Qed.
Lemma lem142471 (m : nat) (n : nat) (h1 : term277 m n) (h2 : term224 m n) : False.
Proof. exact (EQ_MP (@lem142470) (@lem142467 m n h1 h2)). Qed.
Lemma lem142473 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem142474 (m : nat) (n : nat) (h1 : Peano.le m n) : term159 m n.
Proof. exact (fun h0 : term10 m n => @lem142473 m n h1). Qed.
Lemma lem142476 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem142477 (m : nat) (n : nat) : (term159 m n) = (Peano.le m n).
Proof. exact (@lem142476 (Peano.le m n)). Qed.
Lemma lem142478 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (EQ_MP (@lem142477 m n) (@lem142474 m n h1)). Qed.
Lemma lem142481 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem142483 (m : nat) (n : nat) : (term10 m n) = (term161 m n).
Proof. exact (@lem142481 (Peano.le m n)). Qed.
Lemma lem142486 (m : nat) (n : nat) (h1 : term10 m n) : term161 m n.
Proof. exact (EQ_MP (@lem142483 m n) (@lem142258 m n h1)). Qed.
Lemma lem142489 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (@lem142486 m n h1 (@lem142478 m n h2)). Qed.
Lemma lem142490 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : term162.
Proof. exact (fun h0 : ~ False => @lem142489 m n h1 h2). Qed.
Lemma lem142492 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem142493 : term162 = False.
Proof. exact (@lem142492 False). Qed.
Lemma lem142494 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142493) (@lem142490 m n h1 h2)). Qed.
Lemma lem142495 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.le m n => @lem142494 m n h1 h2) (fun h3 : False => @lem142260 m n h2)). Qed.
Lemma lem142496 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142495 m n h1 h2) (@lem142260 m n h2)). Qed.
Lemma lem142497 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : (term10 m n) = False.
Proof. exact (prop_ext (fun h3 : term10 m n => @lem142496 m n h1 h2) (fun h3 : False => @lem142258 m n h1)). Qed.
Lemma lem142498 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142497 m n h1 h2) (@lem142258 m n h1)). Qed.
Lemma lem142499 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.le m n => @lem142425 m n h1 h2) (fun h3 : False => @lem142098 m n h2)). Qed.
Lemma lem142500 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142499 m n h1 h2) (@lem142098 m n h2)). Qed.
Lemma lem142501 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : (term10 m n) = False.
Proof. exact (prop_ext (fun h3 : term10 m n => @lem142500 m n h1 h2) (fun h3 : False => @lem142096 m n h1)). Qed.
Lemma lem142502 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142501 m n h1 h2) (@lem142096 m n h1)). Qed.
Lemma lem142503 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.le m n => @lem142379 m n h1 h2) (fun h3 : False => @lem141990 m n h2)). Qed.
Lemma lem142504 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142503 m n h1 h2) (@lem141990 m n h2)). Qed.
Lemma lem142505 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : (term10 m n) = False.
Proof. exact (prop_ext (fun h3 : term10 m n => @lem142504 m n h1 h2) (fun h3 : False => @lem141988 m n h1)). Qed.
Lemma lem142506 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142505 m n h1 h2) (@lem141988 m n h1)). Qed.
Lemma lem142507 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.le m n => @lem142356 m n h1 h2) (fun h3 : False => @lem141936 m n h2)). Qed.
Lemma lem142508 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142507 m n h1 h2) (@lem141936 m n h2)). Qed.
Lemma lem142509 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : (term10 m n) = False.
Proof. exact (prop_ext (fun h3 : term10 m n => @lem142508 m n h1 h2) (fun h3 : False => @lem141934 m n h1)). Qed.
Lemma lem142510 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142509 m n h1 h2) (@lem141934 m n h1)). Qed.
Lemma lem142511 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.le m n => @lem142498 m n h1 h2) (fun h3 : False => @lem141654 m n h2)). Qed.
Lemma lem142512 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142511 m n h1 h2) (@lem141654 m n h2)). Qed.
Lemma lem142513 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : (term10 m n) = False.
Proof. exact (prop_ext (fun h3 : term10 m n => @lem142512 m n h1 h2) (fun h3 : False => @lem141650 m n h1)). Qed.
Lemma lem142514 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142513 m n h1 h2) (@lem141650 m n h1)). Qed.
Lemma lem142515 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.le m n => @lem142502 m n h1 h2) (fun h3 : False => @lem141342 m n h2)). Qed.
Lemma lem142516 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142515 m n h1 h2) (@lem141342 m n h2)). Qed.
Lemma lem142517 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : (term10 m n) = False.
Proof. exact (prop_ext (fun h3 : term10 m n => @lem142516 m n h1 h2) (fun h3 : False => @lem141338 m n h1)). Qed.
Lemma lem142518 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142517 m n h1 h2) (@lem141338 m n h1)). Qed.
Lemma lem142519 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.le m n => @lem142506 m n h1 h2) (fun h3 : False => @lem141134 m n h2)). Qed.
Lemma lem142520 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142519 m n h1 h2) (@lem141134 m n h2)). Qed.
Lemma lem142521 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : (term10 m n) = False.
Proof. exact (prop_ext (fun h3 : term10 m n => @lem142520 m n h1 h2) (fun h3 : False => @lem141130 m n h1)). Qed.
Lemma lem142522 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142521 m n h1 h2) (@lem141130 m n h1)). Qed.
Lemma lem142523 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.le m n => @lem142510 m n h1 h2) (fun h3 : False => @lem141030 m n h2)). Qed.
Lemma lem142524 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142523 m n h1 h2) (@lem141030 m n h2)). Qed.
Lemma lem142525 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : (term10 m n) = False.
Proof. exact (prop_ext (fun h3 : term10 m n => @lem142524 m n h1 h2) (fun h3 : False => @lem141026 m n h1)). Qed.
Lemma lem142526 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142525 m n h1 h2) (@lem141026 m n h1)). Qed.
Lemma lem142527 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.le m n => @lem142514 m n h1 h2) (fun h3 : False => @lem141654 m n h2)). Qed.
Lemma lem142528 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142527 m n h1 h2) (@lem141654 m n h2)). Qed.
Lemma lem142529 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : (term10 m n) = False.
Proof. exact (prop_ext (fun h3 : term10 m n => @lem142528 m n h1 h2) (fun h3 : False => @lem141650 m n h1)). Qed.
Lemma lem142530 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142529 m n h1 h2) (@lem141650 m n h1)). Qed.
Lemma lem142531 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.le m n => @lem142518 m n h1 h2) (fun h3 : False => @lem141342 m n h2)). Qed.
Lemma lem142532 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142531 m n h1 h2) (@lem141342 m n h2)). Qed.
Lemma lem142533 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : (term10 m n) = False.
Proof. exact (prop_ext (fun h3 : term10 m n => @lem142532 m n h1 h2) (fun h3 : False => @lem141338 m n h1)). Qed.
Lemma lem142534 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142533 m n h1 h2) (@lem141338 m n h1)). Qed.
Lemma lem142535 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.le m n => @lem142522 m n h1 h2) (fun h3 : False => @lem141134 m n h2)). Qed.
Lemma lem142536 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142535 m n h1 h2) (@lem141134 m n h2)). Qed.
Lemma lem142537 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : (term10 m n) = False.
Proof. exact (prop_ext (fun h3 : term10 m n => @lem142536 m n h1 h2) (fun h3 : False => @lem141130 m n h1)). Qed.
Lemma lem142538 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142537 m n h1 h2) (@lem141130 m n h1)). Qed.
Lemma lem142539 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h3 : Peano.le m n => @lem142526 m n h1 h2) (fun h3 : False => @lem141030 m n h2)). Qed.
Lemma lem142540 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142539 m n h1 h2) (@lem141030 m n h2)). Qed.
Lemma lem142541 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : (term10 m n) = False.
Proof. exact (prop_ext (fun h3 : term10 m n => @lem142540 m n h1 h2) (fun h3 : False => @lem141026 m n h1)). Qed.
Lemma lem142542 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142541 m n h1 h2) (@lem141026 m n h1)). Qed.
Lemma lem142543 (m : nat) (n : nat) (h1 : term10 m n) (h2 : term236 m n) (h3 : term224 m n) (h4 : Peano.le m n) : False.
Proof. exact (or_elim (@lem140876 m n h2) (fun h0 : term277 m n => @lem142471 m n h0 h3) (fun h0 : term278 m n => @lem142530 m n h1 h4)). Qed.
Lemma lem142544 (m : nat) (n : nat) (h1 : term10 m n) (h2 : term236 m n) (h3 : term223 m n) (h4 : Peano.le m n) : False.
Proof. exact (or_elim (@lem140876 m n h2) (fun h0 : term277 m n => @lem142534 m n h1 h4) (fun h0 : term278 m n => @lem142448 m n h3 h0)). Qed.
Lemma lem142545 (m : nat) (n : nat) (h1 : term10 m n) (h2 : term236 m n) (h3 : term265 m n) (h4 : Peano.le m n) : False.
Proof. exact (or_elim (@lem140899 m n h3) (fun h0 : term223 m n => @lem142544 m n h1 h2 h0 h4) (fun h0 : term224 m n => @lem142543 m n h1 h2 h0 h4)). Qed.
Lemma lem142546 (m : nat) (n : nat) (h1 : term10 m n) (h2 : term236 m n) (h3 : term226 m n) (h4 : Peano.le m n) : False.
Proof. exact (or_elim (@lem140876 m n h2) (fun h0 : term277 m n => @lem142538 m n h1 h4) (fun h0 : term278 m n => @lem142402 m n h3 h0)). Qed.
Lemma lem142547 (m : nat) (n : nat) (h1 : term10 m n) (h2 : term236 m n) (h3 : term225 m n) (h4 : Peano.le m n) : False.
Proof. exact (or_elim (@lem140876 m n h2) (fun h0 : term277 m n => @lem142333 m n h3 h0) (fun h0 : term278 m n => @lem142542 m n h1 h4)). Qed.
Lemma lem142548 (m : nat) (n : nat) (h1 : term10 m n) (h2 : term236 m n) (h3 : term267 m n) (h4 : Peano.le m n) : False.
Proof. exact (or_elim (@lem140879 m n h3) (fun h0 : term225 m n => @lem142547 m n h1 h2 h0 h4) (fun h0 : term226 m n => @lem142546 m n h1 h2 h0 h4)). Qed.
Lemma lem142549 (m : nat) (n : nat) (h1 : term10 m n) (h2 : term236 m n) (h3 : Peano.le m n) : False.
Proof. exact (or_elim (@lem140875 m n h2) (fun h0 : term267 m n => @lem142548 m n h1 h2 h0 h3) (fun h0 : term265 m n => @lem142545 m n h1 h2 h0 h3)). Qed.
Lemma lem142550 (m : nat) (n : nat) (h1 : term10 m n) (h2 : term236 m n) (h3 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h4 : Peano.le m n => @lem142549 m n h1 h2 h3) (fun h4 : False => @lem140664 m n h3)). Qed.
Lemma lem142551 (m : nat) (n : nat) (h1 : term10 m n) (h2 : term236 m n) (h3 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142550 m n h1 h2 h3) (@lem140664 m n h3)). Qed.
Lemma lem142552 (m : nat) (n : nat) (h1 : term10 m n) (h2 : term236 m n) (h3 : Peano.le m n) : (term10 m n) = False.
Proof. exact (prop_ext (fun h4 : term10 m n => @lem142551 m n h1 h2 h3) (fun h4 : False => @lem140658 m n h1)). Qed.
Lemma lem142553 (m : nat) (n : nat) (h1 : term10 m n) (h2 : term236 m n) (h3 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142552 m n h1 h2 h3) (@lem140658 m n h1)). Qed.
Lemma lem142554 (m : nat) (n : nat) (h1 : term10 m n) (h2 : term236 m n) (h3 : Peano.le m n) : (Peano.le m n) = False.
Proof. exact (prop_ext (fun h4 : Peano.le m n => @lem142553 m n h1 h2 h3) (fun h4 : False => @lem140275 m n h3)). Qed.
Lemma lem142555 (m : nat) (n : nat) (h1 : term10 m n) (h2 : term236 m n) (h3 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142554 m n h1 h2 h3) (@lem140275 m n h3)). Qed.
Lemma lem142556 (m : nat) (n : nat) (h1 : term10 m n) (h2 : term236 m n) (h3 : Peano.le m n) : (term10 m n) = False.
Proof. exact (prop_ext (fun h4 : term10 m n => @lem142555 m n h1 h2 h3) (fun h4 : False => @lem140269 m n h1)). Qed.
Lemma lem142557 (m : nat) (n : nat) (h1 : term10 m n) (h2 : term236 m n) (h3 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142556 m n h1 h2 h3) (@lem140269 m n h1)). Qed.
Lemma lem142558 (m : nat) (n : nat) (h1 : term10 m n) (h2 : term236 m n) (h3 : Peano.le m n) : term241.
Proof. exact (fun h0 : term243 => @lem142557 m n h1 h2 h3). Qed.
Lemma lem142559 : term241 = term242.
Proof. exact (@lem69 term243). Qed.
Lemma lem142560 (m : nat) (n : nat) (h1 : term10 m n) (h2 : term236 m n) (h3 : Peano.le m n) : term242.
Proof. exact (EQ_MP (@lem142559) (@lem142558 m n h1 h2 h3)). Qed.
Lemma lem142561 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : term246 m n.
Proof. exact (fun h0 : term236 m n => @lem142560 m n h1 h0 h2). Qed.
Lemma lem142562 (m : nat) (n : nat) (h1 : term10 m n) : term248 m n.
Proof. exact (fun h0 : Peano.le m n => @lem142561 m n h1 h0). Qed.
Lemma lem142563 (m : nat) (n : nat) : term250 m n.
Proof. exact (fun h0 : term10 m n => @lem142562 m n h0). Qed.
Lemma lem142568 (n : nat) : term254 n.
Proof. exact (fun m : nat => @lem142563 m n). Qed.
Lemma lem142573 : term258.
Proof. exact (fun n : nat => @lem142568 n). Qed.
Lemma lem142574 : term257.
Proof. exact (EQ_MP (@lem140259) (@lem142573)). Qed.
Lemma lem142575 (n : nat) : term281 n.
Proof. exact (@lem142574 n). Qed.
Lemma lem142576 (n : nat) : (term281 n) = (term253 n).
Proof. exact (eq_refl (term281 n)). Qed.
Lemma lem142577 (n : nat) : term253 n.
Proof. exact (EQ_MP (@lem142576 n) (@lem142575 n)). Qed.
Lemma lem142578 (n : nat) (m : nat) : term282 n m.
Proof. exact (@lem142577 n m). Qed.
Lemma lem142579 (m : nat) (n : nat) : (term282 n m) = (term237 m n).
Proof. exact (eq_refl (term282 n m)). Qed.
Lemma lem142580 (m : nat) (n : nat) : term237 m n.
Proof. exact (EQ_MP (@lem142579 m n) (@lem142578 n m)). Qed.
Lemma lem142582 (m : nat) (n : nat) : term237 m n.
Proof. exact (@lem140111 m n (@lem142580 m n)). Qed.
Lemma lem142583 (m : nat) (n : nat) (h1 : term10 m n) : term247 m n.
Proof. exact (@lem142582 m n (@lem137196 m n h1)). Qed.
Lemma lem142584 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : term245 m n.
Proof. exact (@lem142583 m n h1 (@lem137180 m n h2)). Qed.
Lemma lem142585 (m : nat) (n : nat) (h1 : term10 m n) (h2 : term236 m n) (h3 : Peano.le m n) : term241.
Proof. exact (@lem142584 m n h1 h3 (@lem140096 m n h2)). Qed.
Lemma lem142586 (m : nat) (n : nat) (h1 : term10 m n) (h2 : term236 m n) (h3 : Peano.le m n) : False.
Proof. exact (@lem142585 m n h1 h2 h3 (@lem125496)). Qed.
Lemma lem142587 (m : nat) (n : nat) (h1 : term10 m n) (h2 : term236 m n) (h3 : Peano.le m n) : (term236 m n) = False.
Proof. exact (prop_ext (fun h4 : term236 m n => @lem142586 m n h1 h2 h3) (fun h4 : False => @lem140096 m n h2)). Qed.
Lemma lem142588 (m : nat) (n : nat) (h1 : term10 m n) (h2 : term236 m n) (h3 : Peano.le m n) : False.
Proof. exact (EQ_MP (@lem142587 m n h1 h2 h3) (@lem140096 m n h2)). Qed.
Lemma lem142589 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : term235 m n.
Proof. exact (fun h0 : term236 m n => @lem142588 m n h1 h0 h2). Qed.
Lemma lem142590 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : term234 m n.
Proof. exact (EQ_MP (@lem140095 m n) (@lem142589 m n h1 h2)). Qed.
Lemma lem142592 (p : Prop) : p = (term11 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem142593 (m : nat) (n : nat) : (term283 m n) = (term284 m n).
Proof. exact (@lem142592 (term283 m n)). Qed.
Lemma lem142594 (m : nat) (n : nat) : (term284 m n) = (term283 m n).
Proof. exact (SYM (@lem142593 m n)). Qed.
Lemma lem142595 (m : nat) (n : nat) (h1 : term285 m n) : term285 m n.
Proof. exact (h1). Qed.
Lemma lem142598 (m : nat) (n : nat) (h1 : term286 m n) : term286 m n.
Proof. exact (h1). Qed.
Lemma lem142599 (m : nat) (n : nat) : term287 m n.
Proof. exact (fun h0 : term286 m n => @lem142598 m n h0). Qed.
Lemma lem142600 (m : nat) (n : nat) (h1 : term287 m n) : term287 m n.
Proof. exact (h1). Qed.
Lemma lem142601 (m : nat) (n : nat) (h1 : term286 m n) : term286 m n.
Proof. exact (h1). Qed.
Lemma lem142602 (m : nat) (n : nat) (h1 : term286 m n) (h2 : term287 m n) : term286 m n.
Proof. exact (@lem142600 m n h2 (@lem142601 m n h1)). Qed.
Lemma lem142603 (m : nat) (n : nat) (h1 : term286 m n) : term288 m n.
Proof. exact (fun h0 : term287 m n => @lem142602 m n h1 h0). Qed.
Lemma lem142604 (m : nat) (n : nat) (h1 : term287 m n) : term287 m n.
Proof. exact (h1). Qed.
Lemma lem142605 (m : nat) (n : nat) (h1 : term286 m n) (h2 : term287 m n) : term286 m n.
Proof. exact (@lem142603 m n h1 (@lem142604 m n h2)). Qed.
Lemma lem142606 (m : nat) (n : nat) (h1 : term287 m n) : term287 m n.
Proof. exact (fun h0 : term286 m n => @lem142605 m n h0 h1). Qed.
Lemma lem142607 (m : nat) (n : nat) : term289 m n.
Proof. exact (fun h0 : term287 m n => @lem142606 m n h0). Qed.
Lemma lem142610 (m : nat) (n : nat) : term287 m n.
Proof. exact (@lem142607 m n (@lem142599 m n)). Qed.
Lemma lem142628 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem142629 : term241 = term242.
Proof. exact (@lem142628 term243). Qed.
Lemma lem142638 (m : nat) (n : nat) : (term290 m n) = (term290 m n).
Proof. exact (eq_refl (term290 m n)). Qed.
Lemma lem142639 (m : nat) (n : nat) : (term291 m n) = (term292 m n).
Proof. exact (MK_COMB (@lem142638 m n) (@lem142629)). Qed.
Lemma lem142642 (n : nat) (m : nat) : (term36 n m) = (term36 n m).
Proof. exact (eq_refl (term36 n m)). Qed.
Lemma lem142643 (m : nat) (n : nat) : (term293 m n) = (term294 m n).
Proof. exact (MK_COMB (@lem142642 n m) (@lem142639 m n)). Qed.
Lemma lem142646 (m : nat) (n : nat) : (term249 m n) = (term249 m n).
Proof. exact (eq_refl (term249 m n)). Qed.
Lemma lem142647 (m : nat) (n : nat) : (term286 m n) = (term295 m n).
Proof. exact (MK_COMB (@lem142646 m n) (@lem142643 m n)). Qed.
Lemma lem142650 (n : nat) : (term296 n) = (term297 n).
Proof. exact (fun_ext (fun m : nat => @lem142647 m n)). Qed.
Lemma lem142651 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem142652 (n : nat) : (term298 n) = (term299 n).
Proof. exact (MK_COMB (@lem142651) (@lem142650 n)). Qed.
Lemma lem142657 : term300 = term301.
Proof. exact (fun_ext (fun n : nat => @lem142652 n)). Qed.
Lemma lem142658 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem142667 : term302 = term303.
Proof. exact (MK_COMB (@lem142658) (@lem142657)). Qed.
Lemma lem142676 (m : nat) (n : nat) : ((term259 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))) = ((term259 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))).
Proof. exact (eq_refl ((term259 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)))). Qed.
Lemma lem142677 (m : nat) : (term260 m) = (term260 m).
Proof. exact (fun_ext (fun n : nat => @lem142676 m n)). Qed.
Lemma lem142678 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem142679 (m : nat) : (term261 m) = (term261 m).
Proof. exact (MK_COMB (@lem142678) (@lem142677 m)). Qed.
Lemma lem142680 : term262 = term262.
Proof. exact (fun_ext (fun m : nat => @lem142679 m)). Qed.
Lemma lem142681 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem142682 : term243 = term243.
Proof. exact (MK_COMB (@lem142681) (@lem142680)). Qed.
Lemma lem142683 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem142684 : term242 = term242.
Proof. exact (MK_COMB (@lem142683) (@lem142682)). Qed.
Lemma lem142705 (m : nat) (n : nat) : (term290 m n) = (term290 m n).
Proof. exact (eq_refl (term290 m n)). Qed.
Lemma lem142706 (m : nat) (n : nat) : (term292 m n) = (term292 m n).
Proof. exact (MK_COMB (@lem142705 m n) (@lem142684)). Qed.
Lemma lem142709 (n : nat) (m : nat) : (term36 n m) = (term36 n m).
Proof. exact (eq_refl (term36 n m)). Qed.
Lemma lem142710 (m : nat) (n : nat) : (term294 m n) = (term294 m n).
Proof. exact (MK_COMB (@lem142709 n m) (@lem142706 m n)). Qed.
Lemma lem142715 (m : nat) (n : nat) : (term249 m n) = (term249 m n).
Proof. exact (eq_refl (term249 m n)). Qed.
Lemma lem142716 (m : nat) (n : nat) : (term295 m n) = (term295 m n).
Proof. exact (MK_COMB (@lem142715 m n) (@lem142710 m n)). Qed.
Lemma lem142717 (n : nat) : (term297 n) = (term297 n).
Proof. exact (fun_ext (fun m : nat => @lem142716 m n)). Qed.
Lemma lem142718 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem142719 (n : nat) : (term299 n) = (term299 n).
Proof. exact (MK_COMB (@lem142718) (@lem142717 n)). Qed.
Lemma lem142720 : term301 = term301.
Proof. exact (fun_ext (fun n : nat => @lem142719 n)). Qed.
Lemma lem142721 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem142722 : term303 = term303.
Proof. exact (MK_COMB (@lem142721) (@lem142720)). Qed.
Lemma lem142757 : term302 = term303.
Proof. exact (TRANS (@lem142667) (@lem142722)). Qed.
Lemma lem142758 : term303 = term302.
Proof. exact (SYM (@lem142757)). Qed.
Lemma lem142761 (m : nat) (n : nat) (h1 : term285 m n) : term285 m n.
Proof. exact (h1). Qed.
Lemma lem142762 (h1 : term243) : term243.
Proof. exact (h1). Qed.
Lemma lem142789 (n : nat) (m : nat) : ((term233 m n) = (Coq.Arith.PeanoNat.Nat.Even m)) = (term263 n m).
Proof. exact (@lem17500 (term233 m n) (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem142806 (m : nat) (n : nat) : (term52 m n) = (term53 m n).
Proof. exact (@lem17646 (Coq.Arith.PeanoNat.Nat.Even m) (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem142817 (m : nat) (n : nat) : ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)) = (term54 m n).
Proof. exact (@lem17500 (Coq.Arith.PeanoNat.Nat.Even m) (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem142819 (m : nat) (n : nat) : (term61 m n) = (term61 m n).
Proof. exact (eq_refl (term61 m n)). Qed.
Lemma lem142820 (m : nat) (n : nat) : (term264 m n) = (term265 m n).
Proof. exact (MK_COMB (@lem142819 m n) (@lem142817 m n)). Qed.
Lemma lem142822 (m : nat) (n : nat) : (term64 m n) = (term64 m n).
Proof. exact (eq_refl (term64 m n)). Qed.
Lemma lem142823 (m : nat) (n : nat) : (term266 m n) = (term267 m n).
Proof. exact (MK_COMB (@lem142822 m n) (@lem142806 m n)). Qed.
Lemma lem142824 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem142825 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (MK_COMB (@lem142824) (@lem142823 m n)). Qed.
Lemma lem142826 (m : nat) (n : nat) : (term270 m n) = (term271 m n).
Proof. exact (MK_COMB (@lem142825 m n) (@lem142820 m n)). Qed.
Lemma lem142827 (m : nat) (n : nat) : (term272 m n) = (term270 m n).
Proof. exact (@lem17646 (term12 m n) ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))). Qed.
Lemma lem142828 (m : nat) (n : nat) : (term272 m n) = (term271 m n).
Proof. exact (TRANS (@lem142827 m n) (@lem142826 m n)). Qed.
Lemma lem142829 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem142830 (n : nat) (m : nat) : (term273 n m) = (term274 n m).
Proof. exact (MK_COMB (@lem142829) (@lem142789 n m)). Qed.
Lemma lem142831 (m : nat) (n : nat) : (term304 m n) = (term305 m n).
Proof. exact (MK_COMB (@lem142830 n m) (@lem142828 m n)). Qed.
Lemma lem142832 (m : nat) (n : nat) : (term285 m n) = (term304 m n).
Proof. exact (@lem17362 ((term233 m n) = (Coq.Arith.PeanoNat.Nat.Even m)) ((term12 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)))). Qed.
Lemma lem142837 (m : nat) (n : nat) : (term285 m n) = (term305 m n).
Proof. exact (TRANS (@lem142832 m n) (@lem142831 m n)). Qed.
Lemma lem142855 (m : nat) (n : nat) : (term52 m n) = (term306 m n).
Proof. exact (@lem17930 (Coq.Arith.PeanoNat.Nat.Even m) (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem142866 (m : nat) (n : nat) : ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)) = (term307 m n).
Proof. exact (@lem17784 (Coq.Arith.PeanoNat.Nat.Even m) (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem142868 (m : nat) (n : nat) : (term308 m n) = (term308 m n).
Proof. exact (eq_refl (term308 m n)). Qed.
Lemma lem142869 (m : nat) (n : nat) : (term309 m n) = (term310 m n).
Proof. exact (MK_COMB (@lem142868 m n) (@lem142866 m n)). Qed.
Lemma lem142871 (m : nat) (n : nat) : (term311 m n) = (term311 m n).
Proof. exact (eq_refl (term311 m n)). Qed.
Lemma lem142872 (m : nat) (n : nat) : (term312 m n) = (term313 m n).
Proof. exact (MK_COMB (@lem142871 m n) (@lem142855 m n)). Qed.
Lemma lem142873 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem142874 (m : nat) (n : nat) : (term314 m n) = (term315 m n).
Proof. exact (MK_COMB (@lem142873) (@lem142872 m n)). Qed.
Lemma lem142875 (m : nat) (n : nat) : (term316 m n) = (term317 m n).
Proof. exact (MK_COMB (@lem142874 m n) (@lem142869 m n)). Qed.
Lemma lem142876 (m : nat) (n : nat) : ((term259 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))) = (term316 m n).
Proof. exact (@lem17784 (term259 m n) ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))). Qed.
Lemma lem142877 (m : nat) (n : nat) : ((term259 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n))) = (term317 m n).
Proof. exact (TRANS (@lem142876 m n) (@lem142875 m n)). Qed.
Lemma lem142878 (m : nat) : (term260 m) = (term318 m).
Proof. exact (fun_ext (fun n : nat => @lem142877 m n)). Qed.
Lemma lem142879 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem142880 (m : nat) : (term261 m) = (term319 m).
Proof. exact (MK_COMB (@lem142879) (@lem142878 m)). Qed.
Lemma lem142881 : term262 = term320.
Proof. exact (fun_ext (fun m : nat => @lem142880 m)). Qed.
Lemma lem142882 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem142883 : term243 = term321.
Proof. exact (MK_COMB (@lem142882) (@lem142881)). Qed.
Lemma lem142889 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term83 A P Q) = (term84 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem142890 (P : nat -> Prop) (Q : nat -> Prop) : (term85 P Q) = (term86 P Q).
Proof. exact (@lem142889 nat P Q). Qed.
Lemma lem142891 (m : nat) : (term322 m) = (term323 m).
Proof. exact (@lem142890 (term324 m) (term325 m)). Qed.
Lemma lem142892 (m : nat) (n : nat) : (term326 m n) = (term313 m n).
Proof. exact (eq_refl (term326 m n)). Qed.
Lemma lem142893 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem142894 (m : nat) (n : nat) : (term327 m n) = (term315 m n).
Proof. exact (MK_COMB (@lem142893) (@lem142892 m n)). Qed.
Lemma lem142895 (m : nat) (n : nat) : (term328 m n) = (term310 m n).
Proof. exact (eq_refl (term328 m n)). Qed.
Lemma lem142896 (m : nat) (n : nat) : (term329 m n) = (term317 m n).
Proof. exact (MK_COMB (@lem142894 m n) (@lem142895 m n)). Qed.
Lemma lem142897 (m : nat) : (term330 m) = (term318 m).
Proof. exact (fun_ext (fun n : nat => @lem142896 m n)). Qed.
Lemma lem142898 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem142899 (m : nat) : (term322 m) = (term319 m).
Proof. exact (MK_COMB (@lem142898) (@lem142897 m)). Qed.
Lemma lem142900 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem142901 (m : nat) : (term331 m) = (term332 m).
Proof. exact (MK_COMB (@lem142900) (@lem142899 m)). Qed.
Lemma lem142902 (m : nat) (n : nat) : (term326 m n) = (term313 m n).
Proof. exact (eq_refl (term326 m n)). Qed.
Lemma lem142903 (m : nat) : (term333 m) = (term324 m).
Proof. exact (fun_ext (fun n : nat => @lem142902 m n)). Qed.
Lemma lem142904 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem142905 (m : nat) : (term334 m) = (term335 m).
Proof. exact (MK_COMB (@lem142904) (@lem142903 m)). Qed.
Lemma lem142906 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem142907 (m : nat) : (term336 m) = (term337 m).
Proof. exact (MK_COMB (@lem142906) (@lem142905 m)). Qed.
Lemma lem142908 (m : nat) (n : nat) : (term328 m n) = (term310 m n).
Proof. exact (eq_refl (term328 m n)). Qed.
Lemma lem142909 (m : nat) : (term338 m) = (term325 m).
Proof. exact (fun_ext (fun n : nat => @lem142908 m n)). Qed.
Lemma lem142910 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem142911 (m : nat) : (term339 m) = (term340 m).
Proof. exact (MK_COMB (@lem142910) (@lem142909 m)). Qed.
Lemma lem142912 (m : nat) : (term323 m) = (term341 m).
Proof. exact (MK_COMB (@lem142907 m) (@lem142911 m)). Qed.
Lemma lem142913 (m : nat) : ((term322 m) = (term323 m)) = ((term319 m) = (term341 m)).
Proof. exact (MK_COMB (@lem142901 m) (@lem142912 m)). Qed.
Lemma lem142914 (m : nat) : (term319 m) = (term341 m).
Proof. exact (EQ_MP (@lem142913 m) (@lem142891 m)). Qed.
Lemma lem143011 : term320 = term342.
Proof. exact (fun_ext (fun m : nat => @lem142914 m)). Qed.
Lemma lem143012 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem143013 : term321 = term343.
Proof. exact (MK_COMB (@lem143012) (@lem143011)). Qed.
Lemma lem143015 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term83 A P Q) = (term84 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem143016 (P : nat -> Prop) (Q : nat -> Prop) : (term85 P Q) = (term86 P Q).
Proof. exact (@lem143015 nat P Q). Qed.
Lemma lem143017 : term344 = term345.
Proof. exact (@lem143016 term346 term347). Qed.
Lemma lem143018 (m : nat) : (term348 m) = (term335 m).
Proof. exact (eq_refl (term348 m)). Qed.
Lemma lem143019 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem143020 (m : nat) : (term349 m) = (term337 m).
Proof. exact (MK_COMB (@lem143019) (@lem143018 m)). Qed.
Lemma lem143021 (m : nat) : (term350 m) = (term340 m).
Proof. exact (eq_refl (term350 m)). Qed.
Lemma lem143022 (m : nat) : (term351 m) = (term341 m).
Proof. exact (MK_COMB (@lem143020 m) (@lem143021 m)). Qed.
Lemma lem143023 : term352 = term342.
Proof. exact (fun_ext (fun m : nat => @lem143022 m)). Qed.
Lemma lem143024 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem143025 : term344 = term343.
Proof. exact (MK_COMB (@lem143024) (@lem143023)). Qed.
Lemma lem143026 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem143027 : term353 = term354.
Proof. exact (MK_COMB (@lem143026) (@lem143025)). Qed.
Lemma lem143028 (m : nat) : (term348 m) = (term335 m).
Proof. exact (eq_refl (term348 m)). Qed.
Lemma lem143029 : term355 = term346.
Proof. exact (fun_ext (fun m : nat => @lem143028 m)). Qed.
Lemma lem143030 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem143031 : term356 = term357.
Proof. exact (MK_COMB (@lem143030) (@lem143029)). Qed.
Lemma lem143032 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem143033 : term358 = term359.
Proof. exact (MK_COMB (@lem143032) (@lem143031)). Qed.
Lemma lem143034 (m : nat) : (term350 m) = (term340 m).
Proof. exact (eq_refl (term350 m)). Qed.
Lemma lem143035 : term360 = term347.
Proof. exact (fun_ext (fun m : nat => @lem143034 m)). Qed.
Lemma lem143036 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem143037 : term361 = term362.
Proof. exact (MK_COMB (@lem143036) (@lem143035)). Qed.
Lemma lem143038 : term345 = term363.
Proof. exact (MK_COMB (@lem143033) (@lem143037)). Qed.
Lemma lem143039 : (term344 = term345) = (term343 = term363).
Proof. exact (MK_COMB (@lem143027) (@lem143038)). Qed.
Lemma lem143040 : term343 = term363.
Proof. exact (EQ_MP (@lem143039) (@lem143017)). Qed.
Lemma lem143147 : term321 = term363.
Proof. exact (TRANS (@lem143013) (@lem143040)). Qed.
Lemma lem143148 : term243 = term363.
Proof. exact (TRANS (@lem142883) (@lem143147)). Qed.
Lemma lem143149 (h1 : term243) : term363.
Proof. exact (EQ_MP (@lem143148) (@lem142762 h1)). Qed.
Lemma lem143283 (m : nat) (n : nat) (h1 : term285 m n) : term305 m n.
Proof. exact (EQ_MP (@lem142837 m n) (@lem142761 m n h1)). Qed.
Lemma lem143320 (m : nat) (n : nat) : (term310 m n) = (term310 m n).
Proof. exact (eq_refl (term310 m n)). Qed.
Lemma lem143321 (m : nat) : (term325 m) = (term325 m).
Proof. exact (fun_ext (fun n : nat => @lem143320 m n)). Qed.
Lemma lem143322 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem143323 (m : nat) : (term340 m) = (term340 m).
Proof. exact (MK_COMB (@lem143322) (@lem143321 m)). Qed.
Lemma lem143324 : term347 = term347.
Proof. exact (fun_ext (fun m : nat => @lem143323 m)). Qed.
Lemma lem143325 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem143326 : term362 = term362.
Proof. exact (MK_COMB (@lem143325) (@lem143324)). Qed.
Lemma lem143361 (m : nat) (n : nat) : (term313 m n) = (term313 m n).
Proof. exact (eq_refl (term313 m n)). Qed.
Lemma lem143362 (m : nat) : (term324 m) = (term324 m).
Proof. exact (fun_ext (fun n : nat => @lem143361 m n)). Qed.
Lemma lem143363 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem143364 (m : nat) : (term335 m) = (term335 m).
Proof. exact (MK_COMB (@lem143363) (@lem143362 m)). Qed.
Lemma lem143365 : term346 = term346.
Proof. exact (fun_ext (fun m : nat => @lem143364 m)). Qed.
Lemma lem143366 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem143367 : term357 = term357.
Proof. exact (MK_COMB (@lem143366) (@lem143365)). Qed.
Lemma lem143368 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem143369 : term359 = term359.
Proof. exact (MK_COMB (@lem143368) (@lem143367)). Qed.
Lemma lem143370 : term363 = term363.
Proof. exact (MK_COMB (@lem143369) (@lem143326)). Qed.
Lemma lem143371 (h1 : term243) : term363.
Proof. exact (EQ_MP (@lem143370) (@lem143149 h1)). Qed.
Lemma lem143372 (h1 : term243) : term362.
Proof. exact (proj2 (@lem143371 h1)). Qed.
Lemma lem143373 (h1 : term243) : term357.
Proof. exact (proj1 (@lem143371 h1)). Qed.
Lemma lem143374 (m : nat) (n : nat) (h1 : term285 m n) : term271 m n.
Proof. exact (proj2 (@lem143283 m n h1)). Qed.
Lemma lem143375 (m : nat) (n : nat) (h1 : term285 m n) : term263 n m.
Proof. exact (proj1 (@lem143283 m n h1)). Qed.
Lemma lem143376 (m : nat) (n : nat) (h1 : term267 m n) : term267 m n.
Proof. exact (h1). Qed.
Lemma lem143377 (m : nat) (n : nat) (h1 : term265 m n) : term265 m n.
Proof. exact (h1). Qed.
Lemma lem143378 (m : nat) (n : nat) (h1 : term267 m n) : term53 m n.
Proof. exact (proj2 (@lem143376 m n h1)). Qed.
Lemma lem143380 (m : nat) (n : nat) (h1 : term225 m n) : term225 m n.
Proof. exact (h1). Qed.
Lemma lem143381 (m : nat) (n : nat) (h1 : term226 m n) : term226 m n.
Proof. exact (h1). Qed.
Lemma lem143384 (n : nat) (m : nat) (h1 : term277 n m) : term277 n m.
Proof. exact (h1). Qed.
Lemma lem143385 (n : nat) (m : nat) (h1 : term278 n m) : term278 n m.
Proof. exact (h1). Qed.
Lemma lem143392 (n : nat) (m : nat) (h1 : term277 n m) : term277 n m.
Proof. exact (h1). Qed.
Lemma lem143393 (n : nat) (m : nat) (h1 : term278 n m) : term278 n m.
Proof. exact (h1). Qed.
Lemma lem143398 (m : nat) (n : nat) (h1 : term265 m n) : term54 m n.
Proof. exact (proj2 (@lem143377 m n h1)). Qed.
Lemma lem143400 (m : nat) (n : nat) (h1 : term223 m n) : term223 m n.
Proof. exact (h1). Qed.
Lemma lem143401 (m : nat) (n : nat) (h1 : term224 m n) : term224 m n.
Proof. exact (h1). Qed.
Lemma lem143404 (n : nat) (m : nat) (h1 : term277 n m) : term277 n m.
Proof. exact (h1). Qed.
Lemma lem143405 (n : nat) (m : nat) (h1 : term278 n m) : term278 n m.
Proof. exact (h1). Qed.
Lemma lem143412 (n : nat) (m : nat) (h1 : term277 n m) : term277 n m.
Proof. exact (h1). Qed.
Lemma lem143413 (n : nat) (m : nat) (h1 : term278 n m) : term278 n m.
Proof. exact (h1). Qed.
Lemma lem143493 (m : nat) (n : nat) : (term310 m n) = (term364 m n).
Proof. exact (@lem19490 (term165 m n) (term365 m n) (term366 m n)). Qed.
Lemma lem143494 (m : nat) : (term325 m) = (term367 m).
Proof. exact (fun_ext (fun n : nat => @lem143493 m n)). Qed.
Lemma lem143495 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem143496 (m : nat) : (term340 m) = (term368 m).
Proof. exact (MK_COMB (@lem143495) (@lem143494 m)). Qed.
Lemma lem143497 : term347 = term369.
Proof. exact (fun_ext (fun m : nat => @lem143496 m)). Qed.
Lemma lem143498 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem143500 : term362 = term370.
Proof. exact (MK_COMB (@lem143498) (@lem143497)). Qed.
Lemma lem143501 (h1 : term243) : term370.
Proof. exact (EQ_MP (@lem143500) (@lem143372 h1)). Qed.
Lemma lem143767 (m : nat) (n : nat) : (term313 m n) = (term371 m n).
Proof. exact (@lem19490 (term372 m n) (term259 m n) (term373 m n)). Qed.
Lemma lem143768 (m : nat) : (term324 m) = (term374 m).
Proof. exact (fun_ext (fun n : nat => @lem143767 m n)). Qed.
Lemma lem143769 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem143770 (m : nat) : (term335 m) = (term375 m).
Proof. exact (MK_COMB (@lem143769) (@lem143768 m)). Qed.
Lemma lem143771 : term346 = term376.
Proof. exact (fun_ext (fun m : nat => @lem143770 m)). Qed.
Lemma lem143772 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem143774 : term357 = term377.
Proof. exact (MK_COMB (@lem143772) (@lem143771)). Qed.
Lemma lem143775 (h1 : term243) : term377.
Proof. exact (EQ_MP (@lem143774) (@lem143373 h1)). Qed.
Lemma lem143909 (m : nat) (n : nat) : (term310 m n) = (term364 m n).
Proof. exact (@lem19490 (term165 m n) (term365 m n) (term366 m n)). Qed.
Lemma lem143910 (m : nat) : (term325 m) = (term367 m).
Proof. exact (fun_ext (fun n : nat => @lem143909 m n)). Qed.
Lemma lem143911 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem143912 (m : nat) : (term340 m) = (term368 m).
Proof. exact (MK_COMB (@lem143911) (@lem143910 m)). Qed.
Lemma lem143913 : term347 = term369.
Proof. exact (fun_ext (fun m : nat => @lem143912 m)). Qed.
Lemma lem143914 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem143916 : term362 = term370.
Proof. exact (MK_COMB (@lem143914) (@lem143913)). Qed.
Lemma lem143917 (h1 : term243) : term370.
Proof. exact (EQ_MP (@lem143916) (@lem143372 h1)). Qed.
Lemma lem144183 (m : nat) (n : nat) : (term313 m n) = (term371 m n).
Proof. exact (@lem19490 (term372 m n) (term259 m n) (term373 m n)). Qed.
Lemma lem144184 (m : nat) : (term324 m) = (term374 m).
Proof. exact (fun_ext (fun n : nat => @lem144183 m n)). Qed.
Lemma lem144185 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem144186 (m : nat) : (term335 m) = (term375 m).
Proof. exact (MK_COMB (@lem144185) (@lem144184 m)). Qed.
Lemma lem144187 : term346 = term376.
Proof. exact (fun_ext (fun m : nat => @lem144186 m)). Qed.
Lemma lem144188 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem144190 : term357 = term377.
Proof. exact (MK_COMB (@lem144188) (@lem144187)). Qed.
Lemma lem144191 (h1 : term243) : term377.
Proof. exact (EQ_MP (@lem144190) (@lem143373 h1)). Qed.
Lemma lem144256 (_2903 : nat) (h1 : term243) : term378 _2903.
Proof. exact (@lem143501 h1 _2903). Qed.
Lemma lem144257 (_2903 : nat) : (term378 _2903) = (term368 _2903).
Proof. exact (eq_refl (term378 _2903)). Qed.
Lemma lem144258 (_2903 : nat) (h1 : term243) : term368 _2903.
Proof. exact (EQ_MP (@lem144257 _2903) (@lem144256 _2903 h1)). Qed.
Lemma lem144259 (_2903 : nat) (_2904 : nat) (h1 : term243) : term379 _2903 _2904.
Proof. exact (@lem144258 _2903 h1 _2904). Qed.
Lemma lem144260 (_2903 : nat) (_2904 : nat) : (term379 _2903 _2904) = (term364 _2903 _2904).
Proof. exact (eq_refl (term379 _2903 _2904)). Qed.
Lemma lem144261 (_2903 : nat) (_2904 : nat) (h1 : term243) : term364 _2903 _2904.
Proof. exact (EQ_MP (@lem144260 _2903 _2904) (@lem144259 _2903 _2904 h1)). Qed.
Lemma lem144286 (_2913 : nat) (h1 : term243) : term380 _2913.
Proof. exact (@lem143775 h1 _2913). Qed.
Lemma lem144287 (_2913 : nat) : (term380 _2913) = (term375 _2913).
Proof. exact (eq_refl (term380 _2913)). Qed.
Lemma lem144288 (_2913 : nat) (h1 : term243) : term375 _2913.
Proof. exact (EQ_MP (@lem144287 _2913) (@lem144286 _2913 h1)). Qed.
Lemma lem144289 (_2913 : nat) (_2914 : nat) (h1 : term243) : term381 _2913 _2914.
Proof. exact (@lem144288 _2913 h1 _2914). Qed.
Lemma lem144290 (_2913 : nat) (_2914 : nat) : (term381 _2913 _2914) = (term371 _2913 _2914).
Proof. exact (eq_refl (term381 _2913 _2914)). Qed.
Lemma lem144291 (_2913 : nat) (_2914 : nat) (h1 : term243) : term371 _2913 _2914.
Proof. exact (EQ_MP (@lem144290 _2913 _2914) (@lem144289 _2913 _2914 h1)). Qed.
Lemma lem144304 (_2919 : nat) (h1 : term243) : term378 _2919.
Proof. exact (@lem143917 h1 _2919). Qed.
Lemma lem144305 (_2919 : nat) : (term378 _2919) = (term368 _2919).
Proof. exact (eq_refl (term378 _2919)). Qed.
Lemma lem144306 (_2919 : nat) (h1 : term243) : term368 _2919.
Proof. exact (EQ_MP (@lem144305 _2919) (@lem144304 _2919 h1)). Qed.
Lemma lem144307 (_2919 : nat) (_2920 : nat) (h1 : term243) : term379 _2919 _2920.
Proof. exact (@lem144306 _2919 h1 _2920). Qed.
Lemma lem144308 (_2919 : nat) (_2920 : nat) : (term379 _2919 _2920) = (term364 _2919 _2920).
Proof. exact (eq_refl (term379 _2919 _2920)). Qed.
Lemma lem144309 (_2919 : nat) (_2920 : nat) (h1 : term243) : term364 _2919 _2920.
Proof. exact (EQ_MP (@lem144308 _2919 _2920) (@lem144307 _2919 _2920 h1)). Qed.
Lemma lem144334 (_2929 : nat) (h1 : term243) : term380 _2929.
Proof. exact (@lem144191 h1 _2929). Qed.
Lemma lem144335 (_2929 : nat) : (term380 _2929) = (term375 _2929).
Proof. exact (eq_refl (term380 _2929)). Qed.
Lemma lem144336 (_2929 : nat) (h1 : term243) : term375 _2929.
Proof. exact (EQ_MP (@lem144335 _2929) (@lem144334 _2929 h1)). Qed.
Lemma lem144337 (_2929 : nat) (_2930 : nat) (h1 : term243) : term381 _2929 _2930.
Proof. exact (@lem144336 _2929 h1 _2930). Qed.
Lemma lem144338 (_2929 : nat) (_2930 : nat) : (term381 _2929 _2930) = (term371 _2929 _2930).
Proof. exact (eq_refl (term381 _2929 _2930)). Qed.
Lemma lem144339 (_2929 : nat) (_2930 : nat) (h1 : term243) : term371 _2929 _2930.
Proof. exact (EQ_MP (@lem144338 _2929 _2930) (@lem144337 _2929 _2930 h1)). Qed.
Lemma lem144387 (m : nat) (n : nat) (h1 : term225 m n) : term50 n.
Proof. exact (proj2 (@lem143380 m n h1)). Qed.
Lemma lem144411 (_2903 : nat) (_2904 : nat) (h1 : term243) : term382 _2903 _2904.
Proof. exact (proj2 (@lem144261 _2903 _2904 h1)). Qed.
Lemma lem144445 (n : nat) (m : nat) (h1 : term278 n m) : term50 m.
Proof. exact (proj2 (@lem143385 n m h1)). Qed.
Lemma lem144493 (m : nat) (n : nat) (h1 : term226 m n) : term50 m.
Proof. exact (proj1 (@lem143381 m n h1)). Qed.
Lemma lem144551 (n : nat) (m : nat) (h1 : term278 n m) : term383 m n.
Proof. exact (proj1 (@lem143393 n m h1)). Qed.
Lemma lem144593 (_2913 : nat) (_2914 : nat) (h1 : term243) : term384 _2913 _2914.
Proof. exact (proj2 (@lem144291 _2913 _2914 h1)). Qed.
Lemma lem144599 (m : nat) (n : nat) (h1 : term265 m n) : term158 m n.
Proof. exact (proj1 (@lem143377 m n h1)). Qed.
Lemma lem144617 (_2919 : nat) (_2920 : nat) (h1 : term243) : term385 _2919 _2920.
Proof. exact (proj1 (@lem144309 _2919 _2920 h1)). Qed.
Lemma lem144661 (n : nat) (m : nat) (h1 : term278 n m) : term50 m.
Proof. exact (proj2 (@lem143405 n m h1)). Qed.
Lemma lem144709 (m : nat) (n : nat) (h1 : term224 m n) : term50 m.
Proof. exact (proj1 (@lem143401 m n h1)). Qed.
Lemma lem144767 (n : nat) (m : nat) (h1 : term278 n m) : term383 m n.
Proof. exact (proj1 (@lem143413 n m h1)). Qed.
Lemma lem144799 (_2929 : nat) (_2930 : nat) (h1 : term243) : term386 _2929 _2930.
Proof. exact (proj1 (@lem144339 _2929 _2930 h1)). Qed.
Lemma lem144811 (n : nat) (m : nat) (h1 : term277 n m) : term233 m n.
Proof. exact (proj1 (@lem143384 n m h1)). Qed.
Lemma lem144812 (n : nat) (m : nat) (h1 : term277 n m) : term387 m n.
Proof. exact (fun h0 : term383 m n => @lem144811 n m h1). Qed.
Lemma lem144814 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem144815 (m : nat) (n : nat) : (term387 m n) = (term233 m n).
Proof. exact (@lem144814 (term233 m n)). Qed.
Lemma lem144816 (n : nat) (m : nat) (h1 : term277 n m) : term233 m n.
Proof. exact (EQ_MP (@lem144815 m n) (@lem144812 n m h1)). Qed.
Lemma lem144818 (m : nat) (n : nat) (h1 : term267 m n) : term12 m n.
Proof. exact (proj1 (@lem143376 m n h1)). Qed.
Lemma lem144819 (m : nat) (n : nat) (h1 : term267 m n) : term221 m n.
Proof. exact (fun h0 : term158 m n => @lem144818 m n h1). Qed.
Lemma lem144821 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem144822 (m : nat) (n : nat) : (term221 m n) = (term12 m n).
Proof. exact (@lem144821 (term12 m n)). Qed.
Lemma lem144823 (m : nat) (n : nat) (h1 : term267 m n) : term12 m n.
Proof. exact (EQ_MP (@lem144822 m n) (@lem144819 m n h1)). Qed.
Lemma lem144829 (q : Prop) (p : Prop) (r : Prop) : (term185 p q r) = (term185 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem144830 (_2903 : nat) (_2904 : nat) : (term382 _2903 _2904) = (term388 _2903 _2904).
Proof. exact (@lem144829 (term50 _2903) (term365 _2903 _2904) (Coq.Arith.PeanoNat.Nat.Even _2904)). Qed.
Lemma lem144844 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem144845 (_2903 : nat) (_2904 : nat) : (term389 _2903 _2904) = (term390 _2903 _2904).
Proof. exact (@lem144844 (Coq.Arith.PeanoNat.Nat.Even _2904) (term365 _2903 _2904)). Qed.
Lemma lem144851 (_2903 : nat) : (term391 _2903) = (term391 _2903).
Proof. exact (eq_refl (term391 _2903)). Qed.
Lemma lem144852 (_2903 : nat) (_2904 : nat) : (term388 _2903 _2904) = (term392 _2903 _2904).
Proof. exact (MK_COMB (@lem144851 _2903) (@lem144845 _2903 _2904)). Qed.
Lemma lem144856 (q : Prop) (p : Prop) (r : Prop) : (term185 p q r) = (term185 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem144857 (_2903 : nat) (_2904 : nat) : (term392 _2903 _2904) = (term393 _2903 _2904).
Proof. exact (@lem144856 (Coq.Arith.PeanoNat.Nat.Even _2904) (term50 _2903) (term365 _2903 _2904)). Qed.
Lemma lem144873 (_2903 : nat) (_2904 : nat) : (term388 _2903 _2904) = (term393 _2903 _2904).
Proof. exact (TRANS (@lem144852 _2903 _2904) (@lem144857 _2903 _2904)). Qed.
Lemma lem144874 (_2903 : nat) (_2904 : nat) : (term382 _2903 _2904) = (term393 _2903 _2904).
Proof. exact (TRANS (@lem144830 _2903 _2904) (@lem144873 _2903 _2904)). Qed.
Lemma lem144875 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem144876 (_2903 : nat) (_2904 : nat) : (term394 _2903 _2904) = (term395 _2903 _2904).
Proof. exact (MK_COMB (@lem144875) (@lem144874 _2903 _2904)). Qed.
Lemma lem144890 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem144891 (_2903 : nat) (_2904 : nat) : (term396 _2904 _2903) = (term397 _2903 _2904).
Proof. exact (@lem144890 (term50 _2903) (term365 _2903 _2904)). Qed.
Lemma lem144897 (_2904 : nat) : (term398 _2904) = (term398 _2904).
Proof. exact (eq_refl (term398 _2904)). Qed.
Lemma lem144898 (_2903 : nat) (_2904 : nat) : (term399 _2904 _2903) = (term393 _2903 _2904).
Proof. exact (MK_COMB (@lem144897 _2904) (@lem144891 _2903 _2904)). Qed.
Lemma lem144909 (_2903 : nat) (_2904 : nat) : ((term382 _2903 _2904) = (term399 _2904 _2903)) = ((term393 _2903 _2904) = (term393 _2903 _2904)).
Proof. exact (MK_COMB (@lem144876 _2903 _2904) (@lem144898 _2903 _2904)). Qed.
Lemma lem144911 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem144912 (x : Prop) : (x = x) = True.
Proof. exact (@lem144911 Prop x). Qed.
Lemma lem144913 (_2903 : nat) (_2904 : nat) : ((term393 _2903 _2904) = (term393 _2903 _2904)) = True.
Proof. exact (@lem144912 (term393 _2903 _2904)). Qed.
Lemma lem144914 (_2904 : nat) (_2903 : nat) : ((term382 _2903 _2904) = (term399 _2904 _2903)) = True.
Proof. exact (TRANS (@lem144909 _2903 _2904) (@lem144913 _2903 _2904)). Qed.
Lemma lem144915 (_2904 : nat) (_2903 : nat) : True = ((term382 _2903 _2904) = (term399 _2904 _2903)).
Proof. exact (SYM (@lem144914 _2904 _2903)). Qed.
Lemma lem144916 (_2904 : nat) (_2903 : nat) : (term382 _2903 _2904) = (term399 _2904 _2903).
Proof. exact (EQ_MP (@lem144915 _2904 _2903) (@lem0)). Qed.
Lemma lem144917 (_2904 : nat) (_2903 : nat) (h1 : term243) : term399 _2904 _2903.
Proof. exact (EQ_MP (@lem144916 _2904 _2903) (@lem144411 _2903 _2904 h1)). Qed.
Lemma lem144919 (b : Prop) (a : Prop) : (a \/ b) = (term170 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem144920 (_2903 : nat) (_2904 : nat) : (term399 _2904 _2903) = (term400 _2903 _2904).
Proof. exact (@lem144919 (term396 _2904 _2903) (Coq.Arith.PeanoNat.Nat.Even _2904)). Qed.
Lemma lem144922 (a : Prop) (b : Prop) : (term191 a b) = (term192 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem144923 (_2904 : nat) (_2903 : nat) : (term401 _2904 _2903) = (term402 _2904 _2903).
Proof. exact (@lem144922 (term365 _2903 _2904) (term50 _2903)). Qed.
Lemma lem144925 (a : Prop) : (term172 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem144926 (_2903 : nat) (_2904 : nat) : (term403 _2903 _2904) = (term259 _2903 _2904).
Proof. exact (@lem144925 (term259 _2903 _2904)). Qed.
Lemma lem144927 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem144928 (_2903 : nat) (_2904 : nat) : (term404 _2903 _2904) = (term405 _2903 _2904).
Proof. exact (MK_COMB (@lem144927) (@lem144926 _2903 _2904)). Qed.
Lemma lem144930 (a : Prop) : (term172 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem144931 (_2903 : nat) : (term71 _2903) = (Coq.Arith.PeanoNat.Nat.Even _2903).
Proof. exact (@lem144930 (Coq.Arith.PeanoNat.Nat.Even _2903)). Qed.
Lemma lem144932 (_2904 : nat) (_2903 : nat) : (term402 _2904 _2903) = (term406 _2904 _2903).
Proof. exact (MK_COMB (@lem144928 _2903 _2904) (@lem144931 _2903)). Qed.
Lemma lem144933 (_2904 : nat) (_2903 : nat) : (term401 _2904 _2903) = (term406 _2904 _2903).
Proof. exact (TRANS (@lem144923 _2904 _2903) (@lem144932 _2904 _2903)). Qed.
Lemma lem144934 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem144935 (_2904 : nat) (_2903 : nat) : (term407 _2904 _2903) = (term408 _2904 _2903).
Proof. exact (MK_COMB (@lem144934) (@lem144933 _2904 _2903)). Qed.
Lemma lem144936 (_2904 : nat) : (Coq.Arith.PeanoNat.Nat.Even _2904) = (Coq.Arith.PeanoNat.Nat.Even _2904).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Even _2904)). Qed.
Lemma lem144937 (_2903 : nat) (_2904 : nat) : (term400 _2903 _2904) = (term409 _2903 _2904).
Proof. exact (MK_COMB (@lem144935 _2904 _2903) (@lem144936 _2904)). Qed.
Lemma lem144938 (_2903 : nat) (_2904 : nat) : (term399 _2904 _2903) = (term409 _2903 _2904).
Proof. exact (TRANS (@lem144920 _2903 _2904) (@lem144937 _2903 _2904)). Qed.
Lemma lem144940 (m : nat) (n : nat) (h1 : term277 n m) (h2 : term267 m n) : term410 m n.
Proof. exact (conj (@lem144816 n m h1) (@lem144823 m n h2)). Qed.
Lemma lem144942 (_2903 : nat) (_2904 : nat) (h1 : term243) : term409 _2903 _2904.
Proof. exact (EQ_MP (@lem144938 _2903 _2904) (@lem144917 _2904 _2903 h1)). Qed.
Lemma lem144943 (m : nat) (n : nat) (h1 : term243) : term411 m n.
Proof. exact (@lem144942 (Nat.sub m n) n h1). Qed.
Lemma lem144946 (m : nat) (n : nat) (h1 : term243) (h2 : term277 n m) (h3 : term267 m n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (@lem144943 m n h1 (@lem144940 m n h2 h3)). Qed.
Lemma lem144947 (m : nat) (n : nat) (h1 : term243) (h2 : term277 n m) (h3 : term267 m n) : term279 n.
Proof. exact (fun h0 : term50 n => @lem144946 m n h1 h2 h3). Qed.
Lemma lem144949 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem144950 (n : nat) : (term279 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (@lem144949 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem144951 (m : nat) (n : nat) (h1 : term243) (h2 : term277 n m) (h3 : term267 m n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (EQ_MP (@lem144950 n) (@lem144947 m n h1 h2 h3)). Qed.
Lemma lem144954 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem144956 (n : nat) : (term50 n) = (term280 n).
Proof. exact (@lem144954 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem144959 (m : nat) (n : nat) (h1 : term225 m n) : term280 n.
Proof. exact (EQ_MP (@lem144956 n) (@lem144387 m n h1)). Qed.
Lemma lem144962 (m : nat) (n : nat) (h1 : term243) (h2 : term225 m n) (h3 : term277 n m) (h4 : term267 m n) : False.
Proof. exact (@lem144959 m n h2 (@lem144951 m n h1 h3 h4)). Qed.
Lemma lem144963 (m : nat) (n : nat) (h1 : term243) (h2 : term225 m n) (h3 : term277 n m) (h4 : term267 m n) : term162.
Proof. exact (fun h0 : ~ False => @lem144962 m n h1 h2 h3 h4). Qed.
Lemma lem144965 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem144966 : term162 = False.
Proof. exact (@lem144965 False). Qed.
Lemma lem144967 (m : nat) (n : nat) (h1 : term243) (h2 : term225 m n) (h3 : term277 n m) (h4 : term267 m n) : False.
Proof. exact (EQ_MP (@lem144966) (@lem144963 m n h1 h2 h3 h4)). Qed.
Lemma lem144969 (m : nat) (n : nat) (h1 : term225 m n) : Coq.Arith.PeanoNat.Nat.Even m.
Proof. exact (proj1 (@lem143380 m n h1)). Qed.
Lemma lem144970 (m : nat) (n : nat) (h1 : term225 m n) : term279 m.
Proof. exact (fun h0 : term50 m => @lem144969 m n h1). Qed.
Lemma lem144972 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem144973 (m : nat) : (term279 m) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (@lem144972 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem144974 (m : nat) (n : nat) (h1 : term225 m n) : Coq.Arith.PeanoNat.Nat.Even m.
Proof. exact (EQ_MP (@lem144973 m) (@lem144970 m n h1)). Qed.
Lemma lem144977 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem144979 (m : nat) : (term50 m) = (term280 m).
Proof. exact (@lem144977 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem144982 (n : nat) (m : nat) (h1 : term278 n m) : term280 m.
Proof. exact (EQ_MP (@lem144979 m) (@lem144445 n m h1)). Qed.
Lemma lem144985 (n : nat) (m : nat) (h1 : term225 m n) (h2 : term278 n m) : False.
Proof. exact (@lem144982 n m h2 (@lem144974 m n h1)). Qed.
Lemma lem144986 (n : nat) (m : nat) (h1 : term225 m n) (h2 : term278 n m) : term162.
Proof. exact (fun h0 : ~ False => @lem144985 n m h1 h2). Qed.
Lemma lem144988 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem144989 : term162 = False.
Proof. exact (@lem144988 False). Qed.
Lemma lem144990 (n : nat) (m : nat) (h1 : term225 m n) (h2 : term278 n m) : False.
Proof. exact (EQ_MP (@lem144989) (@lem144986 n m h1 h2)). Qed.
Lemma lem144992 (n : nat) (m : nat) (h1 : term277 n m) : Coq.Arith.PeanoNat.Nat.Even m.
Proof. exact (proj2 (@lem143392 n m h1)). Qed.
Lemma lem144993 (n : nat) (m : nat) (h1 : term277 n m) : term279 m.
Proof. exact (fun h0 : term50 m => @lem144992 n m h1). Qed.
Lemma lem144995 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem144996 (m : nat) : (term279 m) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (@lem144995 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem144997 (n : nat) (m : nat) (h1 : term277 n m) : Coq.Arith.PeanoNat.Nat.Even m.
Proof. exact (EQ_MP (@lem144996 m) (@lem144993 n m h1)). Qed.
Lemma lem145000 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem145002 (m : nat) : (term50 m) = (term280 m).
Proof. exact (@lem145000 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem145005 (m : nat) (n : nat) (h1 : term226 m n) : term280 m.
Proof. exact (EQ_MP (@lem145002 m) (@lem144493 m n h1)). Qed.
Lemma lem145008 (m : nat) (n : nat) (h1 : term277 n m) (h2 : term226 m n) : False.
Proof. exact (@lem145005 m n h2 (@lem144997 n m h1)). Qed.
Lemma lem145009 (m : nat) (n : nat) (h1 : term277 n m) (h2 : term226 m n) : term162.
Proof. exact (fun h0 : ~ False => @lem145008 m n h1 h2). Qed.
Lemma lem145011 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem145012 : term162 = False.
Proof. exact (@lem145011 False). Qed.
Lemma lem145013 (m : nat) (n : nat) (h1 : term277 n m) (h2 : term226 m n) : False.
Proof. exact (EQ_MP (@lem145012) (@lem145009 m n h1 h2)). Qed.
Lemma lem145015 (m : nat) (n : nat) (h1 : term267 m n) : term12 m n.
Proof. exact (proj1 (@lem143376 m n h1)). Qed.
Lemma lem145016 (m : nat) (n : nat) (h1 : term267 m n) : term221 m n.
Proof. exact (fun h0 : term158 m n => @lem145015 m n h1). Qed.
Lemma lem145018 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem145019 (m : nat) (n : nat) : (term221 m n) = (term12 m n).
Proof. exact (@lem145018 (term12 m n)). Qed.
Lemma lem145020 (m : nat) (n : nat) (h1 : term267 m n) : term12 m n.
Proof. exact (EQ_MP (@lem145019 m n) (@lem145016 m n h1)). Qed.
Lemma lem145022 (m : nat) (n : nat) (h1 : term226 m n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (proj2 (@lem143381 m n h1)). Qed.
Lemma lem145023 (m : nat) (n : nat) (h1 : term226 m n) : term279 n.
Proof. exact (fun h0 : term50 n => @lem145022 m n h1). Qed.
Lemma lem145025 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem145026 (n : nat) : (term279 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (@lem145025 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem145027 (m : nat) (n : nat) (h1 : term226 m n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (EQ_MP (@lem145026 n) (@lem145023 m n h1)). Qed.
Lemma lem145029 (b : Prop) (a : Prop) : (a \/ b) = (term170 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem145030 (_2913 : nat) (_2914 : nat) : (term384 _2913 _2914) = (term412 _2913 _2914).
Proof. exact (@lem145029 (term373 _2913 _2914) (term259 _2913 _2914)). Qed.
Lemma lem145032 (a : Prop) (b : Prop) : (term191 a b) = (term192 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem145033 (_2913 : nat) (_2914 : nat) : (term413 _2913 _2914) = (term414 _2913 _2914).
Proof. exact (@lem145032 (term50 _2913) (term50 _2914)). Qed.
Lemma lem145035 (a : Prop) : (term172 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem145036 (_2913 : nat) : (term71 _2913) = (Coq.Arith.PeanoNat.Nat.Even _2913).
Proof. exact (@lem145035 (Coq.Arith.PeanoNat.Nat.Even _2913)). Qed.
Lemma lem145037 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem145038 (_2913 : nat) : (term415 _2913) = (term416 _2913).
Proof. exact (MK_COMB (@lem145037) (@lem145036 _2913)). Qed.
Lemma lem145040 (a : Prop) : (term172 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem145041 (_2914 : nat) : (term71 _2914) = (Coq.Arith.PeanoNat.Nat.Even _2914).
Proof. exact (@lem145040 (Coq.Arith.PeanoNat.Nat.Even _2914)). Qed.
Lemma lem145042 (_2913 : nat) (_2914 : nat) : (term414 _2913 _2914) = (term223 _2913 _2914).
Proof. exact (MK_COMB (@lem145038 _2913) (@lem145041 _2914)). Qed.
Lemma lem145043 (_2913 : nat) (_2914 : nat) : (term413 _2913 _2914) = (term223 _2913 _2914).
Proof. exact (TRANS (@lem145033 _2913 _2914) (@lem145042 _2913 _2914)). Qed.
Lemma lem145044 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem145045 (_2913 : nat) (_2914 : nat) : (term417 _2913 _2914) = (term418 _2913 _2914).
Proof. exact (MK_COMB (@lem145044) (@lem145043 _2913 _2914)). Qed.
Lemma lem145046 (_2913 : nat) (_2914 : nat) : (term259 _2913 _2914) = (term259 _2913 _2914).
Proof. exact (eq_refl (term259 _2913 _2914)). Qed.
Lemma lem145047 (_2913 : nat) (_2914 : nat) : (term412 _2913 _2914) = (term419 _2913 _2914).
Proof. exact (MK_COMB (@lem145045 _2913 _2914) (@lem145046 _2913 _2914)). Qed.
Lemma lem145048 (_2913 : nat) (_2914 : nat) : (term384 _2913 _2914) = (term419 _2913 _2914).
Proof. exact (TRANS (@lem145030 _2913 _2914) (@lem145047 _2913 _2914)). Qed.
Lemma lem145050 (m : nat) (n : nat) (h1 : term267 m n) (h2 : term226 m n) : term420 m n.
Proof. exact (conj (@lem145020 m n h1) (@lem145027 m n h2)). Qed.
Lemma lem145052 (_2913 : nat) (_2914 : nat) (h1 : term243) : term419 _2913 _2914.
Proof. exact (EQ_MP (@lem145048 _2913 _2914) (@lem144593 _2913 _2914 h1)). Qed.
Lemma lem145053 (m : nat) (n : nat) (h1 : term243) : term421 m n.
Proof. exact (@lem145052 (Nat.sub m n) n h1). Qed.
Lemma lem145056 (m : nat) (n : nat) (h1 : term243) (h2 : term267 m n) (h3 : term226 m n) : term233 m n.
Proof. exact (@lem145053 m n h1 (@lem145050 m n h2 h3)). Qed.
Lemma lem145057 (m : nat) (n : nat) (h1 : term243) (h2 : term267 m n) (h3 : term226 m n) : term387 m n.
Proof. exact (fun h0 : term383 m n => @lem145056 m n h1 h2 h3). Qed.
Lemma lem145059 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem145060 (m : nat) (n : nat) : (term387 m n) = (term233 m n).
Proof. exact (@lem145059 (term233 m n)). Qed.
Lemma lem145061 (m : nat) (n : nat) (h1 : term243) (h2 : term267 m n) (h3 : term226 m n) : term233 m n.
Proof. exact (EQ_MP (@lem145060 m n) (@lem145057 m n h1 h2 h3)). Qed.
Lemma lem145064 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem145066 (m : nat) (n : nat) : (term383 m n) = (term422 m n).
Proof. exact (@lem145064 (term233 m n)). Qed.
Lemma lem145069 (n : nat) (m : nat) (h1 : term278 n m) : term422 m n.
Proof. exact (EQ_MP (@lem145066 m n) (@lem144551 n m h1)). Qed.
Lemma lem145072 (n : nat) (m : nat) (h1 : term243) (h2 : term267 m n) (h3 : term226 m n) (h4 : term278 n m) : False.
Proof. exact (@lem145069 n m h4 (@lem145061 m n h1 h2 h3)). Qed.
Lemma lem145073 (n : nat) (m : nat) (h1 : term243) (h2 : term267 m n) (h3 : term226 m n) (h4 : term278 n m) : term162.
Proof. exact (fun h0 : ~ False => @lem145072 n m h1 h2 h3 h4). Qed.
Lemma lem145075 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem145076 : term162 = False.
Proof. exact (@lem145075 False). Qed.
Lemma lem145077 (n : nat) (m : nat) (h1 : term243) (h2 : term267 m n) (h3 : term226 m n) (h4 : term278 n m) : False.
Proof. exact (EQ_MP (@lem145076) (@lem145073 n m h1 h2 h3 h4)). Qed.
Lemma lem145079 (n : nat) (m : nat) (h1 : term277 n m) : term233 m n.
Proof. exact (proj1 (@lem143404 n m h1)). Qed.
Lemma lem145080 (n : nat) (m : nat) (h1 : term277 n m) : term387 m n.
Proof. exact (fun h0 : term383 m n => @lem145079 n m h1). Qed.
Lemma lem145082 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem145083 (m : nat) (n : nat) : (term387 m n) = (term233 m n).
Proof. exact (@lem145082 (term233 m n)). Qed.
Lemma lem145084 (n : nat) (m : nat) (h1 : term277 n m) : term233 m n.
Proof. exact (EQ_MP (@lem145083 m n) (@lem145080 n m h1)). Qed.
Lemma lem145086 (m : nat) (n : nat) (h1 : term223 m n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (proj2 (@lem143400 m n h1)). Qed.
Lemma lem145087 (m : nat) (n : nat) (h1 : term223 m n) : term279 n.
Proof. exact (fun h0 : term50 n => @lem145086 m n h1). Qed.
Lemma lem145089 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem145090 (n : nat) : (term279 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (@lem145089 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem145091 (m : nat) (n : nat) (h1 : term223 m n) : Coq.Arith.PeanoNat.Nat.Even n.
Proof. exact (EQ_MP (@lem145090 n) (@lem145087 m n h1)). Qed.
Lemma lem145097 (q : Prop) (p : Prop) (r : Prop) : (term185 p q r) = (term185 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem145098 (_2919 : nat) (_2920 : nat) : (term385 _2919 _2920) = (term423 _2919 _2920).
Proof. exact (@lem145097 (Coq.Arith.PeanoNat.Nat.Even _2919) (term365 _2919 _2920) (term50 _2920)). Qed.
Lemma lem145112 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem145113 (_2919 : nat) (_2920 : nat) : (term424 _2919 _2920) = (term425 _2919 _2920).
Proof. exact (@lem145112 (term50 _2920) (term365 _2919 _2920)). Qed.
Lemma lem145119 (_2919 : nat) : (term398 _2919) = (term398 _2919).
Proof. exact (eq_refl (term398 _2919)). Qed.
Lemma lem145120 (_2919 : nat) (_2920 : nat) : (term423 _2919 _2920) = (term426 _2919 _2920).
Proof. exact (MK_COMB (@lem145119 _2919) (@lem145113 _2919 _2920)). Qed.
Lemma lem145131 (_2919 : nat) (_2920 : nat) : (term385 _2919 _2920) = (term426 _2919 _2920).
Proof. exact (TRANS (@lem145098 _2919 _2920) (@lem145120 _2919 _2920)). Qed.
Lemma lem145132 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem145133 (_2919 : nat) (_2920 : nat) : (term427 _2919 _2920) = (term428 _2919 _2920).
Proof. exact (MK_COMB (@lem145132) (@lem145131 _2919 _2920)). Qed.
Lemma lem145147 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem145148 (_2919 : nat) (_2920 : nat) : (term424 _2919 _2920) = (term425 _2919 _2920).
Proof. exact (@lem145147 (term50 _2920) (term365 _2919 _2920)). Qed.
Lemma lem145154 (_2919 : nat) : (term398 _2919) = (term398 _2919).
Proof. exact (eq_refl (term398 _2919)). Qed.
Lemma lem145155 (_2919 : nat) (_2920 : nat) : (term423 _2919 _2920) = (term426 _2919 _2920).
Proof. exact (MK_COMB (@lem145154 _2919) (@lem145148 _2919 _2920)). Qed.
Lemma lem145166 (_2919 : nat) (_2920 : nat) : ((term385 _2919 _2920) = (term423 _2919 _2920)) = ((term426 _2919 _2920) = (term426 _2919 _2920)).
Proof. exact (MK_COMB (@lem145133 _2919 _2920) (@lem145155 _2919 _2920)). Qed.
Lemma lem145168 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem145169 (x : Prop) : (x = x) = True.
Proof. exact (@lem145168 Prop x). Qed.
Lemma lem145170 (_2919 : nat) (_2920 : nat) : ((term426 _2919 _2920) = (term426 _2919 _2920)) = True.
Proof. exact (@lem145169 (term426 _2919 _2920)). Qed.
Lemma lem145171 (_2919 : nat) (_2920 : nat) : ((term385 _2919 _2920) = (term423 _2919 _2920)) = True.
Proof. exact (TRANS (@lem145166 _2919 _2920) (@lem145170 _2919 _2920)). Qed.
Lemma lem145172 (_2919 : nat) (_2920 : nat) : True = ((term385 _2919 _2920) = (term423 _2919 _2920)).
Proof. exact (SYM (@lem145171 _2919 _2920)). Qed.
Lemma lem145173 (_2919 : nat) (_2920 : nat) : (term385 _2919 _2920) = (term423 _2919 _2920).
Proof. exact (EQ_MP (@lem145172 _2919 _2920) (@lem0)). Qed.
Lemma lem145174 (_2919 : nat) (_2920 : nat) (h1 : term243) : term423 _2919 _2920.
Proof. exact (EQ_MP (@lem145173 _2919 _2920) (@lem144617 _2919 _2920 h1)). Qed.
Lemma lem145176 (b : Prop) (a : Prop) : (a \/ b) = (term170 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem145177 (_2920 : nat) (_2919 : nat) : (term423 _2919 _2920) = (term429 _2920 _2919).
Proof. exact (@lem145176 (term424 _2919 _2920) (Coq.Arith.PeanoNat.Nat.Even _2919)). Qed.
Lemma lem145179 (a : Prop) (b : Prop) : (term191 a b) = (term192 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem145180 (_2919 : nat) (_2920 : nat) : (term430 _2919 _2920) = (term431 _2919 _2920).
Proof. exact (@lem145179 (term365 _2919 _2920) (term50 _2920)). Qed.
Lemma lem145182 (a : Prop) : (term172 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem145183 (_2919 : nat) (_2920 : nat) : (term403 _2919 _2920) = (term259 _2919 _2920).
Proof. exact (@lem145182 (term259 _2919 _2920)). Qed.
Lemma lem145184 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem145185 (_2919 : nat) (_2920 : nat) : (term404 _2919 _2920) = (term405 _2919 _2920).
Proof. exact (MK_COMB (@lem145184) (@lem145183 _2919 _2920)). Qed.
Lemma lem145187 (a : Prop) : (term172 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem145188 (_2920 : nat) : (term71 _2920) = (Coq.Arith.PeanoNat.Nat.Even _2920).
Proof. exact (@lem145187 (Coq.Arith.PeanoNat.Nat.Even _2920)). Qed.
Lemma lem145189 (_2919 : nat) (_2920 : nat) : (term431 _2919 _2920) = (term432 _2919 _2920).
Proof. exact (MK_COMB (@lem145185 _2919 _2920) (@lem145188 _2920)). Qed.
Lemma lem145190 (_2919 : nat) (_2920 : nat) : (term430 _2919 _2920) = (term432 _2919 _2920).
Proof. exact (TRANS (@lem145180 _2919 _2920) (@lem145189 _2919 _2920)). Qed.
Lemma lem145191 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem145192 (_2919 : nat) (_2920 : nat) : (term433 _2919 _2920) = (term434 _2919 _2920).
Proof. exact (MK_COMB (@lem145191) (@lem145190 _2919 _2920)). Qed.
Lemma lem145193 (_2919 : nat) : (Coq.Arith.PeanoNat.Nat.Even _2919) = (Coq.Arith.PeanoNat.Nat.Even _2919).
Proof. exact (eq_refl (Coq.Arith.PeanoNat.Nat.Even _2919)). Qed.
Lemma lem145194 (_2920 : nat) (_2919 : nat) : (term429 _2920 _2919) = (term435 _2920 _2919).
Proof. exact (MK_COMB (@lem145192 _2919 _2920) (@lem145193 _2919)). Qed.
Lemma lem145195 (_2920 : nat) (_2919 : nat) : (term423 _2919 _2920) = (term435 _2920 _2919).
Proof. exact (TRANS (@lem145177 _2920 _2919) (@lem145194 _2920 _2919)). Qed.
Lemma lem145197 (n : nat) (m : nat) (h1 : term223 m n) (h2 : term277 n m) : term436 m n.
Proof. exact (conj (@lem145084 n m h2) (@lem145091 m n h1)). Qed.
Lemma lem145199 (_2920 : nat) (_2919 : nat) (h1 : term243) : term435 _2920 _2919.
Proof. exact (EQ_MP (@lem145195 _2920 _2919) (@lem145174 _2919 _2920 h1)). Qed.
Lemma lem145200 (m : nat) (n : nat) (h1 : term243) : term437 m n.
Proof. exact (@lem145199 n (Nat.sub m n) h1). Qed.
Lemma lem145203 (n : nat) (m : nat) (h1 : term243) (h2 : term223 m n) (h3 : term277 n m) : term12 m n.
Proof. exact (@lem145200 m n h1 (@lem145197 n m h2 h3)). Qed.
Lemma lem145204 (n : nat) (m : nat) (h1 : term243) (h2 : term223 m n) (h3 : term277 n m) : term221 m n.
Proof. exact (fun h0 : term158 m n => @lem145203 n m h1 h2 h3). Qed.
Lemma lem145206 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem145207 (m : nat) (n : nat) : (term221 m n) = (term12 m n).
Proof. exact (@lem145206 (term12 m n)). Qed.
Lemma lem145208 (n : nat) (m : nat) (h1 : term243) (h2 : term223 m n) (h3 : term277 n m) : term12 m n.
Proof. exact (EQ_MP (@lem145207 m n) (@lem145204 n m h1 h2 h3)). Qed.
Lemma lem145211 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem145213 (m : nat) (n : nat) : (term158 m n) = (term222 m n).
Proof. exact (@lem145211 (term12 m n)). Qed.
Lemma lem145216 (m : nat) (n : nat) (h1 : term265 m n) : term222 m n.
Proof. exact (EQ_MP (@lem145213 m n) (@lem144599 m n h1)). Qed.
Lemma lem145219 (m : nat) (n : nat) (h1 : term243) (h2 : term223 m n) (h3 : term277 n m) (h4 : term265 m n) : False.
Proof. exact (@lem145216 m n h4 (@lem145208 n m h1 h2 h3)). Qed.
Lemma lem145220 (m : nat) (n : nat) (h1 : term243) (h2 : term223 m n) (h3 : term277 n m) (h4 : term265 m n) : term162.
Proof. exact (fun h0 : ~ False => @lem145219 m n h1 h2 h3 h4). Qed.
Lemma lem145222 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem145223 : term162 = False.
Proof. exact (@lem145222 False). Qed.
Lemma lem145224 (m : nat) (n : nat) (h1 : term243) (h2 : term223 m n) (h3 : term277 n m) (h4 : term265 m n) : False.
Proof. exact (EQ_MP (@lem145223) (@lem145220 m n h1 h2 h3 h4)). Qed.
Lemma lem145226 (m : nat) (n : nat) (h1 : term223 m n) : Coq.Arith.PeanoNat.Nat.Even m.
Proof. exact (proj1 (@lem143400 m n h1)). Qed.
Lemma lem145227 (m : nat) (n : nat) (h1 : term223 m n) : term279 m.
Proof. exact (fun h0 : term50 m => @lem145226 m n h1). Qed.
Lemma lem145229 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem145230 (m : nat) : (term279 m) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (@lem145229 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem145231 (m : nat) (n : nat) (h1 : term223 m n) : Coq.Arith.PeanoNat.Nat.Even m.
Proof. exact (EQ_MP (@lem145230 m) (@lem145227 m n h1)). Qed.
Lemma lem145234 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem145236 (m : nat) : (term50 m) = (term280 m).
Proof. exact (@lem145234 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem145239 (n : nat) (m : nat) (h1 : term278 n m) : term280 m.
Proof. exact (EQ_MP (@lem145236 m) (@lem144661 n m h1)). Qed.
Lemma lem145242 (n : nat) (m : nat) (h1 : term223 m n) (h2 : term278 n m) : False.
Proof. exact (@lem145239 n m h2 (@lem145231 m n h1)). Qed.
Lemma lem145243 (n : nat) (m : nat) (h1 : term223 m n) (h2 : term278 n m) : term162.
Proof. exact (fun h0 : ~ False => @lem145242 n m h1 h2). Qed.
Lemma lem145245 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem145246 : term162 = False.
Proof. exact (@lem145245 False). Qed.
Lemma lem145247 (n : nat) (m : nat) (h1 : term223 m n) (h2 : term278 n m) : False.
Proof. exact (EQ_MP (@lem145246) (@lem145243 n m h1 h2)). Qed.
Lemma lem145249 (n : nat) (m : nat) (h1 : term277 n m) : Coq.Arith.PeanoNat.Nat.Even m.
Proof. exact (proj2 (@lem143412 n m h1)). Qed.
Lemma lem145250 (n : nat) (m : nat) (h1 : term277 n m) : term279 m.
Proof. exact (fun h0 : term50 m => @lem145249 n m h1). Qed.
Lemma lem145252 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem145253 (m : nat) : (term279 m) = (Coq.Arith.PeanoNat.Nat.Even m).
Proof. exact (@lem145252 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem145254 (n : nat) (m : nat) (h1 : term277 n m) : Coq.Arith.PeanoNat.Nat.Even m.
Proof. exact (EQ_MP (@lem145253 m) (@lem145250 n m h1)). Qed.
Lemma lem145257 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem145259 (m : nat) : (term50 m) = (term280 m).
Proof. exact (@lem145257 (Coq.Arith.PeanoNat.Nat.Even m)). Qed.
Lemma lem145262 (m : nat) (n : nat) (h1 : term224 m n) : term280 m.
Proof. exact (EQ_MP (@lem145259 m) (@lem144709 m n h1)). Qed.
Lemma lem145265 (m : nat) (n : nat) (h1 : term277 n m) (h2 : term224 m n) : False.
Proof. exact (@lem145262 m n h2 (@lem145254 n m h1)). Qed.
Lemma lem145266 (m : nat) (n : nat) (h1 : term277 n m) (h2 : term224 m n) : term162.
Proof. exact (fun h0 : ~ False => @lem145265 m n h1 h2). Qed.
Lemma lem145268 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem145269 : term162 = False.
Proof. exact (@lem145268 False). Qed.
Lemma lem145270 (m : nat) (n : nat) (h1 : term277 n m) (h2 : term224 m n) : False.
Proof. exact (EQ_MP (@lem145269) (@lem145266 m n h1 h2)). Qed.
Lemma lem145272 (m : nat) (n : nat) (h1 : term265 m n) : term158 m n.
Proof. exact (proj1 (@lem143377 m n h1)). Qed.
Lemma lem145273 (m : nat) (n : nat) (h1 : term265 m n) : term438 m n.
Proof. exact (fun h0 : term12 m n => @lem145272 m n h1). Qed.
Lemma lem145275 (p : Prop) : (term439 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem145276 (m : nat) (n : nat) : (term438 m n) = (term158 m n).
Proof. exact (@lem145275 (term12 m n)). Qed.
Lemma lem145277 (m : nat) (n : nat) (h1 : term265 m n) : term158 m n.
Proof. exact (EQ_MP (@lem145276 m n) (@lem145273 m n h1)). Qed.
Lemma lem145279 (m : nat) (n : nat) (h1 : term224 m n) : term50 n.
Proof. exact (proj2 (@lem143401 m n h1)). Qed.
Lemma lem145280 (m : nat) (n : nat) (h1 : term224 m n) : term440 n.
Proof. exact (fun h0 : Coq.Arith.PeanoNat.Nat.Even n => @lem145279 m n h1). Qed.
Lemma lem145282 (p : Prop) : (term439 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem145283 (n : nat) : (term440 n) = (term50 n).
Proof. exact (@lem145282 (Coq.Arith.PeanoNat.Nat.Even n)). Qed.
Lemma lem145284 (m : nat) (n : nat) (h1 : term224 m n) : term50 n.
Proof. exact (EQ_MP (@lem145283 n) (@lem145280 m n h1)). Qed.
Lemma lem145286 (b : Prop) (a : Prop) : (a \/ b) = (term170 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem145287 (_2929 : nat) (_2930 : nat) : (term386 _2929 _2930) = (term441 _2929 _2930).
Proof. exact (@lem145286 (term372 _2929 _2930) (term259 _2929 _2930)). Qed.
Lemma lem145289 (a : Prop) (b : Prop) : (term191 a b) = (term192 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem145290 (_2929 : nat) (_2930 : nat) : (term442 _2929 _2930) = (term224 _2929 _2930).
Proof. exact (@lem145289 (Coq.Arith.PeanoNat.Nat.Even _2929) (Coq.Arith.PeanoNat.Nat.Even _2930)). Qed.
Lemma lem145291 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem145292 (_2929 : nat) (_2930 : nat) : (term443 _2929 _2930) = (term444 _2929 _2930).
Proof. exact (MK_COMB (@lem145291) (@lem145290 _2929 _2930)). Qed.
Lemma lem145293 (_2929 : nat) (_2930 : nat) : (term259 _2929 _2930) = (term259 _2929 _2930).
Proof. exact (eq_refl (term259 _2929 _2930)). Qed.
Lemma lem145294 (_2929 : nat) (_2930 : nat) : (term441 _2929 _2930) = (term445 _2929 _2930).
Proof. exact (MK_COMB (@lem145292 _2929 _2930) (@lem145293 _2929 _2930)). Qed.
Lemma lem145295 (_2929 : nat) (_2930 : nat) : (term386 _2929 _2930) = (term445 _2929 _2930).
Proof. exact (TRANS (@lem145287 _2929 _2930) (@lem145294 _2929 _2930)). Qed.
Lemma lem145297 (m : nat) (n : nat) (h1 : term224 m n) (h2 : term265 m n) : term446 m n.
Proof. exact (conj (@lem145277 m n h2) (@lem145284 m n h1)). Qed.
Lemma lem145299 (_2929 : nat) (_2930 : nat) (h1 : term243) : term445 _2929 _2930.
Proof. exact (EQ_MP (@lem145295 _2929 _2930) (@lem144799 _2929 _2930 h1)). Qed.
Lemma lem145300 (m : nat) (n : nat) (h1 : term243) : term447 m n.
Proof. exact (@lem145299 (Nat.sub m n) n h1). Qed.
Lemma lem145303 (m : nat) (n : nat) (h1 : term243) (h2 : term224 m n) (h3 : term265 m n) : term233 m n.
Proof. exact (@lem145300 m n h1 (@lem145297 m n h2 h3)). Qed.
Lemma lem145304 (m : nat) (n : nat) (h1 : term243) (h2 : term224 m n) (h3 : term265 m n) : term387 m n.
Proof. exact (fun h0 : term383 m n => @lem145303 m n h1 h2 h3). Qed.
Lemma lem145306 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem145307 (m : nat) (n : nat) : (term387 m n) = (term233 m n).
Proof. exact (@lem145306 (term233 m n)). Qed.
Lemma lem145308 (m : nat) (n : nat) (h1 : term243) (h2 : term224 m n) (h3 : term265 m n) : term233 m n.
Proof. exact (EQ_MP (@lem145307 m n) (@lem145304 m n h1 h2 h3)). Qed.
Lemma lem145311 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem145313 (m : nat) (n : nat) : (term383 m n) = (term422 m n).
Proof. exact (@lem145311 (term233 m n)). Qed.
Lemma lem145316 (n : nat) (m : nat) (h1 : term278 n m) : term422 m n.
Proof. exact (EQ_MP (@lem145313 m n) (@lem144767 n m h1)). Qed.
Lemma lem145319 (m : nat) (n : nat) (h1 : term243) (h2 : term224 m n) (h3 : term278 n m) (h4 : term265 m n) : False.
Proof. exact (@lem145316 n m h3 (@lem145308 m n h1 h2 h4)). Qed.
Lemma lem145320 (m : nat) (n : nat) (h1 : term243) (h2 : term224 m n) (h3 : term278 n m) (h4 : term265 m n) : term162.
Proof. exact (fun h0 : ~ False => @lem145319 m n h1 h2 h3 h4). Qed.
Lemma lem145322 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem145323 : term162 = False.
Proof. exact (@lem145322 False). Qed.
Lemma lem145324 (m : nat) (n : nat) (h1 : term243) (h2 : term224 m n) (h3 : term278 n m) (h4 : term265 m n) : False.
Proof. exact (EQ_MP (@lem145323) (@lem145320 m n h1 h2 h3 h4)). Qed.
Lemma lem145325 (m : nat) (n : nat) (h1 : term243) (h2 : term285 m n) (h3 : term224 m n) (h4 : term265 m n) : False.
Proof. exact (or_elim (@lem143375 m n h2) (fun h0 : term277 n m => @lem145270 m n h0 h3) (fun h0 : term278 n m => @lem145324 m n h1 h3 h0 h4)). Qed.
Lemma lem145326 (m : nat) (n : nat) (h1 : term243) (h2 : term285 m n) (h3 : term223 m n) (h4 : term265 m n) : False.
Proof. exact (or_elim (@lem143375 m n h2) (fun h0 : term277 n m => @lem145224 m n h1 h3 h0 h4) (fun h0 : term278 n m => @lem145247 n m h3 h0)). Qed.
Lemma lem145327 (m : nat) (n : nat) (h1 : term243) (h2 : term285 m n) (h3 : term265 m n) : False.
Proof. exact (or_elim (@lem143398 m n h3) (fun h0 : term223 m n => @lem145326 m n h1 h2 h0 h3) (fun h0 : term224 m n => @lem145325 m n h1 h2 h0 h3)). Qed.
Lemma lem145328 (m : nat) (n : nat) (h1 : term243) (h2 : term285 m n) (h3 : term267 m n) (h4 : term226 m n) : False.
Proof. exact (or_elim (@lem143375 m n h2) (fun h0 : term277 n m => @lem145013 m n h0 h4) (fun h0 : term278 n m => @lem145077 n m h1 h3 h4 h0)). Qed.
Lemma lem145329 (m : nat) (n : nat) (h1 : term243) (h2 : term285 m n) (h3 : term225 m n) (h4 : term267 m n) : False.
Proof. exact (or_elim (@lem143375 m n h2) (fun h0 : term277 n m => @lem144967 m n h1 h3 h0 h4) (fun h0 : term278 n m => @lem144990 n m h3 h0)). Qed.
Lemma lem145330 (m : nat) (n : nat) (h1 : term243) (h2 : term285 m n) (h3 : term267 m n) : False.
Proof. exact (or_elim (@lem143378 m n h3) (fun h0 : term225 m n => @lem145329 m n h1 h2 h0 h3) (fun h0 : term226 m n => @lem145328 m n h1 h2 h3 h0)). Qed.
Lemma lem145331 (m : nat) (n : nat) (h1 : term243) (h2 : term285 m n) : False.
Proof. exact (or_elim (@lem143374 m n h2) (fun h0 : term267 m n => @lem145330 m n h1 h2 h0) (fun h0 : term265 m n => @lem145327 m n h1 h2 h0)). Qed.
Lemma lem145332 (m : nat) (n : nat) (h1 : term285 m n) : term241.
Proof. exact (fun h0 : term243 => @lem145331 m n h0 h1). Qed.
Lemma lem145333 : term241 = term242.
Proof. exact (@lem69 term243). Qed.
Lemma lem145334 (m : nat) (n : nat) (h1 : term285 m n) : term242.
Proof. exact (EQ_MP (@lem145333) (@lem145332 m n h1)). Qed.
Lemma lem145335 (m : nat) (n : nat) : term292 m n.
Proof. exact (fun h0 : term285 m n => @lem145334 m n h0). Qed.
Lemma lem145336 (m : nat) (n : nat) : term294 m n.
Proof. exact (fun h0 : Peano.le n m => @lem145335 m n). Qed.
Lemma lem145337 (m : nat) (n : nat) : term295 m n.
Proof. exact (fun h0 : term10 m n => @lem145336 m n). Qed.
Lemma lem145342 (n : nat) : term299 n.
Proof. exact (fun m : nat => @lem145337 m n). Qed.
Lemma lem145347 : term303.
Proof. exact (fun n : nat => @lem145342 n). Qed.
Lemma lem145348 : term302.
Proof. exact (EQ_MP (@lem142758) (@lem145347)). Qed.
Lemma lem145349 (n : nat) : term448 n.
Proof. exact (@lem145348 n). Qed.
Lemma lem145350 (n : nat) : (term448 n) = (term298 n).
Proof. exact (eq_refl (term448 n)). Qed.
Lemma lem145351 (n : nat) : term298 n.
Proof. exact (EQ_MP (@lem145350 n) (@lem145349 n)). Qed.
Lemma lem145352 (n : nat) (m : nat) : term449 n m.
Proof. exact (@lem145351 n m). Qed.
Lemma lem145353 (m : nat) (n : nat) : (term449 n m) = (term286 m n).
Proof. exact (eq_refl (term449 n m)). Qed.
Lemma lem145354 (m : nat) (n : nat) : term286 m n.
Proof. exact (EQ_MP (@lem145353 m n) (@lem145352 n m)). Qed.
Lemma lem145356 (m : nat) (n : nat) : term286 m n.
Proof. exact (@lem142610 m n (@lem145354 m n)). Qed.
Lemma lem145357 (m : nat) (n : nat) (h1 : term10 m n) : term293 m n.
Proof. exact (@lem145356 m n (@lem137196 m n h1)). Qed.
Lemma lem145358 (n : nat) (m : nat) (h1 : term10 m n) (h2 : Peano.le n m) : term291 m n.
Proof. exact (@lem145357 m n h1 (@lem137181 n m h2)). Qed.
Lemma lem145359 (n : nat) (m : nat) (h1 : term10 m n) (h2 : term285 m n) (h3 : Peano.le n m) : term241.
Proof. exact (@lem145358 n m h1 h3 (@lem142595 m n h2)). Qed.
Lemma lem145360 (n : nat) (m : nat) (h1 : term10 m n) (h2 : term285 m n) (h3 : Peano.le n m) : False.
Proof. exact (@lem145359 n m h1 h2 h3 (@lem125496)). Qed.
Lemma lem145361 (n : nat) (m : nat) (h1 : term10 m n) (h2 : term285 m n) (h3 : Peano.le n m) : (term285 m n) = False.
Proof. exact (prop_ext (fun h4 : term285 m n => @lem145360 n m h1 h2 h3) (fun h4 : False => @lem142595 m n h2)). Qed.
Lemma lem145362 (n : nat) (m : nat) (h1 : term10 m n) (h2 : term285 m n) (h3 : Peano.le n m) : False.
Proof. exact (EQ_MP (@lem145361 n m h1 h2 h3) (@lem142595 m n h2)). Qed.
Lemma lem145363 (n : nat) (m : nat) (h1 : term10 m n) (h2 : Peano.le n m) : term284 m n.
Proof. exact (fun h0 : term285 m n => @lem145362 n m h1 h0 h2). Qed.
Lemma lem145364 (n : nat) (m : nat) (h1 : term10 m n) (h2 : Peano.le n m) : term283 m n.
Proof. exact (EQ_MP (@lem142594 m n) (@lem145363 n m h1 h2)). Qed.
Lemma lem145365 (n : nat) (m : nat) (h1 : term10 m n) (h2 : Peano.le n m) : (term12 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (@lem145364 n m h1 h2 (@lem140091 n m h2)). Qed.
Lemma lem145366 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : (term12 m n) = ((Coq.Arith.PeanoNat.Nat.Even m) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (@lem142590 m n h1 h2 (@lem140087 m n h2)). Qed.
Lemma lem145367 (n : nat) (m : nat) (h1 : term10 m n) (h2 : Peano.le n m) : (term12 m n) = (term13 m n).
Proof. exact (EQ_MP (@lem140082 m n h1) (@lem145365 n m h1 h2)). Qed.
Lemma lem145368 (m : nat) (n : nat) (h1 : term10 m n) (h2 : Peano.le m n) : (term12 m n) = (term13 m n).
Proof. exact (EQ_MP (@lem140053 m n h1) (@lem145366 m n h1 h2)). Qed.
Lemma lem145369 (m : nat) (n : nat) (h1 : term10 m n) : (term12 m n) = (term13 m n).
Proof. exact (or_elim (@lem137179 n m) (fun h0 : Peano.le m n => @lem145368 m n h1 h0) (fun h0 : Peano.le n m => @lem145367 n m h1 h0)). Qed.
Lemma lem145370 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (or_elim (@lem137194 m n) (fun h0 : Peano.le m n => @lem140024 m n h0) (fun h0 : term10 m n => @lem145369 m n h0)). Qed.
Lemma lem145375 (m : nat) : term450 m.
Proof. exact (fun n : nat => @lem145370 m n). Qed.
Lemma lem145380 : term451.
Proof. exact (fun m : nat => @lem145375 m). Qed.
