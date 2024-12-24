Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXP_EQ_0_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import ADD_EQ_0_spec.
Require Import BIT1_THM_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_SUC_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Require Import thm86199_spec.
Lemma lem86204 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem86205 : term1.
Proof. exact (@lem86204 term2). Qed.
Lemma lem86206 : term3 = term4.
Proof. exact (eq_refl term3). Qed.
Lemma lem86207 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem86208 : term5 = term6.
Proof. exact (MK_COMB (@lem86207) (@lem86206)). Qed.
Lemma lem86209 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem86210 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem86211 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem86210) (@lem86209 m)). Qed.
Lemma lem86212 (m : nat) : (term11 m) = (term12 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem86213 (m : nat) : (term13 m) = (term14 m).
Proof. exact (MK_COMB (@lem86211 m) (@lem86212 m)). Qed.
Lemma lem86214 : term15 = term16.
Proof. exact (fun_ext (fun m : nat => @lem86213 m)). Qed.
Lemma lem86215 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem86216 : term17 = term18.
Proof. exact (MK_COMB (@lem86215) (@lem86214)). Qed.
Lemma lem86217 : term19 = term20.
Proof. exact (MK_COMB (@lem86208) (@lem86216)). Qed.
Lemma lem86218 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem86219 : term21 = term22.
Proof. exact (MK_COMB (@lem86218) (@lem86217)). Qed.
Lemma lem86220 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem86221 : term23 = term2.
Proof. exact (fun_ext (fun m : nat => @lem86220 m)). Qed.
Lemma lem86222 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem86223 : term24 = term25.
Proof. exact (MK_COMB (@lem86222) (@lem86221)). Qed.
Lemma lem86224 : term1 = term26.
Proof. exact (MK_COMB (@lem86219) (@lem86223)). Qed.
Lemma lem86225 : term26.
Proof. exact (EQ_MP (@lem86224) (@lem86205)). Qed.
Lemma lem86228 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem86229 : term27.
Proof. exact (@lem86228 term28). Qed.
Lemma lem86230 : term29 = ((term30 = (NUMERAL 0)) = term31).
Proof. exact (eq_refl term29). Qed.
Lemma lem86231 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem86232 : term32 = term33.
Proof. exact (MK_COMB (@lem86231) (@lem86230)). Qed.
Lemma lem86233 (n : nat) : (term34 n) = (((term35 n) = (NUMERAL 0)) = (term36 n)).
Proof. exact (eq_refl (term34 n)). Qed.
Lemma lem86234 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem86235 (n : nat) : (term37 n) = (term38 n).
Proof. exact (MK_COMB (@lem86234) (@lem86233 n)). Qed.
Lemma lem86236 (n : nat) : (term39 n) = (((term40 n) = (NUMERAL 0)) = (term41 n)).
Proof. exact (eq_refl (term39 n)). Qed.
Lemma lem86237 (n : nat) : (term42 n) = (term43 n).
Proof. exact (MK_COMB (@lem86235 n) (@lem86236 n)). Qed.
Lemma lem86238 : term44 = term45.
Proof. exact (fun_ext (fun n : nat => @lem86237 n)). Qed.
Lemma lem86239 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem86240 : term46 = term47.
Proof. exact (MK_COMB (@lem86239) (@lem86238)). Qed.
Lemma lem86241 : term48 = term49.
Proof. exact (MK_COMB (@lem86232) (@lem86240)). Qed.
Lemma lem86242 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem86243 : term50 = term51.
Proof. exact (MK_COMB (@lem86242) (@lem86241)). Qed.
Lemma lem86244 (n : nat) : (term34 n) = (((term35 n) = (NUMERAL 0)) = (term36 n)).
Proof. exact (eq_refl (term34 n)). Qed.
Lemma lem86245 : term52 = term28.
Proof. exact (fun_ext (fun n : nat => @lem86244 n)). Qed.
Lemma lem86246 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem86247 : term53 = term4.
Proof. exact (MK_COMB (@lem86246) (@lem86245)). Qed.
Lemma lem86248 : term27 = term54.
Proof. exact (MK_COMB (@lem86243) (@lem86247)). Qed.
Lemma lem86249 : term54.
Proof. exact (EQ_MP (@lem86248) (@lem86229)). Qed.
Lemma lem86256 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem86257 (m : nat) : term55 m.
Proof. exact (@lem86256 (term56 m)). Qed.
Lemma lem86258 (m : nat) : (term57 m) = (((term58 m) = (NUMERAL 0)) = (term59 m)).
Proof. exact (eq_refl (term57 m)). Qed.
Lemma lem86259 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem86260 (m : nat) : (term60 m) = (term61 m).
Proof. exact (MK_COMB (@lem86259) (@lem86258 m)). Qed.
Lemma lem86261 (m : nat) (n : nat) : (term62 m n) = (((term63 m n) = (NUMERAL 0)) = (term64 m n)).
Proof. exact (eq_refl (term62 m n)). Qed.
Lemma lem86262 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem86263 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (MK_COMB (@lem86262) (@lem86261 m n)). Qed.
Lemma lem86264 (m : nat) (n : nat) : (term67 m n) = (((term68 m n) = (NUMERAL 0)) = (term69 m n)).
Proof. exact (eq_refl (term67 m n)). Qed.
Lemma lem86265 (m : nat) (n : nat) : (term70 m n) = (term71 m n).
Proof. exact (MK_COMB (@lem86263 m n) (@lem86264 m n)). Qed.
Lemma lem86266 (m : nat) : (term72 m) = (term73 m).
Proof. exact (fun_ext (fun n : nat => @lem86265 m n)). Qed.
Lemma lem86267 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem86268 (m : nat) : (term74 m) = (term75 m).
Proof. exact (MK_COMB (@lem86267) (@lem86266 m)). Qed.
Lemma lem86269 (m : nat) : (term76 m) = (term77 m).
Proof. exact (MK_COMB (@lem86260 m) (@lem86268 m)). Qed.
Lemma lem86270 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem86271 (m : nat) : (term78 m) = (term79 m).
Proof. exact (MK_COMB (@lem86270) (@lem86269 m)). Qed.
Lemma lem86272 (m : nat) (n : nat) : (term62 m n) = (((term63 m n) = (NUMERAL 0)) = (term64 m n)).
Proof. exact (eq_refl (term62 m n)). Qed.
Lemma lem86273 (m : nat) : (term80 m) = (term56 m).
Proof. exact (fun_ext (fun n : nat => @lem86272 m n)). Qed.
Lemma lem86274 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem86275 (m : nat) : (term81 m) = (term12 m).
Proof. exact (MK_COMB (@lem86274) (@lem86273 m)). Qed.
Lemma lem86276 (m : nat) : (term55 m) = (term82 m).
Proof. exact (MK_COMB (@lem86271 m) (@lem86275 m)). Qed.
Lemma lem86277 (m : nat) : term82 m.
Proof. exact (EQ_MP (@lem86276 m) (@lem86257 m)). Qed.
Lemma lem86309 : term83.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem86310 (n : nat) : term84 n.
Proof. exact (@lem86309 n). Qed.
Lemma lem86311 (n : nat) : (term84 n) = ((term85 n) = n).
Proof. exact (eq_refl (term84 n)). Qed.
Lemma lem86354 : term86.
Proof. exact (proj1 (@lem86199)). Qed.
Lemma lem86355 (m : nat) : term87 m.
Proof. exact (@lem86354 m). Qed.
Lemma lem86356 (m : nat) : (term87 m) = ((term88 m) = term89).
Proof. exact (eq_refl (term87 m)). Qed.
Lemma lem86358 (n : nat) : term90 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem86359 (n : nat) : (term90 n) = (term91 n).
Proof. exact (eq_refl (term90 n)). Qed.
Lemma lem86360 (n : nat) : term91 n.
Proof. exact (EQ_MP (@lem86359 n) (@lem86358 n)). Qed.
Lemma lem86361 (n : nat) : term92 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem86390 (n : nat) : term93 n.
Proof. exact (@lem80210 n). Qed.
Lemma lem86391 (n : nat) : (term93 n) = ((term94 n) = (term95 n)).
Proof. exact (eq_refl (term93 n)). Qed.
Lemma lem86398 (m : nat) : (term88 m) = term89.
Proof. exact (EQ_MP (@lem86356 m) (@lem86355 m)). Qed.
Lemma lem86399 : term30 = term89.
Proof. exact (@lem86398 (NUMERAL 0)). Qed.
Lemma lem86401 (n : nat) : (term94 n) = (term95 n).
Proof. exact (EQ_MP (@lem86391 n) (@lem86390 n)). Qed.
Lemma lem86402 : term89 = term96.
Proof. exact (@lem86401 0). Qed.
Lemma lem86403 : term30 = term96.
Proof. exact (TRANS (@lem86399) (@lem86402)). Qed.
Lemma lem86405 (n : nat) : (term85 n) = n.
Proof. exact (EQ_MP (@lem86311 n) (@lem86310 n)). Qed.
Lemma lem86406 : term97 = (NUMERAL 0).
Proof. exact (@lem86405 (NUMERAL 0)). Qed.
Lemma lem86407 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem86408 : term96 = term98.
Proof. exact (MK_COMB (@lem86407) (@lem86406)). Qed.
Lemma lem86409 : term30 = term98.
Proof. exact (TRANS (@lem86403) (@lem86408)). Qed.
Lemma lem86410 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem86411 : term99 = term100.
Proof. exact (MK_COMB (@lem86410) (@lem86409)). Qed.
Lemma lem86412 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem86413 : (term30 = (NUMERAL 0)) = (term98 = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem86411) (@lem86412)). Qed.
Lemma lem86415 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem86361 n (@lem86360 n)). Qed.
Lemma lem86416 : (term98 = (NUMERAL 0)) = False.
Proof. exact (@lem86415 (NUMERAL 0)). Qed.
Lemma lem86417 : (term30 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem86413) (@lem86416)). Qed.
Lemma lem86418 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem86419 : term101 = (@eq Prop False).
Proof. exact (MK_COMB (@lem86418) (@lem86417)). Qed.
Lemma lem86423 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem86424 (x : nat) : (x = x) = True.
Proof. exact (@lem86423 nat x). Qed.
Lemma lem86425 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem86424 (NUMERAL 0)). Qed.
Lemma lem86426 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem86427 : term102 = (and True).
Proof. exact (MK_COMB (@lem86426) (@lem86425)). Qed.
Lemma lem86429 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem86430 (x : nat) : (x = x) = True.
Proof. exact (@lem86429 nat x). Qed.
Lemma lem86431 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem86430 (NUMERAL 0)). Qed.
Lemma lem86432 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem86433 : term103 = (~ True).
Proof. exact (MK_COMB (@lem86432) (@lem86431)). Qed.
Lemma lem86435 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem86436 : term103 = False.
Proof. exact (TRANS (@lem86433) (@lem86435)). Qed.
Lemma lem86437 : term31 = (True /\ False).
Proof. exact (MK_COMB (@lem86427) (@lem86436)). Qed.
Lemma lem86439 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem86440 : (True /\ False) = False.
Proof. exact (@lem86439 False). Qed.
Lemma lem86441 : term31 = False.
Proof. exact (TRANS (@lem86437) (@lem86440)). Qed.
Lemma lem86442 : ((term30 = (NUMERAL 0)) = term31) = (False = False).
Proof. exact (MK_COMB (@lem86419) (@lem86441)). Qed.
Lemma lem86444 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem86445 : (False = False) = (~ False).
Proof. exact (@lem86444 False). Qed.
Lemma lem86447 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem86448 : (False = False) = True.
Proof. exact (TRANS (@lem86445) (@lem86447)). Qed.
Lemma lem86449 : ((term30 = (NUMERAL 0)) = term31) = True.
Proof. exact (TRANS (@lem86442) (@lem86448)). Qed.
Lemma lem86450 : True = ((term30 = (NUMERAL 0)) = term31).
Proof. exact (SYM (@lem86449)). Qed.
Lemma lem86451 : (term30 = (NUMERAL 0)) = term31.
Proof. exact (EQ_MP (@lem86450) (@lem0)). Qed.
Lemma lem86512 : term104.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem86513 (n : nat) : term105 n.
Proof. exact (@lem86512 n). Qed.
Lemma lem86514 (n : nat) : (term105 n) = ((term106 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term105 n)). Qed.
Lemma lem86516 : term107.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem86517 (m : nat) : term108 m.
Proof. exact (@lem86516 m). Qed.
Lemma lem86518 (m : nat) : (term108 m) = (term109 m).
Proof. exact (eq_refl (term108 m)). Qed.
Lemma lem86519 (m : nat) : term109 m.
Proof. exact (EQ_MP (@lem86518 m) (@lem86517 m)). Qed.
Lemma lem86520 (m : nat) (n : nat) : term110 m n.
Proof. exact (@lem86519 m n). Qed.
Lemma lem86521 (m : nat) (n : nat) : (term110 m n) = ((term111 m n) = (term112 m n)).
Proof. exact (eq_refl (term110 m n)). Qed.
Lemma lem86527 (n : nat) : term90 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem86528 (n : nat) : (term90 n) = (term91 n).
Proof. exact (eq_refl (term90 n)). Qed.
Lemma lem86529 (n : nat) : term91 n.
Proof. exact (EQ_MP (@lem86528 n) (@lem86527 n)). Qed.
Lemma lem86530 (n : nat) : term92 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem86567 (m : nat) (n : nat) : (term111 m n) = (term112 m n).
Proof. exact (EQ_MP (@lem86521 m n) (@lem86520 m n)). Qed.
Lemma lem86568 (n : nat) : (term40 n) = (term113 n).
Proof. exact (@lem86567 (NUMERAL 0) n). Qed.
Lemma lem86570 (n : nat) : (term106 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem86514 n) (@lem86513 n)). Qed.
Lemma lem86571 (n : nat) : (term113 n) = (NUMERAL 0).
Proof. exact (@lem86570 (term35 n)). Qed.
Lemma lem86572 (n : nat) : (term40 n) = (NUMERAL 0).
Proof. exact (TRANS (@lem86568 n) (@lem86571 n)). Qed.
Lemma lem86573 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem86574 (n : nat) : (term114 n) = term115.
Proof. exact (MK_COMB (@lem86573) (@lem86572 n)). Qed.
Lemma lem86575 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem86576 (n : nat) : ((term40 n) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem86574 n) (@lem86575)). Qed.
Lemma lem86578 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem86579 (x : nat) : (x = x) = True.
Proof. exact (@lem86578 nat x). Qed.
Lemma lem86580 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem86579 (NUMERAL 0)). Qed.
Lemma lem86581 (n : nat) : ((term40 n) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem86576 n) (@lem86580)). Qed.
Lemma lem86582 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem86583 (n : nat) : (term116 n) = (@eq Prop True).
Proof. exact (MK_COMB (@lem86582) (@lem86581 n)). Qed.
Lemma lem86587 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem86588 (x : nat) : (x = x) = True.
Proof. exact (@lem86587 nat x). Qed.
Lemma lem86589 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem86588 (NUMERAL 0)). Qed.
Lemma lem86590 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem86591 : term102 = (and True).
Proof. exact (MK_COMB (@lem86590) (@lem86589)). Qed.
Lemma lem86593 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem86530 n (@lem86529 n)). Qed.
Lemma lem86594 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem86595 (n : nat) : (term91 n) = (~ False).
Proof. exact (MK_COMB (@lem86594) (@lem86593 n)). Qed.
Lemma lem86597 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem86598 (n : nat) : (term91 n) = True.
Proof. exact (TRANS (@lem86595 n) (@lem86597)). Qed.
Lemma lem86599 (n : nat) : (term41 n) = (True /\ True).
Proof. exact (MK_COMB (@lem86591) (@lem86598 n)). Qed.
Lemma lem86601 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem86602 : (True /\ True) = True.
Proof. exact (@lem86601 True). Qed.
Lemma lem86603 (n : nat) : (term41 n) = True.
Proof. exact (TRANS (@lem86599 n) (@lem86602)). Qed.
Lemma lem86604 (n : nat) : (((term40 n) = (NUMERAL 0)) = (term41 n)) = (True = True).
Proof. exact (MK_COMB (@lem86583 n) (@lem86603 n)). Qed.
Lemma lem86606 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem86607 : (True = True) = True.
Proof. exact (@lem86606 True). Qed.
Lemma lem86608 (n : nat) : (((term40 n) = (NUMERAL 0)) = (term41 n)) = True.
Proof. exact (TRANS (@lem86604 n) (@lem86607)). Qed.
Lemma lem86609 (n : nat) : True = (((term40 n) = (NUMERAL 0)) = (term41 n)).
Proof. exact (SYM (@lem86608 n)). Qed.
Lemma lem86610 (n : nat) : ((term40 n) = (NUMERAL 0)) = (term41 n).
Proof. exact (EQ_MP (@lem86609 n) (@lem0)). Qed.
Lemma lem86637 : term83.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem86638 (n : nat) : term84 n.
Proof. exact (@lem86637 n). Qed.
Lemma lem86639 (n : nat) : (term84 n) = ((term85 n) = n).
Proof. exact (eq_refl (term84 n)). Qed.
Lemma lem86682 : term86.
Proof. exact (proj1 (@lem86199)). Qed.
Lemma lem86683 (m : nat) : term87 m.
Proof. exact (@lem86682 m). Qed.
Lemma lem86684 (m : nat) : (term87 m) = ((term88 m) = term89).
Proof. exact (eq_refl (term87 m)). Qed.
Lemma lem86686 (n : nat) : term90 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem86687 (n : nat) : (term90 n) = (term91 n).
Proof. exact (eq_refl (term90 n)). Qed.
Lemma lem86688 (n : nat) : term91 n.
Proof. exact (EQ_MP (@lem86687 n) (@lem86686 n)). Qed.
Lemma lem86689 (n : nat) : term92 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem86718 (n : nat) : term93 n.
Proof. exact (@lem80210 n). Qed.
Lemma lem86719 (n : nat) : (term93 n) = ((term94 n) = (term95 n)).
Proof. exact (eq_refl (term93 n)). Qed.
Lemma lem86729 (m : nat) : (term88 m) = term89.
Proof. exact (EQ_MP (@lem86684 m) (@lem86683 m)). Qed.
Lemma lem86730 (m : nat) : (term58 m) = term89.
Proof. exact (@lem86729 (S m)). Qed.
Lemma lem86732 (n : nat) : (term94 n) = (term95 n).
Proof. exact (EQ_MP (@lem86719 n) (@lem86718 n)). Qed.
Lemma lem86733 : term89 = term96.
Proof. exact (@lem86732 0). Qed.
Lemma lem86734 (m : nat) : (term58 m) = term96.
Proof. exact (TRANS (@lem86730 m) (@lem86733)). Qed.
Lemma lem86736 (n : nat) : (term85 n) = n.
Proof. exact (EQ_MP (@lem86639 n) (@lem86638 n)). Qed.
Lemma lem86737 : term97 = (NUMERAL 0).
Proof. exact (@lem86736 (NUMERAL 0)). Qed.
Lemma lem86738 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem86739 : term96 = term98.
Proof. exact (MK_COMB (@lem86738) (@lem86737)). Qed.
Lemma lem86740 (m : nat) : (term58 m) = term98.
Proof. exact (TRANS (@lem86734 m) (@lem86739)). Qed.
Lemma lem86741 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem86742 (m : nat) : (term117 m) = term100.
Proof. exact (MK_COMB (@lem86741) (@lem86740 m)). Qed.
Lemma lem86743 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem86744 (m : nat) : ((term58 m) = (NUMERAL 0)) = (term98 = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem86742 m) (@lem86743)). Qed.
Lemma lem86746 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem86689 n (@lem86688 n)). Qed.
Lemma lem86747 : (term98 = (NUMERAL 0)) = False.
Proof. exact (@lem86746 (NUMERAL 0)). Qed.
Lemma lem86748 (m : nat) : ((term58 m) = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem86744 m) (@lem86747)). Qed.
Lemma lem86749 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem86750 (m : nat) : (term118 m) = (@eq Prop False).
Proof. exact (MK_COMB (@lem86749) (@lem86748 m)). Qed.
Lemma lem86754 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem86689 n (@lem86688 n)). Qed.
Lemma lem86755 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem86754 m). Qed.
Lemma lem86756 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem86757 (m : nat) : (term119 m) = (and False).
Proof. exact (MK_COMB (@lem86756) (@lem86755 m)). Qed.
Lemma lem86759 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem86760 (x : nat) : (x = x) = True.
Proof. exact (@lem86759 nat x). Qed.
Lemma lem86761 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem86760 (NUMERAL 0)). Qed.
Lemma lem86762 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem86763 : term103 = (~ True).
Proof. exact (MK_COMB (@lem86762) (@lem86761)). Qed.
Lemma lem86765 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem86766 : term103 = False.
Proof. exact (TRANS (@lem86763) (@lem86765)). Qed.
Lemma lem86767 (m : nat) : (term59 m) = (False /\ False).
Proof. exact (MK_COMB (@lem86757 m) (@lem86766)). Qed.
Lemma lem86769 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem86770 : (False /\ False) = False.
Proof. exact (@lem86769 False). Qed.
Lemma lem86771 (m : nat) : (term59 m) = False.
Proof. exact (TRANS (@lem86767 m) (@lem86770)). Qed.
Lemma lem86772 (m : nat) : (((term58 m) = (NUMERAL 0)) = (term59 m)) = (False = False).
Proof. exact (MK_COMB (@lem86750 m) (@lem86771 m)). Qed.
Lemma lem86774 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem86775 : (False = False) = (~ False).
Proof. exact (@lem86774 False). Qed.
Lemma lem86777 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem86778 : (False = False) = True.
Proof. exact (TRANS (@lem86775) (@lem86777)). Qed.
Lemma lem86779 (m : nat) : (((term58 m) = (NUMERAL 0)) = (term59 m)) = True.
Proof. exact (TRANS (@lem86772 m) (@lem86778)). Qed.
Lemma lem86780 (m : nat) : True = (((term58 m) = (NUMERAL 0)) = (term59 m)).
Proof. exact (SYM (@lem86779 m)). Qed.
Lemma lem86781 (m : nat) : ((term58 m) = (NUMERAL 0)) = (term59 m).
Proof. exact (EQ_MP (@lem86780 m) (@lem0)). Qed.
Lemma lem86782 (m : nat) : term120 m.
Proof. exact (@lem79432 m). Qed.
Lemma lem86783 (m : nat) : (term120 m) = (term121 m).
Proof. exact (eq_refl (term120 m)). Qed.
Lemma lem86784 (m : nat) : term121 m.
Proof. exact (EQ_MP (@lem86783 m) (@lem86782 m)). Qed.
Lemma lem86785 (m : nat) (n : nat) : term122 m n.
Proof. exact (@lem86784 m n). Qed.
Lemma lem86786 (m : nat) (n : nat) : (term122 m n) = (((Nat.add m n) = (NUMERAL 0)) = (term123 m n)).
Proof. exact (eq_refl (term122 m n)). Qed.
Lemma lem86812 : term124.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem86813 : term125.
Proof. exact (proj2 (@lem86812)). Qed.
Lemma lem86814 : term126.
Proof. exact (proj2 (@lem86813)). Qed.
Lemma lem86815 : term127.
Proof. exact (proj2 (@lem86814)). Qed.
Lemma lem86823 : term128.
Proof. exact (proj1 (@lem86815)). Qed.
Lemma lem86824 (m : nat) : term129 m.
Proof. exact (@lem86823 m). Qed.
Lemma lem86825 (m : nat) : (term129 m) = (term130 m).
Proof. exact (eq_refl (term129 m)). Qed.
Lemma lem86826 (m : nat) : term130 m.
Proof. exact (EQ_MP (@lem86825 m) (@lem86824 m)). Qed.
Lemma lem86827 (m : nat) (n : nat) : term131 m n.
Proof. exact (@lem86826 m n). Qed.
Lemma lem86828 (m : nat) (n : nat) : (term131 m n) = ((term132 m n) = (term133 m n)).
Proof. exact (eq_refl (term131 m n)). Qed.
Lemma lem86846 : term107.
Proof. exact (proj2 (@lem86199)). Qed.
Lemma lem86847 (m : nat) : term108 m.
Proof. exact (@lem86846 m). Qed.
Lemma lem86848 (m : nat) : (term108 m) = (term109 m).
Proof. exact (eq_refl (term108 m)). Qed.
Lemma lem86849 (m : nat) : term109 m.
Proof. exact (EQ_MP (@lem86848 m) (@lem86847 m)). Qed.
Lemma lem86850 (m : nat) (n : nat) : term110 m n.
Proof. exact (@lem86849 m n). Qed.
Lemma lem86851 (m : nat) (n : nat) : (term110 m n) = ((term111 m n) = (term112 m n)).
Proof. exact (eq_refl (term110 m n)). Qed.
Lemma lem86857 (n : nat) : term90 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem86858 (n : nat) : (term90 n) = (term91 n).
Proof. exact (eq_refl (term90 n)). Qed.
Lemma lem86859 (n : nat) : term91 n.
Proof. exact (EQ_MP (@lem86858 n) (@lem86857 n)). Qed.
Lemma lem86860 (n : nat) : term92 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem86900 (m : nat) (n : nat) : (term111 m n) = (term112 m n).
Proof. exact (EQ_MP (@lem86851 m n) (@lem86850 m n)). Qed.
Lemma lem86901 (m : nat) (n : nat) : (term68 m n) = (term134 m n).
Proof. exact (@lem86900 (S m) n). Qed.
Lemma lem86903 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (EQ_MP (@lem86828 m n) (@lem86827 m n)). Qed.
Lemma lem86904 (m : nat) (n : nat) : (term134 m n) = (term135 m n).
Proof. exact (@lem86903 m (term63 m n)). Qed.
Lemma lem86905 (m : nat) (n : nat) : (term68 m n) = (term135 m n).
Proof. exact (TRANS (@lem86901 m n) (@lem86904 m n)). Qed.
Lemma lem86906 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem86907 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (MK_COMB (@lem86906) (@lem86905 m n)). Qed.
Lemma lem86908 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem86909 (m : nat) (n : nat) : ((term68 m n) = (NUMERAL 0)) = ((term135 m n) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem86907 m n) (@lem86908)). Qed.
Lemma lem86911 (m : nat) (n : nat) : ((Nat.add m n) = (NUMERAL 0)) = (term123 m n).
Proof. exact (EQ_MP (@lem86786 m n) (@lem86785 m n)). Qed.
Lemma lem86912 (m : nat) (n : nat) : ((term135 m n) = (NUMERAL 0)) = (term138 m n).
Proof. exact (@lem86911 (term139 m n) (term63 m n)). Qed.
Lemma lem86918 (m : nat) (n : nat) (h1 : ((term63 m n) = (NUMERAL 0)) = (term64 m n)) : ((term63 m n) = (NUMERAL 0)) = (term64 m n).
Proof. exact (h1). Qed.
Lemma lem86922 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem86860 n (@lem86859 n)). Qed.
Lemma lem86923 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem86922 m). Qed.
Lemma lem86924 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem86925 (m : nat) : (term119 m) = (and False).
Proof. exact (MK_COMB (@lem86924) (@lem86923 m)). Qed.
Lemma lem86928 (n : nat) : (term140 n) = (term140 n).
Proof. exact (eq_refl (term140 n)). Qed.
Lemma lem86929 (m : nat) (n : nat) : (term64 m n) = (term141 n).
Proof. exact (MK_COMB (@lem86925 m) (@lem86928 n)). Qed.
Lemma lem86931 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem86932 (n : nat) : (term141 n) = False.
Proof. exact (@lem86931 (term140 n)). Qed.
Lemma lem86933 (m : nat) (n : nat) : (term64 m n) = False.
Proof. exact (TRANS (@lem86929 m n) (@lem86932 n)). Qed.
Lemma lem86934 (m : nat) (n : nat) (h1 : ((term63 m n) = (NUMERAL 0)) = (term64 m n)) : ((term63 m n) = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem86918 m n h1) (@lem86933 m n)). Qed.
Lemma lem86935 (m : nat) (n : nat) : (term142 m n) = (term142 m n).
Proof. exact (eq_refl (term142 m n)). Qed.
Lemma lem86936 (m : nat) (n : nat) (h1 : ((term63 m n) = (NUMERAL 0)) = (term64 m n)) : (term138 m n) = (term143 m n).
Proof. exact (MK_COMB (@lem86935 m n) (@lem86934 m n h1)). Qed.
Lemma lem86938 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem86939 (m : nat) (n : nat) : (term143 m n) = False.
Proof. exact (@lem86938 ((term139 m n) = (NUMERAL 0))). Qed.
Lemma lem86940 (m : nat) (n : nat) (h1 : ((term63 m n) = (NUMERAL 0)) = (term64 m n)) : (term138 m n) = False.
Proof. exact (TRANS (@lem86936 m n h1) (@lem86939 m n)). Qed.
Lemma lem86941 (m : nat) (n : nat) (h1 : ((term63 m n) = (NUMERAL 0)) = (term64 m n)) : ((term135 m n) = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem86912 m n) (@lem86940 m n h1)). Qed.
Lemma lem86942 (m : nat) (n : nat) (h1 : ((term63 m n) = (NUMERAL 0)) = (term64 m n)) : ((term68 m n) = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem86909 m n) (@lem86941 m n h1)). Qed.
Lemma lem86943 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem86944 (m : nat) (n : nat) (h1 : ((term63 m n) = (NUMERAL 0)) = (term64 m n)) : (term144 m n) = (@eq Prop False).
Proof. exact (MK_COMB (@lem86943) (@lem86942 m n h1)). Qed.
Lemma lem86948 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem86860 n (@lem86859 n)). Qed.
Lemma lem86949 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem86948 m). Qed.
Lemma lem86950 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem86951 (m : nat) : (term119 m) = (and False).
Proof. exact (MK_COMB (@lem86950) (@lem86949 m)). Qed.
Lemma lem86953 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem86860 n (@lem86859 n)). Qed.
Lemma lem86954 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem86955 (n : nat) : (term91 n) = (~ False).
Proof. exact (MK_COMB (@lem86954) (@lem86953 n)). Qed.
Lemma lem86957 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem86958 (n : nat) : (term91 n) = True.
Proof. exact (TRANS (@lem86955 n) (@lem86957)). Qed.
Lemma lem86959 (m : nat) (n : nat) : (term69 m n) = (False /\ True).
Proof. exact (MK_COMB (@lem86951 m) (@lem86958 n)). Qed.
Lemma lem86961 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem86962 : (False /\ True) = False.
Proof. exact (@lem86961 True). Qed.
Lemma lem86963 (m : nat) (n : nat) : (term69 m n) = False.
Proof. exact (TRANS (@lem86959 m n) (@lem86962)). Qed.
Lemma lem86964 (m : nat) (n : nat) (h1 : ((term63 m n) = (NUMERAL 0)) = (term64 m n)) : (((term68 m n) = (NUMERAL 0)) = (term69 m n)) = (False = False).
Proof. exact (MK_COMB (@lem86944 m n h1) (@lem86963 m n)). Qed.
Lemma lem86966 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem86967 : (False = False) = (~ False).
Proof. exact (@lem86966 False). Qed.
Lemma lem86969 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem86970 : (False = False) = True.
Proof. exact (TRANS (@lem86967) (@lem86969)). Qed.
Lemma lem86971 (m : nat) (n : nat) (h1 : ((term63 m n) = (NUMERAL 0)) = (term64 m n)) : (((term68 m n) = (NUMERAL 0)) = (term69 m n)) = True.
Proof. exact (TRANS (@lem86964 m n h1) (@lem86970)). Qed.
Lemma lem86972 (m : nat) (n : nat) (h1 : ((term63 m n) = (NUMERAL 0)) = (term64 m n)) : True = (((term68 m n) = (NUMERAL 0)) = (term69 m n)).
Proof. exact (SYM (@lem86971 m n h1)). Qed.
Lemma lem86973 (m : nat) (n : nat) (h1 : ((term63 m n) = (NUMERAL 0)) = (term64 m n)) : ((term68 m n) = (NUMERAL 0)) = (term69 m n).
Proof. exact (EQ_MP (@lem86972 m n h1) (@lem0)). Qed.
Lemma lem86974 (m : nat) (n : nat) : term71 m n.
Proof. exact (fun h0 : ((term63 m n) = (NUMERAL 0)) = (term64 m n) => @lem86973 m n h0). Qed.
Lemma lem86979 (m : nat) : term75 m.
Proof. exact (fun n : nat => @lem86974 m n). Qed.
Lemma lem86980 (m : nat) : term77 m.
Proof. exact (conj (@lem86781 m) (@lem86979 m)). Qed.
Lemma lem86981 (m : nat) : term12 m.
Proof. exact (@lem86277 m (@lem86980 m)). Qed.
Lemma lem86982 (n : nat) : term43 n.
Proof. exact (fun h0 : ((term35 n) = (NUMERAL 0)) = (term36 n) => @lem86610 n). Qed.
Lemma lem86987 : term47.
Proof. exact (fun n : nat => @lem86982 n). Qed.
Lemma lem86988 : term49.
Proof. exact (conj (@lem86451) (@lem86987)). Qed.
Lemma lem86989 : term4.
Proof. exact (@lem86249 (@lem86988)). Qed.
Lemma lem86990 (m : nat) : term14 m.
Proof. exact (fun h0 : term8 m => @lem86981 m). Qed.
Lemma lem86995 : term18.
Proof. exact (fun m : nat => @lem86990 m). Qed.
Lemma lem86996 : term20.
Proof. exact (conj (@lem86989) (@lem86995)). Qed.
Lemma lem86997 : term25.
Proof. exact (@lem86225 (@lem86996)). Qed.
