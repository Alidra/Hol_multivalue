Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIV_LE_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import DIVISION_spec.
Require Import DIV_ZERO_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LE_0_spec.
Require Import LE_ADD_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem178255 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (h1). Qed.
Lemma lem178256 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (SYM (@lem178255 m n p h1)). Qed.
Lemma lem178257 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (h1). Qed.
Lemma lem178258 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (SYM (@lem178257 m n p h1)). Qed.
Lemma lem178259 (m : nat) (n : nat) (p : nat) : ((term0 m n p) = (term1 m n p)) = ((term1 m n p) = (term0 m n p)).
Proof. exact (prop_ext (fun h1 : (term0 m n p) = (term1 m n p) => @lem178256 m n p h1) (fun h1 : (term1 m n p) = (term0 m n p) => @lem178258 m n p h1)). Qed.
Lemma lem178260 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (fun_ext (fun p : nat => @lem178259 m n p)). Qed.
Lemma lem178261 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem178262 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (MK_COMB (@lem178261) (@lem178260 m n)). Qed.
Lemma lem178263 (m : nat) : (term6 m) = (term7 m).
Proof. exact (fun_ext (fun n : nat => @lem178262 m n)). Qed.
Lemma lem178264 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem178265 (m : nat) : (term8 m) = (term9 m).
Proof. exact (MK_COMB (@lem178264) (@lem178263 m)). Qed.
Lemma lem178266 : term10 = term11.
Proof. exact (fun_ext (fun m : nat => @lem178265 m)). Qed.
Lemma lem178267 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem178268 : term12 = term13.
Proof. exact (MK_COMB (@lem178267) (@lem178266)). Qed.
Lemma lem178269 : term13.
Proof. exact (EQ_MP (@lem178268) (@lem77960)). Qed.
Lemma lem178270 (m : nat) : term14 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem178271 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem178272 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem178271 m) (@lem178270 m)). Qed.
Lemma lem178273 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem178272 m n). Qed.
Lemma lem178274 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem178275 (m : nat) (n : nat) : term17 m n.
Proof. exact (EQ_MP (@lem178274 m n) (@lem178273 m n)). Qed.
Lemma lem178276 (m : nat) (n : nat) : (term17 m n) = ((term17 m n) = True).
Proof. exact (@lem7 (term17 m n)). Qed.
Lemma lem178278 (m : nat) : term18 m.
Proof. exact (@lem178269 m). Qed.
Lemma lem178279 (m : nat) : (term18 m) = (term9 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem178280 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem178279 m) (@lem178278 m)). Qed.
Lemma lem178281 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem178280 m n). Qed.
Lemma lem178282 (m : nat) (n : nat) : (term19 m n) = (term5 m n).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem178283 (m : nat) (n : nat) : term5 m n.
Proof. exact (EQ_MP (@lem178282 m n) (@lem178281 m n)). Qed.
Lemma lem178284 (m : nat) (n : nat) (p : nat) : term20 m n p.
Proof. exact (@lem178283 m n p). Qed.
Lemma lem178285 (m : nat) (n : nat) (p : nat) : (term20 m n p) = ((term1 m n p) = (term0 m n p)).
Proof. exact (eq_refl (term20 m n p)). Qed.
Lemma lem178287 : term21.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem178288 : term22.
Proof. exact (proj2 (@lem178287)). Qed.
Lemma lem178289 : term23.
Proof. exact (proj2 (@lem178288)). Qed.
Lemma lem178290 : term24.
Proof. exact (proj2 (@lem178289)). Qed.
Lemma lem178291 : term25.
Proof. exact (proj2 (@lem178290)). Qed.
Lemma lem178292 (m : nat) : term26 m.
Proof. exact (@lem178291 m). Qed.
Lemma lem178293 (m : nat) : (term26 m) = (term27 m).
Proof. exact (eq_refl (term26 m)). Qed.
Lemma lem178294 (m : nat) : term27 m.
Proof. exact (EQ_MP (@lem178293 m) (@lem178292 m)). Qed.
Lemma lem178295 (m : nat) (n : nat) : term28 m n.
Proof. exact (@lem178294 m n). Qed.
Lemma lem178296 (m : nat) (n : nat) : (term28 m n) = ((term29 m n) = (term30 m n)).
Proof. exact (eq_refl (term28 m n)). Qed.
Lemma lem178313 : term31.
Proof. exact (proj1 (@lem178287)). Qed.
Lemma lem178314 (m : nat) : term32 m.
Proof. exact (@lem178313 m). Qed.
Lemma lem178315 (m : nat) : (term32 m) = ((term33 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term32 m)). Qed.
Lemma lem178321 (n : nat) : term34 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem178322 (n : nat) : (term34 n) = (term35 n).
Proof. exact (eq_refl (term34 n)). Qed.
Lemma lem178323 (n : nat) : term35 n.
Proof. exact (EQ_MP (@lem178322 n) (@lem178321 n)). Qed.
Lemma lem178325 (n : nat) (h1 : term36 n) : term36 n.
Proof. exact (h1). Qed.
Lemma lem178326 (n : nat) : term37 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem178327 (n : nat) : (term37 n) = (term38 n).
Proof. exact (eq_refl (term37 n)). Qed.
Lemma lem178328 (n : nat) : term38 n.
Proof. exact (EQ_MP (@lem178327 n) (@lem178326 n)). Qed.
Lemma lem178329 (n : nat) : (term38 n) = ((term38 n) = True).
Proof. exact (@lem7 (term38 n)). Qed.
Lemma lem178331 (n : nat) : term39 n.
Proof. exact (@lem158192 n). Qed.
Lemma lem178332 (n : nat) : (term39 n) = ((term40 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term39 n)). Qed.
Lemma lem178335 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem178336 (m : nat) : (Nat.div m) = (Nat.div m).
Proof. exact (eq_refl (Nat.div m)). Qed.
Lemma lem178337 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.div m n) = (term40 m).
Proof. exact (MK_COMB (@lem178336 m) (@lem178335 n h1)). Qed.
Lemma lem178339 (n : nat) : (term40 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem178332 n) (@lem178331 n)). Qed.
Lemma lem178340 (m : nat) : (term40 m) = (NUMERAL 0).
Proof. exact (@lem178339 m). Qed.
Lemma lem178341 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.div m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem178337 m n h1) (@lem178340 m)). Qed.
Lemma lem178342 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem178343 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term41 m n) = term42.
Proof. exact (MK_COMB (@lem178342) (@lem178341 m n h1)). Qed.
Lemma lem178344 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem178345 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term43 n m) = (term38 m).
Proof. exact (MK_COMB (@lem178343 m n h1) (@lem178344 m)). Qed.
Lemma lem178347 (n : nat) : (term38 n) = True.
Proof. exact (EQ_MP (@lem178329 n) (@lem178328 n)). Qed.
Lemma lem178348 (m : nat) : (term38 m) = True.
Proof. exact (@lem178347 m). Qed.
Lemma lem178349 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term43 n m) = True.
Proof. exact (TRANS (@lem178345 m n h1) (@lem178348 m)). Qed.
Lemma lem178350 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : True = (term43 n m).
Proof. exact (SYM (@lem178349 m n h1)). Qed.
Lemma lem178351 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : term43 n m.
Proof. exact (EQ_MP (@lem178350 m n h1) (@lem0)). Qed.
Lemma lem178375 (h1 : term44) : term44.
Proof. exact (h1). Qed.
Lemma lem178376 (m : nat) (h1 : term44) : term45 m.
Proof. exact (@lem178375 h1 m). Qed.
Lemma lem178377 (m : nat) : (term45 m) = (term46 m).
Proof. exact (eq_refl (term45 m)). Qed.
Lemma lem178378 (m : nat) (h1 : term44) : term46 m.
Proof. exact (EQ_MP (@lem178377 m) (@lem178376 m h1)). Qed.
Lemma lem178379 (m : nat) (n : nat) (h1 : term44) : term47 m n.
Proof. exact (@lem178378 m h1 n). Qed.
Lemma lem178380 (m : nat) (n : nat) : (term47 m n) = (term48 m n).
Proof. exact (eq_refl (term47 m n)). Qed.
Lemma lem178381 (m : nat) (n : nat) (h1 : term44) : term48 m n.
Proof. exact (EQ_MP (@lem178380 m n) (@lem178379 m n h1)). Qed.
Lemma lem178382 (n : nat) (h1 : term36 n) : term36 n.
Proof. exact (h1). Qed.
Lemma lem178383 (m : nat) (n : nat) (h1 : term44) (h2 : term36 n) : term49 m n.
Proof. exact (@lem178381 m n h1 (@lem178382 n h2)). Qed.
Lemma lem178384 (n : nat) (h1 : term44) (h2 : term36 n) : term50 n.
Proof. exact (fun m : nat => @lem178383 m n h1 h2). Qed.
Lemma lem178385 (n : nat) (h1 : term44) : term51 n.
Proof. exact (fun h0 : term36 n => @lem178384 n h1 h0). Qed.
Lemma lem178386 (h1 : term44) : term52.
Proof. exact (fun n : nat => @lem178385 n h1). Qed.
Lemma lem178387 : term53.
Proof. exact (fun h0 : term44 => @lem178386 h0). Qed.
Lemma lem178388 : term52.
Proof. exact (@lem178387 (@lem157261)). Qed.
Lemma lem178389 (n : nat) : term54 n.
Proof. exact (@lem178388 n). Qed.
Lemma lem178390 (n : nat) : (term54 n) = (term51 n).
Proof. exact (eq_refl (term54 n)). Qed.
Lemma lem178393 (n : nat) : term51 n.
Proof. exact (EQ_MP (@lem178390 n) (@lem178389 n)). Qed.
Lemma lem178394 (n : nat) (h1 : term36 n) : term50 n.
Proof. exact (@lem178393 n (@lem178325 n h1)). Qed.
Lemma lem178395 (m : nat) (n : nat) (h1 : term36 n) : term55 n m.
Proof. exact (@lem178394 n h1 m). Qed.
Lemma lem178396 (m : nat) (n : nat) : (term55 n m) = (term49 m n).
Proof. exact (eq_refl (term55 n m)). Qed.
Lemma lem178397 (m : nat) (n : nat) (h1 : term36 n) : term49 m n.
Proof. exact (EQ_MP (@lem178396 m n) (@lem178395 m n h1)). Qed.
Lemma lem178403 (m : nat) (n : nat) (h1 : term36 n) : m = (term56 m n).
Proof. exact (proj1 (@lem178397 m n h1)). Qed.
Lemma lem178404 (m : nat) (n : nat) : (term41 m n) = (term41 m n).
Proof. exact (eq_refl (term41 m n)). Qed.
Lemma lem178405 (m : nat) (n : nat) (h1 : term36 n) : (term43 n m) = (term57 m n).
Proof. exact (MK_COMB (@lem178404 m n) (@lem178403 m n h1)). Qed.
Lemma lem178406 (m : nat) (n : nat) (h1 : term36 n) : (term57 m n) = (term43 n m).
Proof. exact (SYM (@lem178405 m n h1)). Qed.
Lemma lem178408 (P : nat -> Prop) : term58 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem178409 (m : nat) : term59 m.
Proof. exact (@lem178408 (term60 m)). Qed.
Lemma lem178410 (m : nat) : (term61 m) = (term62 m).
Proof. exact (eq_refl (term61 m)). Qed.
Lemma lem178411 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem178412 (m : nat) : (term63 m) = (term64 m).
Proof. exact (MK_COMB (@lem178411) (@lem178410 m)). Qed.
Lemma lem178413 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (eq_refl (term65 m n)). Qed.
Lemma lem178414 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem178415 (m : nat) (n : nat) : (term67 m n) = (term68 m n).
Proof. exact (MK_COMB (@lem178414) (@lem178413 m n)). Qed.
Lemma lem178416 (m : nat) (n : nat) : (term69 m n) = (term70 m n).
Proof. exact (eq_refl (term69 m n)). Qed.
Lemma lem178417 (m : nat) (n : nat) : (term71 m n) = (term72 m n).
Proof. exact (MK_COMB (@lem178415 m n) (@lem178416 m n)). Qed.
Lemma lem178418 (m : nat) : (term73 m) = (term74 m).
Proof. exact (fun_ext (fun n : nat => @lem178417 m n)). Qed.
Lemma lem178419 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem178420 (m : nat) : (term75 m) = (term76 m).
Proof. exact (MK_COMB (@lem178419) (@lem178418 m)). Qed.
Lemma lem178421 (m : nat) : (term77 m) = (term78 m).
Proof. exact (MK_COMB (@lem178412 m) (@lem178420 m)). Qed.
Lemma lem178422 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem178423 (m : nat) : (term79 m) = (term80 m).
Proof. exact (MK_COMB (@lem178422) (@lem178421 m)). Qed.
Lemma lem178424 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (eq_refl (term65 m n)). Qed.
Lemma lem178425 (m : nat) : (term81 m) = (term60 m).
Proof. exact (fun_ext (fun n : nat => @lem178424 m n)). Qed.
Lemma lem178426 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem178427 (m : nat) : (term82 m) = (term83 m).
Proof. exact (MK_COMB (@lem178426) (@lem178425 m)). Qed.
Lemma lem178428 (m : nat) : (term59 m) = (term84 m).
Proof. exact (MK_COMB (@lem178423 m) (@lem178427 m)). Qed.
Lemma lem178429 (m : nat) : term84 m.
Proof. exact (EQ_MP (@lem178428 m) (@lem178409 m)). Qed.
Lemma lem178434 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem178435 (x : nat) : (x = x) = True.
Proof. exact (@lem178434 nat x). Qed.
Lemma lem178436 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem178435 (NUMERAL 0)). Qed.
Lemma lem178437 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem178438 : term85 = (~ True).
Proof. exact (MK_COMB (@lem178437) (@lem178436)). Qed.
Lemma lem178440 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem178441 : term85 = False.
Proof. exact (TRANS (@lem178438) (@lem178440)). Qed.
Lemma lem178442 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem178443 : term86 = (imp False).
Proof. exact (MK_COMB (@lem178442) (@lem178441)). Qed.
Lemma lem178447 (m : nat) : (term33 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem178315 m) (@lem178314 m)). Qed.
Lemma lem178448 (m : nat) : (term87 m) = (NUMERAL 0).
Proof. exact (@lem178447 (term40 m)). Qed.
Lemma lem178449 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem178450 (m : nat) : (term88 m) = term89.
Proof. exact (MK_COMB (@lem178449) (@lem178448 m)). Qed.
Lemma lem178451 (m : nat) : (term90 m) = (term90 m).
Proof. exact (eq_refl (term90 m)). Qed.
Lemma lem178452 (m : nat) : (term91 m) = (term92 m).
Proof. exact (MK_COMB (@lem178450 m) (@lem178451 m)). Qed.
Lemma lem178453 (m : nat) : (term93 m) = (term93 m).
Proof. exact (eq_refl (term93 m)). Qed.
Lemma lem178454 (m : nat) : (term94 m) = (term95 m).
Proof. exact (MK_COMB (@lem178453 m) (@lem178452 m)). Qed.
Lemma lem178457 (m : nat) : (term62 m) = (term96 m).
Proof. exact (MK_COMB (@lem178443) (@lem178454 m)). Qed.
Lemma lem178459 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem178460 (m : nat) : (term96 m) = True.
Proof. exact (@lem178459 (term95 m)). Qed.
Lemma lem178461 (m : nat) : (term62 m) = True.
Proof. exact (TRANS (@lem178457 m) (@lem178460 m)). Qed.
Lemma lem178462 (m : nat) : True = (term62 m).
Proof. exact (SYM (@lem178461 m)). Qed.
Lemma lem178463 (m : nat) : term62 m.
Proof. exact (EQ_MP (@lem178462 m) (@lem0)). Qed.
Lemma lem178471 (m : nat) (n : nat) : (term29 m n) = (term30 m n).
Proof. exact (EQ_MP (@lem178296 m n) (@lem178295 m n)). Qed.
Lemma lem178472 (m : nat) (n : nat) : (term97 m n) = (term98 m n).
Proof. exact (@lem178471 (term99 m n) n). Qed.
Lemma lem178473 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem178474 (m : nat) (n : nat) : (term100 m n) = (term101 m n).
Proof. exact (MK_COMB (@lem178473) (@lem178472 m n)). Qed.
Lemma lem178475 (m : nat) (n : nat) : (term102 m n) = (term102 m n).
Proof. exact (eq_refl (term102 m n)). Qed.
Lemma lem178476 (m : nat) (n : nat) : (term103 m n) = (term104 m n).
Proof. exact (MK_COMB (@lem178474 m n) (@lem178475 m n)). Qed.
Lemma lem178478 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (EQ_MP (@lem178285 m n p) (@lem178284 m n p)). Qed.
Lemma lem178479 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (@lem178478 (term99 m n) (term106 m n) (term102 m n)). Qed.
Lemma lem178480 (m : nat) (n : nat) : (term103 m n) = (term105 m n).
Proof. exact (TRANS (@lem178476 m n) (@lem178479 m n)). Qed.
Lemma lem178481 (m : nat) (n : nat) : (term107 m n) = (term107 m n).
Proof. exact (eq_refl (term107 m n)). Qed.
Lemma lem178482 (m : nat) (n : nat) : (term108 m n) = (term109 m n).
Proof. exact (MK_COMB (@lem178481 m n) (@lem178480 m n)). Qed.
Lemma lem178484 (m : nat) (n : nat) : (term17 m n) = True.
Proof. exact (EQ_MP (@lem178276 m n) (@lem178275 m n)). Qed.
Lemma lem178485 (m : nat) (n : nat) : (term109 m n) = True.
Proof. exact (@lem178484 (term99 m n) (term110 m n)). Qed.
Lemma lem178486 (m : nat) (n : nat) : (term108 m n) = True.
Proof. exact (TRANS (@lem178482 m n) (@lem178485 m n)). Qed.
Lemma lem178487 (n : nat) : (term111 n) = (term111 n).
Proof. exact (eq_refl (term111 n)). Qed.
Lemma lem178488 (m : nat) (n : nat) : (term70 m n) = (term112 n).
Proof. exact (MK_COMB (@lem178487 n) (@lem178486 m n)). Qed.
Lemma lem178490 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem178491 (n : nat) : (term112 n) = True.
Proof. exact (@lem178490 (term113 n)). Qed.
Lemma lem178492 (m : nat) (n : nat) : (term70 m n) = True.
Proof. exact (TRANS (@lem178488 m n) (@lem178491 n)). Qed.
Lemma lem178493 (m : nat) (n : nat) : True = (term70 m n).
Proof. exact (SYM (@lem178492 m n)). Qed.
Lemma lem178494 (m : nat) (n : nat) : term70 m n.
Proof. exact (EQ_MP (@lem178493 m n) (@lem0)). Qed.
Lemma lem178495 (m : nat) (n : nat) : term72 m n.
Proof. exact (fun h0 : term66 m n => @lem178494 m n). Qed.
Lemma lem178500 (m : nat) : term76 m.
Proof. exact (fun n : nat => @lem178495 m n). Qed.
Lemma lem178501 (m : nat) : term78 m.
Proof. exact (conj (@lem178463 m) (@lem178500 m)). Qed.
Lemma lem178502 (m : nat) : term83 m.
Proof. exact (@lem178429 m (@lem178501 m)). Qed.
Lemma lem178503 (m : nat) (n : nat) : term65 m n.
Proof. exact (@lem178502 m n). Qed.
Lemma lem178504 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (eq_refl (term65 m n)). Qed.
Lemma lem178505 (m : nat) (n : nat) : term66 m n.
Proof. exact (EQ_MP (@lem178504 m n) (@lem178503 m n)). Qed.
Lemma lem178506 (m : nat) (n : nat) (h1 : term36 n) : term57 m n.
Proof. exact (@lem178505 m n (@lem178325 n h1)). Qed.
Lemma lem178508 (m : nat) (n : nat) (h1 : term36 n) : term43 n m.
Proof. exact (EQ_MP (@lem178406 m n h1) (@lem178506 m n h1)). Qed.
Lemma lem178509 (n : nat) (m : nat) : term43 n m.
Proof. exact (or_elim (@lem178323 n) (fun h0 : n = (NUMERAL 0) => @lem178351 m n h0) (fun h0 : term36 n => @lem178508 m n h0)). Qed.
Lemma lem178514 (m : nat) : term114 m.
Proof. exact (fun n : nat => @lem178509 n m). Qed.
Lemma lem178519 : term115.
Proof. exact (fun m : nat => @lem178514 m). Qed.
